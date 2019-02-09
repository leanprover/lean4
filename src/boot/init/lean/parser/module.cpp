// Lean compiler output
// Module: init.lean.parser.module
// Imports: init.lean.parser.command init.control.coroutine
#include "runtime/object.h"
#include "runtime/apply.h"
#include "runtime/io.h"
#include "kernel/builtin.h"
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
obj* l_lean_parser_module__parser__m_lean_parser_monad__parsec;
obj* l_lean_parser_module__parser__m_monad__except;
obj* l___private_209794555__commands__aux___main___lambda__17___boxed(obj*, obj*, obj*);
obj* l_lean_parser_module_parser___lambda__5(obj*);
obj* l_lean_parser_parsec__t_bind__mk__res___rarg(obj*, obj*);
obj* l_lean_parser_module_header_parser_lean_parser_has__view;
obj* l_lean_parser_module_import__path_parser___closed__1;
extern obj* l___private_1297690757__many1__aux___main___rarg___closed__1;
obj* l_lean_parser_module_parser___lambda__6(obj*, obj*);
obj* l_lean_parser_module_prelude_has__view_x_27;
obj* l_list_map___main___rarg(obj*, obj*);
obj* l_lean_parser_module_import_has__view;
obj* l_lean_parser_module_parser___lambda__3(obj*);
extern uint8 l_true_decidable;
obj* l___private_209794555__commands__aux___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_module_commands_parser_has__view___lambda__2(obj*);
obj* l_coe__trans___rarg(obj*, obj*, obj*);
obj* l_lean_parser_log__message___at___private_209794555__commands__aux___main___spec__4___lambda__2(obj*, obj*);
extern obj* l_lean_parser_combinators_many___rarg___closed__1;
obj* l_lean_parser_module_yield__command___lambda__8(obj*, obj*, obj*, obj*);
obj* l___private_209794555__commands__aux___main___lambda__9(obj*, obj*, obj*);
obj* l_lean_parser_module_tokens;
obj* l___private_209794555__commands__aux___main___lambda__15(uint8, obj*);
obj* l_list_map___main___at_lean_parser_module_commands_parser_has__view___spec__2(obj*);
obj* l_lean_parser_module_header_has__view_x_27___lambda__1___closed__2;
obj* l_coe__b___rarg(obj*, obj*);
obj* l_lean_parser_module_import__path_has__view_x_27___lambda__1___closed__4;
obj* l_lean_parser_module_import__path;
obj* l_lean_parser_module_parser___lambda__1(obj*, obj*, obj*, obj*);
obj* l_lean_parser_log__message___at___private_209794555__commands__aux___main___spec__4(obj*, obj*, obj*, obj*);
obj* l___private_209794555__commands__aux___main___lambda__16(obj*, obj*);
obj* l_reader__t_lift___at_lean_parser_with__trailing___spec__1___rarg(obj*, obj*, obj*, obj*);
extern obj* l_mjoin___rarg___closed__1;
obj* l_lean_parser_module_import_parser___closed__1;
obj* l_lean_parser_module_header_has__view_x_27___lambda__1___closed__6;
obj* l___private_209794555__commands__aux___main___lambda__3___closed__1;
extern obj* l_lean_parser_basic__parser__m_monad;
obj* l_lean_parser_with__trailing___rarg___lambda__1(obj*, obj*);
obj* l_lean_parser_module_header_has__view_x_27___lambda__1___closed__4;
obj* l___private_209794555__commands__aux___main___lambda__13___closed__1;
obj* l_lean_parser_string__lit_has__view_x_27___lambda__1(obj*);
obj* l_lean_parser_module_parser___lambda__9(obj*);
obj* l___private_209794555__commands__aux___main___lambda__8(obj*, obj*);
obj* l___private_209794555__commands__aux___main(uint8, obj*, obj*, obj*, obj*);
obj* l_lean_parser_list_cons_tokens___rarg(obj*, obj*);
obj* l_coroutine_monad__reader___rarg(obj*);
obj* l_lean_parser_parsec__t_try__mk__res___rarg(obj*);
obj* l_lean_parser_module_commands_parser___lambda__1(obj*, obj*);
extern obj* l_lean_parser_monad__parsec_eoi___rarg___lambda__1___closed__1;
obj* l_lean_parser_monad__parsec_any___at___private_209794555__commands__aux___main___spec__3___lambda__2(obj*, obj*);
obj* l_lean_parser_module_header_has__view_x_27___lambda__2___closed__1;
obj* l_lean_parser_module_import;
obj* l_lean_parser_module__parser__m_monad__coroutine;
obj* l_lean_parser_parsec__t_labels__mk__res___rarg(obj*, obj*);
obj* l_string_quote(obj*);
extern obj* l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
obj* l_lean_parser_module_header_has__view_x_27___lambda__2(obj*);
obj* l___private_209794555__commands__aux___main___lambda__12(obj*);
obj* l___private_209794555__commands__aux___main___lambda__15___boxed(obj*, obj*);
obj* l___private_209794555__commands__aux___main___lambda__4(obj*, obj*, obj*, obj*);
obj* l___private_209794555__commands__aux___main___lambda__2(obj*);
obj* l_lean_parser_message__of__parsec__message___rarg(obj*, obj*);
obj* l_lean_parser_module_header_parser(obj*, obj*, obj*);
obj* l_lean_parser_module_parser___lambda__4(obj*);
obj* l_coe__t___rarg(obj*, obj*);
obj* l_lean_parser_module_import_has__view_x_27;
obj* l_state__t_monad__state___rarg(obj*);
obj* l_list_map___main___at_lean_parser_module_commands_parser_has__view___spec__1(obj*);
obj* l___private_209794555__commands__aux___main___lambda__9___closed__1;
obj* l_lean_parser_module__parser__m_monad__reader;
obj* l_lean_parser_module_yield__command___lambda__2(obj*, obj*, obj*, obj*);
obj* l_lean_parser_module_parser(obj*, obj*, obj*);
extern obj* l_lean_name_to__string___closed__1;
obj* l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__3(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_combinators_optional___at_lean_parser_module_header_parser_lean_parser_has__tokens___spec__1(obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_command_parser___rarg___closed__1;
obj* l_lean_parser_module_import_has__view_x_27___lambda__1___closed__2;
obj* l___private_209794555__commands__aux___main___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_function_comp___rarg(obj*, obj*, obj*);
obj* l_lean_parser_module__parser__config__coe(obj*);
obj* l_lean_parser_module_header_has__view_x_27___lambda__1___closed__3;
obj* l_lean_parser_module_import__path_has__view_x_27___lambda__2(obj*);
obj* l___private_209794555__commands__aux___main___lambda__7(obj*);
obj* l_lean_parser_module_import__path_has__view_x_27;
obj* l_lean_parser_module_yield__command___lambda__7___closed__1;
obj* l___private_209794555__commands__aux___main___lambda__19(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_module_yield__command___lambda__5(obj*, obj*, obj*);
extern obj* l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
obj* l_lean_parser_module_commands_parser___lambda__2(obj*);
obj* l_lean_parser_module__parser__m_lift__parser__t___rarg___closed__1;
obj* l_reader__t_bind___at_lean_parser_with__trailing___spec__2___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_module_parser___lambda__10(obj*);
obj* l_lean_parser_module_import_has__view_x_27___lambda__1___closed__1;
obj* l_lean_parser_module_prelude_has__view;
obj* l_lean_parser_combinators_many1___at_lean_parser_ident__univ__spec_parser_lean_parser_has__view___spec__1(obj*, obj*, obj*, obj*);
obj* l_lean_parser_tokens___rarg(obj*);
extern obj* l_lean_parser_command_parser_lean_parser_has__tokens;
obj* l_option_get__or__else___main___rarg(obj*, obj*);
obj* l_lean_parser_combinators_node___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__8(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_module_header;
extern obj* l_lean_parser_no__kind;
obj* l_lean_parser_syntax_as__node___main(obj*);
obj* l_lean_parser_module_prelude;
obj* l_lean_parser_module_eoi;
obj* l_lean_parser_module_prelude_parser_lean_parser_has__tokens;
obj* l_monad__coroutine__trans___rarg(obj*, obj*, obj*);
obj* l_lean_parser_module_import_parser_lean_parser_has__view;
obj* l_lean_parser_module__parser__m_monad__state;
obj* l_lean_parser_module_prelude_parser(obj*, obj*, obj*);
obj* l_lean_parser_symbol_tokens___rarg(obj*, obj*);
extern obj* l_lean_message__log_empty;
obj* l___private_209794555__commands__aux___main___lambda__14(obj*, obj*);
obj* l_lean_parser_mk__raw__res(obj*, obj*);
obj* l_lean_parser_module_import__path_parser_lean_parser_has__view;
obj* l_lean_parser_parser__core__t_monad___rarg(obj*);
extern obj* l_char_has__repr___closed__1;
obj* l_lean_parser_module__parser__m_monad;
obj* l_coroutine_bind___main___rarg(obj*, obj*, obj*);
obj* l_lean_parser_module_yield__command___lambda__4(obj*, obj*);
obj* l_lean_parser_module__parser;
obj* l_state__t_monad__functor(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_module_yield__command(obj*, obj*, obj*, obj*);
obj* l_lean_parser_command__parser_run(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_combinators_node_view___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_combinators_many___at_lean_parser_module_import__path_parser_lean_parser_has__tokens___spec__1(obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_finish__comment__block___closed__2;
extern obj* l_string_join___closed__1;
obj* l_id___rarg(obj*);
extern obj* l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
obj* l_lean_parser_log__message___at___private_209794555__commands__aux___main___spec__4___lambda__1(obj*, obj*);
obj* l_lean_parser_module_yield__command___lambda__3(obj*, obj*);
obj* l_lean_parser_syntax_mk__node(obj*, obj*);
obj* l___private_209794555__commands__aux___main___lambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l___private_209794555__commands__aux___main___lambda__10(obj*);
obj* l___private_209794555__commands__aux___main___lambda__10___closed__1;
obj* l_lean_parser_monad__parsec_eoi___at___private_209794555__commands__aux___main___spec__2___lambda__1(obj*, obj*);
obj* l_lean_parser_module_import__path_parser_lean_parser_has__view___lambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at___private_209794555__commands__aux___main___spec__1(obj*);
obj* l_lean_parser_command__parser__config__coe__parser__config(obj*);
obj* l_lean_parser_module_commands_tokens;
obj* l_lean_parser_module__parser__m_basic__parser__m___closed__1;
obj* l_state__t_monad__except___rarg(obj*, obj*, obj*);
obj* l_lean_parser_token(obj*, obj*, obj*);
obj* l___private_209794555__commands__aux___main___lambda__11(obj*, obj*);
obj* l_lean_parser_whitespace(obj*, obj*, obj*);
obj* l_lean_parser_module_commands_parser(obj*, obj*, obj*);
obj* l_lean_parser_module_parser___lambda__2(obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec__trans___rarg(obj*, obj*, obj*);
obj* l___private_209794555__commands__aux(uint8, obj*, obj*, obj*, obj*);
obj* l_lean_parser_module_parser___lambda__5___closed__1;
obj* l_lean_parser_monad__parsec_str__core___at___private_4089500695__finish__comment__block__aux___main___spec__3(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_module_import_has__view_x_27___lambda__2(obj*);
obj* l___private_209794555__commands__aux___main___lambda__13(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_module_parser___lambda__7(obj*, obj*);
obj* l_lean_parser_monad__parsec_any___at___private_209794555__commands__aux___main___spec__3(obj*, obj*, obj*);
obj* l_state__t_monad___rarg(obj*);
obj* l___private_209794555__commands__aux___main___lambda__3(obj*, obj*);
obj* l___private_209794555__commands__aux___main___lambda__18(obj*, obj*);
obj* l_lean_parser_module_header_parser_lean_parser_has__tokens;
obj* l_lean_parser_symbol__core___at_lean_parser_unicode__symbol_lean_parser_has__view___spec__1(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2(obj*, obj*);
obj* l_lean_parser_module_commands_parser_has__view___lambda__1(obj*);
obj* l_lean_parser_module_yield__command___lambda__9(obj*, obj*, obj*);
extern obj* l_coroutine_monad___closed__1;
obj* l_lean_parser_monad__parsec_eoi___at___private_209794555__commands__aux___main___spec__2___closed__1;
obj* l_lean_parser_monad__parsec_error___at___private_209794555__commands__aux___main___spec__1___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_module_header_has__view;
obj* l_lean_parser_module_commands_parser_has__view;
obj* l_state__t_alternative___rarg(obj*, obj*);
obj* l___private_209794555__commands__aux___main___lambda__1___closed__1;
obj* l_lean_parser_monad__parsec_error___at___private_209794555__commands__aux___main___spec__1___rarg___lambda__1(obj*, obj*);
obj* l_lean_parser_module_import_has__view_x_27___lambda__1(obj*);
obj* l_lean_parser_module_parser___closed__1;
obj* l_lean_parser_module_import__path_has__view_x_27___lambda__1___closed__3;
obj* l___private_209794555__commands__aux___main___lambda__6(obj*);
obj* l_lean_parser_module_import__path_has__view_x_27___lambda__1___closed__2;
obj* l_lean_parser_module_commands_parser___closed__2;
obj* l_list_map___main___at_lean_parser_module_import__path_has__view_x_27___spec__2(obj*);
obj* l_lean_parser_module_import__path_has__view_x_27___lambda__1___closed__1;
extern obj* l_lean_parser_basic__parser__m_alternative;
obj* l_lean_parser_module_import_parser(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_any___at___private_209794555__commands__aux___main___spec__3___closed__1;
obj* l_lean_parser_module__parser__m_lift__parser__t___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_module_import__path_has__view_x_27___lambda__1(obj*);
obj* l_lean_parser_module_parser___lambda__6___closed__2;
obj* l_string_trim(obj*);
obj* l_lean_parser_module_commands_parser___closed__1;
obj* l_option_get___main___at_lean_parser_run___spec__2(obj*);
obj* l___private_209794555__commands__aux___main___lambda__11___closed__3;
extern obj* l_lean_parser_ident_parser___at_lean_parser_command_notation__spec_fold__action_parser_lean_parser_has__view___spec__4___rarg___closed__1;
extern obj* l_lean_parser_ident__univ__spec_has__view_x_27___lambda__1___closed__1;
obj* l_lean_parser_module_import_parser_lean_parser_has__tokens;
obj* l_lean_parser_parser__core__t_lean_parser_monad__parsec___rarg(obj*);
obj* l_lean_parser_module_header_has__view_x_27___lambda__1(obj*);
obj* l_lean_parser_module_import_has__view_x_27___lambda__2___closed__1;
obj* l_lean_parser_module_parser___lambda__8(obj*, obj*);
obj* l___private_209794555__commands__aux___main___lambda__11___closed__1;
obj* l_lean_parser_monad__parsec_any___at___private_209794555__commands__aux___main___spec__3___lambda__1(obj*, obj*, obj*);
obj* l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__1(obj*);
extern obj* l_lean_parser_parsec__t_monad__fail___rarg___closed__1;
obj* l_lean_parser_parser__core__t_alternative___rarg(obj*);
obj* l_lean_parser_module_prelude_parser_lean_parser_has__view;
obj* l_lean_parser_module_prelude_has__view_x_27___lambda__1(obj*);
obj* l_lean_parser_command_parser(obj*);
obj* l_lean_parser_module_import_has__view_x_27___lambda__1___closed__3;
obj* l_lean_parser_module_header_has__view_x_27___lambda__1___closed__5;
obj* l_lean_parser_module_yield__command___lambda__7(obj*, obj*);
obj* l___private_209794555__commands__aux___main___lambda__17(uint8, obj*, obj*);
obj* l_lean_parser_monad__parsec_eoi___at___private_209794555__commands__aux___main___spec__2(obj*, obj*, obj*);
obj* l_lean_parser_module_header_parser___closed__1;
obj* l_lean_parser_module__parser__m_basic__parser__m(obj*, obj*);
obj* l_lean_parser_module_import__path_has__view;
obj* l_lean_parser_log__message___at___private_209794555__commands__aux___main___spec__5(obj*, obj*, obj*, obj*);
obj* l_lean_parser_parsec__t_has__monad__lift___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_module_import__path_parser(obj*, obj*, obj*);
extern obj* l_lean_parser_basic__parser__m_lean_parser_monad__parsec;
obj* l___private_209794555__commands__aux___main___lambda__11___closed__2;
obj* l_state__t_lift___rarg(obj*, obj*, obj*, obj*);
obj* l_dlist_singleton___rarg(obj*, obj*);
extern obj* l_lean_parser_basic__parser__m_monad__except;
obj* l_lean_parser_parsec__t_orelse__mk__res___rarg(obj*, obj*);
obj* l_list_append___rarg(obj*, obj*);
obj* l_lean_parser_module_parser___lambda__6___closed__1;
obj* l_option_map___rarg(obj*, obj*);
obj* l_lean_parser_module__parser__m_alternative;
obj* l_lean_parser_module__parser__m;
obj* l_coroutine_yield___rarg(obj*, obj*);
obj* l_lean_parser_module_header_has__view_x_27___lambda__1___closed__1;
obj* l_lean_parser_parser__core__t_monad__except___rarg(obj*);
obj* l_lean_parser_ident_parser___at_lean_parser_module_import__path_parser_lean_parser_has__tokens___spec__2(obj*, obj*, obj*);
obj* l_list_map___main___at_lean_parser_module_import__path_has__view_x_27___spec__1(obj*);
obj* l_lean_parser_substring_of__string(obj*);
obj* l___private_209794555__commands__aux___main___lambda__5(obj*);
obj* l_lean_parser_module_yield__command___lambda__6(obj*, obj*, obj*);
extern obj* l_coroutine_yield___rarg___closed__1;
obj* l_char_quote__core(uint32);
obj* l_lean_parser_module_parser___closed__2;
obj* l_lean_parser_module_header_has__view_x_27;
obj* l_lean_parser_module_prelude_parser___closed__1;
obj* l_lean_parser_module_yield__command___lambda__1(obj*, obj*);
obj* l_lean_parser_module_parser___lambda__10___closed__1;
obj* l_lean_parser_module_import__path_parser_lean_parser_has__tokens;
obj* l_lean_parser_module__parser__m_lift__parser__t(obj*);
obj* l_lean_parser_monad__parsec_error___at___private_4089500695__finish__comment__block__aux___main___spec__1___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_raw_view___rarg___lambda__3___closed__1;
obj* l_lean_parser_module__parser__config__coe(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_lean_parser_module__parser__m_monad__coroutine() {
_start:
{
obj* x_0; obj* x_2; obj* x_3; obj* x_5; obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_0 = l_coroutine_monad___closed__1;
lean::inc(x_0);
x_2 = l_lean_parser_parser__core__t_monad___rarg(x_0);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_state__t_lift___rarg), 4, 1);
lean::closure_set(x_3, 0, x_2);
lean::inc(x_0);
x_5 = l_state__t_monad___rarg(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parsec__t_has__monad__lift___rarg), 5, 2);
lean::closure_set(x_6, 0, x_5);
lean::closure_set(x_6, 1, lean::box(0));
lean::inc(x_0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_state__t_lift___rarg), 4, 1);
lean::closure_set(x_8, 0, x_0);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_yield___rarg), 2, 0);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_monad__coroutine__trans___rarg), 3, 2);
lean::closure_set(x_10, 0, x_8);
lean::closure_set(x_10, 1, x_9);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_monad__coroutine__trans___rarg), 3, 2);
lean::closure_set(x_11, 0, x_6);
lean::closure_set(x_11, 1, x_10);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_monad__coroutine__trans___rarg), 3, 2);
lean::closure_set(x_12, 0, x_3);
lean::closure_set(x_12, 1, x_11);
return x_12;
}
}
obj* _init_l_lean_parser_module__parser__m_monad__except() {
_start:
{
obj* x_0; obj* x_2; obj* x_4; obj* x_5; 
x_0 = l_coroutine_monad___closed__1;
lean::inc(x_0);
x_2 = l_lean_parser_parser__core__t_monad___rarg(x_0);
lean::inc(x_0);
x_4 = l_lean_parser_parser__core__t_monad__except___rarg(x_0);
x_5 = l_state__t_monad__except___rarg(x_2, lean::box(0), x_4);
return x_5;
}
}
obj* _init_l_lean_parser_module__parser__m_lean_parser_monad__parsec() {
_start:
{
obj* x_0; obj* x_2; obj* x_4; obj* x_6; obj* x_8; obj* x_9; 
x_0 = l_coroutine_monad___closed__1;
lean::inc(x_0);
x_2 = l_lean_parser_parser__core__t_monad___rarg(x_0);
lean::inc(x_2);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_state__t_lift___rarg), 4, 1);
lean::closure_set(x_4, 0, x_2);
lean::inc(x_2);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_state__t_monad__functor), 6, 5);
lean::closure_set(x_6, 0, lean::box(0));
lean::closure_set(x_6, 1, lean::box(0));
lean::closure_set(x_6, 2, lean::box(0));
lean::closure_set(x_6, 3, x_2);
lean::closure_set(x_6, 4, x_2);
lean::inc(x_0);
x_8 = l_lean_parser_parser__core__t_lean_parser_monad__parsec___rarg(x_0);
x_9 = l_lean_parser_monad__parsec__trans___rarg(x_4, x_6, x_8);
return x_9;
}
}
obj* _init_l_lean_parser_module__parser__m_monad__state() {
_start:
{
obj* x_0; obj* x_2; obj* x_3; 
x_0 = l_coroutine_monad___closed__1;
lean::inc(x_0);
x_2 = l_lean_parser_parser__core__t_monad___rarg(x_0);
x_3 = l_state__t_monad__state___rarg(x_2);
return x_3;
}
}
obj* _init_l_lean_parser_module__parser__m_monad__reader() {
_start:
{
obj* x_0; obj* x_2; obj* x_4; obj* x_5; obj* x_7; obj* x_8; obj* x_9; 
x_0 = l_coroutine_monad___closed__1;
lean::inc(x_0);
x_2 = l_lean_parser_parser__core__t_monad___rarg(x_0);
lean::inc(x_0);
x_4 = l_state__t_monad___rarg(x_0);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_monad__reader___rarg), 1, 0);
lean::inc(x_0);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_state__t_lift___rarg), 4, 3);
lean::closure_set(x_7, 0, x_0);
lean::closure_set(x_7, 1, lean::box(0));
lean::closure_set(x_7, 2, x_5);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parsec__t_has__monad__lift___rarg), 5, 4);
lean::closure_set(x_8, 0, x_4);
lean::closure_set(x_8, 1, lean::box(0));
lean::closure_set(x_8, 2, lean::box(0));
lean::closure_set(x_8, 3, x_7);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_state__t_lift___rarg), 4, 3);
lean::closure_set(x_9, 0, x_2);
lean::closure_set(x_9, 1, lean::box(0));
lean::closure_set(x_9, 2, x_8);
return x_9;
}
}
obj* _init_l_lean_parser_module__parser__m_alternative() {
_start:
{
obj* x_0; obj* x_2; obj* x_4; obj* x_5; 
x_0 = l_coroutine_monad___closed__1;
lean::inc(x_0);
x_2 = l_lean_parser_parser__core__t_monad___rarg(x_0);
lean::inc(x_0);
x_4 = l_lean_parser_parser__core__t_alternative___rarg(x_0);
x_5 = l_state__t_alternative___rarg(x_2, x_4);
return x_5;
}
}
obj* _init_l_lean_parser_module__parser__m_monad() {
_start:
{
obj* x_0; obj* x_2; obj* x_3; 
x_0 = l_coroutine_monad___closed__1;
lean::inc(x_0);
x_2 = l_lean_parser_parser__core__t_monad___rarg(x_0);
x_3 = l_state__t_monad___rarg(x_2);
return x_3;
}
}
obj* _init_l_lean_parser_module__parser__m() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_lean_parser_module__parser() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* l_lean_parser_module__parser__m_lift__parser__t___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_7; obj* x_8; obj* x_10; 
lean::dec(x_1);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__3), 6, 5);
lean::closure_set(x_7, 0, x_0);
lean::closure_set(x_7, 1, x_2);
lean::closure_set(x_7, 2, x_4);
lean::closure_set(x_7, 3, x_5);
lean::closure_set(x_7, 4, x_3);
x_8 = l_lean_parser_module__parser__m_lift__parser__t___rarg___closed__1;
lean::inc(x_8);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_10, 0, x_8);
lean::closure_set(x_10, 1, x_7);
return x_10;
}
}
obj* _init_l_lean_parser_module__parser__m_lift__parser__t___rarg___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__1), 1, 0);
return x_0;
}
}
obj* l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2(obj* x_0, obj* x_1) {
_start:
{
obj* x_3; 
lean::dec(x_1);
x_3 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_3, 0, x_0);
return x_3;
}
}
obj* l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_10; obj* x_12; 
x_6 = lean::apply_1(x_0, x_5);
x_7 = lean::apply_3(x_1, x_6, x_2, x_3);
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_7, 1);
lean::inc(x_10);
if (lean::is_shared(x_7)) {
 lean::dec(x_7);
 x_12 = lean::box(0);
} else {
 lean::cnstr_release(x_7, 0);
 lean::cnstr_release(x_7, 1);
 x_12 = x_7;
}
if (lean::obj_tag(x_8) == 0)
{
obj* x_13; obj* x_15; obj* x_17; obj* x_19; obj* x_20; obj* x_21; obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
x_13 = lean::cnstr_get(x_8, 0);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_8, 1);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_8, 2);
lean::inc(x_17);
if (lean::is_shared(x_8)) {
 lean::dec(x_8);
 x_19 = lean::box(0);
} else {
 lean::cnstr_release(x_8, 0);
 lean::cnstr_release(x_8, 1);
 lean::cnstr_release(x_8, 2);
 x_19 = x_8;
}
if (lean::is_scalar(x_12)) {
 x_20 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_20 = x_12;
}
lean::cnstr_set(x_20, 0, x_13);
lean::cnstr_set(x_20, 1, x_4);
x_21 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_21);
if (lean::is_scalar(x_19)) {
 x_23 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_23 = x_19;
}
lean::cnstr_set(x_23, 0, x_20);
lean::cnstr_set(x_23, 1, x_15);
lean::cnstr_set(x_23, 2, x_21);
x_24 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_17, x_23);
x_25 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_10);
x_26 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_26, 0, x_25);
return x_26;
}
else
{
obj* x_28; uint8 x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; 
lean::dec(x_4);
x_28 = lean::cnstr_get(x_8, 0);
lean::inc(x_28);
x_30 = lean::cnstr_get_scalar<uint8>(x_8, sizeof(void*)*1);
if (lean::is_shared(x_8)) {
 lean::dec(x_8);
 x_31 = lean::box(0);
} else {
 lean::cnstr_release(x_8, 0);
 x_31 = x_8;
}
if (lean::is_scalar(x_31)) {
 x_32 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_32 = x_31;
}
lean::cnstr_set(x_32, 0, x_28);
lean::cnstr_set_scalar(x_32, sizeof(void*)*1, x_30);
x_33 = x_32;
if (lean::is_scalar(x_12)) {
 x_34 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_34 = x_12;
}
lean::cnstr_set(x_34, 0, x_33);
lean::cnstr_set(x_34, 1, x_10);
x_35 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_35, 0, x_34);
return x_35;
}
}
}
obj* l_lean_parser_module__parser__m_lift__parser__t(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg), 6, 0);
return x_2;
}
}
obj* l_lean_parser_module__parser__m_basic__parser__m(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = l_lean_parser_module__parser__m_basic__parser__m___closed__1;
lean::inc(x_4);
return x_4;
}
}
obj* _init_l_lean_parser_module__parser__m_basic__parser__m___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command__parser__config__coe__parser__config), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_coe__b___rarg), 2, 1);
lean::closure_set(x_1, 0, x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__config__coe), 1, 0);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_coe__trans___rarg), 3, 2);
lean::closure_set(x_3, 0, x_2);
lean::closure_set(x_3, 1, x_1);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_coe__t___rarg), 2, 1);
lean::closure_set(x_4, 0, x_3);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg), 6, 1);
lean::closure_set(x_5, 0, x_4);
return x_5;
}
}
obj* l_lean_parser_module_yield__command(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_12; obj* x_13; 
lean::inc(x_1);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_1);
lean::cnstr_set(x_5, 1, x_1);
x_6 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_6);
x_8 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_8, 0, x_5);
lean::cnstr_set(x_8, 1, x_2);
lean::cnstr_set(x_8, 2, x_6);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_3);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_10, 0, x_9);
lean::inc(x_6);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_yield__command___lambda__9), 3, 2);
lean::closure_set(x_12, 0, x_0);
lean::closure_set(x_12, 1, x_6);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_13, 0, x_10);
lean::closure_set(x_13, 1, x_12);
return x_13;
}
}
obj* l_lean_parser_module_yield__command___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
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
x_7 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_0, x_2);
if (lean::is_scalar(x_6)) {
 x_8 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_8 = x_6;
}
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_4);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_9, 0, x_8);
return x_9;
}
}
obj* l_lean_parser_module_yield__command___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_6; obj* x_7; obj* x_9; obj* x_10; obj* x_11; 
lean::dec(x_3);
lean::inc(x_0);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_0);
lean::cnstr_set(x_6, 1, x_1);
x_7 = l_lean_parser_finish__comment__block___closed__2;
lean::inc(x_7);
x_9 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_9, 0, x_6);
lean::cnstr_set(x_9, 1, x_2);
lean::cnstr_set(x_9, 2, x_7);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_0);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_11, 0, x_10);
return x_11;
}
}
obj* l_lean_parser_module_yield__command___lambda__3(obj* x_0, obj* x_1) {
_start:
{
obj* x_3; obj* x_5; 
lean::dec(x_1);
x_3 = l_coroutine_yield___rarg___closed__1;
lean::inc(x_3);
x_5 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_5, 0, x_0);
lean::cnstr_set(x_5, 1, x_3);
return x_5;
}
}
obj* l_lean_parser_module_yield__command___lambda__4(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_1);
lean::cnstr_set(x_2, 1, x_0);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_3, 0, x_2);
return x_3;
}
}
obj* l_lean_parser_module_yield__command___lambda__5(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
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
x_8 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_8, 0, x_3);
lean::cnstr_set(x_8, 1, x_0);
lean::cnstr_set(x_8, 2, x_1);
if (lean::is_scalar(x_7)) {
 x_9 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_9 = x_7;
}
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_5);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_10, 0, x_9);
return x_10;
}
}
obj* l_lean_parser_module_yield__command___lambda__6(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_7; 
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
if (lean::obj_tag(x_3) == 0)
{
obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_8 = lean::cnstr_get(x_3, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_3, 1);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_3, 2);
lean::inc(x_12);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_14 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 1);
 lean::cnstr_release(x_3, 2);
 x_14 = x_3;
}
if (lean::is_scalar(x_7)) {
 x_15 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_15 = x_7;
}
lean::cnstr_set(x_15, 0, x_8);
lean::cnstr_set(x_15, 1, x_0);
if (lean::is_scalar(x_14)) {
 x_16 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_16 = x_14;
}
lean::cnstr_set(x_16, 0, x_15);
lean::cnstr_set(x_16, 1, x_10);
lean::cnstr_set(x_16, 2, x_1);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_5);
x_18 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_18, 0, x_17);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_yield__command___lambda__1), 2, 1);
lean::closure_set(x_19, 0, x_12);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_20, 0, x_18);
lean::closure_set(x_20, 1, x_19);
return x_20;
}
else
{
obj* x_23; uint8 x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
lean::dec(x_1);
lean::dec(x_0);
x_23 = lean::cnstr_get(x_3, 0);
lean::inc(x_23);
x_25 = lean::cnstr_get_scalar<uint8>(x_3, sizeof(void*)*1);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_26 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 x_26 = x_3;
}
if (lean::is_scalar(x_26)) {
 x_27 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_27 = x_26;
}
lean::cnstr_set(x_27, 0, x_23);
lean::cnstr_set_scalar(x_27, sizeof(void*)*1, x_25);
x_28 = x_27;
if (lean::is_scalar(x_7)) {
 x_29 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_29 = x_7;
}
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_5);
x_30 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_30, 0, x_29);
return x_30;
}
}
}
obj* l_lean_parser_module_yield__command___lambda__7(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_6; 
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
if (lean::obj_tag(x_2) == 0)
{
obj* x_7; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_7 = lean::cnstr_get(x_2, 1);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_2, 2);
lean::inc(x_9);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_11 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 lean::cnstr_release(x_2, 1);
 lean::cnstr_release(x_2, 2);
 x_11 = x_2;
}
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_yield__command___lambda__1), 2, 1);
lean::closure_set(x_12, 0, x_9);
x_13 = l_lean_parser_module_yield__command___lambda__7___closed__1;
lean::inc(x_13);
if (lean::is_scalar(x_11)) {
 x_15 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_15 = x_11;
}
lean::cnstr_set(x_15, 0, x_13);
lean::cnstr_set(x_15, 1, x_7);
lean::cnstr_set(x_15, 2, x_0);
if (lean::is_scalar(x_6)) {
 x_16 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_16 = x_6;
}
lean::cnstr_set(x_16, 0, x_15);
lean::cnstr_set(x_16, 1, x_4);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_17, 0, x_16);
x_18 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_18, 0, x_17);
lean::closure_set(x_18, 1, x_12);
return x_18;
}
else
{
obj* x_20; uint8 x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; 
lean::dec(x_0);
x_20 = lean::cnstr_get(x_2, 0);
lean::inc(x_20);
x_22 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*1);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_23 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 x_23 = x_2;
}
if (lean::is_scalar(x_23)) {
 x_24 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_24 = x_23;
}
lean::cnstr_set(x_24, 0, x_20);
lean::cnstr_set_scalar(x_24, sizeof(void*)*1, x_22);
x_25 = x_24;
if (lean::is_scalar(x_6)) {
 x_26 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_26 = x_6;
}
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_4);
x_27 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_27, 0, x_26);
return x_27;
}
}
}
obj* _init_l_lean_parser_module_yield__command___lambda__7___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; 
x_0 = lean::box(0);
x_1 = l_lean_message__log_empty;
lean::inc(x_1);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_1);
return x_3;
}
}
obj* l_lean_parser_module_yield__command___lambda__8(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_6; obj* x_8; 
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
if (lean::obj_tag(x_4) == 0)
{
obj* x_10; obj* x_12; obj* x_14; obj* x_17; obj* x_19; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_28; obj* x_29; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; 
lean::dec(x_8);
x_10 = lean::cnstr_get(x_4, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_4, 1);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_4, 2);
lean::inc(x_14);
lean::dec(x_4);
x_17 = lean::cnstr_get(x_10, 0);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_10, 1);
lean::inc(x_19);
lean::dec(x_10);
x_22 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_yield__command___lambda__1), 2, 1);
lean::closure_set(x_22, 0, x_14);
x_23 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_23, 0, x_0);
lean::cnstr_set(x_23, 1, x_1);
lean::cnstr_set(x_23, 2, x_17);
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_yield__command___lambda__3), 2, 1);
lean::closure_set(x_24, 0, x_23);
x_25 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_yield__command___lambda__4), 2, 1);
lean::closure_set(x_25, 0, x_6);
x_26 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_26, 0, x_24);
lean::closure_set(x_26, 1, x_25);
lean::inc(x_2);
x_28 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_yield__command___lambda__5), 3, 2);
lean::closure_set(x_28, 0, x_12);
lean::closure_set(x_28, 1, x_2);
x_29 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_29, 0, x_26);
lean::closure_set(x_29, 1, x_28);
lean::inc(x_2);
x_31 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_yield__command___lambda__6), 3, 2);
lean::closure_set(x_31, 0, x_19);
lean::closure_set(x_31, 1, x_2);
x_32 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_32, 0, x_29);
lean::closure_set(x_32, 1, x_31);
x_33 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_yield__command___lambda__7), 2, 1);
lean::closure_set(x_33, 0, x_2);
x_34 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_34, 0, x_32);
lean::closure_set(x_34, 1, x_33);
x_35 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_35, 0, x_34);
lean::closure_set(x_35, 1, x_22);
return x_35;
}
else
{
obj* x_39; uint8 x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_39 = lean::cnstr_get(x_4, 0);
lean::inc(x_39);
x_41 = lean::cnstr_get_scalar<uint8>(x_4, sizeof(void*)*1);
if (lean::is_shared(x_4)) {
 lean::dec(x_4);
 x_42 = lean::box(0);
} else {
 lean::cnstr_release(x_4, 0);
 x_42 = x_4;
}
if (lean::is_scalar(x_42)) {
 x_43 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_43 = x_42;
}
lean::cnstr_set(x_43, 0, x_39);
lean::cnstr_set_scalar(x_43, sizeof(void*)*1, x_41);
x_44 = x_43;
if (lean::is_scalar(x_8)) {
 x_45 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_45 = x_8;
}
lean::cnstr_set(x_45, 0, x_44);
lean::cnstr_set(x_45, 1, x_6);
x_46 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_46, 0, x_45);
return x_46;
}
}
}
obj* l_lean_parser_module_yield__command___lambda__9(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_7; 
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
if (lean::obj_tag(x_3) == 0)
{
obj* x_9; obj* x_11; obj* x_13; obj* x_16; obj* x_18; obj* x_21; obj* x_22; obj* x_23; obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
lean::dec(x_7);
x_9 = lean::cnstr_get(x_3, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_3, 1);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_3, 2);
lean::inc(x_13);
lean::dec(x_3);
x_16 = lean::cnstr_get(x_9, 0);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_9, 1);
lean::inc(x_18);
lean::dec(x_9);
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_yield__command___lambda__1), 2, 1);
lean::closure_set(x_21, 0, x_13);
x_22 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_yield__command___lambda__2), 4, 3);
lean::closure_set(x_22, 0, x_5);
lean::closure_set(x_22, 1, x_18);
lean::closure_set(x_22, 2, x_11);
x_23 = l_lean_parser_module__parser__m_lift__parser__t___rarg___closed__1;
lean::inc(x_23);
x_25 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_25, 0, x_23);
lean::closure_set(x_25, 1, x_22);
x_26 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_yield__command___lambda__8), 4, 3);
lean::closure_set(x_26, 0, x_0);
lean::closure_set(x_26, 1, x_16);
lean::closure_set(x_26, 2, x_1);
x_27 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_27, 0, x_25);
lean::closure_set(x_27, 1, x_26);
x_28 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_28, 0, x_27);
lean::closure_set(x_28, 1, x_21);
return x_28;
}
else
{
obj* x_31; uint8 x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
lean::dec(x_1);
lean::dec(x_0);
x_31 = lean::cnstr_get(x_3, 0);
lean::inc(x_31);
x_33 = lean::cnstr_get_scalar<uint8>(x_3, sizeof(void*)*1);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_34 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 x_34 = x_3;
}
if (lean::is_scalar(x_34)) {
 x_35 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_35 = x_34;
}
lean::cnstr_set(x_35, 0, x_31);
lean::cnstr_set_scalar(x_35, sizeof(void*)*1, x_33);
x_36 = x_35;
if (lean::is_scalar(x_7)) {
 x_37 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_37 = x_7;
}
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_5);
x_38 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_38, 0, x_37);
return x_38;
}
}
}
obj* _init_l_lean_parser_module_prelude() {
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
x_7 = lean::mk_string("prelude");
x_8 = lean::name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_lean_parser_module_prelude_has__view_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_string__lit_has__view_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_prelude_has__view_x_27___lambda__1), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* l_lean_parser_module_prelude_has__view_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_10; 
x_1 = l_lean_parser_raw_view___rarg___lambda__3___closed__1;
lean::inc(x_1);
x_3 = l_option_map___rarg(x_1, x_0);
x_4 = lean::box(3);
x_5 = l_option_get__or__else___main___rarg(x_3, x_4);
x_6 = lean::box(0);
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_6);
x_8 = l_lean_parser_module_prelude;
lean::inc(x_8);
x_10 = l_lean_parser_syntax_mk__node(x_8, x_7);
return x_10;
}
}
obj* _init_l_lean_parser_module_prelude_has__view() {
_start:
{
obj* x_0; 
x_0 = l_lean_parser_module_prelude_has__view_x_27;
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_lean_parser_module_prelude_parser_lean_parser_has__tokens() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_0 = lean::mk_string("prelude");
x_1 = lean::mk_nat_obj(0u);
x_2 = l_lean_parser_symbol_tokens___rarg(x_0, x_1);
x_3 = lean::box(0);
x_4 = l_lean_parser_list_cons_tokens___rarg(x_2, x_3);
x_5 = l_lean_parser_tokens___rarg(x_4);
return x_5;
}
}
obj* _init_l_lean_parser_module_prelude_parser_lean_parser_has__view() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_20; 
x_0 = lean::mk_string("prelude");
x_1 = l_string_trim(x_0);
lean::inc(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_3, 0, x_1);
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_unicode__symbol_lean_parser_has__view___spec__1), 6, 3);
lean::closure_set(x_5, 0, x_1);
lean::closure_set(x_5, 1, x_4);
lean::closure_set(x_5, 2, x_3);
x_6 = lean::box(0);
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_6);
x_8 = l_lean_parser_basic__parser__m_monad;
x_9 = l_lean_parser_basic__parser__m_monad__except;
x_10 = l_lean_parser_basic__parser__m_lean_parser_monad__parsec;
x_11 = l_lean_parser_basic__parser__m_alternative;
x_12 = l_lean_parser_module_prelude;
x_13 = l_lean_parser_module_prelude_has__view;
lean::inc(x_13);
lean::inc(x_12);
lean::inc(x_11);
lean::inc(x_10);
lean::inc(x_9);
lean::inc(x_8);
x_20 = l_lean_parser_combinators_node_view___rarg(x_8, x_9, x_10, x_11, x_12, x_7, x_13);
return x_20;
}
}
obj* l_lean_parser_module_prelude_parser(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_7; 
x_3 = l_lean_parser_module_prelude;
x_4 = l_lean_parser_module_prelude_parser___closed__1;
lean::inc(x_4);
lean::inc(x_3);
x_7 = l_lean_parser_combinators_node___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__8(x_3, x_4, x_0, x_1, x_2);
return x_7;
}
}
obj* _init_l_lean_parser_module_prelude_parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_0 = lean::mk_string("prelude");
x_1 = l_string_trim(x_0);
lean::inc(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_3, 0, x_1);
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_unicode__symbol_lean_parser_has__view___spec__1), 6, 3);
lean::closure_set(x_5, 0, x_1);
lean::closure_set(x_5, 1, x_4);
lean::closure_set(x_5, 2, x_3);
x_6 = lean::box(0);
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_6);
return x_7;
}
}
obj* _init_l_lean_parser_module_import__path() {
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
x_7 = lean::mk_string("import_path");
x_8 = lean::name_mk_string(x_6, x_7);
return x_8;
}
}
obj* l_list_map___main___at_lean_parser_module_import__path_has__view_x_27___spec__1(obj* x_0) {
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
obj* x_3; obj* x_5; obj* x_7; obj* x_8; 
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
x_8 = l_list_map___main___at_lean_parser_module_import__path_has__view_x_27___spec__1(x_5);
switch (lean::obj_tag(x_3)) {
case 0:
{
obj* x_9; obj* x_12; obj* x_13; 
x_9 = lean::cnstr_get(x_3, 0);
lean::inc(x_9);
lean::dec(x_3);
x_12 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_12, 0, x_9);
if (lean::is_scalar(x_7)) {
 x_13 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_13 = x_7;
}
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_8);
return x_13;
}
case 1:
{
obj* x_15; obj* x_16; 
lean::dec(x_3);
x_15 = lean::box(0);
if (lean::is_scalar(x_7)) {
 x_16 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_16 = x_7;
}
lean::cnstr_set(x_16, 0, x_15);
lean::cnstr_set(x_16, 1, x_8);
return x_16;
}
case 2:
{
obj* x_18; obj* x_19; 
lean::dec(x_3);
x_18 = lean::box(0);
if (lean::is_scalar(x_7)) {
 x_19 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_19 = x_7;
}
lean::cnstr_set(x_19, 0, x_18);
lean::cnstr_set(x_19, 1, x_8);
return x_19;
}
default:
{
obj* x_21; obj* x_22; 
lean::dec(x_3);
x_21 = lean::box(0);
if (lean::is_scalar(x_7)) {
 x_22 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_22 = x_7;
}
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_8);
return x_22;
}
}
}
}
}
obj* l_list_map___main___at_lean_parser_module_import__path_has__view_x_27___spec__2(obj* x_0) {
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
obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
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
x_8 = l_lean_parser_raw_view___rarg___lambda__3___closed__1;
lean::inc(x_8);
x_10 = l_option_map___rarg(x_8, x_3);
x_11 = lean::box(3);
x_12 = l_option_get__or__else___main___rarg(x_10, x_11);
x_13 = l_list_map___main___at_lean_parser_module_import__path_has__view_x_27___spec__2(x_5);
if (lean::is_scalar(x_7)) {
 x_14 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_14 = x_7;
}
lean::cnstr_set(x_14, 0, x_12);
lean::cnstr_set(x_14, 1, x_13);
return x_14;
}
}
}
obj* _init_l_lean_parser_module_import__path_has__view_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_import__path_has__view_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_import__path_has__view_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* l_lean_parser_module_import__path_has__view_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_4 = l_lean_parser_syntax_as__node___main(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; 
lean::dec(x_4);
x_6 = l_lean_parser_module_import__path_has__view_x_27___lambda__1___closed__4;
lean::inc(x_6);
return x_6;
}
else
{
obj* x_8; obj* x_11; 
x_8 = lean::cnstr_get(x_4, 0);
lean::inc(x_8);
lean::dec(x_4);
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
lean::dec(x_8);
if (lean::obj_tag(x_11) == 0)
{
obj* x_14; 
x_14 = lean::box(3);
x_1 = x_11;
x_2 = x_14;
goto lbl_3;
}
else
{
obj* x_15; obj* x_17; 
x_15 = lean::cnstr_get(x_11, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_11, 1);
lean::inc(x_17);
lean::dec(x_11);
x_1 = x_17;
x_2 = x_15;
goto lbl_3;
}
}
lbl_3:
{
obj* x_20; 
x_20 = l_lean_parser_syntax_as__node___main(x_2);
if (lean::obj_tag(x_20) == 0)
{
lean::dec(x_20);
if (lean::obj_tag(x_1) == 0)
{
obj* x_23; 
lean::dec(x_1);
x_23 = l_lean_parser_module_import__path_has__view_x_27___lambda__1___closed__2;
lean::inc(x_23);
return x_23;
}
else
{
obj* x_25; 
x_25 = lean::cnstr_get(x_1, 0);
lean::inc(x_25);
lean::dec(x_1);
switch (lean::obj_tag(x_25)) {
case 0:
{
obj* x_29; 
lean::dec(x_25);
x_29 = l_lean_parser_module_import__path_has__view_x_27___lambda__1___closed__2;
lean::inc(x_29);
return x_29;
}
case 1:
{
obj* x_31; obj* x_34; obj* x_36; 
x_31 = lean::cnstr_get(x_25, 0);
lean::inc(x_31);
lean::dec(x_25);
x_34 = l_lean_parser_module_import__path_has__view_x_27___lambda__1___closed__3;
lean::inc(x_34);
x_36 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_36, 0, x_34);
lean::cnstr_set(x_36, 1, x_31);
return x_36;
}
case 2:
{
obj* x_38; 
lean::dec(x_25);
x_38 = l_lean_parser_module_import__path_has__view_x_27___lambda__1___closed__2;
lean::inc(x_38);
return x_38;
}
default:
{
obj* x_41; 
lean::dec(x_25);
x_41 = l_lean_parser_module_import__path_has__view_x_27___lambda__1___closed__2;
lean::inc(x_41);
return x_41;
}
}
}
}
else
{
obj* x_43; obj* x_46; obj* x_49; 
x_43 = lean::cnstr_get(x_20, 0);
lean::inc(x_43);
lean::dec(x_20);
x_46 = lean::cnstr_get(x_43, 1);
lean::inc(x_46);
lean::dec(x_43);
x_49 = l_list_map___main___at_lean_parser_module_import__path_has__view_x_27___spec__1(x_46);
if (lean::obj_tag(x_1) == 0)
{
obj* x_51; obj* x_53; 
lean::dec(x_1);
x_51 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_51);
x_53 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_53, 0, x_49);
lean::cnstr_set(x_53, 1, x_51);
return x_53;
}
else
{
obj* x_54; 
x_54 = lean::cnstr_get(x_1, 0);
lean::inc(x_54);
lean::dec(x_1);
switch (lean::obj_tag(x_54)) {
case 0:
{
obj* x_58; obj* x_60; 
lean::dec(x_54);
x_58 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_58);
x_60 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_60, 0, x_49);
lean::cnstr_set(x_60, 1, x_58);
return x_60;
}
case 1:
{
obj* x_61; obj* x_64; 
x_61 = lean::cnstr_get(x_54, 0);
lean::inc(x_61);
lean::dec(x_54);
x_64 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_64, 0, x_49);
lean::cnstr_set(x_64, 1, x_61);
return x_64;
}
case 2:
{
obj* x_66; obj* x_68; 
lean::dec(x_54);
x_66 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_66);
x_68 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_68, 0, x_49);
lean::cnstr_set(x_68, 1, x_66);
return x_68;
}
default:
{
obj* x_70; obj* x_72; 
lean::dec(x_54);
x_70 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_70);
x_72 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_72, 0, x_49);
lean::cnstr_set(x_72, 1, x_70);
return x_72;
}
}
}
}
}
}
}
obj* _init_l_lean_parser_module_import__path_has__view_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_3; obj* x_4; obj* x_6; obj* x_8; obj* x_11; obj* x_12; 
x_0 = lean::box(0);
lean::inc(x_0);
lean::inc(x_0);
x_3 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_0);
x_4 = lean::mk_string("NOT_AN_IDENT");
lean::inc(x_4);
x_6 = l_lean_parser_substring_of__string(x_4);
lean::inc(x_0);
x_8 = lean::name_mk_string(x_0, x_4);
lean::inc(x_0);
lean::inc(x_0);
x_11 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_11, 0, x_0);
lean::cnstr_set(x_11, 1, x_6);
lean::cnstr_set(x_11, 2, x_8);
lean::cnstr_set(x_11, 3, x_0);
lean::cnstr_set(x_11, 4, x_0);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_3);
lean::cnstr_set(x_12, 1, x_11);
return x_12;
}
}
obj* _init_l_lean_parser_module_import__path_has__view_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; 
x_0 = l_lean_parser_module_import__path_has__view_x_27___lambda__1___closed__1;
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_lean_parser_module_import__path_has__view_x_27___lambda__1___closed__3() {
_start:
{
obj* x_0; obj* x_2; 
x_0 = lean::box(0);
lean::inc(x_0);
x_2 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_0);
return x_2;
}
}
obj* _init_l_lean_parser_module_import__path_has__view_x_27___lambda__1___closed__4() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; 
x_3 = lean::box(0);
x_4 = lean::box(3);
x_0 = x_3;
x_1 = x_4;
goto lbl_2;
lbl_2:
{
obj* x_5; 
x_5 = l_lean_parser_syntax_as__node___main(x_1);
if (lean::obj_tag(x_5) == 0)
{
lean::dec(x_5);
if (lean::obj_tag(x_0) == 0)
{
obj* x_8; 
lean::dec(x_0);
x_8 = l_lean_parser_module_import__path_has__view_x_27___lambda__1___closed__2;
lean::inc(x_8);
return x_8;
}
else
{
obj* x_10; 
x_10 = lean::cnstr_get(x_0, 0);
lean::inc(x_10);
lean::dec(x_0);
switch (lean::obj_tag(x_10)) {
case 0:
{
obj* x_14; 
lean::dec(x_10);
x_14 = l_lean_parser_module_import__path_has__view_x_27___lambda__1___closed__2;
lean::inc(x_14);
return x_14;
}
case 1:
{
obj* x_16; obj* x_19; obj* x_21; 
x_16 = lean::cnstr_get(x_10, 0);
lean::inc(x_16);
lean::dec(x_10);
x_19 = l_lean_parser_module_import__path_has__view_x_27___lambda__1___closed__3;
lean::inc(x_19);
x_21 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_21, 0, x_19);
lean::cnstr_set(x_21, 1, x_16);
return x_21;
}
case 2:
{
obj* x_23; 
lean::dec(x_10);
x_23 = l_lean_parser_module_import__path_has__view_x_27___lambda__1___closed__2;
lean::inc(x_23);
return x_23;
}
default:
{
obj* x_26; 
lean::dec(x_10);
x_26 = l_lean_parser_module_import__path_has__view_x_27___lambda__1___closed__2;
lean::inc(x_26);
return x_26;
}
}
}
}
else
{
obj* x_28; obj* x_31; obj* x_34; 
x_28 = lean::cnstr_get(x_5, 0);
lean::inc(x_28);
lean::dec(x_5);
x_31 = lean::cnstr_get(x_28, 1);
lean::inc(x_31);
lean::dec(x_28);
x_34 = l_list_map___main___at_lean_parser_module_import__path_has__view_x_27___spec__1(x_31);
if (lean::obj_tag(x_0) == 0)
{
obj* x_36; obj* x_38; 
lean::dec(x_0);
x_36 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_36);
x_38 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_38, 0, x_34);
lean::cnstr_set(x_38, 1, x_36);
return x_38;
}
else
{
obj* x_39; 
x_39 = lean::cnstr_get(x_0, 0);
lean::inc(x_39);
lean::dec(x_0);
switch (lean::obj_tag(x_39)) {
case 0:
{
obj* x_43; obj* x_45; 
lean::dec(x_39);
x_43 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_43);
x_45 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_45, 0, x_34);
lean::cnstr_set(x_45, 1, x_43);
return x_45;
}
case 1:
{
obj* x_46; obj* x_49; 
x_46 = lean::cnstr_get(x_39, 0);
lean::inc(x_46);
lean::dec(x_39);
x_49 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_49, 0, x_34);
lean::cnstr_set(x_49, 1, x_46);
return x_49;
}
case 2:
{
obj* x_51; obj* x_53; 
lean::dec(x_39);
x_51 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_51);
x_53 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_53, 0, x_34);
lean::cnstr_set(x_53, 1, x_51);
return x_53;
}
default:
{
obj* x_55; obj* x_57; 
lean::dec(x_39);
x_55 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_55);
x_57 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_57, 0, x_34);
lean::cnstr_set(x_57, 1, x_55);
return x_57;
}
}
}
}
}
}
}
obj* l_lean_parser_module_import__path_has__view_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_6; obj* x_7; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_16; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
x_6 = l_list_map___main___at_lean_parser_module_import__path_has__view_x_27___spec__2(x_1);
x_7 = l_lean_parser_no__kind;
lean::inc(x_7);
x_9 = l_lean_parser_syntax_mk__node(x_7, x_6);
x_10 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_10, 0, x_3);
x_11 = lean::box(0);
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_10);
lean::cnstr_set(x_12, 1, x_11);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_9);
lean::cnstr_set(x_13, 1, x_12);
x_14 = l_lean_parser_module_import__path;
lean::inc(x_14);
x_16 = l_lean_parser_syntax_mk__node(x_14, x_13);
return x_16;
}
}
obj* _init_l_lean_parser_module_import__path_has__view() {
_start:
{
obj* x_0; 
x_0 = l_lean_parser_module_import__path_has__view_x_27;
lean::inc(x_0);
return x_0;
}
}
obj* l_lean_parser_combinators_many___at_lean_parser_module_import__path_parser_lean_parser_has__tokens___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; obj* x_6; obj* x_8; obj* x_10; 
lean::inc(x_2);
x_5 = l_lean_parser_combinators_many1___at_lean_parser_ident__univ__spec_parser_lean_parser_has__view___spec__1(x_0, x_1, x_2, x_3);
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
if (lean::is_shared(x_5)) {
 lean::dec(x_5);
 x_10 = lean::box(0);
} else {
 lean::cnstr_release(x_5, 0);
 lean::cnstr_release(x_5, 1);
 x_10 = x_5;
}
if (lean::obj_tag(x_6) == 0)
{
obj* x_12; 
lean::dec(x_2);
if (lean::is_scalar(x_10)) {
 x_12 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_12 = x_10;
}
lean::cnstr_set(x_12, 0, x_6);
lean::cnstr_set(x_12, 1, x_8);
return x_12;
}
else
{
obj* x_13; uint8 x_15; 
x_13 = lean::cnstr_get(x_6, 0);
lean::inc(x_13);
x_15 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*1);
if (x_15 == 0)
{
obj* x_17; obj* x_20; obj* x_22; obj* x_23; obj* x_24; obj* x_26; obj* x_27; 
lean::dec(x_6);
x_17 = lean::cnstr_get(x_13, 2);
lean::inc(x_17);
lean::dec(x_13);
x_20 = l_mjoin___rarg___closed__1;
lean::inc(x_20);
x_22 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_22, 0, x_17);
lean::closure_set(x_22, 1, x_20);
x_23 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_23, 0, x_22);
x_24 = l_lean_parser_combinators_many___rarg___closed__1;
lean::inc(x_24);
x_26 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_26, 0, x_24);
lean::cnstr_set(x_26, 1, x_2);
lean::cnstr_set(x_26, 2, x_23);
if (lean::is_scalar(x_10)) {
 x_27 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_27 = x_10;
}
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_8);
return x_27;
}
else
{
obj* x_30; 
lean::dec(x_13);
lean::dec(x_2);
if (lean::is_scalar(x_10)) {
 x_30 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_30 = x_10;
}
lean::cnstr_set(x_30, 0, x_6);
lean::cnstr_set(x_30, 1, x_8);
return x_30;
}
}
}
}
obj* l_lean_parser_ident_parser___at_lean_parser_module_import__path_parser_lean_parser_has__tokens___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_5; obj* x_6; obj* x_8; obj* x_10; 
lean::inc(x_1);
lean::inc(x_0);
x_5 = l_lean_parser_token(x_0, x_1, x_2);
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
if (lean::is_shared(x_5)) {
 lean::dec(x_5);
 x_10 = lean::box(0);
} else {
 lean::cnstr_release(x_5, 0);
 lean::cnstr_release(x_5, 1);
 x_10 = x_5;
}
if (lean::obj_tag(x_6) == 0)
{
obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_18; 
x_11 = lean::cnstr_get(x_6, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_6, 1);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_6, 2);
lean::inc(x_15);
if (lean::is_shared(x_6)) {
 lean::dec(x_6);
 x_17 = lean::box(0);
} else {
 lean::cnstr_release(x_6, 0);
 lean::cnstr_release(x_6, 1);
 lean::cnstr_release(x_6, 2);
 x_17 = x_6;
}
switch (lean::obj_tag(x_11)) {
case 0:
{
obj* x_22; 
lean::dec(x_17);
lean::dec(x_11);
x_22 = lean::box(0);
x_18 = x_22;
goto lbl_19;
}
case 1:
{
obj* x_26; obj* x_28; obj* x_29; obj* x_31; obj* x_32; obj* x_34; obj* x_35; obj* x_36; 
lean::dec(x_1);
lean::dec(x_10);
lean::dec(x_0);
x_26 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_26);
if (lean::is_scalar(x_17)) {
 x_28 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_28 = x_17;
}
lean::cnstr_set(x_28, 0, x_11);
lean::cnstr_set(x_28, 1, x_13);
lean::cnstr_set(x_28, 2, x_26);
x_29 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_28);
lean::inc(x_26);
x_31 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_26, x_29);
x_32 = l_lean_parser_ident_parser___at_lean_parser_command_notation__spec_fold__action_parser_lean_parser_has__view___spec__4___rarg___closed__1;
lean::inc(x_32);
x_34 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_31, x_32);
x_35 = l_lean_parser_parsec__t_try__mk__res___rarg(x_34);
x_36 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_36, 0, x_35);
lean::cnstr_set(x_36, 1, x_8);
return x_36;
}
case 2:
{
obj* x_39; 
lean::dec(x_17);
lean::dec(x_11);
x_39 = lean::box(0);
x_18 = x_39;
goto lbl_19;
}
default:
{
obj* x_42; 
lean::dec(x_17);
lean::dec(x_11);
x_42 = lean::box(0);
x_18 = x_42;
goto lbl_19;
}
}
lbl_19:
{
obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_50; obj* x_51; obj* x_53; obj* x_56; obj* x_57; obj* x_59; obj* x_61; obj* x_62; obj* x_63; 
lean::dec(x_18);
x_44 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_44, 0, x_1);
x_45 = lean::box(0);
x_46 = l_string_join___closed__1;
x_47 = l_lean_parser_ident_parser___at_lean_parser_command_notation__spec_fold__action_parser_lean_parser_has__view___spec__4___rarg___closed__1;
lean::inc(x_47);
lean::inc(x_46);
x_50 = l_lean_parser_monad__parsec_error___at___private_4089500695__finish__comment__block__aux___main___spec__1___rarg(x_46, x_47, x_44, x_45, x_0, x_13, x_8);
x_51 = lean::cnstr_get(x_50, 0);
lean::inc(x_51);
x_53 = lean::cnstr_get(x_50, 1);
lean::inc(x_53);
lean::dec(x_50);
x_56 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_51);
x_57 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_57);
x_59 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_57, x_56);
lean::inc(x_47);
x_61 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_59, x_47);
x_62 = l_lean_parser_parsec__t_try__mk__res___rarg(x_61);
if (lean::is_scalar(x_10)) {
 x_63 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_63 = x_10;
}
lean::cnstr_set(x_63, 0, x_62);
lean::cnstr_set(x_63, 1, x_53);
return x_63;
}
}
else
{
obj* x_66; uint8 x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_74; obj* x_75; obj* x_77; obj* x_78; obj* x_79; 
lean::dec(x_1);
lean::dec(x_0);
x_66 = lean::cnstr_get(x_6, 0);
lean::inc(x_66);
x_68 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*1);
if (lean::is_shared(x_6)) {
 lean::dec(x_6);
 x_69 = lean::box(0);
} else {
 lean::cnstr_release(x_6, 0);
 x_69 = x_6;
}
if (lean::is_scalar(x_69)) {
 x_70 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_70 = x_69;
}
lean::cnstr_set(x_70, 0, x_66);
lean::cnstr_set_scalar(x_70, sizeof(void*)*1, x_68);
x_71 = x_70;
x_72 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_72);
x_74 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_72, x_71);
x_75 = l_lean_parser_ident_parser___at_lean_parser_command_notation__spec_fold__action_parser_lean_parser_has__view___spec__4___rarg___closed__1;
lean::inc(x_75);
x_77 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_74, x_75);
x_78 = l_lean_parser_parsec__t_try__mk__res___rarg(x_77);
if (lean::is_scalar(x_10)) {
 x_79 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_79 = x_10;
}
lean::cnstr_set(x_79, 0, x_78);
lean::cnstr_set(x_79, 1, x_8);
return x_79;
}
}
}
obj* _init_l_lean_parser_module_import__path_parser_lean_parser_has__tokens() {
_start:
{
obj* x_0; obj* x_2; obj* x_4; obj* x_5; obj* x_6; 
x_0 = lean::box(0);
lean::inc(x_0);
x_2 = l_lean_parser_tokens___rarg(x_0);
lean::inc(x_0);
x_4 = l_lean_parser_list_cons_tokens___rarg(x_0, x_0);
x_5 = l_lean_parser_list_cons_tokens___rarg(x_2, x_4);
x_6 = l_lean_parser_tokens___rarg(x_5);
return x_6;
}
}
obj* _init_l_lean_parser_module_import__path_parser_lean_parser_has__view() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_24; 
x_0 = lean::mk_string(".");
x_1 = l_string_quote(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_2, 0, x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_with__trailing___rarg___lambda__1), 2, 0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_lift___at_lean_parser_with__trailing___spec__1___rarg), 4, 1);
lean::closure_set(x_4, 0, x_3);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_import__path_parser_lean_parser_has__view___lambda__1), 5, 1);
lean::closure_set(x_5, 0, x_2);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_bind___at_lean_parser_with__trailing___spec__2___rarg), 5, 2);
lean::closure_set(x_6, 0, x_4);
lean::closure_set(x_6, 1, x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_many___at_lean_parser_module_import__path_parser_lean_parser_has__tokens___spec__1), 4, 1);
lean::closure_set(x_7, 0, x_6);
x_8 = lean::box(0);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_ident_parser___at_lean_parser_module_import__path_parser_lean_parser_has__tokens___spec__2), 3, 0);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_8);
x_11 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_11, 0, x_7);
lean::cnstr_set(x_11, 1, x_10);
x_12 = l_lean_parser_basic__parser__m_monad;
x_13 = l_lean_parser_basic__parser__m_monad__except;
x_14 = l_lean_parser_basic__parser__m_lean_parser_monad__parsec;
x_15 = l_lean_parser_basic__parser__m_alternative;
x_16 = l_lean_parser_module_import__path;
x_17 = l_lean_parser_module_import__path_has__view;
lean::inc(x_17);
lean::inc(x_16);
lean::inc(x_15);
lean::inc(x_14);
lean::inc(x_13);
lean::inc(x_12);
x_24 = l_lean_parser_combinators_node_view___rarg(x_12, x_13, x_14, x_15, x_16, x_11, x_17);
return x_24;
}
}
obj* l_lean_parser_module_import__path_parser_lean_parser_has__view___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_7; obj* x_8; obj* x_10; obj* x_12; 
x_5 = l_lean_name_to__string___closed__1;
lean::inc(x_5);
x_7 = l_lean_parser_monad__parsec_str__core___at___private_4089500695__finish__comment__block__aux___main___spec__3(x_5, x_0, x_2, x_3, x_4);
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_7, 1);
lean::inc(x_10);
if (lean::is_shared(x_7)) {
 lean::dec(x_7);
 x_12 = lean::box(0);
} else {
 lean::cnstr_release(x_7, 0);
 lean::cnstr_release(x_7, 1);
 x_12 = x_7;
}
if (lean::obj_tag(x_8) == 0)
{
obj* x_13; obj* x_15; obj* x_17; obj* x_19; obj* x_20; obj* x_22; obj* x_23; obj* x_24; 
x_13 = lean::cnstr_get(x_8, 1);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_8, 2);
lean::inc(x_15);
if (lean::is_shared(x_8)) {
 lean::dec(x_8);
 x_17 = lean::box(0);
} else {
 lean::cnstr_release(x_8, 0);
 lean::cnstr_release(x_8, 1);
 lean::cnstr_release(x_8, 2);
 x_17 = x_8;
}
lean::inc(x_13);
x_19 = l_lean_parser_mk__raw__res(x_1, x_13);
x_20 = l_lean_parser_finish__comment__block___closed__2;
lean::inc(x_20);
if (lean::is_scalar(x_17)) {
 x_22 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_22 = x_17;
}
lean::cnstr_set(x_22, 0, x_19);
lean::cnstr_set(x_22, 1, x_13);
lean::cnstr_set(x_22, 2, x_20);
x_23 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_22);
if (lean::is_scalar(x_12)) {
 x_24 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_24 = x_12;
}
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_10);
return x_24;
}
else
{
obj* x_26; uint8 x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; 
lean::dec(x_1);
x_26 = lean::cnstr_get(x_8, 0);
lean::inc(x_26);
x_28 = lean::cnstr_get_scalar<uint8>(x_8, sizeof(void*)*1);
if (lean::is_shared(x_8)) {
 lean::dec(x_8);
 x_29 = lean::box(0);
} else {
 lean::cnstr_release(x_8, 0);
 x_29 = x_8;
}
if (lean::is_scalar(x_29)) {
 x_30 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_30 = x_29;
}
lean::cnstr_set(x_30, 0, x_26);
lean::cnstr_set_scalar(x_30, sizeof(void*)*1, x_28);
x_31 = x_30;
if (lean::is_scalar(x_12)) {
 x_32 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_32 = x_12;
}
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_10);
return x_32;
}
}
}
obj* l_lean_parser_module_import__path_parser(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_7; 
x_3 = l_lean_parser_module_import__path;
x_4 = l_lean_parser_module_import__path_parser___closed__1;
lean::inc(x_4);
lean::inc(x_3);
x_7 = l_lean_parser_combinators_node___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__8(x_3, x_4, x_0, x_1, x_2);
return x_7;
}
}
obj* _init_l_lean_parser_module_import__path_parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_0 = lean::mk_string(".");
x_1 = l_string_quote(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_2, 0, x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_with__trailing___rarg___lambda__1), 2, 0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_lift___at_lean_parser_with__trailing___spec__1___rarg), 4, 1);
lean::closure_set(x_4, 0, x_3);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_import__path_parser_lean_parser_has__view___lambda__1), 5, 1);
lean::closure_set(x_5, 0, x_2);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_bind___at_lean_parser_with__trailing___spec__2___rarg), 5, 2);
lean::closure_set(x_6, 0, x_4);
lean::closure_set(x_6, 1, x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_many___at_lean_parser_module_import__path_parser_lean_parser_has__tokens___spec__1), 4, 1);
lean::closure_set(x_7, 0, x_6);
x_8 = lean::box(0);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_ident_parser___at_lean_parser_module_import__path_parser_lean_parser_has__tokens___spec__2), 3, 0);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_8);
x_11 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_11, 0, x_7);
lean::cnstr_set(x_11, 1, x_10);
return x_11;
}
}
obj* _init_l_lean_parser_module_import() {
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
x_7 = lean::mk_string("import");
x_8 = lean::name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_lean_parser_module_import_has__view_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_import_has__view_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_import_has__view_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* l_lean_parser_module_import_has__view_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_4; obj* x_6; 
x_6 = l_lean_parser_syntax_as__node___main(x_0);
if (lean::obj_tag(x_6) == 0)
{
obj* x_8; 
lean::dec(x_6);
x_8 = l_lean_parser_module_import_has__view_x_27___lambda__1___closed__3;
lean::inc(x_8);
return x_8;
}
else
{
obj* x_10; obj* x_12; obj* x_13; 
x_10 = lean::cnstr_get(x_6, 0);
lean::inc(x_10);
if (lean::is_shared(x_6)) {
 lean::dec(x_6);
 x_12 = lean::box(0);
} else {
 lean::cnstr_release(x_6, 0);
 x_12 = x_6;
}
x_13 = lean::cnstr_get(x_10, 1);
lean::inc(x_13);
lean::dec(x_10);
if (lean::obj_tag(x_13) == 0)
{
lean::dec(x_12);
if (lean::obj_tag(x_13) == 0)
{
obj* x_18; 
lean::dec(x_13);
x_18 = l_lean_parser_module_import_has__view_x_27___lambda__1___closed__3;
lean::inc(x_18);
return x_18;
}
else
{
obj* x_20; obj* x_23; 
x_20 = lean::cnstr_get(x_13, 0);
lean::inc(x_20);
lean::dec(x_13);
x_23 = lean::box(0);
x_3 = x_23;
x_4 = x_20;
goto lbl_5;
}
}
else
{
obj* x_24; obj* x_26; 
x_24 = lean::cnstr_get(x_13, 0);
lean::inc(x_24);
x_26 = lean::cnstr_get(x_13, 1);
lean::inc(x_26);
lean::dec(x_13);
switch (lean::obj_tag(x_24)) {
case 0:
{
obj* x_29; obj* x_32; 
x_29 = lean::cnstr_get(x_24, 0);
lean::inc(x_29);
lean::dec(x_24);
if (lean::is_scalar(x_12)) {
 x_32 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_32 = x_12;
}
lean::cnstr_set(x_32, 0, x_29);
if (lean::obj_tag(x_26) == 0)
{
lean::dec(x_26);
x_1 = x_32;
goto lbl_2;
}
else
{
obj* x_34; 
x_34 = lean::cnstr_get(x_26, 0);
lean::inc(x_34);
lean::dec(x_26);
x_3 = x_32;
x_4 = x_34;
goto lbl_5;
}
}
case 1:
{
lean::dec(x_24);
lean::dec(x_12);
if (lean::obj_tag(x_26) == 0)
{
obj* x_40; 
lean::dec(x_26);
x_40 = l_lean_parser_module_import_has__view_x_27___lambda__1___closed__3;
lean::inc(x_40);
return x_40;
}
else
{
obj* x_42; obj* x_45; 
x_42 = lean::cnstr_get(x_26, 0);
lean::inc(x_42);
lean::dec(x_26);
x_45 = lean::box(0);
x_3 = x_45;
x_4 = x_42;
goto lbl_5;
}
}
case 2:
{
lean::dec(x_24);
lean::dec(x_12);
if (lean::obj_tag(x_26) == 0)
{
obj* x_49; 
lean::dec(x_26);
x_49 = l_lean_parser_module_import_has__view_x_27___lambda__1___closed__3;
lean::inc(x_49);
return x_49;
}
else
{
obj* x_51; obj* x_54; 
x_51 = lean::cnstr_get(x_26, 0);
lean::inc(x_51);
lean::dec(x_26);
x_54 = lean::box(0);
x_3 = x_54;
x_4 = x_51;
goto lbl_5;
}
}
default:
{
lean::dec(x_24);
lean::dec(x_12);
if (lean::obj_tag(x_26) == 0)
{
obj* x_58; 
lean::dec(x_26);
x_58 = l_lean_parser_module_import_has__view_x_27___lambda__1___closed__3;
lean::inc(x_58);
return x_58;
}
else
{
obj* x_60; obj* x_63; 
x_60 = lean::cnstr_get(x_26, 0);
lean::inc(x_60);
lean::dec(x_26);
x_63 = lean::box(0);
x_3 = x_63;
x_4 = x_60;
goto lbl_5;
}
}
}
}
}
lbl_2:
{
obj* x_64; obj* x_65; 
x_64 = lean::box(3);
x_65 = l_lean_parser_syntax_as__node___main(x_64);
if (lean::obj_tag(x_65) == 0)
{
obj* x_67; obj* x_69; 
lean::dec(x_65);
x_67 = l_lean_parser_module_import_has__view_x_27___lambda__1___closed__1;
lean::inc(x_67);
x_69 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_69, 0, x_1);
lean::cnstr_set(x_69, 1, x_67);
return x_69;
}
else
{
obj* x_70; obj* x_73; obj* x_76; obj* x_78; obj* x_79; 
x_70 = lean::cnstr_get(x_65, 0);
lean::inc(x_70);
lean::dec(x_65);
x_73 = lean::cnstr_get(x_70, 1);
lean::inc(x_73);
lean::dec(x_70);
x_76 = l_lean_parser_module_import_has__view_x_27___lambda__1___closed__2;
lean::inc(x_76);
x_78 = l_list_map___main___rarg(x_76, x_73);
x_79 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_79, 0, x_1);
lean::cnstr_set(x_79, 1, x_78);
return x_79;
}
}
lbl_5:
{
obj* x_80; 
x_80 = l_lean_parser_syntax_as__node___main(x_4);
if (lean::obj_tag(x_80) == 0)
{
obj* x_82; obj* x_84; 
lean::dec(x_80);
x_82 = l_lean_parser_module_import_has__view_x_27___lambda__1___closed__1;
lean::inc(x_82);
x_84 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_84, 0, x_3);
lean::cnstr_set(x_84, 1, x_82);
return x_84;
}
else
{
obj* x_85; obj* x_88; obj* x_91; obj* x_93; obj* x_94; 
x_85 = lean::cnstr_get(x_80, 0);
lean::inc(x_85);
lean::dec(x_80);
x_88 = lean::cnstr_get(x_85, 1);
lean::inc(x_88);
lean::dec(x_85);
x_91 = l_lean_parser_module_import_has__view_x_27___lambda__1___closed__2;
lean::inc(x_91);
x_93 = l_list_map___main___rarg(x_91, x_88);
x_94 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_94, 0, x_3);
lean::cnstr_set(x_94, 1, x_93);
return x_94;
}
}
}
}
obj* _init_l_lean_parser_module_import_has__view_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_0 = l_lean_parser_module_import__path_has__view;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::box(3);
x_4 = lean::apply_1(x_1, x_3);
x_5 = lean::box(0);
x_6 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_6, 0, x_4);
lean::cnstr_set(x_6, 1, x_5);
return x_6;
}
}
obj* _init_l_lean_parser_module_import_has__view_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = l_lean_parser_module_import__path_has__view;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
return x_1;
}
}
obj* _init_l_lean_parser_module_import_has__view_x_27___lambda__1___closed__3() {
_start:
{
obj* x_0; obj* x_2; 
x_2 = lean::box(0);
x_0 = x_2;
goto lbl_1;
lbl_1:
{
obj* x_3; obj* x_4; 
x_3 = lean::box(3);
x_4 = l_lean_parser_syntax_as__node___main(x_3);
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; obj* x_8; 
lean::dec(x_4);
x_6 = l_lean_parser_module_import_has__view_x_27___lambda__1___closed__1;
lean::inc(x_6);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_0);
lean::cnstr_set(x_8, 1, x_6);
return x_8;
}
else
{
obj* x_9; obj* x_12; obj* x_15; obj* x_17; obj* x_18; 
x_9 = lean::cnstr_get(x_4, 0);
lean::inc(x_9);
lean::dec(x_4);
x_12 = lean::cnstr_get(x_9, 1);
lean::inc(x_12);
lean::dec(x_9);
x_15 = l_lean_parser_module_import_has__view_x_27___lambda__1___closed__2;
lean::inc(x_15);
x_17 = l_list_map___main___rarg(x_15, x_12);
x_18 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_18, 0, x_0);
lean::cnstr_set(x_18, 1, x_17);
return x_18;
}
}
}
}
obj* l_lean_parser_module_import_has__view_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_13; obj* x_14; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_22; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
x_6 = l_lean_parser_raw_view___rarg___lambda__3___closed__1;
lean::inc(x_6);
x_8 = l_option_map___rarg(x_6, x_1);
x_9 = lean::box(3);
x_10 = l_option_get__or__else___main___rarg(x_8, x_9);
x_11 = l_lean_parser_module_import_has__view_x_27___lambda__2___closed__1;
lean::inc(x_11);
x_13 = l_list_map___main___rarg(x_11, x_3);
x_14 = l_lean_parser_no__kind;
lean::inc(x_14);
x_16 = l_lean_parser_syntax_mk__node(x_14, x_13);
x_17 = lean::box(0);
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_16);
lean::cnstr_set(x_18, 1, x_17);
x_19 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_19, 0, x_10);
lean::cnstr_set(x_19, 1, x_18);
x_20 = l_lean_parser_module_import;
lean::inc(x_20);
x_22 = l_lean_parser_syntax_mk__node(x_20, x_19);
return x_22;
}
}
obj* _init_l_lean_parser_module_import_has__view_x_27___lambda__2___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = l_lean_parser_module_import__path_has__view;
x_1 = lean::cnstr_get(x_0, 1);
lean::inc(x_1);
return x_1;
}
}
obj* _init_l_lean_parser_module_import_has__view() {
_start:
{
obj* x_0; 
x_0 = l_lean_parser_module_import_has__view_x_27;
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_lean_parser_module_import_parser_lean_parser_has__tokens() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_0 = lean::mk_string("import");
x_1 = lean::mk_nat_obj(0u);
x_2 = l_lean_parser_symbol_tokens___rarg(x_0, x_1);
x_3 = l_lean_parser_module_import__path_parser_lean_parser_has__tokens;
lean::inc(x_3);
x_5 = l_lean_parser_tokens___rarg(x_3);
x_6 = lean::box(0);
x_7 = l_lean_parser_list_cons_tokens___rarg(x_5, x_6);
x_8 = l_lean_parser_list_cons_tokens___rarg(x_2, x_7);
x_9 = l_lean_parser_tokens___rarg(x_8);
return x_9;
}
}
obj* _init_l_lean_parser_module_import_parser_lean_parser_has__view() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_23; 
x_0 = lean::mk_string("import");
x_1 = l_string_trim(x_0);
lean::inc(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_3, 0, x_1);
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_unicode__symbol_lean_parser_has__view___spec__1), 6, 3);
lean::closure_set(x_5, 0, x_1);
lean::closure_set(x_5, 1, x_4);
lean::closure_set(x_5, 2, x_3);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_import__path_parser), 3, 0);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_many1___at_lean_parser_ident__univ__spec_parser_lean_parser_has__view___spec__1), 4, 1);
lean::closure_set(x_7, 0, x_6);
x_8 = lean::box(0);
x_9 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_5);
lean::cnstr_set(x_10, 1, x_9);
x_11 = l_lean_parser_basic__parser__m_monad;
x_12 = l_lean_parser_basic__parser__m_monad__except;
x_13 = l_lean_parser_basic__parser__m_lean_parser_monad__parsec;
x_14 = l_lean_parser_basic__parser__m_alternative;
x_15 = l_lean_parser_module_import;
x_16 = l_lean_parser_module_import_has__view;
lean::inc(x_16);
lean::inc(x_15);
lean::inc(x_14);
lean::inc(x_13);
lean::inc(x_12);
lean::inc(x_11);
x_23 = l_lean_parser_combinators_node_view___rarg(x_11, x_12, x_13, x_14, x_15, x_10, x_16);
return x_23;
}
}
obj* l_lean_parser_module_import_parser(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_7; 
x_3 = l_lean_parser_module_import;
x_4 = l_lean_parser_module_import_parser___closed__1;
lean::inc(x_4);
lean::inc(x_3);
x_7 = l_lean_parser_combinators_node___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__8(x_3, x_4, x_0, x_1, x_2);
return x_7;
}
}
obj* _init_l_lean_parser_module_import_parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_0 = lean::mk_string("import");
x_1 = l_string_trim(x_0);
lean::inc(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_3, 0, x_1);
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_unicode__symbol_lean_parser_has__view___spec__1), 6, 3);
lean::closure_set(x_5, 0, x_1);
lean::closure_set(x_5, 1, x_4);
lean::closure_set(x_5, 2, x_3);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_import__path_parser), 3, 0);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_many1___at_lean_parser_ident__univ__spec_parser_lean_parser_has__view___spec__1), 4, 1);
lean::closure_set(x_7, 0, x_6);
x_8 = lean::box(0);
x_9 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_5);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
}
}
obj* _init_l_lean_parser_module_header() {
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
x_7 = lean::mk_string("header");
x_8 = lean::name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_lean_parser_module_header_has__view_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_header_has__view_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_header_has__view_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* l_lean_parser_module_header_has__view_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_9; 
x_9 = l_lean_parser_syntax_as__node___main(x_0);
if (lean::obj_tag(x_9) == 0)
{
obj* x_11; 
lean::dec(x_9);
x_11 = l_lean_parser_module_header_has__view_x_27___lambda__1___closed__6;
lean::inc(x_11);
return x_11;
}
else
{
obj* x_13; obj* x_16; 
x_13 = lean::cnstr_get(x_9, 0);
lean::inc(x_13);
lean::dec(x_9);
x_16 = lean::cnstr_get(x_13, 1);
lean::inc(x_16);
lean::dec(x_13);
if (lean::obj_tag(x_16) == 0)
{
obj* x_19; 
x_19 = lean::box(3);
x_6 = x_16;
x_7 = x_19;
goto lbl_8;
}
else
{
obj* x_20; obj* x_22; 
x_20 = lean::cnstr_get(x_16, 0);
lean::inc(x_20);
x_22 = lean::cnstr_get(x_16, 1);
lean::inc(x_22);
lean::dec(x_16);
x_6 = x_22;
x_7 = x_20;
goto lbl_8;
}
}
lbl_2:
{
obj* x_25; obj* x_26; 
x_25 = lean::box(3);
x_26 = l_lean_parser_syntax_as__node___main(x_25);
if (lean::obj_tag(x_26) == 0)
{
obj* x_28; obj* x_30; 
lean::dec(x_26);
x_28 = l_lean_parser_module_header_has__view_x_27___lambda__1___closed__1;
lean::inc(x_28);
x_30 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_30, 0, x_1);
lean::cnstr_set(x_30, 1, x_28);
return x_30;
}
else
{
obj* x_31; obj* x_34; obj* x_37; obj* x_39; obj* x_40; 
x_31 = lean::cnstr_get(x_26, 0);
lean::inc(x_31);
lean::dec(x_26);
x_34 = lean::cnstr_get(x_31, 1);
lean::inc(x_34);
lean::dec(x_31);
x_37 = l_lean_parser_module_header_has__view_x_27___lambda__1___closed__2;
lean::inc(x_37);
x_39 = l_list_map___main___rarg(x_37, x_34);
x_40 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_40, 0, x_1);
lean::cnstr_set(x_40, 1, x_39);
return x_40;
}
}
lbl_5:
{
obj* x_41; 
x_41 = l_lean_parser_syntax_as__node___main(x_4);
if (lean::obj_tag(x_41) == 0)
{
obj* x_43; obj* x_45; 
lean::dec(x_41);
x_43 = l_lean_parser_module_header_has__view_x_27___lambda__1___closed__1;
lean::inc(x_43);
x_45 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_45, 0, x_3);
lean::cnstr_set(x_45, 1, x_43);
return x_45;
}
else
{
obj* x_46; obj* x_49; obj* x_52; obj* x_54; obj* x_55; 
x_46 = lean::cnstr_get(x_41, 0);
lean::inc(x_46);
lean::dec(x_41);
x_49 = lean::cnstr_get(x_46, 1);
lean::inc(x_49);
lean::dec(x_46);
x_52 = l_lean_parser_module_header_has__view_x_27___lambda__1___closed__2;
lean::inc(x_52);
x_54 = l_list_map___main___rarg(x_52, x_49);
x_55 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_55, 0, x_3);
lean::cnstr_set(x_55, 1, x_54);
return x_55;
}
}
lbl_8:
{
obj* x_56; 
x_56 = l_lean_parser_syntax_as__node___main(x_7);
if (lean::obj_tag(x_56) == 0)
{
lean::dec(x_56);
if (lean::obj_tag(x_6) == 0)
{
obj* x_59; 
lean::dec(x_6);
x_59 = l_lean_parser_module_header_has__view_x_27___lambda__1___closed__3;
lean::inc(x_59);
return x_59;
}
else
{
obj* x_61; obj* x_64; 
x_61 = lean::cnstr_get(x_6, 0);
lean::inc(x_61);
lean::dec(x_6);
x_64 = l_lean_parser_module_header_has__view_x_27___lambda__1___closed__4;
lean::inc(x_64);
x_3 = x_64;
x_4 = x_61;
goto lbl_5;
}
}
else
{
obj* x_66; obj* x_68; obj* x_69; 
x_66 = lean::cnstr_get(x_56, 0);
lean::inc(x_66);
if (lean::is_shared(x_56)) {
 lean::dec(x_56);
 x_68 = lean::box(0);
} else {
 lean::cnstr_release(x_56, 0);
 x_68 = x_56;
}
x_69 = lean::cnstr_get(x_66, 1);
lean::inc(x_69);
lean::dec(x_66);
if (lean::obj_tag(x_69) == 0)
{
lean::dec(x_68);
lean::dec(x_69);
if (lean::obj_tag(x_6) == 0)
{
obj* x_75; 
lean::dec(x_6);
x_75 = l_lean_parser_module_header_has__view_x_27___lambda__1___closed__5;
lean::inc(x_75);
return x_75;
}
else
{
obj* x_77; obj* x_80; 
x_77 = lean::cnstr_get(x_6, 0);
lean::inc(x_77);
lean::dec(x_6);
x_80 = lean::box(0);
x_3 = x_80;
x_4 = x_77;
goto lbl_5;
}
}
else
{
obj* x_81; obj* x_83; 
x_81 = lean::cnstr_get(x_69, 0);
lean::inc(x_81);
x_83 = lean::cnstr_get(x_69, 1);
lean::inc(x_83);
lean::dec(x_69);
if (lean::obj_tag(x_83) == 0)
{
obj* x_87; obj* x_88; obj* x_90; obj* x_91; 
lean::dec(x_83);
x_87 = l_lean_parser_module_prelude_has__view;
x_88 = lean::cnstr_get(x_87, 0);
lean::inc(x_88);
x_90 = lean::apply_1(x_88, x_81);
if (lean::is_scalar(x_68)) {
 x_91 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_91 = x_68;
}
lean::cnstr_set(x_91, 0, x_90);
if (lean::obj_tag(x_6) == 0)
{
lean::dec(x_6);
x_1 = x_91;
goto lbl_2;
}
else
{
obj* x_93; 
x_93 = lean::cnstr_get(x_6, 0);
lean::inc(x_93);
lean::dec(x_6);
x_3 = x_91;
x_4 = x_93;
goto lbl_5;
}
}
else
{
lean::dec(x_68);
lean::dec(x_83);
lean::dec(x_81);
if (lean::obj_tag(x_6) == 0)
{
obj* x_100; 
lean::dec(x_6);
x_100 = l_lean_parser_module_header_has__view_x_27___lambda__1___closed__3;
lean::inc(x_100);
return x_100;
}
else
{
obj* x_102; obj* x_105; 
x_102 = lean::cnstr_get(x_6, 0);
lean::inc(x_102);
lean::dec(x_6);
x_105 = l_lean_parser_module_header_has__view_x_27___lambda__1___closed__4;
lean::inc(x_105);
x_3 = x_105;
x_4 = x_102;
goto lbl_5;
}
}
}
}
}
}
}
obj* _init_l_lean_parser_module_header_has__view_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_0 = l_lean_parser_module_import_has__view;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::box(3);
x_4 = lean::apply_1(x_1, x_3);
x_5 = lean::box(0);
x_6 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_6, 0, x_4);
lean::cnstr_set(x_6, 1, x_5);
return x_6;
}
}
obj* _init_l_lean_parser_module_header_has__view_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = l_lean_parser_module_import_has__view;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
return x_1;
}
}
obj* _init_l_lean_parser_module_header_has__view_x_27___lambda__1___closed__3() {
_start:
{
obj* x_0; obj* x_2; obj* x_3; obj* x_5; obj* x_6; obj* x_7; 
x_2 = l_lean_parser_module_prelude_has__view;
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_5 = lean::box(3);
x_6 = lean::apply_1(x_3, x_5);
x_7 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_7, 0, x_6);
x_0 = x_7;
goto lbl_1;
lbl_1:
{
obj* x_8; obj* x_9; 
x_8 = lean::box(3);
x_9 = l_lean_parser_syntax_as__node___main(x_8);
if (lean::obj_tag(x_9) == 0)
{
obj* x_11; obj* x_13; 
lean::dec(x_9);
x_11 = l_lean_parser_module_header_has__view_x_27___lambda__1___closed__1;
lean::inc(x_11);
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_0);
lean::cnstr_set(x_13, 1, x_11);
return x_13;
}
else
{
obj* x_14; obj* x_17; obj* x_20; obj* x_22; obj* x_23; 
x_14 = lean::cnstr_get(x_9, 0);
lean::inc(x_14);
lean::dec(x_9);
x_17 = lean::cnstr_get(x_14, 1);
lean::inc(x_17);
lean::dec(x_14);
x_20 = l_lean_parser_module_header_has__view_x_27___lambda__1___closed__2;
lean::inc(x_20);
x_22 = l_list_map___main___rarg(x_20, x_17);
x_23 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_23, 0, x_0);
lean::cnstr_set(x_23, 1, x_22);
return x_23;
}
}
}
}
obj* _init_l_lean_parser_module_header_has__view_x_27___lambda__1___closed__4() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; 
x_0 = l_lean_parser_module_prelude_has__view;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::box(3);
x_4 = lean::apply_1(x_1, x_3);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
return x_5;
}
}
obj* _init_l_lean_parser_module_header_has__view_x_27___lambda__1___closed__5() {
_start:
{
obj* x_0; obj* x_2; 
x_2 = lean::box(0);
x_0 = x_2;
goto lbl_1;
lbl_1:
{
obj* x_3; obj* x_4; 
x_3 = lean::box(3);
x_4 = l_lean_parser_syntax_as__node___main(x_3);
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; obj* x_8; 
lean::dec(x_4);
x_6 = l_lean_parser_module_header_has__view_x_27___lambda__1___closed__1;
lean::inc(x_6);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_0);
lean::cnstr_set(x_8, 1, x_6);
return x_8;
}
else
{
obj* x_9; obj* x_12; obj* x_15; obj* x_17; obj* x_18; 
x_9 = lean::cnstr_get(x_4, 0);
lean::inc(x_9);
lean::dec(x_4);
x_12 = lean::cnstr_get(x_9, 1);
lean::inc(x_12);
lean::dec(x_9);
x_15 = l_lean_parser_module_header_has__view_x_27___lambda__1___closed__2;
lean::inc(x_15);
x_17 = l_list_map___main___rarg(x_15, x_12);
x_18 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_18, 0, x_0);
lean::cnstr_set(x_18, 1, x_17);
return x_18;
}
}
}
}
obj* _init_l_lean_parser_module_header_has__view_x_27___lambda__1___closed__6() {
_start:
{
obj* x_0; obj* x_2; obj* x_3; obj* x_5; obj* x_6; obj* x_8; obj* x_9; 
x_8 = lean::box(0);
x_9 = lean::box(3);
x_5 = x_8;
x_6 = x_9;
goto lbl_7;
lbl_1:
{
obj* x_10; obj* x_11; 
x_10 = lean::box(3);
x_11 = l_lean_parser_syntax_as__node___main(x_10);
if (lean::obj_tag(x_11) == 0)
{
obj* x_13; obj* x_15; 
lean::dec(x_11);
x_13 = l_lean_parser_module_header_has__view_x_27___lambda__1___closed__1;
lean::inc(x_13);
x_15 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_15, 0, x_0);
lean::cnstr_set(x_15, 1, x_13);
return x_15;
}
else
{
obj* x_16; obj* x_19; obj* x_22; obj* x_24; obj* x_25; 
x_16 = lean::cnstr_get(x_11, 0);
lean::inc(x_16);
lean::dec(x_11);
x_19 = lean::cnstr_get(x_16, 1);
lean::inc(x_19);
lean::dec(x_16);
x_22 = l_lean_parser_module_header_has__view_x_27___lambda__1___closed__2;
lean::inc(x_22);
x_24 = l_list_map___main___rarg(x_22, x_19);
x_25 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_25, 0, x_0);
lean::cnstr_set(x_25, 1, x_24);
return x_25;
}
}
lbl_4:
{
obj* x_26; 
x_26 = l_lean_parser_syntax_as__node___main(x_3);
if (lean::obj_tag(x_26) == 0)
{
obj* x_28; obj* x_30; 
lean::dec(x_26);
x_28 = l_lean_parser_module_header_has__view_x_27___lambda__1___closed__1;
lean::inc(x_28);
x_30 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_30, 0, x_2);
lean::cnstr_set(x_30, 1, x_28);
return x_30;
}
else
{
obj* x_31; obj* x_34; obj* x_37; obj* x_39; obj* x_40; 
x_31 = lean::cnstr_get(x_26, 0);
lean::inc(x_31);
lean::dec(x_26);
x_34 = lean::cnstr_get(x_31, 1);
lean::inc(x_34);
lean::dec(x_31);
x_37 = l_lean_parser_module_header_has__view_x_27___lambda__1___closed__2;
lean::inc(x_37);
x_39 = l_list_map___main___rarg(x_37, x_34);
x_40 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_40, 0, x_2);
lean::cnstr_set(x_40, 1, x_39);
return x_40;
}
}
lbl_7:
{
obj* x_41; 
x_41 = l_lean_parser_syntax_as__node___main(x_6);
if (lean::obj_tag(x_41) == 0)
{
lean::dec(x_41);
if (lean::obj_tag(x_5) == 0)
{
obj* x_44; 
lean::dec(x_5);
x_44 = l_lean_parser_module_header_has__view_x_27___lambda__1___closed__3;
lean::inc(x_44);
return x_44;
}
else
{
obj* x_46; obj* x_49; 
x_46 = lean::cnstr_get(x_5, 0);
lean::inc(x_46);
lean::dec(x_5);
x_49 = l_lean_parser_module_header_has__view_x_27___lambda__1___closed__4;
lean::inc(x_49);
x_2 = x_49;
x_3 = x_46;
goto lbl_4;
}
}
else
{
obj* x_51; obj* x_53; obj* x_54; 
x_51 = lean::cnstr_get(x_41, 0);
lean::inc(x_51);
if (lean::is_shared(x_41)) {
 lean::dec(x_41);
 x_53 = lean::box(0);
} else {
 lean::cnstr_release(x_41, 0);
 x_53 = x_41;
}
x_54 = lean::cnstr_get(x_51, 1);
lean::inc(x_54);
lean::dec(x_51);
if (lean::obj_tag(x_54) == 0)
{
lean::dec(x_53);
lean::dec(x_54);
if (lean::obj_tag(x_5) == 0)
{
obj* x_60; 
lean::dec(x_5);
x_60 = l_lean_parser_module_header_has__view_x_27___lambda__1___closed__5;
lean::inc(x_60);
return x_60;
}
else
{
obj* x_62; obj* x_65; 
x_62 = lean::cnstr_get(x_5, 0);
lean::inc(x_62);
lean::dec(x_5);
x_65 = lean::box(0);
x_2 = x_65;
x_3 = x_62;
goto lbl_4;
}
}
else
{
obj* x_66; obj* x_68; 
x_66 = lean::cnstr_get(x_54, 0);
lean::inc(x_66);
x_68 = lean::cnstr_get(x_54, 1);
lean::inc(x_68);
lean::dec(x_54);
if (lean::obj_tag(x_68) == 0)
{
obj* x_72; obj* x_73; obj* x_75; obj* x_76; 
lean::dec(x_68);
x_72 = l_lean_parser_module_prelude_has__view;
x_73 = lean::cnstr_get(x_72, 0);
lean::inc(x_73);
x_75 = lean::apply_1(x_73, x_66);
if (lean::is_scalar(x_53)) {
 x_76 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_76 = x_53;
}
lean::cnstr_set(x_76, 0, x_75);
if (lean::obj_tag(x_5) == 0)
{
lean::dec(x_5);
x_0 = x_76;
goto lbl_1;
}
else
{
obj* x_78; 
x_78 = lean::cnstr_get(x_5, 0);
lean::inc(x_78);
lean::dec(x_5);
x_2 = x_76;
x_3 = x_78;
goto lbl_4;
}
}
else
{
lean::dec(x_66);
lean::dec(x_68);
lean::dec(x_53);
if (lean::obj_tag(x_5) == 0)
{
obj* x_85; 
lean::dec(x_5);
x_85 = l_lean_parser_module_header_has__view_x_27___lambda__1___closed__3;
lean::inc(x_85);
return x_85;
}
else
{
obj* x_87; obj* x_90; 
x_87 = lean::cnstr_get(x_5, 0);
lean::inc(x_87);
lean::dec(x_5);
x_90 = l_lean_parser_module_header_has__view_x_27___lambda__1___closed__4;
lean::inc(x_90);
x_2 = x_90;
x_3 = x_87;
goto lbl_4;
}
}
}
}
}
}
}
obj* l_lean_parser_module_header_has__view_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_6; obj* x_8; obj* x_9; obj* x_11; obj* x_12; obj* x_14; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
x_6 = l_lean_parser_module_header_has__view_x_27___lambda__2___closed__1;
lean::inc(x_6);
x_8 = l_list_map___main___rarg(x_6, x_3);
x_9 = l_lean_parser_no__kind;
lean::inc(x_9);
x_11 = l_lean_parser_syntax_mk__node(x_9, x_8);
x_12 = lean::box(0);
lean::inc(x_12);
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_11);
lean::cnstr_set(x_14, 1, x_12);
if (lean::obj_tag(x_1) == 0)
{
obj* x_17; obj* x_19; obj* x_20; obj* x_22; 
lean::dec(x_12);
lean::dec(x_1);
x_17 = l_lean_parser_combinators_many___rarg___closed__1;
lean::inc(x_17);
x_19 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_19, 0, x_17);
lean::cnstr_set(x_19, 1, x_14);
x_20 = l_lean_parser_module_header;
lean::inc(x_20);
x_22 = l_lean_parser_syntax_mk__node(x_20, x_19);
return x_22;
}
else
{
obj* x_23; obj* x_26; obj* x_27; obj* x_29; obj* x_30; obj* x_32; obj* x_33; obj* x_34; obj* x_36; 
x_23 = lean::cnstr_get(x_1, 0);
lean::inc(x_23);
lean::dec(x_1);
x_26 = l_lean_parser_module_prelude_has__view;
x_27 = lean::cnstr_get(x_26, 1);
lean::inc(x_27);
x_29 = lean::apply_1(x_27, x_23);
x_30 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_12);
lean::inc(x_9);
x_32 = l_lean_parser_syntax_mk__node(x_9, x_30);
x_33 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_14);
x_34 = l_lean_parser_module_header;
lean::inc(x_34);
x_36 = l_lean_parser_syntax_mk__node(x_34, x_33);
return x_36;
}
}
}
obj* _init_l_lean_parser_module_header_has__view_x_27___lambda__2___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = l_lean_parser_module_import_has__view;
x_1 = lean::cnstr_get(x_0, 1);
lean::inc(x_1);
return x_1;
}
}
obj* _init_l_lean_parser_module_header_has__view() {
_start:
{
obj* x_0; 
x_0 = l_lean_parser_module_header_has__view_x_27;
lean::inc(x_0);
return x_0;
}
}
obj* l_lean_parser_combinators_optional___at_lean_parser_module_header_parser_lean_parser_has__tokens___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_12; obj* x_13; obj* x_15; 
x_7 = lean::box(0);
lean::inc(x_2);
x_12 = lean::apply_3(x_0, x_1, x_2, x_3);
x_13 = lean::cnstr_get(x_12, 0);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_12, 1);
lean::inc(x_15);
lean::dec(x_12);
if (lean::obj_tag(x_13) == 0)
{
if (lean::obj_tag(x_13) == 0)
{
obj* x_18; obj* x_20; obj* x_22; obj* x_24; obj* x_25; obj* x_26; obj* x_28; obj* x_29; 
x_18 = lean::cnstr_get(x_13, 0);
lean::inc(x_18);
x_20 = lean::cnstr_get(x_13, 1);
lean::inc(x_20);
x_22 = lean::cnstr_get(x_13, 2);
lean::inc(x_22);
if (lean::is_shared(x_13)) {
 lean::dec(x_13);
 x_24 = lean::box(0);
} else {
 lean::cnstr_release(x_13, 0);
 lean::cnstr_release(x_13, 1);
 lean::cnstr_release(x_13, 2);
 x_24 = x_13;
}
x_25 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_25, 0, x_18);
x_26 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_26);
if (lean::is_scalar(x_24)) {
 x_28 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_28 = x_24;
}
lean::cnstr_set(x_28, 0, x_25);
lean::cnstr_set(x_28, 1, x_20);
lean::cnstr_set(x_28, 2, x_26);
x_29 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_22, x_28);
x_8 = x_29;
x_9 = x_15;
goto lbl_10;
}
else
{
obj* x_30; uint8 x_32; obj* x_33; obj* x_34; obj* x_35; 
x_30 = lean::cnstr_get(x_13, 0);
lean::inc(x_30);
x_32 = lean::cnstr_get_scalar<uint8>(x_13, sizeof(void*)*1);
if (lean::is_shared(x_13)) {
 lean::dec(x_13);
 x_33 = lean::box(0);
} else {
 lean::cnstr_release(x_13, 0);
 x_33 = x_13;
}
if (lean::is_scalar(x_33)) {
 x_34 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_34 = x_33;
}
lean::cnstr_set(x_34, 0, x_30);
lean::cnstr_set_scalar(x_34, sizeof(void*)*1, x_32);
x_35 = x_34;
x_8 = x_35;
x_9 = x_15;
goto lbl_10;
}
}
else
{
obj* x_36; uint8 x_38; obj* x_39; obj* x_40; obj* x_42; obj* x_44; obj* x_46; obj* x_49; obj* x_51; obj* x_52; obj* x_54; obj* x_55; obj* x_56; 
x_36 = lean::cnstr_get(x_13, 0);
lean::inc(x_36);
x_38 = lean::cnstr_get_scalar<uint8>(x_13, sizeof(void*)*1);
if (lean::is_shared(x_13)) {
 lean::dec(x_13);
 x_39 = lean::box(0);
} else {
 lean::cnstr_release(x_13, 0);
 x_39 = x_13;
}
x_40 = lean::cnstr_get(x_36, 0);
lean::inc(x_40);
x_42 = lean::cnstr_get(x_36, 1);
lean::inc(x_42);
x_44 = lean::cnstr_get(x_36, 2);
lean::inc(x_44);
x_46 = lean::cnstr_get(x_36, 3);
lean::inc(x_46);
lean::dec(x_36);
x_49 = l_option_get___main___at_lean_parser_run___spec__2(x_46);
lean::inc(x_7);
x_51 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_51, 0, x_49);
lean::cnstr_set(x_51, 1, x_7);
x_52 = l_lean_parser_no__kind;
lean::inc(x_52);
x_54 = l_lean_parser_syntax_mk__node(x_52, x_51);
x_55 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_55, 0, x_54);
x_56 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_56, 0, x_40);
lean::cnstr_set(x_56, 1, x_42);
lean::cnstr_set(x_56, 2, x_44);
lean::cnstr_set(x_56, 3, x_55);
if (x_38 == 0)
{
uint8 x_57; obj* x_58; obj* x_59; 
x_57 = 0;
if (lean::is_scalar(x_39)) {
 x_58 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_58 = x_39;
}
lean::cnstr_set(x_58, 0, x_56);
lean::cnstr_set_scalar(x_58, sizeof(void*)*1, x_57);
x_59 = x_58;
x_8 = x_59;
x_9 = x_15;
goto lbl_10;
}
else
{
obj* x_60; obj* x_61; 
if (lean::is_scalar(x_39)) {
 x_60 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_60 = x_39;
}
lean::cnstr_set(x_60, 0, x_56);
lean::cnstr_set_scalar(x_60, sizeof(void*)*1, x_38);
x_61 = x_60;
x_8 = x_61;
x_9 = x_15;
goto lbl_10;
}
}
lbl_6:
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_62; obj* x_64; obj* x_66; obj* x_68; 
x_62 = lean::cnstr_get(x_4, 0);
lean::inc(x_62);
x_64 = lean::cnstr_get(x_4, 1);
lean::inc(x_64);
x_66 = lean::cnstr_get(x_4, 2);
lean::inc(x_66);
if (lean::is_shared(x_4)) {
 lean::dec(x_4);
 x_68 = lean::box(0);
} else {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_release(x_4, 1);
 lean::cnstr_release(x_4, 2);
 x_68 = x_4;
}
if (lean::obj_tag(x_62) == 0)
{
obj* x_70; obj* x_71; obj* x_74; obj* x_75; obj* x_76; 
lean::dec(x_62);
x_70 = l_lean_parser_combinators_many___rarg___closed__1;
x_71 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_71);
lean::inc(x_70);
if (lean::is_scalar(x_68)) {
 x_74 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_74 = x_68;
}
lean::cnstr_set(x_74, 0, x_70);
lean::cnstr_set(x_74, 1, x_64);
lean::cnstr_set(x_74, 2, x_71);
x_75 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_66, x_74);
x_76 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_76, 0, x_75);
lean::cnstr_set(x_76, 1, x_5);
return x_76;
}
else
{
obj* x_77; obj* x_80; obj* x_81; obj* x_82; obj* x_84; obj* x_85; obj* x_87; obj* x_88; obj* x_89; 
x_77 = lean::cnstr_get(x_62, 0);
lean::inc(x_77);
lean::dec(x_62);
x_80 = lean::box(0);
x_81 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_81, 0, x_77);
lean::cnstr_set(x_81, 1, x_80);
x_82 = l_lean_parser_no__kind;
lean::inc(x_82);
x_84 = l_lean_parser_syntax_mk__node(x_82, x_81);
x_85 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_85);
if (lean::is_scalar(x_68)) {
 x_87 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_87 = x_68;
}
lean::cnstr_set(x_87, 0, x_84);
lean::cnstr_set(x_87, 1, x_64);
lean::cnstr_set(x_87, 2, x_85);
x_88 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_66, x_87);
x_89 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_89, 0, x_88);
lean::cnstr_set(x_89, 1, x_5);
return x_89;
}
}
else
{
obj* x_90; uint8 x_92; obj* x_93; obj* x_94; obj* x_95; obj* x_96; 
x_90 = lean::cnstr_get(x_4, 0);
lean::inc(x_90);
x_92 = lean::cnstr_get_scalar<uint8>(x_4, sizeof(void*)*1);
if (lean::is_shared(x_4)) {
 lean::dec(x_4);
 x_93 = lean::box(0);
} else {
 lean::cnstr_release(x_4, 0);
 x_93 = x_4;
}
if (lean::is_scalar(x_93)) {
 x_94 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_94 = x_93;
}
lean::cnstr_set(x_94, 0, x_90);
lean::cnstr_set_scalar(x_94, sizeof(void*)*1, x_92);
x_95 = x_94;
x_96 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_96, 0, x_95);
lean::cnstr_set(x_96, 1, x_5);
return x_96;
}
}
lbl_10:
{
if (lean::obj_tag(x_8) == 0)
{
lean::dec(x_7);
lean::dec(x_2);
x_4 = x_8;
x_5 = x_9;
goto lbl_6;
}
else
{
obj* x_99; uint8 x_101; 
x_99 = lean::cnstr_get(x_8, 0);
lean::inc(x_99);
x_101 = lean::cnstr_get_scalar<uint8>(x_8, sizeof(void*)*1);
if (x_101 == 0)
{
obj* x_103; obj* x_106; obj* x_108; obj* x_109; obj* x_110; 
lean::dec(x_8);
x_103 = lean::cnstr_get(x_99, 2);
lean::inc(x_103);
lean::dec(x_99);
x_106 = l_mjoin___rarg___closed__1;
lean::inc(x_106);
x_108 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_108, 0, x_103);
lean::closure_set(x_108, 1, x_106);
x_109 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_109, 0, x_108);
x_110 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_110, 0, x_7);
lean::cnstr_set(x_110, 1, x_2);
lean::cnstr_set(x_110, 2, x_109);
x_4 = x_110;
x_5 = x_9;
goto lbl_6;
}
else
{
lean::dec(x_7);
lean::dec(x_2);
lean::dec(x_99);
x_4 = x_8;
x_5 = x_9;
goto lbl_6;
}
}
}
}
}
obj* _init_l_lean_parser_module_header_parser_lean_parser_has__tokens() {
_start:
{
obj* x_0; obj* x_2; obj* x_3; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_0 = l_lean_parser_module_prelude_parser_lean_parser_has__tokens;
lean::inc(x_0);
x_2 = l_lean_parser_tokens___rarg(x_0);
x_3 = l_lean_parser_module_import_parser_lean_parser_has__tokens;
lean::inc(x_3);
x_5 = l_lean_parser_tokens___rarg(x_3);
x_6 = lean::box(0);
x_7 = l_lean_parser_list_cons_tokens___rarg(x_5, x_6);
x_8 = l_lean_parser_list_cons_tokens___rarg(x_2, x_7);
x_9 = l_lean_parser_tokens___rarg(x_8);
return x_9;
}
}
obj* _init_l_lean_parser_module_header_parser_lean_parser_has__view() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_19; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_prelude_parser), 3, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_optional___at_lean_parser_module_header_parser_lean_parser_has__tokens___spec__1), 4, 1);
lean::closure_set(x_1, 0, x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_import_parser), 3, 0);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_many___at_lean_parser_module_import__path_parser_lean_parser_has__tokens___spec__1), 4, 1);
lean::closure_set(x_3, 0, x_2);
x_4 = lean::box(0);
x_5 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_5, 0, x_3);
lean::cnstr_set(x_5, 1, x_4);
x_6 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_6, 0, x_1);
lean::cnstr_set(x_6, 1, x_5);
x_7 = l_lean_parser_basic__parser__m_monad;
x_8 = l_lean_parser_basic__parser__m_monad__except;
x_9 = l_lean_parser_basic__parser__m_lean_parser_monad__parsec;
x_10 = l_lean_parser_basic__parser__m_alternative;
x_11 = l_lean_parser_module_header;
x_12 = l_lean_parser_module_header_has__view;
lean::inc(x_12);
lean::inc(x_11);
lean::inc(x_10);
lean::inc(x_9);
lean::inc(x_8);
lean::inc(x_7);
x_19 = l_lean_parser_combinators_node_view___rarg(x_7, x_8, x_9, x_10, x_11, x_6, x_12);
return x_19;
}
}
obj* l_lean_parser_module_header_parser(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_7; 
x_3 = l_lean_parser_module_header;
x_4 = l_lean_parser_module_header_parser___closed__1;
lean::inc(x_4);
lean::inc(x_3);
x_7 = l_lean_parser_combinators_node___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__8(x_3, x_4, x_0, x_1, x_2);
return x_7;
}
}
obj* _init_l_lean_parser_module_header_parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_prelude_parser), 3, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_optional___at_lean_parser_module_header_parser_lean_parser_has__tokens___spec__1), 4, 1);
lean::closure_set(x_1, 0, x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_import_parser), 3, 0);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_many___at_lean_parser_module_import__path_parser_lean_parser_has__tokens___spec__1), 4, 1);
lean::closure_set(x_3, 0, x_2);
x_4 = lean::box(0);
x_5 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_5, 0, x_3);
lean::cnstr_set(x_5, 1, x_4);
x_6 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_6, 0, x_1);
lean::cnstr_set(x_6, 1, x_5);
return x_6;
}
}
obj* l_lean_parser_monad__parsec_error___at___private_209794555__commands__aux___main___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_8; uint8 x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_7 = l_option_get__or__else___main___rarg(x_2, x_5);
x_8 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_0);
lean::cnstr_set(x_8, 2, x_1);
lean::cnstr_set(x_8, 3, x_3);
x_9 = 0;
x_10 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set_scalar(x_10, sizeof(void*)*1, x_9);
x_11 = x_10;
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_6);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_13, 0, x_12);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___at___private_209794555__commands__aux___main___spec__1___rarg___lambda__1), 2, 1);
lean::closure_set(x_14, 0, x_4);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_15, 0, x_13);
lean::closure_set(x_15, 1, x_14);
return x_15;
}
}
obj* l_lean_parser_monad__parsec_error___at___private_209794555__commands__aux___main___spec__1___rarg___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_6; 
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
if (lean::obj_tag(x_2) == 0)
{
obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_14; obj* x_15; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_7 = lean::cnstr_get(x_2, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_2, 1);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_2, 2);
lean::inc(x_11);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_13 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 lean::cnstr_release(x_2, 1);
 lean::cnstr_release(x_2, 2);
 x_13 = x_2;
}
if (lean::is_scalar(x_6)) {
 x_14 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_14 = x_6;
}
lean::cnstr_set(x_14, 0, x_7);
lean::cnstr_set(x_14, 1, x_0);
x_15 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_15);
if (lean::is_scalar(x_13)) {
 x_17 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_17 = x_13;
}
lean::cnstr_set(x_17, 0, x_14);
lean::cnstr_set(x_17, 1, x_9);
lean::cnstr_set(x_17, 2, x_15);
x_18 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_4);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_19, 0, x_18);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_yield__command___lambda__1), 2, 1);
lean::closure_set(x_20, 0, x_11);
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_21, 0, x_19);
lean::closure_set(x_21, 1, x_20);
return x_21;
}
else
{
obj* x_23; uint8 x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
lean::dec(x_0);
x_23 = lean::cnstr_get(x_2, 0);
lean::inc(x_23);
x_25 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*1);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_26 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 x_26 = x_2;
}
if (lean::is_scalar(x_26)) {
 x_27 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_27 = x_26;
}
lean::cnstr_set(x_27, 0, x_23);
lean::cnstr_set_scalar(x_27, sizeof(void*)*1, x_25);
x_28 = x_27;
if (lean::is_scalar(x_6)) {
 x_29 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_29 = x_6;
}
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_4);
x_30 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_30, 0, x_29);
return x_30;
}
}
}
obj* l_lean_parser_monad__parsec_error___at___private_209794555__commands__aux___main___spec__1(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___at___private_209794555__commands__aux___main___spec__1___rarg), 7, 0);
return x_2;
}
}
obj* l_lean_parser_monad__parsec_eoi___at___private_209794555__commands__aux___main___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_6; obj* x_7; obj* x_8; obj* x_10; obj* x_11; obj* x_12; obj* x_14; 
x_3 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_3);
lean::inc(x_1);
x_6 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_6, 0, x_1);
lean::cnstr_set(x_6, 1, x_1);
lean::cnstr_set(x_6, 2, x_3);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_2);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_8, 0, x_7);
lean::inc(x_3);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_yield__command___lambda__6), 3, 2);
lean::closure_set(x_10, 0, x_0);
lean::closure_set(x_10, 1, x_3);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_11, 0, x_8);
lean::closure_set(x_11, 1, x_10);
x_12 = l_lean_parser_monad__parsec_eoi___at___private_209794555__commands__aux___main___spec__2___closed__1;
lean::inc(x_12);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_14, 0, x_11);
lean::closure_set(x_14, 1, x_12);
return x_14;
}
}
obj* _init_l_lean_parser_monad__parsec_eoi___at___private_209794555__commands__aux___main___spec__2___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_id___rarg), 1, 0);
x_1 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_eoi___at___private_209794555__commands__aux___main___spec__2___lambda__1), 2, 1);
lean::closure_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_lean_parser_monad__parsec_eoi___at___private_209794555__commands__aux___main___spec__2___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_6; 
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
if (lean::obj_tag(x_2) == 0)
{
obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_14; obj* x_16; obj* x_18; obj* x_19; obj* x_20; obj* x_21; uint8 x_22; 
x_7 = lean::cnstr_get(x_2, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_2, 1);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_2, 2);
lean::inc(x_11);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_13 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 lean::cnstr_release(x_2, 1);
 lean::cnstr_release(x_2, 2);
 x_13 = x_2;
}
x_14 = lean::cnstr_get(x_7, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_7, 1);
lean::inc(x_16);
if (lean::is_shared(x_7)) {
 lean::dec(x_7);
 x_18 = lean::box(0);
} else {
 lean::cnstr_release(x_7, 0);
 lean::cnstr_release(x_7, 1);
 x_18 = x_7;
}
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_yield__command___lambda__1), 2, 1);
lean::closure_set(x_19, 0, x_11);
x_20 = lean::string_iterator_remaining(x_14);
x_21 = lean::mk_nat_obj(0u);
x_22 = lean::nat_dec_eq(x_20, x_21);
lean::dec(x_21);
lean::dec(x_20);
if (x_22 == 0)
{
uint32 x_29; obj* x_31; obj* x_32; obj* x_34; obj* x_36; obj* x_37; obj* x_38; obj* x_41; obj* x_42; 
lean::dec(x_18);
lean::dec(x_13);
lean::dec(x_6);
lean::dec(x_0);
x_29 = lean::string_iterator_curr(x_14);
lean::dec(x_14);
x_31 = l_char_quote__core(x_29);
x_32 = l_char_has__repr___closed__1;
lean::inc(x_32);
x_34 = lean::string_append(x_32, x_31);
lean::dec(x_31);
x_36 = lean::string_append(x_34, x_32);
x_37 = lean::box(0);
x_38 = l_lean_parser_monad__parsec_eoi___rarg___lambda__1___closed__1;
lean::inc(x_37);
lean::inc(x_38);
x_41 = l_lean_parser_monad__parsec_error___at___private_209794555__commands__aux___main___spec__1___rarg(x_36, x_38, x_37, x_37, x_16, x_9, x_4);
x_42 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_42, 0, x_41);
lean::closure_set(x_42, 1, x_19);
return x_42;
}
else
{
obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; 
lean::dec(x_14);
x_44 = lean::box(0);
if (lean::is_scalar(x_6)) {
 x_45 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_45 = x_6;
}
lean::cnstr_set(x_45, 0, x_44);
lean::cnstr_set(x_45, 1, x_16);
if (lean::is_scalar(x_13)) {
 x_46 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_46 = x_13;
}
lean::cnstr_set(x_46, 0, x_45);
lean::cnstr_set(x_46, 1, x_9);
lean::cnstr_set(x_46, 2, x_0);
if (lean::is_scalar(x_18)) {
 x_47 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_47 = x_18;
}
lean::cnstr_set(x_47, 0, x_46);
lean::cnstr_set(x_47, 1, x_4);
x_48 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_48, 0, x_47);
x_49 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_49, 0, x_48);
lean::closure_set(x_49, 1, x_19);
return x_49;
}
}
else
{
obj* x_51; uint8 x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; 
lean::dec(x_0);
x_51 = lean::cnstr_get(x_2, 0);
lean::inc(x_51);
x_53 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*1);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_54 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 x_54 = x_2;
}
if (lean::is_scalar(x_54)) {
 x_55 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_55 = x_54;
}
lean::cnstr_set(x_55, 0, x_51);
lean::cnstr_set_scalar(x_55, sizeof(void*)*1, x_53);
x_56 = x_55;
if (lean::is_scalar(x_6)) {
 x_57 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_57 = x_6;
}
lean::cnstr_set(x_57, 0, x_56);
lean::cnstr_set(x_57, 1, x_4);
x_58 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_58, 0, x_57);
return x_58;
}
}
}
obj* l_lean_parser_monad__parsec_any___at___private_209794555__commands__aux___main___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_6; obj* x_7; obj* x_8; obj* x_10; obj* x_11; obj* x_12; obj* x_14; 
x_3 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_3);
lean::inc(x_1);
x_6 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_6, 0, x_1);
lean::cnstr_set(x_6, 1, x_1);
lean::cnstr_set(x_6, 2, x_3);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_2);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_8, 0, x_7);
lean::inc(x_3);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_yield__command___lambda__6), 3, 2);
lean::closure_set(x_10, 0, x_0);
lean::closure_set(x_10, 1, x_3);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_11, 0, x_8);
lean::closure_set(x_11, 1, x_10);
x_12 = l_lean_parser_monad__parsec_any___at___private_209794555__commands__aux___main___spec__3___closed__1;
lean::inc(x_12);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_14, 0, x_11);
lean::closure_set(x_14, 1, x_12);
return x_14;
}
}
obj* _init_l_lean_parser_monad__parsec_any___at___private_209794555__commands__aux___main___spec__3___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_id___rarg), 1, 0);
x_1 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_any___at___private_209794555__commands__aux___main___spec__3___lambda__2), 2, 1);
lean::closure_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_lean_parser_monad__parsec_any___at___private_209794555__commands__aux___main___spec__3___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_7; 
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
if (lean::obj_tag(x_3) == 0)
{
obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_8 = lean::cnstr_get(x_3, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_3, 1);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_3, 2);
lean::inc(x_12);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_14 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 1);
 lean::cnstr_release(x_3, 2);
 x_14 = x_3;
}
if (lean::is_scalar(x_7)) {
 x_15 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_15 = x_7;
}
lean::cnstr_set(x_15, 0, x_8);
lean::cnstr_set(x_15, 1, x_0);
if (lean::is_scalar(x_14)) {
 x_16 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_16 = x_14;
}
lean::cnstr_set(x_16, 0, x_15);
lean::cnstr_set(x_16, 1, x_10);
lean::cnstr_set(x_16, 2, x_1);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_5);
x_18 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_18, 0, x_17);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_yield__command___lambda__1), 2, 1);
lean::closure_set(x_19, 0, x_12);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_20, 0, x_18);
lean::closure_set(x_20, 1, x_19);
return x_20;
}
else
{
obj* x_23; uint8 x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
lean::dec(x_1);
lean::dec(x_0);
x_23 = lean::cnstr_get(x_3, 0);
lean::inc(x_23);
x_25 = lean::cnstr_get_scalar<uint8>(x_3, sizeof(void*)*1);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_26 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 x_26 = x_3;
}
if (lean::is_scalar(x_26)) {
 x_27 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_27 = x_26;
}
lean::cnstr_set(x_27, 0, x_23);
lean::cnstr_set_scalar(x_27, sizeof(void*)*1, x_25);
x_28 = x_27;
if (lean::is_scalar(x_7)) {
 x_29 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_29 = x_7;
}
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_5);
x_30 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_30, 0, x_29);
return x_30;
}
}
}
obj* l_lean_parser_monad__parsec_any___at___private_209794555__commands__aux___main___spec__3___lambda__2(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_6; 
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
if (lean::obj_tag(x_2) == 0)
{
obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_14; obj* x_16; obj* x_19; uint8 x_20; 
x_7 = lean::cnstr_get(x_2, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_2, 1);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_2, 2);
lean::inc(x_11);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_13 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 lean::cnstr_release(x_2, 1);
 lean::cnstr_release(x_2, 2);
 x_13 = x_2;
}
x_14 = lean::cnstr_get(x_7, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_7, 1);
lean::inc(x_16);
lean::dec(x_7);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_yield__command___lambda__1), 2, 1);
lean::closure_set(x_19, 0, x_11);
x_20 = lean::string_iterator_has_next(x_14);
if (x_20 == 0)
{
obj* x_25; obj* x_26; obj* x_27; obj* x_31; obj* x_32; 
lean::dec(x_14);
lean::dec(x_13);
lean::dec(x_6);
lean::dec(x_0);
x_25 = lean::box(0);
x_26 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_27 = l_mjoin___rarg___closed__1;
lean::inc(x_25);
lean::inc(x_27);
lean::inc(x_26);
x_31 = l_lean_parser_monad__parsec_error___at___private_209794555__commands__aux___main___spec__1___rarg(x_26, x_27, x_25, x_25, x_16, x_9, x_4);
x_32 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_32, 0, x_31);
lean::closure_set(x_32, 1, x_19);
return x_32;
}
else
{
uint32 x_33; uint8 x_34; 
x_33 = lean::string_iterator_curr(x_14);
x_34 = l_true_decidable;
if (x_34 == 0)
{
obj* x_39; obj* x_40; obj* x_42; obj* x_44; obj* x_45; obj* x_46; obj* x_49; obj* x_50; 
lean::dec(x_14);
lean::dec(x_13);
lean::dec(x_6);
lean::dec(x_0);
x_39 = l_char_quote__core(x_33);
x_40 = l_char_has__repr___closed__1;
lean::inc(x_40);
x_42 = lean::string_append(x_40, x_39);
lean::dec(x_39);
x_44 = lean::string_append(x_42, x_40);
x_45 = lean::box(0);
x_46 = l_mjoin___rarg___closed__1;
lean::inc(x_45);
lean::inc(x_46);
x_49 = l_lean_parser_monad__parsec_error___at___private_209794555__commands__aux___main___spec__1___rarg(x_44, x_46, x_45, x_45, x_16, x_9, x_4);
x_50 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_50, 0, x_49);
lean::closure_set(x_50, 1, x_19);
return x_50;
}
else
{
obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; 
lean::dec(x_9);
x_52 = lean::string_iterator_next(x_14);
x_53 = lean::box(0);
x_54 = lean::box_uint32(x_33);
if (lean::is_scalar(x_13)) {
 x_55 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_55 = x_13;
}
lean::cnstr_set(x_55, 0, x_54);
lean::cnstr_set(x_55, 1, x_52);
lean::cnstr_set(x_55, 2, x_53);
if (lean::is_scalar(x_6)) {
 x_56 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_56 = x_6;
}
lean::cnstr_set(x_56, 0, x_55);
lean::cnstr_set(x_56, 1, x_4);
x_57 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_57, 0, x_56);
x_58 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_any___at___private_209794555__commands__aux___main___spec__3___lambda__1), 3, 2);
lean::closure_set(x_58, 0, x_16);
lean::closure_set(x_58, 1, x_0);
x_59 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_59, 0, x_57);
lean::closure_set(x_59, 1, x_58);
x_60 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_60, 0, x_59);
lean::closure_set(x_60, 1, x_19);
return x_60;
}
}
}
else
{
obj* x_62; uint8 x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; 
lean::dec(x_0);
x_62 = lean::cnstr_get(x_2, 0);
lean::inc(x_62);
x_64 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*1);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_65 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 x_65 = x_2;
}
if (lean::is_scalar(x_65)) {
 x_66 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_66 = x_65;
}
lean::cnstr_set(x_66, 0, x_62);
lean::cnstr_set_scalar(x_66, sizeof(void*)*1, x_64);
x_67 = x_66;
if (lean::is_scalar(x_6)) {
 x_68 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_68 = x_6;
}
lean::cnstr_set(x_68, 0, x_67);
lean::cnstr_set(x_68, 1, x_4);
x_69 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_69, 0, x_68);
return x_69;
}
}
}
obj* l_lean_parser_log__message___at___private_209794555__commands__aux___main___spec__4(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_yield__command___lambda__4), 2, 1);
lean::closure_set(x_4, 0, x_3);
x_5 = l_lean_parser_module__parser__m_lift__parser__t___rarg___closed__1;
lean::inc(x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_7, 0, x_5);
lean::closure_set(x_7, 1, x_4);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_log__message___at___private_209794555__commands__aux___main___spec__4___lambda__1), 2, 1);
lean::closure_set(x_8, 0, x_2);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_9, 0, x_7);
lean::closure_set(x_9, 1, x_8);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___at___private_209794555__commands__aux___main___spec__1___rarg___lambda__1), 2, 1);
lean::closure_set(x_10, 0, x_1);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_11, 0, x_9);
lean::closure_set(x_11, 1, x_10);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_log__message___at___private_209794555__commands__aux___main___spec__4___lambda__2), 2, 1);
lean::closure_set(x_12, 0, x_0);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_13, 0, x_11);
lean::closure_set(x_13, 1, x_12);
return x_13;
}
}
obj* l_lean_parser_log__message___at___private_209794555__commands__aux___main___spec__4___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_6; obj* x_7; obj* x_9; obj* x_10; obj* x_11; 
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
x_7 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_7);
x_9 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_9, 0, x_2);
lean::cnstr_set(x_9, 1, x_0);
lean::cnstr_set(x_9, 2, x_7);
if (lean::is_scalar(x_6)) {
 x_10 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_10 = x_6;
}
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_4);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_11, 0, x_10);
return x_11;
}
}
obj* l_lean_parser_log__message___at___private_209794555__commands__aux___main___spec__4___lambda__2(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_6; 
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
if (lean::obj_tag(x_2) == 0)
{
obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_14; obj* x_16; obj* x_18; obj* x_19; obj* x_20; obj* x_23; obj* x_26; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
x_7 = lean::cnstr_get(x_2, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_2, 1);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_2, 2);
lean::inc(x_11);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_13 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 lean::cnstr_release(x_2, 1);
 lean::cnstr_release(x_2, 2);
 x_13 = x_2;
}
x_14 = lean::cnstr_get(x_7, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_7, 1);
lean::inc(x_16);
if (lean::is_shared(x_7)) {
 lean::dec(x_7);
 x_18 = lean::box(0);
} else {
 lean::cnstr_release(x_7, 0);
 lean::cnstr_release(x_7, 1);
 x_18 = x_7;
}
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_yield__command___lambda__1), 2, 1);
lean::closure_set(x_19, 0, x_11);
x_20 = lean::cnstr_get(x_14, 0);
lean::inc(x_20);
lean::dec(x_14);
x_23 = lean::cnstr_get(x_20, 0);
lean::inc(x_23);
lean::dec(x_20);
x_26 = lean::cnstr_get(x_23, 0);
lean::inc(x_26);
lean::dec(x_23);
x_29 = l_lean_parser_message__of__parsec__message___rarg(x_26, x_0);
x_30 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_16);
x_31 = lean::box(0);
if (lean::is_scalar(x_6)) {
 x_32 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_32 = x_6;
}
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_30);
x_33 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_33);
if (lean::is_scalar(x_13)) {
 x_35 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_35 = x_13;
}
lean::cnstr_set(x_35, 0, x_32);
lean::cnstr_set(x_35, 1, x_9);
lean::cnstr_set(x_35, 2, x_33);
if (lean::is_scalar(x_18)) {
 x_36 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_36 = x_18;
}
lean::cnstr_set(x_36, 0, x_35);
lean::cnstr_set(x_36, 1, x_4);
x_37 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_37, 0, x_36);
x_38 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_38, 0, x_37);
lean::closure_set(x_38, 1, x_19);
return x_38;
}
else
{
obj* x_40; uint8 x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; 
lean::dec(x_0);
x_40 = lean::cnstr_get(x_2, 0);
lean::inc(x_40);
x_42 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*1);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_43 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 x_43 = x_2;
}
if (lean::is_scalar(x_43)) {
 x_44 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_44 = x_43;
}
lean::cnstr_set(x_44, 0, x_40);
lean::cnstr_set_scalar(x_44, sizeof(void*)*1, x_42);
x_45 = x_44;
if (lean::is_scalar(x_6)) {
 x_46 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_46 = x_6;
}
lean::cnstr_set(x_46, 0, x_45);
lean::cnstr_set(x_46, 1, x_4);
x_47 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_47, 0, x_46);
return x_47;
}
}
}
obj* l_lean_parser_log__message___at___private_209794555__commands__aux___main___spec__5(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_yield__command___lambda__4), 2, 1);
lean::closure_set(x_4, 0, x_3);
x_5 = l_lean_parser_module__parser__m_lift__parser__t___rarg___closed__1;
lean::inc(x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_7, 0, x_5);
lean::closure_set(x_7, 1, x_4);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_log__message___at___private_209794555__commands__aux___main___spec__4___lambda__1), 2, 1);
lean::closure_set(x_8, 0, x_2);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_9, 0, x_7);
lean::closure_set(x_9, 1, x_8);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___at___private_209794555__commands__aux___main___spec__1___rarg___lambda__1), 2, 1);
lean::closure_set(x_10, 0, x_1);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_11, 0, x_9);
lean::closure_set(x_11, 1, x_10);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_log__message___at___private_209794555__commands__aux___main___spec__4___lambda__2), 2, 1);
lean::closure_set(x_12, 0, x_0);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_13, 0, x_11);
lean::closure_set(x_13, 1, x_12);
return x_13;
}
}
obj* l___private_209794555__commands__aux___main(uint8 x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::mk_nat_obj(0u);
x_6 = lean::nat_dec_eq(x_1, x_5);
lean::dec(x_5);
if (x_6 == 0)
{
obj* x_8; obj* x_9; obj* x_14; 
x_8 = lean::mk_nat_obj(1u);
x_9 = lean::nat_sub(x_1, x_8);
lean::dec(x_8);
lean::dec(x_1);
lean::inc(x_3);
lean::inc(x_2);
x_14 = l_lean_parser_monad__parsec_eoi___at___private_209794555__commands__aux___main___spec__2(x_2, x_3, x_4);
if (x_0 == 0)
{
uint8 x_15; obj* x_16; obj* x_17; obj* x_19; obj* x_20; 
x_15 = 1;
x_16 = lean::box(x_15);
x_17 = l_lean_parser_module__parser__m_lift__parser__t___rarg___closed__1;
lean::inc(x_17);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l___private_209794555__commands__aux___main___lambda__19), 6, 5);
lean::closure_set(x_19, 0, x_17);
lean::closure_set(x_19, 1, x_3);
lean::closure_set(x_19, 2, x_2);
lean::closure_set(x_19, 3, x_16);
lean::closure_set(x_19, 4, x_9);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_20, 0, x_14);
lean::closure_set(x_20, 1, x_19);
return x_20;
}
else
{
uint8 x_21; obj* x_22; obj* x_23; obj* x_25; obj* x_26; 
x_21 = 0;
x_22 = lean::box(x_21);
x_23 = l_lean_parser_module__parser__m_lift__parser__t___rarg___closed__1;
lean::inc(x_23);
x_25 = lean::alloc_closure(reinterpret_cast<void*>(l___private_209794555__commands__aux___main___lambda__19), 6, 5);
lean::closure_set(x_25, 0, x_23);
lean::closure_set(x_25, 1, x_3);
lean::closure_set(x_25, 2, x_2);
lean::closure_set(x_25, 3, x_22);
lean::closure_set(x_25, 4, x_9);
x_26 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_26, 0, x_14);
lean::closure_set(x_26, 1, x_25);
return x_26;
}
}
else
{
obj* x_28; obj* x_29; obj* x_30; obj* x_34; 
lean::dec(x_1);
x_28 = lean::box(0);
x_29 = l___private_1297690757__many1__aux___main___rarg___closed__1;
x_30 = l_mjoin___rarg___closed__1;
lean::inc(x_28);
lean::inc(x_30);
lean::inc(x_29);
x_34 = l_lean_parser_monad__parsec_error___at___private_209794555__commands__aux___main___spec__1___rarg(x_29, x_30, x_28, x_28, x_2, x_3, x_4);
return x_34;
}
}
}
obj* l___private_209794555__commands__aux___main___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_8; obj* x_10; obj* x_11; obj* x_13; obj* x_15; 
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
lean::dec(x_4);
x_8 = l___private_209794555__commands__aux___main___lambda__1___closed__1;
lean::inc(x_8);
x_10 = l_lean_parser_command__parser_run(x_0, x_8, x_5, x_1, x_2);
x_11 = lean::cnstr_get(x_10, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_10, 1);
lean::inc(x_13);
if (lean::is_shared(x_10)) {
 lean::dec(x_10);
 x_15 = lean::box(0);
} else {
 lean::cnstr_release(x_10, 0);
 lean::cnstr_release(x_10, 1);
 x_15 = x_10;
}
if (lean::obj_tag(x_11) == 0)
{
obj* x_16; obj* x_18; obj* x_20; obj* x_22; obj* x_23; obj* x_24; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
x_16 = lean::cnstr_get(x_11, 0);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_11, 1);
lean::inc(x_18);
x_20 = lean::cnstr_get(x_11, 2);
lean::inc(x_20);
if (lean::is_shared(x_11)) {
 lean::dec(x_11);
 x_22 = lean::box(0);
} else {
 lean::cnstr_release(x_11, 0);
 lean::cnstr_release(x_11, 1);
 lean::cnstr_release(x_11, 2);
 x_22 = x_11;
}
if (lean::is_scalar(x_15)) {
 x_23 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_23 = x_15;
}
lean::cnstr_set(x_23, 0, x_16);
lean::cnstr_set(x_23, 1, x_3);
x_24 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_24);
if (lean::is_scalar(x_22)) {
 x_26 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_26 = x_22;
}
lean::cnstr_set(x_26, 0, x_23);
lean::cnstr_set(x_26, 1, x_18);
lean::cnstr_set(x_26, 2, x_24);
x_27 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_20, x_26);
x_28 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_13);
x_29 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_29, 0, x_28);
return x_29;
}
else
{
obj* x_31; uint8 x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
lean::dec(x_3);
x_31 = lean::cnstr_get(x_11, 0);
lean::inc(x_31);
x_33 = lean::cnstr_get_scalar<uint8>(x_11, sizeof(void*)*1);
if (lean::is_shared(x_11)) {
 lean::dec(x_11);
 x_34 = lean::box(0);
} else {
 lean::cnstr_release(x_11, 0);
 x_34 = x_11;
}
if (lean::is_scalar(x_34)) {
 x_35 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_35 = x_34;
}
lean::cnstr_set(x_35, 0, x_31);
lean::cnstr_set_scalar(x_35, sizeof(void*)*1, x_33);
x_36 = x_35;
if (lean::is_scalar(x_15)) {
 x_37 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_37 = x_15;
}
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_13);
x_38 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_38, 0, x_37);
return x_38;
}
}
}
obj* _init_l___private_209794555__commands__aux___main___lambda__1___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_parser), 1, 0);
return x_0;
}
}
obj* l___private_209794555__commands__aux___main___lambda__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_5; 
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
if (lean::obj_tag(x_1) == 0)
{
obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_13; obj* x_15; obj* x_17; obj* x_18; obj* x_19; uint8 x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 1);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_1, 2);
lean::inc(x_10);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_12 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 lean::cnstr_release(x_1, 2);
 x_12 = x_1;
}
x_13 = lean::cnstr_get(x_6, 0);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_6, 1);
lean::inc(x_15);
if (lean::is_shared(x_6)) {
 lean::dec(x_6);
 x_17 = lean::box(0);
} else {
 lean::cnstr_release(x_6, 0);
 lean::cnstr_release(x_6, 1);
 x_17 = x_6;
}
x_18 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_yield__command___lambda__1), 2, 1);
lean::closure_set(x_18, 0, x_10);
x_19 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_19, 0, x_13);
x_20 = 0;
x_21 = lean::box(x_20);
if (lean::is_scalar(x_5)) {
 x_22 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_22 = x_5;
}
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_19);
if (lean::is_scalar(x_17)) {
 x_23 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_23 = x_17;
}
lean::cnstr_set(x_23, 0, x_22);
lean::cnstr_set(x_23, 1, x_15);
x_24 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_24);
if (lean::is_scalar(x_12)) {
 x_26 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_26 = x_12;
}
lean::cnstr_set(x_26, 0, x_23);
lean::cnstr_set(x_26, 1, x_8);
lean::cnstr_set(x_26, 2, x_24);
x_27 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_3);
x_28 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_28, 0, x_27);
x_29 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_29, 0, x_28);
lean::closure_set(x_29, 1, x_18);
return x_29;
}
else
{
obj* x_30; uint8 x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; 
x_30 = lean::cnstr_get(x_1, 0);
lean::inc(x_30);
x_32 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*1);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_33 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 x_33 = x_1;
}
if (lean::is_scalar(x_33)) {
 x_34 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_34 = x_33;
}
lean::cnstr_set(x_34, 0, x_30);
lean::cnstr_set_scalar(x_34, sizeof(void*)*1, x_32);
x_35 = x_34;
if (lean::is_scalar(x_5)) {
 x_36 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_36 = x_5;
}
lean::cnstr_set(x_36, 0, x_35);
lean::cnstr_set(x_36, 1, x_3);
x_37 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_37, 0, x_36);
return x_37;
}
}
}
obj* l___private_209794555__commands__aux___main___lambda__3(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_6; 
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
if (lean::obj_tag(x_2) == 0)
{
obj* x_8; obj* x_10; obj* x_12; obj* x_15; obj* x_17; obj* x_20; obj* x_21; obj* x_24; obj* x_25; obj* x_26; obj* x_28; obj* x_29; 
lean::dec(x_6);
x_8 = lean::cnstr_get(x_2, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_2, 1);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_2, 2);
lean::inc(x_12);
lean::dec(x_2);
x_15 = lean::cnstr_get(x_8, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_8, 1);
lean::inc(x_17);
lean::dec(x_8);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_yield__command___lambda__1), 2, 1);
lean::closure_set(x_20, 0, x_12);
x_21 = lean::cnstr_get(x_15, 1);
lean::inc(x_21);
lean::dec(x_15);
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l___private_209794555__commands__aux___main___lambda__1), 5, 4);
lean::closure_set(x_24, 0, x_21);
lean::closure_set(x_24, 1, x_10);
lean::closure_set(x_24, 2, x_4);
lean::closure_set(x_24, 3, x_17);
x_25 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_25, 0, x_0);
lean::closure_set(x_25, 1, x_24);
x_26 = l___private_209794555__commands__aux___main___lambda__3___closed__1;
lean::inc(x_26);
x_28 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_28, 0, x_25);
lean::closure_set(x_28, 1, x_26);
x_29 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_29, 0, x_28);
lean::closure_set(x_29, 1, x_20);
return x_29;
}
else
{
obj* x_31; uint8 x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
lean::dec(x_0);
x_31 = lean::cnstr_get(x_2, 0);
lean::inc(x_31);
x_33 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*1);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_34 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 x_34 = x_2;
}
if (lean::is_scalar(x_34)) {
 x_35 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_35 = x_34;
}
lean::cnstr_set(x_35, 0, x_31);
lean::cnstr_set_scalar(x_35, sizeof(void*)*1, x_33);
x_36 = x_35;
if (lean::is_scalar(x_6)) {
 x_37 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_37 = x_6;
}
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_4);
x_38 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_38, 0, x_37);
return x_38;
}
}
}
obj* _init_l___private_209794555__commands__aux___main___lambda__3___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l___private_209794555__commands__aux___main___lambda__2), 1, 0);
return x_0;
}
}
obj* l___private_209794555__commands__aux___main___lambda__4(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_7; obj* x_10; obj* x_11; obj* x_13; obj* x_15; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
lean::dec(x_3);
x_7 = lean::cnstr_get(x_4, 0);
lean::inc(x_7);
lean::dec(x_4);
x_10 = l_lean_parser_token(x_7, x_0, x_1);
x_11 = lean::cnstr_get(x_10, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_10, 1);
lean::inc(x_13);
if (lean::is_shared(x_10)) {
 lean::dec(x_10);
 x_15 = lean::box(0);
} else {
 lean::cnstr_release(x_10, 0);
 lean::cnstr_release(x_10, 1);
 x_15 = x_10;
}
if (lean::obj_tag(x_11) == 0)
{
obj* x_16; obj* x_18; obj* x_20; obj* x_22; obj* x_23; obj* x_24; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
x_16 = lean::cnstr_get(x_11, 0);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_11, 1);
lean::inc(x_18);
x_20 = lean::cnstr_get(x_11, 2);
lean::inc(x_20);
if (lean::is_shared(x_11)) {
 lean::dec(x_11);
 x_22 = lean::box(0);
} else {
 lean::cnstr_release(x_11, 0);
 lean::cnstr_release(x_11, 1);
 lean::cnstr_release(x_11, 2);
 x_22 = x_11;
}
if (lean::is_scalar(x_15)) {
 x_23 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_23 = x_15;
}
lean::cnstr_set(x_23, 0, x_16);
lean::cnstr_set(x_23, 1, x_2);
x_24 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_24);
if (lean::is_scalar(x_22)) {
 x_26 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_26 = x_22;
}
lean::cnstr_set(x_26, 0, x_23);
lean::cnstr_set(x_26, 1, x_18);
lean::cnstr_set(x_26, 2, x_24);
x_27 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_20, x_26);
x_28 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_13);
x_29 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_29, 0, x_28);
return x_29;
}
else
{
obj* x_31; uint8 x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
lean::dec(x_2);
x_31 = lean::cnstr_get(x_11, 0);
lean::inc(x_31);
x_33 = lean::cnstr_get_scalar<uint8>(x_11, sizeof(void*)*1);
if (lean::is_shared(x_11)) {
 lean::dec(x_11);
 x_34 = lean::box(0);
} else {
 lean::cnstr_release(x_11, 0);
 x_34 = x_11;
}
if (lean::is_scalar(x_34)) {
 x_35 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_35 = x_34;
}
lean::cnstr_set(x_35, 0, x_31);
lean::cnstr_set_scalar(x_35, sizeof(void*)*1, x_33);
x_36 = x_35;
if (lean::is_scalar(x_15)) {
 x_37 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_37 = x_15;
}
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_13);
x_38 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_38, 0, x_37);
return x_38;
}
}
}
obj* l___private_209794555__commands__aux___main___lambda__5(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_5; 
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
if (lean::obj_tag(x_1) == 0)
{
obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_13; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 1);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_1, 2);
lean::inc(x_10);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_12 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 lean::cnstr_release(x_1, 2);
 x_12 = x_1;
}
x_13 = lean::cnstr_get(x_6, 1);
lean::inc(x_13);
if (lean::is_shared(x_6)) {
 lean::dec(x_6);
 x_15 = lean::box(0);
} else {
 lean::cnstr_release(x_6, 0);
 lean::cnstr_release(x_6, 1);
 x_15 = x_6;
}
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_yield__command___lambda__1), 2, 1);
lean::closure_set(x_16, 0, x_10);
x_17 = lean::box(0);
if (lean::is_scalar(x_5)) {
 x_18 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_18 = x_5;
}
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_13);
x_19 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_19);
if (lean::is_scalar(x_12)) {
 x_21 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_21 = x_12;
}
lean::cnstr_set(x_21, 0, x_18);
lean::cnstr_set(x_21, 1, x_8);
lean::cnstr_set(x_21, 2, x_19);
if (lean::is_scalar(x_15)) {
 x_22 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_22 = x_15;
}
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_3);
x_23 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_23, 0, x_22);
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_24, 0, x_23);
lean::closure_set(x_24, 1, x_16);
return x_24;
}
else
{
obj* x_25; uint8 x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; 
x_25 = lean::cnstr_get(x_1, 0);
lean::inc(x_25);
x_27 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*1);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_28 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 x_28 = x_1;
}
if (lean::is_scalar(x_28)) {
 x_29 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_29 = x_28;
}
lean::cnstr_set(x_29, 0, x_25);
lean::cnstr_set_scalar(x_29, sizeof(void*)*1, x_27);
x_30 = x_29;
if (lean::is_scalar(x_5)) {
 x_31 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_31 = x_5;
}
lean::cnstr_set(x_31, 0, x_30);
lean::cnstr_set(x_31, 1, x_3);
x_32 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_32, 0, x_31);
return x_32;
}
}
}
obj* l___private_209794555__commands__aux___main___lambda__6(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
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
x_6 = l_lean_parser_parsec__t_try__mk__res___rarg(x_1);
if (lean::is_scalar(x_5)) {
 x_7 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_7 = x_5;
}
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_3);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_8, 0, x_7);
return x_8;
}
}
obj* l___private_209794555__commands__aux___main___lambda__7(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_5; 
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
if (lean::obj_tag(x_1) == 0)
{
obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_13; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 1);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_1, 2);
lean::inc(x_10);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_12 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 lean::cnstr_release(x_1, 2);
 x_12 = x_1;
}
x_13 = lean::cnstr_get(x_6, 1);
lean::inc(x_13);
if (lean::is_shared(x_6)) {
 lean::dec(x_6);
 x_15 = lean::box(0);
} else {
 lean::cnstr_release(x_6, 0);
 lean::cnstr_release(x_6, 1);
 x_15 = x_6;
}
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_yield__command___lambda__1), 2, 1);
lean::closure_set(x_16, 0, x_10);
x_17 = lean::box(0);
if (lean::is_scalar(x_5)) {
 x_18 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_18 = x_5;
}
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_13);
x_19 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_19);
if (lean::is_scalar(x_12)) {
 x_21 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_21 = x_12;
}
lean::cnstr_set(x_21, 0, x_18);
lean::cnstr_set(x_21, 1, x_8);
lean::cnstr_set(x_21, 2, x_19);
if (lean::is_scalar(x_15)) {
 x_22 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_22 = x_15;
}
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_3);
x_23 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_23, 0, x_22);
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_24, 0, x_23);
lean::closure_set(x_24, 1, x_16);
return x_24;
}
else
{
obj* x_25; uint8 x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; 
x_25 = lean::cnstr_get(x_1, 0);
lean::inc(x_25);
x_27 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*1);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_28 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 x_28 = x_1;
}
if (lean::is_scalar(x_28)) {
 x_29 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_29 = x_28;
}
lean::cnstr_set(x_29, 0, x_25);
lean::cnstr_set_scalar(x_29, sizeof(void*)*1, x_27);
x_30 = x_29;
if (lean::is_scalar(x_5)) {
 x_31 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_31 = x_5;
}
lean::cnstr_set(x_31, 0, x_30);
lean::cnstr_set(x_31, 1, x_3);
x_32 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_32, 0, x_31);
return x_32;
}
}
}
obj* l___private_209794555__commands__aux___main___lambda__8(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
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
x_7 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_0, x_2);
if (lean::is_scalar(x_6)) {
 x_8 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_8 = x_6;
}
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_4);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_9, 0, x_8);
return x_9;
}
}
obj* l___private_209794555__commands__aux___main___lambda__9(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_7; 
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
if (lean::obj_tag(x_3) == 0)
{
obj* x_10; obj* x_11; 
lean::dec(x_1);
lean::dec(x_0);
if (lean::is_scalar(x_7)) {
 x_10 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_10 = x_7;
}
lean::cnstr_set(x_10, 0, x_3);
lean::cnstr_set(x_10, 1, x_5);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_11, 0, x_10);
return x_11;
}
else
{
obj* x_12; uint8 x_14; 
x_12 = lean::cnstr_get(x_3, 0);
lean::inc(x_12);
x_14 = lean::cnstr_get_scalar<uint8>(x_3, sizeof(void*)*1);
if (x_14 == 0)
{
obj* x_17; obj* x_18; obj* x_20; obj* x_21; obj* x_22; 
lean::dec(x_7);
lean::dec(x_3);
x_17 = l_lean_parser_monad__parsec_any___at___private_209794555__commands__aux___main___spec__3(x_0, x_1, x_5);
x_18 = l___private_209794555__commands__aux___main___lambda__9___closed__1;
lean::inc(x_18);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_20, 0, x_17);
lean::closure_set(x_20, 1, x_18);
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l___private_209794555__commands__aux___main___lambda__8), 2, 1);
lean::closure_set(x_21, 0, x_12);
x_22 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_22, 0, x_20);
lean::closure_set(x_22, 1, x_21);
return x_22;
}
else
{
obj* x_26; obj* x_27; 
lean::dec(x_12);
lean::dec(x_1);
lean::dec(x_0);
if (lean::is_scalar(x_7)) {
 x_26 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_26 = x_7;
}
lean::cnstr_set(x_26, 0, x_3);
lean::cnstr_set(x_26, 1, x_5);
x_27 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_27, 0, x_26);
return x_27;
}
}
}
}
obj* _init_l___private_209794555__commands__aux___main___lambda__9___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l___private_209794555__commands__aux___main___lambda__7), 1, 0);
return x_0;
}
}
obj* l___private_209794555__commands__aux___main___lambda__10(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_5; 
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
if (lean::obj_tag(x_1) == 0)
{
obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_13; obj* x_15; obj* x_16; obj* x_17; obj* x_19; obj* x_20; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 1);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_1, 2);
lean::inc(x_10);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_12 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 lean::cnstr_release(x_1, 2);
 x_12 = x_1;
}
x_13 = lean::cnstr_get(x_6, 1);
lean::inc(x_13);
if (lean::is_shared(x_6)) {
 lean::dec(x_6);
 x_15 = lean::box(0);
} else {
 lean::cnstr_release(x_6, 0);
 lean::cnstr_release(x_6, 1);
 x_15 = x_6;
}
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_yield__command___lambda__1), 2, 1);
lean::closure_set(x_16, 0, x_10);
x_17 = l___private_209794555__commands__aux___main___lambda__10___closed__1;
lean::inc(x_17);
if (lean::is_scalar(x_5)) {
 x_19 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_19 = x_5;
}
lean::cnstr_set(x_19, 0, x_17);
lean::cnstr_set(x_19, 1, x_13);
x_20 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_20);
if (lean::is_scalar(x_12)) {
 x_22 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_22 = x_12;
}
lean::cnstr_set(x_22, 0, x_19);
lean::cnstr_set(x_22, 1, x_8);
lean::cnstr_set(x_22, 2, x_20);
if (lean::is_scalar(x_15)) {
 x_23 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_23 = x_15;
}
lean::cnstr_set(x_23, 0, x_22);
lean::cnstr_set(x_23, 1, x_3);
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_24, 0, x_23);
x_25 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_25, 0, x_24);
lean::closure_set(x_25, 1, x_16);
return x_25;
}
else
{
obj* x_26; uint8 x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; 
x_26 = lean::cnstr_get(x_1, 0);
lean::inc(x_26);
x_28 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*1);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_29 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 x_29 = x_1;
}
if (lean::is_scalar(x_29)) {
 x_30 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_30 = x_29;
}
lean::cnstr_set(x_30, 0, x_26);
lean::cnstr_set_scalar(x_30, sizeof(void*)*1, x_28);
x_31 = x_30;
if (lean::is_scalar(x_5)) {
 x_32 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_32 = x_5;
}
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_3);
x_33 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_33, 0, x_32);
return x_33;
}
}
}
obj* _init_l___private_209794555__commands__aux___main___lambda__10___closed__1() {
_start:
{
obj* x_0; uint8 x_1; obj* x_2; obj* x_3; 
x_0 = lean::box(0);
x_1 = 1;
x_2 = lean::box(x_1);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_2);
lean::cnstr_set(x_3, 1, x_0);
return x_3;
}
}
obj* l___private_209794555__commands__aux___main___lambda__11(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_6; 
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
if (lean::obj_tag(x_2) == 0)
{
obj* x_8; obj* x_10; obj* x_12; obj* x_15; obj* x_18; obj* x_21; obj* x_22; obj* x_23; obj* x_25; obj* x_26; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_33; obj* x_34; 
lean::dec(x_6);
x_8 = lean::cnstr_get(x_2, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_2, 1);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_2, 2);
lean::inc(x_12);
lean::dec(x_2);
x_15 = lean::cnstr_get(x_8, 1);
lean::inc(x_15);
lean::dec(x_8);
x_18 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_yield__command___lambda__1), 2, 1);
lean::closure_set(x_18, 0, x_12);
lean::inc(x_15);
lean::inc(x_10);
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l___private_209794555__commands__aux___main___lambda__4), 4, 3);
lean::closure_set(x_21, 0, x_10);
lean::closure_set(x_21, 1, x_4);
lean::closure_set(x_21, 2, x_15);
x_22 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_22, 0, x_0);
lean::closure_set(x_22, 1, x_21);
x_23 = l___private_209794555__commands__aux___main___lambda__11___closed__1;
lean::inc(x_23);
x_25 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_25, 0, x_22);
lean::closure_set(x_25, 1, x_23);
x_26 = l___private_209794555__commands__aux___main___lambda__11___closed__2;
lean::inc(x_26);
x_28 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_28, 0, x_25);
lean::closure_set(x_28, 1, x_26);
x_29 = lean::alloc_closure(reinterpret_cast<void*>(l___private_209794555__commands__aux___main___lambda__9), 3, 2);
lean::closure_set(x_29, 0, x_15);
lean::closure_set(x_29, 1, x_10);
x_30 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_30, 0, x_28);
lean::closure_set(x_30, 1, x_29);
x_31 = l___private_209794555__commands__aux___main___lambda__11___closed__3;
lean::inc(x_31);
x_33 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_33, 0, x_30);
lean::closure_set(x_33, 1, x_31);
x_34 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_34, 0, x_33);
lean::closure_set(x_34, 1, x_18);
return x_34;
}
else
{
obj* x_36; uint8 x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; 
lean::dec(x_0);
x_36 = lean::cnstr_get(x_2, 0);
lean::inc(x_36);
x_38 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*1);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_39 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 x_39 = x_2;
}
if (lean::is_scalar(x_39)) {
 x_40 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_40 = x_39;
}
lean::cnstr_set(x_40, 0, x_36);
lean::cnstr_set_scalar(x_40, sizeof(void*)*1, x_38);
x_41 = x_40;
if (lean::is_scalar(x_6)) {
 x_42 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_42 = x_6;
}
lean::cnstr_set(x_42, 0, x_41);
lean::cnstr_set(x_42, 1, x_4);
x_43 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_43, 0, x_42);
return x_43;
}
}
}
obj* _init_l___private_209794555__commands__aux___main___lambda__11___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l___private_209794555__commands__aux___main___lambda__5), 1, 0);
return x_0;
}
}
obj* _init_l___private_209794555__commands__aux___main___lambda__11___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l___private_209794555__commands__aux___main___lambda__6), 1, 0);
return x_0;
}
}
obj* _init_l___private_209794555__commands__aux___main___lambda__11___closed__3() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l___private_209794555__commands__aux___main___lambda__10), 1, 0);
return x_0;
}
}
obj* l___private_209794555__commands__aux___main___lambda__12(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_5; 
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
if (lean::obj_tag(x_1) == 0)
{
obj* x_7; obj* x_9; obj* x_11; obj* x_14; obj* x_16; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_26; obj* x_27; obj* x_28; 
lean::dec(x_5);
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_1, 1);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_1, 2);
lean::inc(x_11);
lean::dec(x_1);
x_14 = lean::cnstr_get(x_7, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_7, 1);
lean::inc(x_16);
lean::dec(x_7);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_yield__command___lambda__1), 2, 1);
lean::closure_set(x_19, 0, x_11);
x_20 = l_string_join___closed__1;
x_21 = l_lean_parser_command_parser___rarg___closed__1;
x_22 = l_lean_parser_parsec__t_monad__fail___rarg___closed__1;
lean::inc(x_22);
lean::inc(x_21);
lean::inc(x_20);
x_26 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_26, 0, x_14);
lean::cnstr_set(x_26, 1, x_20);
lean::cnstr_set(x_26, 2, x_21);
lean::cnstr_set(x_26, 3, x_22);
x_27 = l_lean_parser_log__message___at___private_209794555__commands__aux___main___spec__4(x_26, x_16, x_9, x_3);
x_28 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_28, 0, x_27);
lean::closure_set(x_28, 1, x_19);
return x_28;
}
else
{
obj* x_29; uint8 x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; 
x_29 = lean::cnstr_get(x_1, 0);
lean::inc(x_29);
x_31 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*1);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_32 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 x_32 = x_1;
}
if (lean::is_scalar(x_32)) {
 x_33 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_33 = x_32;
}
lean::cnstr_set(x_33, 0, x_29);
lean::cnstr_set_scalar(x_33, sizeof(void*)*1, x_31);
x_34 = x_33;
if (lean::is_scalar(x_5)) {
 x_35 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_35 = x_5;
}
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_3);
x_36 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_36, 0, x_35);
return x_36;
}
}
}
obj* l___private_209794555__commands__aux___main___lambda__13(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_7; obj* x_9; 
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
if (lean::obj_tag(x_5) == 0)
{
obj* x_14; obj* x_15; 
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
if (lean::is_scalar(x_9)) {
 x_14 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_14 = x_9;
}
lean::cnstr_set(x_14, 0, x_5);
lean::cnstr_set(x_14, 1, x_7);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_15, 0, x_14);
return x_15;
}
else
{
obj* x_16; uint8 x_18; 
x_16 = lean::cnstr_get(x_5, 0);
lean::inc(x_16);
x_18 = lean::cnstr_get_scalar<uint8>(x_5, sizeof(void*)*1);
if (x_18 == 0)
{
obj* x_20; obj* x_21; uint8 x_22; 
lean::dec(x_5);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l___private_209794555__commands__aux___main___lambda__11), 2, 1);
lean::closure_set(x_20, 0, x_0);
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l___private_209794555__commands__aux___main___lambda__8), 2, 1);
lean::closure_set(x_21, 0, x_16);
x_22 = lean::unbox(x_1);
lean::dec(x_1);
if (x_22 == 0)
{
obj* x_24; obj* x_25; obj* x_26; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; 
x_24 = lean::box(0);
if (lean::is_scalar(x_9)) {
 x_25 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_25 = x_9;
}
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_2);
x_26 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_26);
x_28 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_28, 0, x_25);
lean::cnstr_set(x_28, 1, x_3);
lean::cnstr_set(x_28, 2, x_26);
x_29 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_7);
x_30 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_30, 0, x_29);
x_31 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_31, 0, x_30);
lean::closure_set(x_31, 1, x_20);
x_32 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_32, 0, x_31);
lean::closure_set(x_32, 1, x_21);
return x_32;
}
else
{
obj* x_33; obj* x_36; obj* x_37; obj* x_38; obj* x_40; obj* x_41; obj* x_42; obj* x_44; obj* x_45; obj* x_46; 
x_33 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_33);
lean::inc(x_3);
x_36 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_36, 0, x_3);
lean::cnstr_set(x_36, 1, x_3);
lean::cnstr_set(x_36, 2, x_33);
if (lean::is_scalar(x_9)) {
 x_37 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_37 = x_9;
}
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_7);
x_38 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_38, 0, x_37);
lean::inc(x_33);
x_40 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_yield__command___lambda__6), 3, 2);
lean::closure_set(x_40, 0, x_2);
lean::closure_set(x_40, 1, x_33);
x_41 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_41, 0, x_38);
lean::closure_set(x_41, 1, x_40);
x_42 = l___private_209794555__commands__aux___main___lambda__13___closed__1;
lean::inc(x_42);
x_44 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_44, 0, x_41);
lean::closure_set(x_44, 1, x_42);
x_45 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_45, 0, x_44);
lean::closure_set(x_45, 1, x_20);
x_46 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_46, 0, x_45);
lean::closure_set(x_46, 1, x_21);
return x_46;
}
}
else
{
obj* x_52; obj* x_53; 
lean::dec(x_16);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
if (lean::is_scalar(x_9)) {
 x_52 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_52 = x_9;
}
lean::cnstr_set(x_52, 0, x_5);
lean::cnstr_set(x_52, 1, x_7);
x_53 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_53, 0, x_52);
return x_53;
}
}
}
}
obj* _init_l___private_209794555__commands__aux___main___lambda__13___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l___private_209794555__commands__aux___main___lambda__12), 1, 0);
return x_0;
}
}
obj* l___private_209794555__commands__aux___main___lambda__14(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_6; 
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
if (lean::obj_tag(x_2) == 0)
{
obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_14; obj* x_16; obj* x_17; obj* x_18; obj* x_21; obj* x_22; uint8 x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_29; obj* x_30; obj* x_31; obj* x_32; 
x_7 = lean::cnstr_get(x_2, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_2, 1);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_2, 2);
lean::inc(x_11);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_13 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 lean::cnstr_release(x_2, 1);
 lean::cnstr_release(x_2, 2);
 x_13 = x_2;
}
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
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_yield__command___lambda__1), 2, 1);
lean::closure_set(x_17, 0, x_11);
x_18 = lean::cnstr_get(x_0, 3);
lean::inc(x_18);
lean::dec(x_0);
x_21 = l_option_get___main___at_lean_parser_run___spec__2(x_18);
x_22 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_22, 0, x_21);
x_23 = 1;
x_24 = lean::box(x_23);
if (lean::is_scalar(x_6)) {
 x_25 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_25 = x_6;
}
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_22);
if (lean::is_scalar(x_16)) {
 x_26 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_26 = x_16;
}
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_14);
x_27 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_27);
if (lean::is_scalar(x_13)) {
 x_29 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_29 = x_13;
}
lean::cnstr_set(x_29, 0, x_26);
lean::cnstr_set(x_29, 1, x_9);
lean::cnstr_set(x_29, 2, x_27);
x_30 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_4);
x_31 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_31, 0, x_30);
x_32 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_32, 0, x_31);
lean::closure_set(x_32, 1, x_17);
return x_32;
}
else
{
obj* x_34; uint8 x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; 
lean::dec(x_0);
x_34 = lean::cnstr_get(x_2, 0);
lean::inc(x_34);
x_36 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*1);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_37 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 x_37 = x_2;
}
if (lean::is_scalar(x_37)) {
 x_38 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_38 = x_37;
}
lean::cnstr_set(x_38, 0, x_34);
lean::cnstr_set_scalar(x_38, sizeof(void*)*1, x_36);
x_39 = x_38;
if (lean::is_scalar(x_6)) {
 x_40 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_40 = x_6;
}
lean::cnstr_set(x_40, 0, x_39);
lean::cnstr_set(x_40, 1, x_4);
x_41 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_41, 0, x_40);
return x_41;
}
}
}
obj* l___private_209794555__commands__aux___main___lambda__15(uint8 x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_6; 
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
if (lean::obj_tag(x_2) == 0)
{
obj* x_7; obj* x_8; 
if (lean::is_scalar(x_6)) {
 x_7 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_7 = x_6;
}
lean::cnstr_set(x_7, 0, x_2);
lean::cnstr_set(x_7, 1, x_4);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_8, 0, x_7);
return x_8;
}
else
{
obj* x_9; uint8 x_11; obj* x_12; 
x_9 = lean::cnstr_get(x_2, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*1);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_12 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 x_12 = x_2;
}
if (x_0 == 0)
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
if (lean::is_scalar(x_12)) {
 x_13 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_13 = x_12;
}
lean::cnstr_set(x_13, 0, x_9);
lean::cnstr_set_scalar(x_13, sizeof(void*)*1, x_11);
x_14 = x_13;
if (lean::is_scalar(x_6)) {
 x_15 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_15 = x_6;
}
lean::cnstr_set(x_15, 0, x_14);
lean::cnstr_set(x_15, 1, x_4);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_16, 0, x_15);
return x_16;
}
else
{
obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
if (lean::is_scalar(x_12)) {
 x_17 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_17 = x_12;
}
lean::cnstr_set(x_17, 0, x_9);
lean::cnstr_set_scalar(x_17, sizeof(void*)*1, x_0);
x_18 = x_17;
if (lean::is_scalar(x_6)) {
 x_19 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_19 = x_6;
}
lean::cnstr_set(x_19, 0, x_18);
lean::cnstr_set(x_19, 1, x_4);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_20, 0, x_19);
return x_20;
}
}
}
}
obj* l___private_209794555__commands__aux___main___lambda__16(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_6; 
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
if (lean::obj_tag(x_2) == 0)
{
obj* x_8; obj* x_9; 
lean::dec(x_0);
if (lean::is_scalar(x_6)) {
 x_8 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_8 = x_6;
}
lean::cnstr_set(x_8, 0, x_2);
lean::cnstr_set(x_8, 1, x_4);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_9, 0, x_8);
return x_9;
}
else
{
obj* x_11; uint8 x_13; obj* x_15; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
lean::dec(x_6);
x_11 = lean::cnstr_get(x_2, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*1);
lean::dec(x_2);
x_15 = lean::cnstr_get(x_11, 0);
lean::inc(x_15);
lean::inc(x_11);
x_18 = l_lean_parser_log__message___at___private_209794555__commands__aux___main___spec__5(x_11, x_0, x_15, x_4);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l___private_209794555__commands__aux___main___lambda__14), 2, 1);
lean::closure_set(x_19, 0, x_11);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_20, 0, x_18);
lean::closure_set(x_20, 1, x_19);
x_21 = lean::box(x_13);
x_22 = lean::alloc_closure(reinterpret_cast<void*>(l___private_209794555__commands__aux___main___lambda__15___boxed), 2, 1);
lean::closure_set(x_22, 0, x_21);
x_23 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_23, 0, x_20);
lean::closure_set(x_23, 1, x_22);
return x_23;
}
}
}
obj* l___private_209794555__commands__aux___main___lambda__17(uint8 x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_7; 
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
if (lean::obj_tag(x_3) == 0)
{
obj* x_9; obj* x_11; obj* x_13; obj* x_16; obj* x_19; obj* x_20; obj* x_21; 
lean::dec(x_7);
x_9 = lean::cnstr_get(x_3, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_3, 1);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_3, 2);
lean::inc(x_13);
lean::dec(x_3);
x_16 = lean::cnstr_get(x_9, 1);
lean::inc(x_16);
lean::dec(x_9);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_yield__command___lambda__1), 2, 1);
lean::closure_set(x_19, 0, x_13);
x_20 = l___private_209794555__commands__aux___main(x_0, x_1, x_16, x_11, x_5);
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_21, 0, x_20);
lean::closure_set(x_21, 1, x_19);
return x_21;
}
else
{
obj* x_23; uint8 x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
lean::dec(x_1);
x_23 = lean::cnstr_get(x_3, 0);
lean::inc(x_23);
x_25 = lean::cnstr_get_scalar<uint8>(x_3, sizeof(void*)*1);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_26 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 x_26 = x_3;
}
if (lean::is_scalar(x_26)) {
 x_27 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_27 = x_26;
}
lean::cnstr_set(x_27, 0, x_23);
lean::cnstr_set_scalar(x_27, sizeof(void*)*1, x_25);
x_28 = x_27;
if (lean::is_scalar(x_7)) {
 x_29 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_29 = x_7;
}
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_5);
x_30 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_30, 0, x_29);
return x_30;
}
}
}
obj* l___private_209794555__commands__aux___main___lambda__18(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_6; 
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
if (lean::obj_tag(x_2) == 0)
{
obj* x_8; obj* x_10; obj* x_12; obj* x_15; obj* x_17; obj* x_20; obj* x_22; obj* x_25; 
lean::dec(x_6);
x_8 = lean::cnstr_get(x_2, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_2, 1);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_2, 2);
lean::inc(x_12);
lean::dec(x_2);
x_15 = lean::cnstr_get(x_8, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_8, 1);
lean::inc(x_17);
lean::dec(x_8);
x_20 = lean::cnstr_get(x_15, 0);
lean::inc(x_20);
x_22 = lean::cnstr_get(x_15, 1);
lean::inc(x_22);
lean::dec(x_15);
x_25 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_yield__command___lambda__1), 2, 1);
lean::closure_set(x_25, 0, x_12);
if (lean::obj_tag(x_22) == 0)
{
uint8 x_27; obj* x_29; obj* x_30; 
lean::dec(x_22);
x_27 = lean::unbox(x_20);
lean::dec(x_20);
x_29 = l___private_209794555__commands__aux___main(x_27, x_0, x_17, x_10, x_4);
x_30 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_30, 0, x_29);
lean::closure_set(x_30, 1, x_25);
return x_30;
}
else
{
obj* x_31; obj* x_34; obj* x_35; obj* x_36; obj* x_37; 
x_31 = lean::cnstr_get(x_22, 0);
lean::inc(x_31);
lean::dec(x_22);
x_34 = l_lean_parser_module_yield__command(x_31, x_17, x_10, x_4);
x_35 = lean::alloc_closure(reinterpret_cast<void*>(l___private_209794555__commands__aux___main___lambda__17___boxed), 3, 2);
lean::closure_set(x_35, 0, x_20);
lean::closure_set(x_35, 1, x_0);
x_36 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_36, 0, x_34);
lean::closure_set(x_36, 1, x_35);
x_37 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_37, 0, x_36);
lean::closure_set(x_37, 1, x_25);
return x_37;
}
}
else
{
obj* x_39; uint8 x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; 
lean::dec(x_0);
x_39 = lean::cnstr_get(x_2, 0);
lean::inc(x_39);
x_41 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*1);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_42 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 x_42 = x_2;
}
if (lean::is_scalar(x_42)) {
 x_43 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_43 = x_42;
}
lean::cnstr_set(x_43, 0, x_39);
lean::cnstr_set_scalar(x_43, sizeof(void*)*1, x_41);
x_44 = x_43;
if (lean::is_scalar(x_6)) {
 x_45 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_45 = x_6;
}
lean::cnstr_set(x_45, 0, x_44);
lean::cnstr_set(x_45, 1, x_4);
x_46 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_46, 0, x_45);
return x_46;
}
}
}
obj* l___private_209794555__commands__aux___main___lambda__19(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_8; obj* x_10; 
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
if (lean::is_shared(x_5)) {
 lean::dec(x_5);
 x_10 = lean::box(0);
} else {
 lean::cnstr_release(x_5, 0);
 lean::cnstr_release(x_5, 1);
 x_10 = x_5;
}
if (lean::obj_tag(x_6) == 0)
{
obj* x_16; obj* x_17; 
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
if (lean::is_scalar(x_10)) {
 x_16 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_16 = x_10;
}
lean::cnstr_set(x_16, 0, x_6);
lean::cnstr_set(x_16, 1, x_8);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_17, 0, x_16);
return x_17;
}
else
{
obj* x_18; uint8 x_20; 
x_18 = lean::cnstr_get(x_6, 0);
lean::inc(x_18);
x_20 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*1);
if (x_20 == 0)
{
obj* x_23; obj* x_25; obj* x_27; obj* x_28; obj* x_30; obj* x_31; obj* x_33; obj* x_34; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; 
lean::dec(x_10);
lean::dec(x_6);
x_23 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_yield__command___lambda__4), 2, 1);
lean::closure_set(x_23, 0, x_8);
lean::inc(x_0);
x_25 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_25, 0, x_0);
lean::closure_set(x_25, 1, x_23);
lean::inc(x_1);
x_27 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_log__message___at___private_209794555__commands__aux___main___spec__4___lambda__1), 2, 1);
lean::closure_set(x_27, 0, x_1);
x_28 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_28, 0, x_25);
lean::closure_set(x_28, 1, x_27);
lean::inc(x_2);
x_30 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___at___private_209794555__commands__aux___main___spec__1___rarg___lambda__1), 2, 1);
lean::closure_set(x_30, 0, x_2);
x_31 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_31, 0, x_28);
lean::closure_set(x_31, 1, x_30);
lean::inc(x_0);
x_33 = lean::alloc_closure(reinterpret_cast<void*>(l___private_209794555__commands__aux___main___lambda__3), 2, 1);
lean::closure_set(x_33, 0, x_0);
x_34 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_34, 0, x_31);
lean::closure_set(x_34, 1, x_33);
lean::inc(x_2);
x_36 = lean::alloc_closure(reinterpret_cast<void*>(l___private_209794555__commands__aux___main___lambda__13), 5, 4);
lean::closure_set(x_36, 0, x_0);
lean::closure_set(x_36, 1, x_3);
lean::closure_set(x_36, 2, x_2);
lean::closure_set(x_36, 3, x_1);
x_37 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_37, 0, x_34);
lean::closure_set(x_37, 1, x_36);
x_38 = lean::alloc_closure(reinterpret_cast<void*>(l___private_209794555__commands__aux___main___lambda__16), 2, 1);
lean::closure_set(x_38, 0, x_2);
x_39 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_39, 0, x_37);
lean::closure_set(x_39, 1, x_38);
x_40 = lean::alloc_closure(reinterpret_cast<void*>(l___private_209794555__commands__aux___main___lambda__18), 2, 1);
lean::closure_set(x_40, 0, x_4);
x_41 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_41, 0, x_39);
lean::closure_set(x_41, 1, x_40);
x_42 = lean::alloc_closure(reinterpret_cast<void*>(l___private_209794555__commands__aux___main___lambda__8), 2, 1);
lean::closure_set(x_42, 0, x_18);
x_43 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_43, 0, x_41);
lean::closure_set(x_43, 1, x_42);
return x_43;
}
else
{
obj* x_50; obj* x_51; 
lean::dec(x_18);
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
if (lean::is_scalar(x_10)) {
 x_50 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_50 = x_10;
}
lean::cnstr_set(x_50, 0, x_6);
lean::cnstr_set(x_50, 1, x_8);
x_51 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_51, 0, x_50);
return x_51;
}
}
}
}
obj* l___private_209794555__commands__aux___main___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; obj* x_6; 
x_5 = lean::unbox(x_0);
x_6 = l___private_209794555__commands__aux___main(x_5, x_1, x_2, x_3, x_4);
return x_6;
}
}
obj* l___private_209794555__commands__aux___main___lambda__15___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = lean::unbox(x_0);
x_3 = l___private_209794555__commands__aux___main___lambda__15(x_2, x_1);
return x_3;
}
}
obj* l___private_209794555__commands__aux___main___lambda__17___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_0);
x_4 = l___private_209794555__commands__aux___main___lambda__17(x_3, x_1, x_2);
return x_4;
}
}
obj* l___private_209794555__commands__aux(uint8 x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l___private_209794555__commands__aux___main(x_0, x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* l___private_209794555__commands__aux___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; obj* x_6; 
x_5 = lean::unbox(x_0);
x_6 = l___private_209794555__commands__aux(x_5, x_1, x_2, x_3, x_4);
return x_6;
}
}
obj* l_lean_parser_module_commands_parser(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_6; obj* x_7; obj* x_8; obj* x_10; obj* x_11; obj* x_12; obj* x_14; obj* x_15; obj* x_17; 
x_3 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_3);
lean::inc(x_1);
x_6 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_6, 0, x_1);
lean::cnstr_set(x_6, 1, x_1);
lean::cnstr_set(x_6, 2, x_3);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_2);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_8, 0, x_7);
lean::inc(x_3);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_yield__command___lambda__6), 3, 2);
lean::closure_set(x_10, 0, x_0);
lean::closure_set(x_10, 1, x_3);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_11, 0, x_8);
lean::closure_set(x_11, 1, x_10);
x_12 = l_lean_parser_module_commands_parser___closed__1;
lean::inc(x_12);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_14, 0, x_11);
lean::closure_set(x_14, 1, x_12);
x_15 = l_lean_parser_module_commands_parser___closed__2;
lean::inc(x_15);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_17, 0, x_14);
lean::closure_set(x_17, 1, x_15);
return x_17;
}
}
obj* _init_l_lean_parser_module_commands_parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_id___rarg), 1, 0);
x_1 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_commands_parser___lambda__1), 2, 1);
lean::closure_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_lean_parser_module_commands_parser___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_commands_parser___lambda__2), 1, 0);
return x_0;
}
}
obj* l_lean_parser_module_commands_parser___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_6; 
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
if (lean::obj_tag(x_2) == 0)
{
obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_14; obj* x_16; obj* x_18; obj* x_19; obj* x_20; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
x_7 = lean::cnstr_get(x_2, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_2, 1);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_2, 2);
lean::inc(x_11);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_13 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 lean::cnstr_release(x_2, 1);
 lean::cnstr_release(x_2, 2);
 x_13 = x_2;
}
x_14 = lean::cnstr_get(x_7, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_7, 1);
lean::inc(x_16);
if (lean::is_shared(x_7)) {
 lean::dec(x_7);
 x_18 = lean::box(0);
} else {
 lean::cnstr_release(x_7, 0);
 lean::cnstr_release(x_7, 1);
 x_18 = x_7;
}
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_yield__command___lambda__1), 2, 1);
lean::closure_set(x_19, 0, x_11);
x_20 = lean::string_iterator_remaining(x_14);
lean::dec(x_14);
if (lean::is_scalar(x_6)) {
 x_22 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_22 = x_6;
}
lean::cnstr_set(x_22, 0, x_20);
lean::cnstr_set(x_22, 1, x_16);
if (lean::is_scalar(x_13)) {
 x_23 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_23 = x_13;
}
lean::cnstr_set(x_23, 0, x_22);
lean::cnstr_set(x_23, 1, x_9);
lean::cnstr_set(x_23, 2, x_0);
if (lean::is_scalar(x_18)) {
 x_24 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_24 = x_18;
}
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_4);
x_25 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_25, 0, x_24);
x_26 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_26, 0, x_25);
lean::closure_set(x_26, 1, x_19);
return x_26;
}
else
{
obj* x_28; uint8 x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; 
lean::dec(x_0);
x_28 = lean::cnstr_get(x_2, 0);
lean::inc(x_28);
x_30 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*1);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_31 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 x_31 = x_2;
}
if (lean::is_scalar(x_31)) {
 x_32 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_32 = x_31;
}
lean::cnstr_set(x_32, 0, x_28);
lean::cnstr_set_scalar(x_32, sizeof(void*)*1, x_30);
x_33 = x_32;
if (lean::is_scalar(x_6)) {
 x_34 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_34 = x_6;
}
lean::cnstr_set(x_34, 0, x_33);
lean::cnstr_set(x_34, 1, x_4);
x_35 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_35, 0, x_34);
return x_35;
}
}
}
obj* l_lean_parser_module_commands_parser___lambda__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_5; 
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
if (lean::obj_tag(x_1) == 0)
{
obj* x_7; obj* x_9; obj* x_11; obj* x_14; obj* x_16; obj* x_19; obj* x_20; obj* x_21; uint8 x_24; obj* x_25; obj* x_26; 
lean::dec(x_5);
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_1, 1);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_1, 2);
lean::inc(x_11);
lean::dec(x_1);
x_14 = lean::cnstr_get(x_7, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_7, 1);
lean::inc(x_16);
lean::dec(x_7);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_yield__command___lambda__1), 2, 1);
lean::closure_set(x_19, 0, x_11);
x_20 = lean::mk_nat_obj(1u);
x_21 = lean::nat_add(x_14, x_20);
lean::dec(x_20);
lean::dec(x_14);
x_24 = 0;
x_25 = l___private_209794555__commands__aux___main(x_24, x_21, x_16, x_9, x_3);
x_26 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_26, 0, x_25);
lean::closure_set(x_26, 1, x_19);
return x_26;
}
else
{
obj* x_27; uint8 x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; 
x_27 = lean::cnstr_get(x_1, 0);
lean::inc(x_27);
x_29 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*1);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_30 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 x_30 = x_1;
}
if (lean::is_scalar(x_30)) {
 x_31 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_31 = x_30;
}
lean::cnstr_set(x_31, 0, x_27);
lean::cnstr_set_scalar(x_31, sizeof(void*)*1, x_29);
x_32 = x_31;
if (lean::is_scalar(x_5)) {
 x_33 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_33 = x_5;
}
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_3);
x_34 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_34, 0, x_33);
return x_34;
}
}
}
obj* _init_l_lean_parser_module_commands_tokens() {
_start:
{
obj* x_0; obj* x_2; 
x_0 = l_lean_parser_command_parser_lean_parser_has__tokens;
lean::inc(x_0);
x_2 = l_lean_parser_tokens___rarg(x_0);
return x_2;
}
}
obj* l_list_map___main___at_lean_parser_module_commands_parser_has__view___spec__1(obj* x_0) {
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
x_8 = l_list_map___main___at_lean_parser_module_commands_parser_has__view___spec__1(x_5);
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
obj* l_list_map___main___at_lean_parser_module_commands_parser_has__view___spec__2(obj* x_0) {
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
x_8 = l_list_map___main___at_lean_parser_module_commands_parser_has__view___spec__2(x_5);
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
obj* _init_l_lean_parser_module_commands_parser_has__view() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_commands_parser_has__view___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_commands_parser_has__view___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* l_lean_parser_module_commands_parser_has__view___lambda__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_syntax_as__node___main(x_0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; 
lean::dec(x_1);
x_3 = l_lean_parser_ident__univ__spec_has__view_x_27___lambda__1___closed__1;
lean::inc(x_3);
return x_3;
}
else
{
obj* x_5; obj* x_8; obj* x_11; 
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
lean::dec(x_1);
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
lean::dec(x_5);
x_11 = l_list_map___main___at_lean_parser_module_commands_parser_has__view___spec__1(x_8);
return x_11;
}
}
}
obj* l_lean_parser_module_commands_parser_has__view___lambda__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_1 = l_list_map___main___at_lean_parser_module_commands_parser_has__view___spec__2(x_0);
x_2 = l_lean_parser_no__kind;
lean::inc(x_2);
x_4 = l_lean_parser_syntax_mk__node(x_2, x_1);
return x_4;
}
}
obj* _init_l_lean_parser_module_eoi() {
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
obj* l_lean_parser_module_parser(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_5; obj* x_7; obj* x_8; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_15; 
lean::inc(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_parser___lambda__1), 4, 3);
lean::closure_set(x_4, 0, x_1);
lean::closure_set(x_4, 1, x_2);
lean::closure_set(x_4, 2, x_0);
x_5 = l_lean_parser_module__parser__m_lift__parser__t___rarg___closed__1;
lean::inc(x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_7, 0, x_5);
lean::closure_set(x_7, 1, x_4);
x_8 = l_lean_parser_module_parser___closed__1;
lean::inc(x_8);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_10, 0, x_7);
lean::closure_set(x_10, 1, x_8);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_parser___lambda__8), 2, 1);
lean::closure_set(x_11, 0, x_0);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_12, 0, x_10);
lean::closure_set(x_12, 1, x_11);
x_13 = l_lean_parser_module_parser___closed__2;
lean::inc(x_13);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_15, 0, x_12);
lean::closure_set(x_15, 1, x_13);
return x_15;
}
}
obj* _init_l_lean_parser_module_parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_parser___lambda__6), 2, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_lean_parser_module_parser___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_parser___lambda__10), 1, 0);
return x_0;
}
}
obj* l_lean_parser_module_parser___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_7; obj* x_10; obj* x_11; obj* x_13; obj* x_15; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
lean::dec(x_3);
x_7 = lean::cnstr_get(x_4, 0);
lean::inc(x_7);
lean::dec(x_4);
x_10 = l_lean_parser_whitespace(x_7, x_0, x_1);
x_11 = lean::cnstr_get(x_10, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_10, 1);
lean::inc(x_13);
if (lean::is_shared(x_10)) {
 lean::dec(x_10);
 x_15 = lean::box(0);
} else {
 lean::cnstr_release(x_10, 0);
 lean::cnstr_release(x_10, 1);
 x_15 = x_10;
}
if (lean::obj_tag(x_11) == 0)
{
obj* x_16; obj* x_18; obj* x_20; obj* x_22; obj* x_23; obj* x_24; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
x_16 = lean::cnstr_get(x_11, 0);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_11, 1);
lean::inc(x_18);
x_20 = lean::cnstr_get(x_11, 2);
lean::inc(x_20);
if (lean::is_shared(x_11)) {
 lean::dec(x_11);
 x_22 = lean::box(0);
} else {
 lean::cnstr_release(x_11, 0);
 lean::cnstr_release(x_11, 1);
 lean::cnstr_release(x_11, 2);
 x_22 = x_11;
}
if (lean::is_scalar(x_15)) {
 x_23 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_23 = x_15;
}
lean::cnstr_set(x_23, 0, x_16);
lean::cnstr_set(x_23, 1, x_2);
x_24 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_24);
if (lean::is_scalar(x_22)) {
 x_26 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_26 = x_22;
}
lean::cnstr_set(x_26, 0, x_23);
lean::cnstr_set(x_26, 1, x_18);
lean::cnstr_set(x_26, 2, x_24);
x_27 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_20, x_26);
x_28 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_13);
x_29 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_29, 0, x_28);
return x_29;
}
else
{
obj* x_31; uint8 x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
lean::dec(x_2);
x_31 = lean::cnstr_get(x_11, 0);
lean::inc(x_31);
x_33 = lean::cnstr_get_scalar<uint8>(x_11, sizeof(void*)*1);
if (lean::is_shared(x_11)) {
 lean::dec(x_11);
 x_34 = lean::box(0);
} else {
 lean::cnstr_release(x_11, 0);
 x_34 = x_11;
}
if (lean::is_scalar(x_34)) {
 x_35 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_35 = x_34;
}
lean::cnstr_set(x_35, 0, x_31);
lean::cnstr_set_scalar(x_35, sizeof(void*)*1, x_33);
x_36 = x_35;
if (lean::is_scalar(x_15)) {
 x_37 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_37 = x_15;
}
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_13);
x_38 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_38, 0, x_37);
return x_38;
}
}
}
obj* l_lean_parser_module_parser___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_7; obj* x_10; obj* x_11; obj* x_14; obj* x_15; obj* x_17; obj* x_19; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
lean::dec(x_3);
x_7 = lean::cnstr_get(x_4, 0);
lean::inc(x_7);
lean::dec(x_4);
x_10 = l_lean_parser_module_header;
x_11 = l_lean_parser_module_header_parser___closed__1;
lean::inc(x_11);
lean::inc(x_10);
x_14 = l_lean_parser_combinators_node___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__8(x_10, x_11, x_7, x_0, x_1);
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
if (lean::obj_tag(x_15) == 0)
{
obj* x_20; obj* x_22; obj* x_24; obj* x_26; obj* x_27; obj* x_28; obj* x_30; obj* x_31; obj* x_32; obj* x_33; 
x_20 = lean::cnstr_get(x_15, 0);
lean::inc(x_20);
x_22 = lean::cnstr_get(x_15, 1);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_15, 2);
lean::inc(x_24);
if (lean::is_shared(x_15)) {
 lean::dec(x_15);
 x_26 = lean::box(0);
} else {
 lean::cnstr_release(x_15, 0);
 lean::cnstr_release(x_15, 1);
 lean::cnstr_release(x_15, 2);
 x_26 = x_15;
}
if (lean::is_scalar(x_19)) {
 x_27 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_27 = x_19;
}
lean::cnstr_set(x_27, 0, x_20);
lean::cnstr_set(x_27, 1, x_2);
x_28 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_28);
if (lean::is_scalar(x_26)) {
 x_30 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_30 = x_26;
}
lean::cnstr_set(x_30, 0, x_27);
lean::cnstr_set(x_30, 1, x_22);
lean::cnstr_set(x_30, 2, x_28);
x_31 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_24, x_30);
x_32 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_17);
x_33 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_33, 0, x_32);
return x_33;
}
else
{
obj* x_35; uint8 x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; 
lean::dec(x_2);
x_35 = lean::cnstr_get(x_15, 0);
lean::inc(x_35);
x_37 = lean::cnstr_get_scalar<uint8>(x_15, sizeof(void*)*1);
if (lean::is_shared(x_15)) {
 lean::dec(x_15);
 x_38 = lean::box(0);
} else {
 lean::cnstr_release(x_15, 0);
 x_38 = x_15;
}
if (lean::is_scalar(x_38)) {
 x_39 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_39 = x_38;
}
lean::cnstr_set(x_39, 0, x_35);
lean::cnstr_set_scalar(x_39, sizeof(void*)*1, x_37);
x_40 = x_39;
if (lean::is_scalar(x_19)) {
 x_41 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_41 = x_19;
}
lean::cnstr_set(x_41, 0, x_40);
lean::cnstr_set(x_41, 1, x_17);
x_42 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_42, 0, x_41);
return x_42;
}
}
}
obj* l_lean_parser_module_parser___lambda__3(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_5; 
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
if (lean::obj_tag(x_1) == 0)
{
obj* x_7; obj* x_9; obj* x_11; obj* x_14; obj* x_16; obj* x_19; obj* x_20; obj* x_21; 
lean::dec(x_5);
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_1, 1);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_1, 2);
lean::inc(x_11);
lean::dec(x_1);
x_14 = lean::cnstr_get(x_7, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_7, 1);
lean::inc(x_16);
lean::dec(x_7);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_yield__command___lambda__1), 2, 1);
lean::closure_set(x_19, 0, x_11);
x_20 = l_lean_parser_module_yield__command(x_14, x_16, x_9, x_3);
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_21, 0, x_20);
lean::closure_set(x_21, 1, x_19);
return x_21;
}
else
{
obj* x_22; uint8 x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
x_22 = lean::cnstr_get(x_1, 0);
lean::inc(x_22);
x_24 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*1);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_25 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 x_25 = x_1;
}
if (lean::is_scalar(x_25)) {
 x_26 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_26 = x_25;
}
lean::cnstr_set(x_26, 0, x_22);
lean::cnstr_set_scalar(x_26, sizeof(void*)*1, x_24);
x_27 = x_26;
if (lean::is_scalar(x_5)) {
 x_28 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_28 = x_5;
}
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_3);
x_29 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_29, 0, x_28);
return x_29;
}
}
}
obj* l_lean_parser_module_parser___lambda__4(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_5; 
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
if (lean::obj_tag(x_1) == 0)
{
obj* x_7; obj* x_9; obj* x_11; obj* x_14; obj* x_17; obj* x_18; obj* x_19; 
lean::dec(x_5);
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_1, 1);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_1, 2);
lean::inc(x_11);
lean::dec(x_1);
x_14 = lean::cnstr_get(x_7, 1);
lean::inc(x_14);
lean::dec(x_7);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_yield__command___lambda__1), 2, 1);
lean::closure_set(x_17, 0, x_11);
x_18 = l_lean_parser_monad__parsec_eoi___at___private_209794555__commands__aux___main___spec__2(x_14, x_9, x_3);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_19, 0, x_18);
lean::closure_set(x_19, 1, x_17);
return x_19;
}
else
{
obj* x_20; uint8 x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; 
x_20 = lean::cnstr_get(x_1, 0);
lean::inc(x_20);
x_22 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*1);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_23 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 x_23 = x_1;
}
if (lean::is_scalar(x_23)) {
 x_24 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_24 = x_23;
}
lean::cnstr_set(x_24, 0, x_20);
lean::cnstr_set_scalar(x_24, sizeof(void*)*1, x_22);
x_25 = x_24;
if (lean::is_scalar(x_5)) {
 x_26 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_26 = x_5;
}
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_3);
x_27 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_27, 0, x_26);
return x_27;
}
}
}
obj* l_lean_parser_module_parser___lambda__5(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_5; 
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
if (lean::obj_tag(x_1) == 0)
{
obj* x_7; obj* x_9; obj* x_11; obj* x_14; obj* x_17; obj* x_18; obj* x_19; obj* x_21; obj* x_22; 
lean::dec(x_5);
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_1, 1);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_1, 2);
lean::inc(x_11);
lean::dec(x_1);
x_14 = lean::cnstr_get(x_7, 1);
lean::inc(x_14);
lean::dec(x_7);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_yield__command___lambda__1), 2, 1);
lean::closure_set(x_17, 0, x_11);
x_18 = l_lean_parser_module_commands_parser(x_14, x_9, x_3);
x_19 = l_lean_parser_module_parser___lambda__5___closed__1;
lean::inc(x_19);
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_21, 0, x_18);
lean::closure_set(x_21, 1, x_19);
x_22 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_22, 0, x_21);
lean::closure_set(x_22, 1, x_17);
return x_22;
}
else
{
obj* x_23; uint8 x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_23 = lean::cnstr_get(x_1, 0);
lean::inc(x_23);
x_25 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*1);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_26 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 x_26 = x_1;
}
if (lean::is_scalar(x_26)) {
 x_27 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_27 = x_26;
}
lean::cnstr_set(x_27, 0, x_23);
lean::cnstr_set_scalar(x_27, sizeof(void*)*1, x_25);
x_28 = x_27;
if (lean::is_scalar(x_5)) {
 x_29 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_29 = x_5;
}
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_3);
x_30 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_30, 0, x_29);
return x_30;
}
}
}
obj* _init_l_lean_parser_module_parser___lambda__5___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_parser___lambda__4), 1, 0);
return x_0;
}
}
obj* l_lean_parser_module_parser___lambda__6(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_6; 
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
if (lean::obj_tag(x_2) == 0)
{
obj* x_8; obj* x_10; obj* x_12; obj* x_15; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_23; obj* x_24; obj* x_26; obj* x_27; 
lean::dec(x_6);
x_8 = lean::cnstr_get(x_2, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_2, 1);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_2, 2);
lean::inc(x_12);
lean::dec(x_2);
x_15 = lean::cnstr_get(x_8, 1);
lean::inc(x_15);
lean::dec(x_8);
x_18 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_yield__command___lambda__1), 2, 1);
lean::closure_set(x_18, 0, x_12);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_parser___lambda__2), 4, 3);
lean::closure_set(x_19, 0, x_10);
lean::closure_set(x_19, 1, x_4);
lean::closure_set(x_19, 2, x_15);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_20, 0, x_0);
lean::closure_set(x_20, 1, x_19);
x_21 = l_lean_parser_module_parser___lambda__6___closed__1;
lean::inc(x_21);
x_23 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_23, 0, x_20);
lean::closure_set(x_23, 1, x_21);
x_24 = l_lean_parser_module_parser___lambda__6___closed__2;
lean::inc(x_24);
x_26 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_26, 0, x_23);
lean::closure_set(x_26, 1, x_24);
x_27 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_27, 0, x_26);
lean::closure_set(x_27, 1, x_18);
return x_27;
}
else
{
obj* x_29; uint8 x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; 
lean::dec(x_0);
x_29 = lean::cnstr_get(x_2, 0);
lean::inc(x_29);
x_31 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*1);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_32 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 x_32 = x_2;
}
if (lean::is_scalar(x_32)) {
 x_33 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_33 = x_32;
}
lean::cnstr_set(x_33, 0, x_29);
lean::cnstr_set_scalar(x_33, sizeof(void*)*1, x_31);
x_34 = x_33;
if (lean::is_scalar(x_6)) {
 x_35 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_35 = x_6;
}
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_4);
x_36 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_36, 0, x_35);
return x_36;
}
}
}
obj* _init_l_lean_parser_module_parser___lambda__6___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_parser___lambda__3), 1, 0);
return x_0;
}
}
obj* _init_l_lean_parser_module_parser___lambda__6___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_parser___lambda__5), 1, 0);
return x_0;
}
}
obj* l_lean_parser_module_parser___lambda__7(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_6; 
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
if (lean::obj_tag(x_2) == 0)
{
obj* x_8; obj* x_10; obj* x_12; obj* x_15; obj* x_18; obj* x_19; obj* x_22; obj* x_23; obj* x_24; 
lean::dec(x_6);
x_8 = lean::cnstr_get(x_2, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_2, 1);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_2, 2);
lean::inc(x_12);
lean::dec(x_2);
x_15 = lean::cnstr_get(x_8, 1);
lean::inc(x_15);
lean::dec(x_8);
x_18 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_yield__command___lambda__1), 2, 1);
lean::closure_set(x_18, 0, x_12);
x_19 = lean::cnstr_get(x_0, 3);
lean::inc(x_19);
lean::dec(x_0);
x_22 = l_option_get___main___at_lean_parser_run___spec__2(x_19);
x_23 = l_lean_parser_module_yield__command(x_22, x_15, x_10, x_4);
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_24, 0, x_23);
lean::closure_set(x_24, 1, x_18);
return x_24;
}
else
{
obj* x_26; uint8 x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; 
lean::dec(x_0);
x_26 = lean::cnstr_get(x_2, 0);
lean::inc(x_26);
x_28 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*1);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_29 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 x_29 = x_2;
}
if (lean::is_scalar(x_29)) {
 x_30 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_30 = x_29;
}
lean::cnstr_set(x_30, 0, x_26);
lean::cnstr_set_scalar(x_30, sizeof(void*)*1, x_28);
x_31 = x_30;
if (lean::is_scalar(x_6)) {
 x_32 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_32 = x_6;
}
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_4);
x_33 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_33, 0, x_32);
return x_33;
}
}
}
obj* l_lean_parser_module_parser___lambda__8(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_6; 
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
if (lean::obj_tag(x_2) == 0)
{
obj* x_8; obj* x_9; 
lean::dec(x_0);
if (lean::is_scalar(x_6)) {
 x_8 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_8 = x_6;
}
lean::cnstr_set(x_8, 0, x_2);
lean::cnstr_set(x_8, 1, x_4);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_9, 0, x_8);
return x_9;
}
else
{
obj* x_11; uint8 x_13; obj* x_15; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
lean::dec(x_6);
x_11 = lean::cnstr_get(x_2, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*1);
lean::dec(x_2);
x_15 = lean::cnstr_get(x_11, 0);
lean::inc(x_15);
lean::inc(x_11);
x_18 = l_lean_parser_log__message___at___private_209794555__commands__aux___main___spec__5(x_11, x_0, x_15, x_4);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_parser___lambda__7), 2, 1);
lean::closure_set(x_19, 0, x_11);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_20, 0, x_18);
lean::closure_set(x_20, 1, x_19);
x_21 = lean::box(x_13);
x_22 = lean::alloc_closure(reinterpret_cast<void*>(l___private_209794555__commands__aux___main___lambda__15___boxed), 2, 1);
lean::closure_set(x_22, 0, x_21);
x_23 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_23, 0, x_20);
lean::closure_set(x_23, 1, x_22);
return x_23;
}
}
}
obj* l_lean_parser_module_parser___lambda__9(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_5; 
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
if (lean::obj_tag(x_1) == 0)
{
obj* x_7; obj* x_9; obj* x_11; obj* x_14; obj* x_16; obj* x_19; obj* x_20; obj* x_23; obj* x_24; obj* x_27; obj* x_28; obj* x_29; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_37; obj* x_38; obj* x_39; 
lean::dec(x_5);
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_1, 1);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_1, 2);
lean::inc(x_11);
lean::dec(x_1);
x_14 = lean::cnstr_get(x_7, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_7, 1);
lean::inc(x_16);
lean::dec(x_7);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_yield__command___lambda__1), 2, 1);
lean::closure_set(x_19, 0, x_11);
x_20 = lean::string_iterator_to_end(x_14);
lean::inc(x_20);
lean::inc(x_20);
x_23 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_23, 0, x_20);
lean::cnstr_set(x_23, 1, x_20);
x_24 = lean::string_iterator_offset(x_20);
lean::dec(x_20);
lean::inc(x_23);
x_27 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_27, 0, x_23);
lean::cnstr_set(x_27, 1, x_24);
lean::cnstr_set(x_27, 2, x_23);
x_28 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_28, 0, x_27);
x_29 = l_string_join___closed__1;
lean::inc(x_29);
x_31 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_31, 0, x_28);
lean::cnstr_set(x_31, 1, x_29);
x_32 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_32, 0, x_31);
x_33 = lean::box(0);
x_34 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_34, 0, x_32);
lean::cnstr_set(x_34, 1, x_33);
x_35 = l_lean_parser_module_eoi;
lean::inc(x_35);
x_37 = l_lean_parser_syntax_mk__node(x_35, x_34);
x_38 = l_lean_parser_module_yield__command(x_37, x_16, x_9, x_3);
x_39 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_39, 0, x_38);
lean::closure_set(x_39, 1, x_19);
return x_39;
}
else
{
obj* x_40; uint8 x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; 
x_40 = lean::cnstr_get(x_1, 0);
lean::inc(x_40);
x_42 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*1);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_43 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 x_43 = x_1;
}
if (lean::is_scalar(x_43)) {
 x_44 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_44 = x_43;
}
lean::cnstr_set(x_44, 0, x_40);
lean::cnstr_set_scalar(x_44, sizeof(void*)*1, x_42);
x_45 = x_44;
if (lean::is_scalar(x_5)) {
 x_46 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_46 = x_5;
}
lean::cnstr_set(x_46, 0, x_45);
lean::cnstr_set(x_46, 1, x_3);
x_47 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_47, 0, x_46);
return x_47;
}
}
}
obj* l_lean_parser_module_parser___lambda__10(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_5; 
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
if (lean::obj_tag(x_1) == 0)
{
obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_13; obj* x_16; obj* x_17; obj* x_20; obj* x_21; obj* x_22; obj* x_24; obj* x_25; obj* x_26; obj* x_28; obj* x_29; 
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 1);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_1, 2);
lean::inc(x_10);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_12 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 lean::cnstr_release(x_1, 2);
 x_12 = x_1;
}
x_13 = lean::cnstr_get(x_6, 1);
lean::inc(x_13);
lean::dec(x_6);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_yield__command___lambda__1), 2, 1);
lean::closure_set(x_16, 0, x_10);
x_17 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_17);
lean::inc(x_8);
if (lean::is_scalar(x_12)) {
 x_20 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_20 = x_12;
}
lean::cnstr_set(x_20, 0, x_8);
lean::cnstr_set(x_20, 1, x_8);
lean::cnstr_set(x_20, 2, x_17);
if (lean::is_scalar(x_5)) {
 x_21 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_21 = x_5;
}
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_3);
x_22 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_22, 0, x_21);
lean::inc(x_17);
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_yield__command___lambda__6), 3, 2);
lean::closure_set(x_24, 0, x_13);
lean::closure_set(x_24, 1, x_17);
x_25 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_25, 0, x_22);
lean::closure_set(x_25, 1, x_24);
x_26 = l_lean_parser_module_parser___lambda__10___closed__1;
lean::inc(x_26);
x_28 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_28, 0, x_25);
lean::closure_set(x_28, 1, x_26);
x_29 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_29, 0, x_28);
lean::closure_set(x_29, 1, x_16);
return x_29;
}
else
{
obj* x_30; uint8 x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; 
x_30 = lean::cnstr_get(x_1, 0);
lean::inc(x_30);
x_32 = lean::cnstr_get_scalar<uint8>(x_1, sizeof(void*)*1);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_33 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 x_33 = x_1;
}
if (lean::is_scalar(x_33)) {
 x_34 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_34 = x_33;
}
lean::cnstr_set(x_34, 0, x_30);
lean::cnstr_set_scalar(x_34, sizeof(void*)*1, x_32);
x_35 = x_34;
if (lean::is_scalar(x_5)) {
 x_36 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_36 = x_5;
}
lean::cnstr_set(x_36, 0, x_35);
lean::cnstr_set(x_36, 1, x_3);
x_37 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___lambda__2), 2, 1);
lean::closure_set(x_37, 0, x_36);
return x_37;
}
}
}
obj* _init_l_lean_parser_module_parser___lambda__10___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_parser___lambda__9), 1, 0);
return x_0;
}
}
obj* _init_l_lean_parser_module_tokens() {
_start:
{
obj* x_0; obj* x_2; obj* x_3; obj* x_5; obj* x_6; obj* x_7; obj* x_9; obj* x_10; 
x_0 = l_lean_parser_module_prelude_parser_lean_parser_has__tokens;
lean::inc(x_0);
x_2 = l_lean_parser_tokens___rarg(x_0);
x_3 = l_lean_parser_module_import_parser_lean_parser_has__tokens;
lean::inc(x_3);
x_5 = l_lean_parser_tokens___rarg(x_3);
x_6 = l_list_append___rarg(x_2, x_5);
x_7 = l_lean_parser_module_commands_tokens;
lean::inc(x_7);
x_9 = l_lean_parser_tokens___rarg(x_7);
x_10 = l_list_append___rarg(x_6, x_9);
return x_10;
}
}
void initialize_init_lean_parser_command();
void initialize_init_control_coroutine();
static bool _G_initialized = false;
void initialize_init_lean_parser_module() {
 if (_G_initialized) return;
 _G_initialized = true;
 initialize_init_lean_parser_command();
 initialize_init_control_coroutine();
 l_lean_parser_module__parser__m_monad__coroutine = _init_l_lean_parser_module__parser__m_monad__coroutine();
 l_lean_parser_module__parser__m_monad__except = _init_l_lean_parser_module__parser__m_monad__except();
 l_lean_parser_module__parser__m_lean_parser_monad__parsec = _init_l_lean_parser_module__parser__m_lean_parser_monad__parsec();
 l_lean_parser_module__parser__m_monad__state = _init_l_lean_parser_module__parser__m_monad__state();
 l_lean_parser_module__parser__m_monad__reader = _init_l_lean_parser_module__parser__m_monad__reader();
 l_lean_parser_module__parser__m_alternative = _init_l_lean_parser_module__parser__m_alternative();
 l_lean_parser_module__parser__m_monad = _init_l_lean_parser_module__parser__m_monad();
 l_lean_parser_module__parser__m = _init_l_lean_parser_module__parser__m();
 l_lean_parser_module__parser = _init_l_lean_parser_module__parser();
 l_lean_parser_module__parser__m_lift__parser__t___rarg___closed__1 = _init_l_lean_parser_module__parser__m_lift__parser__t___rarg___closed__1();
 l_lean_parser_module__parser__m_basic__parser__m___closed__1 = _init_l_lean_parser_module__parser__m_basic__parser__m___closed__1();
 l_lean_parser_module_yield__command___lambda__7___closed__1 = _init_l_lean_parser_module_yield__command___lambda__7___closed__1();
 l_lean_parser_module_prelude = _init_l_lean_parser_module_prelude();
 l_lean_parser_module_prelude_has__view_x_27 = _init_l_lean_parser_module_prelude_has__view_x_27();
 l_lean_parser_module_prelude_has__view = _init_l_lean_parser_module_prelude_has__view();
 l_lean_parser_module_prelude_parser_lean_parser_has__tokens = _init_l_lean_parser_module_prelude_parser_lean_parser_has__tokens();
 l_lean_parser_module_prelude_parser_lean_parser_has__view = _init_l_lean_parser_module_prelude_parser_lean_parser_has__view();
 l_lean_parser_module_prelude_parser___closed__1 = _init_l_lean_parser_module_prelude_parser___closed__1();
 l_lean_parser_module_import__path = _init_l_lean_parser_module_import__path();
 l_lean_parser_module_import__path_has__view_x_27 = _init_l_lean_parser_module_import__path_has__view_x_27();
 l_lean_parser_module_import__path_has__view_x_27___lambda__1___closed__1 = _init_l_lean_parser_module_import__path_has__view_x_27___lambda__1___closed__1();
 l_lean_parser_module_import__path_has__view_x_27___lambda__1___closed__2 = _init_l_lean_parser_module_import__path_has__view_x_27___lambda__1___closed__2();
 l_lean_parser_module_import__path_has__view_x_27___lambda__1___closed__3 = _init_l_lean_parser_module_import__path_has__view_x_27___lambda__1___closed__3();
 l_lean_parser_module_import__path_has__view_x_27___lambda__1___closed__4 = _init_l_lean_parser_module_import__path_has__view_x_27___lambda__1___closed__4();
 l_lean_parser_module_import__path_has__view = _init_l_lean_parser_module_import__path_has__view();
 l_lean_parser_module_import__path_parser_lean_parser_has__tokens = _init_l_lean_parser_module_import__path_parser_lean_parser_has__tokens();
 l_lean_parser_module_import__path_parser_lean_parser_has__view = _init_l_lean_parser_module_import__path_parser_lean_parser_has__view();
 l_lean_parser_module_import__path_parser___closed__1 = _init_l_lean_parser_module_import__path_parser___closed__1();
 l_lean_parser_module_import = _init_l_lean_parser_module_import();
 l_lean_parser_module_import_has__view_x_27 = _init_l_lean_parser_module_import_has__view_x_27();
 l_lean_parser_module_import_has__view_x_27___lambda__1___closed__1 = _init_l_lean_parser_module_import_has__view_x_27___lambda__1___closed__1();
 l_lean_parser_module_import_has__view_x_27___lambda__1___closed__2 = _init_l_lean_parser_module_import_has__view_x_27___lambda__1___closed__2();
 l_lean_parser_module_import_has__view_x_27___lambda__1___closed__3 = _init_l_lean_parser_module_import_has__view_x_27___lambda__1___closed__3();
 l_lean_parser_module_import_has__view_x_27___lambda__2___closed__1 = _init_l_lean_parser_module_import_has__view_x_27___lambda__2___closed__1();
 l_lean_parser_module_import_has__view = _init_l_lean_parser_module_import_has__view();
 l_lean_parser_module_import_parser_lean_parser_has__tokens = _init_l_lean_parser_module_import_parser_lean_parser_has__tokens();
 l_lean_parser_module_import_parser_lean_parser_has__view = _init_l_lean_parser_module_import_parser_lean_parser_has__view();
 l_lean_parser_module_import_parser___closed__1 = _init_l_lean_parser_module_import_parser___closed__1();
 l_lean_parser_module_header = _init_l_lean_parser_module_header();
 l_lean_parser_module_header_has__view_x_27 = _init_l_lean_parser_module_header_has__view_x_27();
 l_lean_parser_module_header_has__view_x_27___lambda__1___closed__1 = _init_l_lean_parser_module_header_has__view_x_27___lambda__1___closed__1();
 l_lean_parser_module_header_has__view_x_27___lambda__1___closed__2 = _init_l_lean_parser_module_header_has__view_x_27___lambda__1___closed__2();
 l_lean_parser_module_header_has__view_x_27___lambda__1___closed__3 = _init_l_lean_parser_module_header_has__view_x_27___lambda__1___closed__3();
 l_lean_parser_module_header_has__view_x_27___lambda__1___closed__4 = _init_l_lean_parser_module_header_has__view_x_27___lambda__1___closed__4();
 l_lean_parser_module_header_has__view_x_27___lambda__1___closed__5 = _init_l_lean_parser_module_header_has__view_x_27___lambda__1___closed__5();
 l_lean_parser_module_header_has__view_x_27___lambda__1___closed__6 = _init_l_lean_parser_module_header_has__view_x_27___lambda__1___closed__6();
 l_lean_parser_module_header_has__view_x_27___lambda__2___closed__1 = _init_l_lean_parser_module_header_has__view_x_27___lambda__2___closed__1();
 l_lean_parser_module_header_has__view = _init_l_lean_parser_module_header_has__view();
 l_lean_parser_module_header_parser_lean_parser_has__tokens = _init_l_lean_parser_module_header_parser_lean_parser_has__tokens();
 l_lean_parser_module_header_parser_lean_parser_has__view = _init_l_lean_parser_module_header_parser_lean_parser_has__view();
 l_lean_parser_module_header_parser___closed__1 = _init_l_lean_parser_module_header_parser___closed__1();
 l_lean_parser_monad__parsec_eoi___at___private_209794555__commands__aux___main___spec__2___closed__1 = _init_l_lean_parser_monad__parsec_eoi___at___private_209794555__commands__aux___main___spec__2___closed__1();
 l_lean_parser_monad__parsec_any___at___private_209794555__commands__aux___main___spec__3___closed__1 = _init_l_lean_parser_monad__parsec_any___at___private_209794555__commands__aux___main___spec__3___closed__1();
 l___private_209794555__commands__aux___main___lambda__1___closed__1 = _init_l___private_209794555__commands__aux___main___lambda__1___closed__1();
 l___private_209794555__commands__aux___main___lambda__3___closed__1 = _init_l___private_209794555__commands__aux___main___lambda__3___closed__1();
 l___private_209794555__commands__aux___main___lambda__9___closed__1 = _init_l___private_209794555__commands__aux___main___lambda__9___closed__1();
 l___private_209794555__commands__aux___main___lambda__10___closed__1 = _init_l___private_209794555__commands__aux___main___lambda__10___closed__1();
 l___private_209794555__commands__aux___main___lambda__11___closed__1 = _init_l___private_209794555__commands__aux___main___lambda__11___closed__1();
 l___private_209794555__commands__aux___main___lambda__11___closed__2 = _init_l___private_209794555__commands__aux___main___lambda__11___closed__2();
 l___private_209794555__commands__aux___main___lambda__11___closed__3 = _init_l___private_209794555__commands__aux___main___lambda__11___closed__3();
 l___private_209794555__commands__aux___main___lambda__13___closed__1 = _init_l___private_209794555__commands__aux___main___lambda__13___closed__1();
 l_lean_parser_module_commands_parser___closed__1 = _init_l_lean_parser_module_commands_parser___closed__1();
 l_lean_parser_module_commands_parser___closed__2 = _init_l_lean_parser_module_commands_parser___closed__2();
 l_lean_parser_module_commands_tokens = _init_l_lean_parser_module_commands_tokens();
 l_lean_parser_module_commands_parser_has__view = _init_l_lean_parser_module_commands_parser_has__view();
 l_lean_parser_module_eoi = _init_l_lean_parser_module_eoi();
 l_lean_parser_module_parser___closed__1 = _init_l_lean_parser_module_parser___closed__1();
 l_lean_parser_module_parser___closed__2 = _init_l_lean_parser_module_parser___closed__2();
 l_lean_parser_module_parser___lambda__5___closed__1 = _init_l_lean_parser_module_parser___lambda__5___closed__1();
 l_lean_parser_module_parser___lambda__6___closed__1 = _init_l_lean_parser_module_parser___lambda__6___closed__1();
 l_lean_parser_module_parser___lambda__6___closed__2 = _init_l_lean_parser_module_parser___lambda__6___closed__2();
 l_lean_parser_module_parser___lambda__10___closed__1 = _init_l_lean_parser_module_parser___lambda__10___closed__1();
 l_lean_parser_module_tokens = _init_l_lean_parser_module_tokens();
}
