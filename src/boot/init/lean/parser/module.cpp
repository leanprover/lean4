// Lean compiler output
// Module: init.lean.parser.module
// Imports: init.lean.parser.command init.control.coroutine
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
obj* l_lean_parser_module__parser__m_lean_parser_monad__parsec;
obj* l_lean_parser_module__parser__m_monad__except;
obj* l_lean_parser_module_parser___lambda__5(obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at___private_init_lean_parser_module_1__commands__aux___main___spec__1___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_module_1__commands__aux___main___lambda__15(obj*, obj*, obj*, obj*);
obj* l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__3___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_parsec__t_bind__mk__res___rarg(obj*, obj*);
obj* l_lean_parser_module_header_parser_lean_parser_has__view;
obj* l_lean_parser_module_import__path_parser___closed__1;
obj* l_lean_parser_module_parser___lambda__6(obj*, obj*, obj*, obj*);
obj* l_lean_parser_module_prelude_has__view_x_27;
obj* l_lean_parser_monad__parsec_eoi___at_lean_parser_module_parser___spec__1___lambda__1(obj*, obj*, obj*);
obj* l_list_map___main___rarg(obj*, obj*);
obj* l_lean_parser_module_import_has__view;
obj* l_lean_parser_module_parser___lambda__11(obj*, obj*, obj*, obj*);
obj* l_lean_parser_parsec__t_has__monad__lift___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_module_parser___lambda__3(obj*, obj*, obj*);
obj* l_lean_parser_command__parser__config__coe__parser__config___boxed(obj*);
extern uint8 l_true_decidable;
obj* l_lean_parser_monad__parsec_str__core___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__3(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_symbol__core___at_lean_parser_unicode__symbol_lean_parser_has__tokens___spec__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_module_1__commands__aux___main___lambda__12(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_module_commands_parser_has__view___lambda__2(obj*);
obj* l_coe__trans___rarg(obj*, obj*, obj*);
extern obj* l_lean_parser_ident_parser___at_lean_parser_command_notation__spec_fold__action_parser_lean_parser_has__tokens___spec__4___rarg___closed__1;
extern obj* l_lean_parser_combinators_many___rarg___closed__1;
obj* l___private_init_lean_parser_module_1__commands__aux___main___lambda__15___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at___private_init_lean_parser_module_1__commands__aux___main___spec__1___boxed(obj*);
obj* l_lean_parser_module_yield__command___lambda__8(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_parsec__t_monad_x_27___rarg(obj*, obj*);
obj* l_lean_parser_module_yield__command___lambda__10(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_module_yield__command___closed__1;
obj* l___private_init_lean_parser_module_1__commands__aux___main___lambda__3___closed__1;
obj* l_lean_parser_module_parser___lambda__1___boxed(obj*, obj*, obj*, obj*);
namespace lean {
obj* nat_add(obj*, obj*);
}
obj* l_lean_parser_monad__parsec_pos___at_lean_parser_module_yield__command___spec__2(obj*, obj*, obj*);
obj* l_lean_parser_module_tokens;
obj* l_list_map___main___at_lean_parser_module_commands_parser_has__view___spec__2(obj*);
obj* l_lean_parser_module_header_has__view_x_27___lambda__1___closed__2;
obj* l_coe__b___rarg(obj*, obj*);
obj* l_lean_parser_module_import__path_has__view_x_27___lambda__1___closed__4;
obj* l___private_init_lean_parser_module_1__commands__aux___main___lambda__21(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_module_import__path;
obj* l_lean_parser_module_parser___lambda__1(obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_any___at___private_init_lean_parser_module_1__commands__aux___main___spec__2___lambda__2___boxed(obj*, obj*, obj*, obj*);
extern obj* l_mjoin___rarg___closed__1;
obj* l___private_init_lean_parser_module_1__commands__aux___main___lambda__14___closed__1;
obj* l_lean_parser_module_import_parser___closed__1;
obj* l_lean_parser_module_header_has__view_x_27___lambda__1___closed__6;
extern obj* l_lean_parser_basic__parser__m_monad;
obj* l_lean_parser_with__trailing___rarg___lambda__1(obj*, obj*);
obj* l_state__t_monad__functor___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_module_header_has__view_x_27___lambda__1___closed__4;
obj* l_lean_parser_string__lit_has__view_x_27___lambda__1(obj*);
obj* l_lean_parser_module_parser___lambda__9(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__14___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_list_cons_tokens___rarg(obj*, obj*);
obj* l_coroutine_monad__reader___rarg(obj*);
obj* l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_parsec__t_try__mk__res___rarg(obj*);
obj* l_lean_parser_monad__parsec_any___at___private_init_lean_parser_module_1__commands__aux___main___spec__2(obj*, obj*, obj*);
obj* l_lean_parser_module_commands_parser___lambda__1(obj*, obj*, obj*);
obj* l___private_init_lean_parser_module_1__commands__aux___main___boxed(obj*, obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_monad__parsec_eoi___rarg___lambda__1___closed__1;
obj* l_lean_parser_module_header_has__view_x_27___lambda__2___closed__1;
extern "C" obj* lean_name_mk_string(obj*, obj*);
obj* l_lean_parser_module_import;
obj* l_lean_parser_module__parser__m_lift__parser__t___boxed(obj*);
obj* l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__5___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_module__parser__m_monad__coroutine;
obj* l_lean_parser_module_yield__command___lambda__2___boxed(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_module_1__commands__aux___main___lambda__20(uint8, obj*, obj*, obj*, obj*);
obj* l_lean_parser_parsec__t_labels__mk__res___rarg(obj*, obj*);
extern obj* l___private_init_lean_parser_combinators_1__many1__aux___main___rarg___closed__1;
obj* l___private_init_lean_parser_module_1__commands__aux___main___lambda__1(obj*, obj*, obj*);
obj* l___private_init_lean_parser_module_1__commands__aux___main(uint8, obj*, obj*, obj*, obj*);
obj* l_string_quote(obj*);
extern obj* l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
obj* l_lean_parser_module__parser__config__coe___boxed(obj*);
obj* l_lean_parser_module_header_has__view_x_27___lambda__2(obj*);
obj* l_lean_parser_combinators_many___at_lean_parser_module_import__path_parser_lean_parser_has__view___spec__1(obj*, obj*, obj*, obj*);
namespace lean {
obj* string_iterator_next(obj*);
}
obj* l_lean_parser_monad__parsec_any___at___private_init_lean_parser_module_1__commands__aux___main___spec__2___lambda__3(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_module_1__commands__aux___main___lambda__16(uint8, obj*);
obj* l_lean_parser_message__of__parsec__message___rarg(obj*, obj*);
obj* l___private_init_lean_parser_module_1__commands__aux___main___lambda__10(obj*, obj*);
obj* l_lean_parser_module_header_parser(obj*, obj*, obj*);
obj* l_lean_parser_module_parser___lambda__4(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_any___at___private_init_lean_parser_module_1__commands__aux___main___spec__2___lambda__1(obj*, uint32, obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at___private_init_lean_parser_module_1__commands__aux___main___spec__1(obj*);
obj* l_coe__t___rarg(obj*, obj*);
obj* l_lean_parser_module_import_has__view_x_27;
obj* l___private_init_lean_parser_module_1__commands__aux___main___lambda__13(obj*, obj*, obj*);
obj* l___private_init_lean_parser_module_1__commands__aux___main___lambda__2___closed__1;
obj* l_state__t_monad__state___rarg(obj*);
obj* l___private_init_lean_parser_module_1__commands__aux___main___lambda__2(obj*, obj*, obj*, obj*, obj*);
obj* l_list_map___main___at_lean_parser_module_commands_parser_has__view___spec__1(obj*);
obj* l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__9(obj*, obj*);
namespace lean {
uint32 string_iterator_curr(obj*);
}
obj* l_lean_parser_module__parser__m_monad__reader;
obj* l_lean_parser_module_yield__command___lambda__2(obj*, obj*, obj*, obj*);
obj* l_lean_parser_module_parser(obj*, obj*, obj*);
obj* l_lean_parser_module_yield__command___lambda__7___boxed(obj*, obj*, obj*, obj*);
extern obj* l_lean_name_to__string___closed__1;
extern obj* l_lean_parser_command_parser___rarg___closed__1;
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_lean_parser_module_import_has__view_x_27___lambda__1___closed__2;
obj* l_lean_parser_module_yield__command___lambda__5___boxed(obj*, obj*, obj*, obj*);
obj* l_function_comp___rarg(obj*, obj*, obj*);
obj* l_lean_parser_module__parser__config__coe(obj*);
obj* l_lean_parser_module_header_has__view_x_27___lambda__1___closed__3;
obj* l_lean_parser_module_import__path_has__view_x_27___lambda__2(obj*);
obj* l_lean_parser_module_import__path_has__view_x_27;
obj* l_lean_parser_log__message___at___private_init_lean_parser_module_1__commands__aux___main___spec__3___lambda__1(obj*, obj*, obj*, obj*);
obj* l_lean_parser_module_yield__command___lambda__7___closed__1;
obj* l_lean_parser_module_yield__command___lambda__5(obj*, obj*, obj*, obj*);
obj* l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__14(obj*, obj*, obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
obj* l___private_init_lean_parser_module_1__commands__aux___main___lambda__17(obj*, obj*, obj*);
obj* l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__8___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_reader__t_bind___at_lean_parser_with__trailing___spec__2___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_module_parser___lambda__10(obj*, obj*, obj*);
obj* l_lean_parser_module_import_has__view_x_27___lambda__1___closed__1;
obj* l___private_init_lean_parser_module_1__commands__aux___main___lambda__5___closed__1;
namespace lean {
obj* string_iterator_to_end(obj*);
}
obj* l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__5(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__11(obj*, obj*);
obj* l_lean_parser_module_prelude_has__view;
obj* l_lean_parser_tokens___rarg(obj*);
extern obj* l_lean_parser_command_parser_lean_parser_has__tokens;
obj* l_option_get__or__else___main___rarg(obj*, obj*);
obj* l_lean_parser_monad__parsec_any___at___private_init_lean_parser_module_1__commands__aux___main___spec__2___closed__1;
obj* l_lean_parser_module_header;
obj* l_lean_parser_monad__parsec_eoi___at_lean_parser_module_parser___spec__1(obj*, obj*, obj*);
extern obj* l_lean_parser_no__kind;
obj* l_lean_parser_syntax_as__node___main(obj*);
obj* l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__7(obj*, obj*);
obj* l_lean_parser_module_prelude;
obj* l_lean_parser_module_eoi;
obj* l_lean_parser_module_prelude_parser_lean_parser_has__tokens;
obj* l_monad__coroutine__trans___rarg(obj*, obj*, obj*);
obj* l_lean_parser_module_import_parser_lean_parser_has__view;
namespace lean {
uint8 string_iterator_has_next(obj*);
}
obj* l_lean_parser_module__parser__m_monad__state;
obj* l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__1___boxed(obj*, obj*);
obj* l_lean_parser_module_prelude_parser(obj*, obj*, obj*);
obj* l_lean_parser_symbol_tokens___rarg(obj*, obj*);
extern obj* l_lean_message__log_empty;
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l___private_init_lean_parser_module_1__commands__aux___main___lambda__9(obj*);
obj* l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___closed__1;
obj* l_lean_parser_mk__raw__res(obj*, obj*);
obj* l_lean_parser_module_import__path_parser_lean_parser_has__view;
extern obj* l_char_has__repr___closed__1;
obj* l_lean_parser_module__parser__m_monad;
obj* l_coroutine_bind___main___rarg(obj*, obj*, obj*);
obj* l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__6___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_module_yield__command___lambda__4(obj*, obj*, obj*);
obj* l_lean_parser_module__parser;
obj* l_lean_parser_module_yield__command(obj*, obj*, obj*, obj*);
obj* l_lean_parser_command__parser_run(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_combinators_node_view___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_pos___at_lean_parser_module_yield__command___spec__2___lambda__3(obj*, obj*, obj*, obj*);
obj* l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__10___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_log__message___at___private_init_lean_parser_module_1__commands__aux___main___spec__3(obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_pos___at_lean_parser_module_yield__command___spec__2___closed__2;
obj* l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__12(obj*, obj*, obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_finish__comment__block___closed__2;
extern obj* l_string_join___closed__1;
obj* l_reader__t_lift___at_lean_parser_with__trailing___spec__1___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_module_1__commands__aux___main___lambda__13___closed__1;
obj* l_lean_parser_monad__parsec_pos___at_lean_parser_module_yield__command___spec__2___closed__3;
obj* l___private_init_lean_parser_module_1__commands__aux___main___lambda__19(obj*, obj*, obj*, uint8, obj*, obj*, obj*);
extern obj* l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
obj* l___private_init_lean_parser_module_1__commands__aux___main___lambda__8(obj*, obj*, obj*);
obj* l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__1(obj*, obj*);
obj* l_lean_parser_command_parser___boxed(obj*);
obj* l_lean_parser_monad__parsec_pos___at_lean_parser_module_yield__command___spec__2___closed__1;
obj* l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__12___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_ident_parser___at_lean_parser_module_import__path_parser_lean_parser_has__view___spec__2(obj*, obj*, obj*);
obj* l_lean_parser_module_yield__command___lambda__3(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_syntax_mk__node(obj*, obj*);
obj* l_coroutine_yield___rarg___boxed(obj*, obj*);
obj* l_lean_parser_module_import__path_parser_lean_parser_has__view___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_module_parser___lambda__11___closed__1;
obj* l___private_init_lean_parser_module_1__commands__aux___main___lambda__19___closed__1;
obj* l_lean_parser_module_import__path_parser_lean_parser_has__view___lambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_module_commands_tokens;
obj* l_lean_parser_module__parser__m_basic__parser__m___closed__1;
obj* l_lean_parser_combinators_many1___at_lean_parser_ident__univ__spec_parser_lean_parser_has__tokens___spec__1(obj*, obj*, obj*, obj*);
obj* l_state__t_monad__except___rarg(obj*, obj*, obj*);
obj* l_lean_parser_token(obj*, obj*, obj*);
obj* l_lean_parser_whitespace(obj*, obj*, obj*);
obj* l_lean_parser_module_commands_parser(obj*, obj*, obj*);
obj* l_lean_parser_module_parser___lambda__2(obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec__trans___rarg(obj*, obj*, obj*);
obj* l_lean_parser_module_parser___lambda__5___closed__1;
namespace lean {
obj* string_iterator_offset(obj*);
}
obj* l_lean_parser_monad__parsec_pos___at_lean_parser_module_yield__command___spec__2___lambda__1(obj*, obj*);
obj* l_lean_parser_module_import_has__view_x_27___lambda__2(obj*);
obj* l_state__t_lift___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_module_parser___lambda__7(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_module_1__commands__aux___main___lambda__16___boxed(obj*, obj*);
obj* l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__4(obj*, obj*);
obj* l_state__t_monad___rarg(obj*);
obj* l___private_init_lean_parser_module_1__commands__aux___main___closed__1;
obj* l_lean_parser_combinators_node___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__15(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_module_header_parser_lean_parser_has__tokens;
obj* l___private_init_lean_parser_module_1__commands__aux___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_module_commands_parser_has__view___lambda__1(obj*);
obj* l_lean_parser_module_yield__command___lambda__9(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
extern obj* l_coroutine_monad___closed__1;
obj* l___private_init_lean_parser_module_1__commands__aux___main___lambda__22(obj*, obj*, obj*, uint8, obj*, obj*, obj*);
obj* l_lean_parser_combinators_optional___at_lean_parser_module_header_parser_lean_parser_has__view___spec__1(obj*, obj*, obj*, obj*);
obj* l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___boxed(obj*);
obj* l___private_init_lean_parser_module_1__commands__aux___main___lambda__22___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_module_header_has__view;
obj* l_lean_parser_module_commands_parser_has__view;
obj* l___private_init_lean_parser_module_1__commands__aux(uint8, obj*, obj*, obj*, obj*);
obj* l_state__t_alternative___rarg(obj*, obj*);
obj* l___private_init_lean_parser_module_1__commands__aux___main___lambda__19___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_module_import_has__view_x_27___lambda__1(obj*);
obj* l_lean_parser_module_parser___closed__1;
obj* l___private_init_lean_parser_module_1__commands__aux___main___lambda__5(obj*, obj*, obj*, obj*);
obj* l_lean_parser_module_yield__command___closed__2;
obj* l___private_init_lean_parser_module_1__commands__aux___main___lambda__3(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at___private_init_lean_parser_module_1__commands__aux___main___spec__1___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_module_import__path_has__view_x_27___lambda__1___closed__3;
obj* l_lean_parser_module_import__path_has__view_x_27___lambda__1___closed__2;
obj* l_list_map___main___at_lean_parser_module_import__path_has__view_x_27___spec__2(obj*);
obj* l_lean_parser_module_import__path_has__view_x_27___lambda__1___closed__1;
namespace lean {
obj* string_iterator_remaining(obj*);
}
extern obj* l_lean_parser_basic__parser__m_alternative;
obj* l___private_init_lean_parser_module_1__commands__aux___main___lambda__20___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__8(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_module_import_parser(obj*, obj*, obj*);
obj* l___private_init_lean_parser_module_1__commands__aux___main___lambda__7(obj*, obj*, obj*, obj*);
obj* l_lean_parser_module__parser__m_lift__parser__t___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_module_import__path_has__view_x_27___lambda__1(obj*);
obj* l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__2(obj*, obj*);
obj* l_string_trim(obj*);
obj* l_lean_parser_module_commands_parser___closed__1;
obj* l_option_get___main___at_lean_parser_run___spec__2(obj*);
obj* l_lean_parser_module__parser__m_basic__parser__m___boxed(obj*, obj*);
obj* l_lean_parser_module__parser__m_lift__parser__t___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_module_1__commands__aux___main___lambda__14(obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_ident__univ__spec_has__view_x_27___lambda__1___closed__1;
obj* l_lean_parser_monad__parsec_any___at___private_init_lean_parser_module_1__commands__aux___main___spec__2___lambda__1___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_module_import_parser_lean_parser_has__tokens;
obj* l_lean_parser_parser__core__t_lean_parser_monad__parsec___rarg(obj*);
obj* l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__13(obj*, obj*);
obj* l___private_init_lean_parser_module_1__commands__aux___main___lambda__12___closed__2;
obj* l_lean_parser_module_header_has__view_x_27___lambda__1(obj*);
obj* l_lean_parser_module_yield__command___lambda__4___boxed(obj*, obj*, obj*);
obj* l_lean_parser_module_import_has__view_x_27___lambda__2___closed__1;
obj* l_lean_parser_monad__parsec_error___at___private_init_lean_parser_module_1__commands__aux___main___spec__1___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__10(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_module_parser___lambda__8(obj*, obj*, obj*);
obj* l_lean_parser_module_parser___lambda__7___boxed(obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_parsec__t_monad__fail___rarg___closed__1;
obj* l_lean_parser_parser__core__t_alternative___rarg(obj*);
obj* l_lean_parser_module_prelude_parser_lean_parser_has__view;
obj* l_lean_parser_module_prelude_has__view_x_27___lambda__1(obj*);
obj* l_lean_parser_module_import_has__view_x_27___lambda__1___closed__3;
obj* l_lean_parser_module_header_has__view_x_27___lambda__1___closed__5;
obj* l_lean_parser_module_yield__command___lambda__7(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_module_1__commands__aux___main___lambda__4(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_pos___at_lean_parser_module_yield__command___spec__2___lambda__2(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_module_header_parser___closed__1;
obj* l_lean_parser_module__parser__m_basic__parser__m(obj*, obj*);
obj* l_lean_parser_module_import__path_has__view;
namespace lean {
obj* nat_sub(obj*, obj*);
}
obj* l_lean_parser_log__message___at___private_init_lean_parser_module_1__commands__aux___main___spec__4(obj*, obj*, obj*, obj*);
obj* l_lean_file__map_to__position(obj*, obj*);
obj* l_lean_parser_module_import__path_parser(obj*, obj*, obj*);
extern obj* l_lean_parser_basic__parser__m_lean_parser_monad__parsec;
obj* l_dlist_singleton___rarg(obj*, obj*);
extern obj* l_lean_parser_basic__parser__m_monad__except;
obj* l_lean_parser_parsec__t_orelse__mk__res___rarg(obj*, obj*);
obj* l___private_init_lean_parser_module_1__commands__aux___main___lambda__18(obj*, obj*, obj*);
obj* l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__3(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_any___at___private_init_lean_parser_module_1__commands__aux___main___spec__2___lambda__2(obj*, uint32, obj*, obj*);
obj* l___private_init_lean_parser_module_1__commands__aux___main___lambda__14___closed__2;
obj* l_list_append___rarg(obj*, obj*);
obj* l_lean_parser_module_parser___lambda__6___closed__1;
obj* l_option_map___rarg(obj*, obj*);
obj* l_lean_parser_module__parser__m_alternative;
obj* l_lean_parser_module__parser__m;
obj* l_lean_parser_module_yield__command___lambda__11(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_module_header_has__view_x_27___lambda__1___closed__1;
obj* l_lean_parser_parser__core__t_monad__except___rarg(obj*);
obj* l_list_map___main___at_lean_parser_module_import__path_has__view_x_27___spec__1(obj*);
obj* l_lean_parser_substring_of__string(obj*);
obj* l_lean_parser_monad__parsec_eoi___at_lean_parser_module_parser___spec__1___closed__1;
obj* l_lean_parser_monad__parsec_error___at___private_init_lean_parser_module_1__commands__aux___main___spec__1___rarg___lambda__2(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_module_1__commands__aux___main___lambda__11(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__6(obj*, obj*, obj*, obj*);
obj* l_lean_parser_module_yield__command___lambda__6(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1(obj*);
obj* l_char_quote__core(uint32);
obj* l_lean_parser_module_parser___closed__2;
obj* l___private_init_lean_parser_module_1__commands__aux___main___lambda__6(obj*, obj*, obj*);
obj* l_lean_parser_module_header_has__view_x_27;
obj* l_lean_parser_module_prelude_parser___closed__1;
obj* l_lean_parser_module_yield__command___lambda__1(obj*, obj*, obj*);
obj* l_lean_parser_module_import__path_parser_lean_parser_has__tokens;
obj* l_lean_parser_module__parser__m_lift__parser__t(obj*);
extern obj* l_lean_parser_raw_view___rarg___lambda__3___closed__1;
obj* l___private_init_lean_parser_module_1__commands__aux___main___lambda__12___closed__1;
obj* l_lean_parser_module__parser__config__coe(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
return x_1;
}
}
obj* l_lean_parser_module__parser__config__coe___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_module__parser__config__coe(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_lean_parser_module__parser__m_monad() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; 
x_0 = l_coroutine_monad___closed__1;
x_1 = l_state__t_monad___rarg(x_0);
x_2 = l_lean_parser_parsec__t_monad_x_27___rarg(x_1, lean::box(0));
x_3 = l_state__t_monad___rarg(x_2);
return x_3;
}
}
obj* _init_l_lean_parser_module__parser__m_alternative() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = l_coroutine_monad___closed__1;
x_1 = l_state__t_monad___rarg(x_0);
x_2 = l_lean_parser_parsec__t_monad_x_27___rarg(x_1, lean::box(0));
x_3 = l_lean_parser_parser__core__t_alternative___rarg(x_0);
x_4 = l_state__t_alternative___rarg(x_2, x_3);
return x_4;
}
}
obj* _init_l_lean_parser_module__parser__m_monad__reader() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_0 = l_coroutine_monad___closed__1;
x_1 = l_state__t_monad___rarg(x_0);
lean::inc(x_1);
x_3 = l_lean_parser_parsec__t_monad_x_27___rarg(x_1, lean::box(0));
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_monad__reader___rarg), 1, 0);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_state__t_lift___rarg___boxed), 4, 3);
lean::closure_set(x_5, 0, x_0);
lean::closure_set(x_5, 1, lean::box(0));
lean::closure_set(x_5, 2, x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parsec__t_has__monad__lift___rarg___boxed), 5, 4);
lean::closure_set(x_6, 0, x_1);
lean::closure_set(x_6, 1, lean::box(0));
lean::closure_set(x_6, 2, lean::box(0));
lean::closure_set(x_6, 3, x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_state__t_lift___rarg___boxed), 4, 3);
lean::closure_set(x_7, 0, x_3);
lean::closure_set(x_7, 1, lean::box(0));
lean::closure_set(x_7, 2, x_6);
return x_7;
}
}
obj* _init_l_lean_parser_module__parser__m_monad__state() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; 
x_0 = l_coroutine_monad___closed__1;
x_1 = l_state__t_monad___rarg(x_0);
x_2 = l_lean_parser_parsec__t_monad_x_27___rarg(x_1, lean::box(0));
x_3 = l_state__t_monad__state___rarg(x_2);
return x_3;
}
}
obj* _init_l_lean_parser_module__parser__m_lean_parser_monad__parsec() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_4; obj* x_6; obj* x_7; obj* x_8; 
x_0 = l_coroutine_monad___closed__1;
x_1 = l_state__t_monad___rarg(x_0);
x_2 = l_lean_parser_parsec__t_monad_x_27___rarg(x_1, lean::box(0));
lean::inc(x_2);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_state__t_lift___rarg___boxed), 4, 1);
lean::closure_set(x_4, 0, x_2);
lean::inc(x_2);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_state__t_monad__functor___boxed), 6, 5);
lean::closure_set(x_6, 0, lean::box(0));
lean::closure_set(x_6, 1, lean::box(0));
lean::closure_set(x_6, 2, lean::box(0));
lean::closure_set(x_6, 3, x_2);
lean::closure_set(x_6, 4, x_2);
x_7 = l_lean_parser_parser__core__t_lean_parser_monad__parsec___rarg(x_0);
x_8 = l_lean_parser_monad__parsec__trans___rarg(x_4, x_6, x_7);
return x_8;
}
}
obj* _init_l_lean_parser_module__parser__m_monad__except() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = l_coroutine_monad___closed__1;
x_1 = l_state__t_monad___rarg(x_0);
x_2 = l_lean_parser_parsec__t_monad_x_27___rarg(x_1, lean::box(0));
x_3 = l_lean_parser_parser__core__t_monad__except___rarg(x_0);
x_4 = l_state__t_monad__except___rarg(x_2, lean::box(0), x_3);
return x_4;
}
}
obj* _init_l_lean_parser_module__parser__m_monad__coroutine() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_0 = l_coroutine_monad___closed__1;
x_1 = l_state__t_monad___rarg(x_0);
lean::inc(x_1);
x_3 = l_lean_parser_parsec__t_monad_x_27___rarg(x_1, lean::box(0));
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_state__t_lift___rarg___boxed), 4, 1);
lean::closure_set(x_4, 0, x_3);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parsec__t_has__monad__lift___rarg___boxed), 5, 2);
lean::closure_set(x_5, 0, x_1);
lean::closure_set(x_5, 1, lean::box(0));
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_state__t_lift___rarg___boxed), 4, 1);
lean::closure_set(x_6, 0, x_0);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_yield___rarg___boxed), 2, 0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_monad__coroutine__trans___rarg), 3, 2);
lean::closure_set(x_8, 0, x_6);
lean::closure_set(x_8, 1, x_7);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_monad__coroutine__trans___rarg), 3, 2);
lean::closure_set(x_9, 0, x_5);
lean::closure_set(x_9, 1, x_8);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_monad__coroutine__trans___rarg), 3, 2);
lean::closure_set(x_10, 0, x_4);
lean::closure_set(x_10, 1, x_9);
return x_10;
}
}
obj* _init_l_lean_parser_module__parser__m() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* _init_l_lean_parser_module__parser() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* l_lean_parser_module__parser__m_lift__parser__t___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_8; obj* x_9; 
x_7 = lean::apply_1(x_0, x_6);
x_8 = lean::apply_3(x_2, x_7, x_4, x_5);
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
if (lean::obj_tag(x_9) == 0)
{
obj* x_11; obj* x_13; obj* x_14; obj* x_16; obj* x_18; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
x_11 = lean::cnstr_get(x_8, 1);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_release(x_8, 0);
 x_13 = x_8;
} else {
 lean::inc(x_11);
 lean::dec(x_8);
 x_13 = lean::box(0);
}
x_14 = lean::cnstr_get(x_9, 0);
x_16 = lean::cnstr_get(x_9, 1);
x_18 = lean::cnstr_get(x_9, 2);
if (lean::is_exclusive(x_9)) {
 x_20 = x_9;
} else {
 lean::inc(x_14);
 lean::inc(x_16);
 lean::inc(x_18);
 lean::dec(x_9);
 x_20 = lean::box(0);
}
if (lean::is_scalar(x_13)) {
 x_21 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_21 = x_13;
}
lean::cnstr_set(x_21, 0, x_14);
lean::cnstr_set(x_21, 1, x_3);
x_22 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_20)) {
 x_23 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_23 = x_20;
}
lean::cnstr_set(x_23, 0, x_21);
lean::cnstr_set(x_23, 1, x_16);
lean::cnstr_set(x_23, 2, x_22);
x_24 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_18, x_23);
x_25 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_11);
x_26 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_26, 0, x_25);
return x_26;
}
else
{
obj* x_28; obj* x_30; obj* x_31; uint8 x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
lean::dec(x_3);
x_28 = lean::cnstr_get(x_8, 1);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_release(x_8, 0);
 x_30 = x_8;
} else {
 lean::inc(x_28);
 lean::dec(x_8);
 x_30 = lean::box(0);
}
x_31 = lean::cnstr_get(x_9, 0);
x_33 = lean::cnstr_get_scalar<uint8>(x_9, sizeof(void*)*1);
if (lean::is_exclusive(x_9)) {
 x_34 = x_9;
} else {
 lean::inc(x_31);
 lean::dec(x_9);
 x_34 = lean::box(0);
}
if (lean::is_scalar(x_34)) {
 x_35 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_35 = x_34;
}
lean::cnstr_set(x_35, 0, x_31);
lean::cnstr_set_scalar(x_35, sizeof(void*)*1, x_33);
x_36 = x_35;
if (lean::is_scalar(x_30)) {
 x_37 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_37 = x_30;
}
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_28);
x_38 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_38, 0, x_37);
return x_38;
}
}
}
obj* l_lean_parser_module__parser__m_lift__parser__t(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___boxed), 7, 0);
return x_1;
}
}
obj* l_lean_parser_module__parser__m_lift__parser__t___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_lean_parser_module__parser__m_lift__parser__t___rarg(x_0, x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_1);
return x_7;
}
}
obj* l_lean_parser_module__parser__m_lift__parser__t___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_module__parser__m_lift__parser__t(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_lean_parser_module__parser__m_basic__parser__m___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command__parser__config__coe__parser__config___boxed), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_coe__b___rarg), 2, 1);
lean::closure_set(x_1, 0, x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__config__coe___boxed), 1, 0);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_coe__trans___rarg), 3, 2);
lean::closure_set(x_3, 0, x_2);
lean::closure_set(x_3, 1, x_1);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_coe__t___rarg), 2, 1);
lean::closure_set(x_4, 0, x_3);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module__parser__m_lift__parser__t___rarg___boxed), 7, 1);
lean::closure_set(x_5, 0, x_4);
return x_5;
}
}
obj* l_lean_parser_module__parser__m_basic__parser__m(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_parser_module__parser__m_basic__parser__m___closed__1;
return x_2;
}
}
obj* l_lean_parser_module__parser__m_basic__parser__m___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_parser_module__parser__m_basic__parser__m(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_2, 0, x_0);
return x_2;
}
}
obj* l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__2(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
if (lean::obj_tag(x_2) == 0)
{
obj* x_4; obj* x_6; obj* x_7; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_4 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 x_6 = x_1;
} else {
 lean::inc(x_4);
 lean::dec(x_1);
 x_6 = lean::box(0);
}
x_7 = lean::cnstr_get(x_2, 0);
x_9 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_release(x_2, 2);
 x_11 = x_2;
} else {
 lean::inc(x_7);
 lean::inc(x_9);
 lean::dec(x_2);
 x_11 = lean::box(0);
}
x_12 = lean::apply_1(x_0, x_7);
x_13 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_11)) {
 x_14 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_14 = x_11;
}
lean::cnstr_set(x_14, 0, x_12);
lean::cnstr_set(x_14, 1, x_9);
lean::cnstr_set(x_14, 2, x_13);
if (lean::is_scalar(x_6)) {
 x_15 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_15 = x_6;
}
lean::cnstr_set(x_15, 0, x_14);
lean::cnstr_set(x_15, 1, x_4);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__1___boxed), 2, 1);
lean::closure_set(x_16, 0, x_15);
return x_16;
}
else
{
obj* x_18; obj* x_20; obj* x_21; uint8 x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
lean::dec(x_0);
x_18 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 x_20 = x_1;
} else {
 lean::inc(x_18);
 lean::dec(x_1);
 x_20 = lean::box(0);
}
x_21 = lean::cnstr_get(x_2, 0);
x_23 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*1);
if (lean::is_exclusive(x_2)) {
 x_24 = x_2;
} else {
 lean::inc(x_21);
 lean::dec(x_2);
 x_24 = lean::box(0);
}
if (lean::is_scalar(x_24)) {
 x_25 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_25 = x_24;
}
lean::cnstr_set(x_25, 0, x_21);
lean::cnstr_set_scalar(x_25, sizeof(void*)*1, x_23);
x_26 = x_25;
if (lean::is_scalar(x_20)) {
 x_27 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_27 = x_20;
}
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_18);
x_28 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__1___boxed), 2, 1);
lean::closure_set(x_28, 0, x_27);
return x_28;
}
}
}
obj* l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; 
x_6 = lean::apply_2(x_3, x_4, x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__2), 2, 1);
lean::closure_set(x_7, 0, x_2);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_8, 0, x_6);
lean::closure_set(x_8, 1, x_7);
return x_8;
}
}
obj* l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__4(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
if (lean::obj_tag(x_2) == 0)
{
obj* x_4; obj* x_6; obj* x_7; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_4 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 x_6 = x_1;
} else {
 lean::inc(x_4);
 lean::dec(x_1);
 x_6 = lean::box(0);
}
x_7 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_release(x_2, 0);
 lean::cnstr_release(x_2, 2);
 x_9 = x_2;
} else {
 lean::inc(x_7);
 lean::dec(x_2);
 x_9 = lean::box(0);
}
x_10 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_9)) {
 x_11 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_11 = x_9;
}
lean::cnstr_set(x_11, 0, x_0);
lean::cnstr_set(x_11, 1, x_7);
lean::cnstr_set(x_11, 2, x_10);
if (lean::is_scalar(x_6)) {
 x_12 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_12 = x_6;
}
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_4);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__1___boxed), 2, 1);
lean::closure_set(x_13, 0, x_12);
return x_13;
}
else
{
obj* x_15; obj* x_17; obj* x_18; uint8 x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
lean::dec(x_0);
x_15 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 x_17 = x_1;
} else {
 lean::inc(x_15);
 lean::dec(x_1);
 x_17 = lean::box(0);
}
x_18 = lean::cnstr_get(x_2, 0);
x_20 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*1);
if (lean::is_exclusive(x_2)) {
 x_21 = x_2;
} else {
 lean::inc(x_18);
 lean::dec(x_2);
 x_21 = lean::box(0);
}
if (lean::is_scalar(x_21)) {
 x_22 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_22 = x_21;
}
lean::cnstr_set(x_22, 0, x_18);
lean::cnstr_set_scalar(x_22, sizeof(void*)*1, x_20);
x_23 = x_22;
if (lean::is_scalar(x_17)) {
 x_24 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_24 = x_17;
}
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_15);
x_25 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__1___boxed), 2, 1);
lean::closure_set(x_25, 0, x_24);
return x_25;
}
}
}
obj* l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__5(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; 
x_6 = lean::apply_2(x_3, x_4, x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__4), 2, 1);
lean::closure_set(x_7, 0, x_2);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_8, 0, x_6);
lean::closure_set(x_8, 1, x_7);
return x_8;
}
}
obj* l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__6(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_4 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_5 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_5, 0, x_1);
lean::cnstr_set(x_5, 1, x_2);
lean::cnstr_set(x_5, 2, x_4);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_3);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__1___boxed), 2, 1);
lean::closure_set(x_7, 0, x_6);
return x_7;
}
}
obj* l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__7(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
if (lean::obj_tag(x_2) == 0)
{
obj* x_4; obj* x_7; obj* x_9; obj* x_12; obj* x_13; obj* x_14; 
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::dec(x_1);
x_7 = lean::cnstr_get(x_2, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_2, 1);
lean::inc(x_9);
lean::dec(x_2);
x_12 = lean::apply_2(x_0, x_9, x_4);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__2), 2, 1);
lean::closure_set(x_13, 0, x_7);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_14, 0, x_12);
lean::closure_set(x_14, 1, x_13);
return x_14;
}
else
{
obj* x_16; obj* x_18; obj* x_19; uint8 x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
lean::dec(x_0);
x_16 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 x_18 = x_1;
} else {
 lean::inc(x_16);
 lean::dec(x_1);
 x_18 = lean::box(0);
}
x_19 = lean::cnstr_get(x_2, 0);
x_21 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*1);
if (lean::is_exclusive(x_2)) {
 x_22 = x_2;
} else {
 lean::inc(x_19);
 lean::dec(x_2);
 x_22 = lean::box(0);
}
if (lean::is_scalar(x_22)) {
 x_23 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_23 = x_22;
}
lean::cnstr_set(x_23, 0, x_19);
lean::cnstr_set_scalar(x_23, sizeof(void*)*1, x_21);
x_24 = x_23;
if (lean::is_scalar(x_18)) {
 x_25 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_25 = x_18;
}
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_16);
x_26 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__1___boxed), 2, 1);
lean::closure_set(x_26, 0, x_25);
return x_26;
}
}
}
obj* l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__8(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; 
x_6 = lean::apply_2(x_2, x_4, x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__7), 2, 1);
lean::closure_set(x_7, 0, x_3);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_8, 0, x_6);
lean::closure_set(x_8, 1, x_7);
return x_8;
}
}
obj* l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__9(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
if (lean::obj_tag(x_2) == 0)
{
obj* x_4; obj* x_7; obj* x_9; obj* x_12; obj* x_13; obj* x_14; 
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::dec(x_1);
x_7 = lean::cnstr_get(x_2, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_2, 1);
lean::inc(x_9);
lean::dec(x_2);
x_12 = lean::apply_2(x_0, x_9, x_4);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__4), 2, 1);
lean::closure_set(x_13, 0, x_7);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_14, 0, x_12);
lean::closure_set(x_14, 1, x_13);
return x_14;
}
else
{
obj* x_16; obj* x_18; obj* x_19; uint8 x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
lean::dec(x_0);
x_16 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 x_18 = x_1;
} else {
 lean::inc(x_16);
 lean::dec(x_1);
 x_18 = lean::box(0);
}
x_19 = lean::cnstr_get(x_2, 0);
x_21 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*1);
if (lean::is_exclusive(x_2)) {
 x_22 = x_2;
} else {
 lean::inc(x_19);
 lean::dec(x_2);
 x_22 = lean::box(0);
}
if (lean::is_scalar(x_22)) {
 x_23 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_23 = x_22;
}
lean::cnstr_set(x_23, 0, x_19);
lean::cnstr_set_scalar(x_23, sizeof(void*)*1, x_21);
x_24 = x_23;
if (lean::is_scalar(x_18)) {
 x_25 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_25 = x_18;
}
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_16);
x_26 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__1___boxed), 2, 1);
lean::closure_set(x_26, 0, x_25);
return x_26;
}
}
}
obj* l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__10(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; 
x_6 = lean::apply_2(x_2, x_4, x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__9), 2, 1);
lean::closure_set(x_7, 0, x_3);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_8, 0, x_6);
lean::closure_set(x_8, 1, x_7);
return x_8;
}
}
obj* l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__11(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
if (lean::obj_tag(x_2) == 0)
{
obj* x_4; obj* x_7; obj* x_10; 
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::dec(x_1);
x_7 = lean::cnstr_get(x_2, 1);
lean::inc(x_7);
lean::dec(x_2);
x_10 = lean::apply_2(x_0, x_7, x_4);
return x_10;
}
else
{
obj* x_12; obj* x_14; obj* x_15; uint8 x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
lean::dec(x_0);
x_12 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 x_14 = x_1;
} else {
 lean::inc(x_12);
 lean::dec(x_1);
 x_14 = lean::box(0);
}
x_15 = lean::cnstr_get(x_2, 0);
x_17 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*1);
if (lean::is_exclusive(x_2)) {
 x_18 = x_2;
} else {
 lean::inc(x_15);
 lean::dec(x_2);
 x_18 = lean::box(0);
}
if (lean::is_scalar(x_18)) {
 x_19 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_19 = x_18;
}
lean::cnstr_set(x_19, 0, x_15);
lean::cnstr_set_scalar(x_19, sizeof(void*)*1, x_17);
x_20 = x_19;
if (lean::is_scalar(x_14)) {
 x_21 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_21 = x_14;
}
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_12);
x_22 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__1___boxed), 2, 1);
lean::closure_set(x_22, 0, x_21);
return x_22;
}
}
}
obj* l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__12(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; 
x_6 = lean::apply_2(x_2, x_4, x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__11), 2, 1);
lean::closure_set(x_7, 0, x_3);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_8, 0, x_6);
lean::closure_set(x_8, 1, x_7);
return x_8;
}
}
obj* l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__13(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
if (lean::obj_tag(x_2) == 0)
{
obj* x_4; obj* x_7; obj* x_9; obj* x_12; 
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::dec(x_1);
x_7 = lean::cnstr_get(x_2, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_2, 1);
lean::inc(x_9);
lean::dec(x_2);
x_12 = lean::apply_3(x_0, x_7, x_9, x_4);
return x_12;
}
else
{
obj* x_14; obj* x_16; obj* x_17; uint8 x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
lean::dec(x_0);
x_14 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 x_16 = x_1;
} else {
 lean::inc(x_14);
 lean::dec(x_1);
 x_16 = lean::box(0);
}
x_17 = lean::cnstr_get(x_2, 0);
x_19 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*1);
if (lean::is_exclusive(x_2)) {
 x_20 = x_2;
} else {
 lean::inc(x_17);
 lean::dec(x_2);
 x_20 = lean::box(0);
}
if (lean::is_scalar(x_20)) {
 x_21 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_21 = x_20;
}
lean::cnstr_set(x_21, 0, x_17);
lean::cnstr_set_scalar(x_21, sizeof(void*)*1, x_19);
x_22 = x_21;
if (lean::is_scalar(x_16)) {
 x_23 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_23 = x_16;
}
lean::cnstr_set(x_23, 0, x_22);
lean::cnstr_set(x_23, 1, x_14);
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__1___boxed), 2, 1);
lean::closure_set(x_24, 0, x_23);
return x_24;
}
}
}
obj* l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__14(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; 
x_6 = lean::apply_2(x_2, x_4, x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__13), 2, 1);
lean::closure_set(x_7, 0, x_3);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_8, 0, x_6);
lean::closure_set(x_8, 1, x_7);
return x_8;
}
}
obj* _init_l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__3___boxed), 6, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__5___boxed), 6, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__6___boxed), 4, 0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__8___boxed), 6, 0);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__10___boxed), 6, 0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__12___boxed), 6, 0);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_2);
lean::cnstr_set(x_7, 1, x_3);
lean::cnstr_set(x_7, 2, x_4);
lean::cnstr_set(x_7, 3, x_5);
lean::cnstr_set(x_7, 4, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__14___boxed), 6, 0);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
return x_9;
}
}
obj* l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___closed__1;
return x_1;
}
}
obj* l_lean_parser_monad__parsec_pos___at_lean_parser_module_yield__command___spec__2___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_5; obj* x_6; 
x_2 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_0);
x_4 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_0);
lean::cnstr_set(x_4, 2, x_2);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_1);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__1___boxed), 2, 1);
lean::closure_set(x_6, 0, x_5);
return x_6;
}
}
obj* l_lean_parser_monad__parsec_pos___at_lean_parser_module_yield__command___spec__2___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_8; obj* x_11; obj* x_12; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
lean::dec(x_0);
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
lean::dec(x_5);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_2);
lean::cnstr_set(x_11, 1, x_1);
x_12 = lean::apply_4(x_8, lean::box(0), x_11, x_3, x_4);
return x_12;
}
}
obj* l_lean_parser_monad__parsec_pos___at_lean_parser_module_yield__command___spec__2___lambda__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_11; obj* x_14; obj* x_17; obj* x_18; 
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
x_9 = lean::string_iterator_offset(x_4);
lean::dec(x_4);
x_11 = lean::cnstr_get(x_0, 0);
lean::inc(x_11);
lean::dec(x_0);
x_14 = lean::cnstr_get(x_11, 1);
lean::inc(x_14);
lean::dec(x_11);
if (lean::is_scalar(x_8)) {
 x_17 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_17 = x_8;
}
lean::cnstr_set(x_17, 0, x_9);
lean::cnstr_set(x_17, 1, x_6);
x_18 = lean::apply_4(x_14, lean::box(0), x_17, x_2, x_3);
return x_18;
}
}
obj* _init_l_lean_parser_monad__parsec_pos___at_lean_parser_module_yield__command___spec__2___closed__1() {
_start:
{
obj* x_0; 
x_0 = l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___closed__1;
return x_0;
}
}
obj* _init_l_lean_parser_monad__parsec_pos___at_lean_parser_module_yield__command___spec__2___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_pos___at_lean_parser_module_yield__command___spec__2___lambda__1), 2, 0);
return x_0;
}
}
obj* _init_l_lean_parser_monad__parsec_pos___at_lean_parser_module_yield__command___spec__2___closed__3() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___closed__1;
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_pos___at_lean_parser_module_yield__command___spec__2___lambda__3), 4, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_lean_parser_monad__parsec_pos___at_lean_parser_module_yield__command___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_7; obj* x_8; obj* x_9; obj* x_11; obj* x_12; obj* x_13; 
x_3 = l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___closed__1;
x_4 = lean::cnstr_get(x_3, 1);
lean::inc(x_4);
lean::dec(x_3);
x_7 = l_lean_parser_monad__parsec_pos___at_lean_parser_module_yield__command___spec__2___closed__1;
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_pos___at_lean_parser_module_yield__command___spec__2___lambda__2), 5, 2);
lean::closure_set(x_8, 0, x_7);
lean::closure_set(x_8, 1, x_0);
x_9 = l_lean_parser_monad__parsec_pos___at_lean_parser_module_yield__command___spec__2___closed__2;
lean::inc(x_4);
x_11 = lean::apply_4(x_4, lean::box(0), lean::box(0), x_9, x_8);
x_12 = l_lean_parser_monad__parsec_pos___at_lean_parser_module_yield__command___spec__2___closed__3;
x_13 = lean::apply_6(x_4, lean::box(0), lean::box(0), x_11, x_12, x_1, x_2);
return x_13;
}
}
obj* l_lean_parser_module_yield__command___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_3 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_4 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_4, 0, x_2);
lean::cnstr_set(x_4, 1, x_0);
lean::cnstr_set(x_4, 2, x_3);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_1);
x_6 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_6, 0, x_5);
return x_6;
}
}
obj* l_lean_parser_module_yield__command___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
lean::inc(x_2);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_2);
lean::cnstr_set(x_5, 1, x_0);
x_6 = l_lean_parser_finish__comment__block___closed__2;
x_7 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_1);
lean::cnstr_set(x_7, 2, x_6);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_2);
x_9 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_9, 0, x_8);
return x_9;
}
}
obj* l_lean_parser_module_yield__command___lambda__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_5 = lean::cnstr_get(x_2, 0);
x_7 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 x_9 = x_2;
} else {
 lean::inc(x_5);
 lean::inc(x_7);
 lean::dec(x_2);
 x_9 = lean::box(0);
}
x_10 = l_lean_file__map_to__position(x_0, x_5);
if (lean::is_scalar(x_9)) {
 x_11 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_11 = x_9;
}
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_7);
x_12 = lean::apply_4(x_1, lean::box(0), x_11, x_3, x_4);
return x_12;
}
}
obj* l_lean_parser_module_yield__command___lambda__4(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_3 = lean::box(0);
x_4 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_5 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_5, 0, x_3);
lean::cnstr_set(x_5, 1, x_0);
lean::cnstr_set(x_5, 2, x_4);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_1);
x_7 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_7, 0, x_6);
return x_7;
}
}
obj* l_lean_parser_module_yield__command___lambda__5(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_yield__command___lambda__4___boxed), 3, 2);
lean::closure_set(x_4, 0, x_1);
lean::closure_set(x_4, 1, x_2);
x_5 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_5, 0, x_0);
lean::cnstr_set(x_5, 1, x_4);
return x_5;
}
}
obj* l_lean_parser_module_yield__command___lambda__6(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; 
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_2);
lean::cnstr_set(x_5, 1, x_0);
x_6 = lean::apply_4(x_1, lean::box(0), x_5, x_3, x_4);
return x_6;
}
}
obj* _init_l_lean_parser_module_yield__command___lambda__7___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = l_lean_message__log_empty;
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* l_lean_parser_module_yield__command___lambda__7(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = l_lean_parser_module_yield__command___lambda__7___closed__1;
x_5 = lean::apply_4(x_0, lean::box(0), x_4, x_2, x_3);
return x_5;
}
}
obj* l_lean_parser_module_yield__command___lambda__8(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; obj* x_10; obj* x_13; obj* x_14; obj* x_16; obj* x_18; obj* x_19; obj* x_20; 
x_8 = lean::cnstr_get(x_5, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_5, 1);
lean::inc(x_10);
lean::dec(x_5);
x_13 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_13, 0, x_0);
lean::cnstr_set(x_13, 1, x_1);
lean::cnstr_set(x_13, 2, x_2);
lean::cnstr_set(x_13, 3, x_8);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_yield__command___lambda__5___boxed), 4, 1);
lean::closure_set(x_14, 0, x_13);
lean::inc(x_3);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_yield__command___lambda__6), 5, 2);
lean::closure_set(x_16, 0, x_10);
lean::closure_set(x_16, 1, x_3);
lean::inc(x_4);
x_18 = lean::apply_4(x_4, lean::box(0), lean::box(0), x_14, x_16);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_yield__command___lambda__7___boxed), 4, 1);
lean::closure_set(x_19, 0, x_3);
x_20 = lean::apply_6(x_4, lean::box(0), lean::box(0), x_18, x_19, x_6, x_7);
return x_20;
}
}
obj* l_lean_parser_module_yield__command___lambda__9(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; obj* x_10; obj* x_13; obj* x_16; obj* x_19; obj* x_22; obj* x_25; obj* x_27; obj* x_29; obj* x_31; obj* x_32; 
x_8 = lean::cnstr_get(x_5, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_5, 1);
lean::inc(x_10);
lean::dec(x_5);
x_13 = lean::cnstr_get(x_0, 0);
lean::inc(x_13);
lean::dec(x_0);
x_16 = lean::cnstr_get(x_13, 0);
lean::inc(x_16);
lean::dec(x_13);
x_19 = lean::cnstr_get(x_16, 0);
lean::inc(x_19);
lean::dec(x_16);
x_22 = lean::cnstr_get(x_19, 2);
lean::inc(x_22);
lean::dec(x_19);
x_25 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_pos___at_lean_parser_module_yield__command___spec__2), 3, 1);
lean::closure_set(x_25, 0, x_10);
lean::inc(x_1);
x_27 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_yield__command___lambda__3), 5, 2);
lean::closure_set(x_27, 0, x_22);
lean::closure_set(x_27, 1, x_1);
lean::inc(x_2);
x_29 = lean::apply_4(x_2, lean::box(0), lean::box(0), x_25, x_27);
lean::inc(x_2);
x_31 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_yield__command___lambda__8), 8, 5);
lean::closure_set(x_31, 0, x_3);
lean::closure_set(x_31, 1, x_4);
lean::closure_set(x_31, 2, x_8);
lean::closure_set(x_31, 3, x_1);
lean::closure_set(x_31, 4, x_2);
x_32 = lean::apply_6(x_2, lean::box(0), lean::box(0), x_29, x_31, x_6, x_7);
return x_32;
}
}
obj* l_lean_parser_module_yield__command___lambda__10(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_9; obj* x_12; obj* x_14; obj* x_15; 
x_7 = lean::cnstr_get(x_4, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_4, 1);
lean::inc(x_9);
lean::dec(x_4);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_yield__command___lambda__2___boxed), 4, 1);
lean::closure_set(x_12, 0, x_9);
lean::inc(x_2);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_yield__command___lambda__9), 8, 5);
lean::closure_set(x_14, 0, x_0);
lean::closure_set(x_14, 1, x_1);
lean::closure_set(x_14, 2, x_2);
lean::closure_set(x_14, 3, x_3);
lean::closure_set(x_14, 4, x_7);
x_15 = lean::apply_6(x_2, lean::box(0), lean::box(0), x_12, x_14, x_5, x_6);
return x_15;
}
}
obj* l_lean_parser_module_yield__command___lambda__11(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_8; obj* x_10; obj* x_11; obj* x_14; obj* x_18; obj* x_20; obj* x_22; obj* x_23; 
x_6 = lean::cnstr_get(x_3, 0);
x_8 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 x_10 = x_3;
} else {
 lean::inc(x_6);
 lean::inc(x_8);
 lean::dec(x_3);
 x_10 = lean::box(0);
}
x_11 = lean::cnstr_get(x_0, 0);
lean::inc(x_11);
lean::dec(x_0);
x_14 = lean::cnstr_get(x_11, 1);
lean::inc(x_14);
lean::dec(x_11);
lean::inc(x_8);
if (lean::is_scalar(x_10)) {
 x_18 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_18 = x_10;
}
lean::cnstr_set(x_18, 0, x_8);
lean::cnstr_set(x_18, 1, x_8);
lean::inc(x_14);
x_20 = lean::apply_2(x_14, lean::box(0), x_18);
lean::inc(x_1);
x_22 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_yield__command___lambda__10), 7, 4);
lean::closure_set(x_22, 0, x_6);
lean::closure_set(x_22, 1, x_14);
lean::closure_set(x_22, 2, x_1);
lean::closure_set(x_22, 3, x_2);
x_23 = lean::apply_6(x_1, lean::box(0), lean::box(0), x_20, x_22, x_4, x_5);
return x_23;
}
}
obj* _init_l_lean_parser_module_yield__command___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_yield__command___lambda__1), 3, 0);
return x_0;
}
}
obj* _init_l_lean_parser_module_yield__command___closed__2() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___closed__1;
x_1 = lean::cnstr_get(x_0, 1);
lean::inc(x_1);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_parser_module_yield__command(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_8; obj* x_9; obj* x_10; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_4 = l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___closed__1;
x_5 = lean::cnstr_get(x_4, 1);
lean::inc(x_5);
lean::dec(x_4);
x_8 = l_lean_parser_monad__parsec_pos___at_lean_parser_module_yield__command___spec__2___closed__1;
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_pos___at_lean_parser_module_yield__command___spec__2___lambda__2), 5, 2);
lean::closure_set(x_9, 0, x_8);
lean::closure_set(x_9, 1, x_1);
x_10 = l_lean_parser_module_yield__command___closed__1;
lean::inc(x_5);
x_12 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_10, x_9);
x_13 = l_lean_parser_module_yield__command___closed__2;
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_yield__command___lambda__11), 6, 3);
lean::closure_set(x_14, 0, x_8);
lean::closure_set(x_14, 1, x_13);
lean::closure_set(x_14, 2, x_0);
x_15 = lean::apply_6(x_5, lean::box(0), lean::box(0), x_12, x_14, x_2, x_3);
return x_15;
}
}
obj* l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__1(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__3___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__3(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_0);
lean::dec(x_1);
return x_6;
}
}
obj* l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__5___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__5(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_0);
lean::dec(x_1);
return x_6;
}
}
obj* l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__6___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__6(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__8___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__8(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_0);
lean::dec(x_1);
return x_6;
}
}
obj* l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__10___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__10(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_0);
lean::dec(x_1);
return x_6;
}
}
obj* l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__12___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__12(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_0);
lean::dec(x_1);
return x_6;
}
}
obj* l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__14___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__14(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_0);
lean::dec(x_1);
return x_6;
}
}
obj* l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_parser_module_yield__command___lambda__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_parser_module_yield__command___lambda__2(x_0, x_1, x_2, x_3);
lean::dec(x_3);
return x_4;
}
}
obj* l_lean_parser_module_yield__command___lambda__4___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_parser_module_yield__command___lambda__4(x_0, x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_lean_parser_module_yield__command___lambda__5___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_parser_module_yield__command___lambda__5(x_0, x_1, x_2, x_3);
lean::dec(x_3);
return x_4;
}
}
obj* l_lean_parser_module_yield__command___lambda__7___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_parser_module_yield__command___lambda__7(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* _init_l_lean_parser_module_prelude() {
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
x_7 = lean::mk_string("prelude");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* l_lean_parser_module_prelude_has__view_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = l_lean_parser_raw_view___rarg___lambda__3___closed__1;
x_2 = l_option_map___rarg(x_1, x_0);
x_3 = lean::box(3);
x_4 = l_option_get__or__else___main___rarg(x_2, x_3);
lean::dec(x_2);
x_6 = lean::box(0);
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_4);
lean::cnstr_set(x_7, 1, x_6);
x_8 = l_lean_parser_module_prelude;
x_9 = l_lean_parser_syntax_mk__node(x_8, x_7);
return x_9;
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
obj* _init_l_lean_parser_module_prelude_has__view() {
_start:
{
obj* x_0; 
x_0 = l_lean_parser_module_prelude_has__view_x_27;
return x_0;
}
}
obj* _init_l_lean_parser_module_prelude_parser_lean_parser_has__view() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_0 = lean::mk_string("prelude");
x_1 = l_string_trim(x_0);
lean::inc(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_3, 0, x_1);
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_unicode__symbol_lean_parser_has__tokens___spec__1___boxed), 6, 3);
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
x_14 = l_lean_parser_combinators_node_view___rarg(x_8, x_9, x_10, x_11, x_12, x_7, x_13);
lean::dec(x_7);
return x_14;
}
}
obj* _init_l_lean_parser_module_prelude_parser_lean_parser_has__tokens() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_6; 
x_0 = lean::mk_string("prelude");
x_1 = lean::mk_nat_obj(0u);
x_2 = l_lean_parser_symbol_tokens___rarg(x_0, x_1);
x_3 = lean::box(0);
x_4 = l_lean_parser_list_cons_tokens___rarg(x_2, x_3);
lean::dec(x_2);
x_6 = l_lean_parser_tokens___rarg(x_4);
lean::dec(x_4);
return x_6;
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
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_unicode__symbol_lean_parser_has__tokens___spec__1___boxed), 6, 3);
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
obj* l_lean_parser_module_prelude_parser(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = l_lean_parser_module_prelude;
x_4 = l_lean_parser_module_prelude_parser___closed__1;
x_5 = l_lean_parser_combinators_node___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__15(x_3, x_4, x_0, x_1, x_2);
return x_5;
}
}
obj* _init_l_lean_parser_module_import__path() {
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
x_7 = lean::mk_string("import_path");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* l_list_map___main___at_lean_parser_module_import__path_has__view_x_27___spec__1(obj* x_0) {
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
obj* x_2; obj* x_4; obj* x_6; obj* x_7; 
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
x_7 = l_list_map___main___at_lean_parser_module_import__path_has__view_x_27___spec__1(x_4);
switch (lean::obj_tag(x_2)) {
case 0:
{
obj* x_8; obj* x_11; obj* x_12; 
x_8 = lean::cnstr_get(x_2, 0);
lean::inc(x_8);
lean::dec(x_2);
x_11 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_11, 0, x_8);
if (lean::is_scalar(x_6)) {
 x_12 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_12 = x_6;
}
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_7);
return x_12;
}
case 3:
{
obj* x_13; obj* x_14; 
x_13 = lean::box(0);
if (lean::is_scalar(x_6)) {
 x_14 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_14 = x_6;
}
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_7);
return x_14;
}
default:
{
obj* x_16; obj* x_17; 
lean::dec(x_2);
x_16 = lean::box(0);
if (lean::is_scalar(x_6)) {
 x_17 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_17 = x_6;
}
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_7);
return x_17;
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
obj* x_1; 
x_1 = lean::box(0);
return x_1;
}
else
{
obj* x_2; obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_12; obj* x_13; 
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
x_7 = l_lean_parser_raw_view___rarg___lambda__3___closed__1;
x_8 = l_option_map___rarg(x_7, x_2);
x_9 = lean::box(3);
x_10 = l_option_get__or__else___main___rarg(x_8, x_9);
lean::dec(x_8);
x_12 = l_list_map___main___at_lean_parser_module_import__path_has__view_x_27___spec__2(x_4);
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
obj* _init_l_lean_parser_module_import__path_has__view_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_0 = lean::box(0);
x_1 = lean::box(0);
x_2 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
x_3 = lean::mk_string("NOT_AN_IDENT");
lean::inc(x_3);
x_5 = l_lean_parser_substring_of__string(x_3);
x_6 = lean::box(0);
x_7 = lean_name_mk_string(x_6, x_3);
x_8 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_8, 0, x_0);
lean::cnstr_set(x_8, 1, x_5);
lean::cnstr_set(x_8, 2, x_7);
lean::cnstr_set(x_8, 3, x_1);
lean::cnstr_set(x_8, 4, x_1);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_2);
lean::cnstr_set(x_9, 1, x_8);
return x_9;
}
}
obj* _init_l_lean_parser_module_import__path_has__view_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; 
x_0 = l_lean_parser_module_import__path_has__view_x_27___lambda__1___closed__1;
return x_0;
}
}
obj* _init_l_lean_parser_module_import__path_has__view_x_27___lambda__1___closed__3() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::box(0);
x_2 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
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
if (lean::obj_tag(x_0) == 0)
{
obj* x_6; 
x_6 = l_lean_parser_module_import__path_has__view_x_27___lambda__1___closed__2;
return x_6;
}
else
{
obj* x_7; 
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
lean::dec(x_0);
switch (lean::obj_tag(x_7)) {
case 1:
{
obj* x_10; obj* x_13; obj* x_14; 
x_10 = lean::cnstr_get(x_7, 0);
lean::inc(x_10);
lean::dec(x_7);
x_13 = l_lean_parser_module_import__path_has__view_x_27___lambda__1___closed__3;
x_14 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_10);
return x_14;
}
case 3:
{
obj* x_15; 
x_15 = l_lean_parser_module_import__path_has__view_x_27___lambda__1___closed__2;
return x_15;
}
default:
{
obj* x_17; 
lean::dec(x_7);
x_17 = l_lean_parser_module_import__path_has__view_x_27___lambda__1___closed__2;
return x_17;
}
}
}
}
else
{
obj* x_18; obj* x_21; obj* x_24; 
x_18 = lean::cnstr_get(x_5, 0);
lean::inc(x_18);
lean::dec(x_5);
x_21 = lean::cnstr_get(x_18, 1);
lean::inc(x_21);
lean::dec(x_18);
x_24 = l_list_map___main___at_lean_parser_module_import__path_has__view_x_27___spec__1(x_21);
if (lean::obj_tag(x_0) == 0)
{
obj* x_25; obj* x_26; 
x_25 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
x_26 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_26, 0, x_24);
lean::cnstr_set(x_26, 1, x_25);
return x_26;
}
else
{
obj* x_27; 
x_27 = lean::cnstr_get(x_0, 0);
lean::inc(x_27);
lean::dec(x_0);
switch (lean::obj_tag(x_27)) {
case 1:
{
obj* x_30; obj* x_33; 
x_30 = lean::cnstr_get(x_27, 0);
lean::inc(x_30);
lean::dec(x_27);
x_33 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_33, 0, x_24);
lean::cnstr_set(x_33, 1, x_30);
return x_33;
}
case 3:
{
obj* x_34; obj* x_35; 
x_34 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
x_35 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_35, 0, x_24);
lean::cnstr_set(x_35, 1, x_34);
return x_35;
}
default:
{
obj* x_37; obj* x_38; 
lean::dec(x_27);
x_37 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
x_38 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_38, 0, x_24);
lean::cnstr_set(x_38, 1, x_37);
return x_38;
}
}
}
}
}
}
}
obj* l_lean_parser_module_import__path_has__view_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_4 = l_lean_parser_syntax_as__node___main(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; 
x_5 = l_lean_parser_module_import__path_has__view_x_27___lambda__1___closed__4;
return x_5;
}
else
{
obj* x_6; obj* x_9; 
x_6 = lean::cnstr_get(x_4, 0);
lean::inc(x_6);
lean::dec(x_4);
x_9 = lean::cnstr_get(x_6, 1);
lean::inc(x_9);
lean::dec(x_6);
if (lean::obj_tag(x_9) == 0)
{
obj* x_12; 
x_12 = lean::box(3);
x_1 = x_9;
x_2 = x_12;
goto lbl_3;
}
else
{
obj* x_13; obj* x_15; 
x_13 = lean::cnstr_get(x_9, 0);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_9, 1);
lean::inc(x_15);
lean::dec(x_9);
x_1 = x_15;
x_2 = x_13;
goto lbl_3;
}
}
lbl_3:
{
obj* x_18; 
x_18 = l_lean_parser_syntax_as__node___main(x_2);
if (lean::obj_tag(x_18) == 0)
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_19; 
x_19 = l_lean_parser_module_import__path_has__view_x_27___lambda__1___closed__2;
return x_19;
}
else
{
obj* x_20; 
x_20 = lean::cnstr_get(x_1, 0);
lean::inc(x_20);
lean::dec(x_1);
switch (lean::obj_tag(x_20)) {
case 1:
{
obj* x_23; obj* x_26; obj* x_27; 
x_23 = lean::cnstr_get(x_20, 0);
lean::inc(x_23);
lean::dec(x_20);
x_26 = l_lean_parser_module_import__path_has__view_x_27___lambda__1___closed__3;
x_27 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_23);
return x_27;
}
case 3:
{
obj* x_28; 
x_28 = l_lean_parser_module_import__path_has__view_x_27___lambda__1___closed__2;
return x_28;
}
default:
{
obj* x_30; 
lean::dec(x_20);
x_30 = l_lean_parser_module_import__path_has__view_x_27___lambda__1___closed__2;
return x_30;
}
}
}
}
else
{
obj* x_31; obj* x_34; obj* x_37; 
x_31 = lean::cnstr_get(x_18, 0);
lean::inc(x_31);
lean::dec(x_18);
x_34 = lean::cnstr_get(x_31, 1);
lean::inc(x_34);
lean::dec(x_31);
x_37 = l_list_map___main___at_lean_parser_module_import__path_has__view_x_27___spec__1(x_34);
if (lean::obj_tag(x_1) == 0)
{
obj* x_38; obj* x_39; 
x_38 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
x_39 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_39, 0, x_37);
lean::cnstr_set(x_39, 1, x_38);
return x_39;
}
else
{
obj* x_40; 
x_40 = lean::cnstr_get(x_1, 0);
lean::inc(x_40);
lean::dec(x_1);
switch (lean::obj_tag(x_40)) {
case 1:
{
obj* x_43; obj* x_46; 
x_43 = lean::cnstr_get(x_40, 0);
lean::inc(x_43);
lean::dec(x_40);
x_46 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_46, 0, x_37);
lean::cnstr_set(x_46, 1, x_43);
return x_46;
}
case 3:
{
obj* x_47; obj* x_48; 
x_47 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
x_48 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_48, 0, x_37);
lean::cnstr_set(x_48, 1, x_47);
return x_48;
}
default:
{
obj* x_50; obj* x_51; 
lean::dec(x_40);
x_50 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
x_51 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_51, 0, x_37);
lean::cnstr_set(x_51, 1, x_50);
return x_51;
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
obj* x_1; obj* x_3; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
x_6 = l_list_map___main___at_lean_parser_module_import__path_has__view_x_27___spec__2(x_1);
x_7 = l_lean_parser_no__kind;
x_8 = l_lean_parser_syntax_mk__node(x_7, x_6);
x_9 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_9, 0, x_3);
x_10 = lean::box(0);
x_11 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_11, 0, x_9);
lean::cnstr_set(x_11, 1, x_10);
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_8);
lean::cnstr_set(x_12, 1, x_11);
x_13 = l_lean_parser_module_import__path;
x_14 = l_lean_parser_syntax_mk__node(x_13, x_12);
return x_14;
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
obj* _init_l_lean_parser_module_import__path_has__view() {
_start:
{
obj* x_0; 
x_0 = l_lean_parser_module_import__path_has__view_x_27;
return x_0;
}
}
obj* l_lean_parser_combinators_many___at_lean_parser_module_import__path_parser_lean_parser_has__view___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; obj* x_6; 
lean::inc(x_2);
x_5 = l_lean_parser_combinators_many1___at_lean_parser_ident__univ__spec_parser_lean_parser_has__tokens___spec__1(x_0, x_1, x_2, x_3);
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
if (lean::obj_tag(x_6) == 0)
{
obj* x_9; obj* x_11; obj* x_12; 
lean::dec(x_2);
x_9 = lean::cnstr_get(x_5, 1);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 x_11 = x_5;
} else {
 lean::inc(x_9);
 lean::dec(x_5);
 x_11 = lean::box(0);
}
if (lean::is_scalar(x_11)) {
 x_12 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_12 = x_11;
}
lean::cnstr_set(x_12, 0, x_6);
lean::cnstr_set(x_12, 1, x_9);
return x_12;
}
else
{
uint8 x_13; 
x_13 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*1);
if (x_13 == 0)
{
obj* x_14; obj* x_16; obj* x_17; obj* x_20; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
x_14 = lean::cnstr_get(x_5, 1);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 x_16 = x_5;
} else {
 lean::inc(x_14);
 lean::dec(x_5);
 x_16 = lean::box(0);
}
x_17 = lean::cnstr_get(x_6, 0);
lean::inc(x_17);
lean::dec(x_6);
x_20 = lean::cnstr_get(x_17, 2);
lean::inc(x_20);
lean::dec(x_17);
x_23 = l_mjoin___rarg___closed__1;
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_24, 0, x_20);
lean::closure_set(x_24, 1, x_23);
x_25 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_25, 0, x_24);
x_26 = l_lean_parser_combinators_many___rarg___closed__1;
x_27 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_2);
lean::cnstr_set(x_27, 2, x_25);
if (lean::is_scalar(x_16)) {
 x_28 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_28 = x_16;
}
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_14);
return x_28;
}
else
{
obj* x_30; obj* x_32; obj* x_33; 
lean::dec(x_2);
x_30 = lean::cnstr_get(x_5, 1);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 x_32 = x_5;
} else {
 lean::inc(x_30);
 lean::dec(x_5);
 x_32 = lean::box(0);
}
if (lean::is_scalar(x_32)) {
 x_33 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_33 = x_32;
}
lean::cnstr_set(x_33, 0, x_6);
lean::cnstr_set(x_33, 1, x_30);
return x_33;
}
}
}
}
obj* l_lean_parser_ident_parser___at_lean_parser_module_import__path_parser_lean_parser_has__view___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_5; obj* x_6; 
lean::inc(x_1);
lean::inc(x_0);
x_5 = l_lean_parser_token(x_0, x_1, x_2);
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
if (lean::obj_tag(x_6) == 0)
{
obj* x_8; obj* x_10; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_18; 
x_8 = lean::cnstr_get(x_5, 1);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 lean::cnstr_set(x_5, 1, lean::box(0));
 x_10 = x_5;
} else {
 lean::inc(x_8);
 lean::dec(x_5);
 x_10 = lean::box(0);
}
x_11 = lean::cnstr_get(x_6, 0);
x_13 = lean::cnstr_get(x_6, 1);
x_15 = lean::cnstr_get(x_6, 2);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_set(x_6, 0, lean::box(0));
 lean::cnstr_set(x_6, 1, lean::box(0));
 lean::cnstr_set(x_6, 2, lean::box(0));
 x_17 = x_6;
} else {
 lean::inc(x_11);
 lean::inc(x_13);
 lean::inc(x_15);
 lean::dec(x_6);
 x_17 = lean::box(0);
}
switch (lean::obj_tag(x_11)) {
case 1:
{
obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
lean::dec(x_1);
lean::dec(x_0);
x_22 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_17)) {
 x_23 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_23 = x_17;
}
lean::cnstr_set(x_23, 0, x_11);
lean::cnstr_set(x_23, 1, x_13);
lean::cnstr_set(x_23, 2, x_22);
x_24 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_23);
x_25 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_22, x_24);
x_26 = l_lean_parser_ident_parser___at_lean_parser_command_notation__spec_fold__action_parser_lean_parser_has__tokens___spec__4___rarg___closed__1;
x_27 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_25, x_26);
x_28 = l_lean_parser_parsec__t_try__mk__res___rarg(x_27);
if (lean::is_scalar(x_10)) {
 x_29 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_29 = x_10;
}
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_8);
return x_29;
}
case 3:
{
obj* x_32; 
lean::dec(x_17);
lean::dec(x_10);
x_32 = lean::box(0);
x_18 = x_32;
goto lbl_19;
}
default:
{
obj* x_36; 
lean::dec(x_17);
lean::dec(x_10);
lean::dec(x_11);
x_36 = lean::box(0);
x_18 = x_36;
goto lbl_19;
}
}
lbl_19:
{
obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_46; obj* x_48; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; 
lean::dec(x_18);
x_38 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_38, 0, x_1);
x_39 = lean::box(0);
x_40 = l_string_join___closed__1;
x_41 = l_lean_parser_ident_parser___at_lean_parser_command_notation__spec_fold__action_parser_lean_parser_has__tokens___spec__4___rarg___closed__1;
x_42 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_40, x_41, x_38, x_39, x_0, x_13, x_8);
lean::dec(x_13);
lean::dec(x_0);
lean::dec(x_38);
x_46 = lean::cnstr_get(x_42, 0);
x_48 = lean::cnstr_get(x_42, 1);
if (lean::is_exclusive(x_42)) {
 x_50 = x_42;
} else {
 lean::inc(x_46);
 lean::inc(x_48);
 lean::dec(x_42);
 x_50 = lean::box(0);
}
x_51 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_46);
x_52 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_53 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_52, x_51);
x_54 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_53, x_41);
x_55 = l_lean_parser_parsec__t_try__mk__res___rarg(x_54);
if (lean::is_scalar(x_50)) {
 x_56 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_56 = x_50;
}
lean::cnstr_set(x_56, 0, x_55);
lean::cnstr_set(x_56, 1, x_48);
return x_56;
}
}
else
{
obj* x_59; obj* x_61; obj* x_62; uint8 x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; 
lean::dec(x_1);
lean::dec(x_0);
x_59 = lean::cnstr_get(x_5, 1);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 x_61 = x_5;
} else {
 lean::inc(x_59);
 lean::dec(x_5);
 x_61 = lean::box(0);
}
x_62 = lean::cnstr_get(x_6, 0);
x_64 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*1);
if (lean::is_exclusive(x_6)) {
 x_65 = x_6;
} else {
 lean::inc(x_62);
 lean::dec(x_6);
 x_65 = lean::box(0);
}
if (lean::is_scalar(x_65)) {
 x_66 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_66 = x_65;
}
lean::cnstr_set(x_66, 0, x_62);
lean::cnstr_set_scalar(x_66, sizeof(void*)*1, x_64);
x_67 = x_66;
x_68 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_69 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_68, x_67);
x_70 = l_lean_parser_ident_parser___at_lean_parser_command_notation__spec_fold__action_parser_lean_parser_has__tokens___spec__4___rarg___closed__1;
x_71 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_69, x_70);
x_72 = l_lean_parser_parsec__t_try__mk__res___rarg(x_71);
if (lean::is_scalar(x_61)) {
 x_73 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_73 = x_61;
}
lean::cnstr_set(x_73, 0, x_72);
lean::cnstr_set(x_73, 1, x_59);
return x_73;
}
}
}
obj* l_lean_parser_module_import__path_parser_lean_parser_has__view___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = l_lean_name_to__string___closed__1;
x_6 = l_lean_parser_monad__parsec_str__core___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__3(x_5, x_0, x_2, x_3, x_4);
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
if (lean::obj_tag(x_7) == 0)
{
obj* x_9; obj* x_11; obj* x_12; obj* x_14; obj* x_16; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_9 = lean::cnstr_get(x_6, 1);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 x_11 = x_6;
} else {
 lean::inc(x_9);
 lean::dec(x_6);
 x_11 = lean::box(0);
}
x_12 = lean::cnstr_get(x_7, 1);
x_14 = lean::cnstr_get(x_7, 2);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 x_16 = x_7;
} else {
 lean::inc(x_12);
 lean::inc(x_14);
 lean::dec(x_7);
 x_16 = lean::box(0);
}
lean::inc(x_12);
x_18 = l_lean_parser_mk__raw__res(x_1, x_12);
x_19 = l_lean_parser_finish__comment__block___closed__2;
if (lean::is_scalar(x_16)) {
 x_20 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_20 = x_16;
}
lean::cnstr_set(x_20, 0, x_18);
lean::cnstr_set(x_20, 1, x_12);
lean::cnstr_set(x_20, 2, x_19);
x_21 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_14, x_20);
if (lean::is_scalar(x_11)) {
 x_22 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_22 = x_11;
}
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_9);
return x_22;
}
else
{
obj* x_24; obj* x_26; obj* x_27; uint8 x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; 
lean::dec(x_1);
x_24 = lean::cnstr_get(x_6, 1);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 x_26 = x_6;
} else {
 lean::inc(x_24);
 lean::dec(x_6);
 x_26 = lean::box(0);
}
x_27 = lean::cnstr_get(x_7, 0);
x_29 = lean::cnstr_get_scalar<uint8>(x_7, sizeof(void*)*1);
if (lean::is_exclusive(x_7)) {
 x_30 = x_7;
} else {
 lean::inc(x_27);
 lean::dec(x_7);
 x_30 = lean::box(0);
}
if (lean::is_scalar(x_30)) {
 x_31 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_31 = x_30;
}
lean::cnstr_set(x_31, 0, x_27);
lean::cnstr_set_scalar(x_31, sizeof(void*)*1, x_29);
x_32 = x_31;
if (lean::is_scalar(x_26)) {
 x_33 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_33 = x_26;
}
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_24);
return x_33;
}
}
}
obj* _init_l_lean_parser_module_import__path_parser_lean_parser_has__view() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_0 = lean::mk_string(".");
x_1 = l_string_quote(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_2, 0, x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_with__trailing___rarg___lambda__1), 2, 0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_lift___at_lean_parser_with__trailing___spec__1___rarg___boxed), 4, 1);
lean::closure_set(x_4, 0, x_3);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_import__path_parser_lean_parser_has__view___lambda__1___boxed), 5, 1);
lean::closure_set(x_5, 0, x_2);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_bind___at_lean_parser_with__trailing___spec__2___rarg), 5, 2);
lean::closure_set(x_6, 0, x_4);
lean::closure_set(x_6, 1, x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_many___at_lean_parser_module_import__path_parser_lean_parser_has__view___spec__1), 4, 1);
lean::closure_set(x_7, 0, x_6);
x_8 = lean::box(0);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_ident_parser___at_lean_parser_module_import__path_parser_lean_parser_has__view___spec__2), 3, 0);
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
x_18 = l_lean_parser_combinators_node_view___rarg(x_12, x_13, x_14, x_15, x_16, x_11, x_17);
lean::dec(x_11);
return x_18;
}
}
obj* l_lean_parser_module_import__path_parser_lean_parser_has__view___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_lean_parser_module_import__path_parser_lean_parser_has__view___lambda__1(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* _init_l_lean_parser_module_import__path_parser_lean_parser_has__tokens() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_6; 
x_0 = lean::box(0);
x_1 = l_lean_parser_tokens___rarg(x_0);
x_2 = l_lean_parser_list_cons_tokens___rarg(x_0, x_0);
x_3 = l_lean_parser_list_cons_tokens___rarg(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
x_6 = l_lean_parser_tokens___rarg(x_3);
lean::dec(x_3);
return x_6;
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
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_lift___at_lean_parser_with__trailing___spec__1___rarg___boxed), 4, 1);
lean::closure_set(x_4, 0, x_3);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_import__path_parser_lean_parser_has__view___lambda__1___boxed), 5, 1);
lean::closure_set(x_5, 0, x_2);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_bind___at_lean_parser_with__trailing___spec__2___rarg), 5, 2);
lean::closure_set(x_6, 0, x_4);
lean::closure_set(x_6, 1, x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_many___at_lean_parser_module_import__path_parser_lean_parser_has__view___spec__1), 4, 1);
lean::closure_set(x_7, 0, x_6);
x_8 = lean::box(0);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_ident_parser___at_lean_parser_module_import__path_parser_lean_parser_has__view___spec__2), 3, 0);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_8);
x_11 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_11, 0, x_7);
lean::cnstr_set(x_11, 1, x_10);
return x_11;
}
}
obj* l_lean_parser_module_import__path_parser(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = l_lean_parser_module_import__path;
x_4 = l_lean_parser_module_import__path_parser___closed__1;
x_5 = l_lean_parser_combinators_node___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__15(x_3, x_4, x_0, x_1, x_2);
return x_5;
}
}
obj* _init_l_lean_parser_module_import() {
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
x_7 = lean::mk_string("import");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_lean_parser_module_import_has__view_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_0 = l_lean_parser_module_import__path_has__view;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
x_4 = lean::box(3);
x_5 = lean::apply_1(x_1, x_4);
x_6 = lean::box(0);
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_6);
return x_7;
}
}
obj* _init_l_lean_parser_module_import_has__view_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = l_lean_parser_module_import__path_has__view;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
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
obj* x_5; obj* x_6; 
x_5 = l_lean_parser_module_import_has__view_x_27___lambda__1___closed__1;
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_0);
lean::cnstr_set(x_6, 1, x_5);
return x_6;
}
else
{
obj* x_7; obj* x_10; obj* x_13; obj* x_14; obj* x_15; 
x_7 = lean::cnstr_get(x_4, 0);
lean::inc(x_7);
lean::dec(x_4);
x_10 = lean::cnstr_get(x_7, 1);
lean::inc(x_10);
lean::dec(x_7);
x_13 = l_lean_parser_module_import_has__view_x_27___lambda__1___closed__2;
x_14 = l_list_map___main___rarg(x_13, x_10);
x_15 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_15, 0, x_0);
lean::cnstr_set(x_15, 1, x_14);
return x_15;
}
}
}
}
obj* l_lean_parser_module_import_has__view_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_4; obj* x_6; 
x_6 = l_lean_parser_syntax_as__node___main(x_0);
if (lean::obj_tag(x_6) == 0)
{
obj* x_7; 
x_7 = l_lean_parser_module_import_has__view_x_27___lambda__1___closed__3;
return x_7;
}
else
{
obj* x_8; obj* x_10; obj* x_11; 
x_8 = lean::cnstr_get(x_6, 0);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_set(x_6, 0, lean::box(0));
 x_10 = x_6;
} else {
 lean::inc(x_8);
 lean::dec(x_6);
 x_10 = lean::box(0);
}
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
lean::dec(x_8);
if (lean::obj_tag(x_11) == 0)
{
lean::dec(x_10);
if (lean::obj_tag(x_11) == 0)
{
obj* x_15; 
x_15 = l_lean_parser_module_import_has__view_x_27___lambda__1___closed__3;
return x_15;
}
else
{
obj* x_16; obj* x_19; 
x_16 = lean::cnstr_get(x_11, 0);
lean::inc(x_16);
lean::dec(x_11);
x_19 = lean::box(0);
x_3 = x_19;
x_4 = x_16;
goto lbl_5;
}
}
else
{
obj* x_20; 
x_20 = lean::cnstr_get(x_11, 0);
lean::inc(x_20);
switch (lean::obj_tag(x_20)) {
case 0:
{
obj* x_22; obj* x_25; obj* x_28; 
x_22 = lean::cnstr_get(x_11, 1);
lean::inc(x_22);
lean::dec(x_11);
x_25 = lean::cnstr_get(x_20, 0);
lean::inc(x_25);
lean::dec(x_20);
if (lean::is_scalar(x_10)) {
 x_28 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_28 = x_10;
}
lean::cnstr_set(x_28, 0, x_25);
if (lean::obj_tag(x_22) == 0)
{
x_1 = x_28;
goto lbl_2;
}
else
{
obj* x_29; 
x_29 = lean::cnstr_get(x_22, 0);
lean::inc(x_29);
lean::dec(x_22);
x_3 = x_28;
x_4 = x_29;
goto lbl_5;
}
}
case 3:
{
obj* x_33; 
lean::dec(x_10);
x_33 = lean::cnstr_get(x_11, 1);
lean::inc(x_33);
lean::dec(x_11);
if (lean::obj_tag(x_33) == 0)
{
obj* x_36; 
x_36 = l_lean_parser_module_import_has__view_x_27___lambda__1___closed__3;
return x_36;
}
else
{
obj* x_37; obj* x_40; 
x_37 = lean::cnstr_get(x_33, 0);
lean::inc(x_37);
lean::dec(x_33);
x_40 = lean::box(0);
x_3 = x_40;
x_4 = x_37;
goto lbl_5;
}
}
default:
{
obj* x_43; 
lean::dec(x_10);
lean::dec(x_20);
x_43 = lean::cnstr_get(x_11, 1);
lean::inc(x_43);
lean::dec(x_11);
if (lean::obj_tag(x_43) == 0)
{
obj* x_46; 
x_46 = l_lean_parser_module_import_has__view_x_27___lambda__1___closed__3;
return x_46;
}
else
{
obj* x_47; obj* x_50; 
x_47 = lean::cnstr_get(x_43, 0);
lean::inc(x_47);
lean::dec(x_43);
x_50 = lean::box(0);
x_3 = x_50;
x_4 = x_47;
goto lbl_5;
}
}
}
}
}
lbl_2:
{
obj* x_51; obj* x_52; 
x_51 = lean::box(3);
x_52 = l_lean_parser_syntax_as__node___main(x_51);
if (lean::obj_tag(x_52) == 0)
{
obj* x_53; obj* x_54; 
x_53 = l_lean_parser_module_import_has__view_x_27___lambda__1___closed__1;
x_54 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_54, 0, x_1);
lean::cnstr_set(x_54, 1, x_53);
return x_54;
}
else
{
obj* x_55; obj* x_58; obj* x_61; obj* x_62; obj* x_63; 
x_55 = lean::cnstr_get(x_52, 0);
lean::inc(x_55);
lean::dec(x_52);
x_58 = lean::cnstr_get(x_55, 1);
lean::inc(x_58);
lean::dec(x_55);
x_61 = l_lean_parser_module_import_has__view_x_27___lambda__1___closed__2;
x_62 = l_list_map___main___rarg(x_61, x_58);
x_63 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_63, 0, x_1);
lean::cnstr_set(x_63, 1, x_62);
return x_63;
}
}
lbl_5:
{
obj* x_64; 
x_64 = l_lean_parser_syntax_as__node___main(x_4);
if (lean::obj_tag(x_64) == 0)
{
obj* x_65; obj* x_66; 
x_65 = l_lean_parser_module_import_has__view_x_27___lambda__1___closed__1;
x_66 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_66, 0, x_3);
lean::cnstr_set(x_66, 1, x_65);
return x_66;
}
else
{
obj* x_67; obj* x_70; obj* x_73; obj* x_74; obj* x_75; 
x_67 = lean::cnstr_get(x_64, 0);
lean::inc(x_67);
lean::dec(x_64);
x_70 = lean::cnstr_get(x_67, 1);
lean::inc(x_70);
lean::dec(x_67);
x_73 = l_lean_parser_module_import_has__view_x_27___lambda__1___closed__2;
x_74 = l_list_map___main___rarg(x_73, x_70);
x_75 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_75, 0, x_3);
lean::cnstr_set(x_75, 1, x_74);
return x_75;
}
}
}
}
obj* _init_l_lean_parser_module_import_has__view_x_27___lambda__2___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = l_lean_parser_module_import__path_has__view;
x_1 = lean::cnstr_get(x_0, 1);
lean::inc(x_1);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_parser_module_import_has__view_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
x_6 = l_lean_parser_raw_view___rarg___lambda__3___closed__1;
x_7 = l_option_map___rarg(x_6, x_1);
x_8 = lean::box(3);
x_9 = l_option_get__or__else___main___rarg(x_7, x_8);
lean::dec(x_7);
x_11 = l_lean_parser_module_import_has__view_x_27___lambda__2___closed__1;
x_12 = l_list_map___main___rarg(x_11, x_3);
x_13 = l_lean_parser_no__kind;
x_14 = l_lean_parser_syntax_mk__node(x_13, x_12);
x_15 = lean::box(0);
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_15);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_9);
lean::cnstr_set(x_17, 1, x_16);
x_18 = l_lean_parser_module_import;
x_19 = l_lean_parser_syntax_mk__node(x_18, x_17);
return x_19;
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
obj* _init_l_lean_parser_module_import_has__view() {
_start:
{
obj* x_0; 
x_0 = l_lean_parser_module_import_has__view_x_27;
return x_0;
}
}
obj* _init_l_lean_parser_module_import_parser_lean_parser_has__view() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_0 = lean::mk_string("import");
x_1 = l_string_trim(x_0);
lean::inc(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_3, 0, x_1);
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_unicode__symbol_lean_parser_has__tokens___spec__1___boxed), 6, 3);
lean::closure_set(x_5, 0, x_1);
lean::closure_set(x_5, 1, x_4);
lean::closure_set(x_5, 2, x_3);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_import__path_parser), 3, 0);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_many1___at_lean_parser_ident__univ__spec_parser_lean_parser_has__tokens___spec__1), 4, 1);
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
x_17 = l_lean_parser_combinators_node_view___rarg(x_11, x_12, x_13, x_14, x_15, x_10, x_16);
lean::dec(x_10);
return x_17;
}
}
obj* _init_l_lean_parser_module_import_parser_lean_parser_has__tokens() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_8; obj* x_11; 
x_0 = lean::mk_string("import");
x_1 = lean::mk_nat_obj(0u);
x_2 = l_lean_parser_symbol_tokens___rarg(x_0, x_1);
x_3 = l_lean_parser_module_import__path_parser_lean_parser_has__tokens;
x_4 = l_lean_parser_tokens___rarg(x_3);
x_5 = lean::box(0);
x_6 = l_lean_parser_list_cons_tokens___rarg(x_4, x_5);
lean::dec(x_4);
x_8 = l_lean_parser_list_cons_tokens___rarg(x_2, x_6);
lean::dec(x_6);
lean::dec(x_2);
x_11 = l_lean_parser_tokens___rarg(x_8);
lean::dec(x_8);
return x_11;
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
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_unicode__symbol_lean_parser_has__tokens___spec__1___boxed), 6, 3);
lean::closure_set(x_5, 0, x_1);
lean::closure_set(x_5, 1, x_4);
lean::closure_set(x_5, 2, x_3);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_import__path_parser), 3, 0);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_many1___at_lean_parser_ident__univ__spec_parser_lean_parser_has__tokens___spec__1), 4, 1);
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
obj* l_lean_parser_module_import_parser(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = l_lean_parser_module_import;
x_4 = l_lean_parser_module_import_parser___closed__1;
x_5 = l_lean_parser_combinators_node___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__15(x_3, x_4, x_0, x_1, x_2);
return x_5;
}
}
obj* _init_l_lean_parser_module_header() {
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
x_7 = lean::mk_string("header");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_lean_parser_module_header_has__view_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_0 = l_lean_parser_module_import_has__view;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
x_4 = lean::box(3);
x_5 = lean::apply_1(x_1, x_4);
x_6 = lean::box(0);
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_6);
return x_7;
}
}
obj* _init_l_lean_parser_module_header_has__view_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = l_lean_parser_module_import_has__view;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_lean_parser_module_header_has__view_x_27___lambda__1___closed__3() {
_start:
{
obj* x_0; obj* x_2; obj* x_3; obj* x_6; obj* x_7; obj* x_8; 
x_2 = l_lean_parser_module_prelude_has__view;
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
lean::dec(x_2);
x_6 = lean::box(3);
x_7 = lean::apply_1(x_3, x_6);
x_8 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_8, 0, x_7);
x_0 = x_8;
goto lbl_1;
lbl_1:
{
obj* x_9; obj* x_10; 
x_9 = lean::box(3);
x_10 = l_lean_parser_syntax_as__node___main(x_9);
if (lean::obj_tag(x_10) == 0)
{
obj* x_11; obj* x_12; 
x_11 = l_lean_parser_module_header_has__view_x_27___lambda__1___closed__1;
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_0);
lean::cnstr_set(x_12, 1, x_11);
return x_12;
}
else
{
obj* x_13; obj* x_16; obj* x_19; obj* x_20; obj* x_21; 
x_13 = lean::cnstr_get(x_10, 0);
lean::inc(x_13);
lean::dec(x_10);
x_16 = lean::cnstr_get(x_13, 1);
lean::inc(x_16);
lean::dec(x_13);
x_19 = l_lean_parser_module_header_has__view_x_27___lambda__1___closed__2;
x_20 = l_list_map___main___rarg(x_19, x_16);
x_21 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_21, 0, x_0);
lean::cnstr_set(x_21, 1, x_20);
return x_21;
}
}
}
}
obj* _init_l_lean_parser_module_header_has__view_x_27___lambda__1___closed__4() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; 
x_0 = l_lean_parser_module_prelude_has__view;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
x_4 = lean::box(3);
x_5 = lean::apply_1(x_1, x_4);
x_6 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_6, 0, x_5);
return x_6;
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
obj* x_5; obj* x_6; 
x_5 = l_lean_parser_module_header_has__view_x_27___lambda__1___closed__1;
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_0);
lean::cnstr_set(x_6, 1, x_5);
return x_6;
}
else
{
obj* x_7; obj* x_10; obj* x_13; obj* x_14; obj* x_15; 
x_7 = lean::cnstr_get(x_4, 0);
lean::inc(x_7);
lean::dec(x_4);
x_10 = lean::cnstr_get(x_7, 1);
lean::inc(x_10);
lean::dec(x_7);
x_13 = l_lean_parser_module_header_has__view_x_27___lambda__1___closed__2;
x_14 = l_list_map___main___rarg(x_13, x_10);
x_15 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_15, 0, x_0);
lean::cnstr_set(x_15, 1, x_14);
return x_15;
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
obj* x_12; obj* x_13; 
x_12 = l_lean_parser_module_header_has__view_x_27___lambda__1___closed__1;
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_0);
lean::cnstr_set(x_13, 1, x_12);
return x_13;
}
else
{
obj* x_14; obj* x_17; obj* x_20; obj* x_21; obj* x_22; 
x_14 = lean::cnstr_get(x_11, 0);
lean::inc(x_14);
lean::dec(x_11);
x_17 = lean::cnstr_get(x_14, 1);
lean::inc(x_17);
lean::dec(x_14);
x_20 = l_lean_parser_module_header_has__view_x_27___lambda__1___closed__2;
x_21 = l_list_map___main___rarg(x_20, x_17);
x_22 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_22, 0, x_0);
lean::cnstr_set(x_22, 1, x_21);
return x_22;
}
}
lbl_4:
{
obj* x_23; 
x_23 = l_lean_parser_syntax_as__node___main(x_3);
if (lean::obj_tag(x_23) == 0)
{
obj* x_24; obj* x_25; 
x_24 = l_lean_parser_module_header_has__view_x_27___lambda__1___closed__1;
x_25 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_25, 0, x_2);
lean::cnstr_set(x_25, 1, x_24);
return x_25;
}
else
{
obj* x_26; obj* x_29; obj* x_32; obj* x_33; obj* x_34; 
x_26 = lean::cnstr_get(x_23, 0);
lean::inc(x_26);
lean::dec(x_23);
x_29 = lean::cnstr_get(x_26, 1);
lean::inc(x_29);
lean::dec(x_26);
x_32 = l_lean_parser_module_header_has__view_x_27___lambda__1___closed__2;
x_33 = l_list_map___main___rarg(x_32, x_29);
x_34 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_34, 0, x_2);
lean::cnstr_set(x_34, 1, x_33);
return x_34;
}
}
lbl_7:
{
obj* x_35; 
x_35 = l_lean_parser_syntax_as__node___main(x_6);
if (lean::obj_tag(x_35) == 0)
{
if (lean::obj_tag(x_5) == 0)
{
obj* x_36; 
x_36 = l_lean_parser_module_header_has__view_x_27___lambda__1___closed__3;
return x_36;
}
else
{
obj* x_37; obj* x_40; 
x_37 = lean::cnstr_get(x_5, 0);
lean::inc(x_37);
lean::dec(x_5);
x_40 = l_lean_parser_module_header_has__view_x_27___lambda__1___closed__4;
x_2 = x_40;
x_3 = x_37;
goto lbl_4;
}
}
else
{
obj* x_41; obj* x_43; obj* x_44; 
x_41 = lean::cnstr_get(x_35, 0);
if (lean::is_exclusive(x_35)) {
 lean::cnstr_set(x_35, 0, lean::box(0));
 x_43 = x_35;
} else {
 lean::inc(x_41);
 lean::dec(x_35);
 x_43 = lean::box(0);
}
x_44 = lean::cnstr_get(x_41, 1);
lean::inc(x_44);
lean::dec(x_41);
if (lean::obj_tag(x_44) == 0)
{
lean::dec(x_43);
if (lean::obj_tag(x_5) == 0)
{
obj* x_48; 
x_48 = l_lean_parser_module_header_has__view_x_27___lambda__1___closed__5;
return x_48;
}
else
{
obj* x_49; obj* x_52; 
x_49 = lean::cnstr_get(x_5, 0);
lean::inc(x_49);
lean::dec(x_5);
x_52 = lean::box(0);
x_2 = x_52;
x_3 = x_49;
goto lbl_4;
}
}
else
{
obj* x_53; 
x_53 = lean::cnstr_get(x_44, 1);
lean::inc(x_53);
if (lean::obj_tag(x_53) == 0)
{
obj* x_55; obj* x_58; obj* x_59; obj* x_62; obj* x_63; 
x_55 = lean::cnstr_get(x_44, 0);
lean::inc(x_55);
lean::dec(x_44);
x_58 = l_lean_parser_module_prelude_has__view;
x_59 = lean::cnstr_get(x_58, 0);
lean::inc(x_59);
lean::dec(x_58);
x_62 = lean::apply_1(x_59, x_55);
if (lean::is_scalar(x_43)) {
 x_63 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_63 = x_43;
}
lean::cnstr_set(x_63, 0, x_62);
if (lean::obj_tag(x_5) == 0)
{
x_0 = x_63;
goto lbl_1;
}
else
{
obj* x_64; 
x_64 = lean::cnstr_get(x_5, 0);
lean::inc(x_64);
lean::dec(x_5);
x_2 = x_63;
x_3 = x_64;
goto lbl_4;
}
}
else
{
lean::dec(x_43);
lean::dec(x_44);
lean::dec(x_53);
if (lean::obj_tag(x_5) == 0)
{
obj* x_70; 
x_70 = l_lean_parser_module_header_has__view_x_27___lambda__1___closed__3;
return x_70;
}
else
{
obj* x_71; obj* x_74; 
x_71 = lean::cnstr_get(x_5, 0);
lean::inc(x_71);
lean::dec(x_5);
x_74 = l_lean_parser_module_header_has__view_x_27___lambda__1___closed__4;
x_2 = x_74;
x_3 = x_71;
goto lbl_4;
}
}
}
}
}
}
}
obj* l_lean_parser_module_header_has__view_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_9; 
x_9 = l_lean_parser_syntax_as__node___main(x_0);
if (lean::obj_tag(x_9) == 0)
{
obj* x_10; 
x_10 = l_lean_parser_module_header_has__view_x_27___lambda__1___closed__6;
return x_10;
}
else
{
obj* x_11; obj* x_14; 
x_11 = lean::cnstr_get(x_9, 0);
lean::inc(x_11);
lean::dec(x_9);
x_14 = lean::cnstr_get(x_11, 1);
lean::inc(x_14);
lean::dec(x_11);
if (lean::obj_tag(x_14) == 0)
{
obj* x_17; 
x_17 = lean::box(3);
x_6 = x_14;
x_7 = x_17;
goto lbl_8;
}
else
{
obj* x_18; obj* x_20; 
x_18 = lean::cnstr_get(x_14, 0);
lean::inc(x_18);
x_20 = lean::cnstr_get(x_14, 1);
lean::inc(x_20);
lean::dec(x_14);
x_6 = x_20;
x_7 = x_18;
goto lbl_8;
}
}
lbl_2:
{
obj* x_23; obj* x_24; 
x_23 = lean::box(3);
x_24 = l_lean_parser_syntax_as__node___main(x_23);
if (lean::obj_tag(x_24) == 0)
{
obj* x_25; obj* x_26; 
x_25 = l_lean_parser_module_header_has__view_x_27___lambda__1___closed__1;
x_26 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_26, 0, x_1);
lean::cnstr_set(x_26, 1, x_25);
return x_26;
}
else
{
obj* x_27; obj* x_30; obj* x_33; obj* x_34; obj* x_35; 
x_27 = lean::cnstr_get(x_24, 0);
lean::inc(x_27);
lean::dec(x_24);
x_30 = lean::cnstr_get(x_27, 1);
lean::inc(x_30);
lean::dec(x_27);
x_33 = l_lean_parser_module_header_has__view_x_27___lambda__1___closed__2;
x_34 = l_list_map___main___rarg(x_33, x_30);
x_35 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_35, 0, x_1);
lean::cnstr_set(x_35, 1, x_34);
return x_35;
}
}
lbl_5:
{
obj* x_36; 
x_36 = l_lean_parser_syntax_as__node___main(x_4);
if (lean::obj_tag(x_36) == 0)
{
obj* x_37; obj* x_38; 
x_37 = l_lean_parser_module_header_has__view_x_27___lambda__1___closed__1;
x_38 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_38, 0, x_3);
lean::cnstr_set(x_38, 1, x_37);
return x_38;
}
else
{
obj* x_39; obj* x_42; obj* x_45; obj* x_46; obj* x_47; 
x_39 = lean::cnstr_get(x_36, 0);
lean::inc(x_39);
lean::dec(x_36);
x_42 = lean::cnstr_get(x_39, 1);
lean::inc(x_42);
lean::dec(x_39);
x_45 = l_lean_parser_module_header_has__view_x_27___lambda__1___closed__2;
x_46 = l_list_map___main___rarg(x_45, x_42);
x_47 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_47, 0, x_3);
lean::cnstr_set(x_47, 1, x_46);
return x_47;
}
}
lbl_8:
{
obj* x_48; 
x_48 = l_lean_parser_syntax_as__node___main(x_7);
if (lean::obj_tag(x_48) == 0)
{
if (lean::obj_tag(x_6) == 0)
{
obj* x_49; 
x_49 = l_lean_parser_module_header_has__view_x_27___lambda__1___closed__3;
return x_49;
}
else
{
obj* x_50; obj* x_53; 
x_50 = lean::cnstr_get(x_6, 0);
lean::inc(x_50);
lean::dec(x_6);
x_53 = l_lean_parser_module_header_has__view_x_27___lambda__1___closed__4;
x_3 = x_53;
x_4 = x_50;
goto lbl_5;
}
}
else
{
obj* x_54; obj* x_56; obj* x_57; 
x_54 = lean::cnstr_get(x_48, 0);
if (lean::is_exclusive(x_48)) {
 lean::cnstr_set(x_48, 0, lean::box(0));
 x_56 = x_48;
} else {
 lean::inc(x_54);
 lean::dec(x_48);
 x_56 = lean::box(0);
}
x_57 = lean::cnstr_get(x_54, 1);
lean::inc(x_57);
lean::dec(x_54);
if (lean::obj_tag(x_57) == 0)
{
lean::dec(x_56);
if (lean::obj_tag(x_6) == 0)
{
obj* x_61; 
x_61 = l_lean_parser_module_header_has__view_x_27___lambda__1___closed__5;
return x_61;
}
else
{
obj* x_62; obj* x_65; 
x_62 = lean::cnstr_get(x_6, 0);
lean::inc(x_62);
lean::dec(x_6);
x_65 = lean::box(0);
x_3 = x_65;
x_4 = x_62;
goto lbl_5;
}
}
else
{
obj* x_66; 
x_66 = lean::cnstr_get(x_57, 1);
lean::inc(x_66);
if (lean::obj_tag(x_66) == 0)
{
obj* x_68; obj* x_71; obj* x_72; obj* x_75; obj* x_76; 
x_68 = lean::cnstr_get(x_57, 0);
lean::inc(x_68);
lean::dec(x_57);
x_71 = l_lean_parser_module_prelude_has__view;
x_72 = lean::cnstr_get(x_71, 0);
lean::inc(x_72);
lean::dec(x_71);
x_75 = lean::apply_1(x_72, x_68);
if (lean::is_scalar(x_56)) {
 x_76 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_76 = x_56;
}
lean::cnstr_set(x_76, 0, x_75);
if (lean::obj_tag(x_6) == 0)
{
x_1 = x_76;
goto lbl_2;
}
else
{
obj* x_77; 
x_77 = lean::cnstr_get(x_6, 0);
lean::inc(x_77);
lean::dec(x_6);
x_3 = x_76;
x_4 = x_77;
goto lbl_5;
}
}
else
{
lean::dec(x_66);
lean::dec(x_56);
lean::dec(x_57);
if (lean::obj_tag(x_6) == 0)
{
obj* x_83; 
x_83 = l_lean_parser_module_header_has__view_x_27___lambda__1___closed__3;
return x_83;
}
else
{
obj* x_84; obj* x_87; 
x_84 = lean::cnstr_get(x_6, 0);
lean::inc(x_84);
lean::dec(x_6);
x_87 = l_lean_parser_module_header_has__view_x_27___lambda__1___closed__4;
x_3 = x_87;
x_4 = x_84;
goto lbl_5;
}
}
}
}
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
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_parser_module_header_has__view_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
x_6 = l_lean_parser_module_header_has__view_x_27___lambda__2___closed__1;
x_7 = l_list_map___main___rarg(x_6, x_3);
x_8 = l_lean_parser_no__kind;
x_9 = l_lean_parser_syntax_mk__node(x_8, x_7);
x_10 = lean::box(0);
x_11 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_11, 0, x_9);
lean::cnstr_set(x_11, 1, x_10);
if (lean::obj_tag(x_1) == 0)
{
obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_12 = l_lean_parser_combinators_many___rarg___closed__1;
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_11);
x_14 = l_lean_parser_module_header;
x_15 = l_lean_parser_syntax_mk__node(x_14, x_13);
return x_15;
}
else
{
obj* x_16; obj* x_19; obj* x_20; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
x_16 = lean::cnstr_get(x_1, 0);
lean::inc(x_16);
lean::dec(x_1);
x_19 = l_lean_parser_module_prelude_has__view;
x_20 = lean::cnstr_get(x_19, 1);
lean::inc(x_20);
lean::dec(x_19);
x_23 = lean::apply_1(x_20, x_16);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_10);
x_25 = l_lean_parser_syntax_mk__node(x_8, x_24);
x_26 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_11);
x_27 = l_lean_parser_module_header;
x_28 = l_lean_parser_syntax_mk__node(x_27, x_26);
return x_28;
}
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
obj* _init_l_lean_parser_module_header_has__view() {
_start:
{
obj* x_0; 
x_0 = l_lean_parser_module_header_has__view_x_27;
return x_0;
}
}
obj* l_lean_parser_combinators_optional___at_lean_parser_module_header_parser_lean_parser_has__view___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_12; obj* x_13; 
x_7 = lean::box(0);
lean::inc(x_2);
x_12 = lean::apply_3(x_0, x_1, x_2, x_3);
x_13 = lean::cnstr_get(x_12, 0);
lean::inc(x_13);
if (lean::obj_tag(x_13) == 0)
{
if (lean::obj_tag(x_13) == 0)
{
obj* x_15; obj* x_18; obj* x_20; obj* x_22; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
x_15 = lean::cnstr_get(x_12, 1);
lean::inc(x_15);
lean::dec(x_12);
x_18 = lean::cnstr_get(x_13, 0);
x_20 = lean::cnstr_get(x_13, 1);
x_22 = lean::cnstr_get(x_13, 2);
if (lean::is_exclusive(x_13)) {
 x_24 = x_13;
} else {
 lean::inc(x_18);
 lean::inc(x_20);
 lean::inc(x_22);
 lean::dec(x_13);
 x_24 = lean::box(0);
}
x_25 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_25, 0, x_18);
x_26 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_24)) {
 x_27 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_27 = x_24;
}
lean::cnstr_set(x_27, 0, x_25);
lean::cnstr_set(x_27, 1, x_20);
lean::cnstr_set(x_27, 2, x_26);
x_28 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_22, x_27);
x_8 = x_28;
x_9 = x_15;
goto lbl_10;
}
else
{
obj* x_29; obj* x_32; uint8 x_34; obj* x_35; obj* x_36; obj* x_37; 
x_29 = lean::cnstr_get(x_12, 1);
lean::inc(x_29);
lean::dec(x_12);
x_32 = lean::cnstr_get(x_13, 0);
x_34 = lean::cnstr_get_scalar<uint8>(x_13, sizeof(void*)*1);
if (lean::is_exclusive(x_13)) {
 x_35 = x_13;
} else {
 lean::inc(x_32);
 lean::dec(x_13);
 x_35 = lean::box(0);
}
if (lean::is_scalar(x_35)) {
 x_36 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_36 = x_35;
}
lean::cnstr_set(x_36, 0, x_32);
lean::cnstr_set_scalar(x_36, sizeof(void*)*1, x_34);
x_37 = x_36;
x_8 = x_37;
x_9 = x_29;
goto lbl_10;
}
}
else
{
obj* x_38; obj* x_41; uint8 x_43; obj* x_44; obj* x_45; obj* x_47; obj* x_49; obj* x_51; obj* x_54; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
x_38 = lean::cnstr_get(x_12, 1);
lean::inc(x_38);
lean::dec(x_12);
x_41 = lean::cnstr_get(x_13, 0);
x_43 = lean::cnstr_get_scalar<uint8>(x_13, sizeof(void*)*1);
if (lean::is_exclusive(x_13)) {
 lean::cnstr_set(x_13, 0, lean::box(0));
 x_44 = x_13;
} else {
 lean::inc(x_41);
 lean::dec(x_13);
 x_44 = lean::box(0);
}
x_45 = lean::cnstr_get(x_41, 0);
lean::inc(x_45);
x_47 = lean::cnstr_get(x_41, 1);
lean::inc(x_47);
x_49 = lean::cnstr_get(x_41, 2);
lean::inc(x_49);
x_51 = lean::cnstr_get(x_41, 3);
lean::inc(x_51);
lean::dec(x_41);
x_54 = l_option_get___main___at_lean_parser_run___spec__2(x_51);
lean::dec(x_51);
x_56 = lean::box(0);
x_57 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_57, 0, x_54);
lean::cnstr_set(x_57, 1, x_56);
x_58 = l_lean_parser_no__kind;
x_59 = l_lean_parser_syntax_mk__node(x_58, x_57);
x_60 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_60, 0, x_59);
x_61 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_61, 0, x_45);
lean::cnstr_set(x_61, 1, x_47);
lean::cnstr_set(x_61, 2, x_49);
lean::cnstr_set(x_61, 3, x_60);
if (x_43 == 0)
{
uint8 x_62; obj* x_63; obj* x_64; 
x_62 = 0;
if (lean::is_scalar(x_44)) {
 x_63 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_63 = x_44;
}
lean::cnstr_set(x_63, 0, x_61);
lean::cnstr_set_scalar(x_63, sizeof(void*)*1, x_62);
x_64 = x_63;
x_8 = x_64;
x_9 = x_38;
goto lbl_10;
}
else
{
obj* x_65; obj* x_66; 
if (lean::is_scalar(x_44)) {
 x_65 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_65 = x_44;
}
lean::cnstr_set(x_65, 0, x_61);
lean::cnstr_set_scalar(x_65, sizeof(void*)*1, x_43);
x_66 = x_65;
x_8 = x_66;
x_9 = x_38;
goto lbl_10;
}
}
lbl_6:
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_67; 
x_67 = lean::cnstr_get(x_4, 0);
lean::inc(x_67);
if (lean::obj_tag(x_67) == 0)
{
obj* x_69; obj* x_71; obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; 
x_69 = lean::cnstr_get(x_4, 1);
x_71 = lean::cnstr_get(x_4, 2);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_73 = x_4;
} else {
 lean::inc(x_69);
 lean::inc(x_71);
 lean::dec(x_4);
 x_73 = lean::box(0);
}
x_74 = l_lean_parser_combinators_many___rarg___closed__1;
x_75 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_73)) {
 x_76 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_76 = x_73;
}
lean::cnstr_set(x_76, 0, x_74);
lean::cnstr_set(x_76, 1, x_69);
lean::cnstr_set(x_76, 2, x_75);
x_77 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_71, x_76);
x_78 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_78, 0, x_77);
lean::cnstr_set(x_78, 1, x_5);
return x_78;
}
else
{
obj* x_79; obj* x_81; obj* x_83; obj* x_84; obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; 
x_79 = lean::cnstr_get(x_4, 1);
x_81 = lean::cnstr_get(x_4, 2);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_83 = x_4;
} else {
 lean::inc(x_79);
 lean::inc(x_81);
 lean::dec(x_4);
 x_83 = lean::box(0);
}
x_84 = lean::cnstr_get(x_67, 0);
lean::inc(x_84);
lean::dec(x_67);
x_87 = lean::box(0);
x_88 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_88, 0, x_84);
lean::cnstr_set(x_88, 1, x_87);
x_89 = l_lean_parser_no__kind;
x_90 = l_lean_parser_syntax_mk__node(x_89, x_88);
x_91 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_83)) {
 x_92 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_92 = x_83;
}
lean::cnstr_set(x_92, 0, x_90);
lean::cnstr_set(x_92, 1, x_79);
lean::cnstr_set(x_92, 2, x_91);
x_93 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_81, x_92);
x_94 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_94, 0, x_93);
lean::cnstr_set(x_94, 1, x_5);
return x_94;
}
}
else
{
obj* x_95; uint8 x_97; obj* x_98; obj* x_99; obj* x_100; obj* x_101; 
x_95 = lean::cnstr_get(x_4, 0);
x_97 = lean::cnstr_get_scalar<uint8>(x_4, sizeof(void*)*1);
if (lean::is_exclusive(x_4)) {
 x_98 = x_4;
} else {
 lean::inc(x_95);
 lean::dec(x_4);
 x_98 = lean::box(0);
}
if (lean::is_scalar(x_98)) {
 x_99 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_99 = x_98;
}
lean::cnstr_set(x_99, 0, x_95);
lean::cnstr_set_scalar(x_99, sizeof(void*)*1, x_97);
x_100 = x_99;
x_101 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_101, 0, x_100);
lean::cnstr_set(x_101, 1, x_5);
return x_101;
}
}
lbl_10:
{
if (lean::obj_tag(x_8) == 0)
{
lean::dec(x_2);
x_4 = x_8;
x_5 = x_9;
goto lbl_6;
}
else
{
uint8 x_103; 
x_103 = lean::cnstr_get_scalar<uint8>(x_8, sizeof(void*)*1);
if (x_103 == 0)
{
obj* x_104; obj* x_107; obj* x_110; obj* x_111; obj* x_112; obj* x_113; 
x_104 = lean::cnstr_get(x_8, 0);
lean::inc(x_104);
lean::dec(x_8);
x_107 = lean::cnstr_get(x_104, 2);
lean::inc(x_107);
lean::dec(x_104);
x_110 = l_mjoin___rarg___closed__1;
x_111 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_111, 0, x_107);
lean::closure_set(x_111, 1, x_110);
x_112 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_112, 0, x_111);
x_113 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_113, 0, x_7);
lean::cnstr_set(x_113, 1, x_2);
lean::cnstr_set(x_113, 2, x_112);
x_4 = x_113;
x_5 = x_9;
goto lbl_6;
}
else
{
lean::dec(x_2);
x_4 = x_8;
x_5 = x_9;
goto lbl_6;
}
}
}
}
}
obj* _init_l_lean_parser_module_header_parser_lean_parser_has__view() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_prelude_parser), 3, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_optional___at_lean_parser_module_header_parser_lean_parser_has__view___spec__1), 4, 1);
lean::closure_set(x_1, 0, x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_import_parser), 3, 0);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_many___at_lean_parser_module_import__path_parser_lean_parser_has__view___spec__1), 4, 1);
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
x_13 = l_lean_parser_combinators_node_view___rarg(x_7, x_8, x_9, x_10, x_11, x_6, x_12);
lean::dec(x_6);
return x_13;
}
}
obj* _init_l_lean_parser_module_header_parser_lean_parser_has__tokens() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_7; obj* x_10; 
x_0 = l_lean_parser_module_prelude_parser_lean_parser_has__tokens;
x_1 = l_lean_parser_tokens___rarg(x_0);
x_2 = l_lean_parser_module_import_parser_lean_parser_has__tokens;
x_3 = l_lean_parser_tokens___rarg(x_2);
x_4 = lean::box(0);
x_5 = l_lean_parser_list_cons_tokens___rarg(x_3, x_4);
lean::dec(x_3);
x_7 = l_lean_parser_list_cons_tokens___rarg(x_1, x_5);
lean::dec(x_5);
lean::dec(x_1);
x_10 = l_lean_parser_tokens___rarg(x_7);
lean::dec(x_7);
return x_10;
}
}
obj* _init_l_lean_parser_module_header_parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_prelude_parser), 3, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_optional___at_lean_parser_module_header_parser_lean_parser_has__view___spec__1), 4, 1);
lean::closure_set(x_1, 0, x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_import_parser), 3, 0);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_many___at_lean_parser_module_import__path_parser_lean_parser_has__view___spec__1), 4, 1);
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
obj* l_lean_parser_module_header_parser(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = l_lean_parser_module_header;
x_4 = l_lean_parser_module_header_parser___closed__1;
x_5 = l_lean_parser_combinators_node___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__15(x_3, x_4, x_0, x_1, x_2);
return x_5;
}
}
obj* l_lean_parser_monad__parsec_error___at___private_init_lean_parser_module_1__commands__aux___main___spec__1___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; uint8 x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_6 = l_option_get__or__else___main___rarg(x_0, x_4);
x_7 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_1);
lean::cnstr_set(x_7, 2, x_2);
lean::cnstr_set(x_7, 3, x_3);
x_8 = 0;
x_9 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set_scalar(x_9, sizeof(void*)*1, x_8);
x_10 = x_9;
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_5);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__1___boxed), 2, 1);
lean::closure_set(x_12, 0, x_11);
return x_12;
}
}
obj* l_lean_parser_monad__parsec_error___at___private_init_lean_parser_module_1__commands__aux___main___spec__1___rarg___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_8; obj* x_11; obj* x_12; 
x_4 = l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___closed__1;
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
lean::dec(x_4);
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
lean::dec(x_5);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_1);
lean::cnstr_set(x_11, 1, x_0);
x_12 = lean::apply_4(x_8, lean::box(0), x_11, x_2, x_3);
return x_12;
}
}
obj* l_lean_parser_monad__parsec_error___at___private_init_lean_parser_module_1__commands__aux___main___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_8; obj* x_9; obj* x_12; obj* x_13; 
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___at___private_init_lean_parser_module_1__commands__aux___main___spec__1___rarg___lambda__1___boxed), 6, 4);
lean::closure_set(x_7, 0, x_2);
lean::closure_set(x_7, 1, x_0);
lean::closure_set(x_7, 2, x_1);
lean::closure_set(x_7, 3, x_3);
x_8 = l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___closed__1;
x_9 = lean::cnstr_get(x_8, 1);
lean::inc(x_9);
lean::dec(x_8);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___at___private_init_lean_parser_module_1__commands__aux___main___spec__1___rarg___lambda__2), 4, 1);
lean::closure_set(x_12, 0, x_4);
x_13 = lean::apply_6(x_9, lean::box(0), lean::box(0), x_7, x_12, x_5, x_6);
return x_13;
}
}
obj* l_lean_parser_monad__parsec_error___at___private_init_lean_parser_module_1__commands__aux___main___spec__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___at___private_init_lean_parser_module_1__commands__aux___main___spec__1___rarg), 7, 0);
return x_1;
}
}
obj* l_lean_parser_monad__parsec_any___at___private_init_lean_parser_module_1__commands__aux___main___spec__2___lambda__1(obj* x_0, uint32 x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_4 = lean::string_iterator_next(x_0);
x_5 = lean::box(0);
x_6 = lean::box_uint32(x_1);
x_7 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_4);
lean::cnstr_set(x_7, 2, x_5);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_3);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__1___boxed), 2, 1);
lean::closure_set(x_9, 0, x_8);
return x_9;
}
}
obj* l_lean_parser_monad__parsec_any___at___private_init_lean_parser_module_1__commands__aux___main___spec__2___lambda__2(obj* x_0, uint32 x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_8; obj* x_11; obj* x_12; obj* x_13; 
x_4 = l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___closed__1;
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
lean::dec(x_4);
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
lean::dec(x_5);
x_11 = lean::box_uint32(x_1);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_0);
x_13 = lean::apply_4(x_8, lean::box(0), x_12, x_2, x_3);
return x_13;
}
}
obj* l_lean_parser_monad__parsec_any___at___private_init_lean_parser_module_1__commands__aux___main___spec__2___lambda__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_6; uint8 x_9; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_1, 1);
lean::inc(x_6);
lean::dec(x_1);
x_9 = lean::string_iterator_has_next(x_4);
if (x_9 == 0)
{
obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
lean::dec(x_4);
lean::dec(x_0);
x_12 = lean::box(0);
x_13 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_14 = l_mjoin___rarg___closed__1;
x_15 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_module_1__commands__aux___main___spec__1___rarg(x_13, x_14, x_12, x_12, x_6, x_2, x_3);
return x_15;
}
else
{
uint32 x_16; uint8 x_17; 
x_16 = lean::string_iterator_curr(x_4);
x_17 = l_true_decidable;
if (x_17 == 0)
{
obj* x_20; obj* x_21; obj* x_22; obj* x_24; obj* x_25; obj* x_26; obj* x_27; 
lean::dec(x_4);
lean::dec(x_0);
x_20 = l_char_quote__core(x_16);
x_21 = l_char_has__repr___closed__1;
x_22 = lean::string_append(x_21, x_20);
lean::dec(x_20);
x_24 = lean::string_append(x_22, x_21);
x_25 = lean::box(0);
x_26 = l_mjoin___rarg___closed__1;
x_27 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_module_1__commands__aux___main___spec__1___rarg(x_24, x_26, x_25, x_25, x_6, x_2, x_3);
return x_27;
}
else
{
obj* x_28; obj* x_29; obj* x_30; obj* x_31; 
x_28 = lean::box_uint32(x_16);
x_29 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_any___at___private_init_lean_parser_module_1__commands__aux___main___spec__2___lambda__1___boxed), 4, 2);
lean::closure_set(x_29, 0, x_4);
lean::closure_set(x_29, 1, x_28);
x_30 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_any___at___private_init_lean_parser_module_1__commands__aux___main___spec__2___lambda__2___boxed), 4, 1);
lean::closure_set(x_30, 0, x_6);
x_31 = lean::apply_6(x_0, lean::box(0), lean::box(0), x_29, x_30, x_2, x_3);
return x_31;
}
}
}
}
obj* _init_l_lean_parser_monad__parsec_any___at___private_init_lean_parser_module_1__commands__aux___main___spec__2___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; 
x_0 = l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___closed__1;
x_1 = lean::cnstr_get(x_0, 1);
lean::inc(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_any___at___private_init_lean_parser_module_1__commands__aux___main___spec__2___lambda__3), 4, 1);
lean::closure_set(x_4, 0, x_1);
return x_4;
}
}
obj* l_lean_parser_monad__parsec_any___at___private_init_lean_parser_module_1__commands__aux___main___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_7; obj* x_8; obj* x_10; obj* x_11; obj* x_12; 
x_3 = l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___closed__1;
x_4 = lean::cnstr_get(x_3, 1);
lean::inc(x_4);
lean::dec(x_3);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___at___private_init_lean_parser_module_1__commands__aux___main___spec__1___rarg___lambda__2), 4, 1);
lean::closure_set(x_7, 0, x_0);
x_8 = l_lean_parser_monad__parsec_pos___at_lean_parser_module_yield__command___spec__2___closed__2;
lean::inc(x_4);
x_10 = lean::apply_4(x_4, lean::box(0), lean::box(0), x_8, x_7);
x_11 = l_lean_parser_monad__parsec_any___at___private_init_lean_parser_module_1__commands__aux___main___spec__2___closed__1;
x_12 = lean::apply_6(x_4, lean::box(0), lean::box(0), x_10, x_11, x_1, x_2);
return x_12;
}
}
obj* l_lean_parser_log__message___at___private_init_lean_parser_module_1__commands__aux___main___spec__3___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_13; obj* x_16; obj* x_19; obj* x_22; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
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
x_9 = l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___closed__1;
x_10 = lean::cnstr_get(x_9, 0);
lean::inc(x_10);
lean::dec(x_9);
x_13 = lean::cnstr_get(x_10, 1);
lean::inc(x_13);
lean::dec(x_10);
x_16 = lean::cnstr_get(x_4, 0);
lean::inc(x_16);
lean::dec(x_4);
x_19 = lean::cnstr_get(x_16, 0);
lean::inc(x_19);
lean::dec(x_16);
x_22 = lean::cnstr_get(x_19, 0);
lean::inc(x_22);
lean::dec(x_19);
x_25 = l_lean_parser_message__of__parsec__message___rarg(x_22, x_0);
x_26 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_6);
x_27 = lean::box(0);
if (lean::is_scalar(x_8)) {
 x_28 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_28 = x_8;
}
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_26);
x_29 = lean::apply_4(x_13, lean::box(0), x_28, x_2, x_3);
return x_29;
}
}
obj* l_lean_parser_log__message___at___private_init_lean_parser_module_1__commands__aux___main___spec__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_8; obj* x_9; obj* x_11; obj* x_12; obj* x_13; 
x_4 = l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___closed__1;
x_5 = lean::cnstr_get(x_4, 1);
lean::inc(x_5);
lean::dec(x_4);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___at___private_init_lean_parser_module_1__commands__aux___main___spec__1___rarg___lambda__2), 4, 1);
lean::closure_set(x_8, 0, x_1);
x_9 = l_lean_parser_module_yield__command___closed__1;
lean::inc(x_5);
x_11 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_9, x_8);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_log__message___at___private_init_lean_parser_module_1__commands__aux___main___spec__3___lambda__1), 4, 1);
lean::closure_set(x_12, 0, x_0);
x_13 = lean::apply_6(x_5, lean::box(0), lean::box(0), x_11, x_12, x_2, x_3);
return x_13;
}
}
obj* l_lean_parser_log__message___at___private_init_lean_parser_module_1__commands__aux___main___spec__4(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_8; obj* x_9; obj* x_11; obj* x_12; obj* x_13; 
x_4 = l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___closed__1;
x_5 = lean::cnstr_get(x_4, 1);
lean::inc(x_5);
lean::dec(x_4);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___at___private_init_lean_parser_module_1__commands__aux___main___spec__1___rarg___lambda__2), 4, 1);
lean::closure_set(x_8, 0, x_1);
x_9 = l_lean_parser_module_yield__command___closed__1;
lean::inc(x_5);
x_11 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_9, x_8);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_log__message___at___private_init_lean_parser_module_1__commands__aux___main___spec__3___lambda__1), 4, 1);
lean::closure_set(x_12, 0, x_0);
x_13 = lean::apply_6(x_5, lean::box(0), lean::box(0), x_11, x_12, x_2, x_3);
return x_13;
}
}
obj* l___private_init_lean_parser_module_1__commands__aux___main___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_10; obj* x_11; obj* x_14; obj* x_17; obj* x_18; 
x_3 = lean::cnstr_get(x_0, 0);
x_5 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 x_7 = x_0;
} else {
 lean::inc(x_3);
 lean::inc(x_5);
 lean::dec(x_0);
 x_7 = lean::box(0);
}
x_8 = lean::string_iterator_remaining(x_3);
lean::dec(x_3);
x_10 = l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___closed__1;
x_11 = lean::cnstr_get(x_10, 0);
lean::inc(x_11);
lean::dec(x_10);
x_14 = lean::cnstr_get(x_11, 1);
lean::inc(x_14);
lean::dec(x_11);
if (lean::is_scalar(x_7)) {
 x_17 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_17 = x_7;
}
lean::cnstr_set(x_17, 0, x_8);
lean::cnstr_set(x_17, 1, x_5);
x_18 = lean::apply_4(x_14, lean::box(0), x_17, x_1, x_2);
return x_18;
}
}
obj* _init_l___private_init_lean_parser_module_1__commands__aux___main___lambda__2___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_module_1__commands__aux___main___lambda__1), 3, 0);
return x_0;
}
}
obj* l___private_init_lean_parser_module_1__commands__aux___main___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_7; obj* x_8; obj* x_9; 
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___at___private_init_lean_parser_module_1__commands__aux___main___spec__1___rarg___lambda__2), 4, 1);
lean::closure_set(x_5, 0, x_0);
lean::inc(x_1);
x_7 = lean::apply_4(x_1, lean::box(0), lean::box(0), x_2, x_5);
x_8 = l___private_init_lean_parser_module_1__commands__aux___main___lambda__2___closed__1;
x_9 = lean::apply_6(x_1, lean::box(0), lean::box(0), x_7, x_8, x_3, x_4);
return x_9;
}
}
obj* _init_l___private_init_lean_parser_module_1__commands__aux___main___lambda__3___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command_parser___boxed), 1, 0);
return x_0;
}
}
obj* l___private_init_lean_parser_module_1__commands__aux___main___lambda__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_8; obj* x_9; obj* x_10; 
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
lean::dec(x_4);
x_8 = l___private_init_lean_parser_module_1__commands__aux___main___lambda__3___closed__1;
x_9 = l_lean_parser_command__parser_run(x_0, x_8, x_5, x_2, x_3);
x_10 = lean::cnstr_get(x_9, 0);
lean::inc(x_10);
if (lean::obj_tag(x_10) == 0)
{
obj* x_12; obj* x_14; obj* x_15; obj* x_17; obj* x_19; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; 
x_12 = lean::cnstr_get(x_9, 1);
if (lean::is_exclusive(x_9)) {
 lean::cnstr_release(x_9, 0);
 x_14 = x_9;
} else {
 lean::inc(x_12);
 lean::dec(x_9);
 x_14 = lean::box(0);
}
x_15 = lean::cnstr_get(x_10, 0);
x_17 = lean::cnstr_get(x_10, 1);
x_19 = lean::cnstr_get(x_10, 2);
if (lean::is_exclusive(x_10)) {
 x_21 = x_10;
} else {
 lean::inc(x_15);
 lean::inc(x_17);
 lean::inc(x_19);
 lean::dec(x_10);
 x_21 = lean::box(0);
}
if (lean::is_scalar(x_14)) {
 x_22 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_22 = x_14;
}
lean::cnstr_set(x_22, 0, x_15);
lean::cnstr_set(x_22, 1, x_1);
x_23 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_21)) {
 x_24 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_24 = x_21;
}
lean::cnstr_set(x_24, 0, x_22);
lean::cnstr_set(x_24, 1, x_17);
lean::cnstr_set(x_24, 2, x_23);
x_25 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_19, x_24);
x_26 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_12);
x_27 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_27, 0, x_26);
return x_27;
}
else
{
obj* x_29; obj* x_31; obj* x_32; uint8 x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; 
lean::dec(x_1);
x_29 = lean::cnstr_get(x_9, 1);
if (lean::is_exclusive(x_9)) {
 lean::cnstr_release(x_9, 0);
 x_31 = x_9;
} else {
 lean::inc(x_29);
 lean::dec(x_9);
 x_31 = lean::box(0);
}
x_32 = lean::cnstr_get(x_10, 0);
x_34 = lean::cnstr_get_scalar<uint8>(x_10, sizeof(void*)*1);
if (lean::is_exclusive(x_10)) {
 x_35 = x_10;
} else {
 lean::inc(x_32);
 lean::dec(x_10);
 x_35 = lean::box(0);
}
if (lean::is_scalar(x_35)) {
 x_36 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_36 = x_35;
}
lean::cnstr_set(x_36, 0, x_32);
lean::cnstr_set_scalar(x_36, sizeof(void*)*1, x_34);
x_37 = x_36;
if (lean::is_scalar(x_31)) {
 x_38 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_38 = x_31;
}
lean::cnstr_set(x_38, 0, x_37);
lean::cnstr_set(x_38, 1, x_29);
x_39 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_39, 0, x_38);
return x_39;
}
}
}
obj* l___private_init_lean_parser_module_1__commands__aux___main___lambda__4(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; uint8 x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_16; obj* x_19; obj* x_20; 
x_3 = lean::cnstr_get(x_0, 0);
x_5 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 x_7 = x_0;
} else {
 lean::inc(x_3);
 lean::inc(x_5);
 lean::dec(x_0);
 x_7 = lean::box(0);
}
x_8 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_8, 0, x_3);
x_9 = 0;
x_10 = lean::box(x_9);
if (lean::is_scalar(x_7)) {
 x_11 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_11 = x_7;
}
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_8);
x_12 = l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___closed__1;
x_13 = lean::cnstr_get(x_12, 0);
lean::inc(x_13);
lean::dec(x_12);
x_16 = lean::cnstr_get(x_13, 1);
lean::inc(x_16);
lean::dec(x_13);
x_19 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_19, 0, x_11);
lean::cnstr_set(x_19, 1, x_5);
x_20 = lean::apply_4(x_16, lean::box(0), x_19, x_1, x_2);
return x_20;
}
}
obj* _init_l___private_init_lean_parser_module_1__commands__aux___main___lambda__5___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_module_1__commands__aux___main___lambda__4), 3, 0);
return x_0;
}
}
obj* l___private_init_lean_parser_module_1__commands__aux___main___lambda__5(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_6; obj* x_9; obj* x_12; obj* x_13; obj* x_14; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_1, 1);
lean::inc(x_6);
lean::dec(x_1);
x_9 = lean::cnstr_get(x_4, 1);
lean::inc(x_9);
lean::dec(x_4);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_module_1__commands__aux___main___lambda__3), 5, 2);
lean::closure_set(x_12, 0, x_9);
lean::closure_set(x_12, 1, x_6);
x_13 = l___private_init_lean_parser_module_1__commands__aux___main___lambda__5___closed__1;
x_14 = lean::apply_6(x_0, lean::box(0), lean::box(0), x_12, x_13, x_2, x_3);
return x_14;
}
}
obj* l___private_init_lean_parser_module_1__commands__aux___main___lambda__6(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_6; obj* x_7; obj* x_10; obj* x_13; obj* x_14; obj* x_15; 
x_3 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 x_5 = x_0;
} else {
 lean::inc(x_3);
 lean::dec(x_0);
 x_5 = lean::box(0);
}
x_6 = l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___closed__1;
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
lean::dec(x_6);
x_10 = lean::cnstr_get(x_7, 1);
lean::inc(x_10);
lean::dec(x_7);
x_13 = lean::box(0);
if (lean::is_scalar(x_5)) {
 x_14 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_14 = x_5;
}
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_3);
x_15 = lean::apply_4(x_10, lean::box(0), x_14, x_1, x_2);
return x_15;
}
}
obj* l___private_init_lean_parser_module_1__commands__aux___main___lambda__7(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_7; obj* x_10; obj* x_11; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
lean::dec(x_3);
x_7 = lean::cnstr_get(x_4, 0);
lean::inc(x_7);
lean::dec(x_4);
x_10 = l_lean_parser_token(x_7, x_1, x_2);
x_11 = lean::cnstr_get(x_10, 0);
lean::inc(x_11);
if (lean::obj_tag(x_11) == 0)
{
obj* x_13; obj* x_15; obj* x_16; obj* x_18; obj* x_20; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
x_13 = lean::cnstr_get(x_10, 1);
if (lean::is_exclusive(x_10)) {
 lean::cnstr_release(x_10, 0);
 x_15 = x_10;
} else {
 lean::inc(x_13);
 lean::dec(x_10);
 x_15 = lean::box(0);
}
x_16 = lean::cnstr_get(x_11, 0);
x_18 = lean::cnstr_get(x_11, 1);
x_20 = lean::cnstr_get(x_11, 2);
if (lean::is_exclusive(x_11)) {
 x_22 = x_11;
} else {
 lean::inc(x_16);
 lean::inc(x_18);
 lean::inc(x_20);
 lean::dec(x_11);
 x_22 = lean::box(0);
}
if (lean::is_scalar(x_15)) {
 x_23 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_23 = x_15;
}
lean::cnstr_set(x_23, 0, x_16);
lean::cnstr_set(x_23, 1, x_0);
x_24 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_22)) {
 x_25 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_25 = x_22;
}
lean::cnstr_set(x_25, 0, x_23);
lean::cnstr_set(x_25, 1, x_18);
lean::cnstr_set(x_25, 2, x_24);
x_26 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_20, x_25);
x_27 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_13);
x_28 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_28, 0, x_27);
return x_28;
}
else
{
obj* x_30; obj* x_32; obj* x_33; uint8 x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; 
lean::dec(x_0);
x_30 = lean::cnstr_get(x_10, 1);
if (lean::is_exclusive(x_10)) {
 lean::cnstr_release(x_10, 0);
 x_32 = x_10;
} else {
 lean::inc(x_30);
 lean::dec(x_10);
 x_32 = lean::box(0);
}
x_33 = lean::cnstr_get(x_11, 0);
x_35 = lean::cnstr_get_scalar<uint8>(x_11, sizeof(void*)*1);
if (lean::is_exclusive(x_11)) {
 x_36 = x_11;
} else {
 lean::inc(x_33);
 lean::dec(x_11);
 x_36 = lean::box(0);
}
if (lean::is_scalar(x_36)) {
 x_37 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_37 = x_36;
}
lean::cnstr_set(x_37, 0, x_33);
lean::cnstr_set_scalar(x_37, sizeof(void*)*1, x_35);
x_38 = x_37;
if (lean::is_scalar(x_32)) {
 x_39 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_39 = x_32;
}
lean::cnstr_set(x_39, 0, x_38);
lean::cnstr_set(x_39, 1, x_30);
x_40 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_40, 0, x_39);
return x_40;
}
}
}
obj* l___private_init_lean_parser_module_1__commands__aux___main___lambda__8(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_6; obj* x_7; obj* x_10; obj* x_13; obj* x_14; obj* x_15; 
x_3 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 x_5 = x_0;
} else {
 lean::inc(x_3);
 lean::dec(x_0);
 x_5 = lean::box(0);
}
x_6 = l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___closed__1;
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
lean::dec(x_6);
x_10 = lean::cnstr_get(x_7, 1);
lean::inc(x_10);
lean::dec(x_7);
x_13 = lean::box(0);
if (lean::is_scalar(x_5)) {
 x_14 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_14 = x_5;
}
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_3);
x_15 = lean::apply_4(x_10, lean::box(0), x_14, x_1, x_2);
return x_15;
}
}
obj* l___private_init_lean_parser_module_1__commands__aux___main___lambda__9(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
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
x_6 = l_lean_parser_parsec__t_try__mk__res___rarg(x_1);
if (lean::is_scalar(x_5)) {
 x_7 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_7 = x_5;
}
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_3);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__1___boxed), 2, 1);
lean::closure_set(x_8, 0, x_7);
return x_8;
}
}
obj* l___private_init_lean_parser_module_1__commands__aux___main___lambda__10(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
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
x_7 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_0, x_2);
if (lean::is_scalar(x_6)) {
 x_8 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_8 = x_6;
}
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_4);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__1___boxed), 2, 1);
lean::closure_set(x_9, 0, x_8);
return x_9;
}
}
obj* l___private_init_lean_parser_module_1__commands__aux___main___lambda__11(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
if (lean::obj_tag(x_5) == 0)
{
obj* x_11; obj* x_13; obj* x_14; obj* x_15; 
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
x_11 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_13 = x_4;
} else {
 lean::inc(x_11);
 lean::dec(x_4);
 x_13 = lean::box(0);
}
if (lean::is_scalar(x_13)) {
 x_14 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_14 = x_13;
}
lean::cnstr_set(x_14, 0, x_5);
lean::cnstr_set(x_14, 1, x_11);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__1___boxed), 2, 1);
lean::closure_set(x_15, 0, x_14);
return x_15;
}
else
{
uint8 x_16; 
x_16 = lean::cnstr_get_scalar<uint8>(x_5, sizeof(void*)*1);
if (x_16 == 0)
{
obj* x_17; obj* x_20; obj* x_23; obj* x_24; obj* x_25; 
x_17 = lean::cnstr_get(x_4, 1);
lean::inc(x_17);
lean::dec(x_4);
x_20 = lean::cnstr_get(x_5, 0);
lean::inc(x_20);
lean::dec(x_5);
x_23 = lean::apply_6(x_0, lean::box(0), lean::box(0), x_1, x_2, x_3, x_17);
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_module_1__commands__aux___main___lambda__10), 2, 1);
lean::closure_set(x_24, 0, x_20);
x_25 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_25, 0, x_23);
lean::closure_set(x_25, 1, x_24);
return x_25;
}
else
{
obj* x_30; obj* x_32; obj* x_33; obj* x_34; 
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
x_30 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_32 = x_4;
} else {
 lean::inc(x_30);
 lean::dec(x_4);
 x_32 = lean::box(0);
}
if (lean::is_scalar(x_32)) {
 x_33 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_33 = x_32;
}
lean::cnstr_set(x_33, 0, x_5);
lean::cnstr_set(x_33, 1, x_30);
x_34 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__1___boxed), 2, 1);
lean::closure_set(x_34, 0, x_33);
return x_34;
}
}
}
}
obj* _init_l___private_init_lean_parser_module_1__commands__aux___main___lambda__12___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_module_1__commands__aux___main___lambda__8), 3, 0);
return x_0;
}
}
obj* _init_l___private_init_lean_parser_module_1__commands__aux___main___lambda__12___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_module_1__commands__aux___main___lambda__9), 1, 0);
return x_0;
}
}
obj* l___private_init_lean_parser_module_1__commands__aux___main___lambda__12(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_module_1__commands__aux___main___lambda__7), 4, 1);
lean::closure_set(x_6, 0, x_0);
x_7 = l___private_init_lean_parser_module_1__commands__aux___main___lambda__12___closed__1;
lean::inc(x_4);
lean::inc(x_1);
x_10 = lean::apply_6(x_1, lean::box(0), lean::box(0), x_6, x_7, x_4, x_5);
x_11 = l___private_init_lean_parser_module_1__commands__aux___main___lambda__12___closed__2;
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_12, 0, x_10);
lean::closure_set(x_12, 1, x_11);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_module_1__commands__aux___main___lambda__11), 5, 4);
lean::closure_set(x_13, 0, x_1);
lean::closure_set(x_13, 1, x_2);
lean::closure_set(x_13, 2, x_3);
lean::closure_set(x_13, 3, x_4);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_14, 0, x_12);
lean::closure_set(x_14, 1, x_13);
return x_14;
}
}
obj* _init_l___private_init_lean_parser_module_1__commands__aux___main___lambda__13___closed__1() {
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
obj* l___private_init_lean_parser_module_1__commands__aux___main___lambda__13(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_6; obj* x_7; obj* x_10; obj* x_13; obj* x_14; obj* x_15; 
x_3 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_release(x_0, 0);
 x_5 = x_0;
} else {
 lean::inc(x_3);
 lean::dec(x_0);
 x_5 = lean::box(0);
}
x_6 = l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___closed__1;
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
lean::dec(x_6);
x_10 = lean::cnstr_get(x_7, 1);
lean::inc(x_10);
lean::dec(x_7);
x_13 = l___private_init_lean_parser_module_1__commands__aux___main___lambda__13___closed__1;
if (lean::is_scalar(x_5)) {
 x_14 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_14 = x_5;
}
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_3);
x_15 = lean::apply_4(x_10, lean::box(0), x_14, x_1, x_2);
return x_15;
}
}
obj* _init_l___private_init_lean_parser_module_1__commands__aux___main___lambda__14___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_module_1__commands__aux___main___lambda__6), 3, 0);
return x_0;
}
}
obj* _init_l___private_init_lean_parser_module_1__commands__aux___main___lambda__14___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_module_1__commands__aux___main___lambda__13), 3, 0);
return x_0;
}
}
obj* l___private_init_lean_parser_module_1__commands__aux___main___lambda__14(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_8; obj* x_9; obj* x_11; obj* x_12; obj* x_13; 
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::dec(x_1);
lean::inc(x_4);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_any___at___private_init_lean_parser_module_1__commands__aux___main___spec__2), 3, 1);
lean::closure_set(x_8, 0, x_4);
x_9 = l___private_init_lean_parser_module_1__commands__aux___main___lambda__14___closed__1;
lean::inc(x_0);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_module_1__commands__aux___main___lambda__12), 6, 4);
lean::closure_set(x_11, 0, x_4);
lean::closure_set(x_11, 1, x_0);
lean::closure_set(x_11, 2, x_8);
lean::closure_set(x_11, 3, x_9);
x_12 = l___private_init_lean_parser_module_1__commands__aux___main___lambda__14___closed__2;
x_13 = lean::apply_6(x_0, lean::box(0), lean::box(0), x_11, x_12, x_2, x_3);
return x_13;
}
}
obj* l___private_init_lean_parser_module_1__commands__aux___main___lambda__15(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_9; uint8 x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_17; obj* x_20; obj* x_21; 
x_4 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 x_6 = x_1;
} else {
 lean::inc(x_4);
 lean::dec(x_1);
 x_6 = lean::box(0);
}
x_7 = lean::cnstr_get(x_0, 3);
x_8 = l_option_get___main___at_lean_parser_run___spec__2(x_7);
x_9 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_9, 0, x_8);
x_10 = 1;
x_11 = lean::box(x_10);
if (lean::is_scalar(x_6)) {
 x_12 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_12 = x_6;
}
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_9);
x_13 = l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___closed__1;
x_14 = lean::cnstr_get(x_13, 0);
lean::inc(x_14);
lean::dec(x_13);
x_17 = lean::cnstr_get(x_14, 1);
lean::inc(x_17);
lean::dec(x_14);
x_20 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_20, 0, x_12);
lean::cnstr_set(x_20, 1, x_4);
x_21 = lean::apply_4(x_17, lean::box(0), x_20, x_2, x_3);
return x_21;
}
}
obj* l___private_init_lean_parser_module_1__commands__aux___main___lambda__16(uint8 x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
if (lean::obj_tag(x_2) == 0)
{
obj* x_4; obj* x_6; obj* x_7; obj* x_8; 
x_4 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 x_6 = x_1;
} else {
 lean::inc(x_4);
 lean::dec(x_1);
 x_6 = lean::box(0);
}
if (lean::is_scalar(x_6)) {
 x_7 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_7 = x_6;
}
lean::cnstr_set(x_7, 0, x_2);
lean::cnstr_set(x_7, 1, x_4);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__1___boxed), 2, 1);
lean::closure_set(x_8, 0, x_7);
return x_8;
}
else
{
uint8 x_9; 
x_9 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*1);
if (x_0 == 0)
{
obj* x_10; obj* x_12; obj* x_13; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_10 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 x_12 = x_1;
} else {
 lean::inc(x_10);
 lean::dec(x_1);
 x_12 = lean::box(0);
}
x_13 = lean::cnstr_get(x_2, 0);
if (lean::is_exclusive(x_2)) {
 x_15 = x_2;
} else {
 lean::inc(x_13);
 lean::dec(x_2);
 x_15 = lean::box(0);
}
if (lean::is_scalar(x_15)) {
 x_16 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_16 = x_15;
}
lean::cnstr_set(x_16, 0, x_13);
lean::cnstr_set_scalar(x_16, sizeof(void*)*1, x_9);
x_17 = x_16;
if (lean::is_scalar(x_12)) {
 x_18 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_18 = x_12;
}
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_10);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__1___boxed), 2, 1);
lean::closure_set(x_19, 0, x_18);
return x_19;
}
else
{
obj* x_20; obj* x_22; obj* x_23; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
x_20 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 x_22 = x_1;
} else {
 lean::inc(x_20);
 lean::dec(x_1);
 x_22 = lean::box(0);
}
x_23 = lean::cnstr_get(x_2, 0);
if (lean::is_exclusive(x_2)) {
 x_25 = x_2;
} else {
 lean::inc(x_23);
 lean::dec(x_2);
 x_25 = lean::box(0);
}
if (lean::is_scalar(x_25)) {
 x_26 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_26 = x_25;
}
lean::cnstr_set(x_26, 0, x_23);
lean::cnstr_set_scalar(x_26, sizeof(void*)*1, x_0);
x_27 = x_26;
if (lean::is_scalar(x_22)) {
 x_28 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_28 = x_22;
}
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_20);
x_29 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__1___boxed), 2, 1);
lean::closure_set(x_29, 0, x_28);
return x_29;
}
}
}
}
obj* l___private_init_lean_parser_module_1__commands__aux___main___lambda__17(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
if (lean::obj_tag(x_3) == 0)
{
obj* x_7; obj* x_9; obj* x_10; obj* x_11; 
lean::dec(x_1);
lean::dec(x_0);
x_7 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_release(x_2, 0);
 x_9 = x_2;
} else {
 lean::inc(x_7);
 lean::dec(x_2);
 x_9 = lean::box(0);
}
if (lean::is_scalar(x_9)) {
 x_10 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_10 = x_9;
}
lean::cnstr_set(x_10, 0, x_3);
lean::cnstr_set(x_10, 1, x_7);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__1___boxed), 2, 1);
lean::closure_set(x_11, 0, x_10);
return x_11;
}
else
{
obj* x_12; obj* x_15; uint8 x_17; obj* x_19; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; 
x_12 = lean::cnstr_get(x_2, 1);
lean::inc(x_12);
lean::dec(x_2);
x_15 = lean::cnstr_get(x_3, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get_scalar<uint8>(x_3, sizeof(void*)*1);
lean::dec(x_3);
x_19 = lean::cnstr_get(x_15, 0);
lean::inc(x_19);
lean::inc(x_15);
x_22 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_log__message___at___private_init_lean_parser_module_1__commands__aux___main___spec__3), 4, 2);
lean::closure_set(x_22, 0, x_15);
lean::closure_set(x_22, 1, x_0);
x_23 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_module_1__commands__aux___main___lambda__15___boxed), 4, 1);
lean::closure_set(x_23, 0, x_15);
x_24 = lean::apply_6(x_1, lean::box(0), lean::box(0), x_22, x_23, x_19, x_12);
x_25 = lean::box(x_17);
x_26 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_module_1__commands__aux___main___lambda__16___boxed), 2, 1);
lean::closure_set(x_26, 0, x_25);
x_27 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_27, 0, x_24);
lean::closure_set(x_27, 1, x_26);
return x_27;
}
}
}
obj* l___private_init_lean_parser_module_1__commands__aux___main___lambda__18(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
lean::dec(x_0);
x_8 = l_string_join___closed__1;
x_9 = l_lean_parser_command_parser___rarg___closed__1;
x_10 = l_lean_parser_parsec__t_monad__fail___rarg___closed__1;
x_11 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_11, 0, x_3);
lean::cnstr_set(x_11, 1, x_8);
lean::cnstr_set(x_11, 2, x_9);
lean::cnstr_set(x_11, 3, x_10);
x_12 = l_lean_parser_log__message___at___private_init_lean_parser_module_1__commands__aux___main___spec__4(x_11, x_5, x_1, x_2);
return x_12;
}
}
obj* _init_l___private_init_lean_parser_module_1__commands__aux___main___lambda__19___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_module_1__commands__aux___main___lambda__18), 3, 0);
return x_0;
}
}
obj* l___private_init_lean_parser_module_1__commands__aux___main___lambda__19(obj* x_0, obj* x_1, obj* x_2, uint8 x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_8; obj* x_11; obj* x_13; obj* x_15; obj* x_18; obj* x_21; 
lean::inc(x_0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___at___private_init_lean_parser_module_1__commands__aux___main___spec__1___rarg___lambda__2), 4, 1);
lean::closure_set(x_8, 0, x_0);
lean::inc(x_8);
lean::inc(x_1);
x_11 = lean::apply_4(x_1, lean::box(0), lean::box(0), x_2, x_8);
lean::inc(x_1);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_module_1__commands__aux___main___lambda__5), 4, 1);
lean::closure_set(x_13, 0, x_1);
lean::inc(x_1);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_module_1__commands__aux___main___lambda__14), 4, 1);
lean::closure_set(x_15, 0, x_1);
lean::inc(x_5);
lean::inc(x_1);
x_18 = lean::apply_6(x_1, lean::box(0), lean::box(0), x_11, x_13, x_5, x_6);
lean::inc(x_1);
lean::inc(x_0);
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_module_1__commands__aux___main___lambda__17), 3, 2);
lean::closure_set(x_21, 0, x_0);
lean::closure_set(x_21, 1, x_1);
if (x_3 == 0)
{
obj* x_24; obj* x_25; obj* x_28; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; 
lean::dec(x_8);
lean::dec(x_4);
x_24 = l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___closed__1;
x_25 = lean::cnstr_get(x_24, 0);
lean::inc(x_25);
lean::dec(x_24);
x_28 = lean::cnstr_get(x_25, 1);
lean::inc(x_28);
lean::dec(x_25);
x_31 = lean::box(0);
x_32 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_0);
x_33 = lean::apply_2(x_28, lean::box(0), x_32);
x_34 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_module_1__commands__aux___main___lambda__11), 5, 4);
lean::closure_set(x_34, 0, x_1);
lean::closure_set(x_34, 1, x_33);
lean::closure_set(x_34, 2, x_15);
lean::closure_set(x_34, 3, x_5);
x_35 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_35, 0, x_18);
lean::closure_set(x_35, 1, x_34);
x_36 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_36, 0, x_35);
lean::closure_set(x_36, 1, x_21);
return x_36;
}
else
{
obj* x_39; obj* x_40; obj* x_42; obj* x_43; obj* x_44; obj* x_45; 
lean::dec(x_0);
lean::inc(x_1);
x_39 = lean::apply_4(x_1, lean::box(0), lean::box(0), x_4, x_8);
x_40 = l___private_init_lean_parser_module_1__commands__aux___main___lambda__19___closed__1;
lean::inc(x_1);
x_42 = lean::apply_4(x_1, lean::box(0), lean::box(0), x_39, x_40);
x_43 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_module_1__commands__aux___main___lambda__11), 5, 4);
lean::closure_set(x_43, 0, x_1);
lean::closure_set(x_43, 1, x_42);
lean::closure_set(x_43, 2, x_15);
lean::closure_set(x_43, 3, x_5);
x_44 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_44, 0, x_18);
lean::closure_set(x_44, 1, x_43);
x_45 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_45, 0, x_44);
lean::closure_set(x_45, 1, x_21);
return x_45;
}
}
}
obj* l___private_init_lean_parser_module_1__commands__aux___main___lambda__20(uint8 x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_8; 
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
lean::dec(x_2);
x_8 = l___private_init_lean_parser_module_1__commands__aux___main(x_0, x_1, x_5, x_3, x_4);
return x_8;
}
}
obj* l___private_init_lean_parser_module_1__commands__aux___main___lambda__21(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_7; 
x_5 = lean::cnstr_get(x_2, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_5, 1);
lean::inc(x_7);
if (lean::obj_tag(x_7) == 0)
{
obj* x_10; obj* x_13; uint8 x_16; obj* x_17; 
lean::dec(x_1);
x_10 = lean::cnstr_get(x_2, 1);
lean::inc(x_10);
lean::dec(x_2);
x_13 = lean::cnstr_get(x_5, 0);
lean::inc(x_13);
lean::dec(x_5);
x_16 = lean::unbox(x_13);
x_17 = l___private_init_lean_parser_module_1__commands__aux___main(x_16, x_0, x_10, x_3, x_4);
lean::dec(x_0);
return x_17;
}
else
{
obj* x_19; obj* x_22; obj* x_25; obj* x_28; obj* x_29; obj* x_30; 
x_19 = lean::cnstr_get(x_2, 1);
lean::inc(x_19);
lean::dec(x_2);
x_22 = lean::cnstr_get(x_5, 0);
lean::inc(x_22);
lean::dec(x_5);
x_25 = lean::cnstr_get(x_7, 0);
lean::inc(x_25);
lean::dec(x_7);
x_28 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_yield__command), 4, 2);
lean::closure_set(x_28, 0, x_25);
lean::closure_set(x_28, 1, x_19);
x_29 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_module_1__commands__aux___main___lambda__20___boxed), 5, 2);
lean::closure_set(x_29, 0, x_22);
lean::closure_set(x_29, 1, x_0);
x_30 = lean::apply_6(x_1, lean::box(0), lean::box(0), x_28, x_29, x_3, x_4);
return x_30;
}
}
}
obj* l___private_init_lean_parser_module_1__commands__aux___main___lambda__22(obj* x_0, obj* x_1, obj* x_2, uint8 x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_9; obj* x_11; obj* x_12; uint8 x_13; 
x_7 = lean::cnstr_get(x_4, 0);
x_9 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_set(x_4, 0, lean::box(0));
 lean::cnstr_set(x_4, 1, lean::box(0));
 x_11 = x_4;
} else {
 lean::inc(x_7);
 lean::inc(x_9);
 lean::dec(x_4);
 x_11 = lean::box(0);
}
x_12 = lean::mk_nat_obj(0u);
x_13 = lean::nat_dec_eq(x_7, x_12);
lean::dec(x_7);
if (x_13 == 0)
{
uint8 x_16; 
lean::dec(x_11);
if (x_3 == 0)
{
uint8 x_18; 
x_18 = 1;
x_16 = x_18;
goto lbl_17;
}
else
{
uint8 x_19; 
x_19 = 0;
x_16 = x_19;
goto lbl_17;
}
lbl_17:
{
obj* x_20; obj* x_21; obj* x_23; obj* x_25; obj* x_26; 
x_20 = l_lean_parser_module_yield__command___closed__1;
x_21 = lean::box(x_16);
lean::inc(x_0);
x_23 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_module_1__commands__aux___main___lambda__19___boxed), 7, 5);
lean::closure_set(x_23, 0, x_9);
lean::closure_set(x_23, 1, x_0);
lean::closure_set(x_23, 2, x_20);
lean::closure_set(x_23, 3, x_21);
lean::closure_set(x_23, 4, x_1);
lean::inc(x_0);
x_25 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_module_1__commands__aux___main___lambda__21), 5, 2);
lean::closure_set(x_25, 0, x_2);
lean::closure_set(x_25, 1, x_0);
x_26 = lean::apply_6(x_0, lean::box(0), lean::box(0), x_23, x_25, x_5, x_6);
return x_26;
}
}
else
{
obj* x_30; obj* x_31; obj* x_34; obj* x_37; obj* x_38; obj* x_39; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_30 = l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___closed__1;
x_31 = lean::cnstr_get(x_30, 0);
lean::inc(x_31);
lean::dec(x_30);
x_34 = lean::cnstr_get(x_31, 1);
lean::inc(x_34);
lean::dec(x_31);
x_37 = lean::box(0);
if (lean::is_scalar(x_11)) {
 x_38 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_38 = x_11;
}
lean::cnstr_set(x_38, 0, x_37);
lean::cnstr_set(x_38, 1, x_9);
x_39 = lean::apply_4(x_34, lean::box(0), x_38, x_5, x_6);
return x_39;
}
}
}
obj* _init_l___private_init_lean_parser_module_1__commands__aux___main___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___closed__1;
x_1 = lean::cnstr_get(x_0, 1);
lean::inc(x_1);
lean::dec(x_0);
return x_1;
}
}
obj* l___private_init_lean_parser_module_1__commands__aux___main(uint8 x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::mk_nat_obj(0u);
x_6 = lean::nat_dec_eq(x_1, x_5);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_7 = lean::mk_nat_obj(1u);
x_8 = lean::nat_sub(x_1, x_7);
x_9 = l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___closed__1;
x_10 = lean::cnstr_get(x_9, 1);
lean::inc(x_10);
lean::dec(x_9);
x_13 = l___private_init_lean_parser_module_1__commands__aux___main___closed__1;
x_14 = l_lean_parser_monad__parsec_pos___at_lean_parser_module_yield__command___spec__2___closed__2;
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_module_1__commands__aux___main___lambda__2), 5, 3);
lean::closure_set(x_15, 0, x_2);
lean::closure_set(x_15, 1, x_13);
lean::closure_set(x_15, 2, x_14);
x_16 = lean::box(x_0);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_module_1__commands__aux___main___lambda__22___boxed), 7, 4);
lean::closure_set(x_17, 0, x_13);
lean::closure_set(x_17, 1, x_14);
lean::closure_set(x_17, 2, x_8);
lean::closure_set(x_17, 3, x_16);
x_18 = lean::apply_6(x_10, lean::box(0), lean::box(0), x_15, x_17, x_3, x_4);
return x_18;
}
else
{
obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_19 = lean::box(0);
x_20 = l___private_init_lean_parser_combinators_1__many1__aux___main___rarg___closed__1;
x_21 = l_mjoin___rarg___closed__1;
x_22 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_module_1__commands__aux___main___spec__1___rarg(x_20, x_21, x_19, x_19, x_2, x_3, x_4);
return x_22;
}
}
}
obj* l_lean_parser_monad__parsec_error___at___private_init_lean_parser_module_1__commands__aux___main___spec__1___rarg___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_module_1__commands__aux___main___spec__1___rarg___lambda__1(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_0);
lean::dec(x_4);
return x_6;
}
}
obj* l_lean_parser_monad__parsec_error___at___private_init_lean_parser_module_1__commands__aux___main___spec__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_module_1__commands__aux___main___spec__1(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_parser_monad__parsec_any___at___private_init_lean_parser_module_1__commands__aux___main___spec__2___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint32 x_4; obj* x_5; 
x_4 = lean::unbox_uint32(x_1);
x_5 = l_lean_parser_monad__parsec_any___at___private_init_lean_parser_module_1__commands__aux___main___spec__2___lambda__1(x_0, x_4, x_2, x_3);
lean::dec(x_2);
return x_5;
}
}
obj* l_lean_parser_monad__parsec_any___at___private_init_lean_parser_module_1__commands__aux___main___spec__2___lambda__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint32 x_4; obj* x_5; 
x_4 = lean::unbox_uint32(x_1);
x_5 = l_lean_parser_monad__parsec_any___at___private_init_lean_parser_module_1__commands__aux___main___spec__2___lambda__2(x_0, x_4, x_2, x_3);
return x_5;
}
}
obj* l___private_init_lean_parser_module_1__commands__aux___main___lambda__15___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_parser_module_1__commands__aux___main___lambda__15(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l___private_init_lean_parser_module_1__commands__aux___main___lambda__16___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = lean::unbox(x_0);
x_3 = l___private_init_lean_parser_module_1__commands__aux___main___lambda__16(x_2, x_1);
return x_3;
}
}
obj* l___private_init_lean_parser_module_1__commands__aux___main___lambda__19___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
uint8 x_7; obj* x_8; 
x_7 = lean::unbox(x_3);
x_8 = l___private_init_lean_parser_module_1__commands__aux___main___lambda__19(x_0, x_1, x_2, x_7, x_4, x_5, x_6);
return x_8;
}
}
obj* l___private_init_lean_parser_module_1__commands__aux___main___lambda__20___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; obj* x_6; 
x_5 = lean::unbox(x_0);
x_6 = l___private_init_lean_parser_module_1__commands__aux___main___lambda__20(x_5, x_1, x_2, x_3, x_4);
lean::dec(x_1);
return x_6;
}
}
obj* l___private_init_lean_parser_module_1__commands__aux___main___lambda__22___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
uint8 x_7; obj* x_8; 
x_7 = lean::unbox(x_3);
x_8 = l___private_init_lean_parser_module_1__commands__aux___main___lambda__22(x_0, x_1, x_2, x_7, x_4, x_5, x_6);
return x_8;
}
}
obj* l___private_init_lean_parser_module_1__commands__aux___main___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; obj* x_6; 
x_5 = lean::unbox(x_0);
x_6 = l___private_init_lean_parser_module_1__commands__aux___main(x_5, x_1, x_2, x_3, x_4);
lean::dec(x_1);
return x_6;
}
}
obj* l___private_init_lean_parser_module_1__commands__aux(uint8 x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l___private_init_lean_parser_module_1__commands__aux___main(x_0, x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* l___private_init_lean_parser_module_1__commands__aux___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; obj* x_6; 
x_5 = lean::unbox(x_0);
x_6 = l___private_init_lean_parser_module_1__commands__aux(x_5, x_1, x_2, x_3, x_4);
lean::dec(x_1);
return x_6;
}
}
obj* l_lean_parser_module_commands_parser___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_8; obj* x_9; uint8 x_11; obj* x_12; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
lean::dec(x_0);
x_8 = lean::mk_nat_obj(1u);
x_9 = lean::nat_add(x_3, x_8);
lean::dec(x_3);
x_11 = 0;
x_12 = l___private_init_lean_parser_module_1__commands__aux___main(x_11, x_9, x_5, x_1, x_2);
lean::dec(x_9);
return x_12;
}
}
obj* _init_l_lean_parser_module_commands_parser___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_commands_parser___lambda__1), 3, 0);
return x_0;
}
}
obj* l_lean_parser_module_commands_parser(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_3 = l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___closed__1;
x_4 = lean::cnstr_get(x_3, 1);
lean::inc(x_4);
lean::dec(x_3);
x_7 = l___private_init_lean_parser_module_1__commands__aux___main___closed__1;
x_8 = l_lean_parser_monad__parsec_pos___at_lean_parser_module_yield__command___spec__2___closed__2;
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_module_1__commands__aux___main___lambda__2), 5, 3);
lean::closure_set(x_9, 0, x_0);
lean::closure_set(x_9, 1, x_7);
lean::closure_set(x_9, 2, x_8);
x_10 = l_lean_parser_module_commands_parser___closed__1;
x_11 = lean::apply_6(x_4, lean::box(0), lean::box(0), x_9, x_10, x_1, x_2);
return x_11;
}
}
obj* _init_l_lean_parser_module_commands_tokens() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = l_lean_parser_command_parser_lean_parser_has__tokens;
x_1 = l_lean_parser_tokens___rarg(x_0);
return x_1;
}
}
obj* l_list_map___main___at_lean_parser_module_commands_parser_has__view___spec__1(obj* x_0) {
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
x_7 = l_list_map___main___at_lean_parser_module_commands_parser_has__view___spec__1(x_4);
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
obj* l_list_map___main___at_lean_parser_module_commands_parser_has__view___spec__2(obj* x_0) {
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
x_7 = l_list_map___main___at_lean_parser_module_commands_parser_has__view___spec__2(x_4);
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
obj* l_lean_parser_module_commands_parser_has__view___lambda__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_syntax_as__node___main(x_0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; 
x_2 = l_lean_parser_ident__univ__spec_has__view_x_27___lambda__1___closed__1;
return x_2;
}
else
{
obj* x_3; obj* x_6; obj* x_9; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
lean::dec(x_1);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
lean::dec(x_3);
x_9 = l_list_map___main___at_lean_parser_module_commands_parser_has__view___spec__1(x_6);
return x_9;
}
}
}
obj* l_lean_parser_module_commands_parser_has__view___lambda__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_list_map___main___at_lean_parser_module_commands_parser_has__view___spec__2(x_0);
x_2 = l_lean_parser_no__kind;
x_3 = l_lean_parser_syntax_mk__node(x_2, x_1);
return x_3;
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
obj* _init_l_lean_parser_module_eoi() {
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
obj* l_lean_parser_monad__parsec_eoi___at_lean_parser_module_parser___spec__1___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_9; uint8 x_10; 
x_3 = lean::cnstr_get(x_0, 0);
x_5 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 x_7 = x_0;
} else {
 lean::inc(x_3);
 lean::inc(x_5);
 lean::dec(x_0);
 x_7 = lean::box(0);
}
x_8 = lean::string_iterator_remaining(x_3);
x_9 = lean::mk_nat_obj(0u);
x_10 = lean::nat_dec_eq(x_8, x_9);
lean::dec(x_8);
if (x_10 == 0)
{
uint32 x_13; obj* x_15; obj* x_16; obj* x_17; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
lean::dec(x_7);
x_13 = lean::string_iterator_curr(x_3);
lean::dec(x_3);
x_15 = l_char_quote__core(x_13);
x_16 = l_char_has__repr___closed__1;
x_17 = lean::string_append(x_16, x_15);
lean::dec(x_15);
x_19 = lean::string_append(x_17, x_16);
x_20 = lean::box(0);
x_21 = l_lean_parser_monad__parsec_eoi___rarg___lambda__1___closed__1;
x_22 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_module_1__commands__aux___main___spec__1___rarg(x_19, x_21, x_20, x_20, x_5, x_1, x_2);
return x_22;
}
else
{
obj* x_24; obj* x_25; obj* x_28; obj* x_31; obj* x_32; obj* x_33; 
lean::dec(x_3);
x_24 = l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___closed__1;
x_25 = lean::cnstr_get(x_24, 0);
lean::inc(x_25);
lean::dec(x_24);
x_28 = lean::cnstr_get(x_25, 1);
lean::inc(x_28);
lean::dec(x_25);
x_31 = lean::box(0);
if (lean::is_scalar(x_7)) {
 x_32 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_32 = x_7;
}
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_5);
x_33 = lean::apply_4(x_28, lean::box(0), x_32, x_1, x_2);
return x_33;
}
}
}
obj* _init_l_lean_parser_monad__parsec_eoi___at_lean_parser_module_parser___spec__1___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_eoi___at_lean_parser_module_parser___spec__1___lambda__1), 3, 0);
return x_0;
}
}
obj* l_lean_parser_monad__parsec_eoi___at_lean_parser_module_parser___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_7; obj* x_8; obj* x_10; obj* x_11; obj* x_12; 
x_3 = l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___closed__1;
x_4 = lean::cnstr_get(x_3, 1);
lean::inc(x_4);
lean::dec(x_3);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___at___private_init_lean_parser_module_1__commands__aux___main___spec__1___rarg___lambda__2), 4, 1);
lean::closure_set(x_7, 0, x_0);
x_8 = l_lean_parser_monad__parsec_pos___at_lean_parser_module_yield__command___spec__2___closed__2;
lean::inc(x_4);
x_10 = lean::apply_4(x_4, lean::box(0), lean::box(0), x_8, x_7);
x_11 = l_lean_parser_monad__parsec_eoi___at_lean_parser_module_parser___spec__1___closed__1;
x_12 = lean::apply_6(x_4, lean::box(0), lean::box(0), x_10, x_11, x_1, x_2);
return x_12;
}
}
obj* l_lean_parser_module_parser___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_4 = lean::cnstr_get(x_3, 0);
x_5 = lean::cnstr_get(x_4, 0);
x_6 = l_lean_parser_whitespace(x_5, x_1, x_2);
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
if (lean::obj_tag(x_7) == 0)
{
obj* x_9; obj* x_11; obj* x_12; obj* x_14; obj* x_16; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_9 = lean::cnstr_get(x_6, 1);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 x_11 = x_6;
} else {
 lean::inc(x_9);
 lean::dec(x_6);
 x_11 = lean::box(0);
}
x_12 = lean::cnstr_get(x_7, 0);
x_14 = lean::cnstr_get(x_7, 1);
x_16 = lean::cnstr_get(x_7, 2);
if (lean::is_exclusive(x_7)) {
 x_18 = x_7;
} else {
 lean::inc(x_12);
 lean::inc(x_14);
 lean::inc(x_16);
 lean::dec(x_7);
 x_18 = lean::box(0);
}
if (lean::is_scalar(x_11)) {
 x_19 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_19 = x_11;
}
lean::cnstr_set(x_19, 0, x_12);
lean::cnstr_set(x_19, 1, x_0);
x_20 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_18)) {
 x_21 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_21 = x_18;
}
lean::cnstr_set(x_21, 0, x_19);
lean::cnstr_set(x_21, 1, x_14);
lean::cnstr_set(x_21, 2, x_20);
x_22 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_21);
x_23 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_23, 0, x_22);
lean::cnstr_set(x_23, 1, x_9);
x_24 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_24, 0, x_23);
return x_24;
}
else
{
obj* x_26; obj* x_28; obj* x_29; uint8 x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; 
lean::dec(x_0);
x_26 = lean::cnstr_get(x_6, 1);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 x_28 = x_6;
} else {
 lean::inc(x_26);
 lean::dec(x_6);
 x_28 = lean::box(0);
}
x_29 = lean::cnstr_get(x_7, 0);
x_31 = lean::cnstr_get_scalar<uint8>(x_7, sizeof(void*)*1);
if (lean::is_exclusive(x_7)) {
 x_32 = x_7;
} else {
 lean::inc(x_29);
 lean::dec(x_7);
 x_32 = lean::box(0);
}
if (lean::is_scalar(x_32)) {
 x_33 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_33 = x_32;
}
lean::cnstr_set(x_33, 0, x_29);
lean::cnstr_set_scalar(x_33, sizeof(void*)*1, x_31);
x_34 = x_33;
if (lean::is_scalar(x_28)) {
 x_35 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_35 = x_28;
}
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_26);
x_36 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_36, 0, x_35);
return x_36;
}
}
}
obj* l_lean_parser_module_parser___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_7; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
lean::dec(x_3);
x_7 = lean::cnstr_get(x_4, 0);
lean::inc(x_7);
lean::dec(x_4);
x_10 = l_lean_parser_module_header;
x_11 = l_lean_parser_module_header_parser___closed__1;
x_12 = l_lean_parser_combinators_node___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__15(x_10, x_11, x_7, x_1, x_2);
x_13 = lean::cnstr_get(x_12, 0);
lean::inc(x_13);
if (lean::obj_tag(x_13) == 0)
{
obj* x_15; obj* x_17; obj* x_18; obj* x_20; obj* x_22; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_15 = lean::cnstr_get(x_12, 1);
if (lean::is_exclusive(x_12)) {
 lean::cnstr_release(x_12, 0);
 x_17 = x_12;
} else {
 lean::inc(x_15);
 lean::dec(x_12);
 x_17 = lean::box(0);
}
x_18 = lean::cnstr_get(x_13, 0);
x_20 = lean::cnstr_get(x_13, 1);
x_22 = lean::cnstr_get(x_13, 2);
if (lean::is_exclusive(x_13)) {
 x_24 = x_13;
} else {
 lean::inc(x_18);
 lean::inc(x_20);
 lean::inc(x_22);
 lean::dec(x_13);
 x_24 = lean::box(0);
}
if (lean::is_scalar(x_17)) {
 x_25 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_25 = x_17;
}
lean::cnstr_set(x_25, 0, x_18);
lean::cnstr_set(x_25, 1, x_0);
x_26 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_24)) {
 x_27 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_27 = x_24;
}
lean::cnstr_set(x_27, 0, x_25);
lean::cnstr_set(x_27, 1, x_20);
lean::cnstr_set(x_27, 2, x_26);
x_28 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_22, x_27);
x_29 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_15);
x_30 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_30, 0, x_29);
return x_30;
}
else
{
obj* x_32; obj* x_34; obj* x_35; uint8 x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; 
lean::dec(x_0);
x_32 = lean::cnstr_get(x_12, 1);
if (lean::is_exclusive(x_12)) {
 lean::cnstr_release(x_12, 0);
 x_34 = x_12;
} else {
 lean::inc(x_32);
 lean::dec(x_12);
 x_34 = lean::box(0);
}
x_35 = lean::cnstr_get(x_13, 0);
x_37 = lean::cnstr_get_scalar<uint8>(x_13, sizeof(void*)*1);
if (lean::is_exclusive(x_13)) {
 x_38 = x_13;
} else {
 lean::inc(x_35);
 lean::dec(x_13);
 x_38 = lean::box(0);
}
if (lean::is_scalar(x_38)) {
 x_39 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_39 = x_38;
}
lean::cnstr_set(x_39, 0, x_35);
lean::cnstr_set_scalar(x_39, sizeof(void*)*1, x_37);
x_40 = x_39;
if (lean::is_scalar(x_34)) {
 x_41 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_41 = x_34;
}
lean::cnstr_set(x_41, 0, x_40);
lean::cnstr_set(x_41, 1, x_32);
x_42 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_42, 0, x_41);
return x_42;
}
}
}
obj* l_lean_parser_module_parser___lambda__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_8; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
lean::dec(x_0);
x_8 = l_lean_parser_module_yield__command(x_3, x_5, x_1, x_2);
return x_8;
}
}
obj* l_lean_parser_module_parser___lambda__4(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_6; 
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
x_6 = l_lean_parser_monad__parsec_eoi___at_lean_parser_module_parser___spec__1(x_3, x_1, x_2);
return x_6;
}
}
obj* _init_l_lean_parser_module_parser___lambda__5___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_parser___lambda__4), 3, 0);
return x_0;
}
}
obj* l_lean_parser_module_parser___lambda__5(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_7; obj* x_8; obj* x_9; 
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::dec(x_1);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_commands_parser), 3, 1);
lean::closure_set(x_7, 0, x_4);
x_8 = l_lean_parser_module_parser___lambda__5___closed__1;
x_9 = lean::apply_6(x_0, lean::box(0), lean::box(0), x_7, x_8, x_2, x_3);
return x_9;
}
}
obj* _init_l_lean_parser_module_parser___lambda__6___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_parser___lambda__3), 3, 0);
return x_0;
}
}
obj* l_lean_parser_module_parser___lambda__6(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_7; obj* x_8; obj* x_10; obj* x_12; obj* x_13; 
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::dec(x_1);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_parser___lambda__2), 4, 1);
lean::closure_set(x_7, 0, x_4);
x_8 = l_lean_parser_module_parser___lambda__6___closed__1;
lean::inc(x_0);
x_10 = lean::apply_4(x_0, lean::box(0), lean::box(0), x_7, x_8);
lean::inc(x_0);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_parser___lambda__5), 4, 1);
lean::closure_set(x_12, 0, x_0);
x_13 = lean::apply_6(x_0, lean::box(0), lean::box(0), x_10, x_12, x_2, x_3);
return x_13;
}
}
obj* l_lean_parser_module_parser___lambda__7(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_7; obj* x_8; obj* x_9; 
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::dec(x_1);
x_7 = lean::cnstr_get(x_0, 3);
x_8 = l_option_get___main___at_lean_parser_run___spec__2(x_7);
x_9 = l_lean_parser_module_yield__command(x_8, x_4, x_2, x_3);
return x_9;
}
}
obj* l_lean_parser_module_parser___lambda__8(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
if (lean::obj_tag(x_3) == 0)
{
obj* x_7; obj* x_9; obj* x_10; obj* x_11; 
lean::dec(x_1);
lean::dec(x_0);
x_7 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_release(x_2, 0);
 x_9 = x_2;
} else {
 lean::inc(x_7);
 lean::dec(x_2);
 x_9 = lean::box(0);
}
if (lean::is_scalar(x_9)) {
 x_10 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_10 = x_9;
}
lean::cnstr_set(x_10, 0, x_3);
lean::cnstr_set(x_10, 1, x_7);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___lambda__1___boxed), 2, 1);
lean::closure_set(x_11, 0, x_10);
return x_11;
}
else
{
obj* x_12; obj* x_15; uint8 x_17; obj* x_19; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; 
x_12 = lean::cnstr_get(x_2, 1);
lean::inc(x_12);
lean::dec(x_2);
x_15 = lean::cnstr_get(x_3, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get_scalar<uint8>(x_3, sizeof(void*)*1);
lean::dec(x_3);
x_19 = lean::cnstr_get(x_15, 0);
lean::inc(x_19);
lean::inc(x_15);
x_22 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_log__message___at___private_init_lean_parser_module_1__commands__aux___main___spec__3), 4, 2);
lean::closure_set(x_22, 0, x_15);
lean::closure_set(x_22, 1, x_0);
x_23 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_parser___lambda__7___boxed), 4, 1);
lean::closure_set(x_23, 0, x_15);
x_24 = lean::apply_6(x_1, lean::box(0), lean::box(0), x_22, x_23, x_19, x_12);
x_25 = lean::box(x_17);
x_26 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_module_1__commands__aux___main___lambda__16___boxed), 2, 1);
lean::closure_set(x_26, 0, x_25);
x_27 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_27, 0, x_24);
lean::closure_set(x_27, 1, x_26);
return x_27;
}
}
}
obj* l_lean_parser_module_parser___lambda__9(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_7; obj* x_8; obj* x_9; 
lean::inc(x_0);
x_7 = lean::apply_6(x_0, lean::box(0), lean::box(0), x_1, x_2, x_4, x_5);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_parser___lambda__8), 3, 2);
lean::closure_set(x_8, 0, x_3);
lean::closure_set(x_8, 1, x_0);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_coroutine_bind___main___rarg), 3, 2);
lean::closure_set(x_9, 0, x_7);
lean::closure_set(x_9, 1, x_8);
return x_9;
}
}
obj* l_lean_parser_module_parser___lambda__10(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_8; obj* x_11; obj* x_12; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
lean::dec(x_0);
x_8 = lean::string_iterator_to_end(x_3);
lean::inc(x_8);
lean::inc(x_8);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_8);
lean::cnstr_set(x_11, 1, x_8);
x_12 = lean::string_iterator_offset(x_8);
lean::dec(x_8);
lean::inc(x_11);
x_15 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_15, 0, x_11);
lean::cnstr_set(x_15, 1, x_12);
lean::cnstr_set(x_15, 2, x_11);
x_16 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_16, 0, x_15);
x_17 = l_string_join___closed__1;
x_18 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_18, 0, x_16);
lean::cnstr_set(x_18, 1, x_17);
x_19 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_19, 0, x_18);
x_20 = lean::box(0);
x_21 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_21, 0, x_19);
lean::cnstr_set(x_21, 1, x_20);
x_22 = l_lean_parser_module_eoi;
x_23 = l_lean_parser_syntax_mk__node(x_22, x_21);
x_24 = l_lean_parser_module_yield__command(x_23, x_5, x_1, x_2);
return x_24;
}
}
obj* _init_l_lean_parser_module_parser___lambda__11___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_parser___lambda__10), 3, 0);
return x_0;
}
}
obj* l_lean_parser_module_parser___lambda__11(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_7; obj* x_8; obj* x_10; obj* x_11; obj* x_12; 
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::dec(x_1);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___at___private_init_lean_parser_module_1__commands__aux___main___spec__1___rarg___lambda__2), 4, 1);
lean::closure_set(x_7, 0, x_4);
x_8 = l_lean_parser_monad__parsec_pos___at_lean_parser_module_yield__command___spec__2___closed__2;
lean::inc(x_0);
x_10 = lean::apply_4(x_0, lean::box(0), lean::box(0), x_8, x_7);
x_11 = l_lean_parser_module_parser___lambda__11___closed__1;
x_12 = lean::apply_6(x_0, lean::box(0), lean::box(0), x_10, x_11, x_2, x_3);
return x_12;
}
}
obj* _init_l_lean_parser_module_parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; 
x_0 = l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___closed__1;
x_1 = lean::cnstr_get(x_0, 1);
lean::inc(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_parser___lambda__6), 4, 1);
lean::closure_set(x_4, 0, x_1);
return x_4;
}
}
obj* _init_l_lean_parser_module_parser___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; 
x_0 = l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___closed__1;
x_1 = lean::cnstr_get(x_0, 1);
lean::inc(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_parser___lambda__11), 4, 1);
lean::closure_set(x_4, 0, x_1);
return x_4;
}
}
obj* l_lean_parser_module_parser(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_3 = l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___closed__1;
x_4 = lean::cnstr_get(x_3, 1);
lean::inc(x_4);
lean::dec(x_3);
lean::inc(x_0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_parser___lambda__1___boxed), 4, 1);
lean::closure_set(x_8, 0, x_0);
x_9 = l___private_init_lean_parser_module_1__commands__aux___main___closed__1;
x_10 = l_lean_parser_module_parser___closed__1;
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_module_parser___lambda__9), 6, 4);
lean::closure_set(x_11, 0, x_9);
lean::closure_set(x_11, 1, x_8);
lean::closure_set(x_11, 2, x_10);
lean::closure_set(x_11, 3, x_0);
x_12 = l_lean_parser_module_parser___closed__2;
x_13 = lean::apply_6(x_4, lean::box(0), lean::box(0), x_11, x_12, x_1, x_2);
return x_13;
}
}
obj* l_lean_parser_module_parser___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_parser_module_parser___lambda__1(x_0, x_1, x_2, x_3);
lean::dec(x_3);
return x_4;
}
}
obj* l_lean_parser_module_parser___lambda__7___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_parser_module_parser___lambda__7(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* _init_l_lean_parser_module_tokens() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_0 = l_lean_parser_module_prelude_parser_lean_parser_has__tokens;
x_1 = l_lean_parser_tokens___rarg(x_0);
x_2 = l_lean_parser_module_import_parser_lean_parser_has__tokens;
x_3 = l_lean_parser_tokens___rarg(x_2);
x_4 = l_list_append___rarg(x_1, x_3);
x_5 = l_lean_parser_module_commands_tokens;
x_6 = l_lean_parser_tokens___rarg(x_5);
x_7 = l_list_append___rarg(x_4, x_6);
return x_7;
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
 l_lean_parser_module__parser__m_monad = _init_l_lean_parser_module__parser__m_monad();
lean::mark_persistent(l_lean_parser_module__parser__m_monad);
 l_lean_parser_module__parser__m_alternative = _init_l_lean_parser_module__parser__m_alternative();
lean::mark_persistent(l_lean_parser_module__parser__m_alternative);
 l_lean_parser_module__parser__m_monad__reader = _init_l_lean_parser_module__parser__m_monad__reader();
lean::mark_persistent(l_lean_parser_module__parser__m_monad__reader);
 l_lean_parser_module__parser__m_monad__state = _init_l_lean_parser_module__parser__m_monad__state();
lean::mark_persistent(l_lean_parser_module__parser__m_monad__state);
 l_lean_parser_module__parser__m_lean_parser_monad__parsec = _init_l_lean_parser_module__parser__m_lean_parser_monad__parsec();
lean::mark_persistent(l_lean_parser_module__parser__m_lean_parser_monad__parsec);
 l_lean_parser_module__parser__m_monad__except = _init_l_lean_parser_module__parser__m_monad__except();
lean::mark_persistent(l_lean_parser_module__parser__m_monad__except);
 l_lean_parser_module__parser__m_monad__coroutine = _init_l_lean_parser_module__parser__m_monad__coroutine();
lean::mark_persistent(l_lean_parser_module__parser__m_monad__coroutine);
 l_lean_parser_module__parser__m = _init_l_lean_parser_module__parser__m();
lean::mark_persistent(l_lean_parser_module__parser__m);
 l_lean_parser_module__parser = _init_l_lean_parser_module__parser();
lean::mark_persistent(l_lean_parser_module__parser);
 l_lean_parser_module__parser__m_basic__parser__m___closed__1 = _init_l_lean_parser_module__parser__m_basic__parser__m___closed__1();
lean::mark_persistent(l_lean_parser_module__parser__m_basic__parser__m___closed__1);
 l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___closed__1 = _init_l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___closed__1();
lean::mark_persistent(l_lean_parser_parsec__t_monad_x_27___at_lean_parser_module_yield__command___spec__1___closed__1);
 l_lean_parser_monad__parsec_pos___at_lean_parser_module_yield__command___spec__2___closed__1 = _init_l_lean_parser_monad__parsec_pos___at_lean_parser_module_yield__command___spec__2___closed__1();
lean::mark_persistent(l_lean_parser_monad__parsec_pos___at_lean_parser_module_yield__command___spec__2___closed__1);
 l_lean_parser_monad__parsec_pos___at_lean_parser_module_yield__command___spec__2___closed__2 = _init_l_lean_parser_monad__parsec_pos___at_lean_parser_module_yield__command___spec__2___closed__2();
lean::mark_persistent(l_lean_parser_monad__parsec_pos___at_lean_parser_module_yield__command___spec__2___closed__2);
 l_lean_parser_monad__parsec_pos___at_lean_parser_module_yield__command___spec__2___closed__3 = _init_l_lean_parser_monad__parsec_pos___at_lean_parser_module_yield__command___spec__2___closed__3();
lean::mark_persistent(l_lean_parser_monad__parsec_pos___at_lean_parser_module_yield__command___spec__2___closed__3);
 l_lean_parser_module_yield__command___lambda__7___closed__1 = _init_l_lean_parser_module_yield__command___lambda__7___closed__1();
lean::mark_persistent(l_lean_parser_module_yield__command___lambda__7___closed__1);
 l_lean_parser_module_yield__command___closed__1 = _init_l_lean_parser_module_yield__command___closed__1();
lean::mark_persistent(l_lean_parser_module_yield__command___closed__1);
 l_lean_parser_module_yield__command___closed__2 = _init_l_lean_parser_module_yield__command___closed__2();
lean::mark_persistent(l_lean_parser_module_yield__command___closed__2);
 l_lean_parser_module_prelude = _init_l_lean_parser_module_prelude();
lean::mark_persistent(l_lean_parser_module_prelude);
 l_lean_parser_module_prelude_has__view_x_27 = _init_l_lean_parser_module_prelude_has__view_x_27();
lean::mark_persistent(l_lean_parser_module_prelude_has__view_x_27);
 l_lean_parser_module_prelude_has__view = _init_l_lean_parser_module_prelude_has__view();
lean::mark_persistent(l_lean_parser_module_prelude_has__view);
 l_lean_parser_module_prelude_parser_lean_parser_has__view = _init_l_lean_parser_module_prelude_parser_lean_parser_has__view();
lean::mark_persistent(l_lean_parser_module_prelude_parser_lean_parser_has__view);
 l_lean_parser_module_prelude_parser_lean_parser_has__tokens = _init_l_lean_parser_module_prelude_parser_lean_parser_has__tokens();
lean::mark_persistent(l_lean_parser_module_prelude_parser_lean_parser_has__tokens);
 l_lean_parser_module_prelude_parser___closed__1 = _init_l_lean_parser_module_prelude_parser___closed__1();
lean::mark_persistent(l_lean_parser_module_prelude_parser___closed__1);
 l_lean_parser_module_import__path = _init_l_lean_parser_module_import__path();
lean::mark_persistent(l_lean_parser_module_import__path);
 l_lean_parser_module_import__path_has__view_x_27___lambda__1___closed__1 = _init_l_lean_parser_module_import__path_has__view_x_27___lambda__1___closed__1();
lean::mark_persistent(l_lean_parser_module_import__path_has__view_x_27___lambda__1___closed__1);
 l_lean_parser_module_import__path_has__view_x_27___lambda__1___closed__2 = _init_l_lean_parser_module_import__path_has__view_x_27___lambda__1___closed__2();
lean::mark_persistent(l_lean_parser_module_import__path_has__view_x_27___lambda__1___closed__2);
 l_lean_parser_module_import__path_has__view_x_27___lambda__1___closed__3 = _init_l_lean_parser_module_import__path_has__view_x_27___lambda__1___closed__3();
lean::mark_persistent(l_lean_parser_module_import__path_has__view_x_27___lambda__1___closed__3);
 l_lean_parser_module_import__path_has__view_x_27___lambda__1___closed__4 = _init_l_lean_parser_module_import__path_has__view_x_27___lambda__1___closed__4();
lean::mark_persistent(l_lean_parser_module_import__path_has__view_x_27___lambda__1___closed__4);
 l_lean_parser_module_import__path_has__view_x_27 = _init_l_lean_parser_module_import__path_has__view_x_27();
lean::mark_persistent(l_lean_parser_module_import__path_has__view_x_27);
 l_lean_parser_module_import__path_has__view = _init_l_lean_parser_module_import__path_has__view();
lean::mark_persistent(l_lean_parser_module_import__path_has__view);
 l_lean_parser_module_import__path_parser_lean_parser_has__view = _init_l_lean_parser_module_import__path_parser_lean_parser_has__view();
lean::mark_persistent(l_lean_parser_module_import__path_parser_lean_parser_has__view);
 l_lean_parser_module_import__path_parser_lean_parser_has__tokens = _init_l_lean_parser_module_import__path_parser_lean_parser_has__tokens();
lean::mark_persistent(l_lean_parser_module_import__path_parser_lean_parser_has__tokens);
 l_lean_parser_module_import__path_parser___closed__1 = _init_l_lean_parser_module_import__path_parser___closed__1();
lean::mark_persistent(l_lean_parser_module_import__path_parser___closed__1);
 l_lean_parser_module_import = _init_l_lean_parser_module_import();
lean::mark_persistent(l_lean_parser_module_import);
 l_lean_parser_module_import_has__view_x_27___lambda__1___closed__1 = _init_l_lean_parser_module_import_has__view_x_27___lambda__1___closed__1();
lean::mark_persistent(l_lean_parser_module_import_has__view_x_27___lambda__1___closed__1);
 l_lean_parser_module_import_has__view_x_27___lambda__1___closed__2 = _init_l_lean_parser_module_import_has__view_x_27___lambda__1___closed__2();
lean::mark_persistent(l_lean_parser_module_import_has__view_x_27___lambda__1___closed__2);
 l_lean_parser_module_import_has__view_x_27___lambda__1___closed__3 = _init_l_lean_parser_module_import_has__view_x_27___lambda__1___closed__3();
lean::mark_persistent(l_lean_parser_module_import_has__view_x_27___lambda__1___closed__3);
 l_lean_parser_module_import_has__view_x_27___lambda__2___closed__1 = _init_l_lean_parser_module_import_has__view_x_27___lambda__2___closed__1();
lean::mark_persistent(l_lean_parser_module_import_has__view_x_27___lambda__2___closed__1);
 l_lean_parser_module_import_has__view_x_27 = _init_l_lean_parser_module_import_has__view_x_27();
lean::mark_persistent(l_lean_parser_module_import_has__view_x_27);
 l_lean_parser_module_import_has__view = _init_l_lean_parser_module_import_has__view();
lean::mark_persistent(l_lean_parser_module_import_has__view);
 l_lean_parser_module_import_parser_lean_parser_has__view = _init_l_lean_parser_module_import_parser_lean_parser_has__view();
lean::mark_persistent(l_lean_parser_module_import_parser_lean_parser_has__view);
 l_lean_parser_module_import_parser_lean_parser_has__tokens = _init_l_lean_parser_module_import_parser_lean_parser_has__tokens();
lean::mark_persistent(l_lean_parser_module_import_parser_lean_parser_has__tokens);
 l_lean_parser_module_import_parser___closed__1 = _init_l_lean_parser_module_import_parser___closed__1();
lean::mark_persistent(l_lean_parser_module_import_parser___closed__1);
 l_lean_parser_module_header = _init_l_lean_parser_module_header();
lean::mark_persistent(l_lean_parser_module_header);
 l_lean_parser_module_header_has__view_x_27___lambda__1___closed__1 = _init_l_lean_parser_module_header_has__view_x_27___lambda__1___closed__1();
lean::mark_persistent(l_lean_parser_module_header_has__view_x_27___lambda__1___closed__1);
 l_lean_parser_module_header_has__view_x_27___lambda__1___closed__2 = _init_l_lean_parser_module_header_has__view_x_27___lambda__1___closed__2();
lean::mark_persistent(l_lean_parser_module_header_has__view_x_27___lambda__1___closed__2);
 l_lean_parser_module_header_has__view_x_27___lambda__1___closed__3 = _init_l_lean_parser_module_header_has__view_x_27___lambda__1___closed__3();
lean::mark_persistent(l_lean_parser_module_header_has__view_x_27___lambda__1___closed__3);
 l_lean_parser_module_header_has__view_x_27___lambda__1___closed__4 = _init_l_lean_parser_module_header_has__view_x_27___lambda__1___closed__4();
lean::mark_persistent(l_lean_parser_module_header_has__view_x_27___lambda__1___closed__4);
 l_lean_parser_module_header_has__view_x_27___lambda__1___closed__5 = _init_l_lean_parser_module_header_has__view_x_27___lambda__1___closed__5();
lean::mark_persistent(l_lean_parser_module_header_has__view_x_27___lambda__1___closed__5);
 l_lean_parser_module_header_has__view_x_27___lambda__1___closed__6 = _init_l_lean_parser_module_header_has__view_x_27___lambda__1___closed__6();
lean::mark_persistent(l_lean_parser_module_header_has__view_x_27___lambda__1___closed__6);
 l_lean_parser_module_header_has__view_x_27___lambda__2___closed__1 = _init_l_lean_parser_module_header_has__view_x_27___lambda__2___closed__1();
lean::mark_persistent(l_lean_parser_module_header_has__view_x_27___lambda__2___closed__1);
 l_lean_parser_module_header_has__view_x_27 = _init_l_lean_parser_module_header_has__view_x_27();
lean::mark_persistent(l_lean_parser_module_header_has__view_x_27);
 l_lean_parser_module_header_has__view = _init_l_lean_parser_module_header_has__view();
lean::mark_persistent(l_lean_parser_module_header_has__view);
 l_lean_parser_module_header_parser_lean_parser_has__view = _init_l_lean_parser_module_header_parser_lean_parser_has__view();
lean::mark_persistent(l_lean_parser_module_header_parser_lean_parser_has__view);
 l_lean_parser_module_header_parser_lean_parser_has__tokens = _init_l_lean_parser_module_header_parser_lean_parser_has__tokens();
lean::mark_persistent(l_lean_parser_module_header_parser_lean_parser_has__tokens);
 l_lean_parser_module_header_parser___closed__1 = _init_l_lean_parser_module_header_parser___closed__1();
lean::mark_persistent(l_lean_parser_module_header_parser___closed__1);
 l_lean_parser_monad__parsec_any___at___private_init_lean_parser_module_1__commands__aux___main___spec__2___closed__1 = _init_l_lean_parser_monad__parsec_any___at___private_init_lean_parser_module_1__commands__aux___main___spec__2___closed__1();
lean::mark_persistent(l_lean_parser_monad__parsec_any___at___private_init_lean_parser_module_1__commands__aux___main___spec__2___closed__1);
 l___private_init_lean_parser_module_1__commands__aux___main___lambda__2___closed__1 = _init_l___private_init_lean_parser_module_1__commands__aux___main___lambda__2___closed__1();
lean::mark_persistent(l___private_init_lean_parser_module_1__commands__aux___main___lambda__2___closed__1);
 l___private_init_lean_parser_module_1__commands__aux___main___lambda__3___closed__1 = _init_l___private_init_lean_parser_module_1__commands__aux___main___lambda__3___closed__1();
lean::mark_persistent(l___private_init_lean_parser_module_1__commands__aux___main___lambda__3___closed__1);
 l___private_init_lean_parser_module_1__commands__aux___main___lambda__5___closed__1 = _init_l___private_init_lean_parser_module_1__commands__aux___main___lambda__5___closed__1();
lean::mark_persistent(l___private_init_lean_parser_module_1__commands__aux___main___lambda__5___closed__1);
 l___private_init_lean_parser_module_1__commands__aux___main___lambda__12___closed__1 = _init_l___private_init_lean_parser_module_1__commands__aux___main___lambda__12___closed__1();
lean::mark_persistent(l___private_init_lean_parser_module_1__commands__aux___main___lambda__12___closed__1);
 l___private_init_lean_parser_module_1__commands__aux___main___lambda__12___closed__2 = _init_l___private_init_lean_parser_module_1__commands__aux___main___lambda__12___closed__2();
lean::mark_persistent(l___private_init_lean_parser_module_1__commands__aux___main___lambda__12___closed__2);
 l___private_init_lean_parser_module_1__commands__aux___main___lambda__13___closed__1 = _init_l___private_init_lean_parser_module_1__commands__aux___main___lambda__13___closed__1();
lean::mark_persistent(l___private_init_lean_parser_module_1__commands__aux___main___lambda__13___closed__1);
 l___private_init_lean_parser_module_1__commands__aux___main___lambda__14___closed__1 = _init_l___private_init_lean_parser_module_1__commands__aux___main___lambda__14___closed__1();
lean::mark_persistent(l___private_init_lean_parser_module_1__commands__aux___main___lambda__14___closed__1);
 l___private_init_lean_parser_module_1__commands__aux___main___lambda__14___closed__2 = _init_l___private_init_lean_parser_module_1__commands__aux___main___lambda__14___closed__2();
lean::mark_persistent(l___private_init_lean_parser_module_1__commands__aux___main___lambda__14___closed__2);
 l___private_init_lean_parser_module_1__commands__aux___main___lambda__19___closed__1 = _init_l___private_init_lean_parser_module_1__commands__aux___main___lambda__19___closed__1();
lean::mark_persistent(l___private_init_lean_parser_module_1__commands__aux___main___lambda__19___closed__1);
 l___private_init_lean_parser_module_1__commands__aux___main___closed__1 = _init_l___private_init_lean_parser_module_1__commands__aux___main___closed__1();
lean::mark_persistent(l___private_init_lean_parser_module_1__commands__aux___main___closed__1);
 l_lean_parser_module_commands_parser___closed__1 = _init_l_lean_parser_module_commands_parser___closed__1();
lean::mark_persistent(l_lean_parser_module_commands_parser___closed__1);
 l_lean_parser_module_commands_tokens = _init_l_lean_parser_module_commands_tokens();
lean::mark_persistent(l_lean_parser_module_commands_tokens);
 l_lean_parser_module_commands_parser_has__view = _init_l_lean_parser_module_commands_parser_has__view();
lean::mark_persistent(l_lean_parser_module_commands_parser_has__view);
 l_lean_parser_module_eoi = _init_l_lean_parser_module_eoi();
lean::mark_persistent(l_lean_parser_module_eoi);
 l_lean_parser_monad__parsec_eoi___at_lean_parser_module_parser___spec__1___closed__1 = _init_l_lean_parser_monad__parsec_eoi___at_lean_parser_module_parser___spec__1___closed__1();
lean::mark_persistent(l_lean_parser_monad__parsec_eoi___at_lean_parser_module_parser___spec__1___closed__1);
 l_lean_parser_module_parser___lambda__5___closed__1 = _init_l_lean_parser_module_parser___lambda__5___closed__1();
lean::mark_persistent(l_lean_parser_module_parser___lambda__5___closed__1);
 l_lean_parser_module_parser___lambda__6___closed__1 = _init_l_lean_parser_module_parser___lambda__6___closed__1();
lean::mark_persistent(l_lean_parser_module_parser___lambda__6___closed__1);
 l_lean_parser_module_parser___lambda__11___closed__1 = _init_l_lean_parser_module_parser___lambda__11___closed__1();
lean::mark_persistent(l_lean_parser_module_parser___lambda__11___closed__1);
 l_lean_parser_module_parser___closed__1 = _init_l_lean_parser_module_parser___closed__1();
lean::mark_persistent(l_lean_parser_module_parser___closed__1);
 l_lean_parser_module_parser___closed__2 = _init_l_lean_parser_module_parser___closed__2();
lean::mark_persistent(l_lean_parser_module_parser___closed__2);
 l_lean_parser_module_tokens = _init_l_lean_parser_module_tokens();
lean::mark_persistent(l_lean_parser_module_tokens);
}
