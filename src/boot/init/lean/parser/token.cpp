// Lean compiler output
// Module: init.lean.parser.token
// Imports: init.lean.parser.combinators init.lean.parser.string_literal
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
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__11(obj*, obj*, obj*, obj*);
obj* l_lean_parser_detail__ident__suffix_parser_lean_parser_has__view___lambda__2(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__16(obj*, obj*, obj*);
obj* l_lean_parser_detail__ident__part_parser_lean_parser_has__tokens;
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__28(obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__22(obj*, obj*, obj*);
obj* l_list_mfoldr___main___at_lean_parser_number_x_27___spec__13(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser___spec__10(obj*);
obj* l_lean_parser_match__token___closed__2;
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__4(obj*, obj*, obj*, obj*);
obj* l_lean_parser_parsec__t_bind__mk__res___rarg(obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while1___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__1(obj*, obj*, obj*);
obj* l_reader__t_orelse___at_lean_parser_parse__bin__lit___spec__1(obj*);
obj* l_lean_parser_unicode__symbol_lean_parser_has__tokens(obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__6(uint32, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__6___boxed(obj*, obj*, obj*, obj*);
uint8 l_char_is__whitespace(uint32);
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__19___rarg(obj*, obj*);
obj* l_lean_parser_id__part___at___private_init_lean_parser_token_4__ident_x_27___spec__1(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_foldl__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__21___lambda__2___boxed(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__9(obj*, obj*, obj*);
obj* l_lean_parser_trie_match__prefix___rarg(obj*, obj*);
obj* l_lean_parser_detail__ident__suffix_has__view;
obj* l_lean_parser_match__token(obj*, obj*, obj*);
obj* l_lean_parser_number_parser_view___rarg___closed__2;
extern uint8 l_true_decidable;
obj* l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__4(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser___spec__8(obj*);
obj* l_lean_parser_number_x_27___closed__1;
obj* l___private_init_lean_parser_parsec_6__take__while__aux_x_27___main___at___private_init_lean_parser_token_2__whitespace__aux___main___spec__6(obj*, uint8, obj*);
obj* l_lean_parser_monad__parsec_str__core___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__3(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__3___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_raw_view___rarg(obj*, obj*, obj*, obj*, obj*, uint8);
obj* l_lean_parser_detail__ident__part_has__view;
obj* l_lean_parser_detail__ident__part_has__view_x_27___lambda__1___closed__2;
obj* l_lean_parser_number_has__view_x_27___lambda__2___closed__1;
obj* l_lean_parser_monad__parsec_error___at_lean_parser_number_x_27___spec__12___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_raw___rarg___lambda__3(uint8, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_finish__comment__block___closed__1;
obj* l_lean_parser_monad__parsec_error___at_lean_parser_string__lit_view_value___spec__3(obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__2(uint32, obj*, obj*, obj*);
obj* l_lean_parser_combinators_node___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__9(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_number;
obj* l_reader__t_orelse___at_lean_parser_parse__bin__lit___spec__1___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_token_4__ident_x_27(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1(obj*);
obj* l_lean_parser_raw__str_view__default___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_combinators_many___rarg___closed__1;
obj* l_lean_parser_symbol__or__ident___rarg(obj*, obj*);
obj* l_lean_parser_raw__str_view__default(obj*);
obj* l_lean_parser_as__substring___rarg___lambda__2(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_token_1__finish__comment__block__aux___main(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__21(obj*);
obj* l_lean_parser_monad__parsec_take__while1___at_lean_parser_detail__ident__part_parser___spec__1(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_many1__aux_x_27___main___at_lean_parser_parse__bin__lit___spec__2(obj*, obj*, obj*, obj*);
obj* l_lean_parser_raw___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__12(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__19(obj*);
obj* l_lean_parser_ident_parser_view___rarg___lambda__1___closed__2;
obj* l_lean_parser_raw_view___rarg___lambda__2(obj*);
obj* l_lean_parser_detail__ident_parser___closed__1;
obj* l_lean_parser_parsec__t_lookahead___at___private_init_lean_parser_token_2__whitespace__aux___main___spec__4___closed__2;
namespace lean {
obj* nat_add(obj*, obj*);
}
extern obj* l_lean_parser_parse__quoted__char___rarg___lambda__7___closed__1;
obj* l_lean_parser_monad__parsec_str__core___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__6(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__4(obj*, obj*, obj*, obj*);
obj* l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__4___closed__1;
obj* l_lean_parser_parsec__t_lookahead___at_lean_parser_detail__ident__suffix_parser___spec__1(obj*, obj*, obj*, obj*);
obj* l_lean_parser_indexed(obj*);
obj* l_lean_parser_monad__parsec_unexpected__at___at_lean_parser_string__lit_x_27___spec__6(obj*);
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__20(obj*, obj*, obj*);
obj* l_lean_parser_string__lit_parser___rarg(obj*);
obj* l_lean_parser_symbol__core___rarg(obj*, obj*, obj*, obj*);
obj* l_reader__t_lift___at_lean_parser_with__trailing___spec__1___rarg(obj*, obj*, obj*, obj*);
extern obj* l_mjoin___rarg___closed__1;
obj* l_lean_parser_string__lit_parser_tokens(obj*, obj*);
obj* l_lean_parser_string__lit_parser___rarg___closed__1;
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__9(obj*, obj*, obj*);
extern obj* l_lean_id__end__escape;
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__18(obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser___spec__11(obj*, obj*, obj*);
obj* l_lean_parser_number_view_to__nat(obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_init_lean_parser_token_4__ident_x_27___spec__4___boxed(obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_basic__parser__m_monad;
obj* l_reader__t_bind___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__7___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__6___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_ident_parser_view___rarg(obj*);
obj* l_lean_parser_symbol___rarg(obj*, obj*, obj*);
obj* l_lean_parser_with__trailing___rarg___lambda__1(obj*, obj*);
obj* l_lean_parser_detail__ident__part_has__view_x_27___lambda__1(obj*);
obj* l_lean_parser_string__lit_has__view_x_27___lambda__1(obj*);
obj* l_lean_parser_parse__hex__lit(obj*, obj*, obj*);
extern obj* l_lean_parser_rec__t_run__parsec___rarg___lambda__1___closed__1;
obj* l_lean_parser_monad__parsec_take__while_x_27___at___private_init_lean_parser_token_2__whitespace__aux___main___spec__2(obj*);
obj* l_lean_parser_as__substring___rarg___lambda__1(obj*, obj*, obj*);
obj* l_lean_parser_detail__ident_has__view_x_27___lambda__1(obj*);
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__10(obj*, obj*, obj*);
obj* l_lean_parser_list_cons_tokens___rarg(obj*, obj*);
obj* l_lean_parser_number_parser___rarg___lambda__1(obj*, obj*, obj*, obj*);
obj* l_lean_parser_with__trailing___at_lean_parser_token___spec__3(obj*, obj*, obj*, obj*);
obj* l_lean_parser_raw_view___rarg___closed__1;
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__14(obj*, obj*, obj*);
obj* l_rbmap_find___main___at_lean_parser_indexed___spec__1(obj*);
obj* l_lean_parser_number_has__view_x_27___lambda__1(obj*);
obj* l_lean_parser_raw___rarg___lambda__1(obj*, uint8, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_rec__t_run__parsec___at_lean_parser_detail__ident_parser___spec__1___lambda__1(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__3(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_digit___at_lean_parser_string__lit_view_value___spec__8(obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__2___boxed(obj*, obj*, obj*, obj*);
obj* l_option_to__monad___main___at_lean_parser_indexed___spec__2___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_parser_string__lit_parser___rarg___lambda__1(obj*, obj*, obj*, obj*);
obj* l_lean_parser_parsec__t_try__mk__res___rarg(obj*);
obj* l_lean_parser_raw__ident_parser_view___rarg(obj*);
obj* l_lean_parser_string__lit_x_27___closed__1;
obj* l_lean_parser_detail__ident__suffix_has__view_x_27;
obj* l_lean_parser_monad__parsec_whitespace___at___private_init_lean_parser_token_2__whitespace__aux___main___spec__1(obj*, obj*, obj*);
obj* l_list_reverse___rarg(obj*);
obj* l_lean_parser_ident_parser___rarg___closed__1;
extern "C" obj* lean_name_mk_string(obj*, obj*);
obj* l_reader__t_alternative___rarg(obj*, obj*);
obj* l_lean_parser_unicode__symbol_view__default___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_foldl___at___private_init_lean_parser_token_4__ident_x_27___spec__20(obj*, obj*, obj*, obj*);
obj* l_list_enum__from___main___rarg(obj*, obj*);
obj* l_lean_parser_detail__ident__part_has__view_x_27___lambda__1___closed__1;
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_number_x_27___spec__4___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_detail__ident_has__view_x_27;
obj* l_lean_parser_raw__str___rarg(obj*, obj*, obj*, obj*, uint8);
obj* l_lean_parser_number_parser_view___rarg___closed__1;
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_string__lit_view_value___spec__2(uint32, obj*);
uint8 l_char_is__digit(uint32);
obj* l_lean_parser_number_view_to__nat___main(obj*);
obj* l_lean_parser_as__substring___rarg___lambda__3(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__8___rarg(obj*, obj*);
obj* l_lean_parser_parsec__t_labels__mk__res___rarg(obj*, obj*);
obj* l_lean_parser_id__part__default___at___private_init_lean_parser_token_4__ident_x_27___spec__3(obj*, obj*, obj*);
obj* l___private_init_lean_parser_token_2__whitespace__aux___main(obj*, obj*, obj*, obj*);
obj* l_lean_parser_parsec__t_lookahead___at_lean_parser_number_x_27___spec__11(obj*, obj*, obj*, obj*, obj*, obj*);
uint8 l_lean_parser_syntax_is__of__kind___main(obj*, obj*);
extern obj* l___private_init_lean_parser_combinators_1__many1__aux___main___rarg___closed__1;
obj* l_lean_parser_ident_parser(obj*);
obj* l_lean_parser_raw___rarg(obj*, obj*, obj*, obj*, obj*, uint8);
obj* l_string_quote(obj*);
extern obj* l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_init_lean_parser_token_4__ident_x_27___spec__4(uint32, obj*, obj*, obj*);
obj* l_lean_parser_raw___rarg___lambda__3___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__26(obj*, obj*, obj*);
namespace lean {
obj* string_iterator_next(obj*);
}
obj* l_rbmap_find___main___at_lean_parser_indexed___spec__3___rarg(obj*, obj*);
obj* l_lean_parser_raw__str_lean_parser_has__tokens(obj*, obj*, obj*, obj*, obj*, uint8);
obj* l_lean_parser_ident_parser_view___rarg___closed__1;
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__5(obj*, obj*, obj*);
obj* l_lean_parser_combinators_any__of___at_lean_parser_unicode__symbol_lean_parser_has__tokens___spec__2(obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_longest__match___at_lean_parser_number_x_27___spec__10(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__7(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_foldl__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__21(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__7(obj*, obj*, obj*);
obj* l_list_mfoldl___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__16(obj*, obj*, obj*, obj*, obj*, obj*);
uint8 l_lean_is__id__end__escape(uint32);
obj* l_lean_parser_parsec__t_run___at_lean_parser_parsec_parse___spec__1___rarg(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_unexpected__at___at_lean_parser_string__lit_x_27___spec__6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_string__lit_has__view;
obj* l_lean_parser_parsec__t_failure___at_lean_parser_token___spec__4___rarg(obj*, obj*);
obj* l_lean_parser_monad__parsec_ch___at___private_init_lean_parser_token_4__ident_x_27___spec__11(uint32, obj*, obj*, obj*);
obj* l___private_init_lean_parser_token_1__finish__comment__block__aux___main___closed__3;
obj* l_lean_parser_parse__string__literal___at_lean_parser_string__lit_view_value___spec__1(obj*);
obj* l_lean_parser_monad__parsec_observing___at_lean_parser_peek__token___spec__2(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_foldl__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__21___lambda__1(obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_6__take__while__aux_x_27___main___at___private_init_lean_parser_token_2__whitespace__aux___main___spec__3(obj*, uint8, obj*);
obj* l_lean_parser_raw___rarg___lambda__2___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_raw__ident_parser_tokens(obj*, obj*);
namespace lean {
obj* string_length(obj*);
}
obj* l_list_map___main___at_lean_parser_number_x_27___spec__9(obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__13(uint32, obj*, obj*, obj*);
obj* l_lean_parser_symbol__or__ident(obj*);
obj* l___private_init_lean_parser_parsec_6__take__while__aux_x_27___main___at___private_init_lean_parser_token_2__whitespace__aux___main___spec__6___boxed(obj*, obj*, obj*);
obj* l_lean_parser_string__lit_parser_view(obj*);
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__25___rarg(obj*, obj*);
obj* l_lean_parser_symbol__core(obj*);
uint8 l_string_is__empty(obj*);
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__10___rarg(obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__25(obj*);
obj* l_lean_parser_number_parser_tokens(obj*, obj*);
obj* l_lean_parser_detail__ident__part_has__view_x_27;
obj* l_lean_parser_detail__ident__suffix_parser_lean_parser_has__view___lambda__1(obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while_x_27___at___private_init_lean_parser_token_2__whitespace__aux___main___spec__2___rarg(obj*, obj*);
uint8 l_char_is__alpha(uint32);
obj* l_lean_parser_detail__ident_parser___lambda__1(obj*, obj*, obj*, obj*, obj*);
namespace lean {
uint32 string_iterator_curr(obj*);
}
obj* l_lean_parser_parse__string__literal__aux___main___at_lean_parser_string__lit_x_27___spec__2(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__17___rarg(obj*, obj*);
obj* l_lean_parser_combinators_choice__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__29(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_token_2__whitespace__aux___main___closed__3;
obj* l_lean_parser_parsec__t_lookahead___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__4(obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_parse__hex__lit___spec__2(uint32, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_many1__aux_x_27___main___at_lean_parser_parse__bin__lit___spec__2___closed__1;
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_number_x_27___spec__2(uint32, obj*, obj*, obj*);
extern obj* l_lean_name_to__string___closed__1;
obj* l_lean_parser_number_has__view_x_27___lambda__1___closed__5;
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_lean_parser_symbol__or__ident_view___rarg(obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__3(obj*);
obj* l_function_comp___rarg(obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__14(obj*, obj*, obj*);
obj* l_lean_parser_parsec__t_lookahead___at___private_init_lean_parser_token_4__ident_x_27___spec__19(obj*, obj*, obj*);
obj* l_lean_parser_string__lit_parser_view___rarg___closed__2;
obj* l_lean_parser_number_view_of__nat(obj*);
obj* l_lean_parser_try__view___at_lean_parser_number_parser___spec__1(obj*);
obj* l_lean_parser_number_parser___rarg___closed__1;
obj* l_lean_parser_number_has__view_x_27;
obj* l_reader__t_lift___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__5(obj*);
obj* l_lean_parser_unicode__symbol_view__default(obj*);
obj* l___private_init_lean_parser_token_1__finish__comment__block__aux___main___closed__1;
obj* l_rbmap_find___main___at_lean_parser_indexed___spec__4(obj*);
obj* l_lean_parser_symbol(obj*);
obj* l_lean_parser_detail__ident__suffix;
extern obj* l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
obj* l_lean_parser_detail__ident__part_has__view_x_27___lambda__2___closed__1;
obj* l_lean_parser_raw__str(obj*);
obj* l_lean_parser_string__lit;
obj* l_lean_parser_match__token___closed__1;
obj* l_lean_parser_raw__ident_parser___rarg(obj*);
obj* l_lean_parser_raw__ident_parser(obj*);
obj* l_lean_parser_monad__parsec_take__while1___at_lean_parser_parse__hex__lit___spec__1(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__21___rarg(obj*, obj*);
obj* l___private_init_lean_parser_parsec_1__str__aux___main(obj*, obj*, obj*);
obj* l_rbnode_find___main___at_lean_parser_token__map_insert___spec__2___rarg(obj*, obj*);
obj* l_reader__t_bind___at_lean_parser_with__trailing___spec__2___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_number_has__view_x_27___lambda__1___closed__4;
obj* l_option_to__monad___main___at_lean_parser_indexed___spec__2(obj*);
obj* l_lean_parser_number_has__view;
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser___spec__3(obj*, obj*, obj*);
obj* l_lean_parser_detail__ident_x_27___closed__1;
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__23___rarg(obj*, obj*);
obj* l_reader__t_lift___at_lean_parser_with__trailing___spec__1(obj*);
obj* l_lean_parser_number_has__view_x_27___lambda__2___closed__2;
obj* l___private_init_lean_parser_token_2__whitespace__aux___main___closed__2;
obj* l_lean_parser_unicode__symbol(obj*);
obj* l_lean_parser_peek__token(obj*, obj*, obj*);
obj* l_lean_parser_rec__t_recurse___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__8(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_token_3__update__trailing(obj*, obj*);
obj* l_lean_parser_tokens___rarg(obj*);
obj* l_list_mfoldl___main___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__10(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_option_get__or__else___main___rarg(obj*, obj*);
uint8 l_lean_is__id__rest(uint32);
obj* l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_view_value___spec__7(obj*);
obj* l___private_init_lean_parser_parsec_6__take__while__aux_x_27___main___at___private_init_lean_parser_token_2__whitespace__aux___main___spec__3___boxed(obj*, obj*, obj*);
obj* l_lean_parser_string__lit_x_27___lambda__1(obj*, obj*, obj*, obj*);
obj* l_lean_parser_detail__ident__part_parser_lean_parser_has__view___lambda__3(obj*, obj*, obj*, obj*);
obj* l_lean_parser_raw__ident_parser_view(obj*);
obj* l_lean_parser_raw__str_lean_parser_has__view(obj*);
obj* l_lean_parser_string__lit_parser(obj*);
obj* l_lean_parser_with__trailing___rarg___lambda__3(obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__13(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_ch___at___private_init_lean_parser_token_4__ident_x_27___spec__11___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_parse__quoted__char___at_lean_parser_string__lit_view_value___spec__6(obj*);
extern obj* l_lean_parser_no__kind;
obj* l_lean_parser_syntax_as__node___main(obj*);
obj* l_lean_parser_string__lit_view_value___closed__1;
obj* l_string_to__nat(obj*);
obj* l_lean_parser_monad__parsec_take__while_x_27___at___private_init_lean_parser_token_2__whitespace__aux___main___spec__5(obj*);
obj* l_lean_parser_symbol_view___rarg(obj*, obj*, obj*);
obj* l_lean_parser_rec__t_run___at_lean_parser_detail__ident_parser___spec__2(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__27___rarg(obj*, obj*);
obj* l_lean_parser_symbol_view__default___rarg(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_init_lean_parser_token_4__ident_x_27___spec__17(uint32, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_number_x_27___spec__6(obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser___spec__2(uint32, obj*, obj*, obj*);
namespace lean {
uint8 string_iterator_has_next(obj*);
}
obj* l_lean_parser_raw_tokens___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_symbol_tokens___rarg(obj*, obj*);
obj* l_lean_parser_parsec__t_lookahead___at___private_init_lean_parser_token_2__whitespace__aux___main___spec__4(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_number_x_27___spec__12(obj*);
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_parse__hex__lit___spec__3(obj*, obj*, obj*);
obj* l_lean_parser_raw_view___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l_lean_parser_combinators_optional___at_lean_parser_detail__ident_x_27___spec__2(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_raw_view___rarg___lambda__1(obj*);
obj* l_lean_parser_detail__ident_parser___closed__2;
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_number_x_27___spec__3(obj*, obj*, obj*);
obj* l_lean_parser_mk__raw__res(obj*, obj*);
obj* l_lean_parser_detail__ident_has__view;
extern obj* l_char_has__repr___closed__1;
obj* l___private_init_lean_parser_token_8__to__nat__base(obj*, obj*);
obj* l_string_iterator_nextn___main(obj*, obj*);
obj* l___private_init_lean_parser_token_3__update__trailing___main(obj*, obj*);
obj* l___private_init_lean_parser_token_2__whitespace__aux___main___closed__1;
obj* l_lean_parser_token__cont(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_parsec__t_lookahead___at_lean_parser_peek__token___spec__1(obj*, obj*, obj*);
obj* l_lean_parser_string__lit_has__view_x_27___lambda__2(obj*);
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__8(obj*);
obj* l_lean_parser_detail__ident_parser(obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__7(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser___spec__8___rarg(obj*, obj*);
obj* l_lean_parser_monad__parsec_curr___at___private_init_lean_parser_token_4__ident_x_27___spec__2(obj*);
obj* l_lean_parser_detail__ident_has__view_x_27___lambda__2(obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_init_lean_parser_token_4__ident_x_27___spec__13(uint32, obj*, obj*, obj*);
obj* l_lean_parser_symbol__core___at_lean_parser_unicode__symbol_lean_parser_has__tokens___spec__1(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_combinators_node_view___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_foldl__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__21___closed__1;
obj* l_lean_parser_detail__ident__part_has__view_x_27___lambda__1___closed__3;
obj* l_lean_parser_unicode__symbol___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_parser_detail__ident_has__view_x_27___lambda__1___closed__1;
extern obj* l_lean_parser_monad__parsec_left__over___rarg___closed__1;
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__5(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_init_lean_parser_token_4__ident_x_27___spec__8(obj*, obj*, obj*, obj*);
obj* l_lean_parser_finish__comment__block___closed__2;
obj* l_lean_parser_detail__ident__suffix_has__view_x_27___lambda__2(obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_init_lean_parser_token_4__ident_x_27___spec__13___boxed(obj*, obj*, obj*, obj*);
extern obj* l_string_join___closed__1;
obj* l_lean_parser_raw__str___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_id___rarg(obj*);
obj* l_lean_parser_detail__ident__part;
obj* l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
obj* l_lean_parser_monad__parsec_take__while1___at_lean_parser_number_x_27___spec__1(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__9___boxed(obj*, obj*, obj*, obj*);
obj* l_rbmap_find___main___at_lean_parser_indexed___spec__5(obj*);
obj* l_lean_parser_token___closed__1;
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__12(obj*);
namespace lean {
uint8 nat_dec_le(obj*, obj*);
}
obj* l_lean_parser_rec__t_lean_parser_monad__parsec___rarg(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_str__core___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_parser_raw__str_lean_parser_has__view___rarg(obj*, obj*, obj*, obj*, uint8);
obj* l_lean_parser_number_x_27___lambda__1(obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while1___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__8(obj*, obj*, obj*);
obj* l_rbmap_find___main___at_lean_parser_indexed___spec__1___rarg(obj*, obj*);
obj* l_lean_parser_syntax_mk__node(obj*, obj*);
obj* l_lean_parser_monad__parsec_unexpected__at___at_lean_parser_string__lit_view_value___spec__9___rarg(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__1(uint32, obj*, obj*, obj*, obj*);
obj* l_lean_parser_detail__ident_has__view_x_27___lambda__1___closed__2;
obj* l_lean_parser_match__token___lambda__1(obj*);
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_parse__oct__lit___spec__3(obj*, obj*, obj*);
obj* l_lean_parser_detail__ident__part_parser(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__2(uint32, obj*, obj*, obj*);
obj* l_lean_parser_rec__t_run__parsec___at_lean_parser_detail__ident_parser___spec__1___closed__1;
obj* l_lean_parser_number_parser(obj*);
obj* l_lean_parser_monad__parsec_take__while1___at___private_init_lean_parser_token_4__ident_x_27___spec__12(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_init_lean_parser_token_4__ident_x_27___spec__15(obj*, obj*, obj*, obj*);
obj* l_lean_parser_detail__ident__part_parser___lambda__2(obj*, obj*, obj*, obj*);
obj* l_lean_parser_finish__comment__block(obj*, obj*, obj*, obj*);
obj* l_lean_parser_indexed___rarg___closed__1;
obj* l___private_init_lean_parser_token_5__mk__consume__token(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_raw__ident_parser___rarg___closed__1;
obj* l_lean_parser_ident_parser___rarg___lambda__1(obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_parse__oct__lit___spec__2(uint32, obj*, obj*, obj*);
obj* l_list_map___main___at_lean_parser_number_x_27___spec__9___lambda__1(obj*, obj*, obj*, obj*);
obj* l_lean_parser_combinators_longest__choice___at_lean_parser_number_x_27___spec__8(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__24(obj*, obj*, obj*);
extern obj* l_lean_parser_parsec__t_failure___rarg___closed__1;
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__13___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_token(obj*, obj*, obj*);
obj* l_lean_parser_whitespace(obj*, obj*, obj*);
obj* l_reader__t_monad__except___rarg(obj*);
obj* l_lean_parser_indexed___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_as__substring(obj*);
obj* l_lean_parser_ident_parser_view___rarg___lambda__2(obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_init_lean_parser_token_4__ident_x_27___spec__6(uint32, obj*, obj*, obj*);
obj* l_lean_parser_with__trailing___rarg(obj*, obj*, obj*, obj*);
extern obj* l_lean_id__begin__escape;
obj* l_rbmap_find___main___at_lean_parser_indexed___spec__3(obj*);
namespace lean {
obj* string_iterator_offset(obj*);
}
obj* l_list_foldl___main___at_lean_parser_unicode__symbol_lean_parser_has__tokens___spec__3(obj*, obj*, obj*, obj*, obj*);
obj* l_reader__t_lift___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__5___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_token_7__to__nat__core(obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_curr___at___private_init_lean_parser_token_4__ident_x_27___spec__2___rarg(obj*, obj*);
obj* l_lean_parser_with__trailing___rarg___lambda__2(obj*, obj*, obj*, obj*);
obj* l_lean_parser_parsec__t_failure___at_lean_parser_token___spec__4(obj*, obj*);
obj* l_lean_parser_symbol__or__ident_view(obj*);
obj* l_lean_parser_raw(obj*);
obj* l_lean_parser_monad__parsec_take__while1___at_lean_parser_parse__oct__lit___spec__1(obj*, obj*, obj*);
obj* l_lean_parser_raw_view___rarg___closed__2;
obj* l_lean_parser_detail__ident_has__view_x_27___lambda__2___closed__1;
obj* l_lean_parser_string__lit_parser_view___rarg___closed__1;
obj* l_lean_parser_monad__parsec_many1__aux_x_27___main___at_lean_parser_parse__bin__lit___spec__2___closed__2;
obj* l_lean_parser_symbol_view__default(obj*);
obj* l_lean_parser_combinators_node___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__15(obj*, obj*, obj*, obj*, obj*);
extern obj* l_list_mfoldr___main___at_lean_parser_monad__parsec_longest__match___spec__2___rarg___closed__1;
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__17(obj*);
obj* l_lean_parser_detail__ident__part_parser___lambda__1(obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_any___at_lean_parser_string__lit_view_value___spec__5(obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser___spec__6(uint32, obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__18(obj*, obj*, obj*);
obj* l_lean_parser_parsec__t_merge___rarg(obj*, obj*);
obj* l_lean_parser_indexed___rarg___lambda__1___closed__1;
obj* l_lean_parser_monad__parsec_observing___at_lean_parser_token___spec__2(obj*, obj*, obj*);
obj* l_lean_parser_substring_to__string(obj*);
obj* l_lean_parser_try__view___at_lean_parser_string__lit_parser___spec__1(obj*);
extern "C" uint8 lean_name_dec_eq(obj*, obj*);
obj* l___private_init_lean_parser_token_1__finish__comment__block__aux___main___closed__2;
obj* l_lean_parser_unicode__symbol_lean_parser_has__view(obj*);
obj* l_lean_parser_monad__parsec_unexpected__at___at_lean_parser_string__lit_view_value___spec__9(obj*);
obj* l_lean_parser_parsec__t_lookahead___at___private_init_lean_parser_token_2__whitespace__aux___main___spec__4___closed__1;
namespace lean {
uint8 string_dec_eq(obj*, obj*);
}
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser___spec__5(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_init_lean_parser_token_4__ident_x_27___spec__17___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__12___rarg(obj*, obj*);
obj* l_lean_parser_detail__ident__suffix_has__view_x_27___lambda__1___closed__1;
obj* l_lean_parser_ident_parser_view___rarg___closed__2;
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__10(obj*);
obj* l_lean_parser_detail__ident__part__escaped_has__view;
obj* l_lean_parser_id__part__escaped___at___private_init_lean_parser_token_4__ident_x_27___spec__10(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__2___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_raw__str_view__default___rarg(obj*, obj*, obj*, obj*, uint8);
obj* l_lean_parser_combinators_any__of_view___rarg(obj*, obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_combinators_choice__aux___main___rarg___closed__1;
obj* l___private_init_lean_parser_token_2__whitespace__aux(obj*, obj*, obj*, obj*);
obj* l_lean_parser_raw_view___rarg___lambda__3(obj*);
obj* l_lean_parser_indexed___rarg(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_foldl__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__21___lambda__2(uint32, obj*, obj*, obj*);
obj* l_lean_parser_detail__ident__part__escaped_has__view_x_27___lambda__1(obj*);
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__11(obj*, obj*, obj*);
obj* l_lean_parser_number_has__view_x_27___lambda__1___closed__1;
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser___spec__12(obj*);
obj* l_lean_parser_symbol_tokens(obj*, obj*);
obj* l_lean_parser_detail__ident__part__escaped_has__view_x_27;
obj* l_lean_parser_number_has__view_x_27___lambda__1___closed__3;
obj* l_lean_parser_monad__parsec_take__while_x_27___at___private_init_lean_parser_token_2__whitespace__aux___main___spec__5___rarg(obj*, obj*);
obj* l_lean_parser_as__substring___rarg(obj*, obj*, obj*, obj*);
namespace lean {
obj* string_iterator_remaining(obj*);
}
namespace lean {
obj* string_mk_iterator(obj*);
}
extern obj* l_lean_parser_basic__parser__m_alternative;
obj* l_lean_parser_with__trailing___rarg___closed__1;
obj* l_lean_parser_detail__ident__suffix_parser_lean_parser_has__view;
obj* l_rbmap_find___main___at_lean_parser_indexed___spec__4___rarg(obj*, obj*);
obj* l_lean_parser_symbol__or__ident___rarg___lambda__1(obj*, obj*, obj*, obj*);
obj* l_lean_parser_parsec__t_lookahead___at_lean_parser_token___spec__1(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while1___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__1(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_any___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__2(obj*, obj*, obj*);
obj* l_string_trim(obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_number_x_27___spec__4(uint32, obj*, obj*, obj*);
obj* l_lean_parser_number__or__string__lit(obj*, obj*, obj*);
obj* l_lean_parser_raw___rarg___lambda__2(obj*, uint8, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_option_get___main___at_lean_parser_run___spec__2(obj*);
obj* l_lean_parser_unicode__symbol_lean_parser_has__tokens___rarg(obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser___spec__9(obj*, obj*, obj*);
obj* l_lean_parser_raw___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_raw_view(obj*);
obj* l_lean_parser_ident_parser_view___rarg___lambda__1(obj*);
obj* l_lean_parser_number_parser_view(obj*);
obj* l_lean_parser_number_has__view_x_27___lambda__2(obj*);
obj* l_lean_parser_parse__string__literal__aux___main___at_lean_parser_string__lit_view_value___spec__4(obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__5(obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_5__mk__consumed__result___rarg(uint8, obj*);
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser___spec__7(obj*, obj*, obj*);
obj* l_lean_parser_combinators_monad__lift_view___rarg(obj*, obj*, obj*);
obj* l_lean_parser_combinators_seq__right_view___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_reader__t_monad___rarg(obj*);
obj* l_lean_parser_detail__ident;
obj* l_lean_parser_detail__ident__part_parser_lean_parser_has__view___lambda__2(obj*, obj*, obj*, obj*);
obj* l_lean_parser_parsec__t_lookahead___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__view___spec__1(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_token_7__to__nat__core___main(obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_init_lean_parser_token_4__ident_x_27___spec__6___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser___spec__2___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_number_x_27___lambda__2(obj*, obj*, obj*, obj*);
extern "C" obj* lean_name_mk_numeral(obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser___spec__10___rarg(obj*, obj*);
obj* l_lean_parser_detail__ident__part__escaped;
uint8 l_lean_is__id__first(uint32);
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_nat_repr(obj*);
obj* l_lean_parser_parse__string__literal___at_lean_parser_string__lit_x_27___spec__1(obj*, obj*, obj*);
obj* l___private_init_lean_parser_token_1__finish__comment__block__aux___main___closed__4;
namespace lean {
obj* nat_mul(obj*, obj*);
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser___spec__4(obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_parse__hex__lit___spec__2___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__23(obj*);
obj* l___private_init_lean_parser_parsec_3__mk__string__result___rarg(obj*, obj*);
obj* l_lean_parser_symbol__or__ident_tokens(obj*, obj*, obj*);
obj* l_lean_parser_with__trailing(obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__2(obj*);
uint8 l_lean_is__id__begin__escape(uint32);
obj* l_lean_parser_ident_parser_view(obj*);
obj* l_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens;
obj* l_lean_parser_number_has__view_x_27___lambda__1___closed__2;
obj* l_lean_parser_monad__parsec_foldl__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__21___closed__2;
obj* l_lean_parser_detail__ident__part_has__view_x_27___lambda__2(obj*);
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_number_x_27___spec__5(obj*, obj*, obj*);
obj* l_lean_parser_string__lit_has__view_x_27;
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__6(uint32, obj*, obj*, obj*);
obj* l_lean_parser_detail__ident__part__escaped_has__view_x_27___lambda__2(obj*);
obj* l___private_init_lean_parser_token_1__finish__comment__block__aux(obj*, obj*, obj*, obj*, obj*);
namespace lean {
obj* nat_sub(obj*, obj*);
}
obj* l_lean_parser_string__lit_x_27(obj*, obj*, obj*);
obj* l_lean_parser_detail__ident__part_parser___closed__1;
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__27(obj*);
obj* l_lean_parser_number_x_27___lambda__3(obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_parse__oct__lit___spec__2___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_detail__ident__part_parser_lean_parser_has__view;
obj* l_lean_parser_detail__ident__part_has__view_x_27___lambda__2___closed__2;
obj* l_lean_parser_parse__bin__lit(obj*, obj*, obj*);
extern obj* l_lean_parser_basic__parser__m_lean_parser_monad__parsec;
obj* l_reader__t_bind___at_lean_parser_with__trailing___spec__2(obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__2___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_detail__ident_x_27(obj*, obj*, obj*, obj*);
namespace lean {
obj* string_push(obj*, uint32);
}
obj* l_lean_parser_parse__oct__lit(obj*, obj*, obj*);
obj* l_dlist_singleton___rarg(obj*, obj*);
obj* l_lean_parser_symbol__core___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_basic__parser__m_monad__except;
obj* l_lean_parser_parsec__t_orelse__mk__res___rarg(obj*, obj*);
obj* l_lean_parser_symbol_view(obj*);
obj* l_lean_parser_unicode__symbol_lean_parser_has__view___rarg(obj*, obj*, obj*, obj*);
obj* l_reader__t_bind___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__7(obj*, obj*);
obj* l_lean_parser_detail__ident__part__escaped_has__view_x_27___lambda__1___closed__1;
obj* l_rbmap_find___main___at_lean_parser_indexed___spec__5___rarg(obj*, obj*);
obj* l_lean_parser_detail__ident__suffix_parser___closed__1;
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_string__lit_view_value___spec__2___boxed(obj*, obj*);
obj* l___private_init_lean_parser_token_3__update__trailing__lst(obj*, obj*);
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser___spec__13(obj*, obj*, obj*);
obj* l_lean_parser_number_has__view_x_27___lambda__1___closed__6;
obj* l_option_map___rarg(obj*, obj*);
obj* l_lean_parser_raw__str_lean_parser_has__view___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_rec__t_run__parsec___at_lean_parser_detail__ident_parser___spec__1(obj*, obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_combinators_any__of___rarg___closed__1;
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser___spec__12___rarg(obj*, obj*);
obj* l_lean_parser_number_parser_view___rarg(obj*);
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__3(obj*, obj*, obj*);
obj* l_lean_parser_number_parser___rarg(obj*);
obj* l_lean_parser_raw__str_lean_parser_has__tokens___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_substring_of__string(obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser___spec__6___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_string__lit_view_value(obj*);
obj* l_lean_parser_parse__quoted__char___at_lean_parser_string__lit_x_27___spec__3(obj*, obj*, obj*);
obj* l_lean_parser_ident_parser_tokens(obj*, obj*);
obj* l___private_init_lean_parser_rec_1__run__aux___at_lean_parser_detail__ident_parser___spec__3(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_number_x_27___spec__2___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_detail__ident__suffix_parser(obj*, obj*, obj*, obj*);
obj* l_reader__t_lift___at_lean_parser_detail__ident_x_27___spec__1(obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__9(uint32, obj*, obj*, obj*);
obj* l_lean_parser_number_x_27___lambda__4(obj*, obj*, obj*, obj*);
obj* l_lean_parser_string__lit_parser_view___rarg(obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_string__lit_view_value___spec__3___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_ident_parser___rarg(obj*);
obj* l_reader__t_lift___at_lean_parser_detail__ident_x_27___spec__1___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_detail__ident__suffix_has__view_x_27___lambda__1(obj*);
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_number_x_27___spec__7(obj*, obj*, obj*);
obj* l_char_quote__core(uint32);
obj* l___private_init_lean_parser_token_3__update__trailing__lst___main(obj*, obj*);
obj* l_lean_parser_number_x_27(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_digit___at_lean_parser_string__lit_x_27___spec__5(obj*, obj*, obj*);
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
obj* l_lean_parser_detail__ident__part_parser_lean_parser_has__view___lambda__1(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_rec_1__run__aux___main___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_parser_raw_tokens(obj*, obj*, obj*, obj*, obj*, obj*, uint8);
obj* l_lean_parser_raw_view___rarg___lambda__3___closed__1;
obj* l_lean_parser_match__token___lambda__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::cnstr_get(x_0, 1);
lean::inc(x_1);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_lean_parser_match__token___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_match__token___lambda__1), 1, 0);
return x_0;
}
}
obj* _init_l_lean_parser_match__token___closed__2() {
_start:
{
obj* x_0; obj* x_3; obj* x_4; obj* x_5; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_id___rarg), 1, 0);
lean::inc(x_0);
lean::inc(x_0);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_3, 0, x_0);
lean::closure_set(x_3, 1, x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_4, 0, x_0);
lean::closure_set(x_4, 1, x_3);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
return x_5;
}
}
obj* l_lean_parser_match__token(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_7; obj* x_8; obj* x_10; obj* x_11; obj* x_13; obj* x_14; 
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
lean::inc(x_1);
x_7 = l_lean_parser_trie_match__prefix___rarg(x_3, x_1);
x_8 = l_lean_parser_match__token___closed__1;
lean::inc(x_8);
x_10 = l_option_map___rarg(x_8, x_7);
x_11 = l_lean_parser_match__token___closed__2;
lean::inc(x_11);
x_13 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_13, 0, x_10);
lean::cnstr_set(x_13, 1, x_1);
lean::cnstr_set(x_13, 2, x_11);
x_14 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_2);
return x_14;
}
}
obj* l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_8; obj* x_9; uint8 x_10; obj* x_11; obj* x_12; obj* x_13; 
lean::dec(x_4);
x_8 = l_option_get__or__else___main___rarg(x_2, x_5);
x_9 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_0);
lean::cnstr_set(x_9, 2, x_1);
lean::cnstr_set(x_9, 3, x_3);
x_10 = 0;
x_11 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_11, 0, x_9);
lean::cnstr_set_scalar(x_11, sizeof(void*)*1, x_10);
x_12 = x_11;
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_6);
return x_13;
}
}
obj* l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg), 7, 0);
return x_2;
}
}
obj* l_lean_parser_monad__parsec_any___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = lean::string_iterator_has_next(x_1);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; obj* x_10; obj* x_11; obj* x_13; obj* x_15; obj* x_16; obj* x_18; obj* x_19; 
x_4 = lean::box(0);
x_5 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_6 = l_mjoin___rarg___closed__1;
lean::inc(x_4);
lean::inc(x_6);
lean::inc(x_5);
x_10 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_5, x_6, x_4, x_4, x_0, x_1, x_2);
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
x_16 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_16);
x_18 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_11);
if (lean::is_scalar(x_15)) {
 x_19 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_19 = x_15;
}
lean::cnstr_set(x_19, 0, x_18);
lean::cnstr_set(x_19, 1, x_13);
return x_19;
}
else
{
uint32 x_20; uint8 x_21; 
x_20 = lean::string_iterator_curr(x_1);
x_21 = l_true_decidable;
if (x_21 == 0)
{
obj* x_22; obj* x_23; obj* x_25; obj* x_27; obj* x_28; obj* x_29; obj* x_32; obj* x_33; obj* x_35; obj* x_37; obj* x_38; obj* x_40; obj* x_41; 
x_22 = l_char_quote__core(x_20);
x_23 = l_char_has__repr___closed__1;
lean::inc(x_23);
x_25 = lean::string_append(x_23, x_22);
lean::dec(x_22);
x_27 = lean::string_append(x_25, x_23);
x_28 = lean::box(0);
x_29 = l_mjoin___rarg___closed__1;
lean::inc(x_28);
lean::inc(x_29);
x_32 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_27, x_29, x_28, x_28, x_0, x_1, x_2);
x_33 = lean::cnstr_get(x_32, 0);
lean::inc(x_33);
x_35 = lean::cnstr_get(x_32, 1);
lean::inc(x_35);
if (lean::is_shared(x_32)) {
 lean::dec(x_32);
 x_37 = lean::box(0);
} else {
 lean::cnstr_release(x_32, 0);
 lean::cnstr_release(x_32, 1);
 x_37 = x_32;
}
x_38 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_38);
x_40 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_38, x_33);
if (lean::is_scalar(x_37)) {
 x_41 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_41 = x_37;
}
lean::cnstr_set(x_41, 0, x_40);
lean::cnstr_set(x_41, 1, x_35);
return x_41;
}
else
{
obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; 
lean::dec(x_0);
x_43 = lean::string_iterator_next(x_1);
x_44 = lean::box(0);
x_45 = lean::box_uint32(x_20);
x_46 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_46, 0, x_45);
lean::cnstr_set(x_46, 1, x_43);
lean::cnstr_set(x_46, 2, x_44);
x_47 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_47, 0, x_46);
lean::cnstr_set(x_47, 1, x_2);
return x_47;
}
}
}
}
obj* l_lean_parser_monad__parsec_str__core___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_7; 
lean::dec(x_2);
lean::inc(x_0);
x_7 = l_string_is__empty(x_0);
if (x_7 == 0)
{
obj* x_8; obj* x_10; obj* x_12; 
x_8 = lean::string_length(x_0);
lean::inc(x_0);
x_10 = lean::string_mk_iterator(x_0);
lean::inc(x_3);
x_12 = l___private_init_lean_parser_parsec_1__str__aux___main(x_8, x_10, x_3);
if (lean::obj_tag(x_12) == 0)
{
obj* x_15; obj* x_16; obj* x_18; uint8 x_19; obj* x_20; obj* x_21; obj* x_22; 
lean::dec(x_12);
lean::dec(x_0);
x_15 = lean::box(0);
x_16 = l_string_join___closed__1;
lean::inc(x_16);
x_18 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_18, 0, x_3);
lean::cnstr_set(x_18, 1, x_16);
lean::cnstr_set(x_18, 2, x_1);
lean::cnstr_set(x_18, 3, x_15);
x_19 = 0;
x_20 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_20, 0, x_18);
lean::cnstr_set_scalar(x_20, sizeof(void*)*1, x_19);
x_21 = x_20;
x_22 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_4);
return x_22;
}
else
{
obj* x_25; obj* x_28; obj* x_29; obj* x_30; 
lean::dec(x_1);
lean::dec(x_3);
x_25 = lean::cnstr_get(x_12, 0);
lean::inc(x_25);
lean::dec(x_12);
x_28 = lean::box(0);
x_29 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_29, 0, x_0);
lean::cnstr_set(x_29, 1, x_25);
lean::cnstr_set(x_29, 2, x_28);
x_30 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_4);
return x_30;
}
}
else
{
obj* x_33; obj* x_34; obj* x_37; obj* x_38; 
lean::dec(x_1);
lean::dec(x_0);
x_33 = l_string_join___closed__1;
x_34 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_34);
lean::inc(x_33);
x_37 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_37, 0, x_33);
lean::cnstr_set(x_37, 1, x_3);
lean::cnstr_set(x_37, 2, x_34);
x_38 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_38, 0, x_37);
lean::cnstr_set(x_38, 1, x_4);
return x_38;
}
}
}
obj* _init_l___private_init_lean_parser_token_1__finish__comment__block__aux___main___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("-/");
return x_0;
}
}
obj* _init_l___private_init_lean_parser_token_1__finish__comment__block__aux___main___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_string("-/");
x_1 = l_string_quote(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l___private_init_lean_parser_token_1__finish__comment__block__aux___main___closed__3() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("/-");
return x_0;
}
}
obj* _init_l___private_init_lean_parser_token_1__finish__comment__block__aux___main___closed__4() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_string("/-");
x_1 = l_string_quote(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_2, 0, x_1);
return x_2;
}
}
obj* l___private_init_lean_parser_token_1__finish__comment__block__aux___main(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::mk_nat_obj(0u);
x_6 = lean::nat_dec_eq(x_1, x_5);
lean::dec(x_5);
if (x_6 == 0)
{
obj* x_8; obj* x_9; uint8 x_11; obj* x_12; obj* x_13; obj* x_15; obj* x_16; obj* x_21; obj* x_22; obj* x_24; 
x_8 = lean::mk_nat_obj(1u);
x_9 = lean::nat_sub(x_1, x_8);
lean::dec(x_1);
x_11 = lean::nat_dec_eq(x_0, x_8);
x_15 = l___private_init_lean_parser_token_1__finish__comment__block__aux___main___closed__3;
x_16 = l___private_init_lean_parser_token_1__finish__comment__block__aux___main___closed__4;
lean::inc(x_3);
lean::inc(x_2);
lean::inc(x_16);
lean::inc(x_15);
x_21 = l_lean_parser_monad__parsec_str__core___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__3(x_15, x_16, x_2, x_3, x_4);
x_22 = lean::cnstr_get(x_21, 0);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_21, 1);
lean::inc(x_24);
lean::dec(x_21);
if (lean::obj_tag(x_22) == 0)
{
obj* x_27; obj* x_29; obj* x_32; obj* x_35; obj* x_36; obj* x_38; obj* x_41; 
x_27 = lean::cnstr_get(x_22, 1);
lean::inc(x_27);
x_29 = lean::cnstr_get(x_22, 2);
lean::inc(x_29);
lean::dec(x_22);
x_32 = lean::nat_add(x_0, x_8);
lean::inc(x_2);
lean::inc(x_9);
x_35 = l___private_init_lean_parser_token_1__finish__comment__block__aux___main(x_32, x_9, x_2, x_27, x_24);
x_36 = lean::cnstr_get(x_35, 0);
lean::inc(x_36);
x_38 = lean::cnstr_get(x_35, 1);
lean::inc(x_38);
lean::dec(x_35);
x_41 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_29, x_36);
x_12 = x_41;
x_13 = x_38;
goto lbl_14;
}
else
{
obj* x_42; uint8 x_44; obj* x_45; obj* x_46; obj* x_47; 
x_42 = lean::cnstr_get(x_22, 0);
lean::inc(x_42);
x_44 = lean::cnstr_get_scalar<uint8>(x_22, sizeof(void*)*1);
if (lean::is_shared(x_22)) {
 lean::dec(x_22);
 x_45 = lean::box(0);
} else {
 lean::cnstr_release(x_22, 0);
 x_45 = x_22;
}
if (lean::is_scalar(x_45)) {
 x_46 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_46 = x_45;
}
lean::cnstr_set(x_46, 0, x_42);
lean::cnstr_set_scalar(x_46, sizeof(void*)*1, x_44);
x_47 = x_46;
x_12 = x_47;
x_13 = x_24;
goto lbl_14;
}
lbl_14:
{
if (lean::obj_tag(x_12) == 0)
{
obj* x_53; 
lean::dec(x_9);
lean::dec(x_8);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
x_53 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_53, 0, x_12);
lean::cnstr_set(x_53, 1, x_13);
return x_53;
}
else
{
obj* x_54; uint8 x_56; obj* x_57; obj* x_58; 
x_54 = lean::cnstr_get(x_12, 0);
lean::inc(x_54);
x_56 = lean::cnstr_get_scalar<uint8>(x_12, sizeof(void*)*1);
if (x_56 == 0)
{
obj* x_61; obj* x_62; obj* x_67; obj* x_68; obj* x_70; 
lean::dec(x_12);
x_61 = l___private_init_lean_parser_token_1__finish__comment__block__aux___main___closed__1;
x_62 = l___private_init_lean_parser_token_1__finish__comment__block__aux___main___closed__2;
lean::inc(x_3);
lean::inc(x_2);
lean::inc(x_62);
lean::inc(x_61);
x_67 = l_lean_parser_monad__parsec_str__core___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__3(x_61, x_62, x_2, x_3, x_13);
x_68 = lean::cnstr_get(x_67, 0);
lean::inc(x_68);
x_70 = lean::cnstr_get(x_67, 1);
lean::inc(x_70);
lean::dec(x_67);
if (lean::obj_tag(x_68) == 0)
{
obj* x_73; obj* x_75; obj* x_77; 
x_73 = lean::cnstr_get(x_68, 1);
lean::inc(x_73);
x_75 = lean::cnstr_get(x_68, 2);
lean::inc(x_75);
if (lean::is_shared(x_68)) {
 lean::dec(x_68);
 x_77 = lean::box(0);
} else {
 lean::cnstr_release(x_68, 0);
 lean::cnstr_release(x_68, 1);
 lean::cnstr_release(x_68, 2);
 x_77 = x_68;
}
if (x_11 == 0)
{
obj* x_79; obj* x_83; obj* x_84; obj* x_86; obj* x_89; 
lean::dec(x_77);
x_79 = lean::nat_sub(x_0, x_8);
lean::dec(x_8);
lean::inc(x_2);
lean::inc(x_9);
x_83 = l___private_init_lean_parser_token_1__finish__comment__block__aux___main(x_79, x_9, x_2, x_73, x_70);
x_84 = lean::cnstr_get(x_83, 0);
lean::inc(x_84);
x_86 = lean::cnstr_get(x_83, 1);
lean::inc(x_86);
lean::dec(x_83);
x_89 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_75, x_84);
x_57 = x_89;
x_58 = x_86;
goto lbl_59;
}
else
{
obj* x_91; obj* x_92; obj* x_94; obj* x_95; 
lean::dec(x_8);
x_91 = lean::box(0);
x_92 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_92);
if (lean::is_scalar(x_77)) {
 x_94 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_94 = x_77;
}
lean::cnstr_set(x_94, 0, x_91);
lean::cnstr_set(x_94, 1, x_73);
lean::cnstr_set(x_94, 2, x_92);
x_95 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_75, x_94);
x_57 = x_95;
x_58 = x_70;
goto lbl_59;
}
}
else
{
obj* x_97; uint8 x_99; obj* x_100; obj* x_101; obj* x_102; 
lean::dec(x_8);
x_97 = lean::cnstr_get(x_68, 0);
lean::inc(x_97);
x_99 = lean::cnstr_get_scalar<uint8>(x_68, sizeof(void*)*1);
if (lean::is_shared(x_68)) {
 lean::dec(x_68);
 x_100 = lean::box(0);
} else {
 lean::cnstr_release(x_68, 0);
 x_100 = x_68;
}
if (lean::is_scalar(x_100)) {
 x_101 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_101 = x_100;
}
lean::cnstr_set(x_101, 0, x_97);
lean::cnstr_set_scalar(x_101, sizeof(void*)*1, x_99);
x_102 = x_101;
x_57 = x_102;
x_58 = x_70;
goto lbl_59;
}
}
else
{
obj* x_109; 
lean::dec(x_9);
lean::dec(x_8);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_54);
x_109 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_109, 0, x_12);
lean::cnstr_set(x_109, 1, x_13);
return x_109;
}
lbl_59:
{
if (lean::obj_tag(x_57) == 0)
{
obj* x_114; obj* x_115; 
lean::dec(x_9);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
x_114 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_54, x_57);
x_115 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_115, 0, x_114);
lean::cnstr_set(x_115, 1, x_58);
return x_115;
}
else
{
obj* x_116; uint8 x_118; 
x_116 = lean::cnstr_get(x_57, 0);
lean::inc(x_116);
x_118 = lean::cnstr_get_scalar<uint8>(x_57, sizeof(void*)*1);
if (x_118 == 0)
{
obj* x_121; obj* x_122; obj* x_124; obj* x_126; 
lean::dec(x_57);
lean::inc(x_2);
x_121 = l_lean_parser_monad__parsec_any___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__2(x_2, x_3, x_58);
x_122 = lean::cnstr_get(x_121, 0);
lean::inc(x_122);
x_124 = lean::cnstr_get(x_121, 1);
lean::inc(x_124);
if (lean::is_shared(x_121)) {
 lean::dec(x_121);
 x_126 = lean::box(0);
} else {
 lean::cnstr_release(x_121, 0);
 lean::cnstr_release(x_121, 1);
 x_126 = x_121;
}
if (lean::obj_tag(x_122) == 0)
{
obj* x_127; obj* x_129; obj* x_132; obj* x_133; obj* x_135; obj* x_138; obj* x_139; obj* x_140; obj* x_141; 
x_127 = lean::cnstr_get(x_122, 1);
lean::inc(x_127);
x_129 = lean::cnstr_get(x_122, 2);
lean::inc(x_129);
lean::dec(x_122);
x_132 = l___private_init_lean_parser_token_1__finish__comment__block__aux___main(x_0, x_9, x_2, x_127, x_124);
x_133 = lean::cnstr_get(x_132, 0);
lean::inc(x_133);
x_135 = lean::cnstr_get(x_132, 1);
lean::inc(x_135);
lean::dec(x_132);
x_138 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_129, x_133);
x_139 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_116, x_138);
x_140 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_54, x_139);
if (lean::is_scalar(x_126)) {
 x_141 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_141 = x_126;
}
lean::cnstr_set(x_141, 0, x_140);
lean::cnstr_set(x_141, 1, x_135);
return x_141;
}
else
{
obj* x_145; uint8 x_147; obj* x_148; obj* x_149; obj* x_150; obj* x_151; obj* x_152; obj* x_153; 
lean::dec(x_9);
lean::dec(x_0);
lean::dec(x_2);
x_145 = lean::cnstr_get(x_122, 0);
lean::inc(x_145);
x_147 = lean::cnstr_get_scalar<uint8>(x_122, sizeof(void*)*1);
if (lean::is_shared(x_122)) {
 lean::dec(x_122);
 x_148 = lean::box(0);
} else {
 lean::cnstr_release(x_122, 0);
 x_148 = x_122;
}
if (lean::is_scalar(x_148)) {
 x_149 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_149 = x_148;
}
lean::cnstr_set(x_149, 0, x_145);
lean::cnstr_set_scalar(x_149, sizeof(void*)*1, x_147);
x_150 = x_149;
x_151 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_116, x_150);
x_152 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_54, x_151);
if (lean::is_scalar(x_126)) {
 x_153 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_153 = x_126;
}
lean::cnstr_set(x_153, 0, x_152);
lean::cnstr_set(x_153, 1, x_124);
return x_153;
}
}
else
{
obj* x_159; obj* x_160; 
lean::dec(x_9);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_116);
x_159 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_54, x_57);
x_160 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_160, 0, x_159);
lean::cnstr_set(x_160, 1, x_58);
return x_160;
}
}
}
}
}
}
else
{
obj* x_163; obj* x_164; obj* x_165; obj* x_169; 
lean::dec(x_1);
lean::dec(x_0);
x_163 = lean::box(0);
x_164 = l___private_init_lean_parser_combinators_1__many1__aux___main___rarg___closed__1;
x_165 = l_mjoin___rarg___closed__1;
lean::inc(x_163);
lean::inc(x_165);
lean::inc(x_164);
x_169 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_164, x_165, x_163, x_163, x_2, x_3, x_4);
return x_169;
}
}
}
obj* l___private_init_lean_parser_token_1__finish__comment__block__aux(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l___private_init_lean_parser_token_1__finish__comment__block__aux___main(x_0, x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* _init_l_lean_parser_finish__comment__block___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("end of comment block");
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_lean_parser_finish__comment__block___closed__2() {
_start:
{
obj* x_0; obj* x_2; obj* x_3; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_id___rarg), 1, 0);
lean::inc(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_2, 0, x_0);
lean::closure_set(x_2, 1, x_0);
x_3 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_3, 0, x_2);
return x_3;
}
}
obj* l_lean_parser_finish__comment__block(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_9; obj* x_10; obj* x_12; obj* x_14; obj* x_15; obj* x_17; obj* x_18; obj* x_20; obj* x_21; 
x_4 = lean::string_iterator_remaining(x_2);
x_5 = lean::mk_nat_obj(1u);
x_6 = lean::nat_add(x_4, x_5);
lean::dec(x_5);
lean::dec(x_4);
x_9 = l___private_init_lean_parser_token_1__finish__comment__block__aux___main(x_0, x_6, x_1, x_2, x_3);
x_10 = lean::cnstr_get(x_9, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_9, 1);
lean::inc(x_12);
if (lean::is_shared(x_9)) {
 lean::dec(x_9);
 x_14 = lean::box(0);
} else {
 lean::cnstr_release(x_9, 0);
 lean::cnstr_release(x_9, 1);
 x_14 = x_9;
}
x_15 = l_lean_parser_finish__comment__block___closed__1;
lean::inc(x_15);
x_17 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_10, x_15);
x_18 = l_lean_parser_finish__comment__block___closed__2;
lean::inc(x_18);
x_20 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_18, x_17);
if (lean::is_scalar(x_14)) {
 x_21 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_21 = x_14;
}
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_12);
return x_21;
}
}
obj* l___private_init_lean_parser_parsec_6__take__while__aux_x_27___main___at___private_init_lean_parser_token_2__whitespace__aux___main___spec__3(obj* x_0, uint8 x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
uint8 x_6; 
x_6 = lean::string_iterator_has_next(x_2);
if (x_6 == 0)
{
obj* x_8; 
lean::dec(x_0);
x_8 = l___private_init_lean_parser_parsec_5__mk__consumed__result___rarg(x_1, x_2);
return x_8;
}
else
{
uint32 x_9; uint8 x_10; 
x_9 = lean::string_iterator_curr(x_2);
x_10 = l_char_is__whitespace(x_9);
if (x_10 == 0)
{
obj* x_12; 
lean::dec(x_0);
x_12 = l___private_init_lean_parser_parsec_5__mk__consumed__result___rarg(x_1, x_2);
return x_12;
}
else
{
obj* x_13; obj* x_14; obj* x_17; uint8 x_18; 
x_13 = lean::mk_nat_obj(1u);
x_14 = lean::nat_sub(x_0, x_13);
lean::dec(x_13);
lean::dec(x_0);
x_17 = lean::string_iterator_next(x_2);
x_18 = 1;
x_0 = x_14;
x_1 = x_18;
x_2 = x_17;
goto _start;
}
}
}
else
{
obj* x_21; 
lean::dec(x_0);
x_21 = l___private_init_lean_parser_parsec_5__mk__consumed__result___rarg(x_1, x_2);
return x_21;
}
}
}
obj* l_lean_parser_monad__parsec_take__while_x_27___at___private_init_lean_parser_token_2__whitespace__aux___main___spec__2___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; uint8 x_3; obj* x_4; obj* x_5; 
x_2 = lean::string_iterator_remaining(x_0);
x_3 = 0;
x_4 = l___private_init_lean_parser_parsec_6__take__while__aux_x_27___main___at___private_init_lean_parser_token_2__whitespace__aux___main___spec__3(x_2, x_3, x_0);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_1);
return x_5;
}
}
obj* l_lean_parser_monad__parsec_take__while_x_27___at___private_init_lean_parser_token_2__whitespace__aux___main___spec__2(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_take__while_x_27___at___private_init_lean_parser_token_2__whitespace__aux___main___spec__2___rarg), 2, 0);
return x_2;
}
}
obj* l_lean_parser_monad__parsec_whitespace___at___private_init_lean_parser_token_2__whitespace__aux___main___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; 
lean::dec(x_0);
x_4 = l_lean_parser_monad__parsec_take__while_x_27___at___private_init_lean_parser_token_2__whitespace__aux___main___spec__2___rarg(x_1, x_2);
return x_4;
}
}
obj* _init_l_lean_parser_parsec__t_lookahead___at___private_init_lean_parser_token_2__whitespace__aux___main___spec__4___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("-");
return x_0;
}
}
obj* _init_l_lean_parser_parsec__t_lookahead___at___private_init_lean_parser_token_2__whitespace__aux___main___spec__4___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_string("-");
x_1 = l_string_quote(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_lean_parser_parsec__t_lookahead___at___private_init_lean_parser_token_2__whitespace__aux___main___spec__4(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_8; obj* x_9; obj* x_11; obj* x_13; 
x_3 = l_lean_parser_parsec__t_lookahead___at___private_init_lean_parser_token_2__whitespace__aux___main___spec__4___closed__1;
x_4 = l_lean_parser_parsec__t_lookahead___at___private_init_lean_parser_token_2__whitespace__aux___main___spec__4___closed__2;
lean::inc(x_1);
lean::inc(x_4);
lean::inc(x_3);
x_8 = l_lean_parser_monad__parsec_str__core___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__3(x_3, x_4, x_0, x_1, x_2);
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
if (lean::is_shared(x_8)) {
 lean::dec(x_8);
 x_13 = lean::box(0);
} else {
 lean::cnstr_release(x_8, 0);
 lean::cnstr_release(x_8, 1);
 x_13 = x_8;
}
if (lean::obj_tag(x_9) == 0)
{
obj* x_14; obj* x_16; obj* x_18; uint8 x_19; obj* x_20; obj* x_21; obj* x_23; obj* x_24; 
x_14 = lean::cnstr_get(x_9, 1);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_9, 2);
lean::inc(x_16);
if (lean::is_shared(x_9)) {
 lean::dec(x_9);
 x_18 = lean::box(0);
} else {
 lean::cnstr_release(x_9, 0);
 lean::cnstr_release(x_9, 1);
 lean::cnstr_release(x_9, 2);
 x_18 = x_9;
}
x_19 = 0;
x_20 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_21 = lean::box(x_19);
lean::inc(x_20);
if (lean::is_scalar(x_18)) {
 x_23 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_23 = x_18;
}
lean::cnstr_set(x_23, 0, x_21);
lean::cnstr_set(x_23, 1, x_14);
lean::cnstr_set(x_23, 2, x_20);
x_24 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_23);
if (lean::obj_tag(x_24) == 0)
{
if (lean::obj_tag(x_24) == 0)
{
obj* x_25; obj* x_27; obj* x_29; obj* x_30; 
x_25 = lean::cnstr_get(x_24, 0);
lean::inc(x_25);
if (lean::is_shared(x_24)) {
 lean::dec(x_24);
 x_27 = lean::box(0);
} else {
 lean::cnstr_release(x_24, 0);
 lean::cnstr_release(x_24, 1);
 lean::cnstr_release(x_24, 2);
 x_27 = x_24;
}
lean::inc(x_20);
if (lean::is_scalar(x_27)) {
 x_29 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_29 = x_27;
}
lean::cnstr_set(x_29, 0, x_25);
lean::cnstr_set(x_29, 1, x_1);
lean::cnstr_set(x_29, 2, x_20);
if (lean::is_scalar(x_13)) {
 x_30 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_30 = x_13;
}
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_11);
return x_30;
}
else
{
obj* x_32; 
lean::dec(x_1);
if (lean::is_scalar(x_13)) {
 x_32 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_32 = x_13;
}
lean::cnstr_set(x_32, 0, x_24);
lean::cnstr_set(x_32, 1, x_11);
return x_32;
}
}
else
{
uint8 x_34; obj* x_35; obj* x_37; obj* x_38; 
lean::dec(x_24);
x_34 = 1;
x_35 = lean::box(x_34);
lean::inc(x_20);
x_37 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_37, 0, x_35);
lean::cnstr_set(x_37, 1, x_1);
lean::cnstr_set(x_37, 2, x_20);
if (lean::is_scalar(x_13)) {
 x_38 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_38 = x_13;
}
lean::cnstr_set(x_38, 0, x_37);
lean::cnstr_set(x_38, 1, x_11);
return x_38;
}
}
else
{
uint8 x_40; obj* x_41; obj* x_42; obj* x_44; obj* x_45; 
lean::dec(x_9);
x_40 = 1;
x_41 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_42 = lean::box(x_40);
lean::inc(x_41);
x_44 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_44, 0, x_42);
lean::cnstr_set(x_44, 1, x_1);
lean::cnstr_set(x_44, 2, x_41);
if (lean::is_scalar(x_13)) {
 x_45 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_45 = x_13;
}
lean::cnstr_set(x_45, 0, x_44);
lean::cnstr_set(x_45, 1, x_11);
return x_45;
}
}
}
obj* l___private_init_lean_parser_parsec_6__take__while__aux_x_27___main___at___private_init_lean_parser_token_2__whitespace__aux___main___spec__6(obj* x_0, uint8 x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
uint8 x_6; 
x_6 = lean::string_iterator_has_next(x_2);
if (x_6 == 0)
{
obj* x_8; 
lean::dec(x_0);
x_8 = l___private_init_lean_parser_parsec_5__mk__consumed__result___rarg(x_1, x_2);
return x_8;
}
else
{
uint32 x_9; obj* x_10; obj* x_11; uint8 x_12; 
x_9 = lean::string_iterator_curr(x_2);
x_10 = lean::mk_nat_obj(10u);
x_11 = lean::box_uint32(x_9);
x_12 = lean::nat_dec_eq(x_11, x_10);
lean::dec(x_10);
lean::dec(x_11);
if (x_12 == 0)
{
obj* x_15; obj* x_16; obj* x_19; uint8 x_20; 
x_15 = lean::mk_nat_obj(1u);
x_16 = lean::nat_sub(x_0, x_15);
lean::dec(x_15);
lean::dec(x_0);
x_19 = lean::string_iterator_next(x_2);
x_20 = 1;
x_0 = x_16;
x_1 = x_20;
x_2 = x_19;
goto _start;
}
else
{
obj* x_23; 
lean::dec(x_0);
x_23 = l___private_init_lean_parser_parsec_5__mk__consumed__result___rarg(x_1, x_2);
return x_23;
}
}
}
else
{
obj* x_25; 
lean::dec(x_0);
x_25 = l___private_init_lean_parser_parsec_5__mk__consumed__result___rarg(x_1, x_2);
return x_25;
}
}
}
obj* l_lean_parser_monad__parsec_take__while_x_27___at___private_init_lean_parser_token_2__whitespace__aux___main___spec__5___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; uint8 x_3; obj* x_4; obj* x_5; 
x_2 = lean::string_iterator_remaining(x_0);
x_3 = 0;
x_4 = l___private_init_lean_parser_parsec_6__take__while__aux_x_27___main___at___private_init_lean_parser_token_2__whitespace__aux___main___spec__6(x_2, x_3, x_0);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_1);
return x_5;
}
}
obj* l_lean_parser_monad__parsec_take__while_x_27___at___private_init_lean_parser_token_2__whitespace__aux___main___spec__5(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_take__while_x_27___at___private_init_lean_parser_token_2__whitespace__aux___main___spec__5___rarg), 2, 0);
return x_2;
}
}
obj* _init_l___private_init_lean_parser_token_2__whitespace__aux___main___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("input");
return x_0;
}
}
obj* _init_l___private_init_lean_parser_token_2__whitespace__aux___main___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("--");
return x_0;
}
}
obj* _init_l___private_init_lean_parser_token_2__whitespace__aux___main___closed__3() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_string("--");
x_1 = l_string_quote(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_2, 0, x_1);
return x_2;
}
}
obj* l___private_init_lean_parser_token_2__whitespace__aux___main(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::nat_dec_eq(x_0, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
obj* x_8; obj* x_9; obj* x_11; obj* x_13; 
lean::inc(x_1);
x_8 = l_lean_parser_monad__parsec_whitespace___at___private_init_lean_parser_token_2__whitespace__aux___main___spec__1(x_1, x_2, x_3);
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
if (lean::is_shared(x_8)) {
 lean::dec(x_8);
 x_13 = lean::box(0);
} else {
 lean::cnstr_release(x_8, 0);
 lean::cnstr_release(x_8, 1);
 x_13 = x_8;
}
if (lean::obj_tag(x_9) == 0)
{
obj* x_14; obj* x_16; obj* x_18; obj* x_19; obj* x_20; obj* x_22; obj* x_23; obj* x_25; obj* x_26; obj* x_31; obj* x_32; obj* x_34; 
x_14 = lean::cnstr_get(x_9, 1);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_9, 2);
lean::inc(x_16);
if (lean::is_shared(x_9)) {
 lean::dec(x_9);
 x_18 = lean::box(0);
} else {
 lean::cnstr_release(x_9, 0);
 lean::cnstr_release(x_9, 1);
 lean::cnstr_release(x_9, 2);
 x_18 = x_9;
}
x_19 = lean::mk_nat_obj(1u);
x_20 = lean::nat_sub(x_0, x_19);
lean::dec(x_0);
x_25 = l___private_init_lean_parser_token_2__whitespace__aux___main___closed__2;
x_26 = l___private_init_lean_parser_token_2__whitespace__aux___main___closed__3;
lean::inc(x_14);
lean::inc(x_1);
lean::inc(x_26);
lean::inc(x_25);
x_31 = l_lean_parser_monad__parsec_str__core___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__3(x_25, x_26, x_1, x_14, x_11);
x_32 = lean::cnstr_get(x_31, 0);
lean::inc(x_32);
x_34 = lean::cnstr_get(x_31, 1);
lean::inc(x_34);
lean::dec(x_31);
if (lean::obj_tag(x_32) == 0)
{
obj* x_37; obj* x_39; obj* x_42; obj* x_43; obj* x_45; obj* x_48; 
x_37 = lean::cnstr_get(x_32, 1);
lean::inc(x_37);
x_39 = lean::cnstr_get(x_32, 2);
lean::inc(x_39);
lean::dec(x_32);
x_42 = l_lean_parser_monad__parsec_take__while_x_27___at___private_init_lean_parser_token_2__whitespace__aux___main___spec__5___rarg(x_37, x_34);
x_43 = lean::cnstr_get(x_42, 0);
lean::inc(x_43);
x_45 = lean::cnstr_get(x_42, 1);
lean::inc(x_45);
lean::dec(x_42);
x_48 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_39, x_43);
if (lean::obj_tag(x_48) == 0)
{
obj* x_49; obj* x_51; obj* x_56; obj* x_57; obj* x_59; obj* x_62; 
x_49 = lean::cnstr_get(x_48, 1);
lean::inc(x_49);
x_51 = lean::cnstr_get(x_48, 2);
lean::inc(x_51);
lean::dec(x_48);
lean::inc(x_1);
lean::inc(x_20);
x_56 = l___private_init_lean_parser_token_2__whitespace__aux___main(x_20, x_1, x_49, x_45);
x_57 = lean::cnstr_get(x_56, 0);
lean::inc(x_57);
x_59 = lean::cnstr_get(x_56, 1);
lean::inc(x_59);
lean::dec(x_56);
x_62 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_51, x_57);
x_22 = x_62;
x_23 = x_59;
goto lbl_24;
}
else
{
obj* x_63; uint8 x_65; obj* x_66; obj* x_67; obj* x_68; 
x_63 = lean::cnstr_get(x_48, 0);
lean::inc(x_63);
x_65 = lean::cnstr_get_scalar<uint8>(x_48, sizeof(void*)*1);
if (lean::is_shared(x_48)) {
 lean::dec(x_48);
 x_66 = lean::box(0);
} else {
 lean::cnstr_release(x_48, 0);
 x_66 = x_48;
}
if (lean::is_scalar(x_66)) {
 x_67 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_67 = x_66;
}
lean::cnstr_set(x_67, 0, x_63);
lean::cnstr_set_scalar(x_67, sizeof(void*)*1, x_65);
x_68 = x_67;
x_22 = x_68;
x_23 = x_45;
goto lbl_24;
}
}
else
{
obj* x_69; uint8 x_71; obj* x_72; obj* x_73; obj* x_74; 
x_69 = lean::cnstr_get(x_32, 0);
lean::inc(x_69);
x_71 = lean::cnstr_get_scalar<uint8>(x_32, sizeof(void*)*1);
if (lean::is_shared(x_32)) {
 lean::dec(x_32);
 x_72 = lean::box(0);
} else {
 lean::cnstr_release(x_32, 0);
 x_72 = x_32;
}
if (lean::is_scalar(x_72)) {
 x_73 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_73 = x_72;
}
lean::cnstr_set(x_73, 0, x_69);
lean::cnstr_set_scalar(x_73, sizeof(void*)*1, x_71);
x_74 = x_73;
x_22 = x_74;
x_23 = x_34;
goto lbl_24;
}
lbl_24:
{
if (lean::obj_tag(x_22) == 0)
{
obj* x_80; obj* x_81; 
lean::dec(x_20);
lean::dec(x_14);
lean::dec(x_1);
lean::dec(x_18);
lean::dec(x_19);
x_80 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_22);
if (lean::is_scalar(x_13)) {
 x_81 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_81 = x_13;
}
lean::cnstr_set(x_81, 0, x_80);
lean::cnstr_set(x_81, 1, x_23);
return x_81;
}
else
{
obj* x_82; uint8 x_84; obj* x_85; obj* x_86; 
x_82 = lean::cnstr_get(x_22, 0);
lean::inc(x_82);
x_84 = lean::cnstr_get_scalar<uint8>(x_22, sizeof(void*)*1);
if (x_84 == 0)
{
obj* x_89; obj* x_90; obj* x_95; obj* x_96; obj* x_98; 
lean::dec(x_22);
x_89 = l___private_init_lean_parser_token_1__finish__comment__block__aux___main___closed__3;
x_90 = l___private_init_lean_parser_token_1__finish__comment__block__aux___main___closed__4;
lean::inc(x_14);
lean::inc(x_1);
lean::inc(x_90);
lean::inc(x_89);
x_95 = l_lean_parser_monad__parsec_str__core___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__3(x_89, x_90, x_1, x_14, x_23);
x_96 = lean::cnstr_get(x_95, 0);
lean::inc(x_96);
x_98 = lean::cnstr_get(x_95, 1);
lean::inc(x_98);
lean::dec(x_95);
if (lean::obj_tag(x_96) == 0)
{
obj* x_101; obj* x_103; obj* x_105; obj* x_108; obj* x_109; obj* x_111; 
x_101 = lean::cnstr_get(x_96, 1);
lean::inc(x_101);
x_103 = lean::cnstr_get(x_96, 2);
lean::inc(x_103);
if (lean::is_shared(x_96)) {
 lean::dec(x_96);
 x_105 = lean::box(0);
} else {
 lean::cnstr_release(x_96, 0);
 lean::cnstr_release(x_96, 1);
 lean::cnstr_release(x_96, 2);
 x_105 = x_96;
}
lean::inc(x_101);
lean::inc(x_1);
x_108 = l_lean_parser_parsec__t_lookahead___at___private_init_lean_parser_token_2__whitespace__aux___main___spec__4(x_1, x_101, x_98);
x_109 = lean::cnstr_get(x_108, 0);
lean::inc(x_109);
x_111 = lean::cnstr_get(x_108, 1);
lean::inc(x_111);
lean::dec(x_108);
if (lean::obj_tag(x_109) == 0)
{
obj* x_114; obj* x_116; obj* x_118; uint8 x_121; 
x_114 = lean::cnstr_get(x_109, 0);
lean::inc(x_114);
x_116 = lean::cnstr_get(x_109, 1);
lean::inc(x_116);
x_118 = lean::cnstr_get(x_109, 2);
lean::inc(x_118);
lean::dec(x_109);
x_121 = lean::unbox(x_114);
lean::dec(x_114);
if (x_121 == 0)
{
obj* x_124; obj* x_125; obj* x_126; obj* x_127; obj* x_131; obj* x_132; obj* x_134; obj* x_137; obj* x_138; obj* x_140; obj* x_141; obj* x_142; 
lean::dec(x_105);
x_124 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_124, 0, x_101);
x_125 = lean::box(0);
x_126 = l___private_init_lean_parser_token_2__whitespace__aux___main___closed__1;
x_127 = l_mjoin___rarg___closed__1;
lean::inc(x_1);
lean::inc(x_127);
lean::inc(x_126);
x_131 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_126, x_127, x_124, x_125, x_1, x_116, x_111);
x_132 = lean::cnstr_get(x_131, 0);
lean::inc(x_132);
x_134 = lean::cnstr_get(x_131, 1);
lean::inc(x_134);
lean::dec(x_131);
x_137 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_118, x_132);
x_138 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_138);
x_140 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_138, x_137);
x_141 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_103, x_140);
x_142 = l_lean_parser_parsec__t_try__mk__res___rarg(x_141);
x_85 = x_142;
x_86 = x_134;
goto lbl_87;
}
else
{
obj* x_144; obj* x_145; obj* x_147; obj* x_148; obj* x_150; obj* x_151; obj* x_152; 
lean::dec(x_101);
x_144 = lean::box(0);
x_145 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_145);
if (lean::is_scalar(x_105)) {
 x_147 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_147 = x_105;
}
lean::cnstr_set(x_147, 0, x_144);
lean::cnstr_set(x_147, 1, x_116);
lean::cnstr_set(x_147, 2, x_145);
x_148 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_118, x_147);
lean::inc(x_145);
x_150 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_145, x_148);
x_151 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_103, x_150);
x_152 = l_lean_parser_parsec__t_try__mk__res___rarg(x_151);
x_85 = x_152;
x_86 = x_111;
goto lbl_87;
}
}
else
{
obj* x_155; uint8 x_157; obj* x_158; obj* x_159; obj* x_160; obj* x_161; obj* x_163; obj* x_164; obj* x_165; 
lean::dec(x_101);
lean::dec(x_105);
x_155 = lean::cnstr_get(x_109, 0);
lean::inc(x_155);
x_157 = lean::cnstr_get_scalar<uint8>(x_109, sizeof(void*)*1);
if (lean::is_shared(x_109)) {
 lean::dec(x_109);
 x_158 = lean::box(0);
} else {
 lean::cnstr_release(x_109, 0);
 x_158 = x_109;
}
if (lean::is_scalar(x_158)) {
 x_159 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_159 = x_158;
}
lean::cnstr_set(x_159, 0, x_155);
lean::cnstr_set_scalar(x_159, sizeof(void*)*1, x_157);
x_160 = x_159;
x_161 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_161);
x_163 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_161, x_160);
x_164 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_103, x_163);
x_165 = l_lean_parser_parsec__t_try__mk__res___rarg(x_164);
x_85 = x_165;
x_86 = x_111;
goto lbl_87;
}
}
else
{
obj* x_166; obj* x_168; uint8 x_169; obj* x_170; obj* x_171; 
x_166 = lean::cnstr_get(x_96, 0);
lean::inc(x_166);
if (lean::is_shared(x_96)) {
 lean::dec(x_96);
 x_168 = lean::box(0);
} else {
 lean::cnstr_release(x_96, 0);
 x_168 = x_96;
}
x_169 = 0;
if (lean::is_scalar(x_168)) {
 x_170 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_170 = x_168;
}
lean::cnstr_set(x_170, 0, x_166);
lean::cnstr_set_scalar(x_170, sizeof(void*)*1, x_169);
x_171 = x_170;
x_85 = x_171;
x_86 = x_98;
goto lbl_87;
}
}
else
{
obj* x_179; obj* x_180; 
lean::dec(x_20);
lean::dec(x_13);
lean::dec(x_14);
lean::dec(x_1);
lean::dec(x_18);
lean::dec(x_19);
lean::dec(x_82);
x_179 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_22);
x_180 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_180, 0, x_179);
lean::cnstr_set(x_180, 1, x_23);
return x_180;
}
lbl_87:
{
if (lean::obj_tag(x_85) == 0)
{
obj* x_181; obj* x_183; obj* x_187; obj* x_188; obj* x_190; obj* x_193; 
x_181 = lean::cnstr_get(x_85, 1);
lean::inc(x_181);
x_183 = lean::cnstr_get(x_85, 2);
lean::inc(x_183);
lean::dec(x_85);
lean::inc(x_1);
x_187 = l_lean_parser_finish__comment__block(x_19, x_1, x_181, x_86);
x_188 = lean::cnstr_get(x_187, 0);
lean::inc(x_188);
x_190 = lean::cnstr_get(x_187, 1);
lean::inc(x_190);
lean::dec(x_187);
x_193 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_183, x_188);
if (lean::obj_tag(x_193) == 0)
{
obj* x_194; obj* x_196; obj* x_199; obj* x_200; obj* x_202; obj* x_205; 
x_194 = lean::cnstr_get(x_193, 1);
lean::inc(x_194);
x_196 = lean::cnstr_get(x_193, 2);
lean::inc(x_196);
lean::dec(x_193);
x_199 = l___private_init_lean_parser_token_2__whitespace__aux___main(x_20, x_1, x_194, x_190);
x_200 = lean::cnstr_get(x_199, 0);
lean::inc(x_200);
x_202 = lean::cnstr_get(x_199, 1);
lean::inc(x_202);
lean::dec(x_199);
x_205 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_196, x_200);
if (lean::obj_tag(x_205) == 0)
{
obj* x_208; obj* x_209; obj* x_210; 
lean::dec(x_14);
lean::dec(x_18);
x_208 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_82, x_205);
x_209 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_208);
if (lean::is_scalar(x_13)) {
 x_210 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_210 = x_13;
}
lean::cnstr_set(x_210, 0, x_209);
lean::cnstr_set(x_210, 1, x_202);
return x_210;
}
else
{
obj* x_211; uint8 x_213; 
x_211 = lean::cnstr_get(x_205, 0);
lean::inc(x_211);
x_213 = lean::cnstr_get_scalar<uint8>(x_205, sizeof(void*)*1);
if (x_213 == 0)
{
obj* x_215; obj* x_218; obj* x_220; obj* x_221; obj* x_224; obj* x_225; obj* x_226; obj* x_227; obj* x_228; obj* x_229; 
lean::dec(x_205);
x_215 = lean::cnstr_get(x_211, 2);
lean::inc(x_215);
lean::dec(x_211);
x_218 = l_mjoin___rarg___closed__1;
lean::inc(x_218);
x_220 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_220, 0, x_215);
lean::closure_set(x_220, 1, x_218);
x_221 = lean::cnstr_get(x_82, 2);
lean::inc(x_221);
lean::dec(x_82);
x_224 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_224, 0, x_221);
lean::closure_set(x_224, 1, x_220);
x_225 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_225, 0, x_224);
x_226 = lean::box(0);
if (lean::is_scalar(x_18)) {
 x_227 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_227 = x_18;
}
lean::cnstr_set(x_227, 0, x_226);
lean::cnstr_set(x_227, 1, x_14);
lean::cnstr_set(x_227, 2, x_225);
x_228 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_227);
if (lean::is_scalar(x_13)) {
 x_229 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_229 = x_13;
}
lean::cnstr_set(x_229, 0, x_228);
lean::cnstr_set(x_229, 1, x_202);
return x_229;
}
else
{
obj* x_233; obj* x_234; obj* x_235; 
lean::dec(x_211);
lean::dec(x_14);
lean::dec(x_18);
x_233 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_82, x_205);
x_234 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_233);
if (lean::is_scalar(x_13)) {
 x_235 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_235 = x_13;
}
lean::cnstr_set(x_235, 0, x_234);
lean::cnstr_set(x_235, 1, x_202);
return x_235;
}
}
}
else
{
obj* x_238; uint8 x_240; obj* x_241; 
lean::dec(x_20);
lean::dec(x_1);
x_238 = lean::cnstr_get(x_193, 0);
lean::inc(x_238);
x_240 = lean::cnstr_get_scalar<uint8>(x_193, sizeof(void*)*1);
if (lean::is_shared(x_193)) {
 lean::dec(x_193);
 x_241 = lean::box(0);
} else {
 lean::cnstr_release(x_193, 0);
 x_241 = x_193;
}
if (x_240 == 0)
{
obj* x_243; obj* x_246; obj* x_248; obj* x_249; obj* x_252; obj* x_253; obj* x_254; obj* x_255; obj* x_256; obj* x_257; 
lean::dec(x_241);
x_243 = lean::cnstr_get(x_238, 2);
lean::inc(x_243);
lean::dec(x_238);
x_246 = l_mjoin___rarg___closed__1;
lean::inc(x_246);
x_248 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_248, 0, x_243);
lean::closure_set(x_248, 1, x_246);
x_249 = lean::cnstr_get(x_82, 2);
lean::inc(x_249);
lean::dec(x_82);
x_252 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_252, 0, x_249);
lean::closure_set(x_252, 1, x_248);
x_253 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_253, 0, x_252);
x_254 = lean::box(0);
if (lean::is_scalar(x_18)) {
 x_255 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_255 = x_18;
}
lean::cnstr_set(x_255, 0, x_254);
lean::cnstr_set(x_255, 1, x_14);
lean::cnstr_set(x_255, 2, x_253);
x_256 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_255);
if (lean::is_scalar(x_13)) {
 x_257 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_257 = x_13;
}
lean::cnstr_set(x_257, 0, x_256);
lean::cnstr_set(x_257, 1, x_190);
return x_257;
}
else
{
obj* x_260; obj* x_261; obj* x_262; obj* x_263; obj* x_264; 
lean::dec(x_14);
lean::dec(x_18);
if (lean::is_scalar(x_241)) {
 x_260 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_260 = x_241;
}
lean::cnstr_set(x_260, 0, x_238);
lean::cnstr_set_scalar(x_260, sizeof(void*)*1, x_240);
x_261 = x_260;
x_262 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_82, x_261);
x_263 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_262);
if (lean::is_scalar(x_13)) {
 x_264 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_264 = x_13;
}
lean::cnstr_set(x_264, 0, x_263);
lean::cnstr_set(x_264, 1, x_190);
return x_264;
}
}
}
else
{
obj* x_268; uint8 x_270; obj* x_271; 
lean::dec(x_20);
lean::dec(x_1);
lean::dec(x_19);
x_268 = lean::cnstr_get(x_85, 0);
lean::inc(x_268);
x_270 = lean::cnstr_get_scalar<uint8>(x_85, sizeof(void*)*1);
if (lean::is_shared(x_85)) {
 lean::dec(x_85);
 x_271 = lean::box(0);
} else {
 lean::cnstr_release(x_85, 0);
 x_271 = x_85;
}
if (x_270 == 0)
{
obj* x_273; obj* x_276; obj* x_278; obj* x_279; obj* x_282; obj* x_283; obj* x_284; obj* x_285; obj* x_286; obj* x_287; 
lean::dec(x_271);
x_273 = lean::cnstr_get(x_268, 2);
lean::inc(x_273);
lean::dec(x_268);
x_276 = l_mjoin___rarg___closed__1;
lean::inc(x_276);
x_278 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_278, 0, x_273);
lean::closure_set(x_278, 1, x_276);
x_279 = lean::cnstr_get(x_82, 2);
lean::inc(x_279);
lean::dec(x_82);
x_282 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_282, 0, x_279);
lean::closure_set(x_282, 1, x_278);
x_283 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_283, 0, x_282);
x_284 = lean::box(0);
if (lean::is_scalar(x_18)) {
 x_285 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_285 = x_18;
}
lean::cnstr_set(x_285, 0, x_284);
lean::cnstr_set(x_285, 1, x_14);
lean::cnstr_set(x_285, 2, x_283);
x_286 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_285);
if (lean::is_scalar(x_13)) {
 x_287 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_287 = x_13;
}
lean::cnstr_set(x_287, 0, x_286);
lean::cnstr_set(x_287, 1, x_86);
return x_287;
}
else
{
obj* x_290; obj* x_291; obj* x_292; obj* x_293; obj* x_294; 
lean::dec(x_14);
lean::dec(x_18);
if (lean::is_scalar(x_271)) {
 x_290 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_290 = x_271;
}
lean::cnstr_set(x_290, 0, x_268);
lean::cnstr_set_scalar(x_290, sizeof(void*)*1, x_270);
x_291 = x_290;
x_292 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_82, x_291);
x_293 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_292);
if (lean::is_scalar(x_13)) {
 x_294 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_294 = x_13;
}
lean::cnstr_set(x_294, 0, x_293);
lean::cnstr_set(x_294, 1, x_86);
return x_294;
}
}
}
}
}
}
else
{
obj* x_297; uint8 x_299; obj* x_300; obj* x_301; obj* x_302; obj* x_303; 
lean::dec(x_1);
lean::dec(x_0);
x_297 = lean::cnstr_get(x_9, 0);
lean::inc(x_297);
x_299 = lean::cnstr_get_scalar<uint8>(x_9, sizeof(void*)*1);
if (lean::is_shared(x_9)) {
 lean::dec(x_9);
 x_300 = lean::box(0);
} else {
 lean::cnstr_release(x_9, 0);
 x_300 = x_9;
}
if (lean::is_scalar(x_300)) {
 x_301 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_301 = x_300;
}
lean::cnstr_set(x_301, 0, x_297);
lean::cnstr_set_scalar(x_301, sizeof(void*)*1, x_299);
x_302 = x_301;
if (lean::is_scalar(x_13)) {
 x_303 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_303 = x_13;
}
lean::cnstr_set(x_303, 0, x_302);
lean::cnstr_set(x_303, 1, x_11);
return x_303;
}
}
else
{
obj* x_305; obj* x_306; obj* x_307; obj* x_311; 
lean::dec(x_0);
x_305 = lean::box(0);
x_306 = l___private_init_lean_parser_combinators_1__many1__aux___main___rarg___closed__1;
x_307 = l_mjoin___rarg___closed__1;
lean::inc(x_305);
lean::inc(x_307);
lean::inc(x_306);
x_311 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_306, x_307, x_305, x_305, x_1, x_2, x_3);
return x_311;
}
}
}
obj* l___private_init_lean_parser_parsec_6__take__while__aux_x_27___main___at___private_init_lean_parser_token_2__whitespace__aux___main___spec__3___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_1);
x_4 = l___private_init_lean_parser_parsec_6__take__while__aux_x_27___main___at___private_init_lean_parser_token_2__whitespace__aux___main___spec__3(x_0, x_3, x_2);
return x_4;
}
}
obj* l___private_init_lean_parser_parsec_6__take__while__aux_x_27___main___at___private_init_lean_parser_token_2__whitespace__aux___main___spec__6___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_1);
x_4 = l___private_init_lean_parser_parsec_6__take__while__aux_x_27___main___at___private_init_lean_parser_token_2__whitespace__aux___main___spec__6(x_0, x_3, x_2);
return x_4;
}
}
obj* l___private_init_lean_parser_token_2__whitespace__aux(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_parser_token_2__whitespace__aux___main(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_lean_parser_whitespace(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_8; obj* x_9; obj* x_11; obj* x_13; obj* x_14; obj* x_16; obj* x_17; obj* x_19; obj* x_20; 
x_3 = lean::string_iterator_remaining(x_1);
x_4 = lean::mk_nat_obj(1u);
x_5 = lean::nat_add(x_3, x_4);
lean::dec(x_4);
lean::dec(x_3);
x_8 = l___private_init_lean_parser_token_2__whitespace__aux___main(x_5, x_0, x_1, x_2);
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
if (lean::is_shared(x_8)) {
 lean::dec(x_8);
 x_13 = lean::box(0);
} else {
 lean::cnstr_release(x_8, 0);
 lean::cnstr_release(x_8, 1);
 x_13 = x_8;
}
x_14 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_14);
x_16 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_14, x_9);
x_17 = l_mjoin___rarg___closed__1;
lean::inc(x_17);
x_19 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_16, x_17);
if (lean::is_scalar(x_13)) {
 x_20 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_20 = x_13;
}
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_11);
return x_20;
}
}
obj* l_lean_parser_as__substring___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_6; obj* x_9; obj* x_10; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
lean::dec(x_0);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
lean::dec(x_3);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_1);
lean::cnstr_set(x_9, 1, x_2);
x_10 = lean::apply_2(x_6, lean::box(0), x_9);
return x_10;
}
}
obj* l_lean_parser_as__substring___rarg___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_6; obj* x_7; 
lean::dec(x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_as__substring___rarg___lambda__1), 3, 2);
lean::closure_set(x_6, 0, x_0);
lean::closure_set(x_6, 1, x_1);
x_7 = lean::apply_4(x_2, lean::box(0), lean::box(0), x_3, x_6);
return x_7;
}
}
obj* l_lean_parser_as__substring___rarg___lambda__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_6; obj* x_7; 
lean::inc(x_1);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_as__substring___rarg___lambda__2), 5, 4);
lean::closure_set(x_6, 0, x_0);
lean::closure_set(x_6, 1, x_4);
lean::closure_set(x_6, 2, x_1);
lean::closure_set(x_6, 3, x_2);
x_7 = lean::apply_4(x_1, lean::box(0), lean::box(0), x_3, x_6);
return x_7;
}
}
obj* l_lean_parser_as__substring___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; obj* x_7; obj* x_10; obj* x_12; obj* x_15; obj* x_16; 
lean::dec(x_2);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
lean::dec(x_1);
x_10 = l_lean_parser_monad__parsec_left__over___rarg___closed__1;
lean::inc(x_10);
x_12 = lean::apply_2(x_7, lean::box(0), x_10);
lean::inc(x_12);
lean::inc(x_5);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_as__substring___rarg___lambda__3), 5, 4);
lean::closure_set(x_15, 0, x_0);
lean::closure_set(x_15, 1, x_5);
lean::closure_set(x_15, 2, x_12);
lean::closure_set(x_15, 3, x_3);
x_16 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_12, x_15);
return x_16;
}
}
obj* l_lean_parser_as__substring(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_as__substring___rarg), 4, 0);
return x_2;
}
}
obj* l___private_init_lean_parser_token_3__update__trailing___main(obj* x_0, obj* x_1) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_2; obj* x_4; obj* x_6; obj* x_8; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_2, 1);
lean::inc(x_6);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_8 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 lean::cnstr_release(x_2, 1);
 x_8 = x_2;
}
if (lean::obj_tag(x_4) == 0)
{
lean::dec(x_8);
lean::dec(x_6);
lean::dec(x_4);
lean::dec(x_0);
return x_1;
}
else
{
obj* x_14; obj* x_16; obj* x_17; obj* x_19; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
lean::dec(x_1);
x_14 = lean::cnstr_get(x_4, 0);
lean::inc(x_14);
if (lean::is_shared(x_4)) {
 lean::dec(x_4);
 x_16 = lean::box(0);
} else {
 lean::cnstr_release(x_4, 0);
 x_16 = x_4;
}
x_17 = lean::cnstr_get(x_14, 0);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_14, 1);
lean::inc(x_19);
lean::dec(x_14);
x_22 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_22, 0, x_17);
lean::cnstr_set(x_22, 1, x_19);
lean::cnstr_set(x_22, 2, x_0);
if (lean::is_scalar(x_16)) {
 x_23 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_23 = x_16;
}
lean::cnstr_set(x_23, 0, x_22);
if (lean::is_scalar(x_8)) {
 x_24 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_24 = x_8;
}
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_6);
x_25 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_25, 0, x_24);
return x_25;
}
}
case 1:
{
obj* x_26; obj* x_28; obj* x_30; obj* x_32; obj* x_34; obj* x_36; obj* x_38; 
x_26 = lean::cnstr_get(x_1, 0);
lean::inc(x_26);
x_28 = lean::cnstr_get(x_26, 0);
lean::inc(x_28);
x_30 = lean::cnstr_get(x_26, 1);
lean::inc(x_30);
x_32 = lean::cnstr_get(x_26, 2);
lean::inc(x_32);
x_34 = lean::cnstr_get(x_26, 3);
lean::inc(x_34);
x_36 = lean::cnstr_get(x_26, 4);
lean::inc(x_36);
if (lean::is_shared(x_26)) {
 lean::dec(x_26);
 x_38 = lean::box(0);
} else {
 lean::cnstr_release(x_26, 0);
 lean::cnstr_release(x_26, 1);
 lean::cnstr_release(x_26, 2);
 lean::cnstr_release(x_26, 3);
 lean::cnstr_release(x_26, 4);
 x_38 = x_26;
}
if (lean::obj_tag(x_28) == 0)
{
lean::dec(x_0);
lean::dec(x_32);
lean::dec(x_34);
lean::dec(x_36);
lean::dec(x_38);
lean::dec(x_28);
lean::dec(x_30);
return x_1;
}
else
{
obj* x_47; obj* x_49; obj* x_50; obj* x_52; obj* x_55; obj* x_56; obj* x_57; obj* x_58; 
lean::dec(x_1);
x_47 = lean::cnstr_get(x_28, 0);
lean::inc(x_47);
if (lean::is_shared(x_28)) {
 lean::dec(x_28);
 x_49 = lean::box(0);
} else {
 lean::cnstr_release(x_28, 0);
 x_49 = x_28;
}
x_50 = lean::cnstr_get(x_47, 0);
lean::inc(x_50);
x_52 = lean::cnstr_get(x_47, 1);
lean::inc(x_52);
lean::dec(x_47);
x_55 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_55, 0, x_50);
lean::cnstr_set(x_55, 1, x_52);
lean::cnstr_set(x_55, 2, x_0);
if (lean::is_scalar(x_49)) {
 x_56 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_56 = x_49;
}
lean::cnstr_set(x_56, 0, x_55);
if (lean::is_scalar(x_38)) {
 x_57 = lean::alloc_cnstr(0, 5, 0);
} else {
 x_57 = x_38;
}
lean::cnstr_set(x_57, 0, x_56);
lean::cnstr_set(x_57, 1, x_30);
lean::cnstr_set(x_57, 2, x_32);
lean::cnstr_set(x_57, 3, x_34);
lean::cnstr_set(x_57, 4, x_36);
x_58 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_58, 0, x_57);
return x_58;
}
}
case 2:
{
obj* x_59; obj* x_61; obj* x_62; obj* x_64; obj* x_66; obj* x_67; obj* x_70; obj* x_71; 
x_59 = lean::cnstr_get(x_1, 0);
lean::inc(x_59);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_61 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 x_61 = x_1;
}
x_62 = lean::cnstr_get(x_59, 0);
lean::inc(x_62);
x_64 = lean::cnstr_get(x_59, 1);
lean::inc(x_64);
x_66 = l___private_init_lean_parser_token_3__update__trailing__lst___main(x_0, x_64);
x_67 = lean::cnstr_get(x_59, 2);
lean::inc(x_67);
lean::dec(x_59);
x_70 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_70, 0, x_62);
lean::cnstr_set(x_70, 1, x_66);
lean::cnstr_set(x_70, 2, x_67);
if (lean::is_scalar(x_61)) {
 x_71 = lean::alloc_cnstr(2, 1, 0);
} else {
 x_71 = x_61;
}
lean::cnstr_set(x_71, 0, x_70);
return x_71;
}
default:
{
lean::dec(x_0);
return x_1;
}
}
}
}
obj* l___private_init_lean_parser_token_3__update__trailing__lst___main(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
lean::dec(x_0);
return x_1;
}
else
{
obj* x_3; obj* x_5; obj* x_7; 
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
if (lean::obj_tag(x_5) == 0)
{
obj* x_8; obj* x_9; 
x_8 = l___private_init_lean_parser_token_3__update__trailing___main(x_0, x_3);
if (lean::is_scalar(x_7)) {
 x_9 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_9 = x_7;
}
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_5);
return x_9;
}
else
{
obj* x_10; obj* x_11; 
x_10 = l___private_init_lean_parser_token_3__update__trailing__lst___main(x_0, x_5);
if (lean::is_scalar(x_7)) {
 x_11 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_11 = x_7;
}
lean::cnstr_set(x_11, 0, x_3);
lean::cnstr_set(x_11, 1, x_10);
return x_11;
}
}
}
}
obj* l___private_init_lean_parser_token_3__update__trailing(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_init_lean_parser_token_3__update__trailing___main(x_0, x_1);
return x_2;
}
}
obj* l___private_init_lean_parser_token_3__update__trailing__lst(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_init_lean_parser_token_3__update__trailing__lst___main(x_0, x_1);
return x_2;
}
}
obj* l_reader__t_lift___at_lean_parser_with__trailing___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; 
lean::dec(x_1);
x_5 = lean::apply_2(x_0, x_2, x_3);
return x_5;
}
}
obj* l_reader__t_lift___at_lean_parser_with__trailing___spec__1(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_lift___at_lean_parser_with__trailing___spec__1___rarg), 4, 0);
return x_2;
}
}
obj* l_reader__t_bind___at_lean_parser_with__trailing___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_6; obj* x_7; obj* x_9; obj* x_11; 
lean::inc(x_2);
x_6 = lean::apply_3(x_0, x_2, x_3, x_4);
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_6, 1);
lean::inc(x_9);
if (lean::is_shared(x_6)) {
 lean::dec(x_6);
 x_11 = lean::box(0);
} else {
 lean::cnstr_release(x_6, 0);
 lean::cnstr_release(x_6, 1);
 x_11 = x_6;
}
if (lean::obj_tag(x_7) == 0)
{
obj* x_12; obj* x_14; obj* x_16; obj* x_19; obj* x_20; obj* x_22; obj* x_25; obj* x_26; 
x_12 = lean::cnstr_get(x_7, 0);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_7, 1);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_7, 2);
lean::inc(x_16);
lean::dec(x_7);
x_19 = lean::apply_4(x_1, x_12, x_2, x_14, x_9);
x_20 = lean::cnstr_get(x_19, 0);
lean::inc(x_20);
x_22 = lean::cnstr_get(x_19, 1);
lean::inc(x_22);
lean::dec(x_19);
x_25 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_20);
if (lean::is_scalar(x_11)) {
 x_26 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_26 = x_11;
}
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_22);
return x_26;
}
else
{
obj* x_29; uint8 x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; 
lean::dec(x_1);
lean::dec(x_2);
x_29 = lean::cnstr_get(x_7, 0);
lean::inc(x_29);
x_31 = lean::cnstr_get_scalar<uint8>(x_7, sizeof(void*)*1);
if (lean::is_shared(x_7)) {
 lean::dec(x_7);
 x_32 = lean::box(0);
} else {
 lean::cnstr_release(x_7, 0);
 x_32 = x_7;
}
if (lean::is_scalar(x_32)) {
 x_33 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_33 = x_32;
}
lean::cnstr_set(x_33, 0, x_29);
lean::cnstr_set_scalar(x_33, sizeof(void*)*1, x_31);
x_34 = x_33;
if (lean::is_scalar(x_11)) {
 x_35 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_35 = x_11;
}
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_9);
return x_35;
}
}
}
obj* l_reader__t_bind___at_lean_parser_with__trailing___spec__2(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_bind___at_lean_parser_with__trailing___spec__2___rarg), 5, 0);
return x_4;
}
}
obj* l_lean_parser_with__trailing___rarg___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_5; obj* x_6; 
x_2 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_2);
lean::inc(x_0);
x_5 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_5, 0, x_0);
lean::cnstr_set(x_5, 1, x_0);
lean::cnstr_set(x_5, 2, x_2);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_1);
return x_6;
}
}
obj* l_lean_parser_with__trailing___rarg___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_7; obj* x_9; 
x_4 = l_lean_parser_whitespace(x_1, x_2, x_3);
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
obj* x_10; obj* x_12; obj* x_14; obj* x_16; obj* x_17; obj* x_19; obj* x_20; obj* x_21; 
x_10 = lean::cnstr_get(x_5, 1);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_5, 2);
lean::inc(x_12);
if (lean::is_shared(x_5)) {
 lean::dec(x_5);
 x_14 = lean::box(0);
} else {
 lean::cnstr_release(x_5, 0);
 lean::cnstr_release(x_5, 1);
 lean::cnstr_release(x_5, 2);
 x_14 = x_5;
}
lean::inc(x_10);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_0);
lean::cnstr_set(x_16, 1, x_10);
x_17 = l_lean_parser_finish__comment__block___closed__2;
lean::inc(x_17);
if (lean::is_scalar(x_14)) {
 x_19 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_19 = x_14;
}
lean::cnstr_set(x_19, 0, x_16);
lean::cnstr_set(x_19, 1, x_10);
lean::cnstr_set(x_19, 2, x_17);
x_20 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_12, x_19);
if (lean::is_scalar(x_9)) {
 x_21 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_21 = x_9;
}
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_7);
return x_21;
}
else
{
obj* x_23; uint8 x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
lean::dec(x_0);
x_23 = lean::cnstr_get(x_5, 0);
lean::inc(x_23);
x_25 = lean::cnstr_get_scalar<uint8>(x_5, sizeof(void*)*1);
if (lean::is_shared(x_5)) {
 lean::dec(x_5);
 x_26 = lean::box(0);
} else {
 lean::cnstr_release(x_5, 0);
 x_26 = x_5;
}
if (lean::is_scalar(x_26)) {
 x_27 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_27 = x_26;
}
lean::cnstr_set(x_27, 0, x_23);
lean::cnstr_set_scalar(x_27, sizeof(void*)*1, x_25);
x_28 = x_27;
if (lean::is_scalar(x_9)) {
 x_29 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_29 = x_9;
}
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_7);
return x_29;
}
}
}
obj* l_lean_parser_with__trailing___rarg___lambda__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_6; obj* x_9; obj* x_10; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
lean::dec(x_0);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
lean::dec(x_3);
x_9 = l___private_init_lean_parser_token_3__update__trailing___main(x_2, x_1);
x_10 = lean::apply_2(x_6, lean::box(0), x_9);
return x_10;
}
}
obj* _init_l_lean_parser_with__trailing___rarg___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_with__trailing___rarg___lambda__1), 2, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_lift___at_lean_parser_with__trailing___spec__1___rarg), 4, 1);
lean::closure_set(x_1, 0, x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_with__trailing___rarg___lambda__2), 4, 0);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_bind___at_lean_parser_with__trailing___spec__2___rarg), 5, 2);
lean::closure_set(x_3, 0, x_1);
lean::closure_set(x_3, 1, x_2);
return x_3;
}
}
obj* l_lean_parser_with__trailing___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_11; 
lean::dec(x_1);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
x_7 = l_lean_parser_with__trailing___rarg___closed__1;
lean::inc(x_7);
x_9 = lean::apply_2(x_2, lean::box(0), x_7);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_with__trailing___rarg___lambda__3), 3, 2);
lean::closure_set(x_10, 0, x_0);
lean::closure_set(x_10, 1, x_3);
x_11 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_9, x_10);
return x_11;
}
}
obj* l_lean_parser_with__trailing(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_with__trailing___rarg), 4, 0);
return x_2;
}
}
obj* l_lean_parser_mk__raw__res(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; obj* x_7; obj* x_8; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
lean::inc(x_1);
lean::inc(x_0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
lean::inc(x_0);
lean::inc(x_0);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_0);
lean::cnstr_set(x_7, 1, x_0);
x_8 = lean::string_iterator_offset(x_0);
lean::dec(x_0);
lean::inc(x_1);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_1);
lean::cnstr_set(x_11, 1, x_1);
x_12 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_12, 0, x_7);
lean::cnstr_set(x_12, 1, x_8);
lean::cnstr_set(x_12, 2, x_11);
x_13 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_13, 0, x_12);
x_14 = l_lean_parser_substring_to__string(x_4);
x_15 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_15, 0, x_13);
lean::cnstr_set(x_15, 1, x_14);
x_16 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_16, 0, x_15);
return x_16;
}
}
obj* l_lean_parser_raw___rarg___lambda__1(obj* x_0, uint8 x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_lean_parser_mk__raw__res(x_0, x_5);
if (x_1 == 0)
{
obj* x_9; obj* x_12; obj* x_15; 
lean::dec(x_4);
lean::dec(x_3);
x_9 = lean::cnstr_get(x_2, 0);
lean::inc(x_9);
lean::dec(x_2);
x_12 = lean::cnstr_get(x_9, 1);
lean::inc(x_12);
lean::dec(x_9);
x_15 = lean::apply_2(x_12, lean::box(0), x_6);
return x_15;
}
else
{
obj* x_16; 
x_16 = l_lean_parser_with__trailing___rarg(x_2, x_3, x_4, x_6);
return x_16;
}
}
}
obj* l_lean_parser_raw___rarg___lambda__2(obj* x_0, uint8 x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_9; obj* x_10; obj* x_11; 
lean::dec(x_7);
x_9 = lean::box(x_1);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_raw___rarg___lambda__1___boxed), 6, 5);
lean::closure_set(x_10, 0, x_0);
lean::closure_set(x_10, 1, x_9);
lean::closure_set(x_10, 2, x_2);
lean::closure_set(x_10, 3, x_3);
lean::closure_set(x_10, 4, x_4);
x_11 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_6, x_10);
return x_11;
}
}
obj* l_lean_parser_raw___rarg___lambda__3(uint8 x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; obj* x_10; obj* x_11; 
x_8 = lean::box(x_0);
lean::inc(x_4);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_raw___rarg___lambda__2___boxed), 8, 7);
lean::closure_set(x_10, 0, x_7);
lean::closure_set(x_10, 1, x_8);
lean::closure_set(x_10, 2, x_1);
lean::closure_set(x_10, 3, x_2);
lean::closure_set(x_10, 4, x_3);
lean::closure_set(x_10, 5, x_4);
lean::closure_set(x_10, 6, x_5);
x_11 = lean::apply_4(x_4, lean::box(0), lean::box(0), x_6, x_10);
return x_11;
}
}
obj* l_lean_parser_raw___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, uint8 x_5) {
_start:
{
obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_14; obj* x_17; obj* x_18; 
lean::dec(x_3);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_1, 0);
lean::inc(x_9);
x_11 = l_lean_parser_monad__parsec_left__over___rarg___closed__1;
lean::inc(x_11);
x_13 = lean::apply_2(x_9, lean::box(0), x_11);
x_14 = lean::box(x_5);
lean::inc(x_13);
lean::inc(x_7);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_raw___rarg___lambda__3___boxed), 8, 7);
lean::closure_set(x_17, 0, x_14);
lean::closure_set(x_17, 1, x_0);
lean::closure_set(x_17, 2, x_1);
lean::closure_set(x_17, 3, x_2);
lean::closure_set(x_17, 4, x_7);
lean::closure_set(x_17, 5, x_13);
lean::closure_set(x_17, 6, x_4);
x_18 = lean::apply_4(x_7, lean::box(0), lean::box(0), x_13, x_17);
return x_18;
}
}
obj* l_lean_parser_raw(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_raw___rarg___boxed), 6, 0);
return x_2;
}
}
obj* l_lean_parser_raw___rarg___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; obj* x_7; 
x_6 = lean::unbox(x_1);
x_7 = l_lean_parser_raw___rarg___lambda__1(x_0, x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
obj* l_lean_parser_raw___rarg___lambda__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
uint8 x_8; obj* x_9; 
x_8 = lean::unbox(x_1);
x_9 = l_lean_parser_raw___rarg___lambda__2(x_0, x_8, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
obj* l_lean_parser_raw___rarg___lambda__3___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
uint8 x_8; obj* x_9; 
x_8 = lean::unbox(x_0);
x_9 = l_lean_parser_raw___rarg___lambda__3(x_8, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
obj* l_lean_parser_raw___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; obj* x_7; 
x_6 = lean::unbox(x_5);
x_7 = l_lean_parser_raw___rarg(x_0, x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
obj* l_lean_parser_raw_tokens(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, uint8 x_6) {
_start:
{
obj* x_13; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_13 = lean::box(0);
return x_13;
}
}
obj* l_lean_parser_raw_tokens___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
uint8 x_7; obj* x_8; 
x_7 = lean::unbox(x_6);
x_8 = l_lean_parser_raw_tokens(x_0, x_1, x_2, x_3, x_4, x_5, x_7);
return x_8;
}
}
obj* l_lean_parser_raw_view___rarg___lambda__1(obj* x_0) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_1; obj* x_4; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
x_4 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_4, 0, x_1);
return x_4;
}
case 1:
{
obj* x_6; 
lean::dec(x_0);
x_6 = lean::box(0);
return x_6;
}
case 2:
{
obj* x_8; 
lean::dec(x_0);
x_8 = lean::box(0);
return x_8;
}
default:
{
obj* x_10; 
lean::dec(x_0);
x_10 = lean::box(0);
return x_10;
}
}
}
}
obj* l_lean_parser_raw_view___rarg___lambda__2(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_lean_parser_raw_view___rarg___lambda__3___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_raw_view___rarg___lambda__2), 1, 0);
return x_0;
}
}
obj* l_lean_parser_raw_view___rarg___lambda__3(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_4; obj* x_5; 
x_1 = l_lean_parser_raw_view___rarg___lambda__3___closed__1;
lean::inc(x_1);
x_3 = l_option_map___rarg(x_1, x_0);
x_4 = lean::box(3);
x_5 = l_option_get__or__else___main___rarg(x_3, x_4);
return x_5;
}
}
obj* _init_l_lean_parser_raw_view___rarg___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_raw_view___rarg___lambda__1), 1, 0);
return x_0;
}
}
obj* _init_l_lean_parser_raw_view___rarg___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_raw_view___rarg___lambda__3), 1, 0);
return x_0;
}
}
obj* l_lean_parser_raw_view___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, uint8 x_5) {
_start:
{
obj* x_11; obj* x_12; obj* x_15; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_11 = l_lean_parser_raw_view___rarg___closed__1;
x_12 = l_lean_parser_raw_view___rarg___closed__2;
lean::inc(x_12);
lean::inc(x_11);
x_15 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_15, 0, x_11);
lean::cnstr_set(x_15, 1, x_12);
return x_15;
}
}
obj* l_lean_parser_raw_view(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_raw_view___rarg___boxed), 6, 0);
return x_2;
}
}
obj* l_lean_parser_raw_view___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; obj* x_7; 
x_6 = lean::unbox(x_5);
x_7 = l_lean_parser_raw_view___rarg(x_0, x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
obj* l_lean_parser_raw__str_lean_parser_has__tokens(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, uint8 x_5) {
_start:
{
obj* x_11; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_11 = lean::box(0);
return x_11;
}
}
obj* l_lean_parser_raw__str_lean_parser_has__tokens___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; obj* x_7; 
x_6 = lean::unbox(x_5);
x_7 = l_lean_parser_raw__str_lean_parser_has__tokens(x_0, x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
obj* l_lean_parser_raw__str_lean_parser_has__view___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, uint8 x_4) {
_start:
{
obj* x_6; obj* x_7; obj* x_10; obj* x_11; 
lean::inc(x_3);
x_6 = l_string_quote(x_3);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_7, 0, x_6);
lean::inc(x_1);
lean::inc(x_0);
x_10 = l_lean_parser_monad__parsec_str__core___rarg(x_0, x_1, x_3, x_7);
x_11 = l_lean_parser_raw_view___rarg(x_0, x_1, x_2, lean::box(0), x_10, x_4);
return x_11;
}
}
obj* l_lean_parser_raw__str_lean_parser_has__view(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_raw__str_lean_parser_has__view___rarg___boxed), 5, 0);
return x_2;
}
}
obj* l_lean_parser_raw__str_lean_parser_has__view___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; obj* x_6; 
x_5 = lean::unbox(x_4);
x_6 = l_lean_parser_raw__str_lean_parser_has__view___rarg(x_0, x_1, x_2, x_3, x_5);
return x_6;
}
}
obj* l_lean_parser_raw__str___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, uint8 x_4) {
_start:
{
obj* x_6; obj* x_7; obj* x_10; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_18; obj* x_21; obj* x_22; 
lean::inc(x_3);
x_6 = l_string_quote(x_3);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_7, 0, x_6);
lean::inc(x_1);
lean::inc(x_0);
x_10 = l_lean_parser_monad__parsec_str__core___rarg(x_0, x_1, x_3, x_7);
x_11 = lean::cnstr_get(x_0, 1);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_1, 0);
lean::inc(x_13);
x_15 = l_lean_parser_monad__parsec_left__over___rarg___closed__1;
lean::inc(x_15);
x_17 = lean::apply_2(x_13, lean::box(0), x_15);
x_18 = lean::box(x_4);
lean::inc(x_17);
lean::inc(x_11);
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_raw___rarg___lambda__3___boxed), 8, 7);
lean::closure_set(x_21, 0, x_18);
lean::closure_set(x_21, 1, x_0);
lean::closure_set(x_21, 2, x_1);
lean::closure_set(x_21, 3, x_2);
lean::closure_set(x_21, 4, x_11);
lean::closure_set(x_21, 5, x_17);
lean::closure_set(x_21, 6, x_10);
x_22 = lean::apply_4(x_11, lean::box(0), lean::box(0), x_17, x_21);
return x_22;
}
}
obj* l_lean_parser_raw__str(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_raw__str___rarg___boxed), 5, 0);
return x_2;
}
}
obj* l_lean_parser_raw__str___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; obj* x_6; 
x_5 = lean::unbox(x_4);
x_6 = l_lean_parser_raw__str___rarg(x_0, x_1, x_2, x_3, x_5);
return x_6;
}
}
obj* l_lean_parser_raw__str_view__default___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, uint8 x_4) {
_start:
{
obj* x_9; 
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_9 = lean::box(0);
return x_9;
}
}
obj* l_lean_parser_raw__str_view__default(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_raw__str_view__default___rarg___boxed), 5, 0);
return x_2;
}
}
obj* l_lean_parser_raw__str_view__default___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; obj* x_6; 
x_5 = lean::unbox(x_4);
x_6 = l_lean_parser_raw__str_view__default___rarg(x_0, x_1, x_2, x_3, x_5);
return x_6;
}
}
obj* _init_l_lean_parser_detail__ident__part__escaped() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("detail_ident_part_escaped");
x_6 = lean_name_mk_string(x_4, x_5);
return x_6;
}
}
obj* _init_l_lean_parser_detail__ident__part__escaped_has__view_x_27___lambda__1___closed__1() {
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
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_7; obj* x_10; 
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
lean::dec(x_1);
x_10 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_10, 0, x_7);
x_5 = x_10;
goto lbl_6;
}
case 1:
{
obj* x_12; 
lean::dec(x_1);
x_12 = lean::box(0);
x_5 = x_12;
goto lbl_6;
}
case 2:
{
obj* x_14; 
lean::dec(x_1);
x_14 = lean::box(0);
x_5 = x_14;
goto lbl_6;
}
default:
{
obj* x_16; 
lean::dec(x_1);
x_16 = lean::box(0);
x_5 = x_16;
goto lbl_6;
}
}
lbl_6:
{
obj* x_17; obj* x_18; obj* x_20; obj* x_21; 
if (lean::obj_tag(x_0) == 0)
{
obj* x_23; 
x_23 = lean::box(3);
x_20 = x_0;
x_21 = x_23;
goto lbl_22;
}
else
{
obj* x_24; obj* x_26; 
x_24 = lean::cnstr_get(x_0, 0);
lean::inc(x_24);
x_26 = lean::cnstr_get(x_0, 1);
lean::inc(x_26);
lean::dec(x_0);
x_20 = x_26;
x_21 = x_24;
goto lbl_22;
}
lbl_19:
{
switch (lean::obj_tag(x_18)) {
case 0:
{
obj* x_29; obj* x_32; obj* x_33; 
x_29 = lean::cnstr_get(x_18, 0);
lean::inc(x_29);
lean::dec(x_18);
x_32 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_32, 0, x_29);
x_33 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_33, 0, x_5);
lean::cnstr_set(x_33, 1, x_17);
lean::cnstr_set(x_33, 2, x_32);
return x_33;
}
case 1:
{
obj* x_35; obj* x_36; 
lean::dec(x_18);
x_35 = lean::box(0);
x_36 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_36, 0, x_5);
lean::cnstr_set(x_36, 1, x_17);
lean::cnstr_set(x_36, 2, x_35);
return x_36;
}
case 2:
{
obj* x_38; obj* x_39; 
lean::dec(x_18);
x_38 = lean::box(0);
x_39 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_39, 0, x_5);
lean::cnstr_set(x_39, 1, x_17);
lean::cnstr_set(x_39, 2, x_38);
return x_39;
}
default:
{
obj* x_41; obj* x_42; 
lean::dec(x_18);
x_41 = lean::box(0);
x_42 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_42, 0, x_5);
lean::cnstr_set(x_42, 1, x_17);
lean::cnstr_set(x_42, 2, x_41);
return x_42;
}
}
}
lbl_22:
{
switch (lean::obj_tag(x_21)) {
case 0:
{
obj* x_43; obj* x_46; 
x_43 = lean::cnstr_get(x_21, 0);
lean::inc(x_43);
lean::dec(x_21);
x_46 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_46, 0, x_43);
if (lean::obj_tag(x_20) == 0)
{
obj* x_48; obj* x_49; 
lean::dec(x_20);
x_48 = lean::box(0);
x_49 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_49, 0, x_5);
lean::cnstr_set(x_49, 1, x_46);
lean::cnstr_set(x_49, 2, x_48);
return x_49;
}
else
{
obj* x_50; 
x_50 = lean::cnstr_get(x_20, 0);
lean::inc(x_50);
lean::dec(x_20);
x_17 = x_46;
x_18 = x_50;
goto lbl_19;
}
}
case 1:
{
obj* x_54; 
lean::dec(x_21);
x_54 = lean::box(0);
if (lean::obj_tag(x_20) == 0)
{
obj* x_57; 
lean::dec(x_20);
lean::inc(x_54);
x_57 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_57, 0, x_5);
lean::cnstr_set(x_57, 1, x_54);
lean::cnstr_set(x_57, 2, x_54);
return x_57;
}
else
{
obj* x_58; 
x_58 = lean::cnstr_get(x_20, 0);
lean::inc(x_58);
lean::dec(x_20);
x_17 = x_54;
x_18 = x_58;
goto lbl_19;
}
}
case 2:
{
obj* x_62; 
lean::dec(x_21);
x_62 = lean::box(0);
if (lean::obj_tag(x_20) == 0)
{
obj* x_65; 
lean::dec(x_20);
lean::inc(x_62);
x_65 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_65, 0, x_5);
lean::cnstr_set(x_65, 1, x_62);
lean::cnstr_set(x_65, 2, x_62);
return x_65;
}
else
{
obj* x_66; 
x_66 = lean::cnstr_get(x_20, 0);
lean::inc(x_66);
lean::dec(x_20);
x_17 = x_62;
x_18 = x_66;
goto lbl_19;
}
}
default:
{
obj* x_70; 
lean::dec(x_21);
x_70 = lean::box(0);
if (lean::obj_tag(x_20) == 0)
{
obj* x_73; 
lean::dec(x_20);
lean::inc(x_70);
x_73 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_73, 0, x_5);
lean::cnstr_set(x_73, 1, x_70);
lean::cnstr_set(x_73, 2, x_70);
return x_73;
}
else
{
obj* x_74; 
x_74 = lean::cnstr_get(x_20, 0);
lean::inc(x_74);
lean::dec(x_20);
x_17 = x_70;
x_18 = x_74;
goto lbl_19;
}
}
}
}
}
}
}
}
obj* l_lean_parser_detail__ident__part__escaped_has__view_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_4 = l_lean_parser_syntax_as__node___main(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; 
lean::dec(x_4);
x_6 = l_lean_parser_detail__ident__part__escaped_has__view_x_27___lambda__1___closed__1;
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
switch (lean::obj_tag(x_2)) {
case 0:
{
obj* x_22; obj* x_25; 
x_22 = lean::cnstr_get(x_2, 0);
lean::inc(x_22);
lean::dec(x_2);
x_25 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_25, 0, x_22);
x_20 = x_25;
goto lbl_21;
}
case 1:
{
obj* x_27; 
lean::dec(x_2);
x_27 = lean::box(0);
x_20 = x_27;
goto lbl_21;
}
case 2:
{
obj* x_29; 
lean::dec(x_2);
x_29 = lean::box(0);
x_20 = x_29;
goto lbl_21;
}
default:
{
obj* x_31; 
lean::dec(x_2);
x_31 = lean::box(0);
x_20 = x_31;
goto lbl_21;
}
}
lbl_21:
{
obj* x_32; obj* x_33; obj* x_35; obj* x_36; 
if (lean::obj_tag(x_1) == 0)
{
obj* x_38; 
x_38 = lean::box(3);
x_35 = x_1;
x_36 = x_38;
goto lbl_37;
}
else
{
obj* x_39; obj* x_41; 
x_39 = lean::cnstr_get(x_1, 0);
lean::inc(x_39);
x_41 = lean::cnstr_get(x_1, 1);
lean::inc(x_41);
lean::dec(x_1);
x_35 = x_41;
x_36 = x_39;
goto lbl_37;
}
lbl_34:
{
switch (lean::obj_tag(x_33)) {
case 0:
{
obj* x_44; obj* x_47; obj* x_48; 
x_44 = lean::cnstr_get(x_33, 0);
lean::inc(x_44);
lean::dec(x_33);
x_47 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_47, 0, x_44);
x_48 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_48, 0, x_20);
lean::cnstr_set(x_48, 1, x_32);
lean::cnstr_set(x_48, 2, x_47);
return x_48;
}
case 1:
{
obj* x_50; obj* x_51; 
lean::dec(x_33);
x_50 = lean::box(0);
x_51 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_51, 0, x_20);
lean::cnstr_set(x_51, 1, x_32);
lean::cnstr_set(x_51, 2, x_50);
return x_51;
}
case 2:
{
obj* x_53; obj* x_54; 
lean::dec(x_33);
x_53 = lean::box(0);
x_54 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_54, 0, x_20);
lean::cnstr_set(x_54, 1, x_32);
lean::cnstr_set(x_54, 2, x_53);
return x_54;
}
default:
{
obj* x_56; obj* x_57; 
lean::dec(x_33);
x_56 = lean::box(0);
x_57 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_57, 0, x_20);
lean::cnstr_set(x_57, 1, x_32);
lean::cnstr_set(x_57, 2, x_56);
return x_57;
}
}
}
lbl_37:
{
switch (lean::obj_tag(x_36)) {
case 0:
{
obj* x_58; obj* x_61; 
x_58 = lean::cnstr_get(x_36, 0);
lean::inc(x_58);
lean::dec(x_36);
x_61 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_61, 0, x_58);
if (lean::obj_tag(x_35) == 0)
{
obj* x_63; obj* x_64; 
lean::dec(x_35);
x_63 = lean::box(0);
x_64 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_64, 0, x_20);
lean::cnstr_set(x_64, 1, x_61);
lean::cnstr_set(x_64, 2, x_63);
return x_64;
}
else
{
obj* x_65; 
x_65 = lean::cnstr_get(x_35, 0);
lean::inc(x_65);
lean::dec(x_35);
x_32 = x_61;
x_33 = x_65;
goto lbl_34;
}
}
case 1:
{
obj* x_69; 
lean::dec(x_36);
x_69 = lean::box(0);
if (lean::obj_tag(x_35) == 0)
{
obj* x_72; 
lean::dec(x_35);
lean::inc(x_69);
x_72 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_72, 0, x_20);
lean::cnstr_set(x_72, 1, x_69);
lean::cnstr_set(x_72, 2, x_69);
return x_72;
}
else
{
obj* x_73; 
x_73 = lean::cnstr_get(x_35, 0);
lean::inc(x_73);
lean::dec(x_35);
x_32 = x_69;
x_33 = x_73;
goto lbl_34;
}
}
case 2:
{
obj* x_77; 
lean::dec(x_36);
x_77 = lean::box(0);
if (lean::obj_tag(x_35) == 0)
{
obj* x_80; 
lean::dec(x_35);
lean::inc(x_77);
x_80 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_80, 0, x_20);
lean::cnstr_set(x_80, 1, x_77);
lean::cnstr_set(x_80, 2, x_77);
return x_80;
}
else
{
obj* x_81; 
x_81 = lean::cnstr_get(x_35, 0);
lean::inc(x_81);
lean::dec(x_35);
x_32 = x_77;
x_33 = x_81;
goto lbl_34;
}
}
default:
{
obj* x_85; 
lean::dec(x_36);
x_85 = lean::box(0);
if (lean::obj_tag(x_35) == 0)
{
obj* x_88; 
lean::dec(x_35);
lean::inc(x_85);
x_88 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_88, 0, x_20);
lean::cnstr_set(x_88, 1, x_85);
lean::cnstr_set(x_88, 2, x_85);
return x_88;
}
else
{
obj* x_89; 
x_89 = lean::cnstr_get(x_35, 0);
lean::inc(x_89);
lean::dec(x_35);
x_32 = x_85;
x_33 = x_89;
goto lbl_34;
}
}
}
}
}
}
}
}
obj* l_lean_parser_detail__ident__part__escaped_has__view_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_5; obj* x_8; obj* x_10; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_27; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 2);
lean::inc(x_5);
lean::dec(x_0);
x_8 = l_lean_parser_raw_view___rarg___lambda__3___closed__1;
lean::inc(x_8);
x_10 = l_option_map___rarg(x_8, x_1);
x_11 = lean::box(3);
lean::inc(x_11);
x_13 = l_option_get__or__else___main___rarg(x_10, x_11);
lean::inc(x_8);
x_15 = l_option_map___rarg(x_8, x_3);
lean::inc(x_11);
x_17 = l_option_get__or__else___main___rarg(x_15, x_11);
lean::inc(x_8);
x_19 = l_option_map___rarg(x_8, x_5);
x_20 = l_option_get__or__else___main___rarg(x_19, x_11);
x_21 = lean::box(0);
x_22 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_22, 0, x_20);
lean::cnstr_set(x_22, 1, x_21);
x_23 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_23, 0, x_17);
lean::cnstr_set(x_23, 1, x_22);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_13);
lean::cnstr_set(x_24, 1, x_23);
x_25 = l_lean_parser_detail__ident__part__escaped;
lean::inc(x_25);
x_27 = l_lean_parser_syntax_mk__node(x_25, x_24);
return x_27;
}
}
obj* _init_l_lean_parser_detail__ident__part__escaped_has__view_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_detail__ident__part__escaped_has__view_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_detail__ident__part__escaped_has__view_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_lean_parser_detail__ident__part__escaped_has__view() {
_start:
{
obj* x_0; 
x_0 = l_lean_parser_detail__ident__part__escaped_has__view_x_27;
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_lean_parser_detail__ident__part() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("detail_ident_part");
x_6 = lean_name_mk_string(x_4, x_5);
return x_6;
}
}
obj* _init_l_lean_parser_detail__ident__part_has__view_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(0);
x_1 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_lean_parser_detail__ident__part_has__view_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; 
x_3 = lean::box(3);
x_4 = lean::mk_nat_obj(0u);
x_0 = x_3;
x_1 = x_4;
goto lbl_2;
lbl_2:
{
obj* x_5; uint8 x_6; 
x_5 = lean::mk_nat_obj(0u);
x_6 = lean::nat_dec_eq(x_1, x_5);
lean::dec(x_5);
lean::dec(x_1);
if (x_6 == 0)
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_9; obj* x_12; obj* x_13; 
x_9 = lean::cnstr_get(x_0, 0);
lean::inc(x_9);
lean::dec(x_0);
x_12 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_12, 0, x_9);
x_13 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_13, 0, x_12);
return x_13;
}
case 1:
{
obj* x_15; 
lean::dec(x_0);
x_15 = l_lean_parser_detail__ident__part_has__view_x_27___lambda__1___closed__1;
lean::inc(x_15);
return x_15;
}
case 2:
{
obj* x_18; 
lean::dec(x_0);
x_18 = l_lean_parser_detail__ident__part_has__view_x_27___lambda__1___closed__1;
lean::inc(x_18);
return x_18;
}
default:
{
obj* x_21; 
lean::dec(x_0);
x_21 = l_lean_parser_detail__ident__part_has__view_x_27___lambda__1___closed__1;
lean::inc(x_21);
return x_21;
}
}
}
else
{
obj* x_23; obj* x_24; obj* x_26; obj* x_27; 
x_23 = l_lean_parser_detail__ident__part__escaped_has__view;
x_24 = lean::cnstr_get(x_23, 0);
lean::inc(x_24);
x_26 = lean::apply_1(x_24, x_0);
x_27 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_27, 0, x_26);
return x_27;
}
}
}
}
obj* _init_l_lean_parser_detail__ident__part_has__view_x_27___lambda__1___closed__3() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("detail_ident_part");
x_6 = lean_name_mk_string(x_4, x_5);
return x_6;
}
}
obj* l_lean_parser_detail__ident__part_has__view_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_4 = l_lean_parser_syntax_as__node___main(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; 
lean::dec(x_4);
x_6 = l_lean_parser_detail__ident__part_has__view_x_27___lambda__1___closed__2;
lean::inc(x_6);
return x_6;
}
else
{
obj* x_8; obj* x_11; obj* x_13; obj* x_16; uint8 x_17; 
x_8 = lean::cnstr_get(x_4, 0);
lean::inc(x_8);
lean::dec(x_4);
x_11 = lean::cnstr_get(x_8, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_8, 1);
lean::inc(x_13);
lean::dec(x_8);
x_16 = l_lean_parser_detail__ident__part_has__view_x_27___lambda__1___closed__3;
x_17 = lean_name_dec_eq(x_11, x_16);
lean::dec(x_11);
if (x_17 == 0)
{
obj* x_20; 
lean::dec(x_13);
x_20 = l_lean_parser_detail__ident__part_has__view_x_27___lambda__1___closed__2;
lean::inc(x_20);
return x_20;
}
else
{
if (lean::obj_tag(x_13) == 0)
{
obj* x_23; 
lean::dec(x_13);
x_23 = l_lean_parser_detail__ident__part_has__view_x_27___lambda__1___closed__2;
lean::inc(x_23);
return x_23;
}
else
{
obj* x_25; obj* x_27; 
x_25 = lean::cnstr_get(x_13, 0);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_13, 1);
lean::inc(x_27);
lean::dec(x_13);
if (lean::obj_tag(x_27) == 0)
{
obj* x_31; 
lean::dec(x_27);
x_31 = l_lean_parser_syntax_as__node___main(x_25);
if (lean::obj_tag(x_31) == 0)
{
obj* x_33; 
lean::dec(x_31);
x_33 = l_lean_parser_detail__ident__part_has__view_x_27___lambda__1___closed__2;
lean::inc(x_33);
return x_33;
}
else
{
obj* x_35; obj* x_38; obj* x_40; 
x_35 = lean::cnstr_get(x_31, 0);
lean::inc(x_35);
lean::dec(x_31);
x_38 = lean::cnstr_get(x_35, 0);
lean::inc(x_38);
x_40 = lean::cnstr_get(x_35, 1);
lean::inc(x_40);
lean::dec(x_35);
switch (lean::obj_tag(x_38)) {
case 0:
{
obj* x_45; 
lean::dec(x_38);
lean::dec(x_40);
x_45 = l_lean_parser_detail__ident__part_has__view_x_27___lambda__1___closed__2;
lean::inc(x_45);
return x_45;
}
case 1:
{
obj* x_49; 
lean::dec(x_38);
lean::dec(x_40);
x_49 = l_lean_parser_detail__ident__part_has__view_x_27___lambda__1___closed__2;
lean::inc(x_49);
return x_49;
}
default:
{
obj* x_51; obj* x_53; obj* x_56; uint8 x_57; 
x_51 = lean::cnstr_get(x_38, 0);
lean::inc(x_51);
x_53 = lean::cnstr_get(x_38, 1);
lean::inc(x_53);
lean::dec(x_38);
x_56 = lean::box(0);
x_57 = lean_name_dec_eq(x_51, x_56);
lean::dec(x_56);
lean::dec(x_51);
if (x_57 == 0)
{
obj* x_62; 
lean::dec(x_40);
lean::dec(x_53);
x_62 = l_lean_parser_detail__ident__part_has__view_x_27___lambda__1___closed__2;
lean::inc(x_62);
return x_62;
}
else
{
if (lean::obj_tag(x_40) == 0)
{
obj* x_66; 
lean::dec(x_40);
lean::dec(x_53);
x_66 = l_lean_parser_detail__ident__part_has__view_x_27___lambda__1___closed__2;
lean::inc(x_66);
return x_66;
}
else
{
obj* x_68; obj* x_70; 
x_68 = lean::cnstr_get(x_40, 0);
lean::inc(x_68);
x_70 = lean::cnstr_get(x_40, 1);
lean::inc(x_70);
lean::dec(x_40);
if (lean::obj_tag(x_70) == 0)
{
lean::dec(x_70);
x_1 = x_68;
x_2 = x_53;
goto lbl_3;
}
else
{
obj* x_77; 
lean::dec(x_53);
lean::dec(x_68);
lean::dec(x_70);
x_77 = l_lean_parser_detail__ident__part_has__view_x_27___lambda__1___closed__2;
lean::inc(x_77);
return x_77;
}
}
}
}
}
}
}
else
{
obj* x_81; 
lean::dec(x_25);
lean::dec(x_27);
x_81 = l_lean_parser_detail__ident__part_has__view_x_27___lambda__1___closed__2;
lean::inc(x_81);
return x_81;
}
}
}
}
lbl_3:
{
obj* x_83; uint8 x_84; 
x_83 = lean::mk_nat_obj(0u);
x_84 = lean::nat_dec_eq(x_2, x_83);
lean::dec(x_83);
lean::dec(x_2);
if (x_84 == 0)
{
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_87; obj* x_90; obj* x_91; 
x_87 = lean::cnstr_get(x_1, 0);
lean::inc(x_87);
lean::dec(x_1);
x_90 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_90, 0, x_87);
x_91 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_91, 0, x_90);
return x_91;
}
case 1:
{
obj* x_93; 
lean::dec(x_1);
x_93 = l_lean_parser_detail__ident__part_has__view_x_27___lambda__1___closed__1;
lean::inc(x_93);
return x_93;
}
case 2:
{
obj* x_96; 
lean::dec(x_1);
x_96 = l_lean_parser_detail__ident__part_has__view_x_27___lambda__1___closed__1;
lean::inc(x_96);
return x_96;
}
default:
{
obj* x_99; 
lean::dec(x_1);
x_99 = l_lean_parser_detail__ident__part_has__view_x_27___lambda__1___closed__1;
lean::inc(x_99);
return x_99;
}
}
}
else
{
obj* x_101; obj* x_102; obj* x_104; obj* x_105; 
x_101 = l_lean_parser_detail__ident__part__escaped_has__view;
x_102 = lean::cnstr_get(x_101, 0);
lean::inc(x_102);
x_104 = lean::apply_1(x_102, x_1);
x_105 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_105, 0, x_104);
return x_105;
}
}
}
}
obj* _init_l_lean_parser_detail__ident__part_has__view_x_27___lambda__2___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_nat_obj(0u);
x_2 = lean_name_mk_numeral(x_0, x_1);
return x_2;
}
}
obj* _init_l_lean_parser_detail__ident__part_has__view_x_27___lambda__2___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_nat_obj(1u);
x_2 = lean_name_mk_numeral(x_0, x_1);
return x_2;
}
}
obj* l_lean_parser_detail__ident__part_has__view_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::box(0);
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; obj* x_5; obj* x_6; obj* x_8; obj* x_10; obj* x_11; obj* x_13; obj* x_14; obj* x_15; obj* x_17; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
x_5 = l_lean_parser_detail__ident__part__escaped_has__view;
x_6 = lean::cnstr_get(x_5, 1);
lean::inc(x_6);
x_8 = lean::apply_1(x_6, x_2);
lean::inc(x_1);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_1);
x_11 = l_lean_parser_detail__ident__part_has__view_x_27___lambda__2___closed__1;
lean::inc(x_11);
x_13 = l_lean_parser_syntax_mk__node(x_11, x_10);
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_1);
x_15 = l_lean_parser_detail__ident__part;
lean::inc(x_15);
x_17 = l_lean_parser_syntax_mk__node(x_15, x_14);
return x_17;
}
else
{
obj* x_18; obj* x_21; obj* x_23; obj* x_24; obj* x_25; obj* x_27; obj* x_28; obj* x_30; obj* x_31; obj* x_32; obj* x_34; 
x_18 = lean::cnstr_get(x_0, 0);
lean::inc(x_18);
lean::dec(x_0);
x_21 = l_lean_parser_raw_view___rarg___lambda__3___closed__1;
lean::inc(x_21);
x_23 = l_option_map___rarg(x_21, x_18);
x_24 = lean::box(3);
x_25 = l_option_get__or__else___main___rarg(x_23, x_24);
lean::inc(x_1);
x_27 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_27, 0, x_25);
lean::cnstr_set(x_27, 1, x_1);
x_28 = l_lean_parser_detail__ident__part_has__view_x_27___lambda__2___closed__2;
lean::inc(x_28);
x_30 = l_lean_parser_syntax_mk__node(x_28, x_27);
x_31 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_31, 0, x_30);
lean::cnstr_set(x_31, 1, x_1);
x_32 = l_lean_parser_detail__ident__part;
lean::inc(x_32);
x_34 = l_lean_parser_syntax_mk__node(x_32, x_31);
return x_34;
}
}
}
obj* _init_l_lean_parser_detail__ident__part_has__view_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_detail__ident__part_has__view_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_detail__ident__part_has__view_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_lean_parser_detail__ident__part_has__view() {
_start:
{
obj* x_0; 
x_0 = l_lean_parser_detail__ident__part_has__view_x_27;
lean::inc(x_0);
return x_0;
}
}
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
uint8 x_6; 
x_6 = lean::string_iterator_has_next(x_2);
if (x_6 == 0)
{
obj* x_8; 
lean::dec(x_0);
x_8 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_8;
}
else
{
uint32 x_9; uint8 x_10; 
x_9 = lean::string_iterator_curr(x_2);
x_10 = l_lean_is__id__end__escape(x_9);
if (x_10 == 0)
{
obj* x_11; obj* x_12; obj* x_15; obj* x_16; 
x_11 = lean::mk_nat_obj(1u);
x_12 = lean::nat_sub(x_0, x_11);
lean::dec(x_11);
lean::dec(x_0);
x_15 = lean::string_push(x_1, x_9);
x_16 = lean::string_iterator_next(x_2);
x_0 = x_12;
x_1 = x_15;
x_2 = x_16;
goto _start;
}
else
{
obj* x_19; 
lean::dec(x_0);
x_19 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_19;
}
}
}
else
{
obj* x_21; 
lean::dec(x_0);
x_21 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_21;
}
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__2(uint32 x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
lean::dec(x_1);
x_5 = l_string_join___closed__1;
lean::inc(x_5);
x_7 = lean::string_push(x_5, x_0);
x_8 = lean::string_iterator_remaining(x_2);
x_9 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__3(x_8, x_7, x_2);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_3);
return x_10;
}
}
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__5(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
uint8 x_6; 
x_6 = lean::string_iterator_has_next(x_2);
if (x_6 == 0)
{
obj* x_8; 
lean::dec(x_0);
x_8 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_8;
}
else
{
uint32 x_9; uint8 x_10; 
x_9 = lean::string_iterator_curr(x_2);
x_10 = l_lean_is__id__end__escape(x_9);
if (x_10 == 0)
{
obj* x_11; obj* x_12; obj* x_15; obj* x_16; 
x_11 = lean::mk_nat_obj(1u);
x_12 = lean::nat_sub(x_0, x_11);
lean::dec(x_11);
lean::dec(x_0);
x_15 = lean::string_push(x_1, x_9);
x_16 = lean::string_iterator_next(x_2);
x_0 = x_12;
x_1 = x_15;
x_2 = x_16;
goto _start;
}
else
{
obj* x_19; 
lean::dec(x_0);
x_19 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_19;
}
}
}
else
{
obj* x_21; 
lean::dec(x_0);
x_21 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_21;
}
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__4(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint32 x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
lean::dec(x_1);
x_5 = lean::string_iterator_curr(x_0);
lean::dec(x_0);
x_7 = l_string_join___closed__1;
lean::inc(x_7);
x_9 = lean::string_push(x_7, x_5);
x_10 = lean::string_iterator_remaining(x_2);
x_11 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__5(x_10, x_9, x_2);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_3);
return x_12;
}
}
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__7(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
uint8 x_6; 
x_6 = lean::string_iterator_has_next(x_2);
if (x_6 == 0)
{
obj* x_8; 
lean::dec(x_0);
x_8 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_8;
}
else
{
uint32 x_9; uint8 x_10; 
x_9 = lean::string_iterator_curr(x_2);
x_10 = l_lean_is__id__end__escape(x_9);
if (x_10 == 0)
{
obj* x_11; obj* x_12; obj* x_15; obj* x_16; 
x_11 = lean::mk_nat_obj(1u);
x_12 = lean::nat_sub(x_0, x_11);
lean::dec(x_11);
lean::dec(x_0);
x_15 = lean::string_push(x_1, x_9);
x_16 = lean::string_iterator_next(x_2);
x_0 = x_12;
x_1 = x_15;
x_2 = x_16;
goto _start;
}
else
{
obj* x_19; 
lean::dec(x_0);
x_19 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_19;
}
}
}
else
{
obj* x_21; 
lean::dec(x_0);
x_21 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_21;
}
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__6(uint32 x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
lean::dec(x_1);
x_5 = l_string_join___closed__1;
lean::inc(x_5);
x_7 = lean::string_push(x_5, x_0);
x_8 = lean::string_iterator_remaining(x_2);
x_9 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__7(x_8, x_7, x_2);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_3);
return x_10;
}
}
obj* l_lean_parser_monad__parsec_take__while1___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = lean::string_iterator_has_next(x_1);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; obj* x_11; obj* x_12; obj* x_14; obj* x_16; obj* x_17; obj* x_19; 
x_4 = lean::box(0);
x_5 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_6 = l_mjoin___rarg___closed__1;
lean::inc(x_0);
lean::inc(x_4);
lean::inc(x_6);
lean::inc(x_5);
x_11 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_5, x_6, x_4, x_4, x_0, x_1, x_2);
x_12 = lean::cnstr_get(x_11, 0);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_11, 1);
lean::inc(x_14);
if (lean::is_shared(x_11)) {
 lean::dec(x_11);
 x_16 = lean::box(0);
} else {
 lean::cnstr_release(x_11, 0);
 lean::cnstr_release(x_11, 1);
 x_16 = x_11;
}
x_17 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_17);
x_19 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_17, x_12);
if (lean::obj_tag(x_19) == 0)
{
obj* x_20; obj* x_22; obj* x_24; uint32 x_27; obj* x_29; obj* x_30; obj* x_32; obj* x_35; obj* x_36; 
x_20 = lean::cnstr_get(x_19, 0);
lean::inc(x_20);
x_22 = lean::cnstr_get(x_19, 1);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_19, 2);
lean::inc(x_24);
lean::dec(x_19);
x_27 = lean::unbox_uint32(x_20);
lean::dec(x_20);
x_29 = l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__2(x_27, x_0, x_22, x_14);
x_30 = lean::cnstr_get(x_29, 0);
lean::inc(x_30);
x_32 = lean::cnstr_get(x_29, 1);
lean::inc(x_32);
lean::dec(x_29);
x_35 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_24, x_30);
if (lean::is_scalar(x_16)) {
 x_36 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_36 = x_16;
}
lean::cnstr_set(x_36, 0, x_35);
lean::cnstr_set(x_36, 1, x_32);
return x_36;
}
else
{
obj* x_38; uint8 x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; 
lean::dec(x_0);
x_38 = lean::cnstr_get(x_19, 0);
lean::inc(x_38);
x_40 = lean::cnstr_get_scalar<uint8>(x_19, sizeof(void*)*1);
if (lean::is_shared(x_19)) {
 lean::dec(x_19);
 x_41 = lean::box(0);
} else {
 lean::cnstr_release(x_19, 0);
 x_41 = x_19;
}
if (lean::is_scalar(x_41)) {
 x_42 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_42 = x_41;
}
lean::cnstr_set(x_42, 0, x_38);
lean::cnstr_set_scalar(x_42, sizeof(void*)*1, x_40);
x_43 = x_42;
if (lean::is_scalar(x_16)) {
 x_44 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_44 = x_16;
}
lean::cnstr_set(x_44, 0, x_43);
lean::cnstr_set(x_44, 1, x_14);
return x_44;
}
}
else
{
uint32 x_45; uint8 x_46; 
x_45 = lean::string_iterator_curr(x_1);
x_46 = l_lean_is__id__end__escape(x_45);
if (x_46 == 0)
{
obj* x_48; obj* x_49; obj* x_50; obj* x_52; obj* x_54; obj* x_55; obj* x_56; obj* x_57; 
lean::inc(x_1);
x_48 = lean::string_iterator_next(x_1);
x_49 = l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__4(x_1, x_0, x_48, x_2);
x_50 = lean::cnstr_get(x_49, 0);
lean::inc(x_50);
x_52 = lean::cnstr_get(x_49, 1);
lean::inc(x_52);
if (lean::is_shared(x_49)) {
 lean::dec(x_49);
 x_54 = lean::box(0);
} else {
 lean::cnstr_release(x_49, 0);
 lean::cnstr_release(x_49, 1);
 x_54 = x_49;
}
x_55 = lean::box(0);
x_56 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_55, x_50);
if (lean::is_scalar(x_54)) {
 x_57 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_57 = x_54;
}
lean::cnstr_set(x_57, 0, x_56);
lean::cnstr_set(x_57, 1, x_52);
return x_57;
}
else
{
obj* x_58; obj* x_59; obj* x_61; obj* x_63; obj* x_64; obj* x_65; obj* x_69; obj* x_70; obj* x_72; obj* x_74; obj* x_75; obj* x_77; 
x_58 = l_char_quote__core(x_45);
x_59 = l_char_has__repr___closed__1;
lean::inc(x_59);
x_61 = lean::string_append(x_59, x_58);
lean::dec(x_58);
x_63 = lean::string_append(x_61, x_59);
x_64 = lean::box(0);
x_65 = l_mjoin___rarg___closed__1;
lean::inc(x_0);
lean::inc(x_64);
lean::inc(x_65);
x_69 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_63, x_65, x_64, x_64, x_0, x_1, x_2);
x_70 = lean::cnstr_get(x_69, 0);
lean::inc(x_70);
x_72 = lean::cnstr_get(x_69, 1);
lean::inc(x_72);
if (lean::is_shared(x_69)) {
 lean::dec(x_69);
 x_74 = lean::box(0);
} else {
 lean::cnstr_release(x_69, 0);
 lean::cnstr_release(x_69, 1);
 x_74 = x_69;
}
x_75 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_75);
x_77 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_75, x_70);
if (lean::obj_tag(x_77) == 0)
{
obj* x_78; obj* x_80; obj* x_82; uint32 x_85; obj* x_87; obj* x_88; obj* x_90; obj* x_93; obj* x_94; 
x_78 = lean::cnstr_get(x_77, 0);
lean::inc(x_78);
x_80 = lean::cnstr_get(x_77, 1);
lean::inc(x_80);
x_82 = lean::cnstr_get(x_77, 2);
lean::inc(x_82);
lean::dec(x_77);
x_85 = lean::unbox_uint32(x_78);
lean::dec(x_78);
x_87 = l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__6(x_85, x_0, x_80, x_72);
x_88 = lean::cnstr_get(x_87, 0);
lean::inc(x_88);
x_90 = lean::cnstr_get(x_87, 1);
lean::inc(x_90);
lean::dec(x_87);
x_93 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_82, x_88);
if (lean::is_scalar(x_74)) {
 x_94 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_94 = x_74;
}
lean::cnstr_set(x_94, 0, x_93);
lean::cnstr_set(x_94, 1, x_90);
return x_94;
}
else
{
obj* x_96; uint8 x_98; obj* x_99; obj* x_100; obj* x_101; obj* x_102; 
lean::dec(x_0);
x_96 = lean::cnstr_get(x_77, 0);
lean::inc(x_96);
x_98 = lean::cnstr_get_scalar<uint8>(x_77, sizeof(void*)*1);
if (lean::is_shared(x_77)) {
 lean::dec(x_77);
 x_99 = lean::box(0);
} else {
 lean::cnstr_release(x_77, 0);
 x_99 = x_77;
}
if (lean::is_scalar(x_99)) {
 x_100 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_100 = x_99;
}
lean::cnstr_set(x_100, 0, x_96);
lean::cnstr_set_scalar(x_100, sizeof(void*)*1, x_98);
x_101 = x_100;
if (lean::is_scalar(x_74)) {
 x_102 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_102 = x_74;
}
lean::cnstr_set(x_102, 0, x_101);
lean::cnstr_set(x_102, 1, x_72);
return x_102;
}
}
}
}
}
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__10(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
uint8 x_6; 
x_6 = lean::string_iterator_has_next(x_2);
if (x_6 == 0)
{
obj* x_8; 
lean::dec(x_0);
x_8 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_8;
}
else
{
uint32 x_9; uint8 x_10; 
x_9 = lean::string_iterator_curr(x_2);
x_10 = l_lean_is__id__end__escape(x_9);
if (x_10 == 0)
{
obj* x_11; obj* x_12; obj* x_15; obj* x_16; 
x_11 = lean::mk_nat_obj(1u);
x_12 = lean::nat_sub(x_0, x_11);
lean::dec(x_11);
lean::dec(x_0);
x_15 = lean::string_push(x_1, x_9);
x_16 = lean::string_iterator_next(x_2);
x_0 = x_12;
x_1 = x_15;
x_2 = x_16;
goto _start;
}
else
{
obj* x_19; 
lean::dec(x_0);
x_19 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_19;
}
}
}
else
{
obj* x_21; 
lean::dec(x_0);
x_21 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_21;
}
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__9(uint32 x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
lean::dec(x_1);
x_5 = l_string_join___closed__1;
lean::inc(x_5);
x_7 = lean::string_push(x_5, x_0);
x_8 = lean::string_iterator_remaining(x_2);
x_9 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__10(x_8, x_7, x_2);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_3);
return x_10;
}
}
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__12(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
uint8 x_6; 
x_6 = lean::string_iterator_has_next(x_2);
if (x_6 == 0)
{
obj* x_8; 
lean::dec(x_0);
x_8 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_8;
}
else
{
uint32 x_9; uint8 x_10; 
x_9 = lean::string_iterator_curr(x_2);
x_10 = l_lean_is__id__end__escape(x_9);
if (x_10 == 0)
{
obj* x_11; obj* x_12; obj* x_15; obj* x_16; 
x_11 = lean::mk_nat_obj(1u);
x_12 = lean::nat_sub(x_0, x_11);
lean::dec(x_11);
lean::dec(x_0);
x_15 = lean::string_push(x_1, x_9);
x_16 = lean::string_iterator_next(x_2);
x_0 = x_12;
x_1 = x_15;
x_2 = x_16;
goto _start;
}
else
{
obj* x_19; 
lean::dec(x_0);
x_19 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_19;
}
}
}
else
{
obj* x_21; 
lean::dec(x_0);
x_21 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_21;
}
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__11(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint32 x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
lean::dec(x_1);
x_5 = lean::string_iterator_curr(x_0);
lean::dec(x_0);
x_7 = l_string_join___closed__1;
lean::inc(x_7);
x_9 = lean::string_push(x_7, x_5);
x_10 = lean::string_iterator_remaining(x_2);
x_11 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__12(x_10, x_9, x_2);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_3);
return x_12;
}
}
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__14(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
uint8 x_6; 
x_6 = lean::string_iterator_has_next(x_2);
if (x_6 == 0)
{
obj* x_8; 
lean::dec(x_0);
x_8 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_8;
}
else
{
uint32 x_9; uint8 x_10; 
x_9 = lean::string_iterator_curr(x_2);
x_10 = l_lean_is__id__end__escape(x_9);
if (x_10 == 0)
{
obj* x_11; obj* x_12; obj* x_15; obj* x_16; 
x_11 = lean::mk_nat_obj(1u);
x_12 = lean::nat_sub(x_0, x_11);
lean::dec(x_11);
lean::dec(x_0);
x_15 = lean::string_push(x_1, x_9);
x_16 = lean::string_iterator_next(x_2);
x_0 = x_12;
x_1 = x_15;
x_2 = x_16;
goto _start;
}
else
{
obj* x_19; 
lean::dec(x_0);
x_19 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_19;
}
}
}
else
{
obj* x_21; 
lean::dec(x_0);
x_21 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_21;
}
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__13(uint32 x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
lean::dec(x_1);
x_5 = l_string_join___closed__1;
lean::inc(x_5);
x_7 = lean::string_push(x_5, x_0);
x_8 = lean::string_iterator_remaining(x_2);
x_9 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__14(x_8, x_7, x_2);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_3);
return x_10;
}
}
obj* l_lean_parser_monad__parsec_take__while1___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__8(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = lean::string_iterator_has_next(x_1);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; obj* x_11; obj* x_12; obj* x_14; obj* x_16; obj* x_17; obj* x_19; 
x_4 = lean::box(0);
x_5 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_6 = l_mjoin___rarg___closed__1;
lean::inc(x_0);
lean::inc(x_4);
lean::inc(x_6);
lean::inc(x_5);
x_11 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_5, x_6, x_4, x_4, x_0, x_1, x_2);
x_12 = lean::cnstr_get(x_11, 0);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_11, 1);
lean::inc(x_14);
if (lean::is_shared(x_11)) {
 lean::dec(x_11);
 x_16 = lean::box(0);
} else {
 lean::cnstr_release(x_11, 0);
 lean::cnstr_release(x_11, 1);
 x_16 = x_11;
}
x_17 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_17);
x_19 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_17, x_12);
if (lean::obj_tag(x_19) == 0)
{
obj* x_20; obj* x_22; obj* x_24; uint32 x_27; obj* x_29; obj* x_30; obj* x_32; obj* x_35; obj* x_36; 
x_20 = lean::cnstr_get(x_19, 0);
lean::inc(x_20);
x_22 = lean::cnstr_get(x_19, 1);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_19, 2);
lean::inc(x_24);
lean::dec(x_19);
x_27 = lean::unbox_uint32(x_20);
lean::dec(x_20);
x_29 = l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__9(x_27, x_0, x_22, x_14);
x_30 = lean::cnstr_get(x_29, 0);
lean::inc(x_30);
x_32 = lean::cnstr_get(x_29, 1);
lean::inc(x_32);
lean::dec(x_29);
x_35 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_24, x_30);
if (lean::is_scalar(x_16)) {
 x_36 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_36 = x_16;
}
lean::cnstr_set(x_36, 0, x_35);
lean::cnstr_set(x_36, 1, x_32);
return x_36;
}
else
{
obj* x_38; uint8 x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; 
lean::dec(x_0);
x_38 = lean::cnstr_get(x_19, 0);
lean::inc(x_38);
x_40 = lean::cnstr_get_scalar<uint8>(x_19, sizeof(void*)*1);
if (lean::is_shared(x_19)) {
 lean::dec(x_19);
 x_41 = lean::box(0);
} else {
 lean::cnstr_release(x_19, 0);
 x_41 = x_19;
}
if (lean::is_scalar(x_41)) {
 x_42 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_42 = x_41;
}
lean::cnstr_set(x_42, 0, x_38);
lean::cnstr_set_scalar(x_42, sizeof(void*)*1, x_40);
x_43 = x_42;
if (lean::is_scalar(x_16)) {
 x_44 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_44 = x_16;
}
lean::cnstr_set(x_44, 0, x_43);
lean::cnstr_set(x_44, 1, x_14);
return x_44;
}
}
else
{
uint32 x_45; uint8 x_46; 
x_45 = lean::string_iterator_curr(x_1);
x_46 = l_lean_is__id__end__escape(x_45);
if (x_46 == 0)
{
obj* x_48; obj* x_49; obj* x_50; obj* x_52; obj* x_54; obj* x_55; obj* x_56; obj* x_57; 
lean::inc(x_1);
x_48 = lean::string_iterator_next(x_1);
x_49 = l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__11(x_1, x_0, x_48, x_2);
x_50 = lean::cnstr_get(x_49, 0);
lean::inc(x_50);
x_52 = lean::cnstr_get(x_49, 1);
lean::inc(x_52);
if (lean::is_shared(x_49)) {
 lean::dec(x_49);
 x_54 = lean::box(0);
} else {
 lean::cnstr_release(x_49, 0);
 lean::cnstr_release(x_49, 1);
 x_54 = x_49;
}
x_55 = lean::box(0);
x_56 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_55, x_50);
if (lean::is_scalar(x_54)) {
 x_57 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_57 = x_54;
}
lean::cnstr_set(x_57, 0, x_56);
lean::cnstr_set(x_57, 1, x_52);
return x_57;
}
else
{
obj* x_58; obj* x_59; obj* x_61; obj* x_63; obj* x_64; obj* x_65; obj* x_69; obj* x_70; obj* x_72; obj* x_74; obj* x_75; obj* x_77; 
x_58 = l_char_quote__core(x_45);
x_59 = l_char_has__repr___closed__1;
lean::inc(x_59);
x_61 = lean::string_append(x_59, x_58);
lean::dec(x_58);
x_63 = lean::string_append(x_61, x_59);
x_64 = lean::box(0);
x_65 = l_mjoin___rarg___closed__1;
lean::inc(x_0);
lean::inc(x_64);
lean::inc(x_65);
x_69 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_63, x_65, x_64, x_64, x_0, x_1, x_2);
x_70 = lean::cnstr_get(x_69, 0);
lean::inc(x_70);
x_72 = lean::cnstr_get(x_69, 1);
lean::inc(x_72);
if (lean::is_shared(x_69)) {
 lean::dec(x_69);
 x_74 = lean::box(0);
} else {
 lean::cnstr_release(x_69, 0);
 lean::cnstr_release(x_69, 1);
 x_74 = x_69;
}
x_75 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_75);
x_77 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_75, x_70);
if (lean::obj_tag(x_77) == 0)
{
obj* x_78; obj* x_80; obj* x_82; uint32 x_85; obj* x_87; obj* x_88; obj* x_90; obj* x_93; obj* x_94; 
x_78 = lean::cnstr_get(x_77, 0);
lean::inc(x_78);
x_80 = lean::cnstr_get(x_77, 1);
lean::inc(x_80);
x_82 = lean::cnstr_get(x_77, 2);
lean::inc(x_82);
lean::dec(x_77);
x_85 = lean::unbox_uint32(x_78);
lean::dec(x_78);
x_87 = l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__13(x_85, x_0, x_80, x_72);
x_88 = lean::cnstr_get(x_87, 0);
lean::inc(x_88);
x_90 = lean::cnstr_get(x_87, 1);
lean::inc(x_90);
lean::dec(x_87);
x_93 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_82, x_88);
if (lean::is_scalar(x_74)) {
 x_94 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_94 = x_74;
}
lean::cnstr_set(x_94, 0, x_93);
lean::cnstr_set(x_94, 1, x_90);
return x_94;
}
else
{
obj* x_96; uint8 x_98; obj* x_99; obj* x_100; obj* x_101; obj* x_102; 
lean::dec(x_0);
x_96 = lean::cnstr_get(x_77, 0);
lean::inc(x_96);
x_98 = lean::cnstr_get_scalar<uint8>(x_77, sizeof(void*)*1);
if (lean::is_shared(x_77)) {
 lean::dec(x_77);
 x_99 = lean::box(0);
} else {
 lean::cnstr_release(x_77, 0);
 x_99 = x_77;
}
if (lean::is_scalar(x_99)) {
 x_100 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_100 = x_99;
}
lean::cnstr_set(x_100, 0, x_96);
lean::cnstr_set_scalar(x_100, sizeof(void*)*1, x_98);
x_101 = x_100;
if (lean::is_scalar(x_74)) {
 x_102 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_102 = x_74;
}
lean::cnstr_set(x_102, 0, x_101);
lean::cnstr_set(x_102, 1, x_72);
return x_102;
}
}
}
}
}
obj* l_list_mfoldl___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__16(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_9; obj* x_11; obj* x_12; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
x_9 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_9);
x_11 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_11, 0, x_1);
lean::cnstr_set(x_11, 1, x_4);
lean::cnstr_set(x_11, 2, x_9);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_5);
return x_12;
}
else
{
obj* x_13; obj* x_15; obj* x_17; obj* x_18; obj* x_19; obj* x_22; obj* x_23; obj* x_25; 
x_13 = lean::cnstr_get(x_2, 0);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_2, 1);
lean::inc(x_15);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_17 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 lean::cnstr_release(x_2, 1);
 x_17 = x_2;
}
lean::inc(x_3);
x_22 = lean::apply_3(x_13, x_3, x_4, x_5);
x_23 = lean::cnstr_get(x_22, 0);
lean::inc(x_23);
x_25 = lean::cnstr_get(x_22, 1);
lean::inc(x_25);
lean::dec(x_22);
if (lean::obj_tag(x_23) == 0)
{
x_18 = x_23;
x_19 = x_25;
goto lbl_20;
}
else
{
obj* x_28; uint8 x_30; obj* x_31; 
x_28 = lean::cnstr_get(x_23, 0);
lean::inc(x_28);
x_30 = lean::cnstr_get_scalar<uint8>(x_23, sizeof(void*)*1);
if (lean::is_shared(x_23)) {
 lean::dec(x_23);
 x_31 = lean::box(0);
} else {
 lean::cnstr_release(x_23, 0);
 x_31 = x_23;
}
if (lean::obj_tag(x_1) == 0)
{
if (x_30 == 0)
{
uint8 x_32; obj* x_33; obj* x_34; 
x_32 = 0;
if (lean::is_scalar(x_31)) {
 x_33 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_33 = x_31;
}
lean::cnstr_set(x_33, 0, x_28);
lean::cnstr_set_scalar(x_33, sizeof(void*)*1, x_32);
x_34 = x_33;
x_18 = x_34;
x_19 = x_25;
goto lbl_20;
}
else
{
obj* x_35; obj* x_36; 
if (lean::is_scalar(x_31)) {
 x_35 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_35 = x_31;
}
lean::cnstr_set(x_35, 0, x_28);
lean::cnstr_set_scalar(x_35, sizeof(void*)*1, x_30);
x_36 = x_35;
x_18 = x_36;
x_19 = x_25;
goto lbl_20;
}
}
else
{
obj* x_37; obj* x_39; obj* x_41; obj* x_42; obj* x_44; obj* x_46; obj* x_49; obj* x_51; obj* x_52; obj* x_53; 
x_37 = lean::cnstr_get(x_28, 3);
lean::inc(x_37);
x_39 = l_option_get___main___at_lean_parser_run___spec__2(x_37);
lean::inc(x_1);
x_41 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_41, 0, x_39);
lean::cnstr_set(x_41, 1, x_1);
x_42 = lean::cnstr_get(x_28, 0);
lean::inc(x_42);
x_44 = lean::cnstr_get(x_28, 1);
lean::inc(x_44);
x_46 = lean::cnstr_get(x_28, 2);
lean::inc(x_46);
lean::dec(x_28);
x_49 = l_list_reverse___rarg(x_41);
lean::inc(x_0);
x_51 = l_lean_parser_syntax_mk__node(x_0, x_49);
x_52 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_52, 0, x_51);
x_53 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_53, 0, x_42);
lean::cnstr_set(x_53, 1, x_44);
lean::cnstr_set(x_53, 2, x_46);
lean::cnstr_set(x_53, 3, x_52);
if (x_30 == 0)
{
uint8 x_54; obj* x_55; obj* x_56; 
x_54 = 0;
if (lean::is_scalar(x_31)) {
 x_55 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_55 = x_31;
}
lean::cnstr_set(x_55, 0, x_53);
lean::cnstr_set_scalar(x_55, sizeof(void*)*1, x_54);
x_56 = x_55;
x_18 = x_56;
x_19 = x_25;
goto lbl_20;
}
else
{
obj* x_57; obj* x_58; 
if (lean::is_scalar(x_31)) {
 x_57 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_57 = x_31;
}
lean::cnstr_set(x_57, 0, x_53);
lean::cnstr_set_scalar(x_57, sizeof(void*)*1, x_30);
x_58 = x_57;
x_18 = x_58;
x_19 = x_25;
goto lbl_20;
}
}
}
lbl_20:
{
if (lean::obj_tag(x_18) == 0)
{
obj* x_59; obj* x_61; obj* x_63; obj* x_65; obj* x_66; obj* x_67; obj* x_69; obj* x_70; 
x_59 = lean::cnstr_get(x_18, 0);
lean::inc(x_59);
x_61 = lean::cnstr_get(x_18, 1);
lean::inc(x_61);
x_63 = lean::cnstr_get(x_18, 2);
lean::inc(x_63);
if (lean::is_shared(x_18)) {
 lean::dec(x_18);
 x_65 = lean::box(0);
} else {
 lean::cnstr_release(x_18, 0);
 lean::cnstr_release(x_18, 1);
 lean::cnstr_release(x_18, 2);
 x_65 = x_18;
}
if (lean::is_scalar(x_17)) {
 x_66 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_66 = x_17;
}
lean::cnstr_set(x_66, 0, x_59);
lean::cnstr_set(x_66, 1, x_1);
x_67 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_67);
if (lean::is_scalar(x_65)) {
 x_69 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_69 = x_65;
}
lean::cnstr_set(x_69, 0, x_66);
lean::cnstr_set(x_69, 1, x_61);
lean::cnstr_set(x_69, 2, x_67);
x_70 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_63, x_69);
if (lean::obj_tag(x_70) == 0)
{
obj* x_71; obj* x_73; obj* x_75; obj* x_78; obj* x_79; obj* x_81; obj* x_83; obj* x_84; obj* x_85; 
x_71 = lean::cnstr_get(x_70, 0);
lean::inc(x_71);
x_73 = lean::cnstr_get(x_70, 1);
lean::inc(x_73);
x_75 = lean::cnstr_get(x_70, 2);
lean::inc(x_75);
lean::dec(x_70);
x_78 = l_list_mfoldl___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__16(x_0, x_71, x_15, x_3, x_73, x_19);
x_79 = lean::cnstr_get(x_78, 0);
lean::inc(x_79);
x_81 = lean::cnstr_get(x_78, 1);
lean::inc(x_81);
if (lean::is_shared(x_78)) {
 lean::dec(x_78);
 x_83 = lean::box(0);
} else {
 lean::cnstr_release(x_78, 0);
 lean::cnstr_release(x_78, 1);
 x_83 = x_78;
}
x_84 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_75, x_79);
if (lean::is_scalar(x_83)) {
 x_85 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_85 = x_83;
}
lean::cnstr_set(x_85, 0, x_84);
lean::cnstr_set(x_85, 1, x_81);
return x_85;
}
else
{
obj* x_89; uint8 x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_95; 
lean::dec(x_15);
lean::dec(x_3);
lean::dec(x_0);
x_89 = lean::cnstr_get(x_70, 0);
lean::inc(x_89);
x_91 = lean::cnstr_get_scalar<uint8>(x_70, sizeof(void*)*1);
if (lean::is_shared(x_70)) {
 lean::dec(x_70);
 x_92 = lean::box(0);
} else {
 lean::cnstr_release(x_70, 0);
 x_92 = x_70;
}
if (lean::is_scalar(x_92)) {
 x_93 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_93 = x_92;
}
lean::cnstr_set(x_93, 0, x_89);
lean::cnstr_set_scalar(x_93, sizeof(void*)*1, x_91);
x_94 = x_93;
x_95 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_95, 0, x_94);
lean::cnstr_set(x_95, 1, x_19);
return x_95;
}
}
else
{
obj* x_101; uint8 x_103; obj* x_104; obj* x_105; obj* x_106; obj* x_107; 
lean::dec(x_15);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_17);
x_101 = lean::cnstr_get(x_18, 0);
lean::inc(x_101);
x_103 = lean::cnstr_get_scalar<uint8>(x_18, sizeof(void*)*1);
if (lean::is_shared(x_18)) {
 lean::dec(x_18);
 x_104 = lean::box(0);
} else {
 lean::cnstr_release(x_18, 0);
 x_104 = x_18;
}
if (lean::is_scalar(x_104)) {
 x_105 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_105 = x_104;
}
lean::cnstr_set(x_105, 0, x_101);
lean::cnstr_set_scalar(x_105, sizeof(void*)*1, x_103);
x_106 = x_105;
x_107 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_107, 0, x_106);
lean::cnstr_set(x_107, 1, x_19);
return x_107;
}
}
}
}
}
obj* l_lean_parser_combinators_node___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__15(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_7; obj* x_8; obj* x_10; obj* x_12; 
x_5 = lean::box(0);
lean::inc(x_0);
x_7 = l_list_mfoldl___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__16(x_0, x_5, x_1, x_2, x_3, x_4);
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
obj* x_13; obj* x_15; obj* x_17; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_24; obj* x_25; obj* x_26; 
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
x_20 = l_list_reverse___rarg(x_13);
x_21 = l_lean_parser_syntax_mk__node(x_0, x_20);
x_22 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_22);
if (lean::is_scalar(x_19)) {
 x_24 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_24 = x_19;
}
lean::cnstr_set(x_24, 0, x_21);
lean::cnstr_set(x_24, 1, x_15);
lean::cnstr_set(x_24, 2, x_22);
x_25 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_17, x_24);
if (lean::is_scalar(x_12)) {
 x_26 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_26 = x_12;
}
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_10);
return x_26;
}
else
{
obj* x_28; uint8 x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; 
lean::dec(x_0);
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
return x_34;
}
}
}
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__18(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
uint8 x_6; 
x_6 = lean::string_iterator_has_next(x_2);
if (x_6 == 0)
{
obj* x_8; 
lean::dec(x_0);
x_8 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_8;
}
else
{
uint32 x_9; uint8 x_10; 
x_9 = lean::string_iterator_curr(x_2);
x_10 = l_lean_is__id__rest(x_9);
if (x_10 == 0)
{
obj* x_12; 
lean::dec(x_0);
x_12 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_12;
}
else
{
obj* x_13; obj* x_14; obj* x_17; obj* x_18; 
x_13 = lean::mk_nat_obj(1u);
x_14 = lean::nat_sub(x_0, x_13);
lean::dec(x_13);
lean::dec(x_0);
x_17 = lean::string_push(x_1, x_9);
x_18 = lean::string_iterator_next(x_2);
x_0 = x_14;
x_1 = x_17;
x_2 = x_18;
goto _start;
}
}
}
else
{
obj* x_21; 
lean::dec(x_0);
x_21 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_21;
}
}
}
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__17___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_5; obj* x_6; 
x_2 = lean::string_iterator_remaining(x_0);
x_3 = l_string_join___closed__1;
lean::inc(x_3);
x_5 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__18(x_2, x_3, x_0);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_1);
return x_6;
}
}
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__17(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__17___rarg), 2, 0);
return x_2;
}
}
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__20(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
uint8 x_6; 
x_6 = lean::string_iterator_has_next(x_2);
if (x_6 == 0)
{
obj* x_8; 
lean::dec(x_0);
x_8 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_8;
}
else
{
uint32 x_9; uint8 x_10; 
x_9 = lean::string_iterator_curr(x_2);
x_10 = l_lean_is__id__rest(x_9);
if (x_10 == 0)
{
obj* x_12; 
lean::dec(x_0);
x_12 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_12;
}
else
{
obj* x_13; obj* x_14; obj* x_17; obj* x_18; 
x_13 = lean::mk_nat_obj(1u);
x_14 = lean::nat_sub(x_0, x_13);
lean::dec(x_13);
lean::dec(x_0);
x_17 = lean::string_push(x_1, x_9);
x_18 = lean::string_iterator_next(x_2);
x_0 = x_14;
x_1 = x_17;
x_2 = x_18;
goto _start;
}
}
}
else
{
obj* x_21; 
lean::dec(x_0);
x_21 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_21;
}
}
}
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__19___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_5; obj* x_6; 
x_2 = lean::string_iterator_remaining(x_0);
x_3 = l_string_join___closed__1;
lean::inc(x_3);
x_5 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__20(x_2, x_3, x_0);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_1);
return x_6;
}
}
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__19(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__19___rarg), 2, 0);
return x_2;
}
}
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__22(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
uint8 x_6; 
x_6 = lean::string_iterator_has_next(x_2);
if (x_6 == 0)
{
obj* x_8; 
lean::dec(x_0);
x_8 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_8;
}
else
{
uint32 x_9; uint8 x_10; 
x_9 = lean::string_iterator_curr(x_2);
x_10 = l_lean_is__id__rest(x_9);
if (x_10 == 0)
{
obj* x_12; 
lean::dec(x_0);
x_12 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_12;
}
else
{
obj* x_13; obj* x_14; obj* x_17; obj* x_18; 
x_13 = lean::mk_nat_obj(1u);
x_14 = lean::nat_sub(x_0, x_13);
lean::dec(x_13);
lean::dec(x_0);
x_17 = lean::string_push(x_1, x_9);
x_18 = lean::string_iterator_next(x_2);
x_0 = x_14;
x_1 = x_17;
x_2 = x_18;
goto _start;
}
}
}
else
{
obj* x_21; 
lean::dec(x_0);
x_21 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_21;
}
}
}
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__21___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_5; obj* x_6; 
x_2 = lean::string_iterator_remaining(x_0);
x_3 = l_string_join___closed__1;
lean::inc(x_3);
x_5 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__22(x_2, x_3, x_0);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_1);
return x_6;
}
}
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__21(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__21___rarg), 2, 0);
return x_2;
}
}
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__24(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
uint8 x_6; 
x_6 = lean::string_iterator_has_next(x_2);
if (x_6 == 0)
{
obj* x_8; 
lean::dec(x_0);
x_8 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_8;
}
else
{
uint32 x_9; uint8 x_10; 
x_9 = lean::string_iterator_curr(x_2);
x_10 = l_lean_is__id__rest(x_9);
if (x_10 == 0)
{
obj* x_12; 
lean::dec(x_0);
x_12 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_12;
}
else
{
obj* x_13; obj* x_14; obj* x_17; obj* x_18; 
x_13 = lean::mk_nat_obj(1u);
x_14 = lean::nat_sub(x_0, x_13);
lean::dec(x_13);
lean::dec(x_0);
x_17 = lean::string_push(x_1, x_9);
x_18 = lean::string_iterator_next(x_2);
x_0 = x_14;
x_1 = x_17;
x_2 = x_18;
goto _start;
}
}
}
else
{
obj* x_21; 
lean::dec(x_0);
x_21 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_21;
}
}
}
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__23___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_5; obj* x_6; 
x_2 = lean::string_iterator_remaining(x_0);
x_3 = l_string_join___closed__1;
lean::inc(x_3);
x_5 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__24(x_2, x_3, x_0);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_1);
return x_6;
}
}
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__23(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__23___rarg), 2, 0);
return x_2;
}
}
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__26(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
uint8 x_6; 
x_6 = lean::string_iterator_has_next(x_2);
if (x_6 == 0)
{
obj* x_8; 
lean::dec(x_0);
x_8 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_8;
}
else
{
uint32 x_9; uint8 x_10; 
x_9 = lean::string_iterator_curr(x_2);
x_10 = l_lean_is__id__rest(x_9);
if (x_10 == 0)
{
obj* x_12; 
lean::dec(x_0);
x_12 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_12;
}
else
{
obj* x_13; obj* x_14; obj* x_17; obj* x_18; 
x_13 = lean::mk_nat_obj(1u);
x_14 = lean::nat_sub(x_0, x_13);
lean::dec(x_13);
lean::dec(x_0);
x_17 = lean::string_push(x_1, x_9);
x_18 = lean::string_iterator_next(x_2);
x_0 = x_14;
x_1 = x_17;
x_2 = x_18;
goto _start;
}
}
}
else
{
obj* x_21; 
lean::dec(x_0);
x_21 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_21;
}
}
}
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__25___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_5; obj* x_6; 
x_2 = lean::string_iterator_remaining(x_0);
x_3 = l_string_join___closed__1;
lean::inc(x_3);
x_5 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__26(x_2, x_3, x_0);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_1);
return x_6;
}
}
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__25(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__25___rarg), 2, 0);
return x_2;
}
}
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__28(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
uint8 x_6; 
x_6 = lean::string_iterator_has_next(x_2);
if (x_6 == 0)
{
obj* x_8; 
lean::dec(x_0);
x_8 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_8;
}
else
{
uint32 x_9; uint8 x_10; 
x_9 = lean::string_iterator_curr(x_2);
x_10 = l_lean_is__id__rest(x_9);
if (x_10 == 0)
{
obj* x_12; 
lean::dec(x_0);
x_12 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_12;
}
else
{
obj* x_13; obj* x_14; obj* x_17; obj* x_18; 
x_13 = lean::mk_nat_obj(1u);
x_14 = lean::nat_sub(x_0, x_13);
lean::dec(x_13);
lean::dec(x_0);
x_17 = lean::string_push(x_1, x_9);
x_18 = lean::string_iterator_next(x_2);
x_0 = x_14;
x_1 = x_17;
x_2 = x_18;
goto _start;
}
}
}
else
{
obj* x_21; 
lean::dec(x_0);
x_21 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_21;
}
}
}
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__27___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_5; obj* x_6; 
x_2 = lean::string_iterator_remaining(x_0);
x_3 = l_string_join___closed__1;
lean::inc(x_3);
x_5 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__28(x_2, x_3, x_0);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_1);
return x_6;
}
}
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__27(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__27___rarg), 2, 0);
return x_2;
}
}
obj* l_lean_parser_combinators_choice__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__29(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_13; 
lean::dec(x_1);
lean::dec(x_0);
x_7 = lean::box(0);
x_8 = l_lean_parser_combinators_choice__aux___main___rarg___closed__1;
x_9 = l_mjoin___rarg___closed__1;
lean::inc(x_7);
lean::inc(x_9);
lean::inc(x_8);
x_13 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_8, x_9, x_7, x_7, x_2, x_3, x_4);
return x_13;
}
else
{
obj* x_14; obj* x_16; obj* x_18; obj* x_21; obj* x_22; obj* x_24; obj* x_26; obj* x_27; obj* x_28; 
x_14 = lean::cnstr_get(x_0, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_0, 1);
lean::inc(x_16);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_18 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_18 = x_0;
}
lean::inc(x_3);
lean::inc(x_2);
x_21 = lean::apply_3(x_14, x_2, x_3, x_4);
x_22 = lean::cnstr_get(x_21, 0);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_21, 1);
lean::inc(x_24);
if (lean::is_shared(x_21)) {
 lean::dec(x_21);
 x_26 = lean::box(0);
} else {
 lean::cnstr_release(x_21, 0);
 lean::cnstr_release(x_21, 1);
 x_26 = x_21;
}
x_27 = lean::mk_nat_obj(1u);
x_28 = lean::nat_add(x_1, x_27);
lean::dec(x_27);
if (lean::obj_tag(x_22) == 0)
{
obj* x_30; obj* x_32; obj* x_34; obj* x_36; obj* x_37; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_44; obj* x_45; 
x_30 = lean::cnstr_get(x_22, 0);
lean::inc(x_30);
x_32 = lean::cnstr_get(x_22, 1);
lean::inc(x_32);
x_34 = lean::cnstr_get(x_22, 2);
lean::inc(x_34);
if (lean::is_shared(x_22)) {
 lean::dec(x_22);
 x_36 = lean::box(0);
} else {
 lean::cnstr_release(x_22, 0);
 lean::cnstr_release(x_22, 1);
 lean::cnstr_release(x_22, 2);
 x_36 = x_22;
}
x_37 = lean::box(0);
lean::inc(x_37);
x_39 = lean_name_mk_numeral(x_37, x_1);
if (lean::is_scalar(x_18)) {
 x_40 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_40 = x_18;
}
lean::cnstr_set(x_40, 0, x_30);
lean::cnstr_set(x_40, 1, x_37);
x_41 = l_lean_parser_syntax_mk__node(x_39, x_40);
x_42 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_42);
if (lean::is_scalar(x_36)) {
 x_44 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_44 = x_36;
}
lean::cnstr_set(x_44, 0, x_41);
lean::cnstr_set(x_44, 1, x_32);
lean::cnstr_set(x_44, 2, x_42);
x_45 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_34, x_44);
if (lean::obj_tag(x_45) == 0)
{
obj* x_50; 
lean::dec(x_28);
lean::dec(x_3);
lean::dec(x_16);
lean::dec(x_2);
if (lean::is_scalar(x_26)) {
 x_50 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_50 = x_26;
}
lean::cnstr_set(x_50, 0, x_45);
lean::cnstr_set(x_50, 1, x_24);
return x_50;
}
else
{
obj* x_51; uint8 x_53; 
x_51 = lean::cnstr_get(x_45, 0);
lean::inc(x_51);
x_53 = lean::cnstr_get_scalar<uint8>(x_45, sizeof(void*)*1);
if (x_53 == 0)
{
obj* x_55; obj* x_56; obj* x_58; obj* x_61; obj* x_62; 
lean::dec(x_45);
x_55 = l_lean_parser_combinators_choice__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__29(x_16, x_28, x_2, x_3, x_24);
x_56 = lean::cnstr_get(x_55, 0);
lean::inc(x_56);
x_58 = lean::cnstr_get(x_55, 1);
lean::inc(x_58);
lean::dec(x_55);
x_61 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_51, x_56);
if (lean::is_scalar(x_26)) {
 x_62 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_62 = x_26;
}
lean::cnstr_set(x_62, 0, x_61);
lean::cnstr_set(x_62, 1, x_58);
return x_62;
}
else
{
obj* x_68; 
lean::dec(x_28);
lean::dec(x_3);
lean::dec(x_16);
lean::dec(x_2);
lean::dec(x_51);
if (lean::is_scalar(x_26)) {
 x_68 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_68 = x_26;
}
lean::cnstr_set(x_68, 0, x_45);
lean::cnstr_set(x_68, 1, x_24);
return x_68;
}
}
}
else
{
obj* x_71; uint8 x_73; obj* x_74; 
lean::dec(x_18);
lean::dec(x_1);
x_71 = lean::cnstr_get(x_22, 0);
lean::inc(x_71);
x_73 = lean::cnstr_get_scalar<uint8>(x_22, sizeof(void*)*1);
if (lean::is_shared(x_22)) {
 lean::dec(x_22);
 x_74 = lean::box(0);
} else {
 lean::cnstr_release(x_22, 0);
 x_74 = x_22;
}
if (x_73 == 0)
{
obj* x_76; obj* x_77; obj* x_79; obj* x_82; obj* x_83; 
lean::dec(x_74);
x_76 = l_lean_parser_combinators_choice__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__29(x_16, x_28, x_2, x_3, x_24);
x_77 = lean::cnstr_get(x_76, 0);
lean::inc(x_77);
x_79 = lean::cnstr_get(x_76, 1);
lean::inc(x_79);
lean::dec(x_76);
x_82 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_71, x_77);
if (lean::is_scalar(x_26)) {
 x_83 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_83 = x_26;
}
lean::cnstr_set(x_83, 0, x_82);
lean::cnstr_set(x_83, 1, x_79);
return x_83;
}
else
{
obj* x_88; obj* x_89; obj* x_90; 
lean::dec(x_28);
lean::dec(x_3);
lean::dec(x_16);
lean::dec(x_2);
if (lean::is_scalar(x_74)) {
 x_88 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_88 = x_74;
}
lean::cnstr_set(x_88, 0, x_71);
lean::cnstr_set_scalar(x_88, sizeof(void*)*1, x_73);
x_89 = x_88;
if (lean::is_scalar(x_26)) {
 x_90 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_90 = x_26;
}
lean::cnstr_set(x_90, 0, x_89);
lean::cnstr_set(x_90, 1, x_24);
return x_90;
}
}
}
}
}
obj* _init_l_lean_parser_detail__ident__part_parser_lean_parser_has__tokens() {
_start:
{
obj* x_0; obj* x_3; obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_0 = lean::box(0);
lean::inc(x_0);
lean::inc(x_0);
x_3 = l_lean_parser_list_cons_tokens___rarg(x_0, x_0);
lean::inc(x_3);
lean::inc(x_0);
x_6 = l_lean_parser_list_cons_tokens___rarg(x_0, x_3);
lean::inc(x_0);
x_8 = l_lean_parser_list_cons_tokens___rarg(x_0, x_6);
x_9 = l_lean_parser_tokens___rarg(x_8);
x_10 = l_lean_parser_list_cons_tokens___rarg(x_9, x_3);
x_11 = l_lean_parser_tokens___rarg(x_10);
x_12 = l_lean_parser_list_cons_tokens___rarg(x_11, x_0);
x_13 = l_lean_parser_tokens___rarg(x_12);
return x_13;
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint32 x_4; obj* x_5; 
x_4 = lean::unbox_uint32(x_0);
x_5 = l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__2(x_4, x_1, x_2, x_3);
return x_5;
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__6___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint32 x_4; obj* x_5; 
x_4 = lean::unbox_uint32(x_0);
x_5 = l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__6(x_4, x_1, x_2, x_3);
return x_5;
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__9___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint32 x_4; obj* x_5; 
x_4 = lean::unbox_uint32(x_0);
x_5 = l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__9(x_4, x_1, x_2, x_3);
return x_5;
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__13___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint32 x_4; obj* x_5; 
x_4 = lean::unbox_uint32(x_0);
x_5 = l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__13(x_4, x_1, x_2, x_3);
return x_5;
}
}
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
uint8 x_6; 
x_6 = lean::string_iterator_has_next(x_2);
if (x_6 == 0)
{
obj* x_8; 
lean::dec(x_0);
x_8 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_8;
}
else
{
uint32 x_9; uint8 x_10; 
x_9 = lean::string_iterator_curr(x_2);
x_10 = l_lean_is__id__end__escape(x_9);
if (x_10 == 0)
{
obj* x_11; obj* x_12; obj* x_15; obj* x_16; 
x_11 = lean::mk_nat_obj(1u);
x_12 = lean::nat_sub(x_0, x_11);
lean::dec(x_11);
lean::dec(x_0);
x_15 = lean::string_push(x_1, x_9);
x_16 = lean::string_iterator_next(x_2);
x_0 = x_12;
x_1 = x_15;
x_2 = x_16;
goto _start;
}
else
{
obj* x_19; 
lean::dec(x_0);
x_19 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_19;
}
}
}
else
{
obj* x_21; 
lean::dec(x_0);
x_21 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_21;
}
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__2(uint32 x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
lean::dec(x_1);
x_5 = l_string_join___closed__1;
lean::inc(x_5);
x_7 = lean::string_push(x_5, x_0);
x_8 = lean::string_iterator_remaining(x_2);
x_9 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__3(x_8, x_7, x_2);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_3);
return x_10;
}
}
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__5(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
uint8 x_6; 
x_6 = lean::string_iterator_has_next(x_2);
if (x_6 == 0)
{
obj* x_8; 
lean::dec(x_0);
x_8 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_8;
}
else
{
uint32 x_9; uint8 x_10; 
x_9 = lean::string_iterator_curr(x_2);
x_10 = l_lean_is__id__end__escape(x_9);
if (x_10 == 0)
{
obj* x_11; obj* x_12; obj* x_15; obj* x_16; 
x_11 = lean::mk_nat_obj(1u);
x_12 = lean::nat_sub(x_0, x_11);
lean::dec(x_11);
lean::dec(x_0);
x_15 = lean::string_push(x_1, x_9);
x_16 = lean::string_iterator_next(x_2);
x_0 = x_12;
x_1 = x_15;
x_2 = x_16;
goto _start;
}
else
{
obj* x_19; 
lean::dec(x_0);
x_19 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_19;
}
}
}
else
{
obj* x_21; 
lean::dec(x_0);
x_21 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_21;
}
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__4(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint32 x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
lean::dec(x_1);
x_5 = lean::string_iterator_curr(x_0);
lean::dec(x_0);
x_7 = l_string_join___closed__1;
lean::inc(x_7);
x_9 = lean::string_push(x_7, x_5);
x_10 = lean::string_iterator_remaining(x_2);
x_11 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__5(x_10, x_9, x_2);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_3);
return x_12;
}
}
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__7(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
uint8 x_6; 
x_6 = lean::string_iterator_has_next(x_2);
if (x_6 == 0)
{
obj* x_8; 
lean::dec(x_0);
x_8 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_8;
}
else
{
uint32 x_9; uint8 x_10; 
x_9 = lean::string_iterator_curr(x_2);
x_10 = l_lean_is__id__end__escape(x_9);
if (x_10 == 0)
{
obj* x_11; obj* x_12; obj* x_15; obj* x_16; 
x_11 = lean::mk_nat_obj(1u);
x_12 = lean::nat_sub(x_0, x_11);
lean::dec(x_11);
lean::dec(x_0);
x_15 = lean::string_push(x_1, x_9);
x_16 = lean::string_iterator_next(x_2);
x_0 = x_12;
x_1 = x_15;
x_2 = x_16;
goto _start;
}
else
{
obj* x_19; 
lean::dec(x_0);
x_19 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_19;
}
}
}
else
{
obj* x_21; 
lean::dec(x_0);
x_21 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_21;
}
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__6(uint32 x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
lean::dec(x_1);
x_5 = l_string_join___closed__1;
lean::inc(x_5);
x_7 = lean::string_push(x_5, x_0);
x_8 = lean::string_iterator_remaining(x_2);
x_9 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__7(x_8, x_7, x_2);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_3);
return x_10;
}
}
obj* l_lean_parser_monad__parsec_take__while1___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = lean::string_iterator_has_next(x_1);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; obj* x_11; obj* x_12; obj* x_14; obj* x_16; obj* x_17; obj* x_19; 
x_4 = lean::box(0);
x_5 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_6 = l_mjoin___rarg___closed__1;
lean::inc(x_0);
lean::inc(x_4);
lean::inc(x_6);
lean::inc(x_5);
x_11 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_5, x_6, x_4, x_4, x_0, x_1, x_2);
x_12 = lean::cnstr_get(x_11, 0);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_11, 1);
lean::inc(x_14);
if (lean::is_shared(x_11)) {
 lean::dec(x_11);
 x_16 = lean::box(0);
} else {
 lean::cnstr_release(x_11, 0);
 lean::cnstr_release(x_11, 1);
 x_16 = x_11;
}
x_17 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_17);
x_19 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_17, x_12);
if (lean::obj_tag(x_19) == 0)
{
obj* x_20; obj* x_22; obj* x_24; uint32 x_27; obj* x_29; obj* x_30; obj* x_32; obj* x_35; obj* x_36; 
x_20 = lean::cnstr_get(x_19, 0);
lean::inc(x_20);
x_22 = lean::cnstr_get(x_19, 1);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_19, 2);
lean::inc(x_24);
lean::dec(x_19);
x_27 = lean::unbox_uint32(x_20);
lean::dec(x_20);
x_29 = l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__2(x_27, x_0, x_22, x_14);
x_30 = lean::cnstr_get(x_29, 0);
lean::inc(x_30);
x_32 = lean::cnstr_get(x_29, 1);
lean::inc(x_32);
lean::dec(x_29);
x_35 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_24, x_30);
if (lean::is_scalar(x_16)) {
 x_36 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_36 = x_16;
}
lean::cnstr_set(x_36, 0, x_35);
lean::cnstr_set(x_36, 1, x_32);
return x_36;
}
else
{
obj* x_38; uint8 x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; 
lean::dec(x_0);
x_38 = lean::cnstr_get(x_19, 0);
lean::inc(x_38);
x_40 = lean::cnstr_get_scalar<uint8>(x_19, sizeof(void*)*1);
if (lean::is_shared(x_19)) {
 lean::dec(x_19);
 x_41 = lean::box(0);
} else {
 lean::cnstr_release(x_19, 0);
 x_41 = x_19;
}
if (lean::is_scalar(x_41)) {
 x_42 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_42 = x_41;
}
lean::cnstr_set(x_42, 0, x_38);
lean::cnstr_set_scalar(x_42, sizeof(void*)*1, x_40);
x_43 = x_42;
if (lean::is_scalar(x_16)) {
 x_44 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_44 = x_16;
}
lean::cnstr_set(x_44, 0, x_43);
lean::cnstr_set(x_44, 1, x_14);
return x_44;
}
}
else
{
uint32 x_45; uint8 x_46; 
x_45 = lean::string_iterator_curr(x_1);
x_46 = l_lean_is__id__end__escape(x_45);
if (x_46 == 0)
{
obj* x_48; obj* x_49; obj* x_50; obj* x_52; obj* x_54; obj* x_55; obj* x_56; obj* x_57; 
lean::inc(x_1);
x_48 = lean::string_iterator_next(x_1);
x_49 = l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__4(x_1, x_0, x_48, x_2);
x_50 = lean::cnstr_get(x_49, 0);
lean::inc(x_50);
x_52 = lean::cnstr_get(x_49, 1);
lean::inc(x_52);
if (lean::is_shared(x_49)) {
 lean::dec(x_49);
 x_54 = lean::box(0);
} else {
 lean::cnstr_release(x_49, 0);
 lean::cnstr_release(x_49, 1);
 x_54 = x_49;
}
x_55 = lean::box(0);
x_56 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_55, x_50);
if (lean::is_scalar(x_54)) {
 x_57 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_57 = x_54;
}
lean::cnstr_set(x_57, 0, x_56);
lean::cnstr_set(x_57, 1, x_52);
return x_57;
}
else
{
obj* x_58; obj* x_59; obj* x_61; obj* x_63; obj* x_64; obj* x_65; obj* x_69; obj* x_70; obj* x_72; obj* x_74; obj* x_75; obj* x_77; 
x_58 = l_char_quote__core(x_45);
x_59 = l_char_has__repr___closed__1;
lean::inc(x_59);
x_61 = lean::string_append(x_59, x_58);
lean::dec(x_58);
x_63 = lean::string_append(x_61, x_59);
x_64 = lean::box(0);
x_65 = l_mjoin___rarg___closed__1;
lean::inc(x_0);
lean::inc(x_64);
lean::inc(x_65);
x_69 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_63, x_65, x_64, x_64, x_0, x_1, x_2);
x_70 = lean::cnstr_get(x_69, 0);
lean::inc(x_70);
x_72 = lean::cnstr_get(x_69, 1);
lean::inc(x_72);
if (lean::is_shared(x_69)) {
 lean::dec(x_69);
 x_74 = lean::box(0);
} else {
 lean::cnstr_release(x_69, 0);
 lean::cnstr_release(x_69, 1);
 x_74 = x_69;
}
x_75 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_75);
x_77 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_75, x_70);
if (lean::obj_tag(x_77) == 0)
{
obj* x_78; obj* x_80; obj* x_82; uint32 x_85; obj* x_87; obj* x_88; obj* x_90; obj* x_93; obj* x_94; 
x_78 = lean::cnstr_get(x_77, 0);
lean::inc(x_78);
x_80 = lean::cnstr_get(x_77, 1);
lean::inc(x_80);
x_82 = lean::cnstr_get(x_77, 2);
lean::inc(x_82);
lean::dec(x_77);
x_85 = lean::unbox_uint32(x_78);
lean::dec(x_78);
x_87 = l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__6(x_85, x_0, x_80, x_72);
x_88 = lean::cnstr_get(x_87, 0);
lean::inc(x_88);
x_90 = lean::cnstr_get(x_87, 1);
lean::inc(x_90);
lean::dec(x_87);
x_93 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_82, x_88);
if (lean::is_scalar(x_74)) {
 x_94 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_94 = x_74;
}
lean::cnstr_set(x_94, 0, x_93);
lean::cnstr_set(x_94, 1, x_90);
return x_94;
}
else
{
obj* x_96; uint8 x_98; obj* x_99; obj* x_100; obj* x_101; obj* x_102; 
lean::dec(x_0);
x_96 = lean::cnstr_get(x_77, 0);
lean::inc(x_96);
x_98 = lean::cnstr_get_scalar<uint8>(x_77, sizeof(void*)*1);
if (lean::is_shared(x_77)) {
 lean::dec(x_77);
 x_99 = lean::box(0);
} else {
 lean::cnstr_release(x_77, 0);
 x_99 = x_77;
}
if (lean::is_scalar(x_99)) {
 x_100 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_100 = x_99;
}
lean::cnstr_set(x_100, 0, x_96);
lean::cnstr_set_scalar(x_100, sizeof(void*)*1, x_98);
x_101 = x_100;
if (lean::is_scalar(x_74)) {
 x_102 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_102 = x_74;
}
lean::cnstr_set(x_102, 0, x_101);
lean::cnstr_set(x_102, 1, x_72);
return x_102;
}
}
}
}
}
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__9(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
uint8 x_6; 
x_6 = lean::string_iterator_has_next(x_2);
if (x_6 == 0)
{
obj* x_8; 
lean::dec(x_0);
x_8 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_8;
}
else
{
uint32 x_9; uint8 x_10; 
x_9 = lean::string_iterator_curr(x_2);
x_10 = l_lean_is__id__rest(x_9);
if (x_10 == 0)
{
obj* x_12; 
lean::dec(x_0);
x_12 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_12;
}
else
{
obj* x_13; obj* x_14; obj* x_17; obj* x_18; 
x_13 = lean::mk_nat_obj(1u);
x_14 = lean::nat_sub(x_0, x_13);
lean::dec(x_13);
lean::dec(x_0);
x_17 = lean::string_push(x_1, x_9);
x_18 = lean::string_iterator_next(x_2);
x_0 = x_14;
x_1 = x_17;
x_2 = x_18;
goto _start;
}
}
}
else
{
obj* x_21; 
lean::dec(x_0);
x_21 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_21;
}
}
}
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__8___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_5; obj* x_6; 
x_2 = lean::string_iterator_remaining(x_0);
x_3 = l_string_join___closed__1;
lean::inc(x_3);
x_5 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__9(x_2, x_3, x_0);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_1);
return x_6;
}
}
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__8(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__8___rarg), 2, 0);
return x_2;
}
}
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__11(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
uint8 x_6; 
x_6 = lean::string_iterator_has_next(x_2);
if (x_6 == 0)
{
obj* x_8; 
lean::dec(x_0);
x_8 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_8;
}
else
{
uint32 x_9; uint8 x_10; 
x_9 = lean::string_iterator_curr(x_2);
x_10 = l_lean_is__id__rest(x_9);
if (x_10 == 0)
{
obj* x_12; 
lean::dec(x_0);
x_12 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_12;
}
else
{
obj* x_13; obj* x_14; obj* x_17; obj* x_18; 
x_13 = lean::mk_nat_obj(1u);
x_14 = lean::nat_sub(x_0, x_13);
lean::dec(x_13);
lean::dec(x_0);
x_17 = lean::string_push(x_1, x_9);
x_18 = lean::string_iterator_next(x_2);
x_0 = x_14;
x_1 = x_17;
x_2 = x_18;
goto _start;
}
}
}
else
{
obj* x_21; 
lean::dec(x_0);
x_21 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_21;
}
}
}
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__10___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_5; obj* x_6; 
x_2 = lean::string_iterator_remaining(x_0);
x_3 = l_string_join___closed__1;
lean::inc(x_3);
x_5 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__11(x_2, x_3, x_0);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_1);
return x_6;
}
}
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__10(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__10___rarg), 2, 0);
return x_2;
}
}
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__13(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
uint8 x_6; 
x_6 = lean::string_iterator_has_next(x_2);
if (x_6 == 0)
{
obj* x_8; 
lean::dec(x_0);
x_8 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_8;
}
else
{
uint32 x_9; uint8 x_10; 
x_9 = lean::string_iterator_curr(x_2);
x_10 = l_lean_is__id__rest(x_9);
if (x_10 == 0)
{
obj* x_12; 
lean::dec(x_0);
x_12 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_12;
}
else
{
obj* x_13; obj* x_14; obj* x_17; obj* x_18; 
x_13 = lean::mk_nat_obj(1u);
x_14 = lean::nat_sub(x_0, x_13);
lean::dec(x_13);
lean::dec(x_0);
x_17 = lean::string_push(x_1, x_9);
x_18 = lean::string_iterator_next(x_2);
x_0 = x_14;
x_1 = x_17;
x_2 = x_18;
goto _start;
}
}
}
else
{
obj* x_21; 
lean::dec(x_0);
x_21 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_21;
}
}
}
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__12___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_5; obj* x_6; 
x_2 = lean::string_iterator_remaining(x_0);
x_3 = l_string_join___closed__1;
lean::inc(x_3);
x_5 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__13(x_2, x_3, x_0);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_1);
return x_6;
}
}
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__12(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__12___rarg), 2, 0);
return x_2;
}
}
obj* l_lean_parser_detail__ident__part_parser_lean_parser_has__view___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_9; obj* x_11; 
x_6 = l_lean_parser_monad__parsec_str__core___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__3(x_0, x_1, x_3, x_4, x_5);
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_6, 1);
lean::inc(x_9);
if (lean::is_shared(x_6)) {
 lean::dec(x_6);
 x_11 = lean::box(0);
} else {
 lean::cnstr_release(x_6, 0);
 lean::cnstr_release(x_6, 1);
 x_11 = x_6;
}
if (lean::obj_tag(x_7) == 0)
{
obj* x_12; obj* x_14; obj* x_16; obj* x_18; obj* x_19; obj* x_21; obj* x_22; obj* x_23; 
x_12 = lean::cnstr_get(x_7, 1);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_7, 2);
lean::inc(x_14);
if (lean::is_shared(x_7)) {
 lean::dec(x_7);
 x_16 = lean::box(0);
} else {
 lean::cnstr_release(x_7, 0);
 lean::cnstr_release(x_7, 1);
 lean::cnstr_release(x_7, 2);
 x_16 = x_7;
}
lean::inc(x_12);
x_18 = l_lean_parser_mk__raw__res(x_2, x_12);
x_19 = l_lean_parser_finish__comment__block___closed__2;
lean::inc(x_19);
if (lean::is_scalar(x_16)) {
 x_21 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_21 = x_16;
}
lean::cnstr_set(x_21, 0, x_18);
lean::cnstr_set(x_21, 1, x_12);
lean::cnstr_set(x_21, 2, x_19);
x_22 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_14, x_21);
if (lean::is_scalar(x_11)) {
 x_23 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_23 = x_11;
}
lean::cnstr_set(x_23, 0, x_22);
lean::cnstr_set(x_23, 1, x_9);
return x_23;
}
else
{
obj* x_25; uint8 x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; 
lean::dec(x_2);
x_25 = lean::cnstr_get(x_7, 0);
lean::inc(x_25);
x_27 = lean::cnstr_get_scalar<uint8>(x_7, sizeof(void*)*1);
if (lean::is_shared(x_7)) {
 lean::dec(x_7);
 x_28 = lean::box(0);
} else {
 lean::cnstr_release(x_7, 0);
 x_28 = x_7;
}
if (lean::is_scalar(x_28)) {
 x_29 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_29 = x_28;
}
lean::cnstr_set(x_29, 0, x_25);
lean::cnstr_set_scalar(x_29, sizeof(void*)*1, x_27);
x_30 = x_29;
if (lean::is_scalar(x_11)) {
 x_31 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_31 = x_11;
}
lean::cnstr_set(x_31, 0, x_30);
lean::cnstr_set(x_31, 1, x_9);
return x_31;
}
}
}
obj* l_lean_parser_detail__ident__part_parser_lean_parser_has__view___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_7; obj* x_9; 
x_4 = l_lean_parser_monad__parsec_take__while1___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__1(x_1, x_2, x_3);
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
obj* x_10; obj* x_12; obj* x_14; obj* x_16; obj* x_17; obj* x_19; obj* x_20; obj* x_21; 
x_10 = lean::cnstr_get(x_5, 1);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_5, 2);
lean::inc(x_12);
if (lean::is_shared(x_5)) {
 lean::dec(x_5);
 x_14 = lean::box(0);
} else {
 lean::cnstr_release(x_5, 0);
 lean::cnstr_release(x_5, 1);
 lean::cnstr_release(x_5, 2);
 x_14 = x_5;
}
lean::inc(x_10);
x_16 = l_lean_parser_mk__raw__res(x_0, x_10);
x_17 = l_lean_parser_finish__comment__block___closed__2;
lean::inc(x_17);
if (lean::is_scalar(x_14)) {
 x_19 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_19 = x_14;
}
lean::cnstr_set(x_19, 0, x_16);
lean::cnstr_set(x_19, 1, x_10);
lean::cnstr_set(x_19, 2, x_17);
x_20 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_12, x_19);
if (lean::is_scalar(x_9)) {
 x_21 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_21 = x_9;
}
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_7);
return x_21;
}
else
{
obj* x_23; uint8 x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
lean::dec(x_0);
x_23 = lean::cnstr_get(x_5, 0);
lean::inc(x_23);
x_25 = lean::cnstr_get_scalar<uint8>(x_5, sizeof(void*)*1);
if (lean::is_shared(x_5)) {
 lean::dec(x_5);
 x_26 = lean::box(0);
} else {
 lean::cnstr_release(x_5, 0);
 x_26 = x_5;
}
if (lean::is_scalar(x_26)) {
 x_27 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_27 = x_26;
}
lean::cnstr_set(x_27, 0, x_23);
lean::cnstr_set_scalar(x_27, sizeof(void*)*1, x_25);
x_28 = x_27;
if (lean::is_scalar(x_9)) {
 x_29 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_29 = x_9;
}
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_7);
return x_29;
}
}
}
obj* l_lean_parser_detail__ident__part_parser_lean_parser_has__view___lambda__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; uint8 x_7; 
x_7 = lean::string_iterator_has_next(x_2);
if (x_7 == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_14; obj* x_15; obj* x_17; obj* x_20; obj* x_22; 
x_8 = lean::box(0);
x_9 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_10 = l_mjoin___rarg___closed__1;
lean::inc(x_8);
lean::inc(x_10);
lean::inc(x_9);
x_14 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_9, x_10, x_8, x_8, x_1, x_2, x_3);
x_15 = lean::cnstr_get(x_14, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_14, 1);
lean::inc(x_17);
lean::dec(x_14);
x_20 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_20);
x_22 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_20, x_15);
if (lean::obj_tag(x_22) == 0)
{
obj* x_23; obj* x_25; obj* x_28; obj* x_29; obj* x_31; obj* x_34; 
x_23 = lean::cnstr_get(x_22, 1);
lean::inc(x_23);
x_25 = lean::cnstr_get(x_22, 2);
lean::inc(x_25);
lean::dec(x_22);
x_28 = l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__8___rarg(x_23, x_17);
x_29 = lean::cnstr_get(x_28, 0);
lean::inc(x_29);
x_31 = lean::cnstr_get(x_28, 1);
lean::inc(x_31);
lean::dec(x_28);
x_34 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_25, x_29);
x_4 = x_34;
x_5 = x_31;
goto lbl_6;
}
else
{
obj* x_35; uint8 x_37; obj* x_38; obj* x_39; obj* x_40; 
x_35 = lean::cnstr_get(x_22, 0);
lean::inc(x_35);
x_37 = lean::cnstr_get_scalar<uint8>(x_22, sizeof(void*)*1);
if (lean::is_shared(x_22)) {
 lean::dec(x_22);
 x_38 = lean::box(0);
} else {
 lean::cnstr_release(x_22, 0);
 x_38 = x_22;
}
if (lean::is_scalar(x_38)) {
 x_39 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_39 = x_38;
}
lean::cnstr_set(x_39, 0, x_35);
lean::cnstr_set_scalar(x_39, sizeof(void*)*1, x_37);
x_40 = x_39;
x_4 = x_40;
x_5 = x_17;
goto lbl_6;
}
}
else
{
uint32 x_41; uint8 x_42; 
x_41 = lean::string_iterator_curr(x_2);
x_42 = l_lean_is__id__first(x_41);
if (x_42 == 0)
{
obj* x_43; obj* x_44; obj* x_46; obj* x_48; obj* x_49; obj* x_50; obj* x_53; obj* x_54; obj* x_56; obj* x_59; obj* x_61; 
x_43 = l_char_quote__core(x_41);
x_44 = l_char_has__repr___closed__1;
lean::inc(x_44);
x_46 = lean::string_append(x_44, x_43);
lean::dec(x_43);
x_48 = lean::string_append(x_46, x_44);
x_49 = lean::box(0);
x_50 = l_mjoin___rarg___closed__1;
lean::inc(x_49);
lean::inc(x_50);
x_53 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_48, x_50, x_49, x_49, x_1, x_2, x_3);
x_54 = lean::cnstr_get(x_53, 0);
lean::inc(x_54);
x_56 = lean::cnstr_get(x_53, 1);
lean::inc(x_56);
lean::dec(x_53);
x_59 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_59);
x_61 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_59, x_54);
if (lean::obj_tag(x_61) == 0)
{
obj* x_62; obj* x_64; obj* x_67; obj* x_68; obj* x_70; obj* x_73; 
x_62 = lean::cnstr_get(x_61, 1);
lean::inc(x_62);
x_64 = lean::cnstr_get(x_61, 2);
lean::inc(x_64);
lean::dec(x_61);
x_67 = l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__10___rarg(x_62, x_56);
x_68 = lean::cnstr_get(x_67, 0);
lean::inc(x_68);
x_70 = lean::cnstr_get(x_67, 1);
lean::inc(x_70);
lean::dec(x_67);
x_73 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_64, x_68);
x_4 = x_73;
x_5 = x_70;
goto lbl_6;
}
else
{
obj* x_74; uint8 x_76; obj* x_77; obj* x_78; obj* x_79; 
x_74 = lean::cnstr_get(x_61, 0);
lean::inc(x_74);
x_76 = lean::cnstr_get_scalar<uint8>(x_61, sizeof(void*)*1);
if (lean::is_shared(x_61)) {
 lean::dec(x_61);
 x_77 = lean::box(0);
} else {
 lean::cnstr_release(x_61, 0);
 x_77 = x_61;
}
if (lean::is_scalar(x_77)) {
 x_78 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_78 = x_77;
}
lean::cnstr_set(x_78, 0, x_74);
lean::cnstr_set_scalar(x_78, sizeof(void*)*1, x_76);
x_79 = x_78;
x_4 = x_79;
x_5 = x_56;
goto lbl_6;
}
}
else
{
obj* x_81; obj* x_82; obj* x_83; obj* x_85; obj* x_88; obj* x_89; 
lean::dec(x_1);
x_81 = lean::string_iterator_next(x_2);
x_82 = l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__12___rarg(x_81, x_3);
x_83 = lean::cnstr_get(x_82, 0);
lean::inc(x_83);
x_85 = lean::cnstr_get(x_82, 1);
lean::inc(x_85);
lean::dec(x_82);
x_88 = lean::box(0);
x_89 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_88, x_83);
x_4 = x_89;
x_5 = x_85;
goto lbl_6;
}
}
lbl_6:
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_90; obj* x_92; obj* x_94; obj* x_96; obj* x_97; obj* x_99; obj* x_100; obj* x_101; 
x_90 = lean::cnstr_get(x_4, 1);
lean::inc(x_90);
x_92 = lean::cnstr_get(x_4, 2);
lean::inc(x_92);
if (lean::is_shared(x_4)) {
 lean::dec(x_4);
 x_94 = lean::box(0);
} else {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_release(x_4, 1);
 lean::cnstr_release(x_4, 2);
 x_94 = x_4;
}
lean::inc(x_90);
x_96 = l_lean_parser_mk__raw__res(x_0, x_90);
x_97 = l_lean_parser_finish__comment__block___closed__2;
lean::inc(x_97);
if (lean::is_scalar(x_94)) {
 x_99 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_99 = x_94;
}
lean::cnstr_set(x_99, 0, x_96);
lean::cnstr_set(x_99, 1, x_90);
lean::cnstr_set(x_99, 2, x_97);
x_100 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_92, x_99);
x_101 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_101, 0, x_100);
lean::cnstr_set(x_101, 1, x_5);
return x_101;
}
else
{
obj* x_103; uint8 x_105; obj* x_106; obj* x_107; obj* x_108; obj* x_109; 
lean::dec(x_0);
x_103 = lean::cnstr_get(x_4, 0);
lean::inc(x_103);
x_105 = lean::cnstr_get_scalar<uint8>(x_4, sizeof(void*)*1);
if (lean::is_shared(x_4)) {
 lean::dec(x_4);
 x_106 = lean::box(0);
} else {
 lean::cnstr_release(x_4, 0);
 x_106 = x_4;
}
if (lean::is_scalar(x_106)) {
 x_107 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_107 = x_106;
}
lean::cnstr_set(x_107, 0, x_103);
lean::cnstr_set_scalar(x_107, sizeof(void*)*1, x_105);
x_108 = x_107;
x_109 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_109, 0, x_108);
lean::cnstr_set(x_109, 1, x_5);
return x_109;
}
}
}
}
obj* _init_l_lean_parser_detail__ident__part_parser_lean_parser_has__view() {
_start:
{
obj* x_0; obj* x_1; uint32 x_2; obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_12; obj* x_13; obj* x_15; obj* x_16; uint32 x_17; obj* x_18; obj* x_20; obj* x_21; obj* x_22; obj* x_24; obj* x_25; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_32; obj* x_33; obj* x_34; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_53; 
x_0 = lean::mk_string("");
x_1 = l_lean_id__begin__escape;
x_2 = lean::unbox_uint32(x_1);
lean::inc(x_0);
x_4 = lean::string_push(x_0, x_2);
lean::inc(x_4);
x_6 = l_string_quote(x_4);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_7, 0, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_with__trailing___rarg___lambda__1), 2, 0);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_lift___at_lean_parser_with__trailing___spec__1___rarg), 4, 1);
lean::closure_set(x_9, 0, x_8);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_detail__ident__part_parser_lean_parser_has__view___lambda__1), 6, 2);
lean::closure_set(x_10, 0, x_4);
lean::closure_set(x_10, 1, x_7);
lean::inc(x_9);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_bind___at_lean_parser_with__trailing___spec__2___rarg), 5, 2);
lean::closure_set(x_12, 0, x_9);
lean::closure_set(x_12, 1, x_10);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_detail__ident__part_parser_lean_parser_has__view___lambda__2), 4, 0);
lean::inc(x_9);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_bind___at_lean_parser_with__trailing___spec__2___rarg), 5, 2);
lean::closure_set(x_15, 0, x_9);
lean::closure_set(x_15, 1, x_13);
x_16 = l_lean_id__end__escape;
x_17 = lean::unbox_uint32(x_16);
x_18 = lean::string_push(x_0, x_17);
lean::inc(x_18);
x_20 = l_string_quote(x_18);
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_21, 0, x_20);
x_22 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_detail__ident__part_parser_lean_parser_has__view___lambda__1), 6, 2);
lean::closure_set(x_22, 0, x_18);
lean::closure_set(x_22, 1, x_21);
lean::inc(x_9);
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_bind___at_lean_parser_with__trailing___spec__2___rarg), 5, 2);
lean::closure_set(x_24, 0, x_9);
lean::closure_set(x_24, 1, x_22);
x_25 = lean::box(0);
lean::inc(x_25);
x_27 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_27, 0, x_24);
lean::cnstr_set(x_27, 1, x_25);
x_28 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_28, 0, x_15);
lean::cnstr_set(x_28, 1, x_27);
x_29 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_29, 0, x_12);
lean::cnstr_set(x_29, 1, x_28);
x_30 = l_lean_parser_detail__ident__part__escaped;
lean::inc(x_30);
x_32 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__15), 5, 2);
lean::closure_set(x_32, 0, x_30);
lean::closure_set(x_32, 1, x_29);
x_33 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_detail__ident__part_parser_lean_parser_has__view___lambda__3), 4, 0);
x_34 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_bind___at_lean_parser_with__trailing___spec__2___rarg), 5, 2);
lean::closure_set(x_34, 0, x_9);
lean::closure_set(x_34, 1, x_33);
lean::inc(x_25);
x_36 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_36, 0, x_34);
lean::cnstr_set(x_36, 1, x_25);
x_37 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_37, 0, x_32);
lean::cnstr_set(x_37, 1, x_36);
x_38 = lean::mk_nat_obj(0u);
x_39 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_choice__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__29), 5, 2);
lean::closure_set(x_39, 0, x_37);
lean::closure_set(x_39, 1, x_38);
x_40 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_40, 0, x_39);
lean::cnstr_set(x_40, 1, x_25);
x_41 = l_lean_parser_basic__parser__m_monad;
x_42 = l_lean_parser_basic__parser__m_monad__except;
x_43 = l_lean_parser_basic__parser__m_lean_parser_monad__parsec;
x_44 = l_lean_parser_basic__parser__m_alternative;
x_45 = l_lean_parser_detail__ident__part;
x_46 = l_lean_parser_detail__ident__part_has__view;
lean::inc(x_46);
lean::inc(x_45);
lean::inc(x_44);
lean::inc(x_43);
lean::inc(x_42);
lean::inc(x_41);
x_53 = l_lean_parser_combinators_node_view___rarg(x_41, x_42, x_43, x_44, x_45, x_40, x_46);
return x_53;
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint32 x_4; obj* x_5; 
x_4 = lean::unbox_uint32(x_0);
x_5 = l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__2(x_4, x_1, x_2, x_3);
return x_5;
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__6___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint32 x_4; obj* x_5; 
x_4 = lean::unbox_uint32(x_0);
x_5 = l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__6(x_4, x_1, x_2, x_3);
return x_5;
}
}
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
uint8 x_6; 
x_6 = lean::string_iterator_has_next(x_2);
if (x_6 == 0)
{
obj* x_8; 
lean::dec(x_0);
x_8 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_8;
}
else
{
uint32 x_9; uint8 x_10; 
x_9 = lean::string_iterator_curr(x_2);
x_10 = l_lean_is__id__end__escape(x_9);
if (x_10 == 0)
{
obj* x_11; obj* x_12; obj* x_15; obj* x_16; 
x_11 = lean::mk_nat_obj(1u);
x_12 = lean::nat_sub(x_0, x_11);
lean::dec(x_11);
lean::dec(x_0);
x_15 = lean::string_push(x_1, x_9);
x_16 = lean::string_iterator_next(x_2);
x_0 = x_12;
x_1 = x_15;
x_2 = x_16;
goto _start;
}
else
{
obj* x_19; 
lean::dec(x_0);
x_19 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_19;
}
}
}
else
{
obj* x_21; 
lean::dec(x_0);
x_21 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_21;
}
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser___spec__2(uint32 x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
lean::dec(x_1);
x_5 = l_string_join___closed__1;
lean::inc(x_5);
x_7 = lean::string_push(x_5, x_0);
x_8 = lean::string_iterator_remaining(x_2);
x_9 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser___spec__3(x_8, x_7, x_2);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_3);
return x_10;
}
}
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser___spec__5(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
uint8 x_6; 
x_6 = lean::string_iterator_has_next(x_2);
if (x_6 == 0)
{
obj* x_8; 
lean::dec(x_0);
x_8 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_8;
}
else
{
uint32 x_9; uint8 x_10; 
x_9 = lean::string_iterator_curr(x_2);
x_10 = l_lean_is__id__end__escape(x_9);
if (x_10 == 0)
{
obj* x_11; obj* x_12; obj* x_15; obj* x_16; 
x_11 = lean::mk_nat_obj(1u);
x_12 = lean::nat_sub(x_0, x_11);
lean::dec(x_11);
lean::dec(x_0);
x_15 = lean::string_push(x_1, x_9);
x_16 = lean::string_iterator_next(x_2);
x_0 = x_12;
x_1 = x_15;
x_2 = x_16;
goto _start;
}
else
{
obj* x_19; 
lean::dec(x_0);
x_19 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_19;
}
}
}
else
{
obj* x_21; 
lean::dec(x_0);
x_21 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_21;
}
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser___spec__4(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint32 x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
lean::dec(x_1);
x_5 = lean::string_iterator_curr(x_0);
lean::dec(x_0);
x_7 = l_string_join___closed__1;
lean::inc(x_7);
x_9 = lean::string_push(x_7, x_5);
x_10 = lean::string_iterator_remaining(x_2);
x_11 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser___spec__5(x_10, x_9, x_2);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_3);
return x_12;
}
}
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser___spec__7(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
uint8 x_6; 
x_6 = lean::string_iterator_has_next(x_2);
if (x_6 == 0)
{
obj* x_8; 
lean::dec(x_0);
x_8 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_8;
}
else
{
uint32 x_9; uint8 x_10; 
x_9 = lean::string_iterator_curr(x_2);
x_10 = l_lean_is__id__end__escape(x_9);
if (x_10 == 0)
{
obj* x_11; obj* x_12; obj* x_15; obj* x_16; 
x_11 = lean::mk_nat_obj(1u);
x_12 = lean::nat_sub(x_0, x_11);
lean::dec(x_11);
lean::dec(x_0);
x_15 = lean::string_push(x_1, x_9);
x_16 = lean::string_iterator_next(x_2);
x_0 = x_12;
x_1 = x_15;
x_2 = x_16;
goto _start;
}
else
{
obj* x_19; 
lean::dec(x_0);
x_19 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_19;
}
}
}
else
{
obj* x_21; 
lean::dec(x_0);
x_21 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_21;
}
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser___spec__6(uint32 x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
lean::dec(x_1);
x_5 = l_string_join___closed__1;
lean::inc(x_5);
x_7 = lean::string_push(x_5, x_0);
x_8 = lean::string_iterator_remaining(x_2);
x_9 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser___spec__7(x_8, x_7, x_2);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_3);
return x_10;
}
}
obj* l_lean_parser_monad__parsec_take__while1___at_lean_parser_detail__ident__part_parser___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = lean::string_iterator_has_next(x_1);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; obj* x_11; obj* x_12; obj* x_14; obj* x_16; obj* x_17; obj* x_19; 
x_4 = lean::box(0);
x_5 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_6 = l_mjoin___rarg___closed__1;
lean::inc(x_0);
lean::inc(x_4);
lean::inc(x_6);
lean::inc(x_5);
x_11 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_5, x_6, x_4, x_4, x_0, x_1, x_2);
x_12 = lean::cnstr_get(x_11, 0);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_11, 1);
lean::inc(x_14);
if (lean::is_shared(x_11)) {
 lean::dec(x_11);
 x_16 = lean::box(0);
} else {
 lean::cnstr_release(x_11, 0);
 lean::cnstr_release(x_11, 1);
 x_16 = x_11;
}
x_17 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_17);
x_19 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_17, x_12);
if (lean::obj_tag(x_19) == 0)
{
obj* x_20; obj* x_22; obj* x_24; uint32 x_27; obj* x_29; obj* x_30; obj* x_32; obj* x_35; obj* x_36; 
x_20 = lean::cnstr_get(x_19, 0);
lean::inc(x_20);
x_22 = lean::cnstr_get(x_19, 1);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_19, 2);
lean::inc(x_24);
lean::dec(x_19);
x_27 = lean::unbox_uint32(x_20);
lean::dec(x_20);
x_29 = l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser___spec__2(x_27, x_0, x_22, x_14);
x_30 = lean::cnstr_get(x_29, 0);
lean::inc(x_30);
x_32 = lean::cnstr_get(x_29, 1);
lean::inc(x_32);
lean::dec(x_29);
x_35 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_24, x_30);
if (lean::is_scalar(x_16)) {
 x_36 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_36 = x_16;
}
lean::cnstr_set(x_36, 0, x_35);
lean::cnstr_set(x_36, 1, x_32);
return x_36;
}
else
{
obj* x_38; uint8 x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; 
lean::dec(x_0);
x_38 = lean::cnstr_get(x_19, 0);
lean::inc(x_38);
x_40 = lean::cnstr_get_scalar<uint8>(x_19, sizeof(void*)*1);
if (lean::is_shared(x_19)) {
 lean::dec(x_19);
 x_41 = lean::box(0);
} else {
 lean::cnstr_release(x_19, 0);
 x_41 = x_19;
}
if (lean::is_scalar(x_41)) {
 x_42 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_42 = x_41;
}
lean::cnstr_set(x_42, 0, x_38);
lean::cnstr_set_scalar(x_42, sizeof(void*)*1, x_40);
x_43 = x_42;
if (lean::is_scalar(x_16)) {
 x_44 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_44 = x_16;
}
lean::cnstr_set(x_44, 0, x_43);
lean::cnstr_set(x_44, 1, x_14);
return x_44;
}
}
else
{
uint32 x_45; uint8 x_46; 
x_45 = lean::string_iterator_curr(x_1);
x_46 = l_lean_is__id__end__escape(x_45);
if (x_46 == 0)
{
obj* x_48; obj* x_49; obj* x_50; obj* x_52; obj* x_54; obj* x_55; obj* x_56; obj* x_57; 
lean::inc(x_1);
x_48 = lean::string_iterator_next(x_1);
x_49 = l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser___spec__4(x_1, x_0, x_48, x_2);
x_50 = lean::cnstr_get(x_49, 0);
lean::inc(x_50);
x_52 = lean::cnstr_get(x_49, 1);
lean::inc(x_52);
if (lean::is_shared(x_49)) {
 lean::dec(x_49);
 x_54 = lean::box(0);
} else {
 lean::cnstr_release(x_49, 0);
 lean::cnstr_release(x_49, 1);
 x_54 = x_49;
}
x_55 = lean::box(0);
x_56 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_55, x_50);
if (lean::is_scalar(x_54)) {
 x_57 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_57 = x_54;
}
lean::cnstr_set(x_57, 0, x_56);
lean::cnstr_set(x_57, 1, x_52);
return x_57;
}
else
{
obj* x_58; obj* x_59; obj* x_61; obj* x_63; obj* x_64; obj* x_65; obj* x_69; obj* x_70; obj* x_72; obj* x_74; obj* x_75; obj* x_77; 
x_58 = l_char_quote__core(x_45);
x_59 = l_char_has__repr___closed__1;
lean::inc(x_59);
x_61 = lean::string_append(x_59, x_58);
lean::dec(x_58);
x_63 = lean::string_append(x_61, x_59);
x_64 = lean::box(0);
x_65 = l_mjoin___rarg___closed__1;
lean::inc(x_0);
lean::inc(x_64);
lean::inc(x_65);
x_69 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_63, x_65, x_64, x_64, x_0, x_1, x_2);
x_70 = lean::cnstr_get(x_69, 0);
lean::inc(x_70);
x_72 = lean::cnstr_get(x_69, 1);
lean::inc(x_72);
if (lean::is_shared(x_69)) {
 lean::dec(x_69);
 x_74 = lean::box(0);
} else {
 lean::cnstr_release(x_69, 0);
 lean::cnstr_release(x_69, 1);
 x_74 = x_69;
}
x_75 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_75);
x_77 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_75, x_70);
if (lean::obj_tag(x_77) == 0)
{
obj* x_78; obj* x_80; obj* x_82; uint32 x_85; obj* x_87; obj* x_88; obj* x_90; obj* x_93; obj* x_94; 
x_78 = lean::cnstr_get(x_77, 0);
lean::inc(x_78);
x_80 = lean::cnstr_get(x_77, 1);
lean::inc(x_80);
x_82 = lean::cnstr_get(x_77, 2);
lean::inc(x_82);
lean::dec(x_77);
x_85 = lean::unbox_uint32(x_78);
lean::dec(x_78);
x_87 = l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser___spec__6(x_85, x_0, x_80, x_72);
x_88 = lean::cnstr_get(x_87, 0);
lean::inc(x_88);
x_90 = lean::cnstr_get(x_87, 1);
lean::inc(x_90);
lean::dec(x_87);
x_93 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_82, x_88);
if (lean::is_scalar(x_74)) {
 x_94 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_94 = x_74;
}
lean::cnstr_set(x_94, 0, x_93);
lean::cnstr_set(x_94, 1, x_90);
return x_94;
}
else
{
obj* x_96; uint8 x_98; obj* x_99; obj* x_100; obj* x_101; obj* x_102; 
lean::dec(x_0);
x_96 = lean::cnstr_get(x_77, 0);
lean::inc(x_96);
x_98 = lean::cnstr_get_scalar<uint8>(x_77, sizeof(void*)*1);
if (lean::is_shared(x_77)) {
 lean::dec(x_77);
 x_99 = lean::box(0);
} else {
 lean::cnstr_release(x_77, 0);
 x_99 = x_77;
}
if (lean::is_scalar(x_99)) {
 x_100 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_100 = x_99;
}
lean::cnstr_set(x_100, 0, x_96);
lean::cnstr_set_scalar(x_100, sizeof(void*)*1, x_98);
x_101 = x_100;
if (lean::is_scalar(x_74)) {
 x_102 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_102 = x_74;
}
lean::cnstr_set(x_102, 0, x_101);
lean::cnstr_set(x_102, 1, x_72);
return x_102;
}
}
}
}
}
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser___spec__9(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
uint8 x_6; 
x_6 = lean::string_iterator_has_next(x_2);
if (x_6 == 0)
{
obj* x_8; 
lean::dec(x_0);
x_8 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_8;
}
else
{
uint32 x_9; uint8 x_10; 
x_9 = lean::string_iterator_curr(x_2);
x_10 = l_lean_is__id__rest(x_9);
if (x_10 == 0)
{
obj* x_12; 
lean::dec(x_0);
x_12 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_12;
}
else
{
obj* x_13; obj* x_14; obj* x_17; obj* x_18; 
x_13 = lean::mk_nat_obj(1u);
x_14 = lean::nat_sub(x_0, x_13);
lean::dec(x_13);
lean::dec(x_0);
x_17 = lean::string_push(x_1, x_9);
x_18 = lean::string_iterator_next(x_2);
x_0 = x_14;
x_1 = x_17;
x_2 = x_18;
goto _start;
}
}
}
else
{
obj* x_21; 
lean::dec(x_0);
x_21 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_21;
}
}
}
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser___spec__8___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_5; obj* x_6; 
x_2 = lean::string_iterator_remaining(x_0);
x_3 = l_string_join___closed__1;
lean::inc(x_3);
x_5 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser___spec__9(x_2, x_3, x_0);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_1);
return x_6;
}
}
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser___spec__8(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser___spec__8___rarg), 2, 0);
return x_2;
}
}
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser___spec__11(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
uint8 x_6; 
x_6 = lean::string_iterator_has_next(x_2);
if (x_6 == 0)
{
obj* x_8; 
lean::dec(x_0);
x_8 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_8;
}
else
{
uint32 x_9; uint8 x_10; 
x_9 = lean::string_iterator_curr(x_2);
x_10 = l_lean_is__id__rest(x_9);
if (x_10 == 0)
{
obj* x_12; 
lean::dec(x_0);
x_12 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_12;
}
else
{
obj* x_13; obj* x_14; obj* x_17; obj* x_18; 
x_13 = lean::mk_nat_obj(1u);
x_14 = lean::nat_sub(x_0, x_13);
lean::dec(x_13);
lean::dec(x_0);
x_17 = lean::string_push(x_1, x_9);
x_18 = lean::string_iterator_next(x_2);
x_0 = x_14;
x_1 = x_17;
x_2 = x_18;
goto _start;
}
}
}
else
{
obj* x_21; 
lean::dec(x_0);
x_21 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_21;
}
}
}
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser___spec__10___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_5; obj* x_6; 
x_2 = lean::string_iterator_remaining(x_0);
x_3 = l_string_join___closed__1;
lean::inc(x_3);
x_5 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser___spec__11(x_2, x_3, x_0);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_1);
return x_6;
}
}
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser___spec__10(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser___spec__10___rarg), 2, 0);
return x_2;
}
}
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser___spec__13(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
uint8 x_6; 
x_6 = lean::string_iterator_has_next(x_2);
if (x_6 == 0)
{
obj* x_8; 
lean::dec(x_0);
x_8 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_8;
}
else
{
uint32 x_9; uint8 x_10; 
x_9 = lean::string_iterator_curr(x_2);
x_10 = l_lean_is__id__rest(x_9);
if (x_10 == 0)
{
obj* x_12; 
lean::dec(x_0);
x_12 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_12;
}
else
{
obj* x_13; obj* x_14; obj* x_17; obj* x_18; 
x_13 = lean::mk_nat_obj(1u);
x_14 = lean::nat_sub(x_0, x_13);
lean::dec(x_13);
lean::dec(x_0);
x_17 = lean::string_push(x_1, x_9);
x_18 = lean::string_iterator_next(x_2);
x_0 = x_14;
x_1 = x_17;
x_2 = x_18;
goto _start;
}
}
}
else
{
obj* x_21; 
lean::dec(x_0);
x_21 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_21;
}
}
}
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser___spec__12___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_5; obj* x_6; 
x_2 = lean::string_iterator_remaining(x_0);
x_3 = l_string_join___closed__1;
lean::inc(x_3);
x_5 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser___spec__13(x_2, x_3, x_0);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_1);
return x_6;
}
}
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser___spec__12(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser___spec__12___rarg), 2, 0);
return x_2;
}
}
obj* l_lean_parser_detail__ident__part_parser___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_7; obj* x_9; 
x_4 = l_lean_parser_monad__parsec_take__while1___at_lean_parser_detail__ident__part_parser___spec__1(x_1, x_2, x_3);
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
obj* x_10; obj* x_12; obj* x_14; obj* x_16; obj* x_17; obj* x_19; obj* x_20; obj* x_21; 
x_10 = lean::cnstr_get(x_5, 1);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_5, 2);
lean::inc(x_12);
if (lean::is_shared(x_5)) {
 lean::dec(x_5);
 x_14 = lean::box(0);
} else {
 lean::cnstr_release(x_5, 0);
 lean::cnstr_release(x_5, 1);
 lean::cnstr_release(x_5, 2);
 x_14 = x_5;
}
lean::inc(x_10);
x_16 = l_lean_parser_mk__raw__res(x_0, x_10);
x_17 = l_lean_parser_finish__comment__block___closed__2;
lean::inc(x_17);
if (lean::is_scalar(x_14)) {
 x_19 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_19 = x_14;
}
lean::cnstr_set(x_19, 0, x_16);
lean::cnstr_set(x_19, 1, x_10);
lean::cnstr_set(x_19, 2, x_17);
x_20 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_12, x_19);
if (lean::is_scalar(x_9)) {
 x_21 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_21 = x_9;
}
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_7);
return x_21;
}
else
{
obj* x_23; uint8 x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
lean::dec(x_0);
x_23 = lean::cnstr_get(x_5, 0);
lean::inc(x_23);
x_25 = lean::cnstr_get_scalar<uint8>(x_5, sizeof(void*)*1);
if (lean::is_shared(x_5)) {
 lean::dec(x_5);
 x_26 = lean::box(0);
} else {
 lean::cnstr_release(x_5, 0);
 x_26 = x_5;
}
if (lean::is_scalar(x_26)) {
 x_27 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_27 = x_26;
}
lean::cnstr_set(x_27, 0, x_23);
lean::cnstr_set_scalar(x_27, sizeof(void*)*1, x_25);
x_28 = x_27;
if (lean::is_scalar(x_9)) {
 x_29 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_29 = x_9;
}
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_7);
return x_29;
}
}
}
obj* l_lean_parser_detail__ident__part_parser___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; uint8 x_7; 
x_7 = lean::string_iterator_has_next(x_2);
if (x_7 == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_14; obj* x_15; obj* x_17; obj* x_20; obj* x_22; 
x_8 = lean::box(0);
x_9 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_10 = l_mjoin___rarg___closed__1;
lean::inc(x_8);
lean::inc(x_10);
lean::inc(x_9);
x_14 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_9, x_10, x_8, x_8, x_1, x_2, x_3);
x_15 = lean::cnstr_get(x_14, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_14, 1);
lean::inc(x_17);
lean::dec(x_14);
x_20 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_20);
x_22 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_20, x_15);
if (lean::obj_tag(x_22) == 0)
{
obj* x_23; obj* x_25; obj* x_28; obj* x_29; obj* x_31; obj* x_34; 
x_23 = lean::cnstr_get(x_22, 1);
lean::inc(x_23);
x_25 = lean::cnstr_get(x_22, 2);
lean::inc(x_25);
lean::dec(x_22);
x_28 = l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser___spec__8___rarg(x_23, x_17);
x_29 = lean::cnstr_get(x_28, 0);
lean::inc(x_29);
x_31 = lean::cnstr_get(x_28, 1);
lean::inc(x_31);
lean::dec(x_28);
x_34 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_25, x_29);
x_4 = x_34;
x_5 = x_31;
goto lbl_6;
}
else
{
obj* x_35; uint8 x_37; obj* x_38; obj* x_39; obj* x_40; 
x_35 = lean::cnstr_get(x_22, 0);
lean::inc(x_35);
x_37 = lean::cnstr_get_scalar<uint8>(x_22, sizeof(void*)*1);
if (lean::is_shared(x_22)) {
 lean::dec(x_22);
 x_38 = lean::box(0);
} else {
 lean::cnstr_release(x_22, 0);
 x_38 = x_22;
}
if (lean::is_scalar(x_38)) {
 x_39 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_39 = x_38;
}
lean::cnstr_set(x_39, 0, x_35);
lean::cnstr_set_scalar(x_39, sizeof(void*)*1, x_37);
x_40 = x_39;
x_4 = x_40;
x_5 = x_17;
goto lbl_6;
}
}
else
{
uint32 x_41; uint8 x_42; 
x_41 = lean::string_iterator_curr(x_2);
x_42 = l_lean_is__id__first(x_41);
if (x_42 == 0)
{
obj* x_43; obj* x_44; obj* x_46; obj* x_48; obj* x_49; obj* x_50; obj* x_53; obj* x_54; obj* x_56; obj* x_59; obj* x_61; 
x_43 = l_char_quote__core(x_41);
x_44 = l_char_has__repr___closed__1;
lean::inc(x_44);
x_46 = lean::string_append(x_44, x_43);
lean::dec(x_43);
x_48 = lean::string_append(x_46, x_44);
x_49 = lean::box(0);
x_50 = l_mjoin___rarg___closed__1;
lean::inc(x_49);
lean::inc(x_50);
x_53 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_48, x_50, x_49, x_49, x_1, x_2, x_3);
x_54 = lean::cnstr_get(x_53, 0);
lean::inc(x_54);
x_56 = lean::cnstr_get(x_53, 1);
lean::inc(x_56);
lean::dec(x_53);
x_59 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_59);
x_61 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_59, x_54);
if (lean::obj_tag(x_61) == 0)
{
obj* x_62; obj* x_64; obj* x_67; obj* x_68; obj* x_70; obj* x_73; 
x_62 = lean::cnstr_get(x_61, 1);
lean::inc(x_62);
x_64 = lean::cnstr_get(x_61, 2);
lean::inc(x_64);
lean::dec(x_61);
x_67 = l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser___spec__10___rarg(x_62, x_56);
x_68 = lean::cnstr_get(x_67, 0);
lean::inc(x_68);
x_70 = lean::cnstr_get(x_67, 1);
lean::inc(x_70);
lean::dec(x_67);
x_73 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_64, x_68);
x_4 = x_73;
x_5 = x_70;
goto lbl_6;
}
else
{
obj* x_74; uint8 x_76; obj* x_77; obj* x_78; obj* x_79; 
x_74 = lean::cnstr_get(x_61, 0);
lean::inc(x_74);
x_76 = lean::cnstr_get_scalar<uint8>(x_61, sizeof(void*)*1);
if (lean::is_shared(x_61)) {
 lean::dec(x_61);
 x_77 = lean::box(0);
} else {
 lean::cnstr_release(x_61, 0);
 x_77 = x_61;
}
if (lean::is_scalar(x_77)) {
 x_78 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_78 = x_77;
}
lean::cnstr_set(x_78, 0, x_74);
lean::cnstr_set_scalar(x_78, sizeof(void*)*1, x_76);
x_79 = x_78;
x_4 = x_79;
x_5 = x_56;
goto lbl_6;
}
}
else
{
obj* x_81; obj* x_82; obj* x_83; obj* x_85; obj* x_88; obj* x_89; 
lean::dec(x_1);
x_81 = lean::string_iterator_next(x_2);
x_82 = l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser___spec__12___rarg(x_81, x_3);
x_83 = lean::cnstr_get(x_82, 0);
lean::inc(x_83);
x_85 = lean::cnstr_get(x_82, 1);
lean::inc(x_85);
lean::dec(x_82);
x_88 = lean::box(0);
x_89 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_88, x_83);
x_4 = x_89;
x_5 = x_85;
goto lbl_6;
}
}
lbl_6:
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_90; obj* x_92; obj* x_94; obj* x_96; obj* x_97; obj* x_99; obj* x_100; obj* x_101; 
x_90 = lean::cnstr_get(x_4, 1);
lean::inc(x_90);
x_92 = lean::cnstr_get(x_4, 2);
lean::inc(x_92);
if (lean::is_shared(x_4)) {
 lean::dec(x_4);
 x_94 = lean::box(0);
} else {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_release(x_4, 1);
 lean::cnstr_release(x_4, 2);
 x_94 = x_4;
}
lean::inc(x_90);
x_96 = l_lean_parser_mk__raw__res(x_0, x_90);
x_97 = l_lean_parser_finish__comment__block___closed__2;
lean::inc(x_97);
if (lean::is_scalar(x_94)) {
 x_99 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_99 = x_94;
}
lean::cnstr_set(x_99, 0, x_96);
lean::cnstr_set(x_99, 1, x_90);
lean::cnstr_set(x_99, 2, x_97);
x_100 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_92, x_99);
x_101 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_101, 0, x_100);
lean::cnstr_set(x_101, 1, x_5);
return x_101;
}
else
{
obj* x_103; uint8 x_105; obj* x_106; obj* x_107; obj* x_108; obj* x_109; 
lean::dec(x_0);
x_103 = lean::cnstr_get(x_4, 0);
lean::inc(x_103);
x_105 = lean::cnstr_get_scalar<uint8>(x_4, sizeof(void*)*1);
if (lean::is_shared(x_4)) {
 lean::dec(x_4);
 x_106 = lean::box(0);
} else {
 lean::cnstr_release(x_4, 0);
 x_106 = x_4;
}
if (lean::is_scalar(x_106)) {
 x_107 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_107 = x_106;
}
lean::cnstr_set(x_107, 0, x_103);
lean::cnstr_set_scalar(x_107, sizeof(void*)*1, x_105);
x_108 = x_107;
x_109 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_109, 0, x_108);
lean::cnstr_set(x_109, 1, x_5);
return x_109;
}
}
}
}
obj* _init_l_lean_parser_detail__ident__part_parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; uint32 x_2; obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_12; obj* x_13; obj* x_15; obj* x_16; uint32 x_17; obj* x_18; obj* x_20; obj* x_21; obj* x_22; obj* x_24; obj* x_25; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_32; obj* x_33; obj* x_34; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; 
x_0 = lean::mk_string("");
x_1 = l_lean_id__begin__escape;
x_2 = lean::unbox_uint32(x_1);
lean::inc(x_0);
x_4 = lean::string_push(x_0, x_2);
lean::inc(x_4);
x_6 = l_string_quote(x_4);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_7, 0, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_with__trailing___rarg___lambda__1), 2, 0);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_lift___at_lean_parser_with__trailing___spec__1___rarg), 4, 1);
lean::closure_set(x_9, 0, x_8);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_detail__ident__part_parser_lean_parser_has__view___lambda__1), 6, 2);
lean::closure_set(x_10, 0, x_4);
lean::closure_set(x_10, 1, x_7);
lean::inc(x_9);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_bind___at_lean_parser_with__trailing___spec__2___rarg), 5, 2);
lean::closure_set(x_12, 0, x_9);
lean::closure_set(x_12, 1, x_10);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_detail__ident__part_parser___lambda__1), 4, 0);
lean::inc(x_9);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_bind___at_lean_parser_with__trailing___spec__2___rarg), 5, 2);
lean::closure_set(x_15, 0, x_9);
lean::closure_set(x_15, 1, x_13);
x_16 = l_lean_id__end__escape;
x_17 = lean::unbox_uint32(x_16);
x_18 = lean::string_push(x_0, x_17);
lean::inc(x_18);
x_20 = l_string_quote(x_18);
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_21, 0, x_20);
x_22 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_detail__ident__part_parser_lean_parser_has__view___lambda__1), 6, 2);
lean::closure_set(x_22, 0, x_18);
lean::closure_set(x_22, 1, x_21);
lean::inc(x_9);
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_bind___at_lean_parser_with__trailing___spec__2___rarg), 5, 2);
lean::closure_set(x_24, 0, x_9);
lean::closure_set(x_24, 1, x_22);
x_25 = lean::box(0);
lean::inc(x_25);
x_27 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_27, 0, x_24);
lean::cnstr_set(x_27, 1, x_25);
x_28 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_28, 0, x_15);
lean::cnstr_set(x_28, 1, x_27);
x_29 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_29, 0, x_12);
lean::cnstr_set(x_29, 1, x_28);
x_30 = l_lean_parser_detail__ident__part__escaped;
lean::inc(x_30);
x_32 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__15), 5, 2);
lean::closure_set(x_32, 0, x_30);
lean::closure_set(x_32, 1, x_29);
x_33 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_detail__ident__part_parser___lambda__2), 4, 0);
x_34 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_bind___at_lean_parser_with__trailing___spec__2___rarg), 5, 2);
lean::closure_set(x_34, 0, x_9);
lean::closure_set(x_34, 1, x_33);
lean::inc(x_25);
x_36 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_36, 0, x_34);
lean::cnstr_set(x_36, 1, x_25);
x_37 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_37, 0, x_32);
lean::cnstr_set(x_37, 1, x_36);
x_38 = lean::mk_nat_obj(0u);
x_39 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_choice__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__29), 5, 2);
lean::closure_set(x_39, 0, x_37);
lean::closure_set(x_39, 1, x_38);
x_40 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_40, 0, x_39);
lean::cnstr_set(x_40, 1, x_25);
return x_40;
}
}
obj* l_lean_parser_detail__ident__part_parser(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_7; 
x_3 = l_lean_parser_detail__ident__part;
x_4 = l_lean_parser_detail__ident__part_parser___closed__1;
lean::inc(x_4);
lean::inc(x_3);
x_7 = l_lean_parser_combinators_node___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__15(x_3, x_4, x_0, x_1, x_2);
return x_7;
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint32 x_4; obj* x_5; 
x_4 = lean::unbox_uint32(x_0);
x_5 = l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser___spec__2(x_4, x_1, x_2, x_3);
return x_5;
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser___spec__6___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint32 x_4; obj* x_5; 
x_4 = lean::unbox_uint32(x_0);
x_5 = l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser___spec__6(x_4, x_1, x_2, x_3);
return x_5;
}
}
obj* _init_l_lean_parser_detail__ident__suffix() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("detail_ident_suffix");
x_6 = lean_name_mk_string(x_4, x_5);
return x_6;
}
}
obj* _init_l_lean_parser_detail__ident__suffix_has__view_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::box(3);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* l_lean_parser_detail__ident__suffix_has__view_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_syntax_as__node___main(x_0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; 
lean::dec(x_1);
x_3 = l_lean_parser_detail__ident__suffix_has__view_x_27___lambda__1___closed__1;
lean::inc(x_3);
return x_3;
}
else
{
obj* x_5; obj* x_7; obj* x_8; 
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_7 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 x_7 = x_1;
}
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
lean::dec(x_5);
if (lean::obj_tag(x_8) == 0)
{
lean::dec(x_7);
if (lean::obj_tag(x_8) == 0)
{
obj* x_13; 
lean::dec(x_8);
x_13 = l_lean_parser_detail__ident__suffix_has__view_x_27___lambda__1___closed__1;
lean::inc(x_13);
return x_13;
}
else
{
obj* x_15; obj* x_18; obj* x_19; 
x_15 = lean::cnstr_get(x_8, 0);
lean::inc(x_15);
lean::dec(x_8);
x_18 = lean::box(0);
x_19 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_19, 0, x_18);
lean::cnstr_set(x_19, 1, x_15);
return x_19;
}
}
else
{
obj* x_20; obj* x_22; 
x_20 = lean::cnstr_get(x_8, 0);
lean::inc(x_20);
x_22 = lean::cnstr_get(x_8, 1);
lean::inc(x_22);
lean::dec(x_8);
switch (lean::obj_tag(x_20)) {
case 0:
{
obj* x_25; obj* x_28; 
x_25 = lean::cnstr_get(x_20, 0);
lean::inc(x_25);
lean::dec(x_20);
if (lean::is_scalar(x_7)) {
 x_28 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_28 = x_7;
}
lean::cnstr_set(x_28, 0, x_25);
if (lean::obj_tag(x_22) == 0)
{
obj* x_30; obj* x_31; 
lean::dec(x_22);
x_30 = lean::box(3);
x_31 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_31, 0, x_28);
lean::cnstr_set(x_31, 1, x_30);
return x_31;
}
else
{
obj* x_32; obj* x_35; 
x_32 = lean::cnstr_get(x_22, 0);
lean::inc(x_32);
lean::dec(x_22);
x_35 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_35, 0, x_28);
lean::cnstr_set(x_35, 1, x_32);
return x_35;
}
}
case 1:
{
lean::dec(x_7);
lean::dec(x_20);
if (lean::obj_tag(x_22) == 0)
{
obj* x_39; 
lean::dec(x_22);
x_39 = l_lean_parser_detail__ident__suffix_has__view_x_27___lambda__1___closed__1;
lean::inc(x_39);
return x_39;
}
else
{
obj* x_41; obj* x_44; obj* x_45; 
x_41 = lean::cnstr_get(x_22, 0);
lean::inc(x_41);
lean::dec(x_22);
x_44 = lean::box(0);
x_45 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_45, 0, x_44);
lean::cnstr_set(x_45, 1, x_41);
return x_45;
}
}
case 2:
{
lean::dec(x_7);
lean::dec(x_20);
if (lean::obj_tag(x_22) == 0)
{
obj* x_49; 
lean::dec(x_22);
x_49 = l_lean_parser_detail__ident__suffix_has__view_x_27___lambda__1___closed__1;
lean::inc(x_49);
return x_49;
}
else
{
obj* x_51; obj* x_54; obj* x_55; 
x_51 = lean::cnstr_get(x_22, 0);
lean::inc(x_51);
lean::dec(x_22);
x_54 = lean::box(0);
x_55 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_55, 0, x_54);
lean::cnstr_set(x_55, 1, x_51);
return x_55;
}
}
default:
{
lean::dec(x_7);
lean::dec(x_20);
if (lean::obj_tag(x_22) == 0)
{
obj* x_59; 
lean::dec(x_22);
x_59 = l_lean_parser_detail__ident__suffix_has__view_x_27___lambda__1___closed__1;
lean::inc(x_59);
return x_59;
}
else
{
obj* x_61; obj* x_64; obj* x_65; 
x_61 = lean::cnstr_get(x_22, 0);
lean::inc(x_61);
lean::dec(x_22);
x_64 = lean::box(0);
x_65 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_65, 0, x_64);
lean::cnstr_set(x_65, 1, x_61);
return x_65;
}
}
}
}
}
}
}
obj* l_lean_parser_detail__ident__suffix_has__view_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_16; 
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
x_11 = lean::box(0);
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_3);
lean::cnstr_set(x_12, 1, x_11);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_10);
lean::cnstr_set(x_13, 1, x_12);
x_14 = l_lean_parser_detail__ident__suffix;
lean::inc(x_14);
x_16 = l_lean_parser_syntax_mk__node(x_14, x_13);
return x_16;
}
}
obj* _init_l_lean_parser_detail__ident__suffix_has__view_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_detail__ident__suffix_has__view_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_detail__ident__suffix_has__view_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_lean_parser_detail__ident__suffix_has__view() {
_start:
{
obj* x_0; 
x_0 = l_lean_parser_detail__ident__suffix_has__view_x_27;
lean::inc(x_0);
return x_0;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_10; obj* x_11; uint8 x_12; obj* x_13; obj* x_14; obj* x_15; 
lean::dec(x_5);
lean::dec(x_4);
x_10 = l_option_get__or__else___main___rarg(x_2, x_6);
x_11 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_0);
lean::cnstr_set(x_11, 2, x_1);
lean::cnstr_set(x_11, 3, x_3);
x_12 = 0;
x_13 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_13, 0, x_11);
lean::cnstr_set_scalar(x_13, sizeof(void*)*1, x_12);
x_14 = x_13;
x_15 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_15, 0, x_14);
lean::cnstr_set(x_15, 1, x_7);
return x_15;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__2(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__2___rarg), 8, 0);
return x_2;
}
}
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__1(uint32 x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; 
x_5 = lean::string_iterator_has_next(x_3);
if (x_5 == 0)
{
obj* x_6; obj* x_7; obj* x_8; obj* x_12; obj* x_13; obj* x_15; obj* x_17; obj* x_18; obj* x_20; obj* x_21; 
x_6 = lean::box(0);
x_7 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_8 = l_mjoin___rarg___closed__1;
lean::inc(x_6);
lean::inc(x_8);
lean::inc(x_7);
x_12 = l_lean_parser_monad__parsec_error___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__2___rarg(x_7, x_8, x_6, x_6, x_1, x_2, x_3, x_4);
x_13 = lean::cnstr_get(x_12, 0);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_12, 1);
lean::inc(x_15);
if (lean::is_shared(x_12)) {
 lean::dec(x_12);
 x_17 = lean::box(0);
} else {
 lean::cnstr_release(x_12, 0);
 lean::cnstr_release(x_12, 1);
 x_17 = x_12;
}
x_18 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_18);
x_20 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_18, x_13);
if (lean::is_scalar(x_17)) {
 x_21 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_21 = x_17;
}
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_15);
return x_21;
}
else
{
uint32 x_22; obj* x_23; obj* x_24; uint8 x_25; 
x_22 = lean::string_iterator_curr(x_3);
x_23 = lean::box_uint32(x_22);
x_24 = lean::box_uint32(x_0);
x_25 = lean::nat_dec_eq(x_23, x_24);
lean::dec(x_24);
if (x_25 == 0)
{
obj* x_28; obj* x_29; obj* x_31; obj* x_33; obj* x_34; obj* x_35; obj* x_38; obj* x_39; obj* x_41; obj* x_43; obj* x_44; obj* x_46; obj* x_47; 
lean::dec(x_23);
x_28 = l_char_quote__core(x_22);
x_29 = l_char_has__repr___closed__1;
lean::inc(x_29);
x_31 = lean::string_append(x_29, x_28);
lean::dec(x_28);
x_33 = lean::string_append(x_31, x_29);
x_34 = lean::box(0);
x_35 = l_mjoin___rarg___closed__1;
lean::inc(x_34);
lean::inc(x_35);
x_38 = l_lean_parser_monad__parsec_error___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__2___rarg(x_33, x_35, x_34, x_34, x_1, x_2, x_3, x_4);
x_39 = lean::cnstr_get(x_38, 0);
lean::inc(x_39);
x_41 = lean::cnstr_get(x_38, 1);
lean::inc(x_41);
if (lean::is_shared(x_38)) {
 lean::dec(x_38);
 x_43 = lean::box(0);
} else {
 lean::cnstr_release(x_38, 0);
 lean::cnstr_release(x_38, 1);
 x_43 = x_38;
}
x_44 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_44);
x_46 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_44, x_39);
if (lean::is_scalar(x_43)) {
 x_47 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_47 = x_43;
}
lean::cnstr_set(x_47, 0, x_46);
lean::cnstr_set(x_47, 1, x_41);
return x_47;
}
else
{
obj* x_50; obj* x_51; obj* x_52; obj* x_53; 
lean::dec(x_1);
lean::dec(x_2);
x_50 = lean::string_iterator_next(x_3);
x_51 = lean::box(0);
x_52 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_52, 0, x_23);
lean::cnstr_set(x_52, 1, x_50);
lean::cnstr_set(x_52, 2, x_51);
x_53 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_53, 0, x_52);
lean::cnstr_set(x_53, 1, x_4);
return x_53;
}
}
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__3___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_10; obj* x_11; uint8 x_12; obj* x_13; obj* x_14; obj* x_15; 
lean::dec(x_5);
lean::dec(x_4);
x_10 = l_option_get__or__else___main___rarg(x_2, x_6);
x_11 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_0);
lean::cnstr_set(x_11, 2, x_1);
lean::cnstr_set(x_11, 3, x_3);
x_12 = 0;
x_13 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_13, 0, x_11);
lean::cnstr_set_scalar(x_13, sizeof(void*)*1, x_12);
x_14 = x_13;
x_15 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_15, 0, x_14);
lean::cnstr_set(x_15, 1, x_7);
return x_15;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__3(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__3___rarg), 8, 0);
return x_2;
}
}
obj* l_lean_parser_parsec__t_lookahead___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__4(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_7; uint32 x_8; obj* x_13; obj* x_14; obj* x_16; 
x_7 = lean::mk_nat_obj(46u);
x_8 = lean::unbox_uint32(x_7);
lean::dec(x_7);
lean::inc(x_2);
lean::inc(x_1);
lean::inc(x_0);
x_13 = l_lean_parser_monad__parsec_ch___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__1(x_8, x_0, x_1, x_2, x_3);
x_14 = lean::cnstr_get(x_13, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_13, 1);
lean::inc(x_16);
lean::dec(x_13);
if (lean::obj_tag(x_14) == 0)
{
obj* x_19; obj* x_21; obj* x_23; obj* x_24; uint32 x_25; obj* x_29; obj* x_30; obj* x_32; 
x_19 = lean::cnstr_get(x_14, 1);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_14, 2);
lean::inc(x_21);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_23 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 lean::cnstr_release(x_14, 1);
 lean::cnstr_release(x_14, 2);
 x_23 = x_14;
}
x_24 = l_lean_id__begin__escape;
x_25 = lean::unbox_uint32(x_24);
lean::inc(x_19);
lean::inc(x_1);
lean::inc(x_0);
x_29 = l_lean_parser_monad__parsec_ch___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__1(x_25, x_0, x_1, x_19, x_16);
x_30 = lean::cnstr_get(x_29, 0);
lean::inc(x_30);
x_32 = lean::cnstr_get(x_29, 1);
lean::inc(x_32);
lean::dec(x_29);
if (lean::obj_tag(x_30) == 0)
{
obj* x_39; 
lean::dec(x_19);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_23);
x_39 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_21, x_30);
x_4 = x_39;
x_5 = x_32;
goto lbl_6;
}
else
{
obj* x_40; uint8 x_42; 
x_40 = lean::cnstr_get(x_30, 0);
lean::inc(x_40);
x_42 = lean::cnstr_get_scalar<uint8>(x_30, sizeof(void*)*1);
if (x_42 == 0)
{
uint8 x_44; 
lean::dec(x_30);
x_44 = lean::string_iterator_has_next(x_19);
if (x_44 == 0)
{
obj* x_46; obj* x_47; obj* x_48; obj* x_52; obj* x_53; obj* x_55; obj* x_58; obj* x_60; obj* x_61; obj* x_62; 
lean::dec(x_23);
x_46 = lean::box(0);
x_47 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_48 = l_mjoin___rarg___closed__1;
lean::inc(x_46);
lean::inc(x_48);
lean::inc(x_47);
x_52 = l_lean_parser_monad__parsec_error___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__3___rarg(x_47, x_48, x_46, x_46, x_0, x_1, x_19, x_32);
x_53 = lean::cnstr_get(x_52, 0);
lean::inc(x_53);
x_55 = lean::cnstr_get(x_52, 1);
lean::inc(x_55);
lean::dec(x_52);
x_58 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_58);
x_60 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_58, x_53);
x_61 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_40, x_60);
x_62 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_21, x_61);
x_4 = x_62;
x_5 = x_55;
goto lbl_6;
}
else
{
uint32 x_63; uint8 x_64; 
x_63 = lean::string_iterator_curr(x_19);
x_64 = l_lean_is__id__first(x_63);
if (x_64 == 0)
{
obj* x_66; obj* x_67; obj* x_69; obj* x_71; obj* x_72; obj* x_73; obj* x_76; obj* x_77; obj* x_79; obj* x_82; obj* x_84; obj* x_85; obj* x_86; 
lean::dec(x_23);
x_66 = l_char_quote__core(x_63);
x_67 = l_char_has__repr___closed__1;
lean::inc(x_67);
x_69 = lean::string_append(x_67, x_66);
lean::dec(x_66);
x_71 = lean::string_append(x_69, x_67);
x_72 = lean::box(0);
x_73 = l_mjoin___rarg___closed__1;
lean::inc(x_72);
lean::inc(x_73);
x_76 = l_lean_parser_monad__parsec_error___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__3___rarg(x_71, x_73, x_72, x_72, x_0, x_1, x_19, x_32);
x_77 = lean::cnstr_get(x_76, 0);
lean::inc(x_77);
x_79 = lean::cnstr_get(x_76, 1);
lean::inc(x_79);
lean::dec(x_76);
x_82 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_82);
x_84 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_82, x_77);
x_85 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_40, x_84);
x_86 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_21, x_85);
x_4 = x_86;
x_5 = x_79;
goto lbl_6;
}
else
{
obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_40);
x_90 = lean::string_iterator_next(x_19);
x_91 = lean::box(0);
x_92 = lean::box_uint32(x_63);
if (lean::is_scalar(x_23)) {
 x_93 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_93 = x_23;
}
lean::cnstr_set(x_93, 0, x_92);
lean::cnstr_set(x_93, 1, x_90);
lean::cnstr_set(x_93, 2, x_91);
x_94 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_21, x_93);
x_4 = x_94;
x_5 = x_32;
goto lbl_6;
}
}
}
else
{
obj* x_100; 
lean::dec(x_19);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_23);
lean::dec(x_40);
x_100 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_21, x_30);
x_4 = x_100;
x_5 = x_32;
goto lbl_6;
}
}
}
else
{
obj* x_103; uint8 x_105; obj* x_106; obj* x_107; obj* x_108; 
lean::dec(x_1);
lean::dec(x_0);
x_103 = lean::cnstr_get(x_14, 0);
lean::inc(x_103);
x_105 = lean::cnstr_get_scalar<uint8>(x_14, sizeof(void*)*1);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_106 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 x_106 = x_14;
}
if (lean::is_scalar(x_106)) {
 x_107 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_107 = x_106;
}
lean::cnstr_set(x_107, 0, x_103);
lean::cnstr_set_scalar(x_107, sizeof(void*)*1, x_105);
x_108 = x_107;
x_4 = x_108;
x_5 = x_16;
goto lbl_6;
}
lbl_6:
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_109; obj* x_111; obj* x_112; obj* x_114; obj* x_115; 
x_109 = lean::cnstr_get(x_4, 0);
lean::inc(x_109);
if (lean::is_shared(x_4)) {
 lean::dec(x_4);
 x_111 = lean::box(0);
} else {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_release(x_4, 1);
 lean::cnstr_release(x_4, 2);
 x_111 = x_4;
}
x_112 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_112);
if (lean::is_scalar(x_111)) {
 x_114 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_114 = x_111;
}
lean::cnstr_set(x_114, 0, x_109);
lean::cnstr_set(x_114, 1, x_2);
lean::cnstr_set(x_114, 2, x_112);
x_115 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_115, 0, x_114);
lean::cnstr_set(x_115, 1, x_5);
return x_115;
}
else
{
obj* x_117; 
lean::dec(x_2);
x_117 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_117, 0, x_4);
lean::cnstr_set(x_117, 1, x_5);
return x_117;
}
}
}
}
obj* l_reader__t_lift___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__5___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_6; 
lean::dec(x_1);
x_6 = lean::apply_3(x_0, x_2, x_3, x_4);
return x_6;
}
}
obj* l_reader__t_lift___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__5(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_lift___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__5___rarg), 5, 0);
return x_2;
}
}
obj* l_lean_parser_monad__parsec_str__core___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__6(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_9; 
lean::dec(x_3);
lean::dec(x_2);
lean::inc(x_0);
x_9 = l_string_is__empty(x_0);
if (x_9 == 0)
{
obj* x_10; obj* x_12; obj* x_14; 
x_10 = lean::string_length(x_0);
lean::inc(x_0);
x_12 = lean::string_mk_iterator(x_0);
lean::inc(x_4);
x_14 = l___private_init_lean_parser_parsec_1__str__aux___main(x_10, x_12, x_4);
if (lean::obj_tag(x_14) == 0)
{
obj* x_17; obj* x_18; obj* x_20; uint8 x_21; obj* x_22; obj* x_23; obj* x_24; 
lean::dec(x_14);
lean::dec(x_0);
x_17 = lean::box(0);
x_18 = l_string_join___closed__1;
lean::inc(x_18);
x_20 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_20, 0, x_4);
lean::cnstr_set(x_20, 1, x_18);
lean::cnstr_set(x_20, 2, x_1);
lean::cnstr_set(x_20, 3, x_17);
x_21 = 0;
x_22 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_22, 0, x_20);
lean::cnstr_set_scalar(x_22, sizeof(void*)*1, x_21);
x_23 = x_22;
x_24 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_5);
return x_24;
}
else
{
obj* x_27; obj* x_30; obj* x_31; obj* x_32; 
lean::dec(x_4);
lean::dec(x_1);
x_27 = lean::cnstr_get(x_14, 0);
lean::inc(x_27);
lean::dec(x_14);
x_30 = lean::box(0);
x_31 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_31, 0, x_0);
lean::cnstr_set(x_31, 1, x_27);
lean::cnstr_set(x_31, 2, x_30);
x_32 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_5);
return x_32;
}
}
else
{
obj* x_35; obj* x_36; obj* x_39; obj* x_40; 
lean::dec(x_1);
lean::dec(x_0);
x_35 = l_string_join___closed__1;
x_36 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_36);
lean::inc(x_35);
x_39 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_39, 0, x_35);
lean::cnstr_set(x_39, 1, x_4);
lean::cnstr_set(x_39, 2, x_36);
x_40 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_40, 0, x_39);
lean::cnstr_set(x_40, 1, x_5);
return x_40;
}
}
}
obj* l_reader__t_bind___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__7___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_8; obj* x_9; obj* x_11; obj* x_13; 
lean::inc(x_3);
lean::inc(x_2);
x_8 = lean::apply_4(x_0, x_2, x_3, x_4, x_5);
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
if (lean::is_shared(x_8)) {
 lean::dec(x_8);
 x_13 = lean::box(0);
} else {
 lean::cnstr_release(x_8, 0);
 lean::cnstr_release(x_8, 1);
 x_13 = x_8;
}
if (lean::obj_tag(x_9) == 0)
{
obj* x_14; obj* x_16; obj* x_18; obj* x_21; obj* x_22; obj* x_24; obj* x_27; obj* x_28; 
x_14 = lean::cnstr_get(x_9, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_9, 1);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_9, 2);
lean::inc(x_18);
lean::dec(x_9);
x_21 = lean::apply_5(x_1, x_14, x_2, x_3, x_16, x_11);
x_22 = lean::cnstr_get(x_21, 0);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_21, 1);
lean::inc(x_24);
lean::dec(x_21);
x_27 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_18, x_22);
if (lean::is_scalar(x_13)) {
 x_28 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_28 = x_13;
}
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_24);
return x_28;
}
else
{
obj* x_32; uint8 x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_2);
x_32 = lean::cnstr_get(x_9, 0);
lean::inc(x_32);
x_34 = lean::cnstr_get_scalar<uint8>(x_9, sizeof(void*)*1);
if (lean::is_shared(x_9)) {
 lean::dec(x_9);
 x_35 = lean::box(0);
} else {
 lean::cnstr_release(x_9, 0);
 x_35 = x_9;
}
if (lean::is_scalar(x_35)) {
 x_36 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_36 = x_35;
}
lean::cnstr_set(x_36, 0, x_32);
lean::cnstr_set_scalar(x_36, sizeof(void*)*1, x_34);
x_37 = x_36;
if (lean::is_scalar(x_13)) {
 x_38 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_38 = x_13;
}
lean::cnstr_set(x_38, 0, x_37);
lean::cnstr_set(x_38, 1, x_11);
return x_38;
}
}
}
obj* l_reader__t_bind___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__7(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_bind___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__7___rarg), 6, 0);
return x_4;
}
}
obj* l_lean_parser_rec__t_recurse___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__8(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_8; obj* x_10; obj* x_11; obj* x_13; obj* x_14; 
x_5 = lean::apply_4(x_1, x_0, x_2, x_3, x_4);
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
x_11 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_11);
x_13 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_11, x_6);
if (lean::is_scalar(x_10)) {
 x_14 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_14 = x_10;
}
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_8);
return x_14;
}
}
obj* l_list_mfoldl___main___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__10(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_11; obj* x_13; obj* x_14; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
x_11 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_11);
x_13 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_13, 0, x_1);
lean::cnstr_set(x_13, 1, x_5);
lean::cnstr_set(x_13, 2, x_11);
x_14 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_6);
return x_14;
}
else
{
obj* x_15; obj* x_17; obj* x_19; obj* x_20; obj* x_21; obj* x_25; obj* x_26; obj* x_28; 
x_15 = lean::cnstr_get(x_2, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_2, 1);
lean::inc(x_17);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_19 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 lean::cnstr_release(x_2, 1);
 x_19 = x_2;
}
lean::inc(x_4);
lean::inc(x_3);
x_25 = lean::apply_4(x_15, x_3, x_4, x_5, x_6);
x_26 = lean::cnstr_get(x_25, 0);
lean::inc(x_26);
x_28 = lean::cnstr_get(x_25, 1);
lean::inc(x_28);
lean::dec(x_25);
if (lean::obj_tag(x_26) == 0)
{
x_20 = x_26;
x_21 = x_28;
goto lbl_22;
}
else
{
obj* x_31; uint8 x_33; obj* x_34; 
x_31 = lean::cnstr_get(x_26, 0);
lean::inc(x_31);
x_33 = lean::cnstr_get_scalar<uint8>(x_26, sizeof(void*)*1);
if (lean::is_shared(x_26)) {
 lean::dec(x_26);
 x_34 = lean::box(0);
} else {
 lean::cnstr_release(x_26, 0);
 x_34 = x_26;
}
if (lean::obj_tag(x_1) == 0)
{
if (x_33 == 0)
{
uint8 x_35; obj* x_36; obj* x_37; 
x_35 = 0;
if (lean::is_scalar(x_34)) {
 x_36 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_36 = x_34;
}
lean::cnstr_set(x_36, 0, x_31);
lean::cnstr_set_scalar(x_36, sizeof(void*)*1, x_35);
x_37 = x_36;
x_20 = x_37;
x_21 = x_28;
goto lbl_22;
}
else
{
obj* x_38; obj* x_39; 
if (lean::is_scalar(x_34)) {
 x_38 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_38 = x_34;
}
lean::cnstr_set(x_38, 0, x_31);
lean::cnstr_set_scalar(x_38, sizeof(void*)*1, x_33);
x_39 = x_38;
x_20 = x_39;
x_21 = x_28;
goto lbl_22;
}
}
else
{
obj* x_40; obj* x_42; obj* x_44; obj* x_45; obj* x_47; obj* x_49; obj* x_52; obj* x_54; obj* x_55; obj* x_56; 
x_40 = lean::cnstr_get(x_31, 3);
lean::inc(x_40);
x_42 = l_option_get___main___at_lean_parser_run___spec__2(x_40);
lean::inc(x_1);
x_44 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_44, 0, x_42);
lean::cnstr_set(x_44, 1, x_1);
x_45 = lean::cnstr_get(x_31, 0);
lean::inc(x_45);
x_47 = lean::cnstr_get(x_31, 1);
lean::inc(x_47);
x_49 = lean::cnstr_get(x_31, 2);
lean::inc(x_49);
lean::dec(x_31);
x_52 = l_list_reverse___rarg(x_44);
lean::inc(x_0);
x_54 = l_lean_parser_syntax_mk__node(x_0, x_52);
x_55 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_55, 0, x_54);
x_56 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_56, 0, x_45);
lean::cnstr_set(x_56, 1, x_47);
lean::cnstr_set(x_56, 2, x_49);
lean::cnstr_set(x_56, 3, x_55);
if (x_33 == 0)
{
uint8 x_57; obj* x_58; obj* x_59; 
x_57 = 0;
if (lean::is_scalar(x_34)) {
 x_58 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_58 = x_34;
}
lean::cnstr_set(x_58, 0, x_56);
lean::cnstr_set_scalar(x_58, sizeof(void*)*1, x_57);
x_59 = x_58;
x_20 = x_59;
x_21 = x_28;
goto lbl_22;
}
else
{
obj* x_60; obj* x_61; 
if (lean::is_scalar(x_34)) {
 x_60 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_60 = x_34;
}
lean::cnstr_set(x_60, 0, x_56);
lean::cnstr_set_scalar(x_60, sizeof(void*)*1, x_33);
x_61 = x_60;
x_20 = x_61;
x_21 = x_28;
goto lbl_22;
}
}
}
lbl_22:
{
if (lean::obj_tag(x_20) == 0)
{
obj* x_62; obj* x_64; obj* x_66; obj* x_68; obj* x_69; obj* x_70; obj* x_72; obj* x_73; 
x_62 = lean::cnstr_get(x_20, 0);
lean::inc(x_62);
x_64 = lean::cnstr_get(x_20, 1);
lean::inc(x_64);
x_66 = lean::cnstr_get(x_20, 2);
lean::inc(x_66);
if (lean::is_shared(x_20)) {
 lean::dec(x_20);
 x_68 = lean::box(0);
} else {
 lean::cnstr_release(x_20, 0);
 lean::cnstr_release(x_20, 1);
 lean::cnstr_release(x_20, 2);
 x_68 = x_20;
}
if (lean::is_scalar(x_19)) {
 x_69 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_69 = x_19;
}
lean::cnstr_set(x_69, 0, x_62);
lean::cnstr_set(x_69, 1, x_1);
x_70 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_70);
if (lean::is_scalar(x_68)) {
 x_72 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_72 = x_68;
}
lean::cnstr_set(x_72, 0, x_69);
lean::cnstr_set(x_72, 1, x_64);
lean::cnstr_set(x_72, 2, x_70);
x_73 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_66, x_72);
if (lean::obj_tag(x_73) == 0)
{
obj* x_74; obj* x_76; obj* x_78; obj* x_81; obj* x_82; obj* x_84; obj* x_86; obj* x_87; obj* x_88; 
x_74 = lean::cnstr_get(x_73, 0);
lean::inc(x_74);
x_76 = lean::cnstr_get(x_73, 1);
lean::inc(x_76);
x_78 = lean::cnstr_get(x_73, 2);
lean::inc(x_78);
lean::dec(x_73);
x_81 = l_list_mfoldl___main___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__10(x_0, x_74, x_17, x_3, x_4, x_76, x_21);
x_82 = lean::cnstr_get(x_81, 0);
lean::inc(x_82);
x_84 = lean::cnstr_get(x_81, 1);
lean::inc(x_84);
if (lean::is_shared(x_81)) {
 lean::dec(x_81);
 x_86 = lean::box(0);
} else {
 lean::cnstr_release(x_81, 0);
 lean::cnstr_release(x_81, 1);
 x_86 = x_81;
}
x_87 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_78, x_82);
if (lean::is_scalar(x_86)) {
 x_88 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_88 = x_86;
}
lean::cnstr_set(x_88, 0, x_87);
lean::cnstr_set(x_88, 1, x_84);
return x_88;
}
else
{
obj* x_93; uint8 x_95; obj* x_96; obj* x_97; obj* x_98; obj* x_99; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_17);
x_93 = lean::cnstr_get(x_73, 0);
lean::inc(x_93);
x_95 = lean::cnstr_get_scalar<uint8>(x_73, sizeof(void*)*1);
if (lean::is_shared(x_73)) {
 lean::dec(x_73);
 x_96 = lean::box(0);
} else {
 lean::cnstr_release(x_73, 0);
 x_96 = x_73;
}
if (lean::is_scalar(x_96)) {
 x_97 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_97 = x_96;
}
lean::cnstr_set(x_97, 0, x_93);
lean::cnstr_set_scalar(x_97, sizeof(void*)*1, x_95);
x_98 = x_97;
x_99 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_99, 0, x_98);
lean::cnstr_set(x_99, 1, x_21);
return x_99;
}
}
else
{
obj* x_106; uint8 x_108; obj* x_109; obj* x_110; obj* x_111; obj* x_112; 
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_17);
lean::dec(x_19);
x_106 = lean::cnstr_get(x_20, 0);
lean::inc(x_106);
x_108 = lean::cnstr_get_scalar<uint8>(x_20, sizeof(void*)*1);
if (lean::is_shared(x_20)) {
 lean::dec(x_20);
 x_109 = lean::box(0);
} else {
 lean::cnstr_release(x_20, 0);
 x_109 = x_20;
}
if (lean::is_scalar(x_109)) {
 x_110 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_110 = x_109;
}
lean::cnstr_set(x_110, 0, x_106);
lean::cnstr_set_scalar(x_110, sizeof(void*)*1, x_108);
x_111 = x_110;
x_112 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_112, 0, x_111);
lean::cnstr_set(x_112, 1, x_21);
return x_112;
}
}
}
}
}
obj* l_lean_parser_combinators_node___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__9(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_8; obj* x_9; obj* x_11; obj* x_13; 
x_6 = lean::box(0);
lean::inc(x_0);
x_8 = l_list_mfoldl___main___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__10(x_0, x_6, x_1, x_2, x_3, x_4, x_5);
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
if (lean::is_shared(x_8)) {
 lean::dec(x_8);
 x_13 = lean::box(0);
} else {
 lean::cnstr_release(x_8, 0);
 lean::cnstr_release(x_8, 1);
 x_13 = x_8;
}
if (lean::obj_tag(x_9) == 0)
{
obj* x_14; obj* x_16; obj* x_18; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_25; obj* x_26; obj* x_27; 
x_14 = lean::cnstr_get(x_9, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_9, 1);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_9, 2);
lean::inc(x_18);
if (lean::is_shared(x_9)) {
 lean::dec(x_9);
 x_20 = lean::box(0);
} else {
 lean::cnstr_release(x_9, 0);
 lean::cnstr_release(x_9, 1);
 lean::cnstr_release(x_9, 2);
 x_20 = x_9;
}
x_21 = l_list_reverse___rarg(x_14);
x_22 = l_lean_parser_syntax_mk__node(x_0, x_21);
x_23 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_23);
if (lean::is_scalar(x_20)) {
 x_25 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_25 = x_20;
}
lean::cnstr_set(x_25, 0, x_22);
lean::cnstr_set(x_25, 1, x_16);
lean::cnstr_set(x_25, 2, x_23);
x_26 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_18, x_25);
if (lean::is_scalar(x_13)) {
 x_27 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_27 = x_13;
}
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_11);
return x_27;
}
else
{
obj* x_29; uint8 x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; 
lean::dec(x_0);
x_29 = lean::cnstr_get(x_9, 0);
lean::inc(x_29);
x_31 = lean::cnstr_get_scalar<uint8>(x_9, sizeof(void*)*1);
if (lean::is_shared(x_9)) {
 lean::dec(x_9);
 x_32 = lean::box(0);
} else {
 lean::cnstr_release(x_9, 0);
 x_32 = x_9;
}
if (lean::is_scalar(x_32)) {
 x_33 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_33 = x_32;
}
lean::cnstr_set(x_33, 0, x_29);
lean::cnstr_set_scalar(x_33, sizeof(void*)*1, x_31);
x_34 = x_33;
if (lean::is_scalar(x_13)) {
 x_35 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_35 = x_13;
}
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_11);
return x_35;
}
}
}
obj* _init_l_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens() {
_start:
{
obj* x_0; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_0 = lean::box(0);
lean::inc(x_0);
lean::inc(x_0);
x_3 = l_lean_parser_list_cons_tokens___rarg(x_0, x_0);
x_4 = l_lean_parser_list_cons_tokens___rarg(x_0, x_3);
x_5 = l_lean_parser_tokens___rarg(x_4);
x_6 = l_lean_parser_tokens___rarg(x_5);
return x_6;
}
}
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint32 x_5; obj* x_6; 
x_5 = lean::unbox_uint32(x_0);
x_6 = l_lean_parser_monad__parsec_ch___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__1(x_5, x_1, x_2, x_3, x_4);
return x_6;
}
}
obj* l_lean_parser_parsec__t_lookahead___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__view___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_7; uint32 x_8; obj* x_13; obj* x_14; obj* x_16; 
x_7 = lean::mk_nat_obj(46u);
x_8 = lean::unbox_uint32(x_7);
lean::dec(x_7);
lean::inc(x_2);
lean::inc(x_1);
lean::inc(x_0);
x_13 = l_lean_parser_monad__parsec_ch___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__1(x_8, x_0, x_1, x_2, x_3);
x_14 = lean::cnstr_get(x_13, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_13, 1);
lean::inc(x_16);
lean::dec(x_13);
if (lean::obj_tag(x_14) == 0)
{
obj* x_19; obj* x_21; obj* x_23; obj* x_24; uint32 x_25; obj* x_29; obj* x_30; obj* x_32; 
x_19 = lean::cnstr_get(x_14, 1);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_14, 2);
lean::inc(x_21);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_23 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 lean::cnstr_release(x_14, 1);
 lean::cnstr_release(x_14, 2);
 x_23 = x_14;
}
x_24 = l_lean_id__begin__escape;
x_25 = lean::unbox_uint32(x_24);
lean::inc(x_19);
lean::inc(x_1);
lean::inc(x_0);
x_29 = l_lean_parser_monad__parsec_ch___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__1(x_25, x_0, x_1, x_19, x_16);
x_30 = lean::cnstr_get(x_29, 0);
lean::inc(x_30);
x_32 = lean::cnstr_get(x_29, 1);
lean::inc(x_32);
lean::dec(x_29);
if (lean::obj_tag(x_30) == 0)
{
obj* x_39; 
lean::dec(x_19);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_23);
x_39 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_21, x_30);
x_4 = x_39;
x_5 = x_32;
goto lbl_6;
}
else
{
obj* x_40; uint8 x_42; 
x_40 = lean::cnstr_get(x_30, 0);
lean::inc(x_40);
x_42 = lean::cnstr_get_scalar<uint8>(x_30, sizeof(void*)*1);
if (x_42 == 0)
{
uint8 x_44; 
lean::dec(x_30);
x_44 = lean::string_iterator_has_next(x_19);
if (x_44 == 0)
{
obj* x_46; obj* x_47; obj* x_48; obj* x_52; obj* x_53; obj* x_55; obj* x_58; obj* x_60; obj* x_61; obj* x_62; 
lean::dec(x_23);
x_46 = lean::box(0);
x_47 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_48 = l_mjoin___rarg___closed__1;
lean::inc(x_46);
lean::inc(x_48);
lean::inc(x_47);
x_52 = l_lean_parser_monad__parsec_error___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__3___rarg(x_47, x_48, x_46, x_46, x_0, x_1, x_19, x_32);
x_53 = lean::cnstr_get(x_52, 0);
lean::inc(x_53);
x_55 = lean::cnstr_get(x_52, 1);
lean::inc(x_55);
lean::dec(x_52);
x_58 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_58);
x_60 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_58, x_53);
x_61 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_40, x_60);
x_62 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_21, x_61);
x_4 = x_62;
x_5 = x_55;
goto lbl_6;
}
else
{
uint32 x_63; uint8 x_64; 
x_63 = lean::string_iterator_curr(x_19);
x_64 = l_lean_is__id__first(x_63);
if (x_64 == 0)
{
obj* x_66; obj* x_67; obj* x_69; obj* x_71; obj* x_72; obj* x_73; obj* x_76; obj* x_77; obj* x_79; obj* x_82; obj* x_84; obj* x_85; obj* x_86; 
lean::dec(x_23);
x_66 = l_char_quote__core(x_63);
x_67 = l_char_has__repr___closed__1;
lean::inc(x_67);
x_69 = lean::string_append(x_67, x_66);
lean::dec(x_66);
x_71 = lean::string_append(x_69, x_67);
x_72 = lean::box(0);
x_73 = l_mjoin___rarg___closed__1;
lean::inc(x_72);
lean::inc(x_73);
x_76 = l_lean_parser_monad__parsec_error___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__3___rarg(x_71, x_73, x_72, x_72, x_0, x_1, x_19, x_32);
x_77 = lean::cnstr_get(x_76, 0);
lean::inc(x_77);
x_79 = lean::cnstr_get(x_76, 1);
lean::inc(x_79);
lean::dec(x_76);
x_82 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_82);
x_84 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_82, x_77);
x_85 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_40, x_84);
x_86 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_21, x_85);
x_4 = x_86;
x_5 = x_79;
goto lbl_6;
}
else
{
obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_40);
x_90 = lean::string_iterator_next(x_19);
x_91 = lean::box(0);
x_92 = lean::box_uint32(x_63);
if (lean::is_scalar(x_23)) {
 x_93 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_93 = x_23;
}
lean::cnstr_set(x_93, 0, x_92);
lean::cnstr_set(x_93, 1, x_90);
lean::cnstr_set(x_93, 2, x_91);
x_94 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_21, x_93);
x_4 = x_94;
x_5 = x_32;
goto lbl_6;
}
}
}
else
{
obj* x_100; 
lean::dec(x_19);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_23);
lean::dec(x_40);
x_100 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_21, x_30);
x_4 = x_100;
x_5 = x_32;
goto lbl_6;
}
}
}
else
{
obj* x_103; uint8 x_105; obj* x_106; obj* x_107; obj* x_108; 
lean::dec(x_1);
lean::dec(x_0);
x_103 = lean::cnstr_get(x_14, 0);
lean::inc(x_103);
x_105 = lean::cnstr_get_scalar<uint8>(x_14, sizeof(void*)*1);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_106 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 x_106 = x_14;
}
if (lean::is_scalar(x_106)) {
 x_107 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_107 = x_106;
}
lean::cnstr_set(x_107, 0, x_103);
lean::cnstr_set_scalar(x_107, sizeof(void*)*1, x_105);
x_108 = x_107;
x_4 = x_108;
x_5 = x_16;
goto lbl_6;
}
lbl_6:
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_109; obj* x_111; obj* x_112; obj* x_114; obj* x_115; 
x_109 = lean::cnstr_get(x_4, 0);
lean::inc(x_109);
if (lean::is_shared(x_4)) {
 lean::dec(x_4);
 x_111 = lean::box(0);
} else {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_release(x_4, 1);
 lean::cnstr_release(x_4, 2);
 x_111 = x_4;
}
x_112 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_112);
if (lean::is_scalar(x_111)) {
 x_114 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_114 = x_111;
}
lean::cnstr_set(x_114, 0, x_109);
lean::cnstr_set(x_114, 1, x_2);
lean::cnstr_set(x_114, 2, x_112);
x_115 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_115, 0, x_114);
lean::cnstr_set(x_115, 1, x_5);
return x_115;
}
else
{
obj* x_117; 
lean::dec(x_2);
x_117 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_117, 0, x_4);
lean::cnstr_set(x_117, 1, x_5);
return x_117;
}
}
}
}
obj* l_lean_parser_detail__ident__suffix_parser_lean_parser_has__view___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_11; 
x_4 = l_lean_parser_parsec__t_lookahead___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__view___spec__1(x_0, x_1, x_2, x_3);
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
x_10 = l_lean_parser_parsec__t_try__mk__res___rarg(x_5);
if (lean::is_scalar(x_9)) {
 x_11 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_11 = x_9;
}
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_7);
return x_11;
}
}
obj* l_lean_parser_detail__ident__suffix_parser_lean_parser_has__view___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_8; obj* x_9; obj* x_11; obj* x_13; 
x_6 = l_lean_name_to__string___closed__1;
lean::inc(x_6);
x_8 = l_lean_parser_monad__parsec_str__core___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__6(x_6, x_0, x_2, x_3, x_4, x_5);
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
if (lean::is_shared(x_8)) {
 lean::dec(x_8);
 x_13 = lean::box(0);
} else {
 lean::cnstr_release(x_8, 0);
 lean::cnstr_release(x_8, 1);
 x_13 = x_8;
}
if (lean::obj_tag(x_9) == 0)
{
obj* x_14; obj* x_16; obj* x_18; obj* x_20; obj* x_21; obj* x_23; obj* x_24; obj* x_25; 
x_14 = lean::cnstr_get(x_9, 1);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_9, 2);
lean::inc(x_16);
if (lean::is_shared(x_9)) {
 lean::dec(x_9);
 x_18 = lean::box(0);
} else {
 lean::cnstr_release(x_9, 0);
 lean::cnstr_release(x_9, 1);
 lean::cnstr_release(x_9, 2);
 x_18 = x_9;
}
lean::inc(x_14);
x_20 = l_lean_parser_mk__raw__res(x_1, x_14);
x_21 = l_lean_parser_finish__comment__block___closed__2;
lean::inc(x_21);
if (lean::is_scalar(x_18)) {
 x_23 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_23 = x_18;
}
lean::cnstr_set(x_23, 0, x_20);
lean::cnstr_set(x_23, 1, x_14);
lean::cnstr_set(x_23, 2, x_21);
x_24 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_23);
if (lean::is_scalar(x_13)) {
 x_25 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_25 = x_13;
}
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_11);
return x_25;
}
else
{
obj* x_27; uint8 x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; 
lean::dec(x_1);
x_27 = lean::cnstr_get(x_9, 0);
lean::inc(x_27);
x_29 = lean::cnstr_get_scalar<uint8>(x_9, sizeof(void*)*1);
if (lean::is_shared(x_9)) {
 lean::dec(x_9);
 x_30 = lean::box(0);
} else {
 lean::cnstr_release(x_9, 0);
 x_30 = x_9;
}
if (lean::is_scalar(x_30)) {
 x_31 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_31 = x_30;
}
lean::cnstr_set(x_31, 0, x_27);
lean::cnstr_set_scalar(x_31, sizeof(void*)*1, x_29);
x_32 = x_31;
if (lean::is_scalar(x_13)) {
 x_33 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_33 = x_13;
}
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_11);
return x_33;
}
}
}
obj* _init_l_lean_parser_detail__ident__suffix_parser_lean_parser_has__view() {
_start:
{
obj* x_0; obj* x_2; obj* x_3; obj* x_5; obj* x_6; obj* x_9; obj* x_10; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_30; obj* x_31; obj* x_35; obj* x_36; obj* x_37; 
x_0 = l_lean_parser_basic__parser__m_monad;
lean::inc(x_0);
x_2 = l_reader__t_monad___rarg(x_0);
x_3 = l_lean_parser_basic__parser__m_monad__except;
lean::inc(x_3);
x_5 = l_reader__t_monad__except___rarg(x_3);
x_6 = l_lean_parser_basic__parser__m_lean_parser_monad__parsec;
lean::inc(x_6);
lean::inc(x_0);
x_9 = l_lean_parser_rec__t_lean_parser_monad__parsec___rarg(x_0, lean::box(0), x_6);
x_10 = l_lean_parser_basic__parser__m_alternative;
lean::inc(x_10);
lean::inc(x_0);
x_13 = l_reader__t_alternative___rarg(x_0, x_10);
x_14 = lean::mk_string(".");
x_15 = l_string_quote(x_14);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_16, 0, x_15);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_with__trailing___rarg___lambda__1), 2, 0);
x_18 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_lift___at_lean_parser_with__trailing___spec__1___rarg), 4, 1);
lean::closure_set(x_18, 0, x_17);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_lift___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__5___rarg), 5, 1);
lean::closure_set(x_19, 0, x_18);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_detail__ident__suffix_parser_lean_parser_has__view___lambda__2), 6, 1);
lean::closure_set(x_20, 0, x_16);
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_bind___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__7___rarg), 6, 2);
lean::closure_set(x_21, 0, x_19);
lean::closure_set(x_21, 1, x_20);
x_22 = lean::box(0);
lean::inc(x_22);
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_rec__t_recurse___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__8), 5, 1);
lean::closure_set(x_24, 0, x_22);
x_25 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_22);
x_26 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_26, 0, x_21);
lean::cnstr_set(x_26, 1, x_25);
x_27 = l_lean_parser_detail__ident__suffix;
lean::inc(x_26);
lean::inc(x_27);
x_30 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__9), 6, 2);
lean::closure_set(x_30, 0, x_27);
lean::closure_set(x_30, 1, x_26);
x_31 = l_lean_parser_detail__ident__suffix_has__view;
lean::inc(x_31);
lean::inc(x_27);
lean::inc(x_13);
x_35 = l_lean_parser_combinators_node_view___rarg(x_2, x_5, x_9, x_13, x_27, x_26, x_31);
x_36 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_detail__ident__suffix_parser_lean_parser_has__view___lambda__1), 4, 0);
x_37 = l_lean_parser_combinators_seq__right_view___rarg(x_13, lean::box(0), lean::box(0), x_36, x_30, x_35);
return x_37;
}
}
obj* l_lean_parser_parsec__t_lookahead___at_lean_parser_detail__ident__suffix_parser___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_7; uint32 x_8; obj* x_13; obj* x_14; obj* x_16; 
x_7 = lean::mk_nat_obj(46u);
x_8 = lean::unbox_uint32(x_7);
lean::dec(x_7);
lean::inc(x_2);
lean::inc(x_1);
lean::inc(x_0);
x_13 = l_lean_parser_monad__parsec_ch___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__1(x_8, x_0, x_1, x_2, x_3);
x_14 = lean::cnstr_get(x_13, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_13, 1);
lean::inc(x_16);
lean::dec(x_13);
if (lean::obj_tag(x_14) == 0)
{
obj* x_19; obj* x_21; obj* x_23; obj* x_24; uint32 x_25; obj* x_29; obj* x_30; obj* x_32; 
x_19 = lean::cnstr_get(x_14, 1);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_14, 2);
lean::inc(x_21);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_23 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 lean::cnstr_release(x_14, 1);
 lean::cnstr_release(x_14, 2);
 x_23 = x_14;
}
x_24 = l_lean_id__begin__escape;
x_25 = lean::unbox_uint32(x_24);
lean::inc(x_19);
lean::inc(x_1);
lean::inc(x_0);
x_29 = l_lean_parser_monad__parsec_ch___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__1(x_25, x_0, x_1, x_19, x_16);
x_30 = lean::cnstr_get(x_29, 0);
lean::inc(x_30);
x_32 = lean::cnstr_get(x_29, 1);
lean::inc(x_32);
lean::dec(x_29);
if (lean::obj_tag(x_30) == 0)
{
obj* x_39; 
lean::dec(x_19);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_23);
x_39 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_21, x_30);
x_4 = x_39;
x_5 = x_32;
goto lbl_6;
}
else
{
obj* x_40; uint8 x_42; 
x_40 = lean::cnstr_get(x_30, 0);
lean::inc(x_40);
x_42 = lean::cnstr_get_scalar<uint8>(x_30, sizeof(void*)*1);
if (x_42 == 0)
{
uint8 x_44; 
lean::dec(x_30);
x_44 = lean::string_iterator_has_next(x_19);
if (x_44 == 0)
{
obj* x_46; obj* x_47; obj* x_48; obj* x_52; obj* x_53; obj* x_55; obj* x_58; obj* x_60; obj* x_61; obj* x_62; 
lean::dec(x_23);
x_46 = lean::box(0);
x_47 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_48 = l_mjoin___rarg___closed__1;
lean::inc(x_46);
lean::inc(x_48);
lean::inc(x_47);
x_52 = l_lean_parser_monad__parsec_error___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__3___rarg(x_47, x_48, x_46, x_46, x_0, x_1, x_19, x_32);
x_53 = lean::cnstr_get(x_52, 0);
lean::inc(x_53);
x_55 = lean::cnstr_get(x_52, 1);
lean::inc(x_55);
lean::dec(x_52);
x_58 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_58);
x_60 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_58, x_53);
x_61 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_40, x_60);
x_62 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_21, x_61);
x_4 = x_62;
x_5 = x_55;
goto lbl_6;
}
else
{
uint32 x_63; uint8 x_64; 
x_63 = lean::string_iterator_curr(x_19);
x_64 = l_lean_is__id__first(x_63);
if (x_64 == 0)
{
obj* x_66; obj* x_67; obj* x_69; obj* x_71; obj* x_72; obj* x_73; obj* x_76; obj* x_77; obj* x_79; obj* x_82; obj* x_84; obj* x_85; obj* x_86; 
lean::dec(x_23);
x_66 = l_char_quote__core(x_63);
x_67 = l_char_has__repr___closed__1;
lean::inc(x_67);
x_69 = lean::string_append(x_67, x_66);
lean::dec(x_66);
x_71 = lean::string_append(x_69, x_67);
x_72 = lean::box(0);
x_73 = l_mjoin___rarg___closed__1;
lean::inc(x_72);
lean::inc(x_73);
x_76 = l_lean_parser_monad__parsec_error___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__3___rarg(x_71, x_73, x_72, x_72, x_0, x_1, x_19, x_32);
x_77 = lean::cnstr_get(x_76, 0);
lean::inc(x_77);
x_79 = lean::cnstr_get(x_76, 1);
lean::inc(x_79);
lean::dec(x_76);
x_82 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_82);
x_84 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_82, x_77);
x_85 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_40, x_84);
x_86 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_21, x_85);
x_4 = x_86;
x_5 = x_79;
goto lbl_6;
}
else
{
obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_40);
x_90 = lean::string_iterator_next(x_19);
x_91 = lean::box(0);
x_92 = lean::box_uint32(x_63);
if (lean::is_scalar(x_23)) {
 x_93 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_93 = x_23;
}
lean::cnstr_set(x_93, 0, x_92);
lean::cnstr_set(x_93, 1, x_90);
lean::cnstr_set(x_93, 2, x_91);
x_94 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_21, x_93);
x_4 = x_94;
x_5 = x_32;
goto lbl_6;
}
}
}
else
{
obj* x_100; 
lean::dec(x_19);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_23);
lean::dec(x_40);
x_100 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_21, x_30);
x_4 = x_100;
x_5 = x_32;
goto lbl_6;
}
}
}
else
{
obj* x_103; uint8 x_105; obj* x_106; obj* x_107; obj* x_108; 
lean::dec(x_1);
lean::dec(x_0);
x_103 = lean::cnstr_get(x_14, 0);
lean::inc(x_103);
x_105 = lean::cnstr_get_scalar<uint8>(x_14, sizeof(void*)*1);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_106 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 x_106 = x_14;
}
if (lean::is_scalar(x_106)) {
 x_107 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_107 = x_106;
}
lean::cnstr_set(x_107, 0, x_103);
lean::cnstr_set_scalar(x_107, sizeof(void*)*1, x_105);
x_108 = x_107;
x_4 = x_108;
x_5 = x_16;
goto lbl_6;
}
lbl_6:
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_109; obj* x_111; obj* x_112; obj* x_114; obj* x_115; 
x_109 = lean::cnstr_get(x_4, 0);
lean::inc(x_109);
if (lean::is_shared(x_4)) {
 lean::dec(x_4);
 x_111 = lean::box(0);
} else {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_release(x_4, 1);
 lean::cnstr_release(x_4, 2);
 x_111 = x_4;
}
x_112 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_112);
if (lean::is_scalar(x_111)) {
 x_114 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_114 = x_111;
}
lean::cnstr_set(x_114, 0, x_109);
lean::cnstr_set(x_114, 1, x_2);
lean::cnstr_set(x_114, 2, x_112);
x_115 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_115, 0, x_114);
lean::cnstr_set(x_115, 1, x_5);
return x_115;
}
else
{
obj* x_117; 
lean::dec(x_2);
x_117 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_117, 0, x_4);
lean::cnstr_set(x_117, 1, x_5);
return x_117;
}
}
}
}
obj* _init_l_lean_parser_detail__ident__suffix_parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_10; obj* x_11; obj* x_12; 
x_0 = lean::mk_string(".");
x_1 = l_string_quote(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_2, 0, x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_with__trailing___rarg___lambda__1), 2, 0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_lift___at_lean_parser_with__trailing___spec__1___rarg), 4, 1);
lean::closure_set(x_4, 0, x_3);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_lift___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__5___rarg), 5, 1);
lean::closure_set(x_5, 0, x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_detail__ident__suffix_parser_lean_parser_has__view___lambda__2), 6, 1);
lean::closure_set(x_6, 0, x_2);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_bind___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__7___rarg), 6, 2);
lean::closure_set(x_7, 0, x_5);
lean::closure_set(x_7, 1, x_6);
x_8 = lean::box(0);
lean::inc(x_8);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_rec__t_recurse___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__8), 5, 1);
lean::closure_set(x_10, 0, x_8);
x_11 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_8);
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_7);
lean::cnstr_set(x_12, 1, x_11);
return x_12;
}
}
obj* l_lean_parser_detail__ident__suffix_parser(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_6; obj* x_7; obj* x_9; obj* x_11; obj* x_12; 
lean::inc(x_1);
lean::inc(x_0);
x_6 = l_lean_parser_parsec__t_lookahead___at_lean_parser_detail__ident__suffix_parser___spec__1(x_0, x_1, x_2, x_3);
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_6, 1);
lean::inc(x_9);
if (lean::is_shared(x_6)) {
 lean::dec(x_6);
 x_11 = lean::box(0);
} else {
 lean::cnstr_release(x_6, 0);
 lean::cnstr_release(x_6, 1);
 x_11 = x_6;
}
x_12 = l_lean_parser_parsec__t_try__mk__res___rarg(x_7);
if (lean::obj_tag(x_12) == 0)
{
obj* x_13; obj* x_15; obj* x_18; obj* x_19; obj* x_22; obj* x_23; obj* x_25; obj* x_28; obj* x_29; 
x_13 = lean::cnstr_get(x_12, 1);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_12, 2);
lean::inc(x_15);
lean::dec(x_12);
x_18 = l_lean_parser_detail__ident__suffix;
x_19 = l_lean_parser_detail__ident__suffix_parser___closed__1;
lean::inc(x_19);
lean::inc(x_18);
x_22 = l_lean_parser_combinators_node___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__9(x_18, x_19, x_0, x_1, x_13, x_9);
x_23 = lean::cnstr_get(x_22, 0);
lean::inc(x_23);
x_25 = lean::cnstr_get(x_22, 1);
lean::inc(x_25);
lean::dec(x_22);
x_28 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_23);
if (lean::is_scalar(x_11)) {
 x_29 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_29 = x_11;
}
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_25);
return x_29;
}
else
{
obj* x_32; uint8 x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
lean::dec(x_1);
lean::dec(x_0);
x_32 = lean::cnstr_get(x_12, 0);
lean::inc(x_32);
x_34 = lean::cnstr_get_scalar<uint8>(x_12, sizeof(void*)*1);
if (lean::is_shared(x_12)) {
 lean::dec(x_12);
 x_35 = lean::box(0);
} else {
 lean::cnstr_release(x_12, 0);
 x_35 = x_12;
}
if (lean::is_scalar(x_35)) {
 x_36 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_36 = x_35;
}
lean::cnstr_set(x_36, 0, x_32);
lean::cnstr_set_scalar(x_36, sizeof(void*)*1, x_34);
x_37 = x_36;
if (lean::is_scalar(x_11)) {
 x_38 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_38 = x_11;
}
lean::cnstr_set(x_38, 0, x_37);
lean::cnstr_set(x_38, 1, x_9);
return x_38;
}
}
}
obj* _init_l_lean_parser_detail__ident() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("detail_ident");
x_6 = lean_name_mk_string(x_4, x_5);
return x_6;
}
}
obj* _init_l_lean_parser_detail__ident_has__view_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; 
x_0 = l_lean_parser_detail__ident__suffix_has__view;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::box(3);
x_4 = lean::apply_1(x_1, x_3);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
return x_5;
}
}
obj* _init_l_lean_parser_detail__ident_has__view_x_27___lambda__1___closed__2() {
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
obj* x_5; obj* x_6; obj* x_8; 
x_5 = l_lean_parser_detail__ident__part_has__view;
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
x_8 = lean::apply_1(x_6, x_1);
if (lean::obj_tag(x_0) == 0)
{
obj* x_10; obj* x_11; 
lean::dec(x_0);
x_10 = lean::box(3);
x_11 = l_lean_parser_syntax_as__node___main(x_10);
if (lean::obj_tag(x_11) == 0)
{
obj* x_13; obj* x_15; 
lean::dec(x_11);
x_13 = l_lean_parser_detail__ident_has__view_x_27___lambda__1___closed__1;
lean::inc(x_13);
x_15 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_15, 0, x_8);
lean::cnstr_set(x_15, 1, x_13);
return x_15;
}
else
{
obj* x_16; obj* x_18; obj* x_19; 
x_16 = lean::cnstr_get(x_11, 0);
lean::inc(x_16);
if (lean::is_shared(x_11)) {
 lean::dec(x_11);
 x_18 = lean::box(0);
} else {
 lean::cnstr_release(x_11, 0);
 x_18 = x_11;
}
x_19 = lean::cnstr_get(x_16, 1);
lean::inc(x_19);
lean::dec(x_16);
if (lean::obj_tag(x_19) == 0)
{
obj* x_24; obj* x_25; 
lean::dec(x_18);
lean::dec(x_19);
x_24 = lean::box(0);
x_25 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_25, 0, x_8);
lean::cnstr_set(x_25, 1, x_24);
return x_25;
}
else
{
obj* x_26; obj* x_28; 
x_26 = lean::cnstr_get(x_19, 0);
lean::inc(x_26);
x_28 = lean::cnstr_get(x_19, 1);
lean::inc(x_28);
lean::dec(x_19);
if (lean::obj_tag(x_28) == 0)
{
obj* x_32; obj* x_33; obj* x_35; obj* x_36; obj* x_37; 
lean::dec(x_28);
x_32 = l_lean_parser_detail__ident__suffix_has__view;
x_33 = lean::cnstr_get(x_32, 0);
lean::inc(x_33);
x_35 = lean::apply_1(x_33, x_26);
if (lean::is_scalar(x_18)) {
 x_36 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_36 = x_18;
}
lean::cnstr_set(x_36, 0, x_35);
x_37 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_37, 0, x_8);
lean::cnstr_set(x_37, 1, x_36);
return x_37;
}
else
{
obj* x_41; obj* x_43; 
lean::dec(x_18);
lean::dec(x_26);
lean::dec(x_28);
x_41 = l_lean_parser_detail__ident_has__view_x_27___lambda__1___closed__1;
lean::inc(x_41);
x_43 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_43, 0, x_8);
lean::cnstr_set(x_43, 1, x_41);
return x_43;
}
}
}
}
else
{
obj* x_44; obj* x_47; 
x_44 = lean::cnstr_get(x_0, 0);
lean::inc(x_44);
lean::dec(x_0);
x_47 = l_lean_parser_syntax_as__node___main(x_44);
if (lean::obj_tag(x_47) == 0)
{
obj* x_49; obj* x_51; 
lean::dec(x_47);
x_49 = l_lean_parser_detail__ident_has__view_x_27___lambda__1___closed__1;
lean::inc(x_49);
x_51 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_51, 0, x_8);
lean::cnstr_set(x_51, 1, x_49);
return x_51;
}
else
{
obj* x_52; obj* x_54; obj* x_55; 
x_52 = lean::cnstr_get(x_47, 0);
lean::inc(x_52);
if (lean::is_shared(x_47)) {
 lean::dec(x_47);
 x_54 = lean::box(0);
} else {
 lean::cnstr_release(x_47, 0);
 x_54 = x_47;
}
x_55 = lean::cnstr_get(x_52, 1);
lean::inc(x_55);
lean::dec(x_52);
if (lean::obj_tag(x_55) == 0)
{
obj* x_60; obj* x_61; 
lean::dec(x_54);
lean::dec(x_55);
x_60 = lean::box(0);
x_61 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_61, 0, x_8);
lean::cnstr_set(x_61, 1, x_60);
return x_61;
}
else
{
obj* x_62; obj* x_64; 
x_62 = lean::cnstr_get(x_55, 0);
lean::inc(x_62);
x_64 = lean::cnstr_get(x_55, 1);
lean::inc(x_64);
lean::dec(x_55);
if (lean::obj_tag(x_64) == 0)
{
obj* x_68; obj* x_69; obj* x_71; obj* x_72; obj* x_73; 
lean::dec(x_64);
x_68 = l_lean_parser_detail__ident__suffix_has__view;
x_69 = lean::cnstr_get(x_68, 0);
lean::inc(x_69);
x_71 = lean::apply_1(x_69, x_62);
if (lean::is_scalar(x_54)) {
 x_72 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_72 = x_54;
}
lean::cnstr_set(x_72, 0, x_71);
x_73 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_73, 0, x_8);
lean::cnstr_set(x_73, 1, x_72);
return x_73;
}
else
{
obj* x_77; obj* x_79; 
lean::dec(x_54);
lean::dec(x_62);
lean::dec(x_64);
x_77 = l_lean_parser_detail__ident_has__view_x_27___lambda__1___closed__1;
lean::inc(x_77);
x_79 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_79, 0, x_8);
lean::cnstr_set(x_79, 1, x_77);
return x_79;
}
}
}
}
}
}
}
obj* l_lean_parser_detail__ident_has__view_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_4 = l_lean_parser_syntax_as__node___main(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; 
lean::dec(x_4);
x_6 = l_lean_parser_detail__ident_has__view_x_27___lambda__1___closed__2;
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
obj* x_20; obj* x_21; obj* x_23; 
x_20 = l_lean_parser_detail__ident__part_has__view;
x_21 = lean::cnstr_get(x_20, 0);
lean::inc(x_21);
x_23 = lean::apply_1(x_21, x_2);
if (lean::obj_tag(x_1) == 0)
{
obj* x_25; obj* x_26; 
lean::dec(x_1);
x_25 = lean::box(3);
x_26 = l_lean_parser_syntax_as__node___main(x_25);
if (lean::obj_tag(x_26) == 0)
{
obj* x_28; obj* x_30; 
lean::dec(x_26);
x_28 = l_lean_parser_detail__ident_has__view_x_27___lambda__1___closed__1;
lean::inc(x_28);
x_30 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_30, 0, x_23);
lean::cnstr_set(x_30, 1, x_28);
return x_30;
}
else
{
obj* x_31; obj* x_33; obj* x_34; 
x_31 = lean::cnstr_get(x_26, 0);
lean::inc(x_31);
if (lean::is_shared(x_26)) {
 lean::dec(x_26);
 x_33 = lean::box(0);
} else {
 lean::cnstr_release(x_26, 0);
 x_33 = x_26;
}
x_34 = lean::cnstr_get(x_31, 1);
lean::inc(x_34);
lean::dec(x_31);
if (lean::obj_tag(x_34) == 0)
{
obj* x_39; obj* x_40; 
lean::dec(x_33);
lean::dec(x_34);
x_39 = lean::box(0);
x_40 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_40, 0, x_23);
lean::cnstr_set(x_40, 1, x_39);
return x_40;
}
else
{
obj* x_41; obj* x_43; 
x_41 = lean::cnstr_get(x_34, 0);
lean::inc(x_41);
x_43 = lean::cnstr_get(x_34, 1);
lean::inc(x_43);
lean::dec(x_34);
if (lean::obj_tag(x_43) == 0)
{
obj* x_47; obj* x_48; obj* x_50; obj* x_51; obj* x_52; 
lean::dec(x_43);
x_47 = l_lean_parser_detail__ident__suffix_has__view;
x_48 = lean::cnstr_get(x_47, 0);
lean::inc(x_48);
x_50 = lean::apply_1(x_48, x_41);
if (lean::is_scalar(x_33)) {
 x_51 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_51 = x_33;
}
lean::cnstr_set(x_51, 0, x_50);
x_52 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_52, 0, x_23);
lean::cnstr_set(x_52, 1, x_51);
return x_52;
}
else
{
obj* x_56; obj* x_58; 
lean::dec(x_33);
lean::dec(x_41);
lean::dec(x_43);
x_56 = l_lean_parser_detail__ident_has__view_x_27___lambda__1___closed__1;
lean::inc(x_56);
x_58 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_58, 0, x_23);
lean::cnstr_set(x_58, 1, x_56);
return x_58;
}
}
}
}
else
{
obj* x_59; obj* x_62; 
x_59 = lean::cnstr_get(x_1, 0);
lean::inc(x_59);
lean::dec(x_1);
x_62 = l_lean_parser_syntax_as__node___main(x_59);
if (lean::obj_tag(x_62) == 0)
{
obj* x_64; obj* x_66; 
lean::dec(x_62);
x_64 = l_lean_parser_detail__ident_has__view_x_27___lambda__1___closed__1;
lean::inc(x_64);
x_66 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_66, 0, x_23);
lean::cnstr_set(x_66, 1, x_64);
return x_66;
}
else
{
obj* x_67; obj* x_69; obj* x_70; 
x_67 = lean::cnstr_get(x_62, 0);
lean::inc(x_67);
if (lean::is_shared(x_62)) {
 lean::dec(x_62);
 x_69 = lean::box(0);
} else {
 lean::cnstr_release(x_62, 0);
 x_69 = x_62;
}
x_70 = lean::cnstr_get(x_67, 1);
lean::inc(x_70);
lean::dec(x_67);
if (lean::obj_tag(x_70) == 0)
{
obj* x_75; obj* x_76; 
lean::dec(x_70);
lean::dec(x_69);
x_75 = lean::box(0);
x_76 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_76, 0, x_23);
lean::cnstr_set(x_76, 1, x_75);
return x_76;
}
else
{
obj* x_77; obj* x_79; 
x_77 = lean::cnstr_get(x_70, 0);
lean::inc(x_77);
x_79 = lean::cnstr_get(x_70, 1);
lean::inc(x_79);
lean::dec(x_70);
if (lean::obj_tag(x_79) == 0)
{
obj* x_83; obj* x_84; obj* x_86; obj* x_87; obj* x_88; 
lean::dec(x_79);
x_83 = l_lean_parser_detail__ident__suffix_has__view;
x_84 = lean::cnstr_get(x_83, 0);
lean::inc(x_84);
x_86 = lean::apply_1(x_84, x_77);
if (lean::is_scalar(x_69)) {
 x_87 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_87 = x_69;
}
lean::cnstr_set(x_87, 0, x_86);
x_88 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_88, 0, x_23);
lean::cnstr_set(x_88, 1, x_87);
return x_88;
}
else
{
obj* x_92; obj* x_94; 
lean::dec(x_77);
lean::dec(x_69);
lean::dec(x_79);
x_92 = l_lean_parser_detail__ident_has__view_x_27___lambda__1___closed__1;
lean::inc(x_92);
x_94 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_94, 0, x_23);
lean::cnstr_set(x_94, 1, x_92);
return x_94;
}
}
}
}
}
}
}
obj* _init_l_lean_parser_detail__ident_has__view_x_27___lambda__2___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; 
x_0 = lean::box(0);
x_1 = l_lean_parser_no__kind;
lean::inc(x_0);
lean::inc(x_1);
x_4 = l_lean_parser_syntax_mk__node(x_1, x_0);
x_5 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_0);
return x_5;
}
}
obj* l_lean_parser_detail__ident_has__view_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_6; obj* x_7; obj* x_9; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
x_6 = l_lean_parser_detail__ident__part_has__view;
x_7 = lean::cnstr_get(x_6, 1);
lean::inc(x_7);
x_9 = lean::apply_1(x_7, x_1);
if (lean::obj_tag(x_3) == 0)
{
obj* x_11; obj* x_13; obj* x_14; obj* x_16; 
lean::dec(x_3);
x_11 = l_lean_parser_detail__ident_has__view_x_27___lambda__2___closed__1;
lean::inc(x_11);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_9);
lean::cnstr_set(x_13, 1, x_11);
x_14 = l_lean_parser_detail__ident;
lean::inc(x_14);
x_16 = l_lean_parser_syntax_mk__node(x_14, x_13);
return x_16;
}
else
{
obj* x_17; obj* x_20; obj* x_21; obj* x_22; obj* x_24; obj* x_26; obj* x_27; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_34; 
x_17 = lean::cnstr_get(x_3, 0);
lean::inc(x_17);
lean::dec(x_3);
x_20 = lean::box(0);
x_21 = l_lean_parser_detail__ident__suffix_has__view;
x_22 = lean::cnstr_get(x_21, 1);
lean::inc(x_22);
x_24 = lean::apply_1(x_22, x_17);
lean::inc(x_20);
x_26 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_26, 0, x_24);
lean::cnstr_set(x_26, 1, x_20);
x_27 = l_lean_parser_no__kind;
lean::inc(x_27);
x_29 = l_lean_parser_syntax_mk__node(x_27, x_26);
x_30 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_20);
x_31 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_31, 0, x_9);
lean::cnstr_set(x_31, 1, x_30);
x_32 = l_lean_parser_detail__ident;
lean::inc(x_32);
x_34 = l_lean_parser_syntax_mk__node(x_32, x_31);
return x_34;
}
}
}
obj* _init_l_lean_parser_detail__ident_has__view_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_detail__ident_has__view_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_detail__ident_has__view_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_lean_parser_detail__ident_has__view() {
_start:
{
obj* x_0; 
x_0 = l_lean_parser_detail__ident_has__view_x_27;
lean::inc(x_0);
return x_0;
}
}
obj* l_reader__t_lift___at_lean_parser_detail__ident_x_27___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_6; 
lean::dec(x_1);
x_6 = lean::apply_3(x_0, x_2, x_3, x_4);
return x_6;
}
}
obj* l_reader__t_lift___at_lean_parser_detail__ident_x_27___spec__1(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_lift___at_lean_parser_detail__ident_x_27___spec__1___rarg), 5, 0);
return x_2;
}
}
obj* l_lean_parser_combinators_optional___at_lean_parser_detail__ident_x_27___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_13; obj* x_14; obj* x_16; 
x_8 = lean::box(0);
lean::inc(x_3);
x_13 = lean::apply_4(x_0, x_1, x_2, x_3, x_4);
x_14 = lean::cnstr_get(x_13, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_13, 1);
lean::inc(x_16);
lean::dec(x_13);
if (lean::obj_tag(x_14) == 0)
{
if (lean::obj_tag(x_14) == 0)
{
obj* x_19; obj* x_21; obj* x_23; obj* x_25; obj* x_26; obj* x_27; obj* x_29; obj* x_30; 
x_19 = lean::cnstr_get(x_14, 0);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_14, 1);
lean::inc(x_21);
x_23 = lean::cnstr_get(x_14, 2);
lean::inc(x_23);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_25 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 lean::cnstr_release(x_14, 1);
 lean::cnstr_release(x_14, 2);
 x_25 = x_14;
}
x_26 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_26, 0, x_19);
x_27 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_27);
if (lean::is_scalar(x_25)) {
 x_29 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_29 = x_25;
}
lean::cnstr_set(x_29, 0, x_26);
lean::cnstr_set(x_29, 1, x_21);
lean::cnstr_set(x_29, 2, x_27);
x_30 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_23, x_29);
x_9 = x_30;
x_10 = x_16;
goto lbl_11;
}
else
{
obj* x_31; uint8 x_33; obj* x_34; obj* x_35; obj* x_36; 
x_31 = lean::cnstr_get(x_14, 0);
lean::inc(x_31);
x_33 = lean::cnstr_get_scalar<uint8>(x_14, sizeof(void*)*1);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_34 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 x_34 = x_14;
}
if (lean::is_scalar(x_34)) {
 x_35 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_35 = x_34;
}
lean::cnstr_set(x_35, 0, x_31);
lean::cnstr_set_scalar(x_35, sizeof(void*)*1, x_33);
x_36 = x_35;
x_9 = x_36;
x_10 = x_16;
goto lbl_11;
}
}
else
{
obj* x_37; uint8 x_39; obj* x_40; obj* x_41; obj* x_43; obj* x_45; obj* x_47; obj* x_50; obj* x_52; obj* x_53; obj* x_55; obj* x_56; obj* x_57; 
x_37 = lean::cnstr_get(x_14, 0);
lean::inc(x_37);
x_39 = lean::cnstr_get_scalar<uint8>(x_14, sizeof(void*)*1);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_40 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 x_40 = x_14;
}
x_41 = lean::cnstr_get(x_37, 0);
lean::inc(x_41);
x_43 = lean::cnstr_get(x_37, 1);
lean::inc(x_43);
x_45 = lean::cnstr_get(x_37, 2);
lean::inc(x_45);
x_47 = lean::cnstr_get(x_37, 3);
lean::inc(x_47);
lean::dec(x_37);
x_50 = l_option_get___main___at_lean_parser_run___spec__2(x_47);
lean::inc(x_8);
x_52 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_52, 0, x_50);
lean::cnstr_set(x_52, 1, x_8);
x_53 = l_lean_parser_no__kind;
lean::inc(x_53);
x_55 = l_lean_parser_syntax_mk__node(x_53, x_52);
x_56 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_56, 0, x_55);
x_57 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_57, 0, x_41);
lean::cnstr_set(x_57, 1, x_43);
lean::cnstr_set(x_57, 2, x_45);
lean::cnstr_set(x_57, 3, x_56);
if (x_39 == 0)
{
uint8 x_58; obj* x_59; obj* x_60; 
x_58 = 0;
if (lean::is_scalar(x_40)) {
 x_59 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_59 = x_40;
}
lean::cnstr_set(x_59, 0, x_57);
lean::cnstr_set_scalar(x_59, sizeof(void*)*1, x_58);
x_60 = x_59;
x_9 = x_60;
x_10 = x_16;
goto lbl_11;
}
else
{
obj* x_61; obj* x_62; 
if (lean::is_scalar(x_40)) {
 x_61 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_61 = x_40;
}
lean::cnstr_set(x_61, 0, x_57);
lean::cnstr_set_scalar(x_61, sizeof(void*)*1, x_39);
x_62 = x_61;
x_9 = x_62;
x_10 = x_16;
goto lbl_11;
}
}
lbl_7:
{
if (lean::obj_tag(x_5) == 0)
{
obj* x_63; obj* x_65; obj* x_67; obj* x_69; 
x_63 = lean::cnstr_get(x_5, 0);
lean::inc(x_63);
x_65 = lean::cnstr_get(x_5, 1);
lean::inc(x_65);
x_67 = lean::cnstr_get(x_5, 2);
lean::inc(x_67);
if (lean::is_shared(x_5)) {
 lean::dec(x_5);
 x_69 = lean::box(0);
} else {
 lean::cnstr_release(x_5, 0);
 lean::cnstr_release(x_5, 1);
 lean::cnstr_release(x_5, 2);
 x_69 = x_5;
}
if (lean::obj_tag(x_63) == 0)
{
obj* x_71; obj* x_72; obj* x_75; obj* x_76; obj* x_77; 
lean::dec(x_63);
x_71 = l_lean_parser_combinators_many___rarg___closed__1;
x_72 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_72);
lean::inc(x_71);
if (lean::is_scalar(x_69)) {
 x_75 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_75 = x_69;
}
lean::cnstr_set(x_75, 0, x_71);
lean::cnstr_set(x_75, 1, x_65);
lean::cnstr_set(x_75, 2, x_72);
x_76 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_67, x_75);
x_77 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_77, 0, x_76);
lean::cnstr_set(x_77, 1, x_6);
return x_77;
}
else
{
obj* x_78; obj* x_81; obj* x_82; obj* x_83; obj* x_85; obj* x_86; obj* x_88; obj* x_89; obj* x_90; 
x_78 = lean::cnstr_get(x_63, 0);
lean::inc(x_78);
lean::dec(x_63);
x_81 = lean::box(0);
x_82 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_82, 0, x_78);
lean::cnstr_set(x_82, 1, x_81);
x_83 = l_lean_parser_no__kind;
lean::inc(x_83);
x_85 = l_lean_parser_syntax_mk__node(x_83, x_82);
x_86 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_86);
if (lean::is_scalar(x_69)) {
 x_88 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_88 = x_69;
}
lean::cnstr_set(x_88, 0, x_85);
lean::cnstr_set(x_88, 1, x_65);
lean::cnstr_set(x_88, 2, x_86);
x_89 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_67, x_88);
x_90 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_90, 0, x_89);
lean::cnstr_set(x_90, 1, x_6);
return x_90;
}
}
else
{
obj* x_91; uint8 x_93; obj* x_94; obj* x_95; obj* x_96; obj* x_97; 
x_91 = lean::cnstr_get(x_5, 0);
lean::inc(x_91);
x_93 = lean::cnstr_get_scalar<uint8>(x_5, sizeof(void*)*1);
if (lean::is_shared(x_5)) {
 lean::dec(x_5);
 x_94 = lean::box(0);
} else {
 lean::cnstr_release(x_5, 0);
 x_94 = x_5;
}
if (lean::is_scalar(x_94)) {
 x_95 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_95 = x_94;
}
lean::cnstr_set(x_95, 0, x_91);
lean::cnstr_set_scalar(x_95, sizeof(void*)*1, x_93);
x_96 = x_95;
x_97 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_97, 0, x_96);
lean::cnstr_set(x_97, 1, x_6);
return x_97;
}
}
lbl_11:
{
if (lean::obj_tag(x_9) == 0)
{
lean::dec(x_8);
lean::dec(x_3);
x_5 = x_9;
x_6 = x_10;
goto lbl_7;
}
else
{
obj* x_100; uint8 x_102; 
x_100 = lean::cnstr_get(x_9, 0);
lean::inc(x_100);
x_102 = lean::cnstr_get_scalar<uint8>(x_9, sizeof(void*)*1);
if (x_102 == 0)
{
obj* x_104; obj* x_107; obj* x_109; obj* x_110; obj* x_111; 
lean::dec(x_9);
x_104 = lean::cnstr_get(x_100, 2);
lean::inc(x_104);
lean::dec(x_100);
x_107 = l_mjoin___rarg___closed__1;
lean::inc(x_107);
x_109 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_109, 0, x_104);
lean::closure_set(x_109, 1, x_107);
x_110 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_110, 0, x_109);
x_111 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_111, 0, x_8);
lean::cnstr_set(x_111, 1, x_3);
lean::cnstr_set(x_111, 2, x_110);
x_5 = x_111;
x_6 = x_10;
goto lbl_7;
}
else
{
lean::dec(x_8);
lean::dec(x_3);
lean::dec(x_100);
x_5 = x_9;
x_6 = x_10;
goto lbl_7;
}
}
}
}
}
obj* _init_l_lean_parser_detail__ident_x_27___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_detail__ident__part_parser), 3, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_lift___at_lean_parser_detail__ident_x_27___spec__1___rarg), 5, 1);
lean::closure_set(x_1, 0, x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_detail__ident__suffix_parser), 4, 0);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_optional___at_lean_parser_detail__ident_x_27___spec__2), 5, 1);
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
obj* l_lean_parser_detail__ident_x_27(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_8; 
x_4 = l_lean_parser_detail__ident;
x_5 = l_lean_parser_detail__ident_x_27___closed__1;
lean::inc(x_5);
lean::inc(x_4);
x_8 = l_lean_parser_combinators_node___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__9(x_4, x_5, x_0, x_1, x_2, x_3);
return x_8;
}
}
obj* l___private_init_lean_parser_rec_1__run__aux___at_lean_parser_detail__ident_parser___spec__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_8; 
x_7 = l___private_init_lean_parser_rec_1__run__aux___main___rarg(x_0, x_1, x_2, x_3);
x_8 = lean::apply_3(x_7, x_4, x_5, x_6);
return x_8;
}
}
obj* l_lean_parser_rec__t_run___at_lean_parser_detail__ident_parser___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_8; 
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_rec_1__run__aux___at_lean_parser_detail__ident_parser___spec__3), 7, 3);
lean::closure_set(x_7, 0, x_1);
lean::closure_set(x_7, 1, x_2);
lean::closure_set(x_7, 2, x_3);
x_8 = lean::apply_4(x_0, x_7, x_4, x_5, x_6);
return x_8;
}
}
obj* l_lean_parser_rec__t_run__parsec___at_lean_parser_detail__ident_parser___spec__1___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; obj* x_11; 
lean::dec(x_0);
x_5 = lean::box(0);
x_6 = l_lean_parser_rec__t_run__parsec___rarg___lambda__1___closed__1;
x_7 = l_mjoin___rarg___closed__1;
lean::inc(x_5);
lean::inc(x_7);
lean::inc(x_6);
x_11 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_6, x_7, x_5, x_5, x_1, x_2, x_3);
return x_11;
}
}
obj* _init_l_lean_parser_rec__t_run__parsec___at_lean_parser_detail__ident_parser___spec__1___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_rec__t_run__parsec___at_lean_parser_detail__ident_parser___spec__1___lambda__1), 4, 0);
return x_0;
}
}
obj* l_lean_parser_rec__t_run__parsec___at_lean_parser_detail__ident_parser___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; obj* x_10; obj* x_12; obj* x_13; obj* x_15; obj* x_17; obj* x_18; obj* x_20; obj* x_21; 
x_5 = lean::string_iterator_remaining(x_3);
x_6 = lean::mk_nat_obj(1u);
x_7 = lean::nat_add(x_5, x_6);
lean::dec(x_6);
lean::dec(x_5);
x_10 = l_lean_parser_rec__t_run__parsec___at_lean_parser_detail__ident_parser___spec__1___closed__1;
lean::inc(x_10);
x_12 = l_lean_parser_rec__t_run___at_lean_parser_detail__ident_parser___spec__2(x_0, x_10, x_1, x_7, x_2, x_3, x_4);
x_13 = lean::cnstr_get(x_12, 0);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_12, 1);
lean::inc(x_15);
if (lean::is_shared(x_12)) {
 lean::dec(x_12);
 x_17 = lean::box(0);
} else {
 lean::cnstr_release(x_12, 0);
 lean::cnstr_release(x_12, 1);
 x_17 = x_12;
}
x_18 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_18);
x_20 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_18, x_13);
if (lean::is_scalar(x_17)) {
 x_21 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_21 = x_17;
}
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_15);
return x_21;
}
}
obj* l_lean_parser_detail__ident_parser___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_6; obj* x_7; obj* x_10; 
lean::dec(x_0);
x_6 = l_lean_parser_detail__ident;
x_7 = l_lean_parser_detail__ident_x_27___closed__1;
lean::inc(x_7);
lean::inc(x_6);
x_10 = l_lean_parser_combinators_node___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__9(x_6, x_7, x_1, x_2, x_3, x_4);
return x_10;
}
}
obj* _init_l_lean_parser_detail__ident_parser___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_detail__ident_x_27), 4, 0);
return x_0;
}
}
obj* _init_l_lean_parser_detail__ident_parser___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_detail__ident_parser___lambda__1), 5, 0);
return x_0;
}
}
obj* l_lean_parser_detail__ident_parser(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_7; 
x_3 = l_lean_parser_detail__ident_parser___closed__1;
x_4 = l_lean_parser_detail__ident_parser___closed__2;
lean::inc(x_4);
lean::inc(x_3);
x_7 = l_lean_parser_rec__t_run__parsec___at_lean_parser_detail__ident_parser___spec__1(x_3, x_4, x_0, x_1, x_2);
return x_7;
}
}
obj* l_lean_parser_monad__parsec_curr___at___private_init_lean_parser_token_4__ident_x_27___spec__2___rarg(obj* x_0, obj* x_1) {
_start:
{
uint32 x_2; obj* x_3; obj* x_4; obj* x_6; obj* x_7; 
x_2 = lean::string_iterator_curr(x_0);
x_3 = l_lean_parser_finish__comment__block___closed__2;
x_4 = lean::box_uint32(x_2);
lean::inc(x_3);
x_6 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_6, 0, x_4);
lean::cnstr_set(x_6, 1, x_0);
lean::cnstr_set(x_6, 2, x_3);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_1);
return x_7;
}
}
obj* l_lean_parser_monad__parsec_curr___at___private_init_lean_parser_token_4__ident_x_27___spec__2(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_curr___at___private_init_lean_parser_token_4__ident_x_27___spec__2___rarg), 2, 0);
return x_2;
}
}
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__5(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
uint8 x_6; 
x_6 = lean::string_iterator_has_next(x_2);
if (x_6 == 0)
{
obj* x_8; 
lean::dec(x_0);
x_8 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_8;
}
else
{
uint32 x_9; uint8 x_10; 
x_9 = lean::string_iterator_curr(x_2);
x_10 = l_lean_is__id__rest(x_9);
if (x_10 == 0)
{
obj* x_12; 
lean::dec(x_0);
x_12 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_12;
}
else
{
obj* x_13; obj* x_14; obj* x_17; obj* x_18; 
x_13 = lean::mk_nat_obj(1u);
x_14 = lean::nat_sub(x_0, x_13);
lean::dec(x_13);
lean::dec(x_0);
x_17 = lean::string_push(x_1, x_9);
x_18 = lean::string_iterator_next(x_2);
x_0 = x_14;
x_1 = x_17;
x_2 = x_18;
goto _start;
}
}
}
else
{
obj* x_21; 
lean::dec(x_0);
x_21 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_21;
}
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_init_lean_parser_token_4__ident_x_27___spec__4(uint32 x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
lean::dec(x_1);
x_5 = l_string_join___closed__1;
lean::inc(x_5);
x_7 = lean::string_push(x_5, x_0);
x_8 = lean::string_iterator_remaining(x_2);
x_9 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__5(x_8, x_7, x_2);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_3);
return x_10;
}
}
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__7(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
uint8 x_6; 
x_6 = lean::string_iterator_has_next(x_2);
if (x_6 == 0)
{
obj* x_8; 
lean::dec(x_0);
x_8 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_8;
}
else
{
uint32 x_9; uint8 x_10; 
x_9 = lean::string_iterator_curr(x_2);
x_10 = l_lean_is__id__rest(x_9);
if (x_10 == 0)
{
obj* x_12; 
lean::dec(x_0);
x_12 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_12;
}
else
{
obj* x_13; obj* x_14; obj* x_17; obj* x_18; 
x_13 = lean::mk_nat_obj(1u);
x_14 = lean::nat_sub(x_0, x_13);
lean::dec(x_13);
lean::dec(x_0);
x_17 = lean::string_push(x_1, x_9);
x_18 = lean::string_iterator_next(x_2);
x_0 = x_14;
x_1 = x_17;
x_2 = x_18;
goto _start;
}
}
}
else
{
obj* x_21; 
lean::dec(x_0);
x_21 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_21;
}
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_init_lean_parser_token_4__ident_x_27___spec__6(uint32 x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
lean::dec(x_1);
x_5 = l_string_join___closed__1;
lean::inc(x_5);
x_7 = lean::string_push(x_5, x_0);
x_8 = lean::string_iterator_remaining(x_2);
x_9 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__7(x_8, x_7, x_2);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_3);
return x_10;
}
}
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__9(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
uint8 x_6; 
x_6 = lean::string_iterator_has_next(x_2);
if (x_6 == 0)
{
obj* x_8; 
lean::dec(x_0);
x_8 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_8;
}
else
{
uint32 x_9; uint8 x_10; 
x_9 = lean::string_iterator_curr(x_2);
x_10 = l_lean_is__id__rest(x_9);
if (x_10 == 0)
{
obj* x_12; 
lean::dec(x_0);
x_12 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_12;
}
else
{
obj* x_13; obj* x_14; obj* x_17; obj* x_18; 
x_13 = lean::mk_nat_obj(1u);
x_14 = lean::nat_sub(x_0, x_13);
lean::dec(x_13);
lean::dec(x_0);
x_17 = lean::string_push(x_1, x_9);
x_18 = lean::string_iterator_next(x_2);
x_0 = x_14;
x_1 = x_17;
x_2 = x_18;
goto _start;
}
}
}
else
{
obj* x_21; 
lean::dec(x_0);
x_21 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_21;
}
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_init_lean_parser_token_4__ident_x_27___spec__8(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint32 x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
lean::dec(x_1);
x_5 = lean::string_iterator_curr(x_0);
lean::dec(x_0);
x_7 = l_string_join___closed__1;
lean::inc(x_7);
x_9 = lean::string_push(x_7, x_5);
x_10 = lean::string_iterator_remaining(x_2);
x_11 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__9(x_10, x_9, x_2);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_3);
return x_12;
}
}
obj* l_lean_parser_id__part__default___at___private_init_lean_parser_token_4__ident_x_27___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = lean::string_iterator_has_next(x_1);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; obj* x_11; obj* x_12; obj* x_14; obj* x_16; obj* x_17; obj* x_19; 
x_4 = lean::box(0);
x_5 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_6 = l_mjoin___rarg___closed__1;
lean::inc(x_0);
lean::inc(x_4);
lean::inc(x_6);
lean::inc(x_5);
x_11 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_5, x_6, x_4, x_4, x_0, x_1, x_2);
x_12 = lean::cnstr_get(x_11, 0);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_11, 1);
lean::inc(x_14);
if (lean::is_shared(x_11)) {
 lean::dec(x_11);
 x_16 = lean::box(0);
} else {
 lean::cnstr_release(x_11, 0);
 lean::cnstr_release(x_11, 1);
 x_16 = x_11;
}
x_17 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_17);
x_19 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_17, x_12);
if (lean::obj_tag(x_19) == 0)
{
obj* x_20; obj* x_22; obj* x_24; uint32 x_27; obj* x_29; obj* x_30; obj* x_32; obj* x_35; obj* x_36; 
x_20 = lean::cnstr_get(x_19, 0);
lean::inc(x_20);
x_22 = lean::cnstr_get(x_19, 1);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_19, 2);
lean::inc(x_24);
lean::dec(x_19);
x_27 = lean::unbox_uint32(x_20);
lean::dec(x_20);
x_29 = l_lean_parser_monad__parsec_take__while__cont___at___private_init_lean_parser_token_4__ident_x_27___spec__4(x_27, x_0, x_22, x_14);
x_30 = lean::cnstr_get(x_29, 0);
lean::inc(x_30);
x_32 = lean::cnstr_get(x_29, 1);
lean::inc(x_32);
lean::dec(x_29);
x_35 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_24, x_30);
if (lean::is_scalar(x_16)) {
 x_36 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_36 = x_16;
}
lean::cnstr_set(x_36, 0, x_35);
lean::cnstr_set(x_36, 1, x_32);
return x_36;
}
else
{
obj* x_38; uint8 x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; 
lean::dec(x_0);
x_38 = lean::cnstr_get(x_19, 0);
lean::inc(x_38);
x_40 = lean::cnstr_get_scalar<uint8>(x_19, sizeof(void*)*1);
if (lean::is_shared(x_19)) {
 lean::dec(x_19);
 x_41 = lean::box(0);
} else {
 lean::cnstr_release(x_19, 0);
 x_41 = x_19;
}
if (lean::is_scalar(x_41)) {
 x_42 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_42 = x_41;
}
lean::cnstr_set(x_42, 0, x_38);
lean::cnstr_set_scalar(x_42, sizeof(void*)*1, x_40);
x_43 = x_42;
if (lean::is_scalar(x_16)) {
 x_44 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_44 = x_16;
}
lean::cnstr_set(x_44, 0, x_43);
lean::cnstr_set(x_44, 1, x_14);
return x_44;
}
}
else
{
uint32 x_45; uint8 x_46; 
x_45 = lean::string_iterator_curr(x_1);
x_46 = l_lean_is__id__first(x_45);
if (x_46 == 0)
{
obj* x_47; obj* x_48; obj* x_50; obj* x_52; obj* x_53; obj* x_54; obj* x_58; obj* x_59; obj* x_61; obj* x_63; obj* x_64; obj* x_66; 
x_47 = l_char_quote__core(x_45);
x_48 = l_char_has__repr___closed__1;
lean::inc(x_48);
x_50 = lean::string_append(x_48, x_47);
lean::dec(x_47);
x_52 = lean::string_append(x_50, x_48);
x_53 = lean::box(0);
x_54 = l_mjoin___rarg___closed__1;
lean::inc(x_0);
lean::inc(x_53);
lean::inc(x_54);
x_58 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_52, x_54, x_53, x_53, x_0, x_1, x_2);
x_59 = lean::cnstr_get(x_58, 0);
lean::inc(x_59);
x_61 = lean::cnstr_get(x_58, 1);
lean::inc(x_61);
if (lean::is_shared(x_58)) {
 lean::dec(x_58);
 x_63 = lean::box(0);
} else {
 lean::cnstr_release(x_58, 0);
 lean::cnstr_release(x_58, 1);
 x_63 = x_58;
}
x_64 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_64);
x_66 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_64, x_59);
if (lean::obj_tag(x_66) == 0)
{
obj* x_67; obj* x_69; obj* x_71; uint32 x_74; obj* x_76; obj* x_77; obj* x_79; obj* x_82; obj* x_83; 
x_67 = lean::cnstr_get(x_66, 0);
lean::inc(x_67);
x_69 = lean::cnstr_get(x_66, 1);
lean::inc(x_69);
x_71 = lean::cnstr_get(x_66, 2);
lean::inc(x_71);
lean::dec(x_66);
x_74 = lean::unbox_uint32(x_67);
lean::dec(x_67);
x_76 = l_lean_parser_monad__parsec_take__while__cont___at___private_init_lean_parser_token_4__ident_x_27___spec__6(x_74, x_0, x_69, x_61);
x_77 = lean::cnstr_get(x_76, 0);
lean::inc(x_77);
x_79 = lean::cnstr_get(x_76, 1);
lean::inc(x_79);
lean::dec(x_76);
x_82 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_71, x_77);
if (lean::is_scalar(x_63)) {
 x_83 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_83 = x_63;
}
lean::cnstr_set(x_83, 0, x_82);
lean::cnstr_set(x_83, 1, x_79);
return x_83;
}
else
{
obj* x_85; uint8 x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; 
lean::dec(x_0);
x_85 = lean::cnstr_get(x_66, 0);
lean::inc(x_85);
x_87 = lean::cnstr_get_scalar<uint8>(x_66, sizeof(void*)*1);
if (lean::is_shared(x_66)) {
 lean::dec(x_66);
 x_88 = lean::box(0);
} else {
 lean::cnstr_release(x_66, 0);
 x_88 = x_66;
}
if (lean::is_scalar(x_88)) {
 x_89 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_89 = x_88;
}
lean::cnstr_set(x_89, 0, x_85);
lean::cnstr_set_scalar(x_89, sizeof(void*)*1, x_87);
x_90 = x_89;
if (lean::is_scalar(x_63)) {
 x_91 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_91 = x_63;
}
lean::cnstr_set(x_91, 0, x_90);
lean::cnstr_set(x_91, 1, x_61);
return x_91;
}
}
else
{
obj* x_93; obj* x_94; obj* x_95; obj* x_97; obj* x_99; obj* x_100; obj* x_101; obj* x_102; 
lean::inc(x_1);
x_93 = lean::string_iterator_next(x_1);
x_94 = l_lean_parser_monad__parsec_take__while__cont___at___private_init_lean_parser_token_4__ident_x_27___spec__8(x_1, x_0, x_93, x_2);
x_95 = lean::cnstr_get(x_94, 0);
lean::inc(x_95);
x_97 = lean::cnstr_get(x_94, 1);
lean::inc(x_97);
if (lean::is_shared(x_94)) {
 lean::dec(x_94);
 x_99 = lean::box(0);
} else {
 lean::cnstr_release(x_94, 0);
 lean::cnstr_release(x_94, 1);
 x_99 = x_94;
}
x_100 = lean::box(0);
x_101 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_100, x_95);
if (lean::is_scalar(x_99)) {
 x_102 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_102 = x_99;
}
lean::cnstr_set(x_102, 0, x_101);
lean::cnstr_set(x_102, 1, x_97);
return x_102;
}
}
}
}
obj* l_lean_parser_monad__parsec_ch___at___private_init_lean_parser_token_4__ident_x_27___spec__11(uint32 x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = lean::string_iterator_has_next(x_2);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; obj* x_11; obj* x_12; obj* x_14; obj* x_16; obj* x_17; obj* x_19; obj* x_20; 
x_5 = lean::box(0);
x_6 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_7 = l_mjoin___rarg___closed__1;
lean::inc(x_5);
lean::inc(x_7);
lean::inc(x_6);
x_11 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_6, x_7, x_5, x_5, x_1, x_2, x_3);
x_12 = lean::cnstr_get(x_11, 0);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_11, 1);
lean::inc(x_14);
if (lean::is_shared(x_11)) {
 lean::dec(x_11);
 x_16 = lean::box(0);
} else {
 lean::cnstr_release(x_11, 0);
 lean::cnstr_release(x_11, 1);
 x_16 = x_11;
}
x_17 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_17);
x_19 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_17, x_12);
if (lean::is_scalar(x_16)) {
 x_20 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_20 = x_16;
}
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_14);
return x_20;
}
else
{
uint32 x_21; obj* x_22; obj* x_23; uint8 x_24; 
x_21 = lean::string_iterator_curr(x_2);
x_22 = lean::box_uint32(x_21);
x_23 = lean::box_uint32(x_0);
x_24 = lean::nat_dec_eq(x_22, x_23);
lean::dec(x_23);
if (x_24 == 0)
{
obj* x_27; obj* x_28; obj* x_30; obj* x_32; obj* x_33; obj* x_34; obj* x_37; obj* x_38; obj* x_40; obj* x_42; obj* x_43; obj* x_45; obj* x_46; 
lean::dec(x_22);
x_27 = l_char_quote__core(x_21);
x_28 = l_char_has__repr___closed__1;
lean::inc(x_28);
x_30 = lean::string_append(x_28, x_27);
lean::dec(x_27);
x_32 = lean::string_append(x_30, x_28);
x_33 = lean::box(0);
x_34 = l_mjoin___rarg___closed__1;
lean::inc(x_33);
lean::inc(x_34);
x_37 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_32, x_34, x_33, x_33, x_1, x_2, x_3);
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
x_43 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_43);
x_45 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_43, x_38);
if (lean::is_scalar(x_42)) {
 x_46 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_46 = x_42;
}
lean::cnstr_set(x_46, 0, x_45);
lean::cnstr_set(x_46, 1, x_40);
return x_46;
}
else
{
obj* x_48; obj* x_49; obj* x_50; obj* x_51; 
lean::dec(x_1);
x_48 = lean::string_iterator_next(x_2);
x_49 = lean::box(0);
x_50 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_50, 0, x_22);
lean::cnstr_set(x_50, 1, x_48);
lean::cnstr_set(x_50, 2, x_49);
x_51 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_51, 0, x_50);
lean::cnstr_set(x_51, 1, x_3);
return x_51;
}
}
}
}
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__14(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
uint8 x_6; 
x_6 = lean::string_iterator_has_next(x_2);
if (x_6 == 0)
{
obj* x_8; 
lean::dec(x_0);
x_8 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_8;
}
else
{
uint32 x_9; uint8 x_10; 
x_9 = lean::string_iterator_curr(x_2);
x_10 = l_lean_is__id__end__escape(x_9);
if (x_10 == 0)
{
obj* x_11; obj* x_12; obj* x_15; obj* x_16; 
x_11 = lean::mk_nat_obj(1u);
x_12 = lean::nat_sub(x_0, x_11);
lean::dec(x_11);
lean::dec(x_0);
x_15 = lean::string_push(x_1, x_9);
x_16 = lean::string_iterator_next(x_2);
x_0 = x_12;
x_1 = x_15;
x_2 = x_16;
goto _start;
}
else
{
obj* x_19; 
lean::dec(x_0);
x_19 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_19;
}
}
}
else
{
obj* x_21; 
lean::dec(x_0);
x_21 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_21;
}
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_init_lean_parser_token_4__ident_x_27___spec__13(uint32 x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
lean::dec(x_1);
x_5 = l_string_join___closed__1;
lean::inc(x_5);
x_7 = lean::string_push(x_5, x_0);
x_8 = lean::string_iterator_remaining(x_2);
x_9 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__14(x_8, x_7, x_2);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_3);
return x_10;
}
}
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__16(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
uint8 x_6; 
x_6 = lean::string_iterator_has_next(x_2);
if (x_6 == 0)
{
obj* x_8; 
lean::dec(x_0);
x_8 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_8;
}
else
{
uint32 x_9; uint8 x_10; 
x_9 = lean::string_iterator_curr(x_2);
x_10 = l_lean_is__id__end__escape(x_9);
if (x_10 == 0)
{
obj* x_11; obj* x_12; obj* x_15; obj* x_16; 
x_11 = lean::mk_nat_obj(1u);
x_12 = lean::nat_sub(x_0, x_11);
lean::dec(x_11);
lean::dec(x_0);
x_15 = lean::string_push(x_1, x_9);
x_16 = lean::string_iterator_next(x_2);
x_0 = x_12;
x_1 = x_15;
x_2 = x_16;
goto _start;
}
else
{
obj* x_19; 
lean::dec(x_0);
x_19 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_19;
}
}
}
else
{
obj* x_21; 
lean::dec(x_0);
x_21 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_21;
}
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_init_lean_parser_token_4__ident_x_27___spec__15(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint32 x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
lean::dec(x_1);
x_5 = lean::string_iterator_curr(x_0);
lean::dec(x_0);
x_7 = l_string_join___closed__1;
lean::inc(x_7);
x_9 = lean::string_push(x_7, x_5);
x_10 = lean::string_iterator_remaining(x_2);
x_11 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__16(x_10, x_9, x_2);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_3);
return x_12;
}
}
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__18(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
uint8 x_6; 
x_6 = lean::string_iterator_has_next(x_2);
if (x_6 == 0)
{
obj* x_8; 
lean::dec(x_0);
x_8 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_8;
}
else
{
uint32 x_9; uint8 x_10; 
x_9 = lean::string_iterator_curr(x_2);
x_10 = l_lean_is__id__end__escape(x_9);
if (x_10 == 0)
{
obj* x_11; obj* x_12; obj* x_15; obj* x_16; 
x_11 = lean::mk_nat_obj(1u);
x_12 = lean::nat_sub(x_0, x_11);
lean::dec(x_11);
lean::dec(x_0);
x_15 = lean::string_push(x_1, x_9);
x_16 = lean::string_iterator_next(x_2);
x_0 = x_12;
x_1 = x_15;
x_2 = x_16;
goto _start;
}
else
{
obj* x_19; 
lean::dec(x_0);
x_19 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_19;
}
}
}
else
{
obj* x_21; 
lean::dec(x_0);
x_21 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_21;
}
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_init_lean_parser_token_4__ident_x_27___spec__17(uint32 x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
lean::dec(x_1);
x_5 = l_string_join___closed__1;
lean::inc(x_5);
x_7 = lean::string_push(x_5, x_0);
x_8 = lean::string_iterator_remaining(x_2);
x_9 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__18(x_8, x_7, x_2);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_3);
return x_10;
}
}
obj* l_lean_parser_monad__parsec_take__while1___at___private_init_lean_parser_token_4__ident_x_27___spec__12(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = lean::string_iterator_has_next(x_1);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; obj* x_11; obj* x_12; obj* x_14; obj* x_16; obj* x_17; obj* x_19; 
x_4 = lean::box(0);
x_5 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_6 = l_mjoin___rarg___closed__1;
lean::inc(x_0);
lean::inc(x_4);
lean::inc(x_6);
lean::inc(x_5);
x_11 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_5, x_6, x_4, x_4, x_0, x_1, x_2);
x_12 = lean::cnstr_get(x_11, 0);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_11, 1);
lean::inc(x_14);
if (lean::is_shared(x_11)) {
 lean::dec(x_11);
 x_16 = lean::box(0);
} else {
 lean::cnstr_release(x_11, 0);
 lean::cnstr_release(x_11, 1);
 x_16 = x_11;
}
x_17 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_17);
x_19 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_17, x_12);
if (lean::obj_tag(x_19) == 0)
{
obj* x_20; obj* x_22; obj* x_24; uint32 x_27; obj* x_29; obj* x_30; obj* x_32; obj* x_35; obj* x_36; 
x_20 = lean::cnstr_get(x_19, 0);
lean::inc(x_20);
x_22 = lean::cnstr_get(x_19, 1);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_19, 2);
lean::inc(x_24);
lean::dec(x_19);
x_27 = lean::unbox_uint32(x_20);
lean::dec(x_20);
x_29 = l_lean_parser_monad__parsec_take__while__cont___at___private_init_lean_parser_token_4__ident_x_27___spec__13(x_27, x_0, x_22, x_14);
x_30 = lean::cnstr_get(x_29, 0);
lean::inc(x_30);
x_32 = lean::cnstr_get(x_29, 1);
lean::inc(x_32);
lean::dec(x_29);
x_35 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_24, x_30);
if (lean::is_scalar(x_16)) {
 x_36 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_36 = x_16;
}
lean::cnstr_set(x_36, 0, x_35);
lean::cnstr_set(x_36, 1, x_32);
return x_36;
}
else
{
obj* x_38; uint8 x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; 
lean::dec(x_0);
x_38 = lean::cnstr_get(x_19, 0);
lean::inc(x_38);
x_40 = lean::cnstr_get_scalar<uint8>(x_19, sizeof(void*)*1);
if (lean::is_shared(x_19)) {
 lean::dec(x_19);
 x_41 = lean::box(0);
} else {
 lean::cnstr_release(x_19, 0);
 x_41 = x_19;
}
if (lean::is_scalar(x_41)) {
 x_42 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_42 = x_41;
}
lean::cnstr_set(x_42, 0, x_38);
lean::cnstr_set_scalar(x_42, sizeof(void*)*1, x_40);
x_43 = x_42;
if (lean::is_scalar(x_16)) {
 x_44 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_44 = x_16;
}
lean::cnstr_set(x_44, 0, x_43);
lean::cnstr_set(x_44, 1, x_14);
return x_44;
}
}
else
{
uint32 x_45; uint8 x_46; 
x_45 = lean::string_iterator_curr(x_1);
x_46 = l_lean_is__id__end__escape(x_45);
if (x_46 == 0)
{
obj* x_48; obj* x_49; obj* x_50; obj* x_52; obj* x_54; obj* x_55; obj* x_56; obj* x_57; 
lean::inc(x_1);
x_48 = lean::string_iterator_next(x_1);
x_49 = l_lean_parser_monad__parsec_take__while__cont___at___private_init_lean_parser_token_4__ident_x_27___spec__15(x_1, x_0, x_48, x_2);
x_50 = lean::cnstr_get(x_49, 0);
lean::inc(x_50);
x_52 = lean::cnstr_get(x_49, 1);
lean::inc(x_52);
if (lean::is_shared(x_49)) {
 lean::dec(x_49);
 x_54 = lean::box(0);
} else {
 lean::cnstr_release(x_49, 0);
 lean::cnstr_release(x_49, 1);
 x_54 = x_49;
}
x_55 = lean::box(0);
x_56 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_55, x_50);
if (lean::is_scalar(x_54)) {
 x_57 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_57 = x_54;
}
lean::cnstr_set(x_57, 0, x_56);
lean::cnstr_set(x_57, 1, x_52);
return x_57;
}
else
{
obj* x_58; obj* x_59; obj* x_61; obj* x_63; obj* x_64; obj* x_65; obj* x_69; obj* x_70; obj* x_72; obj* x_74; obj* x_75; obj* x_77; 
x_58 = l_char_quote__core(x_45);
x_59 = l_char_has__repr___closed__1;
lean::inc(x_59);
x_61 = lean::string_append(x_59, x_58);
lean::dec(x_58);
x_63 = lean::string_append(x_61, x_59);
x_64 = lean::box(0);
x_65 = l_mjoin___rarg___closed__1;
lean::inc(x_0);
lean::inc(x_64);
lean::inc(x_65);
x_69 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_63, x_65, x_64, x_64, x_0, x_1, x_2);
x_70 = lean::cnstr_get(x_69, 0);
lean::inc(x_70);
x_72 = lean::cnstr_get(x_69, 1);
lean::inc(x_72);
if (lean::is_shared(x_69)) {
 lean::dec(x_69);
 x_74 = lean::box(0);
} else {
 lean::cnstr_release(x_69, 0);
 lean::cnstr_release(x_69, 1);
 x_74 = x_69;
}
x_75 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_75);
x_77 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_75, x_70);
if (lean::obj_tag(x_77) == 0)
{
obj* x_78; obj* x_80; obj* x_82; uint32 x_85; obj* x_87; obj* x_88; obj* x_90; obj* x_93; obj* x_94; 
x_78 = lean::cnstr_get(x_77, 0);
lean::inc(x_78);
x_80 = lean::cnstr_get(x_77, 1);
lean::inc(x_80);
x_82 = lean::cnstr_get(x_77, 2);
lean::inc(x_82);
lean::dec(x_77);
x_85 = lean::unbox_uint32(x_78);
lean::dec(x_78);
x_87 = l_lean_parser_monad__parsec_take__while__cont___at___private_init_lean_parser_token_4__ident_x_27___spec__17(x_85, x_0, x_80, x_72);
x_88 = lean::cnstr_get(x_87, 0);
lean::inc(x_88);
x_90 = lean::cnstr_get(x_87, 1);
lean::inc(x_90);
lean::dec(x_87);
x_93 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_82, x_88);
if (lean::is_scalar(x_74)) {
 x_94 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_94 = x_74;
}
lean::cnstr_set(x_94, 0, x_93);
lean::cnstr_set(x_94, 1, x_90);
return x_94;
}
else
{
obj* x_96; uint8 x_98; obj* x_99; obj* x_100; obj* x_101; obj* x_102; 
lean::dec(x_0);
x_96 = lean::cnstr_get(x_77, 0);
lean::inc(x_96);
x_98 = lean::cnstr_get_scalar<uint8>(x_77, sizeof(void*)*1);
if (lean::is_shared(x_77)) {
 lean::dec(x_77);
 x_99 = lean::box(0);
} else {
 lean::cnstr_release(x_77, 0);
 x_99 = x_77;
}
if (lean::is_scalar(x_99)) {
 x_100 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_100 = x_99;
}
lean::cnstr_set(x_100, 0, x_96);
lean::cnstr_set_scalar(x_100, sizeof(void*)*1, x_98);
x_101 = x_100;
if (lean::is_scalar(x_74)) {
 x_102 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_102 = x_74;
}
lean::cnstr_set(x_102, 0, x_101);
lean::cnstr_set(x_102, 1, x_72);
return x_102;
}
}
}
}
}
obj* l_lean_parser_id__part__escaped___at___private_init_lean_parser_token_4__ident_x_27___spec__10(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint32 x_4; obj* x_6; obj* x_7; obj* x_9; obj* x_11; 
x_3 = l_lean_id__begin__escape;
x_4 = lean::unbox_uint32(x_3);
lean::inc(x_0);
x_6 = l_lean_parser_monad__parsec_ch___at___private_init_lean_parser_token_4__ident_x_27___spec__11(x_4, x_0, x_1, x_2);
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_6, 1);
lean::inc(x_9);
if (lean::is_shared(x_6)) {
 lean::dec(x_6);
 x_11 = lean::box(0);
} else {
 lean::cnstr_release(x_6, 0);
 lean::cnstr_release(x_6, 1);
 x_11 = x_6;
}
if (lean::obj_tag(x_7) == 0)
{
obj* x_12; obj* x_14; obj* x_16; obj* x_18; obj* x_19; obj* x_21; obj* x_24; 
x_12 = lean::cnstr_get(x_7, 1);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_7, 2);
lean::inc(x_14);
if (lean::is_shared(x_7)) {
 lean::dec(x_7);
 x_16 = lean::box(0);
} else {
 lean::cnstr_release(x_7, 0);
 lean::cnstr_release(x_7, 1);
 lean::cnstr_release(x_7, 2);
 x_16 = x_7;
}
lean::inc(x_0);
x_18 = l_lean_parser_monad__parsec_take__while1___at___private_init_lean_parser_token_4__ident_x_27___spec__12(x_0, x_12, x_9);
x_19 = lean::cnstr_get(x_18, 0);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_18, 1);
lean::inc(x_21);
lean::dec(x_18);
x_24 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_14, x_19);
if (lean::obj_tag(x_24) == 0)
{
obj* x_25; obj* x_27; obj* x_29; obj* x_32; uint32 x_33; obj* x_34; obj* x_35; obj* x_37; 
x_25 = lean::cnstr_get(x_24, 0);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_24, 1);
lean::inc(x_27);
x_29 = lean::cnstr_get(x_24, 2);
lean::inc(x_29);
lean::dec(x_24);
x_32 = l_lean_id__end__escape;
x_33 = lean::unbox_uint32(x_32);
x_34 = l_lean_parser_monad__parsec_ch___at___private_init_lean_parser_token_4__ident_x_27___spec__11(x_33, x_0, x_27, x_21);
x_35 = lean::cnstr_get(x_34, 0);
lean::inc(x_35);
x_37 = lean::cnstr_get(x_34, 1);
lean::inc(x_37);
lean::dec(x_34);
if (lean::obj_tag(x_35) == 0)
{
obj* x_40; obj* x_42; obj* x_45; obj* x_47; obj* x_48; obj* x_49; obj* x_50; 
x_40 = lean::cnstr_get(x_35, 1);
lean::inc(x_40);
x_42 = lean::cnstr_get(x_35, 2);
lean::inc(x_42);
lean::dec(x_35);
x_45 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_45);
if (lean::is_scalar(x_16)) {
 x_47 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_47 = x_16;
}
lean::cnstr_set(x_47, 0, x_25);
lean::cnstr_set(x_47, 1, x_40);
lean::cnstr_set(x_47, 2, x_45);
x_48 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_42, x_47);
x_49 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_29, x_48);
if (lean::is_scalar(x_11)) {
 x_50 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_50 = x_11;
}
lean::cnstr_set(x_50, 0, x_49);
lean::cnstr_set(x_50, 1, x_37);
return x_50;
}
else
{
obj* x_53; uint8 x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; 
lean::dec(x_16);
lean::dec(x_25);
x_53 = lean::cnstr_get(x_35, 0);
lean::inc(x_53);
x_55 = lean::cnstr_get_scalar<uint8>(x_35, sizeof(void*)*1);
if (lean::is_shared(x_35)) {
 lean::dec(x_35);
 x_56 = lean::box(0);
} else {
 lean::cnstr_release(x_35, 0);
 x_56 = x_35;
}
if (lean::is_scalar(x_56)) {
 x_57 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_57 = x_56;
}
lean::cnstr_set(x_57, 0, x_53);
lean::cnstr_set_scalar(x_57, sizeof(void*)*1, x_55);
x_58 = x_57;
x_59 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_29, x_58);
if (lean::is_scalar(x_11)) {
 x_60 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_60 = x_11;
}
lean::cnstr_set(x_60, 0, x_59);
lean::cnstr_set(x_60, 1, x_37);
return x_60;
}
}
else
{
obj* x_63; uint8 x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; 
lean::dec(x_16);
lean::dec(x_0);
x_63 = lean::cnstr_get(x_24, 0);
lean::inc(x_63);
x_65 = lean::cnstr_get_scalar<uint8>(x_24, sizeof(void*)*1);
if (lean::is_shared(x_24)) {
 lean::dec(x_24);
 x_66 = lean::box(0);
} else {
 lean::cnstr_release(x_24, 0);
 x_66 = x_24;
}
if (lean::is_scalar(x_66)) {
 x_67 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_67 = x_66;
}
lean::cnstr_set(x_67, 0, x_63);
lean::cnstr_set_scalar(x_67, sizeof(void*)*1, x_65);
x_68 = x_67;
if (lean::is_scalar(x_11)) {
 x_69 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_69 = x_11;
}
lean::cnstr_set(x_69, 0, x_68);
lean::cnstr_set(x_69, 1, x_21);
return x_69;
}
}
else
{
obj* x_71; uint8 x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; 
lean::dec(x_0);
x_71 = lean::cnstr_get(x_7, 0);
lean::inc(x_71);
x_73 = lean::cnstr_get_scalar<uint8>(x_7, sizeof(void*)*1);
if (lean::is_shared(x_7)) {
 lean::dec(x_7);
 x_74 = lean::box(0);
} else {
 lean::cnstr_release(x_7, 0);
 x_74 = x_7;
}
if (lean::is_scalar(x_74)) {
 x_75 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_75 = x_74;
}
lean::cnstr_set(x_75, 0, x_71);
lean::cnstr_set_scalar(x_75, sizeof(void*)*1, x_73);
x_76 = x_75;
if (lean::is_scalar(x_11)) {
 x_77 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_77 = x_11;
}
lean::cnstr_set(x_77, 0, x_76);
lean::cnstr_set(x_77, 1, x_9);
return x_77;
}
}
}
obj* l_lean_parser_id__part___at___private_init_lean_parser_token_4__ident_x_27___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_6; obj* x_8; 
x_3 = l_lean_parser_monad__parsec_curr___at___private_init_lean_parser_token_4__ident_x_27___spec__2___rarg(x_1, x_2);
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
obj* x_9; obj* x_11; obj* x_13; obj* x_15; uint32 x_16; uint8 x_18; obj* x_19; obj* x_20; obj* x_22; obj* x_23; 
x_9 = lean::cnstr_get(x_4, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_4, 1);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_4, 2);
lean::inc(x_13);
if (lean::is_shared(x_4)) {
 lean::dec(x_4);
 x_15 = lean::box(0);
} else {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_release(x_4, 1);
 lean::cnstr_release(x_4, 2);
 x_15 = x_4;
}
x_16 = lean::unbox_uint32(x_9);
lean::dec(x_9);
x_18 = l_lean_is__id__begin__escape(x_16);
x_19 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_20 = lean::box(x_18);
lean::inc(x_19);
if (lean::is_scalar(x_15)) {
 x_22 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_22 = x_15;
}
lean::cnstr_set(x_22, 0, x_20);
lean::cnstr_set(x_22, 1, x_11);
lean::cnstr_set(x_22, 2, x_19);
x_23 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_13, x_22);
if (lean::obj_tag(x_23) == 0)
{
obj* x_24; obj* x_26; obj* x_28; uint8 x_31; 
x_24 = lean::cnstr_get(x_23, 0);
lean::inc(x_24);
x_26 = lean::cnstr_get(x_23, 1);
lean::inc(x_26);
x_28 = lean::cnstr_get(x_23, 2);
lean::inc(x_28);
lean::dec(x_23);
x_31 = lean::unbox(x_24);
lean::dec(x_24);
if (x_31 == 0)
{
obj* x_33; obj* x_34; obj* x_36; obj* x_39; obj* x_40; 
x_33 = l_lean_parser_id__part__default___at___private_init_lean_parser_token_4__ident_x_27___spec__3(x_0, x_26, x_6);
x_34 = lean::cnstr_get(x_33, 0);
lean::inc(x_34);
x_36 = lean::cnstr_get(x_33, 1);
lean::inc(x_36);
lean::dec(x_33);
x_39 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_28, x_34);
if (lean::is_scalar(x_8)) {
 x_40 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_40 = x_8;
}
lean::cnstr_set(x_40, 0, x_39);
lean::cnstr_set(x_40, 1, x_36);
return x_40;
}
else
{
obj* x_41; obj* x_42; obj* x_44; obj* x_47; obj* x_48; 
x_41 = l_lean_parser_id__part__escaped___at___private_init_lean_parser_token_4__ident_x_27___spec__10(x_0, x_26, x_6);
x_42 = lean::cnstr_get(x_41, 0);
lean::inc(x_42);
x_44 = lean::cnstr_get(x_41, 1);
lean::inc(x_44);
lean::dec(x_41);
x_47 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_28, x_42);
if (lean::is_scalar(x_8)) {
 x_48 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_48 = x_8;
}
lean::cnstr_set(x_48, 0, x_47);
lean::cnstr_set(x_48, 1, x_44);
return x_48;
}
}
else
{
obj* x_50; uint8 x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; 
lean::dec(x_0);
x_50 = lean::cnstr_get(x_23, 0);
lean::inc(x_50);
x_52 = lean::cnstr_get_scalar<uint8>(x_23, sizeof(void*)*1);
if (lean::is_shared(x_23)) {
 lean::dec(x_23);
 x_53 = lean::box(0);
} else {
 lean::cnstr_release(x_23, 0);
 x_53 = x_23;
}
if (lean::is_scalar(x_53)) {
 x_54 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_54 = x_53;
}
lean::cnstr_set(x_54, 0, x_50);
lean::cnstr_set_scalar(x_54, sizeof(void*)*1, x_52);
x_55 = x_54;
if (lean::is_scalar(x_8)) {
 x_56 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_56 = x_8;
}
lean::cnstr_set(x_56, 0, x_55);
lean::cnstr_set(x_56, 1, x_6);
return x_56;
}
}
else
{
obj* x_58; uint8 x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; 
lean::dec(x_0);
x_58 = lean::cnstr_get(x_4, 0);
lean::inc(x_58);
x_60 = lean::cnstr_get_scalar<uint8>(x_4, sizeof(void*)*1);
if (lean::is_shared(x_4)) {
 lean::dec(x_4);
 x_61 = lean::box(0);
} else {
 lean::cnstr_release(x_4, 0);
 x_61 = x_4;
}
if (lean::is_scalar(x_61)) {
 x_62 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_62 = x_61;
}
lean::cnstr_set(x_62, 0, x_58);
lean::cnstr_set_scalar(x_62, sizeof(void*)*1, x_60);
x_63 = x_62;
if (lean::is_scalar(x_8)) {
 x_64 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_64 = x_8;
}
lean::cnstr_set(x_64, 0, x_63);
lean::cnstr_set(x_64, 1, x_6);
return x_64;
}
}
}
obj* l_lean_parser_parsec__t_lookahead___at___private_init_lean_parser_token_4__ident_x_27___spec__19(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_6; uint32 x_7; obj* x_11; obj* x_12; obj* x_14; 
x_6 = lean::mk_nat_obj(46u);
x_7 = lean::unbox_uint32(x_6);
lean::dec(x_6);
lean::inc(x_1);
lean::inc(x_0);
x_11 = l_lean_parser_monad__parsec_ch___at___private_init_lean_parser_token_4__ident_x_27___spec__11(x_7, x_0, x_1, x_2);
x_12 = lean::cnstr_get(x_11, 0);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_11, 1);
lean::inc(x_14);
lean::dec(x_11);
if (lean::obj_tag(x_12) == 0)
{
obj* x_17; obj* x_19; obj* x_21; obj* x_22; uint32 x_23; obj* x_26; obj* x_27; obj* x_29; 
x_17 = lean::cnstr_get(x_12, 1);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_12, 2);
lean::inc(x_19);
if (lean::is_shared(x_12)) {
 lean::dec(x_12);
 x_21 = lean::box(0);
} else {
 lean::cnstr_release(x_12, 0);
 lean::cnstr_release(x_12, 1);
 lean::cnstr_release(x_12, 2);
 x_21 = x_12;
}
x_22 = l_lean_id__begin__escape;
x_23 = lean::unbox_uint32(x_22);
lean::inc(x_17);
lean::inc(x_0);
x_26 = l_lean_parser_monad__parsec_ch___at___private_init_lean_parser_token_4__ident_x_27___spec__11(x_23, x_0, x_17, x_14);
x_27 = lean::cnstr_get(x_26, 0);
lean::inc(x_27);
x_29 = lean::cnstr_get(x_26, 1);
lean::inc(x_29);
lean::dec(x_26);
if (lean::obj_tag(x_27) == 0)
{
obj* x_35; 
lean::dec(x_17);
lean::dec(x_21);
lean::dec(x_0);
x_35 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_19, x_27);
x_3 = x_35;
x_4 = x_29;
goto lbl_5;
}
else
{
obj* x_36; uint8 x_38; 
x_36 = lean::cnstr_get(x_27, 0);
lean::inc(x_36);
x_38 = lean::cnstr_get_scalar<uint8>(x_27, sizeof(void*)*1);
if (x_38 == 0)
{
uint8 x_40; 
lean::dec(x_27);
x_40 = lean::string_iterator_has_next(x_17);
if (x_40 == 0)
{
obj* x_42; obj* x_43; obj* x_44; obj* x_48; obj* x_49; obj* x_51; obj* x_54; obj* x_56; obj* x_57; obj* x_58; 
lean::dec(x_21);
x_42 = lean::box(0);
x_43 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_44 = l_mjoin___rarg___closed__1;
lean::inc(x_42);
lean::inc(x_44);
lean::inc(x_43);
x_48 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_43, x_44, x_42, x_42, x_0, x_17, x_29);
x_49 = lean::cnstr_get(x_48, 0);
lean::inc(x_49);
x_51 = lean::cnstr_get(x_48, 1);
lean::inc(x_51);
lean::dec(x_48);
x_54 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_54);
x_56 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_54, x_49);
x_57 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_36, x_56);
x_58 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_19, x_57);
x_3 = x_58;
x_4 = x_51;
goto lbl_5;
}
else
{
uint32 x_59; uint8 x_60; 
x_59 = lean::string_iterator_curr(x_17);
x_60 = l_lean_is__id__first(x_59);
if (x_60 == 0)
{
obj* x_62; obj* x_63; obj* x_65; obj* x_67; obj* x_68; obj* x_69; obj* x_72; obj* x_73; obj* x_75; obj* x_78; obj* x_80; obj* x_81; obj* x_82; 
lean::dec(x_21);
x_62 = l_char_quote__core(x_59);
x_63 = l_char_has__repr___closed__1;
lean::inc(x_63);
x_65 = lean::string_append(x_63, x_62);
lean::dec(x_62);
x_67 = lean::string_append(x_65, x_63);
x_68 = lean::box(0);
x_69 = l_mjoin___rarg___closed__1;
lean::inc(x_68);
lean::inc(x_69);
x_72 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_67, x_69, x_68, x_68, x_0, x_17, x_29);
x_73 = lean::cnstr_get(x_72, 0);
lean::inc(x_73);
x_75 = lean::cnstr_get(x_72, 1);
lean::inc(x_75);
lean::dec(x_72);
x_78 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_78);
x_80 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_78, x_73);
x_81 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_36, x_80);
x_82 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_19, x_81);
x_3 = x_82;
x_4 = x_75;
goto lbl_5;
}
else
{
obj* x_85; obj* x_86; obj* x_87; obj* x_88; obj* x_89; 
lean::dec(x_0);
lean::dec(x_36);
x_85 = lean::string_iterator_next(x_17);
x_86 = lean::box(0);
x_87 = lean::box_uint32(x_59);
if (lean::is_scalar(x_21)) {
 x_88 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_88 = x_21;
}
lean::cnstr_set(x_88, 0, x_87);
lean::cnstr_set(x_88, 1, x_85);
lean::cnstr_set(x_88, 2, x_86);
x_89 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_19, x_88);
x_3 = x_89;
x_4 = x_29;
goto lbl_5;
}
}
}
else
{
obj* x_94; 
lean::dec(x_17);
lean::dec(x_21);
lean::dec(x_0);
lean::dec(x_36);
x_94 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_19, x_27);
x_3 = x_94;
x_4 = x_29;
goto lbl_5;
}
}
}
else
{
obj* x_96; uint8 x_98; obj* x_99; obj* x_100; obj* x_101; 
lean::dec(x_0);
x_96 = lean::cnstr_get(x_12, 0);
lean::inc(x_96);
x_98 = lean::cnstr_get_scalar<uint8>(x_12, sizeof(void*)*1);
if (lean::is_shared(x_12)) {
 lean::dec(x_12);
 x_99 = lean::box(0);
} else {
 lean::cnstr_release(x_12, 0);
 x_99 = x_12;
}
if (lean::is_scalar(x_99)) {
 x_100 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_100 = x_99;
}
lean::cnstr_set(x_100, 0, x_96);
lean::cnstr_set_scalar(x_100, sizeof(void*)*1, x_98);
x_101 = x_100;
x_3 = x_101;
x_4 = x_14;
goto lbl_5;
}
lbl_5:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_102; obj* x_104; obj* x_105; obj* x_107; obj* x_108; 
x_102 = lean::cnstr_get(x_3, 0);
lean::inc(x_102);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_104 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 1);
 lean::cnstr_release(x_3, 2);
 x_104 = x_3;
}
x_105 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_105);
if (lean::is_scalar(x_104)) {
 x_107 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_107 = x_104;
}
lean::cnstr_set(x_107, 0, x_102);
lean::cnstr_set(x_107, 1, x_1);
lean::cnstr_set(x_107, 2, x_105);
x_108 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_108, 0, x_107);
lean::cnstr_set(x_108, 1, x_4);
return x_108;
}
else
{
obj* x_110; 
lean::dec(x_1);
x_110 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_110, 0, x_3);
lean::cnstr_set(x_110, 1, x_4);
return x_110;
}
}
}
}
obj* l_lean_parser_monad__parsec_foldl__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__21___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_10; 
x_3 = l_lean_parser_parsec__t_lookahead___at___private_init_lean_parser_token_4__ident_x_27___spec__19(x_0, x_1, x_2);
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
x_9 = l_lean_parser_parsec__t_try__mk__res___rarg(x_4);
if (lean::is_scalar(x_8)) {
 x_10 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_10 = x_8;
}
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_6);
return x_10;
}
}
obj* l_lean_parser_monad__parsec_foldl__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__21___lambda__2(uint32 x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint32 x_5; obj* x_8; obj* x_9; obj* x_11; obj* x_13; 
x_4 = lean::mk_nat_obj(46u);
x_5 = lean::unbox_uint32(x_4);
lean::dec(x_4);
lean::inc(x_1);
x_8 = l_lean_parser_monad__parsec_ch___at___private_init_lean_parser_token_4__ident_x_27___spec__11(x_5, x_1, x_2, x_3);
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
if (lean::is_shared(x_8)) {
 lean::dec(x_8);
 x_13 = lean::box(0);
} else {
 lean::cnstr_release(x_8, 0);
 lean::cnstr_release(x_8, 1);
 x_13 = x_8;
}
if (lean::obj_tag(x_9) == 0)
{
obj* x_14; obj* x_16; obj* x_19; obj* x_20; obj* x_22; obj* x_25; obj* x_26; 
x_14 = lean::cnstr_get(x_9, 1);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_9, 2);
lean::inc(x_16);
lean::dec(x_9);
x_19 = l_lean_parser_id__part___at___private_init_lean_parser_token_4__ident_x_27___spec__1(x_1, x_14, x_11);
x_20 = lean::cnstr_get(x_19, 0);
lean::inc(x_20);
x_22 = lean::cnstr_get(x_19, 1);
lean::inc(x_22);
lean::dec(x_19);
x_25 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_20);
if (lean::is_scalar(x_13)) {
 x_26 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_26 = x_13;
}
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_22);
return x_26;
}
else
{
obj* x_28; uint8 x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; 
lean::dec(x_1);
x_28 = lean::cnstr_get(x_9, 0);
lean::inc(x_28);
x_30 = lean::cnstr_get_scalar<uint8>(x_9, sizeof(void*)*1);
if (lean::is_shared(x_9)) {
 lean::dec(x_9);
 x_31 = lean::box(0);
} else {
 lean::cnstr_release(x_9, 0);
 x_31 = x_9;
}
if (lean::is_scalar(x_31)) {
 x_32 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_32 = x_31;
}
lean::cnstr_set(x_32, 0, x_28);
lean::cnstr_set_scalar(x_32, sizeof(void*)*1, x_30);
x_33 = x_32;
if (lean::is_scalar(x_13)) {
 x_34 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_34 = x_13;
}
lean::cnstr_set(x_34, 0, x_33);
lean::cnstr_set(x_34, 1, x_11);
return x_34;
}
}
}
obj* _init_l_lean_parser_monad__parsec_foldl__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__21___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_foldl__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__21___lambda__1), 3, 0);
return x_0;
}
}
obj* _init_l_lean_parser_monad__parsec_foldl__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__21___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_foldl__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__21___lambda__2___boxed), 4, 0);
return x_0;
}
}
obj* l_lean_parser_monad__parsec_foldl__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__21(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::mk_nat_obj(0u);
x_6 = lean::nat_dec_eq(x_1, x_5);
lean::dec(x_5);
if (x_6 == 0)
{
obj* x_8; obj* x_9; obj* x_14; obj* x_15; obj* x_17; obj* x_19; 
x_8 = l_lean_parser_monad__parsec_foldl__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__21___closed__1;
x_9 = l_lean_parser_monad__parsec_foldl__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__21___closed__2;
lean::inc(x_3);
lean::inc(x_2);
lean::inc(x_9);
lean::inc(x_8);
x_14 = l_reader__t_bind___at_lean_parser_with__trailing___spec__2___rarg(x_8, x_9, x_2, x_3, x_4);
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
obj* x_20; obj* x_22; obj* x_24; obj* x_26; obj* x_27; obj* x_28; obj* x_32; obj* x_33; obj* x_34; obj* x_36; obj* x_39; 
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
x_27 = lean::mk_nat_obj(1u);
x_28 = lean::nat_sub(x_1, x_27);
lean::dec(x_27);
lean::dec(x_1);
lean::inc(x_0);
x_32 = lean_name_mk_string(x_0, x_20);
x_33 = l_lean_parser_monad__parsec_foldl__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__21(x_32, x_28, x_2, x_22, x_17);
x_34 = lean::cnstr_get(x_33, 0);
lean::inc(x_34);
x_36 = lean::cnstr_get(x_33, 1);
lean::inc(x_36);
lean::dec(x_33);
x_39 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_24, x_34);
if (lean::obj_tag(x_39) == 0)
{
obj* x_43; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_26);
if (lean::is_scalar(x_19)) {
 x_43 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_43 = x_19;
}
lean::cnstr_set(x_43, 0, x_39);
lean::cnstr_set(x_43, 1, x_36);
return x_43;
}
else
{
obj* x_44; uint8 x_46; 
x_44 = lean::cnstr_get(x_39, 0);
lean::inc(x_44);
x_46 = lean::cnstr_get_scalar<uint8>(x_39, sizeof(void*)*1);
if (x_46 == 0)
{
obj* x_48; obj* x_51; obj* x_53; obj* x_54; obj* x_55; obj* x_56; 
lean::dec(x_39);
x_48 = lean::cnstr_get(x_44, 2);
lean::inc(x_48);
lean::dec(x_44);
x_51 = l_mjoin___rarg___closed__1;
lean::inc(x_51);
x_53 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_53, 0, x_48);
lean::closure_set(x_53, 1, x_51);
x_54 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_54, 0, x_53);
if (lean::is_scalar(x_26)) {
 x_55 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_55 = x_26;
}
lean::cnstr_set(x_55, 0, x_0);
lean::cnstr_set(x_55, 1, x_3);
lean::cnstr_set(x_55, 2, x_54);
if (lean::is_scalar(x_19)) {
 x_56 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_56 = x_19;
}
lean::cnstr_set(x_56, 0, x_55);
lean::cnstr_set(x_56, 1, x_36);
return x_56;
}
else
{
obj* x_61; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_44);
lean::dec(x_26);
if (lean::is_scalar(x_19)) {
 x_61 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_61 = x_19;
}
lean::cnstr_set(x_61, 0, x_39);
lean::cnstr_set(x_61, 1, x_36);
return x_61;
}
}
}
else
{
obj* x_64; uint8 x_66; obj* x_67; 
lean::dec(x_1);
lean::dec(x_2);
x_64 = lean::cnstr_get(x_15, 0);
lean::inc(x_64);
x_66 = lean::cnstr_get_scalar<uint8>(x_15, sizeof(void*)*1);
if (lean::is_shared(x_15)) {
 lean::dec(x_15);
 x_67 = lean::box(0);
} else {
 lean::cnstr_release(x_15, 0);
 x_67 = x_15;
}
if (x_66 == 0)
{
obj* x_69; obj* x_72; obj* x_74; obj* x_75; obj* x_76; obj* x_77; 
lean::dec(x_67);
x_69 = lean::cnstr_get(x_64, 2);
lean::inc(x_69);
lean::dec(x_64);
x_72 = l_mjoin___rarg___closed__1;
lean::inc(x_72);
x_74 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_74, 0, x_69);
lean::closure_set(x_74, 1, x_72);
x_75 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_75, 0, x_74);
x_76 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_76, 0, x_0);
lean::cnstr_set(x_76, 1, x_3);
lean::cnstr_set(x_76, 2, x_75);
if (lean::is_scalar(x_19)) {
 x_77 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_77 = x_19;
}
lean::cnstr_set(x_77, 0, x_76);
lean::cnstr_set(x_77, 1, x_17);
return x_77;
}
else
{
obj* x_80; obj* x_81; obj* x_82; 
lean::dec(x_3);
lean::dec(x_0);
if (lean::is_scalar(x_67)) {
 x_80 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_80 = x_67;
}
lean::cnstr_set(x_80, 0, x_64);
lean::cnstr_set_scalar(x_80, sizeof(void*)*1, x_66);
x_81 = x_80;
if (lean::is_scalar(x_19)) {
 x_82 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_82 = x_19;
}
lean::cnstr_set(x_82, 0, x_81);
lean::cnstr_set(x_82, 1, x_17);
return x_82;
}
}
}
else
{
obj* x_85; obj* x_87; obj* x_88; 
lean::dec(x_1);
lean::dec(x_2);
x_85 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_85);
x_87 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_87, 0, x_0);
lean::cnstr_set(x_87, 1, x_3);
lean::cnstr_set(x_87, 2, x_85);
x_88 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_88, 0, x_87);
lean::cnstr_set(x_88, 1, x_4);
return x_88;
}
}
}
obj* l_lean_parser_monad__parsec_foldl___at___private_init_lean_parser_token_4__ident_x_27___spec__20(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_10; obj* x_12; obj* x_13; obj* x_15; obj* x_16; 
x_4 = lean::box(0);
x_5 = lean_name_mk_string(x_4, x_0);
x_6 = lean::string_iterator_remaining(x_2);
x_7 = l_lean_parser_monad__parsec_foldl__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__21(x_5, x_6, x_1, x_2, x_3);
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
x_13 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_13);
x_15 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_13, x_8);
if (lean::is_scalar(x_12)) {
 x_16 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_16 = x_12;
}
lean::cnstr_set(x_16, 0, x_15);
lean::cnstr_set(x_16, 1, x_10);
return x_16;
}
}
obj* l___private_init_lean_parser_token_4__ident_x_27(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_5; obj* x_6; obj* x_8; obj* x_10; 
lean::inc(x_1);
lean::inc(x_0);
x_5 = l_lean_parser_id__part___at___private_init_lean_parser_token_4__ident_x_27___spec__1(x_0, x_1, x_2);
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
obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_18; obj* x_19; obj* x_21; 
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
x_18 = l_lean_parser_monad__parsec_foldl___at___private_init_lean_parser_token_4__ident_x_27___spec__20(x_11, x_0, x_13, x_8);
x_19 = lean::cnstr_get(x_18, 0);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_18, 1);
lean::inc(x_21);
lean::dec(x_18);
if (lean::obj_tag(x_19) == 0)
{
obj* x_24; obj* x_26; obj* x_28; obj* x_33; obj* x_34; obj* x_37; obj* x_38; obj* x_39; obj* x_41; obj* x_42; obj* x_44; obj* x_45; obj* x_46; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_53; obj* x_54; 
x_24 = lean::cnstr_get(x_19, 0);
lean::inc(x_24);
x_26 = lean::cnstr_get(x_19, 1);
lean::inc(x_26);
x_28 = lean::cnstr_get(x_19, 2);
lean::inc(x_28);
lean::dec(x_19);
lean::inc(x_1);
lean::inc(x_1);
x_33 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_33, 0, x_1);
lean::cnstr_set(x_33, 1, x_1);
x_34 = lean::string_iterator_offset(x_1);
lean::inc(x_26);
lean::inc(x_26);
x_37 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_37, 0, x_26);
lean::cnstr_set(x_37, 1, x_26);
x_38 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_38, 0, x_33);
lean::cnstr_set(x_38, 1, x_34);
lean::cnstr_set(x_38, 2, x_37);
x_39 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_39, 0, x_38);
lean::inc(x_26);
x_41 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_41, 0, x_1);
lean::cnstr_set(x_41, 1, x_26);
x_42 = lean::box(0);
lean::inc(x_42);
x_44 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_44, 0, x_39);
lean::cnstr_set(x_44, 1, x_41);
lean::cnstr_set(x_44, 2, x_24);
lean::cnstr_set(x_44, 3, x_42);
lean::cnstr_set(x_44, 4, x_42);
x_45 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_45, 0, x_44);
x_46 = l_lean_parser_finish__comment__block___closed__2;
lean::inc(x_46);
if (lean::is_scalar(x_17)) {
 x_48 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_48 = x_17;
}
lean::cnstr_set(x_48, 0, x_45);
lean::cnstr_set(x_48, 1, x_26);
lean::cnstr_set(x_48, 2, x_46);
x_49 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_28, x_48);
x_50 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_49);
x_51 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_51);
x_53 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_51, x_50);
if (lean::is_scalar(x_10)) {
 x_54 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_54 = x_10;
}
lean::cnstr_set(x_54, 0, x_53);
lean::cnstr_set(x_54, 1, x_21);
return x_54;
}
else
{
obj* x_57; uint8 x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_66; obj* x_67; 
lean::dec(x_17);
lean::dec(x_1);
x_57 = lean::cnstr_get(x_19, 0);
lean::inc(x_57);
x_59 = lean::cnstr_get_scalar<uint8>(x_19, sizeof(void*)*1);
if (lean::is_shared(x_19)) {
 lean::dec(x_19);
 x_60 = lean::box(0);
} else {
 lean::cnstr_release(x_19, 0);
 x_60 = x_19;
}
if (lean::is_scalar(x_60)) {
 x_61 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_61 = x_60;
}
lean::cnstr_set(x_61, 0, x_57);
lean::cnstr_set_scalar(x_61, sizeof(void*)*1, x_59);
x_62 = x_61;
x_63 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_62);
x_64 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_64);
x_66 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_64, x_63);
if (lean::is_scalar(x_10)) {
 x_67 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_67 = x_10;
}
lean::cnstr_set(x_67, 0, x_66);
lean::cnstr_set(x_67, 1, x_21);
return x_67;
}
}
else
{
obj* x_70; uint8 x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_78; obj* x_79; 
lean::dec(x_1);
lean::dec(x_0);
x_70 = lean::cnstr_get(x_6, 0);
lean::inc(x_70);
x_72 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*1);
if (lean::is_shared(x_6)) {
 lean::dec(x_6);
 x_73 = lean::box(0);
} else {
 lean::cnstr_release(x_6, 0);
 x_73 = x_6;
}
if (lean::is_scalar(x_73)) {
 x_74 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_74 = x_73;
}
lean::cnstr_set(x_74, 0, x_70);
lean::cnstr_set_scalar(x_74, sizeof(void*)*1, x_72);
x_75 = x_74;
x_76 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_76);
x_78 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_76, x_75);
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
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_init_lean_parser_token_4__ident_x_27___spec__4___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint32 x_4; obj* x_5; 
x_4 = lean::unbox_uint32(x_0);
x_5 = l_lean_parser_monad__parsec_take__while__cont___at___private_init_lean_parser_token_4__ident_x_27___spec__4(x_4, x_1, x_2, x_3);
return x_5;
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_init_lean_parser_token_4__ident_x_27___spec__6___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint32 x_4; obj* x_5; 
x_4 = lean::unbox_uint32(x_0);
x_5 = l_lean_parser_monad__parsec_take__while__cont___at___private_init_lean_parser_token_4__ident_x_27___spec__6(x_4, x_1, x_2, x_3);
return x_5;
}
}
obj* l_lean_parser_monad__parsec_ch___at___private_init_lean_parser_token_4__ident_x_27___spec__11___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint32 x_4; obj* x_5; 
x_4 = lean::unbox_uint32(x_0);
x_5 = l_lean_parser_monad__parsec_ch___at___private_init_lean_parser_token_4__ident_x_27___spec__11(x_4, x_1, x_2, x_3);
return x_5;
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_init_lean_parser_token_4__ident_x_27___spec__13___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint32 x_4; obj* x_5; 
x_4 = lean::unbox_uint32(x_0);
x_5 = l_lean_parser_monad__parsec_take__while__cont___at___private_init_lean_parser_token_4__ident_x_27___spec__13(x_4, x_1, x_2, x_3);
return x_5;
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_init_lean_parser_token_4__ident_x_27___spec__17___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint32 x_4; obj* x_5; 
x_4 = lean::unbox_uint32(x_0);
x_5 = l_lean_parser_monad__parsec_take__while__cont___at___private_init_lean_parser_token_4__ident_x_27___spec__17(x_4, x_1, x_2, x_3);
return x_5;
}
}
obj* l_lean_parser_monad__parsec_foldl__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__21___lambda__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint32 x_4; obj* x_5; 
x_4 = lean::unbox_uint32(x_0);
x_5 = l_lean_parser_monad__parsec_foldl__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__21___lambda__2(x_4, x_1, x_2, x_3);
return x_5;
}
}
obj* l_reader__t_orelse___at_lean_parser_parse__bin__lit___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_7; obj* x_8; obj* x_10; obj* x_12; 
lean::inc(x_3);
lean::inc(x_2);
x_7 = lean::apply_3(x_0, x_2, x_3, x_4);
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
obj* x_16; 
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_2);
if (lean::is_scalar(x_12)) {
 x_16 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_16 = x_12;
}
lean::cnstr_set(x_16, 0, x_8);
lean::cnstr_set(x_16, 1, x_10);
return x_16;
}
else
{
obj* x_17; uint8 x_19; 
x_17 = lean::cnstr_get(x_8, 0);
lean::inc(x_17);
x_19 = lean::cnstr_get_scalar<uint8>(x_8, sizeof(void*)*1);
if (x_19 == 0)
{
obj* x_21; obj* x_22; obj* x_24; obj* x_27; obj* x_28; 
lean::dec(x_8);
x_21 = lean::apply_3(x_1, x_2, x_3, x_10);
x_22 = lean::cnstr_get(x_21, 0);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_21, 1);
lean::inc(x_24);
lean::dec(x_21);
x_27 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_17, x_22);
if (lean::is_scalar(x_12)) {
 x_28 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_28 = x_12;
}
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_24);
return x_28;
}
else
{
obj* x_33; 
lean::dec(x_17);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_2);
if (lean::is_scalar(x_12)) {
 x_33 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_33 = x_12;
}
lean::cnstr_set(x_33, 0, x_8);
lean::cnstr_set(x_33, 1, x_10);
return x_33;
}
}
}
}
obj* l_reader__t_orelse___at_lean_parser_parse__bin__lit___spec__1(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_orelse___at_lean_parser_parse__bin__lit___spec__1___rarg), 5, 0);
return x_2;
}
}
obj* _init_l_lean_parser_monad__parsec_many1__aux_x_27___main___at_lean_parser_parse__bin__lit___spec__2___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_nat_obj(48u);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_ch___at___private_init_lean_parser_token_4__ident_x_27___spec__11___boxed), 4, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_lean_parser_monad__parsec_many1__aux_x_27___main___at_lean_parser_parse__bin__lit___spec__2___closed__2() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_nat_obj(49u);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_ch___at___private_init_lean_parser_token_4__ident_x_27___spec__11___boxed), 4, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_lean_parser_monad__parsec_many1__aux_x_27___main___at_lean_parser_parse__bin__lit___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::nat_dec_eq(x_0, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
obj* x_7; obj* x_8; obj* x_12; obj* x_13; obj* x_15; obj* x_17; 
x_7 = l_lean_parser_monad__parsec_many1__aux_x_27___main___at_lean_parser_parse__bin__lit___spec__2___closed__1;
x_8 = l_lean_parser_monad__parsec_many1__aux_x_27___main___at_lean_parser_parse__bin__lit___spec__2___closed__2;
lean::inc(x_1);
lean::inc(x_8);
lean::inc(x_7);
x_12 = l_reader__t_orelse___at_lean_parser_parse__bin__lit___spec__1___rarg(x_7, x_8, x_1, x_2, x_3);
x_13 = lean::cnstr_get(x_12, 0);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_12, 1);
lean::inc(x_15);
if (lean::is_shared(x_12)) {
 lean::dec(x_12);
 x_17 = lean::box(0);
} else {
 lean::cnstr_release(x_12, 0);
 lean::cnstr_release(x_12, 1);
 x_17 = x_12;
}
if (lean::obj_tag(x_13) == 0)
{
obj* x_18; obj* x_20; obj* x_22; obj* x_23; obj* x_24; obj* x_28; obj* x_29; obj* x_31; 
x_18 = lean::cnstr_get(x_13, 1);
lean::inc(x_18);
x_20 = lean::cnstr_get(x_13, 2);
lean::inc(x_20);
if (lean::is_shared(x_13)) {
 lean::dec(x_13);
 x_22 = lean::box(0);
} else {
 lean::cnstr_release(x_13, 0);
 lean::cnstr_release(x_13, 1);
 lean::cnstr_release(x_13, 2);
 x_22 = x_13;
}
x_23 = lean::mk_nat_obj(1u);
x_24 = lean::nat_sub(x_0, x_23);
lean::dec(x_23);
lean::dec(x_0);
lean::inc(x_18);
x_28 = l_lean_parser_monad__parsec_many1__aux_x_27___main___at_lean_parser_parse__bin__lit___spec__2(x_24, x_1, x_18, x_15);
x_29 = lean::cnstr_get(x_28, 0);
lean::inc(x_29);
x_31 = lean::cnstr_get(x_28, 1);
lean::inc(x_31);
lean::dec(x_28);
if (lean::obj_tag(x_29) == 0)
{
obj* x_36; obj* x_37; 
lean::dec(x_22);
lean::dec(x_18);
x_36 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_20, x_29);
if (lean::is_scalar(x_17)) {
 x_37 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_37 = x_17;
}
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_31);
return x_37;
}
else
{
obj* x_38; uint8 x_40; 
x_38 = lean::cnstr_get(x_29, 0);
lean::inc(x_38);
x_40 = lean::cnstr_get_scalar<uint8>(x_29, sizeof(void*)*1);
if (x_40 == 0)
{
obj* x_42; obj* x_45; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; 
lean::dec(x_29);
x_42 = lean::cnstr_get(x_38, 2);
lean::inc(x_42);
lean::dec(x_38);
x_45 = l_mjoin___rarg___closed__1;
lean::inc(x_45);
x_47 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_47, 0, x_42);
lean::closure_set(x_47, 1, x_45);
x_48 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_48, 0, x_47);
x_49 = lean::box(0);
if (lean::is_scalar(x_22)) {
 x_50 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_50 = x_22;
}
lean::cnstr_set(x_50, 0, x_49);
lean::cnstr_set(x_50, 1, x_18);
lean::cnstr_set(x_50, 2, x_48);
x_51 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_20, x_50);
if (lean::is_scalar(x_17)) {
 x_52 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_52 = x_17;
}
lean::cnstr_set(x_52, 0, x_51);
lean::cnstr_set(x_52, 1, x_31);
return x_52;
}
else
{
obj* x_56; obj* x_57; 
lean::dec(x_22);
lean::dec(x_18);
lean::dec(x_38);
x_56 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_20, x_29);
if (lean::is_scalar(x_17)) {
 x_57 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_57 = x_17;
}
lean::cnstr_set(x_57, 0, x_56);
lean::cnstr_set(x_57, 1, x_31);
return x_57;
}
}
}
else
{
obj* x_60; uint8 x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; 
lean::dec(x_1);
lean::dec(x_0);
x_60 = lean::cnstr_get(x_13, 0);
lean::inc(x_60);
x_62 = lean::cnstr_get_scalar<uint8>(x_13, sizeof(void*)*1);
if (lean::is_shared(x_13)) {
 lean::dec(x_13);
 x_63 = lean::box(0);
} else {
 lean::cnstr_release(x_13, 0);
 x_63 = x_13;
}
if (lean::is_scalar(x_63)) {
 x_64 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_64 = x_63;
}
lean::cnstr_set(x_64, 0, x_60);
lean::cnstr_set_scalar(x_64, sizeof(void*)*1, x_62);
x_65 = x_64;
if (lean::is_scalar(x_17)) {
 x_66 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_66 = x_17;
}
lean::cnstr_set(x_66, 0, x_65);
lean::cnstr_set(x_66, 1, x_15);
return x_66;
}
}
else
{
obj* x_68; obj* x_69; obj* x_72; obj* x_73; obj* x_75; obj* x_77; 
lean::dec(x_0);
x_68 = l_lean_parser_monad__parsec_many1__aux_x_27___main___at_lean_parser_parse__bin__lit___spec__2___closed__1;
x_69 = l_lean_parser_monad__parsec_many1__aux_x_27___main___at_lean_parser_parse__bin__lit___spec__2___closed__2;
lean::inc(x_69);
lean::inc(x_68);
x_72 = l_reader__t_orelse___at_lean_parser_parse__bin__lit___spec__1___rarg(x_68, x_69, x_1, x_2, x_3);
x_73 = lean::cnstr_get(x_72, 0);
lean::inc(x_73);
x_75 = lean::cnstr_get(x_72, 1);
lean::inc(x_75);
if (lean::is_shared(x_72)) {
 lean::dec(x_72);
 x_77 = lean::box(0);
} else {
 lean::cnstr_release(x_72, 0);
 lean::cnstr_release(x_72, 1);
 x_77 = x_72;
}
if (lean::obj_tag(x_73) == 0)
{
obj* x_78; obj* x_80; obj* x_82; obj* x_83; obj* x_84; obj* x_86; obj* x_87; obj* x_88; 
x_78 = lean::cnstr_get(x_73, 1);
lean::inc(x_78);
x_80 = lean::cnstr_get(x_73, 2);
lean::inc(x_80);
if (lean::is_shared(x_73)) {
 lean::dec(x_73);
 x_82 = lean::box(0);
} else {
 lean::cnstr_release(x_73, 0);
 lean::cnstr_release(x_73, 1);
 lean::cnstr_release(x_73, 2);
 x_82 = x_73;
}
x_83 = lean::box(0);
x_84 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_84);
if (lean::is_scalar(x_82)) {
 x_86 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_86 = x_82;
}
lean::cnstr_set(x_86, 0, x_83);
lean::cnstr_set(x_86, 1, x_78);
lean::cnstr_set(x_86, 2, x_84);
x_87 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_80, x_86);
if (lean::is_scalar(x_77)) {
 x_88 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_88 = x_77;
}
lean::cnstr_set(x_88, 0, x_87);
lean::cnstr_set(x_88, 1, x_75);
return x_88;
}
else
{
obj* x_89; uint8 x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_95; 
x_89 = lean::cnstr_get(x_73, 0);
lean::inc(x_89);
x_91 = lean::cnstr_get_scalar<uint8>(x_73, sizeof(void*)*1);
if (lean::is_shared(x_73)) {
 lean::dec(x_73);
 x_92 = lean::box(0);
} else {
 lean::cnstr_release(x_73, 0);
 x_92 = x_73;
}
if (lean::is_scalar(x_92)) {
 x_93 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_93 = x_92;
}
lean::cnstr_set(x_93, 0, x_89);
lean::cnstr_set_scalar(x_93, sizeof(void*)*1, x_91);
x_94 = x_93;
if (lean::is_scalar(x_77)) {
 x_95 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_95 = x_77;
}
lean::cnstr_set(x_95, 0, x_94);
lean::cnstr_set(x_95, 1, x_75);
return x_95;
}
}
}
}
obj* l_lean_parser_parse__bin__lit(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_6; uint32 x_7; obj* x_10; obj* x_11; obj* x_13; 
x_6 = lean::mk_nat_obj(48u);
x_7 = lean::unbox_uint32(x_6);
lean::dec(x_6);
lean::inc(x_0);
x_10 = l_lean_parser_monad__parsec_ch___at___private_init_lean_parser_token_4__ident_x_27___spec__11(x_7, x_0, x_1, x_2);
x_11 = lean::cnstr_get(x_10, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_10, 1);
lean::inc(x_13);
lean::dec(x_10);
if (lean::obj_tag(x_11) == 0)
{
obj* x_16; obj* x_18; obj* x_21; uint32 x_22; obj* x_26; obj* x_27; obj* x_29; 
x_16 = lean::cnstr_get(x_11, 1);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_11, 2);
lean::inc(x_18);
lean::dec(x_11);
x_21 = lean::mk_nat_obj(98u);
x_22 = lean::unbox_uint32(x_21);
lean::dec(x_21);
lean::inc(x_16);
lean::inc(x_0);
x_26 = l_lean_parser_monad__parsec_ch___at___private_init_lean_parser_token_4__ident_x_27___spec__11(x_22, x_0, x_16, x_13);
x_27 = lean::cnstr_get(x_26, 0);
lean::inc(x_27);
x_29 = lean::cnstr_get(x_26, 1);
lean::inc(x_29);
lean::dec(x_26);
if (lean::obj_tag(x_27) == 0)
{
obj* x_33; 
lean::dec(x_16);
x_33 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_18, x_27);
x_3 = x_33;
x_4 = x_29;
goto lbl_5;
}
else
{
obj* x_34; uint8 x_36; 
x_34 = lean::cnstr_get(x_27, 0);
lean::inc(x_34);
x_36 = lean::cnstr_get_scalar<uint8>(x_27, sizeof(void*)*1);
if (x_36 == 0)
{
obj* x_38; uint32 x_39; obj* x_42; obj* x_43; obj* x_45; obj* x_48; obj* x_49; 
lean::dec(x_27);
x_38 = lean::mk_nat_obj(66u);
x_39 = lean::unbox_uint32(x_38);
lean::dec(x_38);
lean::inc(x_0);
x_42 = l_lean_parser_monad__parsec_ch___at___private_init_lean_parser_token_4__ident_x_27___spec__11(x_39, x_0, x_16, x_29);
x_43 = lean::cnstr_get(x_42, 0);
lean::inc(x_43);
x_45 = lean::cnstr_get(x_42, 1);
lean::inc(x_45);
lean::dec(x_42);
x_48 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_34, x_43);
x_49 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_18, x_48);
x_3 = x_49;
x_4 = x_45;
goto lbl_5;
}
else
{
obj* x_52; 
lean::dec(x_16);
lean::dec(x_34);
x_52 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_18, x_27);
x_3 = x_52;
x_4 = x_29;
goto lbl_5;
}
}
}
else
{
obj* x_53; uint8 x_55; obj* x_56; obj* x_57; obj* x_58; 
x_53 = lean::cnstr_get(x_11, 0);
lean::inc(x_53);
x_55 = lean::cnstr_get_scalar<uint8>(x_11, sizeof(void*)*1);
if (lean::is_shared(x_11)) {
 lean::dec(x_11);
 x_56 = lean::box(0);
} else {
 lean::cnstr_release(x_11, 0);
 x_56 = x_11;
}
if (lean::is_scalar(x_56)) {
 x_57 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_57 = x_56;
}
lean::cnstr_set(x_57, 0, x_53);
lean::cnstr_set_scalar(x_57, sizeof(void*)*1, x_55);
x_58 = x_57;
x_3 = x_58;
x_4 = x_13;
goto lbl_5;
}
lbl_5:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_59; obj* x_61; obj* x_64; obj* x_65; obj* x_66; obj* x_68; obj* x_70; obj* x_71; obj* x_73; obj* x_74; obj* x_75; 
x_59 = lean::cnstr_get(x_3, 1);
lean::inc(x_59);
x_61 = lean::cnstr_get(x_3, 2);
lean::inc(x_61);
lean::dec(x_3);
x_64 = lean::string_iterator_remaining(x_59);
x_65 = l_lean_parser_monad__parsec_many1__aux_x_27___main___at_lean_parser_parse__bin__lit___spec__2(x_64, x_0, x_59, x_4);
x_66 = lean::cnstr_get(x_65, 0);
lean::inc(x_66);
x_68 = lean::cnstr_get(x_65, 1);
lean::inc(x_68);
if (lean::is_shared(x_65)) {
 lean::dec(x_65);
 x_70 = lean::box(0);
} else {
 lean::cnstr_release(x_65, 0);
 lean::cnstr_release(x_65, 1);
 x_70 = x_65;
}
x_71 = l_lean_parser_finish__comment__block___closed__2;
lean::inc(x_71);
x_73 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_71, x_66);
x_74 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_61, x_73);
if (lean::is_scalar(x_70)) {
 x_75 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_75 = x_70;
}
lean::cnstr_set(x_75, 0, x_74);
lean::cnstr_set(x_75, 1, x_68);
return x_75;
}
else
{
obj* x_77; uint8 x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; 
lean::dec(x_0);
x_77 = lean::cnstr_get(x_3, 0);
lean::inc(x_77);
x_79 = lean::cnstr_get_scalar<uint8>(x_3, sizeof(void*)*1);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_80 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 x_80 = x_3;
}
if (lean::is_scalar(x_80)) {
 x_81 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_81 = x_80;
}
lean::cnstr_set(x_81, 0, x_77);
lean::cnstr_set_scalar(x_81, sizeof(void*)*1, x_79);
x_82 = x_81;
x_83 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_83, 0, x_82);
lean::cnstr_set(x_83, 1, x_4);
return x_83;
}
}
}
}
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_parse__oct__lit___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
uint8 x_6; 
x_6 = lean::string_iterator_has_next(x_2);
if (x_6 == 0)
{
obj* x_8; 
lean::dec(x_0);
x_8 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_8;
}
else
{
uint32 x_9; obj* x_10; obj* x_11; uint8 x_12; 
x_9 = lean::string_iterator_curr(x_2);
x_10 = lean::mk_nat_obj(48u);
x_11 = lean::box_uint32(x_9);
x_12 = lean::nat_dec_le(x_10, x_11);
lean::dec(x_10);
if (x_12 == 0)
{
obj* x_16; 
lean::dec(x_11);
lean::dec(x_0);
x_16 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_16;
}
else
{
obj* x_17; uint8 x_18; 
x_17 = lean::mk_nat_obj(56u);
x_18 = lean::nat_dec_lt(x_11, x_17);
lean::dec(x_17);
lean::dec(x_11);
if (x_18 == 0)
{
obj* x_22; 
lean::dec(x_0);
x_22 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_22;
}
else
{
obj* x_23; obj* x_24; obj* x_27; obj* x_28; 
x_23 = lean::mk_nat_obj(1u);
x_24 = lean::nat_sub(x_0, x_23);
lean::dec(x_23);
lean::dec(x_0);
x_27 = lean::string_push(x_1, x_9);
x_28 = lean::string_iterator_next(x_2);
x_0 = x_24;
x_1 = x_27;
x_2 = x_28;
goto _start;
}
}
}
}
else
{
obj* x_31; 
lean::dec(x_0);
x_31 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_31;
}
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_parse__oct__lit___spec__2(uint32 x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
lean::dec(x_1);
x_5 = l_string_join___closed__1;
lean::inc(x_5);
x_7 = lean::string_push(x_5, x_0);
x_8 = lean::string_iterator_remaining(x_2);
x_9 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_parse__oct__lit___spec__3(x_8, x_7, x_2);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_3);
return x_10;
}
}
obj* l_lean_parser_monad__parsec_take__while1___at_lean_parser_parse__oct__lit___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; uint8 x_6; 
x_6 = lean::string_iterator_has_next(x_1);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_14; obj* x_15; obj* x_17; obj* x_20; obj* x_22; 
x_7 = lean::box(0);
x_8 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_9 = l_mjoin___rarg___closed__1;
lean::inc(x_0);
lean::inc(x_7);
lean::inc(x_9);
lean::inc(x_8);
x_14 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_8, x_9, x_7, x_7, x_0, x_1, x_2);
x_15 = lean::cnstr_get(x_14, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_14, 1);
lean::inc(x_17);
lean::dec(x_14);
x_20 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_20);
x_22 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_20, x_15);
x_3 = x_22;
x_4 = x_17;
goto lbl_5;
}
else
{
uint32 x_23; obj* x_24; obj* x_25; uint8 x_26; 
x_23 = lean::string_iterator_curr(x_1);
x_24 = lean::mk_nat_obj(48u);
x_25 = lean::box_uint32(x_23);
x_26 = lean::nat_dec_le(x_24, x_25);
lean::dec(x_24);
if (x_26 == 0)
{
obj* x_29; obj* x_30; obj* x_32; obj* x_34; obj* x_35; obj* x_36; obj* x_40; obj* x_41; obj* x_43; obj* x_46; obj* x_48; 
lean::dec(x_25);
x_29 = l_char_quote__core(x_23);
x_30 = l_char_has__repr___closed__1;
lean::inc(x_30);
x_32 = lean::string_append(x_30, x_29);
lean::dec(x_29);
x_34 = lean::string_append(x_32, x_30);
x_35 = lean::box(0);
x_36 = l_mjoin___rarg___closed__1;
lean::inc(x_0);
lean::inc(x_35);
lean::inc(x_36);
x_40 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_34, x_36, x_35, x_35, x_0, x_1, x_2);
x_41 = lean::cnstr_get(x_40, 0);
lean::inc(x_41);
x_43 = lean::cnstr_get(x_40, 1);
lean::inc(x_43);
lean::dec(x_40);
x_46 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_46);
x_48 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_46, x_41);
x_3 = x_48;
x_4 = x_43;
goto lbl_5;
}
else
{
obj* x_49; uint8 x_50; 
x_49 = lean::mk_nat_obj(56u);
x_50 = lean::nat_dec_lt(x_25, x_49);
lean::dec(x_49);
if (x_50 == 0)
{
obj* x_53; obj* x_54; obj* x_56; obj* x_58; obj* x_59; obj* x_60; obj* x_64; obj* x_65; obj* x_67; obj* x_70; obj* x_72; 
lean::dec(x_25);
x_53 = l_char_quote__core(x_23);
x_54 = l_char_has__repr___closed__1;
lean::inc(x_54);
x_56 = lean::string_append(x_54, x_53);
lean::dec(x_53);
x_58 = lean::string_append(x_56, x_54);
x_59 = lean::box(0);
x_60 = l_mjoin___rarg___closed__1;
lean::inc(x_0);
lean::inc(x_59);
lean::inc(x_60);
x_64 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_58, x_60, x_59, x_59, x_0, x_1, x_2);
x_65 = lean::cnstr_get(x_64, 0);
lean::inc(x_65);
x_67 = lean::cnstr_get(x_64, 1);
lean::inc(x_67);
lean::dec(x_64);
x_70 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_70);
x_72 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_70, x_65);
x_3 = x_72;
x_4 = x_67;
goto lbl_5;
}
else
{
obj* x_73; obj* x_74; obj* x_75; 
x_73 = lean::string_iterator_next(x_1);
x_74 = lean::box(0);
x_75 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_75, 0, x_25);
lean::cnstr_set(x_75, 1, x_73);
lean::cnstr_set(x_75, 2, x_74);
x_3 = x_75;
x_4 = x_2;
goto lbl_5;
}
}
}
lbl_5:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_76; obj* x_78; obj* x_80; uint32 x_83; obj* x_85; obj* x_86; obj* x_88; obj* x_90; obj* x_91; obj* x_92; 
x_76 = lean::cnstr_get(x_3, 0);
lean::inc(x_76);
x_78 = lean::cnstr_get(x_3, 1);
lean::inc(x_78);
x_80 = lean::cnstr_get(x_3, 2);
lean::inc(x_80);
lean::dec(x_3);
x_83 = lean::unbox_uint32(x_76);
lean::dec(x_76);
x_85 = l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_parse__oct__lit___spec__2(x_83, x_0, x_78, x_4);
x_86 = lean::cnstr_get(x_85, 0);
lean::inc(x_86);
x_88 = lean::cnstr_get(x_85, 1);
lean::inc(x_88);
if (lean::is_shared(x_85)) {
 lean::dec(x_85);
 x_90 = lean::box(0);
} else {
 lean::cnstr_release(x_85, 0);
 lean::cnstr_release(x_85, 1);
 x_90 = x_85;
}
x_91 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_80, x_86);
if (lean::is_scalar(x_90)) {
 x_92 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_92 = x_90;
}
lean::cnstr_set(x_92, 0, x_91);
lean::cnstr_set(x_92, 1, x_88);
return x_92;
}
else
{
obj* x_94; uint8 x_96; obj* x_97; obj* x_98; obj* x_99; obj* x_100; 
lean::dec(x_0);
x_94 = lean::cnstr_get(x_3, 0);
lean::inc(x_94);
x_96 = lean::cnstr_get_scalar<uint8>(x_3, sizeof(void*)*1);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_97 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 x_97 = x_3;
}
if (lean::is_scalar(x_97)) {
 x_98 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_98 = x_97;
}
lean::cnstr_set(x_98, 0, x_94);
lean::cnstr_set_scalar(x_98, sizeof(void*)*1, x_96);
x_99 = x_98;
x_100 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_100, 0, x_99);
lean::cnstr_set(x_100, 1, x_4);
return x_100;
}
}
}
}
obj* l_lean_parser_parse__oct__lit(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_6; uint32 x_7; obj* x_10; obj* x_11; obj* x_13; 
x_6 = lean::mk_nat_obj(48u);
x_7 = lean::unbox_uint32(x_6);
lean::dec(x_6);
lean::inc(x_0);
x_10 = l_lean_parser_monad__parsec_ch___at___private_init_lean_parser_token_4__ident_x_27___spec__11(x_7, x_0, x_1, x_2);
x_11 = lean::cnstr_get(x_10, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_10, 1);
lean::inc(x_13);
lean::dec(x_10);
if (lean::obj_tag(x_11) == 0)
{
obj* x_16; obj* x_18; obj* x_21; uint32 x_22; obj* x_26; obj* x_27; obj* x_29; 
x_16 = lean::cnstr_get(x_11, 1);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_11, 2);
lean::inc(x_18);
lean::dec(x_11);
x_21 = lean::mk_nat_obj(111u);
x_22 = lean::unbox_uint32(x_21);
lean::dec(x_21);
lean::inc(x_16);
lean::inc(x_0);
x_26 = l_lean_parser_monad__parsec_ch___at___private_init_lean_parser_token_4__ident_x_27___spec__11(x_22, x_0, x_16, x_13);
x_27 = lean::cnstr_get(x_26, 0);
lean::inc(x_27);
x_29 = lean::cnstr_get(x_26, 1);
lean::inc(x_29);
lean::dec(x_26);
if (lean::obj_tag(x_27) == 0)
{
obj* x_33; 
lean::dec(x_16);
x_33 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_18, x_27);
x_3 = x_33;
x_4 = x_29;
goto lbl_5;
}
else
{
obj* x_34; uint8 x_36; 
x_34 = lean::cnstr_get(x_27, 0);
lean::inc(x_34);
x_36 = lean::cnstr_get_scalar<uint8>(x_27, sizeof(void*)*1);
if (x_36 == 0)
{
obj* x_38; uint32 x_39; obj* x_42; obj* x_43; obj* x_45; obj* x_48; obj* x_49; 
lean::dec(x_27);
x_38 = lean::mk_nat_obj(79u);
x_39 = lean::unbox_uint32(x_38);
lean::dec(x_38);
lean::inc(x_0);
x_42 = l_lean_parser_monad__parsec_ch___at___private_init_lean_parser_token_4__ident_x_27___spec__11(x_39, x_0, x_16, x_29);
x_43 = lean::cnstr_get(x_42, 0);
lean::inc(x_43);
x_45 = lean::cnstr_get(x_42, 1);
lean::inc(x_45);
lean::dec(x_42);
x_48 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_34, x_43);
x_49 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_18, x_48);
x_3 = x_49;
x_4 = x_45;
goto lbl_5;
}
else
{
obj* x_52; 
lean::dec(x_16);
lean::dec(x_34);
x_52 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_18, x_27);
x_3 = x_52;
x_4 = x_29;
goto lbl_5;
}
}
}
else
{
obj* x_53; uint8 x_55; obj* x_56; obj* x_57; obj* x_58; 
x_53 = lean::cnstr_get(x_11, 0);
lean::inc(x_53);
x_55 = lean::cnstr_get_scalar<uint8>(x_11, sizeof(void*)*1);
if (lean::is_shared(x_11)) {
 lean::dec(x_11);
 x_56 = lean::box(0);
} else {
 lean::cnstr_release(x_11, 0);
 x_56 = x_11;
}
if (lean::is_scalar(x_56)) {
 x_57 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_57 = x_56;
}
lean::cnstr_set(x_57, 0, x_53);
lean::cnstr_set_scalar(x_57, sizeof(void*)*1, x_55);
x_58 = x_57;
x_3 = x_58;
x_4 = x_13;
goto lbl_5;
}
lbl_5:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_59; obj* x_61; obj* x_64; obj* x_65; obj* x_67; obj* x_69; obj* x_70; obj* x_71; 
x_59 = lean::cnstr_get(x_3, 1);
lean::inc(x_59);
x_61 = lean::cnstr_get(x_3, 2);
lean::inc(x_61);
lean::dec(x_3);
x_64 = l_lean_parser_monad__parsec_take__while1___at_lean_parser_parse__oct__lit___spec__1(x_0, x_59, x_4);
x_65 = lean::cnstr_get(x_64, 0);
lean::inc(x_65);
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
x_70 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_61, x_65);
if (lean::is_scalar(x_69)) {
 x_71 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_71 = x_69;
}
lean::cnstr_set(x_71, 0, x_70);
lean::cnstr_set(x_71, 1, x_67);
return x_71;
}
else
{
obj* x_73; uint8 x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; 
lean::dec(x_0);
x_73 = lean::cnstr_get(x_3, 0);
lean::inc(x_73);
x_75 = lean::cnstr_get_scalar<uint8>(x_3, sizeof(void*)*1);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_76 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 x_76 = x_3;
}
if (lean::is_scalar(x_76)) {
 x_77 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_77 = x_76;
}
lean::cnstr_set(x_77, 0, x_73);
lean::cnstr_set_scalar(x_77, sizeof(void*)*1, x_75);
x_78 = x_77;
x_79 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_79, 0, x_78);
lean::cnstr_set(x_79, 1, x_4);
return x_79;
}
}
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_parse__oct__lit___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint32 x_4; obj* x_5; 
x_4 = lean::unbox_uint32(x_0);
x_5 = l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_parse__oct__lit___spec__2(x_4, x_1, x_2, x_3);
return x_5;
}
}
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_parse__hex__lit___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
uint8 x_6; 
x_6 = lean::string_iterator_has_next(x_2);
if (x_6 == 0)
{
obj* x_8; 
lean::dec(x_0);
x_8 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_8;
}
else
{
obj* x_9; obj* x_10; uint32 x_13; uint8 x_14; 
x_9 = lean::mk_nat_obj(1u);
x_10 = lean::nat_sub(x_0, x_9);
lean::dec(x_9);
lean::dec(x_0);
x_13 = lean::string_iterator_curr(x_2);
x_14 = l_char_is__digit(x_13);
if (x_14 == 0)
{
uint8 x_15; 
x_15 = l_char_is__alpha(x_13);
if (x_15 == 0)
{
obj* x_17; 
lean::dec(x_10);
x_17 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_17;
}
else
{
obj* x_18; obj* x_19; 
x_18 = lean::string_push(x_1, x_13);
x_19 = lean::string_iterator_next(x_2);
x_0 = x_10;
x_1 = x_18;
x_2 = x_19;
goto _start;
}
}
else
{
if (x_14 == 0)
{
obj* x_22; 
lean::dec(x_10);
x_22 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_22;
}
else
{
obj* x_23; obj* x_24; 
x_23 = lean::string_push(x_1, x_13);
x_24 = lean::string_iterator_next(x_2);
x_0 = x_10;
x_1 = x_23;
x_2 = x_24;
goto _start;
}
}
}
}
else
{
obj* x_27; 
lean::dec(x_0);
x_27 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_27;
}
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_parse__hex__lit___spec__2(uint32 x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
lean::dec(x_1);
x_5 = l_string_join___closed__1;
lean::inc(x_5);
x_7 = lean::string_push(x_5, x_0);
x_8 = lean::string_iterator_remaining(x_2);
x_9 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_parse__hex__lit___spec__3(x_8, x_7, x_2);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_3);
return x_10;
}
}
obj* l_lean_parser_monad__parsec_take__while1___at_lean_parser_parse__hex__lit___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; uint8 x_6; 
x_6 = lean::string_iterator_has_next(x_1);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_14; obj* x_15; obj* x_17; obj* x_20; obj* x_22; 
x_7 = lean::box(0);
x_8 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_9 = l_mjoin___rarg___closed__1;
lean::inc(x_0);
lean::inc(x_7);
lean::inc(x_9);
lean::inc(x_8);
x_14 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_8, x_9, x_7, x_7, x_0, x_1, x_2);
x_15 = lean::cnstr_get(x_14, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_14, 1);
lean::inc(x_17);
lean::dec(x_14);
x_20 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_20);
x_22 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_20, x_15);
x_3 = x_22;
x_4 = x_17;
goto lbl_5;
}
else
{
uint32 x_23; uint8 x_24; 
x_23 = lean::string_iterator_curr(x_1);
x_24 = l_char_is__digit(x_23);
if (x_24 == 0)
{
uint8 x_25; 
x_25 = l_char_is__alpha(x_23);
if (x_25 == 0)
{
obj* x_26; obj* x_27; obj* x_29; obj* x_31; obj* x_32; obj* x_33; obj* x_37; obj* x_38; obj* x_40; obj* x_43; obj* x_45; 
x_26 = l_char_quote__core(x_23);
x_27 = l_char_has__repr___closed__1;
lean::inc(x_27);
x_29 = lean::string_append(x_27, x_26);
lean::dec(x_26);
x_31 = lean::string_append(x_29, x_27);
x_32 = lean::box(0);
x_33 = l_mjoin___rarg___closed__1;
lean::inc(x_0);
lean::inc(x_32);
lean::inc(x_33);
x_37 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_31, x_33, x_32, x_32, x_0, x_1, x_2);
x_38 = lean::cnstr_get(x_37, 0);
lean::inc(x_38);
x_40 = lean::cnstr_get(x_37, 1);
lean::inc(x_40);
lean::dec(x_37);
x_43 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_43);
x_45 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_43, x_38);
x_3 = x_45;
x_4 = x_40;
goto lbl_5;
}
else
{
obj* x_46; obj* x_47; obj* x_48; obj* x_49; 
x_46 = lean::string_iterator_next(x_1);
x_47 = lean::box(0);
x_48 = lean::box_uint32(x_23);
x_49 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_49, 0, x_48);
lean::cnstr_set(x_49, 1, x_46);
lean::cnstr_set(x_49, 2, x_47);
x_3 = x_49;
x_4 = x_2;
goto lbl_5;
}
}
else
{
if (x_24 == 0)
{
obj* x_50; obj* x_51; obj* x_53; obj* x_55; obj* x_56; obj* x_57; obj* x_61; obj* x_62; obj* x_64; obj* x_67; obj* x_69; 
x_50 = l_char_quote__core(x_23);
x_51 = l_char_has__repr___closed__1;
lean::inc(x_51);
x_53 = lean::string_append(x_51, x_50);
lean::dec(x_50);
x_55 = lean::string_append(x_53, x_51);
x_56 = lean::box(0);
x_57 = l_mjoin___rarg___closed__1;
lean::inc(x_0);
lean::inc(x_56);
lean::inc(x_57);
x_61 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_55, x_57, x_56, x_56, x_0, x_1, x_2);
x_62 = lean::cnstr_get(x_61, 0);
lean::inc(x_62);
x_64 = lean::cnstr_get(x_61, 1);
lean::inc(x_64);
lean::dec(x_61);
x_67 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_67);
x_69 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_67, x_62);
x_3 = x_69;
x_4 = x_64;
goto lbl_5;
}
else
{
obj* x_70; obj* x_71; obj* x_72; obj* x_73; 
x_70 = lean::string_iterator_next(x_1);
x_71 = lean::box(0);
x_72 = lean::box_uint32(x_23);
x_73 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_73, 0, x_72);
lean::cnstr_set(x_73, 1, x_70);
lean::cnstr_set(x_73, 2, x_71);
x_3 = x_73;
x_4 = x_2;
goto lbl_5;
}
}
}
lbl_5:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_74; obj* x_76; obj* x_78; uint32 x_81; obj* x_83; obj* x_84; obj* x_86; obj* x_88; obj* x_89; obj* x_90; 
x_74 = lean::cnstr_get(x_3, 0);
lean::inc(x_74);
x_76 = lean::cnstr_get(x_3, 1);
lean::inc(x_76);
x_78 = lean::cnstr_get(x_3, 2);
lean::inc(x_78);
lean::dec(x_3);
x_81 = lean::unbox_uint32(x_74);
lean::dec(x_74);
x_83 = l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_parse__hex__lit___spec__2(x_81, x_0, x_76, x_4);
x_84 = lean::cnstr_get(x_83, 0);
lean::inc(x_84);
x_86 = lean::cnstr_get(x_83, 1);
lean::inc(x_86);
if (lean::is_shared(x_83)) {
 lean::dec(x_83);
 x_88 = lean::box(0);
} else {
 lean::cnstr_release(x_83, 0);
 lean::cnstr_release(x_83, 1);
 x_88 = x_83;
}
x_89 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_78, x_84);
if (lean::is_scalar(x_88)) {
 x_90 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_90 = x_88;
}
lean::cnstr_set(x_90, 0, x_89);
lean::cnstr_set(x_90, 1, x_86);
return x_90;
}
else
{
obj* x_92; uint8 x_94; obj* x_95; obj* x_96; obj* x_97; obj* x_98; 
lean::dec(x_0);
x_92 = lean::cnstr_get(x_3, 0);
lean::inc(x_92);
x_94 = lean::cnstr_get_scalar<uint8>(x_3, sizeof(void*)*1);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_95 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 x_95 = x_3;
}
if (lean::is_scalar(x_95)) {
 x_96 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_96 = x_95;
}
lean::cnstr_set(x_96, 0, x_92);
lean::cnstr_set_scalar(x_96, sizeof(void*)*1, x_94);
x_97 = x_96;
x_98 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_98, 0, x_97);
lean::cnstr_set(x_98, 1, x_4);
return x_98;
}
}
}
}
obj* l_lean_parser_parse__hex__lit(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_6; uint32 x_7; obj* x_10; obj* x_11; obj* x_13; 
x_6 = lean::mk_nat_obj(48u);
x_7 = lean::unbox_uint32(x_6);
lean::dec(x_6);
lean::inc(x_0);
x_10 = l_lean_parser_monad__parsec_ch___at___private_init_lean_parser_token_4__ident_x_27___spec__11(x_7, x_0, x_1, x_2);
x_11 = lean::cnstr_get(x_10, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_10, 1);
lean::inc(x_13);
lean::dec(x_10);
if (lean::obj_tag(x_11) == 0)
{
obj* x_16; obj* x_18; obj* x_21; uint32 x_22; obj* x_26; obj* x_27; obj* x_29; 
x_16 = lean::cnstr_get(x_11, 1);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_11, 2);
lean::inc(x_18);
lean::dec(x_11);
x_21 = lean::mk_nat_obj(120u);
x_22 = lean::unbox_uint32(x_21);
lean::dec(x_21);
lean::inc(x_16);
lean::inc(x_0);
x_26 = l_lean_parser_monad__parsec_ch___at___private_init_lean_parser_token_4__ident_x_27___spec__11(x_22, x_0, x_16, x_13);
x_27 = lean::cnstr_get(x_26, 0);
lean::inc(x_27);
x_29 = lean::cnstr_get(x_26, 1);
lean::inc(x_29);
lean::dec(x_26);
if (lean::obj_tag(x_27) == 0)
{
obj* x_33; 
lean::dec(x_16);
x_33 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_18, x_27);
x_3 = x_33;
x_4 = x_29;
goto lbl_5;
}
else
{
obj* x_34; uint8 x_36; 
x_34 = lean::cnstr_get(x_27, 0);
lean::inc(x_34);
x_36 = lean::cnstr_get_scalar<uint8>(x_27, sizeof(void*)*1);
if (x_36 == 0)
{
obj* x_38; uint32 x_39; obj* x_42; obj* x_43; obj* x_45; obj* x_48; obj* x_49; 
lean::dec(x_27);
x_38 = lean::mk_nat_obj(88u);
x_39 = lean::unbox_uint32(x_38);
lean::dec(x_38);
lean::inc(x_0);
x_42 = l_lean_parser_monad__parsec_ch___at___private_init_lean_parser_token_4__ident_x_27___spec__11(x_39, x_0, x_16, x_29);
x_43 = lean::cnstr_get(x_42, 0);
lean::inc(x_43);
x_45 = lean::cnstr_get(x_42, 1);
lean::inc(x_45);
lean::dec(x_42);
x_48 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_34, x_43);
x_49 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_18, x_48);
x_3 = x_49;
x_4 = x_45;
goto lbl_5;
}
else
{
obj* x_52; 
lean::dec(x_16);
lean::dec(x_34);
x_52 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_18, x_27);
x_3 = x_52;
x_4 = x_29;
goto lbl_5;
}
}
}
else
{
obj* x_53; uint8 x_55; obj* x_56; obj* x_57; obj* x_58; 
x_53 = lean::cnstr_get(x_11, 0);
lean::inc(x_53);
x_55 = lean::cnstr_get_scalar<uint8>(x_11, sizeof(void*)*1);
if (lean::is_shared(x_11)) {
 lean::dec(x_11);
 x_56 = lean::box(0);
} else {
 lean::cnstr_release(x_11, 0);
 x_56 = x_11;
}
if (lean::is_scalar(x_56)) {
 x_57 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_57 = x_56;
}
lean::cnstr_set(x_57, 0, x_53);
lean::cnstr_set_scalar(x_57, sizeof(void*)*1, x_55);
x_58 = x_57;
x_3 = x_58;
x_4 = x_13;
goto lbl_5;
}
lbl_5:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_59; obj* x_61; obj* x_64; obj* x_65; obj* x_67; obj* x_69; obj* x_70; obj* x_71; 
x_59 = lean::cnstr_get(x_3, 1);
lean::inc(x_59);
x_61 = lean::cnstr_get(x_3, 2);
lean::inc(x_61);
lean::dec(x_3);
x_64 = l_lean_parser_monad__parsec_take__while1___at_lean_parser_parse__hex__lit___spec__1(x_0, x_59, x_4);
x_65 = lean::cnstr_get(x_64, 0);
lean::inc(x_65);
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
x_70 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_61, x_65);
if (lean::is_scalar(x_69)) {
 x_71 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_71 = x_69;
}
lean::cnstr_set(x_71, 0, x_70);
lean::cnstr_set(x_71, 1, x_67);
return x_71;
}
else
{
obj* x_73; uint8 x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; 
lean::dec(x_0);
x_73 = lean::cnstr_get(x_3, 0);
lean::inc(x_73);
x_75 = lean::cnstr_get_scalar<uint8>(x_3, sizeof(void*)*1);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_76 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 x_76 = x_3;
}
if (lean::is_scalar(x_76)) {
 x_77 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_77 = x_76;
}
lean::cnstr_set(x_77, 0, x_73);
lean::cnstr_set_scalar(x_77, sizeof(void*)*1, x_75);
x_78 = x_77;
x_79 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_79, 0, x_78);
lean::cnstr_set(x_79, 1, x_4);
return x_79;
}
}
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_parse__hex__lit___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint32 x_4; obj* x_5; 
x_4 = lean::unbox_uint32(x_0);
x_5 = l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_parse__hex__lit___spec__2(x_4, x_1, x_2, x_3);
return x_5;
}
}
obj* _init_l_lean_parser_number() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("number");
x_6 = lean_name_mk_string(x_4, x_5);
return x_6;
}
}
obj* _init_l_lean_parser_number_has__view_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(0);
x_1 = lean::alloc_cnstr(3, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_lean_parser_number_has__view_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(0);
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_lean_parser_number_has__view_x_27___lambda__1___closed__3() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(0);
x_1 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_lean_parser_number_has__view_x_27___lambda__1___closed__4() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(0);
x_1 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_lean_parser_number_has__view_x_27___lambda__1___closed__5() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; 
x_3 = lean::box(3);
x_4 = lean::mk_nat_obj(0u);
x_0 = x_3;
x_1 = x_4;
goto lbl_2;
lbl_2:
{
obj* x_5; uint8 x_6; 
x_5 = lean::mk_nat_obj(0u);
x_6 = lean::nat_dec_eq(x_1, x_5);
lean::dec(x_5);
if (x_6 == 0)
{
obj* x_8; uint8 x_9; 
x_8 = lean::mk_nat_obj(1u);
x_9 = lean::nat_dec_eq(x_1, x_8);
lean::dec(x_8);
if (x_9 == 0)
{
obj* x_11; uint8 x_12; 
x_11 = lean::mk_nat_obj(2u);
x_12 = lean::nat_dec_eq(x_1, x_11);
lean::dec(x_11);
lean::dec(x_1);
if (x_12 == 0)
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_15; obj* x_18; obj* x_19; 
x_15 = lean::cnstr_get(x_0, 0);
lean::inc(x_15);
lean::dec(x_0);
x_18 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_18, 0, x_15);
x_19 = lean::alloc_cnstr(3, 1, 0);
lean::cnstr_set(x_19, 0, x_18);
return x_19;
}
case 1:
{
obj* x_21; 
lean::dec(x_0);
x_21 = l_lean_parser_number_has__view_x_27___lambda__1___closed__1;
lean::inc(x_21);
return x_21;
}
case 2:
{
obj* x_24; 
lean::dec(x_0);
x_24 = l_lean_parser_number_has__view_x_27___lambda__1___closed__1;
lean::inc(x_24);
return x_24;
}
default:
{
obj* x_27; 
lean::dec(x_0);
x_27 = l_lean_parser_number_has__view_x_27___lambda__1___closed__1;
lean::inc(x_27);
return x_27;
}
}
}
else
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_29; obj* x_32; obj* x_33; 
x_29 = lean::cnstr_get(x_0, 0);
lean::inc(x_29);
lean::dec(x_0);
x_32 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_32, 0, x_29);
x_33 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_33, 0, x_32);
return x_33;
}
case 1:
{
obj* x_35; 
lean::dec(x_0);
x_35 = l_lean_parser_number_has__view_x_27___lambda__1___closed__2;
lean::inc(x_35);
return x_35;
}
case 2:
{
obj* x_38; 
lean::dec(x_0);
x_38 = l_lean_parser_number_has__view_x_27___lambda__1___closed__2;
lean::inc(x_38);
return x_38;
}
default:
{
obj* x_41; 
lean::dec(x_0);
x_41 = l_lean_parser_number_has__view_x_27___lambda__1___closed__2;
lean::inc(x_41);
return x_41;
}
}
}
}
else
{
lean::dec(x_1);
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_44; obj* x_47; obj* x_48; 
x_44 = lean::cnstr_get(x_0, 0);
lean::inc(x_44);
lean::dec(x_0);
x_47 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_47, 0, x_44);
x_48 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_48, 0, x_47);
return x_48;
}
case 1:
{
obj* x_50; 
lean::dec(x_0);
x_50 = l_lean_parser_number_has__view_x_27___lambda__1___closed__3;
lean::inc(x_50);
return x_50;
}
case 2:
{
obj* x_53; 
lean::dec(x_0);
x_53 = l_lean_parser_number_has__view_x_27___lambda__1___closed__3;
lean::inc(x_53);
return x_53;
}
default:
{
obj* x_56; 
lean::dec(x_0);
x_56 = l_lean_parser_number_has__view_x_27___lambda__1___closed__3;
lean::inc(x_56);
return x_56;
}
}
}
}
else
{
lean::dec(x_1);
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_59; obj* x_62; obj* x_63; 
x_59 = lean::cnstr_get(x_0, 0);
lean::inc(x_59);
lean::dec(x_0);
x_62 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_62, 0, x_59);
x_63 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_63, 0, x_62);
return x_63;
}
case 1:
{
obj* x_65; 
lean::dec(x_0);
x_65 = l_lean_parser_number_has__view_x_27___lambda__1___closed__4;
lean::inc(x_65);
return x_65;
}
case 2:
{
obj* x_68; 
lean::dec(x_0);
x_68 = l_lean_parser_number_has__view_x_27___lambda__1___closed__4;
lean::inc(x_68);
return x_68;
}
default:
{
obj* x_71; 
lean::dec(x_0);
x_71 = l_lean_parser_number_has__view_x_27___lambda__1___closed__4;
lean::inc(x_71);
return x_71;
}
}
}
}
}
}
obj* _init_l_lean_parser_number_has__view_x_27___lambda__1___closed__6() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("number");
x_6 = lean_name_mk_string(x_4, x_5);
return x_6;
}
}
obj* l_lean_parser_number_has__view_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_4 = l_lean_parser_syntax_as__node___main(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; 
lean::dec(x_4);
x_6 = l_lean_parser_number_has__view_x_27___lambda__1___closed__5;
lean::inc(x_6);
return x_6;
}
else
{
obj* x_8; obj* x_11; obj* x_13; obj* x_16; uint8 x_17; 
x_8 = lean::cnstr_get(x_4, 0);
lean::inc(x_8);
lean::dec(x_4);
x_11 = lean::cnstr_get(x_8, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_8, 1);
lean::inc(x_13);
lean::dec(x_8);
x_16 = l_lean_parser_number_has__view_x_27___lambda__1___closed__6;
x_17 = lean_name_dec_eq(x_11, x_16);
lean::dec(x_11);
if (x_17 == 0)
{
obj* x_20; 
lean::dec(x_13);
x_20 = l_lean_parser_number_has__view_x_27___lambda__1___closed__5;
lean::inc(x_20);
return x_20;
}
else
{
if (lean::obj_tag(x_13) == 0)
{
obj* x_23; 
lean::dec(x_13);
x_23 = l_lean_parser_number_has__view_x_27___lambda__1___closed__5;
lean::inc(x_23);
return x_23;
}
else
{
obj* x_25; obj* x_27; 
x_25 = lean::cnstr_get(x_13, 0);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_13, 1);
lean::inc(x_27);
lean::dec(x_13);
if (lean::obj_tag(x_27) == 0)
{
obj* x_31; 
lean::dec(x_27);
x_31 = l_lean_parser_syntax_as__node___main(x_25);
if (lean::obj_tag(x_31) == 0)
{
obj* x_33; 
lean::dec(x_31);
x_33 = l_lean_parser_number_has__view_x_27___lambda__1___closed__5;
lean::inc(x_33);
return x_33;
}
else
{
obj* x_35; obj* x_38; obj* x_40; 
x_35 = lean::cnstr_get(x_31, 0);
lean::inc(x_35);
lean::dec(x_31);
x_38 = lean::cnstr_get(x_35, 0);
lean::inc(x_38);
x_40 = lean::cnstr_get(x_35, 1);
lean::inc(x_40);
lean::dec(x_35);
switch (lean::obj_tag(x_38)) {
case 0:
{
obj* x_45; 
lean::dec(x_38);
lean::dec(x_40);
x_45 = l_lean_parser_number_has__view_x_27___lambda__1___closed__5;
lean::inc(x_45);
return x_45;
}
case 1:
{
obj* x_49; 
lean::dec(x_38);
lean::dec(x_40);
x_49 = l_lean_parser_number_has__view_x_27___lambda__1___closed__5;
lean::inc(x_49);
return x_49;
}
default:
{
obj* x_51; obj* x_53; obj* x_56; uint8 x_57; 
x_51 = lean::cnstr_get(x_38, 0);
lean::inc(x_51);
x_53 = lean::cnstr_get(x_38, 1);
lean::inc(x_53);
lean::dec(x_38);
x_56 = lean::box(0);
x_57 = lean_name_dec_eq(x_51, x_56);
lean::dec(x_56);
lean::dec(x_51);
if (x_57 == 0)
{
obj* x_62; 
lean::dec(x_40);
lean::dec(x_53);
x_62 = l_lean_parser_number_has__view_x_27___lambda__1___closed__5;
lean::inc(x_62);
return x_62;
}
else
{
if (lean::obj_tag(x_40) == 0)
{
obj* x_66; 
lean::dec(x_40);
lean::dec(x_53);
x_66 = l_lean_parser_number_has__view_x_27___lambda__1___closed__5;
lean::inc(x_66);
return x_66;
}
else
{
obj* x_68; obj* x_70; 
x_68 = lean::cnstr_get(x_40, 0);
lean::inc(x_68);
x_70 = lean::cnstr_get(x_40, 1);
lean::inc(x_70);
lean::dec(x_40);
if (lean::obj_tag(x_70) == 0)
{
lean::dec(x_70);
x_1 = x_68;
x_2 = x_53;
goto lbl_3;
}
else
{
obj* x_77; 
lean::dec(x_53);
lean::dec(x_68);
lean::dec(x_70);
x_77 = l_lean_parser_number_has__view_x_27___lambda__1___closed__5;
lean::inc(x_77);
return x_77;
}
}
}
}
}
}
}
else
{
obj* x_81; 
lean::dec(x_25);
lean::dec(x_27);
x_81 = l_lean_parser_number_has__view_x_27___lambda__1___closed__5;
lean::inc(x_81);
return x_81;
}
}
}
}
lbl_3:
{
obj* x_83; uint8 x_84; 
x_83 = lean::mk_nat_obj(0u);
x_84 = lean::nat_dec_eq(x_2, x_83);
lean::dec(x_83);
if (x_84 == 0)
{
obj* x_86; uint8 x_87; 
x_86 = lean::mk_nat_obj(1u);
x_87 = lean::nat_dec_eq(x_2, x_86);
lean::dec(x_86);
if (x_87 == 0)
{
obj* x_89; uint8 x_90; 
x_89 = lean::mk_nat_obj(2u);
x_90 = lean::nat_dec_eq(x_2, x_89);
lean::dec(x_89);
lean::dec(x_2);
if (x_90 == 0)
{
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_93; obj* x_96; obj* x_97; 
x_93 = lean::cnstr_get(x_1, 0);
lean::inc(x_93);
lean::dec(x_1);
x_96 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_96, 0, x_93);
x_97 = lean::alloc_cnstr(3, 1, 0);
lean::cnstr_set(x_97, 0, x_96);
return x_97;
}
case 1:
{
obj* x_99; 
lean::dec(x_1);
x_99 = l_lean_parser_number_has__view_x_27___lambda__1___closed__1;
lean::inc(x_99);
return x_99;
}
case 2:
{
obj* x_102; 
lean::dec(x_1);
x_102 = l_lean_parser_number_has__view_x_27___lambda__1___closed__1;
lean::inc(x_102);
return x_102;
}
default:
{
obj* x_105; 
lean::dec(x_1);
x_105 = l_lean_parser_number_has__view_x_27___lambda__1___closed__1;
lean::inc(x_105);
return x_105;
}
}
}
else
{
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_107; obj* x_110; obj* x_111; 
x_107 = lean::cnstr_get(x_1, 0);
lean::inc(x_107);
lean::dec(x_1);
x_110 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_110, 0, x_107);
x_111 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_111, 0, x_110);
return x_111;
}
case 1:
{
obj* x_113; 
lean::dec(x_1);
x_113 = l_lean_parser_number_has__view_x_27___lambda__1___closed__2;
lean::inc(x_113);
return x_113;
}
case 2:
{
obj* x_116; 
lean::dec(x_1);
x_116 = l_lean_parser_number_has__view_x_27___lambda__1___closed__2;
lean::inc(x_116);
return x_116;
}
default:
{
obj* x_119; 
lean::dec(x_1);
x_119 = l_lean_parser_number_has__view_x_27___lambda__1___closed__2;
lean::inc(x_119);
return x_119;
}
}
}
}
else
{
lean::dec(x_2);
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_122; obj* x_125; obj* x_126; 
x_122 = lean::cnstr_get(x_1, 0);
lean::inc(x_122);
lean::dec(x_1);
x_125 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_125, 0, x_122);
x_126 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_126, 0, x_125);
return x_126;
}
case 1:
{
obj* x_128; 
lean::dec(x_1);
x_128 = l_lean_parser_number_has__view_x_27___lambda__1___closed__3;
lean::inc(x_128);
return x_128;
}
case 2:
{
obj* x_131; 
lean::dec(x_1);
x_131 = l_lean_parser_number_has__view_x_27___lambda__1___closed__3;
lean::inc(x_131);
return x_131;
}
default:
{
obj* x_134; 
lean::dec(x_1);
x_134 = l_lean_parser_number_has__view_x_27___lambda__1___closed__3;
lean::inc(x_134);
return x_134;
}
}
}
}
else
{
lean::dec(x_2);
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_137; obj* x_140; obj* x_141; 
x_137 = lean::cnstr_get(x_1, 0);
lean::inc(x_137);
lean::dec(x_1);
x_140 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_140, 0, x_137);
x_141 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_141, 0, x_140);
return x_141;
}
case 1:
{
obj* x_143; 
lean::dec(x_1);
x_143 = l_lean_parser_number_has__view_x_27___lambda__1___closed__4;
lean::inc(x_143);
return x_143;
}
case 2:
{
obj* x_146; 
lean::dec(x_1);
x_146 = l_lean_parser_number_has__view_x_27___lambda__1___closed__4;
lean::inc(x_146);
return x_146;
}
default:
{
obj* x_149; 
lean::dec(x_1);
x_149 = l_lean_parser_number_has__view_x_27___lambda__1___closed__4;
lean::inc(x_149);
return x_149;
}
}
}
}
}
}
obj* _init_l_lean_parser_number_has__view_x_27___lambda__2___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_nat_obj(2u);
x_2 = lean_name_mk_numeral(x_0, x_1);
return x_2;
}
}
obj* _init_l_lean_parser_number_has__view_x_27___lambda__2___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_nat_obj(3u);
x_2 = lean_name_mk_numeral(x_0, x_1);
return x_2;
}
}
obj* l_lean_parser_number_has__view_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::box(0);
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_2; obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_11; obj* x_12; obj* x_14; obj* x_15; obj* x_16; obj* x_18; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
x_5 = l_lean_parser_raw_view___rarg___lambda__3___closed__1;
lean::inc(x_5);
x_7 = l_option_map___rarg(x_5, x_2);
x_8 = lean::box(3);
x_9 = l_option_get__or__else___main___rarg(x_7, x_8);
lean::inc(x_1);
x_11 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_11, 0, x_9);
lean::cnstr_set(x_11, 1, x_1);
x_12 = l_lean_parser_detail__ident__part_has__view_x_27___lambda__2___closed__1;
lean::inc(x_12);
x_14 = l_lean_parser_syntax_mk__node(x_12, x_11);
x_15 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_15, 0, x_14);
lean::cnstr_set(x_15, 1, x_1);
x_16 = l_lean_parser_number;
lean::inc(x_16);
x_18 = l_lean_parser_syntax_mk__node(x_16, x_15);
return x_18;
}
case 1:
{
obj* x_19; obj* x_22; obj* x_24; obj* x_25; obj* x_26; obj* x_28; obj* x_29; obj* x_31; obj* x_32; obj* x_33; obj* x_35; 
x_19 = lean::cnstr_get(x_0, 0);
lean::inc(x_19);
lean::dec(x_0);
x_22 = l_lean_parser_raw_view___rarg___lambda__3___closed__1;
lean::inc(x_22);
x_24 = l_option_map___rarg(x_22, x_19);
x_25 = lean::box(3);
x_26 = l_option_get__or__else___main___rarg(x_24, x_25);
lean::inc(x_1);
x_28 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_28, 0, x_26);
lean::cnstr_set(x_28, 1, x_1);
x_29 = l_lean_parser_detail__ident__part_has__view_x_27___lambda__2___closed__2;
lean::inc(x_29);
x_31 = l_lean_parser_syntax_mk__node(x_29, x_28);
x_32 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_1);
x_33 = l_lean_parser_number;
lean::inc(x_33);
x_35 = l_lean_parser_syntax_mk__node(x_33, x_32);
return x_35;
}
case 2:
{
obj* x_36; obj* x_39; obj* x_41; obj* x_42; obj* x_43; obj* x_45; obj* x_46; obj* x_48; obj* x_49; obj* x_50; obj* x_52; 
x_36 = lean::cnstr_get(x_0, 0);
lean::inc(x_36);
lean::dec(x_0);
x_39 = l_lean_parser_raw_view___rarg___lambda__3___closed__1;
lean::inc(x_39);
x_41 = l_option_map___rarg(x_39, x_36);
x_42 = lean::box(3);
x_43 = l_option_get__or__else___main___rarg(x_41, x_42);
lean::inc(x_1);
x_45 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_45, 0, x_43);
lean::cnstr_set(x_45, 1, x_1);
x_46 = l_lean_parser_number_has__view_x_27___lambda__2___closed__1;
lean::inc(x_46);
x_48 = l_lean_parser_syntax_mk__node(x_46, x_45);
x_49 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_49, 0, x_48);
lean::cnstr_set(x_49, 1, x_1);
x_50 = l_lean_parser_number;
lean::inc(x_50);
x_52 = l_lean_parser_syntax_mk__node(x_50, x_49);
return x_52;
}
default:
{
obj* x_53; obj* x_56; obj* x_58; obj* x_59; obj* x_60; obj* x_62; obj* x_63; obj* x_65; obj* x_66; obj* x_67; obj* x_69; 
x_53 = lean::cnstr_get(x_0, 0);
lean::inc(x_53);
lean::dec(x_0);
x_56 = l_lean_parser_raw_view___rarg___lambda__3___closed__1;
lean::inc(x_56);
x_58 = l_option_map___rarg(x_56, x_53);
x_59 = lean::box(3);
x_60 = l_option_get__or__else___main___rarg(x_58, x_59);
lean::inc(x_1);
x_62 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_62, 0, x_60);
lean::cnstr_set(x_62, 1, x_1);
x_63 = l_lean_parser_number_has__view_x_27___lambda__2___closed__2;
lean::inc(x_63);
x_65 = l_lean_parser_syntax_mk__node(x_63, x_62);
x_66 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_66, 0, x_65);
lean::cnstr_set(x_66, 1, x_1);
x_67 = l_lean_parser_number;
lean::inc(x_67);
x_69 = l_lean_parser_syntax_mk__node(x_67, x_66);
return x_69;
}
}
}
}
obj* _init_l_lean_parser_number_has__view_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_number_has__view_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_number_has__view_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_lean_parser_number_has__view() {
_start:
{
obj* x_0; 
x_0 = l_lean_parser_number_has__view_x_27;
lean::inc(x_0);
return x_0;
}
}
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_number_x_27___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
uint8 x_6; 
x_6 = lean::string_iterator_has_next(x_2);
if (x_6 == 0)
{
obj* x_8; 
lean::dec(x_0);
x_8 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_8;
}
else
{
uint32 x_9; uint8 x_10; 
x_9 = lean::string_iterator_curr(x_2);
x_10 = l_char_is__digit(x_9);
if (x_10 == 0)
{
obj* x_12; 
lean::dec(x_0);
x_12 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_12;
}
else
{
obj* x_13; obj* x_14; obj* x_17; obj* x_18; 
x_13 = lean::mk_nat_obj(1u);
x_14 = lean::nat_sub(x_0, x_13);
lean::dec(x_13);
lean::dec(x_0);
x_17 = lean::string_push(x_1, x_9);
x_18 = lean::string_iterator_next(x_2);
x_0 = x_14;
x_1 = x_17;
x_2 = x_18;
goto _start;
}
}
}
else
{
obj* x_21; 
lean::dec(x_0);
x_21 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_21;
}
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_number_x_27___spec__2(uint32 x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
lean::dec(x_1);
x_5 = l_string_join___closed__1;
lean::inc(x_5);
x_7 = lean::string_push(x_5, x_0);
x_8 = lean::string_iterator_remaining(x_2);
x_9 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_number_x_27___spec__3(x_8, x_7, x_2);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_3);
return x_10;
}
}
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_number_x_27___spec__5(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
uint8 x_6; 
x_6 = lean::string_iterator_has_next(x_2);
if (x_6 == 0)
{
obj* x_8; 
lean::dec(x_0);
x_8 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_8;
}
else
{
uint32 x_9; uint8 x_10; 
x_9 = lean::string_iterator_curr(x_2);
x_10 = l_char_is__digit(x_9);
if (x_10 == 0)
{
obj* x_12; 
lean::dec(x_0);
x_12 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_12;
}
else
{
obj* x_13; obj* x_14; obj* x_17; obj* x_18; 
x_13 = lean::mk_nat_obj(1u);
x_14 = lean::nat_sub(x_0, x_13);
lean::dec(x_13);
lean::dec(x_0);
x_17 = lean::string_push(x_1, x_9);
x_18 = lean::string_iterator_next(x_2);
x_0 = x_14;
x_1 = x_17;
x_2 = x_18;
goto _start;
}
}
}
else
{
obj* x_21; 
lean::dec(x_0);
x_21 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_21;
}
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_number_x_27___spec__4(uint32 x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
lean::dec(x_1);
x_5 = l_string_join___closed__1;
lean::inc(x_5);
x_7 = lean::string_push(x_5, x_0);
x_8 = lean::string_iterator_remaining(x_2);
x_9 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_number_x_27___spec__5(x_8, x_7, x_2);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_3);
return x_10;
}
}
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_number_x_27___spec__7(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
uint8 x_6; 
x_6 = lean::string_iterator_has_next(x_2);
if (x_6 == 0)
{
obj* x_8; 
lean::dec(x_0);
x_8 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_8;
}
else
{
uint32 x_9; uint8 x_10; 
x_9 = lean::string_iterator_curr(x_2);
x_10 = l_char_is__digit(x_9);
if (x_10 == 0)
{
obj* x_12; 
lean::dec(x_0);
x_12 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_12;
}
else
{
obj* x_13; obj* x_14; obj* x_17; obj* x_18; 
x_13 = lean::mk_nat_obj(1u);
x_14 = lean::nat_sub(x_0, x_13);
lean::dec(x_13);
lean::dec(x_0);
x_17 = lean::string_push(x_1, x_9);
x_18 = lean::string_iterator_next(x_2);
x_0 = x_14;
x_1 = x_17;
x_2 = x_18;
goto _start;
}
}
}
else
{
obj* x_21; 
lean::dec(x_0);
x_21 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_21;
}
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_number_x_27___spec__6(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint32 x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
lean::dec(x_1);
x_5 = lean::string_iterator_curr(x_0);
lean::dec(x_0);
x_7 = l_string_join___closed__1;
lean::inc(x_7);
x_9 = lean::string_push(x_7, x_5);
x_10 = lean::string_iterator_remaining(x_2);
x_11 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_number_x_27___spec__7(x_10, x_9, x_2);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_3);
return x_12;
}
}
obj* l_lean_parser_monad__parsec_take__while1___at_lean_parser_number_x_27___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = lean::string_iterator_has_next(x_1);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; obj* x_11; obj* x_12; obj* x_14; obj* x_16; obj* x_17; obj* x_19; 
x_4 = lean::box(0);
x_5 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_6 = l_mjoin___rarg___closed__1;
lean::inc(x_0);
lean::inc(x_4);
lean::inc(x_6);
lean::inc(x_5);
x_11 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_5, x_6, x_4, x_4, x_0, x_1, x_2);
x_12 = lean::cnstr_get(x_11, 0);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_11, 1);
lean::inc(x_14);
if (lean::is_shared(x_11)) {
 lean::dec(x_11);
 x_16 = lean::box(0);
} else {
 lean::cnstr_release(x_11, 0);
 lean::cnstr_release(x_11, 1);
 x_16 = x_11;
}
x_17 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_17);
x_19 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_17, x_12);
if (lean::obj_tag(x_19) == 0)
{
obj* x_20; obj* x_22; obj* x_24; uint32 x_27; obj* x_29; obj* x_30; obj* x_32; obj* x_35; obj* x_36; 
x_20 = lean::cnstr_get(x_19, 0);
lean::inc(x_20);
x_22 = lean::cnstr_get(x_19, 1);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_19, 2);
lean::inc(x_24);
lean::dec(x_19);
x_27 = lean::unbox_uint32(x_20);
lean::dec(x_20);
x_29 = l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_number_x_27___spec__2(x_27, x_0, x_22, x_14);
x_30 = lean::cnstr_get(x_29, 0);
lean::inc(x_30);
x_32 = lean::cnstr_get(x_29, 1);
lean::inc(x_32);
lean::dec(x_29);
x_35 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_24, x_30);
if (lean::is_scalar(x_16)) {
 x_36 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_36 = x_16;
}
lean::cnstr_set(x_36, 0, x_35);
lean::cnstr_set(x_36, 1, x_32);
return x_36;
}
else
{
obj* x_38; uint8 x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; 
lean::dec(x_0);
x_38 = lean::cnstr_get(x_19, 0);
lean::inc(x_38);
x_40 = lean::cnstr_get_scalar<uint8>(x_19, sizeof(void*)*1);
if (lean::is_shared(x_19)) {
 lean::dec(x_19);
 x_41 = lean::box(0);
} else {
 lean::cnstr_release(x_19, 0);
 x_41 = x_19;
}
if (lean::is_scalar(x_41)) {
 x_42 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_42 = x_41;
}
lean::cnstr_set(x_42, 0, x_38);
lean::cnstr_set_scalar(x_42, sizeof(void*)*1, x_40);
x_43 = x_42;
if (lean::is_scalar(x_16)) {
 x_44 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_44 = x_16;
}
lean::cnstr_set(x_44, 0, x_43);
lean::cnstr_set(x_44, 1, x_14);
return x_44;
}
}
else
{
uint32 x_45; uint8 x_46; 
x_45 = lean::string_iterator_curr(x_1);
x_46 = l_char_is__digit(x_45);
if (x_46 == 0)
{
obj* x_47; obj* x_48; obj* x_50; obj* x_52; obj* x_53; obj* x_54; obj* x_58; obj* x_59; obj* x_61; obj* x_63; obj* x_64; obj* x_66; 
x_47 = l_char_quote__core(x_45);
x_48 = l_char_has__repr___closed__1;
lean::inc(x_48);
x_50 = lean::string_append(x_48, x_47);
lean::dec(x_47);
x_52 = lean::string_append(x_50, x_48);
x_53 = lean::box(0);
x_54 = l_mjoin___rarg___closed__1;
lean::inc(x_0);
lean::inc(x_53);
lean::inc(x_54);
x_58 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_52, x_54, x_53, x_53, x_0, x_1, x_2);
x_59 = lean::cnstr_get(x_58, 0);
lean::inc(x_59);
x_61 = lean::cnstr_get(x_58, 1);
lean::inc(x_61);
if (lean::is_shared(x_58)) {
 lean::dec(x_58);
 x_63 = lean::box(0);
} else {
 lean::cnstr_release(x_58, 0);
 lean::cnstr_release(x_58, 1);
 x_63 = x_58;
}
x_64 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_64);
x_66 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_64, x_59);
if (lean::obj_tag(x_66) == 0)
{
obj* x_67; obj* x_69; obj* x_71; uint32 x_74; obj* x_76; obj* x_77; obj* x_79; obj* x_82; obj* x_83; 
x_67 = lean::cnstr_get(x_66, 0);
lean::inc(x_67);
x_69 = lean::cnstr_get(x_66, 1);
lean::inc(x_69);
x_71 = lean::cnstr_get(x_66, 2);
lean::inc(x_71);
lean::dec(x_66);
x_74 = lean::unbox_uint32(x_67);
lean::dec(x_67);
x_76 = l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_number_x_27___spec__4(x_74, x_0, x_69, x_61);
x_77 = lean::cnstr_get(x_76, 0);
lean::inc(x_77);
x_79 = lean::cnstr_get(x_76, 1);
lean::inc(x_79);
lean::dec(x_76);
x_82 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_71, x_77);
if (lean::is_scalar(x_63)) {
 x_83 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_83 = x_63;
}
lean::cnstr_set(x_83, 0, x_82);
lean::cnstr_set(x_83, 1, x_79);
return x_83;
}
else
{
obj* x_85; uint8 x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; 
lean::dec(x_0);
x_85 = lean::cnstr_get(x_66, 0);
lean::inc(x_85);
x_87 = lean::cnstr_get_scalar<uint8>(x_66, sizeof(void*)*1);
if (lean::is_shared(x_66)) {
 lean::dec(x_66);
 x_88 = lean::box(0);
} else {
 lean::cnstr_release(x_66, 0);
 x_88 = x_66;
}
if (lean::is_scalar(x_88)) {
 x_89 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_89 = x_88;
}
lean::cnstr_set(x_89, 0, x_85);
lean::cnstr_set_scalar(x_89, sizeof(void*)*1, x_87);
x_90 = x_89;
if (lean::is_scalar(x_63)) {
 x_91 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_91 = x_63;
}
lean::cnstr_set(x_91, 0, x_90);
lean::cnstr_set(x_91, 1, x_61);
return x_91;
}
}
else
{
obj* x_93; obj* x_94; obj* x_95; obj* x_97; obj* x_99; obj* x_100; obj* x_101; obj* x_102; 
lean::inc(x_1);
x_93 = lean::string_iterator_next(x_1);
x_94 = l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_number_x_27___spec__6(x_1, x_0, x_93, x_2);
x_95 = lean::cnstr_get(x_94, 0);
lean::inc(x_95);
x_97 = lean::cnstr_get(x_94, 1);
lean::inc(x_97);
if (lean::is_shared(x_94)) {
 lean::dec(x_94);
 x_99 = lean::box(0);
} else {
 lean::cnstr_release(x_94, 0);
 lean::cnstr_release(x_94, 1);
 x_99 = x_94;
}
x_100 = lean::box(0);
x_101 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_100, x_95);
if (lean::is_scalar(x_99)) {
 x_102 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_102 = x_99;
}
lean::cnstr_set(x_102, 0, x_101);
lean::cnstr_set(x_102, 1, x_97);
return x_102;
}
}
}
}
obj* l_list_map___main___at_lean_parser_number_x_27___spec__9___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_12; 
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
x_9 = lean::apply_3(x_6, x_1, x_2, x_3);
x_10 = lean::cnstr_get(x_9, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_9, 1);
lean::inc(x_12);
lean::dec(x_9);
if (lean::obj_tag(x_10) == 0)
{
obj* x_15; obj* x_17; obj* x_19; obj* x_21; obj* x_22; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_29; obj* x_30; obj* x_31; 
x_15 = lean::cnstr_get(x_10, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_10, 1);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_10, 2);
lean::inc(x_19);
if (lean::is_shared(x_10)) {
 lean::dec(x_10);
 x_21 = lean::box(0);
} else {
 lean::cnstr_release(x_10, 0);
 lean::cnstr_release(x_10, 1);
 lean::cnstr_release(x_10, 2);
 x_21 = x_10;
}
x_22 = lean::box(0);
lean::inc(x_22);
x_24 = lean_name_mk_numeral(x_22, x_4);
x_25 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_25, 0, x_15);
lean::cnstr_set(x_25, 1, x_22);
x_26 = l_lean_parser_syntax_mk__node(x_24, x_25);
x_27 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_27);
if (lean::is_scalar(x_21)) {
 x_29 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_29 = x_21;
}
lean::cnstr_set(x_29, 0, x_26);
lean::cnstr_set(x_29, 1, x_17);
lean::cnstr_set(x_29, 2, x_27);
x_30 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_19, x_29);
if (lean::is_scalar(x_8)) {
 x_31 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_31 = x_8;
}
lean::cnstr_set(x_31, 0, x_30);
lean::cnstr_set(x_31, 1, x_12);
return x_31;
}
else
{
obj* x_33; uint8 x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; 
lean::dec(x_4);
x_33 = lean::cnstr_get(x_10, 0);
lean::inc(x_33);
x_35 = lean::cnstr_get_scalar<uint8>(x_10, sizeof(void*)*1);
if (lean::is_shared(x_10)) {
 lean::dec(x_10);
 x_36 = lean::box(0);
} else {
 lean::cnstr_release(x_10, 0);
 x_36 = x_10;
}
if (lean::is_scalar(x_36)) {
 x_37 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_37 = x_36;
}
lean::cnstr_set(x_37, 0, x_33);
lean::cnstr_set_scalar(x_37, sizeof(void*)*1, x_35);
x_38 = x_37;
if (lean::is_scalar(x_8)) {
 x_39 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_39 = x_8;
}
lean::cnstr_set(x_39, 0, x_38);
lean::cnstr_set(x_39, 1, x_12);
return x_39;
}
}
}
obj* l_list_map___main___at_lean_parser_number_x_27___spec__9(obj* x_0) {
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
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_list_map___main___at_lean_parser_number_x_27___spec__9___lambda__1), 4, 1);
lean::closure_set(x_8, 0, x_3);
x_9 = l_list_map___main___at_lean_parser_number_x_27___spec__9(x_5);
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
obj* l_lean_parser_parsec__t_lookahead___at_lean_parser_number_x_27___spec__11(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_9; obj* x_10; obj* x_13; obj* x_14; obj* x_16; 
lean::inc(x_4);
x_13 = lean::apply_3(x_1, x_3, x_4, x_5);
x_14 = lean::cnstr_get(x_13, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_13, 1);
lean::inc(x_16);
lean::dec(x_13);
if (lean::obj_tag(x_14) == 0)
{
obj* x_19; obj* x_21; obj* x_23; obj* x_25; obj* x_26; 
x_19 = lean::cnstr_get(x_14, 0);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_14, 1);
lean::inc(x_21);
x_23 = lean::cnstr_get(x_14, 2);
lean::inc(x_23);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_25 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 lean::cnstr_release(x_14, 1);
 lean::cnstr_release(x_14, 2);
 x_25 = x_14;
}
if (lean::obj_tag(x_2) == 0)
{
obj* x_28; obj* x_30; obj* x_32; 
x_28 = lean::cnstr_get(x_2, 0);
lean::inc(x_28);
x_30 = lean::cnstr_get(x_2, 1);
lean::inc(x_30);
x_32 = lean::cnstr_get(x_2, 2);
lean::inc(x_32);
if (lean::obj_tag(x_32) == 0)
{
obj* x_35; obj* x_36; uint8 x_38; 
lean::dec(x_25);
x_35 = lean::string_iterator_offset(x_21);
x_36 = lean::string_iterator_offset(x_30);
lean::dec(x_30);
x_38 = lean::nat_dec_lt(x_35, x_36);
if (x_38 == 0)
{
uint8 x_39; 
x_39 = lean::nat_dec_lt(x_36, x_35);
lean::dec(x_35);
lean::dec(x_36);
if (x_39 == 0)
{
obj* x_42; obj* x_44; obj* x_45; obj* x_47; obj* x_48; 
x_42 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_42, 0, x_19);
lean::cnstr_set(x_42, 1, x_28);
lean::inc(x_21);
x_44 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_44, 0, x_42);
lean::cnstr_set(x_44, 1, x_21);
lean::cnstr_set(x_44, 2, x_32);
x_45 = l_lean_parser_finish__comment__block___closed__2;
lean::inc(x_45);
x_47 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_47, 0, x_44);
lean::cnstr_set(x_47, 1, x_21);
lean::cnstr_set(x_47, 2, x_45);
x_48 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_23, x_47);
x_9 = x_48;
x_10 = x_16;
goto lbl_11;
}
else
{
obj* x_50; obj* x_51; obj* x_53; obj* x_54; obj* x_56; obj* x_57; 
lean::dec(x_28);
x_50 = lean::box(0);
x_51 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_51, 0, x_19);
lean::cnstr_set(x_51, 1, x_50);
lean::inc(x_21);
x_53 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_53, 0, x_51);
lean::cnstr_set(x_53, 1, x_21);
lean::cnstr_set(x_53, 2, x_32);
x_54 = l_lean_parser_finish__comment__block___closed__2;
lean::inc(x_54);
x_56 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_56, 0, x_53);
lean::cnstr_set(x_56, 1, x_21);
lean::cnstr_set(x_56, 2, x_54);
x_57 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_23, x_56);
x_9 = x_57;
x_10 = x_16;
goto lbl_11;
}
}
else
{
obj* x_63; obj* x_66; obj* x_67; 
lean::dec(x_19);
lean::dec(x_36);
lean::dec(x_28);
lean::dec(x_32);
lean::dec(x_35);
x_63 = l_lean_parser_finish__comment__block___closed__2;
lean::inc(x_63);
lean::inc(x_2);
x_66 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_66, 0, x_2);
lean::cnstr_set(x_66, 1, x_21);
lean::cnstr_set(x_66, 2, x_63);
x_67 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_23, x_66);
x_9 = x_67;
x_10 = x_16;
goto lbl_11;
}
}
else
{
obj* x_71; 
lean::dec(x_28);
lean::dec(x_30);
lean::dec(x_32);
x_71 = lean::box(0);
x_26 = x_71;
goto lbl_27;
}
}
else
{
obj* x_72; 
x_72 = lean::box(0);
x_26 = x_72;
goto lbl_27;
}
lbl_27:
{
obj* x_74; obj* x_76; obj* x_78; obj* x_79; obj* x_81; obj* x_82; 
lean::dec(x_26);
x_74 = lean::box(0);
lean::inc(x_74);
x_76 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_76, 0, x_19);
lean::cnstr_set(x_76, 1, x_74);
lean::inc(x_21);
if (lean::is_scalar(x_25)) {
 x_78 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_78 = x_25;
}
lean::cnstr_set(x_78, 0, x_76);
lean::cnstr_set(x_78, 1, x_21);
lean::cnstr_set(x_78, 2, x_74);
x_79 = l_lean_parser_finish__comment__block___closed__2;
lean::inc(x_79);
x_81 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_81, 0, x_78);
lean::cnstr_set(x_81, 1, x_21);
lean::cnstr_set(x_81, 2, x_79);
x_82 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_23, x_81);
x_9 = x_82;
x_10 = x_16;
goto lbl_11;
}
}
else
{
obj* x_83; uint8 x_85; obj* x_86; obj* x_87; obj* x_88; 
x_83 = lean::cnstr_get(x_14, 0);
lean::inc(x_83);
x_85 = lean::cnstr_get_scalar<uint8>(x_14, sizeof(void*)*1);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_86 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 x_86 = x_14;
}
if (lean::is_scalar(x_86)) {
 x_87 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_87 = x_86;
}
lean::cnstr_set(x_87, 0, x_83);
lean::cnstr_set_scalar(x_87, sizeof(void*)*1, x_85);
x_88 = x_87;
x_9 = x_88;
x_10 = x_16;
goto lbl_11;
}
lbl_8:
{
if (lean::obj_tag(x_6) == 0)
{
obj* x_89; obj* x_91; obj* x_92; obj* x_94; obj* x_95; 
x_89 = lean::cnstr_get(x_6, 0);
lean::inc(x_89);
if (lean::is_shared(x_6)) {
 lean::dec(x_6);
 x_91 = lean::box(0);
} else {
 lean::cnstr_release(x_6, 0);
 lean::cnstr_release(x_6, 1);
 lean::cnstr_release(x_6, 2);
 x_91 = x_6;
}
x_92 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_92);
if (lean::is_scalar(x_91)) {
 x_94 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_94 = x_91;
}
lean::cnstr_set(x_94, 0, x_89);
lean::cnstr_set(x_94, 1, x_4);
lean::cnstr_set(x_94, 2, x_92);
x_95 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_95, 0, x_94);
lean::cnstr_set(x_95, 1, x_7);
return x_95;
}
else
{
obj* x_97; 
lean::dec(x_4);
x_97 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_97, 0, x_6);
lean::cnstr_set(x_97, 1, x_7);
return x_97;
}
}
lbl_11:
{
if (lean::obj_tag(x_9) == 0)
{
lean::dec(x_0);
lean::dec(x_2);
x_6 = x_9;
x_7 = x_10;
goto lbl_8;
}
else
{
obj* x_100; obj* x_102; obj* x_103; 
x_100 = lean::cnstr_get(x_9, 0);
lean::inc(x_100);
if (lean::is_shared(x_9)) {
 lean::dec(x_9);
 x_102 = lean::box(0);
} else {
 lean::cnstr_release(x_9, 0);
 x_102 = x_9;
}
x_103 = lean::cnstr_get(x_100, 0);
lean::inc(x_103);
if (lean::obj_tag(x_2) == 0)
{
obj* x_108; obj* x_110; 
lean::dec(x_0);
lean::dec(x_102);
lean::dec(x_100);
x_108 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_108);
x_110 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_110, 0, x_2);
lean::cnstr_set(x_110, 1, x_103);
lean::cnstr_set(x_110, 2, x_108);
x_6 = x_110;
x_7 = x_10;
goto lbl_8;
}
else
{
obj* x_111; obj* x_113; obj* x_114; obj* x_116; uint8 x_118; 
x_111 = lean::cnstr_get(x_2, 0);
lean::inc(x_111);
x_113 = lean::string_iterator_offset(x_103);
x_114 = lean::cnstr_get(x_111, 0);
lean::inc(x_114);
x_116 = lean::string_iterator_offset(x_114);
lean::dec(x_114);
x_118 = lean::nat_dec_lt(x_113, x_116);
if (x_118 == 0)
{
uint8 x_120; 
lean::dec(x_2);
x_120 = lean::nat_dec_lt(x_116, x_113);
lean::dec(x_116);
if (x_120 == 0)
{
obj* x_122; obj* x_123; uint8 x_125; 
x_122 = l_lean_parser_parsec__t_merge___rarg(x_100, x_111);
x_123 = lean::string_iterator_offset(x_0);
lean::dec(x_0);
x_125 = lean::nat_dec_lt(x_123, x_113);
lean::dec(x_113);
lean::dec(x_123);
if (x_125 == 0)
{
uint8 x_128; obj* x_129; obj* x_130; obj* x_131; obj* x_133; 
x_128 = 0;
if (lean::is_scalar(x_102)) {
 x_129 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_129 = x_102;
}
lean::cnstr_set(x_129, 0, x_122);
lean::cnstr_set_scalar(x_129, sizeof(void*)*1, x_128);
x_130 = x_129;
x_131 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_131);
x_133 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_133, 0, x_130);
lean::cnstr_set(x_133, 1, x_103);
lean::cnstr_set(x_133, 2, x_131);
x_6 = x_133;
x_7 = x_10;
goto lbl_8;
}
else
{
uint8 x_134; obj* x_135; obj* x_136; obj* x_137; obj* x_139; 
x_134 = 1;
if (lean::is_scalar(x_102)) {
 x_135 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_135 = x_102;
}
lean::cnstr_set(x_135, 0, x_122);
lean::cnstr_set_scalar(x_135, sizeof(void*)*1, x_134);
x_136 = x_135;
x_137 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_137);
x_139 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_139, 0, x_136);
lean::cnstr_set(x_139, 1, x_103);
lean::cnstr_set(x_139, 2, x_137);
x_6 = x_139;
x_7 = x_10;
goto lbl_8;
}
}
else
{
uint8 x_143; obj* x_144; obj* x_145; obj* x_146; obj* x_148; 
lean::dec(x_0);
lean::dec(x_113);
lean::dec(x_111);
x_143 = 1;
if (lean::is_scalar(x_102)) {
 x_144 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_144 = x_102;
}
lean::cnstr_set(x_144, 0, x_100);
lean::cnstr_set_scalar(x_144, sizeof(void*)*1, x_143);
x_145 = x_144;
x_146 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_146);
x_148 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_148, 0, x_145);
lean::cnstr_set(x_148, 1, x_103);
lean::cnstr_set(x_148, 2, x_146);
x_6 = x_148;
x_7 = x_10;
goto lbl_8;
}
}
else
{
obj* x_155; obj* x_157; 
lean::dec(x_0);
lean::dec(x_116);
lean::dec(x_102);
lean::dec(x_100);
lean::dec(x_113);
lean::dec(x_111);
x_155 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_155);
x_157 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_157, 0, x_2);
lean::cnstr_set(x_157, 1, x_103);
lean::cnstr_set(x_157, 2, x_155);
x_6 = x_157;
x_7 = x_10;
goto lbl_8;
}
}
}
}
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_number_x_27___spec__12___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; uint8 x_7; obj* x_8; obj* x_9; 
x_5 = l_option_get__or__else___main___rarg(x_2, x_4);
x_6 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_0);
lean::cnstr_set(x_6, 2, x_1);
lean::cnstr_set(x_6, 3, x_3);
x_7 = 0;
x_8 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set_scalar(x_8, sizeof(void*)*1, x_7);
x_9 = x_8;
return x_9;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_number_x_27___spec__12(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___at_lean_parser_number_x_27___spec__12___rarg), 5, 0);
return x_2;
}
}
obj* l_list_mfoldr___main___at_lean_parser_number_x_27___spec__13(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_13; obj* x_14; obj* x_16; obj* x_17; 
lean::dec(x_1);
lean::dec(x_2);
x_7 = lean::box(0);
x_8 = l_list_mfoldr___main___at_lean_parser_monad__parsec_longest__match___spec__2___rarg___closed__1;
x_9 = l_mjoin___rarg___closed__1;
lean::inc(x_7);
lean::inc(x_9);
lean::inc(x_8);
x_13 = l_lean_parser_monad__parsec_error___at_lean_parser_number_x_27___spec__12___rarg(x_8, x_9, x_7, x_7, x_0);
x_14 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_14);
x_16 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_16, 0, x_13);
lean::cnstr_set(x_16, 1, x_3);
lean::cnstr_set(x_16, 2, x_14);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_4);
return x_17;
}
else
{
obj* x_18; obj* x_20; obj* x_25; obj* x_26; obj* x_28; obj* x_30; 
x_18 = lean::cnstr_get(x_1, 0);
lean::inc(x_18);
x_20 = lean::cnstr_get(x_1, 1);
lean::inc(x_20);
lean::dec(x_1);
lean::inc(x_2);
lean::inc(x_0);
x_25 = l_list_mfoldr___main___at_lean_parser_number_x_27___spec__13(x_0, x_20, x_2, x_3, x_4);
x_26 = lean::cnstr_get(x_25, 0);
lean::inc(x_26);
x_28 = lean::cnstr_get(x_25, 1);
lean::inc(x_28);
if (lean::is_shared(x_25)) {
 lean::dec(x_25);
 x_30 = lean::box(0);
} else {
 lean::cnstr_release(x_25, 0);
 lean::cnstr_release(x_25, 1);
 x_30 = x_25;
}
if (lean::obj_tag(x_26) == 0)
{
obj* x_31; obj* x_33; obj* x_35; obj* x_38; obj* x_39; obj* x_41; obj* x_44; obj* x_45; 
x_31 = lean::cnstr_get(x_26, 0);
lean::inc(x_31);
x_33 = lean::cnstr_get(x_26, 1);
lean::inc(x_33);
x_35 = lean::cnstr_get(x_26, 2);
lean::inc(x_35);
lean::dec(x_26);
x_38 = l_lean_parser_parsec__t_lookahead___at_lean_parser_number_x_27___spec__11(x_0, x_18, x_31, x_2, x_33, x_28);
x_39 = lean::cnstr_get(x_38, 0);
lean::inc(x_39);
x_41 = lean::cnstr_get(x_38, 1);
lean::inc(x_41);
lean::dec(x_38);
x_44 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_35, x_39);
if (lean::is_scalar(x_30)) {
 x_45 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_45 = x_30;
}
lean::cnstr_set(x_45, 0, x_44);
lean::cnstr_set(x_45, 1, x_41);
return x_45;
}
else
{
obj* x_49; uint8 x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; 
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_18);
x_49 = lean::cnstr_get(x_26, 0);
lean::inc(x_49);
x_51 = lean::cnstr_get_scalar<uint8>(x_26, sizeof(void*)*1);
if (lean::is_shared(x_26)) {
 lean::dec(x_26);
 x_52 = lean::box(0);
} else {
 lean::cnstr_release(x_26, 0);
 x_52 = x_26;
}
if (lean::is_scalar(x_52)) {
 x_53 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_53 = x_52;
}
lean::cnstr_set(x_53, 0, x_49);
lean::cnstr_set_scalar(x_53, sizeof(void*)*1, x_51);
x_54 = x_53;
if (lean::is_scalar(x_30)) {
 x_55 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_55 = x_30;
}
lean::cnstr_set(x_55, 0, x_54);
lean::cnstr_set(x_55, 1, x_28);
return x_55;
}
}
}
}
obj* l_lean_parser_monad__parsec_longest__match___at_lean_parser_number_x_27___spec__10(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_8; obj* x_9; obj* x_11; obj* x_13; 
x_4 = lean::mk_nat_obj(0u);
x_5 = l_list_enum__from___main___rarg(x_4, x_0);
x_6 = l_list_map___main___at_lean_parser_number_x_27___spec__9(x_5);
lean::inc(x_2);
x_8 = l_list_mfoldr___main___at_lean_parser_number_x_27___spec__13(x_2, x_6, x_1, x_2, x_3);
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
if (lean::is_shared(x_8)) {
 lean::dec(x_8);
 x_13 = lean::box(0);
} else {
 lean::cnstr_release(x_8, 0);
 lean::cnstr_release(x_8, 1);
 x_13 = x_8;
}
if (lean::obj_tag(x_9) == 0)
{
obj* x_14; obj* x_16; obj* x_19; obj* x_20; obj* x_22; obj* x_23; 
x_14 = lean::cnstr_get(x_9, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_9, 2);
lean::inc(x_16);
lean::dec(x_9);
x_19 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_14);
x_20 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_20);
x_22 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_20, x_19);
if (lean::is_scalar(x_13)) {
 x_23 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_23 = x_13;
}
lean::cnstr_set(x_23, 0, x_22);
lean::cnstr_set(x_23, 1, x_11);
return x_23;
}
else
{
obj* x_24; uint8 x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_32; obj* x_33; 
x_24 = lean::cnstr_get(x_9, 0);
lean::inc(x_24);
x_26 = lean::cnstr_get_scalar<uint8>(x_9, sizeof(void*)*1);
if (lean::is_shared(x_9)) {
 lean::dec(x_9);
 x_27 = lean::box(0);
} else {
 lean::cnstr_release(x_9, 0);
 x_27 = x_9;
}
if (lean::is_scalar(x_27)) {
 x_28 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_28 = x_27;
}
lean::cnstr_set(x_28, 0, x_24);
lean::cnstr_set_scalar(x_28, sizeof(void*)*1, x_26);
x_29 = x_28;
x_30 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_30);
x_32 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_30, x_29);
if (lean::is_scalar(x_13)) {
 x_33 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_33 = x_13;
}
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_11);
return x_33;
}
}
}
obj* l_lean_parser_combinators_longest__choice___at_lean_parser_number_x_27___spec__8(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; obj* x_6; obj* x_8; obj* x_10; 
lean::inc(x_1);
x_5 = l_lean_parser_monad__parsec_longest__match___at_lean_parser_number_x_27___spec__10(x_0, x_1, x_2, x_3);
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
obj* x_11; obj* x_13; obj* x_15; obj* x_17; 
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
if (lean::obj_tag(x_11) == 0)
{
obj* x_20; obj* x_21; obj* x_22; obj* x_26; obj* x_27; obj* x_29; obj* x_32; obj* x_33; 
lean::dec(x_17);
lean::dec(x_11);
x_20 = lean::box(0);
x_21 = l___private_init_lean_parser_combinators_1__many1__aux___main___rarg___closed__1;
x_22 = l_mjoin___rarg___closed__1;
lean::inc(x_20);
lean::inc(x_22);
lean::inc(x_21);
x_26 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_21, x_22, x_20, x_20, x_1, x_13, x_8);
x_27 = lean::cnstr_get(x_26, 0);
lean::inc(x_27);
x_29 = lean::cnstr_get(x_26, 1);
lean::inc(x_29);
lean::dec(x_26);
x_32 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_27);
if (lean::is_scalar(x_10)) {
 x_33 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_33 = x_10;
}
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_29);
return x_33;
}
else
{
obj* x_35; obj* x_38; obj* x_40; obj* x_41; obj* x_42; 
lean::dec(x_1);
x_35 = lean::cnstr_get(x_11, 0);
lean::inc(x_35);
lean::dec(x_11);
x_38 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_38);
if (lean::is_scalar(x_17)) {
 x_40 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_40 = x_17;
}
lean::cnstr_set(x_40, 0, x_35);
lean::cnstr_set(x_40, 1, x_13);
lean::cnstr_set(x_40, 2, x_38);
x_41 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_40);
if (lean::is_scalar(x_10)) {
 x_42 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_42 = x_10;
}
lean::cnstr_set(x_42, 0, x_41);
lean::cnstr_set(x_42, 1, x_8);
return x_42;
}
}
else
{
obj* x_44; uint8 x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; 
lean::dec(x_1);
x_44 = lean::cnstr_get(x_6, 0);
lean::inc(x_44);
x_46 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*1);
if (lean::is_shared(x_6)) {
 lean::dec(x_6);
 x_47 = lean::box(0);
} else {
 lean::cnstr_release(x_6, 0);
 x_47 = x_6;
}
if (lean::is_scalar(x_47)) {
 x_48 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_48 = x_47;
}
lean::cnstr_set(x_48, 0, x_44);
lean::cnstr_set_scalar(x_48, sizeof(void*)*1, x_46);
x_49 = x_48;
if (lean::is_scalar(x_10)) {
 x_50 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_50 = x_10;
}
lean::cnstr_set(x_50, 0, x_49);
lean::cnstr_set(x_50, 1, x_8);
return x_50;
}
}
}
obj* l_lean_parser_number_x_27___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_7; obj* x_9; 
x_4 = l_lean_parser_monad__parsec_take__while1___at_lean_parser_number_x_27___spec__1(x_1, x_2, x_3);
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
obj* x_10; obj* x_12; obj* x_14; obj* x_16; obj* x_17; obj* x_19; obj* x_20; obj* x_21; 
x_10 = lean::cnstr_get(x_5, 1);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_5, 2);
lean::inc(x_12);
if (lean::is_shared(x_5)) {
 lean::dec(x_5);
 x_14 = lean::box(0);
} else {
 lean::cnstr_release(x_5, 0);
 lean::cnstr_release(x_5, 1);
 lean::cnstr_release(x_5, 2);
 x_14 = x_5;
}
lean::inc(x_10);
x_16 = l_lean_parser_mk__raw__res(x_0, x_10);
x_17 = l_lean_parser_finish__comment__block___closed__2;
lean::inc(x_17);
if (lean::is_scalar(x_14)) {
 x_19 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_19 = x_14;
}
lean::cnstr_set(x_19, 0, x_16);
lean::cnstr_set(x_19, 1, x_10);
lean::cnstr_set(x_19, 2, x_17);
x_20 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_12, x_19);
if (lean::is_scalar(x_9)) {
 x_21 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_21 = x_9;
}
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_7);
return x_21;
}
else
{
obj* x_23; uint8 x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
lean::dec(x_0);
x_23 = lean::cnstr_get(x_5, 0);
lean::inc(x_23);
x_25 = lean::cnstr_get_scalar<uint8>(x_5, sizeof(void*)*1);
if (lean::is_shared(x_5)) {
 lean::dec(x_5);
 x_26 = lean::box(0);
} else {
 lean::cnstr_release(x_5, 0);
 x_26 = x_5;
}
if (lean::is_scalar(x_26)) {
 x_27 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_27 = x_26;
}
lean::cnstr_set(x_27, 0, x_23);
lean::cnstr_set_scalar(x_27, sizeof(void*)*1, x_25);
x_28 = x_27;
if (lean::is_scalar(x_9)) {
 x_29 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_29 = x_9;
}
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_7);
return x_29;
}
}
}
obj* l_lean_parser_number_x_27___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_7; obj* x_9; 
x_4 = l_lean_parser_parse__bin__lit(x_1, x_2, x_3);
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
obj* x_10; obj* x_12; obj* x_14; obj* x_16; obj* x_17; obj* x_19; obj* x_20; obj* x_21; 
x_10 = lean::cnstr_get(x_5, 1);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_5, 2);
lean::inc(x_12);
if (lean::is_shared(x_5)) {
 lean::dec(x_5);
 x_14 = lean::box(0);
} else {
 lean::cnstr_release(x_5, 0);
 lean::cnstr_release(x_5, 1);
 lean::cnstr_release(x_5, 2);
 x_14 = x_5;
}
lean::inc(x_10);
x_16 = l_lean_parser_mk__raw__res(x_0, x_10);
x_17 = l_lean_parser_finish__comment__block___closed__2;
lean::inc(x_17);
if (lean::is_scalar(x_14)) {
 x_19 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_19 = x_14;
}
lean::cnstr_set(x_19, 0, x_16);
lean::cnstr_set(x_19, 1, x_10);
lean::cnstr_set(x_19, 2, x_17);
x_20 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_12, x_19);
if (lean::is_scalar(x_9)) {
 x_21 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_21 = x_9;
}
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_7);
return x_21;
}
else
{
obj* x_23; uint8 x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
lean::dec(x_0);
x_23 = lean::cnstr_get(x_5, 0);
lean::inc(x_23);
x_25 = lean::cnstr_get_scalar<uint8>(x_5, sizeof(void*)*1);
if (lean::is_shared(x_5)) {
 lean::dec(x_5);
 x_26 = lean::box(0);
} else {
 lean::cnstr_release(x_5, 0);
 x_26 = x_5;
}
if (lean::is_scalar(x_26)) {
 x_27 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_27 = x_26;
}
lean::cnstr_set(x_27, 0, x_23);
lean::cnstr_set_scalar(x_27, sizeof(void*)*1, x_25);
x_28 = x_27;
if (lean::is_scalar(x_9)) {
 x_29 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_29 = x_9;
}
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_7);
return x_29;
}
}
}
obj* l_lean_parser_number_x_27___lambda__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_7; obj* x_9; 
x_4 = l_lean_parser_parse__oct__lit(x_1, x_2, x_3);
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
obj* x_10; obj* x_12; obj* x_14; obj* x_16; obj* x_17; obj* x_19; obj* x_20; obj* x_21; 
x_10 = lean::cnstr_get(x_5, 1);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_5, 2);
lean::inc(x_12);
if (lean::is_shared(x_5)) {
 lean::dec(x_5);
 x_14 = lean::box(0);
} else {
 lean::cnstr_release(x_5, 0);
 lean::cnstr_release(x_5, 1);
 lean::cnstr_release(x_5, 2);
 x_14 = x_5;
}
lean::inc(x_10);
x_16 = l_lean_parser_mk__raw__res(x_0, x_10);
x_17 = l_lean_parser_finish__comment__block___closed__2;
lean::inc(x_17);
if (lean::is_scalar(x_14)) {
 x_19 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_19 = x_14;
}
lean::cnstr_set(x_19, 0, x_16);
lean::cnstr_set(x_19, 1, x_10);
lean::cnstr_set(x_19, 2, x_17);
x_20 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_12, x_19);
if (lean::is_scalar(x_9)) {
 x_21 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_21 = x_9;
}
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_7);
return x_21;
}
else
{
obj* x_23; uint8 x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
lean::dec(x_0);
x_23 = lean::cnstr_get(x_5, 0);
lean::inc(x_23);
x_25 = lean::cnstr_get_scalar<uint8>(x_5, sizeof(void*)*1);
if (lean::is_shared(x_5)) {
 lean::dec(x_5);
 x_26 = lean::box(0);
} else {
 lean::cnstr_release(x_5, 0);
 x_26 = x_5;
}
if (lean::is_scalar(x_26)) {
 x_27 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_27 = x_26;
}
lean::cnstr_set(x_27, 0, x_23);
lean::cnstr_set_scalar(x_27, sizeof(void*)*1, x_25);
x_28 = x_27;
if (lean::is_scalar(x_9)) {
 x_29 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_29 = x_9;
}
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_7);
return x_29;
}
}
}
obj* l_lean_parser_number_x_27___lambda__4(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_7; obj* x_9; 
x_4 = l_lean_parser_parse__hex__lit(x_1, x_2, x_3);
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
obj* x_10; obj* x_12; obj* x_14; obj* x_16; obj* x_17; obj* x_19; obj* x_20; obj* x_21; 
x_10 = lean::cnstr_get(x_5, 1);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_5, 2);
lean::inc(x_12);
if (lean::is_shared(x_5)) {
 lean::dec(x_5);
 x_14 = lean::box(0);
} else {
 lean::cnstr_release(x_5, 0);
 lean::cnstr_release(x_5, 1);
 lean::cnstr_release(x_5, 2);
 x_14 = x_5;
}
lean::inc(x_10);
x_16 = l_lean_parser_mk__raw__res(x_0, x_10);
x_17 = l_lean_parser_finish__comment__block___closed__2;
lean::inc(x_17);
if (lean::is_scalar(x_14)) {
 x_19 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_19 = x_14;
}
lean::cnstr_set(x_19, 0, x_16);
lean::cnstr_set(x_19, 1, x_10);
lean::cnstr_set(x_19, 2, x_17);
x_20 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_12, x_19);
if (lean::is_scalar(x_9)) {
 x_21 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_21 = x_9;
}
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_7);
return x_21;
}
else
{
obj* x_23; uint8 x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
lean::dec(x_0);
x_23 = lean::cnstr_get(x_5, 0);
lean::inc(x_23);
x_25 = lean::cnstr_get_scalar<uint8>(x_5, sizeof(void*)*1);
if (lean::is_shared(x_5)) {
 lean::dec(x_5);
 x_26 = lean::box(0);
} else {
 lean::cnstr_release(x_5, 0);
 x_26 = x_5;
}
if (lean::is_scalar(x_26)) {
 x_27 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_27 = x_26;
}
lean::cnstr_set(x_27, 0, x_23);
lean::cnstr_set_scalar(x_27, sizeof(void*)*1, x_25);
x_28 = x_27;
if (lean::is_scalar(x_9)) {
 x_29 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_29 = x_9;
}
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_7);
return x_29;
}
}
}
obj* _init_l_lean_parser_number_x_27___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_4; obj* x_5; obj* x_7; obj* x_8; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_with__trailing___rarg___lambda__1), 2, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_lift___at_lean_parser_with__trailing___spec__1___rarg), 4, 1);
lean::closure_set(x_1, 0, x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_number_x_27___lambda__1), 4, 0);
lean::inc(x_1);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_bind___at_lean_parser_with__trailing___spec__2___rarg), 5, 2);
lean::closure_set(x_4, 0, x_1);
lean::closure_set(x_4, 1, x_2);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_number_x_27___lambda__2), 4, 0);
lean::inc(x_1);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_bind___at_lean_parser_with__trailing___spec__2___rarg), 5, 2);
lean::closure_set(x_7, 0, x_1);
lean::closure_set(x_7, 1, x_5);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_number_x_27___lambda__3), 4, 0);
lean::inc(x_1);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_bind___at_lean_parser_with__trailing___spec__2___rarg), 5, 2);
lean::closure_set(x_10, 0, x_1);
lean::closure_set(x_10, 1, x_8);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_number_x_27___lambda__4), 4, 0);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_bind___at_lean_parser_with__trailing___spec__2___rarg), 5, 2);
lean::closure_set(x_12, 0, x_1);
lean::closure_set(x_12, 1, x_11);
x_13 = lean::box(0);
lean::inc(x_13);
x_15 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_15, 0, x_12);
lean::cnstr_set(x_15, 1, x_13);
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_10);
lean::cnstr_set(x_16, 1, x_15);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_7);
lean::cnstr_set(x_17, 1, x_16);
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_4);
lean::cnstr_set(x_18, 1, x_17);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_longest__choice___at_lean_parser_number_x_27___spec__8), 4, 1);
lean::closure_set(x_19, 0, x_18);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_13);
return x_20;
}
}
obj* l_lean_parser_number_x_27(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_7; 
x_3 = l_lean_parser_number;
x_4 = l_lean_parser_number_x_27___closed__1;
lean::inc(x_4);
lean::inc(x_3);
x_7 = l_lean_parser_combinators_node___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__15(x_3, x_4, x_0, x_1, x_2);
return x_7;
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_number_x_27___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint32 x_4; obj* x_5; 
x_4 = lean::unbox_uint32(x_0);
x_5 = l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_number_x_27___spec__2(x_4, x_1, x_2, x_3);
return x_5;
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_number_x_27___spec__4___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint32 x_4; obj* x_5; 
x_4 = lean::unbox_uint32(x_0);
x_5 = l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_number_x_27___spec__4(x_4, x_1, x_2, x_3);
return x_5;
}
}
obj* _init_l_lean_parser_string__lit() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("string_lit");
x_6 = lean_name_mk_string(x_4, x_5);
return x_6;
}
}
obj* l_lean_parser_string__lit_has__view_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_syntax_as__node___main(x_0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; 
lean::dec(x_1);
x_3 = lean::box(0);
return x_3;
}
else
{
obj* x_4; obj* x_6; obj* x_7; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_6 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 x_6 = x_1;
}
x_7 = lean::cnstr_get(x_4, 1);
lean::inc(x_7);
lean::dec(x_4);
if (lean::obj_tag(x_7) == 0)
{
obj* x_12; 
lean::dec(x_7);
lean::dec(x_6);
x_12 = lean::box(0);
return x_12;
}
else
{
obj* x_13; 
x_13 = lean::cnstr_get(x_7, 0);
lean::inc(x_13);
lean::dec(x_7);
switch (lean::obj_tag(x_13)) {
case 0:
{
obj* x_16; obj* x_19; 
x_16 = lean::cnstr_get(x_13, 0);
lean::inc(x_16);
lean::dec(x_13);
if (lean::is_scalar(x_6)) {
 x_19 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_19 = x_6;
}
lean::cnstr_set(x_19, 0, x_16);
return x_19;
}
case 1:
{
obj* x_22; 
lean::dec(x_13);
lean::dec(x_6);
x_22 = lean::box(0);
return x_22;
}
case 2:
{
obj* x_25; 
lean::dec(x_13);
lean::dec(x_6);
x_25 = lean::box(0);
return x_25;
}
default:
{
obj* x_28; 
lean::dec(x_13);
lean::dec(x_6);
x_28 = lean::box(0);
return x_28;
}
}
}
}
}
}
obj* l_lean_parser_string__lit_has__view_x_27___lambda__2(obj* x_0) {
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
x_8 = l_lean_parser_string__lit;
lean::inc(x_8);
x_10 = l_lean_parser_syntax_mk__node(x_8, x_7);
return x_10;
}
}
obj* _init_l_lean_parser_string__lit_has__view_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_string__lit_has__view_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_string__lit_has__view_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_lean_parser_string__lit_has__view() {
_start:
{
obj* x_0; 
x_0 = l_lean_parser_string__lit_has__view_x_27;
lean::inc(x_0);
return x_0;
}
}
obj* l_lean_parser_monad__parsec_digit___at_lean_parser_string__lit_x_27___spec__5(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = lean::string_iterator_has_next(x_1);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; obj* x_10; obj* x_11; obj* x_13; obj* x_15; obj* x_16; obj* x_18; obj* x_19; 
x_4 = lean::box(0);
x_5 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_6 = l_mjoin___rarg___closed__1;
lean::inc(x_4);
lean::inc(x_6);
lean::inc(x_5);
x_10 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_5, x_6, x_4, x_4, x_0, x_1, x_2);
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
x_16 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_16);
x_18 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_11);
if (lean::is_scalar(x_15)) {
 x_19 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_19 = x_15;
}
lean::cnstr_set(x_19, 0, x_18);
lean::cnstr_set(x_19, 1, x_13);
return x_19;
}
else
{
uint32 x_20; uint8 x_21; 
x_20 = lean::string_iterator_curr(x_1);
x_21 = l_char_is__digit(x_20);
if (x_21 == 0)
{
obj* x_22; obj* x_23; obj* x_25; obj* x_27; obj* x_28; obj* x_29; obj* x_32; obj* x_33; obj* x_35; obj* x_37; obj* x_38; obj* x_40; obj* x_41; 
x_22 = l_char_quote__core(x_20);
x_23 = l_char_has__repr___closed__1;
lean::inc(x_23);
x_25 = lean::string_append(x_23, x_22);
lean::dec(x_22);
x_27 = lean::string_append(x_25, x_23);
x_28 = lean::box(0);
x_29 = l_mjoin___rarg___closed__1;
lean::inc(x_28);
lean::inc(x_29);
x_32 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_27, x_29, x_28, x_28, x_0, x_1, x_2);
x_33 = lean::cnstr_get(x_32, 0);
lean::inc(x_33);
x_35 = lean::cnstr_get(x_32, 1);
lean::inc(x_35);
if (lean::is_shared(x_32)) {
 lean::dec(x_32);
 x_37 = lean::box(0);
} else {
 lean::cnstr_release(x_32, 0);
 lean::cnstr_release(x_32, 1);
 x_37 = x_32;
}
x_38 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_38);
x_40 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_38, x_33);
if (lean::is_scalar(x_37)) {
 x_41 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_41 = x_37;
}
lean::cnstr_set(x_41, 0, x_40);
lean::cnstr_set(x_41, 1, x_35);
return x_41;
}
else
{
obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; 
lean::dec(x_0);
x_43 = lean::string_iterator_next(x_1);
x_44 = lean::box(0);
x_45 = lean::box_uint32(x_20);
x_46 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_46, 0, x_45);
lean::cnstr_set(x_46, 1, x_43);
lean::cnstr_set(x_46, 2, x_44);
x_47 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_47, 0, x_46);
lean::cnstr_set(x_47, 1, x_2);
return x_47;
}
}
}
}
obj* _init_l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__4___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("hexadecimal");
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__4(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_8; obj* x_9; obj* x_11; 
lean::inc(x_1);
lean::inc(x_0);
x_8 = l_lean_parser_monad__parsec_digit___at_lean_parser_string__lit_x_27___spec__5(x_0, x_1, x_2);
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
lean::dec(x_8);
if (lean::obj_tag(x_9) == 0)
{
obj* x_14; obj* x_16; obj* x_18; obj* x_20; obj* x_21; obj* x_22; obj* x_25; obj* x_27; obj* x_28; 
x_14 = lean::cnstr_get(x_9, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_9, 1);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_9, 2);
lean::inc(x_18);
if (lean::is_shared(x_9)) {
 lean::dec(x_9);
 x_20 = lean::box(0);
} else {
 lean::cnstr_release(x_9, 0);
 lean::cnstr_release(x_9, 1);
 lean::cnstr_release(x_9, 2);
 x_20 = x_9;
}
x_21 = lean::mk_nat_obj(48u);
x_22 = lean::nat_sub(x_14, x_21);
lean::dec(x_21);
lean::dec(x_14);
x_25 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_25);
if (lean::is_scalar(x_20)) {
 x_27 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_27 = x_20;
}
lean::cnstr_set(x_27, 0, x_22);
lean::cnstr_set(x_27, 1, x_16);
lean::cnstr_set(x_27, 2, x_25);
x_28 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_18, x_27);
x_3 = x_28;
x_4 = x_11;
goto lbl_5;
}
else
{
obj* x_29; uint8 x_31; obj* x_32; obj* x_33; obj* x_34; 
x_29 = lean::cnstr_get(x_9, 0);
lean::inc(x_29);
x_31 = lean::cnstr_get_scalar<uint8>(x_9, sizeof(void*)*1);
if (lean::is_shared(x_9)) {
 lean::dec(x_9);
 x_32 = lean::box(0);
} else {
 lean::cnstr_release(x_9, 0);
 x_32 = x_9;
}
if (lean::is_scalar(x_32)) {
 x_33 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_33 = x_32;
}
lean::cnstr_set(x_33, 0, x_29);
lean::cnstr_set_scalar(x_33, sizeof(void*)*1, x_31);
x_34 = x_33;
x_3 = x_34;
x_4 = x_11;
goto lbl_5;
}
lbl_5:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_37; obj* x_39; obj* x_40; 
lean::dec(x_1);
lean::dec(x_0);
x_37 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__4___closed__1;
lean::inc(x_37);
x_39 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_3, x_37);
x_40 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_40, 0, x_39);
lean::cnstr_set(x_40, 1, x_4);
return x_40;
}
else
{
obj* x_41; uint8 x_43; obj* x_44; obj* x_45; obj* x_47; obj* x_48; 
x_41 = lean::cnstr_get(x_3, 0);
lean::inc(x_41);
x_43 = lean::cnstr_get_scalar<uint8>(x_3, sizeof(void*)*1);
if (x_43 == 0)
{
uint8 x_51; 
lean::dec(x_3);
x_51 = lean::string_iterator_has_next(x_1);
if (x_51 == 0)
{
obj* x_52; obj* x_53; obj* x_54; obj* x_60; obj* x_61; obj* x_63; obj* x_66; obj* x_68; 
x_52 = lean::box(0);
x_53 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_54 = l_mjoin___rarg___closed__1;
lean::inc(x_1);
lean::inc(x_0);
lean::inc(x_52);
lean::inc(x_54);
lean::inc(x_53);
x_60 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_53, x_54, x_52, x_52, x_0, x_1, x_4);
x_61 = lean::cnstr_get(x_60, 0);
lean::inc(x_61);
x_63 = lean::cnstr_get(x_60, 1);
lean::inc(x_63);
lean::dec(x_60);
x_66 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_66);
x_68 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_66, x_61);
x_47 = x_68;
x_48 = x_63;
goto lbl_49;
}
else
{
uint32 x_69; uint8 x_70; obj* x_72; obj* x_73; uint8 x_74; 
x_69 = lean::string_iterator_curr(x_1);
x_72 = lean::mk_nat_obj(97u);
x_73 = lean::box_uint32(x_69);
x_74 = lean::nat_dec_le(x_72, x_73);
lean::dec(x_73);
lean::dec(x_72);
if (x_74 == 0)
{
obj* x_77; obj* x_78; obj* x_80; obj* x_82; obj* x_83; obj* x_84; obj* x_89; obj* x_90; obj* x_92; obj* x_95; obj* x_97; 
x_77 = l_char_quote__core(x_69);
x_78 = l_char_has__repr___closed__1;
lean::inc(x_78);
x_80 = lean::string_append(x_78, x_77);
lean::dec(x_77);
x_82 = lean::string_append(x_80, x_78);
x_83 = lean::box(0);
x_84 = l_mjoin___rarg___closed__1;
lean::inc(x_1);
lean::inc(x_0);
lean::inc(x_83);
lean::inc(x_84);
x_89 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_82, x_84, x_83, x_83, x_0, x_1, x_4);
x_90 = lean::cnstr_get(x_89, 0);
lean::inc(x_90);
x_92 = lean::cnstr_get(x_89, 1);
lean::inc(x_92);
lean::dec(x_89);
x_95 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_95);
x_97 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_95, x_90);
x_47 = x_97;
x_48 = x_92;
goto lbl_49;
}
else
{
uint8 x_98; 
x_98 = 1;
x_70 = x_98;
goto lbl_71;
}
lbl_71:
{
obj* x_99; obj* x_100; uint8 x_101; 
x_99 = lean::mk_nat_obj(102u);
x_100 = lean::box_uint32(x_69);
x_101 = lean::nat_dec_le(x_100, x_99);
lean::dec(x_99);
if (x_101 == 0)
{
obj* x_104; obj* x_105; obj* x_107; obj* x_109; obj* x_110; obj* x_111; obj* x_116; obj* x_117; obj* x_119; obj* x_122; obj* x_124; 
lean::dec(x_100);
x_104 = l_char_quote__core(x_69);
x_105 = l_char_has__repr___closed__1;
lean::inc(x_105);
x_107 = lean::string_append(x_105, x_104);
lean::dec(x_104);
x_109 = lean::string_append(x_107, x_105);
x_110 = lean::box(0);
x_111 = l_mjoin___rarg___closed__1;
lean::inc(x_1);
lean::inc(x_0);
lean::inc(x_110);
lean::inc(x_111);
x_116 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_109, x_111, x_110, x_110, x_0, x_1, x_4);
x_117 = lean::cnstr_get(x_116, 0);
lean::inc(x_117);
x_119 = lean::cnstr_get(x_116, 1);
lean::inc(x_119);
lean::dec(x_116);
x_122 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_122);
x_124 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_122, x_117);
x_47 = x_124;
x_48 = x_119;
goto lbl_49;
}
else
{
if (x_70 == 0)
{
obj* x_126; obj* x_127; obj* x_129; obj* x_131; obj* x_132; obj* x_133; obj* x_138; obj* x_139; obj* x_141; obj* x_144; obj* x_146; 
lean::dec(x_100);
x_126 = l_char_quote__core(x_69);
x_127 = l_char_has__repr___closed__1;
lean::inc(x_127);
x_129 = lean::string_append(x_127, x_126);
lean::dec(x_126);
x_131 = lean::string_append(x_129, x_127);
x_132 = lean::box(0);
x_133 = l_mjoin___rarg___closed__1;
lean::inc(x_1);
lean::inc(x_0);
lean::inc(x_132);
lean::inc(x_133);
x_138 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_131, x_133, x_132, x_132, x_0, x_1, x_4);
x_139 = lean::cnstr_get(x_138, 0);
lean::inc(x_139);
x_141 = lean::cnstr_get(x_138, 1);
lean::inc(x_141);
lean::dec(x_138);
x_144 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_144);
x_146 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_144, x_139);
x_47 = x_146;
x_48 = x_141;
goto lbl_49;
}
else
{
obj* x_148; obj* x_149; obj* x_150; 
lean::inc(x_1);
x_148 = lean::string_iterator_next(x_1);
x_149 = lean::box(0);
x_150 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_150, 0, x_100);
lean::cnstr_set(x_150, 1, x_148);
lean::cnstr_set(x_150, 2, x_149);
x_47 = x_150;
x_48 = x_4;
goto lbl_49;
}
}
}
}
}
else
{
obj* x_154; obj* x_156; obj* x_157; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_41);
x_154 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__4___closed__1;
lean::inc(x_154);
x_156 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_3, x_154);
x_157 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_157, 0, x_156);
lean::cnstr_set(x_157, 1, x_4);
return x_157;
}
lbl_46:
{
if (lean::obj_tag(x_44) == 0)
{
obj* x_160; obj* x_161; obj* x_163; obj* x_164; 
lean::dec(x_1);
lean::dec(x_0);
x_160 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_41, x_44);
x_161 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__4___closed__1;
lean::inc(x_161);
x_163 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_160, x_161);
x_164 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_164, 0, x_163);
lean::cnstr_set(x_164, 1, x_45);
return x_164;
}
else
{
obj* x_165; uint8 x_167; obj* x_168; obj* x_169; 
x_165 = lean::cnstr_get(x_44, 0);
lean::inc(x_165);
x_167 = lean::cnstr_get_scalar<uint8>(x_44, sizeof(void*)*1);
if (x_167 == 0)
{
uint8 x_172; 
lean::dec(x_44);
x_172 = lean::string_iterator_has_next(x_1);
if (x_172 == 0)
{
obj* x_173; obj* x_174; obj* x_175; obj* x_179; obj* x_180; obj* x_182; obj* x_185; obj* x_187; 
x_173 = lean::box(0);
x_174 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_175 = l_mjoin___rarg___closed__1;
lean::inc(x_173);
lean::inc(x_175);
lean::inc(x_174);
x_179 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_174, x_175, x_173, x_173, x_0, x_1, x_45);
x_180 = lean::cnstr_get(x_179, 0);
lean::inc(x_180);
x_182 = lean::cnstr_get(x_179, 1);
lean::inc(x_182);
lean::dec(x_179);
x_185 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_185);
x_187 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_185, x_180);
x_168 = x_187;
x_169 = x_182;
goto lbl_170;
}
else
{
uint32 x_188; uint8 x_189; obj* x_191; obj* x_192; uint8 x_193; 
x_188 = lean::string_iterator_curr(x_1);
x_191 = lean::mk_nat_obj(65u);
x_192 = lean::box_uint32(x_188);
x_193 = lean::nat_dec_le(x_191, x_192);
lean::dec(x_192);
lean::dec(x_191);
if (x_193 == 0)
{
obj* x_196; obj* x_197; obj* x_199; obj* x_201; obj* x_202; obj* x_203; obj* x_206; obj* x_207; obj* x_209; obj* x_212; obj* x_214; 
x_196 = l_char_quote__core(x_188);
x_197 = l_char_has__repr___closed__1;
lean::inc(x_197);
x_199 = lean::string_append(x_197, x_196);
lean::dec(x_196);
x_201 = lean::string_append(x_199, x_197);
x_202 = lean::box(0);
x_203 = l_mjoin___rarg___closed__1;
lean::inc(x_202);
lean::inc(x_203);
x_206 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_201, x_203, x_202, x_202, x_0, x_1, x_45);
x_207 = lean::cnstr_get(x_206, 0);
lean::inc(x_207);
x_209 = lean::cnstr_get(x_206, 1);
lean::inc(x_209);
lean::dec(x_206);
x_212 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_212);
x_214 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_212, x_207);
x_168 = x_214;
x_169 = x_209;
goto lbl_170;
}
else
{
uint8 x_215; 
x_215 = 1;
x_189 = x_215;
goto lbl_190;
}
lbl_190:
{
obj* x_216; obj* x_217; uint8 x_218; 
x_216 = lean::mk_nat_obj(70u);
x_217 = lean::box_uint32(x_188);
x_218 = lean::nat_dec_le(x_217, x_216);
lean::dec(x_216);
if (x_218 == 0)
{
obj* x_221; obj* x_222; obj* x_224; obj* x_226; obj* x_227; obj* x_228; obj* x_231; obj* x_232; obj* x_234; obj* x_237; obj* x_239; 
lean::dec(x_217);
x_221 = l_char_quote__core(x_188);
x_222 = l_char_has__repr___closed__1;
lean::inc(x_222);
x_224 = lean::string_append(x_222, x_221);
lean::dec(x_221);
x_226 = lean::string_append(x_224, x_222);
x_227 = lean::box(0);
x_228 = l_mjoin___rarg___closed__1;
lean::inc(x_227);
lean::inc(x_228);
x_231 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_226, x_228, x_227, x_227, x_0, x_1, x_45);
x_232 = lean::cnstr_get(x_231, 0);
lean::inc(x_232);
x_234 = lean::cnstr_get(x_231, 1);
lean::inc(x_234);
lean::dec(x_231);
x_237 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_237);
x_239 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_237, x_232);
x_168 = x_239;
x_169 = x_234;
goto lbl_170;
}
else
{
if (x_189 == 0)
{
obj* x_241; obj* x_242; obj* x_244; obj* x_246; obj* x_247; obj* x_248; obj* x_251; obj* x_252; obj* x_254; obj* x_257; obj* x_259; 
lean::dec(x_217);
x_241 = l_char_quote__core(x_188);
x_242 = l_char_has__repr___closed__1;
lean::inc(x_242);
x_244 = lean::string_append(x_242, x_241);
lean::dec(x_241);
x_246 = lean::string_append(x_244, x_242);
x_247 = lean::box(0);
x_248 = l_mjoin___rarg___closed__1;
lean::inc(x_247);
lean::inc(x_248);
x_251 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_246, x_248, x_247, x_247, x_0, x_1, x_45);
x_252 = lean::cnstr_get(x_251, 0);
lean::inc(x_252);
x_254 = lean::cnstr_get(x_251, 1);
lean::inc(x_254);
lean::dec(x_251);
x_257 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_257);
x_259 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_257, x_252);
x_168 = x_259;
x_169 = x_254;
goto lbl_170;
}
else
{
obj* x_261; obj* x_262; obj* x_263; 
lean::dec(x_0);
x_261 = lean::string_iterator_next(x_1);
x_262 = lean::box(0);
x_263 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_263, 0, x_217);
lean::cnstr_set(x_263, 1, x_261);
lean::cnstr_set(x_263, 2, x_262);
x_168 = x_263;
x_169 = x_45;
goto lbl_170;
}
}
}
}
}
else
{
obj* x_267; obj* x_268; obj* x_270; obj* x_271; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_165);
x_267 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_41, x_44);
x_268 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__4___closed__1;
lean::inc(x_268);
x_270 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_267, x_268);
x_271 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_271, 0, x_270);
lean::cnstr_set(x_271, 1, x_45);
return x_271;
}
lbl_170:
{
if (lean::obj_tag(x_168) == 0)
{
obj* x_272; obj* x_274; obj* x_276; obj* x_278; obj* x_279; obj* x_280; obj* x_283; obj* x_284; obj* x_287; obj* x_289; obj* x_290; obj* x_291; obj* x_292; obj* x_293; obj* x_295; obj* x_296; 
x_272 = lean::cnstr_get(x_168, 0);
lean::inc(x_272);
x_274 = lean::cnstr_get(x_168, 1);
lean::inc(x_274);
x_276 = lean::cnstr_get(x_168, 2);
lean::inc(x_276);
if (lean::is_shared(x_168)) {
 lean::dec(x_168);
 x_278 = lean::box(0);
} else {
 lean::cnstr_release(x_168, 0);
 lean::cnstr_release(x_168, 1);
 lean::cnstr_release(x_168, 2);
 x_278 = x_168;
}
x_279 = lean::mk_nat_obj(65u);
x_280 = lean::nat_sub(x_272, x_279);
lean::dec(x_279);
lean::dec(x_272);
x_283 = lean::mk_nat_obj(10u);
x_284 = lean::nat_add(x_283, x_280);
lean::dec(x_280);
lean::dec(x_283);
x_287 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_287);
if (lean::is_scalar(x_278)) {
 x_289 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_289 = x_278;
}
lean::cnstr_set(x_289, 0, x_284);
lean::cnstr_set(x_289, 1, x_274);
lean::cnstr_set(x_289, 2, x_287);
x_290 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_276, x_289);
x_291 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_165, x_290);
x_292 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_41, x_291);
x_293 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__4___closed__1;
lean::inc(x_293);
x_295 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_292, x_293);
x_296 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_296, 0, x_295);
lean::cnstr_set(x_296, 1, x_169);
return x_296;
}
else
{
obj* x_297; uint8 x_299; obj* x_300; obj* x_301; obj* x_302; obj* x_303; obj* x_304; obj* x_305; obj* x_307; obj* x_308; 
x_297 = lean::cnstr_get(x_168, 0);
lean::inc(x_297);
x_299 = lean::cnstr_get_scalar<uint8>(x_168, sizeof(void*)*1);
if (lean::is_shared(x_168)) {
 lean::dec(x_168);
 x_300 = lean::box(0);
} else {
 lean::cnstr_release(x_168, 0);
 x_300 = x_168;
}
if (lean::is_scalar(x_300)) {
 x_301 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_301 = x_300;
}
lean::cnstr_set(x_301, 0, x_297);
lean::cnstr_set_scalar(x_301, sizeof(void*)*1, x_299);
x_302 = x_301;
x_303 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_165, x_302);
x_304 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_41, x_303);
x_305 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__4___closed__1;
lean::inc(x_305);
x_307 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_304, x_305);
x_308 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_308, 0, x_307);
lean::cnstr_set(x_308, 1, x_169);
return x_308;
}
}
}
}
lbl_49:
{
if (lean::obj_tag(x_47) == 0)
{
obj* x_309; obj* x_311; obj* x_313; obj* x_315; obj* x_316; obj* x_317; obj* x_320; obj* x_321; obj* x_324; obj* x_326; obj* x_327; 
x_309 = lean::cnstr_get(x_47, 0);
lean::inc(x_309);
x_311 = lean::cnstr_get(x_47, 1);
lean::inc(x_311);
x_313 = lean::cnstr_get(x_47, 2);
lean::inc(x_313);
if (lean::is_shared(x_47)) {
 lean::dec(x_47);
 x_315 = lean::box(0);
} else {
 lean::cnstr_release(x_47, 0);
 lean::cnstr_release(x_47, 1);
 lean::cnstr_release(x_47, 2);
 x_315 = x_47;
}
x_316 = lean::mk_nat_obj(97u);
x_317 = lean::nat_sub(x_309, x_316);
lean::dec(x_316);
lean::dec(x_309);
x_320 = lean::mk_nat_obj(10u);
x_321 = lean::nat_add(x_320, x_317);
lean::dec(x_317);
lean::dec(x_320);
x_324 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_324);
if (lean::is_scalar(x_315)) {
 x_326 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_326 = x_315;
}
lean::cnstr_set(x_326, 0, x_321);
lean::cnstr_set(x_326, 1, x_311);
lean::cnstr_set(x_326, 2, x_324);
x_327 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_313, x_326);
x_44 = x_327;
x_45 = x_48;
goto lbl_46;
}
else
{
obj* x_328; uint8 x_330; obj* x_331; obj* x_332; obj* x_333; 
x_328 = lean::cnstr_get(x_47, 0);
lean::inc(x_328);
x_330 = lean::cnstr_get_scalar<uint8>(x_47, sizeof(void*)*1);
if (lean::is_shared(x_47)) {
 lean::dec(x_47);
 x_331 = lean::box(0);
} else {
 lean::cnstr_release(x_47, 0);
 x_331 = x_47;
}
if (lean::is_scalar(x_331)) {
 x_332 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_332 = x_331;
}
lean::cnstr_set(x_332, 0, x_328);
lean::cnstr_set_scalar(x_332, sizeof(void*)*1, x_330);
x_333 = x_332;
x_44 = x_333;
x_45 = x_48;
goto lbl_46;
}
}
}
}
}
}
obj* l_lean_parser_monad__parsec_unexpected__at___at_lean_parser_string__lit_x_27___spec__6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; obj* x_9; 
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_1);
x_6 = lean::box(0);
x_7 = l_mjoin___rarg___closed__1;
lean::inc(x_7);
x_9 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_0, x_7, x_5, x_6, x_2, x_3, x_4);
return x_9;
}
}
obj* l_lean_parser_monad__parsec_unexpected__at___at_lean_parser_string__lit_x_27___spec__6(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_unexpected__at___at_lean_parser_string__lit_x_27___spec__6___rarg), 5, 0);
return x_2;
}
}
obj* l_lean_parser_parse__quoted__char___at_lean_parser_string__lit_x_27___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_5; obj* x_6; obj* x_8; obj* x_10; 
lean::inc(x_1);
lean::inc(x_0);
x_5 = l_lean_parser_monad__parsec_any___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__2(x_0, x_1, x_2);
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
obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_18; obj* x_20; obj* x_22; obj* x_24; uint8 x_25; 
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
x_24 = lean::mk_nat_obj(92u);
x_25 = lean::nat_dec_eq(x_11, x_24);
if (x_25 == 0)
{
obj* x_27; uint8 x_28; 
lean::dec(x_24);
x_27 = lean::mk_nat_obj(34u);
x_28 = lean::nat_dec_eq(x_11, x_27);
if (x_28 == 0)
{
obj* x_30; uint8 x_31; 
lean::dec(x_27);
x_30 = lean::mk_nat_obj(39u);
x_31 = lean::nat_dec_eq(x_11, x_30);
if (x_31 == 0)
{
obj* x_33; 
lean::dec(x_30);
x_33 = lean::box(0);
x_22 = x_33;
goto lbl_23;
}
else
{
obj* x_39; obj* x_41; obj* x_42; obj* x_44; obj* x_45; 
lean::dec(x_17);
lean::dec(x_11);
lean::dec(x_1);
lean::dec(x_10);
lean::dec(x_0);
x_39 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_39);
x_41 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_41, 0, x_30);
lean::cnstr_set(x_41, 1, x_13);
lean::cnstr_set(x_41, 2, x_39);
x_42 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_41);
lean::inc(x_39);
x_44 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_39, x_42);
x_45 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_45, 0, x_44);
lean::cnstr_set(x_45, 1, x_8);
return x_45;
}
}
else
{
obj* x_51; obj* x_53; obj* x_54; obj* x_56; obj* x_57; 
lean::dec(x_17);
lean::dec(x_11);
lean::dec(x_1);
lean::dec(x_10);
lean::dec(x_0);
x_51 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_51);
x_53 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_53, 0, x_27);
lean::cnstr_set(x_53, 1, x_13);
lean::cnstr_set(x_53, 2, x_51);
x_54 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_53);
lean::inc(x_51);
x_56 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_51, x_54);
x_57 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_57, 0, x_56);
lean::cnstr_set(x_57, 1, x_8);
return x_57;
}
}
else
{
obj* x_63; obj* x_65; obj* x_66; obj* x_68; obj* x_69; 
lean::dec(x_17);
lean::dec(x_11);
lean::dec(x_1);
lean::dec(x_10);
lean::dec(x_0);
x_63 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_63);
x_65 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_65, 0, x_24);
lean::cnstr_set(x_65, 1, x_13);
lean::cnstr_set(x_65, 2, x_63);
x_66 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_65);
lean::inc(x_63);
x_68 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_63, x_66);
x_69 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_69, 0, x_68);
lean::cnstr_set(x_69, 1, x_8);
return x_69;
}
lbl_19:
{
obj* x_72; obj* x_73; obj* x_75; 
lean::dec(x_18);
lean::inc(x_0);
x_72 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__4(x_0, x_13, x_8);
x_73 = lean::cnstr_get(x_72, 0);
lean::inc(x_73);
x_75 = lean::cnstr_get(x_72, 1);
lean::inc(x_75);
lean::dec(x_72);
if (lean::obj_tag(x_73) == 0)
{
obj* x_78; obj* x_80; obj* x_82; obj* x_86; obj* x_87; obj* x_89; 
x_78 = lean::cnstr_get(x_73, 0);
lean::inc(x_78);
x_80 = lean::cnstr_get(x_73, 1);
lean::inc(x_80);
x_82 = lean::cnstr_get(x_73, 2);
lean::inc(x_82);
lean::dec(x_73);
lean::inc(x_0);
x_86 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__4(x_0, x_80, x_75);
x_87 = lean::cnstr_get(x_86, 0);
lean::inc(x_87);
x_89 = lean::cnstr_get(x_86, 1);
lean::inc(x_89);
lean::dec(x_86);
if (lean::obj_tag(x_87) == 0)
{
obj* x_92; obj* x_94; obj* x_96; obj* x_100; obj* x_101; obj* x_103; 
x_92 = lean::cnstr_get(x_87, 0);
lean::inc(x_92);
x_94 = lean::cnstr_get(x_87, 1);
lean::inc(x_94);
x_96 = lean::cnstr_get(x_87, 2);
lean::inc(x_96);
lean::dec(x_87);
lean::inc(x_0);
x_100 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__4(x_0, x_94, x_89);
x_101 = lean::cnstr_get(x_100, 0);
lean::inc(x_101);
x_103 = lean::cnstr_get(x_100, 1);
lean::inc(x_103);
lean::dec(x_100);
if (lean::obj_tag(x_101) == 0)
{
obj* x_106; obj* x_108; obj* x_110; obj* x_113; obj* x_114; obj* x_116; 
x_106 = lean::cnstr_get(x_101, 0);
lean::inc(x_106);
x_108 = lean::cnstr_get(x_101, 1);
lean::inc(x_108);
x_110 = lean::cnstr_get(x_101, 2);
lean::inc(x_110);
lean::dec(x_101);
x_113 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__4(x_0, x_108, x_103);
x_114 = lean::cnstr_get(x_113, 0);
lean::inc(x_114);
x_116 = lean::cnstr_get(x_113, 1);
lean::inc(x_116);
lean::dec(x_113);
if (lean::obj_tag(x_114) == 0)
{
obj* x_119; obj* x_121; obj* x_123; obj* x_126; obj* x_127; obj* x_129; obj* x_132; obj* x_134; obj* x_137; obj* x_140; obj* x_143; uint8 x_144; 
x_119 = lean::cnstr_get(x_114, 0);
lean::inc(x_119);
x_121 = lean::cnstr_get(x_114, 1);
lean::inc(x_121);
x_123 = lean::cnstr_get(x_114, 2);
lean::inc(x_123);
lean::dec(x_114);
x_126 = lean::mk_nat_obj(16u);
x_127 = lean::nat_mul(x_126, x_78);
lean::dec(x_78);
x_129 = lean::nat_add(x_127, x_92);
lean::dec(x_92);
lean::dec(x_127);
x_132 = lean::nat_mul(x_126, x_129);
lean::dec(x_129);
x_134 = lean::nat_add(x_132, x_106);
lean::dec(x_106);
lean::dec(x_132);
x_137 = lean::nat_mul(x_126, x_134);
lean::dec(x_134);
lean::dec(x_126);
x_140 = lean::nat_add(x_137, x_119);
lean::dec(x_119);
lean::dec(x_137);
x_143 = lean::mk_nat_obj(55296u);
x_144 = lean::nat_dec_lt(x_140, x_143);
lean::dec(x_143);
if (x_144 == 0)
{
obj* x_146; uint8 x_147; 
x_146 = lean::mk_nat_obj(57343u);
x_147 = lean::nat_dec_lt(x_146, x_140);
lean::dec(x_146);
if (x_147 == 0)
{
obj* x_150; obj* x_151; obj* x_153; obj* x_154; obj* x_155; obj* x_156; obj* x_157; obj* x_158; obj* x_160; obj* x_161; 
lean::dec(x_140);
x_150 = lean::mk_nat_obj(0u);
x_151 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_151);
if (lean::is_scalar(x_17)) {
 x_153 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_153 = x_17;
}
lean::cnstr_set(x_153, 0, x_150);
lean::cnstr_set(x_153, 1, x_121);
lean::cnstr_set(x_153, 2, x_151);
x_154 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_123, x_153);
x_155 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_110, x_154);
x_156 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_96, x_155);
x_157 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_82, x_156);
x_158 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_157);
lean::inc(x_151);
x_160 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_151, x_158);
if (lean::is_scalar(x_10)) {
 x_161 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_161 = x_10;
}
lean::cnstr_set(x_161, 0, x_160);
lean::cnstr_set(x_161, 1, x_116);
return x_161;
}
else
{
obj* x_162; uint8 x_163; 
x_162 = lean::mk_nat_obj(1114112u);
x_163 = lean::nat_dec_lt(x_140, x_162);
lean::dec(x_162);
if (x_163 == 0)
{
obj* x_166; obj* x_167; obj* x_169; obj* x_170; obj* x_171; obj* x_172; obj* x_173; obj* x_174; obj* x_176; obj* x_177; 
lean::dec(x_140);
x_166 = lean::mk_nat_obj(0u);
x_167 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_167);
if (lean::is_scalar(x_17)) {
 x_169 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_169 = x_17;
}
lean::cnstr_set(x_169, 0, x_166);
lean::cnstr_set(x_169, 1, x_121);
lean::cnstr_set(x_169, 2, x_167);
x_170 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_123, x_169);
x_171 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_110, x_170);
x_172 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_96, x_171);
x_173 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_82, x_172);
x_174 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_173);
lean::inc(x_167);
x_176 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_167, x_174);
if (lean::is_scalar(x_10)) {
 x_177 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_177 = x_10;
}
lean::cnstr_set(x_177, 0, x_176);
lean::cnstr_set(x_177, 1, x_116);
return x_177;
}
else
{
obj* x_178; obj* x_180; obj* x_181; obj* x_182; obj* x_183; obj* x_184; obj* x_185; obj* x_187; obj* x_188; 
x_178 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_178);
if (lean::is_scalar(x_17)) {
 x_180 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_180 = x_17;
}
lean::cnstr_set(x_180, 0, x_140);
lean::cnstr_set(x_180, 1, x_121);
lean::cnstr_set(x_180, 2, x_178);
x_181 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_123, x_180);
x_182 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_110, x_181);
x_183 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_96, x_182);
x_184 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_82, x_183);
x_185 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_184);
lean::inc(x_178);
x_187 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_178, x_185);
if (lean::is_scalar(x_10)) {
 x_188 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_188 = x_10;
}
lean::cnstr_set(x_188, 0, x_187);
lean::cnstr_set(x_188, 1, x_116);
return x_188;
}
}
}
else
{
obj* x_189; obj* x_191; obj* x_192; obj* x_193; obj* x_194; obj* x_195; obj* x_196; obj* x_198; obj* x_199; 
x_189 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_189);
if (lean::is_scalar(x_17)) {
 x_191 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_191 = x_17;
}
lean::cnstr_set(x_191, 0, x_140);
lean::cnstr_set(x_191, 1, x_121);
lean::cnstr_set(x_191, 2, x_189);
x_192 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_123, x_191);
x_193 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_110, x_192);
x_194 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_96, x_193);
x_195 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_82, x_194);
x_196 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_195);
lean::inc(x_189);
x_198 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_189, x_196);
if (lean::is_scalar(x_10)) {
 x_199 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_199 = x_10;
}
lean::cnstr_set(x_199, 0, x_198);
lean::cnstr_set(x_199, 1, x_116);
return x_199;
}
}
else
{
obj* x_204; uint8 x_206; obj* x_207; obj* x_208; obj* x_209; obj* x_210; obj* x_211; obj* x_212; obj* x_213; obj* x_214; obj* x_216; obj* x_217; 
lean::dec(x_106);
lean::dec(x_92);
lean::dec(x_78);
lean::dec(x_17);
x_204 = lean::cnstr_get(x_114, 0);
lean::inc(x_204);
x_206 = lean::cnstr_get_scalar<uint8>(x_114, sizeof(void*)*1);
if (lean::is_shared(x_114)) {
 lean::dec(x_114);
 x_207 = lean::box(0);
} else {
 lean::cnstr_release(x_114, 0);
 x_207 = x_114;
}
if (lean::is_scalar(x_207)) {
 x_208 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_208 = x_207;
}
lean::cnstr_set(x_208, 0, x_204);
lean::cnstr_set_scalar(x_208, sizeof(void*)*1, x_206);
x_209 = x_208;
x_210 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_110, x_209);
x_211 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_96, x_210);
x_212 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_82, x_211);
x_213 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_212);
x_214 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_214);
x_216 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_214, x_213);
if (lean::is_scalar(x_10)) {
 x_217 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_217 = x_10;
}
lean::cnstr_set(x_217, 0, x_216);
lean::cnstr_set(x_217, 1, x_116);
return x_217;
}
}
else
{
obj* x_222; uint8 x_224; obj* x_225; obj* x_226; obj* x_227; obj* x_228; obj* x_229; obj* x_230; obj* x_231; obj* x_233; obj* x_234; 
lean::dec(x_92);
lean::dec(x_78);
lean::dec(x_17);
lean::dec(x_0);
x_222 = lean::cnstr_get(x_101, 0);
lean::inc(x_222);
x_224 = lean::cnstr_get_scalar<uint8>(x_101, sizeof(void*)*1);
if (lean::is_shared(x_101)) {
 lean::dec(x_101);
 x_225 = lean::box(0);
} else {
 lean::cnstr_release(x_101, 0);
 x_225 = x_101;
}
if (lean::is_scalar(x_225)) {
 x_226 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_226 = x_225;
}
lean::cnstr_set(x_226, 0, x_222);
lean::cnstr_set_scalar(x_226, sizeof(void*)*1, x_224);
x_227 = x_226;
x_228 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_96, x_227);
x_229 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_82, x_228);
x_230 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_229);
x_231 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_231);
x_233 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_231, x_230);
if (lean::is_scalar(x_10)) {
 x_234 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_234 = x_10;
}
lean::cnstr_set(x_234, 0, x_233);
lean::cnstr_set(x_234, 1, x_103);
return x_234;
}
}
else
{
obj* x_238; uint8 x_240; obj* x_241; obj* x_242; obj* x_243; obj* x_244; obj* x_245; obj* x_246; obj* x_248; obj* x_249; 
lean::dec(x_78);
lean::dec(x_17);
lean::dec(x_0);
x_238 = lean::cnstr_get(x_87, 0);
lean::inc(x_238);
x_240 = lean::cnstr_get_scalar<uint8>(x_87, sizeof(void*)*1);
if (lean::is_shared(x_87)) {
 lean::dec(x_87);
 x_241 = lean::box(0);
} else {
 lean::cnstr_release(x_87, 0);
 x_241 = x_87;
}
if (lean::is_scalar(x_241)) {
 x_242 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_242 = x_241;
}
lean::cnstr_set(x_242, 0, x_238);
lean::cnstr_set_scalar(x_242, sizeof(void*)*1, x_240);
x_243 = x_242;
x_244 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_82, x_243);
x_245 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_244);
x_246 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_246);
x_248 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_246, x_245);
if (lean::is_scalar(x_10)) {
 x_249 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_249 = x_10;
}
lean::cnstr_set(x_249, 0, x_248);
lean::cnstr_set(x_249, 1, x_89);
return x_249;
}
}
else
{
obj* x_252; uint8 x_254; obj* x_255; obj* x_256; obj* x_257; obj* x_258; obj* x_259; obj* x_261; obj* x_262; 
lean::dec(x_17);
lean::dec(x_0);
x_252 = lean::cnstr_get(x_73, 0);
lean::inc(x_252);
x_254 = lean::cnstr_get_scalar<uint8>(x_73, sizeof(void*)*1);
if (lean::is_shared(x_73)) {
 lean::dec(x_73);
 x_255 = lean::box(0);
} else {
 lean::cnstr_release(x_73, 0);
 x_255 = x_73;
}
if (lean::is_scalar(x_255)) {
 x_256 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_256 = x_255;
}
lean::cnstr_set(x_256, 0, x_252);
lean::cnstr_set_scalar(x_256, sizeof(void*)*1, x_254);
x_257 = x_256;
x_258 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_257);
x_259 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_259);
x_261 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_259, x_258);
if (lean::is_scalar(x_10)) {
 x_262 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_262 = x_10;
}
lean::cnstr_set(x_262, 0, x_261);
lean::cnstr_set(x_262, 1, x_75);
return x_262;
}
}
lbl_21:
{
obj* x_265; obj* x_266; obj* x_268; obj* x_270; 
lean::dec(x_20);
lean::inc(x_0);
x_265 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__4(x_0, x_13, x_8);
x_266 = lean::cnstr_get(x_265, 0);
lean::inc(x_266);
x_268 = lean::cnstr_get(x_265, 1);
lean::inc(x_268);
if (lean::is_shared(x_265)) {
 lean::dec(x_265);
 x_270 = lean::box(0);
} else {
 lean::cnstr_release(x_265, 0);
 lean::cnstr_release(x_265, 1);
 x_270 = x_265;
}
if (lean::obj_tag(x_266) == 0)
{
obj* x_271; obj* x_273; obj* x_275; obj* x_277; obj* x_278; obj* x_279; obj* x_281; 
x_271 = lean::cnstr_get(x_266, 0);
lean::inc(x_271);
x_273 = lean::cnstr_get(x_266, 1);
lean::inc(x_273);
x_275 = lean::cnstr_get(x_266, 2);
lean::inc(x_275);
if (lean::is_shared(x_266)) {
 lean::dec(x_266);
 x_277 = lean::box(0);
} else {
 lean::cnstr_release(x_266, 0);
 lean::cnstr_release(x_266, 1);
 lean::cnstr_release(x_266, 2);
 x_277 = x_266;
}
x_278 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__4(x_0, x_273, x_268);
x_279 = lean::cnstr_get(x_278, 0);
lean::inc(x_279);
x_281 = lean::cnstr_get(x_278, 1);
lean::inc(x_281);
lean::dec(x_278);
if (lean::obj_tag(x_279) == 0)
{
obj* x_284; obj* x_286; obj* x_288; obj* x_291; obj* x_292; obj* x_295; obj* x_298; uint8 x_299; 
x_284 = lean::cnstr_get(x_279, 0);
lean::inc(x_284);
x_286 = lean::cnstr_get(x_279, 1);
lean::inc(x_286);
x_288 = lean::cnstr_get(x_279, 2);
lean::inc(x_288);
lean::dec(x_279);
x_291 = lean::mk_nat_obj(16u);
x_292 = lean::nat_mul(x_291, x_271);
lean::dec(x_271);
lean::dec(x_291);
x_295 = lean::nat_add(x_292, x_284);
lean::dec(x_284);
lean::dec(x_292);
x_298 = lean::mk_nat_obj(55296u);
x_299 = lean::nat_dec_lt(x_295, x_298);
lean::dec(x_298);
if (x_299 == 0)
{
obj* x_301; uint8 x_302; 
x_301 = lean::mk_nat_obj(57343u);
x_302 = lean::nat_dec_lt(x_301, x_295);
lean::dec(x_301);
if (x_302 == 0)
{
obj* x_305; obj* x_306; obj* x_308; obj* x_309; obj* x_310; obj* x_311; obj* x_313; obj* x_314; 
lean::dec(x_295);
x_305 = lean::mk_nat_obj(0u);
x_306 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_306);
if (lean::is_scalar(x_277)) {
 x_308 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_308 = x_277;
}
lean::cnstr_set(x_308, 0, x_305);
lean::cnstr_set(x_308, 1, x_286);
lean::cnstr_set(x_308, 2, x_306);
x_309 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_288, x_308);
x_310 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_275, x_309);
x_311 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_310);
lean::inc(x_306);
x_313 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_306, x_311);
if (lean::is_scalar(x_270)) {
 x_314 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_314 = x_270;
}
lean::cnstr_set(x_314, 0, x_313);
lean::cnstr_set(x_314, 1, x_281);
return x_314;
}
else
{
obj* x_315; uint8 x_316; 
x_315 = lean::mk_nat_obj(1114112u);
x_316 = lean::nat_dec_lt(x_295, x_315);
lean::dec(x_315);
if (x_316 == 0)
{
obj* x_319; obj* x_320; obj* x_322; obj* x_323; obj* x_324; obj* x_325; obj* x_327; obj* x_328; 
lean::dec(x_295);
x_319 = lean::mk_nat_obj(0u);
x_320 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_320);
if (lean::is_scalar(x_277)) {
 x_322 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_322 = x_277;
}
lean::cnstr_set(x_322, 0, x_319);
lean::cnstr_set(x_322, 1, x_286);
lean::cnstr_set(x_322, 2, x_320);
x_323 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_288, x_322);
x_324 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_275, x_323);
x_325 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_324);
lean::inc(x_320);
x_327 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_320, x_325);
if (lean::is_scalar(x_270)) {
 x_328 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_328 = x_270;
}
lean::cnstr_set(x_328, 0, x_327);
lean::cnstr_set(x_328, 1, x_281);
return x_328;
}
else
{
obj* x_329; obj* x_331; obj* x_332; obj* x_333; obj* x_334; obj* x_336; obj* x_337; 
x_329 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_329);
if (lean::is_scalar(x_277)) {
 x_331 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_331 = x_277;
}
lean::cnstr_set(x_331, 0, x_295);
lean::cnstr_set(x_331, 1, x_286);
lean::cnstr_set(x_331, 2, x_329);
x_332 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_288, x_331);
x_333 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_275, x_332);
x_334 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_333);
lean::inc(x_329);
x_336 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_329, x_334);
if (lean::is_scalar(x_270)) {
 x_337 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_337 = x_270;
}
lean::cnstr_set(x_337, 0, x_336);
lean::cnstr_set(x_337, 1, x_281);
return x_337;
}
}
}
else
{
obj* x_338; obj* x_340; obj* x_341; obj* x_342; obj* x_343; obj* x_345; obj* x_346; 
x_338 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_338);
if (lean::is_scalar(x_277)) {
 x_340 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_340 = x_277;
}
lean::cnstr_set(x_340, 0, x_295);
lean::cnstr_set(x_340, 1, x_286);
lean::cnstr_set(x_340, 2, x_338);
x_341 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_288, x_340);
x_342 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_275, x_341);
x_343 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_342);
lean::inc(x_338);
x_345 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_338, x_343);
if (lean::is_scalar(x_270)) {
 x_346 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_346 = x_270;
}
lean::cnstr_set(x_346, 0, x_345);
lean::cnstr_set(x_346, 1, x_281);
return x_346;
}
}
else
{
obj* x_349; uint8 x_351; obj* x_352; obj* x_353; obj* x_354; obj* x_355; obj* x_356; obj* x_357; obj* x_359; obj* x_360; 
lean::dec(x_271);
lean::dec(x_277);
x_349 = lean::cnstr_get(x_279, 0);
lean::inc(x_349);
x_351 = lean::cnstr_get_scalar<uint8>(x_279, sizeof(void*)*1);
if (lean::is_shared(x_279)) {
 lean::dec(x_279);
 x_352 = lean::box(0);
} else {
 lean::cnstr_release(x_279, 0);
 x_352 = x_279;
}
if (lean::is_scalar(x_352)) {
 x_353 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_353 = x_352;
}
lean::cnstr_set(x_353, 0, x_349);
lean::cnstr_set_scalar(x_353, sizeof(void*)*1, x_351);
x_354 = x_353;
x_355 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_275, x_354);
x_356 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_355);
x_357 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_357);
x_359 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_357, x_356);
if (lean::is_scalar(x_270)) {
 x_360 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_360 = x_270;
}
lean::cnstr_set(x_360, 0, x_359);
lean::cnstr_set(x_360, 1, x_281);
return x_360;
}
}
else
{
obj* x_362; uint8 x_364; obj* x_365; obj* x_366; obj* x_367; obj* x_368; obj* x_369; obj* x_371; obj* x_372; 
lean::dec(x_0);
x_362 = lean::cnstr_get(x_266, 0);
lean::inc(x_362);
x_364 = lean::cnstr_get_scalar<uint8>(x_266, sizeof(void*)*1);
if (lean::is_shared(x_266)) {
 lean::dec(x_266);
 x_365 = lean::box(0);
} else {
 lean::cnstr_release(x_266, 0);
 x_365 = x_266;
}
if (lean::is_scalar(x_365)) {
 x_366 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_366 = x_365;
}
lean::cnstr_set(x_366, 0, x_362);
lean::cnstr_set_scalar(x_366, sizeof(void*)*1, x_364);
x_367 = x_366;
x_368 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_367);
x_369 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_369);
x_371 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_369, x_368);
if (lean::is_scalar(x_270)) {
 x_372 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_372 = x_270;
}
lean::cnstr_set(x_372, 0, x_371);
lean::cnstr_set(x_372, 1, x_268);
return x_372;
}
}
lbl_23:
{
obj* x_374; uint8 x_375; 
lean::dec(x_22);
x_374 = lean::mk_nat_obj(110u);
x_375 = lean::nat_dec_eq(x_11, x_374);
lean::dec(x_374);
if (x_375 == 0)
{
obj* x_377; uint8 x_378; 
x_377 = lean::mk_nat_obj(116u);
x_378 = lean::nat_dec_eq(x_11, x_377);
lean::dec(x_377);
if (x_378 == 0)
{
obj* x_380; uint8 x_381; 
x_380 = lean::mk_nat_obj(120u);
x_381 = lean::nat_dec_eq(x_11, x_380);
lean::dec(x_380);
if (x_381 == 0)
{
obj* x_383; uint8 x_384; 
x_383 = lean::mk_nat_obj(117u);
x_384 = lean::nat_dec_eq(x_11, x_383);
lean::dec(x_383);
lean::dec(x_11);
if (x_384 == 0)
{
obj* x_389; obj* x_391; obj* x_392; obj* x_394; obj* x_396; obj* x_397; obj* x_398; obj* x_400; obj* x_401; 
lean::dec(x_17);
lean::dec(x_10);
x_389 = l_lean_parser_parse__quoted__char___rarg___lambda__7___closed__1;
lean::inc(x_389);
x_391 = l_lean_parser_monad__parsec_unexpected__at___at_lean_parser_string__lit_x_27___spec__6___rarg(x_389, x_1, x_0, x_13, x_8);
x_392 = lean::cnstr_get(x_391, 0);
lean::inc(x_392);
x_394 = lean::cnstr_get(x_391, 1);
lean::inc(x_394);
if (lean::is_shared(x_391)) {
 lean::dec(x_391);
 x_396 = lean::box(0);
} else {
 lean::cnstr_release(x_391, 0);
 lean::cnstr_release(x_391, 1);
 x_396 = x_391;
}
x_397 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_392);
x_398 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_398);
x_400 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_398, x_397);
if (lean::is_scalar(x_396)) {
 x_401 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_401 = x_396;
}
lean::cnstr_set(x_401, 0, x_400);
lean::cnstr_set(x_401, 1, x_394);
return x_401;
}
else
{
obj* x_403; 
lean::dec(x_1);
x_403 = lean::box(0);
x_18 = x_403;
goto lbl_19;
}
}
else
{
obj* x_408; 
lean::dec(x_17);
lean::dec(x_11);
lean::dec(x_1);
lean::dec(x_10);
x_408 = lean::box(0);
x_20 = x_408;
goto lbl_21;
}
}
else
{
obj* x_414; obj* x_415; obj* x_417; obj* x_418; obj* x_420; obj* x_421; 
lean::dec(x_17);
lean::dec(x_11);
lean::dec(x_1);
lean::dec(x_10);
lean::dec(x_0);
x_414 = lean::mk_nat_obj(9u);
x_415 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_415);
x_417 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_417, 0, x_414);
lean::cnstr_set(x_417, 1, x_13);
lean::cnstr_set(x_417, 2, x_415);
x_418 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_417);
lean::inc(x_415);
x_420 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_415, x_418);
x_421 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_421, 0, x_420);
lean::cnstr_set(x_421, 1, x_8);
return x_421;
}
}
else
{
obj* x_427; obj* x_428; obj* x_430; obj* x_431; obj* x_433; obj* x_434; 
lean::dec(x_17);
lean::dec(x_11);
lean::dec(x_1);
lean::dec(x_10);
lean::dec(x_0);
x_427 = lean::mk_nat_obj(10u);
x_428 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_428);
x_430 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_430, 0, x_427);
lean::cnstr_set(x_430, 1, x_13);
lean::cnstr_set(x_430, 2, x_428);
x_431 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_430);
lean::inc(x_428);
x_433 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_428, x_431);
x_434 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_434, 0, x_433);
lean::cnstr_set(x_434, 1, x_8);
return x_434;
}
}
}
else
{
obj* x_437; uint8 x_439; obj* x_440; obj* x_441; obj* x_442; obj* x_443; obj* x_445; obj* x_446; 
lean::dec(x_1);
lean::dec(x_0);
x_437 = lean::cnstr_get(x_6, 0);
lean::inc(x_437);
x_439 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*1);
if (lean::is_shared(x_6)) {
 lean::dec(x_6);
 x_440 = lean::box(0);
} else {
 lean::cnstr_release(x_6, 0);
 x_440 = x_6;
}
if (lean::is_scalar(x_440)) {
 x_441 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_441 = x_440;
}
lean::cnstr_set(x_441, 0, x_437);
lean::cnstr_set_scalar(x_441, sizeof(void*)*1, x_439);
x_442 = x_441;
x_443 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_443);
x_445 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_443, x_442);
if (lean::is_scalar(x_10)) {
 x_446 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_446 = x_10;
}
lean::cnstr_set(x_446, 0, x_445);
lean::cnstr_set(x_446, 1, x_8);
return x_446;
}
}
}
obj* l_lean_parser_parse__string__literal__aux___main___at_lean_parser_string__lit_x_27___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::mk_nat_obj(0u);
x_6 = lean::nat_dec_eq(x_0, x_5);
lean::dec(x_5);
if (x_6 == 0)
{
obj* x_9; obj* x_10; obj* x_12; obj* x_14; 
lean::inc(x_2);
x_9 = l_lean_parser_monad__parsec_any___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__2(x_2, x_3, x_4);
x_10 = lean::cnstr_get(x_9, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_9, 1);
lean::inc(x_12);
if (lean::is_shared(x_9)) {
 lean::dec(x_9);
 x_14 = lean::box(0);
} else {
 lean::cnstr_release(x_9, 0);
 lean::cnstr_release(x_9, 1);
 x_14 = x_9;
}
if (lean::obj_tag(x_10) == 0)
{
obj* x_15; obj* x_17; obj* x_19; obj* x_21; obj* x_22; obj* x_23; obj* x_26; uint8 x_27; 
x_15 = lean::cnstr_get(x_10, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_10, 1);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_10, 2);
lean::inc(x_19);
if (lean::is_shared(x_10)) {
 lean::dec(x_10);
 x_21 = lean::box(0);
} else {
 lean::cnstr_release(x_10, 0);
 lean::cnstr_release(x_10, 1);
 lean::cnstr_release(x_10, 2);
 x_21 = x_10;
}
x_22 = lean::mk_nat_obj(1u);
x_23 = lean::nat_sub(x_0, x_22);
lean::dec(x_22);
lean::dec(x_0);
x_26 = lean::mk_nat_obj(92u);
x_27 = lean::nat_dec_eq(x_15, x_26);
lean::dec(x_26);
if (x_27 == 0)
{
obj* x_29; uint8 x_30; 
x_29 = lean::mk_nat_obj(34u);
x_30 = lean::nat_dec_eq(x_15, x_29);
lean::dec(x_29);
if (x_30 == 0)
{
uint32 x_33; obj* x_35; obj* x_36; obj* x_37; obj* x_39; obj* x_42; obj* x_43; 
lean::dec(x_21);
x_33 = lean::unbox_uint32(x_15);
lean::dec(x_15);
x_35 = lean::string_push(x_1, x_33);
x_36 = l_lean_parser_parse__string__literal__aux___main___at_lean_parser_string__lit_x_27___spec__2(x_23, x_35, x_2, x_17, x_12);
x_37 = lean::cnstr_get(x_36, 0);
lean::inc(x_37);
x_39 = lean::cnstr_get(x_36, 1);
lean::inc(x_39);
lean::dec(x_36);
x_42 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_19, x_37);
if (lean::is_scalar(x_14)) {
 x_43 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_43 = x_14;
}
lean::cnstr_set(x_43, 0, x_42);
lean::cnstr_set(x_43, 1, x_39);
return x_43;
}
else
{
obj* x_47; obj* x_49; obj* x_50; obj* x_51; 
lean::dec(x_15);
lean::dec(x_2);
lean::dec(x_23);
x_47 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_47);
if (lean::is_scalar(x_21)) {
 x_49 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_49 = x_21;
}
lean::cnstr_set(x_49, 0, x_1);
lean::cnstr_set(x_49, 1, x_17);
lean::cnstr_set(x_49, 2, x_47);
x_50 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_19, x_49);
if (lean::is_scalar(x_14)) {
 x_51 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_51 = x_14;
}
lean::cnstr_set(x_51, 0, x_50);
lean::cnstr_set(x_51, 1, x_12);
return x_51;
}
}
else
{
obj* x_55; obj* x_56; obj* x_58; 
lean::dec(x_21);
lean::dec(x_15);
lean::inc(x_2);
x_55 = l_lean_parser_parse__quoted__char___at_lean_parser_string__lit_x_27___spec__3(x_2, x_17, x_12);
x_56 = lean::cnstr_get(x_55, 0);
lean::inc(x_56);
x_58 = lean::cnstr_get(x_55, 1);
lean::inc(x_58);
lean::dec(x_55);
if (lean::obj_tag(x_56) == 0)
{
obj* x_61; obj* x_63; obj* x_65; uint32 x_68; obj* x_70; obj* x_71; obj* x_72; obj* x_74; obj* x_77; obj* x_78; obj* x_79; 
x_61 = lean::cnstr_get(x_56, 0);
lean::inc(x_61);
x_63 = lean::cnstr_get(x_56, 1);
lean::inc(x_63);
x_65 = lean::cnstr_get(x_56, 2);
lean::inc(x_65);
lean::dec(x_56);
x_68 = lean::unbox_uint32(x_61);
lean::dec(x_61);
x_70 = lean::string_push(x_1, x_68);
x_71 = l_lean_parser_parse__string__literal__aux___main___at_lean_parser_string__lit_x_27___spec__2(x_23, x_70, x_2, x_63, x_58);
x_72 = lean::cnstr_get(x_71, 0);
lean::inc(x_72);
x_74 = lean::cnstr_get(x_71, 1);
lean::inc(x_74);
lean::dec(x_71);
x_77 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_65, x_72);
x_78 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_19, x_77);
if (lean::is_scalar(x_14)) {
 x_79 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_79 = x_14;
}
lean::cnstr_set(x_79, 0, x_78);
lean::cnstr_set(x_79, 1, x_74);
return x_79;
}
else
{
obj* x_83; uint8 x_85; obj* x_86; obj* x_87; obj* x_88; obj* x_89; obj* x_90; 
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_23);
x_83 = lean::cnstr_get(x_56, 0);
lean::inc(x_83);
x_85 = lean::cnstr_get_scalar<uint8>(x_56, sizeof(void*)*1);
if (lean::is_shared(x_56)) {
 lean::dec(x_56);
 x_86 = lean::box(0);
} else {
 lean::cnstr_release(x_56, 0);
 x_86 = x_56;
}
if (lean::is_scalar(x_86)) {
 x_87 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_87 = x_86;
}
lean::cnstr_set(x_87, 0, x_83);
lean::cnstr_set_scalar(x_87, sizeof(void*)*1, x_85);
x_88 = x_87;
x_89 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_19, x_88);
if (lean::is_scalar(x_14)) {
 x_90 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_90 = x_14;
}
lean::cnstr_set(x_90, 0, x_89);
lean::cnstr_set(x_90, 1, x_58);
return x_90;
}
}
}
else
{
obj* x_94; uint8 x_96; obj* x_97; obj* x_98; obj* x_99; obj* x_100; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_94 = lean::cnstr_get(x_10, 0);
lean::inc(x_94);
x_96 = lean::cnstr_get_scalar<uint8>(x_10, sizeof(void*)*1);
if (lean::is_shared(x_10)) {
 lean::dec(x_10);
 x_97 = lean::box(0);
} else {
 lean::cnstr_release(x_10, 0);
 x_97 = x_10;
}
if (lean::is_scalar(x_97)) {
 x_98 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_98 = x_97;
}
lean::cnstr_set(x_98, 0, x_94);
lean::cnstr_set_scalar(x_98, sizeof(void*)*1, x_96);
x_99 = x_98;
if (lean::is_scalar(x_14)) {
 x_100 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_100 = x_14;
}
lean::cnstr_set(x_100, 0, x_99);
lean::cnstr_set(x_100, 1, x_12);
return x_100;
}
}
else
{
obj* x_102; uint32 x_103; obj* x_105; obj* x_106; obj* x_108; obj* x_110; 
lean::dec(x_0);
x_102 = lean::mk_nat_obj(34u);
x_103 = lean::unbox_uint32(x_102);
lean::dec(x_102);
x_105 = l_lean_parser_monad__parsec_ch___at___private_init_lean_parser_token_4__ident_x_27___spec__11(x_103, x_2, x_3, x_4);
x_106 = lean::cnstr_get(x_105, 0);
lean::inc(x_106);
x_108 = lean::cnstr_get(x_105, 1);
lean::inc(x_108);
if (lean::is_shared(x_105)) {
 lean::dec(x_105);
 x_110 = lean::box(0);
} else {
 lean::cnstr_release(x_105, 0);
 lean::cnstr_release(x_105, 1);
 x_110 = x_105;
}
if (lean::obj_tag(x_106) == 0)
{
obj* x_111; obj* x_113; obj* x_115; obj* x_116; obj* x_118; obj* x_119; obj* x_120; 
x_111 = lean::cnstr_get(x_106, 1);
lean::inc(x_111);
x_113 = lean::cnstr_get(x_106, 2);
lean::inc(x_113);
if (lean::is_shared(x_106)) {
 lean::dec(x_106);
 x_115 = lean::box(0);
} else {
 lean::cnstr_release(x_106, 0);
 lean::cnstr_release(x_106, 1);
 lean::cnstr_release(x_106, 2);
 x_115 = x_106;
}
x_116 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_116);
if (lean::is_scalar(x_115)) {
 x_118 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_118 = x_115;
}
lean::cnstr_set(x_118, 0, x_1);
lean::cnstr_set(x_118, 1, x_111);
lean::cnstr_set(x_118, 2, x_116);
x_119 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_113, x_118);
if (lean::is_scalar(x_110)) {
 x_120 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_120 = x_110;
}
lean::cnstr_set(x_120, 0, x_119);
lean::cnstr_set(x_120, 1, x_108);
return x_120;
}
else
{
obj* x_122; uint8 x_124; obj* x_125; obj* x_126; obj* x_127; obj* x_128; 
lean::dec(x_1);
x_122 = lean::cnstr_get(x_106, 0);
lean::inc(x_122);
x_124 = lean::cnstr_get_scalar<uint8>(x_106, sizeof(void*)*1);
if (lean::is_shared(x_106)) {
 lean::dec(x_106);
 x_125 = lean::box(0);
} else {
 lean::cnstr_release(x_106, 0);
 x_125 = x_106;
}
if (lean::is_scalar(x_125)) {
 x_126 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_126 = x_125;
}
lean::cnstr_set(x_126, 0, x_122);
lean::cnstr_set_scalar(x_126, sizeof(void*)*1, x_124);
x_127 = x_126;
if (lean::is_scalar(x_110)) {
 x_128 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_128 = x_110;
}
lean::cnstr_set(x_128, 0, x_127);
lean::cnstr_set(x_128, 1, x_108);
return x_128;
}
}
}
}
obj* l_lean_parser_parse__string__literal___at_lean_parser_string__lit_x_27___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint32 x_4; obj* x_7; obj* x_8; obj* x_10; obj* x_12; 
x_3 = lean::mk_nat_obj(34u);
x_4 = lean::unbox_uint32(x_3);
lean::dec(x_3);
lean::inc(x_0);
x_7 = l_lean_parser_monad__parsec_ch___at___private_init_lean_parser_token_4__ident_x_27___spec__11(x_4, x_0, x_1, x_2);
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
obj* x_13; obj* x_15; obj* x_18; obj* x_19; obj* x_21; obj* x_22; obj* x_24; obj* x_27; obj* x_29; obj* x_30; obj* x_31; 
x_13 = lean::cnstr_get(x_8, 1);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_8, 2);
lean::inc(x_15);
lean::dec(x_8);
x_18 = lean::string_iterator_remaining(x_13);
x_19 = l_string_join___closed__1;
lean::inc(x_19);
x_21 = l_lean_parser_parse__string__literal__aux___main___at_lean_parser_string__lit_x_27___spec__2(x_18, x_19, x_0, x_13, x_10);
x_22 = lean::cnstr_get(x_21, 0);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_21, 1);
lean::inc(x_24);
lean::dec(x_21);
x_27 = l_lean_parser_finish__comment__block___closed__2;
lean::inc(x_27);
x_29 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_27, x_22);
x_30 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_29);
if (lean::is_scalar(x_12)) {
 x_31 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_31 = x_12;
}
lean::cnstr_set(x_31, 0, x_30);
lean::cnstr_set(x_31, 1, x_24);
return x_31;
}
else
{
obj* x_33; uint8 x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; 
lean::dec(x_0);
x_33 = lean::cnstr_get(x_8, 0);
lean::inc(x_33);
x_35 = lean::cnstr_get_scalar<uint8>(x_8, sizeof(void*)*1);
if (lean::is_shared(x_8)) {
 lean::dec(x_8);
 x_36 = lean::box(0);
} else {
 lean::cnstr_release(x_8, 0);
 x_36 = x_8;
}
if (lean::is_scalar(x_36)) {
 x_37 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_37 = x_36;
}
lean::cnstr_set(x_37, 0, x_33);
lean::cnstr_set_scalar(x_37, sizeof(void*)*1, x_35);
x_38 = x_37;
if (lean::is_scalar(x_12)) {
 x_39 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_39 = x_12;
}
lean::cnstr_set(x_39, 0, x_38);
lean::cnstr_set(x_39, 1, x_10);
return x_39;
}
}
}
obj* l_lean_parser_string__lit_x_27___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_7; obj* x_9; 
x_4 = l_lean_parser_parse__string__literal___at_lean_parser_string__lit_x_27___spec__1(x_1, x_2, x_3);
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
obj* x_10; obj* x_12; obj* x_14; obj* x_16; obj* x_17; obj* x_19; obj* x_20; obj* x_21; 
x_10 = lean::cnstr_get(x_5, 1);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_5, 2);
lean::inc(x_12);
if (lean::is_shared(x_5)) {
 lean::dec(x_5);
 x_14 = lean::box(0);
} else {
 lean::cnstr_release(x_5, 0);
 lean::cnstr_release(x_5, 1);
 lean::cnstr_release(x_5, 2);
 x_14 = x_5;
}
lean::inc(x_10);
x_16 = l_lean_parser_mk__raw__res(x_0, x_10);
x_17 = l_lean_parser_finish__comment__block___closed__2;
lean::inc(x_17);
if (lean::is_scalar(x_14)) {
 x_19 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_19 = x_14;
}
lean::cnstr_set(x_19, 0, x_16);
lean::cnstr_set(x_19, 1, x_10);
lean::cnstr_set(x_19, 2, x_17);
x_20 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_12, x_19);
if (lean::is_scalar(x_9)) {
 x_21 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_21 = x_9;
}
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_7);
return x_21;
}
else
{
obj* x_23; uint8 x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
lean::dec(x_0);
x_23 = lean::cnstr_get(x_5, 0);
lean::inc(x_23);
x_25 = lean::cnstr_get_scalar<uint8>(x_5, sizeof(void*)*1);
if (lean::is_shared(x_5)) {
 lean::dec(x_5);
 x_26 = lean::box(0);
} else {
 lean::cnstr_release(x_5, 0);
 x_26 = x_5;
}
if (lean::is_scalar(x_26)) {
 x_27 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_27 = x_26;
}
lean::cnstr_set(x_27, 0, x_23);
lean::cnstr_set_scalar(x_27, sizeof(void*)*1, x_25);
x_28 = x_27;
if (lean::is_scalar(x_9)) {
 x_29 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_29 = x_9;
}
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_7);
return x_29;
}
}
}
obj* _init_l_lean_parser_string__lit_x_27___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_with__trailing___rarg___lambda__1), 2, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_lift___at_lean_parser_with__trailing___spec__1___rarg), 4, 1);
lean::closure_set(x_1, 0, x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_string__lit_x_27___lambda__1), 4, 0);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_bind___at_lean_parser_with__trailing___spec__2___rarg), 5, 2);
lean::closure_set(x_3, 0, x_1);
lean::closure_set(x_3, 1, x_2);
x_4 = lean::box(0);
x_5 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_5, 0, x_3);
lean::cnstr_set(x_5, 1, x_4);
return x_5;
}
}
obj* l_lean_parser_string__lit_x_27(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_7; 
x_3 = l_lean_parser_string__lit;
x_4 = l_lean_parser_string__lit_x_27___closed__1;
lean::inc(x_4);
lean::inc(x_3);
x_7 = l_lean_parser_combinators_node___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__15(x_3, x_4, x_0, x_1, x_2);
return x_7;
}
}
obj* l___private_init_lean_parser_token_5__mk__consume__token(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_7; obj* x_10; obj* x_13; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
lean::dec(x_3);
lean::dec(x_2);
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::string_length(x_7);
lean::dec(x_7);
lean::inc(x_1);
x_13 = l_string_iterator_nextn___main(x_1, x_10);
lean::inc(x_13);
x_15 = l_lean_parser_mk__raw__res(x_1, x_13);
x_16 = lean::box(0);
x_17 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_13);
lean::cnstr_set(x_17, 2, x_16);
x_18 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_4);
return x_18;
}
}
obj* l_lean_parser_number__or__string__lit(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_9; obj* x_10; obj* x_12; obj* x_14; 
x_3 = l_lean_parser_number;
x_4 = l_lean_parser_number_x_27___closed__1;
lean::inc(x_1);
lean::inc(x_0);
lean::inc(x_4);
lean::inc(x_3);
x_9 = l_lean_parser_combinators_node___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__15(x_3, x_4, x_0, x_1, x_2);
x_10 = lean::cnstr_get(x_9, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_9, 1);
lean::inc(x_12);
if (lean::is_shared(x_9)) {
 lean::dec(x_9);
 x_14 = lean::box(0);
} else {
 lean::cnstr_release(x_9, 0);
 lean::cnstr_release(x_9, 1);
 x_14 = x_9;
}
if (lean::obj_tag(x_10) == 0)
{
obj* x_17; 
lean::dec(x_1);
lean::dec(x_0);
if (lean::is_scalar(x_14)) {
 x_17 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_17 = x_14;
}
lean::cnstr_set(x_17, 0, x_10);
lean::cnstr_set(x_17, 1, x_12);
return x_17;
}
else
{
obj* x_18; uint8 x_20; 
x_18 = lean::cnstr_get(x_10, 0);
lean::inc(x_18);
x_20 = lean::cnstr_get_scalar<uint8>(x_10, sizeof(void*)*1);
if (x_20 == 0)
{
obj* x_22; obj* x_23; obj* x_26; obj* x_27; obj* x_29; obj* x_32; obj* x_33; 
lean::dec(x_10);
x_22 = l_lean_parser_string__lit;
x_23 = l_lean_parser_string__lit_x_27___closed__1;
lean::inc(x_23);
lean::inc(x_22);
x_26 = l_lean_parser_combinators_node___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__15(x_22, x_23, x_0, x_1, x_12);
x_27 = lean::cnstr_get(x_26, 0);
lean::inc(x_27);
x_29 = lean::cnstr_get(x_26, 1);
lean::inc(x_29);
lean::dec(x_26);
x_32 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_18, x_27);
if (lean::is_scalar(x_14)) {
 x_33 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_33 = x_14;
}
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_29);
return x_33;
}
else
{
obj* x_37; 
lean::dec(x_18);
lean::dec(x_1);
lean::dec(x_0);
if (lean::is_scalar(x_14)) {
 x_37 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_37 = x_14;
}
lean::cnstr_set(x_37, 0, x_10);
lean::cnstr_set(x_37, 1, x_12);
return x_37;
}
}
}
}
obj* l_lean_parser_token__cont(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_6; obj* x_7; obj* x_9; obj* x_11; 
lean::inc(x_2);
x_6 = l___private_init_lean_parser_token_4__ident_x_27(x_2, x_3, x_4);
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_6, 1);
lean::inc(x_9);
if (lean::is_shared(x_6)) {
 lean::dec(x_6);
 x_11 = lean::box(0);
} else {
 lean::cnstr_release(x_6, 0);
 lean::cnstr_release(x_6, 1);
 x_11 = x_6;
}
if (lean::obj_tag(x_7) == 0)
{
obj* x_12; obj* x_14; obj* x_16; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_23; obj* x_25; uint8 x_28; 
x_12 = lean::cnstr_get(x_7, 0);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_7, 1);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_7, 2);
lean::inc(x_16);
if (lean::is_shared(x_7)) {
 lean::dec(x_7);
 x_18 = lean::box(0);
} else {
 lean::cnstr_release(x_7, 0);
 lean::cnstr_release(x_7, 1);
 lean::cnstr_release(x_7, 2);
 x_18 = x_7;
}
x_19 = lean::string_iterator_offset(x_14);
x_20 = lean::string_iterator_offset(x_0);
x_21 = lean::cnstr_get(x_1, 0);
lean::inc(x_21);
x_23 = lean::string_length(x_21);
lean::dec(x_21);
x_25 = lean::nat_add(x_20, x_23);
lean::dec(x_23);
lean::dec(x_20);
x_28 = lean::nat_dec_le(x_19, x_25);
lean::dec(x_25);
lean::dec(x_19);
if (x_28 == 0)
{
obj* x_34; obj* x_36; obj* x_37; obj* x_38; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_34 = l_lean_parser_finish__comment__block___closed__2;
lean::inc(x_34);
if (lean::is_scalar(x_18)) {
 x_36 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_36 = x_18;
}
lean::cnstr_set(x_36, 0, x_12);
lean::cnstr_set(x_36, 1, x_14);
lean::cnstr_set(x_36, 2, x_34);
x_37 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_36);
if (lean::is_scalar(x_11)) {
 x_38 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_38 = x_11;
}
lean::cnstr_set(x_38, 0, x_37);
lean::cnstr_set(x_38, 1, x_9);
return x_38;
}
else
{
obj* x_41; obj* x_42; obj* x_44; obj* x_47; obj* x_49; obj* x_50; obj* x_51; 
lean::dec(x_12);
lean::dec(x_18);
x_41 = l___private_init_lean_parser_token_5__mk__consume__token(x_1, x_0, x_2, x_14, x_9);
x_42 = lean::cnstr_get(x_41, 0);
lean::inc(x_42);
x_44 = lean::cnstr_get(x_41, 1);
lean::inc(x_44);
lean::dec(x_41);
x_47 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_47);
x_49 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_47, x_42);
x_50 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_49);
if (lean::is_scalar(x_11)) {
 x_51 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_51 = x_11;
}
lean::cnstr_set(x_51, 0, x_50);
lean::cnstr_set(x_51, 1, x_44);
return x_51;
}
}
else
{
obj* x_55; uint8 x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_55 = lean::cnstr_get(x_7, 0);
lean::inc(x_55);
x_57 = lean::cnstr_get_scalar<uint8>(x_7, sizeof(void*)*1);
if (lean::is_shared(x_7)) {
 lean::dec(x_7);
 x_58 = lean::box(0);
} else {
 lean::cnstr_release(x_7, 0);
 x_58 = x_7;
}
if (lean::is_scalar(x_58)) {
 x_59 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_59 = x_58;
}
lean::cnstr_set(x_59, 0, x_55);
lean::cnstr_set_scalar(x_59, sizeof(void*)*1, x_57);
x_60 = x_59;
if (lean::is_scalar(x_11)) {
 x_61 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_61 = x_11;
}
lean::cnstr_set(x_61, 0, x_60);
lean::cnstr_set(x_61, 1, x_9);
return x_61;
}
}
}
obj* l_lean_parser_parsec__t_lookahead___at_lean_parser_token___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; uint8 x_6; 
x_6 = lean::string_iterator_has_next(x_1);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_15; obj* x_16; obj* x_18; obj* x_21; obj* x_23; 
x_7 = lean::box(0);
x_8 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_9 = l_mjoin___rarg___closed__1;
lean::inc(x_1);
lean::inc(x_0);
lean::inc(x_7);
lean::inc(x_9);
lean::inc(x_8);
x_15 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_8, x_9, x_7, x_7, x_0, x_1, x_2);
x_16 = lean::cnstr_get(x_15, 0);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_15, 1);
lean::inc(x_18);
lean::dec(x_15);
x_21 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_21);
x_23 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_21, x_16);
if (lean::obj_tag(x_23) == 0)
{
lean::dec(x_0);
x_3 = x_23;
x_4 = x_18;
goto lbl_5;
}
else
{
obj* x_25; uint8 x_27; 
x_25 = lean::cnstr_get(x_23, 0);
lean::inc(x_25);
x_27 = lean::cnstr_get_scalar<uint8>(x_23, sizeof(void*)*1);
if (x_27 == 0)
{
obj* x_29; uint32 x_30; obj* x_32; obj* x_33; obj* x_35; obj* x_38; 
lean::dec(x_23);
x_29 = l_lean_id__begin__escape;
x_30 = lean::unbox_uint32(x_29);
lean::inc(x_1);
x_32 = l_lean_parser_monad__parsec_ch___at___private_init_lean_parser_token_4__ident_x_27___spec__11(x_30, x_0, x_1, x_18);
x_33 = lean::cnstr_get(x_32, 0);
lean::inc(x_33);
x_35 = lean::cnstr_get(x_32, 1);
lean::inc(x_35);
lean::dec(x_32);
x_38 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_25, x_33);
x_3 = x_38;
x_4 = x_35;
goto lbl_5;
}
else
{
lean::dec(x_0);
lean::dec(x_25);
x_3 = x_23;
x_4 = x_18;
goto lbl_5;
}
}
}
else
{
uint32 x_41; uint8 x_42; 
x_41 = lean::string_iterator_curr(x_1);
x_42 = l_lean_is__id__first(x_41);
if (x_42 == 0)
{
obj* x_43; obj* x_44; obj* x_46; obj* x_48; obj* x_49; obj* x_50; obj* x_55; obj* x_56; obj* x_58; obj* x_61; obj* x_63; 
x_43 = l_char_quote__core(x_41);
x_44 = l_char_has__repr___closed__1;
lean::inc(x_44);
x_46 = lean::string_append(x_44, x_43);
lean::dec(x_43);
x_48 = lean::string_append(x_46, x_44);
x_49 = lean::box(0);
x_50 = l_mjoin___rarg___closed__1;
lean::inc(x_1);
lean::inc(x_0);
lean::inc(x_49);
lean::inc(x_50);
x_55 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_48, x_50, x_49, x_49, x_0, x_1, x_2);
x_56 = lean::cnstr_get(x_55, 0);
lean::inc(x_56);
x_58 = lean::cnstr_get(x_55, 1);
lean::inc(x_58);
lean::dec(x_55);
x_61 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_61);
x_63 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_61, x_56);
if (lean::obj_tag(x_63) == 0)
{
lean::dec(x_0);
x_3 = x_63;
x_4 = x_58;
goto lbl_5;
}
else
{
obj* x_65; uint8 x_67; 
x_65 = lean::cnstr_get(x_63, 0);
lean::inc(x_65);
x_67 = lean::cnstr_get_scalar<uint8>(x_63, sizeof(void*)*1);
if (x_67 == 0)
{
obj* x_69; uint32 x_70; obj* x_72; obj* x_73; obj* x_75; obj* x_78; 
lean::dec(x_63);
x_69 = l_lean_id__begin__escape;
x_70 = lean::unbox_uint32(x_69);
lean::inc(x_1);
x_72 = l_lean_parser_monad__parsec_ch___at___private_init_lean_parser_token_4__ident_x_27___spec__11(x_70, x_0, x_1, x_58);
x_73 = lean::cnstr_get(x_72, 0);
lean::inc(x_73);
x_75 = lean::cnstr_get(x_72, 1);
lean::inc(x_75);
lean::dec(x_72);
x_78 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_65, x_73);
x_3 = x_78;
x_4 = x_75;
goto lbl_5;
}
else
{
lean::dec(x_0);
lean::dec(x_65);
x_3 = x_63;
x_4 = x_58;
goto lbl_5;
}
}
}
else
{
obj* x_83; obj* x_84; obj* x_85; obj* x_86; 
lean::dec(x_0);
lean::inc(x_1);
x_83 = lean::string_iterator_next(x_1);
x_84 = lean::box(0);
x_85 = lean::box_uint32(x_41);
x_86 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_86, 0, x_85);
lean::cnstr_set(x_86, 1, x_83);
lean::cnstr_set(x_86, 2, x_84);
x_3 = x_86;
x_4 = x_2;
goto lbl_5;
}
}
lbl_5:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_87; obj* x_89; obj* x_90; obj* x_92; obj* x_93; 
x_87 = lean::cnstr_get(x_3, 0);
lean::inc(x_87);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_89 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 1);
 lean::cnstr_release(x_3, 2);
 x_89 = x_3;
}
x_90 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_90);
if (lean::is_scalar(x_89)) {
 x_92 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_92 = x_89;
}
lean::cnstr_set(x_92, 0, x_87);
lean::cnstr_set(x_92, 1, x_1);
lean::cnstr_set(x_92, 2, x_90);
x_93 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_93, 0, x_92);
lean::cnstr_set(x_93, 1, x_4);
return x_93;
}
else
{
obj* x_95; 
lean::dec(x_1);
x_95 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_95, 0, x_3);
lean::cnstr_set(x_95, 1, x_4);
return x_95;
}
}
}
}
obj* l_lean_parser_monad__parsec_observing___at_lean_parser_token___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_6; obj* x_8; 
x_3 = l_lean_parser_parsec__t_lookahead___at_lean_parser_token___spec__1(x_0, x_1, x_2);
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
obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_16; obj* x_17; obj* x_19; obj* x_20; 
x_9 = lean::cnstr_get(x_4, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_4, 1);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_4, 2);
lean::inc(x_13);
if (lean::is_shared(x_4)) {
 lean::dec(x_4);
 x_15 = lean::box(0);
} else {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_release(x_4, 1);
 lean::cnstr_release(x_4, 2);
 x_15 = x_4;
}
x_16 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_16, 0, x_9);
x_17 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_17);
if (lean::is_scalar(x_15)) {
 x_19 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_19 = x_15;
}
lean::cnstr_set(x_19, 0, x_16);
lean::cnstr_set(x_19, 1, x_11);
lean::cnstr_set(x_19, 2, x_17);
x_20 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_13, x_19);
if (lean::obj_tag(x_20) == 0)
{
obj* x_21; 
if (lean::is_scalar(x_8)) {
 x_21 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_21 = x_8;
}
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_6);
return x_21;
}
else
{
obj* x_22; obj* x_25; obj* x_27; obj* x_29; obj* x_30; 
x_22 = lean::cnstr_get(x_20, 0);
lean::inc(x_22);
lean::dec(x_20);
x_25 = lean::cnstr_get(x_22, 0);
lean::inc(x_25);
x_27 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_27, 0, x_22);
lean::inc(x_17);
x_29 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_29, 0, x_27);
lean::cnstr_set(x_29, 1, x_25);
lean::cnstr_set(x_29, 2, x_17);
if (lean::is_scalar(x_8)) {
 x_30 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_30 = x_8;
}
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_6);
return x_30;
}
}
else
{
obj* x_31; obj* x_34; obj* x_36; obj* x_37; obj* x_39; obj* x_40; 
x_31 = lean::cnstr_get(x_4, 0);
lean::inc(x_31);
lean::dec(x_4);
x_34 = lean::cnstr_get(x_31, 0);
lean::inc(x_34);
x_36 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_36, 0, x_31);
x_37 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_37);
x_39 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_39, 0, x_36);
lean::cnstr_set(x_39, 1, x_34);
lean::cnstr_set(x_39, 2, x_37);
if (lean::is_scalar(x_8)) {
 x_40 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_40 = x_8;
}
lean::cnstr_set(x_40, 0, x_39);
lean::cnstr_set(x_40, 1, x_6);
return x_40;
}
}
}
obj* l_lean_parser_with__trailing___at_lean_parser_token___spec__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; obj* x_6; obj* x_8; obj* x_10; 
lean::inc(x_2);
x_5 = l_lean_parser_whitespace(x_1, x_2, x_3);
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
obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_18; obj* x_20; obj* x_21; obj* x_22; obj* x_24; 
x_11 = lean::cnstr_get(x_6, 1);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_6, 2);
lean::inc(x_13);
if (lean::is_shared(x_6)) {
 lean::dec(x_6);
 x_15 = lean::box(0);
} else {
 lean::cnstr_release(x_6, 0);
 lean::cnstr_release(x_6, 1);
 lean::cnstr_release(x_6, 2);
 x_15 = x_6;
}
lean::inc(x_11);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_2);
lean::cnstr_set(x_17, 1, x_11);
x_18 = l_lean_parser_finish__comment__block___closed__2;
lean::inc(x_18);
if (lean::is_scalar(x_15)) {
 x_20 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_20 = x_15;
}
lean::cnstr_set(x_20, 0, x_17);
lean::cnstr_set(x_20, 1, x_11);
lean::cnstr_set(x_20, 2, x_18);
x_21 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_13, x_20);
x_22 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_22);
x_24 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_22, x_21);
if (lean::obj_tag(x_24) == 0)
{
obj* x_25; obj* x_27; obj* x_29; obj* x_31; obj* x_32; obj* x_34; obj* x_35; obj* x_36; 
x_25 = lean::cnstr_get(x_24, 0);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_24, 1);
lean::inc(x_27);
x_29 = lean::cnstr_get(x_24, 2);
lean::inc(x_29);
if (lean::is_shared(x_24)) {
 lean::dec(x_24);
 x_31 = lean::box(0);
} else {
 lean::cnstr_release(x_24, 0);
 lean::cnstr_release(x_24, 1);
 lean::cnstr_release(x_24, 2);
 x_31 = x_24;
}
x_32 = l___private_init_lean_parser_token_3__update__trailing___main(x_25, x_0);
lean::inc(x_22);
if (lean::is_scalar(x_31)) {
 x_34 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_34 = x_31;
}
lean::cnstr_set(x_34, 0, x_32);
lean::cnstr_set(x_34, 1, x_27);
lean::cnstr_set(x_34, 2, x_22);
x_35 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_29, x_34);
if (lean::is_scalar(x_10)) {
 x_36 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_36 = x_10;
}
lean::cnstr_set(x_36, 0, x_35);
lean::cnstr_set(x_36, 1, x_8);
return x_36;
}
else
{
obj* x_38; uint8 x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; 
lean::dec(x_0);
x_38 = lean::cnstr_get(x_24, 0);
lean::inc(x_38);
x_40 = lean::cnstr_get_scalar<uint8>(x_24, sizeof(void*)*1);
if (lean::is_shared(x_24)) {
 lean::dec(x_24);
 x_41 = lean::box(0);
} else {
 lean::cnstr_release(x_24, 0);
 x_41 = x_24;
}
if (lean::is_scalar(x_41)) {
 x_42 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_42 = x_41;
}
lean::cnstr_set(x_42, 0, x_38);
lean::cnstr_set_scalar(x_42, sizeof(void*)*1, x_40);
x_43 = x_42;
if (lean::is_scalar(x_10)) {
 x_44 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_44 = x_10;
}
lean::cnstr_set(x_44, 0, x_43);
lean::cnstr_set(x_44, 1, x_8);
return x_44;
}
}
else
{
obj* x_46; uint8 x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_54; 
lean::dec(x_2);
x_46 = lean::cnstr_get(x_6, 0);
lean::inc(x_46);
x_48 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*1);
if (lean::is_shared(x_6)) {
 lean::dec(x_6);
 x_49 = lean::box(0);
} else {
 lean::cnstr_release(x_6, 0);
 x_49 = x_6;
}
if (lean::is_scalar(x_49)) {
 x_50 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_50 = x_49;
}
lean::cnstr_set(x_50, 0, x_46);
lean::cnstr_set_scalar(x_50, sizeof(void*)*1, x_48);
x_51 = x_50;
x_52 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_52);
x_54 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_52, x_51);
if (lean::obj_tag(x_54) == 0)
{
obj* x_55; obj* x_57; obj* x_59; obj* x_61; obj* x_62; obj* x_64; obj* x_65; obj* x_66; 
x_55 = lean::cnstr_get(x_54, 0);
lean::inc(x_55);
x_57 = lean::cnstr_get(x_54, 1);
lean::inc(x_57);
x_59 = lean::cnstr_get(x_54, 2);
lean::inc(x_59);
if (lean::is_shared(x_54)) {
 lean::dec(x_54);
 x_61 = lean::box(0);
} else {
 lean::cnstr_release(x_54, 0);
 lean::cnstr_release(x_54, 1);
 lean::cnstr_release(x_54, 2);
 x_61 = x_54;
}
x_62 = l___private_init_lean_parser_token_3__update__trailing___main(x_55, x_0);
lean::inc(x_52);
if (lean::is_scalar(x_61)) {
 x_64 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_64 = x_61;
}
lean::cnstr_set(x_64, 0, x_62);
lean::cnstr_set(x_64, 1, x_57);
lean::cnstr_set(x_64, 2, x_52);
x_65 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_59, x_64);
if (lean::is_scalar(x_10)) {
 x_66 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_66 = x_10;
}
lean::cnstr_set(x_66, 0, x_65);
lean::cnstr_set(x_66, 1, x_8);
return x_66;
}
else
{
obj* x_68; uint8 x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; 
lean::dec(x_0);
x_68 = lean::cnstr_get(x_54, 0);
lean::inc(x_68);
x_70 = lean::cnstr_get_scalar<uint8>(x_54, sizeof(void*)*1);
if (lean::is_shared(x_54)) {
 lean::dec(x_54);
 x_71 = lean::box(0);
} else {
 lean::cnstr_release(x_54, 0);
 x_71 = x_54;
}
if (lean::is_scalar(x_71)) {
 x_72 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_72 = x_71;
}
lean::cnstr_set(x_72, 0, x_68);
lean::cnstr_set_scalar(x_72, sizeof(void*)*1, x_70);
x_73 = x_72;
if (lean::is_scalar(x_10)) {
 x_74 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_74 = x_10;
}
lean::cnstr_set(x_74, 0, x_73);
lean::cnstr_set(x_74, 1, x_8);
return x_74;
}
}
}
}
obj* l_lean_parser_parsec__t_failure___at_lean_parser_token___spec__4___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_7; uint8 x_8; obj* x_9; obj* x_10; obj* x_11; 
x_2 = lean::box(0);
x_3 = l_lean_parser_parsec__t_failure___rarg___closed__1;
x_4 = l_mjoin___rarg___closed__1;
lean::inc(x_4);
lean::inc(x_3);
x_7 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_7, 0, x_0);
lean::cnstr_set(x_7, 1, x_3);
lean::cnstr_set(x_7, 2, x_4);
lean::cnstr_set(x_7, 3, x_2);
x_8 = 0;
x_9 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set_scalar(x_9, sizeof(void*)*1, x_8);
x_10 = x_9;
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_1);
return x_11;
}
}
obj* l_lean_parser_parsec__t_failure___at_lean_parser_token___spec__4(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parsec__t_failure___at_lean_parser_token___spec__4___rarg), 2, 0);
return x_4;
}
}
obj* _init_l_lean_parser_token___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("token: not implemented");
return x_0;
}
}
obj* l_lean_parser_token(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_6; 
x_6 = lean::cnstr_get(x_2, 0);
lean::inc(x_6);
if (lean::obj_tag(x_6) == 0)
{
obj* x_11; obj* x_12; obj* x_14; obj* x_17; obj* x_19; 
lean::dec(x_6);
lean::inc(x_2);
lean::inc(x_1);
x_11 = l_lean_parser_parsec__t_failure___at_lean_parser_token___spec__4___rarg(x_1, x_2);
x_12 = lean::cnstr_get(x_11, 0);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_11, 1);
lean::inc(x_14);
lean::dec(x_11);
x_17 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_17);
x_19 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_17, x_12);
x_3 = x_19;
x_4 = x_14;
goto lbl_5;
}
else
{
obj* x_20; obj* x_22; obj* x_23; obj* x_25; uint8 x_27; 
x_20 = lean::cnstr_get(x_6, 0);
lean::inc(x_20);
x_22 = lean::string_iterator_offset(x_1);
x_23 = lean::cnstr_get(x_20, 0);
lean::inc(x_23);
x_25 = lean::string_iterator_offset(x_23);
lean::dec(x_23);
x_27 = lean::nat_dec_eq(x_22, x_25);
lean::dec(x_25);
lean::dec(x_22);
if (x_27 == 0)
{
obj* x_32; obj* x_33; obj* x_35; 
lean::inc(x_2);
lean::inc(x_1);
x_32 = l_lean_parser_parsec__t_failure___at_lean_parser_token___spec__4___rarg(x_1, x_2);
x_33 = lean::cnstr_get(x_32, 0);
lean::inc(x_33);
x_35 = lean::cnstr_get(x_32, 1);
lean::inc(x_35);
lean::dec(x_32);
if (lean::obj_tag(x_33) == 0)
{
obj* x_39; obj* x_41; obj* x_42; obj* x_44; obj* x_45; obj* x_47; obj* x_48; obj* x_51; obj* x_53; obj* x_54; obj* x_57; obj* x_58; obj* x_59; obj* x_61; 
lean::dec(x_35);
x_39 = lean::cnstr_get(x_33, 2);
lean::inc(x_39);
if (lean::is_shared(x_33)) {
 lean::dec(x_33);
 x_41 = lean::box(0);
} else {
 lean::cnstr_release(x_33, 0);
 lean::cnstr_release(x_33, 1);
 lean::cnstr_release(x_33, 2);
 x_41 = x_33;
}
x_42 = lean::cnstr_get(x_20, 1);
lean::inc(x_42);
x_44 = lean::box(0);
x_45 = lean::cnstr_get(x_2, 1);
lean::inc(x_45);
x_47 = lean::mk_nat_obj(1u);
x_48 = lean::nat_add(x_45, x_47);
lean::dec(x_47);
lean::dec(x_45);
x_51 = lean::cnstr_get(x_2, 2);
lean::inc(x_51);
x_53 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_53, 0, x_6);
lean::cnstr_set(x_53, 1, x_48);
lean::cnstr_set(x_53, 2, x_51);
x_54 = lean::cnstr_get(x_20, 2);
lean::inc(x_54);
lean::dec(x_20);
if (lean::is_scalar(x_41)) {
 x_57 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_57 = x_41;
}
lean::cnstr_set(x_57, 0, x_54);
lean::cnstr_set(x_57, 1, x_42);
lean::cnstr_set(x_57, 2, x_44);
x_58 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_39, x_57);
x_59 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_59);
x_61 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_59, x_58);
x_3 = x_61;
x_4 = x_53;
goto lbl_5;
}
else
{
obj* x_64; uint8 x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_72; 
lean::dec(x_6);
lean::dec(x_20);
x_64 = lean::cnstr_get(x_33, 0);
lean::inc(x_64);
x_66 = lean::cnstr_get_scalar<uint8>(x_33, sizeof(void*)*1);
if (lean::is_shared(x_33)) {
 lean::dec(x_33);
 x_67 = lean::box(0);
} else {
 lean::cnstr_release(x_33, 0);
 x_67 = x_33;
}
if (lean::is_scalar(x_67)) {
 x_68 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_68 = x_67;
}
lean::cnstr_set(x_68, 0, x_64);
lean::cnstr_set_scalar(x_68, sizeof(void*)*1, x_66);
x_69 = x_68;
x_70 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_70);
x_72 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_70, x_69);
x_3 = x_72;
x_4 = x_35;
goto lbl_5;
}
}
else
{
obj* x_73; obj* x_75; obj* x_76; obj* x_78; obj* x_79; obj* x_82; obj* x_84; obj* x_85; obj* x_88; 
x_73 = lean::cnstr_get(x_20, 1);
lean::inc(x_73);
x_75 = lean::box(0);
x_76 = lean::cnstr_get(x_2, 1);
lean::inc(x_76);
x_78 = lean::mk_nat_obj(1u);
x_79 = lean::nat_add(x_76, x_78);
lean::dec(x_78);
lean::dec(x_76);
x_82 = lean::cnstr_get(x_2, 2);
lean::inc(x_82);
x_84 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_84, 0, x_6);
lean::cnstr_set(x_84, 1, x_79);
lean::cnstr_set(x_84, 2, x_82);
x_85 = lean::cnstr_get(x_20, 2);
lean::inc(x_85);
lean::dec(x_20);
x_88 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_88, 0, x_85);
lean::cnstr_set(x_88, 1, x_73);
lean::cnstr_set(x_88, 2, x_75);
x_3 = x_88;
x_4 = x_84;
goto lbl_5;
}
}
lbl_5:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_92; obj* x_94; obj* x_96; obj* x_97; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_92 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_92);
x_94 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_92, x_3);
lean::inc(x_92);
x_96 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_92, x_94);
x_97 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_97, 0, x_96);
lean::cnstr_set(x_97, 1, x_4);
return x_97;
}
else
{
obj* x_98; uint8 x_100; obj* x_101; obj* x_102; obj* x_103; obj* x_105; obj* x_109; obj* x_110; obj* x_112; 
x_98 = lean::cnstr_get(x_3, 0);
lean::inc(x_98);
x_100 = lean::cnstr_get_scalar<uint8>(x_3, sizeof(void*)*1);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_101 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 x_101 = x_3;
}
x_105 = lean::cnstr_get(x_98, 0);
lean::inc(x_105);
lean::dec(x_98);
lean::inc(x_0);
x_109 = l_lean_parser_monad__parsec_observing___at_lean_parser_token___spec__2(x_0, x_105, x_4);
x_110 = lean::cnstr_get(x_109, 0);
lean::inc(x_110);
x_112 = lean::cnstr_get(x_109, 1);
lean::inc(x_112);
lean::dec(x_109);
if (lean::obj_tag(x_110) == 0)
{
obj* x_115; obj* x_117; obj* x_119; obj* x_121; obj* x_123; obj* x_124; obj* x_126; 
x_115 = lean::cnstr_get(x_110, 0);
lean::inc(x_115);
x_117 = lean::cnstr_get(x_110, 1);
lean::inc(x_117);
x_119 = lean::cnstr_get(x_110, 2);
lean::inc(x_119);
if (lean::is_shared(x_110)) {
 lean::dec(x_110);
 x_121 = lean::box(0);
} else {
 lean::cnstr_release(x_110, 0);
 lean::cnstr_release(x_110, 1);
 lean::cnstr_release(x_110, 2);
 x_121 = x_110;
}
lean::inc(x_0);
x_123 = l_lean_parser_match__token(x_0, x_117, x_112);
x_124 = lean::cnstr_get(x_123, 0);
lean::inc(x_124);
x_126 = lean::cnstr_get(x_123, 1);
lean::inc(x_126);
lean::dec(x_123);
if (lean::obj_tag(x_124) == 0)
{
obj* x_129; obj* x_131; obj* x_133; obj* x_136; obj* x_137; obj* x_139; 
x_129 = lean::cnstr_get(x_124, 0);
lean::inc(x_129);
x_131 = lean::cnstr_get(x_124, 1);
lean::inc(x_131);
x_133 = lean::cnstr_get(x_124, 2);
lean::inc(x_133);
lean::dec(x_124);
if (lean::obj_tag(x_129) == 0)
{
lean::dec(x_129);
if (lean::obj_tag(x_115) == 0)
{
obj* x_144; obj* x_145; obj* x_147; 
lean::dec(x_115);
lean::inc(x_0);
x_144 = l_lean_parser_number__or__string__lit(x_0, x_131, x_126);
x_145 = lean::cnstr_get(x_144, 0);
lean::inc(x_145);
x_147 = lean::cnstr_get(x_144, 1);
lean::inc(x_147);
lean::dec(x_144);
x_136 = x_145;
x_137 = x_147;
goto lbl_138;
}
else
{
obj* x_152; obj* x_153; obj* x_155; 
lean::dec(x_115);
lean::inc(x_0);
x_152 = l___private_init_lean_parser_token_4__ident_x_27(x_0, x_131, x_126);
x_153 = lean::cnstr_get(x_152, 0);
lean::inc(x_153);
x_155 = lean::cnstr_get(x_152, 1);
lean::inc(x_155);
lean::dec(x_152);
x_136 = x_153;
x_137 = x_155;
goto lbl_138;
}
}
else
{
obj* x_158; obj* x_161; 
x_158 = lean::cnstr_get(x_129, 0);
lean::inc(x_158);
lean::dec(x_129);
x_161 = lean::cnstr_get(x_158, 2);
lean::inc(x_161);
if (lean::obj_tag(x_161) == 0)
{
lean::dec(x_161);
if (lean::obj_tag(x_115) == 0)
{
obj* x_167; obj* x_168; obj* x_170; 
lean::dec(x_115);
lean::inc(x_0);
lean::inc(x_1);
x_167 = l___private_init_lean_parser_token_5__mk__consume__token(x_158, x_1, x_0, x_131, x_126);
x_168 = lean::cnstr_get(x_167, 0);
lean::inc(x_168);
x_170 = lean::cnstr_get(x_167, 1);
lean::inc(x_170);
lean::dec(x_167);
x_136 = x_168;
x_137 = x_170;
goto lbl_138;
}
else
{
obj* x_176; obj* x_177; obj* x_179; 
lean::dec(x_115);
lean::inc(x_0);
lean::inc(x_1);
x_176 = l_lean_parser_token__cont(x_1, x_158, x_0, x_131, x_126);
x_177 = lean::cnstr_get(x_176, 0);
lean::inc(x_177);
x_179 = lean::cnstr_get(x_176, 1);
lean::inc(x_179);
lean::dec(x_176);
x_136 = x_177;
x_137 = x_179;
goto lbl_138;
}
}
else
{
obj* x_185; 
lean::dec(x_161);
lean::dec(x_158);
lean::dec(x_115);
x_185 = lean::box(0);
x_139 = x_185;
goto lbl_140;
}
}
lbl_138:
{
if (lean::obj_tag(x_136) == 0)
{
obj* x_186; obj* x_188; obj* x_190; obj* x_193; obj* x_194; obj* x_196; 
x_186 = lean::cnstr_get(x_136, 0);
lean::inc(x_186);
x_188 = lean::cnstr_get(x_136, 1);
lean::inc(x_188);
x_190 = lean::cnstr_get(x_136, 2);
lean::inc(x_190);
lean::dec(x_136);
x_193 = l_lean_parser_with__trailing___at_lean_parser_token___spec__3(x_186, x_0, x_188, x_137);
x_194 = lean::cnstr_get(x_193, 0);
lean::inc(x_194);
x_196 = lean::cnstr_get(x_193, 1);
lean::inc(x_196);
lean::dec(x_193);
if (lean::obj_tag(x_194) == 0)
{
obj* x_200; obj* x_202; obj* x_204; obj* x_209; obj* x_210; obj* x_211; obj* x_213; obj* x_216; obj* x_217; obj* x_220; obj* x_221; obj* x_223; obj* x_224; obj* x_225; obj* x_226; obj* x_227; 
lean::dec(x_196);
x_200 = lean::cnstr_get(x_194, 0);
lean::inc(x_200);
x_202 = lean::cnstr_get(x_194, 1);
lean::inc(x_202);
x_204 = lean::cnstr_get(x_194, 2);
lean::inc(x_204);
lean::dec(x_194);
lean::inc(x_200);
lean::inc(x_202);
x_209 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_209, 0, x_1);
lean::cnstr_set(x_209, 1, x_202);
lean::cnstr_set(x_209, 2, x_200);
x_210 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_210, 0, x_209);
x_211 = lean::cnstr_get(x_2, 1);
lean::inc(x_211);
x_213 = lean::cnstr_get(x_2, 2);
lean::inc(x_213);
lean::dec(x_2);
x_216 = lean::mk_nat_obj(1u);
x_217 = lean::nat_add(x_213, x_216);
lean::dec(x_216);
lean::dec(x_213);
x_220 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_220, 0, x_210);
lean::cnstr_set(x_220, 1, x_211);
lean::cnstr_set(x_220, 2, x_217);
x_221 = l_lean_parser_match__token___closed__2;
lean::inc(x_221);
if (lean::is_scalar(x_121)) {
 x_223 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_223 = x_121;
}
lean::cnstr_set(x_223, 0, x_200);
lean::cnstr_set(x_223, 1, x_202);
lean::cnstr_set(x_223, 2, x_221);
x_224 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_204, x_223);
x_225 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_190, x_224);
x_226 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_133, x_225);
x_227 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_119, x_226);
x_102 = x_227;
x_103 = x_220;
goto lbl_104;
}
else
{
obj* x_231; uint8 x_233; obj* x_234; obj* x_235; obj* x_236; obj* x_237; obj* x_238; obj* x_239; 
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_121);
x_231 = lean::cnstr_get(x_194, 0);
lean::inc(x_231);
x_233 = lean::cnstr_get_scalar<uint8>(x_194, sizeof(void*)*1);
if (lean::is_shared(x_194)) {
 lean::dec(x_194);
 x_234 = lean::box(0);
} else {
 lean::cnstr_release(x_194, 0);
 x_234 = x_194;
}
if (lean::is_scalar(x_234)) {
 x_235 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_235 = x_234;
}
lean::cnstr_set(x_235, 0, x_231);
lean::cnstr_set_scalar(x_235, sizeof(void*)*1, x_233);
x_236 = x_235;
x_237 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_190, x_236);
x_238 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_133, x_237);
x_239 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_119, x_238);
x_102 = x_239;
x_103 = x_196;
goto lbl_104;
}
}
else
{
obj* x_244; uint8 x_246; obj* x_247; obj* x_248; obj* x_249; obj* x_250; obj* x_251; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_121);
x_244 = lean::cnstr_get(x_136, 0);
lean::inc(x_244);
x_246 = lean::cnstr_get_scalar<uint8>(x_136, sizeof(void*)*1);
if (lean::is_shared(x_136)) {
 lean::dec(x_136);
 x_247 = lean::box(0);
} else {
 lean::cnstr_release(x_136, 0);
 x_247 = x_136;
}
if (lean::is_scalar(x_247)) {
 x_248 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_248 = x_247;
}
lean::cnstr_set(x_248, 0, x_244);
lean::cnstr_set_scalar(x_248, sizeof(void*)*1, x_246);
x_249 = x_248;
x_250 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_133, x_249);
x_251 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_119, x_250);
x_102 = x_251;
x_103 = x_137;
goto lbl_104;
}
}
lbl_140:
{
obj* x_253; obj* x_254; obj* x_255; obj* x_260; obj* x_261; obj* x_263; 
lean::dec(x_139);
x_253 = lean::box(0);
x_254 = l_lean_parser_token___closed__1;
x_255 = l_mjoin___rarg___closed__1;
lean::inc(x_0);
lean::inc(x_253);
lean::inc(x_255);
lean::inc(x_254);
x_260 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_254, x_255, x_253, x_253, x_0, x_131, x_126);
x_261 = lean::cnstr_get(x_260, 0);
lean::inc(x_261);
x_263 = lean::cnstr_get(x_260, 1);
lean::inc(x_263);
lean::dec(x_260);
x_136 = x_261;
x_137 = x_263;
goto lbl_138;
}
}
else
{
obj* x_271; uint8 x_273; obj* x_274; obj* x_275; obj* x_276; obj* x_277; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_115);
lean::dec(x_121);
x_271 = lean::cnstr_get(x_124, 0);
lean::inc(x_271);
x_273 = lean::cnstr_get_scalar<uint8>(x_124, sizeof(void*)*1);
if (lean::is_shared(x_124)) {
 lean::dec(x_124);
 x_274 = lean::box(0);
} else {
 lean::cnstr_release(x_124, 0);
 x_274 = x_124;
}
if (lean::is_scalar(x_274)) {
 x_275 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_275 = x_274;
}
lean::cnstr_set(x_275, 0, x_271);
lean::cnstr_set_scalar(x_275, sizeof(void*)*1, x_273);
x_276 = x_275;
x_277 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_119, x_276);
x_102 = x_277;
x_103 = x_126;
goto lbl_104;
}
}
else
{
obj* x_281; uint8 x_283; obj* x_284; obj* x_285; obj* x_286; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_281 = lean::cnstr_get(x_110, 0);
lean::inc(x_281);
x_283 = lean::cnstr_get_scalar<uint8>(x_110, sizeof(void*)*1);
if (lean::is_shared(x_110)) {
 lean::dec(x_110);
 x_284 = lean::box(0);
} else {
 lean::cnstr_release(x_110, 0);
 x_284 = x_110;
}
if (lean::is_scalar(x_284)) {
 x_285 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_285 = x_284;
}
lean::cnstr_set(x_285, 0, x_281);
lean::cnstr_set_scalar(x_285, sizeof(void*)*1, x_283);
x_286 = x_285;
x_102 = x_286;
x_103 = x_112;
goto lbl_104;
}
lbl_104:
{
if (lean::obj_tag(x_102) == 0)
{
obj* x_288; obj* x_290; obj* x_292; obj* x_293; 
lean::dec(x_101);
x_288 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_288);
x_290 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_288, x_102);
lean::inc(x_288);
x_292 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_288, x_290);
x_293 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_293, 0, x_292);
lean::cnstr_set(x_293, 1, x_103);
return x_293;
}
else
{
obj* x_294; uint8 x_296; 
x_294 = lean::cnstr_get(x_102, 0);
lean::inc(x_294);
x_296 = lean::cnstr_get_scalar<uint8>(x_102, sizeof(void*)*1);
lean::dec(x_102);
if (x_100 == 0)
{
obj* x_298; obj* x_299; obj* x_300; obj* x_302; obj* x_304; obj* x_305; 
if (lean::is_scalar(x_101)) {
 x_298 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_298 = x_101;
}
lean::cnstr_set(x_298, 0, x_294);
lean::cnstr_set_scalar(x_298, sizeof(void*)*1, x_296);
x_299 = x_298;
x_300 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_300);
x_302 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_300, x_299);
lean::inc(x_300);
x_304 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_300, x_302);
x_305 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_305, 0, x_304);
lean::cnstr_set(x_305, 1, x_103);
return x_305;
}
else
{
obj* x_306; obj* x_307; obj* x_308; obj* x_310; obj* x_312; obj* x_313; 
if (lean::is_scalar(x_101)) {
 x_306 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_306 = x_101;
}
lean::cnstr_set(x_306, 0, x_294);
lean::cnstr_set_scalar(x_306, sizeof(void*)*1, x_100);
x_307 = x_306;
x_308 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_308);
x_310 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_308, x_307);
lean::inc(x_308);
x_312 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_308, x_310);
x_313 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_313, 0, x_312);
lean::cnstr_set(x_313, 1, x_103);
return x_313;
}
}
}
}
}
}
}
obj* l_lean_parser_parsec__t_lookahead___at_lean_parser_peek__token___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_5; obj* x_7; obj* x_9; 
lean::inc(x_1);
x_4 = l_lean_parser_token(x_0, x_1, x_2);
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
obj* x_10; obj* x_12; obj* x_13; obj* x_15; obj* x_16; 
x_10 = lean::cnstr_get(x_5, 0);
lean::inc(x_10);
if (lean::is_shared(x_5)) {
 lean::dec(x_5);
 x_12 = lean::box(0);
} else {
 lean::cnstr_release(x_5, 0);
 lean::cnstr_release(x_5, 1);
 lean::cnstr_release(x_5, 2);
 x_12 = x_5;
}
x_13 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_13);
if (lean::is_scalar(x_12)) {
 x_15 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_15 = x_12;
}
lean::cnstr_set(x_15, 0, x_10);
lean::cnstr_set(x_15, 1, x_1);
lean::cnstr_set(x_15, 2, x_13);
if (lean::is_scalar(x_9)) {
 x_16 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_16 = x_9;
}
lean::cnstr_set(x_16, 0, x_15);
lean::cnstr_set(x_16, 1, x_7);
return x_16;
}
else
{
obj* x_18; 
lean::dec(x_1);
if (lean::is_scalar(x_9)) {
 x_18 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_18 = x_9;
}
lean::cnstr_set(x_18, 0, x_5);
lean::cnstr_set(x_18, 1, x_7);
return x_18;
}
}
}
obj* l_lean_parser_monad__parsec_observing___at_lean_parser_peek__token___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_6; obj* x_8; obj* x_9; 
x_3 = l_lean_parser_parsec__t_lookahead___at_lean_parser_peek__token___spec__1(x_0, x_1, x_2);
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
x_9 = l_lean_parser_parsec__t_try__mk__res___rarg(x_4);
if (lean::obj_tag(x_9) == 0)
{
obj* x_10; obj* x_12; obj* x_14; obj* x_16; obj* x_17; obj* x_18; obj* x_20; obj* x_21; 
x_10 = lean::cnstr_get(x_9, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_9, 1);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_9, 2);
lean::inc(x_14);
if (lean::is_shared(x_9)) {
 lean::dec(x_9);
 x_16 = lean::box(0);
} else {
 lean::cnstr_release(x_9, 0);
 lean::cnstr_release(x_9, 1);
 lean::cnstr_release(x_9, 2);
 x_16 = x_9;
}
x_17 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_17, 0, x_10);
x_18 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_18);
if (lean::is_scalar(x_16)) {
 x_20 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_20 = x_16;
}
lean::cnstr_set(x_20, 0, x_17);
lean::cnstr_set(x_20, 1, x_12);
lean::cnstr_set(x_20, 2, x_18);
x_21 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_14, x_20);
if (lean::obj_tag(x_21) == 0)
{
obj* x_22; 
if (lean::is_scalar(x_8)) {
 x_22 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_22 = x_8;
}
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_6);
return x_22;
}
else
{
obj* x_23; obj* x_26; obj* x_28; obj* x_30; obj* x_31; 
x_23 = lean::cnstr_get(x_21, 0);
lean::inc(x_23);
lean::dec(x_21);
x_26 = lean::cnstr_get(x_23, 0);
lean::inc(x_26);
x_28 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_28, 0, x_23);
lean::inc(x_18);
x_30 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_30, 0, x_28);
lean::cnstr_set(x_30, 1, x_26);
lean::cnstr_set(x_30, 2, x_18);
if (lean::is_scalar(x_8)) {
 x_31 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_31 = x_8;
}
lean::cnstr_set(x_31, 0, x_30);
lean::cnstr_set(x_31, 1, x_6);
return x_31;
}
}
else
{
obj* x_32; obj* x_35; obj* x_37; obj* x_38; obj* x_40; obj* x_41; 
x_32 = lean::cnstr_get(x_9, 0);
lean::inc(x_32);
lean::dec(x_9);
x_35 = lean::cnstr_get(x_32, 0);
lean::inc(x_35);
x_37 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_37, 0, x_32);
x_38 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_38);
x_40 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_40, 0, x_37);
lean::cnstr_set(x_40, 1, x_35);
lean::cnstr_set(x_40, 2, x_38);
if (lean::is_scalar(x_8)) {
 x_41 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_41 = x_8;
}
lean::cnstr_set(x_41, 0, x_40);
lean::cnstr_set(x_41, 1, x_6);
return x_41;
}
}
}
obj* l_lean_parser_peek__token(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_parser_monad__parsec_observing___at_lean_parser_peek__token___spec__2(x_0, x_1, x_2);
return x_3;
}
}
obj* l_lean_parser_symbol__core___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_8; obj* x_9; obj* x_11; obj* x_13; 
lean::inc(x_4);
lean::inc(x_3);
x_8 = l_lean_parser_token(x_3, x_4, x_5);
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
if (lean::is_shared(x_8)) {
 lean::dec(x_8);
 x_13 = lean::box(0);
} else {
 lean::cnstr_release(x_8, 0);
 lean::cnstr_release(x_8, 1);
 x_13 = x_8;
}
if (lean::obj_tag(x_9) == 0)
{
obj* x_14; obj* x_16; obj* x_18; obj* x_20; obj* x_21; 
x_14 = lean::cnstr_get(x_9, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_9, 1);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_9, 2);
lean::inc(x_18);
if (lean::is_shared(x_9)) {
 lean::dec(x_9);
 x_20 = lean::box(0);
} else {
 lean::cnstr_release(x_9, 0);
 lean::cnstr_release(x_9, 1);
 lean::cnstr_release(x_9, 2);
 x_20 = x_9;
}
switch (lean::obj_tag(x_14)) {
case 0:
{
obj* x_24; obj* x_26; uint8 x_29; 
lean::dec(x_13);
x_24 = lean::cnstr_get(x_14, 0);
lean::inc(x_24);
x_26 = lean::cnstr_get(x_24, 1);
lean::inc(x_26);
lean::dec(x_24);
x_29 = lean::string_dec_eq(x_2, x_26);
lean::dec(x_2);
if (x_29 == 0)
{
obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_36; obj* x_38; 
x_31 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_31, 0, x_4);
x_32 = lean::box(0);
x_33 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_26, x_0, x_31, x_32, x_3, x_16, x_11);
x_34 = lean::cnstr_get(x_33, 0);
lean::inc(x_34);
x_36 = lean::cnstr_get(x_33, 1);
lean::inc(x_36);
if (lean::is_shared(x_33)) {
 lean::dec(x_33);
 x_38 = lean::box(0);
} else {
 lean::cnstr_release(x_33, 0);
 lean::cnstr_release(x_33, 1);
 x_38 = x_33;
}
if (lean::obj_tag(x_34) == 0)
{
obj* x_39; obj* x_41; obj* x_44; obj* x_46; obj* x_47; obj* x_48; obj* x_50; obj* x_51; obj* x_52; obj* x_53; 
x_39 = lean::cnstr_get(x_34, 1);
lean::inc(x_39);
x_41 = lean::cnstr_get(x_34, 2);
lean::inc(x_41);
lean::dec(x_34);
x_44 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_44);
if (lean::is_scalar(x_20)) {
 x_46 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_46 = x_20;
}
lean::cnstr_set(x_46, 0, x_14);
lean::cnstr_set(x_46, 1, x_39);
lean::cnstr_set(x_46, 2, x_44);
x_47 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_41, x_46);
x_48 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_18, x_47);
lean::inc(x_44);
x_50 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_44, x_48);
x_51 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_50, x_1);
x_52 = l_lean_parser_parsec__t_try__mk__res___rarg(x_51);
if (lean::is_scalar(x_38)) {
 x_53 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_53 = x_38;
}
lean::cnstr_set(x_53, 0, x_52);
lean::cnstr_set(x_53, 1, x_36);
return x_53;
}
else
{
obj* x_56; uint8 x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_65; obj* x_66; obj* x_67; obj* x_68; 
lean::dec(x_14);
lean::dec(x_20);
x_56 = lean::cnstr_get(x_34, 0);
lean::inc(x_56);
x_58 = lean::cnstr_get_scalar<uint8>(x_34, sizeof(void*)*1);
if (lean::is_shared(x_34)) {
 lean::dec(x_34);
 x_59 = lean::box(0);
} else {
 lean::cnstr_release(x_34, 0);
 x_59 = x_34;
}
if (lean::is_scalar(x_59)) {
 x_60 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_60 = x_59;
}
lean::cnstr_set(x_60, 0, x_56);
lean::cnstr_set_scalar(x_60, sizeof(void*)*1, x_58);
x_61 = x_60;
x_62 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_18, x_61);
x_63 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_63);
x_65 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_63, x_62);
x_66 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_65, x_1);
x_67 = l_lean_parser_parsec__t_try__mk__res___rarg(x_66);
if (lean::is_scalar(x_38)) {
 x_68 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_68 = x_38;
}
lean::cnstr_set(x_68, 0, x_67);
lean::cnstr_set(x_68, 1, x_36);
return x_68;
}
}
else
{
obj* x_73; obj* x_75; obj* x_76; obj* x_77; obj* x_79; obj* x_80; obj* x_81; obj* x_82; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_26);
x_73 = l_lean_parser_finish__comment__block___closed__2;
lean::inc(x_73);
if (lean::is_scalar(x_20)) {
 x_75 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_75 = x_20;
}
lean::cnstr_set(x_75, 0, x_14);
lean::cnstr_set(x_75, 1, x_16);
lean::cnstr_set(x_75, 2, x_73);
x_76 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_18, x_75);
x_77 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_77);
x_79 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_77, x_76);
x_80 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_79, x_1);
x_81 = l_lean_parser_parsec__t_try__mk__res___rarg(x_80);
x_82 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_82, 0, x_81);
lean::cnstr_set(x_82, 1, x_11);
return x_82;
}
}
case 1:
{
obj* x_86; 
lean::dec(x_14);
lean::dec(x_20);
lean::dec(x_2);
x_86 = lean::box(0);
x_21 = x_86;
goto lbl_22;
}
case 2:
{
obj* x_90; 
lean::dec(x_14);
lean::dec(x_20);
lean::dec(x_2);
x_90 = lean::box(0);
x_21 = x_90;
goto lbl_22;
}
default:
{
obj* x_94; 
lean::dec(x_14);
lean::dec(x_20);
lean::dec(x_2);
x_94 = lean::box(0);
x_21 = x_94;
goto lbl_22;
}
}
lbl_22:
{
obj* x_96; obj* x_97; obj* x_98; obj* x_100; obj* x_101; obj* x_103; obj* x_106; obj* x_107; obj* x_109; obj* x_110; obj* x_111; obj* x_112; 
lean::dec(x_21);
x_96 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_96, 0, x_4);
x_97 = lean::box(0);
x_98 = l_string_join___closed__1;
lean::inc(x_98);
x_100 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_98, x_0, x_96, x_97, x_3, x_16, x_11);
x_101 = lean::cnstr_get(x_100, 0);
lean::inc(x_101);
x_103 = lean::cnstr_get(x_100, 1);
lean::inc(x_103);
lean::dec(x_100);
x_106 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_18, x_101);
x_107 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_107);
x_109 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_107, x_106);
x_110 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_109, x_1);
x_111 = l_lean_parser_parsec__t_try__mk__res___rarg(x_110);
if (lean::is_scalar(x_13)) {
 x_112 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_112 = x_13;
}
lean::cnstr_set(x_112, 0, x_111);
lean::cnstr_set(x_112, 1, x_103);
return x_112;
}
}
else
{
obj* x_117; uint8 x_119; obj* x_120; obj* x_121; obj* x_122; obj* x_123; obj* x_125; obj* x_126; obj* x_127; obj* x_128; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
x_117 = lean::cnstr_get(x_9, 0);
lean::inc(x_117);
x_119 = lean::cnstr_get_scalar<uint8>(x_9, sizeof(void*)*1);
if (lean::is_shared(x_9)) {
 lean::dec(x_9);
 x_120 = lean::box(0);
} else {
 lean::cnstr_release(x_9, 0);
 x_120 = x_9;
}
if (lean::is_scalar(x_120)) {
 x_121 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_121 = x_120;
}
lean::cnstr_set(x_121, 0, x_117);
lean::cnstr_set_scalar(x_121, sizeof(void*)*1, x_119);
x_122 = x_121;
x_123 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_123);
x_125 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_123, x_122);
x_126 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_125, x_1);
x_127 = l_lean_parser_parsec__t_try__mk__res___rarg(x_126);
if (lean::is_scalar(x_13)) {
 x_128 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_128 = x_13;
}
lean::cnstr_set(x_128, 0, x_127);
lean::cnstr_set(x_128, 1, x_11);
return x_128;
}
}
}
obj* l_lean_parser_symbol__core___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; 
lean::dec(x_2);
lean::inc(x_1);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_6, 0, x_1);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___rarg___lambda__1), 6, 3);
lean::closure_set(x_7, 0, x_3);
lean::closure_set(x_7, 1, x_6);
lean::closure_set(x_7, 2, x_1);
x_8 = lean::apply_2(x_0, lean::box(0), x_7);
return x_8;
}
}
obj* l_lean_parser_symbol__core(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___rarg), 4, 0);
return x_2;
}
}
obj* l_lean_parser_symbol___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_6; 
x_3 = l_string_trim(x_1);
lean::inc(x_3);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_5, 0, x_3);
x_6 = l_lean_parser_symbol__core___rarg(x_0, x_3, x_2, x_5);
return x_6;
}
}
obj* l_lean_parser_symbol(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol___rarg), 3, 0);
return x_2;
}
}
obj* l_lean_parser_symbol_tokens___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_5; obj* x_6; 
x_2 = l_string_trim(x_0);
x_3 = lean::box(0);
lean::inc(x_3);
x_5 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_5, 0, x_2);
lean::cnstr_set(x_5, 1, x_1);
lean::cnstr_set(x_5, 2, x_3);
x_6 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_3);
return x_6;
}
}
obj* l_lean_parser_symbol_tokens(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol_tokens___rarg), 2, 0);
return x_4;
}
}
obj* l_lean_parser_symbol_view___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; obj* x_7; obj* x_10; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = l_lean_parser_raw_view___rarg___closed__1;
x_7 = l_lean_parser_raw_view___rarg___closed__2;
lean::inc(x_7);
lean::inc(x_6);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_6);
lean::cnstr_set(x_10, 1, x_7);
return x_10;
}
}
obj* l_lean_parser_symbol_view(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol_view___rarg), 3, 0);
return x_2;
}
}
obj* l_lean_parser_symbol_view__default___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::box(0);
return x_6;
}
}
obj* l_lean_parser_symbol_view__default(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol_view__default___rarg), 3, 0);
return x_2;
}
}
obj* l_lean_parser_try__view___at_lean_parser_number_parser___spec__1(obj* x_0) {
_start:
{
obj* x_1; uint8 x_4; 
x_1 = l_lean_parser_number;
lean::inc(x_0);
lean::inc(x_1);
x_4 = l_lean_parser_syntax_is__of__kind___main(x_1, x_0);
if (x_4 == 0)
{
obj* x_6; 
lean::dec(x_0);
x_6 = lean::box(0);
return x_6;
}
else
{
obj* x_7; obj* x_8; obj* x_10; obj* x_11; 
x_7 = l_lean_parser_number_has__view;
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
x_10 = lean::apply_1(x_8, x_0);
x_11 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_11, 0, x_10);
return x_11;
}
}
}
obj* l_lean_parser_number_parser___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_6; obj* x_7; obj* x_9; obj* x_11; 
lean::inc(x_2);
lean::inc(x_1);
x_6 = l_lean_parser_token(x_1, x_2, x_3);
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_6, 1);
lean::inc(x_9);
if (lean::is_shared(x_6)) {
 lean::dec(x_6);
 x_11 = lean::box(0);
} else {
 lean::cnstr_release(x_6, 0);
 lean::cnstr_release(x_6, 1);
 x_11 = x_6;
}
if (lean::obj_tag(x_7) == 0)
{
obj* x_12; obj* x_14; obj* x_16; obj* x_18; obj* x_20; 
x_12 = lean::cnstr_get(x_7, 0);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_7, 1);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_7, 2);
lean::inc(x_16);
if (lean::is_shared(x_7)) {
 lean::dec(x_7);
 x_18 = lean::box(0);
} else {
 lean::cnstr_release(x_7, 0);
 lean::cnstr_release(x_7, 1);
 lean::cnstr_release(x_7, 2);
 x_18 = x_7;
}
lean::inc(x_12);
x_20 = l_lean_parser_try__view___at_lean_parser_number_parser___spec__1(x_12);
if (lean::obj_tag(x_20) == 0)
{
obj* x_24; obj* x_25; obj* x_26; obj* x_29; obj* x_30; obj* x_32; obj* x_35; obj* x_37; obj* x_38; obj* x_40; obj* x_41; obj* x_42; obj* x_43; 
lean::dec(x_18);
lean::dec(x_12);
lean::dec(x_20);
x_24 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_24, 0, x_2);
x_25 = lean::box(0);
x_26 = l_string_join___closed__1;
lean::inc(x_0);
lean::inc(x_26);
x_29 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_26, x_0, x_24, x_25, x_1, x_14, x_9);
x_30 = lean::cnstr_get(x_29, 0);
lean::inc(x_30);
x_32 = lean::cnstr_get(x_29, 1);
lean::inc(x_32);
lean::dec(x_29);
x_35 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_35);
x_37 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_35, x_30);
x_38 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_37);
lean::inc(x_35);
x_40 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_35, x_38);
x_41 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_40, x_0);
x_42 = l_lean_parser_parsec__t_try__mk__res___rarg(x_41);
if (lean::is_scalar(x_11)) {
 x_43 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_43 = x_11;
}
lean::cnstr_set(x_43, 0, x_42);
lean::cnstr_set(x_43, 1, x_32);
return x_43;
}
else
{
obj* x_47; obj* x_49; obj* x_50; obj* x_51; obj* x_53; obj* x_54; obj* x_55; obj* x_56; 
lean::dec(x_1);
lean::dec(x_20);
lean::dec(x_2);
x_47 = l_lean_parser_finish__comment__block___closed__2;
lean::inc(x_47);
if (lean::is_scalar(x_18)) {
 x_49 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_49 = x_18;
}
lean::cnstr_set(x_49, 0, x_12);
lean::cnstr_set(x_49, 1, x_14);
lean::cnstr_set(x_49, 2, x_47);
x_50 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_49);
x_51 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_51);
x_53 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_51, x_50);
x_54 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_53, x_0);
x_55 = l_lean_parser_parsec__t_try__mk__res___rarg(x_54);
if (lean::is_scalar(x_11)) {
 x_56 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_56 = x_11;
}
lean::cnstr_set(x_56, 0, x_55);
lean::cnstr_set(x_56, 1, x_9);
return x_56;
}
}
else
{
obj* x_59; uint8 x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_67; obj* x_68; obj* x_69; obj* x_70; 
lean::dec(x_1);
lean::dec(x_2);
x_59 = lean::cnstr_get(x_7, 0);
lean::inc(x_59);
x_61 = lean::cnstr_get_scalar<uint8>(x_7, sizeof(void*)*1);
if (lean::is_shared(x_7)) {
 lean::dec(x_7);
 x_62 = lean::box(0);
} else {
 lean::cnstr_release(x_7, 0);
 x_62 = x_7;
}
if (lean::is_scalar(x_62)) {
 x_63 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_63 = x_62;
}
lean::cnstr_set(x_63, 0, x_59);
lean::cnstr_set_scalar(x_63, sizeof(void*)*1, x_61);
x_64 = x_63;
x_65 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_65);
x_67 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_65, x_64);
x_68 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_67, x_0);
x_69 = l_lean_parser_parsec__t_try__mk__res___rarg(x_68);
if (lean::is_scalar(x_11)) {
 x_70 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_70 = x_11;
}
lean::cnstr_set(x_70, 0, x_69);
lean::cnstr_set(x_70, 1, x_9);
return x_70;
}
}
}
obj* _init_l_lean_parser_number_parser___rarg___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_string("number");
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_1, 0, x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_number_parser___rarg___lambda__1), 4, 1);
lean::closure_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_lean_parser_number_parser___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; 
x_1 = l_lean_parser_number_parser___rarg___closed__1;
lean::inc(x_1);
x_3 = lean::apply_2(x_0, lean::box(0), x_1);
return x_3;
}
}
obj* l_lean_parser_number_parser(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_number_parser___rarg), 1, 0);
return x_2;
}
}
obj* l_lean_parser_number_parser_tokens(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::box(0);
return x_4;
}
}
obj* _init_l_lean_parser_number_parser_view___rarg___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = l_lean_parser_number_has__view;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
return x_1;
}
}
obj* _init_l_lean_parser_number_parser_view___rarg___closed__2() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = l_lean_parser_number_has__view;
x_1 = lean::cnstr_get(x_0, 1);
lean::inc(x_1);
return x_1;
}
}
obj* l_lean_parser_number_parser_view___rarg(obj* x_0) {
_start:
{
obj* x_2; obj* x_3; obj* x_6; 
lean::dec(x_0);
x_2 = l_lean_parser_number_parser_view___rarg___closed__1;
x_3 = l_lean_parser_number_parser_view___rarg___closed__2;
lean::inc(x_3);
lean::inc(x_2);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_2);
lean::cnstr_set(x_6, 1, x_3);
return x_6;
}
}
obj* l_lean_parser_number_parser_view(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_number_parser_view___rarg), 1, 0);
return x_2;
}
}
obj* l___private_init_lean_parser_token_7__to__nat__core___main(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::nat_dec_eq(x_2, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
obj* x_7; obj* x_8; uint32 x_11; uint8 x_12; obj* x_13; obj* x_15; 
x_7 = lean::mk_nat_obj(1u);
x_8 = lean::nat_sub(x_2, x_7);
lean::dec(x_7);
lean::dec(x_2);
x_11 = lean::string_iterator_curr(x_1);
x_12 = l_char_is__digit(x_11);
x_13 = lean::nat_mul(x_3, x_0);
lean::dec(x_3);
x_15 = lean::string_iterator_next(x_1);
if (x_12 == 0)
{
obj* x_16; obj* x_17; uint8 x_18; 
x_16 = lean::mk_nat_obj(97u);
x_17 = lean::box_uint32(x_11);
x_18 = lean::nat_dec_le(x_16, x_17);
if (x_18 == 0)
{
obj* x_20; obj* x_21; obj* x_24; 
lean::dec(x_16);
x_20 = lean::mk_nat_obj(65u);
x_21 = lean::nat_sub(x_17, x_20);
lean::dec(x_20);
lean::dec(x_17);
x_24 = lean::nat_add(x_13, x_21);
lean::dec(x_21);
lean::dec(x_13);
x_1 = x_15;
x_2 = x_8;
x_3 = x_24;
goto _start;
}
else
{
obj* x_28; uint8 x_29; 
x_28 = lean::mk_nat_obj(102u);
x_29 = lean::nat_dec_le(x_17, x_28);
lean::dec(x_28);
if (x_29 == 0)
{
obj* x_32; obj* x_33; obj* x_36; 
lean::dec(x_16);
x_32 = lean::mk_nat_obj(65u);
x_33 = lean::nat_sub(x_17, x_32);
lean::dec(x_32);
lean::dec(x_17);
x_36 = lean::nat_add(x_13, x_33);
lean::dec(x_33);
lean::dec(x_13);
x_1 = x_15;
x_2 = x_8;
x_3 = x_36;
goto _start;
}
else
{
obj* x_40; obj* x_43; 
x_40 = lean::nat_sub(x_17, x_16);
lean::dec(x_16);
lean::dec(x_17);
x_43 = lean::nat_add(x_13, x_40);
lean::dec(x_40);
lean::dec(x_13);
x_1 = x_15;
x_2 = x_8;
x_3 = x_43;
goto _start;
}
}
}
else
{
obj* x_47; obj* x_48; obj* x_49; obj* x_52; 
x_47 = lean::mk_nat_obj(48u);
x_48 = lean::box_uint32(x_11);
x_49 = lean::nat_sub(x_48, x_47);
lean::dec(x_47);
lean::dec(x_48);
x_52 = lean::nat_add(x_13, x_49);
lean::dec(x_49);
lean::dec(x_13);
x_1 = x_15;
x_2 = x_8;
x_3 = x_52;
goto _start;
}
}
else
{
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
return x_3;
}
}
}
obj* l___private_init_lean_parser_token_7__to__nat__core(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_parser_token_7__to__nat__core___main(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l___private_init_lean_parser_token_8__to__nat__base(obj* x_0, obj* x_1) {
_start:
{
obj* x_3; obj* x_4; obj* x_6; obj* x_7; 
lean::inc(x_0);
x_3 = lean::string_mk_iterator(x_0);
x_4 = lean::string_length(x_0);
lean::dec(x_0);
x_6 = lean::mk_nat_obj(0u);
x_7 = l___private_init_lean_parser_token_7__to__nat__core___main(x_1, x_3, x_4, x_6);
return x_7;
}
}
obj* l_lean_parser_number_view_to__nat___main(obj* x_0) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_1; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_5; 
lean::dec(x_1);
x_5 = lean::mk_nat_obj(1138u);
return x_5;
}
else
{
obj* x_6; obj* x_9; obj* x_12; 
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
lean::dec(x_1);
x_9 = lean::cnstr_get(x_6, 1);
lean::inc(x_9);
lean::dec(x_6);
x_12 = l_string_to__nat(x_9);
return x_12;
}
}
case 1:
{
obj* x_13; 
x_13 = lean::cnstr_get(x_0, 0);
lean::inc(x_13);
lean::dec(x_0);
if (lean::obj_tag(x_13) == 0)
{
obj* x_17; 
lean::dec(x_13);
x_17 = lean::mk_nat_obj(1138u);
return x_17;
}
else
{
obj* x_18; obj* x_21; obj* x_24; obj* x_25; 
x_18 = lean::cnstr_get(x_13, 0);
lean::inc(x_18);
lean::dec(x_13);
x_21 = lean::cnstr_get(x_18, 1);
lean::inc(x_21);
lean::dec(x_18);
x_24 = lean::mk_nat_obj(2u);
x_25 = l___private_init_lean_parser_token_8__to__nat__base(x_21, x_24);
return x_25;
}
}
case 2:
{
obj* x_26; 
x_26 = lean::cnstr_get(x_0, 0);
lean::inc(x_26);
lean::dec(x_0);
if (lean::obj_tag(x_26) == 0)
{
obj* x_30; 
lean::dec(x_26);
x_30 = lean::mk_nat_obj(1138u);
return x_30;
}
else
{
obj* x_31; obj* x_34; obj* x_37; obj* x_38; 
x_31 = lean::cnstr_get(x_26, 0);
lean::inc(x_31);
lean::dec(x_26);
x_34 = lean::cnstr_get(x_31, 1);
lean::inc(x_34);
lean::dec(x_31);
x_37 = lean::mk_nat_obj(8u);
x_38 = l___private_init_lean_parser_token_8__to__nat__base(x_34, x_37);
return x_38;
}
}
default:
{
obj* x_39; 
x_39 = lean::cnstr_get(x_0, 0);
lean::inc(x_39);
lean::dec(x_0);
if (lean::obj_tag(x_39) == 0)
{
obj* x_43; 
lean::dec(x_39);
x_43 = lean::mk_nat_obj(1138u);
return x_43;
}
else
{
obj* x_44; obj* x_47; obj* x_50; obj* x_51; 
x_44 = lean::cnstr_get(x_39, 0);
lean::inc(x_44);
lean::dec(x_39);
x_47 = lean::cnstr_get(x_44, 1);
lean::inc(x_47);
lean::dec(x_44);
x_50 = lean::mk_nat_obj(16u);
x_51 = l___private_init_lean_parser_token_8__to__nat__base(x_47, x_50);
return x_51;
}
}
}
}
}
obj* l_lean_parser_number_view_to__nat(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_number_view_to__nat___main(x_0);
return x_1;
}
}
obj* l_lean_parser_number_view_of__nat(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_1 = lean::box(0);
x_2 = l_nat_repr(x_0);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
x_4 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_4, 0, x_3);
x_5 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
return x_5;
}
}
obj* l_lean_parser_try__view___at_lean_parser_string__lit_parser___spec__1(obj* x_0) {
_start:
{
obj* x_1; uint8 x_4; 
x_1 = l_lean_parser_string__lit;
lean::inc(x_0);
lean::inc(x_1);
x_4 = l_lean_parser_syntax_is__of__kind___main(x_1, x_0);
if (x_4 == 0)
{
obj* x_6; 
lean::dec(x_0);
x_6 = lean::box(0);
return x_6;
}
else
{
obj* x_7; obj* x_8; obj* x_10; obj* x_11; 
x_7 = l_lean_parser_string__lit_has__view;
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
x_10 = lean::apply_1(x_8, x_0);
x_11 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_11, 0, x_10);
return x_11;
}
}
}
obj* l_lean_parser_string__lit_parser___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_6; obj* x_7; obj* x_9; obj* x_11; 
lean::inc(x_2);
lean::inc(x_1);
x_6 = l_lean_parser_token(x_1, x_2, x_3);
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_6, 1);
lean::inc(x_9);
if (lean::is_shared(x_6)) {
 lean::dec(x_6);
 x_11 = lean::box(0);
} else {
 lean::cnstr_release(x_6, 0);
 lean::cnstr_release(x_6, 1);
 x_11 = x_6;
}
if (lean::obj_tag(x_7) == 0)
{
obj* x_12; obj* x_14; obj* x_16; obj* x_18; obj* x_20; 
x_12 = lean::cnstr_get(x_7, 0);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_7, 1);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_7, 2);
lean::inc(x_16);
if (lean::is_shared(x_7)) {
 lean::dec(x_7);
 x_18 = lean::box(0);
} else {
 lean::cnstr_release(x_7, 0);
 lean::cnstr_release(x_7, 1);
 lean::cnstr_release(x_7, 2);
 x_18 = x_7;
}
lean::inc(x_12);
x_20 = l_lean_parser_try__view___at_lean_parser_string__lit_parser___spec__1(x_12);
if (lean::obj_tag(x_20) == 0)
{
obj* x_24; obj* x_25; obj* x_26; obj* x_29; obj* x_30; obj* x_32; obj* x_35; obj* x_37; obj* x_38; obj* x_40; obj* x_41; obj* x_42; obj* x_43; 
lean::dec(x_18);
lean::dec(x_12);
lean::dec(x_20);
x_24 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_24, 0, x_2);
x_25 = lean::box(0);
x_26 = l_string_join___closed__1;
lean::inc(x_0);
lean::inc(x_26);
x_29 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_26, x_0, x_24, x_25, x_1, x_14, x_9);
x_30 = lean::cnstr_get(x_29, 0);
lean::inc(x_30);
x_32 = lean::cnstr_get(x_29, 1);
lean::inc(x_32);
lean::dec(x_29);
x_35 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_35);
x_37 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_35, x_30);
x_38 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_37);
lean::inc(x_35);
x_40 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_35, x_38);
x_41 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_40, x_0);
x_42 = l_lean_parser_parsec__t_try__mk__res___rarg(x_41);
if (lean::is_scalar(x_11)) {
 x_43 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_43 = x_11;
}
lean::cnstr_set(x_43, 0, x_42);
lean::cnstr_set(x_43, 1, x_32);
return x_43;
}
else
{
obj* x_47; obj* x_49; obj* x_50; obj* x_51; obj* x_53; obj* x_54; obj* x_55; obj* x_56; 
lean::dec(x_1);
lean::dec(x_20);
lean::dec(x_2);
x_47 = l_lean_parser_finish__comment__block___closed__2;
lean::inc(x_47);
if (lean::is_scalar(x_18)) {
 x_49 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_49 = x_18;
}
lean::cnstr_set(x_49, 0, x_12);
lean::cnstr_set(x_49, 1, x_14);
lean::cnstr_set(x_49, 2, x_47);
x_50 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_49);
x_51 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_51);
x_53 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_51, x_50);
x_54 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_53, x_0);
x_55 = l_lean_parser_parsec__t_try__mk__res___rarg(x_54);
if (lean::is_scalar(x_11)) {
 x_56 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_56 = x_11;
}
lean::cnstr_set(x_56, 0, x_55);
lean::cnstr_set(x_56, 1, x_9);
return x_56;
}
}
else
{
obj* x_59; uint8 x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_67; obj* x_68; obj* x_69; obj* x_70; 
lean::dec(x_1);
lean::dec(x_2);
x_59 = lean::cnstr_get(x_7, 0);
lean::inc(x_59);
x_61 = lean::cnstr_get_scalar<uint8>(x_7, sizeof(void*)*1);
if (lean::is_shared(x_7)) {
 lean::dec(x_7);
 x_62 = lean::box(0);
} else {
 lean::cnstr_release(x_7, 0);
 x_62 = x_7;
}
if (lean::is_scalar(x_62)) {
 x_63 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_63 = x_62;
}
lean::cnstr_set(x_63, 0, x_59);
lean::cnstr_set_scalar(x_63, sizeof(void*)*1, x_61);
x_64 = x_63;
x_65 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_65);
x_67 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_65, x_64);
x_68 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_67, x_0);
x_69 = l_lean_parser_parsec__t_try__mk__res___rarg(x_68);
if (lean::is_scalar(x_11)) {
 x_70 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_70 = x_11;
}
lean::cnstr_set(x_70, 0, x_69);
lean::cnstr_set(x_70, 1, x_9);
return x_70;
}
}
}
obj* _init_l_lean_parser_string__lit_parser___rarg___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_string("string");
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_1, 0, x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_string__lit_parser___rarg___lambda__1), 4, 1);
lean::closure_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_lean_parser_string__lit_parser___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; 
x_1 = l_lean_parser_string__lit_parser___rarg___closed__1;
lean::inc(x_1);
x_3 = lean::apply_2(x_0, lean::box(0), x_1);
return x_3;
}
}
obj* l_lean_parser_string__lit_parser(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_string__lit_parser___rarg), 1, 0);
return x_2;
}
}
obj* l_lean_parser_string__lit_parser_tokens(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::box(0);
return x_4;
}
}
obj* _init_l_lean_parser_string__lit_parser_view___rarg___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = l_lean_parser_string__lit_has__view;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
return x_1;
}
}
obj* _init_l_lean_parser_string__lit_parser_view___rarg___closed__2() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = l_lean_parser_string__lit_has__view;
x_1 = lean::cnstr_get(x_0, 1);
lean::inc(x_1);
return x_1;
}
}
obj* l_lean_parser_string__lit_parser_view___rarg(obj* x_0) {
_start:
{
obj* x_2; obj* x_3; obj* x_6; 
lean::dec(x_0);
x_2 = l_lean_parser_string__lit_parser_view___rarg___closed__1;
x_3 = l_lean_parser_string__lit_parser_view___rarg___closed__2;
lean::inc(x_3);
lean::inc(x_2);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_2);
lean::cnstr_set(x_6, 1, x_3);
return x_6;
}
}
obj* l_lean_parser_string__lit_parser_view(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_string__lit_parser_view___rarg), 1, 0);
return x_2;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_string__lit_view_value___spec__3___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; uint8 x_7; obj* x_8; obj* x_9; 
x_5 = l_option_get__or__else___main___rarg(x_2, x_4);
x_6 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_0);
lean::cnstr_set(x_6, 2, x_1);
lean::cnstr_set(x_6, 3, x_3);
x_7 = 0;
x_8 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set_scalar(x_8, sizeof(void*)*1, x_7);
x_9 = x_8;
return x_9;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_string__lit_view_value___spec__3(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___at_lean_parser_string__lit_view_value___spec__3___rarg), 5, 0);
return x_2;
}
}
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_string__lit_view_value___spec__2(uint32 x_0, obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = lean::string_iterator_has_next(x_1);
if (x_2 == 0)
{
obj* x_3; obj* x_4; obj* x_5; obj* x_9; obj* x_10; obj* x_12; 
x_3 = lean::box(0);
x_4 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_5 = l_mjoin___rarg___closed__1;
lean::inc(x_3);
lean::inc(x_5);
lean::inc(x_4);
x_9 = l_lean_parser_monad__parsec_error___at_lean_parser_string__lit_view_value___spec__3___rarg(x_4, x_5, x_3, x_3, x_1);
x_10 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_10);
x_12 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_10, x_9);
return x_12;
}
else
{
uint32 x_13; obj* x_14; obj* x_15; uint8 x_16; 
x_13 = lean::string_iterator_curr(x_1);
x_14 = lean::box_uint32(x_13);
x_15 = lean::box_uint32(x_0);
x_16 = lean::nat_dec_eq(x_14, x_15);
lean::dec(x_15);
if (x_16 == 0)
{
obj* x_19; obj* x_20; obj* x_22; obj* x_24; obj* x_25; obj* x_26; obj* x_29; obj* x_30; obj* x_32; 
lean::dec(x_14);
x_19 = l_char_quote__core(x_13);
x_20 = l_char_has__repr___closed__1;
lean::inc(x_20);
x_22 = lean::string_append(x_20, x_19);
lean::dec(x_19);
x_24 = lean::string_append(x_22, x_20);
x_25 = lean::box(0);
x_26 = l_mjoin___rarg___closed__1;
lean::inc(x_25);
lean::inc(x_26);
x_29 = l_lean_parser_monad__parsec_error___at_lean_parser_string__lit_view_value___spec__3___rarg(x_24, x_26, x_25, x_25, x_1);
x_30 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_30);
x_32 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_30, x_29);
return x_32;
}
else
{
obj* x_33; obj* x_34; obj* x_35; 
x_33 = lean::string_iterator_next(x_1);
x_34 = lean::box(0);
x_35 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_35, 0, x_14);
lean::cnstr_set(x_35, 1, x_33);
lean::cnstr_set(x_35, 2, x_34);
return x_35;
}
}
}
}
obj* l_lean_parser_monad__parsec_any___at_lean_parser_string__lit_view_value___spec__5(obj* x_0) {
_start:
{
uint8 x_1; 
x_1 = lean::string_iterator_has_next(x_0);
if (x_1 == 0)
{
obj* x_2; obj* x_3; obj* x_4; obj* x_8; obj* x_9; obj* x_11; 
x_2 = lean::box(0);
x_3 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_4 = l_mjoin___rarg___closed__1;
lean::inc(x_2);
lean::inc(x_4);
lean::inc(x_3);
x_8 = l_lean_parser_monad__parsec_error___at_lean_parser_string__lit_view_value___spec__3___rarg(x_3, x_4, x_2, x_2, x_0);
x_9 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_9);
x_11 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_9, x_8);
return x_11;
}
else
{
uint32 x_12; uint8 x_13; 
x_12 = lean::string_iterator_curr(x_0);
x_13 = l_true_decidable;
if (x_13 == 0)
{
obj* x_14; obj* x_15; obj* x_17; obj* x_19; obj* x_20; obj* x_21; obj* x_24; obj* x_25; obj* x_27; 
x_14 = l_char_quote__core(x_12);
x_15 = l_char_has__repr___closed__1;
lean::inc(x_15);
x_17 = lean::string_append(x_15, x_14);
lean::dec(x_14);
x_19 = lean::string_append(x_17, x_15);
x_20 = lean::box(0);
x_21 = l_mjoin___rarg___closed__1;
lean::inc(x_20);
lean::inc(x_21);
x_24 = l_lean_parser_monad__parsec_error___at_lean_parser_string__lit_view_value___spec__3___rarg(x_19, x_21, x_20, x_20, x_0);
x_25 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_25);
x_27 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_25, x_24);
return x_27;
}
else
{
obj* x_28; obj* x_29; obj* x_30; obj* x_31; 
x_28 = lean::string_iterator_next(x_0);
x_29 = lean::box(0);
x_30 = lean::box_uint32(x_12);
x_31 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_31, 0, x_30);
lean::cnstr_set(x_31, 1, x_28);
lean::cnstr_set(x_31, 2, x_29);
return x_31;
}
}
}
}
obj* l_lean_parser_monad__parsec_digit___at_lean_parser_string__lit_view_value___spec__8(obj* x_0) {
_start:
{
uint8 x_1; 
x_1 = lean::string_iterator_has_next(x_0);
if (x_1 == 0)
{
obj* x_2; obj* x_3; obj* x_4; obj* x_8; obj* x_9; obj* x_11; 
x_2 = lean::box(0);
x_3 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_4 = l_mjoin___rarg___closed__1;
lean::inc(x_2);
lean::inc(x_4);
lean::inc(x_3);
x_8 = l_lean_parser_monad__parsec_error___at_lean_parser_string__lit_view_value___spec__3___rarg(x_3, x_4, x_2, x_2, x_0);
x_9 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_9);
x_11 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_9, x_8);
return x_11;
}
else
{
uint32 x_12; uint8 x_13; 
x_12 = lean::string_iterator_curr(x_0);
x_13 = l_char_is__digit(x_12);
if (x_13 == 0)
{
obj* x_14; obj* x_15; obj* x_17; obj* x_19; obj* x_20; obj* x_21; obj* x_24; obj* x_25; obj* x_27; 
x_14 = l_char_quote__core(x_12);
x_15 = l_char_has__repr___closed__1;
lean::inc(x_15);
x_17 = lean::string_append(x_15, x_14);
lean::dec(x_14);
x_19 = lean::string_append(x_17, x_15);
x_20 = lean::box(0);
x_21 = l_mjoin___rarg___closed__1;
lean::inc(x_20);
lean::inc(x_21);
x_24 = l_lean_parser_monad__parsec_error___at_lean_parser_string__lit_view_value___spec__3___rarg(x_19, x_21, x_20, x_20, x_0);
x_25 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_25);
x_27 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_25, x_24);
return x_27;
}
else
{
obj* x_28; obj* x_29; obj* x_30; obj* x_31; 
x_28 = lean::string_iterator_next(x_0);
x_29 = lean::box(0);
x_30 = lean::box_uint32(x_12);
x_31 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_31, 0, x_30);
lean::cnstr_set(x_31, 1, x_28);
lean::cnstr_set(x_31, 2, x_29);
return x_31;
}
}
}
}
obj* l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_view_value___spec__7(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; uint8 x_3; obj* x_6; 
lean::inc(x_0);
x_6 = l_lean_parser_monad__parsec_digit___at_lean_parser_string__lit_view_value___spec__8(x_0);
if (lean::obj_tag(x_6) == 0)
{
obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_14; obj* x_15; obj* x_18; obj* x_20; obj* x_21; 
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_6, 1);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_6, 2);
lean::inc(x_11);
if (lean::is_shared(x_6)) {
 lean::dec(x_6);
 x_13 = lean::box(0);
} else {
 lean::cnstr_release(x_6, 0);
 lean::cnstr_release(x_6, 1);
 lean::cnstr_release(x_6, 2);
 x_13 = x_6;
}
x_14 = lean::mk_nat_obj(48u);
x_15 = lean::nat_sub(x_7, x_14);
lean::dec(x_14);
lean::dec(x_7);
x_18 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_18);
if (lean::is_scalar(x_13)) {
 x_20 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_20 = x_13;
}
lean::cnstr_set(x_20, 0, x_15);
lean::cnstr_set(x_20, 1, x_9);
lean::cnstr_set(x_20, 2, x_18);
x_21 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_11, x_20);
if (lean::obj_tag(x_21) == 0)
{
obj* x_23; obj* x_25; 
lean::dec(x_0);
x_23 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__4___closed__1;
lean::inc(x_23);
x_25 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_21, x_23);
return x_25;
}
else
{
obj* x_26; uint8 x_28; 
x_26 = lean::cnstr_get(x_21, 0);
lean::inc(x_26);
x_28 = lean::cnstr_get_scalar<uint8>(x_21, sizeof(void*)*1);
x_1 = x_21;
x_2 = x_26;
x_3 = x_28;
goto lbl_4;
}
}
else
{
obj* x_29; uint8 x_31; obj* x_32; obj* x_34; obj* x_35; 
x_29 = lean::cnstr_get(x_6, 0);
lean::inc(x_29);
x_31 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*1);
if (lean::is_shared(x_6)) {
 lean::dec(x_6);
 x_32 = lean::box(0);
} else {
 lean::cnstr_release(x_6, 0);
 x_32 = x_6;
}
lean::inc(x_29);
if (lean::is_scalar(x_32)) {
 x_34 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_34 = x_32;
}
lean::cnstr_set(x_34, 0, x_29);
lean::cnstr_set_scalar(x_34, sizeof(void*)*1, x_31);
x_35 = x_34;
x_1 = x_35;
x_2 = x_29;
x_3 = x_31;
goto lbl_4;
}
lbl_4:
{
obj* x_36; obj* x_37; uint8 x_38; 
if (x_3 == 0)
{
obj* x_41; uint8 x_43; 
lean::dec(x_1);
x_43 = lean::string_iterator_has_next(x_0);
if (x_43 == 0)
{
obj* x_44; obj* x_45; obj* x_46; obj* x_51; 
x_44 = lean::box(0);
x_45 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_46 = l_mjoin___rarg___closed__1;
lean::inc(x_0);
lean::inc(x_44);
lean::inc(x_46);
lean::inc(x_45);
x_51 = l_lean_parser_monad__parsec_error___at_lean_parser_string__lit_view_value___spec__3___rarg(x_45, x_46, x_44, x_44, x_0);
x_41 = x_51;
goto lbl_42;
}
else
{
uint32 x_52; uint8 x_53; obj* x_55; obj* x_56; uint8 x_57; 
x_52 = lean::string_iterator_curr(x_0);
x_55 = lean::mk_nat_obj(97u);
x_56 = lean::box_uint32(x_52);
x_57 = lean::nat_dec_le(x_55, x_56);
lean::dec(x_56);
lean::dec(x_55);
if (x_57 == 0)
{
obj* x_60; obj* x_61; obj* x_63; obj* x_65; obj* x_66; obj* x_67; obj* x_71; 
x_60 = l_char_quote__core(x_52);
x_61 = l_char_has__repr___closed__1;
lean::inc(x_61);
x_63 = lean::string_append(x_61, x_60);
lean::dec(x_60);
x_65 = lean::string_append(x_63, x_61);
x_66 = lean::box(0);
x_67 = l_mjoin___rarg___closed__1;
lean::inc(x_0);
lean::inc(x_66);
lean::inc(x_67);
x_71 = l_lean_parser_monad__parsec_error___at_lean_parser_string__lit_view_value___spec__3___rarg(x_65, x_67, x_66, x_66, x_0);
x_41 = x_71;
goto lbl_42;
}
else
{
uint8 x_72; 
x_72 = 1;
x_53 = x_72;
goto lbl_54;
}
lbl_54:
{
obj* x_73; obj* x_74; uint8 x_75; 
x_73 = lean::mk_nat_obj(102u);
x_74 = lean::box_uint32(x_52);
x_75 = lean::nat_dec_le(x_74, x_73);
lean::dec(x_73);
if (x_75 == 0)
{
obj* x_78; obj* x_79; obj* x_81; obj* x_83; obj* x_84; obj* x_85; obj* x_89; 
lean::dec(x_74);
x_78 = l_char_quote__core(x_52);
x_79 = l_char_has__repr___closed__1;
lean::inc(x_79);
x_81 = lean::string_append(x_79, x_78);
lean::dec(x_78);
x_83 = lean::string_append(x_81, x_79);
x_84 = lean::box(0);
x_85 = l_mjoin___rarg___closed__1;
lean::inc(x_0);
lean::inc(x_84);
lean::inc(x_85);
x_89 = l_lean_parser_monad__parsec_error___at_lean_parser_string__lit_view_value___spec__3___rarg(x_83, x_85, x_84, x_84, x_0);
x_41 = x_89;
goto lbl_42;
}
else
{
if (x_53 == 0)
{
obj* x_91; obj* x_92; obj* x_94; obj* x_96; obj* x_97; obj* x_98; obj* x_102; 
lean::dec(x_74);
x_91 = l_char_quote__core(x_52);
x_92 = l_char_has__repr___closed__1;
lean::inc(x_92);
x_94 = lean::string_append(x_92, x_91);
lean::dec(x_91);
x_96 = lean::string_append(x_94, x_92);
x_97 = lean::box(0);
x_98 = l_mjoin___rarg___closed__1;
lean::inc(x_0);
lean::inc(x_97);
lean::inc(x_98);
x_102 = l_lean_parser_monad__parsec_error___at_lean_parser_string__lit_view_value___spec__3___rarg(x_96, x_98, x_97, x_97, x_0);
x_41 = x_102;
goto lbl_42;
}
else
{
obj* x_104; obj* x_105; obj* x_106; 
lean::inc(x_0);
x_104 = lean::string_iterator_next(x_0);
x_105 = lean::box(0);
x_106 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_106, 0, x_74);
lean::cnstr_set(x_106, 1, x_104);
lean::cnstr_set(x_106, 2, x_105);
x_41 = x_106;
goto lbl_42;
}
}
}
}
lbl_42:
{
obj* x_107; obj* x_109; 
x_107 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_107);
x_109 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_107, x_41);
if (lean::obj_tag(x_109) == 0)
{
obj* x_110; obj* x_112; obj* x_114; obj* x_116; obj* x_117; obj* x_118; obj* x_121; obj* x_122; obj* x_126; obj* x_127; 
x_110 = lean::cnstr_get(x_109, 0);
lean::inc(x_110);
x_112 = lean::cnstr_get(x_109, 1);
lean::inc(x_112);
x_114 = lean::cnstr_get(x_109, 2);
lean::inc(x_114);
if (lean::is_shared(x_109)) {
 lean::dec(x_109);
 x_116 = lean::box(0);
} else {
 lean::cnstr_release(x_109, 0);
 lean::cnstr_release(x_109, 1);
 lean::cnstr_release(x_109, 2);
 x_116 = x_109;
}
x_117 = lean::mk_nat_obj(97u);
x_118 = lean::nat_sub(x_110, x_117);
lean::dec(x_117);
lean::dec(x_110);
x_121 = lean::mk_nat_obj(10u);
x_122 = lean::nat_add(x_121, x_118);
lean::dec(x_118);
lean::dec(x_121);
lean::inc(x_107);
if (lean::is_scalar(x_116)) {
 x_126 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_126 = x_116;
}
lean::cnstr_set(x_126, 0, x_122);
lean::cnstr_set(x_126, 1, x_112);
lean::cnstr_set(x_126, 2, x_107);
x_127 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_114, x_126);
if (lean::obj_tag(x_127) == 0)
{
obj* x_129; obj* x_130; obj* x_132; 
lean::dec(x_0);
x_129 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_2, x_127);
x_130 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__4___closed__1;
lean::inc(x_130);
x_132 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_129, x_130);
return x_132;
}
else
{
obj* x_133; uint8 x_135; 
x_133 = lean::cnstr_get(x_127, 0);
lean::inc(x_133);
x_135 = lean::cnstr_get_scalar<uint8>(x_127, sizeof(void*)*1);
x_36 = x_127;
x_37 = x_133;
x_38 = x_135;
goto lbl_39;
}
}
else
{
obj* x_136; uint8 x_138; obj* x_139; obj* x_141; obj* x_142; 
x_136 = lean::cnstr_get(x_109, 0);
lean::inc(x_136);
x_138 = lean::cnstr_get_scalar<uint8>(x_109, sizeof(void*)*1);
if (lean::is_shared(x_109)) {
 lean::dec(x_109);
 x_139 = lean::box(0);
} else {
 lean::cnstr_release(x_109, 0);
 x_139 = x_109;
}
lean::inc(x_136);
if (lean::is_scalar(x_139)) {
 x_141 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_141 = x_139;
}
lean::cnstr_set(x_141, 0, x_136);
lean::cnstr_set_scalar(x_141, sizeof(void*)*1, x_138);
x_142 = x_141;
x_36 = x_142;
x_37 = x_136;
x_38 = x_138;
goto lbl_39;
}
}
}
else
{
obj* x_145; obj* x_147; 
lean::dec(x_0);
lean::dec(x_2);
x_145 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__4___closed__1;
lean::inc(x_145);
x_147 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_1, x_145);
return x_147;
}
lbl_39:
{
if (x_38 == 0)
{
obj* x_149; uint8 x_151; 
lean::dec(x_36);
x_151 = lean::string_iterator_has_next(x_0);
if (x_151 == 0)
{
obj* x_152; obj* x_153; obj* x_154; obj* x_158; 
x_152 = lean::box(0);
x_153 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_154 = l_mjoin___rarg___closed__1;
lean::inc(x_152);
lean::inc(x_154);
lean::inc(x_153);
x_158 = l_lean_parser_monad__parsec_error___at_lean_parser_string__lit_view_value___spec__3___rarg(x_153, x_154, x_152, x_152, x_0);
x_149 = x_158;
goto lbl_150;
}
else
{
uint32 x_159; uint8 x_160; obj* x_162; obj* x_163; uint8 x_164; 
x_159 = lean::string_iterator_curr(x_0);
x_162 = lean::mk_nat_obj(65u);
x_163 = lean::box_uint32(x_159);
x_164 = lean::nat_dec_le(x_162, x_163);
lean::dec(x_163);
lean::dec(x_162);
if (x_164 == 0)
{
obj* x_167; obj* x_168; obj* x_170; obj* x_172; obj* x_173; obj* x_174; obj* x_177; 
x_167 = l_char_quote__core(x_159);
x_168 = l_char_has__repr___closed__1;
lean::inc(x_168);
x_170 = lean::string_append(x_168, x_167);
lean::dec(x_167);
x_172 = lean::string_append(x_170, x_168);
x_173 = lean::box(0);
x_174 = l_mjoin___rarg___closed__1;
lean::inc(x_173);
lean::inc(x_174);
x_177 = l_lean_parser_monad__parsec_error___at_lean_parser_string__lit_view_value___spec__3___rarg(x_172, x_174, x_173, x_173, x_0);
x_149 = x_177;
goto lbl_150;
}
else
{
uint8 x_178; 
x_178 = 1;
x_160 = x_178;
goto lbl_161;
}
lbl_161:
{
obj* x_179; obj* x_180; uint8 x_181; 
x_179 = lean::mk_nat_obj(70u);
x_180 = lean::box_uint32(x_159);
x_181 = lean::nat_dec_le(x_180, x_179);
lean::dec(x_179);
if (x_181 == 0)
{
obj* x_184; obj* x_185; obj* x_187; obj* x_189; obj* x_190; obj* x_191; obj* x_194; 
lean::dec(x_180);
x_184 = l_char_quote__core(x_159);
x_185 = l_char_has__repr___closed__1;
lean::inc(x_185);
x_187 = lean::string_append(x_185, x_184);
lean::dec(x_184);
x_189 = lean::string_append(x_187, x_185);
x_190 = lean::box(0);
x_191 = l_mjoin___rarg___closed__1;
lean::inc(x_190);
lean::inc(x_191);
x_194 = l_lean_parser_monad__parsec_error___at_lean_parser_string__lit_view_value___spec__3___rarg(x_189, x_191, x_190, x_190, x_0);
x_149 = x_194;
goto lbl_150;
}
else
{
if (x_160 == 0)
{
obj* x_196; obj* x_197; obj* x_199; obj* x_201; obj* x_202; obj* x_203; obj* x_206; 
lean::dec(x_180);
x_196 = l_char_quote__core(x_159);
x_197 = l_char_has__repr___closed__1;
lean::inc(x_197);
x_199 = lean::string_append(x_197, x_196);
lean::dec(x_196);
x_201 = lean::string_append(x_199, x_197);
x_202 = lean::box(0);
x_203 = l_mjoin___rarg___closed__1;
lean::inc(x_202);
lean::inc(x_203);
x_206 = l_lean_parser_monad__parsec_error___at_lean_parser_string__lit_view_value___spec__3___rarg(x_201, x_203, x_202, x_202, x_0);
x_149 = x_206;
goto lbl_150;
}
else
{
obj* x_207; obj* x_208; obj* x_209; 
x_207 = lean::string_iterator_next(x_0);
x_208 = lean::box(0);
x_209 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_209, 0, x_180);
lean::cnstr_set(x_209, 1, x_207);
lean::cnstr_set(x_209, 2, x_208);
x_149 = x_209;
goto lbl_150;
}
}
}
}
lbl_150:
{
obj* x_210; obj* x_212; 
x_210 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_210);
x_212 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_210, x_149);
if (lean::obj_tag(x_212) == 0)
{
obj* x_213; obj* x_215; obj* x_217; obj* x_219; obj* x_220; obj* x_221; obj* x_224; obj* x_225; obj* x_229; obj* x_230; obj* x_231; obj* x_232; obj* x_233; obj* x_235; 
x_213 = lean::cnstr_get(x_212, 0);
lean::inc(x_213);
x_215 = lean::cnstr_get(x_212, 1);
lean::inc(x_215);
x_217 = lean::cnstr_get(x_212, 2);
lean::inc(x_217);
if (lean::is_shared(x_212)) {
 lean::dec(x_212);
 x_219 = lean::box(0);
} else {
 lean::cnstr_release(x_212, 0);
 lean::cnstr_release(x_212, 1);
 lean::cnstr_release(x_212, 2);
 x_219 = x_212;
}
x_220 = lean::mk_nat_obj(65u);
x_221 = lean::nat_sub(x_213, x_220);
lean::dec(x_220);
lean::dec(x_213);
x_224 = lean::mk_nat_obj(10u);
x_225 = lean::nat_add(x_224, x_221);
lean::dec(x_221);
lean::dec(x_224);
lean::inc(x_210);
if (lean::is_scalar(x_219)) {
 x_229 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_229 = x_219;
}
lean::cnstr_set(x_229, 0, x_225);
lean::cnstr_set(x_229, 1, x_215);
lean::cnstr_set(x_229, 2, x_210);
x_230 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_217, x_229);
x_231 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_37, x_230);
x_232 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_2, x_231);
x_233 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__4___closed__1;
lean::inc(x_233);
x_235 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_232, x_233);
return x_235;
}
else
{
obj* x_236; uint8 x_238; obj* x_239; obj* x_240; obj* x_241; obj* x_242; obj* x_243; obj* x_244; obj* x_246; 
x_236 = lean::cnstr_get(x_212, 0);
lean::inc(x_236);
x_238 = lean::cnstr_get_scalar<uint8>(x_212, sizeof(void*)*1);
if (lean::is_shared(x_212)) {
 lean::dec(x_212);
 x_239 = lean::box(0);
} else {
 lean::cnstr_release(x_212, 0);
 x_239 = x_212;
}
if (lean::is_scalar(x_239)) {
 x_240 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_240 = x_239;
}
lean::cnstr_set(x_240, 0, x_236);
lean::cnstr_set_scalar(x_240, sizeof(void*)*1, x_238);
x_241 = x_240;
x_242 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_37, x_241);
x_243 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_2, x_242);
x_244 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__4___closed__1;
lean::inc(x_244);
x_246 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_243, x_244);
return x_246;
}
}
}
else
{
obj* x_249; obj* x_250; obj* x_252; 
lean::dec(x_0);
lean::dec(x_37);
x_249 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_2, x_36);
x_250 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__4___closed__1;
lean::inc(x_250);
x_252 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_249, x_250);
return x_252;
}
}
}
}
}
obj* l_lean_parser_monad__parsec_unexpected__at___at_lean_parser_string__lit_view_value___spec__9___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_7; 
x_3 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_3, 0, x_1);
x_4 = lean::box(0);
x_5 = l_mjoin___rarg___closed__1;
lean::inc(x_5);
x_7 = l_lean_parser_monad__parsec_error___at_lean_parser_string__lit_view_value___spec__3___rarg(x_0, x_5, x_3, x_4, x_2);
return x_7;
}
}
obj* l_lean_parser_monad__parsec_unexpected__at___at_lean_parser_string__lit_view_value___spec__9(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_unexpected__at___at_lean_parser_string__lit_view_value___spec__9___rarg), 3, 0);
return x_2;
}
}
obj* l_lean_parser_parse__quoted__char___at_lean_parser_string__lit_view_value___spec__6(obj* x_0) {
_start:
{
obj* x_2; 
lean::inc(x_0);
x_2 = l_lean_parser_monad__parsec_any___at_lean_parser_string__lit_view_value___spec__5(x_0);
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_14; obj* x_16; uint8 x_17; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_2, 2);
lean::inc(x_7);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_9 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 lean::cnstr_release(x_2, 1);
 lean::cnstr_release(x_2, 2);
 x_9 = x_2;
}
x_16 = lean::mk_nat_obj(92u);
x_17 = lean::nat_dec_eq(x_3, x_16);
if (x_17 == 0)
{
obj* x_19; uint8 x_20; 
lean::dec(x_16);
x_19 = lean::mk_nat_obj(34u);
x_20 = lean::nat_dec_eq(x_3, x_19);
if (x_20 == 0)
{
obj* x_22; uint8 x_23; 
lean::dec(x_19);
x_22 = lean::mk_nat_obj(39u);
x_23 = lean::nat_dec_eq(x_3, x_22);
if (x_23 == 0)
{
obj* x_25; 
lean::dec(x_22);
x_25 = lean::box(0);
x_14 = x_25;
goto lbl_15;
}
else
{
obj* x_29; obj* x_31; obj* x_32; obj* x_34; 
lean::dec(x_9);
lean::dec(x_0);
lean::dec(x_3);
x_29 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_29);
x_31 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_31, 0, x_22);
lean::cnstr_set(x_31, 1, x_5);
lean::cnstr_set(x_31, 2, x_29);
x_32 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_31);
lean::inc(x_29);
x_34 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_29, x_32);
return x_34;
}
}
else
{
obj* x_38; obj* x_40; obj* x_41; obj* x_43; 
lean::dec(x_9);
lean::dec(x_0);
lean::dec(x_3);
x_38 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_38);
x_40 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_40, 0, x_19);
lean::cnstr_set(x_40, 1, x_5);
lean::cnstr_set(x_40, 2, x_38);
x_41 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_40);
lean::inc(x_38);
x_43 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_38, x_41);
return x_43;
}
}
else
{
obj* x_47; obj* x_49; obj* x_50; obj* x_52; 
lean::dec(x_9);
lean::dec(x_0);
lean::dec(x_3);
x_47 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_47);
x_49 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_49, 0, x_16);
lean::cnstr_set(x_49, 1, x_5);
lean::cnstr_set(x_49, 2, x_47);
x_50 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_49);
lean::inc(x_47);
x_52 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_47, x_50);
return x_52;
}
lbl_11:
{
obj* x_54; 
lean::dec(x_10);
x_54 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_view_value___spec__7(x_5);
if (lean::obj_tag(x_54) == 0)
{
obj* x_55; obj* x_57; obj* x_59; obj* x_62; 
x_55 = lean::cnstr_get(x_54, 0);
lean::inc(x_55);
x_57 = lean::cnstr_get(x_54, 1);
lean::inc(x_57);
x_59 = lean::cnstr_get(x_54, 2);
lean::inc(x_59);
lean::dec(x_54);
x_62 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_view_value___spec__7(x_57);
if (lean::obj_tag(x_62) == 0)
{
obj* x_63; obj* x_65; obj* x_67; obj* x_70; 
x_63 = lean::cnstr_get(x_62, 0);
lean::inc(x_63);
x_65 = lean::cnstr_get(x_62, 1);
lean::inc(x_65);
x_67 = lean::cnstr_get(x_62, 2);
lean::inc(x_67);
lean::dec(x_62);
x_70 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_view_value___spec__7(x_65);
if (lean::obj_tag(x_70) == 0)
{
obj* x_71; obj* x_73; obj* x_75; obj* x_78; 
x_71 = lean::cnstr_get(x_70, 0);
lean::inc(x_71);
x_73 = lean::cnstr_get(x_70, 1);
lean::inc(x_73);
x_75 = lean::cnstr_get(x_70, 2);
lean::inc(x_75);
lean::dec(x_70);
x_78 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_view_value___spec__7(x_73);
if (lean::obj_tag(x_78) == 0)
{
obj* x_79; obj* x_81; obj* x_83; obj* x_86; obj* x_87; obj* x_89; obj* x_92; obj* x_94; obj* x_97; obj* x_100; obj* x_103; uint8 x_104; 
x_79 = lean::cnstr_get(x_78, 0);
lean::inc(x_79);
x_81 = lean::cnstr_get(x_78, 1);
lean::inc(x_81);
x_83 = lean::cnstr_get(x_78, 2);
lean::inc(x_83);
lean::dec(x_78);
x_86 = lean::mk_nat_obj(16u);
x_87 = lean::nat_mul(x_86, x_55);
lean::dec(x_55);
x_89 = lean::nat_add(x_87, x_63);
lean::dec(x_63);
lean::dec(x_87);
x_92 = lean::nat_mul(x_86, x_89);
lean::dec(x_89);
x_94 = lean::nat_add(x_92, x_71);
lean::dec(x_71);
lean::dec(x_92);
x_97 = lean::nat_mul(x_86, x_94);
lean::dec(x_94);
lean::dec(x_86);
x_100 = lean::nat_add(x_97, x_79);
lean::dec(x_79);
lean::dec(x_97);
x_103 = lean::mk_nat_obj(55296u);
x_104 = lean::nat_dec_lt(x_100, x_103);
lean::dec(x_103);
if (x_104 == 0)
{
obj* x_106; uint8 x_107; 
x_106 = lean::mk_nat_obj(57343u);
x_107 = lean::nat_dec_lt(x_106, x_100);
lean::dec(x_106);
if (x_107 == 0)
{
obj* x_110; obj* x_111; obj* x_113; obj* x_114; obj* x_115; obj* x_116; obj* x_117; obj* x_118; obj* x_120; 
lean::dec(x_100);
x_110 = lean::mk_nat_obj(0u);
x_111 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_111);
if (lean::is_scalar(x_9)) {
 x_113 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_113 = x_9;
}
lean::cnstr_set(x_113, 0, x_110);
lean::cnstr_set(x_113, 1, x_81);
lean::cnstr_set(x_113, 2, x_111);
x_114 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_83, x_113);
x_115 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_75, x_114);
x_116 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_67, x_115);
x_117 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_59, x_116);
x_118 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_117);
lean::inc(x_111);
x_120 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_111, x_118);
return x_120;
}
else
{
obj* x_121; uint8 x_122; 
x_121 = lean::mk_nat_obj(1114112u);
x_122 = lean::nat_dec_lt(x_100, x_121);
lean::dec(x_121);
if (x_122 == 0)
{
obj* x_125; obj* x_126; obj* x_128; obj* x_129; obj* x_130; obj* x_131; obj* x_132; obj* x_133; obj* x_135; 
lean::dec(x_100);
x_125 = lean::mk_nat_obj(0u);
x_126 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_126);
if (lean::is_scalar(x_9)) {
 x_128 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_128 = x_9;
}
lean::cnstr_set(x_128, 0, x_125);
lean::cnstr_set(x_128, 1, x_81);
lean::cnstr_set(x_128, 2, x_126);
x_129 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_83, x_128);
x_130 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_75, x_129);
x_131 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_67, x_130);
x_132 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_59, x_131);
x_133 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_132);
lean::inc(x_126);
x_135 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_126, x_133);
return x_135;
}
else
{
obj* x_136; obj* x_138; obj* x_139; obj* x_140; obj* x_141; obj* x_142; obj* x_143; obj* x_145; 
x_136 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_136);
if (lean::is_scalar(x_9)) {
 x_138 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_138 = x_9;
}
lean::cnstr_set(x_138, 0, x_100);
lean::cnstr_set(x_138, 1, x_81);
lean::cnstr_set(x_138, 2, x_136);
x_139 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_83, x_138);
x_140 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_75, x_139);
x_141 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_67, x_140);
x_142 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_59, x_141);
x_143 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_142);
lean::inc(x_136);
x_145 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_136, x_143);
return x_145;
}
}
}
else
{
obj* x_146; obj* x_148; obj* x_149; obj* x_150; obj* x_151; obj* x_152; obj* x_153; obj* x_155; 
x_146 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_146);
if (lean::is_scalar(x_9)) {
 x_148 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_148 = x_9;
}
lean::cnstr_set(x_148, 0, x_100);
lean::cnstr_set(x_148, 1, x_81);
lean::cnstr_set(x_148, 2, x_146);
x_149 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_83, x_148);
x_150 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_75, x_149);
x_151 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_67, x_150);
x_152 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_59, x_151);
x_153 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_152);
lean::inc(x_146);
x_155 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_146, x_153);
return x_155;
}
}
else
{
obj* x_160; uint8 x_162; obj* x_163; obj* x_164; obj* x_165; obj* x_166; obj* x_167; obj* x_168; obj* x_169; obj* x_170; obj* x_172; 
lean::dec(x_55);
lean::dec(x_71);
lean::dec(x_63);
lean::dec(x_9);
x_160 = lean::cnstr_get(x_78, 0);
lean::inc(x_160);
x_162 = lean::cnstr_get_scalar<uint8>(x_78, sizeof(void*)*1);
if (lean::is_shared(x_78)) {
 lean::dec(x_78);
 x_163 = lean::box(0);
} else {
 lean::cnstr_release(x_78, 0);
 x_163 = x_78;
}
if (lean::is_scalar(x_163)) {
 x_164 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_164 = x_163;
}
lean::cnstr_set(x_164, 0, x_160);
lean::cnstr_set_scalar(x_164, sizeof(void*)*1, x_162);
x_165 = x_164;
x_166 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_75, x_165);
x_167 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_67, x_166);
x_168 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_59, x_167);
x_169 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_168);
x_170 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_170);
x_172 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_170, x_169);
return x_172;
}
}
else
{
obj* x_176; uint8 x_178; obj* x_179; obj* x_180; obj* x_181; obj* x_182; obj* x_183; obj* x_184; obj* x_185; obj* x_187; 
lean::dec(x_55);
lean::dec(x_63);
lean::dec(x_9);
x_176 = lean::cnstr_get(x_70, 0);
lean::inc(x_176);
x_178 = lean::cnstr_get_scalar<uint8>(x_70, sizeof(void*)*1);
if (lean::is_shared(x_70)) {
 lean::dec(x_70);
 x_179 = lean::box(0);
} else {
 lean::cnstr_release(x_70, 0);
 x_179 = x_70;
}
if (lean::is_scalar(x_179)) {
 x_180 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_180 = x_179;
}
lean::cnstr_set(x_180, 0, x_176);
lean::cnstr_set_scalar(x_180, sizeof(void*)*1, x_178);
x_181 = x_180;
x_182 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_67, x_181);
x_183 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_59, x_182);
x_184 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_183);
x_185 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_185);
x_187 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_185, x_184);
return x_187;
}
}
else
{
obj* x_190; uint8 x_192; obj* x_193; obj* x_194; obj* x_195; obj* x_196; obj* x_197; obj* x_198; obj* x_200; 
lean::dec(x_55);
lean::dec(x_9);
x_190 = lean::cnstr_get(x_62, 0);
lean::inc(x_190);
x_192 = lean::cnstr_get_scalar<uint8>(x_62, sizeof(void*)*1);
if (lean::is_shared(x_62)) {
 lean::dec(x_62);
 x_193 = lean::box(0);
} else {
 lean::cnstr_release(x_62, 0);
 x_193 = x_62;
}
if (lean::is_scalar(x_193)) {
 x_194 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_194 = x_193;
}
lean::cnstr_set(x_194, 0, x_190);
lean::cnstr_set_scalar(x_194, sizeof(void*)*1, x_192);
x_195 = x_194;
x_196 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_59, x_195);
x_197 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_196);
x_198 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_198);
x_200 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_198, x_197);
return x_200;
}
}
else
{
obj* x_202; uint8 x_204; obj* x_205; obj* x_206; obj* x_207; obj* x_208; obj* x_209; obj* x_211; 
lean::dec(x_9);
x_202 = lean::cnstr_get(x_54, 0);
lean::inc(x_202);
x_204 = lean::cnstr_get_scalar<uint8>(x_54, sizeof(void*)*1);
if (lean::is_shared(x_54)) {
 lean::dec(x_54);
 x_205 = lean::box(0);
} else {
 lean::cnstr_release(x_54, 0);
 x_205 = x_54;
}
if (lean::is_scalar(x_205)) {
 x_206 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_206 = x_205;
}
lean::cnstr_set(x_206, 0, x_202);
lean::cnstr_set_scalar(x_206, sizeof(void*)*1, x_204);
x_207 = x_206;
x_208 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_207);
x_209 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_209);
x_211 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_209, x_208);
return x_211;
}
}
lbl_13:
{
obj* x_213; 
lean::dec(x_12);
x_213 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_view_value___spec__7(x_5);
if (lean::obj_tag(x_213) == 0)
{
obj* x_214; obj* x_216; obj* x_218; obj* x_220; obj* x_221; 
x_214 = lean::cnstr_get(x_213, 0);
lean::inc(x_214);
x_216 = lean::cnstr_get(x_213, 1);
lean::inc(x_216);
x_218 = lean::cnstr_get(x_213, 2);
lean::inc(x_218);
if (lean::is_shared(x_213)) {
 lean::dec(x_213);
 x_220 = lean::box(0);
} else {
 lean::cnstr_release(x_213, 0);
 lean::cnstr_release(x_213, 1);
 lean::cnstr_release(x_213, 2);
 x_220 = x_213;
}
x_221 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_view_value___spec__7(x_216);
if (lean::obj_tag(x_221) == 0)
{
obj* x_222; obj* x_224; obj* x_226; obj* x_229; obj* x_230; obj* x_233; obj* x_236; uint8 x_237; 
x_222 = lean::cnstr_get(x_221, 0);
lean::inc(x_222);
x_224 = lean::cnstr_get(x_221, 1);
lean::inc(x_224);
x_226 = lean::cnstr_get(x_221, 2);
lean::inc(x_226);
lean::dec(x_221);
x_229 = lean::mk_nat_obj(16u);
x_230 = lean::nat_mul(x_229, x_214);
lean::dec(x_214);
lean::dec(x_229);
x_233 = lean::nat_add(x_230, x_222);
lean::dec(x_222);
lean::dec(x_230);
x_236 = lean::mk_nat_obj(55296u);
x_237 = lean::nat_dec_lt(x_233, x_236);
lean::dec(x_236);
if (x_237 == 0)
{
obj* x_239; uint8 x_240; 
x_239 = lean::mk_nat_obj(57343u);
x_240 = lean::nat_dec_lt(x_239, x_233);
lean::dec(x_239);
if (x_240 == 0)
{
obj* x_243; obj* x_244; obj* x_246; obj* x_247; obj* x_248; obj* x_249; obj* x_251; 
lean::dec(x_233);
x_243 = lean::mk_nat_obj(0u);
x_244 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_244);
if (lean::is_scalar(x_220)) {
 x_246 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_246 = x_220;
}
lean::cnstr_set(x_246, 0, x_243);
lean::cnstr_set(x_246, 1, x_224);
lean::cnstr_set(x_246, 2, x_244);
x_247 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_226, x_246);
x_248 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_218, x_247);
x_249 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_248);
lean::inc(x_244);
x_251 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_244, x_249);
return x_251;
}
else
{
obj* x_252; uint8 x_253; 
x_252 = lean::mk_nat_obj(1114112u);
x_253 = lean::nat_dec_lt(x_233, x_252);
lean::dec(x_252);
if (x_253 == 0)
{
obj* x_256; obj* x_257; obj* x_259; obj* x_260; obj* x_261; obj* x_262; obj* x_264; 
lean::dec(x_233);
x_256 = lean::mk_nat_obj(0u);
x_257 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_257);
if (lean::is_scalar(x_220)) {
 x_259 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_259 = x_220;
}
lean::cnstr_set(x_259, 0, x_256);
lean::cnstr_set(x_259, 1, x_224);
lean::cnstr_set(x_259, 2, x_257);
x_260 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_226, x_259);
x_261 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_218, x_260);
x_262 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_261);
lean::inc(x_257);
x_264 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_257, x_262);
return x_264;
}
else
{
obj* x_265; obj* x_267; obj* x_268; obj* x_269; obj* x_270; obj* x_272; 
x_265 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_265);
if (lean::is_scalar(x_220)) {
 x_267 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_267 = x_220;
}
lean::cnstr_set(x_267, 0, x_233);
lean::cnstr_set(x_267, 1, x_224);
lean::cnstr_set(x_267, 2, x_265);
x_268 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_226, x_267);
x_269 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_218, x_268);
x_270 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_269);
lean::inc(x_265);
x_272 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_265, x_270);
return x_272;
}
}
}
else
{
obj* x_273; obj* x_275; obj* x_276; obj* x_277; obj* x_278; obj* x_280; 
x_273 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_273);
if (lean::is_scalar(x_220)) {
 x_275 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_275 = x_220;
}
lean::cnstr_set(x_275, 0, x_233);
lean::cnstr_set(x_275, 1, x_224);
lean::cnstr_set(x_275, 2, x_273);
x_276 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_226, x_275);
x_277 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_218, x_276);
x_278 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_277);
lean::inc(x_273);
x_280 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_273, x_278);
return x_280;
}
}
else
{
obj* x_283; uint8 x_285; obj* x_286; obj* x_287; obj* x_288; obj* x_289; obj* x_290; obj* x_291; obj* x_293; 
lean::dec(x_214);
lean::dec(x_220);
x_283 = lean::cnstr_get(x_221, 0);
lean::inc(x_283);
x_285 = lean::cnstr_get_scalar<uint8>(x_221, sizeof(void*)*1);
if (lean::is_shared(x_221)) {
 lean::dec(x_221);
 x_286 = lean::box(0);
} else {
 lean::cnstr_release(x_221, 0);
 x_286 = x_221;
}
if (lean::is_scalar(x_286)) {
 x_287 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_287 = x_286;
}
lean::cnstr_set(x_287, 0, x_283);
lean::cnstr_set_scalar(x_287, sizeof(void*)*1, x_285);
x_288 = x_287;
x_289 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_218, x_288);
x_290 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_289);
x_291 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_291);
x_293 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_291, x_290);
return x_293;
}
}
else
{
obj* x_294; uint8 x_296; obj* x_297; obj* x_298; obj* x_299; obj* x_300; obj* x_301; obj* x_303; 
x_294 = lean::cnstr_get(x_213, 0);
lean::inc(x_294);
x_296 = lean::cnstr_get_scalar<uint8>(x_213, sizeof(void*)*1);
if (lean::is_shared(x_213)) {
 lean::dec(x_213);
 x_297 = lean::box(0);
} else {
 lean::cnstr_release(x_213, 0);
 x_297 = x_213;
}
if (lean::is_scalar(x_297)) {
 x_298 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_298 = x_297;
}
lean::cnstr_set(x_298, 0, x_294);
lean::cnstr_set_scalar(x_298, sizeof(void*)*1, x_296);
x_299 = x_298;
x_300 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_299);
x_301 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_301);
x_303 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_301, x_300);
return x_303;
}
}
lbl_15:
{
obj* x_305; uint8 x_306; 
lean::dec(x_14);
x_305 = lean::mk_nat_obj(110u);
x_306 = lean::nat_dec_eq(x_3, x_305);
lean::dec(x_305);
if (x_306 == 0)
{
obj* x_308; uint8 x_309; 
x_308 = lean::mk_nat_obj(116u);
x_309 = lean::nat_dec_eq(x_3, x_308);
lean::dec(x_308);
if (x_309 == 0)
{
obj* x_311; uint8 x_312; 
x_311 = lean::mk_nat_obj(120u);
x_312 = lean::nat_dec_eq(x_3, x_311);
lean::dec(x_311);
if (x_312 == 0)
{
obj* x_314; uint8 x_315; 
x_314 = lean::mk_nat_obj(117u);
x_315 = lean::nat_dec_eq(x_3, x_314);
lean::dec(x_314);
lean::dec(x_3);
if (x_315 == 0)
{
obj* x_319; obj* x_321; obj* x_322; obj* x_323; obj* x_325; 
lean::dec(x_9);
x_319 = l_lean_parser_parse__quoted__char___rarg___lambda__7___closed__1;
lean::inc(x_319);
x_321 = l_lean_parser_monad__parsec_unexpected__at___at_lean_parser_string__lit_view_value___spec__9___rarg(x_319, x_0, x_5);
x_322 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_321);
x_323 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_323);
x_325 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_323, x_322);
return x_325;
}
else
{
obj* x_327; 
lean::dec(x_0);
x_327 = lean::box(0);
x_10 = x_327;
goto lbl_11;
}
}
else
{
obj* x_331; 
lean::dec(x_9);
lean::dec(x_0);
lean::dec(x_3);
x_331 = lean::box(0);
x_12 = x_331;
goto lbl_13;
}
}
else
{
obj* x_335; obj* x_336; obj* x_338; obj* x_339; obj* x_341; 
lean::dec(x_9);
lean::dec(x_0);
lean::dec(x_3);
x_335 = lean::mk_nat_obj(9u);
x_336 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_336);
x_338 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_338, 0, x_335);
lean::cnstr_set(x_338, 1, x_5);
lean::cnstr_set(x_338, 2, x_336);
x_339 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_338);
lean::inc(x_336);
x_341 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_336, x_339);
return x_341;
}
}
else
{
obj* x_345; obj* x_346; obj* x_348; obj* x_349; obj* x_351; 
lean::dec(x_9);
lean::dec(x_0);
lean::dec(x_3);
x_345 = lean::mk_nat_obj(10u);
x_346 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_346);
x_348 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_348, 0, x_345);
lean::cnstr_set(x_348, 1, x_5);
lean::cnstr_set(x_348, 2, x_346);
x_349 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_348);
lean::inc(x_346);
x_351 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_346, x_349);
return x_351;
}
}
}
else
{
obj* x_353; uint8 x_355; obj* x_356; obj* x_357; obj* x_358; obj* x_359; obj* x_361; 
lean::dec(x_0);
x_353 = lean::cnstr_get(x_2, 0);
lean::inc(x_353);
x_355 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*1);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_356 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 x_356 = x_2;
}
if (lean::is_scalar(x_356)) {
 x_357 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_357 = x_356;
}
lean::cnstr_set(x_357, 0, x_353);
lean::cnstr_set_scalar(x_357, sizeof(void*)*1, x_355);
x_358 = x_357;
x_359 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_359);
x_361 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_359, x_358);
return x_361;
}
}
}
obj* l_lean_parser_parse__string__literal__aux___main___at_lean_parser_string__lit_view_value___spec__4(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
obj* x_6; 
x_6 = l_lean_parser_monad__parsec_any___at_lean_parser_string__lit_view_value___spec__5(x_2);
if (lean::obj_tag(x_6) == 0)
{
obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_14; obj* x_15; obj* x_18; uint8 x_19; 
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_6, 1);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_6, 2);
lean::inc(x_11);
if (lean::is_shared(x_6)) {
 lean::dec(x_6);
 x_13 = lean::box(0);
} else {
 lean::cnstr_release(x_6, 0);
 lean::cnstr_release(x_6, 1);
 lean::cnstr_release(x_6, 2);
 x_13 = x_6;
}
x_14 = lean::mk_nat_obj(1u);
x_15 = lean::nat_sub(x_0, x_14);
lean::dec(x_14);
lean::dec(x_0);
x_18 = lean::mk_nat_obj(92u);
x_19 = lean::nat_dec_eq(x_7, x_18);
lean::dec(x_18);
if (x_19 == 0)
{
obj* x_21; uint8 x_22; 
x_21 = lean::mk_nat_obj(34u);
x_22 = lean::nat_dec_eq(x_7, x_21);
lean::dec(x_21);
if (x_22 == 0)
{
uint32 x_25; obj* x_27; obj* x_28; obj* x_29; 
lean::dec(x_13);
x_25 = lean::unbox_uint32(x_7);
lean::dec(x_7);
x_27 = lean::string_push(x_1, x_25);
x_28 = l_lean_parser_parse__string__literal__aux___main___at_lean_parser_string__lit_view_value___spec__4(x_15, x_27, x_9);
x_29 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_11, x_28);
return x_29;
}
else
{
obj* x_32; obj* x_34; obj* x_35; 
lean::dec(x_15);
lean::dec(x_7);
x_32 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_32);
if (lean::is_scalar(x_13)) {
 x_34 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_34 = x_13;
}
lean::cnstr_set(x_34, 0, x_1);
lean::cnstr_set(x_34, 1, x_9);
lean::cnstr_set(x_34, 2, x_32);
x_35 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_11, x_34);
return x_35;
}
}
else
{
obj* x_38; 
lean::dec(x_13);
lean::dec(x_7);
x_38 = l_lean_parser_parse__quoted__char___at_lean_parser_string__lit_view_value___spec__6(x_9);
if (lean::obj_tag(x_38) == 0)
{
obj* x_39; obj* x_41; obj* x_43; uint32 x_46; obj* x_48; obj* x_49; obj* x_50; obj* x_51; 
x_39 = lean::cnstr_get(x_38, 0);
lean::inc(x_39);
x_41 = lean::cnstr_get(x_38, 1);
lean::inc(x_41);
x_43 = lean::cnstr_get(x_38, 2);
lean::inc(x_43);
lean::dec(x_38);
x_46 = lean::unbox_uint32(x_39);
lean::dec(x_39);
x_48 = lean::string_push(x_1, x_46);
x_49 = l_lean_parser_parse__string__literal__aux___main___at_lean_parser_string__lit_view_value___spec__4(x_15, x_48, x_41);
x_50 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_43, x_49);
x_51 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_11, x_50);
return x_51;
}
else
{
obj* x_54; uint8 x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; 
lean::dec(x_15);
lean::dec(x_1);
x_54 = lean::cnstr_get(x_38, 0);
lean::inc(x_54);
x_56 = lean::cnstr_get_scalar<uint8>(x_38, sizeof(void*)*1);
if (lean::is_shared(x_38)) {
 lean::dec(x_38);
 x_57 = lean::box(0);
} else {
 lean::cnstr_release(x_38, 0);
 x_57 = x_38;
}
if (lean::is_scalar(x_57)) {
 x_58 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_58 = x_57;
}
lean::cnstr_set(x_58, 0, x_54);
lean::cnstr_set_scalar(x_58, sizeof(void*)*1, x_56);
x_59 = x_58;
x_60 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_11, x_59);
return x_60;
}
}
}
else
{
obj* x_63; uint8 x_65; obj* x_66; obj* x_67; obj* x_68; 
lean::dec(x_1);
lean::dec(x_0);
x_63 = lean::cnstr_get(x_6, 0);
lean::inc(x_63);
x_65 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*1);
if (lean::is_shared(x_6)) {
 lean::dec(x_6);
 x_66 = lean::box(0);
} else {
 lean::cnstr_release(x_6, 0);
 x_66 = x_6;
}
if (lean::is_scalar(x_66)) {
 x_67 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_67 = x_66;
}
lean::cnstr_set(x_67, 0, x_63);
lean::cnstr_set_scalar(x_67, sizeof(void*)*1, x_65);
x_68 = x_67;
return x_68;
}
}
else
{
obj* x_70; uint32 x_71; obj* x_73; 
lean::dec(x_0);
x_70 = lean::mk_nat_obj(34u);
x_71 = lean::unbox_uint32(x_70);
lean::dec(x_70);
x_73 = l_lean_parser_monad__parsec_ch___at_lean_parser_string__lit_view_value___spec__2(x_71, x_2);
if (lean::obj_tag(x_73) == 0)
{
obj* x_74; obj* x_76; obj* x_78; obj* x_79; obj* x_81; obj* x_82; 
x_74 = lean::cnstr_get(x_73, 1);
lean::inc(x_74);
x_76 = lean::cnstr_get(x_73, 2);
lean::inc(x_76);
if (lean::is_shared(x_73)) {
 lean::dec(x_73);
 x_78 = lean::box(0);
} else {
 lean::cnstr_release(x_73, 0);
 lean::cnstr_release(x_73, 1);
 lean::cnstr_release(x_73, 2);
 x_78 = x_73;
}
x_79 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_79);
if (lean::is_scalar(x_78)) {
 x_81 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_81 = x_78;
}
lean::cnstr_set(x_81, 0, x_1);
lean::cnstr_set(x_81, 1, x_74);
lean::cnstr_set(x_81, 2, x_79);
x_82 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_76, x_81);
return x_82;
}
else
{
obj* x_84; uint8 x_86; obj* x_87; obj* x_88; obj* x_89; 
lean::dec(x_1);
x_84 = lean::cnstr_get(x_73, 0);
lean::inc(x_84);
x_86 = lean::cnstr_get_scalar<uint8>(x_73, sizeof(void*)*1);
if (lean::is_shared(x_73)) {
 lean::dec(x_73);
 x_87 = lean::box(0);
} else {
 lean::cnstr_release(x_73, 0);
 x_87 = x_73;
}
if (lean::is_scalar(x_87)) {
 x_88 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_88 = x_87;
}
lean::cnstr_set(x_88, 0, x_84);
lean::cnstr_set_scalar(x_88, sizeof(void*)*1, x_86);
x_89 = x_88;
return x_89;
}
}
}
}
obj* l_lean_parser_parse__string__literal___at_lean_parser_string__lit_view_value___spec__1(obj* x_0) {
_start:
{
obj* x_1; uint32 x_2; obj* x_4; 
x_1 = lean::mk_nat_obj(34u);
x_2 = lean::unbox_uint32(x_1);
lean::dec(x_1);
x_4 = l_lean_parser_monad__parsec_ch___at_lean_parser_string__lit_view_value___spec__2(x_2, x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; obj* x_7; obj* x_10; obj* x_11; obj* x_13; obj* x_14; obj* x_16; obj* x_17; 
x_5 = lean::cnstr_get(x_4, 1);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_4, 2);
lean::inc(x_7);
lean::dec(x_4);
x_10 = lean::string_iterator_remaining(x_5);
x_11 = l_string_join___closed__1;
lean::inc(x_11);
x_13 = l_lean_parser_parse__string__literal__aux___main___at_lean_parser_string__lit_view_value___spec__4(x_10, x_11, x_5);
x_14 = l_lean_parser_finish__comment__block___closed__2;
lean::inc(x_14);
x_16 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_14, x_13);
x_17 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_16);
return x_17;
}
else
{
obj* x_18; uint8 x_20; obj* x_21; obj* x_22; obj* x_23; 
x_18 = lean::cnstr_get(x_4, 0);
lean::inc(x_18);
x_20 = lean::cnstr_get_scalar<uint8>(x_4, sizeof(void*)*1);
if (lean::is_shared(x_4)) {
 lean::dec(x_4);
 x_21 = lean::box(0);
} else {
 lean::cnstr_release(x_4, 0);
 x_21 = x_4;
}
if (lean::is_scalar(x_21)) {
 x_22 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_22 = x_21;
}
lean::cnstr_set(x_22, 0, x_18);
lean::cnstr_set_scalar(x_22, sizeof(void*)*1, x_20);
x_23 = x_22;
return x_23;
}
}
}
obj* _init_l_lean_parser_string__lit_view_value___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parse__string__literal___at_lean_parser_string__lit_view_value___spec__1), 1, 0);
return x_0;
}
}
obj* l_lean_parser_string__lit_view_value(obj* x_0) {
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
obj* x_3; obj* x_5; obj* x_6; obj* x_9; obj* x_10; obj* x_13; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_5 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 x_5 = x_0;
}
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
lean::dec(x_3);
x_9 = l_lean_parser_string__lit_view_value___closed__1;
x_10 = l_string_join___closed__1;
lean::inc(x_10);
lean::inc(x_9);
x_13 = l_lean_parser_parsec__t_run___at_lean_parser_parsec_parse___spec__1___rarg(x_9, x_6, x_10);
if (lean::obj_tag(x_13) == 0)
{
obj* x_16; 
lean::dec(x_13);
lean::dec(x_5);
x_16 = lean::box(0);
return x_16;
}
else
{
obj* x_17; obj* x_20; 
x_17 = lean::cnstr_get(x_13, 0);
lean::inc(x_17);
lean::dec(x_13);
if (lean::is_scalar(x_5)) {
 x_20 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_20 = x_5;
}
lean::cnstr_set(x_20, 0, x_17);
return x_20;
}
}
}
}
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_string__lit_view_value___spec__2___boxed(obj* x_0, obj* x_1) {
_start:
{
uint32 x_2; obj* x_3; 
x_2 = lean::unbox_uint32(x_0);
x_3 = l_lean_parser_monad__parsec_ch___at_lean_parser_string__lit_view_value___spec__2(x_2, x_1);
return x_3;
}
}
obj* l_lean_parser_ident_parser___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_6; obj* x_7; obj* x_9; obj* x_11; 
lean::inc(x_2);
lean::inc(x_1);
x_6 = l_lean_parser_token(x_1, x_2, x_3);
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_6, 1);
lean::inc(x_9);
if (lean::is_shared(x_6)) {
 lean::dec(x_6);
 x_11 = lean::box(0);
} else {
 lean::cnstr_release(x_6, 0);
 lean::cnstr_release(x_6, 1);
 x_11 = x_6;
}
if (lean::obj_tag(x_7) == 0)
{
obj* x_12; obj* x_14; obj* x_16; obj* x_18; obj* x_19; 
x_12 = lean::cnstr_get(x_7, 0);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_7, 1);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_7, 2);
lean::inc(x_16);
if (lean::is_shared(x_7)) {
 lean::dec(x_7);
 x_18 = lean::box(0);
} else {
 lean::cnstr_release(x_7, 0);
 lean::cnstr_release(x_7, 1);
 lean::cnstr_release(x_7, 2);
 x_18 = x_7;
}
switch (lean::obj_tag(x_12)) {
case 0:
{
obj* x_23; 
lean::dec(x_18);
lean::dec(x_12);
x_23 = lean::box(0);
x_19 = x_23;
goto lbl_20;
}
case 1:
{
obj* x_27; obj* x_29; obj* x_30; obj* x_32; obj* x_33; obj* x_34; obj* x_35; 
lean::dec(x_11);
lean::dec(x_1);
lean::dec(x_2);
x_27 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_27);
if (lean::is_scalar(x_18)) {
 x_29 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_29 = x_18;
}
lean::cnstr_set(x_29, 0, x_12);
lean::cnstr_set(x_29, 1, x_14);
lean::cnstr_set(x_29, 2, x_27);
x_30 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_29);
lean::inc(x_27);
x_32 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_27, x_30);
x_33 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_32, x_0);
x_34 = l_lean_parser_parsec__t_try__mk__res___rarg(x_33);
x_35 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_9);
return x_35;
}
case 2:
{
obj* x_38; 
lean::dec(x_18);
lean::dec(x_12);
x_38 = lean::box(0);
x_19 = x_38;
goto lbl_20;
}
default:
{
obj* x_41; 
lean::dec(x_18);
lean::dec(x_12);
x_41 = lean::box(0);
x_19 = x_41;
goto lbl_20;
}
}
lbl_20:
{
obj* x_43; obj* x_44; obj* x_45; obj* x_48; obj* x_49; obj* x_51; obj* x_54; obj* x_55; obj* x_57; obj* x_58; obj* x_59; obj* x_60; 
lean::dec(x_19);
x_43 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_43, 0, x_2);
x_44 = lean::box(0);
x_45 = l_string_join___closed__1;
lean::inc(x_0);
lean::inc(x_45);
x_48 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_45, x_0, x_43, x_44, x_1, x_14, x_9);
x_49 = lean::cnstr_get(x_48, 0);
lean::inc(x_49);
x_51 = lean::cnstr_get(x_48, 1);
lean::inc(x_51);
lean::dec(x_48);
x_54 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_49);
x_55 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_55);
x_57 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_55, x_54);
x_58 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_57, x_0);
x_59 = l_lean_parser_parsec__t_try__mk__res___rarg(x_58);
if (lean::is_scalar(x_11)) {
 x_60 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_60 = x_11;
}
lean::cnstr_set(x_60, 0, x_59);
lean::cnstr_set(x_60, 1, x_51);
return x_60;
}
}
else
{
obj* x_63; uint8 x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_71; obj* x_72; obj* x_73; obj* x_74; 
lean::dec(x_1);
lean::dec(x_2);
x_63 = lean::cnstr_get(x_7, 0);
lean::inc(x_63);
x_65 = lean::cnstr_get_scalar<uint8>(x_7, sizeof(void*)*1);
if (lean::is_shared(x_7)) {
 lean::dec(x_7);
 x_66 = lean::box(0);
} else {
 lean::cnstr_release(x_7, 0);
 x_66 = x_7;
}
if (lean::is_scalar(x_66)) {
 x_67 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_67 = x_66;
}
lean::cnstr_set(x_67, 0, x_63);
lean::cnstr_set_scalar(x_67, sizeof(void*)*1, x_65);
x_68 = x_67;
x_69 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_69);
x_71 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_69, x_68);
x_72 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_71, x_0);
x_73 = l_lean_parser_parsec__t_try__mk__res___rarg(x_72);
if (lean::is_scalar(x_11)) {
 x_74 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_74 = x_11;
}
lean::cnstr_set(x_74, 0, x_73);
lean::cnstr_set(x_74, 1, x_9);
return x_74;
}
}
}
obj* _init_l_lean_parser_ident_parser___rarg___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_string("identifier");
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_1, 0, x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_ident_parser___rarg___lambda__1), 4, 1);
lean::closure_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_lean_parser_ident_parser___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; 
x_1 = l_lean_parser_ident_parser___rarg___closed__1;
lean::inc(x_1);
x_3 = lean::apply_2(x_0, lean::box(0), x_1);
return x_3;
}
}
obj* l_lean_parser_ident_parser(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_ident_parser___rarg), 1, 0);
return x_2;
}
}
obj* l_lean_parser_ident_parser_tokens(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::box(0);
return x_4;
}
}
obj* _init_l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_5; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("NOT_AN_IDENT");
lean::inc(x_1);
x_3 = l_lean_parser_substring_of__string(x_1);
lean::inc(x_0);
x_5 = lean_name_mk_string(x_0, x_1);
lean::inc(x_0);
lean::inc(x_0);
x_8 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_8, 0, x_0);
lean::cnstr_set(x_8, 1, x_3);
lean::cnstr_set(x_8, 2, x_5);
lean::cnstr_set(x_8, 3, x_0);
lean::cnstr_set(x_8, 4, x_0);
return x_8;
}
}
obj* _init_l_lean_parser_ident_parser_view___rarg___lambda__1___closed__2() {
_start:
{
obj* x_0; 
x_0 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
lean::inc(x_0);
return x_0;
}
}
obj* l_lean_parser_ident_parser_view___rarg___lambda__1(obj* x_0) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_2; 
lean::dec(x_0);
x_2 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__2;
lean::inc(x_2);
return x_2;
}
case 1:
{
obj* x_4; 
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
lean::dec(x_0);
return x_4;
}
case 2:
{
obj* x_8; 
lean::dec(x_0);
x_8 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__2;
lean::inc(x_8);
return x_8;
}
default:
{
obj* x_11; 
lean::dec(x_0);
x_11 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__2;
lean::inc(x_11);
return x_11;
}
}
}
}
obj* l_lean_parser_ident_parser_view___rarg___lambda__2(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_lean_parser_ident_parser_view___rarg___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_ident_parser_view___rarg___lambda__1), 1, 0);
return x_0;
}
}
obj* _init_l_lean_parser_ident_parser_view___rarg___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_ident_parser_view___rarg___lambda__2), 1, 0);
return x_0;
}
}
obj* l_lean_parser_ident_parser_view___rarg(obj* x_0) {
_start:
{
obj* x_2; obj* x_3; obj* x_6; 
lean::dec(x_0);
x_2 = l_lean_parser_ident_parser_view___rarg___closed__1;
x_3 = l_lean_parser_ident_parser_view___rarg___closed__2;
lean::inc(x_3);
lean::inc(x_2);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_2);
lean::cnstr_set(x_6, 1, x_3);
return x_6;
}
}
obj* l_lean_parser_ident_parser_view(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_ident_parser_view___rarg), 1, 0);
return x_2;
}
}
obj* _init_l_lean_parser_raw__ident_parser___rarg___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_token_4__ident_x_27), 3, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_with__trailing___at_lean_parser_token___spec__3), 4, 0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_bind___at_lean_parser_with__trailing___spec__2___rarg), 5, 2);
lean::closure_set(x_2, 0, x_0);
lean::closure_set(x_2, 1, x_1);
return x_2;
}
}
obj* l_lean_parser_raw__ident_parser___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; 
x_1 = l_lean_parser_raw__ident_parser___rarg___closed__1;
lean::inc(x_1);
x_3 = lean::apply_2(x_0, lean::box(0), x_1);
return x_3;
}
}
obj* l_lean_parser_raw__ident_parser(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_raw__ident_parser___rarg), 1, 0);
return x_2;
}
}
obj* l_lean_parser_raw__ident_parser_tokens(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::box(0);
return x_4;
}
}
obj* l_lean_parser_raw__ident_parser_view___rarg(obj* x_0) {
_start:
{
obj* x_2; obj* x_3; obj* x_6; 
lean::dec(x_0);
x_2 = l_lean_parser_ident_parser_view___rarg___closed__1;
x_3 = l_lean_parser_ident_parser_view___rarg___closed__2;
lean::inc(x_3);
lean::inc(x_2);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_2);
lean::cnstr_set(x_6, 1, x_3);
return x_6;
}
}
obj* l_lean_parser_raw__ident_parser_view(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_raw__ident_parser_view___rarg), 1, 0);
return x_2;
}
}
obj* l_lean_parser_symbol__or__ident___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_6; obj* x_7; obj* x_9; obj* x_11; 
lean::inc(x_2);
lean::inc(x_1);
x_6 = l_lean_parser_token(x_1, x_2, x_3);
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_6, 1);
lean::inc(x_9);
if (lean::is_shared(x_6)) {
 lean::dec(x_6);
 x_11 = lean::box(0);
} else {
 lean::cnstr_release(x_6, 0);
 lean::cnstr_release(x_6, 1);
 x_11 = x_6;
}
if (lean::obj_tag(x_7) == 0)
{
obj* x_12; obj* x_14; obj* x_16; obj* x_18; obj* x_19; 
x_12 = lean::cnstr_get(x_7, 0);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_7, 1);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_7, 2);
lean::inc(x_16);
if (lean::is_shared(x_7)) {
 lean::dec(x_7);
 x_18 = lean::box(0);
} else {
 lean::cnstr_release(x_7, 0);
 lean::cnstr_release(x_7, 1);
 lean::cnstr_release(x_7, 2);
 x_18 = x_7;
}
switch (lean::obj_tag(x_12)) {
case 0:
{
obj* x_21; obj* x_23; obj* x_26; 
x_21 = lean::cnstr_get(x_12, 0);
lean::inc(x_21);
x_23 = lean::cnstr_get(x_21, 1);
lean::inc(x_23);
lean::dec(x_21);
x_26 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_26, 0, x_23);
x_19 = x_26;
goto lbl_20;
}
case 1:
{
obj* x_27; obj* x_29; obj* x_32; obj* x_33; 
x_27 = lean::cnstr_get(x_12, 0);
lean::inc(x_27);
x_29 = lean::cnstr_get(x_27, 1);
lean::inc(x_29);
lean::dec(x_27);
x_32 = l_lean_parser_substring_to__string(x_29);
x_33 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_33, 0, x_32);
x_19 = x_33;
goto lbl_20;
}
case 2:
{
obj* x_34; 
x_34 = lean::box(0);
x_19 = x_34;
goto lbl_20;
}
default:
{
obj* x_35; 
x_35 = lean::box(0);
x_19 = x_35;
goto lbl_20;
}
}
lbl_20:
{
uint8 x_36; 
if (lean::obj_tag(x_19) == 0)
{
uint8 x_39; 
lean::dec(x_19);
x_39 = 1;
x_36 = x_39;
goto lbl_37;
}
else
{
obj* x_40; uint8 x_43; 
x_40 = lean::cnstr_get(x_19, 0);
lean::inc(x_40);
lean::dec(x_19);
x_43 = lean::string_dec_eq(x_40, x_0);
lean::dec(x_40);
if (x_43 == 0)
{
uint8 x_45; 
x_45 = 1;
x_36 = x_45;
goto lbl_37;
}
else
{
uint8 x_46; 
x_46 = 0;
x_36 = x_46;
goto lbl_37;
}
}
lbl_37:
{
if (x_36 == 0)
{
obj* x_50; obj* x_52; obj* x_53; obj* x_54; obj* x_56; obj* x_57; obj* x_58; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_50 = l_lean_parser_finish__comment__block___closed__2;
lean::inc(x_50);
if (lean::is_scalar(x_18)) {
 x_52 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_52 = x_18;
}
lean::cnstr_set(x_52, 0, x_12);
lean::cnstr_set(x_52, 1, x_14);
lean::cnstr_set(x_52, 2, x_50);
x_53 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_52);
x_54 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_54);
x_56 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_54, x_53);
x_57 = l_lean_parser_parsec__t_try__mk__res___rarg(x_56);
if (lean::is_scalar(x_11)) {
 x_58 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_58 = x_11;
}
lean::cnstr_set(x_58, 0, x_57);
lean::cnstr_set(x_58, 1, x_9);
return x_58;
}
else
{
obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_65; obj* x_66; obj* x_68; 
x_59 = l_string_quote(x_0);
x_60 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_60, 0, x_59);
x_61 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_61, 0, x_2);
x_62 = lean::box(0);
x_63 = l_string_join___closed__1;
lean::inc(x_63);
x_65 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_63, x_60, x_61, x_62, x_1, x_14, x_9);
x_66 = lean::cnstr_get(x_65, 0);
lean::inc(x_66);
x_68 = lean::cnstr_get(x_65, 1);
lean::inc(x_68);
lean::dec(x_65);
if (lean::obj_tag(x_66) == 0)
{
obj* x_71; obj* x_73; obj* x_76; obj* x_78; obj* x_79; obj* x_80; obj* x_82; obj* x_83; obj* x_84; 
x_71 = lean::cnstr_get(x_66, 1);
lean::inc(x_71);
x_73 = lean::cnstr_get(x_66, 2);
lean::inc(x_73);
lean::dec(x_66);
x_76 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_76);
if (lean::is_scalar(x_18)) {
 x_78 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_78 = x_18;
}
lean::cnstr_set(x_78, 0, x_12);
lean::cnstr_set(x_78, 1, x_71);
lean::cnstr_set(x_78, 2, x_76);
x_79 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_73, x_78);
x_80 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_79);
lean::inc(x_76);
x_82 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_76, x_80);
x_83 = l_lean_parser_parsec__t_try__mk__res___rarg(x_82);
if (lean::is_scalar(x_11)) {
 x_84 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_84 = x_11;
}
lean::cnstr_set(x_84, 0, x_83);
lean::cnstr_set(x_84, 1, x_68);
return x_84;
}
else
{
obj* x_87; uint8 x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_96; obj* x_97; obj* x_98; 
lean::dec(x_18);
lean::dec(x_12);
x_87 = lean::cnstr_get(x_66, 0);
lean::inc(x_87);
x_89 = lean::cnstr_get_scalar<uint8>(x_66, sizeof(void*)*1);
if (lean::is_shared(x_66)) {
 lean::dec(x_66);
 x_90 = lean::box(0);
} else {
 lean::cnstr_release(x_66, 0);
 x_90 = x_66;
}
if (lean::is_scalar(x_90)) {
 x_91 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_91 = x_90;
}
lean::cnstr_set(x_91, 0, x_87);
lean::cnstr_set_scalar(x_91, sizeof(void*)*1, x_89);
x_92 = x_91;
x_93 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_92);
x_94 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_94);
x_96 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_94, x_93);
x_97 = l_lean_parser_parsec__t_try__mk__res___rarg(x_96);
if (lean::is_scalar(x_11)) {
 x_98 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_98 = x_11;
}
lean::cnstr_set(x_98, 0, x_97);
lean::cnstr_set(x_98, 1, x_68);
return x_98;
}
}
}
}
}
else
{
obj* x_102; uint8 x_104; obj* x_105; obj* x_106; obj* x_107; obj* x_108; obj* x_110; obj* x_111; obj* x_112; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_102 = lean::cnstr_get(x_7, 0);
lean::inc(x_102);
x_104 = lean::cnstr_get_scalar<uint8>(x_7, sizeof(void*)*1);
if (lean::is_shared(x_7)) {
 lean::dec(x_7);
 x_105 = lean::box(0);
} else {
 lean::cnstr_release(x_7, 0);
 x_105 = x_7;
}
if (lean::is_scalar(x_105)) {
 x_106 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_106 = x_105;
}
lean::cnstr_set(x_106, 0, x_102);
lean::cnstr_set_scalar(x_106, sizeof(void*)*1, x_104);
x_107 = x_106;
x_108 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_108);
x_110 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_108, x_107);
x_111 = l_lean_parser_parsec__t_try__mk__res___rarg(x_110);
if (lean::is_scalar(x_11)) {
 x_112 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_112 = x_11;
}
lean::cnstr_set(x_112, 0, x_111);
lean::cnstr_set(x_112, 1, x_9);
return x_112;
}
}
}
obj* l_lean_parser_symbol__or__ident___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__or__ident___rarg___lambda__1), 4, 1);
lean::closure_set(x_2, 0, x_1);
x_3 = lean::apply_2(x_0, lean::box(0), x_2);
return x_3;
}
}
obj* l_lean_parser_symbol__or__ident(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__or__ident___rarg), 2, 0);
return x_2;
}
}
obj* l_lean_parser_symbol__or__ident_tokens(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::box(0);
return x_6;
}
}
obj* l_lean_parser_symbol__or__ident_view___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; obj* x_7; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = l_mjoin___rarg___closed__1;
lean::inc(x_4);
lean::inc(x_4);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_4);
lean::cnstr_set(x_7, 1, x_4);
return x_7;
}
}
obj* l_lean_parser_symbol__or__ident_view(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__or__ident_view___rarg), 2, 0);
return x_2;
}
}
obj* l_lean_parser_symbol__core___at_lean_parser_unicode__symbol_lean_parser_has__tokens___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_9; obj* x_10; obj* x_12; obj* x_14; obj* x_16; 
lean::dec(x_1);
lean::inc(x_4);
lean::inc(x_3);
x_9 = l_lean_parser_token(x_3, x_4, x_5);
x_10 = lean::cnstr_get(x_9, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_9, 1);
lean::inc(x_12);
if (lean::is_shared(x_9)) {
 lean::dec(x_9);
 x_14 = lean::box(0);
} else {
 lean::cnstr_release(x_9, 0);
 lean::cnstr_release(x_9, 1);
 x_14 = x_9;
}
lean::inc(x_0);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_16, 0, x_0);
if (lean::obj_tag(x_10) == 0)
{
obj* x_17; obj* x_19; obj* x_21; obj* x_23; obj* x_24; 
x_17 = lean::cnstr_get(x_10, 0);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_10, 1);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_10, 2);
lean::inc(x_21);
if (lean::is_shared(x_10)) {
 lean::dec(x_10);
 x_23 = lean::box(0);
} else {
 lean::cnstr_release(x_10, 0);
 lean::cnstr_release(x_10, 1);
 lean::cnstr_release(x_10, 2);
 x_23 = x_10;
}
switch (lean::obj_tag(x_17)) {
case 0:
{
obj* x_27; obj* x_29; uint8 x_32; 
lean::dec(x_14);
x_27 = lean::cnstr_get(x_17, 0);
lean::inc(x_27);
x_29 = lean::cnstr_get(x_27, 1);
lean::inc(x_29);
lean::dec(x_27);
x_32 = lean::string_dec_eq(x_0, x_29);
lean::dec(x_0);
if (x_32 == 0)
{
obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_39; obj* x_41; 
x_34 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_34, 0, x_4);
x_35 = lean::box(0);
x_36 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_29, x_2, x_34, x_35, x_3, x_19, x_12);
x_37 = lean::cnstr_get(x_36, 0);
lean::inc(x_37);
x_39 = lean::cnstr_get(x_36, 1);
lean::inc(x_39);
if (lean::is_shared(x_36)) {
 lean::dec(x_36);
 x_41 = lean::box(0);
} else {
 lean::cnstr_release(x_36, 0);
 lean::cnstr_release(x_36, 1);
 x_41 = x_36;
}
if (lean::obj_tag(x_37) == 0)
{
obj* x_42; obj* x_44; obj* x_47; obj* x_49; obj* x_50; obj* x_51; obj* x_53; obj* x_54; obj* x_55; obj* x_56; 
x_42 = lean::cnstr_get(x_37, 1);
lean::inc(x_42);
x_44 = lean::cnstr_get(x_37, 2);
lean::inc(x_44);
lean::dec(x_37);
x_47 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_47);
if (lean::is_scalar(x_23)) {
 x_49 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_49 = x_23;
}
lean::cnstr_set(x_49, 0, x_17);
lean::cnstr_set(x_49, 1, x_42);
lean::cnstr_set(x_49, 2, x_47);
x_50 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_44, x_49);
x_51 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_21, x_50);
lean::inc(x_47);
x_53 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_47, x_51);
x_54 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_53, x_16);
x_55 = l_lean_parser_parsec__t_try__mk__res___rarg(x_54);
if (lean::is_scalar(x_41)) {
 x_56 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_56 = x_41;
}
lean::cnstr_set(x_56, 0, x_55);
lean::cnstr_set(x_56, 1, x_39);
return x_56;
}
else
{
obj* x_59; uint8 x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_68; obj* x_69; obj* x_70; obj* x_71; 
lean::dec(x_23);
lean::dec(x_17);
x_59 = lean::cnstr_get(x_37, 0);
lean::inc(x_59);
x_61 = lean::cnstr_get_scalar<uint8>(x_37, sizeof(void*)*1);
if (lean::is_shared(x_37)) {
 lean::dec(x_37);
 x_62 = lean::box(0);
} else {
 lean::cnstr_release(x_37, 0);
 x_62 = x_37;
}
if (lean::is_scalar(x_62)) {
 x_63 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_63 = x_62;
}
lean::cnstr_set(x_63, 0, x_59);
lean::cnstr_set_scalar(x_63, sizeof(void*)*1, x_61);
x_64 = x_63;
x_65 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_21, x_64);
x_66 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_66);
x_68 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_66, x_65);
x_69 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_68, x_16);
x_70 = l_lean_parser_parsec__t_try__mk__res___rarg(x_69);
if (lean::is_scalar(x_41)) {
 x_71 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_71 = x_41;
}
lean::cnstr_set(x_71, 0, x_70);
lean::cnstr_set(x_71, 1, x_39);
return x_71;
}
}
else
{
obj* x_76; obj* x_78; obj* x_79; obj* x_80; obj* x_82; obj* x_83; obj* x_84; obj* x_85; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_29);
x_76 = l_lean_parser_finish__comment__block___closed__2;
lean::inc(x_76);
if (lean::is_scalar(x_23)) {
 x_78 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_78 = x_23;
}
lean::cnstr_set(x_78, 0, x_17);
lean::cnstr_set(x_78, 1, x_19);
lean::cnstr_set(x_78, 2, x_76);
x_79 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_21, x_78);
x_80 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_80);
x_82 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_80, x_79);
x_83 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_82, x_16);
x_84 = l_lean_parser_parsec__t_try__mk__res___rarg(x_83);
x_85 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_85, 0, x_84);
lean::cnstr_set(x_85, 1, x_12);
return x_85;
}
}
case 1:
{
obj* x_89; 
lean::dec(x_23);
lean::dec(x_17);
lean::dec(x_0);
x_89 = lean::box(0);
x_24 = x_89;
goto lbl_25;
}
case 2:
{
obj* x_93; 
lean::dec(x_23);
lean::dec(x_17);
lean::dec(x_0);
x_93 = lean::box(0);
x_24 = x_93;
goto lbl_25;
}
default:
{
obj* x_97; 
lean::dec(x_23);
lean::dec(x_17);
lean::dec(x_0);
x_97 = lean::box(0);
x_24 = x_97;
goto lbl_25;
}
}
lbl_25:
{
obj* x_99; obj* x_100; obj* x_101; obj* x_103; obj* x_104; obj* x_106; obj* x_109; obj* x_110; obj* x_112; obj* x_113; obj* x_114; obj* x_115; 
lean::dec(x_24);
x_99 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_99, 0, x_4);
x_100 = lean::box(0);
x_101 = l_string_join___closed__1;
lean::inc(x_101);
x_103 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_101, x_2, x_99, x_100, x_3, x_19, x_12);
x_104 = lean::cnstr_get(x_103, 0);
lean::inc(x_104);
x_106 = lean::cnstr_get(x_103, 1);
lean::inc(x_106);
lean::dec(x_103);
x_109 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_21, x_104);
x_110 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_110);
x_112 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_110, x_109);
x_113 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_112, x_16);
x_114 = l_lean_parser_parsec__t_try__mk__res___rarg(x_113);
if (lean::is_scalar(x_14)) {
 x_115 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_115 = x_14;
}
lean::cnstr_set(x_115, 0, x_114);
lean::cnstr_set(x_115, 1, x_106);
return x_115;
}
}
else
{
obj* x_120; uint8 x_122; obj* x_123; obj* x_124; obj* x_125; obj* x_126; obj* x_128; obj* x_129; obj* x_130; obj* x_131; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
x_120 = lean::cnstr_get(x_10, 0);
lean::inc(x_120);
x_122 = lean::cnstr_get_scalar<uint8>(x_10, sizeof(void*)*1);
if (lean::is_shared(x_10)) {
 lean::dec(x_10);
 x_123 = lean::box(0);
} else {
 lean::cnstr_release(x_10, 0);
 x_123 = x_10;
}
if (lean::is_scalar(x_123)) {
 x_124 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_124 = x_123;
}
lean::cnstr_set(x_124, 0, x_120);
lean::cnstr_set_scalar(x_124, sizeof(void*)*1, x_122);
x_125 = x_124;
x_126 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_126);
x_128 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_126, x_125);
x_129 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_128, x_16);
x_130 = l_lean_parser_parsec__t_try__mk__res___rarg(x_129);
if (lean::is_scalar(x_14)) {
 x_131 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_131 = x_14;
}
lean::cnstr_set(x_131, 0, x_130);
lean::cnstr_set(x_131, 1, x_12);
return x_131;
}
}
}
obj* l_list_foldl___main___at_lean_parser_unicode__symbol_lean_parser_has__tokens___spec__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_6; 
lean::dec(x_1);
x_6 = lean::apply_3(x_0, x_2, x_3, x_4);
return x_6;
}
else
{
obj* x_7; obj* x_9; obj* x_12; 
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_1, 1);
lean::inc(x_9);
lean::dec(x_1);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_orelse___at_lean_parser_parse__bin__lit___spec__1___rarg), 5, 2);
lean::closure_set(x_12, 0, x_0);
lean::closure_set(x_12, 1, x_7);
x_0 = x_12;
x_1 = x_9;
goto _start;
}
}
}
obj* l_lean_parser_combinators_any__of___at_lean_parser_unicode__symbol_lean_parser_has__tokens___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_5; obj* x_6; obj* x_7; obj* x_11; 
lean::dec(x_0);
x_5 = lean::box(0);
x_6 = l_lean_parser_combinators_any__of___rarg___closed__1;
x_7 = l_mjoin___rarg___closed__1;
lean::inc(x_5);
lean::inc(x_7);
lean::inc(x_6);
x_11 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_6, x_7, x_5, x_5, x_1, x_2, x_3);
return x_11;
}
else
{
obj* x_12; obj* x_14; obj* x_17; 
x_12 = lean::cnstr_get(x_0, 0);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_0, 1);
lean::inc(x_14);
lean::dec(x_0);
x_17 = l_list_foldl___main___at_lean_parser_unicode__symbol_lean_parser_has__tokens___spec__3(x_12, x_14, x_1, x_2, x_3);
return x_17;
}
}
}
obj* l_lean_parser_unicode__symbol_lean_parser_has__tokens___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
lean::inc(x_2);
x_4 = l_lean_parser_symbol_tokens___rarg(x_0, x_2);
x_5 = l_lean_parser_symbol_tokens___rarg(x_1, x_2);
x_6 = lean::box(0);
x_7 = l_lean_parser_list_cons_tokens___rarg(x_5, x_6);
x_8 = l_lean_parser_list_cons_tokens___rarg(x_4, x_7);
x_9 = l_lean_parser_tokens___rarg(x_8);
x_10 = l_lean_parser_tokens___rarg(x_9);
return x_10;
}
}
obj* l_lean_parser_unicode__symbol_lean_parser_has__tokens(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_unicode__symbol_lean_parser_has__tokens___rarg), 3, 0);
return x_4;
}
}
obj* l_lean_parser_unicode__symbol_lean_parser_has__view___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_26; obj* x_27; 
x_4 = l_string_trim(x_1);
lean::inc(x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_6, 0, x_4);
lean::inc(x_3);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_unicode__symbol_lean_parser_has__tokens___spec__1), 6, 3);
lean::closure_set(x_8, 0, x_4);
lean::closure_set(x_8, 1, x_3);
lean::closure_set(x_8, 2, x_6);
x_9 = l_string_trim(x_2);
lean::inc(x_9);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_11, 0, x_9);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_unicode__symbol_lean_parser_has__tokens___spec__1), 6, 3);
lean::closure_set(x_12, 0, x_9);
lean::closure_set(x_12, 1, x_3);
lean::closure_set(x_12, 2, x_11);
x_13 = lean::box(0);
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_12);
lean::cnstr_set(x_14, 1, x_13);
x_15 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_15, 0, x_8);
lean::cnstr_set(x_15, 1, x_14);
lean::inc(x_15);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_any__of___at_lean_parser_unicode__symbol_lean_parser_has__tokens___spec__2), 4, 1);
lean::closure_set(x_17, 0, x_15);
x_18 = l_lean_parser_basic__parser__m_monad;
x_19 = l_lean_parser_basic__parser__m_monad__except;
x_20 = l_lean_parser_basic__parser__m_lean_parser_monad__parsec;
x_21 = l_lean_parser_basic__parser__m_alternative;
lean::inc(x_21);
lean::inc(x_20);
lean::inc(x_19);
lean::inc(x_18);
x_26 = l_lean_parser_combinators_any__of_view___rarg(x_18, x_19, x_20, x_21, x_15);
x_27 = l_lean_parser_combinators_monad__lift_view___rarg(x_0, x_17, x_26);
return x_27;
}
}
obj* l_lean_parser_unicode__symbol_lean_parser_has__view(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_unicode__symbol_lean_parser_has__view___rarg), 4, 0);
return x_2;
}
}
obj* l_lean_parser_unicode__symbol___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_4 = l_string_trim(x_1);
lean::inc(x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_6, 0, x_4);
lean::inc(x_3);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_unicode__symbol_lean_parser_has__tokens___spec__1), 6, 3);
lean::closure_set(x_8, 0, x_4);
lean::closure_set(x_8, 1, x_3);
lean::closure_set(x_8, 2, x_6);
x_9 = l_string_trim(x_2);
lean::inc(x_9);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_11, 0, x_9);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_unicode__symbol_lean_parser_has__tokens___spec__1), 6, 3);
lean::closure_set(x_12, 0, x_9);
lean::closure_set(x_12, 1, x_3);
lean::closure_set(x_12, 2, x_11);
x_13 = lean::box(0);
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_12);
lean::cnstr_set(x_14, 1, x_13);
x_15 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_15, 0, x_8);
lean::cnstr_set(x_15, 1, x_14);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_any__of___at_lean_parser_unicode__symbol_lean_parser_has__tokens___spec__2), 4, 1);
lean::closure_set(x_16, 0, x_15);
x_17 = lean::apply_2(x_0, lean::box(0), x_16);
return x_17;
}
}
obj* l_lean_parser_unicode__symbol(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_unicode__symbol___rarg), 4, 0);
return x_2;
}
}
obj* l_lean_parser_unicode__symbol_view__default___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_8; 
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_8 = lean::box(0);
return x_8;
}
}
obj* l_lean_parser_unicode__symbol_view__default(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_unicode__symbol_view__default___rarg), 4, 0);
return x_2;
}
}
obj* l_rbmap_find___main___at_lean_parser_indexed___spec__1___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_find___main___at_lean_parser_token__map_insert___spec__2___rarg(x_0, x_1);
return x_2;
}
}
obj* l_rbmap_find___main___at_lean_parser_indexed___spec__1(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_find___main___at_lean_parser_indexed___spec__1___rarg), 2, 0);
return x_2;
}
}
obj* l_option_to__monad___main___at_lean_parser_indexed___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
lean::dec(x_1);
if (lean::obj_tag(x_0) == 0)
{
obj* x_6; 
lean::dec(x_0);
x_6 = l_lean_parser_parsec__t_failure___at_lean_parser_token___spec__4___rarg(x_2, x_3);
return x_6;
}
else
{
obj* x_7; obj* x_10; obj* x_12; obj* x_13; 
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
lean::dec(x_0);
x_10 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_10);
x_12 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_12, 0, x_7);
lean::cnstr_set(x_12, 1, x_2);
lean::cnstr_set(x_12, 2, x_10);
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_3);
return x_13;
}
}
}
obj* l_option_to__monad___main___at_lean_parser_indexed___spec__2(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_option_to__monad___main___at_lean_parser_indexed___spec__2___rarg), 4, 0);
return x_2;
}
}
obj* l_rbmap_find___main___at_lean_parser_indexed___spec__3___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_find___main___at_lean_parser_token__map_insert___spec__2___rarg(x_0, x_1);
return x_2;
}
}
obj* l_rbmap_find___main___at_lean_parser_indexed___spec__3(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_find___main___at_lean_parser_indexed___spec__3___rarg), 2, 0);
return x_2;
}
}
obj* l_rbmap_find___main___at_lean_parser_indexed___spec__4___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_find___main___at_lean_parser_token__map_insert___spec__2___rarg(x_0, x_1);
return x_2;
}
}
obj* l_rbmap_find___main___at_lean_parser_indexed___spec__4(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_find___main___at_lean_parser_indexed___spec__4___rarg), 2, 0);
return x_2;
}
}
obj* l_rbmap_find___main___at_lean_parser_indexed___spec__5___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_find___main___at_lean_parser_token__map_insert___spec__2___rarg(x_0, x_1);
return x_2;
}
}
obj* l_rbmap_find___main___at_lean_parser_indexed___spec__5(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_find___main___at_lean_parser_indexed___spec__5___rarg), 2, 0);
return x_2;
}
}
obj* _init_l_lean_parser_indexed___rarg___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("ident");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* l_lean_parser_indexed___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_13; 
lean::dec(x_1);
lean::dec(x_0);
x_7 = lean::box(0);
x_8 = l_string_join___closed__1;
x_9 = l_mjoin___rarg___closed__1;
lean::inc(x_7);
lean::inc(x_9);
lean::inc(x_8);
x_13 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_8, x_9, x_7, x_7, x_2, x_3, x_4);
return x_13;
}
else
{
obj* x_14; 
x_14 = lean::cnstr_get(x_1, 0);
lean::inc(x_14);
lean::dec(x_1);
switch (lean::obj_tag(x_14)) {
case 0:
{
obj* x_17; obj* x_20; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_29; obj* x_31; obj* x_32; obj* x_34; obj* x_35; 
x_17 = lean::cnstr_get(x_14, 0);
lean::inc(x_17);
lean::dec(x_14);
x_20 = lean::cnstr_get(x_17, 1);
lean::inc(x_20);
lean::dec(x_17);
x_23 = lean::box(0);
x_24 = lean_name_mk_string(x_23, x_20);
x_25 = l_rbnode_find___main___at_lean_parser_token__map_insert___spec__2___rarg(x_0, x_24);
x_26 = l_option_to__monad___main___at_lean_parser_indexed___spec__2___rarg(x_25, x_2, x_3, x_4);
x_27 = lean::cnstr_get(x_26, 0);
lean::inc(x_27);
x_29 = lean::cnstr_get(x_26, 1);
lean::inc(x_29);
if (lean::is_shared(x_26)) {
 lean::dec(x_26);
 x_31 = lean::box(0);
} else {
 lean::cnstr_release(x_26, 0);
 lean::cnstr_release(x_26, 1);
 x_31 = x_26;
}
x_32 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_32);
x_34 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_32, x_27);
if (lean::is_scalar(x_31)) {
 x_35 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_35 = x_31;
}
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_29);
return x_35;
}
case 1:
{
obj* x_37; obj* x_39; obj* x_40; obj* x_41; obj* x_43; obj* x_45; obj* x_46; obj* x_48; obj* x_49; 
lean::dec(x_14);
x_37 = l_lean_parser_indexed___rarg___lambda__1___closed__1;
lean::inc(x_37);
x_39 = l_rbnode_find___main___at_lean_parser_token__map_insert___spec__2___rarg(x_0, x_37);
x_40 = l_option_to__monad___main___at_lean_parser_indexed___spec__2___rarg(x_39, x_2, x_3, x_4);
x_41 = lean::cnstr_get(x_40, 0);
lean::inc(x_41);
x_43 = lean::cnstr_get(x_40, 1);
lean::inc(x_43);
if (lean::is_shared(x_40)) {
 lean::dec(x_40);
 x_45 = lean::box(0);
} else {
 lean::cnstr_release(x_40, 0);
 lean::cnstr_release(x_40, 1);
 x_45 = x_40;
}
x_46 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_46);
x_48 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_46, x_41);
if (lean::is_scalar(x_45)) {
 x_49 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_49 = x_45;
}
lean::cnstr_set(x_49, 0, x_48);
lean::cnstr_set(x_49, 1, x_43);
return x_49;
}
case 2:
{
obj* x_50; obj* x_53; obj* x_56; obj* x_57; obj* x_58; obj* x_60; obj* x_62; obj* x_63; obj* x_65; obj* x_66; 
x_50 = lean::cnstr_get(x_14, 0);
lean::inc(x_50);
lean::dec(x_14);
x_53 = lean::cnstr_get(x_50, 0);
lean::inc(x_53);
lean::dec(x_50);
x_56 = l_rbnode_find___main___at_lean_parser_token__map_insert___spec__2___rarg(x_0, x_53);
x_57 = l_option_to__monad___main___at_lean_parser_indexed___spec__2___rarg(x_56, x_2, x_3, x_4);
x_58 = lean::cnstr_get(x_57, 0);
lean::inc(x_58);
x_60 = lean::cnstr_get(x_57, 1);
lean::inc(x_60);
if (lean::is_shared(x_57)) {
 lean::dec(x_57);
 x_62 = lean::box(0);
} else {
 lean::cnstr_release(x_57, 0);
 lean::cnstr_release(x_57, 1);
 x_62 = x_57;
}
x_63 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_63);
x_65 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_63, x_58);
if (lean::is_scalar(x_62)) {
 x_66 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_66 = x_62;
}
lean::cnstr_set(x_66, 0, x_65);
lean::cnstr_set(x_66, 1, x_60);
return x_66;
}
default:
{
obj* x_68; obj* x_69; obj* x_70; obj* x_75; obj* x_76; obj* x_78; obj* x_80; 
lean::dec(x_14);
x_68 = lean::box(0);
x_69 = l_string_join___closed__1;
x_70 = l_mjoin___rarg___closed__1;
lean::inc(x_2);
lean::inc(x_68);
lean::inc(x_70);
lean::inc(x_69);
x_75 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_69, x_70, x_68, x_68, x_2, x_3, x_4);
x_76 = lean::cnstr_get(x_75, 0);
lean::inc(x_76);
x_78 = lean::cnstr_get(x_75, 1);
lean::inc(x_78);
if (lean::is_shared(x_75)) {
 lean::dec(x_75);
 x_80 = lean::box(0);
} else {
 lean::cnstr_release(x_75, 0);
 lean::cnstr_release(x_75, 1);
 x_80 = x_75;
}
if (lean::obj_tag(x_76) == 0)
{
obj* x_81; obj* x_83; obj* x_85; obj* x_88; obj* x_89; obj* x_90; obj* x_92; obj* x_95; obj* x_96; 
x_81 = lean::cnstr_get(x_76, 0);
lean::inc(x_81);
x_83 = lean::cnstr_get(x_76, 1);
lean::inc(x_83);
x_85 = lean::cnstr_get(x_76, 2);
lean::inc(x_85);
lean::dec(x_76);
x_88 = l_rbnode_find___main___at_lean_parser_token__map_insert___spec__2___rarg(x_0, x_81);
x_89 = l_option_to__monad___main___at_lean_parser_indexed___spec__2___rarg(x_88, x_2, x_83, x_78);
x_90 = lean::cnstr_get(x_89, 0);
lean::inc(x_90);
x_92 = lean::cnstr_get(x_89, 1);
lean::inc(x_92);
lean::dec(x_89);
x_95 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_85, x_90);
if (lean::is_scalar(x_80)) {
 x_96 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_96 = x_80;
}
lean::cnstr_set(x_96, 0, x_95);
lean::cnstr_set(x_96, 1, x_92);
return x_96;
}
else
{
obj* x_99; uint8 x_101; obj* x_102; obj* x_103; obj* x_104; obj* x_105; 
lean::dec(x_0);
lean::dec(x_2);
x_99 = lean::cnstr_get(x_76, 0);
lean::inc(x_99);
x_101 = lean::cnstr_get_scalar<uint8>(x_76, sizeof(void*)*1);
if (lean::is_shared(x_76)) {
 lean::dec(x_76);
 x_102 = lean::box(0);
} else {
 lean::cnstr_release(x_76, 0);
 x_102 = x_76;
}
if (lean::is_scalar(x_102)) {
 x_103 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_103 = x_102;
}
lean::cnstr_set(x_103, 0, x_99);
lean::cnstr_set_scalar(x_103, sizeof(void*)*1, x_101);
x_104 = x_103;
if (lean::is_scalar(x_80)) {
 x_105 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_105 = x_80;
}
lean::cnstr_set(x_105, 0, x_104);
lean::cnstr_set(x_105, 1, x_78);
return x_105;
}
}
}
}
}
}
obj* _init_l_lean_parser_indexed___rarg___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_peek__token), 3, 0);
return x_0;
}
}
obj* l_lean_parser_indexed___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_5; obj* x_7; obj* x_8; 
lean::dec(x_1);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_indexed___rarg___lambda__1), 5, 1);
lean::closure_set(x_4, 0, x_2);
x_5 = l_lean_parser_indexed___rarg___closed__1;
lean::inc(x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_bind___at_lean_parser_with__trailing___spec__2___rarg), 5, 2);
lean::closure_set(x_7, 0, x_5);
lean::closure_set(x_7, 1, x_4);
x_8 = lean::apply_2(x_0, lean::box(0), x_7);
return x_8;
}
}
obj* l_lean_parser_indexed(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_indexed___rarg), 3, 0);
return x_2;
}
}
void initialize_init_lean_parser_combinators();
void initialize_init_lean_parser_string__literal();
static bool _G_initialized = false;
void initialize_init_lean_parser_token() {
 if (_G_initialized) return;
 _G_initialized = true;
 initialize_init_lean_parser_combinators();
 initialize_init_lean_parser_string__literal();
 l_lean_parser_match__token___closed__1 = _init_l_lean_parser_match__token___closed__1();
 l_lean_parser_match__token___closed__2 = _init_l_lean_parser_match__token___closed__2();
 l___private_init_lean_parser_token_1__finish__comment__block__aux___main___closed__1 = _init_l___private_init_lean_parser_token_1__finish__comment__block__aux___main___closed__1();
 l___private_init_lean_parser_token_1__finish__comment__block__aux___main___closed__2 = _init_l___private_init_lean_parser_token_1__finish__comment__block__aux___main___closed__2();
 l___private_init_lean_parser_token_1__finish__comment__block__aux___main___closed__3 = _init_l___private_init_lean_parser_token_1__finish__comment__block__aux___main___closed__3();
 l___private_init_lean_parser_token_1__finish__comment__block__aux___main___closed__4 = _init_l___private_init_lean_parser_token_1__finish__comment__block__aux___main___closed__4();
 l_lean_parser_finish__comment__block___closed__1 = _init_l_lean_parser_finish__comment__block___closed__1();
 l_lean_parser_finish__comment__block___closed__2 = _init_l_lean_parser_finish__comment__block___closed__2();
 l_lean_parser_parsec__t_lookahead___at___private_init_lean_parser_token_2__whitespace__aux___main___spec__4___closed__1 = _init_l_lean_parser_parsec__t_lookahead___at___private_init_lean_parser_token_2__whitespace__aux___main___spec__4___closed__1();
 l_lean_parser_parsec__t_lookahead___at___private_init_lean_parser_token_2__whitespace__aux___main___spec__4___closed__2 = _init_l_lean_parser_parsec__t_lookahead___at___private_init_lean_parser_token_2__whitespace__aux___main___spec__4___closed__2();
 l___private_init_lean_parser_token_2__whitespace__aux___main___closed__1 = _init_l___private_init_lean_parser_token_2__whitespace__aux___main___closed__1();
 l___private_init_lean_parser_token_2__whitespace__aux___main___closed__2 = _init_l___private_init_lean_parser_token_2__whitespace__aux___main___closed__2();
 l___private_init_lean_parser_token_2__whitespace__aux___main___closed__3 = _init_l___private_init_lean_parser_token_2__whitespace__aux___main___closed__3();
 l_lean_parser_with__trailing___rarg___closed__1 = _init_l_lean_parser_with__trailing___rarg___closed__1();
 l_lean_parser_raw_view___rarg___lambda__3___closed__1 = _init_l_lean_parser_raw_view___rarg___lambda__3___closed__1();
 l_lean_parser_raw_view___rarg___closed__1 = _init_l_lean_parser_raw_view___rarg___closed__1();
 l_lean_parser_raw_view___rarg___closed__2 = _init_l_lean_parser_raw_view___rarg___closed__2();
 l_lean_parser_detail__ident__part__escaped = _init_l_lean_parser_detail__ident__part__escaped();
 l_lean_parser_detail__ident__part__escaped_has__view_x_27___lambda__1___closed__1 = _init_l_lean_parser_detail__ident__part__escaped_has__view_x_27___lambda__1___closed__1();
 l_lean_parser_detail__ident__part__escaped_has__view_x_27 = _init_l_lean_parser_detail__ident__part__escaped_has__view_x_27();
 l_lean_parser_detail__ident__part__escaped_has__view = _init_l_lean_parser_detail__ident__part__escaped_has__view();
 l_lean_parser_detail__ident__part = _init_l_lean_parser_detail__ident__part();
 l_lean_parser_detail__ident__part_has__view_x_27___lambda__1___closed__1 = _init_l_lean_parser_detail__ident__part_has__view_x_27___lambda__1___closed__1();
 l_lean_parser_detail__ident__part_has__view_x_27___lambda__1___closed__2 = _init_l_lean_parser_detail__ident__part_has__view_x_27___lambda__1___closed__2();
 l_lean_parser_detail__ident__part_has__view_x_27___lambda__1___closed__3 = _init_l_lean_parser_detail__ident__part_has__view_x_27___lambda__1___closed__3();
 l_lean_parser_detail__ident__part_has__view_x_27___lambda__2___closed__1 = _init_l_lean_parser_detail__ident__part_has__view_x_27___lambda__2___closed__1();
 l_lean_parser_detail__ident__part_has__view_x_27___lambda__2___closed__2 = _init_l_lean_parser_detail__ident__part_has__view_x_27___lambda__2___closed__2();
 l_lean_parser_detail__ident__part_has__view_x_27 = _init_l_lean_parser_detail__ident__part_has__view_x_27();
 l_lean_parser_detail__ident__part_has__view = _init_l_lean_parser_detail__ident__part_has__view();
 l_lean_parser_detail__ident__part_parser_lean_parser_has__tokens = _init_l_lean_parser_detail__ident__part_parser_lean_parser_has__tokens();
 l_lean_parser_detail__ident__part_parser_lean_parser_has__view = _init_l_lean_parser_detail__ident__part_parser_lean_parser_has__view();
 l_lean_parser_detail__ident__part_parser___closed__1 = _init_l_lean_parser_detail__ident__part_parser___closed__1();
 l_lean_parser_detail__ident__suffix = _init_l_lean_parser_detail__ident__suffix();
 l_lean_parser_detail__ident__suffix_has__view_x_27___lambda__1___closed__1 = _init_l_lean_parser_detail__ident__suffix_has__view_x_27___lambda__1___closed__1();
 l_lean_parser_detail__ident__suffix_has__view_x_27 = _init_l_lean_parser_detail__ident__suffix_has__view_x_27();
 l_lean_parser_detail__ident__suffix_has__view = _init_l_lean_parser_detail__ident__suffix_has__view();
 l_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens = _init_l_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens();
 l_lean_parser_detail__ident__suffix_parser_lean_parser_has__view = _init_l_lean_parser_detail__ident__suffix_parser_lean_parser_has__view();
 l_lean_parser_detail__ident__suffix_parser___closed__1 = _init_l_lean_parser_detail__ident__suffix_parser___closed__1();
 l_lean_parser_detail__ident = _init_l_lean_parser_detail__ident();
 l_lean_parser_detail__ident_has__view_x_27___lambda__1___closed__1 = _init_l_lean_parser_detail__ident_has__view_x_27___lambda__1___closed__1();
 l_lean_parser_detail__ident_has__view_x_27___lambda__1___closed__2 = _init_l_lean_parser_detail__ident_has__view_x_27___lambda__1___closed__2();
 l_lean_parser_detail__ident_has__view_x_27___lambda__2___closed__1 = _init_l_lean_parser_detail__ident_has__view_x_27___lambda__2___closed__1();
 l_lean_parser_detail__ident_has__view_x_27 = _init_l_lean_parser_detail__ident_has__view_x_27();
 l_lean_parser_detail__ident_has__view = _init_l_lean_parser_detail__ident_has__view();
 l_lean_parser_detail__ident_x_27___closed__1 = _init_l_lean_parser_detail__ident_x_27___closed__1();
 l_lean_parser_rec__t_run__parsec___at_lean_parser_detail__ident_parser___spec__1___closed__1 = _init_l_lean_parser_rec__t_run__parsec___at_lean_parser_detail__ident_parser___spec__1___closed__1();
 l_lean_parser_detail__ident_parser___closed__1 = _init_l_lean_parser_detail__ident_parser___closed__1();
 l_lean_parser_detail__ident_parser___closed__2 = _init_l_lean_parser_detail__ident_parser___closed__2();
 l_lean_parser_monad__parsec_foldl__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__21___closed__1 = _init_l_lean_parser_monad__parsec_foldl__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__21___closed__1();
 l_lean_parser_monad__parsec_foldl__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__21___closed__2 = _init_l_lean_parser_monad__parsec_foldl__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__21___closed__2();
 l_lean_parser_monad__parsec_many1__aux_x_27___main___at_lean_parser_parse__bin__lit___spec__2___closed__1 = _init_l_lean_parser_monad__parsec_many1__aux_x_27___main___at_lean_parser_parse__bin__lit___spec__2___closed__1();
 l_lean_parser_monad__parsec_many1__aux_x_27___main___at_lean_parser_parse__bin__lit___spec__2___closed__2 = _init_l_lean_parser_monad__parsec_many1__aux_x_27___main___at_lean_parser_parse__bin__lit___spec__2___closed__2();
 l_lean_parser_number = _init_l_lean_parser_number();
 l_lean_parser_number_has__view_x_27___lambda__1___closed__1 = _init_l_lean_parser_number_has__view_x_27___lambda__1___closed__1();
 l_lean_parser_number_has__view_x_27___lambda__1___closed__2 = _init_l_lean_parser_number_has__view_x_27___lambda__1___closed__2();
 l_lean_parser_number_has__view_x_27___lambda__1___closed__3 = _init_l_lean_parser_number_has__view_x_27___lambda__1___closed__3();
 l_lean_parser_number_has__view_x_27___lambda__1___closed__4 = _init_l_lean_parser_number_has__view_x_27___lambda__1___closed__4();
 l_lean_parser_number_has__view_x_27___lambda__1___closed__5 = _init_l_lean_parser_number_has__view_x_27___lambda__1___closed__5();
 l_lean_parser_number_has__view_x_27___lambda__1___closed__6 = _init_l_lean_parser_number_has__view_x_27___lambda__1___closed__6();
 l_lean_parser_number_has__view_x_27___lambda__2___closed__1 = _init_l_lean_parser_number_has__view_x_27___lambda__2___closed__1();
 l_lean_parser_number_has__view_x_27___lambda__2___closed__2 = _init_l_lean_parser_number_has__view_x_27___lambda__2___closed__2();
 l_lean_parser_number_has__view_x_27 = _init_l_lean_parser_number_has__view_x_27();
 l_lean_parser_number_has__view = _init_l_lean_parser_number_has__view();
 l_lean_parser_number_x_27___closed__1 = _init_l_lean_parser_number_x_27___closed__1();
 l_lean_parser_string__lit = _init_l_lean_parser_string__lit();
 l_lean_parser_string__lit_has__view_x_27 = _init_l_lean_parser_string__lit_has__view_x_27();
 l_lean_parser_string__lit_has__view = _init_l_lean_parser_string__lit_has__view();
 l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__4___closed__1 = _init_l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__4___closed__1();
 l_lean_parser_string__lit_x_27___closed__1 = _init_l_lean_parser_string__lit_x_27___closed__1();
 l_lean_parser_token___closed__1 = _init_l_lean_parser_token___closed__1();
 l_lean_parser_number_parser___rarg___closed__1 = _init_l_lean_parser_number_parser___rarg___closed__1();
 l_lean_parser_number_parser_view___rarg___closed__1 = _init_l_lean_parser_number_parser_view___rarg___closed__1();
 l_lean_parser_number_parser_view___rarg___closed__2 = _init_l_lean_parser_number_parser_view___rarg___closed__2();
 l_lean_parser_string__lit_parser___rarg___closed__1 = _init_l_lean_parser_string__lit_parser___rarg___closed__1();
 l_lean_parser_string__lit_parser_view___rarg___closed__1 = _init_l_lean_parser_string__lit_parser_view___rarg___closed__1();
 l_lean_parser_string__lit_parser_view___rarg___closed__2 = _init_l_lean_parser_string__lit_parser_view___rarg___closed__2();
 l_lean_parser_string__lit_view_value___closed__1 = _init_l_lean_parser_string__lit_view_value___closed__1();
 l_lean_parser_ident_parser___rarg___closed__1 = _init_l_lean_parser_ident_parser___rarg___closed__1();
 l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1 = _init_l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1();
 l_lean_parser_ident_parser_view___rarg___lambda__1___closed__2 = _init_l_lean_parser_ident_parser_view___rarg___lambda__1___closed__2();
 l_lean_parser_ident_parser_view___rarg___closed__1 = _init_l_lean_parser_ident_parser_view___rarg___closed__1();
 l_lean_parser_ident_parser_view___rarg___closed__2 = _init_l_lean_parser_ident_parser_view___rarg___closed__2();
 l_lean_parser_raw__ident_parser___rarg___closed__1 = _init_l_lean_parser_raw__ident_parser___rarg___closed__1();
 l_lean_parser_indexed___rarg___lambda__1___closed__1 = _init_l_lean_parser_indexed___rarg___lambda__1___closed__1();
 l_lean_parser_indexed___rarg___closed__1 = _init_l_lean_parser_indexed___rarg___closed__1();
}
