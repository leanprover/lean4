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
obj* l_lean_parser_detail__ident__suffix_parser_lean_parser_has__view___lambda__2(uint32, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__16(obj*, obj*, obj*);
obj* l_lean_parser_detail__ident__part_parser_lean_parser_has__tokens;
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__28(obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__22(obj*, obj*, obj*);
obj* l_list_mfoldr___main___at_lean_parser_number_x_27___spec__13(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser___spec__10(obj*);
obj* l_lean_parser_match__token___closed__2;
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_parse__oct__lit___spec__6___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__4(obj*, obj*, obj*, obj*);
obj* l_lean_parser_parsec__t_bind__mk__res___rarg(obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while1___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__1(obj*, obj*, obj*);
obj* l_reader__t_orelse___at_lean_parser_parse__bin__lit___spec__1(obj*);
obj* l_lean_parser_unicode__symbol_lean_parser_has__tokens(obj*, obj*);
obj* l_lean_parser_monad__parsec_many1__aux_x_27___main___at_lean_parser_parse__bin__lit___spec__2___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__6(uint32, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__6___boxed(obj*, obj*, obj*, obj*);
uint8 l_char_is__whitespace(uint32);
obj* l_lean_parser_monad__parsec_take__while1___at_lean_parser_parse__oct__lit___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__19___rarg(obj*, obj*);
extern obj* l_lean_parser_parse__hex__digit___rarg___lambda__5___closed__1;
obj* l_lean_parser_id__part___at___private_init_lean_parser_token_4__ident_x_27___spec__1(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_foldl__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__21___lambda__2___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__9(obj*, obj*, obj*);
obj* l_lean_parser_trie_match__prefix___rarg(obj*, obj*);
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_parse__oct__lit___spec__7___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_detail__ident__suffix_has__view;
obj* l_lean_parser_match__token(obj*, obj*, obj*);
obj* l_lean_parser_number_parser_view___rarg___closed__2;
extern uint8 l_true_decidable;
obj* l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__4(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser___spec__8(obj*);
obj* l_lean_parser_number_x_27___closed__1;
obj* l___private_init_lean_parser_parsec_6__take__while__aux_x_27___main___at___private_init_lean_parser_token_2__whitespace__aux___main___spec__6(obj*, uint8, obj*);
obj* l_lean_parser_monad__parsec_str__core___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__3(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_raw_view___rarg(obj*, obj*, obj*, obj*, obj*, uint8);
obj* l_lean_parser_detail__ident__part_has__view;
extern obj* l_lean_parser_parse__hex__digit___rarg___lambda__3___closed__1;
obj* l_lean_parser_detail__ident__part_has__view_x_27___lambda__1___closed__2;
obj* l_lean_parser_number_has__view_x_27___lambda__2___closed__1;
obj* l_lean_parser_monad__parsec_error___at_lean_parser_number_x_27___spec__12___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_raw___rarg___lambda__3(uint8, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_finish__comment__block___closed__1;
obj* l_reader__t_bind___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__3(obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_string__lit_view_value___spec__3(obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__2(uint32, obj*, obj*, obj*);
obj* l_lean_parser_number;
obj* l_reader__t_orelse___at_lean_parser_parse__bin__lit___spec__1___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_token_4__ident_x_27(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1(obj*);
obj* l_lean_parser_raw__str_view__default___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_combinators_many___rarg___closed__1;
obj* l_lean_parser_symbol__or__ident___rarg(obj*, obj*);
obj* l_lean_parser_raw__str_view__default(obj*);
obj* l_lean_parser_as__substring___rarg___lambda__2(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_parse__oct__lit___spec__5___boxed(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_token_1__finish__comment__block__aux___main(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__21(obj*);
obj* l_lean_parser_monad__parsec_take__while1___at_lean_parser_detail__ident__part_parser___spec__1(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_many1__aux_x_27___main___at_lean_parser_parse__bin__lit___spec__2(uint32, uint32, obj*, obj*, obj*, obj*);
obj* l_lean_parser_raw___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_parsec__t_lookahead___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__10___boxed(obj*, obj*, obj*, obj*, obj*);
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
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__4(obj*, obj*, obj*, obj*);
obj* l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__4___closed__1;
obj* l_lean_parser_parsec__t_lookahead___at_lean_parser_detail__ident__suffix_parser___spec__1(obj*, obj*, obj*, uint32, obj*);
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
extern uint32 l_lean_id__end__escape;
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__18(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__9(obj*);
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser___spec__11(obj*, obj*, obj*);
obj* l_lean_parser_number_view_to__nat(obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_init_lean_parser_token_4__ident_x_27___spec__4___boxed(obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_basic__parser__m_monad;
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
obj* l_reader__t_lift___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__1(obj*);
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
extern obj* l___private_init_data_string_basic_4__to__nat__core___main___closed__2;
obj* l_reader__t_alternative___rarg(obj*, obj*);
obj* l_lean_parser_unicode__symbol_view__default___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_foldl___at___private_init_lean_parser_token_4__ident_x_27___spec__20(obj*, uint32, obj*, obj*, obj*);
obj* l_list_enum__from___main___rarg(obj*, obj*);
obj* l_lean_parser_detail__ident__part_has__view_x_27___lambda__1___closed__1;
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_number_x_27___spec__4___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_detail__ident_has__view_x_27;
obj* l_lean_parser_parsec__t_lookahead___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__10(uint32, obj*, obj*, obj*, obj*);
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
obj* l_lean_parser_combinators_node___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__5(obj*, obj*, obj*, obj*, obj*, obj*);
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
obj* l_lean_parser_monad__parsec_foldl__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__21(uint32, obj*, obj*, obj*, obj*, obj*);
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
obj* l_lean_parser_monad__parsec_foldl__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__21___lambda__1(uint32, obj*, obj*, obj*);
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
obj* l_lean_parser_detail__ident__suffix_parser_lean_parser_has__view___lambda__1(obj*, obj*, obj*, obj*, obj*, obj*);
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
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_parse__hex__lit___spec__2(uint32, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_number_x_27___spec__2(uint32, obj*, obj*, obj*);
extern obj* l_lean_name_to__string___closed__1;
obj* l_lean_parser_number_has__view_x_27___lambda__1___closed__5;
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__8(obj*);
obj* l_lean_parser_symbol__or__ident_view___rarg(obj*, obj*);
obj* l_function_comp___rarg(obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__14(obj*, obj*, obj*);
obj* l_lean_parser_parsec__t_lookahead___at___private_init_lean_parser_token_4__ident_x_27___spec__19(uint32, obj*, obj*, obj*);
obj* l_lean_parser_string__lit_parser_view___rarg___closed__2;
obj* l_lean_parser_number_view_of__nat(obj*);
obj* l_lean_parser_try__view___at_lean_parser_number_parser___spec__1(obj*);
obj* l_lean_parser_number_parser___rarg___closed__1;
obj* l_lean_parser_number_has__view_x_27;
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
obj* l_lean_parser_monad__parsec_foldl___at___private_init_lean_parser_token_4__ident_x_27___spec__20___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__7___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_unicode__symbol(obj*);
obj* l_lean_parser_peek__token(obj*, obj*, obj*);
obj* l___private_init_lean_parser_token_3__update__trailing(obj*, obj*);
obj* l_lean_parser_tokens___rarg(obj*);
obj* l_option_get__or__else___main___rarg(obj*, obj*);
uint8 l_lean_is__id__rest(uint32);
obj* l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_view_value___spec__7(obj*);
obj* l___private_init_lean_parser_parsec_6__take__while__aux_x_27___main___at___private_init_lean_parser_token_2__whitespace__aux___main___spec__3___boxed(obj*, obj*, obj*);
obj* l_lean_parser_string__lit_x_27___lambda__1(obj*, obj*, obj*, obj*);
obj* l_lean_parser_detail__ident__part_parser_lean_parser_has__view___lambda__3(obj*, obj*, obj*, obj*);
obj* l_lean_parser_raw__ident_parser_view(obj*);
obj* l_lean_parser_raw__str_lean_parser_has__view(obj*);
obj* l_lean_parser_monad__parsec_foldl__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__21___lambda__1___boxed(obj*, obj*, obj*, obj*);
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
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_parse__oct__lit___spec__4___boxed(obj*, obj*, obj*, obj*, obj*);
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
obj* l_lean_parser_monad__parsec_error___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__8___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while1___at_lean_parser_number_x_27___spec__1(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__9___boxed(obj*, obj*, obj*, obj*);
obj* l_rbmap_find___main___at_lean_parser_indexed___spec__5(obj*);
obj* l_lean_parser_token___closed__1;
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__12(obj*);
namespace lean {
uint8 nat_dec_le(obj*, obj*);
}
namespace lean {
obj* uint32_to_nat(uint32);
}
obj* l_lean_parser_rec__t_lean_parser_monad__parsec___rarg(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_str__core___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_parser_raw__str_lean_parser_has__view___rarg(obj*, obj*, obj*, obj*, uint8);
obj* l_lean_parser_number_x_27___lambda__1(obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while1___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__8(obj*, obj*, obj*);
obj* l_rbmap_find___main___at_lean_parser_indexed___spec__1___rarg(obj*, obj*);
obj* l_lean_parser_syntax_mk__node(obj*, obj*);
obj* l_lean_parser_monad__parsec_unexpected__at___at_lean_parser_string__lit_view_value___spec__9___rarg(obj*, obj*, obj*);
obj* l_lean_parser_detail__ident_has__view_x_27___lambda__1___closed__2;
obj* l_lean_parser_match__token___lambda__1(obj*);
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_parse__oct__lit___spec__3(uint32, obj*, obj*, obj*);
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
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_parse__oct__lit___spec__2(uint32, uint32, obj*, obj*, obj*);
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
extern uint32 l_lean_id__begin__escape;
obj* l_rbmap_find___main___at_lean_parser_indexed___spec__3(obj*);
namespace lean {
obj* string_iterator_offset(obj*);
}
obj* l_list_foldl___main___at_lean_parser_unicode__symbol_lean_parser_has__tokens___spec__3(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_token_7__to__nat__core(obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_curr___at___private_init_lean_parser_token_4__ident_x_27___spec__2___rarg(obj*, obj*);
obj* l_lean_parser_with__trailing___rarg___lambda__2(obj*, obj*, obj*, obj*);
obj* l_lean_parser_parsec__t_failure___at_lean_parser_token___spec__4(obj*, obj*);
obj* l_lean_parser_symbol__or__ident_view(obj*);
obj* l_lean_parser_raw(obj*);
obj* l_lean_parser_monad__parsec_take__while1___at_lean_parser_parse__oct__lit___spec__1(uint32, obj*, obj*, obj*);
obj* l_lean_parser_raw_view___rarg___closed__2;
obj* l_lean_parser_detail__ident_has__view_x_27___lambda__2___closed__1;
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_parse__oct__lit___spec__5(uint32, obj*, obj*, obj*);
obj* l_lean_parser_string__lit_parser_view___rarg___closed__1;
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
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_parse__oct__lit___spec__6(uint32, obj*, obj*, obj*, obj*);
obj* l_list_mfoldl___main___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__6(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
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
obj* l_lean_parser_monad__parsec_str__core___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__2(obj*, obj*, obj*, obj*, obj*, obj*);
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
obj* l_lean_parser_monad__parsec_foldl__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__21___lambda__2(uint32, uint32, obj*, obj*, obj*);
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
obj* l_reader__t_bind___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__3___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
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
obj* l_lean_parser_parsec__t_lookahead___at_lean_parser_detail__ident__suffix_parser___spec__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_raw_view(obj*);
obj* l_lean_parser_ident_parser_view___rarg___lambda__1(obj*);
obj* l_lean_parser_number_parser_view(obj*);
obj* l_lean_parser_number_has__view_x_27___lambda__2(obj*);
obj* l_lean_parser_parse__string__literal__aux___main___at_lean_parser_string__lit_view_value___spec__4(obj*, obj*, obj*);
obj* l_lean_parser_parsec__t_lookahead___at___private_init_lean_parser_token_4__ident_x_27___spec__19___boxed(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__5(obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_5__mk__consumed__result___rarg(uint8, obj*);
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser___spec__7(obj*, obj*, obj*);
obj* l_lean_parser_combinators_monad__lift_view___rarg(obj*, obj*, obj*);
obj* l_lean_parser_combinators_seq__right_view___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_reader__t_monad___rarg(obj*);
obj* l_lean_parser_detail__ident;
obj* l_lean_parser_parsec__t_lookahead___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__view___spec__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_detail__ident__part_parser_lean_parser_has__view___lambda__2(obj*, obj*, obj*, obj*);
obj* l_lean_parser_parsec__t_lookahead___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__view___spec__1(uint32, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_token_7__to__nat__core___main(obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_init_lean_parser_token_4__ident_x_27___spec__6___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser___spec__2___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_number_x_27___lambda__2(obj*, obj*, obj*, obj*);
extern "C" obj* lean_name_mk_numeral(obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser___spec__10___rarg(obj*, obj*);
obj* l_lean_parser_detail__ident__part__escaped;
uint8 l_lean_is__id__first(uint32);
obj* l_lean_parser_monad__parsec_foldl__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__21___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_nat_repr(obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_parse__oct__lit___spec__4(uint32, uint32, obj*, obj*, obj*);
obj* l_lean_parser_parse__string__literal___at_lean_parser_string__lit_x_27___spec__1(obj*, obj*, obj*);
obj* l___private_init_lean_parser_token_1__finish__comment__block__aux___main___closed__4;
namespace lean {
uint32 uint32_of_nat(obj*);
}
namespace lean {
obj* nat_mul(obj*, obj*);
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser___spec__4(obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_parse__hex__lit___spec__2___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__23(obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__9___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_3__mk__string__result___rarg(obj*, obj*);
obj* l_lean_parser_symbol__or__ident_tokens(obj*, obj*, obj*);
obj* l_lean_parser_with__trailing(obj*);
obj* l_reader__t_lift___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__1___rarg(obj*, obj*, obj*, obj*, obj*);
uint8 l_lean_is__id__begin__escape(uint32);
obj* l_lean_parser_ident_parser_view(obj*);
obj* l_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens;
obj* l_lean_parser_number_has__view_x_27___lambda__1___closed__2;
obj* l_lean_parser_detail__ident__part_has__view_x_27___lambda__2(obj*);
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_number_x_27___spec__5(obj*, obj*, obj*);
obj* l_lean_parser_string__lit_has__view_x_27;
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__6(uint32, obj*, obj*, obj*);
obj* l_lean_parser_detail__ident__part__escaped_has__view_x_27___lambda__2(obj*);
extern obj* l___private_init_data_string_basic_4__to__nat__core___main___closed__1;
obj* l___private_init_lean_parser_token_1__finish__comment__block__aux(obj*, obj*, obj*, obj*, obj*);
namespace lean {
obj* nat_sub(obj*, obj*);
}
obj* l_lean_parser_string__lit_x_27(obj*, obj*, obj*);
obj* l_lean_parser_detail__ident__part_parser___closed__1;
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__27(obj*);
obj* l_lean_parser_number_x_27___lambda__3(obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_parse__oct__lit___spec__2___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_detail__ident__part_parser_lean_parser_has__view;
obj* l_lean_parser_detail__ident__part_has__view_x_27___lambda__2___closed__2;
obj* l_lean_parser_parse__bin__lit(obj*, obj*, obj*);
extern obj* l_lean_parser_basic__parser__m_lean_parser_monad__parsec;
obj* l_reader__t_bind___at_lean_parser_with__trailing___spec__2(obj*, obj*);
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
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_parse__oct__lit___spec__7(uint32, obj*, obj*, obj*);
obj* l_lean_parser_number_parser_view___rarg(obj*);
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__3(obj*, obj*, obj*);
obj* l_lean_parser_number_parser___rarg(obj*);
obj* l_lean_parser_detail__ident__suffix_parser_lean_parser_has__view___lambda__2___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_raw__str_lean_parser_has__tokens___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_substring_of__string(obj*);
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__7(uint32, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser___spec__6___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_string__lit_view_value(obj*);
obj* l_lean_parser_parse__quoted__char___at_lean_parser_string__lit_x_27___spec__3(obj*, obj*, obj*);
obj* l_lean_parser_ident_parser_tokens(obj*, obj*);
obj* l___private_init_lean_parser_rec_1__run__aux___at_lean_parser_detail__ident_parser___spec__3(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_parse__oct__lit___spec__3___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_number_x_27___spec__2___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_detail__ident__suffix_parser(obj*, obj*, obj*, obj*);
obj* l_reader__t_lift___at_lean_parser_detail__ident_x_27___spec__1(obj*);
obj* l_lean_parser_rec__t_recurse___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__4(obj*, obj*, obj*, obj*, obj*);
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
obj* x_9; obj* x_10; uint32 x_13; uint32 x_14; uint32 x_15; uint8 x_16; 
x_9 = lean::mk_nat_obj(1u);
x_10 = lean::nat_sub(x_0, x_9);
lean::dec(x_9);
lean::dec(x_0);
x_13 = lean::string_iterator_curr(x_2);
x_14 = 10;
x_15 = 55296;
x_16 = x_14 < x_15;
if (x_16 == 0)
{
uint32 x_17; uint8 x_18; 
x_17 = 57343;
x_18 = x_17 < x_14;
if (x_18 == 0)
{
uint32 x_19; uint8 x_20; 
x_19 = 0;
x_20 = x_13 == x_19;
if (x_20 == 0)
{
obj* x_21; uint8 x_22; 
x_21 = lean::string_iterator_next(x_2);
x_22 = 1;
x_0 = x_10;
x_1 = x_22;
x_2 = x_21;
goto _start;
}
else
{
obj* x_25; 
lean::dec(x_10);
x_25 = l___private_init_lean_parser_parsec_5__mk__consumed__result___rarg(x_1, x_2);
return x_25;
}
}
else
{
uint32 x_26; uint8 x_27; 
x_26 = 1114112;
x_27 = x_14 < x_26;
if (x_27 == 0)
{
uint32 x_28; uint8 x_29; 
x_28 = 0;
x_29 = x_13 == x_28;
if (x_29 == 0)
{
obj* x_30; uint8 x_31; 
x_30 = lean::string_iterator_next(x_2);
x_31 = 1;
x_0 = x_10;
x_1 = x_31;
x_2 = x_30;
goto _start;
}
else
{
obj* x_34; 
lean::dec(x_10);
x_34 = l___private_init_lean_parser_parsec_5__mk__consumed__result___rarg(x_1, x_2);
return x_34;
}
}
else
{
uint8 x_35; 
x_35 = x_13 == x_14;
if (x_35 == 0)
{
obj* x_36; uint8 x_37; 
x_36 = lean::string_iterator_next(x_2);
x_37 = 1;
x_0 = x_10;
x_1 = x_37;
x_2 = x_36;
goto _start;
}
else
{
obj* x_40; 
lean::dec(x_10);
x_40 = l___private_init_lean_parser_parsec_5__mk__consumed__result___rarg(x_1, x_2);
return x_40;
}
}
}
}
else
{
uint8 x_41; 
x_41 = x_13 == x_14;
if (x_41 == 0)
{
obj* x_42; uint8 x_43; 
x_42 = lean::string_iterator_next(x_2);
x_43 = 1;
x_0 = x_10;
x_1 = x_43;
x_2 = x_42;
goto _start;
}
else
{
obj* x_46; 
lean::dec(x_10);
x_46 = l___private_init_lean_parser_parsec_5__mk__consumed__result___rarg(x_1, x_2);
return x_46;
}
}
}
}
else
{
obj* x_48; 
lean::dec(x_0);
x_48 = l___private_init_lean_parser_parsec_5__mk__consumed__result___rarg(x_1, x_2);
return x_48;
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
obj* x_0; uint32 x_1; obj* x_3; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_11; obj* x_12; obj* x_14; uint32 x_15; obj* x_16; obj* x_18; obj* x_19; obj* x_20; obj* x_22; obj* x_23; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_30; obj* x_31; obj* x_32; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_51; 
x_0 = lean::mk_string("");
x_1 = l_lean_id__begin__escape;
lean::inc(x_0);
x_3 = lean::string_push(x_0, x_1);
lean::inc(x_3);
x_5 = l_string_quote(x_3);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_6, 0, x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_with__trailing___rarg___lambda__1), 2, 0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_lift___at_lean_parser_with__trailing___spec__1___rarg), 4, 1);
lean::closure_set(x_8, 0, x_7);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_detail__ident__part_parser_lean_parser_has__view___lambda__1), 6, 2);
lean::closure_set(x_9, 0, x_3);
lean::closure_set(x_9, 1, x_6);
lean::inc(x_8);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_bind___at_lean_parser_with__trailing___spec__2___rarg), 5, 2);
lean::closure_set(x_11, 0, x_8);
lean::closure_set(x_11, 1, x_9);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_detail__ident__part_parser_lean_parser_has__view___lambda__2), 4, 0);
lean::inc(x_8);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_bind___at_lean_parser_with__trailing___spec__2___rarg), 5, 2);
lean::closure_set(x_14, 0, x_8);
lean::closure_set(x_14, 1, x_12);
x_15 = l_lean_id__end__escape;
x_16 = lean::string_push(x_0, x_15);
lean::inc(x_16);
x_18 = l_string_quote(x_16);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_19, 0, x_18);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_detail__ident__part_parser_lean_parser_has__view___lambda__1), 6, 2);
lean::closure_set(x_20, 0, x_16);
lean::closure_set(x_20, 1, x_19);
lean::inc(x_8);
x_22 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_bind___at_lean_parser_with__trailing___spec__2___rarg), 5, 2);
lean::closure_set(x_22, 0, x_8);
lean::closure_set(x_22, 1, x_20);
x_23 = lean::box(0);
lean::inc(x_23);
x_25 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_25, 0, x_22);
lean::cnstr_set(x_25, 1, x_23);
x_26 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_26, 0, x_14);
lean::cnstr_set(x_26, 1, x_25);
x_27 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_27, 0, x_11);
lean::cnstr_set(x_27, 1, x_26);
x_28 = l_lean_parser_detail__ident__part__escaped;
lean::inc(x_28);
x_30 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__15), 5, 2);
lean::closure_set(x_30, 0, x_28);
lean::closure_set(x_30, 1, x_27);
x_31 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_detail__ident__part_parser_lean_parser_has__view___lambda__3), 4, 0);
x_32 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_bind___at_lean_parser_with__trailing___spec__2___rarg), 5, 2);
lean::closure_set(x_32, 0, x_8);
lean::closure_set(x_32, 1, x_31);
lean::inc(x_23);
x_34 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_34, 0, x_32);
lean::cnstr_set(x_34, 1, x_23);
x_35 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_35, 0, x_30);
lean::cnstr_set(x_35, 1, x_34);
x_36 = lean::mk_nat_obj(0u);
x_37 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_choice__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__29), 5, 2);
lean::closure_set(x_37, 0, x_35);
lean::closure_set(x_37, 1, x_36);
x_38 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_38, 0, x_37);
lean::cnstr_set(x_38, 1, x_23);
x_39 = l_lean_parser_basic__parser__m_monad;
x_40 = l_lean_parser_basic__parser__m_monad__except;
x_41 = l_lean_parser_basic__parser__m_lean_parser_monad__parsec;
x_42 = l_lean_parser_basic__parser__m_alternative;
x_43 = l_lean_parser_detail__ident__part;
x_44 = l_lean_parser_detail__ident__part_has__view;
lean::inc(x_44);
lean::inc(x_43);
lean::inc(x_42);
lean::inc(x_41);
lean::inc(x_40);
lean::inc(x_39);
x_51 = l_lean_parser_combinators_node_view___rarg(x_39, x_40, x_41, x_42, x_43, x_38, x_44);
return x_51;
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
obj* x_0; uint32 x_1; obj* x_3; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_11; obj* x_12; obj* x_14; uint32 x_15; obj* x_16; obj* x_18; obj* x_19; obj* x_20; obj* x_22; obj* x_23; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_30; obj* x_31; obj* x_32; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
x_0 = lean::mk_string("");
x_1 = l_lean_id__begin__escape;
lean::inc(x_0);
x_3 = lean::string_push(x_0, x_1);
lean::inc(x_3);
x_5 = l_string_quote(x_3);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_6, 0, x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_with__trailing___rarg___lambda__1), 2, 0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_lift___at_lean_parser_with__trailing___spec__1___rarg), 4, 1);
lean::closure_set(x_8, 0, x_7);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_detail__ident__part_parser_lean_parser_has__view___lambda__1), 6, 2);
lean::closure_set(x_9, 0, x_3);
lean::closure_set(x_9, 1, x_6);
lean::inc(x_8);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_bind___at_lean_parser_with__trailing___spec__2___rarg), 5, 2);
lean::closure_set(x_11, 0, x_8);
lean::closure_set(x_11, 1, x_9);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_detail__ident__part_parser___lambda__1), 4, 0);
lean::inc(x_8);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_bind___at_lean_parser_with__trailing___spec__2___rarg), 5, 2);
lean::closure_set(x_14, 0, x_8);
lean::closure_set(x_14, 1, x_12);
x_15 = l_lean_id__end__escape;
x_16 = lean::string_push(x_0, x_15);
lean::inc(x_16);
x_18 = l_string_quote(x_16);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_19, 0, x_18);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_detail__ident__part_parser_lean_parser_has__view___lambda__1), 6, 2);
lean::closure_set(x_20, 0, x_16);
lean::closure_set(x_20, 1, x_19);
lean::inc(x_8);
x_22 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_bind___at_lean_parser_with__trailing___spec__2___rarg), 5, 2);
lean::closure_set(x_22, 0, x_8);
lean::closure_set(x_22, 1, x_20);
x_23 = lean::box(0);
lean::inc(x_23);
x_25 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_25, 0, x_22);
lean::cnstr_set(x_25, 1, x_23);
x_26 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_26, 0, x_14);
lean::cnstr_set(x_26, 1, x_25);
x_27 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_27, 0, x_11);
lean::cnstr_set(x_27, 1, x_26);
x_28 = l_lean_parser_detail__ident__part__escaped;
lean::inc(x_28);
x_30 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__15), 5, 2);
lean::closure_set(x_30, 0, x_28);
lean::closure_set(x_30, 1, x_27);
x_31 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_detail__ident__part_parser___lambda__2), 4, 0);
x_32 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_bind___at_lean_parser_with__trailing___spec__2___rarg), 5, 2);
lean::closure_set(x_32, 0, x_8);
lean::closure_set(x_32, 1, x_31);
lean::inc(x_23);
x_34 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_34, 0, x_32);
lean::cnstr_set(x_34, 1, x_23);
x_35 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_35, 0, x_30);
lean::cnstr_set(x_35, 1, x_34);
x_36 = lean::mk_nat_obj(0u);
x_37 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_choice__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__29), 5, 2);
lean::closure_set(x_37, 0, x_35);
lean::closure_set(x_37, 1, x_36);
x_38 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_38, 0, x_37);
lean::cnstr_set(x_38, 1, x_23);
return x_38;
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
obj* l_reader__t_lift___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_6; 
lean::dec(x_1);
x_6 = lean::apply_3(x_0, x_2, x_3, x_4);
return x_6;
}
}
obj* l_reader__t_lift___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__1(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_lift___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__1___rarg), 5, 0);
return x_2;
}
}
obj* l_lean_parser_monad__parsec_str__core___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
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
obj* l_reader__t_bind___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__3___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
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
obj* l_reader__t_bind___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__3(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_bind___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__3___rarg), 6, 0);
return x_4;
}
}
obj* l_lean_parser_rec__t_recurse___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__4(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
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
obj* l_list_mfoldl___main___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__6(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
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
x_81 = l_list_mfoldl___main___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__6(x_0, x_74, x_17, x_3, x_4, x_76, x_21);
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
obj* l_lean_parser_combinators_node___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__5(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_8; obj* x_9; obj* x_11; obj* x_13; 
x_6 = lean::box(0);
lean::inc(x_0);
x_8 = l_list_mfoldl___main___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__6(x_0, x_6, x_1, x_2, x_3, x_4, x_5);
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
obj* l_lean_parser_monad__parsec_error___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__8___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
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
obj* l_lean_parser_monad__parsec_error___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__8(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__8___rarg), 8, 0);
return x_2;
}
}
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__7(uint32 x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
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
x_12 = l_lean_parser_monad__parsec_error___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__8___rarg(x_7, x_8, x_6, x_6, x_1, x_2, x_3, x_4);
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
uint32 x_22; uint8 x_23; 
x_22 = lean::string_iterator_curr(x_3);
x_23 = x_22 == x_0;
if (x_23 == 0)
{
obj* x_24; obj* x_25; obj* x_27; obj* x_29; obj* x_30; obj* x_31; obj* x_34; obj* x_35; obj* x_37; obj* x_39; obj* x_40; obj* x_42; obj* x_43; 
x_24 = l_char_quote__core(x_22);
x_25 = l_char_has__repr___closed__1;
lean::inc(x_25);
x_27 = lean::string_append(x_25, x_24);
lean::dec(x_24);
x_29 = lean::string_append(x_27, x_25);
x_30 = lean::box(0);
x_31 = l_mjoin___rarg___closed__1;
lean::inc(x_30);
lean::inc(x_31);
x_34 = l_lean_parser_monad__parsec_error___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__8___rarg(x_29, x_31, x_30, x_30, x_1, x_2, x_3, x_4);
x_35 = lean::cnstr_get(x_34, 0);
lean::inc(x_35);
x_37 = lean::cnstr_get(x_34, 1);
lean::inc(x_37);
if (lean::is_shared(x_34)) {
 lean::dec(x_34);
 x_39 = lean::box(0);
} else {
 lean::cnstr_release(x_34, 0);
 lean::cnstr_release(x_34, 1);
 x_39 = x_34;
}
x_40 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_40);
x_42 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_40, x_35);
if (lean::is_scalar(x_39)) {
 x_43 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_43 = x_39;
}
lean::cnstr_set(x_43, 0, x_42);
lean::cnstr_set(x_43, 1, x_37);
return x_43;
}
else
{
obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; 
lean::dec(x_1);
lean::dec(x_2);
x_46 = lean::string_iterator_next(x_3);
x_47 = lean::box(0);
x_48 = lean::box_uint32(x_22);
x_49 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_49, 0, x_48);
lean::cnstr_set(x_49, 1, x_46);
lean::cnstr_set(x_49, 2, x_47);
x_50 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_50, 0, x_49);
lean::cnstr_set(x_50, 1, x_4);
return x_50;
}
}
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__9___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
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
obj* l_lean_parser_monad__parsec_error___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__9(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__9___rarg), 8, 0);
return x_2;
}
}
obj* l_lean_parser_parsec__t_lookahead___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__10(uint32 x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_11; obj* x_12; obj* x_14; 
lean::inc(x_3);
lean::inc(x_2);
lean::inc(x_1);
x_11 = l_lean_parser_monad__parsec_ch___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__7(x_0, x_1, x_2, x_3, x_4);
x_12 = lean::cnstr_get(x_11, 0);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_11, 1);
lean::inc(x_14);
lean::dec(x_11);
if (lean::obj_tag(x_12) == 0)
{
obj* x_17; obj* x_19; obj* x_21; uint32 x_22; obj* x_26; obj* x_27; obj* x_29; 
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
lean::inc(x_17);
lean::inc(x_2);
lean::inc(x_1);
x_26 = l_lean_parser_monad__parsec_ch___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__7(x_22, x_1, x_2, x_17, x_14);
x_27 = lean::cnstr_get(x_26, 0);
lean::inc(x_27);
x_29 = lean::cnstr_get(x_26, 1);
lean::inc(x_29);
lean::dec(x_26);
if (lean::obj_tag(x_27) == 0)
{
obj* x_36; 
lean::dec(x_17);
lean::dec(x_21);
lean::dec(x_1);
lean::dec(x_2);
x_36 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_19, x_27);
x_5 = x_36;
x_6 = x_29;
goto lbl_7;
}
else
{
obj* x_37; uint8 x_39; 
x_37 = lean::cnstr_get(x_27, 0);
lean::inc(x_37);
x_39 = lean::cnstr_get_scalar<uint8>(x_27, sizeof(void*)*1);
if (x_39 == 0)
{
uint8 x_41; 
lean::dec(x_27);
x_41 = lean::string_iterator_has_next(x_17);
if (x_41 == 0)
{
obj* x_43; obj* x_44; obj* x_45; obj* x_49; obj* x_50; obj* x_52; obj* x_55; obj* x_57; obj* x_58; obj* x_59; 
lean::dec(x_21);
x_43 = lean::box(0);
x_44 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_45 = l_mjoin___rarg___closed__1;
lean::inc(x_43);
lean::inc(x_45);
lean::inc(x_44);
x_49 = l_lean_parser_monad__parsec_error___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__9___rarg(x_44, x_45, x_43, x_43, x_1, x_2, x_17, x_29);
x_50 = lean::cnstr_get(x_49, 0);
lean::inc(x_50);
x_52 = lean::cnstr_get(x_49, 1);
lean::inc(x_52);
lean::dec(x_49);
x_55 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_55);
x_57 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_55, x_50);
x_58 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_37, x_57);
x_59 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_19, x_58);
x_5 = x_59;
x_6 = x_52;
goto lbl_7;
}
else
{
uint32 x_60; uint8 x_61; 
x_60 = lean::string_iterator_curr(x_17);
x_61 = l_lean_is__id__first(x_60);
if (x_61 == 0)
{
obj* x_63; obj* x_64; obj* x_66; obj* x_68; obj* x_69; obj* x_70; obj* x_73; obj* x_74; obj* x_76; obj* x_79; obj* x_81; obj* x_82; obj* x_83; 
lean::dec(x_21);
x_63 = l_char_quote__core(x_60);
x_64 = l_char_has__repr___closed__1;
lean::inc(x_64);
x_66 = lean::string_append(x_64, x_63);
lean::dec(x_63);
x_68 = lean::string_append(x_66, x_64);
x_69 = lean::box(0);
x_70 = l_mjoin___rarg___closed__1;
lean::inc(x_69);
lean::inc(x_70);
x_73 = l_lean_parser_monad__parsec_error___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__9___rarg(x_68, x_70, x_69, x_69, x_1, x_2, x_17, x_29);
x_74 = lean::cnstr_get(x_73, 0);
lean::inc(x_74);
x_76 = lean::cnstr_get(x_73, 1);
lean::inc(x_76);
lean::dec(x_73);
x_79 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_79);
x_81 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_79, x_74);
x_82 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_37, x_81);
x_83 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_19, x_82);
x_5 = x_83;
x_6 = x_76;
goto lbl_7;
}
else
{
obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; 
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_37);
x_87 = lean::string_iterator_next(x_17);
x_88 = lean::box(0);
x_89 = lean::box_uint32(x_60);
if (lean::is_scalar(x_21)) {
 x_90 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_90 = x_21;
}
lean::cnstr_set(x_90, 0, x_89);
lean::cnstr_set(x_90, 1, x_87);
lean::cnstr_set(x_90, 2, x_88);
x_91 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_19, x_90);
x_5 = x_91;
x_6 = x_29;
goto lbl_7;
}
}
}
else
{
obj* x_97; 
lean::dec(x_17);
lean::dec(x_21);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_37);
x_97 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_19, x_27);
x_5 = x_97;
x_6 = x_29;
goto lbl_7;
}
}
}
else
{
obj* x_100; uint8 x_102; obj* x_103; obj* x_104; obj* x_105; 
lean::dec(x_1);
lean::dec(x_2);
x_100 = lean::cnstr_get(x_12, 0);
lean::inc(x_100);
x_102 = lean::cnstr_get_scalar<uint8>(x_12, sizeof(void*)*1);
if (lean::is_shared(x_12)) {
 lean::dec(x_12);
 x_103 = lean::box(0);
} else {
 lean::cnstr_release(x_12, 0);
 x_103 = x_12;
}
if (lean::is_scalar(x_103)) {
 x_104 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_104 = x_103;
}
lean::cnstr_set(x_104, 0, x_100);
lean::cnstr_set_scalar(x_104, sizeof(void*)*1, x_102);
x_105 = x_104;
x_5 = x_105;
x_6 = x_14;
goto lbl_7;
}
lbl_7:
{
if (lean::obj_tag(x_5) == 0)
{
obj* x_106; obj* x_108; obj* x_109; obj* x_111; obj* x_112; 
x_106 = lean::cnstr_get(x_5, 0);
lean::inc(x_106);
if (lean::is_shared(x_5)) {
 lean::dec(x_5);
 x_108 = lean::box(0);
} else {
 lean::cnstr_release(x_5, 0);
 lean::cnstr_release(x_5, 1);
 lean::cnstr_release(x_5, 2);
 x_108 = x_5;
}
x_109 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_109);
if (lean::is_scalar(x_108)) {
 x_111 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_111 = x_108;
}
lean::cnstr_set(x_111, 0, x_106);
lean::cnstr_set(x_111, 1, x_3);
lean::cnstr_set(x_111, 2, x_109);
x_112 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_112, 0, x_111);
lean::cnstr_set(x_112, 1, x_6);
return x_112;
}
else
{
obj* x_114; 
lean::dec(x_3);
x_114 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_114, 0, x_5);
lean::cnstr_set(x_114, 1, x_6);
return x_114;
}
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
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__7___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint32 x_5; obj* x_6; 
x_5 = lean::unbox_uint32(x_0);
x_6 = l_lean_parser_monad__parsec_ch___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__7(x_5, x_1, x_2, x_3, x_4);
return x_6;
}
}
obj* l_lean_parser_parsec__t_lookahead___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__10___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint32 x_5; obj* x_6; 
x_5 = lean::unbox_uint32(x_0);
x_6 = l_lean_parser_parsec__t_lookahead___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__10(x_5, x_1, x_2, x_3, x_4);
return x_6;
}
}
obj* l_lean_parser_parsec__t_lookahead___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__view___spec__1(uint32 x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_11; obj* x_12; obj* x_14; 
lean::inc(x_3);
lean::inc(x_2);
lean::inc(x_1);
x_11 = l_lean_parser_monad__parsec_ch___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__7(x_0, x_1, x_2, x_3, x_4);
x_12 = lean::cnstr_get(x_11, 0);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_11, 1);
lean::inc(x_14);
lean::dec(x_11);
if (lean::obj_tag(x_12) == 0)
{
obj* x_17; obj* x_19; obj* x_21; uint32 x_22; obj* x_26; obj* x_27; obj* x_29; 
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
lean::inc(x_17);
lean::inc(x_2);
lean::inc(x_1);
x_26 = l_lean_parser_monad__parsec_ch___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__7(x_22, x_1, x_2, x_17, x_14);
x_27 = lean::cnstr_get(x_26, 0);
lean::inc(x_27);
x_29 = lean::cnstr_get(x_26, 1);
lean::inc(x_29);
lean::dec(x_26);
if (lean::obj_tag(x_27) == 0)
{
obj* x_36; 
lean::dec(x_17);
lean::dec(x_21);
lean::dec(x_1);
lean::dec(x_2);
x_36 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_19, x_27);
x_5 = x_36;
x_6 = x_29;
goto lbl_7;
}
else
{
obj* x_37; uint8 x_39; 
x_37 = lean::cnstr_get(x_27, 0);
lean::inc(x_37);
x_39 = lean::cnstr_get_scalar<uint8>(x_27, sizeof(void*)*1);
if (x_39 == 0)
{
uint8 x_41; 
lean::dec(x_27);
x_41 = lean::string_iterator_has_next(x_17);
if (x_41 == 0)
{
obj* x_43; obj* x_44; obj* x_45; obj* x_49; obj* x_50; obj* x_52; obj* x_55; obj* x_57; obj* x_58; obj* x_59; 
lean::dec(x_21);
x_43 = lean::box(0);
x_44 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_45 = l_mjoin___rarg___closed__1;
lean::inc(x_43);
lean::inc(x_45);
lean::inc(x_44);
x_49 = l_lean_parser_monad__parsec_error___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__9___rarg(x_44, x_45, x_43, x_43, x_1, x_2, x_17, x_29);
x_50 = lean::cnstr_get(x_49, 0);
lean::inc(x_50);
x_52 = lean::cnstr_get(x_49, 1);
lean::inc(x_52);
lean::dec(x_49);
x_55 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_55);
x_57 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_55, x_50);
x_58 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_37, x_57);
x_59 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_19, x_58);
x_5 = x_59;
x_6 = x_52;
goto lbl_7;
}
else
{
uint32 x_60; uint8 x_61; 
x_60 = lean::string_iterator_curr(x_17);
x_61 = l_lean_is__id__first(x_60);
if (x_61 == 0)
{
obj* x_63; obj* x_64; obj* x_66; obj* x_68; obj* x_69; obj* x_70; obj* x_73; obj* x_74; obj* x_76; obj* x_79; obj* x_81; obj* x_82; obj* x_83; 
lean::dec(x_21);
x_63 = l_char_quote__core(x_60);
x_64 = l_char_has__repr___closed__1;
lean::inc(x_64);
x_66 = lean::string_append(x_64, x_63);
lean::dec(x_63);
x_68 = lean::string_append(x_66, x_64);
x_69 = lean::box(0);
x_70 = l_mjoin___rarg___closed__1;
lean::inc(x_69);
lean::inc(x_70);
x_73 = l_lean_parser_monad__parsec_error___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__9___rarg(x_68, x_70, x_69, x_69, x_1, x_2, x_17, x_29);
x_74 = lean::cnstr_get(x_73, 0);
lean::inc(x_74);
x_76 = lean::cnstr_get(x_73, 1);
lean::inc(x_76);
lean::dec(x_73);
x_79 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_79);
x_81 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_79, x_74);
x_82 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_37, x_81);
x_83 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_19, x_82);
x_5 = x_83;
x_6 = x_76;
goto lbl_7;
}
else
{
obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; 
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_37);
x_87 = lean::string_iterator_next(x_17);
x_88 = lean::box(0);
x_89 = lean::box_uint32(x_60);
if (lean::is_scalar(x_21)) {
 x_90 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_90 = x_21;
}
lean::cnstr_set(x_90, 0, x_89);
lean::cnstr_set(x_90, 1, x_87);
lean::cnstr_set(x_90, 2, x_88);
x_91 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_19, x_90);
x_5 = x_91;
x_6 = x_29;
goto lbl_7;
}
}
}
else
{
obj* x_97; 
lean::dec(x_17);
lean::dec(x_21);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_37);
x_97 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_19, x_27);
x_5 = x_97;
x_6 = x_29;
goto lbl_7;
}
}
}
else
{
obj* x_100; uint8 x_102; obj* x_103; obj* x_104; obj* x_105; 
lean::dec(x_1);
lean::dec(x_2);
x_100 = lean::cnstr_get(x_12, 0);
lean::inc(x_100);
x_102 = lean::cnstr_get_scalar<uint8>(x_12, sizeof(void*)*1);
if (lean::is_shared(x_12)) {
 lean::dec(x_12);
 x_103 = lean::box(0);
} else {
 lean::cnstr_release(x_12, 0);
 x_103 = x_12;
}
if (lean::is_scalar(x_103)) {
 x_104 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_104 = x_103;
}
lean::cnstr_set(x_104, 0, x_100);
lean::cnstr_set_scalar(x_104, sizeof(void*)*1, x_102);
x_105 = x_104;
x_5 = x_105;
x_6 = x_14;
goto lbl_7;
}
lbl_7:
{
if (lean::obj_tag(x_5) == 0)
{
obj* x_106; obj* x_108; obj* x_109; obj* x_111; obj* x_112; 
x_106 = lean::cnstr_get(x_5, 0);
lean::inc(x_106);
if (lean::is_shared(x_5)) {
 lean::dec(x_5);
 x_108 = lean::box(0);
} else {
 lean::cnstr_release(x_5, 0);
 lean::cnstr_release(x_5, 1);
 lean::cnstr_release(x_5, 2);
 x_108 = x_5;
}
x_109 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_109);
if (lean::is_scalar(x_108)) {
 x_111 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_111 = x_108;
}
lean::cnstr_set(x_111, 0, x_106);
lean::cnstr_set(x_111, 1, x_3);
lean::cnstr_set(x_111, 2, x_109);
x_112 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_112, 0, x_111);
lean::cnstr_set(x_112, 1, x_6);
return x_112;
}
else
{
obj* x_114; 
lean::dec(x_3);
x_114 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_114, 0, x_5);
lean::cnstr_set(x_114, 1, x_6);
return x_114;
}
}
}
}
obj* l_lean_parser_detail__ident__suffix_parser_lean_parser_has__view___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_8; obj* x_9; obj* x_11; obj* x_13; 
x_6 = l_lean_name_to__string___closed__1;
lean::inc(x_6);
x_8 = l_lean_parser_monad__parsec_str__core___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__2(x_6, x_0, x_2, x_3, x_4, x_5);
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
obj* l_lean_parser_detail__ident__suffix_parser_lean_parser_has__view___lambda__2(uint32 x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_8; obj* x_10; obj* x_11; obj* x_12; 
x_5 = l_lean_parser_parsec__t_lookahead___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__view___spec__1(x_0, x_1, x_2, x_3, x_4);
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
x_11 = l_lean_parser_parsec__t_try__mk__res___rarg(x_6);
if (lean::is_scalar(x_10)) {
 x_12 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_12 = x_10;
}
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_8);
return x_12;
}
}
obj* _init_l_lean_parser_detail__ident__suffix_parser_lean_parser_has__view() {
_start:
{
obj* x_0; obj* x_2; obj* x_3; obj* x_5; obj* x_6; obj* x_9; obj* x_10; obj* x_13; uint32 x_14; uint32 x_15; uint8 x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_33; obj* x_34; obj* x_38; 
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
x_14 = 46;
x_15 = 55296;
x_16 = x_14 < x_15;
x_17 = lean::mk_string(".");
x_18 = l_string_quote(x_17);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_19, 0, x_18);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_with__trailing___rarg___lambda__1), 2, 0);
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_lift___at_lean_parser_with__trailing___spec__1___rarg), 4, 1);
lean::closure_set(x_21, 0, x_20);
x_22 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_lift___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__1___rarg), 5, 1);
lean::closure_set(x_22, 0, x_21);
x_23 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_detail__ident__suffix_parser_lean_parser_has__view___lambda__1), 6, 1);
lean::closure_set(x_23, 0, x_19);
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_bind___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__3___rarg), 6, 2);
lean::closure_set(x_24, 0, x_22);
lean::closure_set(x_24, 1, x_23);
x_25 = lean::box(0);
lean::inc(x_25);
x_27 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_rec__t_recurse___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__4), 5, 1);
lean::closure_set(x_27, 0, x_25);
x_28 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_25);
x_29 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_29, 0, x_24);
lean::cnstr_set(x_29, 1, x_28);
x_30 = l_lean_parser_detail__ident__suffix;
lean::inc(x_29);
lean::inc(x_30);
x_33 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__5), 6, 2);
lean::closure_set(x_33, 0, x_30);
lean::closure_set(x_33, 1, x_29);
x_34 = l_lean_parser_detail__ident__suffix_has__view;
lean::inc(x_34);
lean::inc(x_30);
lean::inc(x_13);
x_38 = l_lean_parser_combinators_node_view___rarg(x_2, x_5, x_9, x_13, x_30, x_29, x_34);
if (x_16 == 0)
{
uint32 x_39; uint8 x_40; 
x_39 = 57343;
x_40 = x_39 < x_14;
if (x_40 == 0)
{
uint32 x_41; obj* x_42; obj* x_43; obj* x_44; 
x_41 = 0;
x_42 = lean::box_uint32(x_41);
x_43 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_detail__ident__suffix_parser_lean_parser_has__view___lambda__2___boxed), 5, 1);
lean::closure_set(x_43, 0, x_42);
x_44 = l_lean_parser_combinators_seq__right_view___rarg(x_13, lean::box(0), lean::box(0), x_43, x_33, x_38);
return x_44;
}
else
{
uint32 x_45; uint8 x_46; 
x_45 = 1114112;
x_46 = x_14 < x_45;
if (x_46 == 0)
{
uint32 x_47; obj* x_48; obj* x_49; obj* x_50; 
x_47 = 0;
x_48 = lean::box_uint32(x_47);
x_49 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_detail__ident__suffix_parser_lean_parser_has__view___lambda__2___boxed), 5, 1);
lean::closure_set(x_49, 0, x_48);
x_50 = l_lean_parser_combinators_seq__right_view___rarg(x_13, lean::box(0), lean::box(0), x_49, x_33, x_38);
return x_50;
}
else
{
obj* x_51; obj* x_52; obj* x_53; 
x_51 = lean::box_uint32(x_14);
x_52 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_detail__ident__suffix_parser_lean_parser_has__view___lambda__2___boxed), 5, 1);
lean::closure_set(x_52, 0, x_51);
x_53 = l_lean_parser_combinators_seq__right_view___rarg(x_13, lean::box(0), lean::box(0), x_52, x_33, x_38);
return x_53;
}
}
}
else
{
obj* x_54; obj* x_55; obj* x_56; 
x_54 = lean::box_uint32(x_14);
x_55 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_detail__ident__suffix_parser_lean_parser_has__view___lambda__2___boxed), 5, 1);
lean::closure_set(x_55, 0, x_54);
x_56 = l_lean_parser_combinators_seq__right_view___rarg(x_13, lean::box(0), lean::box(0), x_55, x_33, x_38);
return x_56;
}
}
}
obj* l_lean_parser_parsec__t_lookahead___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__view___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint32 x_5; obj* x_6; 
x_5 = lean::unbox_uint32(x_0);
x_6 = l_lean_parser_parsec__t_lookahead___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__view___spec__1(x_5, x_1, x_2, x_3, x_4);
return x_6;
}
}
obj* l_lean_parser_detail__ident__suffix_parser_lean_parser_has__view___lambda__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint32 x_5; obj* x_6; 
x_5 = lean::unbox_uint32(x_0);
x_6 = l_lean_parser_detail__ident__suffix_parser_lean_parser_has__view___lambda__2(x_5, x_1, x_2, x_3, x_4);
return x_6;
}
}
obj* l_lean_parser_parsec__t_lookahead___at_lean_parser_detail__ident__suffix_parser___spec__1(obj* x_0, obj* x_1, obj* x_2, uint32 x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_11; obj* x_12; obj* x_14; 
lean::inc(x_2);
lean::inc(x_1);
lean::inc(x_0);
x_11 = l_lean_parser_monad__parsec_ch___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__7(x_3, x_0, x_1, x_2, x_4);
x_12 = lean::cnstr_get(x_11, 0);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_11, 1);
lean::inc(x_14);
lean::dec(x_11);
if (lean::obj_tag(x_12) == 0)
{
obj* x_17; obj* x_19; obj* x_21; uint32 x_22; obj* x_26; obj* x_27; obj* x_29; 
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
lean::inc(x_17);
lean::inc(x_1);
lean::inc(x_0);
x_26 = l_lean_parser_monad__parsec_ch___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__7(x_22, x_0, x_1, x_17, x_14);
x_27 = lean::cnstr_get(x_26, 0);
lean::inc(x_27);
x_29 = lean::cnstr_get(x_26, 1);
lean::inc(x_29);
lean::dec(x_26);
if (lean::obj_tag(x_27) == 0)
{
obj* x_36; 
lean::dec(x_17);
lean::dec(x_21);
lean::dec(x_1);
lean::dec(x_0);
x_36 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_19, x_27);
x_5 = x_36;
x_6 = x_29;
goto lbl_7;
}
else
{
obj* x_37; uint8 x_39; 
x_37 = lean::cnstr_get(x_27, 0);
lean::inc(x_37);
x_39 = lean::cnstr_get_scalar<uint8>(x_27, sizeof(void*)*1);
if (x_39 == 0)
{
uint8 x_41; 
lean::dec(x_27);
x_41 = lean::string_iterator_has_next(x_17);
if (x_41 == 0)
{
obj* x_43; obj* x_44; obj* x_45; obj* x_49; obj* x_50; obj* x_52; obj* x_55; obj* x_57; obj* x_58; obj* x_59; 
lean::dec(x_21);
x_43 = lean::box(0);
x_44 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_45 = l_mjoin___rarg___closed__1;
lean::inc(x_43);
lean::inc(x_45);
lean::inc(x_44);
x_49 = l_lean_parser_monad__parsec_error___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__9___rarg(x_44, x_45, x_43, x_43, x_0, x_1, x_17, x_29);
x_50 = lean::cnstr_get(x_49, 0);
lean::inc(x_50);
x_52 = lean::cnstr_get(x_49, 1);
lean::inc(x_52);
lean::dec(x_49);
x_55 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_55);
x_57 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_55, x_50);
x_58 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_37, x_57);
x_59 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_19, x_58);
x_5 = x_59;
x_6 = x_52;
goto lbl_7;
}
else
{
uint32 x_60; uint8 x_61; 
x_60 = lean::string_iterator_curr(x_17);
x_61 = l_lean_is__id__first(x_60);
if (x_61 == 0)
{
obj* x_63; obj* x_64; obj* x_66; obj* x_68; obj* x_69; obj* x_70; obj* x_73; obj* x_74; obj* x_76; obj* x_79; obj* x_81; obj* x_82; obj* x_83; 
lean::dec(x_21);
x_63 = l_char_quote__core(x_60);
x_64 = l_char_has__repr___closed__1;
lean::inc(x_64);
x_66 = lean::string_append(x_64, x_63);
lean::dec(x_63);
x_68 = lean::string_append(x_66, x_64);
x_69 = lean::box(0);
x_70 = l_mjoin___rarg___closed__1;
lean::inc(x_69);
lean::inc(x_70);
x_73 = l_lean_parser_monad__parsec_error___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__9___rarg(x_68, x_70, x_69, x_69, x_0, x_1, x_17, x_29);
x_74 = lean::cnstr_get(x_73, 0);
lean::inc(x_74);
x_76 = lean::cnstr_get(x_73, 1);
lean::inc(x_76);
lean::dec(x_73);
x_79 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_79);
x_81 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_79, x_74);
x_82 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_37, x_81);
x_83 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_19, x_82);
x_5 = x_83;
x_6 = x_76;
goto lbl_7;
}
else
{
obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_37);
x_87 = lean::string_iterator_next(x_17);
x_88 = lean::box(0);
x_89 = lean::box_uint32(x_60);
if (lean::is_scalar(x_21)) {
 x_90 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_90 = x_21;
}
lean::cnstr_set(x_90, 0, x_89);
lean::cnstr_set(x_90, 1, x_87);
lean::cnstr_set(x_90, 2, x_88);
x_91 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_19, x_90);
x_5 = x_91;
x_6 = x_29;
goto lbl_7;
}
}
}
else
{
obj* x_97; 
lean::dec(x_17);
lean::dec(x_21);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_37);
x_97 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_19, x_27);
x_5 = x_97;
x_6 = x_29;
goto lbl_7;
}
}
}
else
{
obj* x_100; uint8 x_102; obj* x_103; obj* x_104; obj* x_105; 
lean::dec(x_1);
lean::dec(x_0);
x_100 = lean::cnstr_get(x_12, 0);
lean::inc(x_100);
x_102 = lean::cnstr_get_scalar<uint8>(x_12, sizeof(void*)*1);
if (lean::is_shared(x_12)) {
 lean::dec(x_12);
 x_103 = lean::box(0);
} else {
 lean::cnstr_release(x_12, 0);
 x_103 = x_12;
}
if (lean::is_scalar(x_103)) {
 x_104 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_104 = x_103;
}
lean::cnstr_set(x_104, 0, x_100);
lean::cnstr_set_scalar(x_104, sizeof(void*)*1, x_102);
x_105 = x_104;
x_5 = x_105;
x_6 = x_14;
goto lbl_7;
}
lbl_7:
{
if (lean::obj_tag(x_5) == 0)
{
obj* x_106; obj* x_108; obj* x_109; obj* x_111; obj* x_112; 
x_106 = lean::cnstr_get(x_5, 0);
lean::inc(x_106);
if (lean::is_shared(x_5)) {
 lean::dec(x_5);
 x_108 = lean::box(0);
} else {
 lean::cnstr_release(x_5, 0);
 lean::cnstr_release(x_5, 1);
 lean::cnstr_release(x_5, 2);
 x_108 = x_5;
}
x_109 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_109);
if (lean::is_scalar(x_108)) {
 x_111 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_111 = x_108;
}
lean::cnstr_set(x_111, 0, x_106);
lean::cnstr_set(x_111, 1, x_2);
lean::cnstr_set(x_111, 2, x_109);
x_112 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_112, 0, x_111);
lean::cnstr_set(x_112, 1, x_6);
return x_112;
}
else
{
obj* x_114; 
lean::dec(x_2);
x_114 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_114, 0, x_5);
lean::cnstr_set(x_114, 1, x_6);
return x_114;
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
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_lift___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__1___rarg), 5, 1);
lean::closure_set(x_5, 0, x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_detail__ident__suffix_parser_lean_parser_has__view___lambda__1), 6, 1);
lean::closure_set(x_6, 0, x_2);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_bind___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__3___rarg), 6, 2);
lean::closure_set(x_7, 0, x_5);
lean::closure_set(x_7, 1, x_6);
x_8 = lean::box(0);
lean::inc(x_8);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_rec__t_recurse___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__4), 5, 1);
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
uint32 x_4; uint32 x_5; uint8 x_6; uint32 x_7; 
x_4 = 46;
x_5 = 55296;
x_6 = x_4 < x_5;
if (x_6 == 0)
{
uint32 x_9; uint8 x_10; 
x_9 = 57343;
x_10 = x_9 < x_4;
if (x_10 == 0)
{
uint32 x_11; 
x_11 = 0;
x_7 = x_11;
goto lbl_8;
}
else
{
uint32 x_12; uint8 x_13; 
x_12 = 1114112;
x_13 = x_4 < x_12;
if (x_13 == 0)
{
uint32 x_14; 
x_14 = 0;
x_7 = x_14;
goto lbl_8;
}
else
{
x_7 = x_4;
goto lbl_8;
}
}
}
else
{
x_7 = x_4;
goto lbl_8;
}
lbl_8:
{
obj* x_17; obj* x_18; obj* x_20; obj* x_22; obj* x_23; 
lean::inc(x_1);
lean::inc(x_0);
x_17 = l_lean_parser_parsec__t_lookahead___at_lean_parser_detail__ident__suffix_parser___spec__1(x_0, x_1, x_2, x_7, x_3);
x_18 = lean::cnstr_get(x_17, 0);
lean::inc(x_18);
x_20 = lean::cnstr_get(x_17, 1);
lean::inc(x_20);
if (lean::is_shared(x_17)) {
 lean::dec(x_17);
 x_22 = lean::box(0);
} else {
 lean::cnstr_release(x_17, 0);
 lean::cnstr_release(x_17, 1);
 x_22 = x_17;
}
x_23 = l_lean_parser_parsec__t_try__mk__res___rarg(x_18);
if (lean::obj_tag(x_23) == 0)
{
obj* x_24; obj* x_26; obj* x_29; obj* x_30; obj* x_33; obj* x_34; obj* x_36; obj* x_39; obj* x_40; 
x_24 = lean::cnstr_get(x_23, 1);
lean::inc(x_24);
x_26 = lean::cnstr_get(x_23, 2);
lean::inc(x_26);
lean::dec(x_23);
x_29 = l_lean_parser_detail__ident__suffix;
x_30 = l_lean_parser_detail__ident__suffix_parser___closed__1;
lean::inc(x_30);
lean::inc(x_29);
x_33 = l_lean_parser_combinators_node___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__5(x_29, x_30, x_0, x_1, x_24, x_20);
x_34 = lean::cnstr_get(x_33, 0);
lean::inc(x_34);
x_36 = lean::cnstr_get(x_33, 1);
lean::inc(x_36);
lean::dec(x_33);
x_39 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_26, x_34);
if (lean::is_scalar(x_22)) {
 x_40 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_40 = x_22;
}
lean::cnstr_set(x_40, 0, x_39);
lean::cnstr_set(x_40, 1, x_36);
return x_40;
}
else
{
obj* x_43; uint8 x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; 
lean::dec(x_1);
lean::dec(x_0);
x_43 = lean::cnstr_get(x_23, 0);
lean::inc(x_43);
x_45 = lean::cnstr_get_scalar<uint8>(x_23, sizeof(void*)*1);
if (lean::is_shared(x_23)) {
 lean::dec(x_23);
 x_46 = lean::box(0);
} else {
 lean::cnstr_release(x_23, 0);
 x_46 = x_23;
}
if (lean::is_scalar(x_46)) {
 x_47 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_47 = x_46;
}
lean::cnstr_set(x_47, 0, x_43);
lean::cnstr_set_scalar(x_47, sizeof(void*)*1, x_45);
x_48 = x_47;
if (lean::is_scalar(x_22)) {
 x_49 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_49 = x_22;
}
lean::cnstr_set(x_49, 0, x_48);
lean::cnstr_set(x_49, 1, x_20);
return x_49;
}
}
}
}
obj* l_lean_parser_parsec__t_lookahead___at_lean_parser_detail__ident__suffix_parser___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint32 x_5; obj* x_6; 
x_5 = lean::unbox_uint32(x_3);
x_6 = l_lean_parser_parsec__t_lookahead___at_lean_parser_detail__ident__suffix_parser___spec__1(x_0, x_1, x_2, x_5, x_4);
return x_6;
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
x_0 = l_lean_parser_detail__ident__suffix_parser_lean_parser_has__view;
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
x_32 = l_lean_parser_detail__ident__suffix_parser_lean_parser_has__view;
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
x_68 = l_lean_parser_detail__ident__suffix_parser_lean_parser_has__view;
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
x_47 = l_lean_parser_detail__ident__suffix_parser_lean_parser_has__view;
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
x_83 = l_lean_parser_detail__ident__suffix_parser_lean_parser_has__view;
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
x_21 = l_lean_parser_detail__ident__suffix_parser_lean_parser_has__view;
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
x_8 = l_lean_parser_combinators_node___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__5(x_4, x_5, x_0, x_1, x_2, x_3);
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
x_10 = l_lean_parser_combinators_node___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__5(x_6, x_7, x_1, x_2, x_3, x_4);
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
uint32 x_21; uint8 x_22; 
x_21 = lean::string_iterator_curr(x_2);
x_22 = x_21 == x_0;
if (x_22 == 0)
{
obj* x_23; obj* x_24; obj* x_26; obj* x_28; obj* x_29; obj* x_30; obj* x_33; obj* x_34; obj* x_36; obj* x_38; obj* x_39; obj* x_41; obj* x_42; 
x_23 = l_char_quote__core(x_21);
x_24 = l_char_has__repr___closed__1;
lean::inc(x_24);
x_26 = lean::string_append(x_24, x_23);
lean::dec(x_23);
x_28 = lean::string_append(x_26, x_24);
x_29 = lean::box(0);
x_30 = l_mjoin___rarg___closed__1;
lean::inc(x_29);
lean::inc(x_30);
x_33 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_28, x_30, x_29, x_29, x_1, x_2, x_3);
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
x_39 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_39);
x_41 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_39, x_34);
if (lean::is_scalar(x_38)) {
 x_42 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_42 = x_38;
}
lean::cnstr_set(x_42, 0, x_41);
lean::cnstr_set(x_42, 1, x_36);
return x_42;
}
else
{
obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; 
lean::dec(x_1);
x_44 = lean::string_iterator_next(x_2);
x_45 = lean::box(0);
x_46 = lean::box_uint32(x_21);
x_47 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_47, 0, x_46);
lean::cnstr_set(x_47, 1, x_44);
lean::cnstr_set(x_47, 2, x_45);
x_48 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_48, 0, x_47);
lean::cnstr_set(x_48, 1, x_3);
return x_48;
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
uint32 x_3; obj* x_5; obj* x_6; obj* x_8; obj* x_10; 
x_3 = l_lean_id__begin__escape;
lean::inc(x_0);
x_5 = l_lean_parser_monad__parsec_ch___at___private_init_lean_parser_token_4__ident_x_27___spec__11(x_3, x_0, x_1, x_2);
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
obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_18; obj* x_20; obj* x_23; 
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
lean::inc(x_0);
x_17 = l_lean_parser_monad__parsec_take__while1___at___private_init_lean_parser_token_4__ident_x_27___spec__12(x_0, x_11, x_8);
x_18 = lean::cnstr_get(x_17, 0);
lean::inc(x_18);
x_20 = lean::cnstr_get(x_17, 1);
lean::inc(x_20);
lean::dec(x_17);
x_23 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_13, x_18);
if (lean::obj_tag(x_23) == 0)
{
obj* x_24; obj* x_26; obj* x_28; uint32 x_31; obj* x_32; obj* x_33; obj* x_35; 
x_24 = lean::cnstr_get(x_23, 0);
lean::inc(x_24);
x_26 = lean::cnstr_get(x_23, 1);
lean::inc(x_26);
x_28 = lean::cnstr_get(x_23, 2);
lean::inc(x_28);
lean::dec(x_23);
x_31 = l_lean_id__end__escape;
x_32 = l_lean_parser_monad__parsec_ch___at___private_init_lean_parser_token_4__ident_x_27___spec__11(x_31, x_0, x_26, x_20);
x_33 = lean::cnstr_get(x_32, 0);
lean::inc(x_33);
x_35 = lean::cnstr_get(x_32, 1);
lean::inc(x_35);
lean::dec(x_32);
if (lean::obj_tag(x_33) == 0)
{
obj* x_38; obj* x_40; obj* x_43; obj* x_45; obj* x_46; obj* x_47; obj* x_48; 
x_38 = lean::cnstr_get(x_33, 1);
lean::inc(x_38);
x_40 = lean::cnstr_get(x_33, 2);
lean::inc(x_40);
lean::dec(x_33);
x_43 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_43);
if (lean::is_scalar(x_15)) {
 x_45 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_45 = x_15;
}
lean::cnstr_set(x_45, 0, x_24);
lean::cnstr_set(x_45, 1, x_38);
lean::cnstr_set(x_45, 2, x_43);
x_46 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_40, x_45);
x_47 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_28, x_46);
if (lean::is_scalar(x_10)) {
 x_48 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_48 = x_10;
}
lean::cnstr_set(x_48, 0, x_47);
lean::cnstr_set(x_48, 1, x_35);
return x_48;
}
else
{
obj* x_51; uint8 x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; 
lean::dec(x_24);
lean::dec(x_15);
x_51 = lean::cnstr_get(x_33, 0);
lean::inc(x_51);
x_53 = lean::cnstr_get_scalar<uint8>(x_33, sizeof(void*)*1);
if (lean::is_shared(x_33)) {
 lean::dec(x_33);
 x_54 = lean::box(0);
} else {
 lean::cnstr_release(x_33, 0);
 x_54 = x_33;
}
if (lean::is_scalar(x_54)) {
 x_55 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_55 = x_54;
}
lean::cnstr_set(x_55, 0, x_51);
lean::cnstr_set_scalar(x_55, sizeof(void*)*1, x_53);
x_56 = x_55;
x_57 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_28, x_56);
if (lean::is_scalar(x_10)) {
 x_58 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_58 = x_10;
}
lean::cnstr_set(x_58, 0, x_57);
lean::cnstr_set(x_58, 1, x_35);
return x_58;
}
}
else
{
obj* x_61; uint8 x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; 
lean::dec(x_15);
lean::dec(x_0);
x_61 = lean::cnstr_get(x_23, 0);
lean::inc(x_61);
x_63 = lean::cnstr_get_scalar<uint8>(x_23, sizeof(void*)*1);
if (lean::is_shared(x_23)) {
 lean::dec(x_23);
 x_64 = lean::box(0);
} else {
 lean::cnstr_release(x_23, 0);
 x_64 = x_23;
}
if (lean::is_scalar(x_64)) {
 x_65 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_65 = x_64;
}
lean::cnstr_set(x_65, 0, x_61);
lean::cnstr_set_scalar(x_65, sizeof(void*)*1, x_63);
x_66 = x_65;
if (lean::is_scalar(x_10)) {
 x_67 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_67 = x_10;
}
lean::cnstr_set(x_67, 0, x_66);
lean::cnstr_set(x_67, 1, x_20);
return x_67;
}
}
else
{
obj* x_69; uint8 x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; 
lean::dec(x_0);
x_69 = lean::cnstr_get(x_6, 0);
lean::inc(x_69);
x_71 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*1);
if (lean::is_shared(x_6)) {
 lean::dec(x_6);
 x_72 = lean::box(0);
} else {
 lean::cnstr_release(x_6, 0);
 x_72 = x_6;
}
if (lean::is_scalar(x_72)) {
 x_73 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_73 = x_72;
}
lean::cnstr_set(x_73, 0, x_69);
lean::cnstr_set_scalar(x_73, sizeof(void*)*1, x_71);
x_74 = x_73;
if (lean::is_scalar(x_10)) {
 x_75 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_75 = x_10;
}
lean::cnstr_set(x_75, 0, x_74);
lean::cnstr_set(x_75, 1, x_8);
return x_75;
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
obj* l_lean_parser_parsec__t_lookahead___at___private_init_lean_parser_token_4__ident_x_27___spec__19(uint32 x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_9; obj* x_10; obj* x_12; 
lean::inc(x_2);
lean::inc(x_1);
x_9 = l_lean_parser_monad__parsec_ch___at___private_init_lean_parser_token_4__ident_x_27___spec__11(x_0, x_1, x_2, x_3);
x_10 = lean::cnstr_get(x_9, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_9, 1);
lean::inc(x_12);
lean::dec(x_9);
if (lean::obj_tag(x_10) == 0)
{
obj* x_15; obj* x_17; obj* x_19; uint32 x_20; obj* x_23; obj* x_24; obj* x_26; 
x_15 = lean::cnstr_get(x_10, 1);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_10, 2);
lean::inc(x_17);
if (lean::is_shared(x_10)) {
 lean::dec(x_10);
 x_19 = lean::box(0);
} else {
 lean::cnstr_release(x_10, 0);
 lean::cnstr_release(x_10, 1);
 lean::cnstr_release(x_10, 2);
 x_19 = x_10;
}
x_20 = l_lean_id__begin__escape;
lean::inc(x_15);
lean::inc(x_1);
x_23 = l_lean_parser_monad__parsec_ch___at___private_init_lean_parser_token_4__ident_x_27___spec__11(x_20, x_1, x_15, x_12);
x_24 = lean::cnstr_get(x_23, 0);
lean::inc(x_24);
x_26 = lean::cnstr_get(x_23, 1);
lean::inc(x_26);
lean::dec(x_23);
if (lean::obj_tag(x_24) == 0)
{
obj* x_32; 
lean::dec(x_15);
lean::dec(x_19);
lean::dec(x_1);
x_32 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_17, x_24);
x_4 = x_32;
x_5 = x_26;
goto lbl_6;
}
else
{
obj* x_33; uint8 x_35; 
x_33 = lean::cnstr_get(x_24, 0);
lean::inc(x_33);
x_35 = lean::cnstr_get_scalar<uint8>(x_24, sizeof(void*)*1);
if (x_35 == 0)
{
uint8 x_37; 
lean::dec(x_24);
x_37 = lean::string_iterator_has_next(x_15);
if (x_37 == 0)
{
obj* x_39; obj* x_40; obj* x_41; obj* x_45; obj* x_46; obj* x_48; obj* x_51; obj* x_53; obj* x_54; obj* x_55; 
lean::dec(x_19);
x_39 = lean::box(0);
x_40 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_41 = l_mjoin___rarg___closed__1;
lean::inc(x_39);
lean::inc(x_41);
lean::inc(x_40);
x_45 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_40, x_41, x_39, x_39, x_1, x_15, x_26);
x_46 = lean::cnstr_get(x_45, 0);
lean::inc(x_46);
x_48 = lean::cnstr_get(x_45, 1);
lean::inc(x_48);
lean::dec(x_45);
x_51 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_51);
x_53 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_51, x_46);
x_54 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_33, x_53);
x_55 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_17, x_54);
x_4 = x_55;
x_5 = x_48;
goto lbl_6;
}
else
{
uint32 x_56; uint8 x_57; 
x_56 = lean::string_iterator_curr(x_15);
x_57 = l_lean_is__id__first(x_56);
if (x_57 == 0)
{
obj* x_59; obj* x_60; obj* x_62; obj* x_64; obj* x_65; obj* x_66; obj* x_69; obj* x_70; obj* x_72; obj* x_75; obj* x_77; obj* x_78; obj* x_79; 
lean::dec(x_19);
x_59 = l_char_quote__core(x_56);
x_60 = l_char_has__repr___closed__1;
lean::inc(x_60);
x_62 = lean::string_append(x_60, x_59);
lean::dec(x_59);
x_64 = lean::string_append(x_62, x_60);
x_65 = lean::box(0);
x_66 = l_mjoin___rarg___closed__1;
lean::inc(x_65);
lean::inc(x_66);
x_69 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_64, x_66, x_65, x_65, x_1, x_15, x_26);
x_70 = lean::cnstr_get(x_69, 0);
lean::inc(x_70);
x_72 = lean::cnstr_get(x_69, 1);
lean::inc(x_72);
lean::dec(x_69);
x_75 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_75);
x_77 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_75, x_70);
x_78 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_33, x_77);
x_79 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_17, x_78);
x_4 = x_79;
x_5 = x_72;
goto lbl_6;
}
else
{
obj* x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_86; 
lean::dec(x_1);
lean::dec(x_33);
x_82 = lean::string_iterator_next(x_15);
x_83 = lean::box(0);
x_84 = lean::box_uint32(x_56);
if (lean::is_scalar(x_19)) {
 x_85 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_85 = x_19;
}
lean::cnstr_set(x_85, 0, x_84);
lean::cnstr_set(x_85, 1, x_82);
lean::cnstr_set(x_85, 2, x_83);
x_86 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_17, x_85);
x_4 = x_86;
x_5 = x_26;
goto lbl_6;
}
}
}
else
{
obj* x_91; 
lean::dec(x_15);
lean::dec(x_19);
lean::dec(x_1);
lean::dec(x_33);
x_91 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_17, x_24);
x_4 = x_91;
x_5 = x_26;
goto lbl_6;
}
}
}
else
{
obj* x_93; uint8 x_95; obj* x_96; obj* x_97; obj* x_98; 
lean::dec(x_1);
x_93 = lean::cnstr_get(x_10, 0);
lean::inc(x_93);
x_95 = lean::cnstr_get_scalar<uint8>(x_10, sizeof(void*)*1);
if (lean::is_shared(x_10)) {
 lean::dec(x_10);
 x_96 = lean::box(0);
} else {
 lean::cnstr_release(x_10, 0);
 x_96 = x_10;
}
if (lean::is_scalar(x_96)) {
 x_97 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_97 = x_96;
}
lean::cnstr_set(x_97, 0, x_93);
lean::cnstr_set_scalar(x_97, sizeof(void*)*1, x_95);
x_98 = x_97;
x_4 = x_98;
x_5 = x_12;
goto lbl_6;
}
lbl_6:
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_99; obj* x_101; obj* x_102; obj* x_104; obj* x_105; 
x_99 = lean::cnstr_get(x_4, 0);
lean::inc(x_99);
if (lean::is_shared(x_4)) {
 lean::dec(x_4);
 x_101 = lean::box(0);
} else {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_release(x_4, 1);
 lean::cnstr_release(x_4, 2);
 x_101 = x_4;
}
x_102 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_102);
if (lean::is_scalar(x_101)) {
 x_104 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_104 = x_101;
}
lean::cnstr_set(x_104, 0, x_99);
lean::cnstr_set(x_104, 1, x_2);
lean::cnstr_set(x_104, 2, x_102);
x_105 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_105, 0, x_104);
lean::cnstr_set(x_105, 1, x_5);
return x_105;
}
else
{
obj* x_107; 
lean::dec(x_2);
x_107 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_107, 0, x_4);
lean::cnstr_set(x_107, 1, x_5);
return x_107;
}
}
}
}
obj* l_lean_parser_monad__parsec_foldl__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__21___lambda__1(uint32 x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_11; 
x_4 = l_lean_parser_parsec__t_lookahead___at___private_init_lean_parser_token_4__ident_x_27___spec__19(x_0, x_1, x_2, x_3);
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
obj* l_lean_parser_monad__parsec_foldl__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__21___lambda__2(uint32 x_0, uint32 x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_6; obj* x_7; obj* x_9; obj* x_11; 
lean::inc(x_2);
x_6 = l_lean_parser_monad__parsec_ch___at___private_init_lean_parser_token_4__ident_x_27___spec__11(x_0, x_2, x_3, x_4);
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
obj* x_12; obj* x_14; obj* x_17; obj* x_18; obj* x_20; obj* x_23; obj* x_24; 
x_12 = lean::cnstr_get(x_7, 1);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_7, 2);
lean::inc(x_14);
lean::dec(x_7);
x_17 = l_lean_parser_id__part___at___private_init_lean_parser_token_4__ident_x_27___spec__1(x_2, x_12, x_9);
x_18 = lean::cnstr_get(x_17, 0);
lean::inc(x_18);
x_20 = lean::cnstr_get(x_17, 1);
lean::inc(x_20);
lean::dec(x_17);
x_23 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_14, x_18);
if (lean::is_scalar(x_11)) {
 x_24 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_24 = x_11;
}
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_20);
return x_24;
}
else
{
obj* x_26; uint8 x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; 
lean::dec(x_2);
x_26 = lean::cnstr_get(x_7, 0);
lean::inc(x_26);
x_28 = lean::cnstr_get_scalar<uint8>(x_7, sizeof(void*)*1);
if (lean::is_shared(x_7)) {
 lean::dec(x_7);
 x_29 = lean::box(0);
} else {
 lean::cnstr_release(x_7, 0);
 x_29 = x_7;
}
if (lean::is_scalar(x_29)) {
 x_30 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_30 = x_29;
}
lean::cnstr_set(x_30, 0, x_26);
lean::cnstr_set_scalar(x_30, sizeof(void*)*1, x_28);
x_31 = x_30;
if (lean::is_scalar(x_11)) {
 x_32 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_32 = x_11;
}
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_9);
return x_32;
}
}
}
obj* l_lean_parser_monad__parsec_foldl__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__21(uint32 x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_7; 
x_6 = lean::mk_nat_obj(0u);
x_7 = lean::nat_dec_eq(x_2, x_6);
lean::dec(x_6);
if (x_7 == 0)
{
obj* x_9; obj* x_11; obj* x_12; obj* x_15; obj* x_16; obj* x_18; obj* x_20; 
x_9 = lean::box_uint32(x_0);
lean::inc(x_9);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_foldl__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__21___lambda__1___boxed), 4, 1);
lean::closure_set(x_11, 0, x_9);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_foldl__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__21___lambda__2___boxed), 5, 1);
lean::closure_set(x_12, 0, x_9);
lean::inc(x_4);
lean::inc(x_3);
x_15 = l_reader__t_bind___at_lean_parser_with__trailing___spec__2___rarg(x_11, x_12, x_3, x_4, x_5);
x_16 = lean::cnstr_get(x_15, 0);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_15, 1);
lean::inc(x_18);
if (lean::is_shared(x_15)) {
 lean::dec(x_15);
 x_20 = lean::box(0);
} else {
 lean::cnstr_release(x_15, 0);
 lean::cnstr_release(x_15, 1);
 x_20 = x_15;
}
if (lean::obj_tag(x_16) == 0)
{
obj* x_21; obj* x_23; obj* x_25; obj* x_27; obj* x_28; obj* x_29; obj* x_33; obj* x_34; obj* x_35; obj* x_37; obj* x_40; 
x_21 = lean::cnstr_get(x_16, 0);
lean::inc(x_21);
x_23 = lean::cnstr_get(x_16, 1);
lean::inc(x_23);
x_25 = lean::cnstr_get(x_16, 2);
lean::inc(x_25);
if (lean::is_shared(x_16)) {
 lean::dec(x_16);
 x_27 = lean::box(0);
} else {
 lean::cnstr_release(x_16, 0);
 lean::cnstr_release(x_16, 1);
 lean::cnstr_release(x_16, 2);
 x_27 = x_16;
}
x_28 = lean::mk_nat_obj(1u);
x_29 = lean::nat_sub(x_2, x_28);
lean::dec(x_28);
lean::dec(x_2);
lean::inc(x_1);
x_33 = lean_name_mk_string(x_1, x_21);
x_34 = l_lean_parser_monad__parsec_foldl__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__21(x_0, x_33, x_29, x_3, x_23, x_18);
x_35 = lean::cnstr_get(x_34, 0);
lean::inc(x_35);
x_37 = lean::cnstr_get(x_34, 1);
lean::inc(x_37);
lean::dec(x_34);
x_40 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_25, x_35);
if (lean::obj_tag(x_40) == 0)
{
obj* x_44; 
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_27);
if (lean::is_scalar(x_20)) {
 x_44 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_44 = x_20;
}
lean::cnstr_set(x_44, 0, x_40);
lean::cnstr_set(x_44, 1, x_37);
return x_44;
}
else
{
obj* x_45; uint8 x_47; 
x_45 = lean::cnstr_get(x_40, 0);
lean::inc(x_45);
x_47 = lean::cnstr_get_scalar<uint8>(x_40, sizeof(void*)*1);
if (x_47 == 0)
{
obj* x_49; obj* x_52; obj* x_54; obj* x_55; obj* x_56; obj* x_57; 
lean::dec(x_40);
x_49 = lean::cnstr_get(x_45, 2);
lean::inc(x_49);
lean::dec(x_45);
x_52 = l_mjoin___rarg___closed__1;
lean::inc(x_52);
x_54 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_54, 0, x_49);
lean::closure_set(x_54, 1, x_52);
x_55 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_55, 0, x_54);
if (lean::is_scalar(x_27)) {
 x_56 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_56 = x_27;
}
lean::cnstr_set(x_56, 0, x_1);
lean::cnstr_set(x_56, 1, x_4);
lean::cnstr_set(x_56, 2, x_55);
if (lean::is_scalar(x_20)) {
 x_57 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_57 = x_20;
}
lean::cnstr_set(x_57, 0, x_56);
lean::cnstr_set(x_57, 1, x_37);
return x_57;
}
else
{
obj* x_62; 
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_45);
lean::dec(x_27);
if (lean::is_scalar(x_20)) {
 x_62 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_62 = x_20;
}
lean::cnstr_set(x_62, 0, x_40);
lean::cnstr_set(x_62, 1, x_37);
return x_62;
}
}
}
else
{
obj* x_65; uint8 x_67; obj* x_68; 
lean::dec(x_3);
lean::dec(x_2);
x_65 = lean::cnstr_get(x_16, 0);
lean::inc(x_65);
x_67 = lean::cnstr_get_scalar<uint8>(x_16, sizeof(void*)*1);
if (lean::is_shared(x_16)) {
 lean::dec(x_16);
 x_68 = lean::box(0);
} else {
 lean::cnstr_release(x_16, 0);
 x_68 = x_16;
}
if (x_67 == 0)
{
obj* x_70; obj* x_73; obj* x_75; obj* x_76; obj* x_77; obj* x_78; 
lean::dec(x_68);
x_70 = lean::cnstr_get(x_65, 2);
lean::inc(x_70);
lean::dec(x_65);
x_73 = l_mjoin___rarg___closed__1;
lean::inc(x_73);
x_75 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_75, 0, x_70);
lean::closure_set(x_75, 1, x_73);
x_76 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_76, 0, x_75);
x_77 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_77, 0, x_1);
lean::cnstr_set(x_77, 1, x_4);
lean::cnstr_set(x_77, 2, x_76);
if (lean::is_scalar(x_20)) {
 x_78 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_78 = x_20;
}
lean::cnstr_set(x_78, 0, x_77);
lean::cnstr_set(x_78, 1, x_18);
return x_78;
}
else
{
obj* x_81; obj* x_82; obj* x_83; 
lean::dec(x_4);
lean::dec(x_1);
if (lean::is_scalar(x_68)) {
 x_81 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_81 = x_68;
}
lean::cnstr_set(x_81, 0, x_65);
lean::cnstr_set_scalar(x_81, sizeof(void*)*1, x_67);
x_82 = x_81;
if (lean::is_scalar(x_20)) {
 x_83 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_83 = x_20;
}
lean::cnstr_set(x_83, 0, x_82);
lean::cnstr_set(x_83, 1, x_18);
return x_83;
}
}
}
else
{
obj* x_86; obj* x_88; obj* x_89; 
lean::dec(x_3);
lean::dec(x_2);
x_86 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_86);
x_88 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_88, 0, x_1);
lean::cnstr_set(x_88, 1, x_4);
lean::cnstr_set(x_88, 2, x_86);
x_89 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_89, 0, x_88);
lean::cnstr_set(x_89, 1, x_5);
return x_89;
}
}
}
obj* l_lean_parser_monad__parsec_foldl___at___private_init_lean_parser_token_4__ident_x_27___spec__20(obj* x_0, uint32 x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_11; obj* x_13; obj* x_14; obj* x_16; obj* x_17; 
x_5 = lean::box(0);
x_6 = lean_name_mk_string(x_5, x_0);
x_7 = lean::string_iterator_remaining(x_3);
x_8 = l_lean_parser_monad__parsec_foldl__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__21(x_1, x_6, x_7, x_2, x_3, x_4);
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
if (lean::is_scalar(x_13)) {
 x_17 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_17 = x_13;
}
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_11);
return x_17;
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
obj* x_11; obj* x_13; obj* x_15; obj* x_17; uint32 x_18; uint32 x_19; uint8 x_20; uint32 x_21; 
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
x_18 = 46;
x_19 = 55296;
x_20 = x_18 < x_19;
if (x_20 == 0)
{
uint32 x_23; uint8 x_24; 
x_23 = 57343;
x_24 = x_23 < x_18;
if (x_24 == 0)
{
uint32 x_25; 
x_25 = 0;
x_21 = x_25;
goto lbl_22;
}
else
{
uint32 x_26; uint8 x_27; 
x_26 = 1114112;
x_27 = x_18 < x_26;
if (x_27 == 0)
{
uint32 x_28; 
x_28 = 0;
x_21 = x_28;
goto lbl_22;
}
else
{
x_21 = x_18;
goto lbl_22;
}
}
}
else
{
x_21 = x_18;
goto lbl_22;
}
lbl_22:
{
obj* x_29; obj* x_30; obj* x_32; 
x_29 = l_lean_parser_monad__parsec_foldl___at___private_init_lean_parser_token_4__ident_x_27___spec__20(x_11, x_21, x_0, x_13, x_8);
x_30 = lean::cnstr_get(x_29, 0);
lean::inc(x_30);
x_32 = lean::cnstr_get(x_29, 1);
lean::inc(x_32);
lean::dec(x_29);
if (lean::obj_tag(x_30) == 0)
{
obj* x_35; obj* x_37; obj* x_39; obj* x_44; obj* x_45; obj* x_48; obj* x_49; obj* x_50; obj* x_52; obj* x_53; obj* x_55; obj* x_56; obj* x_57; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_64; obj* x_65; 
x_35 = lean::cnstr_get(x_30, 0);
lean::inc(x_35);
x_37 = lean::cnstr_get(x_30, 1);
lean::inc(x_37);
x_39 = lean::cnstr_get(x_30, 2);
lean::inc(x_39);
lean::dec(x_30);
lean::inc(x_1);
lean::inc(x_1);
x_44 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_44, 0, x_1);
lean::cnstr_set(x_44, 1, x_1);
x_45 = lean::string_iterator_offset(x_1);
lean::inc(x_37);
lean::inc(x_37);
x_48 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_48, 0, x_37);
lean::cnstr_set(x_48, 1, x_37);
x_49 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_49, 0, x_44);
lean::cnstr_set(x_49, 1, x_45);
lean::cnstr_set(x_49, 2, x_48);
x_50 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_50, 0, x_49);
lean::inc(x_37);
x_52 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_52, 0, x_1);
lean::cnstr_set(x_52, 1, x_37);
x_53 = lean::box(0);
lean::inc(x_53);
x_55 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_55, 0, x_50);
lean::cnstr_set(x_55, 1, x_52);
lean::cnstr_set(x_55, 2, x_35);
lean::cnstr_set(x_55, 3, x_53);
lean::cnstr_set(x_55, 4, x_53);
x_56 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_56, 0, x_55);
x_57 = l_lean_parser_finish__comment__block___closed__2;
lean::inc(x_57);
if (lean::is_scalar(x_17)) {
 x_59 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_59 = x_17;
}
lean::cnstr_set(x_59, 0, x_56);
lean::cnstr_set(x_59, 1, x_37);
lean::cnstr_set(x_59, 2, x_57);
x_60 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_39, x_59);
x_61 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_60);
x_62 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_62);
x_64 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_62, x_61);
if (lean::is_scalar(x_10)) {
 x_65 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_65 = x_10;
}
lean::cnstr_set(x_65, 0, x_64);
lean::cnstr_set(x_65, 1, x_32);
return x_65;
}
else
{
obj* x_68; uint8 x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_77; obj* x_78; 
lean::dec(x_17);
lean::dec(x_1);
x_68 = lean::cnstr_get(x_30, 0);
lean::inc(x_68);
x_70 = lean::cnstr_get_scalar<uint8>(x_30, sizeof(void*)*1);
if (lean::is_shared(x_30)) {
 lean::dec(x_30);
 x_71 = lean::box(0);
} else {
 lean::cnstr_release(x_30, 0);
 x_71 = x_30;
}
if (lean::is_scalar(x_71)) {
 x_72 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_72 = x_71;
}
lean::cnstr_set(x_72, 0, x_68);
lean::cnstr_set_scalar(x_72, sizeof(void*)*1, x_70);
x_73 = x_72;
x_74 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_73);
x_75 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_75);
x_77 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_75, x_74);
if (lean::is_scalar(x_10)) {
 x_78 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_78 = x_10;
}
lean::cnstr_set(x_78, 0, x_77);
lean::cnstr_set(x_78, 1, x_32);
return x_78;
}
}
}
else
{
obj* x_81; uint8 x_83; obj* x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_89; obj* x_90; 
lean::dec(x_1);
lean::dec(x_0);
x_81 = lean::cnstr_get(x_6, 0);
lean::inc(x_81);
x_83 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*1);
if (lean::is_shared(x_6)) {
 lean::dec(x_6);
 x_84 = lean::box(0);
} else {
 lean::cnstr_release(x_6, 0);
 x_84 = x_6;
}
if (lean::is_scalar(x_84)) {
 x_85 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_85 = x_84;
}
lean::cnstr_set(x_85, 0, x_81);
lean::cnstr_set_scalar(x_85, sizeof(void*)*1, x_83);
x_86 = x_85;
x_87 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_87);
x_89 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_87, x_86);
if (lean::is_scalar(x_10)) {
 x_90 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_90 = x_10;
}
lean::cnstr_set(x_90, 0, x_89);
lean::cnstr_set(x_90, 1, x_8);
return x_90;
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
obj* l_lean_parser_parsec__t_lookahead___at___private_init_lean_parser_token_4__ident_x_27___spec__19___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint32 x_4; obj* x_5; 
x_4 = lean::unbox_uint32(x_0);
x_5 = l_lean_parser_parsec__t_lookahead___at___private_init_lean_parser_token_4__ident_x_27___spec__19(x_4, x_1, x_2, x_3);
return x_5;
}
}
obj* l_lean_parser_monad__parsec_foldl__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__21___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint32 x_4; obj* x_5; 
x_4 = lean::unbox_uint32(x_0);
x_5 = l_lean_parser_monad__parsec_foldl__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__21___lambda__1(x_4, x_1, x_2, x_3);
return x_5;
}
}
obj* l_lean_parser_monad__parsec_foldl__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__21___lambda__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint32 x_5; uint32 x_6; obj* x_7; 
x_5 = lean::unbox_uint32(x_0);
x_6 = lean::unbox_uint32(x_1);
x_7 = l_lean_parser_monad__parsec_foldl__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__21___lambda__2(x_5, x_6, x_2, x_3, x_4);
return x_7;
}
}
obj* l_lean_parser_monad__parsec_foldl__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__21___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint32 x_6; obj* x_7; 
x_6 = lean::unbox_uint32(x_0);
x_7 = l_lean_parser_monad__parsec_foldl__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__21(x_6, x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
obj* l_lean_parser_monad__parsec_foldl___at___private_init_lean_parser_token_4__ident_x_27___spec__20___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint32 x_5; obj* x_6; 
x_5 = lean::unbox_uint32(x_1);
x_6 = l_lean_parser_monad__parsec_foldl___at___private_init_lean_parser_token_4__ident_x_27___spec__20(x_0, x_5, x_2, x_3, x_4);
return x_6;
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
obj* l_lean_parser_monad__parsec_many1__aux_x_27___main___at_lean_parser_parse__bin__lit___spec__2(uint32 x_0, uint32 x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; uint8 x_11; 
x_6 = lean::box_uint32(x_0);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_ch___at___private_init_lean_parser_token_4__ident_x_27___spec__11___boxed), 4, 1);
lean::closure_set(x_7, 0, x_6);
x_8 = lean::box_uint32(x_1);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_ch___at___private_init_lean_parser_token_4__ident_x_27___spec__11___boxed), 4, 1);
lean::closure_set(x_9, 0, x_8);
x_10 = lean::mk_nat_obj(0u);
x_11 = lean::nat_dec_eq(x_2, x_10);
lean::dec(x_10);
if (x_11 == 0)
{
obj* x_14; obj* x_15; obj* x_17; obj* x_19; 
lean::inc(x_3);
x_14 = l_reader__t_orelse___at_lean_parser_parse__bin__lit___spec__1___rarg(x_7, x_9, x_3, x_4, x_5);
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
obj* x_20; obj* x_22; obj* x_24; obj* x_25; obj* x_26; obj* x_30; obj* x_31; obj* x_33; 
x_20 = lean::cnstr_get(x_15, 1);
lean::inc(x_20);
x_22 = lean::cnstr_get(x_15, 2);
lean::inc(x_22);
if (lean::is_shared(x_15)) {
 lean::dec(x_15);
 x_24 = lean::box(0);
} else {
 lean::cnstr_release(x_15, 0);
 lean::cnstr_release(x_15, 1);
 lean::cnstr_release(x_15, 2);
 x_24 = x_15;
}
x_25 = lean::mk_nat_obj(1u);
x_26 = lean::nat_sub(x_2, x_25);
lean::dec(x_25);
lean::dec(x_2);
lean::inc(x_20);
x_30 = l_lean_parser_monad__parsec_many1__aux_x_27___main___at_lean_parser_parse__bin__lit___spec__2(x_0, x_1, x_26, x_3, x_20, x_17);
x_31 = lean::cnstr_get(x_30, 0);
lean::inc(x_31);
x_33 = lean::cnstr_get(x_30, 1);
lean::inc(x_33);
lean::dec(x_30);
if (lean::obj_tag(x_31) == 0)
{
obj* x_38; obj* x_39; 
lean::dec(x_20);
lean::dec(x_24);
x_38 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_22, x_31);
if (lean::is_scalar(x_19)) {
 x_39 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_39 = x_19;
}
lean::cnstr_set(x_39, 0, x_38);
lean::cnstr_set(x_39, 1, x_33);
return x_39;
}
else
{
obj* x_40; uint8 x_42; 
x_40 = lean::cnstr_get(x_31, 0);
lean::inc(x_40);
x_42 = lean::cnstr_get_scalar<uint8>(x_31, sizeof(void*)*1);
if (x_42 == 0)
{
obj* x_44; obj* x_47; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; 
lean::dec(x_31);
x_44 = lean::cnstr_get(x_40, 2);
lean::inc(x_44);
lean::dec(x_40);
x_47 = l_mjoin___rarg___closed__1;
lean::inc(x_47);
x_49 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_49, 0, x_44);
lean::closure_set(x_49, 1, x_47);
x_50 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_50, 0, x_49);
x_51 = lean::box(0);
if (lean::is_scalar(x_24)) {
 x_52 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_52 = x_24;
}
lean::cnstr_set(x_52, 0, x_51);
lean::cnstr_set(x_52, 1, x_20);
lean::cnstr_set(x_52, 2, x_50);
x_53 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_22, x_52);
if (lean::is_scalar(x_19)) {
 x_54 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_54 = x_19;
}
lean::cnstr_set(x_54, 0, x_53);
lean::cnstr_set(x_54, 1, x_33);
return x_54;
}
else
{
obj* x_58; obj* x_59; 
lean::dec(x_40);
lean::dec(x_20);
lean::dec(x_24);
x_58 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_22, x_31);
if (lean::is_scalar(x_19)) {
 x_59 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_59 = x_19;
}
lean::cnstr_set(x_59, 0, x_58);
lean::cnstr_set(x_59, 1, x_33);
return x_59;
}
}
}
else
{
obj* x_62; uint8 x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; 
lean::dec(x_3);
lean::dec(x_2);
x_62 = lean::cnstr_get(x_15, 0);
lean::inc(x_62);
x_64 = lean::cnstr_get_scalar<uint8>(x_15, sizeof(void*)*1);
if (lean::is_shared(x_15)) {
 lean::dec(x_15);
 x_65 = lean::box(0);
} else {
 lean::cnstr_release(x_15, 0);
 x_65 = x_15;
}
if (lean::is_scalar(x_65)) {
 x_66 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_66 = x_65;
}
lean::cnstr_set(x_66, 0, x_62);
lean::cnstr_set_scalar(x_66, sizeof(void*)*1, x_64);
x_67 = x_66;
if (lean::is_scalar(x_19)) {
 x_68 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_68 = x_19;
}
lean::cnstr_set(x_68, 0, x_67);
lean::cnstr_set(x_68, 1, x_17);
return x_68;
}
}
else
{
obj* x_70; obj* x_71; obj* x_73; obj* x_75; 
lean::dec(x_2);
x_70 = l_reader__t_orelse___at_lean_parser_parse__bin__lit___spec__1___rarg(x_7, x_9, x_3, x_4, x_5);
x_71 = lean::cnstr_get(x_70, 0);
lean::inc(x_71);
x_73 = lean::cnstr_get(x_70, 1);
lean::inc(x_73);
if (lean::is_shared(x_70)) {
 lean::dec(x_70);
 x_75 = lean::box(0);
} else {
 lean::cnstr_release(x_70, 0);
 lean::cnstr_release(x_70, 1);
 x_75 = x_70;
}
if (lean::obj_tag(x_71) == 0)
{
obj* x_76; obj* x_78; obj* x_80; obj* x_81; obj* x_82; obj* x_84; obj* x_85; obj* x_86; 
x_76 = lean::cnstr_get(x_71, 1);
lean::inc(x_76);
x_78 = lean::cnstr_get(x_71, 2);
lean::inc(x_78);
if (lean::is_shared(x_71)) {
 lean::dec(x_71);
 x_80 = lean::box(0);
} else {
 lean::cnstr_release(x_71, 0);
 lean::cnstr_release(x_71, 1);
 lean::cnstr_release(x_71, 2);
 x_80 = x_71;
}
x_81 = lean::box(0);
x_82 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_82);
if (lean::is_scalar(x_80)) {
 x_84 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_84 = x_80;
}
lean::cnstr_set(x_84, 0, x_81);
lean::cnstr_set(x_84, 1, x_76);
lean::cnstr_set(x_84, 2, x_82);
x_85 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_78, x_84);
if (lean::is_scalar(x_75)) {
 x_86 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_86 = x_75;
}
lean::cnstr_set(x_86, 0, x_85);
lean::cnstr_set(x_86, 1, x_73);
return x_86;
}
else
{
obj* x_87; uint8 x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; 
x_87 = lean::cnstr_get(x_71, 0);
lean::inc(x_87);
x_89 = lean::cnstr_get_scalar<uint8>(x_71, sizeof(void*)*1);
if (lean::is_shared(x_71)) {
 lean::dec(x_71);
 x_90 = lean::box(0);
} else {
 lean::cnstr_release(x_71, 0);
 x_90 = x_71;
}
if (lean::is_scalar(x_90)) {
 x_91 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_91 = x_90;
}
lean::cnstr_set(x_91, 0, x_87);
lean::cnstr_set_scalar(x_91, sizeof(void*)*1, x_89);
x_92 = x_91;
if (lean::is_scalar(x_75)) {
 x_93 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_93 = x_75;
}
lean::cnstr_set(x_93, 0, x_92);
lean::cnstr_set(x_93, 1, x_73);
return x_93;
}
}
}
}
obj* l_lean_parser_parse__bin__lit(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint32 x_3; uint32 x_4; uint8 x_5; uint32 x_6; uint8 x_7; uint32 x_8; uint8 x_9; uint32 x_10; uint8 x_11; uint32 x_12; 
x_3 = 48;
x_4 = 55296;
x_5 = x_3 < x_4;
x_6 = 98;
x_7 = x_6 < x_4;
x_8 = 66;
x_9 = x_8 < x_4;
x_10 = 49;
x_11 = x_10 < x_4;
if (x_5 == 0)
{
uint32 x_14; uint8 x_15; 
x_14 = 57343;
x_15 = x_14 < x_3;
if (x_15 == 0)
{
uint32 x_16; 
x_16 = 0;
x_12 = x_16;
goto lbl_13;
}
else
{
uint32 x_17; uint8 x_18; 
x_17 = 1114112;
x_18 = x_3 < x_17;
if (x_18 == 0)
{
uint32 x_19; 
x_19 = 0;
x_12 = x_19;
goto lbl_13;
}
else
{
x_12 = x_3;
goto lbl_13;
}
}
}
else
{
x_12 = x_3;
goto lbl_13;
}
lbl_13:
{
obj* x_21; uint32 x_22; 
lean::inc(x_0);
x_21 = l_lean_parser_monad__parsec_ch___at___private_init_lean_parser_token_4__ident_x_27___spec__11(x_12, x_0, x_1, x_2);
if (x_7 == 0)
{
uint32 x_24; uint8 x_25; 
x_24 = 57343;
x_25 = x_24 < x_6;
if (x_25 == 0)
{
uint32 x_26; 
x_26 = 0;
x_22 = x_26;
goto lbl_23;
}
else
{
uint32 x_27; uint8 x_28; 
x_27 = 1114112;
x_28 = x_6 < x_27;
if (x_28 == 0)
{
uint32 x_29; 
x_29 = 0;
x_22 = x_29;
goto lbl_23;
}
else
{
x_22 = x_6;
goto lbl_23;
}
}
}
else
{
x_22 = x_6;
goto lbl_23;
}
lbl_23:
{
uint32 x_30; 
if (x_9 == 0)
{
uint32 x_32; uint8 x_33; 
x_32 = 57343;
x_33 = x_32 < x_8;
if (x_33 == 0)
{
uint32 x_34; 
x_34 = 0;
x_30 = x_34;
goto lbl_31;
}
else
{
uint32 x_35; uint8 x_36; 
x_35 = 1114112;
x_36 = x_8 < x_35;
if (x_36 == 0)
{
uint32 x_37; 
x_37 = 0;
x_30 = x_37;
goto lbl_31;
}
else
{
x_30 = x_8;
goto lbl_31;
}
}
}
else
{
x_30 = x_8;
goto lbl_31;
}
lbl_31:
{
uint32 x_38; 
if (x_11 == 0)
{
uint32 x_40; uint8 x_41; 
x_40 = 57343;
x_41 = x_40 < x_10;
if (x_41 == 0)
{
uint32 x_42; 
x_42 = 0;
x_38 = x_42;
goto lbl_39;
}
else
{
uint32 x_43; uint8 x_44; 
x_43 = 1114112;
x_44 = x_10 < x_43;
if (x_44 == 0)
{
uint32 x_45; 
x_45 = 0;
x_38 = x_45;
goto lbl_39;
}
else
{
x_38 = x_10;
goto lbl_39;
}
}
}
else
{
x_38 = x_10;
goto lbl_39;
}
lbl_39:
{
obj* x_46; obj* x_47; obj* x_49; obj* x_51; 
x_49 = lean::cnstr_get(x_21, 0);
lean::inc(x_49);
x_51 = lean::cnstr_get(x_21, 1);
lean::inc(x_51);
lean::dec(x_21);
if (lean::obj_tag(x_49) == 0)
{
obj* x_54; obj* x_56; obj* x_61; obj* x_62; obj* x_64; 
x_54 = lean::cnstr_get(x_49, 1);
lean::inc(x_54);
x_56 = lean::cnstr_get(x_49, 2);
lean::inc(x_56);
lean::dec(x_49);
lean::inc(x_54);
lean::inc(x_0);
x_61 = l_lean_parser_monad__parsec_ch___at___private_init_lean_parser_token_4__ident_x_27___spec__11(x_22, x_0, x_54, x_51);
x_62 = lean::cnstr_get(x_61, 0);
lean::inc(x_62);
x_64 = lean::cnstr_get(x_61, 1);
lean::inc(x_64);
lean::dec(x_61);
if (lean::obj_tag(x_62) == 0)
{
obj* x_68; 
lean::dec(x_54);
x_68 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_56, x_62);
x_46 = x_68;
x_47 = x_64;
goto lbl_48;
}
else
{
obj* x_69; uint8 x_71; 
x_69 = lean::cnstr_get(x_62, 0);
lean::inc(x_69);
x_71 = lean::cnstr_get_scalar<uint8>(x_62, sizeof(void*)*1);
if (x_71 == 0)
{
obj* x_74; obj* x_75; obj* x_77; obj* x_80; obj* x_81; 
lean::dec(x_62);
lean::inc(x_0);
x_74 = l_lean_parser_monad__parsec_ch___at___private_init_lean_parser_token_4__ident_x_27___spec__11(x_30, x_0, x_54, x_64);
x_75 = lean::cnstr_get(x_74, 0);
lean::inc(x_75);
x_77 = lean::cnstr_get(x_74, 1);
lean::inc(x_77);
lean::dec(x_74);
x_80 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_69, x_75);
x_81 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_56, x_80);
x_46 = x_81;
x_47 = x_77;
goto lbl_48;
}
else
{
obj* x_84; 
lean::dec(x_54);
lean::dec(x_69);
x_84 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_56, x_62);
x_46 = x_84;
x_47 = x_64;
goto lbl_48;
}
}
}
else
{
obj* x_85; uint8 x_87; obj* x_88; obj* x_89; obj* x_90; 
x_85 = lean::cnstr_get(x_49, 0);
lean::inc(x_85);
x_87 = lean::cnstr_get_scalar<uint8>(x_49, sizeof(void*)*1);
if (lean::is_shared(x_49)) {
 lean::dec(x_49);
 x_88 = lean::box(0);
} else {
 lean::cnstr_release(x_49, 0);
 x_88 = x_49;
}
if (lean::is_scalar(x_88)) {
 x_89 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_89 = x_88;
}
lean::cnstr_set(x_89, 0, x_85);
lean::cnstr_set_scalar(x_89, sizeof(void*)*1, x_87);
x_90 = x_89;
x_46 = x_90;
x_47 = x_51;
goto lbl_48;
}
lbl_48:
{
if (lean::obj_tag(x_46) == 0)
{
obj* x_91; obj* x_93; obj* x_96; obj* x_97; obj* x_98; obj* x_100; obj* x_102; obj* x_103; obj* x_105; obj* x_106; obj* x_107; 
x_91 = lean::cnstr_get(x_46, 1);
lean::inc(x_91);
x_93 = lean::cnstr_get(x_46, 2);
lean::inc(x_93);
lean::dec(x_46);
x_96 = lean::string_iterator_remaining(x_91);
x_97 = l_lean_parser_monad__parsec_many1__aux_x_27___main___at_lean_parser_parse__bin__lit___spec__2(x_12, x_38, x_96, x_0, x_91, x_47);
x_98 = lean::cnstr_get(x_97, 0);
lean::inc(x_98);
x_100 = lean::cnstr_get(x_97, 1);
lean::inc(x_100);
if (lean::is_shared(x_97)) {
 lean::dec(x_97);
 x_102 = lean::box(0);
} else {
 lean::cnstr_release(x_97, 0);
 lean::cnstr_release(x_97, 1);
 x_102 = x_97;
}
x_103 = l_lean_parser_finish__comment__block___closed__2;
lean::inc(x_103);
x_105 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_103, x_98);
x_106 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_93, x_105);
if (lean::is_scalar(x_102)) {
 x_107 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_107 = x_102;
}
lean::cnstr_set(x_107, 0, x_106);
lean::cnstr_set(x_107, 1, x_100);
return x_107;
}
else
{
obj* x_109; uint8 x_111; obj* x_112; obj* x_113; obj* x_114; obj* x_115; 
lean::dec(x_0);
x_109 = lean::cnstr_get(x_46, 0);
lean::inc(x_109);
x_111 = lean::cnstr_get_scalar<uint8>(x_46, sizeof(void*)*1);
if (lean::is_shared(x_46)) {
 lean::dec(x_46);
 x_112 = lean::box(0);
} else {
 lean::cnstr_release(x_46, 0);
 x_112 = x_46;
}
if (lean::is_scalar(x_112)) {
 x_113 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_113 = x_112;
}
lean::cnstr_set(x_113, 0, x_109);
lean::cnstr_set_scalar(x_113, sizeof(void*)*1, x_111);
x_114 = x_113;
x_115 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_115, 0, x_114);
lean::cnstr_set(x_115, 1, x_47);
return x_115;
}
}
}
}
}
}
}
}
obj* l_lean_parser_monad__parsec_many1__aux_x_27___main___at_lean_parser_parse__bin__lit___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint32 x_6; uint32 x_7; obj* x_8; 
x_6 = lean::unbox_uint32(x_0);
x_7 = lean::unbox_uint32(x_1);
x_8 = l_lean_parser_monad__parsec_many1__aux_x_27___main___at_lean_parser_parse__bin__lit___spec__2(x_6, x_7, x_2, x_3, x_4, x_5);
return x_8;
}
}
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_parse__oct__lit___spec__3(uint32 x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::nat_dec_eq(x_1, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
uint8 x_7; 
x_7 = lean::string_iterator_has_next(x_3);
if (x_7 == 0)
{
obj* x_9; 
lean::dec(x_1);
x_9 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_2, x_3);
return x_9;
}
else
{
obj* x_10; obj* x_11; uint32 x_14; uint32 x_15; obj* x_16; uint8 x_18; uint8 x_20; 
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_sub(x_1, x_10);
lean::dec(x_10);
lean::dec(x_1);
x_14 = 55296;
x_15 = lean::string_iterator_curr(x_3);
x_20 = x_0 <= x_15;
if (x_20 == 0)
{
obj* x_22; 
lean::dec(x_11);
x_22 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_2, x_3);
return x_22;
}
else
{
uint8 x_23; 
x_23 = 1;
x_18 = x_23;
goto lbl_19;
}
lbl_17:
{
obj* x_25; obj* x_26; 
lean::dec(x_16);
x_25 = lean::string_push(x_2, x_15);
x_26 = lean::string_iterator_next(x_3);
x_1 = x_11;
x_2 = x_25;
x_3 = x_26;
goto _start;
}
lbl_19:
{
uint32 x_28; uint8 x_29; 
x_28 = 56;
x_29 = x_28 < x_14;
if (x_29 == 0)
{
uint32 x_30; uint8 x_31; 
x_30 = 57343;
x_31 = x_30 < x_28;
if (x_31 == 0)
{
uint32 x_32; uint8 x_33; 
x_32 = 0;
x_33 = x_15 < x_32;
if (x_33 == 0)
{
obj* x_35; 
lean::dec(x_11);
x_35 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_2, x_3);
return x_35;
}
else
{
if (x_18 == 0)
{
obj* x_37; 
lean::dec(x_11);
x_37 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_2, x_3);
return x_37;
}
else
{
obj* x_38; 
x_38 = lean::box(0);
x_16 = x_38;
goto lbl_17;
}
}
}
else
{
uint32 x_39; uint8 x_40; 
x_39 = 1114112;
x_40 = x_28 < x_39;
if (x_40 == 0)
{
uint32 x_41; uint8 x_42; 
x_41 = 0;
x_42 = x_15 < x_41;
if (x_42 == 0)
{
obj* x_44; 
lean::dec(x_11);
x_44 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_2, x_3);
return x_44;
}
else
{
if (x_18 == 0)
{
obj* x_46; 
lean::dec(x_11);
x_46 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_2, x_3);
return x_46;
}
else
{
obj* x_47; 
x_47 = lean::box(0);
x_16 = x_47;
goto lbl_17;
}
}
}
else
{
uint8 x_48; 
x_48 = x_15 < x_28;
if (x_48 == 0)
{
obj* x_50; 
lean::dec(x_11);
x_50 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_2, x_3);
return x_50;
}
else
{
if (x_18 == 0)
{
obj* x_52; 
lean::dec(x_11);
x_52 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_2, x_3);
return x_52;
}
else
{
obj* x_53; 
x_53 = lean::box(0);
x_16 = x_53;
goto lbl_17;
}
}
}
}
}
else
{
uint8 x_54; 
x_54 = x_15 < x_28;
if (x_54 == 0)
{
obj* x_56; 
lean::dec(x_11);
x_56 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_2, x_3);
return x_56;
}
else
{
if (x_18 == 0)
{
obj* x_58; 
lean::dec(x_11);
x_58 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_2, x_3);
return x_58;
}
else
{
obj* x_59; 
x_59 = lean::box(0);
x_16 = x_59;
goto lbl_17;
}
}
}
}
}
}
else
{
obj* x_61; 
lean::dec(x_1);
x_61 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_2, x_3);
return x_61;
}
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_parse__oct__lit___spec__2(uint32 x_0, uint32 x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
lean::dec(x_2);
x_6 = l_string_join___closed__1;
lean::inc(x_6);
x_8 = lean::string_push(x_6, x_1);
x_9 = lean::string_iterator_remaining(x_3);
x_10 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_parse__oct__lit___spec__3(x_0, x_9, x_8, x_3);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_4);
return x_11;
}
}
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_parse__oct__lit___spec__5(uint32 x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::nat_dec_eq(x_1, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
uint8 x_7; 
x_7 = lean::string_iterator_has_next(x_3);
if (x_7 == 0)
{
obj* x_9; 
lean::dec(x_1);
x_9 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_2, x_3);
return x_9;
}
else
{
obj* x_10; obj* x_11; uint32 x_14; uint32 x_15; obj* x_16; uint8 x_18; uint8 x_20; 
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_sub(x_1, x_10);
lean::dec(x_10);
lean::dec(x_1);
x_14 = 55296;
x_15 = lean::string_iterator_curr(x_3);
x_20 = x_0 <= x_15;
if (x_20 == 0)
{
obj* x_22; 
lean::dec(x_11);
x_22 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_2, x_3);
return x_22;
}
else
{
uint8 x_23; 
x_23 = 1;
x_18 = x_23;
goto lbl_19;
}
lbl_17:
{
obj* x_25; obj* x_26; 
lean::dec(x_16);
x_25 = lean::string_push(x_2, x_15);
x_26 = lean::string_iterator_next(x_3);
x_1 = x_11;
x_2 = x_25;
x_3 = x_26;
goto _start;
}
lbl_19:
{
uint32 x_28; uint8 x_29; 
x_28 = 56;
x_29 = x_28 < x_14;
if (x_29 == 0)
{
uint32 x_30; uint8 x_31; 
x_30 = 57343;
x_31 = x_30 < x_28;
if (x_31 == 0)
{
uint32 x_32; uint8 x_33; 
x_32 = 0;
x_33 = x_15 < x_32;
if (x_33 == 0)
{
obj* x_35; 
lean::dec(x_11);
x_35 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_2, x_3);
return x_35;
}
else
{
if (x_18 == 0)
{
obj* x_37; 
lean::dec(x_11);
x_37 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_2, x_3);
return x_37;
}
else
{
obj* x_38; 
x_38 = lean::box(0);
x_16 = x_38;
goto lbl_17;
}
}
}
else
{
uint32 x_39; uint8 x_40; 
x_39 = 1114112;
x_40 = x_28 < x_39;
if (x_40 == 0)
{
uint32 x_41; uint8 x_42; 
x_41 = 0;
x_42 = x_15 < x_41;
if (x_42 == 0)
{
obj* x_44; 
lean::dec(x_11);
x_44 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_2, x_3);
return x_44;
}
else
{
if (x_18 == 0)
{
obj* x_46; 
lean::dec(x_11);
x_46 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_2, x_3);
return x_46;
}
else
{
obj* x_47; 
x_47 = lean::box(0);
x_16 = x_47;
goto lbl_17;
}
}
}
else
{
uint8 x_48; 
x_48 = x_15 < x_28;
if (x_48 == 0)
{
obj* x_50; 
lean::dec(x_11);
x_50 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_2, x_3);
return x_50;
}
else
{
if (x_18 == 0)
{
obj* x_52; 
lean::dec(x_11);
x_52 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_2, x_3);
return x_52;
}
else
{
obj* x_53; 
x_53 = lean::box(0);
x_16 = x_53;
goto lbl_17;
}
}
}
}
}
else
{
uint8 x_54; 
x_54 = x_15 < x_28;
if (x_54 == 0)
{
obj* x_56; 
lean::dec(x_11);
x_56 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_2, x_3);
return x_56;
}
else
{
if (x_18 == 0)
{
obj* x_58; 
lean::dec(x_11);
x_58 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_2, x_3);
return x_58;
}
else
{
obj* x_59; 
x_59 = lean::box(0);
x_16 = x_59;
goto lbl_17;
}
}
}
}
}
}
else
{
obj* x_61; 
lean::dec(x_1);
x_61 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_2, x_3);
return x_61;
}
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_parse__oct__lit___spec__4(uint32 x_0, uint32 x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
lean::dec(x_2);
x_6 = l_string_join___closed__1;
lean::inc(x_6);
x_8 = lean::string_push(x_6, x_1);
x_9 = lean::string_iterator_remaining(x_3);
x_10 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_parse__oct__lit___spec__5(x_0, x_9, x_8, x_3);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_4);
return x_11;
}
}
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_parse__oct__lit___spec__7(uint32 x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::nat_dec_eq(x_1, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
uint8 x_7; 
x_7 = lean::string_iterator_has_next(x_3);
if (x_7 == 0)
{
obj* x_9; 
lean::dec(x_1);
x_9 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_2, x_3);
return x_9;
}
else
{
obj* x_10; obj* x_11; uint32 x_14; uint32 x_15; obj* x_16; uint8 x_18; uint8 x_20; 
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_sub(x_1, x_10);
lean::dec(x_10);
lean::dec(x_1);
x_14 = 55296;
x_15 = lean::string_iterator_curr(x_3);
x_20 = x_0 <= x_15;
if (x_20 == 0)
{
obj* x_22; 
lean::dec(x_11);
x_22 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_2, x_3);
return x_22;
}
else
{
uint8 x_23; 
x_23 = 1;
x_18 = x_23;
goto lbl_19;
}
lbl_17:
{
obj* x_25; obj* x_26; 
lean::dec(x_16);
x_25 = lean::string_push(x_2, x_15);
x_26 = lean::string_iterator_next(x_3);
x_1 = x_11;
x_2 = x_25;
x_3 = x_26;
goto _start;
}
lbl_19:
{
uint32 x_28; uint8 x_29; 
x_28 = 56;
x_29 = x_28 < x_14;
if (x_29 == 0)
{
uint32 x_30; uint8 x_31; 
x_30 = 57343;
x_31 = x_30 < x_28;
if (x_31 == 0)
{
uint32 x_32; uint8 x_33; 
x_32 = 0;
x_33 = x_15 < x_32;
if (x_33 == 0)
{
obj* x_35; 
lean::dec(x_11);
x_35 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_2, x_3);
return x_35;
}
else
{
if (x_18 == 0)
{
obj* x_37; 
lean::dec(x_11);
x_37 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_2, x_3);
return x_37;
}
else
{
obj* x_38; 
x_38 = lean::box(0);
x_16 = x_38;
goto lbl_17;
}
}
}
else
{
uint32 x_39; uint8 x_40; 
x_39 = 1114112;
x_40 = x_28 < x_39;
if (x_40 == 0)
{
uint32 x_41; uint8 x_42; 
x_41 = 0;
x_42 = x_15 < x_41;
if (x_42 == 0)
{
obj* x_44; 
lean::dec(x_11);
x_44 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_2, x_3);
return x_44;
}
else
{
if (x_18 == 0)
{
obj* x_46; 
lean::dec(x_11);
x_46 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_2, x_3);
return x_46;
}
else
{
obj* x_47; 
x_47 = lean::box(0);
x_16 = x_47;
goto lbl_17;
}
}
}
else
{
uint8 x_48; 
x_48 = x_15 < x_28;
if (x_48 == 0)
{
obj* x_50; 
lean::dec(x_11);
x_50 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_2, x_3);
return x_50;
}
else
{
if (x_18 == 0)
{
obj* x_52; 
lean::dec(x_11);
x_52 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_2, x_3);
return x_52;
}
else
{
obj* x_53; 
x_53 = lean::box(0);
x_16 = x_53;
goto lbl_17;
}
}
}
}
}
else
{
uint8 x_54; 
x_54 = x_15 < x_28;
if (x_54 == 0)
{
obj* x_56; 
lean::dec(x_11);
x_56 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_2, x_3);
return x_56;
}
else
{
if (x_18 == 0)
{
obj* x_58; 
lean::dec(x_11);
x_58 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_2, x_3);
return x_58;
}
else
{
obj* x_59; 
x_59 = lean::box(0);
x_16 = x_59;
goto lbl_17;
}
}
}
}
}
}
else
{
obj* x_61; 
lean::dec(x_1);
x_61 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_2, x_3);
return x_61;
}
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_parse__oct__lit___spec__6(uint32 x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint32 x_6; obj* x_8; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
lean::dec(x_2);
x_6 = lean::string_iterator_curr(x_1);
lean::dec(x_1);
x_8 = l_string_join___closed__1;
lean::inc(x_8);
x_10 = lean::string_push(x_8, x_6);
x_11 = lean::string_iterator_remaining(x_3);
x_12 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_parse__oct__lit___spec__7(x_0, x_11, x_10, x_3);
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_4);
return x_13;
}
}
obj* l_lean_parser_monad__parsec_take__while1___at_lean_parser_parse__oct__lit___spec__1(uint32 x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = lean::string_iterator_has_next(x_2);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; obj* x_12; obj* x_13; obj* x_15; obj* x_17; obj* x_18; obj* x_20; 
x_5 = lean::box(0);
x_6 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_7 = l_mjoin___rarg___closed__1;
lean::inc(x_1);
lean::inc(x_5);
lean::inc(x_7);
lean::inc(x_6);
x_12 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_6, x_7, x_5, x_5, x_1, x_2, x_3);
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
if (lean::obj_tag(x_20) == 0)
{
obj* x_21; obj* x_23; obj* x_25; uint32 x_28; obj* x_30; obj* x_31; obj* x_33; obj* x_36; obj* x_37; 
x_21 = lean::cnstr_get(x_20, 0);
lean::inc(x_21);
x_23 = lean::cnstr_get(x_20, 1);
lean::inc(x_23);
x_25 = lean::cnstr_get(x_20, 2);
lean::inc(x_25);
lean::dec(x_20);
x_28 = lean::unbox_uint32(x_21);
lean::dec(x_21);
x_30 = l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_parse__oct__lit___spec__2(x_0, x_28, x_1, x_23, x_15);
x_31 = lean::cnstr_get(x_30, 0);
lean::inc(x_31);
x_33 = lean::cnstr_get(x_30, 1);
lean::inc(x_33);
lean::dec(x_30);
x_36 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_25, x_31);
if (lean::is_scalar(x_17)) {
 x_37 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_37 = x_17;
}
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_33);
return x_37;
}
else
{
obj* x_39; uint8 x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; 
lean::dec(x_1);
x_39 = lean::cnstr_get(x_20, 0);
lean::inc(x_39);
x_41 = lean::cnstr_get_scalar<uint8>(x_20, sizeof(void*)*1);
if (lean::is_shared(x_20)) {
 lean::dec(x_20);
 x_42 = lean::box(0);
} else {
 lean::cnstr_release(x_20, 0);
 x_42 = x_20;
}
if (lean::is_scalar(x_42)) {
 x_43 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_43 = x_42;
}
lean::cnstr_set(x_43, 0, x_39);
lean::cnstr_set_scalar(x_43, sizeof(void*)*1, x_41);
x_44 = x_43;
if (lean::is_scalar(x_17)) {
 x_45 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_45 = x_17;
}
lean::cnstr_set(x_45, 0, x_44);
lean::cnstr_set(x_45, 1, x_15);
return x_45;
}
}
else
{
uint32 x_46; uint32 x_47; obj* x_48; obj* x_50; uint8 x_52; uint8 x_54; 
x_46 = 55296;
x_47 = lean::string_iterator_curr(x_2);
x_54 = x_0 <= x_47;
if (x_54 == 0)
{
obj* x_55; 
x_55 = lean::box(0);
x_48 = x_55;
goto lbl_49;
}
else
{
uint8 x_56; 
x_56 = 1;
x_52 = x_56;
goto lbl_53;
}
lbl_49:
{
obj* x_58; obj* x_59; obj* x_61; obj* x_63; obj* x_64; obj* x_65; obj* x_69; obj* x_70; obj* x_72; obj* x_74; obj* x_75; obj* x_77; 
lean::dec(x_48);
x_58 = l_char_quote__core(x_47);
x_59 = l_char_has__repr___closed__1;
lean::inc(x_59);
x_61 = lean::string_append(x_59, x_58);
lean::dec(x_58);
x_63 = lean::string_append(x_61, x_59);
x_64 = lean::box(0);
x_65 = l_mjoin___rarg___closed__1;
lean::inc(x_1);
lean::inc(x_64);
lean::inc(x_65);
x_69 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_63, x_65, x_64, x_64, x_1, x_2, x_3);
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
x_87 = l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_parse__oct__lit___spec__4(x_0, x_85, x_1, x_80, x_72);
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
lean::dec(x_1);
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
lbl_51:
{
obj* x_105; obj* x_106; obj* x_107; obj* x_109; obj* x_111; obj* x_112; obj* x_113; obj* x_114; 
lean::dec(x_50);
lean::inc(x_2);
x_105 = lean::string_iterator_next(x_2);
x_106 = l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_parse__oct__lit___spec__6(x_0, x_2, x_1, x_105, x_3);
x_107 = lean::cnstr_get(x_106, 0);
lean::inc(x_107);
x_109 = lean::cnstr_get(x_106, 1);
lean::inc(x_109);
if (lean::is_shared(x_106)) {
 lean::dec(x_106);
 x_111 = lean::box(0);
} else {
 lean::cnstr_release(x_106, 0);
 lean::cnstr_release(x_106, 1);
 x_111 = x_106;
}
x_112 = lean::box(0);
x_113 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_112, x_107);
if (lean::is_scalar(x_111)) {
 x_114 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_114 = x_111;
}
lean::cnstr_set(x_114, 0, x_113);
lean::cnstr_set(x_114, 1, x_109);
return x_114;
}
lbl_53:
{
uint32 x_115; uint8 x_116; 
x_115 = 56;
x_116 = x_115 < x_46;
if (x_116 == 0)
{
uint32 x_117; uint8 x_118; 
x_117 = 57343;
x_118 = x_117 < x_115;
if (x_118 == 0)
{
uint32 x_119; uint8 x_120; 
x_119 = 0;
x_120 = x_47 < x_119;
if (x_120 == 0)
{
obj* x_121; 
x_121 = lean::box(0);
x_48 = x_121;
goto lbl_49;
}
else
{
if (x_52 == 0)
{
obj* x_122; 
x_122 = lean::box(0);
x_48 = x_122;
goto lbl_49;
}
else
{
obj* x_123; 
x_123 = lean::box(0);
x_50 = x_123;
goto lbl_51;
}
}
}
else
{
uint32 x_124; uint8 x_125; 
x_124 = 1114112;
x_125 = x_115 < x_124;
if (x_125 == 0)
{
uint32 x_126; uint8 x_127; 
x_126 = 0;
x_127 = x_47 < x_126;
if (x_127 == 0)
{
obj* x_128; 
x_128 = lean::box(0);
x_48 = x_128;
goto lbl_49;
}
else
{
if (x_52 == 0)
{
obj* x_129; 
x_129 = lean::box(0);
x_48 = x_129;
goto lbl_49;
}
else
{
obj* x_130; 
x_130 = lean::box(0);
x_50 = x_130;
goto lbl_51;
}
}
}
else
{
uint8 x_131; 
x_131 = x_47 < x_115;
if (x_131 == 0)
{
obj* x_132; 
x_132 = lean::box(0);
x_48 = x_132;
goto lbl_49;
}
else
{
if (x_52 == 0)
{
obj* x_133; 
x_133 = lean::box(0);
x_48 = x_133;
goto lbl_49;
}
else
{
obj* x_134; 
x_134 = lean::box(0);
x_50 = x_134;
goto lbl_51;
}
}
}
}
}
else
{
uint8 x_135; 
x_135 = x_47 < x_115;
if (x_135 == 0)
{
obj* x_136; 
x_136 = lean::box(0);
x_48 = x_136;
goto lbl_49;
}
else
{
if (x_52 == 0)
{
obj* x_137; 
x_137 = lean::box(0);
x_48 = x_137;
goto lbl_49;
}
else
{
obj* x_138; 
x_138 = lean::box(0);
x_50 = x_138;
goto lbl_51;
}
}
}
}
}
}
}
obj* l_lean_parser_parse__oct__lit(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint32 x_3; uint32 x_4; uint8 x_5; uint32 x_6; uint8 x_7; uint32 x_8; uint8 x_9; uint32 x_10; 
x_3 = 48;
x_4 = 55296;
x_5 = x_3 < x_4;
x_6 = 111;
x_7 = x_6 < x_4;
x_8 = 79;
x_9 = x_8 < x_4;
if (x_5 == 0)
{
uint32 x_12; uint8 x_13; 
x_12 = 57343;
x_13 = x_12 < x_3;
if (x_13 == 0)
{
uint32 x_14; 
x_14 = 0;
x_10 = x_14;
goto lbl_11;
}
else
{
uint32 x_15; uint8 x_16; 
x_15 = 1114112;
x_16 = x_3 < x_15;
if (x_16 == 0)
{
uint32 x_17; 
x_17 = 0;
x_10 = x_17;
goto lbl_11;
}
else
{
x_10 = x_3;
goto lbl_11;
}
}
}
else
{
x_10 = x_3;
goto lbl_11;
}
lbl_11:
{
obj* x_18; obj* x_19; obj* x_22; uint32 x_23; 
lean::inc(x_0);
x_22 = l_lean_parser_monad__parsec_ch___at___private_init_lean_parser_token_4__ident_x_27___spec__11(x_10, x_0, x_1, x_2);
if (x_7 == 0)
{
uint32 x_25; uint8 x_26; 
x_25 = 57343;
x_26 = x_25 < x_6;
if (x_26 == 0)
{
uint32 x_27; 
x_27 = 0;
x_23 = x_27;
goto lbl_24;
}
else
{
uint32 x_28; uint8 x_29; 
x_28 = 1114112;
x_29 = x_6 < x_28;
if (x_29 == 0)
{
uint32 x_30; 
x_30 = 0;
x_23 = x_30;
goto lbl_24;
}
else
{
x_23 = x_6;
goto lbl_24;
}
}
}
else
{
x_23 = x_6;
goto lbl_24;
}
lbl_20:
{
if (lean::obj_tag(x_18) == 0)
{
obj* x_31; obj* x_33; obj* x_36; obj* x_37; obj* x_39; obj* x_41; obj* x_42; obj* x_43; 
x_31 = lean::cnstr_get(x_18, 1);
lean::inc(x_31);
x_33 = lean::cnstr_get(x_18, 2);
lean::inc(x_33);
lean::dec(x_18);
x_36 = l_lean_parser_monad__parsec_take__while1___at_lean_parser_parse__oct__lit___spec__1(x_10, x_0, x_31, x_19);
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
x_42 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_33, x_37);
if (lean::is_scalar(x_41)) {
 x_43 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_43 = x_41;
}
lean::cnstr_set(x_43, 0, x_42);
lean::cnstr_set(x_43, 1, x_39);
return x_43;
}
else
{
obj* x_45; uint8 x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; 
lean::dec(x_0);
x_45 = lean::cnstr_get(x_18, 0);
lean::inc(x_45);
x_47 = lean::cnstr_get_scalar<uint8>(x_18, sizeof(void*)*1);
if (lean::is_shared(x_18)) {
 lean::dec(x_18);
 x_48 = lean::box(0);
} else {
 lean::cnstr_release(x_18, 0);
 x_48 = x_18;
}
if (lean::is_scalar(x_48)) {
 x_49 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_49 = x_48;
}
lean::cnstr_set(x_49, 0, x_45);
lean::cnstr_set_scalar(x_49, sizeof(void*)*1, x_47);
x_50 = x_49;
x_51 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_51, 0, x_50);
lean::cnstr_set(x_51, 1, x_19);
return x_51;
}
}
lbl_24:
{
uint32 x_52; obj* x_53; obj* x_54; 
if (x_9 == 0)
{
uint32 x_56; uint8 x_57; 
x_56 = 57343;
x_57 = x_56 < x_8;
if (x_57 == 0)
{
obj* x_58; obj* x_60; uint32 x_63; 
x_58 = lean::cnstr_get(x_22, 0);
lean::inc(x_58);
x_60 = lean::cnstr_get(x_22, 1);
lean::inc(x_60);
lean::dec(x_22);
x_63 = 0;
x_52 = x_63;
x_53 = x_58;
x_54 = x_60;
goto lbl_55;
}
else
{
uint32 x_64; uint8 x_65; 
x_64 = 1114112;
x_65 = x_8 < x_64;
if (x_65 == 0)
{
obj* x_66; obj* x_68; uint32 x_71; 
x_66 = lean::cnstr_get(x_22, 0);
lean::inc(x_66);
x_68 = lean::cnstr_get(x_22, 1);
lean::inc(x_68);
lean::dec(x_22);
x_71 = 0;
x_52 = x_71;
x_53 = x_66;
x_54 = x_68;
goto lbl_55;
}
else
{
obj* x_72; obj* x_74; 
x_72 = lean::cnstr_get(x_22, 0);
lean::inc(x_72);
x_74 = lean::cnstr_get(x_22, 1);
lean::inc(x_74);
lean::dec(x_22);
x_52 = x_8;
x_53 = x_72;
x_54 = x_74;
goto lbl_55;
}
}
}
else
{
obj* x_77; obj* x_79; 
x_77 = lean::cnstr_get(x_22, 0);
lean::inc(x_77);
x_79 = lean::cnstr_get(x_22, 1);
lean::inc(x_79);
lean::dec(x_22);
x_52 = x_8;
x_53 = x_77;
x_54 = x_79;
goto lbl_55;
}
lbl_55:
{
if (lean::obj_tag(x_53) == 0)
{
obj* x_82; obj* x_84; obj* x_89; obj* x_90; obj* x_92; 
x_82 = lean::cnstr_get(x_53, 1);
lean::inc(x_82);
x_84 = lean::cnstr_get(x_53, 2);
lean::inc(x_84);
lean::dec(x_53);
lean::inc(x_82);
lean::inc(x_0);
x_89 = l_lean_parser_monad__parsec_ch___at___private_init_lean_parser_token_4__ident_x_27___spec__11(x_23, x_0, x_82, x_54);
x_90 = lean::cnstr_get(x_89, 0);
lean::inc(x_90);
x_92 = lean::cnstr_get(x_89, 1);
lean::inc(x_92);
lean::dec(x_89);
if (lean::obj_tag(x_90) == 0)
{
obj* x_96; 
lean::dec(x_82);
x_96 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_84, x_90);
x_18 = x_96;
x_19 = x_92;
goto lbl_20;
}
else
{
obj* x_97; uint8 x_99; 
x_97 = lean::cnstr_get(x_90, 0);
lean::inc(x_97);
x_99 = lean::cnstr_get_scalar<uint8>(x_90, sizeof(void*)*1);
if (x_99 == 0)
{
obj* x_102; obj* x_103; obj* x_105; obj* x_108; obj* x_109; 
lean::dec(x_90);
lean::inc(x_0);
x_102 = l_lean_parser_monad__parsec_ch___at___private_init_lean_parser_token_4__ident_x_27___spec__11(x_52, x_0, x_82, x_92);
x_103 = lean::cnstr_get(x_102, 0);
lean::inc(x_103);
x_105 = lean::cnstr_get(x_102, 1);
lean::inc(x_105);
lean::dec(x_102);
x_108 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_97, x_103);
x_109 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_84, x_108);
x_18 = x_109;
x_19 = x_105;
goto lbl_20;
}
else
{
obj* x_112; 
lean::dec(x_82);
lean::dec(x_97);
x_112 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_84, x_90);
x_18 = x_112;
x_19 = x_92;
goto lbl_20;
}
}
}
else
{
obj* x_113; uint8 x_115; obj* x_116; obj* x_117; obj* x_118; 
x_113 = lean::cnstr_get(x_53, 0);
lean::inc(x_113);
x_115 = lean::cnstr_get_scalar<uint8>(x_53, sizeof(void*)*1);
if (lean::is_shared(x_53)) {
 lean::dec(x_53);
 x_116 = lean::box(0);
} else {
 lean::cnstr_release(x_53, 0);
 x_116 = x_53;
}
if (lean::is_scalar(x_116)) {
 x_117 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_117 = x_116;
}
lean::cnstr_set(x_117, 0, x_113);
lean::cnstr_set_scalar(x_117, sizeof(void*)*1, x_115);
x_118 = x_117;
x_18 = x_118;
x_19 = x_54;
goto lbl_20;
}
}
}
}
}
}
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_parse__oct__lit___spec__3___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint32 x_4; obj* x_5; 
x_4 = lean::unbox_uint32(x_0);
x_5 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_parse__oct__lit___spec__3(x_4, x_1, x_2, x_3);
return x_5;
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_parse__oct__lit___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint32 x_5; uint32 x_6; obj* x_7; 
x_5 = lean::unbox_uint32(x_0);
x_6 = lean::unbox_uint32(x_1);
x_7 = l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_parse__oct__lit___spec__2(x_5, x_6, x_2, x_3, x_4);
return x_7;
}
}
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_parse__oct__lit___spec__5___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint32 x_4; obj* x_5; 
x_4 = lean::unbox_uint32(x_0);
x_5 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_parse__oct__lit___spec__5(x_4, x_1, x_2, x_3);
return x_5;
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_parse__oct__lit___spec__4___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint32 x_5; uint32 x_6; obj* x_7; 
x_5 = lean::unbox_uint32(x_0);
x_6 = lean::unbox_uint32(x_1);
x_7 = l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_parse__oct__lit___spec__4(x_5, x_6, x_2, x_3, x_4);
return x_7;
}
}
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_parse__oct__lit___spec__7___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint32 x_4; obj* x_5; 
x_4 = lean::unbox_uint32(x_0);
x_5 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_parse__oct__lit___spec__7(x_4, x_1, x_2, x_3);
return x_5;
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_parse__oct__lit___spec__6___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint32 x_5; obj* x_6; 
x_5 = lean::unbox_uint32(x_0);
x_6 = l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_parse__oct__lit___spec__6(x_5, x_1, x_2, x_3, x_4);
return x_6;
}
}
obj* l_lean_parser_monad__parsec_take__while1___at_lean_parser_parse__oct__lit___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint32 x_4; obj* x_5; 
x_4 = lean::unbox_uint32(x_0);
x_5 = l_lean_parser_monad__parsec_take__while1___at_lean_parser_parse__oct__lit___spec__1(x_4, x_1, x_2, x_3);
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
uint32 x_3; uint32 x_4; uint8 x_5; uint32 x_6; uint8 x_7; uint32 x_8; uint8 x_9; obj* x_10; obj* x_11; uint32 x_13; 
x_3 = 48;
x_4 = 55296;
x_5 = x_3 < x_4;
x_6 = 120;
x_7 = x_6 < x_4;
x_8 = 88;
x_9 = x_8 < x_4;
if (x_5 == 0)
{
uint32 x_15; uint8 x_16; 
x_15 = 57343;
x_16 = x_15 < x_3;
if (x_16 == 0)
{
uint32 x_17; 
x_17 = 0;
x_13 = x_17;
goto lbl_14;
}
else
{
uint32 x_18; uint8 x_19; 
x_18 = 1114112;
x_19 = x_3 < x_18;
if (x_19 == 0)
{
uint32 x_20; 
x_20 = 0;
x_13 = x_20;
goto lbl_14;
}
else
{
x_13 = x_3;
goto lbl_14;
}
}
}
else
{
x_13 = x_3;
goto lbl_14;
}
lbl_12:
{
if (lean::obj_tag(x_10) == 0)
{
obj* x_21; obj* x_23; obj* x_26; obj* x_27; obj* x_29; obj* x_31; obj* x_32; obj* x_33; 
x_21 = lean::cnstr_get(x_10, 1);
lean::inc(x_21);
x_23 = lean::cnstr_get(x_10, 2);
lean::inc(x_23);
lean::dec(x_10);
x_26 = l_lean_parser_monad__parsec_take__while1___at_lean_parser_parse__hex__lit___spec__1(x_0, x_21, x_11);
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
x_32 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_23, x_27);
if (lean::is_scalar(x_31)) {
 x_33 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_33 = x_31;
}
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_29);
return x_33;
}
else
{
obj* x_35; uint8 x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; 
lean::dec(x_0);
x_35 = lean::cnstr_get(x_10, 0);
lean::inc(x_35);
x_37 = lean::cnstr_get_scalar<uint8>(x_10, sizeof(void*)*1);
if (lean::is_shared(x_10)) {
 lean::dec(x_10);
 x_38 = lean::box(0);
} else {
 lean::cnstr_release(x_10, 0);
 x_38 = x_10;
}
if (lean::is_scalar(x_38)) {
 x_39 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_39 = x_38;
}
lean::cnstr_set(x_39, 0, x_35);
lean::cnstr_set_scalar(x_39, sizeof(void*)*1, x_37);
x_40 = x_39;
x_41 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_41, 0, x_40);
lean::cnstr_set(x_41, 1, x_11);
return x_41;
}
}
lbl_14:
{
obj* x_43; uint32 x_44; 
lean::inc(x_0);
x_43 = l_lean_parser_monad__parsec_ch___at___private_init_lean_parser_token_4__ident_x_27___spec__11(x_13, x_0, x_1, x_2);
if (x_7 == 0)
{
uint32 x_46; uint8 x_47; 
x_46 = 57343;
x_47 = x_46 < x_6;
if (x_47 == 0)
{
uint32 x_48; 
x_48 = 0;
x_44 = x_48;
goto lbl_45;
}
else
{
uint32 x_49; uint8 x_50; 
x_49 = 1114112;
x_50 = x_6 < x_49;
if (x_50 == 0)
{
uint32 x_51; 
x_51 = 0;
x_44 = x_51;
goto lbl_45;
}
else
{
x_44 = x_6;
goto lbl_45;
}
}
}
else
{
x_44 = x_6;
goto lbl_45;
}
lbl_45:
{
uint32 x_52; obj* x_53; obj* x_54; 
if (x_9 == 0)
{
uint32 x_56; uint8 x_57; 
x_56 = 57343;
x_57 = x_56 < x_8;
if (x_57 == 0)
{
obj* x_58; obj* x_60; uint32 x_63; 
x_58 = lean::cnstr_get(x_43, 0);
lean::inc(x_58);
x_60 = lean::cnstr_get(x_43, 1);
lean::inc(x_60);
lean::dec(x_43);
x_63 = 0;
x_52 = x_63;
x_53 = x_58;
x_54 = x_60;
goto lbl_55;
}
else
{
uint32 x_64; uint8 x_65; 
x_64 = 1114112;
x_65 = x_8 < x_64;
if (x_65 == 0)
{
obj* x_66; obj* x_68; uint32 x_71; 
x_66 = lean::cnstr_get(x_43, 0);
lean::inc(x_66);
x_68 = lean::cnstr_get(x_43, 1);
lean::inc(x_68);
lean::dec(x_43);
x_71 = 0;
x_52 = x_71;
x_53 = x_66;
x_54 = x_68;
goto lbl_55;
}
else
{
obj* x_72; obj* x_74; 
x_72 = lean::cnstr_get(x_43, 0);
lean::inc(x_72);
x_74 = lean::cnstr_get(x_43, 1);
lean::inc(x_74);
lean::dec(x_43);
x_52 = x_8;
x_53 = x_72;
x_54 = x_74;
goto lbl_55;
}
}
}
else
{
obj* x_77; obj* x_79; 
x_77 = lean::cnstr_get(x_43, 0);
lean::inc(x_77);
x_79 = lean::cnstr_get(x_43, 1);
lean::inc(x_79);
lean::dec(x_43);
x_52 = x_8;
x_53 = x_77;
x_54 = x_79;
goto lbl_55;
}
lbl_55:
{
if (lean::obj_tag(x_53) == 0)
{
obj* x_82; obj* x_84; obj* x_89; obj* x_90; obj* x_92; 
x_82 = lean::cnstr_get(x_53, 1);
lean::inc(x_82);
x_84 = lean::cnstr_get(x_53, 2);
lean::inc(x_84);
lean::dec(x_53);
lean::inc(x_82);
lean::inc(x_0);
x_89 = l_lean_parser_monad__parsec_ch___at___private_init_lean_parser_token_4__ident_x_27___spec__11(x_44, x_0, x_82, x_54);
x_90 = lean::cnstr_get(x_89, 0);
lean::inc(x_90);
x_92 = lean::cnstr_get(x_89, 1);
lean::inc(x_92);
lean::dec(x_89);
if (lean::obj_tag(x_90) == 0)
{
obj* x_96; 
lean::dec(x_82);
x_96 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_84, x_90);
x_10 = x_96;
x_11 = x_92;
goto lbl_12;
}
else
{
obj* x_97; uint8 x_99; 
x_97 = lean::cnstr_get(x_90, 0);
lean::inc(x_97);
x_99 = lean::cnstr_get_scalar<uint8>(x_90, sizeof(void*)*1);
if (x_99 == 0)
{
obj* x_102; obj* x_103; obj* x_105; obj* x_108; obj* x_109; 
lean::dec(x_90);
lean::inc(x_0);
x_102 = l_lean_parser_monad__parsec_ch___at___private_init_lean_parser_token_4__ident_x_27___spec__11(x_52, x_0, x_82, x_92);
x_103 = lean::cnstr_get(x_102, 0);
lean::inc(x_103);
x_105 = lean::cnstr_get(x_102, 1);
lean::inc(x_105);
lean::dec(x_102);
x_108 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_97, x_103);
x_109 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_84, x_108);
x_10 = x_109;
x_11 = x_105;
goto lbl_12;
}
else
{
obj* x_112; 
lean::dec(x_82);
lean::dec(x_97);
x_112 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_84, x_90);
x_10 = x_112;
x_11 = x_92;
goto lbl_12;
}
}
}
else
{
obj* x_113; uint8 x_115; obj* x_116; obj* x_117; obj* x_118; 
x_113 = lean::cnstr_get(x_53, 0);
lean::inc(x_113);
x_115 = lean::cnstr_get_scalar<uint8>(x_53, sizeof(void*)*1);
if (lean::is_shared(x_53)) {
 lean::dec(x_53);
 x_116 = lean::box(0);
} else {
 lean::cnstr_release(x_53, 0);
 x_116 = x_53;
}
if (lean::is_scalar(x_116)) {
 x_117 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_117 = x_116;
}
lean::cnstr_set(x_117, 0, x_113);
lean::cnstr_set_scalar(x_117, sizeof(void*)*1, x_115);
x_118 = x_117;
x_10 = x_118;
x_11 = x_54;
goto lbl_12;
}
}
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
obj* x_3; obj* x_5; obj* x_6; obj* x_10; obj* x_11; obj* x_13; 
lean::inc(x_1);
lean::inc(x_0);
x_10 = l_lean_parser_monad__parsec_digit___at_lean_parser_string__lit_x_27___spec__5(x_0, x_1, x_2);
x_11 = lean::cnstr_get(x_10, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_10, 1);
lean::inc(x_13);
lean::dec(x_10);
if (lean::obj_tag(x_11) == 0)
{
obj* x_16; obj* x_18; obj* x_20; obj* x_22; uint32 x_23; obj* x_25; uint32 x_26; uint32 x_27; uint8 x_28; 
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
x_23 = lean::unbox_uint32(x_16);
lean::dec(x_16);
x_25 = lean::uint32_to_nat(x_23);
x_26 = 48;
x_27 = 55296;
x_28 = x_26 < x_27;
if (x_28 == 0)
{
uint32 x_29; uint8 x_30; 
x_29 = 57343;
x_30 = x_29 < x_26;
if (x_30 == 0)
{
obj* x_31; obj* x_32; obj* x_34; obj* x_36; obj* x_37; 
x_31 = l___private_init_data_string_basic_4__to__nat__core___main___closed__1;
x_32 = lean::nat_sub(x_25, x_31);
lean::dec(x_25);
x_34 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_34);
if (lean::is_scalar(x_22)) {
 x_36 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_36 = x_22;
}
lean::cnstr_set(x_36, 0, x_32);
lean::cnstr_set(x_36, 1, x_18);
lean::cnstr_set(x_36, 2, x_34);
x_37 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_20, x_36);
x_5 = x_37;
x_6 = x_13;
goto lbl_7;
}
else
{
uint32 x_38; uint8 x_39; 
x_38 = 1114112;
x_39 = x_26 < x_38;
if (x_39 == 0)
{
obj* x_40; obj* x_41; obj* x_43; obj* x_45; obj* x_46; 
x_40 = l___private_init_data_string_basic_4__to__nat__core___main___closed__1;
x_41 = lean::nat_sub(x_25, x_40);
lean::dec(x_25);
x_43 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_43);
if (lean::is_scalar(x_22)) {
 x_45 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_45 = x_22;
}
lean::cnstr_set(x_45, 0, x_41);
lean::cnstr_set(x_45, 1, x_18);
lean::cnstr_set(x_45, 2, x_43);
x_46 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_20, x_45);
x_5 = x_46;
x_6 = x_13;
goto lbl_7;
}
else
{
obj* x_47; obj* x_48; obj* x_50; obj* x_52; obj* x_53; 
x_47 = l___private_init_data_string_basic_4__to__nat__core___main___closed__2;
x_48 = lean::nat_sub(x_25, x_47);
lean::dec(x_25);
x_50 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_50);
if (lean::is_scalar(x_22)) {
 x_52 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_52 = x_22;
}
lean::cnstr_set(x_52, 0, x_48);
lean::cnstr_set(x_52, 1, x_18);
lean::cnstr_set(x_52, 2, x_50);
x_53 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_20, x_52);
x_5 = x_53;
x_6 = x_13;
goto lbl_7;
}
}
}
else
{
obj* x_54; obj* x_55; obj* x_57; obj* x_59; obj* x_60; 
x_54 = l___private_init_data_string_basic_4__to__nat__core___main___closed__2;
x_55 = lean::nat_sub(x_25, x_54);
lean::dec(x_25);
x_57 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_57);
if (lean::is_scalar(x_22)) {
 x_59 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_59 = x_22;
}
lean::cnstr_set(x_59, 0, x_55);
lean::cnstr_set(x_59, 1, x_18);
lean::cnstr_set(x_59, 2, x_57);
x_60 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_20, x_59);
x_5 = x_60;
x_6 = x_13;
goto lbl_7;
}
}
else
{
obj* x_61; uint8 x_63; obj* x_64; obj* x_65; obj* x_66; 
x_61 = lean::cnstr_get(x_11, 0);
lean::inc(x_61);
x_63 = lean::cnstr_get_scalar<uint8>(x_11, sizeof(void*)*1);
if (lean::is_shared(x_11)) {
 lean::dec(x_11);
 x_64 = lean::box(0);
} else {
 lean::cnstr_release(x_11, 0);
 x_64 = x_11;
}
if (lean::is_scalar(x_64)) {
 x_65 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_65 = x_64;
}
lean::cnstr_set(x_65, 0, x_61);
lean::cnstr_set_scalar(x_65, sizeof(void*)*1, x_63);
x_66 = x_65;
x_5 = x_66;
x_6 = x_13;
goto lbl_7;
}
lbl_4:
{
obj* x_67; obj* x_69; obj* x_71; obj* x_72; obj* x_74; obj* x_75; 
x_67 = lean::cnstr_get(x_3, 0);
lean::inc(x_67);
x_69 = lean::cnstr_get(x_3, 1);
lean::inc(x_69);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_71 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 1);
 x_71 = x_3;
}
x_72 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__4___closed__1;
lean::inc(x_72);
x_74 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_67, x_72);
if (lean::is_scalar(x_71)) {
 x_75 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_75 = x_71;
}
lean::cnstr_set(x_75, 0, x_74);
lean::cnstr_set(x_75, 1, x_69);
return x_75;
}
lbl_7:
{
if (lean::obj_tag(x_5) == 0)
{
obj* x_78; obj* x_80; obj* x_81; 
lean::dec(x_1);
lean::dec(x_0);
x_78 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__4___closed__1;
lean::inc(x_78);
x_80 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_5, x_78);
x_81 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_81, 0, x_80);
lean::cnstr_set(x_81, 1, x_6);
return x_81;
}
else
{
obj* x_82; uint8 x_84; obj* x_85; obj* x_87; obj* x_88; obj* x_90; obj* x_91; 
x_82 = lean::cnstr_get(x_5, 0);
lean::inc(x_82);
x_84 = lean::cnstr_get_scalar<uint8>(x_5, sizeof(void*)*1);
if (x_84 == 0)
{
uint8 x_94; 
lean::dec(x_5);
x_94 = lean::string_iterator_has_next(x_1);
if (x_94 == 0)
{
obj* x_95; obj* x_96; obj* x_97; obj* x_103; obj* x_104; obj* x_106; obj* x_109; obj* x_111; 
x_95 = lean::box(0);
x_96 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_97 = l_mjoin___rarg___closed__1;
lean::inc(x_1);
lean::inc(x_0);
lean::inc(x_95);
lean::inc(x_97);
lean::inc(x_96);
x_103 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_96, x_97, x_95, x_95, x_0, x_1, x_6);
x_104 = lean::cnstr_get(x_103, 0);
lean::inc(x_104);
x_106 = lean::cnstr_get(x_103, 1);
lean::inc(x_106);
lean::dec(x_103);
x_109 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_109);
x_111 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_109, x_104);
x_90 = x_111;
x_91 = x_106;
goto lbl_92;
}
else
{
uint32 x_112; obj* x_113; obj* x_115; uint32 x_117; uint32 x_118; uint8 x_119; uint8 x_120; 
x_112 = lean::string_iterator_curr(x_1);
x_117 = 97;
x_118 = 55296;
x_119 = x_117 < x_118;
if (x_119 == 0)
{
uint32 x_122; uint8 x_123; 
x_122 = 57343;
x_123 = x_122 < x_117;
if (x_123 == 0)
{
uint32 x_124; uint8 x_125; 
x_124 = 0;
x_125 = x_124 <= x_112;
if (x_125 == 0)
{
obj* x_126; 
x_126 = lean::box(0);
x_113 = x_126;
goto lbl_114;
}
else
{
uint8 x_127; 
x_127 = 1;
x_120 = x_127;
goto lbl_121;
}
}
else
{
uint32 x_128; uint8 x_129; 
x_128 = 1114112;
x_129 = x_117 < x_128;
if (x_129 == 0)
{
uint32 x_130; uint8 x_131; 
x_130 = 0;
x_131 = x_130 <= x_112;
if (x_131 == 0)
{
obj* x_132; 
x_132 = lean::box(0);
x_113 = x_132;
goto lbl_114;
}
else
{
uint8 x_133; 
x_133 = 1;
x_120 = x_133;
goto lbl_121;
}
}
else
{
uint8 x_134; 
x_134 = x_117 <= x_112;
if (x_134 == 0)
{
obj* x_135; 
x_135 = lean::box(0);
x_113 = x_135;
goto lbl_114;
}
else
{
uint8 x_136; 
x_136 = 1;
x_120 = x_136;
goto lbl_121;
}
}
}
}
else
{
uint8 x_137; 
x_137 = x_117 <= x_112;
if (x_137 == 0)
{
obj* x_138; 
x_138 = lean::box(0);
x_113 = x_138;
goto lbl_114;
}
else
{
uint8 x_139; 
x_139 = 1;
x_120 = x_139;
goto lbl_121;
}
}
lbl_114:
{
obj* x_141; obj* x_142; obj* x_144; obj* x_146; obj* x_147; obj* x_148; obj* x_153; obj* x_154; obj* x_156; obj* x_159; obj* x_161; 
lean::dec(x_113);
x_141 = l_char_quote__core(x_112);
x_142 = l_char_has__repr___closed__1;
lean::inc(x_142);
x_144 = lean::string_append(x_142, x_141);
lean::dec(x_141);
x_146 = lean::string_append(x_144, x_142);
x_147 = lean::box(0);
x_148 = l_mjoin___rarg___closed__1;
lean::inc(x_1);
lean::inc(x_0);
lean::inc(x_147);
lean::inc(x_148);
x_153 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_146, x_148, x_147, x_147, x_0, x_1, x_6);
x_154 = lean::cnstr_get(x_153, 0);
lean::inc(x_154);
x_156 = lean::cnstr_get(x_153, 1);
lean::inc(x_156);
lean::dec(x_153);
x_159 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_159);
x_161 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_159, x_154);
x_90 = x_161;
x_91 = x_156;
goto lbl_92;
}
lbl_116:
{
obj* x_164; obj* x_165; obj* x_166; obj* x_167; 
lean::dec(x_115);
lean::inc(x_1);
x_164 = lean::string_iterator_next(x_1);
x_165 = lean::box(0);
x_166 = lean::box_uint32(x_112);
x_167 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_167, 0, x_166);
lean::cnstr_set(x_167, 1, x_164);
lean::cnstr_set(x_167, 2, x_165);
x_90 = x_167;
x_91 = x_6;
goto lbl_92;
}
lbl_121:
{
uint32 x_168; uint8 x_169; 
x_168 = 102;
x_169 = x_168 < x_118;
if (x_169 == 0)
{
uint32 x_170; uint8 x_171; 
x_170 = 57343;
x_171 = x_170 < x_168;
if (x_171 == 0)
{
uint32 x_172; uint8 x_173; 
x_172 = 0;
x_173 = x_112 <= x_172;
if (x_173 == 0)
{
obj* x_174; 
x_174 = lean::box(0);
x_113 = x_174;
goto lbl_114;
}
else
{
if (x_120 == 0)
{
obj* x_175; 
x_175 = lean::box(0);
x_113 = x_175;
goto lbl_114;
}
else
{
obj* x_176; 
x_176 = lean::box(0);
x_115 = x_176;
goto lbl_116;
}
}
}
else
{
uint32 x_177; uint8 x_178; 
x_177 = 1114112;
x_178 = x_168 < x_177;
if (x_178 == 0)
{
uint32 x_179; uint8 x_180; 
x_179 = 0;
x_180 = x_112 <= x_179;
if (x_180 == 0)
{
obj* x_181; 
x_181 = lean::box(0);
x_113 = x_181;
goto lbl_114;
}
else
{
if (x_120 == 0)
{
obj* x_182; 
x_182 = lean::box(0);
x_113 = x_182;
goto lbl_114;
}
else
{
obj* x_183; 
x_183 = lean::box(0);
x_115 = x_183;
goto lbl_116;
}
}
}
else
{
uint8 x_184; 
x_184 = x_112 <= x_168;
if (x_184 == 0)
{
obj* x_185; 
x_185 = lean::box(0);
x_113 = x_185;
goto lbl_114;
}
else
{
if (x_120 == 0)
{
obj* x_186; 
x_186 = lean::box(0);
x_113 = x_186;
goto lbl_114;
}
else
{
obj* x_187; 
x_187 = lean::box(0);
x_115 = x_187;
goto lbl_116;
}
}
}
}
}
else
{
uint8 x_188; 
x_188 = x_112 <= x_168;
if (x_188 == 0)
{
obj* x_189; 
x_189 = lean::box(0);
x_113 = x_189;
goto lbl_114;
}
else
{
if (x_120 == 0)
{
obj* x_190; 
x_190 = lean::box(0);
x_113 = x_190;
goto lbl_114;
}
else
{
obj* x_191; 
x_191 = lean::box(0);
x_115 = x_191;
goto lbl_116;
}
}
}
}
}
}
else
{
obj* x_195; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_82);
x_195 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_195, 0, x_5);
lean::cnstr_set(x_195, 1, x_6);
x_3 = x_195;
goto lbl_4;
}
lbl_86:
{
obj* x_196; obj* x_198; obj* x_200; obj* x_201; obj* x_202; 
x_196 = lean::cnstr_get(x_85, 0);
lean::inc(x_196);
x_198 = lean::cnstr_get(x_85, 1);
lean::inc(x_198);
if (lean::is_shared(x_85)) {
 lean::dec(x_85);
 x_200 = lean::box(0);
} else {
 lean::cnstr_release(x_85, 0);
 lean::cnstr_release(x_85, 1);
 x_200 = x_85;
}
x_201 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_82, x_196);
if (lean::is_scalar(x_200)) {
 x_202 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_202 = x_200;
}
lean::cnstr_set(x_202, 0, x_201);
lean::cnstr_set(x_202, 1, x_198);
x_3 = x_202;
goto lbl_4;
}
lbl_89:
{
if (lean::obj_tag(x_87) == 0)
{
obj* x_205; 
lean::dec(x_1);
lean::dec(x_0);
x_205 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_205, 0, x_87);
lean::cnstr_set(x_205, 1, x_88);
x_85 = x_205;
goto lbl_86;
}
else
{
obj* x_206; uint8 x_208; obj* x_209; obj* x_210; 
x_206 = lean::cnstr_get(x_87, 0);
lean::inc(x_206);
x_208 = lean::cnstr_get_scalar<uint8>(x_87, sizeof(void*)*1);
if (x_208 == 0)
{
uint8 x_213; 
lean::dec(x_87);
x_213 = lean::string_iterator_has_next(x_1);
if (x_213 == 0)
{
obj* x_214; obj* x_215; obj* x_216; obj* x_220; obj* x_221; obj* x_223; obj* x_226; obj* x_228; 
x_214 = lean::box(0);
x_215 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_216 = l_mjoin___rarg___closed__1;
lean::inc(x_214);
lean::inc(x_216);
lean::inc(x_215);
x_220 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_215, x_216, x_214, x_214, x_0, x_1, x_88);
x_221 = lean::cnstr_get(x_220, 0);
lean::inc(x_221);
x_223 = lean::cnstr_get(x_220, 1);
lean::inc(x_223);
lean::dec(x_220);
x_226 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_226);
x_228 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_226, x_221);
x_209 = x_228;
x_210 = x_223;
goto lbl_211;
}
else
{
uint32 x_229; obj* x_230; obj* x_232; uint32 x_234; uint32 x_235; uint8 x_236; uint8 x_237; 
x_229 = lean::string_iterator_curr(x_1);
x_234 = 65;
x_235 = 55296;
x_236 = x_234 < x_235;
if (x_236 == 0)
{
uint32 x_239; uint8 x_240; 
x_239 = 57343;
x_240 = x_239 < x_234;
if (x_240 == 0)
{
uint32 x_241; uint8 x_242; 
x_241 = 0;
x_242 = x_241 <= x_229;
if (x_242 == 0)
{
obj* x_243; 
x_243 = lean::box(0);
x_230 = x_243;
goto lbl_231;
}
else
{
uint8 x_244; 
x_244 = 1;
x_237 = x_244;
goto lbl_238;
}
}
else
{
uint32 x_245; uint8 x_246; 
x_245 = 1114112;
x_246 = x_234 < x_245;
if (x_246 == 0)
{
uint32 x_247; uint8 x_248; 
x_247 = 0;
x_248 = x_247 <= x_229;
if (x_248 == 0)
{
obj* x_249; 
x_249 = lean::box(0);
x_230 = x_249;
goto lbl_231;
}
else
{
uint8 x_250; 
x_250 = 1;
x_237 = x_250;
goto lbl_238;
}
}
else
{
uint8 x_251; 
x_251 = x_234 <= x_229;
if (x_251 == 0)
{
obj* x_252; 
x_252 = lean::box(0);
x_230 = x_252;
goto lbl_231;
}
else
{
uint8 x_253; 
x_253 = 1;
x_237 = x_253;
goto lbl_238;
}
}
}
}
else
{
uint8 x_254; 
x_254 = x_234 <= x_229;
if (x_254 == 0)
{
obj* x_255; 
x_255 = lean::box(0);
x_230 = x_255;
goto lbl_231;
}
else
{
uint8 x_256; 
x_256 = 1;
x_237 = x_256;
goto lbl_238;
}
}
lbl_231:
{
obj* x_258; obj* x_259; obj* x_261; obj* x_263; obj* x_264; obj* x_265; obj* x_268; obj* x_269; obj* x_271; obj* x_274; obj* x_276; 
lean::dec(x_230);
x_258 = l_char_quote__core(x_229);
x_259 = l_char_has__repr___closed__1;
lean::inc(x_259);
x_261 = lean::string_append(x_259, x_258);
lean::dec(x_258);
x_263 = lean::string_append(x_261, x_259);
x_264 = lean::box(0);
x_265 = l_mjoin___rarg___closed__1;
lean::inc(x_264);
lean::inc(x_265);
x_268 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_263, x_265, x_264, x_264, x_0, x_1, x_88);
x_269 = lean::cnstr_get(x_268, 0);
lean::inc(x_269);
x_271 = lean::cnstr_get(x_268, 1);
lean::inc(x_271);
lean::dec(x_268);
x_274 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_274);
x_276 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_274, x_269);
x_209 = x_276;
x_210 = x_271;
goto lbl_211;
}
lbl_233:
{
obj* x_278; obj* x_279; obj* x_280; obj* x_281; 
lean::dec(x_232);
x_278 = lean::string_iterator_next(x_1);
x_279 = lean::box(0);
x_280 = lean::box_uint32(x_229);
x_281 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_281, 0, x_280);
lean::cnstr_set(x_281, 1, x_278);
lean::cnstr_set(x_281, 2, x_279);
x_209 = x_281;
x_210 = x_88;
goto lbl_211;
}
lbl_238:
{
uint32 x_282; uint8 x_283; 
x_282 = 70;
x_283 = x_282 < x_235;
if (x_283 == 0)
{
uint32 x_284; uint8 x_285; 
x_284 = 57343;
x_285 = x_284 < x_282;
if (x_285 == 0)
{
uint32 x_286; uint8 x_287; 
x_286 = 0;
x_287 = x_229 <= x_286;
if (x_287 == 0)
{
obj* x_288; 
x_288 = lean::box(0);
x_230 = x_288;
goto lbl_231;
}
else
{
if (x_237 == 0)
{
obj* x_289; 
x_289 = lean::box(0);
x_230 = x_289;
goto lbl_231;
}
else
{
obj* x_291; 
lean::dec(x_0);
x_291 = lean::box(0);
x_232 = x_291;
goto lbl_233;
}
}
}
else
{
uint32 x_292; uint8 x_293; 
x_292 = 1114112;
x_293 = x_282 < x_292;
if (x_293 == 0)
{
uint32 x_294; uint8 x_295; 
x_294 = 0;
x_295 = x_229 <= x_294;
if (x_295 == 0)
{
obj* x_296; 
x_296 = lean::box(0);
x_230 = x_296;
goto lbl_231;
}
else
{
if (x_237 == 0)
{
obj* x_297; 
x_297 = lean::box(0);
x_230 = x_297;
goto lbl_231;
}
else
{
obj* x_299; 
lean::dec(x_0);
x_299 = lean::box(0);
x_232 = x_299;
goto lbl_233;
}
}
}
else
{
uint8 x_300; 
x_300 = x_229 <= x_282;
if (x_300 == 0)
{
obj* x_301; 
x_301 = lean::box(0);
x_230 = x_301;
goto lbl_231;
}
else
{
if (x_237 == 0)
{
obj* x_302; 
x_302 = lean::box(0);
x_230 = x_302;
goto lbl_231;
}
else
{
obj* x_304; 
lean::dec(x_0);
x_304 = lean::box(0);
x_232 = x_304;
goto lbl_233;
}
}
}
}
}
else
{
uint8 x_305; 
x_305 = x_229 <= x_282;
if (x_305 == 0)
{
obj* x_306; 
x_306 = lean::box(0);
x_230 = x_306;
goto lbl_231;
}
else
{
if (x_237 == 0)
{
obj* x_307; 
x_307 = lean::box(0);
x_230 = x_307;
goto lbl_231;
}
else
{
obj* x_309; 
lean::dec(x_0);
x_309 = lean::box(0);
x_232 = x_309;
goto lbl_233;
}
}
}
}
}
}
else
{
obj* x_313; 
lean::dec(x_206);
lean::dec(x_1);
lean::dec(x_0);
x_313 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_313, 0, x_87);
lean::cnstr_set(x_313, 1, x_88);
x_85 = x_313;
goto lbl_86;
}
lbl_211:
{
if (lean::obj_tag(x_209) == 0)
{
obj* x_314; obj* x_316; obj* x_318; obj* x_320; uint32 x_321; obj* x_323; uint32 x_324; uint32 x_325; uint8 x_326; 
x_314 = lean::cnstr_get(x_209, 0);
lean::inc(x_314);
x_316 = lean::cnstr_get(x_209, 1);
lean::inc(x_316);
x_318 = lean::cnstr_get(x_209, 2);
lean::inc(x_318);
if (lean::is_shared(x_209)) {
 lean::dec(x_209);
 x_320 = lean::box(0);
} else {
 lean::cnstr_release(x_209, 0);
 lean::cnstr_release(x_209, 1);
 lean::cnstr_release(x_209, 2);
 x_320 = x_209;
}
x_321 = lean::unbox_uint32(x_314);
lean::dec(x_314);
x_323 = lean::uint32_to_nat(x_321);
x_324 = 65;
x_325 = 55296;
x_326 = x_324 < x_325;
if (x_326 == 0)
{
uint32 x_327; uint8 x_328; 
x_327 = 57343;
x_328 = x_327 < x_324;
if (x_328 == 0)
{
obj* x_329; obj* x_330; obj* x_332; obj* x_333; obj* x_336; obj* x_338; obj* x_339; obj* x_340; obj* x_341; 
x_329 = l___private_init_data_string_basic_4__to__nat__core___main___closed__1;
x_330 = lean::nat_sub(x_323, x_329);
lean::dec(x_323);
x_332 = lean::mk_nat_obj(10u);
x_333 = lean::nat_add(x_332, x_330);
lean::dec(x_330);
lean::dec(x_332);
x_336 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_336);
if (lean::is_scalar(x_320)) {
 x_338 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_338 = x_320;
}
lean::cnstr_set(x_338, 0, x_333);
lean::cnstr_set(x_338, 1, x_316);
lean::cnstr_set(x_338, 2, x_336);
x_339 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_318, x_338);
x_340 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_206, x_339);
x_341 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_341, 0, x_340);
lean::cnstr_set(x_341, 1, x_210);
x_85 = x_341;
goto lbl_86;
}
else
{
uint32 x_342; uint8 x_343; 
x_342 = 1114112;
x_343 = x_324 < x_342;
if (x_343 == 0)
{
obj* x_344; obj* x_345; obj* x_347; obj* x_348; obj* x_351; obj* x_353; obj* x_354; obj* x_355; obj* x_356; 
x_344 = l___private_init_data_string_basic_4__to__nat__core___main___closed__1;
x_345 = lean::nat_sub(x_323, x_344);
lean::dec(x_323);
x_347 = lean::mk_nat_obj(10u);
x_348 = lean::nat_add(x_347, x_345);
lean::dec(x_345);
lean::dec(x_347);
x_351 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_351);
if (lean::is_scalar(x_320)) {
 x_353 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_353 = x_320;
}
lean::cnstr_set(x_353, 0, x_348);
lean::cnstr_set(x_353, 1, x_316);
lean::cnstr_set(x_353, 2, x_351);
x_354 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_318, x_353);
x_355 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_206, x_354);
x_356 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_356, 0, x_355);
lean::cnstr_set(x_356, 1, x_210);
x_85 = x_356;
goto lbl_86;
}
else
{
obj* x_357; obj* x_358; obj* x_360; obj* x_361; obj* x_364; obj* x_366; obj* x_367; obj* x_368; obj* x_369; 
x_357 = l_lean_parser_parse__hex__digit___rarg___lambda__5___closed__1;
x_358 = lean::nat_sub(x_323, x_357);
lean::dec(x_323);
x_360 = lean::mk_nat_obj(10u);
x_361 = lean::nat_add(x_360, x_358);
lean::dec(x_358);
lean::dec(x_360);
x_364 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_364);
if (lean::is_scalar(x_320)) {
 x_366 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_366 = x_320;
}
lean::cnstr_set(x_366, 0, x_361);
lean::cnstr_set(x_366, 1, x_316);
lean::cnstr_set(x_366, 2, x_364);
x_367 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_318, x_366);
x_368 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_206, x_367);
x_369 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_369, 0, x_368);
lean::cnstr_set(x_369, 1, x_210);
x_85 = x_369;
goto lbl_86;
}
}
}
else
{
obj* x_370; obj* x_371; obj* x_373; obj* x_374; obj* x_377; obj* x_379; obj* x_380; obj* x_381; obj* x_382; 
x_370 = l_lean_parser_parse__hex__digit___rarg___lambda__5___closed__1;
x_371 = lean::nat_sub(x_323, x_370);
lean::dec(x_323);
x_373 = lean::mk_nat_obj(10u);
x_374 = lean::nat_add(x_373, x_371);
lean::dec(x_371);
lean::dec(x_373);
x_377 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_377);
if (lean::is_scalar(x_320)) {
 x_379 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_379 = x_320;
}
lean::cnstr_set(x_379, 0, x_374);
lean::cnstr_set(x_379, 1, x_316);
lean::cnstr_set(x_379, 2, x_377);
x_380 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_318, x_379);
x_381 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_206, x_380);
x_382 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_382, 0, x_381);
lean::cnstr_set(x_382, 1, x_210);
x_85 = x_382;
goto lbl_86;
}
}
else
{
obj* x_383; uint8 x_385; obj* x_386; obj* x_387; obj* x_388; obj* x_389; obj* x_390; 
x_383 = lean::cnstr_get(x_209, 0);
lean::inc(x_383);
x_385 = lean::cnstr_get_scalar<uint8>(x_209, sizeof(void*)*1);
if (lean::is_shared(x_209)) {
 lean::dec(x_209);
 x_386 = lean::box(0);
} else {
 lean::cnstr_release(x_209, 0);
 x_386 = x_209;
}
if (lean::is_scalar(x_386)) {
 x_387 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_387 = x_386;
}
lean::cnstr_set(x_387, 0, x_383);
lean::cnstr_set_scalar(x_387, sizeof(void*)*1, x_385);
x_388 = x_387;
x_389 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_206, x_388);
x_390 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_390, 0, x_389);
lean::cnstr_set(x_390, 1, x_210);
x_85 = x_390;
goto lbl_86;
}
}
}
}
lbl_92:
{
if (lean::obj_tag(x_90) == 0)
{
obj* x_391; obj* x_393; obj* x_395; obj* x_397; uint32 x_398; obj* x_400; uint32 x_401; uint32 x_402; uint8 x_403; 
x_391 = lean::cnstr_get(x_90, 0);
lean::inc(x_391);
x_393 = lean::cnstr_get(x_90, 1);
lean::inc(x_393);
x_395 = lean::cnstr_get(x_90, 2);
lean::inc(x_395);
if (lean::is_shared(x_90)) {
 lean::dec(x_90);
 x_397 = lean::box(0);
} else {
 lean::cnstr_release(x_90, 0);
 lean::cnstr_release(x_90, 1);
 lean::cnstr_release(x_90, 2);
 x_397 = x_90;
}
x_398 = lean::unbox_uint32(x_391);
lean::dec(x_391);
x_400 = lean::uint32_to_nat(x_398);
x_401 = 97;
x_402 = 55296;
x_403 = x_401 < x_402;
if (x_403 == 0)
{
uint32 x_404; uint8 x_405; 
x_404 = 57343;
x_405 = x_404 < x_401;
if (x_405 == 0)
{
obj* x_406; obj* x_407; obj* x_409; obj* x_410; obj* x_413; obj* x_415; obj* x_416; 
x_406 = l___private_init_data_string_basic_4__to__nat__core___main___closed__1;
x_407 = lean::nat_sub(x_400, x_406);
lean::dec(x_400);
x_409 = lean::mk_nat_obj(10u);
x_410 = lean::nat_add(x_409, x_407);
lean::dec(x_407);
lean::dec(x_409);
x_413 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_413);
if (lean::is_scalar(x_397)) {
 x_415 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_415 = x_397;
}
lean::cnstr_set(x_415, 0, x_410);
lean::cnstr_set(x_415, 1, x_393);
lean::cnstr_set(x_415, 2, x_413);
x_416 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_395, x_415);
x_87 = x_416;
x_88 = x_91;
goto lbl_89;
}
else
{
uint32 x_417; uint8 x_418; 
x_417 = 1114112;
x_418 = x_401 < x_417;
if (x_418 == 0)
{
obj* x_419; obj* x_420; obj* x_422; obj* x_423; obj* x_426; obj* x_428; obj* x_429; 
x_419 = l___private_init_data_string_basic_4__to__nat__core___main___closed__1;
x_420 = lean::nat_sub(x_400, x_419);
lean::dec(x_400);
x_422 = lean::mk_nat_obj(10u);
x_423 = lean::nat_add(x_422, x_420);
lean::dec(x_420);
lean::dec(x_422);
x_426 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_426);
if (lean::is_scalar(x_397)) {
 x_428 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_428 = x_397;
}
lean::cnstr_set(x_428, 0, x_423);
lean::cnstr_set(x_428, 1, x_393);
lean::cnstr_set(x_428, 2, x_426);
x_429 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_395, x_428);
x_87 = x_429;
x_88 = x_91;
goto lbl_89;
}
else
{
obj* x_430; obj* x_431; obj* x_433; obj* x_434; obj* x_437; obj* x_439; obj* x_440; 
x_430 = l_lean_parser_parse__hex__digit___rarg___lambda__3___closed__1;
x_431 = lean::nat_sub(x_400, x_430);
lean::dec(x_400);
x_433 = lean::mk_nat_obj(10u);
x_434 = lean::nat_add(x_433, x_431);
lean::dec(x_431);
lean::dec(x_433);
x_437 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_437);
if (lean::is_scalar(x_397)) {
 x_439 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_439 = x_397;
}
lean::cnstr_set(x_439, 0, x_434);
lean::cnstr_set(x_439, 1, x_393);
lean::cnstr_set(x_439, 2, x_437);
x_440 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_395, x_439);
x_87 = x_440;
x_88 = x_91;
goto lbl_89;
}
}
}
else
{
obj* x_441; obj* x_442; obj* x_444; obj* x_445; obj* x_448; obj* x_450; obj* x_451; 
x_441 = l_lean_parser_parse__hex__digit___rarg___lambda__3___closed__1;
x_442 = lean::nat_sub(x_400, x_441);
lean::dec(x_400);
x_444 = lean::mk_nat_obj(10u);
x_445 = lean::nat_add(x_444, x_442);
lean::dec(x_442);
lean::dec(x_444);
x_448 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_448);
if (lean::is_scalar(x_397)) {
 x_450 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_450 = x_397;
}
lean::cnstr_set(x_450, 0, x_445);
lean::cnstr_set(x_450, 1, x_393);
lean::cnstr_set(x_450, 2, x_448);
x_451 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_395, x_450);
x_87 = x_451;
x_88 = x_91;
goto lbl_89;
}
}
else
{
obj* x_452; uint8 x_454; obj* x_455; obj* x_456; obj* x_457; 
x_452 = lean::cnstr_get(x_90, 0);
lean::inc(x_452);
x_454 = lean::cnstr_get_scalar<uint8>(x_90, sizeof(void*)*1);
if (lean::is_shared(x_90)) {
 lean::dec(x_90);
 x_455 = lean::box(0);
} else {
 lean::cnstr_release(x_90, 0);
 x_455 = x_90;
}
if (lean::is_scalar(x_455)) {
 x_456 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_456 = x_455;
}
lean::cnstr_set(x_456, 0, x_452);
lean::cnstr_set_scalar(x_456, sizeof(void*)*1, x_454);
x_457 = x_456;
x_87 = x_457;
x_88 = x_91;
goto lbl_89;
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
obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_18; obj* x_20; obj* x_22; obj* x_24; obj* x_26; obj* x_28; obj* x_30; obj* x_32; obj* x_34; obj* x_36; uint32 x_38; uint32 x_39; uint8 x_40; uint32 x_41; 
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
x_38 = 92;
x_39 = 55296;
x_40 = x_38 < x_39;
if (x_40 == 0)
{
uint32 x_43; uint8 x_44; 
x_43 = 57343;
x_44 = x_43 < x_38;
if (x_44 == 0)
{
uint32 x_45; 
x_45 = 0;
x_41 = x_45;
goto lbl_42;
}
else
{
uint32 x_46; uint8 x_47; 
x_46 = 1114112;
x_47 = x_38 < x_46;
if (x_47 == 0)
{
uint32 x_48; 
x_48 = 0;
x_41 = x_48;
goto lbl_42;
}
else
{
x_41 = x_38;
goto lbl_42;
}
}
}
else
{
x_41 = x_38;
goto lbl_42;
}
lbl_19:
{
obj* x_51; obj* x_52; obj* x_54; 
lean::dec(x_18);
lean::inc(x_0);
x_51 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__4(x_0, x_13, x_8);
x_52 = lean::cnstr_get(x_51, 0);
lean::inc(x_52);
x_54 = lean::cnstr_get(x_51, 1);
lean::inc(x_54);
lean::dec(x_51);
if (lean::obj_tag(x_52) == 0)
{
obj* x_57; obj* x_59; obj* x_61; obj* x_65; obj* x_66; obj* x_68; 
x_57 = lean::cnstr_get(x_52, 0);
lean::inc(x_57);
x_59 = lean::cnstr_get(x_52, 1);
lean::inc(x_59);
x_61 = lean::cnstr_get(x_52, 2);
lean::inc(x_61);
lean::dec(x_52);
lean::inc(x_0);
x_65 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__4(x_0, x_59, x_54);
x_66 = lean::cnstr_get(x_65, 0);
lean::inc(x_66);
x_68 = lean::cnstr_get(x_65, 1);
lean::inc(x_68);
lean::dec(x_65);
if (lean::obj_tag(x_66) == 0)
{
obj* x_71; obj* x_73; obj* x_75; obj* x_79; obj* x_80; obj* x_82; 
x_71 = lean::cnstr_get(x_66, 0);
lean::inc(x_71);
x_73 = lean::cnstr_get(x_66, 1);
lean::inc(x_73);
x_75 = lean::cnstr_get(x_66, 2);
lean::inc(x_75);
lean::dec(x_66);
lean::inc(x_0);
x_79 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__4(x_0, x_73, x_68);
x_80 = lean::cnstr_get(x_79, 0);
lean::inc(x_80);
x_82 = lean::cnstr_get(x_79, 1);
lean::inc(x_82);
lean::dec(x_79);
if (lean::obj_tag(x_80) == 0)
{
obj* x_85; obj* x_87; obj* x_89; obj* x_92; obj* x_93; obj* x_95; 
x_85 = lean::cnstr_get(x_80, 0);
lean::inc(x_85);
x_87 = lean::cnstr_get(x_80, 1);
lean::inc(x_87);
x_89 = lean::cnstr_get(x_80, 2);
lean::inc(x_89);
lean::dec(x_80);
x_92 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__4(x_0, x_87, x_82);
x_93 = lean::cnstr_get(x_92, 0);
lean::inc(x_93);
x_95 = lean::cnstr_get(x_92, 1);
lean::inc(x_95);
lean::dec(x_92);
if (lean::obj_tag(x_93) == 0)
{
obj* x_98; obj* x_100; obj* x_102; obj* x_105; obj* x_106; obj* x_108; obj* x_111; obj* x_113; obj* x_116; obj* x_119; uint32 x_122; uint32 x_124; uint8 x_125; 
x_98 = lean::cnstr_get(x_93, 0);
lean::inc(x_98);
x_100 = lean::cnstr_get(x_93, 1);
lean::inc(x_100);
x_102 = lean::cnstr_get(x_93, 2);
lean::inc(x_102);
lean::dec(x_93);
x_105 = lean::mk_nat_obj(16u);
x_106 = lean::nat_mul(x_105, x_57);
lean::dec(x_57);
x_108 = lean::nat_add(x_106, x_71);
lean::dec(x_71);
lean::dec(x_106);
x_111 = lean::nat_mul(x_105, x_108);
lean::dec(x_108);
x_113 = lean::nat_add(x_111, x_85);
lean::dec(x_85);
lean::dec(x_111);
x_116 = lean::nat_mul(x_105, x_113);
lean::dec(x_113);
lean::dec(x_105);
x_119 = lean::nat_add(x_116, x_98);
lean::dec(x_98);
lean::dec(x_116);
x_122 = lean::uint32_of_nat(x_119);
lean::dec(x_119);
x_124 = 55296;
x_125 = x_122 < x_124;
if (x_125 == 0)
{
uint32 x_126; uint8 x_127; 
x_126 = 57343;
x_127 = x_126 < x_122;
if (x_127 == 0)
{
uint32 x_128; obj* x_129; obj* x_130; obj* x_132; obj* x_133; obj* x_134; obj* x_135; obj* x_136; obj* x_137; obj* x_139; obj* x_140; 
x_128 = 0;
x_129 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_130 = lean::box_uint32(x_128);
lean::inc(x_129);
if (lean::is_scalar(x_17)) {
 x_132 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_132 = x_17;
}
lean::cnstr_set(x_132, 0, x_130);
lean::cnstr_set(x_132, 1, x_100);
lean::cnstr_set(x_132, 2, x_129);
x_133 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_102, x_132);
x_134 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_89, x_133);
x_135 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_75, x_134);
x_136 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_61, x_135);
x_137 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_136);
lean::inc(x_129);
x_139 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_129, x_137);
if (lean::is_scalar(x_10)) {
 x_140 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_140 = x_10;
}
lean::cnstr_set(x_140, 0, x_139);
lean::cnstr_set(x_140, 1, x_95);
return x_140;
}
else
{
uint32 x_141; uint8 x_142; 
x_141 = 1114112;
x_142 = x_122 < x_141;
if (x_142 == 0)
{
uint32 x_143; obj* x_144; obj* x_145; obj* x_147; obj* x_148; obj* x_149; obj* x_150; obj* x_151; obj* x_152; obj* x_154; obj* x_155; 
x_143 = 0;
x_144 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_145 = lean::box_uint32(x_143);
lean::inc(x_144);
if (lean::is_scalar(x_17)) {
 x_147 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_147 = x_17;
}
lean::cnstr_set(x_147, 0, x_145);
lean::cnstr_set(x_147, 1, x_100);
lean::cnstr_set(x_147, 2, x_144);
x_148 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_102, x_147);
x_149 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_89, x_148);
x_150 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_75, x_149);
x_151 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_61, x_150);
x_152 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_151);
lean::inc(x_144);
x_154 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_144, x_152);
if (lean::is_scalar(x_10)) {
 x_155 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_155 = x_10;
}
lean::cnstr_set(x_155, 0, x_154);
lean::cnstr_set(x_155, 1, x_95);
return x_155;
}
else
{
obj* x_156; obj* x_157; obj* x_159; obj* x_160; obj* x_161; obj* x_162; obj* x_163; obj* x_164; obj* x_166; obj* x_167; 
x_156 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_157 = lean::box_uint32(x_122);
lean::inc(x_156);
if (lean::is_scalar(x_17)) {
 x_159 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_159 = x_17;
}
lean::cnstr_set(x_159, 0, x_157);
lean::cnstr_set(x_159, 1, x_100);
lean::cnstr_set(x_159, 2, x_156);
x_160 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_102, x_159);
x_161 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_89, x_160);
x_162 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_75, x_161);
x_163 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_61, x_162);
x_164 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_163);
lean::inc(x_156);
x_166 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_156, x_164);
if (lean::is_scalar(x_10)) {
 x_167 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_167 = x_10;
}
lean::cnstr_set(x_167, 0, x_166);
lean::cnstr_set(x_167, 1, x_95);
return x_167;
}
}
}
else
{
obj* x_168; obj* x_169; obj* x_171; obj* x_172; obj* x_173; obj* x_174; obj* x_175; obj* x_176; obj* x_178; obj* x_179; 
x_168 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_169 = lean::box_uint32(x_122);
lean::inc(x_168);
if (lean::is_scalar(x_17)) {
 x_171 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_171 = x_17;
}
lean::cnstr_set(x_171, 0, x_169);
lean::cnstr_set(x_171, 1, x_100);
lean::cnstr_set(x_171, 2, x_168);
x_172 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_102, x_171);
x_173 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_89, x_172);
x_174 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_75, x_173);
x_175 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_61, x_174);
x_176 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_175);
lean::inc(x_168);
x_178 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_168, x_176);
if (lean::is_scalar(x_10)) {
 x_179 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_179 = x_10;
}
lean::cnstr_set(x_179, 0, x_178);
lean::cnstr_set(x_179, 1, x_95);
return x_179;
}
}
else
{
obj* x_184; uint8 x_186; obj* x_187; obj* x_188; obj* x_189; obj* x_190; obj* x_191; obj* x_192; obj* x_193; obj* x_194; obj* x_196; obj* x_197; 
lean::dec(x_85);
lean::dec(x_71);
lean::dec(x_17);
lean::dec(x_57);
x_184 = lean::cnstr_get(x_93, 0);
lean::inc(x_184);
x_186 = lean::cnstr_get_scalar<uint8>(x_93, sizeof(void*)*1);
if (lean::is_shared(x_93)) {
 lean::dec(x_93);
 x_187 = lean::box(0);
} else {
 lean::cnstr_release(x_93, 0);
 x_187 = x_93;
}
if (lean::is_scalar(x_187)) {
 x_188 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_188 = x_187;
}
lean::cnstr_set(x_188, 0, x_184);
lean::cnstr_set_scalar(x_188, sizeof(void*)*1, x_186);
x_189 = x_188;
x_190 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_89, x_189);
x_191 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_75, x_190);
x_192 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_61, x_191);
x_193 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_192);
x_194 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_194);
x_196 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_194, x_193);
if (lean::is_scalar(x_10)) {
 x_197 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_197 = x_10;
}
lean::cnstr_set(x_197, 0, x_196);
lean::cnstr_set(x_197, 1, x_95);
return x_197;
}
}
else
{
obj* x_202; uint8 x_204; obj* x_205; obj* x_206; obj* x_207; obj* x_208; obj* x_209; obj* x_210; obj* x_211; obj* x_213; obj* x_214; 
lean::dec(x_71);
lean::dec(x_17);
lean::dec(x_0);
lean::dec(x_57);
x_202 = lean::cnstr_get(x_80, 0);
lean::inc(x_202);
x_204 = lean::cnstr_get_scalar<uint8>(x_80, sizeof(void*)*1);
if (lean::is_shared(x_80)) {
 lean::dec(x_80);
 x_205 = lean::box(0);
} else {
 lean::cnstr_release(x_80, 0);
 x_205 = x_80;
}
if (lean::is_scalar(x_205)) {
 x_206 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_206 = x_205;
}
lean::cnstr_set(x_206, 0, x_202);
lean::cnstr_set_scalar(x_206, sizeof(void*)*1, x_204);
x_207 = x_206;
x_208 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_75, x_207);
x_209 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_61, x_208);
x_210 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_209);
x_211 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_211);
x_213 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_211, x_210);
if (lean::is_scalar(x_10)) {
 x_214 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_214 = x_10;
}
lean::cnstr_set(x_214, 0, x_213);
lean::cnstr_set(x_214, 1, x_82);
return x_214;
}
}
else
{
obj* x_218; uint8 x_220; obj* x_221; obj* x_222; obj* x_223; obj* x_224; obj* x_225; obj* x_226; obj* x_228; obj* x_229; 
lean::dec(x_17);
lean::dec(x_0);
lean::dec(x_57);
x_218 = lean::cnstr_get(x_66, 0);
lean::inc(x_218);
x_220 = lean::cnstr_get_scalar<uint8>(x_66, sizeof(void*)*1);
if (lean::is_shared(x_66)) {
 lean::dec(x_66);
 x_221 = lean::box(0);
} else {
 lean::cnstr_release(x_66, 0);
 x_221 = x_66;
}
if (lean::is_scalar(x_221)) {
 x_222 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_222 = x_221;
}
lean::cnstr_set(x_222, 0, x_218);
lean::cnstr_set_scalar(x_222, sizeof(void*)*1, x_220);
x_223 = x_222;
x_224 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_61, x_223);
x_225 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_224);
x_226 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_226);
x_228 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_226, x_225);
if (lean::is_scalar(x_10)) {
 x_229 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_229 = x_10;
}
lean::cnstr_set(x_229, 0, x_228);
lean::cnstr_set(x_229, 1, x_68);
return x_229;
}
}
else
{
obj* x_232; uint8 x_234; obj* x_235; obj* x_236; obj* x_237; obj* x_238; obj* x_239; obj* x_241; obj* x_242; 
lean::dec(x_17);
lean::dec(x_0);
x_232 = lean::cnstr_get(x_52, 0);
lean::inc(x_232);
x_234 = lean::cnstr_get_scalar<uint8>(x_52, sizeof(void*)*1);
if (lean::is_shared(x_52)) {
 lean::dec(x_52);
 x_235 = lean::box(0);
} else {
 lean::cnstr_release(x_52, 0);
 x_235 = x_52;
}
if (lean::is_scalar(x_235)) {
 x_236 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_236 = x_235;
}
lean::cnstr_set(x_236, 0, x_232);
lean::cnstr_set_scalar(x_236, sizeof(void*)*1, x_234);
x_237 = x_236;
x_238 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_237);
x_239 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_239);
x_241 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_239, x_238);
if (lean::is_scalar(x_10)) {
 x_242 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_242 = x_10;
}
lean::cnstr_set(x_242, 0, x_241);
lean::cnstr_set(x_242, 1, x_54);
return x_242;
}
}
lbl_21:
{
uint32 x_244; uint32 x_245; uint8 x_246; 
lean::dec(x_20);
x_244 = 117;
x_245 = 55296;
x_246 = x_244 < x_245;
if (x_246 == 0)
{
uint32 x_247; uint8 x_248; 
x_247 = 57343;
x_248 = x_247 < x_244;
if (x_248 == 0)
{
uint32 x_249; uint32 x_250; uint8 x_252; 
x_249 = 0;
x_250 = lean::unbox_uint32(x_11);
lean::dec(x_11);
x_252 = x_250 == x_249;
if (x_252 == 0)
{
obj* x_255; obj* x_257; obj* x_258; obj* x_260; obj* x_262; obj* x_263; obj* x_264; obj* x_266; obj* x_267; 
lean::dec(x_17);
lean::dec(x_10);
x_255 = l_lean_parser_parse__quoted__char___rarg___lambda__7___closed__1;
lean::inc(x_255);
x_257 = l_lean_parser_monad__parsec_unexpected__at___at_lean_parser_string__lit_x_27___spec__6___rarg(x_255, x_1, x_0, x_13, x_8);
x_258 = lean::cnstr_get(x_257, 0);
lean::inc(x_258);
x_260 = lean::cnstr_get(x_257, 1);
lean::inc(x_260);
if (lean::is_shared(x_257)) {
 lean::dec(x_257);
 x_262 = lean::box(0);
} else {
 lean::cnstr_release(x_257, 0);
 lean::cnstr_release(x_257, 1);
 x_262 = x_257;
}
x_263 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_258);
x_264 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_264);
x_266 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_264, x_263);
if (lean::is_scalar(x_262)) {
 x_267 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_267 = x_262;
}
lean::cnstr_set(x_267, 0, x_266);
lean::cnstr_set(x_267, 1, x_260);
return x_267;
}
else
{
obj* x_269; 
lean::dec(x_1);
x_269 = lean::box(0);
x_18 = x_269;
goto lbl_19;
}
}
else
{
uint32 x_270; uint8 x_271; 
x_270 = 1114112;
x_271 = x_244 < x_270;
if (x_271 == 0)
{
uint32 x_272; uint32 x_273; uint8 x_275; 
x_272 = 0;
x_273 = lean::unbox_uint32(x_11);
lean::dec(x_11);
x_275 = x_273 == x_272;
if (x_275 == 0)
{
obj* x_278; obj* x_280; obj* x_281; obj* x_283; obj* x_285; obj* x_286; obj* x_287; obj* x_289; obj* x_290; 
lean::dec(x_17);
lean::dec(x_10);
x_278 = l_lean_parser_parse__quoted__char___rarg___lambda__7___closed__1;
lean::inc(x_278);
x_280 = l_lean_parser_monad__parsec_unexpected__at___at_lean_parser_string__lit_x_27___spec__6___rarg(x_278, x_1, x_0, x_13, x_8);
x_281 = lean::cnstr_get(x_280, 0);
lean::inc(x_281);
x_283 = lean::cnstr_get(x_280, 1);
lean::inc(x_283);
if (lean::is_shared(x_280)) {
 lean::dec(x_280);
 x_285 = lean::box(0);
} else {
 lean::cnstr_release(x_280, 0);
 lean::cnstr_release(x_280, 1);
 x_285 = x_280;
}
x_286 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_281);
x_287 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_287);
x_289 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_287, x_286);
if (lean::is_scalar(x_285)) {
 x_290 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_290 = x_285;
}
lean::cnstr_set(x_290, 0, x_289);
lean::cnstr_set(x_290, 1, x_283);
return x_290;
}
else
{
obj* x_292; 
lean::dec(x_1);
x_292 = lean::box(0);
x_18 = x_292;
goto lbl_19;
}
}
else
{
uint32 x_293; uint8 x_295; 
x_293 = lean::unbox_uint32(x_11);
lean::dec(x_11);
x_295 = x_293 == x_244;
if (x_295 == 0)
{
obj* x_298; obj* x_300; obj* x_301; obj* x_303; obj* x_305; obj* x_306; obj* x_307; obj* x_309; obj* x_310; 
lean::dec(x_17);
lean::dec(x_10);
x_298 = l_lean_parser_parse__quoted__char___rarg___lambda__7___closed__1;
lean::inc(x_298);
x_300 = l_lean_parser_monad__parsec_unexpected__at___at_lean_parser_string__lit_x_27___spec__6___rarg(x_298, x_1, x_0, x_13, x_8);
x_301 = lean::cnstr_get(x_300, 0);
lean::inc(x_301);
x_303 = lean::cnstr_get(x_300, 1);
lean::inc(x_303);
if (lean::is_shared(x_300)) {
 lean::dec(x_300);
 x_305 = lean::box(0);
} else {
 lean::cnstr_release(x_300, 0);
 lean::cnstr_release(x_300, 1);
 x_305 = x_300;
}
x_306 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_301);
x_307 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_307);
x_309 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_307, x_306);
if (lean::is_scalar(x_305)) {
 x_310 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_310 = x_305;
}
lean::cnstr_set(x_310, 0, x_309);
lean::cnstr_set(x_310, 1, x_303);
return x_310;
}
else
{
obj* x_312; 
lean::dec(x_1);
x_312 = lean::box(0);
x_18 = x_312;
goto lbl_19;
}
}
}
}
else
{
uint32 x_313; uint8 x_315; 
x_313 = lean::unbox_uint32(x_11);
lean::dec(x_11);
x_315 = x_313 == x_244;
if (x_315 == 0)
{
obj* x_318; obj* x_320; obj* x_321; obj* x_323; obj* x_325; obj* x_326; obj* x_327; obj* x_329; obj* x_330; 
lean::dec(x_17);
lean::dec(x_10);
x_318 = l_lean_parser_parse__quoted__char___rarg___lambda__7___closed__1;
lean::inc(x_318);
x_320 = l_lean_parser_monad__parsec_unexpected__at___at_lean_parser_string__lit_x_27___spec__6___rarg(x_318, x_1, x_0, x_13, x_8);
x_321 = lean::cnstr_get(x_320, 0);
lean::inc(x_321);
x_323 = lean::cnstr_get(x_320, 1);
lean::inc(x_323);
if (lean::is_shared(x_320)) {
 lean::dec(x_320);
 x_325 = lean::box(0);
} else {
 lean::cnstr_release(x_320, 0);
 lean::cnstr_release(x_320, 1);
 x_325 = x_320;
}
x_326 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_321);
x_327 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_327);
x_329 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_327, x_326);
if (lean::is_scalar(x_325)) {
 x_330 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_330 = x_325;
}
lean::cnstr_set(x_330, 0, x_329);
lean::cnstr_set(x_330, 1, x_323);
return x_330;
}
else
{
obj* x_332; 
lean::dec(x_1);
x_332 = lean::box(0);
x_18 = x_332;
goto lbl_19;
}
}
}
lbl_23:
{
obj* x_335; obj* x_336; obj* x_338; obj* x_340; 
lean::dec(x_22);
lean::inc(x_0);
x_335 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__4(x_0, x_13, x_8);
x_336 = lean::cnstr_get(x_335, 0);
lean::inc(x_336);
x_338 = lean::cnstr_get(x_335, 1);
lean::inc(x_338);
if (lean::is_shared(x_335)) {
 lean::dec(x_335);
 x_340 = lean::box(0);
} else {
 lean::cnstr_release(x_335, 0);
 lean::cnstr_release(x_335, 1);
 x_340 = x_335;
}
if (lean::obj_tag(x_336) == 0)
{
obj* x_341; obj* x_343; obj* x_345; obj* x_347; obj* x_348; obj* x_349; obj* x_351; 
x_341 = lean::cnstr_get(x_336, 0);
lean::inc(x_341);
x_343 = lean::cnstr_get(x_336, 1);
lean::inc(x_343);
x_345 = lean::cnstr_get(x_336, 2);
lean::inc(x_345);
if (lean::is_shared(x_336)) {
 lean::dec(x_336);
 x_347 = lean::box(0);
} else {
 lean::cnstr_release(x_336, 0);
 lean::cnstr_release(x_336, 1);
 lean::cnstr_release(x_336, 2);
 x_347 = x_336;
}
x_348 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__4(x_0, x_343, x_338);
x_349 = lean::cnstr_get(x_348, 0);
lean::inc(x_349);
x_351 = lean::cnstr_get(x_348, 1);
lean::inc(x_351);
lean::dec(x_348);
if (lean::obj_tag(x_349) == 0)
{
obj* x_354; obj* x_356; obj* x_358; obj* x_361; obj* x_362; obj* x_365; uint32 x_368; uint32 x_370; uint8 x_371; 
x_354 = lean::cnstr_get(x_349, 0);
lean::inc(x_354);
x_356 = lean::cnstr_get(x_349, 1);
lean::inc(x_356);
x_358 = lean::cnstr_get(x_349, 2);
lean::inc(x_358);
lean::dec(x_349);
x_361 = lean::mk_nat_obj(16u);
x_362 = lean::nat_mul(x_361, x_341);
lean::dec(x_341);
lean::dec(x_361);
x_365 = lean::nat_add(x_362, x_354);
lean::dec(x_354);
lean::dec(x_362);
x_368 = lean::uint32_of_nat(x_365);
lean::dec(x_365);
x_370 = 55296;
x_371 = x_368 < x_370;
if (x_371 == 0)
{
uint32 x_372; uint8 x_373; 
x_372 = 57343;
x_373 = x_372 < x_368;
if (x_373 == 0)
{
uint32 x_374; obj* x_375; obj* x_376; obj* x_378; obj* x_379; obj* x_380; obj* x_381; obj* x_383; obj* x_384; 
x_374 = 0;
x_375 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_376 = lean::box_uint32(x_374);
lean::inc(x_375);
if (lean::is_scalar(x_347)) {
 x_378 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_378 = x_347;
}
lean::cnstr_set(x_378, 0, x_376);
lean::cnstr_set(x_378, 1, x_356);
lean::cnstr_set(x_378, 2, x_375);
x_379 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_358, x_378);
x_380 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_345, x_379);
x_381 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_380);
lean::inc(x_375);
x_383 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_375, x_381);
if (lean::is_scalar(x_340)) {
 x_384 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_384 = x_340;
}
lean::cnstr_set(x_384, 0, x_383);
lean::cnstr_set(x_384, 1, x_351);
return x_384;
}
else
{
uint32 x_385; uint8 x_386; 
x_385 = 1114112;
x_386 = x_368 < x_385;
if (x_386 == 0)
{
uint32 x_387; obj* x_388; obj* x_389; obj* x_391; obj* x_392; obj* x_393; obj* x_394; obj* x_396; obj* x_397; 
x_387 = 0;
x_388 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_389 = lean::box_uint32(x_387);
lean::inc(x_388);
if (lean::is_scalar(x_347)) {
 x_391 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_391 = x_347;
}
lean::cnstr_set(x_391, 0, x_389);
lean::cnstr_set(x_391, 1, x_356);
lean::cnstr_set(x_391, 2, x_388);
x_392 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_358, x_391);
x_393 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_345, x_392);
x_394 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_393);
lean::inc(x_388);
x_396 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_388, x_394);
if (lean::is_scalar(x_340)) {
 x_397 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_397 = x_340;
}
lean::cnstr_set(x_397, 0, x_396);
lean::cnstr_set(x_397, 1, x_351);
return x_397;
}
else
{
obj* x_398; obj* x_399; obj* x_401; obj* x_402; obj* x_403; obj* x_404; obj* x_406; obj* x_407; 
x_398 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_399 = lean::box_uint32(x_368);
lean::inc(x_398);
if (lean::is_scalar(x_347)) {
 x_401 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_401 = x_347;
}
lean::cnstr_set(x_401, 0, x_399);
lean::cnstr_set(x_401, 1, x_356);
lean::cnstr_set(x_401, 2, x_398);
x_402 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_358, x_401);
x_403 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_345, x_402);
x_404 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_403);
lean::inc(x_398);
x_406 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_398, x_404);
if (lean::is_scalar(x_340)) {
 x_407 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_407 = x_340;
}
lean::cnstr_set(x_407, 0, x_406);
lean::cnstr_set(x_407, 1, x_351);
return x_407;
}
}
}
else
{
obj* x_408; obj* x_409; obj* x_411; obj* x_412; obj* x_413; obj* x_414; obj* x_416; obj* x_417; 
x_408 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_409 = lean::box_uint32(x_368);
lean::inc(x_408);
if (lean::is_scalar(x_347)) {
 x_411 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_411 = x_347;
}
lean::cnstr_set(x_411, 0, x_409);
lean::cnstr_set(x_411, 1, x_356);
lean::cnstr_set(x_411, 2, x_408);
x_412 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_358, x_411);
x_413 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_345, x_412);
x_414 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_413);
lean::inc(x_408);
x_416 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_408, x_414);
if (lean::is_scalar(x_340)) {
 x_417 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_417 = x_340;
}
lean::cnstr_set(x_417, 0, x_416);
lean::cnstr_set(x_417, 1, x_351);
return x_417;
}
}
else
{
obj* x_420; uint8 x_422; obj* x_423; obj* x_424; obj* x_425; obj* x_426; obj* x_427; obj* x_428; obj* x_430; obj* x_431; 
lean::dec(x_347);
lean::dec(x_341);
x_420 = lean::cnstr_get(x_349, 0);
lean::inc(x_420);
x_422 = lean::cnstr_get_scalar<uint8>(x_349, sizeof(void*)*1);
if (lean::is_shared(x_349)) {
 lean::dec(x_349);
 x_423 = lean::box(0);
} else {
 lean::cnstr_release(x_349, 0);
 x_423 = x_349;
}
if (lean::is_scalar(x_423)) {
 x_424 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_424 = x_423;
}
lean::cnstr_set(x_424, 0, x_420);
lean::cnstr_set_scalar(x_424, sizeof(void*)*1, x_422);
x_425 = x_424;
x_426 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_345, x_425);
x_427 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_426);
x_428 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_428);
x_430 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_428, x_427);
if (lean::is_scalar(x_340)) {
 x_431 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_431 = x_340;
}
lean::cnstr_set(x_431, 0, x_430);
lean::cnstr_set(x_431, 1, x_351);
return x_431;
}
}
else
{
obj* x_433; uint8 x_435; obj* x_436; obj* x_437; obj* x_438; obj* x_439; obj* x_440; obj* x_442; obj* x_443; 
lean::dec(x_0);
x_433 = lean::cnstr_get(x_336, 0);
lean::inc(x_433);
x_435 = lean::cnstr_get_scalar<uint8>(x_336, sizeof(void*)*1);
if (lean::is_shared(x_336)) {
 lean::dec(x_336);
 x_436 = lean::box(0);
} else {
 lean::cnstr_release(x_336, 0);
 x_436 = x_336;
}
if (lean::is_scalar(x_436)) {
 x_437 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_437 = x_436;
}
lean::cnstr_set(x_437, 0, x_433);
lean::cnstr_set_scalar(x_437, sizeof(void*)*1, x_435);
x_438 = x_437;
x_439 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_438);
x_440 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_440);
x_442 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_440, x_439);
if (lean::is_scalar(x_340)) {
 x_443 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_443 = x_340;
}
lean::cnstr_set(x_443, 0, x_442);
lean::cnstr_set(x_443, 1, x_338);
return x_443;
}
}
lbl_25:
{
uint32 x_445; uint32 x_446; uint8 x_447; 
lean::dec(x_24);
x_445 = 120;
x_446 = 55296;
x_447 = x_445 < x_446;
if (x_447 == 0)
{
uint32 x_448; uint8 x_449; 
x_448 = 57343;
x_449 = x_448 < x_445;
if (x_449 == 0)
{
uint32 x_450; uint32 x_451; uint8 x_452; 
x_450 = 0;
x_451 = lean::unbox_uint32(x_11);
x_452 = x_451 == x_450;
if (x_452 == 0)
{
obj* x_453; 
x_453 = lean::box(0);
x_20 = x_453;
goto lbl_21;
}
else
{
obj* x_458; 
lean::dec(x_17);
lean::dec(x_11);
lean::dec(x_1);
lean::dec(x_10);
x_458 = lean::box(0);
x_22 = x_458;
goto lbl_23;
}
}
else
{
uint32 x_459; uint8 x_460; 
x_459 = 1114112;
x_460 = x_445 < x_459;
if (x_460 == 0)
{
uint32 x_461; uint32 x_462; uint8 x_463; 
x_461 = 0;
x_462 = lean::unbox_uint32(x_11);
x_463 = x_462 == x_461;
if (x_463 == 0)
{
obj* x_464; 
x_464 = lean::box(0);
x_20 = x_464;
goto lbl_21;
}
else
{
obj* x_469; 
lean::dec(x_17);
lean::dec(x_11);
lean::dec(x_1);
lean::dec(x_10);
x_469 = lean::box(0);
x_22 = x_469;
goto lbl_23;
}
}
else
{
uint32 x_470; uint8 x_471; 
x_470 = lean::unbox_uint32(x_11);
x_471 = x_470 == x_445;
if (x_471 == 0)
{
obj* x_472; 
x_472 = lean::box(0);
x_20 = x_472;
goto lbl_21;
}
else
{
obj* x_477; 
lean::dec(x_17);
lean::dec(x_11);
lean::dec(x_1);
lean::dec(x_10);
x_477 = lean::box(0);
x_22 = x_477;
goto lbl_23;
}
}
}
}
else
{
uint32 x_478; uint8 x_479; 
x_478 = lean::unbox_uint32(x_11);
x_479 = x_478 == x_445;
if (x_479 == 0)
{
obj* x_480; 
x_480 = lean::box(0);
x_20 = x_480;
goto lbl_21;
}
else
{
obj* x_485; 
lean::dec(x_17);
lean::dec(x_11);
lean::dec(x_1);
lean::dec(x_10);
x_485 = lean::box(0);
x_22 = x_485;
goto lbl_23;
}
}
}
lbl_27:
{
uint32 x_487; uint32 x_488; uint8 x_489; 
lean::dec(x_26);
x_487 = 9;
x_488 = 55296;
x_489 = x_487 < x_488;
if (x_489 == 0)
{
uint32 x_490; uint8 x_491; 
x_490 = 57343;
x_491 = x_490 < x_487;
if (x_491 == 0)
{
uint32 x_492; obj* x_493; obj* x_494; obj* x_496; obj* x_497; obj* x_499; obj* x_500; 
x_492 = 0;
x_493 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_494 = lean::box_uint32(x_492);
lean::inc(x_493);
x_496 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_496, 0, x_494);
lean::cnstr_set(x_496, 1, x_13);
lean::cnstr_set(x_496, 2, x_493);
x_497 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_496);
lean::inc(x_493);
x_499 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_493, x_497);
x_500 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_500, 0, x_499);
lean::cnstr_set(x_500, 1, x_8);
return x_500;
}
else
{
uint32 x_501; uint8 x_502; 
x_501 = 1114112;
x_502 = x_487 < x_501;
if (x_502 == 0)
{
uint32 x_503; obj* x_504; obj* x_505; obj* x_507; obj* x_508; obj* x_510; obj* x_511; 
x_503 = 0;
x_504 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_505 = lean::box_uint32(x_503);
lean::inc(x_504);
x_507 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_507, 0, x_505);
lean::cnstr_set(x_507, 1, x_13);
lean::cnstr_set(x_507, 2, x_504);
x_508 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_507);
lean::inc(x_504);
x_510 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_504, x_508);
x_511 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_511, 0, x_510);
lean::cnstr_set(x_511, 1, x_8);
return x_511;
}
else
{
obj* x_512; obj* x_513; obj* x_515; obj* x_516; obj* x_518; obj* x_519; 
x_512 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_513 = lean::box_uint32(x_487);
lean::inc(x_512);
x_515 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_515, 0, x_513);
lean::cnstr_set(x_515, 1, x_13);
lean::cnstr_set(x_515, 2, x_512);
x_516 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_515);
lean::inc(x_512);
x_518 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_512, x_516);
x_519 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_519, 0, x_518);
lean::cnstr_set(x_519, 1, x_8);
return x_519;
}
}
}
else
{
obj* x_520; obj* x_521; obj* x_523; obj* x_524; obj* x_526; obj* x_527; 
x_520 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_521 = lean::box_uint32(x_487);
lean::inc(x_520);
x_523 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_523, 0, x_521);
lean::cnstr_set(x_523, 1, x_13);
lean::cnstr_set(x_523, 2, x_520);
x_524 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_523);
lean::inc(x_520);
x_526 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_520, x_524);
x_527 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_527, 0, x_526);
lean::cnstr_set(x_527, 1, x_8);
return x_527;
}
}
lbl_29:
{
uint32 x_529; uint32 x_530; uint8 x_531; 
lean::dec(x_28);
x_529 = 116;
x_530 = 55296;
x_531 = x_529 < x_530;
if (x_531 == 0)
{
uint32 x_532; uint8 x_533; 
x_532 = 57343;
x_533 = x_532 < x_529;
if (x_533 == 0)
{
uint32 x_534; uint32 x_535; uint8 x_536; 
x_534 = 0;
x_535 = lean::unbox_uint32(x_11);
x_536 = x_535 == x_534;
if (x_536 == 0)
{
obj* x_537; 
x_537 = lean::box(0);
x_24 = x_537;
goto lbl_25;
}
else
{
obj* x_543; 
lean::dec(x_17);
lean::dec(x_11);
lean::dec(x_1);
lean::dec(x_10);
lean::dec(x_0);
x_543 = lean::box(0);
x_26 = x_543;
goto lbl_27;
}
}
else
{
uint32 x_544; uint8 x_545; 
x_544 = 1114112;
x_545 = x_529 < x_544;
if (x_545 == 0)
{
uint32 x_546; uint32 x_547; uint8 x_548; 
x_546 = 0;
x_547 = lean::unbox_uint32(x_11);
x_548 = x_547 == x_546;
if (x_548 == 0)
{
obj* x_549; 
x_549 = lean::box(0);
x_24 = x_549;
goto lbl_25;
}
else
{
obj* x_555; 
lean::dec(x_17);
lean::dec(x_11);
lean::dec(x_1);
lean::dec(x_10);
lean::dec(x_0);
x_555 = lean::box(0);
x_26 = x_555;
goto lbl_27;
}
}
else
{
uint32 x_556; uint8 x_557; 
x_556 = lean::unbox_uint32(x_11);
x_557 = x_556 == x_529;
if (x_557 == 0)
{
obj* x_558; 
x_558 = lean::box(0);
x_24 = x_558;
goto lbl_25;
}
else
{
obj* x_564; 
lean::dec(x_17);
lean::dec(x_11);
lean::dec(x_1);
lean::dec(x_10);
lean::dec(x_0);
x_564 = lean::box(0);
x_26 = x_564;
goto lbl_27;
}
}
}
}
else
{
uint32 x_565; uint8 x_566; 
x_565 = lean::unbox_uint32(x_11);
x_566 = x_565 == x_529;
if (x_566 == 0)
{
obj* x_567; 
x_567 = lean::box(0);
x_24 = x_567;
goto lbl_25;
}
else
{
obj* x_573; 
lean::dec(x_17);
lean::dec(x_11);
lean::dec(x_1);
lean::dec(x_10);
lean::dec(x_0);
x_573 = lean::box(0);
x_26 = x_573;
goto lbl_27;
}
}
}
lbl_31:
{
uint32 x_575; uint32 x_576; uint8 x_577; 
lean::dec(x_30);
x_575 = 10;
x_576 = 55296;
x_577 = x_575 < x_576;
if (x_577 == 0)
{
uint32 x_578; uint8 x_579; 
x_578 = 57343;
x_579 = x_578 < x_575;
if (x_579 == 0)
{
uint32 x_580; obj* x_581; obj* x_582; obj* x_584; obj* x_585; obj* x_587; obj* x_588; 
x_580 = 0;
x_581 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_582 = lean::box_uint32(x_580);
lean::inc(x_581);
x_584 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_584, 0, x_582);
lean::cnstr_set(x_584, 1, x_13);
lean::cnstr_set(x_584, 2, x_581);
x_585 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_584);
lean::inc(x_581);
x_587 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_581, x_585);
x_588 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_588, 0, x_587);
lean::cnstr_set(x_588, 1, x_8);
return x_588;
}
else
{
uint32 x_589; uint8 x_590; 
x_589 = 1114112;
x_590 = x_575 < x_589;
if (x_590 == 0)
{
uint32 x_591; obj* x_592; obj* x_593; obj* x_595; obj* x_596; obj* x_598; obj* x_599; 
x_591 = 0;
x_592 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_593 = lean::box_uint32(x_591);
lean::inc(x_592);
x_595 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_595, 0, x_593);
lean::cnstr_set(x_595, 1, x_13);
lean::cnstr_set(x_595, 2, x_592);
x_596 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_595);
lean::inc(x_592);
x_598 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_592, x_596);
x_599 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_599, 0, x_598);
lean::cnstr_set(x_599, 1, x_8);
return x_599;
}
else
{
obj* x_600; obj* x_601; obj* x_603; obj* x_604; obj* x_606; obj* x_607; 
x_600 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_601 = lean::box_uint32(x_575);
lean::inc(x_600);
x_603 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_603, 0, x_601);
lean::cnstr_set(x_603, 1, x_13);
lean::cnstr_set(x_603, 2, x_600);
x_604 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_603);
lean::inc(x_600);
x_606 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_600, x_604);
x_607 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_607, 0, x_606);
lean::cnstr_set(x_607, 1, x_8);
return x_607;
}
}
}
else
{
obj* x_608; obj* x_609; obj* x_611; obj* x_612; obj* x_614; obj* x_615; 
x_608 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_609 = lean::box_uint32(x_575);
lean::inc(x_608);
x_611 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_611, 0, x_609);
lean::cnstr_set(x_611, 1, x_13);
lean::cnstr_set(x_611, 2, x_608);
x_612 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_611);
lean::inc(x_608);
x_614 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_608, x_612);
x_615 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_615, 0, x_614);
lean::cnstr_set(x_615, 1, x_8);
return x_615;
}
}
lbl_33:
{
uint32 x_617; uint32 x_618; uint8 x_619; 
lean::dec(x_32);
x_617 = 110;
x_618 = 55296;
x_619 = x_617 < x_618;
if (x_619 == 0)
{
uint32 x_620; uint8 x_621; 
x_620 = 57343;
x_621 = x_620 < x_617;
if (x_621 == 0)
{
uint32 x_622; uint32 x_623; uint8 x_624; 
x_622 = 0;
x_623 = lean::unbox_uint32(x_11);
x_624 = x_623 == x_622;
if (x_624 == 0)
{
obj* x_625; 
x_625 = lean::box(0);
x_28 = x_625;
goto lbl_29;
}
else
{
obj* x_631; 
lean::dec(x_17);
lean::dec(x_11);
lean::dec(x_1);
lean::dec(x_10);
lean::dec(x_0);
x_631 = lean::box(0);
x_30 = x_631;
goto lbl_31;
}
}
else
{
uint32 x_632; uint8 x_633; 
x_632 = 1114112;
x_633 = x_617 < x_632;
if (x_633 == 0)
{
uint32 x_634; uint32 x_635; uint8 x_636; 
x_634 = 0;
x_635 = lean::unbox_uint32(x_11);
x_636 = x_635 == x_634;
if (x_636 == 0)
{
obj* x_637; 
x_637 = lean::box(0);
x_28 = x_637;
goto lbl_29;
}
else
{
obj* x_643; 
lean::dec(x_17);
lean::dec(x_11);
lean::dec(x_1);
lean::dec(x_10);
lean::dec(x_0);
x_643 = lean::box(0);
x_30 = x_643;
goto lbl_31;
}
}
else
{
uint32 x_644; uint8 x_645; 
x_644 = lean::unbox_uint32(x_11);
x_645 = x_644 == x_617;
if (x_645 == 0)
{
obj* x_646; 
x_646 = lean::box(0);
x_28 = x_646;
goto lbl_29;
}
else
{
obj* x_652; 
lean::dec(x_17);
lean::dec(x_11);
lean::dec(x_1);
lean::dec(x_10);
lean::dec(x_0);
x_652 = lean::box(0);
x_30 = x_652;
goto lbl_31;
}
}
}
}
else
{
uint32 x_653; uint8 x_654; 
x_653 = lean::unbox_uint32(x_11);
x_654 = x_653 == x_617;
if (x_654 == 0)
{
obj* x_655; 
x_655 = lean::box(0);
x_28 = x_655;
goto lbl_29;
}
else
{
obj* x_661; 
lean::dec(x_17);
lean::dec(x_11);
lean::dec(x_1);
lean::dec(x_10);
lean::dec(x_0);
x_661 = lean::box(0);
x_30 = x_661;
goto lbl_31;
}
}
}
lbl_35:
{
uint32 x_663; uint32 x_664; uint8 x_665; uint32 x_666; 
lean::dec(x_34);
x_663 = 39;
x_664 = 55296;
x_665 = x_663 < x_664;
if (x_665 == 0)
{
uint32 x_668; uint8 x_669; 
x_668 = 57343;
x_669 = x_668 < x_663;
if (x_669 == 0)
{
uint32 x_670; 
x_670 = 0;
x_666 = x_670;
goto lbl_667;
}
else
{
uint32 x_671; uint8 x_672; 
x_671 = 1114112;
x_672 = x_663 < x_671;
if (x_672 == 0)
{
uint32 x_673; 
x_673 = 0;
x_666 = x_673;
goto lbl_667;
}
else
{
x_666 = x_663;
goto lbl_667;
}
}
}
else
{
x_666 = x_663;
goto lbl_667;
}
lbl_667:
{
uint32 x_674; uint8 x_675; 
x_674 = lean::unbox_uint32(x_11);
x_675 = x_674 == x_666;
if (x_675 == 0)
{
obj* x_676; 
x_676 = lean::box(0);
x_32 = x_676;
goto lbl_33;
}
else
{
obj* x_682; obj* x_683; obj* x_685; obj* x_686; obj* x_688; obj* x_689; 
lean::dec(x_17);
lean::dec(x_11);
lean::dec(x_1);
lean::dec(x_10);
lean::dec(x_0);
x_682 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_683 = lean::box_uint32(x_666);
lean::inc(x_682);
x_685 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_685, 0, x_683);
lean::cnstr_set(x_685, 1, x_13);
lean::cnstr_set(x_685, 2, x_682);
x_686 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_685);
lean::inc(x_682);
x_688 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_682, x_686);
x_689 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_689, 0, x_688);
lean::cnstr_set(x_689, 1, x_8);
return x_689;
}
}
}
lbl_37:
{
uint32 x_691; uint32 x_692; uint8 x_693; uint32 x_694; 
lean::dec(x_36);
x_691 = 34;
x_692 = 55296;
x_693 = x_691 < x_692;
if (x_693 == 0)
{
uint32 x_696; uint8 x_697; 
x_696 = 57343;
x_697 = x_696 < x_691;
if (x_697 == 0)
{
uint32 x_698; 
x_698 = 0;
x_694 = x_698;
goto lbl_695;
}
else
{
uint32 x_699; uint8 x_700; 
x_699 = 1114112;
x_700 = x_691 < x_699;
if (x_700 == 0)
{
uint32 x_701; 
x_701 = 0;
x_694 = x_701;
goto lbl_695;
}
else
{
x_694 = x_691;
goto lbl_695;
}
}
}
else
{
x_694 = x_691;
goto lbl_695;
}
lbl_695:
{
uint32 x_702; uint8 x_703; 
x_702 = lean::unbox_uint32(x_11);
x_703 = x_702 == x_694;
if (x_703 == 0)
{
obj* x_704; 
x_704 = lean::box(0);
x_34 = x_704;
goto lbl_35;
}
else
{
obj* x_710; obj* x_711; obj* x_713; obj* x_714; obj* x_716; obj* x_717; 
lean::dec(x_17);
lean::dec(x_11);
lean::dec(x_1);
lean::dec(x_10);
lean::dec(x_0);
x_710 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_711 = lean::box_uint32(x_694);
lean::inc(x_710);
x_713 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_713, 0, x_711);
lean::cnstr_set(x_713, 1, x_13);
lean::cnstr_set(x_713, 2, x_710);
x_714 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_713);
lean::inc(x_710);
x_716 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_710, x_714);
x_717 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_717, 0, x_716);
lean::cnstr_set(x_717, 1, x_8);
return x_717;
}
}
}
lbl_42:
{
uint32 x_718; uint8 x_719; 
x_718 = lean::unbox_uint32(x_11);
x_719 = x_718 == x_41;
if (x_719 == 0)
{
obj* x_720; 
x_720 = lean::box(0);
x_36 = x_720;
goto lbl_37;
}
else
{
obj* x_726; obj* x_727; obj* x_729; obj* x_730; obj* x_732; obj* x_733; 
lean::dec(x_17);
lean::dec(x_11);
lean::dec(x_1);
lean::dec(x_10);
lean::dec(x_0);
x_726 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_727 = lean::box_uint32(x_41);
lean::inc(x_726);
x_729 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_729, 0, x_727);
lean::cnstr_set(x_729, 1, x_13);
lean::cnstr_set(x_729, 2, x_726);
x_730 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_729);
lean::inc(x_726);
x_732 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_726, x_730);
x_733 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_733, 0, x_732);
lean::cnstr_set(x_733, 1, x_8);
return x_733;
}
}
}
else
{
obj* x_736; uint8 x_738; obj* x_739; obj* x_740; obj* x_741; obj* x_742; obj* x_744; obj* x_745; 
lean::dec(x_1);
lean::dec(x_0);
x_736 = lean::cnstr_get(x_6, 0);
lean::inc(x_736);
x_738 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*1);
if (lean::is_shared(x_6)) {
 lean::dec(x_6);
 x_739 = lean::box(0);
} else {
 lean::cnstr_release(x_6, 0);
 x_739 = x_6;
}
if (lean::is_scalar(x_739)) {
 x_740 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_740 = x_739;
}
lean::cnstr_set(x_740, 0, x_736);
lean::cnstr_set_scalar(x_740, sizeof(void*)*1, x_738);
x_741 = x_740;
x_742 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_742);
x_744 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_742, x_741);
if (lean::is_scalar(x_10)) {
 x_745 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_745 = x_10;
}
lean::cnstr_set(x_745, 0, x_744);
lean::cnstr_set(x_745, 1, x_8);
return x_745;
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
obj* x_15; obj* x_17; obj* x_19; obj* x_21; obj* x_22; obj* x_23; obj* x_26; uint32 x_28; uint32 x_29; uint8 x_30; uint32 x_31; 
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
x_28 = 92;
x_29 = 55296;
x_30 = x_28 < x_29;
if (x_30 == 0)
{
uint32 x_33; uint8 x_34; 
x_33 = 57343;
x_34 = x_33 < x_28;
if (x_34 == 0)
{
uint32 x_35; 
x_35 = 0;
x_31 = x_35;
goto lbl_32;
}
else
{
uint32 x_36; uint8 x_37; 
x_36 = 1114112;
x_37 = x_28 < x_36;
if (x_37 == 0)
{
uint32 x_38; 
x_38 = 0;
x_31 = x_38;
goto lbl_32;
}
else
{
x_31 = x_28;
goto lbl_32;
}
}
}
else
{
x_31 = x_28;
goto lbl_32;
}
lbl_27:
{
uint32 x_40; uint32 x_41; uint8 x_42; uint32 x_43; 
lean::dec(x_26);
x_40 = 34;
x_41 = 55296;
x_42 = x_40 < x_41;
if (x_42 == 0)
{
uint32 x_45; uint8 x_46; 
x_45 = 57343;
x_46 = x_45 < x_40;
if (x_46 == 0)
{
uint32 x_47; 
x_47 = 0;
x_43 = x_47;
goto lbl_44;
}
else
{
uint32 x_48; uint8 x_49; 
x_48 = 1114112;
x_49 = x_40 < x_48;
if (x_49 == 0)
{
uint32 x_50; 
x_50 = 0;
x_43 = x_50;
goto lbl_44;
}
else
{
x_43 = x_40;
goto lbl_44;
}
}
}
else
{
x_43 = x_40;
goto lbl_44;
}
lbl_44:
{
uint32 x_51; uint8 x_53; 
x_51 = lean::unbox_uint32(x_15);
lean::dec(x_15);
x_53 = x_51 == x_43;
if (x_53 == 0)
{
obj* x_55; obj* x_56; obj* x_57; obj* x_59; obj* x_62; obj* x_63; 
lean::dec(x_21);
x_55 = lean::string_push(x_1, x_51);
x_56 = l_lean_parser_parse__string__literal__aux___main___at_lean_parser_string__lit_x_27___spec__2(x_23, x_55, x_2, x_17, x_12);
x_57 = lean::cnstr_get(x_56, 0);
lean::inc(x_57);
x_59 = lean::cnstr_get(x_56, 1);
lean::inc(x_59);
lean::dec(x_56);
x_62 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_19, x_57);
if (lean::is_scalar(x_14)) {
 x_63 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_63 = x_14;
}
lean::cnstr_set(x_63, 0, x_62);
lean::cnstr_set(x_63, 1, x_59);
return x_63;
}
else
{
obj* x_66; obj* x_68; obj* x_69; obj* x_70; 
lean::dec(x_2);
lean::dec(x_23);
x_66 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_66);
if (lean::is_scalar(x_21)) {
 x_68 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_68 = x_21;
}
lean::cnstr_set(x_68, 0, x_1);
lean::cnstr_set(x_68, 1, x_17);
lean::cnstr_set(x_68, 2, x_66);
x_69 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_19, x_68);
if (lean::is_scalar(x_14)) {
 x_70 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_70 = x_14;
}
lean::cnstr_set(x_70, 0, x_69);
lean::cnstr_set(x_70, 1, x_12);
return x_70;
}
}
}
lbl_32:
{
uint32 x_71; uint8 x_72; 
x_71 = lean::unbox_uint32(x_15);
x_72 = x_71 == x_31;
if (x_72 == 0)
{
obj* x_73; 
x_73 = lean::box(0);
x_26 = x_73;
goto lbl_27;
}
else
{
obj* x_78; obj* x_79; obj* x_81; obj* x_83; 
lean::dec(x_21);
lean::dec(x_15);
lean::dec(x_14);
lean::inc(x_2);
x_78 = l_lean_parser_parse__quoted__char___at_lean_parser_string__lit_x_27___spec__3(x_2, x_17, x_12);
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
if (lean::obj_tag(x_79) == 0)
{
obj* x_84; obj* x_86; obj* x_88; uint32 x_91; obj* x_93; obj* x_94; obj* x_95; obj* x_97; obj* x_100; obj* x_101; obj* x_102; 
x_84 = lean::cnstr_get(x_79, 0);
lean::inc(x_84);
x_86 = lean::cnstr_get(x_79, 1);
lean::inc(x_86);
x_88 = lean::cnstr_get(x_79, 2);
lean::inc(x_88);
lean::dec(x_79);
x_91 = lean::unbox_uint32(x_84);
lean::dec(x_84);
x_93 = lean::string_push(x_1, x_91);
x_94 = l_lean_parser_parse__string__literal__aux___main___at_lean_parser_string__lit_x_27___spec__2(x_23, x_93, x_2, x_86, x_81);
x_95 = lean::cnstr_get(x_94, 0);
lean::inc(x_95);
x_97 = lean::cnstr_get(x_94, 1);
lean::inc(x_97);
lean::dec(x_94);
x_100 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_88, x_95);
x_101 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_19, x_100);
if (lean::is_scalar(x_83)) {
 x_102 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_102 = x_83;
}
lean::cnstr_set(x_102, 0, x_101);
lean::cnstr_set(x_102, 1, x_97);
return x_102;
}
else
{
obj* x_106; uint8 x_108; obj* x_109; obj* x_110; obj* x_111; obj* x_112; obj* x_113; 
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_23);
x_106 = lean::cnstr_get(x_79, 0);
lean::inc(x_106);
x_108 = lean::cnstr_get_scalar<uint8>(x_79, sizeof(void*)*1);
if (lean::is_shared(x_79)) {
 lean::dec(x_79);
 x_109 = lean::box(0);
} else {
 lean::cnstr_release(x_79, 0);
 x_109 = x_79;
}
if (lean::is_scalar(x_109)) {
 x_110 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_110 = x_109;
}
lean::cnstr_set(x_110, 0, x_106);
lean::cnstr_set_scalar(x_110, sizeof(void*)*1, x_108);
x_111 = x_110;
x_112 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_19, x_111);
if (lean::is_scalar(x_83)) {
 x_113 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_113 = x_83;
}
lean::cnstr_set(x_113, 0, x_112);
lean::cnstr_set(x_113, 1, x_81);
return x_113;
}
}
}
}
else
{
obj* x_117; uint8 x_119; obj* x_120; obj* x_121; obj* x_122; obj* x_123; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_117 = lean::cnstr_get(x_10, 0);
lean::inc(x_117);
x_119 = lean::cnstr_get_scalar<uint8>(x_10, sizeof(void*)*1);
if (lean::is_shared(x_10)) {
 lean::dec(x_10);
 x_120 = lean::box(0);
} else {
 lean::cnstr_release(x_10, 0);
 x_120 = x_10;
}
if (lean::is_scalar(x_120)) {
 x_121 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_121 = x_120;
}
lean::cnstr_set(x_121, 0, x_117);
lean::cnstr_set_scalar(x_121, sizeof(void*)*1, x_119);
x_122 = x_121;
if (lean::is_scalar(x_14)) {
 x_123 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_123 = x_14;
}
lean::cnstr_set(x_123, 0, x_122);
lean::cnstr_set(x_123, 1, x_12);
return x_123;
}
}
else
{
uint32 x_125; uint32 x_126; uint8 x_127; 
lean::dec(x_0);
x_125 = 34;
x_126 = 55296;
x_127 = x_125 < x_126;
if (x_127 == 0)
{
uint32 x_128; uint8 x_129; 
x_128 = 57343;
x_129 = x_128 < x_125;
if (x_129 == 0)
{
uint32 x_130; obj* x_131; obj* x_132; obj* x_134; obj* x_136; 
x_130 = 0;
x_131 = l_lean_parser_monad__parsec_ch___at___private_init_lean_parser_token_4__ident_x_27___spec__11(x_130, x_2, x_3, x_4);
x_132 = lean::cnstr_get(x_131, 0);
lean::inc(x_132);
x_134 = lean::cnstr_get(x_131, 1);
lean::inc(x_134);
if (lean::is_shared(x_131)) {
 lean::dec(x_131);
 x_136 = lean::box(0);
} else {
 lean::cnstr_release(x_131, 0);
 lean::cnstr_release(x_131, 1);
 x_136 = x_131;
}
if (lean::obj_tag(x_132) == 0)
{
obj* x_137; obj* x_139; obj* x_141; obj* x_142; obj* x_144; obj* x_145; obj* x_146; 
x_137 = lean::cnstr_get(x_132, 1);
lean::inc(x_137);
x_139 = lean::cnstr_get(x_132, 2);
lean::inc(x_139);
if (lean::is_shared(x_132)) {
 lean::dec(x_132);
 x_141 = lean::box(0);
} else {
 lean::cnstr_release(x_132, 0);
 lean::cnstr_release(x_132, 1);
 lean::cnstr_release(x_132, 2);
 x_141 = x_132;
}
x_142 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_142);
if (lean::is_scalar(x_141)) {
 x_144 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_144 = x_141;
}
lean::cnstr_set(x_144, 0, x_1);
lean::cnstr_set(x_144, 1, x_137);
lean::cnstr_set(x_144, 2, x_142);
x_145 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_139, x_144);
if (lean::is_scalar(x_136)) {
 x_146 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_146 = x_136;
}
lean::cnstr_set(x_146, 0, x_145);
lean::cnstr_set(x_146, 1, x_134);
return x_146;
}
else
{
obj* x_148; uint8 x_150; obj* x_151; obj* x_152; obj* x_153; obj* x_154; 
lean::dec(x_1);
x_148 = lean::cnstr_get(x_132, 0);
lean::inc(x_148);
x_150 = lean::cnstr_get_scalar<uint8>(x_132, sizeof(void*)*1);
if (lean::is_shared(x_132)) {
 lean::dec(x_132);
 x_151 = lean::box(0);
} else {
 lean::cnstr_release(x_132, 0);
 x_151 = x_132;
}
if (lean::is_scalar(x_151)) {
 x_152 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_152 = x_151;
}
lean::cnstr_set(x_152, 0, x_148);
lean::cnstr_set_scalar(x_152, sizeof(void*)*1, x_150);
x_153 = x_152;
if (lean::is_scalar(x_136)) {
 x_154 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_154 = x_136;
}
lean::cnstr_set(x_154, 0, x_153);
lean::cnstr_set(x_154, 1, x_134);
return x_154;
}
}
else
{
uint32 x_155; uint8 x_156; 
x_155 = 1114112;
x_156 = x_125 < x_155;
if (x_156 == 0)
{
uint32 x_157; obj* x_158; obj* x_159; obj* x_161; obj* x_163; 
x_157 = 0;
x_158 = l_lean_parser_monad__parsec_ch___at___private_init_lean_parser_token_4__ident_x_27___spec__11(x_157, x_2, x_3, x_4);
x_159 = lean::cnstr_get(x_158, 0);
lean::inc(x_159);
x_161 = lean::cnstr_get(x_158, 1);
lean::inc(x_161);
if (lean::is_shared(x_158)) {
 lean::dec(x_158);
 x_163 = lean::box(0);
} else {
 lean::cnstr_release(x_158, 0);
 lean::cnstr_release(x_158, 1);
 x_163 = x_158;
}
if (lean::obj_tag(x_159) == 0)
{
obj* x_164; obj* x_166; obj* x_168; obj* x_169; obj* x_171; obj* x_172; obj* x_173; 
x_164 = lean::cnstr_get(x_159, 1);
lean::inc(x_164);
x_166 = lean::cnstr_get(x_159, 2);
lean::inc(x_166);
if (lean::is_shared(x_159)) {
 lean::dec(x_159);
 x_168 = lean::box(0);
} else {
 lean::cnstr_release(x_159, 0);
 lean::cnstr_release(x_159, 1);
 lean::cnstr_release(x_159, 2);
 x_168 = x_159;
}
x_169 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_169);
if (lean::is_scalar(x_168)) {
 x_171 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_171 = x_168;
}
lean::cnstr_set(x_171, 0, x_1);
lean::cnstr_set(x_171, 1, x_164);
lean::cnstr_set(x_171, 2, x_169);
x_172 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_166, x_171);
if (lean::is_scalar(x_163)) {
 x_173 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_173 = x_163;
}
lean::cnstr_set(x_173, 0, x_172);
lean::cnstr_set(x_173, 1, x_161);
return x_173;
}
else
{
obj* x_175; uint8 x_177; obj* x_178; obj* x_179; obj* x_180; obj* x_181; 
lean::dec(x_1);
x_175 = lean::cnstr_get(x_159, 0);
lean::inc(x_175);
x_177 = lean::cnstr_get_scalar<uint8>(x_159, sizeof(void*)*1);
if (lean::is_shared(x_159)) {
 lean::dec(x_159);
 x_178 = lean::box(0);
} else {
 lean::cnstr_release(x_159, 0);
 x_178 = x_159;
}
if (lean::is_scalar(x_178)) {
 x_179 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_179 = x_178;
}
lean::cnstr_set(x_179, 0, x_175);
lean::cnstr_set_scalar(x_179, sizeof(void*)*1, x_177);
x_180 = x_179;
if (lean::is_scalar(x_163)) {
 x_181 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_181 = x_163;
}
lean::cnstr_set(x_181, 0, x_180);
lean::cnstr_set(x_181, 1, x_161);
return x_181;
}
}
else
{
obj* x_182; obj* x_183; obj* x_185; obj* x_187; 
x_182 = l_lean_parser_monad__parsec_ch___at___private_init_lean_parser_token_4__ident_x_27___spec__11(x_125, x_2, x_3, x_4);
x_183 = lean::cnstr_get(x_182, 0);
lean::inc(x_183);
x_185 = lean::cnstr_get(x_182, 1);
lean::inc(x_185);
if (lean::is_shared(x_182)) {
 lean::dec(x_182);
 x_187 = lean::box(0);
} else {
 lean::cnstr_release(x_182, 0);
 lean::cnstr_release(x_182, 1);
 x_187 = x_182;
}
if (lean::obj_tag(x_183) == 0)
{
obj* x_188; obj* x_190; obj* x_192; obj* x_193; obj* x_195; obj* x_196; obj* x_197; 
x_188 = lean::cnstr_get(x_183, 1);
lean::inc(x_188);
x_190 = lean::cnstr_get(x_183, 2);
lean::inc(x_190);
if (lean::is_shared(x_183)) {
 lean::dec(x_183);
 x_192 = lean::box(0);
} else {
 lean::cnstr_release(x_183, 0);
 lean::cnstr_release(x_183, 1);
 lean::cnstr_release(x_183, 2);
 x_192 = x_183;
}
x_193 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_193);
if (lean::is_scalar(x_192)) {
 x_195 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_195 = x_192;
}
lean::cnstr_set(x_195, 0, x_1);
lean::cnstr_set(x_195, 1, x_188);
lean::cnstr_set(x_195, 2, x_193);
x_196 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_190, x_195);
if (lean::is_scalar(x_187)) {
 x_197 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_197 = x_187;
}
lean::cnstr_set(x_197, 0, x_196);
lean::cnstr_set(x_197, 1, x_185);
return x_197;
}
else
{
obj* x_199; uint8 x_201; obj* x_202; obj* x_203; obj* x_204; obj* x_205; 
lean::dec(x_1);
x_199 = lean::cnstr_get(x_183, 0);
lean::inc(x_199);
x_201 = lean::cnstr_get_scalar<uint8>(x_183, sizeof(void*)*1);
if (lean::is_shared(x_183)) {
 lean::dec(x_183);
 x_202 = lean::box(0);
} else {
 lean::cnstr_release(x_183, 0);
 x_202 = x_183;
}
if (lean::is_scalar(x_202)) {
 x_203 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_203 = x_202;
}
lean::cnstr_set(x_203, 0, x_199);
lean::cnstr_set_scalar(x_203, sizeof(void*)*1, x_201);
x_204 = x_203;
if (lean::is_scalar(x_187)) {
 x_205 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_205 = x_187;
}
lean::cnstr_set(x_205, 0, x_204);
lean::cnstr_set(x_205, 1, x_185);
return x_205;
}
}
}
}
else
{
obj* x_206; obj* x_207; obj* x_209; obj* x_211; 
x_206 = l_lean_parser_monad__parsec_ch___at___private_init_lean_parser_token_4__ident_x_27___spec__11(x_125, x_2, x_3, x_4);
x_207 = lean::cnstr_get(x_206, 0);
lean::inc(x_207);
x_209 = lean::cnstr_get(x_206, 1);
lean::inc(x_209);
if (lean::is_shared(x_206)) {
 lean::dec(x_206);
 x_211 = lean::box(0);
} else {
 lean::cnstr_release(x_206, 0);
 lean::cnstr_release(x_206, 1);
 x_211 = x_206;
}
if (lean::obj_tag(x_207) == 0)
{
obj* x_212; obj* x_214; obj* x_216; obj* x_217; obj* x_219; obj* x_220; obj* x_221; 
x_212 = lean::cnstr_get(x_207, 1);
lean::inc(x_212);
x_214 = lean::cnstr_get(x_207, 2);
lean::inc(x_214);
if (lean::is_shared(x_207)) {
 lean::dec(x_207);
 x_216 = lean::box(0);
} else {
 lean::cnstr_release(x_207, 0);
 lean::cnstr_release(x_207, 1);
 lean::cnstr_release(x_207, 2);
 x_216 = x_207;
}
x_217 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_217);
if (lean::is_scalar(x_216)) {
 x_219 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_219 = x_216;
}
lean::cnstr_set(x_219, 0, x_1);
lean::cnstr_set(x_219, 1, x_212);
lean::cnstr_set(x_219, 2, x_217);
x_220 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_214, x_219);
if (lean::is_scalar(x_211)) {
 x_221 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_221 = x_211;
}
lean::cnstr_set(x_221, 0, x_220);
lean::cnstr_set(x_221, 1, x_209);
return x_221;
}
else
{
obj* x_223; uint8 x_225; obj* x_226; obj* x_227; obj* x_228; obj* x_229; 
lean::dec(x_1);
x_223 = lean::cnstr_get(x_207, 0);
lean::inc(x_223);
x_225 = lean::cnstr_get_scalar<uint8>(x_207, sizeof(void*)*1);
if (lean::is_shared(x_207)) {
 lean::dec(x_207);
 x_226 = lean::box(0);
} else {
 lean::cnstr_release(x_207, 0);
 x_226 = x_207;
}
if (lean::is_scalar(x_226)) {
 x_227 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_227 = x_226;
}
lean::cnstr_set(x_227, 0, x_223);
lean::cnstr_set_scalar(x_227, sizeof(void*)*1, x_225);
x_228 = x_227;
if (lean::is_scalar(x_211)) {
 x_229 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_229 = x_211;
}
lean::cnstr_set(x_229, 0, x_228);
lean::cnstr_set(x_229, 1, x_209);
return x_229;
}
}
}
}
}
obj* l_lean_parser_parse__string__literal___at_lean_parser_string__lit_x_27___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint32 x_3; uint32 x_4; uint8 x_5; 
x_3 = 34;
x_4 = 55296;
x_5 = x_3 < x_4;
if (x_5 == 0)
{
uint32 x_6; uint8 x_7; 
x_6 = 57343;
x_7 = x_6 < x_3;
if (x_7 == 0)
{
uint32 x_8; obj* x_10; obj* x_11; obj* x_13; obj* x_15; 
x_8 = 0;
lean::inc(x_0);
x_10 = l_lean_parser_monad__parsec_ch___at___private_init_lean_parser_token_4__ident_x_27___spec__11(x_8, x_0, x_1, x_2);
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
obj* x_16; obj* x_18; obj* x_21; obj* x_22; obj* x_24; obj* x_25; obj* x_27; obj* x_30; obj* x_32; obj* x_33; obj* x_34; 
x_16 = lean::cnstr_get(x_11, 1);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_11, 2);
lean::inc(x_18);
lean::dec(x_11);
x_21 = lean::string_iterator_remaining(x_16);
x_22 = l_string_join___closed__1;
lean::inc(x_22);
x_24 = l_lean_parser_parse__string__literal__aux___main___at_lean_parser_string__lit_x_27___spec__2(x_21, x_22, x_0, x_16, x_13);
x_25 = lean::cnstr_get(x_24, 0);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_24, 1);
lean::inc(x_27);
lean::dec(x_24);
x_30 = l_lean_parser_finish__comment__block___closed__2;
lean::inc(x_30);
x_32 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_30, x_25);
x_33 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_18, x_32);
if (lean::is_scalar(x_15)) {
 x_34 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_34 = x_15;
}
lean::cnstr_set(x_34, 0, x_33);
lean::cnstr_set(x_34, 1, x_27);
return x_34;
}
else
{
obj* x_36; uint8 x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; 
lean::dec(x_0);
x_36 = lean::cnstr_get(x_11, 0);
lean::inc(x_36);
x_38 = lean::cnstr_get_scalar<uint8>(x_11, sizeof(void*)*1);
if (lean::is_shared(x_11)) {
 lean::dec(x_11);
 x_39 = lean::box(0);
} else {
 lean::cnstr_release(x_11, 0);
 x_39 = x_11;
}
if (lean::is_scalar(x_39)) {
 x_40 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_40 = x_39;
}
lean::cnstr_set(x_40, 0, x_36);
lean::cnstr_set_scalar(x_40, sizeof(void*)*1, x_38);
x_41 = x_40;
if (lean::is_scalar(x_15)) {
 x_42 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_42 = x_15;
}
lean::cnstr_set(x_42, 0, x_41);
lean::cnstr_set(x_42, 1, x_13);
return x_42;
}
}
else
{
uint32 x_43; uint8 x_44; 
x_43 = 1114112;
x_44 = x_3 < x_43;
if (x_44 == 0)
{
uint32 x_45; obj* x_47; obj* x_48; obj* x_50; obj* x_52; 
x_45 = 0;
lean::inc(x_0);
x_47 = l_lean_parser_monad__parsec_ch___at___private_init_lean_parser_token_4__ident_x_27___spec__11(x_45, x_0, x_1, x_2);
x_48 = lean::cnstr_get(x_47, 0);
lean::inc(x_48);
x_50 = lean::cnstr_get(x_47, 1);
lean::inc(x_50);
if (lean::is_shared(x_47)) {
 lean::dec(x_47);
 x_52 = lean::box(0);
} else {
 lean::cnstr_release(x_47, 0);
 lean::cnstr_release(x_47, 1);
 x_52 = x_47;
}
if (lean::obj_tag(x_48) == 0)
{
obj* x_53; obj* x_55; obj* x_58; obj* x_59; obj* x_61; obj* x_62; obj* x_64; obj* x_67; obj* x_69; obj* x_70; obj* x_71; 
x_53 = lean::cnstr_get(x_48, 1);
lean::inc(x_53);
x_55 = lean::cnstr_get(x_48, 2);
lean::inc(x_55);
lean::dec(x_48);
x_58 = lean::string_iterator_remaining(x_53);
x_59 = l_string_join___closed__1;
lean::inc(x_59);
x_61 = l_lean_parser_parse__string__literal__aux___main___at_lean_parser_string__lit_x_27___spec__2(x_58, x_59, x_0, x_53, x_50);
x_62 = lean::cnstr_get(x_61, 0);
lean::inc(x_62);
x_64 = lean::cnstr_get(x_61, 1);
lean::inc(x_64);
lean::dec(x_61);
x_67 = l_lean_parser_finish__comment__block___closed__2;
lean::inc(x_67);
x_69 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_67, x_62);
x_70 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_55, x_69);
if (lean::is_scalar(x_52)) {
 x_71 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_71 = x_52;
}
lean::cnstr_set(x_71, 0, x_70);
lean::cnstr_set(x_71, 1, x_64);
return x_71;
}
else
{
obj* x_73; uint8 x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; 
lean::dec(x_0);
x_73 = lean::cnstr_get(x_48, 0);
lean::inc(x_73);
x_75 = lean::cnstr_get_scalar<uint8>(x_48, sizeof(void*)*1);
if (lean::is_shared(x_48)) {
 lean::dec(x_48);
 x_76 = lean::box(0);
} else {
 lean::cnstr_release(x_48, 0);
 x_76 = x_48;
}
if (lean::is_scalar(x_76)) {
 x_77 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_77 = x_76;
}
lean::cnstr_set(x_77, 0, x_73);
lean::cnstr_set_scalar(x_77, sizeof(void*)*1, x_75);
x_78 = x_77;
if (lean::is_scalar(x_52)) {
 x_79 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_79 = x_52;
}
lean::cnstr_set(x_79, 0, x_78);
lean::cnstr_set(x_79, 1, x_50);
return x_79;
}
}
else
{
obj* x_81; obj* x_82; obj* x_84; obj* x_86; 
lean::inc(x_0);
x_81 = l_lean_parser_monad__parsec_ch___at___private_init_lean_parser_token_4__ident_x_27___spec__11(x_3, x_0, x_1, x_2);
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
if (lean::obj_tag(x_82) == 0)
{
obj* x_87; obj* x_89; obj* x_92; obj* x_93; obj* x_95; obj* x_96; obj* x_98; obj* x_101; obj* x_103; obj* x_104; obj* x_105; 
x_87 = lean::cnstr_get(x_82, 1);
lean::inc(x_87);
x_89 = lean::cnstr_get(x_82, 2);
lean::inc(x_89);
lean::dec(x_82);
x_92 = lean::string_iterator_remaining(x_87);
x_93 = l_string_join___closed__1;
lean::inc(x_93);
x_95 = l_lean_parser_parse__string__literal__aux___main___at_lean_parser_string__lit_x_27___spec__2(x_92, x_93, x_0, x_87, x_84);
x_96 = lean::cnstr_get(x_95, 0);
lean::inc(x_96);
x_98 = lean::cnstr_get(x_95, 1);
lean::inc(x_98);
lean::dec(x_95);
x_101 = l_lean_parser_finish__comment__block___closed__2;
lean::inc(x_101);
x_103 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_101, x_96);
x_104 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_89, x_103);
if (lean::is_scalar(x_86)) {
 x_105 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_105 = x_86;
}
lean::cnstr_set(x_105, 0, x_104);
lean::cnstr_set(x_105, 1, x_98);
return x_105;
}
else
{
obj* x_107; uint8 x_109; obj* x_110; obj* x_111; obj* x_112; obj* x_113; 
lean::dec(x_0);
x_107 = lean::cnstr_get(x_82, 0);
lean::inc(x_107);
x_109 = lean::cnstr_get_scalar<uint8>(x_82, sizeof(void*)*1);
if (lean::is_shared(x_82)) {
 lean::dec(x_82);
 x_110 = lean::box(0);
} else {
 lean::cnstr_release(x_82, 0);
 x_110 = x_82;
}
if (lean::is_scalar(x_110)) {
 x_111 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_111 = x_110;
}
lean::cnstr_set(x_111, 0, x_107);
lean::cnstr_set_scalar(x_111, sizeof(void*)*1, x_109);
x_112 = x_111;
if (lean::is_scalar(x_86)) {
 x_113 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_113 = x_86;
}
lean::cnstr_set(x_113, 0, x_112);
lean::cnstr_set(x_113, 1, x_84);
return x_113;
}
}
}
}
else
{
obj* x_115; obj* x_116; obj* x_118; obj* x_120; 
lean::inc(x_0);
x_115 = l_lean_parser_monad__parsec_ch___at___private_init_lean_parser_token_4__ident_x_27___spec__11(x_3, x_0, x_1, x_2);
x_116 = lean::cnstr_get(x_115, 0);
lean::inc(x_116);
x_118 = lean::cnstr_get(x_115, 1);
lean::inc(x_118);
if (lean::is_shared(x_115)) {
 lean::dec(x_115);
 x_120 = lean::box(0);
} else {
 lean::cnstr_release(x_115, 0);
 lean::cnstr_release(x_115, 1);
 x_120 = x_115;
}
if (lean::obj_tag(x_116) == 0)
{
obj* x_121; obj* x_123; obj* x_126; obj* x_127; obj* x_129; obj* x_130; obj* x_132; obj* x_135; obj* x_137; obj* x_138; obj* x_139; 
x_121 = lean::cnstr_get(x_116, 1);
lean::inc(x_121);
x_123 = lean::cnstr_get(x_116, 2);
lean::inc(x_123);
lean::dec(x_116);
x_126 = lean::string_iterator_remaining(x_121);
x_127 = l_string_join___closed__1;
lean::inc(x_127);
x_129 = l_lean_parser_parse__string__literal__aux___main___at_lean_parser_string__lit_x_27___spec__2(x_126, x_127, x_0, x_121, x_118);
x_130 = lean::cnstr_get(x_129, 0);
lean::inc(x_130);
x_132 = lean::cnstr_get(x_129, 1);
lean::inc(x_132);
lean::dec(x_129);
x_135 = l_lean_parser_finish__comment__block___closed__2;
lean::inc(x_135);
x_137 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_135, x_130);
x_138 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_123, x_137);
if (lean::is_scalar(x_120)) {
 x_139 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_139 = x_120;
}
lean::cnstr_set(x_139, 0, x_138);
lean::cnstr_set(x_139, 1, x_132);
return x_139;
}
else
{
obj* x_141; uint8 x_143; obj* x_144; obj* x_145; obj* x_146; obj* x_147; 
lean::dec(x_0);
x_141 = lean::cnstr_get(x_116, 0);
lean::inc(x_141);
x_143 = lean::cnstr_get_scalar<uint8>(x_116, sizeof(void*)*1);
if (lean::is_shared(x_116)) {
 lean::dec(x_116);
 x_144 = lean::box(0);
} else {
 lean::cnstr_release(x_116, 0);
 x_144 = x_116;
}
if (lean::is_scalar(x_144)) {
 x_145 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_145 = x_144;
}
lean::cnstr_set(x_145, 0, x_141);
lean::cnstr_set_scalar(x_145, sizeof(void*)*1, x_143);
x_146 = x_145;
if (lean::is_scalar(x_120)) {
 x_147 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_147 = x_120;
}
lean::cnstr_set(x_147, 0, x_146);
lean::cnstr_set(x_147, 1, x_118);
return x_147;
}
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
uint32 x_29; obj* x_31; obj* x_32; obj* x_34; obj* x_37; 
lean::dec(x_23);
x_29 = l_lean_id__begin__escape;
lean::inc(x_1);
x_31 = l_lean_parser_monad__parsec_ch___at___private_init_lean_parser_token_4__ident_x_27___spec__11(x_29, x_0, x_1, x_18);
x_32 = lean::cnstr_get(x_31, 0);
lean::inc(x_32);
x_34 = lean::cnstr_get(x_31, 1);
lean::inc(x_34);
lean::dec(x_31);
x_37 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_25, x_32);
x_3 = x_37;
x_4 = x_34;
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
uint32 x_40; uint8 x_41; 
x_40 = lean::string_iterator_curr(x_1);
x_41 = l_lean_is__id__first(x_40);
if (x_41 == 0)
{
obj* x_42; obj* x_43; obj* x_45; obj* x_47; obj* x_48; obj* x_49; obj* x_54; obj* x_55; obj* x_57; obj* x_60; obj* x_62; 
x_42 = l_char_quote__core(x_40);
x_43 = l_char_has__repr___closed__1;
lean::inc(x_43);
x_45 = lean::string_append(x_43, x_42);
lean::dec(x_42);
x_47 = lean::string_append(x_45, x_43);
x_48 = lean::box(0);
x_49 = l_mjoin___rarg___closed__1;
lean::inc(x_1);
lean::inc(x_0);
lean::inc(x_48);
lean::inc(x_49);
x_54 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_47, x_49, x_48, x_48, x_0, x_1, x_2);
x_55 = lean::cnstr_get(x_54, 0);
lean::inc(x_55);
x_57 = lean::cnstr_get(x_54, 1);
lean::inc(x_57);
lean::dec(x_54);
x_60 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_60);
x_62 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_60, x_55);
if (lean::obj_tag(x_62) == 0)
{
lean::dec(x_0);
x_3 = x_62;
x_4 = x_57;
goto lbl_5;
}
else
{
obj* x_64; uint8 x_66; 
x_64 = lean::cnstr_get(x_62, 0);
lean::inc(x_64);
x_66 = lean::cnstr_get_scalar<uint8>(x_62, sizeof(void*)*1);
if (x_66 == 0)
{
uint32 x_68; obj* x_70; obj* x_71; obj* x_73; obj* x_76; 
lean::dec(x_62);
x_68 = l_lean_id__begin__escape;
lean::inc(x_1);
x_70 = l_lean_parser_monad__parsec_ch___at___private_init_lean_parser_token_4__ident_x_27___spec__11(x_68, x_0, x_1, x_57);
x_71 = lean::cnstr_get(x_70, 0);
lean::inc(x_71);
x_73 = lean::cnstr_get(x_70, 1);
lean::inc(x_73);
lean::dec(x_70);
x_76 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_64, x_71);
x_3 = x_76;
x_4 = x_73;
goto lbl_5;
}
else
{
lean::dec(x_0);
lean::dec(x_64);
x_3 = x_62;
x_4 = x_57;
goto lbl_5;
}
}
}
else
{
obj* x_81; obj* x_82; obj* x_83; obj* x_84; 
lean::dec(x_0);
lean::inc(x_1);
x_81 = lean::string_iterator_next(x_1);
x_82 = lean::box(0);
x_83 = lean::box_uint32(x_40);
x_84 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_84, 0, x_83);
lean::cnstr_set(x_84, 1, x_81);
lean::cnstr_set(x_84, 2, x_82);
x_3 = x_84;
x_4 = x_2;
goto lbl_5;
}
}
lbl_5:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_85; obj* x_87; obj* x_88; obj* x_90; obj* x_91; 
x_85 = lean::cnstr_get(x_3, 0);
lean::inc(x_85);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_87 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 1);
 lean::cnstr_release(x_3, 2);
 x_87 = x_3;
}
x_88 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_88);
if (lean::is_scalar(x_87)) {
 x_90 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_90 = x_87;
}
lean::cnstr_set(x_90, 0, x_85);
lean::cnstr_set(x_90, 1, x_1);
lean::cnstr_set(x_90, 2, x_88);
x_91 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_91, 0, x_90);
lean::cnstr_set(x_91, 1, x_4);
return x_91;
}
else
{
obj* x_93; 
lean::dec(x_1);
x_93 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_93, 0, x_3);
lean::cnstr_set(x_93, 1, x_4);
return x_93;
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
obj* x_7; obj* x_8; uint32 x_11; uint8 x_12; obj* x_13; obj* x_15; obj* x_16; uint32 x_18; obj* x_20; 
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
uint32 x_22; uint32 x_23; uint8 x_24; 
x_22 = 97;
x_23 = 55296;
x_24 = x_22 < x_23;
if (x_24 == 0)
{
uint32 x_25; uint8 x_26; 
x_25 = 57343;
x_26 = x_25 < x_22;
if (x_26 == 0)
{
uint32 x_27; 
x_27 = 0;
x_18 = x_27;
goto lbl_19;
}
else
{
uint32 x_28; uint8 x_29; 
x_28 = 1114112;
x_29 = x_22 < x_28;
if (x_29 == 0)
{
uint32 x_30; 
x_30 = 0;
x_18 = x_30;
goto lbl_19;
}
else
{
x_18 = x_22;
goto lbl_19;
}
}
}
else
{
x_18 = x_22;
goto lbl_19;
}
}
else
{
obj* x_31; 
x_31 = lean::box(0);
x_20 = x_31;
goto lbl_21;
}
lbl_17:
{
obj* x_33; uint32 x_34; uint32 x_35; uint8 x_36; 
lean::dec(x_16);
x_33 = lean::uint32_to_nat(x_11);
x_34 = 65;
x_35 = 55296;
x_36 = x_34 < x_35;
if (x_36 == 0)
{
uint32 x_37; uint8 x_38; 
x_37 = 57343;
x_38 = x_37 < x_34;
if (x_38 == 0)
{
obj* x_39; obj* x_40; obj* x_42; 
x_39 = l___private_init_data_string_basic_4__to__nat__core___main___closed__1;
x_40 = lean::nat_sub(x_33, x_39);
lean::dec(x_33);
x_42 = lean::nat_add(x_13, x_40);
lean::dec(x_40);
lean::dec(x_13);
x_1 = x_15;
x_2 = x_8;
x_3 = x_42;
goto _start;
}
else
{
uint32 x_46; uint8 x_47; 
x_46 = 1114112;
x_47 = x_34 < x_46;
if (x_47 == 0)
{
obj* x_48; obj* x_49; obj* x_51; 
x_48 = l___private_init_data_string_basic_4__to__nat__core___main___closed__1;
x_49 = lean::nat_sub(x_33, x_48);
lean::dec(x_33);
x_51 = lean::nat_add(x_13, x_49);
lean::dec(x_49);
lean::dec(x_13);
x_1 = x_15;
x_2 = x_8;
x_3 = x_51;
goto _start;
}
else
{
obj* x_55; obj* x_56; obj* x_58; 
x_55 = l_lean_parser_parse__hex__digit___rarg___lambda__5___closed__1;
x_56 = lean::nat_sub(x_33, x_55);
lean::dec(x_33);
x_58 = lean::nat_add(x_13, x_56);
lean::dec(x_56);
lean::dec(x_13);
x_1 = x_15;
x_2 = x_8;
x_3 = x_58;
goto _start;
}
}
}
else
{
obj* x_62; obj* x_63; obj* x_65; 
x_62 = l_lean_parser_parse__hex__digit___rarg___lambda__5___closed__1;
x_63 = lean::nat_sub(x_33, x_62);
lean::dec(x_33);
x_65 = lean::nat_add(x_13, x_63);
lean::dec(x_63);
lean::dec(x_13);
x_1 = x_15;
x_2 = x_8;
x_3 = x_65;
goto _start;
}
}
lbl_19:
{
uint32 x_69; uint8 x_71; 
x_71 = x_18 <= x_11;
if (x_71 == 0)
{
obj* x_72; 
x_72 = lean::box(0);
x_16 = x_72;
goto lbl_17;
}
else
{
uint32 x_73; uint32 x_74; uint8 x_75; 
x_73 = 102;
x_74 = 55296;
x_75 = x_73 < x_74;
if (x_75 == 0)
{
uint32 x_76; uint8 x_77; 
x_76 = 57343;
x_77 = x_76 < x_73;
if (x_77 == 0)
{
uint32 x_78; 
x_78 = 0;
x_69 = x_78;
goto lbl_70;
}
else
{
uint32 x_79; uint8 x_80; 
x_79 = 1114112;
x_80 = x_73 < x_79;
if (x_80 == 0)
{
uint32 x_81; 
x_81 = 0;
x_69 = x_81;
goto lbl_70;
}
else
{
x_69 = x_73;
goto lbl_70;
}
}
}
else
{
x_69 = x_73;
goto lbl_70;
}
}
lbl_70:
{
uint8 x_82; 
x_82 = x_11 <= x_69;
if (x_82 == 0)
{
obj* x_83; 
x_83 = lean::box(0);
x_16 = x_83;
goto lbl_17;
}
else
{
obj* x_84; obj* x_85; obj* x_86; obj* x_89; 
x_84 = lean::uint32_to_nat(x_11);
x_85 = lean::uint32_to_nat(x_18);
x_86 = lean::nat_sub(x_84, x_85);
lean::dec(x_85);
lean::dec(x_84);
x_89 = lean::nat_add(x_13, x_86);
lean::dec(x_86);
lean::dec(x_13);
x_1 = x_15;
x_2 = x_8;
x_3 = x_89;
goto _start;
}
}
}
lbl_21:
{
obj* x_94; uint32 x_95; uint32 x_96; uint8 x_97; 
lean::dec(x_20);
x_94 = lean::uint32_to_nat(x_11);
x_95 = 48;
x_96 = 55296;
x_97 = x_95 < x_96;
if (x_97 == 0)
{
uint32 x_98; uint8 x_99; 
x_98 = 57343;
x_99 = x_98 < x_95;
if (x_99 == 0)
{
obj* x_100; obj* x_101; obj* x_103; 
x_100 = l___private_init_data_string_basic_4__to__nat__core___main___closed__1;
x_101 = lean::nat_sub(x_94, x_100);
lean::dec(x_94);
x_103 = lean::nat_add(x_13, x_101);
lean::dec(x_101);
lean::dec(x_13);
x_1 = x_15;
x_2 = x_8;
x_3 = x_103;
goto _start;
}
else
{
uint32 x_107; uint8 x_108; 
x_107 = 1114112;
x_108 = x_95 < x_107;
if (x_108 == 0)
{
obj* x_109; obj* x_110; obj* x_112; 
x_109 = l___private_init_data_string_basic_4__to__nat__core___main___closed__1;
x_110 = lean::nat_sub(x_94, x_109);
lean::dec(x_94);
x_112 = lean::nat_add(x_13, x_110);
lean::dec(x_110);
lean::dec(x_13);
x_1 = x_15;
x_2 = x_8;
x_3 = x_112;
goto _start;
}
else
{
obj* x_116; obj* x_117; obj* x_119; 
x_116 = l___private_init_data_string_basic_4__to__nat__core___main___closed__2;
x_117 = lean::nat_sub(x_94, x_116);
lean::dec(x_94);
x_119 = lean::nat_add(x_13, x_117);
lean::dec(x_117);
lean::dec(x_13);
x_1 = x_15;
x_2 = x_8;
x_3 = x_119;
goto _start;
}
}
}
else
{
obj* x_123; obj* x_124; obj* x_126; 
x_123 = l___private_init_data_string_basic_4__to__nat__core___main___closed__2;
x_124 = lean::nat_sub(x_94, x_123);
lean::dec(x_94);
x_126 = lean::nat_add(x_13, x_124);
lean::dec(x_124);
lean::dec(x_13);
x_1 = x_15;
x_2 = x_8;
x_3 = x_126;
goto _start;
}
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
uint32 x_13; uint8 x_14; 
x_13 = lean::string_iterator_curr(x_1);
x_14 = x_13 == x_0;
if (x_14 == 0)
{
obj* x_15; obj* x_16; obj* x_18; obj* x_20; obj* x_21; obj* x_22; obj* x_25; obj* x_26; obj* x_28; 
x_15 = l_char_quote__core(x_13);
x_16 = l_char_has__repr___closed__1;
lean::inc(x_16);
x_18 = lean::string_append(x_16, x_15);
lean::dec(x_15);
x_20 = lean::string_append(x_18, x_16);
x_21 = lean::box(0);
x_22 = l_mjoin___rarg___closed__1;
lean::inc(x_21);
lean::inc(x_22);
x_25 = l_lean_parser_monad__parsec_error___at_lean_parser_string__lit_view_value___spec__3___rarg(x_20, x_22, x_21, x_21, x_1);
x_26 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_26);
x_28 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_26, x_25);
return x_28;
}
else
{
obj* x_29; obj* x_30; obj* x_31; obj* x_32; 
x_29 = lean::string_iterator_next(x_1);
x_30 = lean::box(0);
x_31 = lean::box_uint32(x_13);
x_32 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_29);
lean::cnstr_set(x_32, 2, x_30);
return x_32;
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
obj* x_7; obj* x_9; obj* x_11; obj* x_13; uint32 x_14; obj* x_16; uint32 x_17; uint32 x_18; uint8 x_19; 
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
x_14 = lean::unbox_uint32(x_7);
lean::dec(x_7);
x_16 = lean::uint32_to_nat(x_14);
x_17 = 48;
x_18 = 55296;
x_19 = x_17 < x_18;
if (x_19 == 0)
{
uint32 x_20; uint8 x_21; 
x_20 = 57343;
x_21 = x_20 < x_17;
if (x_21 == 0)
{
obj* x_22; obj* x_23; obj* x_25; obj* x_27; obj* x_28; 
x_22 = l___private_init_data_string_basic_4__to__nat__core___main___closed__1;
x_23 = lean::nat_sub(x_16, x_22);
lean::dec(x_16);
x_25 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_25);
if (lean::is_scalar(x_13)) {
 x_27 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_27 = x_13;
}
lean::cnstr_set(x_27, 0, x_23);
lean::cnstr_set(x_27, 1, x_9);
lean::cnstr_set(x_27, 2, x_25);
x_28 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_11, x_27);
if (lean::obj_tag(x_28) == 0)
{
obj* x_30; obj* x_32; 
lean::dec(x_0);
x_30 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__4___closed__1;
lean::inc(x_30);
x_32 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_28, x_30);
return x_32;
}
else
{
obj* x_33; uint8 x_35; 
x_33 = lean::cnstr_get(x_28, 0);
lean::inc(x_33);
x_35 = lean::cnstr_get_scalar<uint8>(x_28, sizeof(void*)*1);
x_1 = x_28;
x_2 = x_33;
x_3 = x_35;
goto lbl_4;
}
}
else
{
uint32 x_36; uint8 x_37; 
x_36 = 1114112;
x_37 = x_17 < x_36;
if (x_37 == 0)
{
obj* x_38; obj* x_39; obj* x_41; obj* x_43; obj* x_44; 
x_38 = l___private_init_data_string_basic_4__to__nat__core___main___closed__1;
x_39 = lean::nat_sub(x_16, x_38);
lean::dec(x_16);
x_41 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_41);
if (lean::is_scalar(x_13)) {
 x_43 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_43 = x_13;
}
lean::cnstr_set(x_43, 0, x_39);
lean::cnstr_set(x_43, 1, x_9);
lean::cnstr_set(x_43, 2, x_41);
x_44 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_11, x_43);
if (lean::obj_tag(x_44) == 0)
{
obj* x_46; obj* x_48; 
lean::dec(x_0);
x_46 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__4___closed__1;
lean::inc(x_46);
x_48 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_44, x_46);
return x_48;
}
else
{
obj* x_49; uint8 x_51; 
x_49 = lean::cnstr_get(x_44, 0);
lean::inc(x_49);
x_51 = lean::cnstr_get_scalar<uint8>(x_44, sizeof(void*)*1);
x_1 = x_44;
x_2 = x_49;
x_3 = x_51;
goto lbl_4;
}
}
else
{
obj* x_52; obj* x_53; obj* x_55; obj* x_57; obj* x_58; 
x_52 = l___private_init_data_string_basic_4__to__nat__core___main___closed__2;
x_53 = lean::nat_sub(x_16, x_52);
lean::dec(x_16);
x_55 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_55);
if (lean::is_scalar(x_13)) {
 x_57 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_57 = x_13;
}
lean::cnstr_set(x_57, 0, x_53);
lean::cnstr_set(x_57, 1, x_9);
lean::cnstr_set(x_57, 2, x_55);
x_58 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_11, x_57);
if (lean::obj_tag(x_58) == 0)
{
obj* x_60; obj* x_62; 
lean::dec(x_0);
x_60 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__4___closed__1;
lean::inc(x_60);
x_62 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_58, x_60);
return x_62;
}
else
{
obj* x_63; uint8 x_65; 
x_63 = lean::cnstr_get(x_58, 0);
lean::inc(x_63);
x_65 = lean::cnstr_get_scalar<uint8>(x_58, sizeof(void*)*1);
x_1 = x_58;
x_2 = x_63;
x_3 = x_65;
goto lbl_4;
}
}
}
}
else
{
obj* x_66; obj* x_67; obj* x_69; obj* x_71; obj* x_72; 
x_66 = l___private_init_data_string_basic_4__to__nat__core___main___closed__2;
x_67 = lean::nat_sub(x_16, x_66);
lean::dec(x_16);
x_69 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_69);
if (lean::is_scalar(x_13)) {
 x_71 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_71 = x_13;
}
lean::cnstr_set(x_71, 0, x_67);
lean::cnstr_set(x_71, 1, x_9);
lean::cnstr_set(x_71, 2, x_69);
x_72 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_11, x_71);
if (lean::obj_tag(x_72) == 0)
{
obj* x_74; obj* x_76; 
lean::dec(x_0);
x_74 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__4___closed__1;
lean::inc(x_74);
x_76 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_72, x_74);
return x_76;
}
else
{
obj* x_77; uint8 x_79; 
x_77 = lean::cnstr_get(x_72, 0);
lean::inc(x_77);
x_79 = lean::cnstr_get_scalar<uint8>(x_72, sizeof(void*)*1);
x_1 = x_72;
x_2 = x_77;
x_3 = x_79;
goto lbl_4;
}
}
}
else
{
obj* x_80; uint8 x_82; obj* x_83; obj* x_85; obj* x_86; 
x_80 = lean::cnstr_get(x_6, 0);
lean::inc(x_80);
x_82 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*1);
if (lean::is_shared(x_6)) {
 lean::dec(x_6);
 x_83 = lean::box(0);
} else {
 lean::cnstr_release(x_6, 0);
 x_83 = x_6;
}
lean::inc(x_80);
if (lean::is_scalar(x_83)) {
 x_85 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_85 = x_83;
}
lean::cnstr_set(x_85, 0, x_80);
lean::cnstr_set_scalar(x_85, sizeof(void*)*1, x_82);
x_86 = x_85;
x_1 = x_86;
x_2 = x_80;
x_3 = x_82;
goto lbl_4;
}
lbl_4:
{
obj* x_87; obj* x_88; uint8 x_89; 
if (x_3 == 0)
{
obj* x_92; uint8 x_94; 
lean::dec(x_1);
x_94 = lean::string_iterator_has_next(x_0);
if (x_94 == 0)
{
obj* x_95; obj* x_96; obj* x_97; obj* x_102; 
x_95 = lean::box(0);
x_96 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_97 = l_mjoin___rarg___closed__1;
lean::inc(x_0);
lean::inc(x_95);
lean::inc(x_97);
lean::inc(x_96);
x_102 = l_lean_parser_monad__parsec_error___at_lean_parser_string__lit_view_value___spec__3___rarg(x_96, x_97, x_95, x_95, x_0);
x_92 = x_102;
goto lbl_93;
}
else
{
uint32 x_103; obj* x_104; obj* x_106; uint32 x_108; uint32 x_109; uint8 x_110; uint8 x_111; 
x_103 = lean::string_iterator_curr(x_0);
x_108 = 97;
x_109 = 55296;
x_110 = x_108 < x_109;
if (x_110 == 0)
{
uint32 x_113; uint8 x_114; 
x_113 = 57343;
x_114 = x_113 < x_108;
if (x_114 == 0)
{
uint32 x_115; uint8 x_116; 
x_115 = 0;
x_116 = x_115 <= x_103;
if (x_116 == 0)
{
obj* x_117; 
x_117 = lean::box(0);
x_104 = x_117;
goto lbl_105;
}
else
{
uint8 x_118; 
x_118 = 1;
x_111 = x_118;
goto lbl_112;
}
}
else
{
uint32 x_119; uint8 x_120; 
x_119 = 1114112;
x_120 = x_108 < x_119;
if (x_120 == 0)
{
uint32 x_121; uint8 x_122; 
x_121 = 0;
x_122 = x_121 <= x_103;
if (x_122 == 0)
{
obj* x_123; 
x_123 = lean::box(0);
x_104 = x_123;
goto lbl_105;
}
else
{
uint8 x_124; 
x_124 = 1;
x_111 = x_124;
goto lbl_112;
}
}
else
{
uint8 x_125; 
x_125 = x_108 <= x_103;
if (x_125 == 0)
{
obj* x_126; 
x_126 = lean::box(0);
x_104 = x_126;
goto lbl_105;
}
else
{
uint8 x_127; 
x_127 = 1;
x_111 = x_127;
goto lbl_112;
}
}
}
}
else
{
uint8 x_128; 
x_128 = x_108 <= x_103;
if (x_128 == 0)
{
obj* x_129; 
x_129 = lean::box(0);
x_104 = x_129;
goto lbl_105;
}
else
{
uint8 x_130; 
x_130 = 1;
x_111 = x_130;
goto lbl_112;
}
}
lbl_105:
{
obj* x_132; obj* x_133; obj* x_135; obj* x_137; obj* x_138; obj* x_139; obj* x_143; 
lean::dec(x_104);
x_132 = l_char_quote__core(x_103);
x_133 = l_char_has__repr___closed__1;
lean::inc(x_133);
x_135 = lean::string_append(x_133, x_132);
lean::dec(x_132);
x_137 = lean::string_append(x_135, x_133);
x_138 = lean::box(0);
x_139 = l_mjoin___rarg___closed__1;
lean::inc(x_0);
lean::inc(x_138);
lean::inc(x_139);
x_143 = l_lean_parser_monad__parsec_error___at_lean_parser_string__lit_view_value___spec__3___rarg(x_137, x_139, x_138, x_138, x_0);
x_92 = x_143;
goto lbl_93;
}
lbl_107:
{
obj* x_146; obj* x_147; obj* x_148; obj* x_149; 
lean::dec(x_106);
lean::inc(x_0);
x_146 = lean::string_iterator_next(x_0);
x_147 = lean::box(0);
x_148 = lean::box_uint32(x_103);
x_149 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_149, 0, x_148);
lean::cnstr_set(x_149, 1, x_146);
lean::cnstr_set(x_149, 2, x_147);
x_92 = x_149;
goto lbl_93;
}
lbl_112:
{
uint32 x_150; uint8 x_151; 
x_150 = 102;
x_151 = x_150 < x_109;
if (x_151 == 0)
{
uint32 x_152; uint8 x_153; 
x_152 = 57343;
x_153 = x_152 < x_150;
if (x_153 == 0)
{
uint32 x_154; uint8 x_155; 
x_154 = 0;
x_155 = x_103 <= x_154;
if (x_155 == 0)
{
obj* x_156; 
x_156 = lean::box(0);
x_104 = x_156;
goto lbl_105;
}
else
{
if (x_111 == 0)
{
obj* x_157; 
x_157 = lean::box(0);
x_104 = x_157;
goto lbl_105;
}
else
{
obj* x_158; 
x_158 = lean::box(0);
x_106 = x_158;
goto lbl_107;
}
}
}
else
{
uint32 x_159; uint8 x_160; 
x_159 = 1114112;
x_160 = x_150 < x_159;
if (x_160 == 0)
{
uint32 x_161; uint8 x_162; 
x_161 = 0;
x_162 = x_103 <= x_161;
if (x_162 == 0)
{
obj* x_163; 
x_163 = lean::box(0);
x_104 = x_163;
goto lbl_105;
}
else
{
if (x_111 == 0)
{
obj* x_164; 
x_164 = lean::box(0);
x_104 = x_164;
goto lbl_105;
}
else
{
obj* x_165; 
x_165 = lean::box(0);
x_106 = x_165;
goto lbl_107;
}
}
}
else
{
uint8 x_166; 
x_166 = x_103 <= x_150;
if (x_166 == 0)
{
obj* x_167; 
x_167 = lean::box(0);
x_104 = x_167;
goto lbl_105;
}
else
{
if (x_111 == 0)
{
obj* x_168; 
x_168 = lean::box(0);
x_104 = x_168;
goto lbl_105;
}
else
{
obj* x_169; 
x_169 = lean::box(0);
x_106 = x_169;
goto lbl_107;
}
}
}
}
}
else
{
uint8 x_170; 
x_170 = x_103 <= x_150;
if (x_170 == 0)
{
obj* x_171; 
x_171 = lean::box(0);
x_104 = x_171;
goto lbl_105;
}
else
{
if (x_111 == 0)
{
obj* x_172; 
x_172 = lean::box(0);
x_104 = x_172;
goto lbl_105;
}
else
{
obj* x_173; 
x_173 = lean::box(0);
x_106 = x_173;
goto lbl_107;
}
}
}
}
}
lbl_93:
{
obj* x_174; obj* x_176; 
x_174 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_174);
x_176 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_174, x_92);
if (lean::obj_tag(x_176) == 0)
{
obj* x_177; obj* x_179; obj* x_181; obj* x_183; uint32 x_184; obj* x_186; uint32 x_187; uint32 x_188; uint8 x_189; 
x_177 = lean::cnstr_get(x_176, 0);
lean::inc(x_177);
x_179 = lean::cnstr_get(x_176, 1);
lean::inc(x_179);
x_181 = lean::cnstr_get(x_176, 2);
lean::inc(x_181);
if (lean::is_shared(x_176)) {
 lean::dec(x_176);
 x_183 = lean::box(0);
} else {
 lean::cnstr_release(x_176, 0);
 lean::cnstr_release(x_176, 1);
 lean::cnstr_release(x_176, 2);
 x_183 = x_176;
}
x_184 = lean::unbox_uint32(x_177);
lean::dec(x_177);
x_186 = lean::uint32_to_nat(x_184);
x_187 = 97;
x_188 = 55296;
x_189 = x_187 < x_188;
if (x_189 == 0)
{
uint32 x_190; uint8 x_191; 
x_190 = 57343;
x_191 = x_190 < x_187;
if (x_191 == 0)
{
obj* x_192; obj* x_193; obj* x_195; obj* x_196; obj* x_200; obj* x_201; 
x_192 = l___private_init_data_string_basic_4__to__nat__core___main___closed__1;
x_193 = lean::nat_sub(x_186, x_192);
lean::dec(x_186);
x_195 = lean::mk_nat_obj(10u);
x_196 = lean::nat_add(x_195, x_193);
lean::dec(x_193);
lean::dec(x_195);
lean::inc(x_174);
if (lean::is_scalar(x_183)) {
 x_200 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_200 = x_183;
}
lean::cnstr_set(x_200, 0, x_196);
lean::cnstr_set(x_200, 1, x_179);
lean::cnstr_set(x_200, 2, x_174);
x_201 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_181, x_200);
if (lean::obj_tag(x_201) == 0)
{
obj* x_203; obj* x_204; obj* x_206; 
lean::dec(x_0);
x_203 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_2, x_201);
x_204 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__4___closed__1;
lean::inc(x_204);
x_206 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_203, x_204);
return x_206;
}
else
{
obj* x_207; uint8 x_209; 
x_207 = lean::cnstr_get(x_201, 0);
lean::inc(x_207);
x_209 = lean::cnstr_get_scalar<uint8>(x_201, sizeof(void*)*1);
x_87 = x_201;
x_88 = x_207;
x_89 = x_209;
goto lbl_90;
}
}
else
{
uint32 x_210; uint8 x_211; 
x_210 = 1114112;
x_211 = x_187 < x_210;
if (x_211 == 0)
{
obj* x_212; obj* x_213; obj* x_215; obj* x_216; obj* x_220; obj* x_221; 
x_212 = l___private_init_data_string_basic_4__to__nat__core___main___closed__1;
x_213 = lean::nat_sub(x_186, x_212);
lean::dec(x_186);
x_215 = lean::mk_nat_obj(10u);
x_216 = lean::nat_add(x_215, x_213);
lean::dec(x_213);
lean::dec(x_215);
lean::inc(x_174);
if (lean::is_scalar(x_183)) {
 x_220 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_220 = x_183;
}
lean::cnstr_set(x_220, 0, x_216);
lean::cnstr_set(x_220, 1, x_179);
lean::cnstr_set(x_220, 2, x_174);
x_221 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_181, x_220);
if (lean::obj_tag(x_221) == 0)
{
obj* x_223; obj* x_224; obj* x_226; 
lean::dec(x_0);
x_223 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_2, x_221);
x_224 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__4___closed__1;
lean::inc(x_224);
x_226 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_223, x_224);
return x_226;
}
else
{
obj* x_227; uint8 x_229; 
x_227 = lean::cnstr_get(x_221, 0);
lean::inc(x_227);
x_229 = lean::cnstr_get_scalar<uint8>(x_221, sizeof(void*)*1);
x_87 = x_221;
x_88 = x_227;
x_89 = x_229;
goto lbl_90;
}
}
else
{
obj* x_230; obj* x_231; obj* x_233; obj* x_234; obj* x_238; obj* x_239; 
x_230 = l_lean_parser_parse__hex__digit___rarg___lambda__3___closed__1;
x_231 = lean::nat_sub(x_186, x_230);
lean::dec(x_186);
x_233 = lean::mk_nat_obj(10u);
x_234 = lean::nat_add(x_233, x_231);
lean::dec(x_231);
lean::dec(x_233);
lean::inc(x_174);
if (lean::is_scalar(x_183)) {
 x_238 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_238 = x_183;
}
lean::cnstr_set(x_238, 0, x_234);
lean::cnstr_set(x_238, 1, x_179);
lean::cnstr_set(x_238, 2, x_174);
x_239 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_181, x_238);
if (lean::obj_tag(x_239) == 0)
{
obj* x_241; obj* x_242; obj* x_244; 
lean::dec(x_0);
x_241 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_2, x_239);
x_242 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__4___closed__1;
lean::inc(x_242);
x_244 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_241, x_242);
return x_244;
}
else
{
obj* x_245; uint8 x_247; 
x_245 = lean::cnstr_get(x_239, 0);
lean::inc(x_245);
x_247 = lean::cnstr_get_scalar<uint8>(x_239, sizeof(void*)*1);
x_87 = x_239;
x_88 = x_245;
x_89 = x_247;
goto lbl_90;
}
}
}
}
else
{
obj* x_248; obj* x_249; obj* x_251; obj* x_252; obj* x_256; obj* x_257; 
x_248 = l_lean_parser_parse__hex__digit___rarg___lambda__3___closed__1;
x_249 = lean::nat_sub(x_186, x_248);
lean::dec(x_186);
x_251 = lean::mk_nat_obj(10u);
x_252 = lean::nat_add(x_251, x_249);
lean::dec(x_249);
lean::dec(x_251);
lean::inc(x_174);
if (lean::is_scalar(x_183)) {
 x_256 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_256 = x_183;
}
lean::cnstr_set(x_256, 0, x_252);
lean::cnstr_set(x_256, 1, x_179);
lean::cnstr_set(x_256, 2, x_174);
x_257 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_181, x_256);
if (lean::obj_tag(x_257) == 0)
{
obj* x_259; obj* x_260; obj* x_262; 
lean::dec(x_0);
x_259 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_2, x_257);
x_260 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__4___closed__1;
lean::inc(x_260);
x_262 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_259, x_260);
return x_262;
}
else
{
obj* x_263; uint8 x_265; 
x_263 = lean::cnstr_get(x_257, 0);
lean::inc(x_263);
x_265 = lean::cnstr_get_scalar<uint8>(x_257, sizeof(void*)*1);
x_87 = x_257;
x_88 = x_263;
x_89 = x_265;
goto lbl_90;
}
}
}
else
{
obj* x_266; uint8 x_268; obj* x_269; obj* x_271; obj* x_272; 
x_266 = lean::cnstr_get(x_176, 0);
lean::inc(x_266);
x_268 = lean::cnstr_get_scalar<uint8>(x_176, sizeof(void*)*1);
if (lean::is_shared(x_176)) {
 lean::dec(x_176);
 x_269 = lean::box(0);
} else {
 lean::cnstr_release(x_176, 0);
 x_269 = x_176;
}
lean::inc(x_266);
if (lean::is_scalar(x_269)) {
 x_271 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_271 = x_269;
}
lean::cnstr_set(x_271, 0, x_266);
lean::cnstr_set_scalar(x_271, sizeof(void*)*1, x_268);
x_272 = x_271;
x_87 = x_272;
x_88 = x_266;
x_89 = x_268;
goto lbl_90;
}
}
}
else
{
obj* x_275; obj* x_277; 
lean::dec(x_0);
lean::dec(x_2);
x_275 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__4___closed__1;
lean::inc(x_275);
x_277 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_1, x_275);
return x_277;
}
lbl_90:
{
if (x_89 == 0)
{
obj* x_279; uint8 x_281; 
lean::dec(x_87);
x_281 = lean::string_iterator_has_next(x_0);
if (x_281 == 0)
{
obj* x_282; obj* x_283; obj* x_284; obj* x_288; 
x_282 = lean::box(0);
x_283 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_284 = l_mjoin___rarg___closed__1;
lean::inc(x_282);
lean::inc(x_284);
lean::inc(x_283);
x_288 = l_lean_parser_monad__parsec_error___at_lean_parser_string__lit_view_value___spec__3___rarg(x_283, x_284, x_282, x_282, x_0);
x_279 = x_288;
goto lbl_280;
}
else
{
uint32 x_289; obj* x_290; obj* x_292; uint32 x_294; uint32 x_295; uint8 x_296; uint8 x_297; 
x_289 = lean::string_iterator_curr(x_0);
x_294 = 65;
x_295 = 55296;
x_296 = x_294 < x_295;
if (x_296 == 0)
{
uint32 x_299; uint8 x_300; 
x_299 = 57343;
x_300 = x_299 < x_294;
if (x_300 == 0)
{
uint32 x_301; uint8 x_302; 
x_301 = 0;
x_302 = x_301 <= x_289;
if (x_302 == 0)
{
obj* x_303; 
x_303 = lean::box(0);
x_290 = x_303;
goto lbl_291;
}
else
{
uint8 x_304; 
x_304 = 1;
x_297 = x_304;
goto lbl_298;
}
}
else
{
uint32 x_305; uint8 x_306; 
x_305 = 1114112;
x_306 = x_294 < x_305;
if (x_306 == 0)
{
uint32 x_307; uint8 x_308; 
x_307 = 0;
x_308 = x_307 <= x_289;
if (x_308 == 0)
{
obj* x_309; 
x_309 = lean::box(0);
x_290 = x_309;
goto lbl_291;
}
else
{
uint8 x_310; 
x_310 = 1;
x_297 = x_310;
goto lbl_298;
}
}
else
{
uint8 x_311; 
x_311 = x_294 <= x_289;
if (x_311 == 0)
{
obj* x_312; 
x_312 = lean::box(0);
x_290 = x_312;
goto lbl_291;
}
else
{
uint8 x_313; 
x_313 = 1;
x_297 = x_313;
goto lbl_298;
}
}
}
}
else
{
uint8 x_314; 
x_314 = x_294 <= x_289;
if (x_314 == 0)
{
obj* x_315; 
x_315 = lean::box(0);
x_290 = x_315;
goto lbl_291;
}
else
{
uint8 x_316; 
x_316 = 1;
x_297 = x_316;
goto lbl_298;
}
}
lbl_291:
{
obj* x_318; obj* x_319; obj* x_321; obj* x_323; obj* x_324; obj* x_325; obj* x_328; 
lean::dec(x_290);
x_318 = l_char_quote__core(x_289);
x_319 = l_char_has__repr___closed__1;
lean::inc(x_319);
x_321 = lean::string_append(x_319, x_318);
lean::dec(x_318);
x_323 = lean::string_append(x_321, x_319);
x_324 = lean::box(0);
x_325 = l_mjoin___rarg___closed__1;
lean::inc(x_324);
lean::inc(x_325);
x_328 = l_lean_parser_monad__parsec_error___at_lean_parser_string__lit_view_value___spec__3___rarg(x_323, x_325, x_324, x_324, x_0);
x_279 = x_328;
goto lbl_280;
}
lbl_293:
{
obj* x_330; obj* x_331; obj* x_332; obj* x_333; 
lean::dec(x_292);
x_330 = lean::string_iterator_next(x_0);
x_331 = lean::box(0);
x_332 = lean::box_uint32(x_289);
x_333 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_333, 0, x_332);
lean::cnstr_set(x_333, 1, x_330);
lean::cnstr_set(x_333, 2, x_331);
x_279 = x_333;
goto lbl_280;
}
lbl_298:
{
uint32 x_334; uint8 x_335; 
x_334 = 70;
x_335 = x_334 < x_295;
if (x_335 == 0)
{
uint32 x_336; uint8 x_337; 
x_336 = 57343;
x_337 = x_336 < x_334;
if (x_337 == 0)
{
uint32 x_338; uint8 x_339; 
x_338 = 0;
x_339 = x_289 <= x_338;
if (x_339 == 0)
{
obj* x_340; 
x_340 = lean::box(0);
x_290 = x_340;
goto lbl_291;
}
else
{
if (x_297 == 0)
{
obj* x_341; 
x_341 = lean::box(0);
x_290 = x_341;
goto lbl_291;
}
else
{
obj* x_342; 
x_342 = lean::box(0);
x_292 = x_342;
goto lbl_293;
}
}
}
else
{
uint32 x_343; uint8 x_344; 
x_343 = 1114112;
x_344 = x_334 < x_343;
if (x_344 == 0)
{
uint32 x_345; uint8 x_346; 
x_345 = 0;
x_346 = x_289 <= x_345;
if (x_346 == 0)
{
obj* x_347; 
x_347 = lean::box(0);
x_290 = x_347;
goto lbl_291;
}
else
{
if (x_297 == 0)
{
obj* x_348; 
x_348 = lean::box(0);
x_290 = x_348;
goto lbl_291;
}
else
{
obj* x_349; 
x_349 = lean::box(0);
x_292 = x_349;
goto lbl_293;
}
}
}
else
{
uint8 x_350; 
x_350 = x_289 <= x_334;
if (x_350 == 0)
{
obj* x_351; 
x_351 = lean::box(0);
x_290 = x_351;
goto lbl_291;
}
else
{
if (x_297 == 0)
{
obj* x_352; 
x_352 = lean::box(0);
x_290 = x_352;
goto lbl_291;
}
else
{
obj* x_353; 
x_353 = lean::box(0);
x_292 = x_353;
goto lbl_293;
}
}
}
}
}
else
{
uint8 x_354; 
x_354 = x_289 <= x_334;
if (x_354 == 0)
{
obj* x_355; 
x_355 = lean::box(0);
x_290 = x_355;
goto lbl_291;
}
else
{
if (x_297 == 0)
{
obj* x_356; 
x_356 = lean::box(0);
x_290 = x_356;
goto lbl_291;
}
else
{
obj* x_357; 
x_357 = lean::box(0);
x_292 = x_357;
goto lbl_293;
}
}
}
}
}
lbl_280:
{
obj* x_358; obj* x_360; 
x_358 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_358);
x_360 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_358, x_279);
if (lean::obj_tag(x_360) == 0)
{
obj* x_361; obj* x_363; obj* x_365; obj* x_367; uint32 x_368; obj* x_370; uint32 x_371; uint32 x_372; uint8 x_373; 
x_361 = lean::cnstr_get(x_360, 0);
lean::inc(x_361);
x_363 = lean::cnstr_get(x_360, 1);
lean::inc(x_363);
x_365 = lean::cnstr_get(x_360, 2);
lean::inc(x_365);
if (lean::is_shared(x_360)) {
 lean::dec(x_360);
 x_367 = lean::box(0);
} else {
 lean::cnstr_release(x_360, 0);
 lean::cnstr_release(x_360, 1);
 lean::cnstr_release(x_360, 2);
 x_367 = x_360;
}
x_368 = lean::unbox_uint32(x_361);
lean::dec(x_361);
x_370 = lean::uint32_to_nat(x_368);
x_371 = 65;
x_372 = 55296;
x_373 = x_371 < x_372;
if (x_373 == 0)
{
uint32 x_374; uint8 x_375; 
x_374 = 57343;
x_375 = x_374 < x_371;
if (x_375 == 0)
{
obj* x_376; obj* x_377; obj* x_379; obj* x_380; obj* x_384; obj* x_385; obj* x_386; obj* x_387; obj* x_388; obj* x_390; 
x_376 = l___private_init_data_string_basic_4__to__nat__core___main___closed__1;
x_377 = lean::nat_sub(x_370, x_376);
lean::dec(x_370);
x_379 = lean::mk_nat_obj(10u);
x_380 = lean::nat_add(x_379, x_377);
lean::dec(x_377);
lean::dec(x_379);
lean::inc(x_358);
if (lean::is_scalar(x_367)) {
 x_384 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_384 = x_367;
}
lean::cnstr_set(x_384, 0, x_380);
lean::cnstr_set(x_384, 1, x_363);
lean::cnstr_set(x_384, 2, x_358);
x_385 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_365, x_384);
x_386 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_88, x_385);
x_387 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_2, x_386);
x_388 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__4___closed__1;
lean::inc(x_388);
x_390 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_387, x_388);
return x_390;
}
else
{
uint32 x_391; uint8 x_392; 
x_391 = 1114112;
x_392 = x_371 < x_391;
if (x_392 == 0)
{
obj* x_393; obj* x_394; obj* x_396; obj* x_397; obj* x_401; obj* x_402; obj* x_403; obj* x_404; obj* x_405; obj* x_407; 
x_393 = l___private_init_data_string_basic_4__to__nat__core___main___closed__1;
x_394 = lean::nat_sub(x_370, x_393);
lean::dec(x_370);
x_396 = lean::mk_nat_obj(10u);
x_397 = lean::nat_add(x_396, x_394);
lean::dec(x_394);
lean::dec(x_396);
lean::inc(x_358);
if (lean::is_scalar(x_367)) {
 x_401 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_401 = x_367;
}
lean::cnstr_set(x_401, 0, x_397);
lean::cnstr_set(x_401, 1, x_363);
lean::cnstr_set(x_401, 2, x_358);
x_402 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_365, x_401);
x_403 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_88, x_402);
x_404 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_2, x_403);
x_405 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__4___closed__1;
lean::inc(x_405);
x_407 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_404, x_405);
return x_407;
}
else
{
obj* x_408; obj* x_409; obj* x_411; obj* x_412; obj* x_416; obj* x_417; obj* x_418; obj* x_419; obj* x_420; obj* x_422; 
x_408 = l_lean_parser_parse__hex__digit___rarg___lambda__5___closed__1;
x_409 = lean::nat_sub(x_370, x_408);
lean::dec(x_370);
x_411 = lean::mk_nat_obj(10u);
x_412 = lean::nat_add(x_411, x_409);
lean::dec(x_409);
lean::dec(x_411);
lean::inc(x_358);
if (lean::is_scalar(x_367)) {
 x_416 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_416 = x_367;
}
lean::cnstr_set(x_416, 0, x_412);
lean::cnstr_set(x_416, 1, x_363);
lean::cnstr_set(x_416, 2, x_358);
x_417 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_365, x_416);
x_418 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_88, x_417);
x_419 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_2, x_418);
x_420 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__4___closed__1;
lean::inc(x_420);
x_422 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_419, x_420);
return x_422;
}
}
}
else
{
obj* x_423; obj* x_424; obj* x_426; obj* x_427; obj* x_431; obj* x_432; obj* x_433; obj* x_434; obj* x_435; obj* x_437; 
x_423 = l_lean_parser_parse__hex__digit___rarg___lambda__5___closed__1;
x_424 = lean::nat_sub(x_370, x_423);
lean::dec(x_370);
x_426 = lean::mk_nat_obj(10u);
x_427 = lean::nat_add(x_426, x_424);
lean::dec(x_424);
lean::dec(x_426);
lean::inc(x_358);
if (lean::is_scalar(x_367)) {
 x_431 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_431 = x_367;
}
lean::cnstr_set(x_431, 0, x_427);
lean::cnstr_set(x_431, 1, x_363);
lean::cnstr_set(x_431, 2, x_358);
x_432 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_365, x_431);
x_433 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_88, x_432);
x_434 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_2, x_433);
x_435 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__4___closed__1;
lean::inc(x_435);
x_437 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_434, x_435);
return x_437;
}
}
else
{
obj* x_438; uint8 x_440; obj* x_441; obj* x_442; obj* x_443; obj* x_444; obj* x_445; obj* x_446; obj* x_448; 
x_438 = lean::cnstr_get(x_360, 0);
lean::inc(x_438);
x_440 = lean::cnstr_get_scalar<uint8>(x_360, sizeof(void*)*1);
if (lean::is_shared(x_360)) {
 lean::dec(x_360);
 x_441 = lean::box(0);
} else {
 lean::cnstr_release(x_360, 0);
 x_441 = x_360;
}
if (lean::is_scalar(x_441)) {
 x_442 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_442 = x_441;
}
lean::cnstr_set(x_442, 0, x_438);
lean::cnstr_set_scalar(x_442, sizeof(void*)*1, x_440);
x_443 = x_442;
x_444 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_88, x_443);
x_445 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_2, x_444);
x_446 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__4___closed__1;
lean::inc(x_446);
x_448 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_445, x_446);
return x_448;
}
}
}
else
{
obj* x_451; obj* x_452; obj* x_454; 
lean::dec(x_88);
lean::dec(x_0);
x_451 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_2, x_87);
x_452 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__4___closed__1;
lean::inc(x_452);
x_454 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_451, x_452);
return x_454;
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
obj* x_3; obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_14; obj* x_16; obj* x_18; obj* x_20; obj* x_22; obj* x_24; obj* x_26; obj* x_28; uint32 x_30; uint32 x_31; uint8 x_32; uint32 x_33; 
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
x_30 = 92;
x_31 = 55296;
x_32 = x_30 < x_31;
if (x_32 == 0)
{
uint32 x_35; uint8 x_36; 
x_35 = 57343;
x_36 = x_35 < x_30;
if (x_36 == 0)
{
uint32 x_37; 
x_37 = 0;
x_33 = x_37;
goto lbl_34;
}
else
{
uint32 x_38; uint8 x_39; 
x_38 = 1114112;
x_39 = x_30 < x_38;
if (x_39 == 0)
{
uint32 x_40; 
x_40 = 0;
x_33 = x_40;
goto lbl_34;
}
else
{
x_33 = x_30;
goto lbl_34;
}
}
}
else
{
x_33 = x_30;
goto lbl_34;
}
lbl_11:
{
obj* x_42; 
lean::dec(x_10);
x_42 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_view_value___spec__7(x_5);
if (lean::obj_tag(x_42) == 0)
{
obj* x_43; obj* x_45; obj* x_47; obj* x_50; 
x_43 = lean::cnstr_get(x_42, 0);
lean::inc(x_43);
x_45 = lean::cnstr_get(x_42, 1);
lean::inc(x_45);
x_47 = lean::cnstr_get(x_42, 2);
lean::inc(x_47);
lean::dec(x_42);
x_50 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_view_value___spec__7(x_45);
if (lean::obj_tag(x_50) == 0)
{
obj* x_51; obj* x_53; obj* x_55; obj* x_58; 
x_51 = lean::cnstr_get(x_50, 0);
lean::inc(x_51);
x_53 = lean::cnstr_get(x_50, 1);
lean::inc(x_53);
x_55 = lean::cnstr_get(x_50, 2);
lean::inc(x_55);
lean::dec(x_50);
x_58 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_view_value___spec__7(x_53);
if (lean::obj_tag(x_58) == 0)
{
obj* x_59; obj* x_61; obj* x_63; obj* x_66; 
x_59 = lean::cnstr_get(x_58, 0);
lean::inc(x_59);
x_61 = lean::cnstr_get(x_58, 1);
lean::inc(x_61);
x_63 = lean::cnstr_get(x_58, 2);
lean::inc(x_63);
lean::dec(x_58);
x_66 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_view_value___spec__7(x_61);
if (lean::obj_tag(x_66) == 0)
{
obj* x_67; obj* x_69; obj* x_71; obj* x_74; obj* x_75; obj* x_77; obj* x_80; obj* x_82; obj* x_85; obj* x_88; uint32 x_91; uint32 x_93; uint8 x_94; 
x_67 = lean::cnstr_get(x_66, 0);
lean::inc(x_67);
x_69 = lean::cnstr_get(x_66, 1);
lean::inc(x_69);
x_71 = lean::cnstr_get(x_66, 2);
lean::inc(x_71);
lean::dec(x_66);
x_74 = lean::mk_nat_obj(16u);
x_75 = lean::nat_mul(x_74, x_43);
lean::dec(x_43);
x_77 = lean::nat_add(x_75, x_51);
lean::dec(x_51);
lean::dec(x_75);
x_80 = lean::nat_mul(x_74, x_77);
lean::dec(x_77);
x_82 = lean::nat_add(x_80, x_59);
lean::dec(x_59);
lean::dec(x_80);
x_85 = lean::nat_mul(x_74, x_82);
lean::dec(x_82);
lean::dec(x_74);
x_88 = lean::nat_add(x_85, x_67);
lean::dec(x_67);
lean::dec(x_85);
x_91 = lean::uint32_of_nat(x_88);
lean::dec(x_88);
x_93 = 55296;
x_94 = x_91 < x_93;
if (x_94 == 0)
{
uint32 x_95; uint8 x_96; 
x_95 = 57343;
x_96 = x_95 < x_91;
if (x_96 == 0)
{
uint32 x_97; obj* x_98; obj* x_99; obj* x_101; obj* x_102; obj* x_103; obj* x_104; obj* x_105; obj* x_106; obj* x_108; 
x_97 = 0;
x_98 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_99 = lean::box_uint32(x_97);
lean::inc(x_98);
if (lean::is_scalar(x_9)) {
 x_101 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_101 = x_9;
}
lean::cnstr_set(x_101, 0, x_99);
lean::cnstr_set(x_101, 1, x_69);
lean::cnstr_set(x_101, 2, x_98);
x_102 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_71, x_101);
x_103 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_63, x_102);
x_104 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_55, x_103);
x_105 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_47, x_104);
x_106 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_105);
lean::inc(x_98);
x_108 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_98, x_106);
return x_108;
}
else
{
uint32 x_109; uint8 x_110; 
x_109 = 1114112;
x_110 = x_91 < x_109;
if (x_110 == 0)
{
uint32 x_111; obj* x_112; obj* x_113; obj* x_115; obj* x_116; obj* x_117; obj* x_118; obj* x_119; obj* x_120; obj* x_122; 
x_111 = 0;
x_112 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_113 = lean::box_uint32(x_111);
lean::inc(x_112);
if (lean::is_scalar(x_9)) {
 x_115 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_115 = x_9;
}
lean::cnstr_set(x_115, 0, x_113);
lean::cnstr_set(x_115, 1, x_69);
lean::cnstr_set(x_115, 2, x_112);
x_116 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_71, x_115);
x_117 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_63, x_116);
x_118 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_55, x_117);
x_119 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_47, x_118);
x_120 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_119);
lean::inc(x_112);
x_122 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_112, x_120);
return x_122;
}
else
{
obj* x_123; obj* x_124; obj* x_126; obj* x_127; obj* x_128; obj* x_129; obj* x_130; obj* x_131; obj* x_133; 
x_123 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_124 = lean::box_uint32(x_91);
lean::inc(x_123);
if (lean::is_scalar(x_9)) {
 x_126 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_126 = x_9;
}
lean::cnstr_set(x_126, 0, x_124);
lean::cnstr_set(x_126, 1, x_69);
lean::cnstr_set(x_126, 2, x_123);
x_127 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_71, x_126);
x_128 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_63, x_127);
x_129 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_55, x_128);
x_130 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_47, x_129);
x_131 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_130);
lean::inc(x_123);
x_133 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_123, x_131);
return x_133;
}
}
}
else
{
obj* x_134; obj* x_135; obj* x_137; obj* x_138; obj* x_139; obj* x_140; obj* x_141; obj* x_142; obj* x_144; 
x_134 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_135 = lean::box_uint32(x_91);
lean::inc(x_134);
if (lean::is_scalar(x_9)) {
 x_137 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_137 = x_9;
}
lean::cnstr_set(x_137, 0, x_135);
lean::cnstr_set(x_137, 1, x_69);
lean::cnstr_set(x_137, 2, x_134);
x_138 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_71, x_137);
x_139 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_63, x_138);
x_140 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_55, x_139);
x_141 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_47, x_140);
x_142 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_141);
lean::inc(x_134);
x_144 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_134, x_142);
return x_144;
}
}
else
{
obj* x_149; uint8 x_151; obj* x_152; obj* x_153; obj* x_154; obj* x_155; obj* x_156; obj* x_157; obj* x_158; obj* x_159; obj* x_161; 
lean::dec(x_9);
lean::dec(x_59);
lean::dec(x_51);
lean::dec(x_43);
x_149 = lean::cnstr_get(x_66, 0);
lean::inc(x_149);
x_151 = lean::cnstr_get_scalar<uint8>(x_66, sizeof(void*)*1);
if (lean::is_shared(x_66)) {
 lean::dec(x_66);
 x_152 = lean::box(0);
} else {
 lean::cnstr_release(x_66, 0);
 x_152 = x_66;
}
if (lean::is_scalar(x_152)) {
 x_153 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_153 = x_152;
}
lean::cnstr_set(x_153, 0, x_149);
lean::cnstr_set_scalar(x_153, sizeof(void*)*1, x_151);
x_154 = x_153;
x_155 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_63, x_154);
x_156 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_55, x_155);
x_157 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_47, x_156);
x_158 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_157);
x_159 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_159);
x_161 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_159, x_158);
return x_161;
}
}
else
{
obj* x_165; uint8 x_167; obj* x_168; obj* x_169; obj* x_170; obj* x_171; obj* x_172; obj* x_173; obj* x_174; obj* x_176; 
lean::dec(x_9);
lean::dec(x_51);
lean::dec(x_43);
x_165 = lean::cnstr_get(x_58, 0);
lean::inc(x_165);
x_167 = lean::cnstr_get_scalar<uint8>(x_58, sizeof(void*)*1);
if (lean::is_shared(x_58)) {
 lean::dec(x_58);
 x_168 = lean::box(0);
} else {
 lean::cnstr_release(x_58, 0);
 x_168 = x_58;
}
if (lean::is_scalar(x_168)) {
 x_169 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_169 = x_168;
}
lean::cnstr_set(x_169, 0, x_165);
lean::cnstr_set_scalar(x_169, sizeof(void*)*1, x_167);
x_170 = x_169;
x_171 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_55, x_170);
x_172 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_47, x_171);
x_173 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_172);
x_174 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_174);
x_176 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_174, x_173);
return x_176;
}
}
else
{
obj* x_179; uint8 x_181; obj* x_182; obj* x_183; obj* x_184; obj* x_185; obj* x_186; obj* x_187; obj* x_189; 
lean::dec(x_9);
lean::dec(x_43);
x_179 = lean::cnstr_get(x_50, 0);
lean::inc(x_179);
x_181 = lean::cnstr_get_scalar<uint8>(x_50, sizeof(void*)*1);
if (lean::is_shared(x_50)) {
 lean::dec(x_50);
 x_182 = lean::box(0);
} else {
 lean::cnstr_release(x_50, 0);
 x_182 = x_50;
}
if (lean::is_scalar(x_182)) {
 x_183 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_183 = x_182;
}
lean::cnstr_set(x_183, 0, x_179);
lean::cnstr_set_scalar(x_183, sizeof(void*)*1, x_181);
x_184 = x_183;
x_185 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_47, x_184);
x_186 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_185);
x_187 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_187);
x_189 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_187, x_186);
return x_189;
}
}
else
{
obj* x_191; uint8 x_193; obj* x_194; obj* x_195; obj* x_196; obj* x_197; obj* x_198; obj* x_200; 
lean::dec(x_9);
x_191 = lean::cnstr_get(x_42, 0);
lean::inc(x_191);
x_193 = lean::cnstr_get_scalar<uint8>(x_42, sizeof(void*)*1);
if (lean::is_shared(x_42)) {
 lean::dec(x_42);
 x_194 = lean::box(0);
} else {
 lean::cnstr_release(x_42, 0);
 x_194 = x_42;
}
if (lean::is_scalar(x_194)) {
 x_195 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_195 = x_194;
}
lean::cnstr_set(x_195, 0, x_191);
lean::cnstr_set_scalar(x_195, sizeof(void*)*1, x_193);
x_196 = x_195;
x_197 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_196);
x_198 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_198);
x_200 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_198, x_197);
return x_200;
}
}
lbl_13:
{
uint32 x_202; uint32 x_203; uint8 x_204; 
lean::dec(x_12);
x_202 = 117;
x_203 = 55296;
x_204 = x_202 < x_203;
if (x_204 == 0)
{
uint32 x_205; uint8 x_206; 
x_205 = 57343;
x_206 = x_205 < x_202;
if (x_206 == 0)
{
uint32 x_207; uint32 x_208; uint8 x_210; 
x_207 = 0;
x_208 = lean::unbox_uint32(x_3);
lean::dec(x_3);
x_210 = x_208 == x_207;
if (x_210 == 0)
{
obj* x_212; obj* x_214; obj* x_215; obj* x_216; obj* x_218; 
lean::dec(x_9);
x_212 = l_lean_parser_parse__quoted__char___rarg___lambda__7___closed__1;
lean::inc(x_212);
x_214 = l_lean_parser_monad__parsec_unexpected__at___at_lean_parser_string__lit_view_value___spec__9___rarg(x_212, x_0, x_5);
x_215 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_214);
x_216 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_216);
x_218 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_216, x_215);
return x_218;
}
else
{
obj* x_220; 
lean::dec(x_0);
x_220 = lean::box(0);
x_10 = x_220;
goto lbl_11;
}
}
else
{
uint32 x_221; uint8 x_222; 
x_221 = 1114112;
x_222 = x_202 < x_221;
if (x_222 == 0)
{
uint32 x_223; uint32 x_224; uint8 x_226; 
x_223 = 0;
x_224 = lean::unbox_uint32(x_3);
lean::dec(x_3);
x_226 = x_224 == x_223;
if (x_226 == 0)
{
obj* x_228; obj* x_230; obj* x_231; obj* x_232; obj* x_234; 
lean::dec(x_9);
x_228 = l_lean_parser_parse__quoted__char___rarg___lambda__7___closed__1;
lean::inc(x_228);
x_230 = l_lean_parser_monad__parsec_unexpected__at___at_lean_parser_string__lit_view_value___spec__9___rarg(x_228, x_0, x_5);
x_231 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_230);
x_232 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_232);
x_234 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_232, x_231);
return x_234;
}
else
{
obj* x_236; 
lean::dec(x_0);
x_236 = lean::box(0);
x_10 = x_236;
goto lbl_11;
}
}
else
{
uint32 x_237; uint8 x_239; 
x_237 = lean::unbox_uint32(x_3);
lean::dec(x_3);
x_239 = x_237 == x_202;
if (x_239 == 0)
{
obj* x_241; obj* x_243; obj* x_244; obj* x_245; obj* x_247; 
lean::dec(x_9);
x_241 = l_lean_parser_parse__quoted__char___rarg___lambda__7___closed__1;
lean::inc(x_241);
x_243 = l_lean_parser_monad__parsec_unexpected__at___at_lean_parser_string__lit_view_value___spec__9___rarg(x_241, x_0, x_5);
x_244 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_243);
x_245 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_245);
x_247 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_245, x_244);
return x_247;
}
else
{
obj* x_249; 
lean::dec(x_0);
x_249 = lean::box(0);
x_10 = x_249;
goto lbl_11;
}
}
}
}
else
{
uint32 x_250; uint8 x_252; 
x_250 = lean::unbox_uint32(x_3);
lean::dec(x_3);
x_252 = x_250 == x_202;
if (x_252 == 0)
{
obj* x_254; obj* x_256; obj* x_257; obj* x_258; obj* x_260; 
lean::dec(x_9);
x_254 = l_lean_parser_parse__quoted__char___rarg___lambda__7___closed__1;
lean::inc(x_254);
x_256 = l_lean_parser_monad__parsec_unexpected__at___at_lean_parser_string__lit_view_value___spec__9___rarg(x_254, x_0, x_5);
x_257 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_256);
x_258 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_258);
x_260 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_258, x_257);
return x_260;
}
else
{
obj* x_262; 
lean::dec(x_0);
x_262 = lean::box(0);
x_10 = x_262;
goto lbl_11;
}
}
}
lbl_15:
{
obj* x_264; 
lean::dec(x_14);
x_264 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_view_value___spec__7(x_5);
if (lean::obj_tag(x_264) == 0)
{
obj* x_265; obj* x_267; obj* x_269; obj* x_271; obj* x_272; 
x_265 = lean::cnstr_get(x_264, 0);
lean::inc(x_265);
x_267 = lean::cnstr_get(x_264, 1);
lean::inc(x_267);
x_269 = lean::cnstr_get(x_264, 2);
lean::inc(x_269);
if (lean::is_shared(x_264)) {
 lean::dec(x_264);
 x_271 = lean::box(0);
} else {
 lean::cnstr_release(x_264, 0);
 lean::cnstr_release(x_264, 1);
 lean::cnstr_release(x_264, 2);
 x_271 = x_264;
}
x_272 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_view_value___spec__7(x_267);
if (lean::obj_tag(x_272) == 0)
{
obj* x_273; obj* x_275; obj* x_277; obj* x_280; obj* x_281; obj* x_284; uint32 x_287; uint32 x_289; uint8 x_290; 
x_273 = lean::cnstr_get(x_272, 0);
lean::inc(x_273);
x_275 = lean::cnstr_get(x_272, 1);
lean::inc(x_275);
x_277 = lean::cnstr_get(x_272, 2);
lean::inc(x_277);
lean::dec(x_272);
x_280 = lean::mk_nat_obj(16u);
x_281 = lean::nat_mul(x_280, x_265);
lean::dec(x_265);
lean::dec(x_280);
x_284 = lean::nat_add(x_281, x_273);
lean::dec(x_273);
lean::dec(x_281);
x_287 = lean::uint32_of_nat(x_284);
lean::dec(x_284);
x_289 = 55296;
x_290 = x_287 < x_289;
if (x_290 == 0)
{
uint32 x_291; uint8 x_292; 
x_291 = 57343;
x_292 = x_291 < x_287;
if (x_292 == 0)
{
uint32 x_293; obj* x_294; obj* x_295; obj* x_297; obj* x_298; obj* x_299; obj* x_300; obj* x_302; 
x_293 = 0;
x_294 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_295 = lean::box_uint32(x_293);
lean::inc(x_294);
if (lean::is_scalar(x_271)) {
 x_297 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_297 = x_271;
}
lean::cnstr_set(x_297, 0, x_295);
lean::cnstr_set(x_297, 1, x_275);
lean::cnstr_set(x_297, 2, x_294);
x_298 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_277, x_297);
x_299 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_269, x_298);
x_300 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_299);
lean::inc(x_294);
x_302 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_294, x_300);
return x_302;
}
else
{
uint32 x_303; uint8 x_304; 
x_303 = 1114112;
x_304 = x_287 < x_303;
if (x_304 == 0)
{
uint32 x_305; obj* x_306; obj* x_307; obj* x_309; obj* x_310; obj* x_311; obj* x_312; obj* x_314; 
x_305 = 0;
x_306 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_307 = lean::box_uint32(x_305);
lean::inc(x_306);
if (lean::is_scalar(x_271)) {
 x_309 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_309 = x_271;
}
lean::cnstr_set(x_309, 0, x_307);
lean::cnstr_set(x_309, 1, x_275);
lean::cnstr_set(x_309, 2, x_306);
x_310 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_277, x_309);
x_311 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_269, x_310);
x_312 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_311);
lean::inc(x_306);
x_314 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_306, x_312);
return x_314;
}
else
{
obj* x_315; obj* x_316; obj* x_318; obj* x_319; obj* x_320; obj* x_321; obj* x_323; 
x_315 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_316 = lean::box_uint32(x_287);
lean::inc(x_315);
if (lean::is_scalar(x_271)) {
 x_318 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_318 = x_271;
}
lean::cnstr_set(x_318, 0, x_316);
lean::cnstr_set(x_318, 1, x_275);
lean::cnstr_set(x_318, 2, x_315);
x_319 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_277, x_318);
x_320 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_269, x_319);
x_321 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_320);
lean::inc(x_315);
x_323 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_315, x_321);
return x_323;
}
}
}
else
{
obj* x_324; obj* x_325; obj* x_327; obj* x_328; obj* x_329; obj* x_330; obj* x_332; 
x_324 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_325 = lean::box_uint32(x_287);
lean::inc(x_324);
if (lean::is_scalar(x_271)) {
 x_327 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_327 = x_271;
}
lean::cnstr_set(x_327, 0, x_325);
lean::cnstr_set(x_327, 1, x_275);
lean::cnstr_set(x_327, 2, x_324);
x_328 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_277, x_327);
x_329 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_269, x_328);
x_330 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_329);
lean::inc(x_324);
x_332 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_324, x_330);
return x_332;
}
}
else
{
obj* x_335; uint8 x_337; obj* x_338; obj* x_339; obj* x_340; obj* x_341; obj* x_342; obj* x_343; obj* x_345; 
lean::dec(x_271);
lean::dec(x_265);
x_335 = lean::cnstr_get(x_272, 0);
lean::inc(x_335);
x_337 = lean::cnstr_get_scalar<uint8>(x_272, sizeof(void*)*1);
if (lean::is_shared(x_272)) {
 lean::dec(x_272);
 x_338 = lean::box(0);
} else {
 lean::cnstr_release(x_272, 0);
 x_338 = x_272;
}
if (lean::is_scalar(x_338)) {
 x_339 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_339 = x_338;
}
lean::cnstr_set(x_339, 0, x_335);
lean::cnstr_set_scalar(x_339, sizeof(void*)*1, x_337);
x_340 = x_339;
x_341 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_269, x_340);
x_342 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_341);
x_343 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_343);
x_345 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_343, x_342);
return x_345;
}
}
else
{
obj* x_346; uint8 x_348; obj* x_349; obj* x_350; obj* x_351; obj* x_352; obj* x_353; obj* x_355; 
x_346 = lean::cnstr_get(x_264, 0);
lean::inc(x_346);
x_348 = lean::cnstr_get_scalar<uint8>(x_264, sizeof(void*)*1);
if (lean::is_shared(x_264)) {
 lean::dec(x_264);
 x_349 = lean::box(0);
} else {
 lean::cnstr_release(x_264, 0);
 x_349 = x_264;
}
if (lean::is_scalar(x_349)) {
 x_350 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_350 = x_349;
}
lean::cnstr_set(x_350, 0, x_346);
lean::cnstr_set_scalar(x_350, sizeof(void*)*1, x_348);
x_351 = x_350;
x_352 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_351);
x_353 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_353);
x_355 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_353, x_352);
return x_355;
}
}
lbl_17:
{
uint32 x_357; uint32 x_358; uint8 x_359; 
lean::dec(x_16);
x_357 = 120;
x_358 = 55296;
x_359 = x_357 < x_358;
if (x_359 == 0)
{
uint32 x_360; uint8 x_361; 
x_360 = 57343;
x_361 = x_360 < x_357;
if (x_361 == 0)
{
uint32 x_362; uint32 x_363; uint8 x_364; 
x_362 = 0;
x_363 = lean::unbox_uint32(x_3);
x_364 = x_363 == x_362;
if (x_364 == 0)
{
obj* x_365; 
x_365 = lean::box(0);
x_12 = x_365;
goto lbl_13;
}
else
{
obj* x_369; 
lean::dec(x_9);
lean::dec(x_0);
lean::dec(x_3);
x_369 = lean::box(0);
x_14 = x_369;
goto lbl_15;
}
}
else
{
uint32 x_370; uint8 x_371; 
x_370 = 1114112;
x_371 = x_357 < x_370;
if (x_371 == 0)
{
uint32 x_372; uint32 x_373; uint8 x_374; 
x_372 = 0;
x_373 = lean::unbox_uint32(x_3);
x_374 = x_373 == x_372;
if (x_374 == 0)
{
obj* x_375; 
x_375 = lean::box(0);
x_12 = x_375;
goto lbl_13;
}
else
{
obj* x_379; 
lean::dec(x_9);
lean::dec(x_0);
lean::dec(x_3);
x_379 = lean::box(0);
x_14 = x_379;
goto lbl_15;
}
}
else
{
uint32 x_380; uint8 x_381; 
x_380 = lean::unbox_uint32(x_3);
x_381 = x_380 == x_357;
if (x_381 == 0)
{
obj* x_382; 
x_382 = lean::box(0);
x_12 = x_382;
goto lbl_13;
}
else
{
obj* x_386; 
lean::dec(x_9);
lean::dec(x_0);
lean::dec(x_3);
x_386 = lean::box(0);
x_14 = x_386;
goto lbl_15;
}
}
}
}
else
{
uint32 x_387; uint8 x_388; 
x_387 = lean::unbox_uint32(x_3);
x_388 = x_387 == x_357;
if (x_388 == 0)
{
obj* x_389; 
x_389 = lean::box(0);
x_12 = x_389;
goto lbl_13;
}
else
{
obj* x_393; 
lean::dec(x_9);
lean::dec(x_0);
lean::dec(x_3);
x_393 = lean::box(0);
x_14 = x_393;
goto lbl_15;
}
}
}
lbl_19:
{
uint32 x_395; uint32 x_396; uint8 x_397; 
lean::dec(x_18);
x_395 = 9;
x_396 = 55296;
x_397 = x_395 < x_396;
if (x_397 == 0)
{
uint32 x_398; uint8 x_399; 
x_398 = 57343;
x_399 = x_398 < x_395;
if (x_399 == 0)
{
uint32 x_400; obj* x_401; obj* x_402; obj* x_404; obj* x_405; obj* x_407; 
x_400 = 0;
x_401 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_402 = lean::box_uint32(x_400);
lean::inc(x_401);
x_404 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_404, 0, x_402);
lean::cnstr_set(x_404, 1, x_5);
lean::cnstr_set(x_404, 2, x_401);
x_405 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_404);
lean::inc(x_401);
x_407 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_401, x_405);
return x_407;
}
else
{
uint32 x_408; uint8 x_409; 
x_408 = 1114112;
x_409 = x_395 < x_408;
if (x_409 == 0)
{
uint32 x_410; obj* x_411; obj* x_412; obj* x_414; obj* x_415; obj* x_417; 
x_410 = 0;
x_411 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_412 = lean::box_uint32(x_410);
lean::inc(x_411);
x_414 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_414, 0, x_412);
lean::cnstr_set(x_414, 1, x_5);
lean::cnstr_set(x_414, 2, x_411);
x_415 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_414);
lean::inc(x_411);
x_417 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_411, x_415);
return x_417;
}
else
{
obj* x_418; obj* x_419; obj* x_421; obj* x_422; obj* x_424; 
x_418 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_419 = lean::box_uint32(x_395);
lean::inc(x_418);
x_421 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_421, 0, x_419);
lean::cnstr_set(x_421, 1, x_5);
lean::cnstr_set(x_421, 2, x_418);
x_422 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_421);
lean::inc(x_418);
x_424 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_418, x_422);
return x_424;
}
}
}
else
{
obj* x_425; obj* x_426; obj* x_428; obj* x_429; obj* x_431; 
x_425 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_426 = lean::box_uint32(x_395);
lean::inc(x_425);
x_428 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_428, 0, x_426);
lean::cnstr_set(x_428, 1, x_5);
lean::cnstr_set(x_428, 2, x_425);
x_429 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_428);
lean::inc(x_425);
x_431 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_425, x_429);
return x_431;
}
}
lbl_21:
{
uint32 x_433; uint32 x_434; uint8 x_435; 
lean::dec(x_20);
x_433 = 116;
x_434 = 55296;
x_435 = x_433 < x_434;
if (x_435 == 0)
{
uint32 x_436; uint8 x_437; 
x_436 = 57343;
x_437 = x_436 < x_433;
if (x_437 == 0)
{
uint32 x_438; uint32 x_439; uint8 x_440; 
x_438 = 0;
x_439 = lean::unbox_uint32(x_3);
x_440 = x_439 == x_438;
if (x_440 == 0)
{
obj* x_441; 
x_441 = lean::box(0);
x_16 = x_441;
goto lbl_17;
}
else
{
obj* x_445; 
lean::dec(x_9);
lean::dec(x_0);
lean::dec(x_3);
x_445 = lean::box(0);
x_18 = x_445;
goto lbl_19;
}
}
else
{
uint32 x_446; uint8 x_447; 
x_446 = 1114112;
x_447 = x_433 < x_446;
if (x_447 == 0)
{
uint32 x_448; uint32 x_449; uint8 x_450; 
x_448 = 0;
x_449 = lean::unbox_uint32(x_3);
x_450 = x_449 == x_448;
if (x_450 == 0)
{
obj* x_451; 
x_451 = lean::box(0);
x_16 = x_451;
goto lbl_17;
}
else
{
obj* x_455; 
lean::dec(x_9);
lean::dec(x_0);
lean::dec(x_3);
x_455 = lean::box(0);
x_18 = x_455;
goto lbl_19;
}
}
else
{
uint32 x_456; uint8 x_457; 
x_456 = lean::unbox_uint32(x_3);
x_457 = x_456 == x_433;
if (x_457 == 0)
{
obj* x_458; 
x_458 = lean::box(0);
x_16 = x_458;
goto lbl_17;
}
else
{
obj* x_462; 
lean::dec(x_9);
lean::dec(x_0);
lean::dec(x_3);
x_462 = lean::box(0);
x_18 = x_462;
goto lbl_19;
}
}
}
}
else
{
uint32 x_463; uint8 x_464; 
x_463 = lean::unbox_uint32(x_3);
x_464 = x_463 == x_433;
if (x_464 == 0)
{
obj* x_465; 
x_465 = lean::box(0);
x_16 = x_465;
goto lbl_17;
}
else
{
obj* x_469; 
lean::dec(x_9);
lean::dec(x_0);
lean::dec(x_3);
x_469 = lean::box(0);
x_18 = x_469;
goto lbl_19;
}
}
}
lbl_23:
{
uint32 x_471; uint32 x_472; uint8 x_473; 
lean::dec(x_22);
x_471 = 10;
x_472 = 55296;
x_473 = x_471 < x_472;
if (x_473 == 0)
{
uint32 x_474; uint8 x_475; 
x_474 = 57343;
x_475 = x_474 < x_471;
if (x_475 == 0)
{
uint32 x_476; obj* x_477; obj* x_478; obj* x_480; obj* x_481; obj* x_483; 
x_476 = 0;
x_477 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_478 = lean::box_uint32(x_476);
lean::inc(x_477);
x_480 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_480, 0, x_478);
lean::cnstr_set(x_480, 1, x_5);
lean::cnstr_set(x_480, 2, x_477);
x_481 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_480);
lean::inc(x_477);
x_483 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_477, x_481);
return x_483;
}
else
{
uint32 x_484; uint8 x_485; 
x_484 = 1114112;
x_485 = x_471 < x_484;
if (x_485 == 0)
{
uint32 x_486; obj* x_487; obj* x_488; obj* x_490; obj* x_491; obj* x_493; 
x_486 = 0;
x_487 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_488 = lean::box_uint32(x_486);
lean::inc(x_487);
x_490 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_490, 0, x_488);
lean::cnstr_set(x_490, 1, x_5);
lean::cnstr_set(x_490, 2, x_487);
x_491 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_490);
lean::inc(x_487);
x_493 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_487, x_491);
return x_493;
}
else
{
obj* x_494; obj* x_495; obj* x_497; obj* x_498; obj* x_500; 
x_494 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_495 = lean::box_uint32(x_471);
lean::inc(x_494);
x_497 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_497, 0, x_495);
lean::cnstr_set(x_497, 1, x_5);
lean::cnstr_set(x_497, 2, x_494);
x_498 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_497);
lean::inc(x_494);
x_500 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_494, x_498);
return x_500;
}
}
}
else
{
obj* x_501; obj* x_502; obj* x_504; obj* x_505; obj* x_507; 
x_501 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_502 = lean::box_uint32(x_471);
lean::inc(x_501);
x_504 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_504, 0, x_502);
lean::cnstr_set(x_504, 1, x_5);
lean::cnstr_set(x_504, 2, x_501);
x_505 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_504);
lean::inc(x_501);
x_507 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_501, x_505);
return x_507;
}
}
lbl_25:
{
uint32 x_509; uint32 x_510; uint8 x_511; 
lean::dec(x_24);
x_509 = 110;
x_510 = 55296;
x_511 = x_509 < x_510;
if (x_511 == 0)
{
uint32 x_512; uint8 x_513; 
x_512 = 57343;
x_513 = x_512 < x_509;
if (x_513 == 0)
{
uint32 x_514; uint32 x_515; uint8 x_516; 
x_514 = 0;
x_515 = lean::unbox_uint32(x_3);
x_516 = x_515 == x_514;
if (x_516 == 0)
{
obj* x_517; 
x_517 = lean::box(0);
x_20 = x_517;
goto lbl_21;
}
else
{
obj* x_521; 
lean::dec(x_9);
lean::dec(x_0);
lean::dec(x_3);
x_521 = lean::box(0);
x_22 = x_521;
goto lbl_23;
}
}
else
{
uint32 x_522; uint8 x_523; 
x_522 = 1114112;
x_523 = x_509 < x_522;
if (x_523 == 0)
{
uint32 x_524; uint32 x_525; uint8 x_526; 
x_524 = 0;
x_525 = lean::unbox_uint32(x_3);
x_526 = x_525 == x_524;
if (x_526 == 0)
{
obj* x_527; 
x_527 = lean::box(0);
x_20 = x_527;
goto lbl_21;
}
else
{
obj* x_531; 
lean::dec(x_9);
lean::dec(x_0);
lean::dec(x_3);
x_531 = lean::box(0);
x_22 = x_531;
goto lbl_23;
}
}
else
{
uint32 x_532; uint8 x_533; 
x_532 = lean::unbox_uint32(x_3);
x_533 = x_532 == x_509;
if (x_533 == 0)
{
obj* x_534; 
x_534 = lean::box(0);
x_20 = x_534;
goto lbl_21;
}
else
{
obj* x_538; 
lean::dec(x_9);
lean::dec(x_0);
lean::dec(x_3);
x_538 = lean::box(0);
x_22 = x_538;
goto lbl_23;
}
}
}
}
else
{
uint32 x_539; uint8 x_540; 
x_539 = lean::unbox_uint32(x_3);
x_540 = x_539 == x_509;
if (x_540 == 0)
{
obj* x_541; 
x_541 = lean::box(0);
x_20 = x_541;
goto lbl_21;
}
else
{
obj* x_545; 
lean::dec(x_9);
lean::dec(x_0);
lean::dec(x_3);
x_545 = lean::box(0);
x_22 = x_545;
goto lbl_23;
}
}
}
lbl_27:
{
uint32 x_547; uint32 x_548; uint8 x_549; uint32 x_550; 
lean::dec(x_26);
x_547 = 39;
x_548 = 55296;
x_549 = x_547 < x_548;
if (x_549 == 0)
{
uint32 x_552; uint8 x_553; 
x_552 = 57343;
x_553 = x_552 < x_547;
if (x_553 == 0)
{
uint32 x_554; 
x_554 = 0;
x_550 = x_554;
goto lbl_551;
}
else
{
uint32 x_555; uint8 x_556; 
x_555 = 1114112;
x_556 = x_547 < x_555;
if (x_556 == 0)
{
uint32 x_557; 
x_557 = 0;
x_550 = x_557;
goto lbl_551;
}
else
{
x_550 = x_547;
goto lbl_551;
}
}
}
else
{
x_550 = x_547;
goto lbl_551;
}
lbl_551:
{
uint32 x_558; uint8 x_559; 
x_558 = lean::unbox_uint32(x_3);
x_559 = x_558 == x_550;
if (x_559 == 0)
{
obj* x_560; 
x_560 = lean::box(0);
x_24 = x_560;
goto lbl_25;
}
else
{
obj* x_564; obj* x_565; obj* x_567; obj* x_568; obj* x_570; 
lean::dec(x_9);
lean::dec(x_0);
lean::dec(x_3);
x_564 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_565 = lean::box_uint32(x_550);
lean::inc(x_564);
x_567 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_567, 0, x_565);
lean::cnstr_set(x_567, 1, x_5);
lean::cnstr_set(x_567, 2, x_564);
x_568 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_567);
lean::inc(x_564);
x_570 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_564, x_568);
return x_570;
}
}
}
lbl_29:
{
uint32 x_572; uint32 x_573; uint8 x_574; uint32 x_575; 
lean::dec(x_28);
x_572 = 34;
x_573 = 55296;
x_574 = x_572 < x_573;
if (x_574 == 0)
{
uint32 x_577; uint8 x_578; 
x_577 = 57343;
x_578 = x_577 < x_572;
if (x_578 == 0)
{
uint32 x_579; 
x_579 = 0;
x_575 = x_579;
goto lbl_576;
}
else
{
uint32 x_580; uint8 x_581; 
x_580 = 1114112;
x_581 = x_572 < x_580;
if (x_581 == 0)
{
uint32 x_582; 
x_582 = 0;
x_575 = x_582;
goto lbl_576;
}
else
{
x_575 = x_572;
goto lbl_576;
}
}
}
else
{
x_575 = x_572;
goto lbl_576;
}
lbl_576:
{
uint32 x_583; uint8 x_584; 
x_583 = lean::unbox_uint32(x_3);
x_584 = x_583 == x_575;
if (x_584 == 0)
{
obj* x_585; 
x_585 = lean::box(0);
x_26 = x_585;
goto lbl_27;
}
else
{
obj* x_589; obj* x_590; obj* x_592; obj* x_593; obj* x_595; 
lean::dec(x_9);
lean::dec(x_0);
lean::dec(x_3);
x_589 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_590 = lean::box_uint32(x_575);
lean::inc(x_589);
x_592 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_592, 0, x_590);
lean::cnstr_set(x_592, 1, x_5);
lean::cnstr_set(x_592, 2, x_589);
x_593 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_592);
lean::inc(x_589);
x_595 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_589, x_593);
return x_595;
}
}
}
lbl_34:
{
uint32 x_596; uint8 x_597; 
x_596 = lean::unbox_uint32(x_3);
x_597 = x_596 == x_33;
if (x_597 == 0)
{
obj* x_598; 
x_598 = lean::box(0);
x_28 = x_598;
goto lbl_29;
}
else
{
obj* x_602; obj* x_603; obj* x_605; obj* x_606; obj* x_608; 
lean::dec(x_9);
lean::dec(x_0);
lean::dec(x_3);
x_602 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_603 = lean::box_uint32(x_33);
lean::inc(x_602);
x_605 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_605, 0, x_603);
lean::cnstr_set(x_605, 1, x_5);
lean::cnstr_set(x_605, 2, x_602);
x_606 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_605);
lean::inc(x_602);
x_608 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_602, x_606);
return x_608;
}
}
}
else
{
obj* x_610; uint8 x_612; obj* x_613; obj* x_614; obj* x_615; obj* x_616; obj* x_618; 
lean::dec(x_0);
x_610 = lean::cnstr_get(x_2, 0);
lean::inc(x_610);
x_612 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*1);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_613 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 x_613 = x_2;
}
if (lean::is_scalar(x_613)) {
 x_614 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_614 = x_613;
}
lean::cnstr_set(x_614, 0, x_610);
lean::cnstr_set_scalar(x_614, sizeof(void*)*1, x_612);
x_615 = x_614;
x_616 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_616);
x_618 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_616, x_615);
return x_618;
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
obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_14; obj* x_15; obj* x_18; uint32 x_20; uint32 x_21; uint8 x_22; uint32 x_23; 
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
x_20 = 92;
x_21 = 55296;
x_22 = x_20 < x_21;
if (x_22 == 0)
{
uint32 x_25; uint8 x_26; 
x_25 = 57343;
x_26 = x_25 < x_20;
if (x_26 == 0)
{
uint32 x_27; 
x_27 = 0;
x_23 = x_27;
goto lbl_24;
}
else
{
uint32 x_28; uint8 x_29; 
x_28 = 1114112;
x_29 = x_20 < x_28;
if (x_29 == 0)
{
uint32 x_30; 
x_30 = 0;
x_23 = x_30;
goto lbl_24;
}
else
{
x_23 = x_20;
goto lbl_24;
}
}
}
else
{
x_23 = x_20;
goto lbl_24;
}
lbl_19:
{
uint32 x_32; uint32 x_33; uint8 x_34; uint32 x_35; 
lean::dec(x_18);
x_32 = 34;
x_33 = 55296;
x_34 = x_32 < x_33;
if (x_34 == 0)
{
uint32 x_37; uint8 x_38; 
x_37 = 57343;
x_38 = x_37 < x_32;
if (x_38 == 0)
{
uint32 x_39; 
x_39 = 0;
x_35 = x_39;
goto lbl_36;
}
else
{
uint32 x_40; uint8 x_41; 
x_40 = 1114112;
x_41 = x_32 < x_40;
if (x_41 == 0)
{
uint32 x_42; 
x_42 = 0;
x_35 = x_42;
goto lbl_36;
}
else
{
x_35 = x_32;
goto lbl_36;
}
}
}
else
{
x_35 = x_32;
goto lbl_36;
}
lbl_36:
{
uint32 x_43; uint8 x_45; 
x_43 = lean::unbox_uint32(x_7);
lean::dec(x_7);
x_45 = x_43 == x_35;
if (x_45 == 0)
{
obj* x_47; obj* x_48; obj* x_49; 
lean::dec(x_13);
x_47 = lean::string_push(x_1, x_43);
x_48 = l_lean_parser_parse__string__literal__aux___main___at_lean_parser_string__lit_view_value___spec__4(x_15, x_47, x_9);
x_49 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_11, x_48);
return x_49;
}
else
{
obj* x_51; obj* x_53; obj* x_54; 
lean::dec(x_15);
x_51 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_51);
if (lean::is_scalar(x_13)) {
 x_53 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_53 = x_13;
}
lean::cnstr_set(x_53, 0, x_1);
lean::cnstr_set(x_53, 1, x_9);
lean::cnstr_set(x_53, 2, x_51);
x_54 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_11, x_53);
return x_54;
}
}
}
lbl_24:
{
uint32 x_55; uint8 x_56; 
x_55 = lean::unbox_uint32(x_7);
x_56 = x_55 == x_23;
if (x_56 == 0)
{
obj* x_57; 
x_57 = lean::box(0);
x_18 = x_57;
goto lbl_19;
}
else
{
obj* x_60; 
lean::dec(x_13);
lean::dec(x_7);
x_60 = l_lean_parser_parse__quoted__char___at_lean_parser_string__lit_view_value___spec__6(x_9);
if (lean::obj_tag(x_60) == 0)
{
obj* x_61; obj* x_63; obj* x_65; uint32 x_68; obj* x_70; obj* x_71; obj* x_72; obj* x_73; 
x_61 = lean::cnstr_get(x_60, 0);
lean::inc(x_61);
x_63 = lean::cnstr_get(x_60, 1);
lean::inc(x_63);
x_65 = lean::cnstr_get(x_60, 2);
lean::inc(x_65);
lean::dec(x_60);
x_68 = lean::unbox_uint32(x_61);
lean::dec(x_61);
x_70 = lean::string_push(x_1, x_68);
x_71 = l_lean_parser_parse__string__literal__aux___main___at_lean_parser_string__lit_view_value___spec__4(x_15, x_70, x_63);
x_72 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_65, x_71);
x_73 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_11, x_72);
return x_73;
}
else
{
obj* x_76; uint8 x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; 
lean::dec(x_15);
lean::dec(x_1);
x_76 = lean::cnstr_get(x_60, 0);
lean::inc(x_76);
x_78 = lean::cnstr_get_scalar<uint8>(x_60, sizeof(void*)*1);
if (lean::is_shared(x_60)) {
 lean::dec(x_60);
 x_79 = lean::box(0);
} else {
 lean::cnstr_release(x_60, 0);
 x_79 = x_60;
}
if (lean::is_scalar(x_79)) {
 x_80 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_80 = x_79;
}
lean::cnstr_set(x_80, 0, x_76);
lean::cnstr_set_scalar(x_80, sizeof(void*)*1, x_78);
x_81 = x_80;
x_82 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_11, x_81);
return x_82;
}
}
}
}
else
{
obj* x_85; uint8 x_87; obj* x_88; obj* x_89; obj* x_90; 
lean::dec(x_1);
lean::dec(x_0);
x_85 = lean::cnstr_get(x_6, 0);
lean::inc(x_85);
x_87 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*1);
if (lean::is_shared(x_6)) {
 lean::dec(x_6);
 x_88 = lean::box(0);
} else {
 lean::cnstr_release(x_6, 0);
 x_88 = x_6;
}
if (lean::is_scalar(x_88)) {
 x_89 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_89 = x_88;
}
lean::cnstr_set(x_89, 0, x_85);
lean::cnstr_set_scalar(x_89, sizeof(void*)*1, x_87);
x_90 = x_89;
return x_90;
}
}
else
{
uint32 x_92; uint32 x_93; uint8 x_94; 
lean::dec(x_0);
x_92 = 34;
x_93 = 55296;
x_94 = x_92 < x_93;
if (x_94 == 0)
{
uint32 x_95; uint8 x_96; 
x_95 = 57343;
x_96 = x_95 < x_92;
if (x_96 == 0)
{
uint32 x_97; obj* x_98; 
x_97 = 0;
x_98 = l_lean_parser_monad__parsec_ch___at_lean_parser_string__lit_view_value___spec__2(x_97, x_2);
if (lean::obj_tag(x_98) == 0)
{
obj* x_99; obj* x_101; obj* x_103; obj* x_104; obj* x_106; obj* x_107; 
x_99 = lean::cnstr_get(x_98, 1);
lean::inc(x_99);
x_101 = lean::cnstr_get(x_98, 2);
lean::inc(x_101);
if (lean::is_shared(x_98)) {
 lean::dec(x_98);
 x_103 = lean::box(0);
} else {
 lean::cnstr_release(x_98, 0);
 lean::cnstr_release(x_98, 1);
 lean::cnstr_release(x_98, 2);
 x_103 = x_98;
}
x_104 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_104);
if (lean::is_scalar(x_103)) {
 x_106 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_106 = x_103;
}
lean::cnstr_set(x_106, 0, x_1);
lean::cnstr_set(x_106, 1, x_99);
lean::cnstr_set(x_106, 2, x_104);
x_107 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_101, x_106);
return x_107;
}
else
{
obj* x_109; uint8 x_111; obj* x_112; obj* x_113; obj* x_114; 
lean::dec(x_1);
x_109 = lean::cnstr_get(x_98, 0);
lean::inc(x_109);
x_111 = lean::cnstr_get_scalar<uint8>(x_98, sizeof(void*)*1);
if (lean::is_shared(x_98)) {
 lean::dec(x_98);
 x_112 = lean::box(0);
} else {
 lean::cnstr_release(x_98, 0);
 x_112 = x_98;
}
if (lean::is_scalar(x_112)) {
 x_113 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_113 = x_112;
}
lean::cnstr_set(x_113, 0, x_109);
lean::cnstr_set_scalar(x_113, sizeof(void*)*1, x_111);
x_114 = x_113;
return x_114;
}
}
else
{
uint32 x_115; uint8 x_116; 
x_115 = 1114112;
x_116 = x_92 < x_115;
if (x_116 == 0)
{
uint32 x_117; obj* x_118; 
x_117 = 0;
x_118 = l_lean_parser_monad__parsec_ch___at_lean_parser_string__lit_view_value___spec__2(x_117, x_2);
if (lean::obj_tag(x_118) == 0)
{
obj* x_119; obj* x_121; obj* x_123; obj* x_124; obj* x_126; obj* x_127; 
x_119 = lean::cnstr_get(x_118, 1);
lean::inc(x_119);
x_121 = lean::cnstr_get(x_118, 2);
lean::inc(x_121);
if (lean::is_shared(x_118)) {
 lean::dec(x_118);
 x_123 = lean::box(0);
} else {
 lean::cnstr_release(x_118, 0);
 lean::cnstr_release(x_118, 1);
 lean::cnstr_release(x_118, 2);
 x_123 = x_118;
}
x_124 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_124);
if (lean::is_scalar(x_123)) {
 x_126 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_126 = x_123;
}
lean::cnstr_set(x_126, 0, x_1);
lean::cnstr_set(x_126, 1, x_119);
lean::cnstr_set(x_126, 2, x_124);
x_127 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_121, x_126);
return x_127;
}
else
{
obj* x_129; uint8 x_131; obj* x_132; obj* x_133; obj* x_134; 
lean::dec(x_1);
x_129 = lean::cnstr_get(x_118, 0);
lean::inc(x_129);
x_131 = lean::cnstr_get_scalar<uint8>(x_118, sizeof(void*)*1);
if (lean::is_shared(x_118)) {
 lean::dec(x_118);
 x_132 = lean::box(0);
} else {
 lean::cnstr_release(x_118, 0);
 x_132 = x_118;
}
if (lean::is_scalar(x_132)) {
 x_133 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_133 = x_132;
}
lean::cnstr_set(x_133, 0, x_129);
lean::cnstr_set_scalar(x_133, sizeof(void*)*1, x_131);
x_134 = x_133;
return x_134;
}
}
else
{
obj* x_135; 
x_135 = l_lean_parser_monad__parsec_ch___at_lean_parser_string__lit_view_value___spec__2(x_92, x_2);
if (lean::obj_tag(x_135) == 0)
{
obj* x_136; obj* x_138; obj* x_140; obj* x_141; obj* x_143; obj* x_144; 
x_136 = lean::cnstr_get(x_135, 1);
lean::inc(x_136);
x_138 = lean::cnstr_get(x_135, 2);
lean::inc(x_138);
if (lean::is_shared(x_135)) {
 lean::dec(x_135);
 x_140 = lean::box(0);
} else {
 lean::cnstr_release(x_135, 0);
 lean::cnstr_release(x_135, 1);
 lean::cnstr_release(x_135, 2);
 x_140 = x_135;
}
x_141 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_141);
if (lean::is_scalar(x_140)) {
 x_143 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_143 = x_140;
}
lean::cnstr_set(x_143, 0, x_1);
lean::cnstr_set(x_143, 1, x_136);
lean::cnstr_set(x_143, 2, x_141);
x_144 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_138, x_143);
return x_144;
}
else
{
obj* x_146; uint8 x_148; obj* x_149; obj* x_150; obj* x_151; 
lean::dec(x_1);
x_146 = lean::cnstr_get(x_135, 0);
lean::inc(x_146);
x_148 = lean::cnstr_get_scalar<uint8>(x_135, sizeof(void*)*1);
if (lean::is_shared(x_135)) {
 lean::dec(x_135);
 x_149 = lean::box(0);
} else {
 lean::cnstr_release(x_135, 0);
 x_149 = x_135;
}
if (lean::is_scalar(x_149)) {
 x_150 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_150 = x_149;
}
lean::cnstr_set(x_150, 0, x_146);
lean::cnstr_set_scalar(x_150, sizeof(void*)*1, x_148);
x_151 = x_150;
return x_151;
}
}
}
}
else
{
obj* x_152; 
x_152 = l_lean_parser_monad__parsec_ch___at_lean_parser_string__lit_view_value___spec__2(x_92, x_2);
if (lean::obj_tag(x_152) == 0)
{
obj* x_153; obj* x_155; obj* x_157; obj* x_158; obj* x_160; obj* x_161; 
x_153 = lean::cnstr_get(x_152, 1);
lean::inc(x_153);
x_155 = lean::cnstr_get(x_152, 2);
lean::inc(x_155);
if (lean::is_shared(x_152)) {
 lean::dec(x_152);
 x_157 = lean::box(0);
} else {
 lean::cnstr_release(x_152, 0);
 lean::cnstr_release(x_152, 1);
 lean::cnstr_release(x_152, 2);
 x_157 = x_152;
}
x_158 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_158);
if (lean::is_scalar(x_157)) {
 x_160 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_160 = x_157;
}
lean::cnstr_set(x_160, 0, x_1);
lean::cnstr_set(x_160, 1, x_153);
lean::cnstr_set(x_160, 2, x_158);
x_161 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_155, x_160);
return x_161;
}
else
{
obj* x_163; uint8 x_165; obj* x_166; obj* x_167; obj* x_168; 
lean::dec(x_1);
x_163 = lean::cnstr_get(x_152, 0);
lean::inc(x_163);
x_165 = lean::cnstr_get_scalar<uint8>(x_152, sizeof(void*)*1);
if (lean::is_shared(x_152)) {
 lean::dec(x_152);
 x_166 = lean::box(0);
} else {
 lean::cnstr_release(x_152, 0);
 x_166 = x_152;
}
if (lean::is_scalar(x_166)) {
 x_167 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_167 = x_166;
}
lean::cnstr_set(x_167, 0, x_163);
lean::cnstr_set_scalar(x_167, sizeof(void*)*1, x_165);
x_168 = x_167;
return x_168;
}
}
}
}
}
obj* l_lean_parser_parse__string__literal___at_lean_parser_string__lit_view_value___spec__1(obj* x_0) {
_start:
{
uint32 x_1; uint32 x_2; uint8 x_3; 
x_1 = 34;
x_2 = 55296;
x_3 = x_1 < x_2;
if (x_3 == 0)
{
uint32 x_4; uint8 x_5; 
x_4 = 57343;
x_5 = x_4 < x_1;
if (x_5 == 0)
{
uint32 x_6; obj* x_7; 
x_6 = 0;
x_7 = l_lean_parser_monad__parsec_ch___at_lean_parser_string__lit_view_value___spec__2(x_6, x_0);
if (lean::obj_tag(x_7) == 0)
{
obj* x_8; obj* x_10; obj* x_13; obj* x_14; obj* x_16; obj* x_17; obj* x_19; obj* x_20; 
x_8 = lean::cnstr_get(x_7, 1);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_7, 2);
lean::inc(x_10);
lean::dec(x_7);
x_13 = lean::string_iterator_remaining(x_8);
x_14 = l_string_join___closed__1;
lean::inc(x_14);
x_16 = l_lean_parser_parse__string__literal__aux___main___at_lean_parser_string__lit_view_value___spec__4(x_13, x_14, x_8);
x_17 = l_lean_parser_finish__comment__block___closed__2;
lean::inc(x_17);
x_19 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_17, x_16);
x_20 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_10, x_19);
return x_20;
}
else
{
obj* x_21; uint8 x_23; obj* x_24; obj* x_25; obj* x_26; 
x_21 = lean::cnstr_get(x_7, 0);
lean::inc(x_21);
x_23 = lean::cnstr_get_scalar<uint8>(x_7, sizeof(void*)*1);
if (lean::is_shared(x_7)) {
 lean::dec(x_7);
 x_24 = lean::box(0);
} else {
 lean::cnstr_release(x_7, 0);
 x_24 = x_7;
}
if (lean::is_scalar(x_24)) {
 x_25 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_25 = x_24;
}
lean::cnstr_set(x_25, 0, x_21);
lean::cnstr_set_scalar(x_25, sizeof(void*)*1, x_23);
x_26 = x_25;
return x_26;
}
}
else
{
uint32 x_27; uint8 x_28; 
x_27 = 1114112;
x_28 = x_1 < x_27;
if (x_28 == 0)
{
uint32 x_29; obj* x_30; 
x_29 = 0;
x_30 = l_lean_parser_monad__parsec_ch___at_lean_parser_string__lit_view_value___spec__2(x_29, x_0);
if (lean::obj_tag(x_30) == 0)
{
obj* x_31; obj* x_33; obj* x_36; obj* x_37; obj* x_39; obj* x_40; obj* x_42; obj* x_43; 
x_31 = lean::cnstr_get(x_30, 1);
lean::inc(x_31);
x_33 = lean::cnstr_get(x_30, 2);
lean::inc(x_33);
lean::dec(x_30);
x_36 = lean::string_iterator_remaining(x_31);
x_37 = l_string_join___closed__1;
lean::inc(x_37);
x_39 = l_lean_parser_parse__string__literal__aux___main___at_lean_parser_string__lit_view_value___spec__4(x_36, x_37, x_31);
x_40 = l_lean_parser_finish__comment__block___closed__2;
lean::inc(x_40);
x_42 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_40, x_39);
x_43 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_33, x_42);
return x_43;
}
else
{
obj* x_44; uint8 x_46; obj* x_47; obj* x_48; obj* x_49; 
x_44 = lean::cnstr_get(x_30, 0);
lean::inc(x_44);
x_46 = lean::cnstr_get_scalar<uint8>(x_30, sizeof(void*)*1);
if (lean::is_shared(x_30)) {
 lean::dec(x_30);
 x_47 = lean::box(0);
} else {
 lean::cnstr_release(x_30, 0);
 x_47 = x_30;
}
if (lean::is_scalar(x_47)) {
 x_48 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_48 = x_47;
}
lean::cnstr_set(x_48, 0, x_44);
lean::cnstr_set_scalar(x_48, sizeof(void*)*1, x_46);
x_49 = x_48;
return x_49;
}
}
else
{
obj* x_50; 
x_50 = l_lean_parser_monad__parsec_ch___at_lean_parser_string__lit_view_value___spec__2(x_1, x_0);
if (lean::obj_tag(x_50) == 0)
{
obj* x_51; obj* x_53; obj* x_56; obj* x_57; obj* x_59; obj* x_60; obj* x_62; obj* x_63; 
x_51 = lean::cnstr_get(x_50, 1);
lean::inc(x_51);
x_53 = lean::cnstr_get(x_50, 2);
lean::inc(x_53);
lean::dec(x_50);
x_56 = lean::string_iterator_remaining(x_51);
x_57 = l_string_join___closed__1;
lean::inc(x_57);
x_59 = l_lean_parser_parse__string__literal__aux___main___at_lean_parser_string__lit_view_value___spec__4(x_56, x_57, x_51);
x_60 = l_lean_parser_finish__comment__block___closed__2;
lean::inc(x_60);
x_62 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_60, x_59);
x_63 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_53, x_62);
return x_63;
}
else
{
obj* x_64; uint8 x_66; obj* x_67; obj* x_68; obj* x_69; 
x_64 = lean::cnstr_get(x_50, 0);
lean::inc(x_64);
x_66 = lean::cnstr_get_scalar<uint8>(x_50, sizeof(void*)*1);
if (lean::is_shared(x_50)) {
 lean::dec(x_50);
 x_67 = lean::box(0);
} else {
 lean::cnstr_release(x_50, 0);
 x_67 = x_50;
}
if (lean::is_scalar(x_67)) {
 x_68 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_68 = x_67;
}
lean::cnstr_set(x_68, 0, x_64);
lean::cnstr_set_scalar(x_68, sizeof(void*)*1, x_66);
x_69 = x_68;
return x_69;
}
}
}
}
else
{
obj* x_70; 
x_70 = l_lean_parser_monad__parsec_ch___at_lean_parser_string__lit_view_value___spec__2(x_1, x_0);
if (lean::obj_tag(x_70) == 0)
{
obj* x_71; obj* x_73; obj* x_76; obj* x_77; obj* x_79; obj* x_80; obj* x_82; obj* x_83; 
x_71 = lean::cnstr_get(x_70, 1);
lean::inc(x_71);
x_73 = lean::cnstr_get(x_70, 2);
lean::inc(x_73);
lean::dec(x_70);
x_76 = lean::string_iterator_remaining(x_71);
x_77 = l_string_join___closed__1;
lean::inc(x_77);
x_79 = l_lean_parser_parse__string__literal__aux___main___at_lean_parser_string__lit_view_value___spec__4(x_76, x_77, x_71);
x_80 = l_lean_parser_finish__comment__block___closed__2;
lean::inc(x_80);
x_82 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_80, x_79);
x_83 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_73, x_82);
return x_83;
}
else
{
obj* x_84; uint8 x_86; obj* x_87; obj* x_88; obj* x_89; 
x_84 = lean::cnstr_get(x_70, 0);
lean::inc(x_84);
x_86 = lean::cnstr_get_scalar<uint8>(x_70, sizeof(void*)*1);
if (lean::is_shared(x_70)) {
 lean::dec(x_70);
 x_87 = lean::box(0);
} else {
 lean::cnstr_release(x_70, 0);
 x_87 = x_70;
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
