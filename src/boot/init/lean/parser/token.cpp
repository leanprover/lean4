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
obj* l_lean_parser_monad__parsec_take__while_x_27___at___private_init_lean_parser_token_2__whitespace__aux___main___spec__2___boxed(obj*);
obj* l_lean_parser_detail__ident__suffix_parser_lean_parser_has__view___lambda__2(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__16(obj*, obj*, obj*);
obj* l_lean_parser_detail__ident__part_parser_lean_parser_has__tokens;
obj* l_lean_parser_finish__comment__block___boxed(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__28(obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__22(obj*, obj*, obj*);
obj* l_list_mfoldr___main___at_lean_parser_number_x_27___spec__13(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_with__trailing___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser___spec__10(obj*);
obj* l_lean_parser_ident_parser_view___rarg___lambda__1___boxed(obj*);
obj* l_reader__t_orelse___at_lean_parser_parse__bin__lit___spec__1___boxed(obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__4(obj*, obj*, obj*, obj*);
obj* l_lean_parser_parsec__t_bind__mk__res___rarg(obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while1___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__1(obj*, obj*, obj*);
obj* l_reader__t_orelse___at_lean_parser_parse__bin__lit___spec__1(obj*);
obj* l_lean_parser_unicode__symbol_lean_parser_has__tokens(obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while_x_27___at___private_init_lean_parser_token_2__whitespace__aux___main___spec__5___boxed(obj*);
obj* l_lean_parser_as__substring___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_many1__aux_x_27___main___at_lean_parser_parse__bin__lit___spec__2___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__6(uint32, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__6___boxed(obj*, obj*, obj*, obj*);
uint8 l_char_is__whitespace(uint32);
obj* l_lean_parser_monad__parsec_take__while1___at_lean_parser_parse__oct__lit___spec__1___boxed(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__19___rarg(obj*, obj*);
extern obj* l_lean_parser_parse__hex__digit___rarg___lambda__5___closed__1;
obj* l_lean_parser_id__part___at___private_init_lean_parser_token_4__ident_x_27___spec__1(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_foldl__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__21___lambda__2___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__9(obj*, obj*, obj*);
obj* l_lean_parser_trie_match__prefix___rarg(obj*, obj*);
obj* l_lean_parser_string__lit_parser_view___boxed(obj*);
obj* l_lean_parser_detail__ident__suffix_has__view;
obj* l_lean_parser_match__token(obj*, obj*, obj*);
obj* l_lean_parser_with__trailing___boxed(obj*);
obj* l_lean_parser_number_parser_view___rarg___closed__2;
extern uint8 l_true_decidable;
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser___spec__8(obj*);
obj* l_lean_parser_number_x_27___closed__1;
obj* l___private_init_lean_parser_parsec_6__take__while__aux_x_27___main___at___private_init_lean_parser_token_2__whitespace__aux___main___spec__6(obj*, uint8, obj*);
obj* l_lean_parser_monad__parsec_str__core___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__3(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_symbol__core___at_lean_parser_unicode__symbol_lean_parser_has__tokens___spec__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__3___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_raw_view___rarg(obj*, obj*, obj*, obj*, obj*, uint8);
obj* l_lean_parser_detail__ident__part_has__view;
extern obj* l_lean_parser_parse__hex__digit___rarg___lambda__3___closed__1;
obj* l_lean_parser_detail__ident__part_has__view_x_27___lambda__1___closed__2;
obj* l_lean_parser_number_has__view_x_27___lambda__2___closed__1;
obj* l_lean_parser_detail__ident__part__escaped_has__view_x_27___lambda__2___closed__3;
obj* l_lean_parser_monad__parsec_error___at_lean_parser_number_x_27___spec__12___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_raw___rarg___lambda__3(uint8, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_finish__comment__block___closed__1;
obj* l_lean_parser_monad__parsec_error___at_lean_parser_string__lit_view_value___spec__3(obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__2(uint32, obj*, obj*, obj*);
obj* l_lean_parser_combinators_node___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__9(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_number;
obj* l_reader__t_orelse___at_lean_parser_parse__bin__lit___spec__1___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_detail__ident__suffix_parser_lean_parser_has__view___lambda__1___boxed(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_token_4__ident_x_27(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1(obj*);
obj* l_lean_parser_raw__str_view__default___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__2___boxed(obj*);
extern obj* l_lean_parser_combinators_many___rarg___closed__1;
obj* l_lean_parser_symbol__or__ident___rarg(obj*, obj*);
obj* l_lean_parser_raw__str_view__default(obj*);
obj* l_lean_parser_as__substring___rarg___lambda__2(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_token_1__finish__comment__block__aux___main(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__21(obj*);
obj* l_lean_parser_monad__parsec_take__while1___at_lean_parser_detail__ident__part_parser___spec__1(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_many1__aux_x_27___main___at_lean_parser_parse__bin__lit___spec__2(obj*, obj*, obj*, obj*);
obj* l_lean_parser_raw___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__21___boxed(obj*);
obj* l_lean_parser_monad__parsec_take__while1___at_lean_parser_parse__hex__lit___spec__1___boxed(obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__12(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_unexpected__at___at_lean_parser_string__lit_view_value___spec__7(obj*);
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__19(obj*);
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__27___boxed(obj*);
obj* l_lean_parser_ident_parser_view___rarg___lambda__1___closed__2;
obj* l_lean_parser_raw_view___rarg___lambda__2(obj*);
obj* l_lean_parser_detail__ident_parser___closed__1;
obj* l_lean_parser_parsec__t_lookahead___at___private_init_lean_parser_token_2__whitespace__aux___main___spec__4___closed__2;
namespace lean {
obj* nat_add(obj*, obj*);
}
extern obj* l_lean_parser_parse__quoted__char___rarg___lambda__7___closed__1;
obj* l_rbmap_find___main___at_lean_parser_indexed___spec__5___boxed(obj*);
obj* l_lean_parser_monad__parsec_str__core___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__6(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__4(obj*, obj*, obj*, obj*);
obj* l_lean_parser_parsec__t_lookahead___at_lean_parser_detail__ident__suffix_parser___spec__1(obj*, obj*, obj*, obj*);
obj* l_lean_parser_indexed(obj*);
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__20(obj*, obj*, obj*);
obj* l_lean_parser_string__lit_parser___rarg(obj*);
obj* l_lean_parser_symbol__core___rarg(obj*, obj*, obj*, obj*);
obj* l_reader__t_lift___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__5___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_reader__t_lift___at_lean_parser_with__trailing___spec__1___rarg(obj*, obj*, obj*, obj*);
extern obj* l_mjoin___rarg___closed__1;
obj* l_lean_parser_string__lit_parser_tokens(obj*, obj*);
obj* l_lean_parser_string__lit_parser___rarg___closed__1;
obj* l_lean_parser_ident_parser_tokens___boxed(obj*, obj*);
obj* l_lean_parser_symbol_tokens___boxed(obj*, obj*);
obj* l_reader__t_lift___at_lean_parser_with__trailing___spec__1___boxed(obj*);
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__9(obj*, obj*, obj*);
extern uint32 l_lean_id__end__escape;
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__18(obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser___spec__11(obj*, obj*, obj*);
obj* l_lean_parser_number_view_to__nat(obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_init_lean_parser_token_4__ident_x_27___spec__4___boxed(obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_basic__parser__m_monad;
obj* l_reader__t_bind___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__7___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__6___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_ident_parser_view___rarg(obj*);
obj* l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__5___boxed(obj*, obj*, obj*);
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
obj* l_lean_parser_symbol_view___rarg___boxed(obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__14(obj*, obj*, obj*);
obj* l_rbmap_find___main___at_lean_parser_indexed___spec__1(obj*);
obj* l_lean_parser_symbol__core___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_number_has__view_x_27___lambda__1(obj*);
obj* l_lean_parser_raw___rarg___lambda__1(obj*, uint8, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_rec__t_run__parsec___at_lean_parser_detail__ident_parser___spec__1___lambda__1(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__3(obj*, obj*, obj*);
obj* l_lean_parser_detail__ident__part_parser___lambda__1___boxed(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_token_2__whitespace__aux___main___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__2___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_ident_parser_view___boxed(obj*);
obj* l_option_to__monad___main___at_lean_parser_indexed___spec__2___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___boxed(obj*);
obj* l_lean_parser_string__lit_parser___rarg___lambda__1(obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__10___boxed(obj*);
obj* l_lean_parser_parsec__t_try__mk__res___rarg(obj*);
obj* l_lean_parser_raw__ident_parser_view___rarg(obj*);
obj* l_lean_parser_string__lit_x_27___closed__1;
obj* l_lean_parser_symbol_view__default___boxed(obj*);
obj* l_lean_parser_detail__ident__suffix_has__view_x_27;
obj* l_lean_parser_monad__parsec_whitespace___at___private_init_lean_parser_token_2__whitespace__aux___main___spec__1(obj*, obj*, obj*);
obj* l_list_reverse___rarg(obj*);
obj* l_lean_parser_detail__ident__part_parser_lean_parser_has__view___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser___spec__4___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_ident_parser___rarg___closed__1;
extern "C" obj* lean_name_mk_string(obj*, obj*);
obj* l_reader__t_alternative___rarg(obj*, obj*);
obj* l_lean_parser_unicode__symbol_view__default___rarg(obj*, obj*, obj*, obj*);
obj* l_rbmap_find___main___at_lean_parser_indexed___spec__5___rarg___boxed(obj*, obj*);
obj* l_lean_parser_parse__hex__lit___boxed(obj*, obj*, obj*);
obj* l_lean_parser_symbol__or__ident_view___boxed(obj*);
obj* l_lean_parser_detail__ident__part_parser_lean_parser_has__view___lambda__2___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_foldl___at___private_init_lean_parser_token_4__ident_x_27___spec__20(obj*, obj*, obj*, obj*);
obj* l_list_enum__from___main___rarg(obj*, obj*);
obj* l_lean_parser_detail__ident__part_has__view_x_27___lambda__1___closed__1;
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_number_x_27___spec__4___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_number_has__view_x_27___lambda__2___closed__6;
obj* l_lean_parser_detail__ident_has__view_x_27;
obj* l_lean_parser_raw__str___rarg(obj*, obj*, obj*, obj*, uint8);
obj* l_lean_parser_number_parser_view___rarg___closed__1;
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_string__lit_view_value___spec__2(uint32, obj*);
obj* l_rbmap_find___main___at_lean_parser_indexed___spec__4___rarg___boxed(obj*, obj*);
uint8 l_char_is__digit(uint32);
obj* l_lean_parser_number_view_to__nat___main(obj*);
obj* l_lean_parser_as__substring___rarg___lambda__3(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__8___rarg(obj*, obj*);
obj* l_lean_parser_parsec__t_labels__mk__res___rarg(obj*, obj*);
obj* l_lean_parser_id__part__default___at___private_init_lean_parser_token_4__ident_x_27___spec__3(obj*, obj*, obj*);
obj* l___private_init_lean_parser_token_1__finish__comment__block__aux___main___boxed(obj*, obj*, obj*, obj*, obj*);
uint32 l_char_of__nat(obj*);
obj* l___private_init_lean_parser_token_2__whitespace__aux___main(obj*, obj*, obj*, obj*);
obj* l_lean_parser_indexed___rarg___boxed(obj*, obj*, obj*);
obj* l_lean_parser_parsec__t_lookahead___at_lean_parser_number_x_27___spec__11(obj*, obj*, obj*, obj*, obj*, obj*);
uint8 l_lean_parser_syntax_is__of__kind___main(obj*, obj*);
extern obj* l___private_init_lean_parser_combinators_1__many1__aux___main___rarg___closed__1;
obj* l_lean_parser_ident_parser(obj*);
obj* l_id___rarg___boxed(obj*);
obj* l_lean_parser_raw___rarg(obj*, obj*, obj*, obj*, obj*, uint8);
obj* l_lean_parser_monad__parsec_take__while1___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__1___boxed(obj*, obj*, obj*);
obj* l_lean_parser_number_x_27___lambda__3___boxed(obj*, obj*, obj*, obj*);
obj* l_string_quote(obj*);
extern obj* l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_init_lean_parser_token_4__ident_x_27___spec__4(uint32, obj*, obj*, obj*);
obj* l_lean_parser_raw___rarg___lambda__3___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_parse__oct__lit___boxed(obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__26(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__11___boxed(obj*, obj*, obj*, obj*);
namespace lean {
obj* string_iterator_next(obj*);
}
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__17___boxed(obj*);
obj* l_lean_parser_monad__parsec_whitespace___at___private_init_lean_parser_token_2__whitespace__aux___main___spec__1___boxed(obj*, obj*, obj*);
obj* l_rbmap_find___main___at_lean_parser_indexed___spec__3___rarg(obj*, obj*);
obj* l_lean_parser_raw__str_lean_parser_has__tokens(obj*, obj*, obj*, obj*, obj*, uint8);
obj* l_lean_parser_with__trailing___rarg___lambda__2___boxed(obj*, obj*, obj*, obj*);
obj* l_list_mfoldr___main___at_lean_parser_number_x_27___spec__13___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_ident_parser_view___rarg___closed__1;
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__5(obj*, obj*, obj*);
obj* l_lean_parser_combinators_any__of___at_lean_parser_unicode__symbol_lean_parser_has__tokens___spec__2(obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_unexpected__at___at_lean_parser_string__lit_view_value___spec__7___rarg___boxed(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_longest__match___at_lean_parser_number_x_27___spec__10(obj*, obj*, obj*, obj*);
obj* l_lean_parser_raw__ident_parser_view___rarg___boxed(obj*);
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__7(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_foldl__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__21(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__7(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_str__core___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__3___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_list_mfoldl___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__16(obj*, obj*, obj*, obj*, obj*, obj*);
uint8 l_lean_is__id__end__escape(uint32);
obj* l_lean_parser_parsec__t_run___at_lean_parser_parsec_parse___spec__1___rarg(obj*, obj*, obj*);
obj* l___private_init_lean_parser_token_8__to__nat__base___boxed(obj*, obj*);
obj* l_lean_parser_string__lit_has__view;
obj* l_lean_parser_parsec__t_failure___at_lean_parser_token___spec__4___rarg(obj*, obj*);
obj* l_lean_parser_monad__parsec_ch___at___private_init_lean_parser_token_4__ident_x_27___spec__11(uint32, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_unexpected__at___at_lean_parser_string__lit_x_27___spec__4(obj*);
obj* l___private_init_lean_parser_token_1__finish__comment__block__aux___main___closed__3;
obj* l_lean_parser_parse__string__literal___at_lean_parser_string__lit_view_value___spec__1(obj*);
obj* l_lean_parser_symbol_view___boxed(obj*);
obj* l_lean_parser_monad__parsec_observing___at_lean_parser_peek__token___spec__2(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_foldl__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__21___lambda__1(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_init_lean_parser_token_4__ident_x_27___spec__8___boxed(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_6__take__while__aux_x_27___main___at___private_init_lean_parser_token_2__whitespace__aux___main___spec__3(obj*, uint8, obj*);
obj* l_lean_parser_raw___rarg___lambda__2___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_raw__ident_parser_tokens(obj*, obj*);
namespace lean {
obj* string_length(obj*);
}
obj* l_list_map___main___at_lean_parser_number_x_27___spec__9(obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__13(uint32, obj*, obj*, obj*);
obj* l_lean_parser_symbol__or__ident(obj*);
obj* l_lean_parser_unicode__symbol_view__default___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_6__take__while__aux_x_27___main___at___private_init_lean_parser_token_2__whitespace__aux___main___spec__6___boxed(obj*, obj*, obj*);
obj* l_lean_parser_string__lit_parser_view(obj*);
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__25___rarg(obj*, obj*);
obj* l_lean_parser_symbol__core(obj*);
uint8 l_string_is__empty(obj*);
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__10___rarg(obj*, obj*);
obj* l_lean_parser_symbol__or__ident_view___rarg___boxed(obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__25(obj*);
obj* l_lean_parser_number_parser_tokens(obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_init_lean_parser_token_4__ident_x_27___spec__15___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_detail__ident__part_has__view_x_27;
obj* l_lean_parser_detail__ident__suffix_parser_lean_parser_has__view___lambda__1(obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while_x_27___at___private_init_lean_parser_token_2__whitespace__aux___main___spec__2___rarg(obj*, obj*);
uint8 l_char_is__alpha(uint32);
obj* l_lean_parser_detail__ident_parser___lambda__1(obj*, obj*, obj*, obj*, obj*);
namespace lean {
uint32 string_iterator_curr(obj*);
}
obj* l_lean_parser_with__trailing___at_lean_parser_token___spec__3___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_parse__string__literal__aux___main___at_lean_parser_string__lit_x_27___spec__2(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__17___rarg(obj*, obj*);
obj* l_lean_parser_combinators_choice__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__29(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_raw__ident_parser_tokens___boxed(obj*, obj*);
obj* l___private_init_lean_parser_token_2__whitespace__aux___main___closed__3;
obj* l_lean_parser_parsec__t_lookahead___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__4(obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_parse__hex__lit___spec__2(uint32, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_many1__aux_x_27___main___at_lean_parser_parse__bin__lit___spec__2___closed__1;
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_number_x_27___spec__2(uint32, obj*, obj*, obj*);
extern obj* l_lean_name_to__string___closed__1;
obj* l_lean_parser_symbol__or__ident_tokens___boxed(obj*, obj*, obj*);
obj* l_lean_parser_number_has__view_x_27___lambda__1___closed__5;
obj* l_lean_parser_ident_parser___boxed(obj*);
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_lean_parser_symbol__or__ident_view___rarg(obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__3(obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__2___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__4___boxed(obj*, obj*, obj*, obj*);
obj* l_function_comp___rarg(obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__14(obj*, obj*, obj*);
obj* l_lean_parser_as__substring___boxed(obj*);
obj* l_lean_parser_parsec__t_lookahead___at___private_init_lean_parser_token_4__ident_x_27___spec__19(obj*, obj*, obj*);
obj* l_lean_parser_id__part__default___at___private_init_lean_parser_token_4__ident_x_27___spec__3___boxed(obj*, obj*, obj*);
obj* l_lean_parser_string__lit_parser_view___rarg___closed__2;
obj* l_lean_parser_number_view_of__nat(obj*);
obj* l_lean_parser_try__view___at_lean_parser_number_parser___spec__1(obj*);
obj* l_lean_parser_monad__parsec_digit___at_lean_parser_string__lit_x_27___spec__6(obj*, obj*, obj*);
obj* l_lean_parser_number_parser___rarg___closed__1;
obj* l_lean_parser_number_has__view_x_27;
obj* l_lean_parser_parsec__t_lookahead___at_lean_parser_token___spec__1___boxed(obj*, obj*, obj*);
obj* l_reader__t_lift___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__5(obj*);
obj* l_lean_parser_unicode__symbol_view__default(obj*);
obj* l___private_init_lean_parser_token_1__finish__comment__block__aux___main___closed__1;
obj* l_lean_parser_number_parser___boxed(obj*);
obj* l_rbmap_find___main___at_lean_parser_indexed___spec__4(obj*);
obj* l_lean_parser_monad__parsec_take__while1___at_lean_parser_number_x_27___spec__1___boxed(obj*, obj*, obj*);
obj* l_lean_parser_symbol(obj*);
obj* l_lean_parser_detail__ident__suffix;
obj* l_lean_parser_number_parser_view___rarg___boxed(obj*);
extern obj* l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
obj* l_lean_parser_detail__ident__part_parser___lambda__2___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_detail__ident__part_has__view_x_27___lambda__2___closed__1;
obj* l_lean_parser_raw__str(obj*);
obj* l_lean_parser_string__lit;
obj* l_lean_parser_id__part___at___private_init_lean_parser_token_4__ident_x_27___spec__1___boxed(obj*, obj*, obj*);
obj* l_lean_parser_match__token___closed__1;
obj* l_lean_parser_raw__ident_parser___rarg(obj*);
obj* l_lean_parser_raw__ident_parser(obj*);
obj* l_lean_parser_monad__parsec_take__while1___at_lean_parser_parse__hex__lit___spec__1(obj*, obj*, obj*);
obj* l_lean_parser_whitespace___boxed(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__21___rarg(obj*, obj*);
obj* l___private_init_lean_parser_parsec_1__str__aux___main(obj*, obj*, obj*);
obj* l_reader__t_bind___at_lean_parser_with__trailing___spec__2___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_number_has__view_x_27___lambda__1___closed__4;
obj* l_option_to__monad___main___at_lean_parser_indexed___spec__2(obj*);
obj* l_lean_parser_detail__ident__part_has__view_x_27___lambda__2___closed__3;
obj* l_lean_parser_unicode__symbol_lean_parser_has__view___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_rbmap_find___main___at_lean_parser_indexed___spec__4___boxed(obj*);
obj* l_lean_parser_number_has__view;
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser___spec__3(obj*, obj*, obj*);
obj* l_lean_parser_detail__ident_x_27___closed__1;
obj* l_lean_parser_number_x_27___lambda__4___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_observing___at_lean_parser_token___spec__2___boxed(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__23___rarg(obj*, obj*);
obj* l_reader__t_lift___at_lean_parser_with__trailing___spec__1(obj*);
obj* l_lean_parser_number_has__view_x_27___lambda__2___closed__2;
obj* l___private_init_lean_parser_token_2__whitespace__aux___main___closed__2;
obj* l_lean_parser_raw__ident_parser___boxed(obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_string__lit_view_value___spec__3___boxed(obj*);
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser___spec__8___boxed(obj*);
obj* l_lean_parser_unicode__symbol(obj*);
obj* l_lean_parser_peek__token(obj*, obj*, obj*);
obj* l_lean_parser_rec__t_recurse___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__8(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_token_3__update__trailing(obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_tokens___rarg(obj*);
obj* l_list_mfoldl___main___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__10(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_option_get__or__else___main___rarg(obj*, obj*);
uint8 l_lean_is__id__rest(uint32);
obj* l___private_init_lean_parser_parsec_6__take__while__aux_x_27___main___at___private_init_lean_parser_token_2__whitespace__aux___main___spec__3___boxed(obj*, obj*, obj*);
obj* l_lean_parser_string__lit_x_27___lambda__1(obj*, obj*, obj*, obj*);
obj* l_lean_parser_detail__ident__part_parser_lean_parser_has__view___lambda__3(obj*, obj*, obj*, obj*);
obj* l_lean_parser_raw__ident_parser_view(obj*);
obj* l_lean_parser_ident_parser_view___rarg___boxed(obj*);
obj* l_lean_parser_raw__str_lean_parser_has__view(obj*);
obj* l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__5___closed__1;
obj* l_lean_parser_monad__parsec_foldl__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__21___lambda__1___boxed(obj*, obj*, obj*);
obj* l_lean_parser_string__lit_parser(obj*);
obj* l_lean_parser_with__trailing___rarg___lambda__3(obj*, obj*, obj*);
obj* l_lean_parser_detail__ident__part__escaped_has__view_x_27___lambda__2___closed__1;
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__8___boxed(obj*);
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__13(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__23___boxed(obj*);
obj* l_lean_parser_monad__parsec_ch___at___private_init_lean_parser_token_4__ident_x_27___spec__11___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_parse__quoted__char___at_lean_parser_string__lit_view_value___spec__6(obj*);
extern obj* l_lean_parser_no__kind;
obj* l_lean_parser_syntax_as__node___main(obj*);
obj* l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__5(obj*, obj*, obj*);
obj* l_lean_parser_parse__string__literal__aux___main___at_lean_parser_string__lit_view_value___spec__4___boxed(obj*, obj*, obj*);
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
obj* l_lean_parser_number_has__view_x_27___lambda__2___closed__3;
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
obj* l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_view_value___spec__8(obj*);
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
obj* l_lean_parser_string__lit_parser___boxed(obj*);
obj* l_lean_parser_monad__parsec_curr___at___private_init_lean_parser_token_4__ident_x_27___spec__2(obj*);
obj* l_lean_parser_detail__ident_has__view_x_27___lambda__2(obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_init_lean_parser_token_4__ident_x_27___spec__13(uint32, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_unexpected__at___at_lean_parser_string__lit_view_value___spec__7___rarg(obj*, obj*, obj*);
obj* l_lean_parser_symbol__core___at_lean_parser_unicode__symbol_lean_parser_has__tokens___spec__1(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_combinators_node_view___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_foldl__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__21___closed__1;
obj* l___private_init_lean_parser_rec_1__run__aux___at_lean_parser_detail__ident_parser___spec__3___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_detail__ident__part_has__view_x_27___lambda__1___closed__3;
obj* l_lean_parser_unicode__symbol___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_parser_symbol__core___boxed(obj*);
obj* l_lean_parser_detail__ident_has__view_x_27___lambda__1___closed__1;
obj* l_lean_parser_monad__parsec_curr___at___private_init_lean_parser_token_4__ident_x_27___spec__2___boxed(obj*);
obj* l_rbmap_find___main___at_lean_parser_indexed___spec__3___rarg___boxed(obj*, obj*);
extern obj* l_lean_parser_monad__parsec_left__over___rarg___closed__1;
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__5(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_digit___at_lean_parser_string__lit_view_value___spec__9(obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_init_lean_parser_token_4__ident_x_27___spec__8(obj*, obj*, obj*, obj*);
obj* l_lean_parser_finish__comment__block___closed__2;
obj* l_lean_parser_detail__ident__suffix_has__view_x_27___lambda__2(obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_init_lean_parser_token_4__ident_x_27___spec__13___boxed(obj*, obj*, obj*, obj*);
extern obj* l_string_join___closed__1;
obj* l_lean_parser_raw__str___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_reader__t_lift___at_lean_parser_with__trailing___spec__1___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_detail__ident__part;
obj* l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
obj* l_lean_parser_detail__ident_parser___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while1___at_lean_parser_number_x_27___spec__1(obj*, obj*, obj*);
obj* l_lean_parser_parsec__t_lookahead___at_lean_parser_number_x_27___spec__11___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_rbmap_find___main___at_lean_parser_indexed___spec__1___rarg___boxed(obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__9___boxed(obj*, obj*, obj*, obj*);
obj* l_rbmap_find___main___at_lean_parser_indexed___spec__5(obj*);
obj* l_lean_parser_token___closed__1;
obj* l_lean_parser_number_x_27___lambda__1___boxed(obj*, obj*, obj*, obj*);
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
obj* l_lean_parser_string__lit_parser_tokens___boxed(obj*, obj*);
obj* l_lean_parser_number_x_27___lambda__1(obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while1___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__8(obj*, obj*, obj*);
obj* l_lean_parser_unicode__symbol_lean_parser_has__view___boxed(obj*);
obj* l_rbmap_find___main___at_lean_parser_indexed___spec__1___rarg(obj*, obj*);
obj* l_lean_parser_syntax_mk__node(obj*, obj*);
obj* l_reader__t_lift___at_lean_parser_detail__ident_x_27___spec__1___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__1(uint32, obj*, obj*, obj*, obj*);
obj* l_lean_parser_symbol_view__default___rarg___boxed(obj*, obj*, obj*);
obj* l_lean_parser_detail__ident_has__view_x_27___lambda__1___closed__2;
obj* l_lean_parser_detail__ident__part__escaped_has__view_x_27___lambda__2___closed__2;
obj* l_rbmap_find___main___at_lean_parser_indexed___spec__1___boxed(obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__3___boxed(obj*);
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
obj* l_rbnode_find___main___at_lean_name__map_contains___spec__2___rarg(obj*, obj*);
obj* l_list_map___main___at_lean_parser_number_x_27___spec__9___lambda__1(obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__4___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_combinators_longest__choice___at_lean_parser_number_x_27___spec__8(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__24(obj*, obj*, obj*);
extern obj* l_lean_parser_parsec__t_failure___rarg___closed__1;
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__13___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_token(obj*, obj*, obj*);
obj* l_lean_parser_whitespace(obj*, obj*, obj*);
obj* l_reader__t_monad__except___rarg(obj*);
obj* l_lean_parser_indexed___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_as__substring(obj*);
obj* l_lean_parser_raw__ident_parser_view___boxed(obj*);
obj* l_lean_parser_ident_parser_view___rarg___lambda__2(obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_init_lean_parser_token_4__ident_x_27___spec__6(uint32, obj*, obj*, obj*);
obj* l_lean_parser_with__trailing___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_parser_raw_view___boxed(obj*);
extern uint32 l_lean_id__begin__escape;
obj* l_rbmap_find___main___at_lean_parser_indexed___spec__3(obj*);
namespace lean {
obj* string_iterator_offset(obj*);
}
obj* l_list_foldl___main___at_lean_parser_unicode__symbol_lean_parser_has__tokens___spec__3(obj*, obj*, obj*, obj*, obj*);
obj* l_reader__t_lift___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__5___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser___spec__10___boxed(obj*);
obj* l___private_init_lean_parser_token_7__to__nat__core(obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_curr___at___private_init_lean_parser_token_4__ident_x_27___spec__2___rarg(obj*, obj*);
obj* l_lean_parser_detail__ident__part_parser_lean_parser_has__view___lambda__3___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser___spec__12___boxed(obj*);
obj* l_lean_parser_with__trailing___rarg___lambda__2(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_token_5__mk__consume__token___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_parsec__t_failure___at_lean_parser_token___spec__4(obj*, obj*);
obj* l_lean_parser_symbol__or__ident_view(obj*);
obj* l_lean_parser_monad__parsec_take__while1___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__8___boxed(obj*, obj*, obj*);
obj* l_lean_parser_raw(obj*);
obj* l_lean_parser_monad__parsec_take__while1___at_lean_parser_parse__oct__lit___spec__1(obj*, obj*, obj*);
obj* l_lean_parser_raw_view___rarg___closed__2;
obj* l_lean_parser_unicode__symbol___boxed(obj*);
obj* l_lean_parser_monad__parsec_any___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__2___boxed(obj*, obj*, obj*);
obj* l_lean_parser_detail__ident_has__view_x_27___lambda__2___closed__1;
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__12___boxed(obj*);
obj* l_lean_parser_string__lit_parser_view___rarg___closed__1;
obj* l_lean_parser_monad__parsec_many1__aux_x_27___main___at_lean_parser_parse__bin__lit___spec__2___closed__2;
obj* l_lean_parser_symbol_view__default(obj*);
obj* l_lean_parser_combinators_node___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__15(obj*, obj*, obj*, obj*, obj*);
extern obj* l_list_mfoldr___main___at_lean_parser_monad__parsec_longest__match___spec__2___rarg___closed__1;
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__17(obj*);
obj* l_lean_parser_raw__str___boxed(obj*);
obj* l_lean_parser_detail__ident__part_parser___lambda__1(obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_any___at_lean_parser_string__lit_view_value___spec__5(obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser___spec__6(uint32, obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__18(obj*, obj*, obj*);
obj* l_lean_parser_parsec__t_merge___rarg(obj*, obj*);
obj* l_lean_parser_indexed___rarg___lambda__1___closed__1;
obj* l_lean_parser_token__cont___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_observing___at_lean_parser_token___spec__2(obj*, obj*, obj*);
obj* l_lean_parser_substring_to__string(obj*);
obj* l_lean_parser_try__view___at_lean_parser_string__lit_parser___spec__1(obj*);
extern "C" uint8 lean_name_dec_eq(obj*, obj*);
obj* l___private_init_lean_parser_token_7__to__nat__core___boxed(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_token_1__finish__comment__block__aux___main___closed__2;
obj* l_lean_parser_unicode__symbol_lean_parser_has__view(obj*);
obj* l_lean_parser_parsec__t_lookahead___at___private_init_lean_parser_token_2__whitespace__aux___main___spec__4___closed__1;
namespace lean {
uint8 string_dec_eq(obj*, obj*);
}
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser___spec__5(obj*, obj*, obj*);
obj* l_option_to__monad___main___at_lean_parser_indexed___spec__2___boxed(obj*);
obj* l_lean_parser_raw__str_view__default___boxed(obj*);
obj* l_lean_parser_number_has__view_x_27___lambda__2___closed__5;
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_init_lean_parser_token_4__ident_x_27___spec__17___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_raw__str_lean_parser_has__view___boxed(obj*);
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__12___rarg(obj*, obj*);
obj* l_lean_parser_monad__parsec_unexpected__at___at_lean_parser_string__lit_x_27___spec__4___rarg(obj*, obj*, obj*, obj*, obj*);
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
obj* l_lean_parser_indexed___rarg(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_foldl__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__21___lambda__2(uint32, uint32, obj*, obj*, obj*);
obj* l_lean_parser_detail__ident__part__escaped_has__view_x_27___lambda__1(obj*);
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__11(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__19___boxed(obj*);
obj* l_lean_parser_number_has__view_x_27___lambda__1___closed__1;
obj* l_lean_parser_parsec__t_failure___at_lean_parser_token___spec__4___boxed(obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while1___at_lean_parser_detail__ident__part_parser___spec__1___boxed(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser___spec__12(obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_string__lit_view_value___spec__3___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
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
obj* l_lean_parser_parse__string__literal___at_lean_parser_string__lit_x_27___spec__1___boxed(obj*, obj*, obj*);
obj* l_lean_parser_with__trailing___rarg___closed__1;
obj* l_lean_parser_detail__ident__suffix_parser_lean_parser_has__view;
obj* l_rbmap_find___main___at_lean_parser_indexed___spec__4___rarg(obj*, obj*);
obj* l_lean_parser_monad__parsec_digit___at_lean_parser_string__lit_x_27___spec__6___boxed(obj*, obj*, obj*);
obj* l___private_init_lean_parser_token_1__finish__comment__block__aux___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_symbol__or__ident___rarg___lambda__1(obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_unexpected__at___at_lean_parser_string__lit_view_value___spec__7___boxed(obj*);
obj* l_lean_parser_parsec__t_lookahead___at_lean_parser_token___spec__1(obj*, obj*, obj*);
obj* l_reader__t_lift___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__5___boxed(obj*);
obj* l_lean_parser_monad__parsec_take__while1___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__1(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_any___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__2(obj*, obj*, obj*);
obj* l_string_trim(obj*);
obj* l_lean_parser_string__lit_has__view_x_27___lambda__2___closed__1;
obj* l_lean_parser_monad__parsec_unexpected__at___at_lean_parser_string__lit_x_27___spec__4___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_number_x_27___spec__4(uint32, obj*, obj*, obj*);
obj* l_lean_parser_number__or__string__lit(obj*, obj*, obj*);
obj* l_lean_parser_raw___rarg___lambda__2(obj*, uint8, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_option_get___main___at_lean_parser_run___spec__2(obj*);
obj* l_lean_parser_unicode__symbol_lean_parser_has__tokens___rarg(obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser___spec__9(obj*, obj*, obj*);
obj* l_lean_parser_raw___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_parsec__t_lookahead___at_lean_parser_detail__ident__suffix_parser___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_raw_view(obj*);
obj* l_lean_parser_indexed___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_ident_parser_view___rarg___lambda__1(obj*);
obj* l_lean_parser_number_parser_view(obj*);
obj* l_lean_parser_number_has__view_x_27___lambda__2(obj*);
obj* l_lean_parser_parse__string__literal__aux___main___at_lean_parser_string__lit_view_value___spec__4(obj*, obj*, obj*);
obj* l_lean_parser_parsec__t_lookahead___at___private_init_lean_parser_token_4__ident_x_27___spec__19___boxed(obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__5(obj*, obj*, obj*);
obj* l_lean_parser_id__part__escaped___at___private_init_lean_parser_token_4__ident_x_27___spec__10___boxed(obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_5__mk__consumed__result___rarg(uint8, obj*);
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser___spec__7(obj*, obj*, obj*);
obj* l_lean_parser_combinators_monad__lift_view___rarg(obj*, obj*, obj*);
obj* l_lean_parser_combinators_seq__right_view___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_reader__t_monad___rarg(obj*);
obj* l_lean_parser_detail__ident;
obj* l_lean_parser_symbol___rarg___boxed(obj*, obj*, obj*);
obj* l_lean_parser_parsec__t_lookahead___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__view___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_reader__t_lift___at_lean_parser_detail__ident_x_27___spec__1___boxed(obj*);
obj* l_lean_parser_detail__ident__part_parser_lean_parser_has__view___lambda__2(obj*, obj*, obj*, obj*);
obj* l_lean_parser_as__substring___rarg___lambda__2___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_number_parser_view___boxed(obj*);
obj* l_lean_parser_parsec__t_lookahead___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__view___spec__1(obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_number_x_27___spec__12___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_symbol__or__ident___boxed(obj*);
obj* l___private_init_lean_parser_token_7__to__nat__core___main(obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_init_lean_parser_token_4__ident_x_27___spec__6___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser___spec__2___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_number_x_27___lambda__2(obj*, obj*, obj*, obj*);
obj* l_lean_parser_number_parser_tokens___boxed(obj*, obj*);
extern "C" obj* lean_name_mk_numeral(obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_number_x_27___spec__6___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser___spec__10___rarg(obj*, obj*);
obj* l_lean_parser_detail__ident__part__escaped;
uint8 l_lean_is__id__first(uint32);
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_foldl__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__21___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while1___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__1___boxed(obj*, obj*, obj*);
obj* l_nat_repr(obj*);
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__25___boxed(obj*);
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
obj* l___private_init_lean_parser_parsec_3__mk__string__result___rarg(obj*, obj*);
obj* l_lean_parser_symbol__or__ident_tokens(obj*, obj*, obj*);
obj* l_lean_parser_with__trailing(obj*);
obj* l_reader__t_bind___at_lean_parser_with__trailing___spec__2___boxed(obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__2(obj*);
uint8 l_lean_is__id__begin__escape(uint32);
obj* l_option_to__monad___main___at_lean_parser_indexed___spec__2___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_ident_parser_view(obj*);
obj* l_lean_parser_indexed___boxed(obj*);
obj* l_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens;
obj* l_lean_parser_rec__t_run__parsec___at_lean_parser_detail__ident_parser___spec__1___lambda__1___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_number_has__view_x_27___lambda__1___closed__2;
obj* l_lean_parser_monad__parsec_foldl__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__21___closed__2;
obj* l_lean_parser_monad__parsec_str__core___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__6___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while1___at___private_init_lean_parser_token_4__ident_x_27___spec__12___boxed(obj*, obj*, obj*);
obj* l_lean_parser_detail__ident__part_has__view_x_27___lambda__2(obj*);
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_number_x_27___spec__5(obj*, obj*, obj*);
obj* l_lean_parser_string__lit_has__view_x_27;
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__6(uint32, obj*, obj*, obj*);
obj* l_lean_parser_symbol___boxed(obj*);
obj* l_lean_parser_detail__ident__part__escaped_has__view_x_27___lambda__2(obj*);
extern obj* l___private_init_data_string_basic_4__to__nat__core___main___closed__1;
obj* l_lean_parser_raw___boxed(obj*);
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
obj* l_lean_parser_parse__quoted__char___at_lean_parser_string__lit_x_27___spec__3___boxed(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__2___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_detail__ident_x_27(obj*, obj*, obj*, obj*);
namespace lean {
obj* string_push(obj*, uint32);
}
obj* l_lean_parser_parse__oct__lit(obj*, obj*, obj*);
obj* l_rbmap_find___main___at_lean_parser_indexed___spec__3___boxed(obj*);
obj* l_dlist_singleton___rarg(obj*, obj*);
obj* l_lean_parser_symbol__core___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_basic__parser__m_monad__except;
obj* l_lean_parser_parsec__t_orelse__mk__res___rarg(obj*, obj*);
obj* l_lean_parser_symbol_view(obj*);
obj* l_lean_parser_unicode__symbol_lean_parser_has__view___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_parser_parsec__t_lookahead___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__4___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_number_x_27___spec__12___boxed(obj*);
obj* l_reader__t_bind___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__7(obj*, obj*);
obj* l___private_init_lean_parser_token_2__whitespace__aux___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_detail__ident__part__escaped_has__view_x_27___lambda__1___closed__1;
obj* l_rbmap_find___main___at_lean_parser_indexed___spec__5___rarg(obj*, obj*);
obj* l_lean_parser_detail__ident__suffix_parser___closed__1;
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_string__lit_view_value___spec__2___boxed(obj*, obj*);
obj* l_lean_parser_parsec__t_lookahead___at___private_init_lean_parser_token_2__whitespace__aux___main___spec__4___boxed(obj*, obj*, obj*);
obj* l___private_init_lean_parser_token_3__update__trailing__lst(obj*, obj*);
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser___spec__13(obj*, obj*, obj*);
obj* l___private_init_lean_parser_token_7__to__nat__core___main___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_number_has__view_x_27___lambda__1___closed__6;
obj* l_lean_parser_raw__str_lean_parser_has__view___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_string__lit_parser_view___rarg___boxed(obj*);
obj* l_lean_parser_rec__t_run__parsec___at_lean_parser_detail__ident_parser___spec__1(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_unexpected__at___at_lean_parser_string__lit_x_27___spec__4___boxed(obj*);
obj* l_reader__t_bind___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__7___boxed(obj*, obj*);
extern obj* l_lean_parser_combinators_any__of___rarg___closed__1;
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser___spec__12___rarg(obj*, obj*);
obj* l_lean_parser_raw_view___rarg___lambda__2___closed__1;
obj* l_lean_parser_number_parser_view___rarg(obj*);
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__3(obj*, obj*, obj*);
obj* l_lean_parser_symbol__core___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_number_parser___rarg(obj*);
obj* l_lean_parser_detail__ident__suffix_parser_lean_parser_has__view___lambda__2___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_raw__str_lean_parser_has__tokens___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_substring_of__string(obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__3___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser___spec__6___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_unicode__symbol_lean_parser_has__tokens___boxed(obj*, obj*);
obj* l_lean_parser_string__lit_view_value(obj*);
obj* l_lean_parser_unicode__symbol_view__default___boxed(obj*);
obj* l_lean_parser_parse__quoted__char___at_lean_parser_string__lit_x_27___spec__3(obj*, obj*, obj*);
obj* l_lean_parser_ident_parser_tokens(obj*, obj*);
obj* l___private_init_lean_parser_rec_1__run__aux___at_lean_parser_detail__ident_parser___spec__3(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_string__lit_x_27___lambda__1___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_number_x_27___spec__2___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_detail__ident__suffix_parser(obj*, obj*, obj*, obj*);
obj* l_reader__t_lift___at_lean_parser_detail__ident_x_27___spec__1(obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__9(uint32, obj*, obj*, obj*);
obj* l_lean_parser_number_x_27___lambda__4(obj*, obj*, obj*, obj*);
obj* l_lean_parser_string__lit_parser_view___rarg(obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_string__lit_view_value___spec__3___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_ident_parser___rarg(obj*);
obj* l_lean_parser_number_has__view_x_27___lambda__2___closed__4;
obj* l_reader__t_lift___at_lean_parser_detail__ident_x_27___spec__1___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_detail__ident__suffix_has__view_x_27___lambda__1(obj*);
obj* l_lean_parser_parse__string__literal__aux___main___at_lean_parser_string__lit_x_27___spec__2___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_number_x_27___spec__7(obj*, obj*, obj*);
obj* l_char_quote__core(uint32);
obj* l___private_init_lean_parser_token_3__update__trailing__lst___main(obj*, obj*);
obj* l_lean_parser_number_x_27(obj*, obj*, obj*);
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
obj* l_lean_parser_detail__ident__part_parser_lean_parser_has__view___lambda__1(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_rec_1__run__aux___main___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_parser_raw_tokens(obj*, obj*, obj*, obj*, obj*, obj*, uint8);
obj* _init_l_lean_parser_match__token___closed__1() {
_start:
{
obj* x_0; obj* x_3; obj* x_4; obj* x_5; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_id___rarg___boxed), 1, 0);
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
obj* x_3; obj* x_7; 
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
lean::inc(x_1);
x_7 = l_lean_parser_trie_match__prefix___rarg(x_3, x_1);
if (lean::obj_tag(x_7) == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_8 = lean::box(0);
x_9 = l_lean_parser_match__token___closed__1;
x_10 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_1);
lean::cnstr_set(x_10, 2, x_9);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_2);
return x_11;
}
else
{
obj* x_12; obj* x_14; obj* x_15; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_12 = lean::cnstr_get(x_7, 0);
if (lean::is_exclusive(x_7)) {
 x_14 = x_7;
} else {
 lean::inc(x_12);
 lean::dec(x_7);
 x_14 = lean::box(0);
}
x_15 = lean::cnstr_get(x_12, 1);
lean::inc(x_15);
lean::dec(x_12);
if (lean::is_scalar(x_14)) {
 x_18 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_18 = x_14;
}
lean::cnstr_set(x_18, 0, x_15);
x_19 = l_lean_parser_match__token___closed__1;
x_20 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_20, 0, x_18);
lean::cnstr_set(x_20, 1, x_1);
lean::cnstr_set(x_20, 2, x_19);
x_21 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_2);
return x_21;
}
}
}
obj* l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_8; uint8 x_9; obj* x_10; obj* x_11; obj* x_12; 
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
return x_12;
}
}
obj* l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg___boxed), 7, 0);
return x_1;
}
}
obj* l_lean_parser_monad__parsec_any___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = lean::string_iterator_has_next(x_1);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_4 = lean::box(0);
x_5 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_6 = l_mjoin___rarg___closed__1;
x_7 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_5, x_6, x_4, x_4, x_0, x_1, x_2);
lean::dec(x_1);
x_9 = lean::cnstr_get(x_7, 0);
x_11 = lean::cnstr_get(x_7, 1);
if (lean::is_exclusive(x_7)) {
 x_13 = x_7;
} else {
 lean::inc(x_9);
 lean::inc(x_11);
 lean::dec(x_7);
 x_13 = lean::box(0);
}
x_14 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_15 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_14, x_9);
if (lean::is_scalar(x_13)) {
 x_16 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_16 = x_13;
}
lean::cnstr_set(x_16, 0, x_15);
lean::cnstr_set(x_16, 1, x_11);
return x_16;
}
else
{
uint32 x_17; uint8 x_18; 
x_17 = lean::string_iterator_curr(x_1);
x_18 = l_true_decidable;
if (x_18 == 0)
{
obj* x_19; obj* x_20; obj* x_21; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_28; obj* x_30; obj* x_32; obj* x_33; obj* x_34; obj* x_35; 
x_19 = l_char_quote__core(x_17);
x_20 = l_char_has__repr___closed__1;
x_21 = lean::string_append(x_20, x_19);
lean::dec(x_19);
x_23 = lean::string_append(x_21, x_20);
x_24 = lean::box(0);
x_25 = l_mjoin___rarg___closed__1;
x_26 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_23, x_25, x_24, x_24, x_0, x_1, x_2);
lean::dec(x_1);
x_28 = lean::cnstr_get(x_26, 0);
x_30 = lean::cnstr_get(x_26, 1);
if (lean::is_exclusive(x_26)) {
 x_32 = x_26;
} else {
 lean::inc(x_28);
 lean::inc(x_30);
 lean::dec(x_26);
 x_32 = lean::box(0);
}
x_33 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_34 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_33, x_28);
if (lean::is_scalar(x_32)) {
 x_35 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_35 = x_32;
}
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_30);
return x_35;
}
else
{
obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; 
x_36 = lean::string_iterator_next(x_1);
x_37 = lean::box(0);
x_38 = lean::box_uint32(x_17);
x_39 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_39, 0, x_38);
lean::cnstr_set(x_39, 1, x_36);
lean::cnstr_set(x_39, 2, x_37);
x_40 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_40, 0, x_39);
lean::cnstr_set(x_40, 1, x_2);
return x_40;
}
}
}
}
obj* l_lean_parser_monad__parsec_str__core___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; 
x_5 = l_string_is__empty(x_0);
if (x_5 == 0)
{
obj* x_6; obj* x_8; obj* x_10; 
x_6 = lean::string_length(x_0);
lean::inc(x_0);
x_8 = lean::string_mk_iterator(x_0);
lean::inc(x_3);
x_10 = l___private_init_lean_parser_parsec_1__str__aux___main(x_6, x_8, x_3);
if (lean::obj_tag(x_10) == 0)
{
obj* x_12; obj* x_13; obj* x_14; uint8 x_15; obj* x_16; obj* x_17; obj* x_18; 
lean::dec(x_0);
x_12 = lean::box(0);
x_13 = l_string_join___closed__1;
x_14 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_14, 0, x_3);
lean::cnstr_set(x_14, 1, x_13);
lean::cnstr_set(x_14, 2, x_1);
lean::cnstr_set(x_14, 3, x_12);
x_15 = 0;
x_16 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set_scalar(x_16, sizeof(void*)*1, x_15);
x_17 = x_16;
x_18 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_4);
return x_18;
}
else
{
obj* x_21; obj* x_24; obj* x_25; obj* x_26; 
lean::dec(x_1);
lean::dec(x_3);
x_21 = lean::cnstr_get(x_10, 0);
lean::inc(x_21);
lean::dec(x_10);
x_24 = lean::box(0);
x_25 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_25, 0, x_0);
lean::cnstr_set(x_25, 1, x_21);
lean::cnstr_set(x_25, 2, x_24);
x_26 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_4);
return x_26;
}
}
else
{
obj* x_29; obj* x_30; obj* x_31; obj* x_32; 
lean::dec(x_1);
lean::dec(x_0);
x_29 = l_string_join___closed__1;
x_30 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_31 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_31, 0, x_29);
lean::cnstr_set(x_31, 1, x_3);
lean::cnstr_set(x_31, 2, x_30);
x_32 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_4);
return x_32;
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
if (x_6 == 0)
{
obj* x_7; obj* x_8; uint8 x_9; obj* x_10; obj* x_11; obj* x_13; obj* x_14; obj* x_16; obj* x_17; 
x_7 = lean::mk_nat_obj(1u);
x_8 = lean::nat_sub(x_1, x_7);
x_9 = lean::nat_dec_eq(x_0, x_7);
x_13 = l___private_init_lean_parser_token_1__finish__comment__block__aux___main___closed__3;
x_14 = l___private_init_lean_parser_token_1__finish__comment__block__aux___main___closed__4;
lean::inc(x_3);
x_16 = l_lean_parser_monad__parsec_str__core___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__3(x_13, x_14, x_2, x_3, x_4);
x_17 = lean::cnstr_get(x_16, 0);
lean::inc(x_17);
if (lean::obj_tag(x_17) == 0)
{
obj* x_19; obj* x_22; obj* x_24; obj* x_27; obj* x_28; obj* x_30; obj* x_32; obj* x_35; 
x_19 = lean::cnstr_get(x_16, 1);
lean::inc(x_19);
lean::dec(x_16);
x_22 = lean::cnstr_get(x_17, 1);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_17, 2);
lean::inc(x_24);
lean::dec(x_17);
x_27 = lean::nat_add(x_0, x_7);
x_28 = l___private_init_lean_parser_token_1__finish__comment__block__aux___main(x_27, x_8, x_2, x_22, x_19);
lean::dec(x_27);
x_30 = lean::cnstr_get(x_28, 0);
lean::inc(x_30);
x_32 = lean::cnstr_get(x_28, 1);
lean::inc(x_32);
lean::dec(x_28);
x_35 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_24, x_30);
x_10 = x_35;
x_11 = x_32;
goto lbl_12;
}
else
{
obj* x_36; obj* x_39; uint8 x_41; obj* x_42; obj* x_43; obj* x_44; 
x_36 = lean::cnstr_get(x_16, 1);
lean::inc(x_36);
lean::dec(x_16);
x_39 = lean::cnstr_get(x_17, 0);
x_41 = lean::cnstr_get_scalar<uint8>(x_17, sizeof(void*)*1);
if (lean::is_exclusive(x_17)) {
 x_42 = x_17;
} else {
 lean::inc(x_39);
 lean::dec(x_17);
 x_42 = lean::box(0);
}
if (lean::is_scalar(x_42)) {
 x_43 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_43 = x_42;
}
lean::cnstr_set(x_43, 0, x_39);
lean::cnstr_set_scalar(x_43, sizeof(void*)*1, x_41);
x_44 = x_43;
x_10 = x_44;
x_11 = x_36;
goto lbl_12;
}
lbl_12:
{
if (lean::obj_tag(x_10) == 0)
{
obj* x_47; 
lean::dec(x_8);
lean::dec(x_3);
x_47 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_47, 0, x_10);
lean::cnstr_set(x_47, 1, x_11);
return x_47;
}
else
{
obj* x_48; uint8 x_50; obj* x_51; obj* x_52; 
x_48 = lean::cnstr_get(x_10, 0);
lean::inc(x_48);
x_50 = lean::cnstr_get_scalar<uint8>(x_10, sizeof(void*)*1);
if (x_50 == 0)
{
obj* x_55; obj* x_56; obj* x_58; obj* x_59; 
lean::dec(x_10);
x_55 = l___private_init_lean_parser_token_1__finish__comment__block__aux___main___closed__1;
x_56 = l___private_init_lean_parser_token_1__finish__comment__block__aux___main___closed__2;
lean::inc(x_3);
x_58 = l_lean_parser_monad__parsec_str__core___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__3(x_55, x_56, x_2, x_3, x_11);
x_59 = lean::cnstr_get(x_58, 0);
lean::inc(x_59);
if (lean::obj_tag(x_59) == 0)
{
if (x_9 == 0)
{
obj* x_61; obj* x_64; obj* x_66; obj* x_69; obj* x_70; obj* x_72; obj* x_74; obj* x_77; 
x_61 = lean::cnstr_get(x_58, 1);
lean::inc(x_61);
lean::dec(x_58);
x_64 = lean::cnstr_get(x_59, 1);
lean::inc(x_64);
x_66 = lean::cnstr_get(x_59, 2);
lean::inc(x_66);
lean::dec(x_59);
x_69 = lean::nat_sub(x_0, x_7);
x_70 = l___private_init_lean_parser_token_1__finish__comment__block__aux___main(x_69, x_8, x_2, x_64, x_61);
lean::dec(x_69);
x_72 = lean::cnstr_get(x_70, 0);
lean::inc(x_72);
x_74 = lean::cnstr_get(x_70, 1);
lean::inc(x_74);
lean::dec(x_70);
x_77 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_66, x_72);
x_51 = x_77;
x_52 = x_74;
goto lbl_53;
}
else
{
obj* x_78; obj* x_81; obj* x_83; obj* x_85; obj* x_86; obj* x_87; obj* x_88; obj* x_89; 
x_78 = lean::cnstr_get(x_58, 1);
lean::inc(x_78);
lean::dec(x_58);
x_81 = lean::cnstr_get(x_59, 1);
x_83 = lean::cnstr_get(x_59, 2);
if (lean::is_exclusive(x_59)) {
 lean::cnstr_release(x_59, 0);
 x_85 = x_59;
} else {
 lean::inc(x_81);
 lean::inc(x_83);
 lean::dec(x_59);
 x_85 = lean::box(0);
}
x_86 = lean::box(0);
x_87 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_85)) {
 x_88 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_88 = x_85;
}
lean::cnstr_set(x_88, 0, x_86);
lean::cnstr_set(x_88, 1, x_81);
lean::cnstr_set(x_88, 2, x_87);
x_89 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_83, x_88);
x_51 = x_89;
x_52 = x_78;
goto lbl_53;
}
}
else
{
obj* x_90; obj* x_93; uint8 x_95; obj* x_96; obj* x_97; obj* x_98; 
x_90 = lean::cnstr_get(x_58, 1);
lean::inc(x_90);
lean::dec(x_58);
x_93 = lean::cnstr_get(x_59, 0);
x_95 = lean::cnstr_get_scalar<uint8>(x_59, sizeof(void*)*1);
if (lean::is_exclusive(x_59)) {
 x_96 = x_59;
} else {
 lean::inc(x_93);
 lean::dec(x_59);
 x_96 = lean::box(0);
}
if (lean::is_scalar(x_96)) {
 x_97 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_97 = x_96;
}
lean::cnstr_set(x_97, 0, x_93);
lean::cnstr_set_scalar(x_97, sizeof(void*)*1, x_95);
x_98 = x_97;
x_51 = x_98;
x_52 = x_90;
goto lbl_53;
}
}
else
{
obj* x_102; 
lean::dec(x_8);
lean::dec(x_3);
lean::dec(x_48);
x_102 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_102, 0, x_10);
lean::cnstr_set(x_102, 1, x_11);
return x_102;
}
lbl_53:
{
if (lean::obj_tag(x_51) == 0)
{
obj* x_105; obj* x_106; 
lean::dec(x_8);
lean::dec(x_3);
x_105 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_48, x_51);
x_106 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_106, 0, x_105);
lean::cnstr_set(x_106, 1, x_52);
return x_106;
}
else
{
uint8 x_107; 
x_107 = lean::cnstr_get_scalar<uint8>(x_51, sizeof(void*)*1);
if (x_107 == 0)
{
obj* x_108; obj* x_111; obj* x_112; 
x_108 = lean::cnstr_get(x_51, 0);
lean::inc(x_108);
lean::dec(x_51);
x_111 = l_lean_parser_monad__parsec_any___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__2(x_2, x_3, x_52);
x_112 = lean::cnstr_get(x_111, 0);
lean::inc(x_112);
if (lean::obj_tag(x_112) == 0)
{
obj* x_114; obj* x_117; obj* x_119; obj* x_122; obj* x_124; obj* x_126; obj* x_128; obj* x_129; obj* x_130; obj* x_131; obj* x_132; 
x_114 = lean::cnstr_get(x_111, 1);
lean::inc(x_114);
lean::dec(x_111);
x_117 = lean::cnstr_get(x_112, 1);
lean::inc(x_117);
x_119 = lean::cnstr_get(x_112, 2);
lean::inc(x_119);
lean::dec(x_112);
x_122 = l___private_init_lean_parser_token_1__finish__comment__block__aux___main(x_0, x_8, x_2, x_117, x_114);
lean::dec(x_8);
x_124 = lean::cnstr_get(x_122, 0);
x_126 = lean::cnstr_get(x_122, 1);
if (lean::is_exclusive(x_122)) {
 x_128 = x_122;
} else {
 lean::inc(x_124);
 lean::inc(x_126);
 lean::dec(x_122);
 x_128 = lean::box(0);
}
x_129 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_119, x_124);
x_130 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_108, x_129);
x_131 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_48, x_130);
if (lean::is_scalar(x_128)) {
 x_132 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_132 = x_128;
}
lean::cnstr_set(x_132, 0, x_131);
lean::cnstr_set(x_132, 1, x_126);
return x_132;
}
else
{
obj* x_134; obj* x_136; obj* x_137; uint8 x_139; obj* x_140; obj* x_141; obj* x_142; obj* x_143; obj* x_144; obj* x_145; 
lean::dec(x_8);
x_134 = lean::cnstr_get(x_111, 1);
if (lean::is_exclusive(x_111)) {
 lean::cnstr_release(x_111, 0);
 x_136 = x_111;
} else {
 lean::inc(x_134);
 lean::dec(x_111);
 x_136 = lean::box(0);
}
x_137 = lean::cnstr_get(x_112, 0);
x_139 = lean::cnstr_get_scalar<uint8>(x_112, sizeof(void*)*1);
if (lean::is_exclusive(x_112)) {
 x_140 = x_112;
} else {
 lean::inc(x_137);
 lean::dec(x_112);
 x_140 = lean::box(0);
}
if (lean::is_scalar(x_140)) {
 x_141 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_141 = x_140;
}
lean::cnstr_set(x_141, 0, x_137);
lean::cnstr_set_scalar(x_141, sizeof(void*)*1, x_139);
x_142 = x_141;
x_143 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_108, x_142);
x_144 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_48, x_143);
if (lean::is_scalar(x_136)) {
 x_145 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_145 = x_136;
}
lean::cnstr_set(x_145, 0, x_144);
lean::cnstr_set(x_145, 1, x_134);
return x_145;
}
}
else
{
obj* x_148; obj* x_149; 
lean::dec(x_8);
lean::dec(x_3);
x_148 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_48, x_51);
x_149 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_149, 0, x_148);
lean::cnstr_set(x_149, 1, x_52);
return x_149;
}
}
}
}
}
}
else
{
obj* x_150; obj* x_151; obj* x_152; obj* x_153; 
x_150 = lean::box(0);
x_151 = l___private_init_lean_parser_combinators_1__many1__aux___main___rarg___closed__1;
x_152 = l_mjoin___rarg___closed__1;
x_153 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_151, x_152, x_150, x_150, x_2, x_3, x_4);
lean::dec(x_3);
return x_153;
}
}
}
obj* l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_0, x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_2);
lean::dec(x_4);
lean::dec(x_5);
return x_7;
}
}
obj* l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_parser_monad__parsec_any___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_parser_monad__parsec_any___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__2(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_lean_parser_monad__parsec_str__core___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__3___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_lean_parser_monad__parsec_str__core___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__3(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* l___private_init_lean_parser_token_1__finish__comment__block__aux___main___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l___private_init_lean_parser_token_1__finish__comment__block__aux___main(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_5;
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
obj* l___private_init_lean_parser_token_1__finish__comment__block__aux___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l___private_init_lean_parser_token_1__finish__comment__block__aux(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
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
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_id___rarg___boxed), 1, 0);
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
obj* x_4; obj* x_5; obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_4 = lean::string_iterator_remaining(x_2);
x_5 = lean::mk_nat_obj(1u);
x_6 = lean::nat_add(x_4, x_5);
lean::dec(x_4);
x_8 = l___private_init_lean_parser_token_1__finish__comment__block__aux___main(x_0, x_6, x_1, x_2, x_3);
lean::dec(x_6);
x_10 = lean::cnstr_get(x_8, 0);
x_12 = lean::cnstr_get(x_8, 1);
if (lean::is_exclusive(x_8)) {
 x_14 = x_8;
} else {
 lean::inc(x_10);
 lean::inc(x_12);
 lean::dec(x_8);
 x_14 = lean::box(0);
}
x_15 = l_lean_parser_finish__comment__block___closed__1;
x_16 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_10, x_15);
x_17 = l_lean_parser_finish__comment__block___closed__2;
x_18 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_17, x_16);
if (lean::is_scalar(x_14)) {
 x_19 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_19 = x_14;
}
lean::cnstr_set(x_19, 0, x_18);
lean::cnstr_set(x_19, 1, x_12);
return x_19;
}
}
obj* l_lean_parser_finish__comment__block___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_parser_finish__comment__block(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
return x_4;
}
}
obj* l___private_init_lean_parser_parsec_6__take__while__aux_x_27___main___at___private_init_lean_parser_token_2__whitespace__aux___main___spec__3(obj* x_0, uint8 x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = lean::string_iterator_has_next(x_2);
if (x_5 == 0)
{
obj* x_7; 
lean::dec(x_0);
x_7 = l___private_init_lean_parser_parsec_5__mk__consumed__result___rarg(x_1, x_2);
return x_7;
}
else
{
uint32 x_8; uint8 x_9; 
x_8 = lean::string_iterator_curr(x_2);
x_9 = l_char_is__whitespace(x_8);
if (x_9 == 0)
{
obj* x_11; 
lean::dec(x_0);
x_11 = l___private_init_lean_parser_parsec_5__mk__consumed__result___rarg(x_1, x_2);
return x_11;
}
else
{
obj* x_12; obj* x_13; obj* x_15; uint8 x_16; 
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_sub(x_0, x_12);
lean::dec(x_0);
x_15 = lean::string_iterator_next(x_2);
x_16 = 1;
x_0 = x_13;
x_1 = x_16;
x_2 = x_15;
goto _start;
}
}
}
else
{
obj* x_19; 
lean::dec(x_0);
x_19 = l___private_init_lean_parser_parsec_5__mk__consumed__result___rarg(x_1, x_2);
return x_19;
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
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_take__while_x_27___at___private_init_lean_parser_token_2__whitespace__aux___main___spec__2___rarg), 2, 0);
return x_1;
}
}
obj* l_lean_parser_monad__parsec_whitespace___at___private_init_lean_parser_token_2__whitespace__aux___main___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_parser_monad__parsec_take__while_x_27___at___private_init_lean_parser_token_2__whitespace__aux___main___spec__2___rarg(x_1, x_2);
return x_3;
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
obj* x_3; obj* x_4; obj* x_6; obj* x_7; 
x_3 = l_lean_parser_parsec__t_lookahead___at___private_init_lean_parser_token_2__whitespace__aux___main___spec__4___closed__1;
x_4 = l_lean_parser_parsec__t_lookahead___at___private_init_lean_parser_token_2__whitespace__aux___main___spec__4___closed__2;
lean::inc(x_1);
x_6 = l_lean_parser_monad__parsec_str__core___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__3(x_3, x_4, x_0, x_1, x_2);
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
if (lean::obj_tag(x_7) == 0)
{
obj* x_9; obj* x_11; obj* x_12; obj* x_14; obj* x_16; uint8 x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_9 = lean::cnstr_get(x_6, 1);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 lean::cnstr_set(x_6, 1, lean::box(0));
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
x_17 = 0;
x_18 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_19 = lean::box(x_17);
if (lean::is_scalar(x_16)) {
 x_20 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_20 = x_16;
}
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_12);
lean::cnstr_set(x_20, 2, x_18);
x_21 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_14, x_20);
if (lean::obj_tag(x_21) == 0)
{
if (lean::obj_tag(x_21) == 0)
{
obj* x_22; obj* x_24; obj* x_25; obj* x_26; 
x_22 = lean::cnstr_get(x_21, 0);
if (lean::is_exclusive(x_21)) {
 lean::cnstr_release(x_21, 1);
 lean::cnstr_release(x_21, 2);
 x_24 = x_21;
} else {
 lean::inc(x_22);
 lean::dec(x_21);
 x_24 = lean::box(0);
}
if (lean::is_scalar(x_24)) {
 x_25 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_25 = x_24;
}
lean::cnstr_set(x_25, 0, x_22);
lean::cnstr_set(x_25, 1, x_1);
lean::cnstr_set(x_25, 2, x_18);
if (lean::is_scalar(x_11)) {
 x_26 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_26 = x_11;
}
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_9);
return x_26;
}
else
{
obj* x_28; 
lean::dec(x_1);
if (lean::is_scalar(x_11)) {
 x_28 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_28 = x_11;
}
lean::cnstr_set(x_28, 0, x_21);
lean::cnstr_set(x_28, 1, x_9);
return x_28;
}
}
else
{
uint8 x_30; obj* x_31; obj* x_32; obj* x_33; 
lean::dec(x_21);
x_30 = 1;
x_31 = lean::box(x_30);
x_32 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_1);
lean::cnstr_set(x_32, 2, x_18);
if (lean::is_scalar(x_11)) {
 x_33 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_33 = x_11;
}
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_9);
return x_33;
}
}
else
{
obj* x_35; obj* x_37; uint8 x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; 
lean::dec(x_7);
x_35 = lean::cnstr_get(x_6, 1);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 x_37 = x_6;
} else {
 lean::inc(x_35);
 lean::dec(x_6);
 x_37 = lean::box(0);
}
x_38 = 1;
x_39 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_40 = lean::box(x_38);
x_41 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_41, 0, x_40);
lean::cnstr_set(x_41, 1, x_1);
lean::cnstr_set(x_41, 2, x_39);
if (lean::is_scalar(x_37)) {
 x_42 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_42 = x_37;
}
lean::cnstr_set(x_42, 0, x_41);
lean::cnstr_set(x_42, 1, x_35);
return x_42;
}
}
}
obj* l___private_init_lean_parser_parsec_6__take__while__aux_x_27___main___at___private_init_lean_parser_token_2__whitespace__aux___main___spec__6(obj* x_0, uint8 x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = lean::string_iterator_has_next(x_2);
if (x_5 == 0)
{
obj* x_7; 
lean::dec(x_0);
x_7 = l___private_init_lean_parser_parsec_5__mk__consumed__result___rarg(x_1, x_2);
return x_7;
}
else
{
uint32 x_8; uint32 x_9; uint8 x_10; 
x_8 = lean::string_iterator_curr(x_2);
x_9 = 10;
x_10 = x_8 == x_9;
if (x_10 == 0)
{
obj* x_11; obj* x_12; obj* x_14; uint8 x_15; 
x_11 = lean::mk_nat_obj(1u);
x_12 = lean::nat_sub(x_0, x_11);
lean::dec(x_0);
x_14 = lean::string_iterator_next(x_2);
x_15 = 1;
x_0 = x_12;
x_1 = x_15;
x_2 = x_14;
goto _start;
}
else
{
obj* x_18; 
lean::dec(x_0);
x_18 = l___private_init_lean_parser_parsec_5__mk__consumed__result___rarg(x_1, x_2);
return x_18;
}
}
}
else
{
obj* x_20; 
lean::dec(x_0);
x_20 = l___private_init_lean_parser_parsec_5__mk__consumed__result___rarg(x_1, x_2);
return x_20;
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
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_take__while_x_27___at___private_init_lean_parser_token_2__whitespace__aux___main___spec__5___rarg), 2, 0);
return x_1;
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
if (x_5 == 0)
{
obj* x_6; obj* x_7; 
x_6 = l_lean_parser_monad__parsec_whitespace___at___private_init_lean_parser_token_2__whitespace__aux___main___spec__1(x_1, x_2, x_3);
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
if (lean::obj_tag(x_7) == 0)
{
obj* x_9; obj* x_11; obj* x_12; obj* x_14; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_22; obj* x_23; obj* x_25; obj* x_26; 
x_9 = lean::cnstr_get(x_6, 1);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 lean::cnstr_set(x_6, 1, lean::box(0));
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
 lean::cnstr_set(x_7, 1, lean::box(0));
 lean::cnstr_set(x_7, 2, lean::box(0));
 x_16 = x_7;
} else {
 lean::inc(x_12);
 lean::inc(x_14);
 lean::dec(x_7);
 x_16 = lean::box(0);
}
x_17 = lean::mk_nat_obj(1u);
x_18 = lean::nat_sub(x_0, x_17);
x_22 = l___private_init_lean_parser_token_2__whitespace__aux___main___closed__2;
x_23 = l___private_init_lean_parser_token_2__whitespace__aux___main___closed__3;
lean::inc(x_12);
x_25 = l_lean_parser_monad__parsec_str__core___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__3(x_22, x_23, x_1, x_12, x_9);
x_26 = lean::cnstr_get(x_25, 0);
lean::inc(x_26);
if (lean::obj_tag(x_26) == 0)
{
obj* x_28; obj* x_31; obj* x_33; obj* x_36; obj* x_37; obj* x_39; obj* x_42; 
x_28 = lean::cnstr_get(x_25, 1);
lean::inc(x_28);
lean::dec(x_25);
x_31 = lean::cnstr_get(x_26, 1);
lean::inc(x_31);
x_33 = lean::cnstr_get(x_26, 2);
lean::inc(x_33);
lean::dec(x_26);
x_36 = l_lean_parser_monad__parsec_take__while_x_27___at___private_init_lean_parser_token_2__whitespace__aux___main___spec__5___rarg(x_31, x_28);
x_37 = lean::cnstr_get(x_36, 0);
lean::inc(x_37);
x_39 = lean::cnstr_get(x_36, 1);
lean::inc(x_39);
lean::dec(x_36);
x_42 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_33, x_37);
if (lean::obj_tag(x_42) == 0)
{
obj* x_43; obj* x_45; obj* x_48; obj* x_49; obj* x_51; obj* x_54; 
x_43 = lean::cnstr_get(x_42, 1);
lean::inc(x_43);
x_45 = lean::cnstr_get(x_42, 2);
lean::inc(x_45);
lean::dec(x_42);
x_48 = l___private_init_lean_parser_token_2__whitespace__aux___main(x_18, x_1, x_43, x_39);
x_49 = lean::cnstr_get(x_48, 0);
lean::inc(x_49);
x_51 = lean::cnstr_get(x_48, 1);
lean::inc(x_51);
lean::dec(x_48);
x_54 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_45, x_49);
x_19 = x_54;
x_20 = x_51;
goto lbl_21;
}
else
{
obj* x_55; uint8 x_57; obj* x_58; obj* x_59; obj* x_60; 
x_55 = lean::cnstr_get(x_42, 0);
x_57 = lean::cnstr_get_scalar<uint8>(x_42, sizeof(void*)*1);
if (lean::is_exclusive(x_42)) {
 x_58 = x_42;
} else {
 lean::inc(x_55);
 lean::dec(x_42);
 x_58 = lean::box(0);
}
if (lean::is_scalar(x_58)) {
 x_59 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_59 = x_58;
}
lean::cnstr_set(x_59, 0, x_55);
lean::cnstr_set_scalar(x_59, sizeof(void*)*1, x_57);
x_60 = x_59;
x_19 = x_60;
x_20 = x_39;
goto lbl_21;
}
}
else
{
obj* x_61; obj* x_64; uint8 x_66; obj* x_67; obj* x_68; obj* x_69; 
x_61 = lean::cnstr_get(x_25, 1);
lean::inc(x_61);
lean::dec(x_25);
x_64 = lean::cnstr_get(x_26, 0);
x_66 = lean::cnstr_get_scalar<uint8>(x_26, sizeof(void*)*1);
if (lean::is_exclusive(x_26)) {
 x_67 = x_26;
} else {
 lean::inc(x_64);
 lean::dec(x_26);
 x_67 = lean::box(0);
}
if (lean::is_scalar(x_67)) {
 x_68 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_68 = x_67;
}
lean::cnstr_set(x_68, 0, x_64);
lean::cnstr_set_scalar(x_68, sizeof(void*)*1, x_66);
x_69 = x_68;
x_19 = x_69;
x_20 = x_61;
goto lbl_21;
}
lbl_21:
{
if (lean::obj_tag(x_19) == 0)
{
obj* x_73; obj* x_74; 
lean::dec(x_18);
lean::dec(x_12);
lean::dec(x_16);
x_73 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_14, x_19);
if (lean::is_scalar(x_11)) {
 x_74 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_74 = x_11;
}
lean::cnstr_set(x_74, 0, x_73);
lean::cnstr_set(x_74, 1, x_20);
return x_74;
}
else
{
obj* x_75; uint8 x_77; obj* x_78; obj* x_79; 
x_75 = lean::cnstr_get(x_19, 0);
lean::inc(x_75);
x_77 = lean::cnstr_get_scalar<uint8>(x_19, sizeof(void*)*1);
if (x_77 == 0)
{
obj* x_82; obj* x_83; obj* x_85; obj* x_86; 
lean::dec(x_19);
x_82 = l___private_init_lean_parser_token_1__finish__comment__block__aux___main___closed__3;
x_83 = l___private_init_lean_parser_token_1__finish__comment__block__aux___main___closed__4;
lean::inc(x_12);
x_85 = l_lean_parser_monad__parsec_str__core___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__3(x_82, x_83, x_1, x_12, x_20);
x_86 = lean::cnstr_get(x_85, 0);
lean::inc(x_86);
if (lean::obj_tag(x_86) == 0)
{
obj* x_88; obj* x_91; obj* x_93; obj* x_97; obj* x_98; 
x_88 = lean::cnstr_get(x_85, 1);
lean::inc(x_88);
lean::dec(x_85);
x_91 = lean::cnstr_get(x_86, 1);
lean::inc(x_91);
x_93 = lean::cnstr_get(x_86, 2);
lean::inc(x_93);
lean::dec(x_86);
lean::inc(x_91);
x_97 = l_lean_parser_parsec__t_lookahead___at___private_init_lean_parser_token_2__whitespace__aux___main___spec__4(x_1, x_91, x_88);
x_98 = lean::cnstr_get(x_97, 0);
lean::inc(x_98);
if (lean::obj_tag(x_98) == 0)
{
obj* x_100; uint8 x_102; 
x_100 = lean::cnstr_get(x_98, 0);
lean::inc(x_100);
x_102 = lean::unbox(x_100);
if (x_102 == 0)
{
obj* x_103; obj* x_106; obj* x_108; obj* x_111; obj* x_112; obj* x_113; obj* x_114; obj* x_115; obj* x_118; obj* x_120; obj* x_123; obj* x_124; obj* x_125; obj* x_126; obj* x_127; 
x_103 = lean::cnstr_get(x_97, 1);
lean::inc(x_103);
lean::dec(x_97);
x_106 = lean::cnstr_get(x_98, 1);
lean::inc(x_106);
x_108 = lean::cnstr_get(x_98, 2);
lean::inc(x_108);
lean::dec(x_98);
x_111 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_111, 0, x_91);
x_112 = lean::box(0);
x_113 = l___private_init_lean_parser_token_2__whitespace__aux___main___closed__1;
x_114 = l_mjoin___rarg___closed__1;
x_115 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_113, x_114, x_111, x_112, x_1, x_106, x_103);
lean::dec(x_106);
lean::dec(x_111);
x_118 = lean::cnstr_get(x_115, 0);
lean::inc(x_118);
x_120 = lean::cnstr_get(x_115, 1);
lean::inc(x_120);
lean::dec(x_115);
x_123 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_108, x_118);
x_124 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_125 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_124, x_123);
x_126 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_93, x_125);
x_127 = l_lean_parser_parsec__t_try__mk__res___rarg(x_126);
x_78 = x_127;
x_79 = x_120;
goto lbl_80;
}
else
{
obj* x_129; obj* x_132; obj* x_134; obj* x_136; obj* x_137; obj* x_138; obj* x_139; obj* x_140; obj* x_141; obj* x_142; obj* x_143; 
lean::dec(x_91);
x_129 = lean::cnstr_get(x_97, 1);
lean::inc(x_129);
lean::dec(x_97);
x_132 = lean::cnstr_get(x_98, 1);
x_134 = lean::cnstr_get(x_98, 2);
if (lean::is_exclusive(x_98)) {
 lean::cnstr_release(x_98, 0);
 x_136 = x_98;
} else {
 lean::inc(x_132);
 lean::inc(x_134);
 lean::dec(x_98);
 x_136 = lean::box(0);
}
x_137 = lean::box(0);
x_138 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_136)) {
 x_139 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_139 = x_136;
}
lean::cnstr_set(x_139, 0, x_137);
lean::cnstr_set(x_139, 1, x_132);
lean::cnstr_set(x_139, 2, x_138);
x_140 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_134, x_139);
x_141 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_138, x_140);
x_142 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_93, x_141);
x_143 = l_lean_parser_parsec__t_try__mk__res___rarg(x_142);
x_78 = x_143;
x_79 = x_129;
goto lbl_80;
}
}
else
{
obj* x_145; obj* x_148; uint8 x_150; obj* x_151; obj* x_152; obj* x_153; obj* x_154; obj* x_155; obj* x_156; obj* x_157; 
lean::dec(x_91);
x_145 = lean::cnstr_get(x_97, 1);
lean::inc(x_145);
lean::dec(x_97);
x_148 = lean::cnstr_get(x_98, 0);
x_150 = lean::cnstr_get_scalar<uint8>(x_98, sizeof(void*)*1);
if (lean::is_exclusive(x_98)) {
 x_151 = x_98;
} else {
 lean::inc(x_148);
 lean::dec(x_98);
 x_151 = lean::box(0);
}
if (lean::is_scalar(x_151)) {
 x_152 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_152 = x_151;
}
lean::cnstr_set(x_152, 0, x_148);
lean::cnstr_set_scalar(x_152, sizeof(void*)*1, x_150);
x_153 = x_152;
x_154 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_155 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_154, x_153);
x_156 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_93, x_155);
x_157 = l_lean_parser_parsec__t_try__mk__res___rarg(x_156);
x_78 = x_157;
x_79 = x_145;
goto lbl_80;
}
}
else
{
obj* x_158; obj* x_161; obj* x_163; uint8 x_164; obj* x_165; obj* x_166; 
x_158 = lean::cnstr_get(x_85, 1);
lean::inc(x_158);
lean::dec(x_85);
x_161 = lean::cnstr_get(x_86, 0);
if (lean::is_exclusive(x_86)) {
 x_163 = x_86;
} else {
 lean::inc(x_161);
 lean::dec(x_86);
 x_163 = lean::box(0);
}
x_164 = 0;
if (lean::is_scalar(x_163)) {
 x_165 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_165 = x_163;
}
lean::cnstr_set(x_165, 0, x_161);
lean::cnstr_set_scalar(x_165, sizeof(void*)*1, x_164);
x_166 = x_165;
x_78 = x_166;
x_79 = x_158;
goto lbl_80;
}
}
else
{
obj* x_172; obj* x_173; 
lean::dec(x_18);
lean::dec(x_11);
lean::dec(x_12);
lean::dec(x_16);
lean::dec(x_75);
x_172 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_14, x_19);
x_173 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_173, 0, x_172);
lean::cnstr_set(x_173, 1, x_20);
return x_173;
}
lbl_80:
{
if (lean::obj_tag(x_78) == 0)
{
obj* x_176; obj* x_178; obj* x_180; obj* x_181; obj* x_182; obj* x_184; obj* x_186; obj* x_187; 
lean::dec(x_11);
lean::dec(x_16);
x_176 = lean::cnstr_get(x_78, 1);
x_178 = lean::cnstr_get(x_78, 2);
if (lean::is_exclusive(x_78)) {
 lean::cnstr_release(x_78, 0);
 lean::cnstr_set(x_78, 1, lean::box(0));
 lean::cnstr_set(x_78, 2, lean::box(0));
 x_180 = x_78;
} else {
 lean::inc(x_176);
 lean::inc(x_178);
 lean::dec(x_78);
 x_180 = lean::box(0);
}
x_181 = l_lean_parser_finish__comment__block(x_17, x_1, x_176, x_79);
x_182 = lean::cnstr_get(x_181, 0);
x_184 = lean::cnstr_get(x_181, 1);
if (lean::is_exclusive(x_181)) {
 lean::cnstr_set(x_181, 0, lean::box(0));
 lean::cnstr_set(x_181, 1, lean::box(0));
 x_186 = x_181;
} else {
 lean::inc(x_182);
 lean::inc(x_184);
 lean::dec(x_181);
 x_186 = lean::box(0);
}
x_187 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_178, x_182);
if (lean::obj_tag(x_187) == 0)
{
obj* x_190; obj* x_192; obj* x_194; obj* x_195; obj* x_197; obj* x_199; obj* x_201; obj* x_202; 
lean::dec(x_186);
lean::dec(x_180);
x_190 = lean::cnstr_get(x_187, 1);
x_192 = lean::cnstr_get(x_187, 2);
if (lean::is_exclusive(x_187)) {
 lean::cnstr_release(x_187, 0);
 lean::cnstr_set(x_187, 1, lean::box(0));
 lean::cnstr_set(x_187, 2, lean::box(0));
 x_194 = x_187;
} else {
 lean::inc(x_190);
 lean::inc(x_192);
 lean::dec(x_187);
 x_194 = lean::box(0);
}
x_195 = l___private_init_lean_parser_token_2__whitespace__aux___main(x_18, x_1, x_190, x_184);
lean::dec(x_18);
x_197 = lean::cnstr_get(x_195, 0);
x_199 = lean::cnstr_get(x_195, 1);
if (lean::is_exclusive(x_195)) {
 lean::cnstr_set(x_195, 0, lean::box(0));
 lean::cnstr_set(x_195, 1, lean::box(0));
 x_201 = x_195;
} else {
 lean::inc(x_197);
 lean::inc(x_199);
 lean::dec(x_195);
 x_201 = lean::box(0);
}
x_202 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_192, x_197);
if (lean::obj_tag(x_202) == 0)
{
obj* x_205; obj* x_206; obj* x_207; 
lean::dec(x_194);
lean::dec(x_12);
x_205 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_75, x_202);
x_206 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_14, x_205);
if (lean::is_scalar(x_201)) {
 x_207 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_207 = x_201;
}
lean::cnstr_set(x_207, 0, x_206);
lean::cnstr_set(x_207, 1, x_199);
return x_207;
}
else
{
uint8 x_208; 
x_208 = lean::cnstr_get_scalar<uint8>(x_202, sizeof(void*)*1);
if (x_208 == 0)
{
obj* x_209; obj* x_212; obj* x_215; obj* x_216; obj* x_217; obj* x_220; obj* x_221; obj* x_222; obj* x_223; obj* x_224; obj* x_225; 
x_209 = lean::cnstr_get(x_202, 0);
lean::inc(x_209);
lean::dec(x_202);
x_212 = lean::cnstr_get(x_209, 2);
lean::inc(x_212);
lean::dec(x_209);
x_215 = l_mjoin___rarg___closed__1;
x_216 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_216, 0, x_212);
lean::closure_set(x_216, 1, x_215);
x_217 = lean::cnstr_get(x_75, 2);
lean::inc(x_217);
lean::dec(x_75);
x_220 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_220, 0, x_217);
lean::closure_set(x_220, 1, x_216);
x_221 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_221, 0, x_220);
x_222 = lean::box(0);
if (lean::is_scalar(x_194)) {
 x_223 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_223 = x_194;
}
lean::cnstr_set(x_223, 0, x_222);
lean::cnstr_set(x_223, 1, x_12);
lean::cnstr_set(x_223, 2, x_221);
x_224 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_14, x_223);
if (lean::is_scalar(x_201)) {
 x_225 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_225 = x_201;
}
lean::cnstr_set(x_225, 0, x_224);
lean::cnstr_set(x_225, 1, x_199);
return x_225;
}
else
{
obj* x_228; obj* x_229; obj* x_230; 
lean::dec(x_194);
lean::dec(x_12);
x_228 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_75, x_202);
x_229 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_14, x_228);
if (lean::is_scalar(x_201)) {
 x_230 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_230 = x_201;
}
lean::cnstr_set(x_230, 0, x_229);
lean::cnstr_set(x_230, 1, x_199);
return x_230;
}
}
}
else
{
uint8 x_232; 
lean::dec(x_18);
x_232 = lean::cnstr_get_scalar<uint8>(x_187, sizeof(void*)*1);
if (x_232 == 0)
{
obj* x_233; obj* x_236; obj* x_239; obj* x_240; obj* x_241; obj* x_244; obj* x_245; obj* x_246; obj* x_247; obj* x_248; obj* x_249; 
x_233 = lean::cnstr_get(x_187, 0);
lean::inc(x_233);
lean::dec(x_187);
x_236 = lean::cnstr_get(x_233, 2);
lean::inc(x_236);
lean::dec(x_233);
x_239 = l_mjoin___rarg___closed__1;
x_240 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_240, 0, x_236);
lean::closure_set(x_240, 1, x_239);
x_241 = lean::cnstr_get(x_75, 2);
lean::inc(x_241);
lean::dec(x_75);
x_244 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_244, 0, x_241);
lean::closure_set(x_244, 1, x_240);
x_245 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_245, 0, x_244);
x_246 = lean::box(0);
if (lean::is_scalar(x_180)) {
 x_247 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_247 = x_180;
}
lean::cnstr_set(x_247, 0, x_246);
lean::cnstr_set(x_247, 1, x_12);
lean::cnstr_set(x_247, 2, x_245);
x_248 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_14, x_247);
if (lean::is_scalar(x_186)) {
 x_249 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_249 = x_186;
}
lean::cnstr_set(x_249, 0, x_248);
lean::cnstr_set(x_249, 1, x_184);
return x_249;
}
else
{
obj* x_252; obj* x_254; obj* x_255; obj* x_256; obj* x_257; obj* x_258; obj* x_259; 
lean::dec(x_180);
lean::dec(x_12);
x_252 = lean::cnstr_get(x_187, 0);
if (lean::is_exclusive(x_187)) {
 x_254 = x_187;
} else {
 lean::inc(x_252);
 lean::dec(x_187);
 x_254 = lean::box(0);
}
if (lean::is_scalar(x_254)) {
 x_255 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_255 = x_254;
}
lean::cnstr_set(x_255, 0, x_252);
lean::cnstr_set_scalar(x_255, sizeof(void*)*1, x_232);
x_256 = x_255;
x_257 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_75, x_256);
x_258 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_14, x_257);
if (lean::is_scalar(x_186)) {
 x_259 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_259 = x_186;
}
lean::cnstr_set(x_259, 0, x_258);
lean::cnstr_set(x_259, 1, x_184);
return x_259;
}
}
}
else
{
uint8 x_261; 
lean::dec(x_18);
x_261 = lean::cnstr_get_scalar<uint8>(x_78, sizeof(void*)*1);
if (x_261 == 0)
{
obj* x_262; obj* x_265; obj* x_268; obj* x_269; obj* x_270; obj* x_273; obj* x_274; obj* x_275; obj* x_276; obj* x_277; obj* x_278; 
x_262 = lean::cnstr_get(x_78, 0);
lean::inc(x_262);
lean::dec(x_78);
x_265 = lean::cnstr_get(x_262, 2);
lean::inc(x_265);
lean::dec(x_262);
x_268 = l_mjoin___rarg___closed__1;
x_269 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_269, 0, x_265);
lean::closure_set(x_269, 1, x_268);
x_270 = lean::cnstr_get(x_75, 2);
lean::inc(x_270);
lean::dec(x_75);
x_273 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_273, 0, x_270);
lean::closure_set(x_273, 1, x_269);
x_274 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_274, 0, x_273);
x_275 = lean::box(0);
if (lean::is_scalar(x_16)) {
 x_276 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_276 = x_16;
}
lean::cnstr_set(x_276, 0, x_275);
lean::cnstr_set(x_276, 1, x_12);
lean::cnstr_set(x_276, 2, x_274);
x_277 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_14, x_276);
if (lean::is_scalar(x_11)) {
 x_278 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_278 = x_11;
}
lean::cnstr_set(x_278, 0, x_277);
lean::cnstr_set(x_278, 1, x_79);
return x_278;
}
else
{
obj* x_281; obj* x_283; obj* x_284; obj* x_285; obj* x_286; obj* x_287; obj* x_288; 
lean::dec(x_12);
lean::dec(x_16);
x_281 = lean::cnstr_get(x_78, 0);
if (lean::is_exclusive(x_78)) {
 x_283 = x_78;
} else {
 lean::inc(x_281);
 lean::dec(x_78);
 x_283 = lean::box(0);
}
if (lean::is_scalar(x_283)) {
 x_284 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_284 = x_283;
}
lean::cnstr_set(x_284, 0, x_281);
lean::cnstr_set_scalar(x_284, sizeof(void*)*1, x_261);
x_285 = x_284;
x_286 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_75, x_285);
x_287 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_14, x_286);
if (lean::is_scalar(x_11)) {
 x_288 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_288 = x_11;
}
lean::cnstr_set(x_288, 0, x_287);
lean::cnstr_set(x_288, 1, x_79);
return x_288;
}
}
}
}
}
}
else
{
obj* x_289; obj* x_291; obj* x_292; uint8 x_294; obj* x_295; obj* x_296; obj* x_297; obj* x_298; 
x_289 = lean::cnstr_get(x_6, 1);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 x_291 = x_6;
} else {
 lean::inc(x_289);
 lean::dec(x_6);
 x_291 = lean::box(0);
}
x_292 = lean::cnstr_get(x_7, 0);
x_294 = lean::cnstr_get_scalar<uint8>(x_7, sizeof(void*)*1);
if (lean::is_exclusive(x_7)) {
 x_295 = x_7;
} else {
 lean::inc(x_292);
 lean::dec(x_7);
 x_295 = lean::box(0);
}
if (lean::is_scalar(x_295)) {
 x_296 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_296 = x_295;
}
lean::cnstr_set(x_296, 0, x_292);
lean::cnstr_set_scalar(x_296, sizeof(void*)*1, x_294);
x_297 = x_296;
if (lean::is_scalar(x_291)) {
 x_298 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_298 = x_291;
}
lean::cnstr_set(x_298, 0, x_297);
lean::cnstr_set(x_298, 1, x_289);
return x_298;
}
}
else
{
obj* x_299; obj* x_300; obj* x_301; obj* x_302; 
x_299 = lean::box(0);
x_300 = l___private_init_lean_parser_combinators_1__many1__aux___main___rarg___closed__1;
x_301 = l_mjoin___rarg___closed__1;
x_302 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_300, x_301, x_299, x_299, x_1, x_2, x_3);
lean::dec(x_2);
return x_302;
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
obj* l_lean_parser_monad__parsec_take__while_x_27___at___private_init_lean_parser_token_2__whitespace__aux___main___spec__2___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_monad__parsec_take__while_x_27___at___private_init_lean_parser_token_2__whitespace__aux___main___spec__2(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_parser_monad__parsec_whitespace___at___private_init_lean_parser_token_2__whitespace__aux___main___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_parser_monad__parsec_whitespace___at___private_init_lean_parser_token_2__whitespace__aux___main___spec__1(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_lean_parser_parsec__t_lookahead___at___private_init_lean_parser_token_2__whitespace__aux___main___spec__4___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_parser_parsec__t_lookahead___at___private_init_lean_parser_token_2__whitespace__aux___main___spec__4(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
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
obj* l_lean_parser_monad__parsec_take__while_x_27___at___private_init_lean_parser_token_2__whitespace__aux___main___spec__5___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_monad__parsec_take__while_x_27___at___private_init_lean_parser_token_2__whitespace__aux___main___spec__5(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l___private_init_lean_parser_token_2__whitespace__aux___main___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_parser_token_2__whitespace__aux___main(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
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
obj* l___private_init_lean_parser_token_2__whitespace__aux___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_parser_token_2__whitespace__aux(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
return x_4;
}
}
obj* l_lean_parser_whitespace(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_3 = lean::string_iterator_remaining(x_1);
x_4 = lean::mk_nat_obj(1u);
x_5 = lean::nat_add(x_3, x_4);
lean::dec(x_3);
x_7 = l___private_init_lean_parser_token_2__whitespace__aux___main(x_5, x_0, x_1, x_2);
lean::dec(x_5);
x_9 = lean::cnstr_get(x_7, 0);
x_11 = lean::cnstr_get(x_7, 1);
if (lean::is_exclusive(x_7)) {
 x_13 = x_7;
} else {
 lean::inc(x_9);
 lean::inc(x_11);
 lean::dec(x_7);
 x_13 = lean::box(0);
}
x_14 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_15 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_14, x_9);
x_16 = l_mjoin___rarg___closed__1;
x_17 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_15, x_16);
if (lean::is_scalar(x_13)) {
 x_18 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_18 = x_13;
}
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_11);
return x_18;
}
}
obj* l_lean_parser_whitespace___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_parser_whitespace(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
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
obj* x_5; obj* x_6; 
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_as__substring___rarg___lambda__1), 3, 2);
lean::closure_set(x_5, 0, x_0);
lean::closure_set(x_5, 1, x_1);
x_6 = lean::apply_4(x_2, lean::box(0), lean::box(0), x_3, x_5);
return x_6;
}
}
obj* l_lean_parser_as__substring___rarg___lambda__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_6; obj* x_7; 
lean::inc(x_1);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_as__substring___rarg___lambda__2___boxed), 5, 4);
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
obj* x_4; obj* x_6; obj* x_9; obj* x_10; obj* x_13; obj* x_14; 
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
lean::dec(x_1);
x_9 = l_lean_parser_monad__parsec_left__over___rarg___closed__1;
x_10 = lean::apply_2(x_6, lean::box(0), x_9);
lean::inc(x_10);
lean::inc(x_4);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_as__substring___rarg___lambda__3), 5, 4);
lean::closure_set(x_13, 0, x_0);
lean::closure_set(x_13, 1, x_4);
lean::closure_set(x_13, 2, x_10);
lean::closure_set(x_13, 3, x_3);
x_14 = lean::apply_4(x_4, lean::box(0), lean::box(0), x_10, x_13);
return x_14;
}
}
obj* l_lean_parser_as__substring(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_as__substring___rarg___boxed), 4, 0);
return x_1;
}
}
obj* l_lean_parser_as__substring___rarg___lambda__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_lean_parser_as__substring___rarg___lambda__2(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_4);
return x_5;
}
}
obj* l_lean_parser_as__substring___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_parser_as__substring___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_lean_parser_as__substring___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_as__substring(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l___private_init_lean_parser_token_3__update__trailing___main(obj* x_0, obj* x_1) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_2; obj* x_4; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
if (lean::obj_tag(x_4) == 0)
{
lean::dec(x_2);
lean::dec(x_0);
return x_1;
}
else
{
obj* x_8; obj* x_9; obj* x_11; obj* x_12; obj* x_14; obj* x_15; obj* x_17; obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 x_8 = x_1;
} else {
 lean::dec(x_1);
 x_8 = lean::box(0);
}
x_9 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_release(x_2, 0);
 x_11 = x_2;
} else {
 lean::inc(x_9);
 lean::dec(x_2);
 x_11 = lean::box(0);
}
x_12 = lean::cnstr_get(x_4, 0);
if (lean::is_exclusive(x_4)) {
 x_14 = x_4;
} else {
 lean::inc(x_12);
 lean::dec(x_4);
 x_14 = lean::box(0);
}
x_15 = lean::cnstr_get(x_12, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_12, 1);
lean::inc(x_17);
lean::dec(x_12);
x_20 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_20, 0, x_15);
lean::cnstr_set(x_20, 1, x_17);
lean::cnstr_set(x_20, 2, x_0);
if (lean::is_scalar(x_14)) {
 x_21 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_21 = x_14;
}
lean::cnstr_set(x_21, 0, x_20);
if (lean::is_scalar(x_11)) {
 x_22 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_22 = x_11;
}
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_9);
if (lean::is_scalar(x_8)) {
 x_23 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_23 = x_8;
}
lean::cnstr_set(x_23, 0, x_22);
return x_23;
}
}
case 1:
{
obj* x_24; obj* x_26; 
x_24 = lean::cnstr_get(x_1, 0);
lean::inc(x_24);
x_26 = lean::cnstr_get(x_24, 0);
lean::inc(x_26);
if (lean::obj_tag(x_26) == 0)
{
lean::dec(x_0);
lean::dec(x_24);
return x_1;
}
else
{
obj* x_30; obj* x_31; obj* x_33; obj* x_35; obj* x_37; obj* x_39; obj* x_40; obj* x_42; obj* x_43; obj* x_45; obj* x_48; obj* x_49; obj* x_50; obj* x_51; 
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 x_30 = x_1;
} else {
 lean::dec(x_1);
 x_30 = lean::box(0);
}
x_31 = lean::cnstr_get(x_24, 1);
x_33 = lean::cnstr_get(x_24, 2);
x_35 = lean::cnstr_get(x_24, 3);
x_37 = lean::cnstr_get(x_24, 4);
if (lean::is_exclusive(x_24)) {
 lean::cnstr_release(x_24, 0);
 x_39 = x_24;
} else {
 lean::inc(x_31);
 lean::inc(x_33);
 lean::inc(x_35);
 lean::inc(x_37);
 lean::dec(x_24);
 x_39 = lean::box(0);
}
x_40 = lean::cnstr_get(x_26, 0);
if (lean::is_exclusive(x_26)) {
 x_42 = x_26;
} else {
 lean::inc(x_40);
 lean::dec(x_26);
 x_42 = lean::box(0);
}
x_43 = lean::cnstr_get(x_40, 0);
lean::inc(x_43);
x_45 = lean::cnstr_get(x_40, 1);
lean::inc(x_45);
lean::dec(x_40);
x_48 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_48, 0, x_43);
lean::cnstr_set(x_48, 1, x_45);
lean::cnstr_set(x_48, 2, x_0);
if (lean::is_scalar(x_42)) {
 x_49 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_49 = x_42;
}
lean::cnstr_set(x_49, 0, x_48);
if (lean::is_scalar(x_39)) {
 x_50 = lean::alloc_cnstr(0, 5, 0);
} else {
 x_50 = x_39;
}
lean::cnstr_set(x_50, 0, x_49);
lean::cnstr_set(x_50, 1, x_31);
lean::cnstr_set(x_50, 2, x_33);
lean::cnstr_set(x_50, 3, x_35);
lean::cnstr_set(x_50, 4, x_37);
if (lean::is_scalar(x_30)) {
 x_51 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_51 = x_30;
}
lean::cnstr_set(x_51, 0, x_50);
return x_51;
}
}
case 2:
{
obj* x_52; obj* x_54; obj* x_55; obj* x_57; obj* x_59; obj* x_60; obj* x_63; obj* x_64; 
x_52 = lean::cnstr_get(x_1, 0);
if (lean::is_exclusive(x_1)) {
 x_54 = x_1;
} else {
 lean::inc(x_52);
 lean::dec(x_1);
 x_54 = lean::box(0);
}
x_55 = lean::cnstr_get(x_52, 0);
lean::inc(x_55);
x_57 = lean::cnstr_get(x_52, 1);
lean::inc(x_57);
x_59 = l___private_init_lean_parser_token_3__update__trailing__lst___main(x_0, x_57);
x_60 = lean::cnstr_get(x_52, 2);
lean::inc(x_60);
lean::dec(x_52);
x_63 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_63, 0, x_55);
lean::cnstr_set(x_63, 1, x_59);
lean::cnstr_set(x_63, 2, x_60);
if (lean::is_scalar(x_54)) {
 x_64 = lean::alloc_cnstr(2, 1, 0);
} else {
 x_64 = x_54;
}
lean::cnstr_set(x_64, 0, x_63);
return x_64;
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
obj* x_3; 
x_3 = lean::cnstr_get(x_1, 1);
lean::inc(x_3);
if (lean::obj_tag(x_3) == 0)
{
obj* x_5; obj* x_7; obj* x_8; obj* x_9; 
x_5 = lean::cnstr_get(x_1, 0);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 1);
 x_7 = x_1;
} else {
 lean::inc(x_5);
 lean::dec(x_1);
 x_7 = lean::box(0);
}
x_8 = l___private_init_lean_parser_token_3__update__trailing___main(x_0, x_5);
if (lean::is_scalar(x_7)) {
 x_9 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_9 = x_7;
}
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_3);
return x_9;
}
else
{
obj* x_10; obj* x_14; obj* x_15; obj* x_16; 
x_10 = lean::cnstr_get(x_1, 0);
lean::inc(x_10);
lean::dec(x_1);
lean::inc(x_3);
x_14 = l___private_init_lean_parser_token_3__update__trailing__lst___main(x_0, x_3);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 1);
 x_15 = x_3;
} else {
 lean::dec(x_3);
 x_15 = lean::box(0);
}
if (lean::is_scalar(x_15)) {
 x_16 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_16 = x_15;
}
lean::cnstr_set(x_16, 0, x_10);
lean::cnstr_set(x_16, 1, x_14);
return x_16;
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
obj* x_4; 
x_4 = lean::apply_2(x_0, x_2, x_3);
return x_4;
}
}
obj* l_reader__t_lift___at_lean_parser_with__trailing___spec__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_lift___at_lean_parser_with__trailing___spec__1___rarg___boxed), 4, 0);
return x_1;
}
}
obj* l_reader__t_bind___at_lean_parser_with__trailing___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_6; obj* x_7; 
lean::inc(x_2);
x_6 = lean::apply_3(x_0, x_2, x_3, x_4);
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
if (lean::obj_tag(x_7) == 0)
{
obj* x_9; obj* x_12; obj* x_14; obj* x_16; obj* x_19; obj* x_20; obj* x_22; obj* x_24; obj* x_25; obj* x_26; 
x_9 = lean::cnstr_get(x_6, 1);
lean::inc(x_9);
lean::dec(x_6);
x_12 = lean::cnstr_get(x_7, 0);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_7, 1);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_7, 2);
lean::inc(x_16);
lean::dec(x_7);
x_19 = lean::apply_4(x_1, x_12, x_2, x_14, x_9);
x_20 = lean::cnstr_get(x_19, 0);
x_22 = lean::cnstr_get(x_19, 1);
if (lean::is_exclusive(x_19)) {
 x_24 = x_19;
} else {
 lean::inc(x_20);
 lean::inc(x_22);
 lean::dec(x_19);
 x_24 = lean::box(0);
}
x_25 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_20);
if (lean::is_scalar(x_24)) {
 x_26 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_26 = x_24;
}
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_22);
return x_26;
}
else
{
obj* x_29; obj* x_31; obj* x_32; uint8 x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
lean::dec(x_1);
lean::dec(x_2);
x_29 = lean::cnstr_get(x_6, 1);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 x_31 = x_6;
} else {
 lean::inc(x_29);
 lean::dec(x_6);
 x_31 = lean::box(0);
}
x_32 = lean::cnstr_get(x_7, 0);
x_34 = lean::cnstr_get_scalar<uint8>(x_7, sizeof(void*)*1);
if (lean::is_exclusive(x_7)) {
 x_35 = x_7;
} else {
 lean::inc(x_32);
 lean::dec(x_7);
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
return x_38;
}
}
}
obj* l_reader__t_bind___at_lean_parser_with__trailing___spec__2(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_bind___at_lean_parser_with__trailing___spec__2___rarg), 5, 0);
return x_2;
}
}
obj* l_lean_parser_with__trailing___rarg___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_5; 
x_2 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_0);
x_4 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_0);
lean::cnstr_set(x_4, 2, x_2);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_1);
return x_5;
}
}
obj* l_lean_parser_with__trailing___rarg___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = l_lean_parser_whitespace(x_1, x_2, x_3);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
if (lean::obj_tag(x_5) == 0)
{
obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_14; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_7 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_9 = x_4;
} else {
 lean::inc(x_7);
 lean::dec(x_4);
 x_9 = lean::box(0);
}
x_10 = lean::cnstr_get(x_5, 1);
x_12 = lean::cnstr_get(x_5, 2);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 x_14 = x_5;
} else {
 lean::inc(x_10);
 lean::inc(x_12);
 lean::dec(x_5);
 x_14 = lean::box(0);
}
lean::inc(x_10);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_0);
lean::cnstr_set(x_16, 1, x_10);
x_17 = l_lean_parser_finish__comment__block___closed__2;
if (lean::is_scalar(x_14)) {
 x_18 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_18 = x_14;
}
lean::cnstr_set(x_18, 0, x_16);
lean::cnstr_set(x_18, 1, x_10);
lean::cnstr_set(x_18, 2, x_17);
x_19 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_12, x_18);
if (lean::is_scalar(x_9)) {
 x_20 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_20 = x_9;
}
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_7);
return x_20;
}
else
{
obj* x_22; obj* x_24; obj* x_25; uint8 x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; 
lean::dec(x_0);
x_22 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_24 = x_4;
} else {
 lean::inc(x_22);
 lean::dec(x_4);
 x_24 = lean::box(0);
}
x_25 = lean::cnstr_get(x_5, 0);
x_27 = lean::cnstr_get_scalar<uint8>(x_5, sizeof(void*)*1);
if (lean::is_exclusive(x_5)) {
 x_28 = x_5;
} else {
 lean::inc(x_25);
 lean::dec(x_5);
 x_28 = lean::box(0);
}
if (lean::is_scalar(x_28)) {
 x_29 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_29 = x_28;
}
lean::cnstr_set(x_29, 0, x_25);
lean::cnstr_set_scalar(x_29, sizeof(void*)*1, x_27);
x_30 = x_29;
if (lean::is_scalar(x_24)) {
 x_31 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_31 = x_24;
}
lean::cnstr_set(x_31, 0, x_30);
lean::cnstr_set(x_31, 1, x_22);
return x_31;
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
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_lift___at_lean_parser_with__trailing___spec__1___rarg___boxed), 4, 1);
lean::closure_set(x_1, 0, x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_with__trailing___rarg___lambda__2___boxed), 4, 0);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_bind___at_lean_parser_with__trailing___spec__2___rarg), 5, 2);
lean::closure_set(x_3, 0, x_1);
lean::closure_set(x_3, 1, x_2);
return x_3;
}
}
obj* l_lean_parser_with__trailing___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
x_6 = l_lean_parser_with__trailing___rarg___closed__1;
x_7 = lean::apply_2(x_2, lean::box(0), x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_with__trailing___rarg___lambda__3), 3, 2);
lean::closure_set(x_8, 0, x_0);
lean::closure_set(x_8, 1, x_3);
x_9 = lean::apply_4(x_4, lean::box(0), lean::box(0), x_7, x_8);
return x_9;
}
}
obj* l_lean_parser_with__trailing(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_with__trailing___rarg___boxed), 4, 0);
return x_1;
}
}
obj* l_reader__t_lift___at_lean_parser_with__trailing___spec__1___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_reader__t_lift___at_lean_parser_with__trailing___spec__1___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_reader__t_lift___at_lean_parser_with__trailing___spec__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_reader__t_lift___at_lean_parser_with__trailing___spec__1(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_reader__t_bind___at_lean_parser_with__trailing___spec__2___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_reader__t_bind___at_lean_parser_with__trailing___spec__2(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_lean_parser_with__trailing___rarg___lambda__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_parser_with__trailing___rarg___lambda__2(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_lean_parser_with__trailing___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_parser_with__trailing___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_lean_parser_with__trailing___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_with__trailing(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_parser_mk__raw__res(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; obj* x_7; obj* x_8; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_16; obj* x_17; 
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
lean::dec(x_4);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_13);
lean::cnstr_set(x_16, 1, x_14);
x_17 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_17, 0, x_16);
return x_17;
}
}
obj* l_lean_parser_raw___rarg___lambda__1(obj* x_0, uint8 x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_lean_parser_mk__raw__res(x_0, x_5);
if (x_1 == 0)
{
obj* x_8; obj* x_11; obj* x_14; 
lean::dec(x_4);
x_8 = lean::cnstr_get(x_2, 0);
lean::inc(x_8);
lean::dec(x_2);
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
lean::dec(x_8);
x_14 = lean::apply_2(x_11, lean::box(0), x_6);
return x_14;
}
else
{
obj* x_15; 
x_15 = l_lean_parser_with__trailing___rarg(x_2, x_3, x_4, x_6);
return x_15;
}
}
}
obj* l_lean_parser_raw___rarg___lambda__2(obj* x_0, uint8 x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; obj* x_9; obj* x_10; 
x_8 = lean::box(x_1);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_raw___rarg___lambda__1___boxed), 6, 5);
lean::closure_set(x_9, 0, x_0);
lean::closure_set(x_9, 1, x_8);
lean::closure_set(x_9, 2, x_2);
lean::closure_set(x_9, 3, x_3);
lean::closure_set(x_9, 4, x_4);
x_10 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_6, x_9);
return x_10;
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
obj* x_6; obj* x_8; obj* x_10; obj* x_11; obj* x_12; obj* x_15; obj* x_16; 
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 0);
lean::inc(x_8);
x_10 = l_lean_parser_monad__parsec_left__over___rarg___closed__1;
x_11 = lean::apply_2(x_8, lean::box(0), x_10);
x_12 = lean::box(x_5);
lean::inc(x_11);
lean::inc(x_6);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_raw___rarg___lambda__3___boxed), 8, 7);
lean::closure_set(x_15, 0, x_12);
lean::closure_set(x_15, 1, x_0);
lean::closure_set(x_15, 2, x_1);
lean::closure_set(x_15, 3, x_2);
lean::closure_set(x_15, 4, x_6);
lean::closure_set(x_15, 5, x_11);
lean::closure_set(x_15, 6, x_4);
x_16 = lean::apply_4(x_6, lean::box(0), lean::box(0), x_11, x_15);
return x_16;
}
}
obj* l_lean_parser_raw(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_raw___rarg___boxed), 6, 0);
return x_1;
}
}
obj* l_lean_parser_raw___rarg___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; obj* x_7; 
x_6 = lean::unbox(x_1);
x_7 = l_lean_parser_raw___rarg___lambda__1(x_0, x_6, x_2, x_3, x_4, x_5);
lean::dec(x_3);
return x_7;
}
}
obj* l_lean_parser_raw___rarg___lambda__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
uint8 x_8; obj* x_9; 
x_8 = lean::unbox(x_1);
x_9 = l_lean_parser_raw___rarg___lambda__2(x_0, x_8, x_2, x_3, x_4, x_5, x_6, x_7);
lean::dec(x_7);
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
lean::dec(x_3);
return x_7;
}
}
obj* l_lean_parser_raw___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_raw(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_parser_raw_tokens(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, uint8 x_6) {
_start:
{
obj* x_7; 
x_7 = lean::box(0);
return x_7;
}
}
obj* l_lean_parser_raw_tokens___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
uint8 x_7; obj* x_8; 
x_7 = lean::unbox(x_6);
x_8 = l_lean_parser_raw_tokens(x_0, x_1, x_2, x_3, x_4, x_5, x_7);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
lean::dec(x_4);
lean::dec(x_5);
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
case 3:
{
obj* x_5; 
x_5 = lean::box(0);
return x_5;
}
default:
{
obj* x_7; 
lean::dec(x_0);
x_7 = lean::box(0);
return x_7;
}
}
}
}
obj* _init_l_lean_parser_raw_view___rarg___lambda__2___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::box(3);
x_2 = l_option_get__or__else___main___rarg(x_0, x_1);
return x_2;
}
}
obj* l_lean_parser_raw_view___rarg___lambda__2(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_1; 
x_1 = l_lean_parser_raw_view___rarg___lambda__2___closed__1;
return x_1;
}
else
{
obj* x_2; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_2 = lean::cnstr_get(x_0, 0);
if (lean::is_exclusive(x_0)) {
 x_4 = x_0;
} else {
 lean::inc(x_2);
 lean::dec(x_0);
 x_4 = lean::box(0);
}
x_5 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_5, 0, x_2);
if (lean::is_scalar(x_4)) {
 x_6 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_6 = x_4;
}
lean::cnstr_set(x_6, 0, x_5);
x_7 = lean::box(3);
x_8 = l_option_get__or__else___main___rarg(x_6, x_7);
lean::dec(x_6);
return x_8;
}
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
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_raw_view___rarg___lambda__2), 1, 0);
return x_0;
}
}
obj* l_lean_parser_raw_view___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, uint8 x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; 
x_6 = l_lean_parser_raw_view___rarg___closed__1;
x_7 = l_lean_parser_raw_view___rarg___closed__2;
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set(x_8, 1, x_7);
return x_8;
}
}
obj* l_lean_parser_raw_view(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_raw_view___rarg___boxed), 6, 0);
return x_1;
}
}
obj* l_lean_parser_raw_view___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; obj* x_7; 
x_6 = lean::unbox(x_5);
x_7 = l_lean_parser_raw_view___rarg(x_0, x_1, x_2, x_3, x_4, x_6);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
lean::dec(x_4);
return x_7;
}
}
obj* l_lean_parser_raw_view___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_raw_view(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_parser_raw__str_lean_parser_has__tokens(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, uint8 x_5) {
_start:
{
obj* x_6; 
x_6 = lean::box(0);
return x_6;
}
}
obj* l_lean_parser_raw__str_lean_parser_has__tokens___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; obj* x_7; 
x_6 = lean::unbox(x_5);
x_7 = l_lean_parser_raw__str_lean_parser_has__tokens(x_0, x_1, x_2, x_3, x_4, x_6);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
lean::dec(x_4);
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
lean::dec(x_10);
lean::dec(x_1);
lean::dec(x_0);
return x_11;
}
}
obj* l_lean_parser_raw__str_lean_parser_has__view(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_raw__str_lean_parser_has__view___rarg___boxed), 5, 0);
return x_1;
}
}
obj* l_lean_parser_raw__str_lean_parser_has__view___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; obj* x_6; 
x_5 = lean::unbox(x_4);
x_6 = l_lean_parser_raw__str_lean_parser_has__view___rarg(x_0, x_1, x_2, x_3, x_5);
lean::dec(x_2);
return x_6;
}
}
obj* l_lean_parser_raw__str_lean_parser_has__view___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_raw__str_lean_parser_has__view(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_parser_raw__str___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, uint8 x_4) {
_start:
{
obj* x_6; obj* x_7; obj* x_10; obj* x_11; obj* x_13; obj* x_15; obj* x_16; obj* x_17; obj* x_20; obj* x_21; 
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
x_16 = lean::apply_2(x_13, lean::box(0), x_15);
x_17 = lean::box(x_4);
lean::inc(x_16);
lean::inc(x_11);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_raw___rarg___lambda__3___boxed), 8, 7);
lean::closure_set(x_20, 0, x_17);
lean::closure_set(x_20, 1, x_0);
lean::closure_set(x_20, 2, x_1);
lean::closure_set(x_20, 3, x_2);
lean::closure_set(x_20, 4, x_11);
lean::closure_set(x_20, 5, x_16);
lean::closure_set(x_20, 6, x_10);
x_21 = lean::apply_4(x_11, lean::box(0), lean::box(0), x_16, x_20);
return x_21;
}
}
obj* l_lean_parser_raw__str(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_raw__str___rarg___boxed), 5, 0);
return x_1;
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
obj* l_lean_parser_raw__str___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_raw__str(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_parser_raw__str_view__default___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, uint8 x_4) {
_start:
{
obj* x_5; 
x_5 = lean::box(0);
return x_5;
}
}
obj* l_lean_parser_raw__str_view__default(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_raw__str_view__default___rarg___boxed), 5, 0);
return x_1;
}
}
obj* l_lean_parser_raw__str_view__default___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; obj* x_6; 
x_5 = lean::unbox(x_4);
x_6 = l_lean_parser_raw__str_view__default___rarg(x_0, x_1, x_2, x_3, x_5);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
return x_6;
}
}
obj* l_lean_parser_raw__str_view__default___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_raw__str_view__default(x_0);
lean::dec(x_0);
return x_1;
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
case 3:
{
obj* x_11; 
x_11 = lean::box(0);
x_5 = x_11;
goto lbl_6;
}
default:
{
obj* x_13; 
lean::dec(x_1);
x_13 = lean::box(0);
x_5 = x_13;
goto lbl_6;
}
}
lbl_6:
{
obj* x_14; obj* x_15; obj* x_17; obj* x_18; 
if (lean::obj_tag(x_0) == 0)
{
obj* x_20; 
x_20 = lean::box(3);
x_17 = x_0;
x_18 = x_20;
goto lbl_19;
}
else
{
obj* x_21; obj* x_23; 
x_21 = lean::cnstr_get(x_0, 0);
lean::inc(x_21);
x_23 = lean::cnstr_get(x_0, 1);
lean::inc(x_23);
lean::dec(x_0);
x_17 = x_23;
x_18 = x_21;
goto lbl_19;
}
lbl_16:
{
switch (lean::obj_tag(x_15)) {
case 0:
{
obj* x_26; obj* x_29; obj* x_30; 
x_26 = lean::cnstr_get(x_15, 0);
lean::inc(x_26);
lean::dec(x_15);
x_29 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_29, 0, x_26);
x_30 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_30, 0, x_5);
lean::cnstr_set(x_30, 1, x_14);
lean::cnstr_set(x_30, 2, x_29);
return x_30;
}
case 3:
{
obj* x_31; obj* x_32; 
x_31 = lean::box(0);
x_32 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_32, 0, x_5);
lean::cnstr_set(x_32, 1, x_14);
lean::cnstr_set(x_32, 2, x_31);
return x_32;
}
default:
{
obj* x_34; obj* x_35; 
lean::dec(x_15);
x_34 = lean::box(0);
x_35 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_35, 0, x_5);
lean::cnstr_set(x_35, 1, x_14);
lean::cnstr_set(x_35, 2, x_34);
return x_35;
}
}
}
lbl_19:
{
switch (lean::obj_tag(x_18)) {
case 0:
{
obj* x_36; obj* x_39; 
x_36 = lean::cnstr_get(x_18, 0);
lean::inc(x_36);
lean::dec(x_18);
x_39 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_39, 0, x_36);
if (lean::obj_tag(x_17) == 0)
{
obj* x_40; obj* x_41; 
x_40 = lean::box(0);
x_41 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_41, 0, x_5);
lean::cnstr_set(x_41, 1, x_39);
lean::cnstr_set(x_41, 2, x_40);
return x_41;
}
else
{
obj* x_42; 
x_42 = lean::cnstr_get(x_17, 0);
lean::inc(x_42);
lean::dec(x_17);
x_14 = x_39;
x_15 = x_42;
goto lbl_16;
}
}
case 3:
{
obj* x_45; 
x_45 = lean::box(0);
if (lean::obj_tag(x_17) == 0)
{
obj* x_46; 
x_46 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_46, 0, x_5);
lean::cnstr_set(x_46, 1, x_45);
lean::cnstr_set(x_46, 2, x_45);
return x_46;
}
else
{
obj* x_47; 
x_47 = lean::cnstr_get(x_17, 0);
lean::inc(x_47);
lean::dec(x_17);
x_14 = x_45;
x_15 = x_47;
goto lbl_16;
}
}
default:
{
obj* x_51; 
lean::dec(x_18);
x_51 = lean::box(0);
if (lean::obj_tag(x_17) == 0)
{
obj* x_52; 
x_52 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_52, 0, x_5);
lean::cnstr_set(x_52, 1, x_51);
lean::cnstr_set(x_52, 2, x_51);
return x_52;
}
else
{
obj* x_53; 
x_53 = lean::cnstr_get(x_17, 0);
lean::inc(x_53);
lean::dec(x_17);
x_14 = x_51;
x_15 = x_53;
goto lbl_16;
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
obj* x_5; 
x_5 = l_lean_parser_detail__ident__part__escaped_has__view_x_27___lambda__1___closed__1;
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
switch (lean::obj_tag(x_2)) {
case 0:
{
obj* x_20; obj* x_23; 
x_20 = lean::cnstr_get(x_2, 0);
lean::inc(x_20);
lean::dec(x_2);
x_23 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_23, 0, x_20);
x_18 = x_23;
goto lbl_19;
}
case 3:
{
obj* x_24; 
x_24 = lean::box(0);
x_18 = x_24;
goto lbl_19;
}
default:
{
obj* x_26; 
lean::dec(x_2);
x_26 = lean::box(0);
x_18 = x_26;
goto lbl_19;
}
}
lbl_19:
{
obj* x_27; obj* x_28; obj* x_30; obj* x_31; 
if (lean::obj_tag(x_1) == 0)
{
obj* x_33; 
x_33 = lean::box(3);
x_30 = x_1;
x_31 = x_33;
goto lbl_32;
}
else
{
obj* x_34; obj* x_36; 
x_34 = lean::cnstr_get(x_1, 0);
lean::inc(x_34);
x_36 = lean::cnstr_get(x_1, 1);
lean::inc(x_36);
lean::dec(x_1);
x_30 = x_36;
x_31 = x_34;
goto lbl_32;
}
lbl_29:
{
switch (lean::obj_tag(x_28)) {
case 0:
{
obj* x_39; obj* x_42; obj* x_43; 
x_39 = lean::cnstr_get(x_28, 0);
lean::inc(x_39);
lean::dec(x_28);
x_42 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_42, 0, x_39);
x_43 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_43, 0, x_18);
lean::cnstr_set(x_43, 1, x_27);
lean::cnstr_set(x_43, 2, x_42);
return x_43;
}
case 3:
{
obj* x_44; obj* x_45; 
x_44 = lean::box(0);
x_45 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_45, 0, x_18);
lean::cnstr_set(x_45, 1, x_27);
lean::cnstr_set(x_45, 2, x_44);
return x_45;
}
default:
{
obj* x_47; obj* x_48; 
lean::dec(x_28);
x_47 = lean::box(0);
x_48 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_48, 0, x_18);
lean::cnstr_set(x_48, 1, x_27);
lean::cnstr_set(x_48, 2, x_47);
return x_48;
}
}
}
lbl_32:
{
switch (lean::obj_tag(x_31)) {
case 0:
{
obj* x_49; obj* x_52; 
x_49 = lean::cnstr_get(x_31, 0);
lean::inc(x_49);
lean::dec(x_31);
x_52 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_52, 0, x_49);
if (lean::obj_tag(x_30) == 0)
{
obj* x_53; obj* x_54; 
x_53 = lean::box(0);
x_54 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_54, 0, x_18);
lean::cnstr_set(x_54, 1, x_52);
lean::cnstr_set(x_54, 2, x_53);
return x_54;
}
else
{
obj* x_55; 
x_55 = lean::cnstr_get(x_30, 0);
lean::inc(x_55);
lean::dec(x_30);
x_27 = x_52;
x_28 = x_55;
goto lbl_29;
}
}
case 3:
{
obj* x_58; 
x_58 = lean::box(0);
if (lean::obj_tag(x_30) == 0)
{
obj* x_59; 
x_59 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_59, 0, x_18);
lean::cnstr_set(x_59, 1, x_58);
lean::cnstr_set(x_59, 2, x_58);
return x_59;
}
else
{
obj* x_60; 
x_60 = lean::cnstr_get(x_30, 0);
lean::inc(x_60);
lean::dec(x_30);
x_27 = x_58;
x_28 = x_60;
goto lbl_29;
}
}
default:
{
obj* x_64; 
lean::dec(x_31);
x_64 = lean::box(0);
if (lean::obj_tag(x_30) == 0)
{
obj* x_65; 
x_65 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_65, 0, x_18);
lean::cnstr_set(x_65, 1, x_64);
lean::cnstr_set(x_65, 2, x_64);
return x_65;
}
else
{
obj* x_66; 
x_66 = lean::cnstr_get(x_30, 0);
lean::inc(x_66);
lean::dec(x_30);
x_27 = x_64;
x_28 = x_66;
goto lbl_29;
}
}
}
}
}
}
}
}
obj* _init_l_lean_parser_detail__ident__part__escaped_has__view_x_27___lambda__2___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_0 = lean::box(0);
x_1 = lean::box(0);
x_2 = lean::box(3);
x_3 = l_option_get__or__else___main___rarg(x_1, x_2);
lean::inc(x_3);
x_5 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_5, 0, x_3);
lean::cnstr_set(x_5, 1, x_0);
lean::inc(x_3);
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_3);
lean::cnstr_set(x_7, 1, x_5);
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_3);
lean::cnstr_set(x_8, 1, x_7);
x_9 = l_lean_parser_detail__ident__part__escaped;
x_10 = l_lean_parser_syntax_mk__node(x_9, x_8);
return x_10;
}
}
obj* _init_l_lean_parser_detail__ident__part__escaped_has__view_x_27___lambda__2___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = lean::box(0);
x_1 = lean::box(0);
x_2 = lean::box(3);
x_3 = l_option_get__or__else___main___rarg(x_1, x_2);
x_4 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_0);
return x_4;
}
}
obj* _init_l_lean_parser_detail__ident__part__escaped_has__view_x_27___lambda__2___closed__3() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_5; obj* x_6; 
x_0 = lean::box(0);
x_1 = lean::box(0);
x_2 = lean::box(3);
x_3 = l_option_get__or__else___main___rarg(x_1, x_2);
lean::inc(x_3);
x_5 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_5, 0, x_3);
lean::cnstr_set(x_5, 1, x_0);
x_6 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_6, 0, x_3);
lean::cnstr_set(x_6, 1, x_5);
return x_6;
}
}
obj* l_lean_parser_detail__ident__part__escaped_has__view_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_5; obj* x_8; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 2);
lean::inc(x_5);
lean::dec(x_0);
x_8 = lean::box(0);
if (lean::obj_tag(x_1) == 0)
{
if (lean::obj_tag(x_3) == 0)
{
if (lean::obj_tag(x_5) == 0)
{
obj* x_9; 
x_9 = l_lean_parser_detail__ident__part__escaped_has__view_x_27___lambda__2___closed__1;
return x_9;
}
else
{
obj* x_10; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
x_10 = lean::cnstr_get(x_5, 0);
if (lean::is_exclusive(x_5)) {
 x_12 = x_5;
} else {
 lean::inc(x_10);
 lean::dec(x_5);
 x_12 = lean::box(0);
}
x_13 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_13, 0, x_10);
if (lean::is_scalar(x_12)) {
 x_14 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_14 = x_12;
}
lean::cnstr_set(x_14, 0, x_13);
x_15 = lean::box(3);
x_16 = l_option_get__or__else___main___rarg(x_14, x_15);
lean::dec(x_14);
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_16);
lean::cnstr_set(x_18, 1, x_8);
x_19 = l_lean_parser_raw_view___rarg___lambda__2___closed__1;
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_18);
x_21 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_21, 0, x_19);
lean::cnstr_set(x_21, 1, x_20);
x_22 = l_lean_parser_detail__ident__part__escaped;
x_23 = l_lean_parser_syntax_mk__node(x_22, x_21);
return x_23;
}
}
else
{
obj* x_24; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_24 = lean::cnstr_get(x_3, 0);
if (lean::is_exclusive(x_3)) {
 x_26 = x_3;
} else {
 lean::inc(x_24);
 lean::dec(x_3);
 x_26 = lean::box(0);
}
x_27 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_27, 0, x_24);
if (lean::is_scalar(x_26)) {
 x_28 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_28 = x_26;
}
lean::cnstr_set(x_28, 0, x_27);
x_29 = lean::box(3);
x_30 = l_option_get__or__else___main___rarg(x_28, x_29);
lean::dec(x_28);
if (lean::obj_tag(x_5) == 0)
{
obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; 
x_32 = l_lean_parser_detail__ident__part__escaped_has__view_x_27___lambda__2___closed__2;
x_33 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_33, 0, x_30);
lean::cnstr_set(x_33, 1, x_32);
x_34 = l_lean_parser_raw_view___rarg___lambda__2___closed__1;
x_35 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_33);
x_36 = l_lean_parser_detail__ident__part__escaped;
x_37 = l_lean_parser_syntax_mk__node(x_36, x_35);
return x_37;
}
else
{
obj* x_38; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; 
x_38 = lean::cnstr_get(x_5, 0);
if (lean::is_exclusive(x_5)) {
 x_40 = x_5;
} else {
 lean::inc(x_38);
 lean::dec(x_5);
 x_40 = lean::box(0);
}
x_41 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_41, 0, x_38);
if (lean::is_scalar(x_40)) {
 x_42 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_42 = x_40;
}
lean::cnstr_set(x_42, 0, x_41);
x_43 = l_option_get__or__else___main___rarg(x_42, x_29);
lean::dec(x_42);
x_45 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_45, 0, x_43);
lean::cnstr_set(x_45, 1, x_8);
x_46 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_46, 0, x_30);
lean::cnstr_set(x_46, 1, x_45);
x_47 = l_lean_parser_raw_view___rarg___lambda__2___closed__1;
x_48 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_48, 0, x_47);
lean::cnstr_set(x_48, 1, x_46);
x_49 = l_lean_parser_detail__ident__part__escaped;
x_50 = l_lean_parser_syntax_mk__node(x_49, x_48);
return x_50;
}
}
}
else
{
obj* x_51; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; 
x_51 = lean::cnstr_get(x_1, 0);
if (lean::is_exclusive(x_1)) {
 x_53 = x_1;
} else {
 lean::inc(x_51);
 lean::dec(x_1);
 x_53 = lean::box(0);
}
x_54 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_54, 0, x_51);
if (lean::is_scalar(x_53)) {
 x_55 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_55 = x_53;
}
lean::cnstr_set(x_55, 0, x_54);
x_56 = lean::box(3);
x_57 = l_option_get__or__else___main___rarg(x_55, x_56);
lean::dec(x_55);
if (lean::obj_tag(x_3) == 0)
{
if (lean::obj_tag(x_5) == 0)
{
obj* x_59; obj* x_60; obj* x_61; obj* x_62; 
x_59 = l_lean_parser_detail__ident__part__escaped_has__view_x_27___lambda__2___closed__3;
x_60 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_60, 0, x_57);
lean::cnstr_set(x_60, 1, x_59);
x_61 = l_lean_parser_detail__ident__part__escaped;
x_62 = l_lean_parser_syntax_mk__node(x_61, x_60);
return x_62;
}
else
{
obj* x_63; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; 
x_63 = lean::cnstr_get(x_5, 0);
if (lean::is_exclusive(x_5)) {
 x_65 = x_5;
} else {
 lean::inc(x_63);
 lean::dec(x_5);
 x_65 = lean::box(0);
}
x_66 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_66, 0, x_63);
if (lean::is_scalar(x_65)) {
 x_67 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_67 = x_65;
}
lean::cnstr_set(x_67, 0, x_66);
x_68 = l_option_get__or__else___main___rarg(x_67, x_56);
lean::dec(x_67);
x_70 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_70, 0, x_68);
lean::cnstr_set(x_70, 1, x_8);
x_71 = l_lean_parser_raw_view___rarg___lambda__2___closed__1;
x_72 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_72, 0, x_71);
lean::cnstr_set(x_72, 1, x_70);
x_73 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_73, 0, x_57);
lean::cnstr_set(x_73, 1, x_72);
x_74 = l_lean_parser_detail__ident__part__escaped;
x_75 = l_lean_parser_syntax_mk__node(x_74, x_73);
return x_75;
}
}
else
{
obj* x_76; obj* x_78; obj* x_79; obj* x_80; obj* x_81; 
x_76 = lean::cnstr_get(x_3, 0);
if (lean::is_exclusive(x_3)) {
 x_78 = x_3;
} else {
 lean::inc(x_76);
 lean::dec(x_3);
 x_78 = lean::box(0);
}
x_79 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_79, 0, x_76);
if (lean::is_scalar(x_78)) {
 x_80 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_80 = x_78;
}
lean::cnstr_set(x_80, 0, x_79);
x_81 = l_option_get__or__else___main___rarg(x_80, x_56);
lean::dec(x_80);
if (lean::obj_tag(x_5) == 0)
{
obj* x_83; obj* x_84; obj* x_85; obj* x_86; obj* x_87; 
x_83 = l_lean_parser_detail__ident__part__escaped_has__view_x_27___lambda__2___closed__2;
x_84 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_84, 0, x_81);
lean::cnstr_set(x_84, 1, x_83);
x_85 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_85, 0, x_57);
lean::cnstr_set(x_85, 1, x_84);
x_86 = l_lean_parser_detail__ident__part__escaped;
x_87 = l_lean_parser_syntax_mk__node(x_86, x_85);
return x_87;
}
else
{
obj* x_88; obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_95; obj* x_96; obj* x_97; obj* x_98; obj* x_99; 
x_88 = lean::cnstr_get(x_5, 0);
if (lean::is_exclusive(x_5)) {
 x_90 = x_5;
} else {
 lean::inc(x_88);
 lean::dec(x_5);
 x_90 = lean::box(0);
}
x_91 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_91, 0, x_88);
if (lean::is_scalar(x_90)) {
 x_92 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_92 = x_90;
}
lean::cnstr_set(x_92, 0, x_91);
x_93 = l_option_get__or__else___main___rarg(x_92, x_56);
lean::dec(x_92);
x_95 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_95, 0, x_93);
lean::cnstr_set(x_95, 1, x_8);
x_96 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_96, 0, x_81);
lean::cnstr_set(x_96, 1, x_95);
x_97 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_97, 0, x_57);
lean::cnstr_set(x_97, 1, x_96);
x_98 = l_lean_parser_detail__ident__part__escaped;
x_99 = l_lean_parser_syntax_mk__node(x_98, x_97);
return x_99;
}
}
}
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
lean::dec(x_1);
if (x_6 == 0)
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_8; obj* x_11; obj* x_12; 
x_8 = lean::cnstr_get(x_0, 0);
lean::inc(x_8);
lean::dec(x_0);
x_11 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_11, 0, x_8);
x_12 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_12, 0, x_11);
return x_12;
}
case 3:
{
obj* x_13; 
x_13 = l_lean_parser_detail__ident__part_has__view_x_27___lambda__1___closed__1;
return x_13;
}
default:
{
obj* x_15; 
lean::dec(x_0);
x_15 = l_lean_parser_detail__ident__part_has__view_x_27___lambda__1___closed__1;
return x_15;
}
}
}
else
{
obj* x_16; obj* x_17; obj* x_20; obj* x_21; 
x_16 = l_lean_parser_detail__ident__part__escaped_has__view;
x_17 = lean::cnstr_get(x_16, 0);
lean::inc(x_17);
lean::dec(x_16);
x_20 = lean::apply_1(x_17, x_0);
x_21 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_21, 0, x_20);
return x_21;
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
obj* x_5; 
x_5 = l_lean_parser_detail__ident__part_has__view_x_27___lambda__1___closed__2;
return x_5;
}
else
{
obj* x_6; obj* x_9; obj* x_11; obj* x_14; uint8 x_15; 
x_6 = lean::cnstr_get(x_4, 0);
lean::inc(x_6);
lean::dec(x_4);
x_9 = lean::cnstr_get(x_6, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_6, 1);
lean::inc(x_11);
lean::dec(x_6);
x_14 = l_lean_parser_detail__ident__part_has__view_x_27___lambda__1___closed__3;
x_15 = lean_name_dec_eq(x_9, x_14);
lean::dec(x_9);
if (x_15 == 0)
{
obj* x_18; 
lean::dec(x_11);
x_18 = l_lean_parser_detail__ident__part_has__view_x_27___lambda__1___closed__2;
return x_18;
}
else
{
if (lean::obj_tag(x_11) == 0)
{
obj* x_19; 
x_19 = l_lean_parser_detail__ident__part_has__view_x_27___lambda__1___closed__2;
return x_19;
}
else
{
obj* x_20; 
x_20 = lean::cnstr_get(x_11, 1);
lean::inc(x_20);
if (lean::obj_tag(x_20) == 0)
{
obj* x_22; obj* x_25; 
x_22 = lean::cnstr_get(x_11, 0);
lean::inc(x_22);
lean::dec(x_11);
x_25 = l_lean_parser_syntax_as__node___main(x_22);
if (lean::obj_tag(x_25) == 0)
{
obj* x_26; 
x_26 = l_lean_parser_detail__ident__part_has__view_x_27___lambda__1___closed__2;
return x_26;
}
else
{
obj* x_27; obj* x_30; 
x_27 = lean::cnstr_get(x_25, 0);
lean::inc(x_27);
lean::dec(x_25);
x_30 = lean::cnstr_get(x_27, 0);
lean::inc(x_30);
switch (lean::obj_tag(x_30)) {
case 0:
{
obj* x_33; 
lean::dec(x_27);
x_33 = l_lean_parser_detail__ident__part_has__view_x_27___lambda__1___closed__2;
return x_33;
}
case 1:
{
obj* x_36; 
lean::dec(x_27);
lean::dec(x_30);
x_36 = l_lean_parser_detail__ident__part_has__view_x_27___lambda__1___closed__2;
return x_36;
}
default:
{
obj* x_37; obj* x_40; obj* x_42; obj* x_45; uint8 x_46; 
x_37 = lean::cnstr_get(x_27, 1);
lean::inc(x_37);
lean::dec(x_27);
x_40 = lean::cnstr_get(x_30, 0);
lean::inc(x_40);
x_42 = lean::cnstr_get(x_30, 1);
lean::inc(x_42);
lean::dec(x_30);
x_45 = lean::box(0);
x_46 = lean_name_dec_eq(x_40, x_45);
lean::dec(x_40);
if (x_46 == 0)
{
obj* x_50; 
lean::dec(x_42);
lean::dec(x_37);
x_50 = l_lean_parser_detail__ident__part_has__view_x_27___lambda__1___closed__2;
return x_50;
}
else
{
if (lean::obj_tag(x_37) == 0)
{
obj* x_52; 
lean::dec(x_42);
x_52 = l_lean_parser_detail__ident__part_has__view_x_27___lambda__1___closed__2;
return x_52;
}
else
{
obj* x_53; 
x_53 = lean::cnstr_get(x_37, 1);
lean::inc(x_53);
if (lean::obj_tag(x_53) == 0)
{
obj* x_55; 
x_55 = lean::cnstr_get(x_37, 0);
lean::inc(x_55);
lean::dec(x_37);
x_1 = x_55;
x_2 = x_42;
goto lbl_3;
}
else
{
obj* x_61; 
lean::dec(x_42);
lean::dec(x_53);
lean::dec(x_37);
x_61 = l_lean_parser_detail__ident__part_has__view_x_27___lambda__1___closed__2;
return x_61;
}
}
}
}
}
}
}
else
{
obj* x_64; 
lean::dec(x_11);
lean::dec(x_20);
x_64 = l_lean_parser_detail__ident__part_has__view_x_27___lambda__1___closed__2;
return x_64;
}
}
}
}
lbl_3:
{
obj* x_65; uint8 x_66; 
x_65 = lean::mk_nat_obj(0u);
x_66 = lean::nat_dec_eq(x_2, x_65);
lean::dec(x_2);
if (x_66 == 0)
{
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_68; obj* x_71; obj* x_72; 
x_68 = lean::cnstr_get(x_1, 0);
lean::inc(x_68);
lean::dec(x_1);
x_71 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_71, 0, x_68);
x_72 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_72, 0, x_71);
return x_72;
}
case 3:
{
obj* x_73; 
x_73 = l_lean_parser_detail__ident__part_has__view_x_27___lambda__1___closed__1;
return x_73;
}
default:
{
obj* x_75; 
lean::dec(x_1);
x_75 = l_lean_parser_detail__ident__part_has__view_x_27___lambda__1___closed__1;
return x_75;
}
}
}
else
{
obj* x_76; obj* x_77; obj* x_80; obj* x_81; 
x_76 = l_lean_parser_detail__ident__part__escaped_has__view;
x_77 = lean::cnstr_get(x_76, 0);
lean::inc(x_77);
lean::dec(x_76);
x_80 = lean::apply_1(x_77, x_1);
x_81 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_81, 0, x_80);
return x_81;
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
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_0 = lean::box(0);
x_1 = lean::box(0);
x_2 = lean::mk_nat_obj(1u);
x_3 = lean_name_mk_numeral(x_1, x_2);
x_4 = lean::box(0);
x_5 = lean::box(3);
x_6 = l_option_get__or__else___main___rarg(x_4, x_5);
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_0);
x_8 = l_lean_parser_syntax_mk__node(x_3, x_7);
x_9 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_0);
x_10 = l_lean_parser_detail__ident__part;
x_11 = l_lean_parser_syntax_mk__node(x_10, x_9);
return x_11;
}
}
obj* _init_l_lean_parser_detail__ident__part_has__view_x_27___lambda__2___closed__3() {
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
obj* x_2; obj* x_5; obj* x_6; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
x_5 = l_lean_parser_detail__ident__part__escaped_has__view;
x_6 = lean::cnstr_get(x_5, 1);
lean::inc(x_6);
lean::dec(x_5);
x_9 = lean::apply_1(x_6, x_2);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_1);
x_11 = l_lean_parser_detail__ident__part_has__view_x_27___lambda__2___closed__1;
x_12 = l_lean_parser_syntax_mk__node(x_11, x_10);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_1);
x_14 = l_lean_parser_detail__ident__part;
x_15 = l_lean_parser_syntax_mk__node(x_14, x_13);
return x_15;
}
else
{
obj* x_16; 
x_16 = lean::cnstr_get(x_0, 0);
lean::inc(x_16);
lean::dec(x_0);
if (lean::obj_tag(x_16) == 0)
{
obj* x_19; 
x_19 = l_lean_parser_detail__ident__part_has__view_x_27___lambda__2___closed__2;
return x_19;
}
else
{
obj* x_20; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; 
x_20 = lean::cnstr_get(x_16, 0);
if (lean::is_exclusive(x_16)) {
 x_22 = x_16;
} else {
 lean::inc(x_20);
 lean::dec(x_16);
 x_22 = lean::box(0);
}
x_23 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_23, 0, x_20);
if (lean::is_scalar(x_22)) {
 x_24 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_24 = x_22;
}
lean::cnstr_set(x_24, 0, x_23);
x_25 = lean::box(3);
x_26 = l_option_get__or__else___main___rarg(x_24, x_25);
lean::dec(x_24);
x_28 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_28, 0, x_26);
lean::cnstr_set(x_28, 1, x_1);
x_29 = l_lean_parser_detail__ident__part_has__view_x_27___lambda__2___closed__3;
x_30 = l_lean_parser_syntax_mk__node(x_29, x_28);
x_31 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_31, 0, x_30);
lean::cnstr_set(x_31, 1, x_1);
x_32 = l_lean_parser_detail__ident__part;
x_33 = l_lean_parser_syntax_mk__node(x_32, x_31);
return x_33;
}
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
return x_0;
}
}
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = lean::string_iterator_has_next(x_2);
if (x_5 == 0)
{
obj* x_7; 
lean::dec(x_0);
x_7 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_7;
}
else
{
uint32 x_8; uint8 x_9; 
x_8 = lean::string_iterator_curr(x_2);
x_9 = l_lean_is__id__end__escape(x_8);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_13; obj* x_14; 
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_sub(x_0, x_10);
lean::dec(x_0);
x_13 = lean::string_push(x_1, x_8);
x_14 = lean::string_iterator_next(x_2);
x_0 = x_11;
x_1 = x_13;
x_2 = x_14;
goto _start;
}
else
{
obj* x_17; 
lean::dec(x_0);
x_17 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_17;
}
}
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
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__2(uint32 x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_4 = l_string_join___closed__1;
x_5 = lean::string_push(x_4, x_0);
x_6 = lean::string_iterator_remaining(x_2);
x_7 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__3(x_6, x_5, x_2);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_3);
return x_8;
}
}
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__5(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = lean::string_iterator_has_next(x_2);
if (x_5 == 0)
{
obj* x_7; 
lean::dec(x_0);
x_7 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_7;
}
else
{
uint32 x_8; uint8 x_9; 
x_8 = lean::string_iterator_curr(x_2);
x_9 = l_lean_is__id__end__escape(x_8);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_13; obj* x_14; 
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_sub(x_0, x_10);
lean::dec(x_0);
x_13 = lean::string_push(x_1, x_8);
x_14 = lean::string_iterator_next(x_2);
x_0 = x_11;
x_1 = x_13;
x_2 = x_14;
goto _start;
}
else
{
obj* x_17; 
lean::dec(x_0);
x_17 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_17;
}
}
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
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__4(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint32 x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_4 = lean::string_iterator_curr(x_0);
x_5 = l_string_join___closed__1;
x_6 = lean::string_push(x_5, x_4);
x_7 = lean::string_iterator_remaining(x_2);
x_8 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__5(x_7, x_6, x_2);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_3);
return x_9;
}
}
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__7(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = lean::string_iterator_has_next(x_2);
if (x_5 == 0)
{
obj* x_7; 
lean::dec(x_0);
x_7 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_7;
}
else
{
uint32 x_8; uint8 x_9; 
x_8 = lean::string_iterator_curr(x_2);
x_9 = l_lean_is__id__end__escape(x_8);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_13; obj* x_14; 
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_sub(x_0, x_10);
lean::dec(x_0);
x_13 = lean::string_push(x_1, x_8);
x_14 = lean::string_iterator_next(x_2);
x_0 = x_11;
x_1 = x_13;
x_2 = x_14;
goto _start;
}
else
{
obj* x_17; 
lean::dec(x_0);
x_17 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_17;
}
}
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
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__6(uint32 x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_4 = l_string_join___closed__1;
x_5 = lean::string_push(x_4, x_0);
x_6 = lean::string_iterator_remaining(x_2);
x_7 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__7(x_6, x_5, x_2);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_3);
return x_8;
}
}
obj* l_lean_parser_monad__parsec_take__while1___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = lean::string_iterator_has_next(x_1);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_14; obj* x_15; 
x_4 = lean::box(0);
x_5 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_6 = l_mjoin___rarg___closed__1;
x_7 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_5, x_6, x_4, x_4, x_0, x_1, x_2);
lean::dec(x_1);
x_9 = lean::cnstr_get(x_7, 0);
x_11 = lean::cnstr_get(x_7, 1);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_set(x_7, 0, lean::box(0));
 lean::cnstr_set(x_7, 1, lean::box(0));
 x_13 = x_7;
} else {
 lean::inc(x_9);
 lean::inc(x_11);
 lean::dec(x_7);
 x_13 = lean::box(0);
}
x_14 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_15 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_14, x_9);
if (lean::obj_tag(x_15) == 0)
{
obj* x_17; obj* x_19; obj* x_21; uint32 x_24; obj* x_25; obj* x_26; obj* x_28; obj* x_30; obj* x_31; obj* x_32; 
lean::dec(x_13);
x_17 = lean::cnstr_get(x_15, 0);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_15, 1);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_15, 2);
lean::inc(x_21);
lean::dec(x_15);
x_24 = lean::unbox_uint32(x_17);
x_25 = l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__2(x_24, x_0, x_19, x_11);
x_26 = lean::cnstr_get(x_25, 0);
x_28 = lean::cnstr_get(x_25, 1);
if (lean::is_exclusive(x_25)) {
 x_30 = x_25;
} else {
 lean::inc(x_26);
 lean::inc(x_28);
 lean::dec(x_25);
 x_30 = lean::box(0);
}
x_31 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_21, x_26);
if (lean::is_scalar(x_30)) {
 x_32 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_32 = x_30;
}
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_28);
return x_32;
}
else
{
obj* x_33; uint8 x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; 
x_33 = lean::cnstr_get(x_15, 0);
x_35 = lean::cnstr_get_scalar<uint8>(x_15, sizeof(void*)*1);
if (lean::is_exclusive(x_15)) {
 x_36 = x_15;
} else {
 lean::inc(x_33);
 lean::dec(x_15);
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
if (lean::is_scalar(x_13)) {
 x_39 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_39 = x_13;
}
lean::cnstr_set(x_39, 0, x_38);
lean::cnstr_set(x_39, 1, x_11);
return x_39;
}
}
else
{
uint32 x_40; uint8 x_41; 
x_40 = lean::string_iterator_curr(x_1);
x_41 = l_lean_is__id__end__escape(x_40);
if (x_41 == 0)
{
obj* x_43; obj* x_44; obj* x_46; obj* x_48; obj* x_50; obj* x_51; obj* x_52; obj* x_53; 
lean::inc(x_1);
x_43 = lean::string_iterator_next(x_1);
x_44 = l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__4(x_1, x_0, x_43, x_2);
lean::dec(x_1);
x_46 = lean::cnstr_get(x_44, 0);
x_48 = lean::cnstr_get(x_44, 1);
if (lean::is_exclusive(x_44)) {
 x_50 = x_44;
} else {
 lean::inc(x_46);
 lean::inc(x_48);
 lean::dec(x_44);
 x_50 = lean::box(0);
}
x_51 = lean::box(0);
x_52 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_51, x_46);
if (lean::is_scalar(x_50)) {
 x_53 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_53 = x_50;
}
lean::cnstr_set(x_53, 0, x_52);
lean::cnstr_set(x_53, 1, x_48);
return x_53;
}
else
{
obj* x_54; obj* x_55; obj* x_56; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_63; obj* x_65; obj* x_67; obj* x_68; obj* x_69; 
x_54 = l_char_quote__core(x_40);
x_55 = l_char_has__repr___closed__1;
x_56 = lean::string_append(x_55, x_54);
lean::dec(x_54);
x_58 = lean::string_append(x_56, x_55);
x_59 = lean::box(0);
x_60 = l_mjoin___rarg___closed__1;
x_61 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_58, x_60, x_59, x_59, x_0, x_1, x_2);
lean::dec(x_1);
x_63 = lean::cnstr_get(x_61, 0);
x_65 = lean::cnstr_get(x_61, 1);
if (lean::is_exclusive(x_61)) {
 lean::cnstr_set(x_61, 0, lean::box(0));
 lean::cnstr_set(x_61, 1, lean::box(0));
 x_67 = x_61;
} else {
 lean::inc(x_63);
 lean::inc(x_65);
 lean::dec(x_61);
 x_67 = lean::box(0);
}
x_68 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_69 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_68, x_63);
if (lean::obj_tag(x_69) == 0)
{
obj* x_71; obj* x_73; obj* x_75; uint32 x_78; obj* x_79; obj* x_80; obj* x_82; obj* x_84; obj* x_85; obj* x_86; 
lean::dec(x_67);
x_71 = lean::cnstr_get(x_69, 0);
lean::inc(x_71);
x_73 = lean::cnstr_get(x_69, 1);
lean::inc(x_73);
x_75 = lean::cnstr_get(x_69, 2);
lean::inc(x_75);
lean::dec(x_69);
x_78 = lean::unbox_uint32(x_71);
x_79 = l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__6(x_78, x_0, x_73, x_65);
x_80 = lean::cnstr_get(x_79, 0);
x_82 = lean::cnstr_get(x_79, 1);
if (lean::is_exclusive(x_79)) {
 x_84 = x_79;
} else {
 lean::inc(x_80);
 lean::inc(x_82);
 lean::dec(x_79);
 x_84 = lean::box(0);
}
x_85 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_75, x_80);
if (lean::is_scalar(x_84)) {
 x_86 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_86 = x_84;
}
lean::cnstr_set(x_86, 0, x_85);
lean::cnstr_set(x_86, 1, x_82);
return x_86;
}
else
{
obj* x_87; uint8 x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; 
x_87 = lean::cnstr_get(x_69, 0);
x_89 = lean::cnstr_get_scalar<uint8>(x_69, sizeof(void*)*1);
if (lean::is_exclusive(x_69)) {
 x_90 = x_69;
} else {
 lean::inc(x_87);
 lean::dec(x_69);
 x_90 = lean::box(0);
}
if (lean::is_scalar(x_90)) {
 x_91 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_91 = x_90;
}
lean::cnstr_set(x_91, 0, x_87);
lean::cnstr_set_scalar(x_91, sizeof(void*)*1, x_89);
x_92 = x_91;
if (lean::is_scalar(x_67)) {
 x_93 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_93 = x_67;
}
lean::cnstr_set(x_93, 0, x_92);
lean::cnstr_set(x_93, 1, x_65);
return x_93;
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
if (x_4 == 0)
{
uint8 x_5; 
x_5 = lean::string_iterator_has_next(x_2);
if (x_5 == 0)
{
obj* x_7; 
lean::dec(x_0);
x_7 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_7;
}
else
{
uint32 x_8; uint8 x_9; 
x_8 = lean::string_iterator_curr(x_2);
x_9 = l_lean_is__id__end__escape(x_8);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_13; obj* x_14; 
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_sub(x_0, x_10);
lean::dec(x_0);
x_13 = lean::string_push(x_1, x_8);
x_14 = lean::string_iterator_next(x_2);
x_0 = x_11;
x_1 = x_13;
x_2 = x_14;
goto _start;
}
else
{
obj* x_17; 
lean::dec(x_0);
x_17 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_17;
}
}
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
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__9(uint32 x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_4 = l_string_join___closed__1;
x_5 = lean::string_push(x_4, x_0);
x_6 = lean::string_iterator_remaining(x_2);
x_7 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__10(x_6, x_5, x_2);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_3);
return x_8;
}
}
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__12(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = lean::string_iterator_has_next(x_2);
if (x_5 == 0)
{
obj* x_7; 
lean::dec(x_0);
x_7 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_7;
}
else
{
uint32 x_8; uint8 x_9; 
x_8 = lean::string_iterator_curr(x_2);
x_9 = l_lean_is__id__end__escape(x_8);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_13; obj* x_14; 
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_sub(x_0, x_10);
lean::dec(x_0);
x_13 = lean::string_push(x_1, x_8);
x_14 = lean::string_iterator_next(x_2);
x_0 = x_11;
x_1 = x_13;
x_2 = x_14;
goto _start;
}
else
{
obj* x_17; 
lean::dec(x_0);
x_17 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_17;
}
}
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
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__11(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint32 x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_4 = lean::string_iterator_curr(x_0);
x_5 = l_string_join___closed__1;
x_6 = lean::string_push(x_5, x_4);
x_7 = lean::string_iterator_remaining(x_2);
x_8 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__12(x_7, x_6, x_2);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_3);
return x_9;
}
}
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__14(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = lean::string_iterator_has_next(x_2);
if (x_5 == 0)
{
obj* x_7; 
lean::dec(x_0);
x_7 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_7;
}
else
{
uint32 x_8; uint8 x_9; 
x_8 = lean::string_iterator_curr(x_2);
x_9 = l_lean_is__id__end__escape(x_8);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_13; obj* x_14; 
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_sub(x_0, x_10);
lean::dec(x_0);
x_13 = lean::string_push(x_1, x_8);
x_14 = lean::string_iterator_next(x_2);
x_0 = x_11;
x_1 = x_13;
x_2 = x_14;
goto _start;
}
else
{
obj* x_17; 
lean::dec(x_0);
x_17 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_17;
}
}
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
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__13(uint32 x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_4 = l_string_join___closed__1;
x_5 = lean::string_push(x_4, x_0);
x_6 = lean::string_iterator_remaining(x_2);
x_7 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__14(x_6, x_5, x_2);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_3);
return x_8;
}
}
obj* l_lean_parser_monad__parsec_take__while1___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__8(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = lean::string_iterator_has_next(x_1);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_14; obj* x_15; 
x_4 = lean::box(0);
x_5 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_6 = l_mjoin___rarg___closed__1;
x_7 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_5, x_6, x_4, x_4, x_0, x_1, x_2);
lean::dec(x_1);
x_9 = lean::cnstr_get(x_7, 0);
x_11 = lean::cnstr_get(x_7, 1);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_set(x_7, 0, lean::box(0));
 lean::cnstr_set(x_7, 1, lean::box(0));
 x_13 = x_7;
} else {
 lean::inc(x_9);
 lean::inc(x_11);
 lean::dec(x_7);
 x_13 = lean::box(0);
}
x_14 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_15 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_14, x_9);
if (lean::obj_tag(x_15) == 0)
{
obj* x_17; obj* x_19; obj* x_21; uint32 x_24; obj* x_25; obj* x_26; obj* x_28; obj* x_30; obj* x_31; obj* x_32; 
lean::dec(x_13);
x_17 = lean::cnstr_get(x_15, 0);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_15, 1);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_15, 2);
lean::inc(x_21);
lean::dec(x_15);
x_24 = lean::unbox_uint32(x_17);
x_25 = l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__9(x_24, x_0, x_19, x_11);
x_26 = lean::cnstr_get(x_25, 0);
x_28 = lean::cnstr_get(x_25, 1);
if (lean::is_exclusive(x_25)) {
 x_30 = x_25;
} else {
 lean::inc(x_26);
 lean::inc(x_28);
 lean::dec(x_25);
 x_30 = lean::box(0);
}
x_31 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_21, x_26);
if (lean::is_scalar(x_30)) {
 x_32 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_32 = x_30;
}
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_28);
return x_32;
}
else
{
obj* x_33; uint8 x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; 
x_33 = lean::cnstr_get(x_15, 0);
x_35 = lean::cnstr_get_scalar<uint8>(x_15, sizeof(void*)*1);
if (lean::is_exclusive(x_15)) {
 x_36 = x_15;
} else {
 lean::inc(x_33);
 lean::dec(x_15);
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
if (lean::is_scalar(x_13)) {
 x_39 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_39 = x_13;
}
lean::cnstr_set(x_39, 0, x_38);
lean::cnstr_set(x_39, 1, x_11);
return x_39;
}
}
else
{
uint32 x_40; uint8 x_41; 
x_40 = lean::string_iterator_curr(x_1);
x_41 = l_lean_is__id__end__escape(x_40);
if (x_41 == 0)
{
obj* x_43; obj* x_44; obj* x_46; obj* x_48; obj* x_50; obj* x_51; obj* x_52; obj* x_53; 
lean::inc(x_1);
x_43 = lean::string_iterator_next(x_1);
x_44 = l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__11(x_1, x_0, x_43, x_2);
lean::dec(x_1);
x_46 = lean::cnstr_get(x_44, 0);
x_48 = lean::cnstr_get(x_44, 1);
if (lean::is_exclusive(x_44)) {
 x_50 = x_44;
} else {
 lean::inc(x_46);
 lean::inc(x_48);
 lean::dec(x_44);
 x_50 = lean::box(0);
}
x_51 = lean::box(0);
x_52 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_51, x_46);
if (lean::is_scalar(x_50)) {
 x_53 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_53 = x_50;
}
lean::cnstr_set(x_53, 0, x_52);
lean::cnstr_set(x_53, 1, x_48);
return x_53;
}
else
{
obj* x_54; obj* x_55; obj* x_56; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_63; obj* x_65; obj* x_67; obj* x_68; obj* x_69; 
x_54 = l_char_quote__core(x_40);
x_55 = l_char_has__repr___closed__1;
x_56 = lean::string_append(x_55, x_54);
lean::dec(x_54);
x_58 = lean::string_append(x_56, x_55);
x_59 = lean::box(0);
x_60 = l_mjoin___rarg___closed__1;
x_61 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_58, x_60, x_59, x_59, x_0, x_1, x_2);
lean::dec(x_1);
x_63 = lean::cnstr_get(x_61, 0);
x_65 = lean::cnstr_get(x_61, 1);
if (lean::is_exclusive(x_61)) {
 lean::cnstr_set(x_61, 0, lean::box(0));
 lean::cnstr_set(x_61, 1, lean::box(0));
 x_67 = x_61;
} else {
 lean::inc(x_63);
 lean::inc(x_65);
 lean::dec(x_61);
 x_67 = lean::box(0);
}
x_68 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_69 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_68, x_63);
if (lean::obj_tag(x_69) == 0)
{
obj* x_71; obj* x_73; obj* x_75; uint32 x_78; obj* x_79; obj* x_80; obj* x_82; obj* x_84; obj* x_85; obj* x_86; 
lean::dec(x_67);
x_71 = lean::cnstr_get(x_69, 0);
lean::inc(x_71);
x_73 = lean::cnstr_get(x_69, 1);
lean::inc(x_73);
x_75 = lean::cnstr_get(x_69, 2);
lean::inc(x_75);
lean::dec(x_69);
x_78 = lean::unbox_uint32(x_71);
x_79 = l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__13(x_78, x_0, x_73, x_65);
x_80 = lean::cnstr_get(x_79, 0);
x_82 = lean::cnstr_get(x_79, 1);
if (lean::is_exclusive(x_79)) {
 x_84 = x_79;
} else {
 lean::inc(x_80);
 lean::inc(x_82);
 lean::dec(x_79);
 x_84 = lean::box(0);
}
x_85 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_75, x_80);
if (lean::is_scalar(x_84)) {
 x_86 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_86 = x_84;
}
lean::cnstr_set(x_86, 0, x_85);
lean::cnstr_set(x_86, 1, x_82);
return x_86;
}
else
{
obj* x_87; uint8 x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; 
x_87 = lean::cnstr_get(x_69, 0);
x_89 = lean::cnstr_get_scalar<uint8>(x_69, sizeof(void*)*1);
if (lean::is_exclusive(x_69)) {
 x_90 = x_69;
} else {
 lean::inc(x_87);
 lean::dec(x_69);
 x_90 = lean::box(0);
}
if (lean::is_scalar(x_90)) {
 x_91 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_91 = x_90;
}
lean::cnstr_set(x_91, 0, x_87);
lean::cnstr_set_scalar(x_91, sizeof(void*)*1, x_89);
x_92 = x_91;
if (lean::is_scalar(x_67)) {
 x_93 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_93 = x_67;
}
lean::cnstr_set(x_93, 0, x_92);
lean::cnstr_set(x_93, 1, x_65);
return x_93;
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
obj* x_8; obj* x_9; obj* x_10; 
lean::dec(x_3);
lean::dec(x_0);
x_8 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_9 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_9, 0, x_1);
lean::cnstr_set(x_9, 1, x_4);
lean::cnstr_set(x_9, 2, x_8);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_5);
return x_10;
}
else
{
obj* x_11; obj* x_13; obj* x_15; obj* x_16; obj* x_17; obj* x_20; obj* x_21; 
x_11 = lean::cnstr_get(x_2, 0);
x_13 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_set(x_2, 0, lean::box(0));
 lean::cnstr_set(x_2, 1, lean::box(0));
 x_15 = x_2;
} else {
 lean::inc(x_11);
 lean::inc(x_13);
 lean::dec(x_2);
 x_15 = lean::box(0);
}
lean::inc(x_3);
x_20 = lean::apply_3(x_11, x_3, x_4, x_5);
x_21 = lean::cnstr_get(x_20, 0);
lean::inc(x_21);
if (lean::obj_tag(x_21) == 0)
{
obj* x_23; 
x_23 = lean::cnstr_get(x_20, 1);
lean::inc(x_23);
lean::dec(x_20);
x_16 = x_21;
x_17 = x_23;
goto lbl_18;
}
else
{
uint8 x_26; 
x_26 = lean::cnstr_get_scalar<uint8>(x_21, sizeof(void*)*1);
if (lean::obj_tag(x_1) == 0)
{
if (x_26 == 0)
{
obj* x_27; obj* x_30; obj* x_32; uint8 x_33; obj* x_34; obj* x_35; 
x_27 = lean::cnstr_get(x_20, 1);
lean::inc(x_27);
lean::dec(x_20);
x_30 = lean::cnstr_get(x_21, 0);
if (lean::is_exclusive(x_21)) {
 x_32 = x_21;
} else {
 lean::inc(x_30);
 lean::dec(x_21);
 x_32 = lean::box(0);
}
x_33 = 0;
if (lean::is_scalar(x_32)) {
 x_34 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_34 = x_32;
}
lean::cnstr_set(x_34, 0, x_30);
lean::cnstr_set_scalar(x_34, sizeof(void*)*1, x_33);
x_35 = x_34;
x_16 = x_35;
x_17 = x_27;
goto lbl_18;
}
else
{
obj* x_36; obj* x_39; obj* x_41; obj* x_42; obj* x_43; 
x_36 = lean::cnstr_get(x_20, 1);
lean::inc(x_36);
lean::dec(x_20);
x_39 = lean::cnstr_get(x_21, 0);
if (lean::is_exclusive(x_21)) {
 x_41 = x_21;
} else {
 lean::inc(x_39);
 lean::dec(x_21);
 x_41 = lean::box(0);
}
if (lean::is_scalar(x_41)) {
 x_42 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_42 = x_41;
}
lean::cnstr_set(x_42, 0, x_39);
lean::cnstr_set_scalar(x_42, sizeof(void*)*1, x_26);
x_43 = x_42;
x_16 = x_43;
x_17 = x_36;
goto lbl_18;
}
}
else
{
obj* x_44; obj* x_47; obj* x_49; obj* x_50; obj* x_52; obj* x_55; obj* x_56; obj* x_58; obj* x_60; obj* x_63; obj* x_65; obj* x_66; obj* x_67; 
x_44 = lean::cnstr_get(x_20, 1);
lean::inc(x_44);
lean::dec(x_20);
x_47 = lean::cnstr_get(x_21, 0);
if (lean::is_exclusive(x_21)) {
 lean::cnstr_set(x_21, 0, lean::box(0));
 x_49 = x_21;
} else {
 lean::inc(x_47);
 lean::dec(x_21);
 x_49 = lean::box(0);
}
x_50 = lean::cnstr_get(x_47, 3);
lean::inc(x_50);
x_52 = l_option_get___main___at_lean_parser_run___spec__2(x_50);
lean::dec(x_50);
lean::inc(x_1);
x_55 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_55, 0, x_52);
lean::cnstr_set(x_55, 1, x_1);
x_56 = lean::cnstr_get(x_47, 0);
lean::inc(x_56);
x_58 = lean::cnstr_get(x_47, 1);
lean::inc(x_58);
x_60 = lean::cnstr_get(x_47, 2);
lean::inc(x_60);
lean::dec(x_47);
x_63 = l_list_reverse___rarg(x_55);
lean::inc(x_0);
x_65 = l_lean_parser_syntax_mk__node(x_0, x_63);
x_66 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_66, 0, x_65);
x_67 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_67, 0, x_56);
lean::cnstr_set(x_67, 1, x_58);
lean::cnstr_set(x_67, 2, x_60);
lean::cnstr_set(x_67, 3, x_66);
if (x_26 == 0)
{
uint8 x_68; obj* x_69; obj* x_70; 
x_68 = 0;
if (lean::is_scalar(x_49)) {
 x_69 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_69 = x_49;
}
lean::cnstr_set(x_69, 0, x_67);
lean::cnstr_set_scalar(x_69, sizeof(void*)*1, x_68);
x_70 = x_69;
x_16 = x_70;
x_17 = x_44;
goto lbl_18;
}
else
{
obj* x_71; obj* x_72; 
if (lean::is_scalar(x_49)) {
 x_71 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_71 = x_49;
}
lean::cnstr_set(x_71, 0, x_67);
lean::cnstr_set_scalar(x_71, sizeof(void*)*1, x_26);
x_72 = x_71;
x_16 = x_72;
x_17 = x_44;
goto lbl_18;
}
}
}
lbl_18:
{
if (lean::obj_tag(x_16) == 0)
{
obj* x_73; obj* x_75; obj* x_77; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; 
x_73 = lean::cnstr_get(x_16, 0);
x_75 = lean::cnstr_get(x_16, 1);
x_77 = lean::cnstr_get(x_16, 2);
if (lean::is_exclusive(x_16)) {
 x_79 = x_16;
} else {
 lean::inc(x_73);
 lean::inc(x_75);
 lean::inc(x_77);
 lean::dec(x_16);
 x_79 = lean::box(0);
}
if (lean::is_scalar(x_15)) {
 x_80 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_80 = x_15;
}
lean::cnstr_set(x_80, 0, x_73);
lean::cnstr_set(x_80, 1, x_1);
x_81 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_79)) {
 x_82 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_82 = x_79;
}
lean::cnstr_set(x_82, 0, x_80);
lean::cnstr_set(x_82, 1, x_75);
lean::cnstr_set(x_82, 2, x_81);
x_83 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_77, x_82);
if (lean::obj_tag(x_83) == 0)
{
obj* x_84; obj* x_86; obj* x_88; obj* x_91; obj* x_92; obj* x_94; obj* x_96; obj* x_97; obj* x_98; 
x_84 = lean::cnstr_get(x_83, 0);
lean::inc(x_84);
x_86 = lean::cnstr_get(x_83, 1);
lean::inc(x_86);
x_88 = lean::cnstr_get(x_83, 2);
lean::inc(x_88);
lean::dec(x_83);
x_91 = l_list_mfoldl___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__16(x_0, x_84, x_13, x_3, x_86, x_17);
x_92 = lean::cnstr_get(x_91, 0);
x_94 = lean::cnstr_get(x_91, 1);
if (lean::is_exclusive(x_91)) {
 x_96 = x_91;
} else {
 lean::inc(x_92);
 lean::inc(x_94);
 lean::dec(x_91);
 x_96 = lean::box(0);
}
x_97 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_88, x_92);
if (lean::is_scalar(x_96)) {
 x_98 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_98 = x_96;
}
lean::cnstr_set(x_98, 0, x_97);
lean::cnstr_set(x_98, 1, x_94);
return x_98;
}
else
{
obj* x_102; uint8 x_104; obj* x_105; obj* x_106; obj* x_107; obj* x_108; 
lean::dec(x_13);
lean::dec(x_3);
lean::dec(x_0);
x_102 = lean::cnstr_get(x_83, 0);
x_104 = lean::cnstr_get_scalar<uint8>(x_83, sizeof(void*)*1);
if (lean::is_exclusive(x_83)) {
 x_105 = x_83;
} else {
 lean::inc(x_102);
 lean::dec(x_83);
 x_105 = lean::box(0);
}
if (lean::is_scalar(x_105)) {
 x_106 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_106 = x_105;
}
lean::cnstr_set(x_106, 0, x_102);
lean::cnstr_set_scalar(x_106, sizeof(void*)*1, x_104);
x_107 = x_106;
x_108 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_108, 0, x_107);
lean::cnstr_set(x_108, 1, x_17);
return x_108;
}
}
else
{
obj* x_114; uint8 x_116; obj* x_117; obj* x_118; obj* x_119; obj* x_120; 
lean::dec(x_13);
lean::dec(x_15);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
x_114 = lean::cnstr_get(x_16, 0);
x_116 = lean::cnstr_get_scalar<uint8>(x_16, sizeof(void*)*1);
if (lean::is_exclusive(x_16)) {
 x_117 = x_16;
} else {
 lean::inc(x_114);
 lean::dec(x_16);
 x_117 = lean::box(0);
}
if (lean::is_scalar(x_117)) {
 x_118 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_118 = x_117;
}
lean::cnstr_set(x_118, 0, x_114);
lean::cnstr_set_scalar(x_118, sizeof(void*)*1, x_116);
x_119 = x_118;
x_120 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_120, 0, x_119);
lean::cnstr_set(x_120, 1, x_17);
return x_120;
}
}
}
}
}
obj* l_lean_parser_combinators_node___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__15(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_7; obj* x_8; 
x_5 = lean::box(0);
lean::inc(x_0);
x_7 = l_list_mfoldl___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__16(x_0, x_5, x_1, x_2, x_3, x_4);
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
if (lean::obj_tag(x_8) == 0)
{
obj* x_10; obj* x_12; obj* x_13; obj* x_15; obj* x_17; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_10 = lean::cnstr_get(x_7, 1);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 x_12 = x_7;
} else {
 lean::inc(x_10);
 lean::dec(x_7);
 x_12 = lean::box(0);
}
x_13 = lean::cnstr_get(x_8, 0);
x_15 = lean::cnstr_get(x_8, 1);
x_17 = lean::cnstr_get(x_8, 2);
if (lean::is_exclusive(x_8)) {
 x_19 = x_8;
} else {
 lean::inc(x_13);
 lean::inc(x_15);
 lean::inc(x_17);
 lean::dec(x_8);
 x_19 = lean::box(0);
}
x_20 = l_list_reverse___rarg(x_13);
x_21 = l_lean_parser_syntax_mk__node(x_0, x_20);
x_22 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_19)) {
 x_23 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_23 = x_19;
}
lean::cnstr_set(x_23, 0, x_21);
lean::cnstr_set(x_23, 1, x_15);
lean::cnstr_set(x_23, 2, x_22);
x_24 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_17, x_23);
if (lean::is_scalar(x_12)) {
 x_25 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_25 = x_12;
}
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_10);
return x_25;
}
else
{
obj* x_27; obj* x_29; obj* x_30; uint8 x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; 
lean::dec(x_0);
x_27 = lean::cnstr_get(x_7, 1);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 x_29 = x_7;
} else {
 lean::inc(x_27);
 lean::dec(x_7);
 x_29 = lean::box(0);
}
x_30 = lean::cnstr_get(x_8, 0);
x_32 = lean::cnstr_get_scalar<uint8>(x_8, sizeof(void*)*1);
if (lean::is_exclusive(x_8)) {
 x_33 = x_8;
} else {
 lean::inc(x_30);
 lean::dec(x_8);
 x_33 = lean::box(0);
}
if (lean::is_scalar(x_33)) {
 x_34 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_34 = x_33;
}
lean::cnstr_set(x_34, 0, x_30);
lean::cnstr_set_scalar(x_34, sizeof(void*)*1, x_32);
x_35 = x_34;
if (lean::is_scalar(x_29)) {
 x_36 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_36 = x_29;
}
lean::cnstr_set(x_36, 0, x_35);
lean::cnstr_set(x_36, 1, x_27);
return x_36;
}
}
}
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__18(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = lean::string_iterator_has_next(x_2);
if (x_5 == 0)
{
obj* x_7; 
lean::dec(x_0);
x_7 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_7;
}
else
{
uint32 x_8; uint8 x_9; 
x_8 = lean::string_iterator_curr(x_2);
x_9 = l_lean_is__id__rest(x_8);
if (x_9 == 0)
{
obj* x_11; 
lean::dec(x_0);
x_11 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_11;
}
else
{
obj* x_12; obj* x_13; obj* x_15; obj* x_16; 
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_sub(x_0, x_12);
lean::dec(x_0);
x_15 = lean::string_push(x_1, x_8);
x_16 = lean::string_iterator_next(x_2);
x_0 = x_13;
x_1 = x_15;
x_2 = x_16;
goto _start;
}
}
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
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__17___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = lean::string_iterator_remaining(x_0);
x_3 = l_string_join___closed__1;
x_4 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__18(x_2, x_3, x_0);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_1);
return x_5;
}
}
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__17(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__17___rarg), 2, 0);
return x_1;
}
}
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__20(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = lean::string_iterator_has_next(x_2);
if (x_5 == 0)
{
obj* x_7; 
lean::dec(x_0);
x_7 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_7;
}
else
{
uint32 x_8; uint8 x_9; 
x_8 = lean::string_iterator_curr(x_2);
x_9 = l_lean_is__id__rest(x_8);
if (x_9 == 0)
{
obj* x_11; 
lean::dec(x_0);
x_11 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_11;
}
else
{
obj* x_12; obj* x_13; obj* x_15; obj* x_16; 
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_sub(x_0, x_12);
lean::dec(x_0);
x_15 = lean::string_push(x_1, x_8);
x_16 = lean::string_iterator_next(x_2);
x_0 = x_13;
x_1 = x_15;
x_2 = x_16;
goto _start;
}
}
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
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__19___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = lean::string_iterator_remaining(x_0);
x_3 = l_string_join___closed__1;
x_4 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__20(x_2, x_3, x_0);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_1);
return x_5;
}
}
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__19(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__19___rarg), 2, 0);
return x_1;
}
}
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__22(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = lean::string_iterator_has_next(x_2);
if (x_5 == 0)
{
obj* x_7; 
lean::dec(x_0);
x_7 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_7;
}
else
{
uint32 x_8; uint8 x_9; 
x_8 = lean::string_iterator_curr(x_2);
x_9 = l_lean_is__id__rest(x_8);
if (x_9 == 0)
{
obj* x_11; 
lean::dec(x_0);
x_11 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_11;
}
else
{
obj* x_12; obj* x_13; obj* x_15; obj* x_16; 
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_sub(x_0, x_12);
lean::dec(x_0);
x_15 = lean::string_push(x_1, x_8);
x_16 = lean::string_iterator_next(x_2);
x_0 = x_13;
x_1 = x_15;
x_2 = x_16;
goto _start;
}
}
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
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__21___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = lean::string_iterator_remaining(x_0);
x_3 = l_string_join___closed__1;
x_4 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__22(x_2, x_3, x_0);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_1);
return x_5;
}
}
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__21(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__21___rarg), 2, 0);
return x_1;
}
}
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__24(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = lean::string_iterator_has_next(x_2);
if (x_5 == 0)
{
obj* x_7; 
lean::dec(x_0);
x_7 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_7;
}
else
{
uint32 x_8; uint8 x_9; 
x_8 = lean::string_iterator_curr(x_2);
x_9 = l_lean_is__id__rest(x_8);
if (x_9 == 0)
{
obj* x_11; 
lean::dec(x_0);
x_11 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_11;
}
else
{
obj* x_12; obj* x_13; obj* x_15; obj* x_16; 
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_sub(x_0, x_12);
lean::dec(x_0);
x_15 = lean::string_push(x_1, x_8);
x_16 = lean::string_iterator_next(x_2);
x_0 = x_13;
x_1 = x_15;
x_2 = x_16;
goto _start;
}
}
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
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__23___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = lean::string_iterator_remaining(x_0);
x_3 = l_string_join___closed__1;
x_4 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__24(x_2, x_3, x_0);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_1);
return x_5;
}
}
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__23(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__23___rarg), 2, 0);
return x_1;
}
}
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__26(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = lean::string_iterator_has_next(x_2);
if (x_5 == 0)
{
obj* x_7; 
lean::dec(x_0);
x_7 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_7;
}
else
{
uint32 x_8; uint8 x_9; 
x_8 = lean::string_iterator_curr(x_2);
x_9 = l_lean_is__id__rest(x_8);
if (x_9 == 0)
{
obj* x_11; 
lean::dec(x_0);
x_11 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_11;
}
else
{
obj* x_12; obj* x_13; obj* x_15; obj* x_16; 
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_sub(x_0, x_12);
lean::dec(x_0);
x_15 = lean::string_push(x_1, x_8);
x_16 = lean::string_iterator_next(x_2);
x_0 = x_13;
x_1 = x_15;
x_2 = x_16;
goto _start;
}
}
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
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__25___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = lean::string_iterator_remaining(x_0);
x_3 = l_string_join___closed__1;
x_4 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__26(x_2, x_3, x_0);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_1);
return x_5;
}
}
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__25(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__25___rarg), 2, 0);
return x_1;
}
}
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__28(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = lean::string_iterator_has_next(x_2);
if (x_5 == 0)
{
obj* x_7; 
lean::dec(x_0);
x_7 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_7;
}
else
{
uint32 x_8; uint8 x_9; 
x_8 = lean::string_iterator_curr(x_2);
x_9 = l_lean_is__id__rest(x_8);
if (x_9 == 0)
{
obj* x_11; 
lean::dec(x_0);
x_11 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_11;
}
else
{
obj* x_12; obj* x_13; obj* x_15; obj* x_16; 
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_sub(x_0, x_12);
lean::dec(x_0);
x_15 = lean::string_push(x_1, x_8);
x_16 = lean::string_iterator_next(x_2);
x_0 = x_13;
x_1 = x_15;
x_2 = x_16;
goto _start;
}
}
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
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__27___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = lean::string_iterator_remaining(x_0);
x_3 = l_string_join___closed__1;
x_4 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__28(x_2, x_3, x_0);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_1);
return x_5;
}
}
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__27(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__27___rarg), 2, 0);
return x_1;
}
}
obj* l_lean_parser_combinators_choice__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__29(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
lean::dec(x_1);
x_6 = lean::box(0);
x_7 = l_lean_parser_combinators_choice__aux___main___rarg___closed__1;
x_8 = l_mjoin___rarg___closed__1;
x_9 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_7, x_8, x_6, x_6, x_2, x_3, x_4);
lean::dec(x_3);
lean::dec(x_2);
return x_9;
}
else
{
obj* x_12; obj* x_14; obj* x_16; obj* x_19; obj* x_20; obj* x_22; obj* x_24; obj* x_25; obj* x_26; 
x_12 = lean::cnstr_get(x_0, 0);
x_14 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 x_16 = x_0;
} else {
 lean::inc(x_12);
 lean::inc(x_14);
 lean::dec(x_0);
 x_16 = lean::box(0);
}
lean::inc(x_3);
lean::inc(x_2);
x_19 = lean::apply_3(x_12, x_2, x_3, x_4);
x_20 = lean::cnstr_get(x_19, 0);
x_22 = lean::cnstr_get(x_19, 1);
if (lean::is_exclusive(x_19)) {
 lean::cnstr_set(x_19, 0, lean::box(0));
 lean::cnstr_set(x_19, 1, lean::box(0));
 x_24 = x_19;
} else {
 lean::inc(x_20);
 lean::inc(x_22);
 lean::dec(x_19);
 x_24 = lean::box(0);
}
x_25 = lean::mk_nat_obj(1u);
x_26 = lean::nat_add(x_1, x_25);
if (lean::obj_tag(x_20) == 0)
{
obj* x_27; obj* x_29; obj* x_31; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; 
x_27 = lean::cnstr_get(x_20, 0);
x_29 = lean::cnstr_get(x_20, 1);
x_31 = lean::cnstr_get(x_20, 2);
if (lean::is_exclusive(x_20)) {
 x_33 = x_20;
} else {
 lean::inc(x_27);
 lean::inc(x_29);
 lean::inc(x_31);
 lean::dec(x_20);
 x_33 = lean::box(0);
}
x_34 = lean::box(0);
x_35 = lean_name_mk_numeral(x_34, x_1);
x_36 = lean::box(0);
if (lean::is_scalar(x_16)) {
 x_37 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_37 = x_16;
}
lean::cnstr_set(x_37, 0, x_27);
lean::cnstr_set(x_37, 1, x_36);
x_38 = l_lean_parser_syntax_mk__node(x_35, x_37);
x_39 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_33)) {
 x_40 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_40 = x_33;
}
lean::cnstr_set(x_40, 0, x_38);
lean::cnstr_set(x_40, 1, x_29);
lean::cnstr_set(x_40, 2, x_39);
x_41 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_31, x_40);
if (lean::obj_tag(x_41) == 0)
{
obj* x_46; 
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_26);
lean::dec(x_14);
if (lean::is_scalar(x_24)) {
 x_46 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_46 = x_24;
}
lean::cnstr_set(x_46, 0, x_41);
lean::cnstr_set(x_46, 1, x_22);
return x_46;
}
else
{
uint8 x_47; 
x_47 = lean::cnstr_get_scalar<uint8>(x_41, sizeof(void*)*1);
if (x_47 == 0)
{
obj* x_49; obj* x_52; obj* x_53; obj* x_55; obj* x_57; obj* x_58; obj* x_59; 
lean::dec(x_24);
x_49 = lean::cnstr_get(x_41, 0);
lean::inc(x_49);
lean::dec(x_41);
x_52 = l_lean_parser_combinators_choice__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__29(x_14, x_26, x_2, x_3, x_22);
x_53 = lean::cnstr_get(x_52, 0);
x_55 = lean::cnstr_get(x_52, 1);
if (lean::is_exclusive(x_52)) {
 x_57 = x_52;
} else {
 lean::inc(x_53);
 lean::inc(x_55);
 lean::dec(x_52);
 x_57 = lean::box(0);
}
x_58 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_49, x_53);
if (lean::is_scalar(x_57)) {
 x_59 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_59 = x_57;
}
lean::cnstr_set(x_59, 0, x_58);
lean::cnstr_set(x_59, 1, x_55);
return x_59;
}
else
{
obj* x_64; 
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_26);
lean::dec(x_14);
if (lean::is_scalar(x_24)) {
 x_64 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_64 = x_24;
}
lean::cnstr_set(x_64, 0, x_41);
lean::cnstr_set(x_64, 1, x_22);
return x_64;
}
}
}
else
{
uint8 x_67; 
lean::dec(x_1);
lean::dec(x_16);
x_67 = lean::cnstr_get_scalar<uint8>(x_20, sizeof(void*)*1);
if (x_67 == 0)
{
obj* x_69; obj* x_72; obj* x_73; obj* x_75; obj* x_77; obj* x_78; obj* x_79; 
lean::dec(x_24);
x_69 = lean::cnstr_get(x_20, 0);
lean::inc(x_69);
lean::dec(x_20);
x_72 = l_lean_parser_combinators_choice__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__29(x_14, x_26, x_2, x_3, x_22);
x_73 = lean::cnstr_get(x_72, 0);
x_75 = lean::cnstr_get(x_72, 1);
if (lean::is_exclusive(x_72)) {
 x_77 = x_72;
} else {
 lean::inc(x_73);
 lean::inc(x_75);
 lean::dec(x_72);
 x_77 = lean::box(0);
}
x_78 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_69, x_73);
if (lean::is_scalar(x_77)) {
 x_79 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_79 = x_77;
}
lean::cnstr_set(x_79, 0, x_78);
lean::cnstr_set(x_79, 1, x_75);
return x_79;
}
else
{
obj* x_84; obj* x_86; obj* x_87; obj* x_88; obj* x_89; 
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_26);
lean::dec(x_14);
x_84 = lean::cnstr_get(x_20, 0);
if (lean::is_exclusive(x_20)) {
 x_86 = x_20;
} else {
 lean::inc(x_84);
 lean::dec(x_20);
 x_86 = lean::box(0);
}
if (lean::is_scalar(x_86)) {
 x_87 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_87 = x_86;
}
lean::cnstr_set(x_87, 0, x_84);
lean::cnstr_set_scalar(x_87, sizeof(void*)*1, x_67);
x_88 = x_87;
if (lean::is_scalar(x_24)) {
 x_89 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_89 = x_24;
}
lean::cnstr_set(x_89, 0, x_88);
lean::cnstr_set(x_89, 1, x_22);
return x_89;
}
}
}
}
}
obj* _init_l_lean_parser_detail__ident__part_parser_lean_parser_has__tokens() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_5; obj* x_7; obj* x_10; obj* x_12; obj* x_14; 
x_0 = lean::box(0);
x_1 = l_lean_parser_list_cons_tokens___rarg(x_0, x_0);
x_2 = l_lean_parser_list_cons_tokens___rarg(x_0, x_1);
x_3 = l_lean_parser_list_cons_tokens___rarg(x_0, x_2);
lean::dec(x_2);
x_5 = l_lean_parser_tokens___rarg(x_3);
lean::dec(x_3);
x_7 = l_lean_parser_list_cons_tokens___rarg(x_5, x_1);
lean::dec(x_1);
lean::dec(x_5);
x_10 = l_lean_parser_tokens___rarg(x_7);
lean::dec(x_7);
x_12 = l_lean_parser_list_cons_tokens___rarg(x_10, x_0);
lean::dec(x_10);
x_14 = l_lean_parser_tokens___rarg(x_12);
lean::dec(x_12);
return x_14;
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint32 x_4; obj* x_5; 
x_4 = lean::unbox_uint32(x_0);
x_5 = l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__2(x_4, x_1, x_2, x_3);
lean::dec(x_1);
return x_5;
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__4___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__4(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
return x_4;
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__6___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint32 x_4; obj* x_5; 
x_4 = lean::unbox_uint32(x_0);
x_5 = l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__6(x_4, x_1, x_2, x_3);
lean::dec(x_1);
return x_5;
}
}
obj* l_lean_parser_monad__parsec_take__while1___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_parser_monad__parsec_take__while1___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__1(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__9___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint32 x_4; obj* x_5; 
x_4 = lean::unbox_uint32(x_0);
x_5 = l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__9(x_4, x_1, x_2, x_3);
lean::dec(x_1);
return x_5;
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__11___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__11(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
return x_4;
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__13___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint32 x_4; obj* x_5; 
x_4 = lean::unbox_uint32(x_0);
x_5 = l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__13(x_4, x_1, x_2, x_3);
lean::dec(x_1);
return x_5;
}
}
obj* l_lean_parser_monad__parsec_take__while1___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__8___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_parser_monad__parsec_take__while1___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__8(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__17___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__17(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__19___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__19(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__21___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__21(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__23___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__23(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__25___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__25(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__27___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__27(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = lean::string_iterator_has_next(x_2);
if (x_5 == 0)
{
obj* x_7; 
lean::dec(x_0);
x_7 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_7;
}
else
{
uint32 x_8; uint8 x_9; 
x_8 = lean::string_iterator_curr(x_2);
x_9 = l_lean_is__id__end__escape(x_8);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_13; obj* x_14; 
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_sub(x_0, x_10);
lean::dec(x_0);
x_13 = lean::string_push(x_1, x_8);
x_14 = lean::string_iterator_next(x_2);
x_0 = x_11;
x_1 = x_13;
x_2 = x_14;
goto _start;
}
else
{
obj* x_17; 
lean::dec(x_0);
x_17 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_17;
}
}
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
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__2(uint32 x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_4 = l_string_join___closed__1;
x_5 = lean::string_push(x_4, x_0);
x_6 = lean::string_iterator_remaining(x_2);
x_7 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__3(x_6, x_5, x_2);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_3);
return x_8;
}
}
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__5(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = lean::string_iterator_has_next(x_2);
if (x_5 == 0)
{
obj* x_7; 
lean::dec(x_0);
x_7 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_7;
}
else
{
uint32 x_8; uint8 x_9; 
x_8 = lean::string_iterator_curr(x_2);
x_9 = l_lean_is__id__end__escape(x_8);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_13; obj* x_14; 
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_sub(x_0, x_10);
lean::dec(x_0);
x_13 = lean::string_push(x_1, x_8);
x_14 = lean::string_iterator_next(x_2);
x_0 = x_11;
x_1 = x_13;
x_2 = x_14;
goto _start;
}
else
{
obj* x_17; 
lean::dec(x_0);
x_17 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_17;
}
}
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
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__4(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint32 x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_4 = lean::string_iterator_curr(x_0);
x_5 = l_string_join___closed__1;
x_6 = lean::string_push(x_5, x_4);
x_7 = lean::string_iterator_remaining(x_2);
x_8 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__5(x_7, x_6, x_2);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_3);
return x_9;
}
}
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__7(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = lean::string_iterator_has_next(x_2);
if (x_5 == 0)
{
obj* x_7; 
lean::dec(x_0);
x_7 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_7;
}
else
{
uint32 x_8; uint8 x_9; 
x_8 = lean::string_iterator_curr(x_2);
x_9 = l_lean_is__id__end__escape(x_8);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_13; obj* x_14; 
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_sub(x_0, x_10);
lean::dec(x_0);
x_13 = lean::string_push(x_1, x_8);
x_14 = lean::string_iterator_next(x_2);
x_0 = x_11;
x_1 = x_13;
x_2 = x_14;
goto _start;
}
else
{
obj* x_17; 
lean::dec(x_0);
x_17 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_17;
}
}
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
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__6(uint32 x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_4 = l_string_join___closed__1;
x_5 = lean::string_push(x_4, x_0);
x_6 = lean::string_iterator_remaining(x_2);
x_7 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__7(x_6, x_5, x_2);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_3);
return x_8;
}
}
obj* l_lean_parser_monad__parsec_take__while1___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = lean::string_iterator_has_next(x_1);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_14; obj* x_15; 
x_4 = lean::box(0);
x_5 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_6 = l_mjoin___rarg___closed__1;
x_7 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_5, x_6, x_4, x_4, x_0, x_1, x_2);
lean::dec(x_1);
x_9 = lean::cnstr_get(x_7, 0);
x_11 = lean::cnstr_get(x_7, 1);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_set(x_7, 0, lean::box(0));
 lean::cnstr_set(x_7, 1, lean::box(0));
 x_13 = x_7;
} else {
 lean::inc(x_9);
 lean::inc(x_11);
 lean::dec(x_7);
 x_13 = lean::box(0);
}
x_14 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_15 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_14, x_9);
if (lean::obj_tag(x_15) == 0)
{
obj* x_17; obj* x_19; obj* x_21; uint32 x_24; obj* x_25; obj* x_26; obj* x_28; obj* x_30; obj* x_31; obj* x_32; 
lean::dec(x_13);
x_17 = lean::cnstr_get(x_15, 0);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_15, 1);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_15, 2);
lean::inc(x_21);
lean::dec(x_15);
x_24 = lean::unbox_uint32(x_17);
x_25 = l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__2(x_24, x_0, x_19, x_11);
x_26 = lean::cnstr_get(x_25, 0);
x_28 = lean::cnstr_get(x_25, 1);
if (lean::is_exclusive(x_25)) {
 x_30 = x_25;
} else {
 lean::inc(x_26);
 lean::inc(x_28);
 lean::dec(x_25);
 x_30 = lean::box(0);
}
x_31 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_21, x_26);
if (lean::is_scalar(x_30)) {
 x_32 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_32 = x_30;
}
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_28);
return x_32;
}
else
{
obj* x_33; uint8 x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; 
x_33 = lean::cnstr_get(x_15, 0);
x_35 = lean::cnstr_get_scalar<uint8>(x_15, sizeof(void*)*1);
if (lean::is_exclusive(x_15)) {
 x_36 = x_15;
} else {
 lean::inc(x_33);
 lean::dec(x_15);
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
if (lean::is_scalar(x_13)) {
 x_39 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_39 = x_13;
}
lean::cnstr_set(x_39, 0, x_38);
lean::cnstr_set(x_39, 1, x_11);
return x_39;
}
}
else
{
uint32 x_40; uint8 x_41; 
x_40 = lean::string_iterator_curr(x_1);
x_41 = l_lean_is__id__end__escape(x_40);
if (x_41 == 0)
{
obj* x_43; obj* x_44; obj* x_46; obj* x_48; obj* x_50; obj* x_51; obj* x_52; obj* x_53; 
lean::inc(x_1);
x_43 = lean::string_iterator_next(x_1);
x_44 = l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__4(x_1, x_0, x_43, x_2);
lean::dec(x_1);
x_46 = lean::cnstr_get(x_44, 0);
x_48 = lean::cnstr_get(x_44, 1);
if (lean::is_exclusive(x_44)) {
 x_50 = x_44;
} else {
 lean::inc(x_46);
 lean::inc(x_48);
 lean::dec(x_44);
 x_50 = lean::box(0);
}
x_51 = lean::box(0);
x_52 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_51, x_46);
if (lean::is_scalar(x_50)) {
 x_53 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_53 = x_50;
}
lean::cnstr_set(x_53, 0, x_52);
lean::cnstr_set(x_53, 1, x_48);
return x_53;
}
else
{
obj* x_54; obj* x_55; obj* x_56; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_63; obj* x_65; obj* x_67; obj* x_68; obj* x_69; 
x_54 = l_char_quote__core(x_40);
x_55 = l_char_has__repr___closed__1;
x_56 = lean::string_append(x_55, x_54);
lean::dec(x_54);
x_58 = lean::string_append(x_56, x_55);
x_59 = lean::box(0);
x_60 = l_mjoin___rarg___closed__1;
x_61 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_58, x_60, x_59, x_59, x_0, x_1, x_2);
lean::dec(x_1);
x_63 = lean::cnstr_get(x_61, 0);
x_65 = lean::cnstr_get(x_61, 1);
if (lean::is_exclusive(x_61)) {
 lean::cnstr_set(x_61, 0, lean::box(0));
 lean::cnstr_set(x_61, 1, lean::box(0));
 x_67 = x_61;
} else {
 lean::inc(x_63);
 lean::inc(x_65);
 lean::dec(x_61);
 x_67 = lean::box(0);
}
x_68 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_69 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_68, x_63);
if (lean::obj_tag(x_69) == 0)
{
obj* x_71; obj* x_73; obj* x_75; uint32 x_78; obj* x_79; obj* x_80; obj* x_82; obj* x_84; obj* x_85; obj* x_86; 
lean::dec(x_67);
x_71 = lean::cnstr_get(x_69, 0);
lean::inc(x_71);
x_73 = lean::cnstr_get(x_69, 1);
lean::inc(x_73);
x_75 = lean::cnstr_get(x_69, 2);
lean::inc(x_75);
lean::dec(x_69);
x_78 = lean::unbox_uint32(x_71);
x_79 = l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__6(x_78, x_0, x_73, x_65);
x_80 = lean::cnstr_get(x_79, 0);
x_82 = lean::cnstr_get(x_79, 1);
if (lean::is_exclusive(x_79)) {
 x_84 = x_79;
} else {
 lean::inc(x_80);
 lean::inc(x_82);
 lean::dec(x_79);
 x_84 = lean::box(0);
}
x_85 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_75, x_80);
if (lean::is_scalar(x_84)) {
 x_86 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_86 = x_84;
}
lean::cnstr_set(x_86, 0, x_85);
lean::cnstr_set(x_86, 1, x_82);
return x_86;
}
else
{
obj* x_87; uint8 x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; 
x_87 = lean::cnstr_get(x_69, 0);
x_89 = lean::cnstr_get_scalar<uint8>(x_69, sizeof(void*)*1);
if (lean::is_exclusive(x_69)) {
 x_90 = x_69;
} else {
 lean::inc(x_87);
 lean::dec(x_69);
 x_90 = lean::box(0);
}
if (lean::is_scalar(x_90)) {
 x_91 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_91 = x_90;
}
lean::cnstr_set(x_91, 0, x_87);
lean::cnstr_set_scalar(x_91, sizeof(void*)*1, x_89);
x_92 = x_91;
if (lean::is_scalar(x_67)) {
 x_93 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_93 = x_67;
}
lean::cnstr_set(x_93, 0, x_92);
lean::cnstr_set(x_93, 1, x_65);
return x_93;
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
if (x_4 == 0)
{
uint8 x_5; 
x_5 = lean::string_iterator_has_next(x_2);
if (x_5 == 0)
{
obj* x_7; 
lean::dec(x_0);
x_7 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_7;
}
else
{
uint32 x_8; uint8 x_9; 
x_8 = lean::string_iterator_curr(x_2);
x_9 = l_lean_is__id__rest(x_8);
if (x_9 == 0)
{
obj* x_11; 
lean::dec(x_0);
x_11 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_11;
}
else
{
obj* x_12; obj* x_13; obj* x_15; obj* x_16; 
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_sub(x_0, x_12);
lean::dec(x_0);
x_15 = lean::string_push(x_1, x_8);
x_16 = lean::string_iterator_next(x_2);
x_0 = x_13;
x_1 = x_15;
x_2 = x_16;
goto _start;
}
}
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
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__8___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = lean::string_iterator_remaining(x_0);
x_3 = l_string_join___closed__1;
x_4 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__9(x_2, x_3, x_0);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_1);
return x_5;
}
}
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__8(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__8___rarg), 2, 0);
return x_1;
}
}
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__11(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = lean::string_iterator_has_next(x_2);
if (x_5 == 0)
{
obj* x_7; 
lean::dec(x_0);
x_7 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_7;
}
else
{
uint32 x_8; uint8 x_9; 
x_8 = lean::string_iterator_curr(x_2);
x_9 = l_lean_is__id__rest(x_8);
if (x_9 == 0)
{
obj* x_11; 
lean::dec(x_0);
x_11 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_11;
}
else
{
obj* x_12; obj* x_13; obj* x_15; obj* x_16; 
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_sub(x_0, x_12);
lean::dec(x_0);
x_15 = lean::string_push(x_1, x_8);
x_16 = lean::string_iterator_next(x_2);
x_0 = x_13;
x_1 = x_15;
x_2 = x_16;
goto _start;
}
}
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
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__10___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = lean::string_iterator_remaining(x_0);
x_3 = l_string_join___closed__1;
x_4 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__11(x_2, x_3, x_0);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_1);
return x_5;
}
}
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__10(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__10___rarg), 2, 0);
return x_1;
}
}
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__13(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = lean::string_iterator_has_next(x_2);
if (x_5 == 0)
{
obj* x_7; 
lean::dec(x_0);
x_7 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_7;
}
else
{
uint32 x_8; uint8 x_9; 
x_8 = lean::string_iterator_curr(x_2);
x_9 = l_lean_is__id__rest(x_8);
if (x_9 == 0)
{
obj* x_11; 
lean::dec(x_0);
x_11 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_11;
}
else
{
obj* x_12; obj* x_13; obj* x_15; obj* x_16; 
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_sub(x_0, x_12);
lean::dec(x_0);
x_15 = lean::string_push(x_1, x_8);
x_16 = lean::string_iterator_next(x_2);
x_0 = x_13;
x_1 = x_15;
x_2 = x_16;
goto _start;
}
}
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
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__12___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = lean::string_iterator_remaining(x_0);
x_3 = l_string_join___closed__1;
x_4 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__13(x_2, x_3, x_0);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_1);
return x_5;
}
}
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__12(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__12___rarg), 2, 0);
return x_1;
}
}
obj* l_lean_parser_detail__ident__part_parser_lean_parser_has__view___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; 
x_6 = l_lean_parser_monad__parsec_str__core___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__3(x_0, x_1, x_3, x_4, x_5);
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
x_18 = l_lean_parser_mk__raw__res(x_2, x_12);
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
lean::dec(x_2);
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
obj* l_lean_parser_detail__ident__part_parser_lean_parser_has__view___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = l_lean_parser_monad__parsec_take__while1___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__1(x_1, x_2, x_3);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
if (lean::obj_tag(x_5) == 0)
{
obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_14; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_7 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_9 = x_4;
} else {
 lean::inc(x_7);
 lean::dec(x_4);
 x_9 = lean::box(0);
}
x_10 = lean::cnstr_get(x_5, 1);
x_12 = lean::cnstr_get(x_5, 2);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 x_14 = x_5;
} else {
 lean::inc(x_10);
 lean::inc(x_12);
 lean::dec(x_5);
 x_14 = lean::box(0);
}
lean::inc(x_10);
x_16 = l_lean_parser_mk__raw__res(x_0, x_10);
x_17 = l_lean_parser_finish__comment__block___closed__2;
if (lean::is_scalar(x_14)) {
 x_18 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_18 = x_14;
}
lean::cnstr_set(x_18, 0, x_16);
lean::cnstr_set(x_18, 1, x_10);
lean::cnstr_set(x_18, 2, x_17);
x_19 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_12, x_18);
if (lean::is_scalar(x_9)) {
 x_20 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_20 = x_9;
}
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_7);
return x_20;
}
else
{
obj* x_22; obj* x_24; obj* x_25; uint8 x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; 
lean::dec(x_0);
x_22 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_24 = x_4;
} else {
 lean::inc(x_22);
 lean::dec(x_4);
 x_24 = lean::box(0);
}
x_25 = lean::cnstr_get(x_5, 0);
x_27 = lean::cnstr_get_scalar<uint8>(x_5, sizeof(void*)*1);
if (lean::is_exclusive(x_5)) {
 x_28 = x_5;
} else {
 lean::inc(x_25);
 lean::dec(x_5);
 x_28 = lean::box(0);
}
if (lean::is_scalar(x_28)) {
 x_29 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_29 = x_28;
}
lean::cnstr_set(x_29, 0, x_25);
lean::cnstr_set_scalar(x_29, sizeof(void*)*1, x_27);
x_30 = x_29;
if (lean::is_scalar(x_24)) {
 x_31 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_31 = x_24;
}
lean::cnstr_set(x_31, 0, x_30);
lean::cnstr_set(x_31, 1, x_22);
return x_31;
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
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_13; obj* x_15; obj* x_18; obj* x_19; 
x_8 = lean::box(0);
x_9 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_10 = l_mjoin___rarg___closed__1;
x_11 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_9, x_10, x_8, x_8, x_1, x_2, x_3);
lean::dec(x_2);
x_13 = lean::cnstr_get(x_11, 0);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_11, 1);
lean::inc(x_15);
lean::dec(x_11);
x_18 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_19 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_18, x_13);
if (lean::obj_tag(x_19) == 0)
{
obj* x_20; obj* x_22; obj* x_25; obj* x_26; obj* x_28; obj* x_31; 
x_20 = lean::cnstr_get(x_19, 1);
lean::inc(x_20);
x_22 = lean::cnstr_get(x_19, 2);
lean::inc(x_22);
lean::dec(x_19);
x_25 = l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__8___rarg(x_20, x_15);
x_26 = lean::cnstr_get(x_25, 0);
lean::inc(x_26);
x_28 = lean::cnstr_get(x_25, 1);
lean::inc(x_28);
lean::dec(x_25);
x_31 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_22, x_26);
x_4 = x_31;
x_5 = x_28;
goto lbl_6;
}
else
{
obj* x_32; uint8 x_34; obj* x_35; obj* x_36; obj* x_37; 
x_32 = lean::cnstr_get(x_19, 0);
x_34 = lean::cnstr_get_scalar<uint8>(x_19, sizeof(void*)*1);
if (lean::is_exclusive(x_19)) {
 x_35 = x_19;
} else {
 lean::inc(x_32);
 lean::dec(x_19);
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
x_4 = x_37;
x_5 = x_15;
goto lbl_6;
}
}
else
{
uint32 x_38; uint8 x_39; 
x_38 = lean::string_iterator_curr(x_2);
x_39 = l_lean_is__id__first(x_38);
if (x_39 == 0)
{
obj* x_40; obj* x_41; obj* x_42; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_49; obj* x_51; obj* x_54; obj* x_55; 
x_40 = l_char_quote__core(x_38);
x_41 = l_char_has__repr___closed__1;
x_42 = lean::string_append(x_41, x_40);
lean::dec(x_40);
x_44 = lean::string_append(x_42, x_41);
x_45 = lean::box(0);
x_46 = l_mjoin___rarg___closed__1;
x_47 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_44, x_46, x_45, x_45, x_1, x_2, x_3);
lean::dec(x_2);
x_49 = lean::cnstr_get(x_47, 0);
lean::inc(x_49);
x_51 = lean::cnstr_get(x_47, 1);
lean::inc(x_51);
lean::dec(x_47);
x_54 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_55 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_54, x_49);
if (lean::obj_tag(x_55) == 0)
{
obj* x_56; obj* x_58; obj* x_61; obj* x_62; obj* x_64; obj* x_67; 
x_56 = lean::cnstr_get(x_55, 1);
lean::inc(x_56);
x_58 = lean::cnstr_get(x_55, 2);
lean::inc(x_58);
lean::dec(x_55);
x_61 = l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__10___rarg(x_56, x_51);
x_62 = lean::cnstr_get(x_61, 0);
lean::inc(x_62);
x_64 = lean::cnstr_get(x_61, 1);
lean::inc(x_64);
lean::dec(x_61);
x_67 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_58, x_62);
x_4 = x_67;
x_5 = x_64;
goto lbl_6;
}
else
{
obj* x_68; uint8 x_70; obj* x_71; obj* x_72; obj* x_73; 
x_68 = lean::cnstr_get(x_55, 0);
x_70 = lean::cnstr_get_scalar<uint8>(x_55, sizeof(void*)*1);
if (lean::is_exclusive(x_55)) {
 x_71 = x_55;
} else {
 lean::inc(x_68);
 lean::dec(x_55);
 x_71 = lean::box(0);
}
if (lean::is_scalar(x_71)) {
 x_72 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_72 = x_71;
}
lean::cnstr_set(x_72, 0, x_68);
lean::cnstr_set_scalar(x_72, sizeof(void*)*1, x_70);
x_73 = x_72;
x_4 = x_73;
x_5 = x_51;
goto lbl_6;
}
}
else
{
obj* x_74; obj* x_75; obj* x_76; obj* x_78; obj* x_81; obj* x_82; 
x_74 = lean::string_iterator_next(x_2);
x_75 = l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__12___rarg(x_74, x_3);
x_76 = lean::cnstr_get(x_75, 0);
lean::inc(x_76);
x_78 = lean::cnstr_get(x_75, 1);
lean::inc(x_78);
lean::dec(x_75);
x_81 = lean::box(0);
x_82 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_81, x_76);
x_4 = x_82;
x_5 = x_78;
goto lbl_6;
}
}
lbl_6:
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_83; obj* x_85; obj* x_87; obj* x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; 
x_83 = lean::cnstr_get(x_4, 1);
x_85 = lean::cnstr_get(x_4, 2);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_87 = x_4;
} else {
 lean::inc(x_83);
 lean::inc(x_85);
 lean::dec(x_4);
 x_87 = lean::box(0);
}
lean::inc(x_83);
x_89 = l_lean_parser_mk__raw__res(x_0, x_83);
x_90 = l_lean_parser_finish__comment__block___closed__2;
if (lean::is_scalar(x_87)) {
 x_91 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_91 = x_87;
}
lean::cnstr_set(x_91, 0, x_89);
lean::cnstr_set(x_91, 1, x_83);
lean::cnstr_set(x_91, 2, x_90);
x_92 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_85, x_91);
x_93 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_93, 0, x_92);
lean::cnstr_set(x_93, 1, x_5);
return x_93;
}
else
{
obj* x_95; uint8 x_97; obj* x_98; obj* x_99; obj* x_100; obj* x_101; 
lean::dec(x_0);
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
}
}
obj* _init_l_lean_parser_detail__ident__part_parser_lean_parser_has__view() {
_start:
{
obj* x_0; uint32 x_1; obj* x_3; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_11; obj* x_12; obj* x_14; uint32 x_15; obj* x_16; obj* x_18; obj* x_19; obj* x_20; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; 
x_0 = lean::mk_string("");
x_1 = l_lean_id__begin__escape;
lean::inc(x_0);
x_3 = lean::string_push(x_0, x_1);
lean::inc(x_3);
x_5 = l_string_quote(x_3);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_6, 0, x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_with__trailing___rarg___lambda__1), 2, 0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_lift___at_lean_parser_with__trailing___spec__1___rarg___boxed), 4, 1);
lean::closure_set(x_8, 0, x_7);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_detail__ident__part_parser_lean_parser_has__view___lambda__1___boxed), 6, 2);
lean::closure_set(x_9, 0, x_3);
lean::closure_set(x_9, 1, x_6);
lean::inc(x_8);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_bind___at_lean_parser_with__trailing___spec__2___rarg), 5, 2);
lean::closure_set(x_11, 0, x_8);
lean::closure_set(x_11, 1, x_9);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_detail__ident__part_parser_lean_parser_has__view___lambda__2___boxed), 4, 0);
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
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_detail__ident__part_parser_lean_parser_has__view___lambda__1___boxed), 6, 2);
lean::closure_set(x_20, 0, x_16);
lean::closure_set(x_20, 1, x_19);
lean::inc(x_8);
x_22 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_bind___at_lean_parser_with__trailing___spec__2___rarg), 5, 2);
lean::closure_set(x_22, 0, x_8);
lean::closure_set(x_22, 1, x_20);
x_23 = lean::box(0);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_22);
lean::cnstr_set(x_24, 1, x_23);
x_25 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_25, 0, x_14);
lean::cnstr_set(x_25, 1, x_24);
x_26 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_26, 0, x_11);
lean::cnstr_set(x_26, 1, x_25);
x_27 = l_lean_parser_detail__ident__part__escaped;
x_28 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__15), 5, 2);
lean::closure_set(x_28, 0, x_27);
lean::closure_set(x_28, 1, x_26);
x_29 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_detail__ident__part_parser_lean_parser_has__view___lambda__3___boxed), 4, 0);
x_30 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_bind___at_lean_parser_with__trailing___spec__2___rarg), 5, 2);
lean::closure_set(x_30, 0, x_8);
lean::closure_set(x_30, 1, x_29);
x_31 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_31, 0, x_30);
lean::cnstr_set(x_31, 1, x_23);
x_32 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_32, 0, x_28);
lean::cnstr_set(x_32, 1, x_31);
x_33 = lean::mk_nat_obj(0u);
x_34 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_choice__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__29), 5, 2);
lean::closure_set(x_34, 0, x_32);
lean::closure_set(x_34, 1, x_33);
x_35 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_23);
x_36 = l_lean_parser_basic__parser__m_monad;
x_37 = l_lean_parser_basic__parser__m_monad__except;
x_38 = l_lean_parser_basic__parser__m_lean_parser_monad__parsec;
x_39 = l_lean_parser_basic__parser__m_alternative;
x_40 = l_lean_parser_detail__ident__part;
x_41 = l_lean_parser_detail__ident__part_has__view;
x_42 = l_lean_parser_combinators_node_view___rarg(x_36, x_37, x_38, x_39, x_40, x_35, x_41);
lean::dec(x_35);
return x_42;
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint32 x_4; obj* x_5; 
x_4 = lean::unbox_uint32(x_0);
x_5 = l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__2(x_4, x_1, x_2, x_3);
lean::dec(x_1);
return x_5;
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__4___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__4(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
return x_4;
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__6___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint32 x_4; obj* x_5; 
x_4 = lean::unbox_uint32(x_0);
x_5 = l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__6(x_4, x_1, x_2, x_3);
lean::dec(x_1);
return x_5;
}
}
obj* l_lean_parser_monad__parsec_take__while1___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_parser_monad__parsec_take__while1___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__1(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__8___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__8(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__10___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__10(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__12___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__12(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_parser_detail__ident__part_parser_lean_parser_has__view___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_lean_parser_detail__ident__part_parser_lean_parser_has__view___lambda__1(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_3);
return x_6;
}
}
obj* l_lean_parser_detail__ident__part_parser_lean_parser_has__view___lambda__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_parser_detail__ident__part_parser_lean_parser_has__view___lambda__2(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_lean_parser_detail__ident__part_parser_lean_parser_has__view___lambda__3___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_parser_detail__ident__part_parser_lean_parser_has__view___lambda__3(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = lean::string_iterator_has_next(x_2);
if (x_5 == 0)
{
obj* x_7; 
lean::dec(x_0);
x_7 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_7;
}
else
{
uint32 x_8; uint8 x_9; 
x_8 = lean::string_iterator_curr(x_2);
x_9 = l_lean_is__id__end__escape(x_8);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_13; obj* x_14; 
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_sub(x_0, x_10);
lean::dec(x_0);
x_13 = lean::string_push(x_1, x_8);
x_14 = lean::string_iterator_next(x_2);
x_0 = x_11;
x_1 = x_13;
x_2 = x_14;
goto _start;
}
else
{
obj* x_17; 
lean::dec(x_0);
x_17 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_17;
}
}
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
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser___spec__2(uint32 x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_4 = l_string_join___closed__1;
x_5 = lean::string_push(x_4, x_0);
x_6 = lean::string_iterator_remaining(x_2);
x_7 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser___spec__3(x_6, x_5, x_2);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_3);
return x_8;
}
}
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser___spec__5(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = lean::string_iterator_has_next(x_2);
if (x_5 == 0)
{
obj* x_7; 
lean::dec(x_0);
x_7 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_7;
}
else
{
uint32 x_8; uint8 x_9; 
x_8 = lean::string_iterator_curr(x_2);
x_9 = l_lean_is__id__end__escape(x_8);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_13; obj* x_14; 
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_sub(x_0, x_10);
lean::dec(x_0);
x_13 = lean::string_push(x_1, x_8);
x_14 = lean::string_iterator_next(x_2);
x_0 = x_11;
x_1 = x_13;
x_2 = x_14;
goto _start;
}
else
{
obj* x_17; 
lean::dec(x_0);
x_17 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_17;
}
}
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
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser___spec__4(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint32 x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_4 = lean::string_iterator_curr(x_0);
x_5 = l_string_join___closed__1;
x_6 = lean::string_push(x_5, x_4);
x_7 = lean::string_iterator_remaining(x_2);
x_8 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser___spec__5(x_7, x_6, x_2);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_3);
return x_9;
}
}
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser___spec__7(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = lean::string_iterator_has_next(x_2);
if (x_5 == 0)
{
obj* x_7; 
lean::dec(x_0);
x_7 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_7;
}
else
{
uint32 x_8; uint8 x_9; 
x_8 = lean::string_iterator_curr(x_2);
x_9 = l_lean_is__id__end__escape(x_8);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_13; obj* x_14; 
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_sub(x_0, x_10);
lean::dec(x_0);
x_13 = lean::string_push(x_1, x_8);
x_14 = lean::string_iterator_next(x_2);
x_0 = x_11;
x_1 = x_13;
x_2 = x_14;
goto _start;
}
else
{
obj* x_17; 
lean::dec(x_0);
x_17 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_17;
}
}
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
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser___spec__6(uint32 x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_4 = l_string_join___closed__1;
x_5 = lean::string_push(x_4, x_0);
x_6 = lean::string_iterator_remaining(x_2);
x_7 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser___spec__7(x_6, x_5, x_2);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_3);
return x_8;
}
}
obj* l_lean_parser_monad__parsec_take__while1___at_lean_parser_detail__ident__part_parser___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = lean::string_iterator_has_next(x_1);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_14; obj* x_15; 
x_4 = lean::box(0);
x_5 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_6 = l_mjoin___rarg___closed__1;
x_7 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_5, x_6, x_4, x_4, x_0, x_1, x_2);
lean::dec(x_1);
x_9 = lean::cnstr_get(x_7, 0);
x_11 = lean::cnstr_get(x_7, 1);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_set(x_7, 0, lean::box(0));
 lean::cnstr_set(x_7, 1, lean::box(0));
 x_13 = x_7;
} else {
 lean::inc(x_9);
 lean::inc(x_11);
 lean::dec(x_7);
 x_13 = lean::box(0);
}
x_14 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_15 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_14, x_9);
if (lean::obj_tag(x_15) == 0)
{
obj* x_17; obj* x_19; obj* x_21; uint32 x_24; obj* x_25; obj* x_26; obj* x_28; obj* x_30; obj* x_31; obj* x_32; 
lean::dec(x_13);
x_17 = lean::cnstr_get(x_15, 0);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_15, 1);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_15, 2);
lean::inc(x_21);
lean::dec(x_15);
x_24 = lean::unbox_uint32(x_17);
x_25 = l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser___spec__2(x_24, x_0, x_19, x_11);
x_26 = lean::cnstr_get(x_25, 0);
x_28 = lean::cnstr_get(x_25, 1);
if (lean::is_exclusive(x_25)) {
 x_30 = x_25;
} else {
 lean::inc(x_26);
 lean::inc(x_28);
 lean::dec(x_25);
 x_30 = lean::box(0);
}
x_31 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_21, x_26);
if (lean::is_scalar(x_30)) {
 x_32 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_32 = x_30;
}
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_28);
return x_32;
}
else
{
obj* x_33; uint8 x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; 
x_33 = lean::cnstr_get(x_15, 0);
x_35 = lean::cnstr_get_scalar<uint8>(x_15, sizeof(void*)*1);
if (lean::is_exclusive(x_15)) {
 x_36 = x_15;
} else {
 lean::inc(x_33);
 lean::dec(x_15);
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
if (lean::is_scalar(x_13)) {
 x_39 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_39 = x_13;
}
lean::cnstr_set(x_39, 0, x_38);
lean::cnstr_set(x_39, 1, x_11);
return x_39;
}
}
else
{
uint32 x_40; uint8 x_41; 
x_40 = lean::string_iterator_curr(x_1);
x_41 = l_lean_is__id__end__escape(x_40);
if (x_41 == 0)
{
obj* x_43; obj* x_44; obj* x_46; obj* x_48; obj* x_50; obj* x_51; obj* x_52; obj* x_53; 
lean::inc(x_1);
x_43 = lean::string_iterator_next(x_1);
x_44 = l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser___spec__4(x_1, x_0, x_43, x_2);
lean::dec(x_1);
x_46 = lean::cnstr_get(x_44, 0);
x_48 = lean::cnstr_get(x_44, 1);
if (lean::is_exclusive(x_44)) {
 x_50 = x_44;
} else {
 lean::inc(x_46);
 lean::inc(x_48);
 lean::dec(x_44);
 x_50 = lean::box(0);
}
x_51 = lean::box(0);
x_52 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_51, x_46);
if (lean::is_scalar(x_50)) {
 x_53 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_53 = x_50;
}
lean::cnstr_set(x_53, 0, x_52);
lean::cnstr_set(x_53, 1, x_48);
return x_53;
}
else
{
obj* x_54; obj* x_55; obj* x_56; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_63; obj* x_65; obj* x_67; obj* x_68; obj* x_69; 
x_54 = l_char_quote__core(x_40);
x_55 = l_char_has__repr___closed__1;
x_56 = lean::string_append(x_55, x_54);
lean::dec(x_54);
x_58 = lean::string_append(x_56, x_55);
x_59 = lean::box(0);
x_60 = l_mjoin___rarg___closed__1;
x_61 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_58, x_60, x_59, x_59, x_0, x_1, x_2);
lean::dec(x_1);
x_63 = lean::cnstr_get(x_61, 0);
x_65 = lean::cnstr_get(x_61, 1);
if (lean::is_exclusive(x_61)) {
 lean::cnstr_set(x_61, 0, lean::box(0));
 lean::cnstr_set(x_61, 1, lean::box(0));
 x_67 = x_61;
} else {
 lean::inc(x_63);
 lean::inc(x_65);
 lean::dec(x_61);
 x_67 = lean::box(0);
}
x_68 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_69 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_68, x_63);
if (lean::obj_tag(x_69) == 0)
{
obj* x_71; obj* x_73; obj* x_75; uint32 x_78; obj* x_79; obj* x_80; obj* x_82; obj* x_84; obj* x_85; obj* x_86; 
lean::dec(x_67);
x_71 = lean::cnstr_get(x_69, 0);
lean::inc(x_71);
x_73 = lean::cnstr_get(x_69, 1);
lean::inc(x_73);
x_75 = lean::cnstr_get(x_69, 2);
lean::inc(x_75);
lean::dec(x_69);
x_78 = lean::unbox_uint32(x_71);
x_79 = l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser___spec__6(x_78, x_0, x_73, x_65);
x_80 = lean::cnstr_get(x_79, 0);
x_82 = lean::cnstr_get(x_79, 1);
if (lean::is_exclusive(x_79)) {
 x_84 = x_79;
} else {
 lean::inc(x_80);
 lean::inc(x_82);
 lean::dec(x_79);
 x_84 = lean::box(0);
}
x_85 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_75, x_80);
if (lean::is_scalar(x_84)) {
 x_86 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_86 = x_84;
}
lean::cnstr_set(x_86, 0, x_85);
lean::cnstr_set(x_86, 1, x_82);
return x_86;
}
else
{
obj* x_87; uint8 x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; 
x_87 = lean::cnstr_get(x_69, 0);
x_89 = lean::cnstr_get_scalar<uint8>(x_69, sizeof(void*)*1);
if (lean::is_exclusive(x_69)) {
 x_90 = x_69;
} else {
 lean::inc(x_87);
 lean::dec(x_69);
 x_90 = lean::box(0);
}
if (lean::is_scalar(x_90)) {
 x_91 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_91 = x_90;
}
lean::cnstr_set(x_91, 0, x_87);
lean::cnstr_set_scalar(x_91, sizeof(void*)*1, x_89);
x_92 = x_91;
if (lean::is_scalar(x_67)) {
 x_93 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_93 = x_67;
}
lean::cnstr_set(x_93, 0, x_92);
lean::cnstr_set(x_93, 1, x_65);
return x_93;
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
if (x_4 == 0)
{
uint8 x_5; 
x_5 = lean::string_iterator_has_next(x_2);
if (x_5 == 0)
{
obj* x_7; 
lean::dec(x_0);
x_7 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_7;
}
else
{
uint32 x_8; uint8 x_9; 
x_8 = lean::string_iterator_curr(x_2);
x_9 = l_lean_is__id__rest(x_8);
if (x_9 == 0)
{
obj* x_11; 
lean::dec(x_0);
x_11 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_11;
}
else
{
obj* x_12; obj* x_13; obj* x_15; obj* x_16; 
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_sub(x_0, x_12);
lean::dec(x_0);
x_15 = lean::string_push(x_1, x_8);
x_16 = lean::string_iterator_next(x_2);
x_0 = x_13;
x_1 = x_15;
x_2 = x_16;
goto _start;
}
}
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
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser___spec__8___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = lean::string_iterator_remaining(x_0);
x_3 = l_string_join___closed__1;
x_4 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser___spec__9(x_2, x_3, x_0);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_1);
return x_5;
}
}
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser___spec__8(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser___spec__8___rarg), 2, 0);
return x_1;
}
}
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser___spec__11(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = lean::string_iterator_has_next(x_2);
if (x_5 == 0)
{
obj* x_7; 
lean::dec(x_0);
x_7 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_7;
}
else
{
uint32 x_8; uint8 x_9; 
x_8 = lean::string_iterator_curr(x_2);
x_9 = l_lean_is__id__rest(x_8);
if (x_9 == 0)
{
obj* x_11; 
lean::dec(x_0);
x_11 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_11;
}
else
{
obj* x_12; obj* x_13; obj* x_15; obj* x_16; 
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_sub(x_0, x_12);
lean::dec(x_0);
x_15 = lean::string_push(x_1, x_8);
x_16 = lean::string_iterator_next(x_2);
x_0 = x_13;
x_1 = x_15;
x_2 = x_16;
goto _start;
}
}
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
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser___spec__10___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = lean::string_iterator_remaining(x_0);
x_3 = l_string_join___closed__1;
x_4 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser___spec__11(x_2, x_3, x_0);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_1);
return x_5;
}
}
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser___spec__10(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser___spec__10___rarg), 2, 0);
return x_1;
}
}
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser___spec__13(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = lean::string_iterator_has_next(x_2);
if (x_5 == 0)
{
obj* x_7; 
lean::dec(x_0);
x_7 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_7;
}
else
{
uint32 x_8; uint8 x_9; 
x_8 = lean::string_iterator_curr(x_2);
x_9 = l_lean_is__id__rest(x_8);
if (x_9 == 0)
{
obj* x_11; 
lean::dec(x_0);
x_11 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_11;
}
else
{
obj* x_12; obj* x_13; obj* x_15; obj* x_16; 
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_sub(x_0, x_12);
lean::dec(x_0);
x_15 = lean::string_push(x_1, x_8);
x_16 = lean::string_iterator_next(x_2);
x_0 = x_13;
x_1 = x_15;
x_2 = x_16;
goto _start;
}
}
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
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser___spec__12___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = lean::string_iterator_remaining(x_0);
x_3 = l_string_join___closed__1;
x_4 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_detail__ident__part_parser___spec__13(x_2, x_3, x_0);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_1);
return x_5;
}
}
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser___spec__12(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser___spec__12___rarg), 2, 0);
return x_1;
}
}
obj* l_lean_parser_detail__ident__part_parser___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = l_lean_parser_monad__parsec_take__while1___at_lean_parser_detail__ident__part_parser___spec__1(x_1, x_2, x_3);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
if (lean::obj_tag(x_5) == 0)
{
obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_14; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_7 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_9 = x_4;
} else {
 lean::inc(x_7);
 lean::dec(x_4);
 x_9 = lean::box(0);
}
x_10 = lean::cnstr_get(x_5, 1);
x_12 = lean::cnstr_get(x_5, 2);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 x_14 = x_5;
} else {
 lean::inc(x_10);
 lean::inc(x_12);
 lean::dec(x_5);
 x_14 = lean::box(0);
}
lean::inc(x_10);
x_16 = l_lean_parser_mk__raw__res(x_0, x_10);
x_17 = l_lean_parser_finish__comment__block___closed__2;
if (lean::is_scalar(x_14)) {
 x_18 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_18 = x_14;
}
lean::cnstr_set(x_18, 0, x_16);
lean::cnstr_set(x_18, 1, x_10);
lean::cnstr_set(x_18, 2, x_17);
x_19 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_12, x_18);
if (lean::is_scalar(x_9)) {
 x_20 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_20 = x_9;
}
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_7);
return x_20;
}
else
{
obj* x_22; obj* x_24; obj* x_25; uint8 x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; 
lean::dec(x_0);
x_22 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_24 = x_4;
} else {
 lean::inc(x_22);
 lean::dec(x_4);
 x_24 = lean::box(0);
}
x_25 = lean::cnstr_get(x_5, 0);
x_27 = lean::cnstr_get_scalar<uint8>(x_5, sizeof(void*)*1);
if (lean::is_exclusive(x_5)) {
 x_28 = x_5;
} else {
 lean::inc(x_25);
 lean::dec(x_5);
 x_28 = lean::box(0);
}
if (lean::is_scalar(x_28)) {
 x_29 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_29 = x_28;
}
lean::cnstr_set(x_29, 0, x_25);
lean::cnstr_set_scalar(x_29, sizeof(void*)*1, x_27);
x_30 = x_29;
if (lean::is_scalar(x_24)) {
 x_31 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_31 = x_24;
}
lean::cnstr_set(x_31, 0, x_30);
lean::cnstr_set(x_31, 1, x_22);
return x_31;
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
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_13; obj* x_15; obj* x_18; obj* x_19; 
x_8 = lean::box(0);
x_9 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_10 = l_mjoin___rarg___closed__1;
x_11 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_9, x_10, x_8, x_8, x_1, x_2, x_3);
lean::dec(x_2);
x_13 = lean::cnstr_get(x_11, 0);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_11, 1);
lean::inc(x_15);
lean::dec(x_11);
x_18 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_19 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_18, x_13);
if (lean::obj_tag(x_19) == 0)
{
obj* x_20; obj* x_22; obj* x_25; obj* x_26; obj* x_28; obj* x_31; 
x_20 = lean::cnstr_get(x_19, 1);
lean::inc(x_20);
x_22 = lean::cnstr_get(x_19, 2);
lean::inc(x_22);
lean::dec(x_19);
x_25 = l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser___spec__8___rarg(x_20, x_15);
x_26 = lean::cnstr_get(x_25, 0);
lean::inc(x_26);
x_28 = lean::cnstr_get(x_25, 1);
lean::inc(x_28);
lean::dec(x_25);
x_31 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_22, x_26);
x_4 = x_31;
x_5 = x_28;
goto lbl_6;
}
else
{
obj* x_32; uint8 x_34; obj* x_35; obj* x_36; obj* x_37; 
x_32 = lean::cnstr_get(x_19, 0);
x_34 = lean::cnstr_get_scalar<uint8>(x_19, sizeof(void*)*1);
if (lean::is_exclusive(x_19)) {
 x_35 = x_19;
} else {
 lean::inc(x_32);
 lean::dec(x_19);
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
x_4 = x_37;
x_5 = x_15;
goto lbl_6;
}
}
else
{
uint32 x_38; uint8 x_39; 
x_38 = lean::string_iterator_curr(x_2);
x_39 = l_lean_is__id__first(x_38);
if (x_39 == 0)
{
obj* x_40; obj* x_41; obj* x_42; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_49; obj* x_51; obj* x_54; obj* x_55; 
x_40 = l_char_quote__core(x_38);
x_41 = l_char_has__repr___closed__1;
x_42 = lean::string_append(x_41, x_40);
lean::dec(x_40);
x_44 = lean::string_append(x_42, x_41);
x_45 = lean::box(0);
x_46 = l_mjoin___rarg___closed__1;
x_47 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_44, x_46, x_45, x_45, x_1, x_2, x_3);
lean::dec(x_2);
x_49 = lean::cnstr_get(x_47, 0);
lean::inc(x_49);
x_51 = lean::cnstr_get(x_47, 1);
lean::inc(x_51);
lean::dec(x_47);
x_54 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_55 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_54, x_49);
if (lean::obj_tag(x_55) == 0)
{
obj* x_56; obj* x_58; obj* x_61; obj* x_62; obj* x_64; obj* x_67; 
x_56 = lean::cnstr_get(x_55, 1);
lean::inc(x_56);
x_58 = lean::cnstr_get(x_55, 2);
lean::inc(x_58);
lean::dec(x_55);
x_61 = l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser___spec__10___rarg(x_56, x_51);
x_62 = lean::cnstr_get(x_61, 0);
lean::inc(x_62);
x_64 = lean::cnstr_get(x_61, 1);
lean::inc(x_64);
lean::dec(x_61);
x_67 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_58, x_62);
x_4 = x_67;
x_5 = x_64;
goto lbl_6;
}
else
{
obj* x_68; uint8 x_70; obj* x_71; obj* x_72; obj* x_73; 
x_68 = lean::cnstr_get(x_55, 0);
x_70 = lean::cnstr_get_scalar<uint8>(x_55, sizeof(void*)*1);
if (lean::is_exclusive(x_55)) {
 x_71 = x_55;
} else {
 lean::inc(x_68);
 lean::dec(x_55);
 x_71 = lean::box(0);
}
if (lean::is_scalar(x_71)) {
 x_72 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_72 = x_71;
}
lean::cnstr_set(x_72, 0, x_68);
lean::cnstr_set_scalar(x_72, sizeof(void*)*1, x_70);
x_73 = x_72;
x_4 = x_73;
x_5 = x_51;
goto lbl_6;
}
}
else
{
obj* x_74; obj* x_75; obj* x_76; obj* x_78; obj* x_81; obj* x_82; 
x_74 = lean::string_iterator_next(x_2);
x_75 = l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser___spec__12___rarg(x_74, x_3);
x_76 = lean::cnstr_get(x_75, 0);
lean::inc(x_76);
x_78 = lean::cnstr_get(x_75, 1);
lean::inc(x_78);
lean::dec(x_75);
x_81 = lean::box(0);
x_82 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_81, x_76);
x_4 = x_82;
x_5 = x_78;
goto lbl_6;
}
}
lbl_6:
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_83; obj* x_85; obj* x_87; obj* x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; 
x_83 = lean::cnstr_get(x_4, 1);
x_85 = lean::cnstr_get(x_4, 2);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_87 = x_4;
} else {
 lean::inc(x_83);
 lean::inc(x_85);
 lean::dec(x_4);
 x_87 = lean::box(0);
}
lean::inc(x_83);
x_89 = l_lean_parser_mk__raw__res(x_0, x_83);
x_90 = l_lean_parser_finish__comment__block___closed__2;
if (lean::is_scalar(x_87)) {
 x_91 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_91 = x_87;
}
lean::cnstr_set(x_91, 0, x_89);
lean::cnstr_set(x_91, 1, x_83);
lean::cnstr_set(x_91, 2, x_90);
x_92 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_85, x_91);
x_93 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_93, 0, x_92);
lean::cnstr_set(x_93, 1, x_5);
return x_93;
}
else
{
obj* x_95; uint8 x_97; obj* x_98; obj* x_99; obj* x_100; obj* x_101; 
lean::dec(x_0);
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
}
}
obj* _init_l_lean_parser_detail__ident__part_parser___closed__1() {
_start:
{
obj* x_0; uint32 x_1; obj* x_3; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_11; obj* x_12; obj* x_14; uint32 x_15; obj* x_16; obj* x_18; obj* x_19; obj* x_20; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; 
x_0 = lean::mk_string("");
x_1 = l_lean_id__begin__escape;
lean::inc(x_0);
x_3 = lean::string_push(x_0, x_1);
lean::inc(x_3);
x_5 = l_string_quote(x_3);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_6, 0, x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_with__trailing___rarg___lambda__1), 2, 0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_lift___at_lean_parser_with__trailing___spec__1___rarg___boxed), 4, 1);
lean::closure_set(x_8, 0, x_7);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_detail__ident__part_parser_lean_parser_has__view___lambda__1___boxed), 6, 2);
lean::closure_set(x_9, 0, x_3);
lean::closure_set(x_9, 1, x_6);
lean::inc(x_8);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_bind___at_lean_parser_with__trailing___spec__2___rarg), 5, 2);
lean::closure_set(x_11, 0, x_8);
lean::closure_set(x_11, 1, x_9);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_detail__ident__part_parser___lambda__1___boxed), 4, 0);
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
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_detail__ident__part_parser_lean_parser_has__view___lambda__1___boxed), 6, 2);
lean::closure_set(x_20, 0, x_16);
lean::closure_set(x_20, 1, x_19);
lean::inc(x_8);
x_22 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_bind___at_lean_parser_with__trailing___spec__2___rarg), 5, 2);
lean::closure_set(x_22, 0, x_8);
lean::closure_set(x_22, 1, x_20);
x_23 = lean::box(0);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_22);
lean::cnstr_set(x_24, 1, x_23);
x_25 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_25, 0, x_14);
lean::cnstr_set(x_25, 1, x_24);
x_26 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_26, 0, x_11);
lean::cnstr_set(x_26, 1, x_25);
x_27 = l_lean_parser_detail__ident__part__escaped;
x_28 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__15), 5, 2);
lean::closure_set(x_28, 0, x_27);
lean::closure_set(x_28, 1, x_26);
x_29 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_detail__ident__part_parser___lambda__2___boxed), 4, 0);
x_30 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_bind___at_lean_parser_with__trailing___spec__2___rarg), 5, 2);
lean::closure_set(x_30, 0, x_8);
lean::closure_set(x_30, 1, x_29);
x_31 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_31, 0, x_30);
lean::cnstr_set(x_31, 1, x_23);
x_32 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_32, 0, x_28);
lean::cnstr_set(x_32, 1, x_31);
x_33 = lean::mk_nat_obj(0u);
x_34 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_choice__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__29), 5, 2);
lean::closure_set(x_34, 0, x_32);
lean::closure_set(x_34, 1, x_33);
x_35 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_23);
return x_35;
}
}
obj* l_lean_parser_detail__ident__part_parser(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = l_lean_parser_detail__ident__part;
x_4 = l_lean_parser_detail__ident__part_parser___closed__1;
x_5 = l_lean_parser_combinators_node___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__15(x_3, x_4, x_0, x_1, x_2);
return x_5;
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint32 x_4; obj* x_5; 
x_4 = lean::unbox_uint32(x_0);
x_5 = l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser___spec__2(x_4, x_1, x_2, x_3);
lean::dec(x_1);
return x_5;
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser___spec__4___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser___spec__4(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
return x_4;
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser___spec__6___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint32 x_4; obj* x_5; 
x_4 = lean::unbox_uint32(x_0);
x_5 = l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser___spec__6(x_4, x_1, x_2, x_3);
lean::dec(x_1);
return x_5;
}
}
obj* l_lean_parser_monad__parsec_take__while1___at_lean_parser_detail__ident__part_parser___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_parser_monad__parsec_take__while1___at_lean_parser_detail__ident__part_parser___spec__1(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser___spec__8___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser___spec__8(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser___spec__10___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser___spec__10(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser___spec__12___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser___spec__12(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_parser_detail__ident__part_parser___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_parser_detail__ident__part_parser___lambda__1(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_lean_parser_detail__ident__part_parser___lambda__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_parser_detail__ident__part_parser___lambda__2(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
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
obj* x_2; 
x_2 = l_lean_parser_detail__ident__suffix_has__view_x_27___lambda__1___closed__1;
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_6; 
x_3 = lean::cnstr_get(x_1, 0);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 x_5 = x_1;
} else {
 lean::inc(x_3);
 lean::dec(x_1);
 x_5 = lean::box(0);
}
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
lean::dec(x_3);
if (lean::obj_tag(x_6) == 0)
{
lean::dec(x_5);
if (lean::obj_tag(x_6) == 0)
{
obj* x_10; 
x_10 = l_lean_parser_detail__ident__suffix_has__view_x_27___lambda__1___closed__1;
return x_10;
}
else
{
obj* x_11; obj* x_14; obj* x_15; 
x_11 = lean::cnstr_get(x_6, 0);
lean::inc(x_11);
lean::dec(x_6);
x_14 = lean::box(0);
x_15 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_15, 0, x_14);
lean::cnstr_set(x_15, 1, x_11);
return x_15;
}
}
else
{
obj* x_16; 
x_16 = lean::cnstr_get(x_6, 0);
lean::inc(x_16);
switch (lean::obj_tag(x_16)) {
case 0:
{
obj* x_18; obj* x_21; obj* x_24; 
x_18 = lean::cnstr_get(x_6, 1);
lean::inc(x_18);
lean::dec(x_6);
x_21 = lean::cnstr_get(x_16, 0);
lean::inc(x_21);
lean::dec(x_16);
if (lean::is_scalar(x_5)) {
 x_24 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_24 = x_5;
}
lean::cnstr_set(x_24, 0, x_21);
if (lean::obj_tag(x_18) == 0)
{
obj* x_25; obj* x_26; 
x_25 = lean::box(3);
x_26 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_26, 0, x_24);
lean::cnstr_set(x_26, 1, x_25);
return x_26;
}
else
{
obj* x_27; obj* x_30; 
x_27 = lean::cnstr_get(x_18, 0);
lean::inc(x_27);
lean::dec(x_18);
x_30 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_30, 0, x_24);
lean::cnstr_set(x_30, 1, x_27);
return x_30;
}
}
case 3:
{
obj* x_32; 
lean::dec(x_5);
x_32 = lean::cnstr_get(x_6, 1);
lean::inc(x_32);
lean::dec(x_6);
if (lean::obj_tag(x_32) == 0)
{
obj* x_35; 
x_35 = l_lean_parser_detail__ident__suffix_has__view_x_27___lambda__1___closed__1;
return x_35;
}
else
{
obj* x_36; obj* x_39; obj* x_40; 
x_36 = lean::cnstr_get(x_32, 0);
lean::inc(x_36);
lean::dec(x_32);
x_39 = lean::box(0);
x_40 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_40, 0, x_39);
lean::cnstr_set(x_40, 1, x_36);
return x_40;
}
}
default:
{
obj* x_43; 
lean::dec(x_5);
lean::dec(x_16);
x_43 = lean::cnstr_get(x_6, 1);
lean::inc(x_43);
lean::dec(x_6);
if (lean::obj_tag(x_43) == 0)
{
obj* x_46; 
x_46 = l_lean_parser_detail__ident__suffix_has__view_x_27___lambda__1___closed__1;
return x_46;
}
else
{
obj* x_47; obj* x_50; obj* x_51; 
x_47 = lean::cnstr_get(x_43, 0);
lean::inc(x_47);
lean::dec(x_43);
x_50 = lean::box(0);
x_51 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_51, 0, x_50);
lean::cnstr_set(x_51, 1, x_47);
return x_51;
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
obj* x_1; obj* x_3; obj* x_6; obj* x_7; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
x_6 = lean::box(0);
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_3);
lean::cnstr_set(x_7, 1, x_6);
if (lean::obj_tag(x_1) == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_8 = l_lean_parser_raw_view___rarg___lambda__2___closed__1;
x_9 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_7);
x_10 = l_lean_parser_detail__ident__suffix;
x_11 = l_lean_parser_syntax_mk__node(x_10, x_9);
return x_11;
}
else
{
obj* x_12; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_20; obj* x_21; obj* x_22; 
x_12 = lean::cnstr_get(x_1, 0);
if (lean::is_exclusive(x_1)) {
 x_14 = x_1;
} else {
 lean::inc(x_12);
 lean::dec(x_1);
 x_14 = lean::box(0);
}
x_15 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_15, 0, x_12);
if (lean::is_scalar(x_14)) {
 x_16 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_16 = x_14;
}
lean::cnstr_set(x_16, 0, x_15);
x_17 = lean::box(3);
x_18 = l_option_get__or__else___main___rarg(x_16, x_17);
lean::dec(x_16);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_18);
lean::cnstr_set(x_20, 1, x_7);
x_21 = l_lean_parser_detail__ident__suffix;
x_22 = l_lean_parser_syntax_mk__node(x_21, x_20);
return x_22;
}
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
return x_0;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; obj* x_9; uint8 x_10; obj* x_11; obj* x_12; obj* x_13; 
x_8 = l_option_get__or__else___main___rarg(x_2, x_6);
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
lean::cnstr_set(x_13, 1, x_7);
return x_13;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__2(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__2___rarg___boxed), 8, 0);
return x_1;
}
}
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__1(uint32 x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; 
x_5 = lean::string_iterator_has_next(x_3);
if (x_5 == 0)
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_6 = lean::box(0);
x_7 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_8 = l_mjoin___rarg___closed__1;
x_9 = l_lean_parser_monad__parsec_error___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__2___rarg(x_7, x_8, x_6, x_6, x_1, x_2, x_3, x_4);
lean::dec(x_3);
x_11 = lean::cnstr_get(x_9, 0);
x_13 = lean::cnstr_get(x_9, 1);
if (lean::is_exclusive(x_9)) {
 x_15 = x_9;
} else {
 lean::inc(x_11);
 lean::inc(x_13);
 lean::dec(x_9);
 x_15 = lean::box(0);
}
x_16 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_17 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_11);
if (lean::is_scalar(x_15)) {
 x_18 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_18 = x_15;
}
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_13);
return x_18;
}
else
{
uint32 x_19; uint8 x_20; 
x_19 = lean::string_iterator_curr(x_3);
x_20 = x_19 == x_0;
if (x_20 == 0)
{
obj* x_21; obj* x_22; obj* x_23; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_30; obj* x_32; obj* x_34; obj* x_35; obj* x_36; obj* x_37; 
x_21 = l_char_quote__core(x_19);
x_22 = l_char_has__repr___closed__1;
x_23 = lean::string_append(x_22, x_21);
lean::dec(x_21);
x_25 = lean::string_append(x_23, x_22);
x_26 = lean::box(0);
x_27 = l_mjoin___rarg___closed__1;
x_28 = l_lean_parser_monad__parsec_error___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__2___rarg(x_25, x_27, x_26, x_26, x_1, x_2, x_3, x_4);
lean::dec(x_3);
x_30 = lean::cnstr_get(x_28, 0);
x_32 = lean::cnstr_get(x_28, 1);
if (lean::is_exclusive(x_28)) {
 x_34 = x_28;
} else {
 lean::inc(x_30);
 lean::inc(x_32);
 lean::dec(x_28);
 x_34 = lean::box(0);
}
x_35 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_36 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_35, x_30);
if (lean::is_scalar(x_34)) {
 x_37 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_37 = x_34;
}
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_32);
return x_37;
}
else
{
obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; 
x_38 = lean::string_iterator_next(x_3);
x_39 = lean::box(0);
x_40 = lean::box_uint32(x_19);
x_41 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_41, 0, x_40);
lean::cnstr_set(x_41, 1, x_38);
lean::cnstr_set(x_41, 2, x_39);
x_42 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_42, 0, x_41);
lean::cnstr_set(x_42, 1, x_4);
return x_42;
}
}
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__3___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; obj* x_9; uint8 x_10; obj* x_11; obj* x_12; obj* x_13; 
x_8 = l_option_get__or__else___main___rarg(x_2, x_6);
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
lean::cnstr_set(x_13, 1, x_7);
return x_13;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__3(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__3___rarg___boxed), 8, 0);
return x_1;
}
}
obj* l_lean_parser_parsec__t_lookahead___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__4(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; uint32 x_7; obj* x_9; obj* x_10; 
x_7 = 46;
lean::inc(x_2);
x_9 = l_lean_parser_monad__parsec_ch___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__1(x_7, x_0, x_1, x_2, x_3);
x_10 = lean::cnstr_get(x_9, 0);
lean::inc(x_10);
if (lean::obj_tag(x_10) == 0)
{
obj* x_12; obj* x_15; obj* x_17; obj* x_19; uint32 x_20; obj* x_22; obj* x_23; 
x_12 = lean::cnstr_get(x_9, 1);
lean::inc(x_12);
lean::dec(x_9);
x_15 = lean::cnstr_get(x_10, 1);
x_17 = lean::cnstr_get(x_10, 2);
if (lean::is_exclusive(x_10)) {
 lean::cnstr_release(x_10, 0);
 lean::cnstr_set(x_10, 1, lean::box(0));
 lean::cnstr_set(x_10, 2, lean::box(0));
 x_19 = x_10;
} else {
 lean::inc(x_15);
 lean::inc(x_17);
 lean::dec(x_10);
 x_19 = lean::box(0);
}
x_20 = l_lean_id__begin__escape;
lean::inc(x_15);
x_22 = l_lean_parser_monad__parsec_ch___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__1(x_20, x_0, x_1, x_15, x_12);
x_23 = lean::cnstr_get(x_22, 0);
lean::inc(x_23);
if (lean::obj_tag(x_23) == 0)
{
obj* x_27; obj* x_30; 
lean::dec(x_15);
lean::dec(x_19);
x_27 = lean::cnstr_get(x_22, 1);
lean::inc(x_27);
lean::dec(x_22);
x_30 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_17, x_23);
x_4 = x_30;
x_5 = x_27;
goto lbl_6;
}
else
{
uint8 x_31; 
x_31 = lean::cnstr_get_scalar<uint8>(x_23, sizeof(void*)*1);
if (x_31 == 0)
{
obj* x_32; obj* x_35; uint8 x_38; 
x_32 = lean::cnstr_get(x_22, 1);
lean::inc(x_32);
lean::dec(x_22);
x_35 = lean::cnstr_get(x_23, 0);
lean::inc(x_35);
lean::dec(x_23);
x_38 = lean::string_iterator_has_next(x_15);
if (x_38 == 0)
{
obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_45; obj* x_47; obj* x_50; obj* x_51; obj* x_52; obj* x_53; 
lean::dec(x_19);
x_40 = lean::box(0);
x_41 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_42 = l_mjoin___rarg___closed__1;
x_43 = l_lean_parser_monad__parsec_error___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__3___rarg(x_41, x_42, x_40, x_40, x_0, x_1, x_15, x_32);
lean::dec(x_15);
x_45 = lean::cnstr_get(x_43, 0);
lean::inc(x_45);
x_47 = lean::cnstr_get(x_43, 1);
lean::inc(x_47);
lean::dec(x_43);
x_50 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_51 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_50, x_45);
x_52 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_35, x_51);
x_53 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_17, x_52);
x_4 = x_53;
x_5 = x_47;
goto lbl_6;
}
else
{
uint32 x_54; uint8 x_55; 
x_54 = lean::string_iterator_curr(x_15);
x_55 = l_lean_is__id__first(x_54);
if (x_55 == 0)
{
obj* x_57; obj* x_58; obj* x_59; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_66; obj* x_68; obj* x_71; obj* x_72; obj* x_73; obj* x_74; 
lean::dec(x_19);
x_57 = l_char_quote__core(x_54);
x_58 = l_char_has__repr___closed__1;
x_59 = lean::string_append(x_58, x_57);
lean::dec(x_57);
x_61 = lean::string_append(x_59, x_58);
x_62 = lean::box(0);
x_63 = l_mjoin___rarg___closed__1;
x_64 = l_lean_parser_monad__parsec_error___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__3___rarg(x_61, x_63, x_62, x_62, x_0, x_1, x_15, x_32);
lean::dec(x_15);
x_66 = lean::cnstr_get(x_64, 0);
lean::inc(x_66);
x_68 = lean::cnstr_get(x_64, 1);
lean::inc(x_68);
lean::dec(x_64);
x_71 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_72 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_71, x_66);
x_73 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_35, x_72);
x_74 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_17, x_73);
x_4 = x_74;
x_5 = x_68;
goto lbl_6;
}
else
{
obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; 
lean::dec(x_35);
x_76 = lean::string_iterator_next(x_15);
x_77 = lean::box(0);
x_78 = lean::box_uint32(x_54);
if (lean::is_scalar(x_19)) {
 x_79 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_79 = x_19;
}
lean::cnstr_set(x_79, 0, x_78);
lean::cnstr_set(x_79, 1, x_76);
lean::cnstr_set(x_79, 2, x_77);
x_80 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_17, x_79);
x_4 = x_80;
x_5 = x_32;
goto lbl_6;
}
}
}
else
{
obj* x_83; obj* x_86; 
lean::dec(x_15);
lean::dec(x_19);
x_83 = lean::cnstr_get(x_22, 1);
lean::inc(x_83);
lean::dec(x_22);
x_86 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_17, x_23);
x_4 = x_86;
x_5 = x_83;
goto lbl_6;
}
}
}
else
{
obj* x_87; obj* x_90; uint8 x_92; obj* x_93; obj* x_94; obj* x_95; 
x_87 = lean::cnstr_get(x_9, 1);
lean::inc(x_87);
lean::dec(x_9);
x_90 = lean::cnstr_get(x_10, 0);
x_92 = lean::cnstr_get_scalar<uint8>(x_10, sizeof(void*)*1);
if (lean::is_exclusive(x_10)) {
 x_93 = x_10;
} else {
 lean::inc(x_90);
 lean::dec(x_10);
 x_93 = lean::box(0);
}
if (lean::is_scalar(x_93)) {
 x_94 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_94 = x_93;
}
lean::cnstr_set(x_94, 0, x_90);
lean::cnstr_set_scalar(x_94, sizeof(void*)*1, x_92);
x_95 = x_94;
x_4 = x_95;
x_5 = x_87;
goto lbl_6;
}
lbl_6:
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_96; obj* x_98; obj* x_99; obj* x_100; obj* x_101; 
x_96 = lean::cnstr_get(x_4, 0);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 1);
 lean::cnstr_release(x_4, 2);
 x_98 = x_4;
} else {
 lean::inc(x_96);
 lean::dec(x_4);
 x_98 = lean::box(0);
}
x_99 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_98)) {
 x_100 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_100 = x_98;
}
lean::cnstr_set(x_100, 0, x_96);
lean::cnstr_set(x_100, 1, x_2);
lean::cnstr_set(x_100, 2, x_99);
x_101 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_101, 0, x_100);
lean::cnstr_set(x_101, 1, x_5);
return x_101;
}
else
{
obj* x_103; 
lean::dec(x_2);
x_103 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_103, 0, x_4);
lean::cnstr_set(x_103, 1, x_5);
return x_103;
}
}
}
}
obj* l_reader__t_lift___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__5___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = lean::apply_3(x_0, x_2, x_3, x_4);
return x_5;
}
}
obj* l_reader__t_lift___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__5(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_lift___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__5___rarg___boxed), 5, 0);
return x_1;
}
}
obj* l_lean_parser_monad__parsec_str__core___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__6(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; 
x_6 = l_string_is__empty(x_0);
if (x_6 == 0)
{
obj* x_7; obj* x_9; obj* x_11; 
x_7 = lean::string_length(x_0);
lean::inc(x_0);
x_9 = lean::string_mk_iterator(x_0);
lean::inc(x_4);
x_11 = l___private_init_lean_parser_parsec_1__str__aux___main(x_7, x_9, x_4);
if (lean::obj_tag(x_11) == 0)
{
obj* x_13; obj* x_14; obj* x_15; uint8 x_16; obj* x_17; obj* x_18; obj* x_19; 
lean::dec(x_0);
x_13 = lean::box(0);
x_14 = l_string_join___closed__1;
x_15 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_15, 0, x_4);
lean::cnstr_set(x_15, 1, x_14);
lean::cnstr_set(x_15, 2, x_1);
lean::cnstr_set(x_15, 3, x_13);
x_16 = 0;
x_17 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set_scalar(x_17, sizeof(void*)*1, x_16);
x_18 = x_17;
x_19 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_19, 0, x_18);
lean::cnstr_set(x_19, 1, x_5);
return x_19;
}
else
{
obj* x_22; obj* x_25; obj* x_26; obj* x_27; 
lean::dec(x_4);
lean::dec(x_1);
x_22 = lean::cnstr_get(x_11, 0);
lean::inc(x_22);
lean::dec(x_11);
x_25 = lean::box(0);
x_26 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_26, 0, x_0);
lean::cnstr_set(x_26, 1, x_22);
lean::cnstr_set(x_26, 2, x_25);
x_27 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_5);
return x_27;
}
}
else
{
obj* x_30; obj* x_31; obj* x_32; obj* x_33; 
lean::dec(x_1);
lean::dec(x_0);
x_30 = l_string_join___closed__1;
x_31 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_32 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_32, 0, x_30);
lean::cnstr_set(x_32, 1, x_4);
lean::cnstr_set(x_32, 2, x_31);
x_33 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_5);
return x_33;
}
}
}
obj* l_reader__t_bind___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__7___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_8; obj* x_9; 
lean::inc(x_3);
lean::inc(x_2);
x_8 = lean::apply_4(x_0, x_2, x_3, x_4, x_5);
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
if (lean::obj_tag(x_9) == 0)
{
obj* x_11; obj* x_14; obj* x_16; obj* x_18; obj* x_21; obj* x_22; obj* x_24; obj* x_26; obj* x_27; obj* x_28; 
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
lean::dec(x_8);
x_14 = lean::cnstr_get(x_9, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_9, 1);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_9, 2);
lean::inc(x_18);
lean::dec(x_9);
x_21 = lean::apply_5(x_1, x_14, x_2, x_3, x_16, x_11);
x_22 = lean::cnstr_get(x_21, 0);
x_24 = lean::cnstr_get(x_21, 1);
if (lean::is_exclusive(x_21)) {
 x_26 = x_21;
} else {
 lean::inc(x_22);
 lean::inc(x_24);
 lean::dec(x_21);
 x_26 = lean::box(0);
}
x_27 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_18, x_22);
if (lean::is_scalar(x_26)) {
 x_28 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_28 = x_26;
}
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_24);
return x_28;
}
else
{
obj* x_32; obj* x_34; obj* x_35; uint8 x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; 
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_2);
x_32 = lean::cnstr_get(x_8, 1);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_release(x_8, 0);
 x_34 = x_8;
} else {
 lean::inc(x_32);
 lean::dec(x_8);
 x_34 = lean::box(0);
}
x_35 = lean::cnstr_get(x_9, 0);
x_37 = lean::cnstr_get_scalar<uint8>(x_9, sizeof(void*)*1);
if (lean::is_exclusive(x_9)) {
 x_38 = x_9;
} else {
 lean::inc(x_35);
 lean::dec(x_9);
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
return x_41;
}
}
}
obj* l_reader__t_bind___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__7(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_bind___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__7___rarg), 6, 0);
return x_2;
}
}
obj* l_lean_parser_rec__t_recurse___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__8(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_8; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_5 = lean::apply_4(x_1, x_0, x_2, x_3, x_4);
x_6 = lean::cnstr_get(x_5, 0);
x_8 = lean::cnstr_get(x_5, 1);
if (lean::is_exclusive(x_5)) {
 x_10 = x_5;
} else {
 lean::inc(x_6);
 lean::inc(x_8);
 lean::dec(x_5);
 x_10 = lean::box(0);
}
x_11 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_12 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_11, x_6);
if (lean::is_scalar(x_10)) {
 x_13 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_13 = x_10;
}
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_8);
return x_13;
}
}
obj* l_list_mfoldl___main___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__10(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_10; obj* x_11; obj* x_12; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_0);
x_10 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_11 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_11, 0, x_1);
lean::cnstr_set(x_11, 1, x_5);
lean::cnstr_set(x_11, 2, x_10);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_6);
return x_12;
}
else
{
obj* x_13; obj* x_15; obj* x_17; obj* x_18; obj* x_19; obj* x_23; obj* x_24; 
x_13 = lean::cnstr_get(x_2, 0);
x_15 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_set(x_2, 0, lean::box(0));
 lean::cnstr_set(x_2, 1, lean::box(0));
 x_17 = x_2;
} else {
 lean::inc(x_13);
 lean::inc(x_15);
 lean::dec(x_2);
 x_17 = lean::box(0);
}
lean::inc(x_4);
lean::inc(x_3);
x_23 = lean::apply_4(x_13, x_3, x_4, x_5, x_6);
x_24 = lean::cnstr_get(x_23, 0);
lean::inc(x_24);
if (lean::obj_tag(x_24) == 0)
{
obj* x_26; 
x_26 = lean::cnstr_get(x_23, 1);
lean::inc(x_26);
lean::dec(x_23);
x_18 = x_24;
x_19 = x_26;
goto lbl_20;
}
else
{
uint8 x_29; 
x_29 = lean::cnstr_get_scalar<uint8>(x_24, sizeof(void*)*1);
if (lean::obj_tag(x_1) == 0)
{
if (x_29 == 0)
{
obj* x_30; obj* x_33; obj* x_35; uint8 x_36; obj* x_37; obj* x_38; 
x_30 = lean::cnstr_get(x_23, 1);
lean::inc(x_30);
lean::dec(x_23);
x_33 = lean::cnstr_get(x_24, 0);
if (lean::is_exclusive(x_24)) {
 x_35 = x_24;
} else {
 lean::inc(x_33);
 lean::dec(x_24);
 x_35 = lean::box(0);
}
x_36 = 0;
if (lean::is_scalar(x_35)) {
 x_37 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_37 = x_35;
}
lean::cnstr_set(x_37, 0, x_33);
lean::cnstr_set_scalar(x_37, sizeof(void*)*1, x_36);
x_38 = x_37;
x_18 = x_38;
x_19 = x_30;
goto lbl_20;
}
else
{
obj* x_39; obj* x_42; obj* x_44; obj* x_45; obj* x_46; 
x_39 = lean::cnstr_get(x_23, 1);
lean::inc(x_39);
lean::dec(x_23);
x_42 = lean::cnstr_get(x_24, 0);
if (lean::is_exclusive(x_24)) {
 x_44 = x_24;
} else {
 lean::inc(x_42);
 lean::dec(x_24);
 x_44 = lean::box(0);
}
if (lean::is_scalar(x_44)) {
 x_45 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_45 = x_44;
}
lean::cnstr_set(x_45, 0, x_42);
lean::cnstr_set_scalar(x_45, sizeof(void*)*1, x_29);
x_46 = x_45;
x_18 = x_46;
x_19 = x_39;
goto lbl_20;
}
}
else
{
obj* x_47; obj* x_50; obj* x_52; obj* x_53; obj* x_55; obj* x_58; obj* x_59; obj* x_61; obj* x_63; obj* x_66; obj* x_68; obj* x_69; obj* x_70; 
x_47 = lean::cnstr_get(x_23, 1);
lean::inc(x_47);
lean::dec(x_23);
x_50 = lean::cnstr_get(x_24, 0);
if (lean::is_exclusive(x_24)) {
 lean::cnstr_set(x_24, 0, lean::box(0));
 x_52 = x_24;
} else {
 lean::inc(x_50);
 lean::dec(x_24);
 x_52 = lean::box(0);
}
x_53 = lean::cnstr_get(x_50, 3);
lean::inc(x_53);
x_55 = l_option_get___main___at_lean_parser_run___spec__2(x_53);
lean::dec(x_53);
lean::inc(x_1);
x_58 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_58, 0, x_55);
lean::cnstr_set(x_58, 1, x_1);
x_59 = lean::cnstr_get(x_50, 0);
lean::inc(x_59);
x_61 = lean::cnstr_get(x_50, 1);
lean::inc(x_61);
x_63 = lean::cnstr_get(x_50, 2);
lean::inc(x_63);
lean::dec(x_50);
x_66 = l_list_reverse___rarg(x_58);
lean::inc(x_0);
x_68 = l_lean_parser_syntax_mk__node(x_0, x_66);
x_69 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_69, 0, x_68);
x_70 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_70, 0, x_59);
lean::cnstr_set(x_70, 1, x_61);
lean::cnstr_set(x_70, 2, x_63);
lean::cnstr_set(x_70, 3, x_69);
if (x_29 == 0)
{
uint8 x_71; obj* x_72; obj* x_73; 
x_71 = 0;
if (lean::is_scalar(x_52)) {
 x_72 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_72 = x_52;
}
lean::cnstr_set(x_72, 0, x_70);
lean::cnstr_set_scalar(x_72, sizeof(void*)*1, x_71);
x_73 = x_72;
x_18 = x_73;
x_19 = x_47;
goto lbl_20;
}
else
{
obj* x_74; obj* x_75; 
if (lean::is_scalar(x_52)) {
 x_74 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_74 = x_52;
}
lean::cnstr_set(x_74, 0, x_70);
lean::cnstr_set_scalar(x_74, sizeof(void*)*1, x_29);
x_75 = x_74;
x_18 = x_75;
x_19 = x_47;
goto lbl_20;
}
}
}
lbl_20:
{
if (lean::obj_tag(x_18) == 0)
{
obj* x_76; obj* x_78; obj* x_80; obj* x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_86; 
x_76 = lean::cnstr_get(x_18, 0);
x_78 = lean::cnstr_get(x_18, 1);
x_80 = lean::cnstr_get(x_18, 2);
if (lean::is_exclusive(x_18)) {
 x_82 = x_18;
} else {
 lean::inc(x_76);
 lean::inc(x_78);
 lean::inc(x_80);
 lean::dec(x_18);
 x_82 = lean::box(0);
}
if (lean::is_scalar(x_17)) {
 x_83 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_83 = x_17;
}
lean::cnstr_set(x_83, 0, x_76);
lean::cnstr_set(x_83, 1, x_1);
x_84 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_82)) {
 x_85 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_85 = x_82;
}
lean::cnstr_set(x_85, 0, x_83);
lean::cnstr_set(x_85, 1, x_78);
lean::cnstr_set(x_85, 2, x_84);
x_86 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_80, x_85);
if (lean::obj_tag(x_86) == 0)
{
obj* x_87; obj* x_89; obj* x_91; obj* x_94; obj* x_95; obj* x_97; obj* x_99; obj* x_100; obj* x_101; 
x_87 = lean::cnstr_get(x_86, 0);
lean::inc(x_87);
x_89 = lean::cnstr_get(x_86, 1);
lean::inc(x_89);
x_91 = lean::cnstr_get(x_86, 2);
lean::inc(x_91);
lean::dec(x_86);
x_94 = l_list_mfoldl___main___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__10(x_0, x_87, x_15, x_3, x_4, x_89, x_19);
x_95 = lean::cnstr_get(x_94, 0);
x_97 = lean::cnstr_get(x_94, 1);
if (lean::is_exclusive(x_94)) {
 x_99 = x_94;
} else {
 lean::inc(x_95);
 lean::inc(x_97);
 lean::dec(x_94);
 x_99 = lean::box(0);
}
x_100 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_91, x_95);
if (lean::is_scalar(x_99)) {
 x_101 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_101 = x_99;
}
lean::cnstr_set(x_101, 0, x_100);
lean::cnstr_set(x_101, 1, x_97);
return x_101;
}
else
{
obj* x_106; uint8 x_108; obj* x_109; obj* x_110; obj* x_111; obj* x_112; 
lean::dec(x_15);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_0);
x_106 = lean::cnstr_get(x_86, 0);
x_108 = lean::cnstr_get_scalar<uint8>(x_86, sizeof(void*)*1);
if (lean::is_exclusive(x_86)) {
 x_109 = x_86;
} else {
 lean::inc(x_106);
 lean::dec(x_86);
 x_109 = lean::box(0);
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
lean::cnstr_set(x_112, 1, x_19);
return x_112;
}
}
else
{
obj* x_119; uint8 x_121; obj* x_122; obj* x_123; obj* x_124; obj* x_125; 
lean::dec(x_15);
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_17);
x_119 = lean::cnstr_get(x_18, 0);
x_121 = lean::cnstr_get_scalar<uint8>(x_18, sizeof(void*)*1);
if (lean::is_exclusive(x_18)) {
 x_122 = x_18;
} else {
 lean::inc(x_119);
 lean::dec(x_18);
 x_122 = lean::box(0);
}
if (lean::is_scalar(x_122)) {
 x_123 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_123 = x_122;
}
lean::cnstr_set(x_123, 0, x_119);
lean::cnstr_set_scalar(x_123, sizeof(void*)*1, x_121);
x_124 = x_123;
x_125 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_125, 0, x_124);
lean::cnstr_set(x_125, 1, x_19);
return x_125;
}
}
}
}
}
obj* l_lean_parser_combinators_node___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__9(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_8; obj* x_9; 
x_6 = lean::box(0);
lean::inc(x_0);
x_8 = l_list_mfoldl___main___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__10(x_0, x_6, x_1, x_2, x_3, x_4, x_5);
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
x_21 = l_list_reverse___rarg(x_14);
x_22 = l_lean_parser_syntax_mk__node(x_0, x_21);
x_23 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_20)) {
 x_24 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_24 = x_20;
}
lean::cnstr_set(x_24, 0, x_22);
lean::cnstr_set(x_24, 1, x_16);
lean::cnstr_set(x_24, 2, x_23);
x_25 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_18, x_24);
if (lean::is_scalar(x_13)) {
 x_26 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_26 = x_13;
}
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_11);
return x_26;
}
else
{
obj* x_28; obj* x_30; obj* x_31; uint8 x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; 
lean::dec(x_0);
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
return x_37;
}
}
}
obj* _init_l_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_4; obj* x_6; 
x_0 = lean::box(0);
x_1 = l_lean_parser_list_cons_tokens___rarg(x_0, x_0);
x_2 = l_lean_parser_list_cons_tokens___rarg(x_0, x_1);
lean::dec(x_1);
x_4 = l_lean_parser_tokens___rarg(x_2);
lean::dec(x_2);
x_6 = l_lean_parser_tokens___rarg(x_4);
lean::dec(x_4);
return x_6;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__2___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = l_lean_parser_monad__parsec_error___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__2___rarg(x_0, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean::dec(x_2);
lean::dec(x_4);
lean::dec(x_5);
lean::dec(x_6);
return x_8;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__2___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_monad__parsec_error___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__2(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint32 x_5; obj* x_6; 
x_5 = lean::unbox_uint32(x_0);
x_6 = l_lean_parser_monad__parsec_ch___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__1(x_5, x_1, x_2, x_3, x_4);
lean::dec(x_1);
lean::dec(x_2);
return x_6;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__3___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = l_lean_parser_monad__parsec_error___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__3___rarg(x_0, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean::dec(x_2);
lean::dec(x_4);
lean::dec(x_5);
lean::dec(x_6);
return x_8;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__3___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_monad__parsec_error___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__3(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_parser_parsec__t_lookahead___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__4___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_parser_parsec__t_lookahead___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__4(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
return x_4;
}
}
obj* l_reader__t_lift___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__5___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_reader__t_lift___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__5___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
return x_5;
}
}
obj* l_reader__t_lift___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__5___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_reader__t_lift___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__5(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_parser_monad__parsec_str__core___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__6___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_lean_parser_monad__parsec_str__core___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__6(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_2);
lean::dec(x_3);
return x_6;
}
}
obj* l_reader__t_bind___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__7___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_reader__t_bind___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__7(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_lean_parser_parsec__t_lookahead___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__view___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; uint32 x_7; obj* x_9; obj* x_10; 
x_7 = 46;
lean::inc(x_2);
x_9 = l_lean_parser_monad__parsec_ch___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__1(x_7, x_0, x_1, x_2, x_3);
x_10 = lean::cnstr_get(x_9, 0);
lean::inc(x_10);
if (lean::obj_tag(x_10) == 0)
{
obj* x_12; obj* x_15; obj* x_17; obj* x_19; uint32 x_20; obj* x_22; obj* x_23; 
x_12 = lean::cnstr_get(x_9, 1);
lean::inc(x_12);
lean::dec(x_9);
x_15 = lean::cnstr_get(x_10, 1);
x_17 = lean::cnstr_get(x_10, 2);
if (lean::is_exclusive(x_10)) {
 lean::cnstr_release(x_10, 0);
 lean::cnstr_set(x_10, 1, lean::box(0));
 lean::cnstr_set(x_10, 2, lean::box(0));
 x_19 = x_10;
} else {
 lean::inc(x_15);
 lean::inc(x_17);
 lean::dec(x_10);
 x_19 = lean::box(0);
}
x_20 = l_lean_id__begin__escape;
lean::inc(x_15);
x_22 = l_lean_parser_monad__parsec_ch___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__1(x_20, x_0, x_1, x_15, x_12);
x_23 = lean::cnstr_get(x_22, 0);
lean::inc(x_23);
if (lean::obj_tag(x_23) == 0)
{
obj* x_27; obj* x_30; 
lean::dec(x_15);
lean::dec(x_19);
x_27 = lean::cnstr_get(x_22, 1);
lean::inc(x_27);
lean::dec(x_22);
x_30 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_17, x_23);
x_4 = x_30;
x_5 = x_27;
goto lbl_6;
}
else
{
uint8 x_31; 
x_31 = lean::cnstr_get_scalar<uint8>(x_23, sizeof(void*)*1);
if (x_31 == 0)
{
obj* x_32; obj* x_35; uint8 x_38; 
x_32 = lean::cnstr_get(x_22, 1);
lean::inc(x_32);
lean::dec(x_22);
x_35 = lean::cnstr_get(x_23, 0);
lean::inc(x_35);
lean::dec(x_23);
x_38 = lean::string_iterator_has_next(x_15);
if (x_38 == 0)
{
obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_45; obj* x_47; obj* x_50; obj* x_51; obj* x_52; obj* x_53; 
lean::dec(x_19);
x_40 = lean::box(0);
x_41 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_42 = l_mjoin___rarg___closed__1;
x_43 = l_lean_parser_monad__parsec_error___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__3___rarg(x_41, x_42, x_40, x_40, x_0, x_1, x_15, x_32);
lean::dec(x_15);
x_45 = lean::cnstr_get(x_43, 0);
lean::inc(x_45);
x_47 = lean::cnstr_get(x_43, 1);
lean::inc(x_47);
lean::dec(x_43);
x_50 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_51 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_50, x_45);
x_52 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_35, x_51);
x_53 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_17, x_52);
x_4 = x_53;
x_5 = x_47;
goto lbl_6;
}
else
{
uint32 x_54; uint8 x_55; 
x_54 = lean::string_iterator_curr(x_15);
x_55 = l_lean_is__id__first(x_54);
if (x_55 == 0)
{
obj* x_57; obj* x_58; obj* x_59; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_66; obj* x_68; obj* x_71; obj* x_72; obj* x_73; obj* x_74; 
lean::dec(x_19);
x_57 = l_char_quote__core(x_54);
x_58 = l_char_has__repr___closed__1;
x_59 = lean::string_append(x_58, x_57);
lean::dec(x_57);
x_61 = lean::string_append(x_59, x_58);
x_62 = lean::box(0);
x_63 = l_mjoin___rarg___closed__1;
x_64 = l_lean_parser_monad__parsec_error___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__3___rarg(x_61, x_63, x_62, x_62, x_0, x_1, x_15, x_32);
lean::dec(x_15);
x_66 = lean::cnstr_get(x_64, 0);
lean::inc(x_66);
x_68 = lean::cnstr_get(x_64, 1);
lean::inc(x_68);
lean::dec(x_64);
x_71 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_72 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_71, x_66);
x_73 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_35, x_72);
x_74 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_17, x_73);
x_4 = x_74;
x_5 = x_68;
goto lbl_6;
}
else
{
obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; 
lean::dec(x_35);
x_76 = lean::string_iterator_next(x_15);
x_77 = lean::box(0);
x_78 = lean::box_uint32(x_54);
if (lean::is_scalar(x_19)) {
 x_79 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_79 = x_19;
}
lean::cnstr_set(x_79, 0, x_78);
lean::cnstr_set(x_79, 1, x_76);
lean::cnstr_set(x_79, 2, x_77);
x_80 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_17, x_79);
x_4 = x_80;
x_5 = x_32;
goto lbl_6;
}
}
}
else
{
obj* x_83; obj* x_86; 
lean::dec(x_15);
lean::dec(x_19);
x_83 = lean::cnstr_get(x_22, 1);
lean::inc(x_83);
lean::dec(x_22);
x_86 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_17, x_23);
x_4 = x_86;
x_5 = x_83;
goto lbl_6;
}
}
}
else
{
obj* x_87; obj* x_90; uint8 x_92; obj* x_93; obj* x_94; obj* x_95; 
x_87 = lean::cnstr_get(x_9, 1);
lean::inc(x_87);
lean::dec(x_9);
x_90 = lean::cnstr_get(x_10, 0);
x_92 = lean::cnstr_get_scalar<uint8>(x_10, sizeof(void*)*1);
if (lean::is_exclusive(x_10)) {
 x_93 = x_10;
} else {
 lean::inc(x_90);
 lean::dec(x_10);
 x_93 = lean::box(0);
}
if (lean::is_scalar(x_93)) {
 x_94 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_94 = x_93;
}
lean::cnstr_set(x_94, 0, x_90);
lean::cnstr_set_scalar(x_94, sizeof(void*)*1, x_92);
x_95 = x_94;
x_4 = x_95;
x_5 = x_87;
goto lbl_6;
}
lbl_6:
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_96; obj* x_98; obj* x_99; obj* x_100; obj* x_101; 
x_96 = lean::cnstr_get(x_4, 0);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 1);
 lean::cnstr_release(x_4, 2);
 x_98 = x_4;
} else {
 lean::inc(x_96);
 lean::dec(x_4);
 x_98 = lean::box(0);
}
x_99 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_98)) {
 x_100 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_100 = x_98;
}
lean::cnstr_set(x_100, 0, x_96);
lean::cnstr_set(x_100, 1, x_2);
lean::cnstr_set(x_100, 2, x_99);
x_101 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_101, 0, x_100);
lean::cnstr_set(x_101, 1, x_5);
return x_101;
}
else
{
obj* x_103; 
lean::dec(x_2);
x_103 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_103, 0, x_4);
lean::cnstr_set(x_103, 1, x_5);
return x_103;
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
x_7 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 x_9 = x_4;
} else {
 lean::inc(x_5);
 lean::inc(x_7);
 lean::dec(x_4);
 x_9 = lean::box(0);
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
obj* x_6; obj* x_7; obj* x_8; 
x_6 = l_lean_name_to__string___closed__1;
x_7 = l_lean_parser_monad__parsec_str__core___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__6(x_6, x_0, x_2, x_3, x_4, x_5);
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
if (lean::obj_tag(x_8) == 0)
{
obj* x_10; obj* x_12; obj* x_13; obj* x_15; obj* x_17; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
x_10 = lean::cnstr_get(x_7, 1);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 x_12 = x_7;
} else {
 lean::inc(x_10);
 lean::dec(x_7);
 x_12 = lean::box(0);
}
x_13 = lean::cnstr_get(x_8, 1);
x_15 = lean::cnstr_get(x_8, 2);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_release(x_8, 0);
 x_17 = x_8;
} else {
 lean::inc(x_13);
 lean::inc(x_15);
 lean::dec(x_8);
 x_17 = lean::box(0);
}
lean::inc(x_13);
x_19 = l_lean_parser_mk__raw__res(x_1, x_13);
x_20 = l_lean_parser_finish__comment__block___closed__2;
if (lean::is_scalar(x_17)) {
 x_21 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_21 = x_17;
}
lean::cnstr_set(x_21, 0, x_19);
lean::cnstr_set(x_21, 1, x_13);
lean::cnstr_set(x_21, 2, x_20);
x_22 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_21);
if (lean::is_scalar(x_12)) {
 x_23 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_23 = x_12;
}
lean::cnstr_set(x_23, 0, x_22);
lean::cnstr_set(x_23, 1, x_10);
return x_23;
}
else
{
obj* x_25; obj* x_27; obj* x_28; uint8 x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; 
lean::dec(x_1);
x_25 = lean::cnstr_get(x_7, 1);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 x_27 = x_7;
} else {
 lean::inc(x_25);
 lean::dec(x_7);
 x_27 = lean::box(0);
}
x_28 = lean::cnstr_get(x_8, 0);
x_30 = lean::cnstr_get_scalar<uint8>(x_8, sizeof(void*)*1);
if (lean::is_exclusive(x_8)) {
 x_31 = x_8;
} else {
 lean::inc(x_28);
 lean::dec(x_8);
 x_31 = lean::box(0);
}
if (lean::is_scalar(x_31)) {
 x_32 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_32 = x_31;
}
lean::cnstr_set(x_32, 0, x_28);
lean::cnstr_set_scalar(x_32, sizeof(void*)*1, x_30);
x_33 = x_32;
if (lean::is_scalar(x_27)) {
 x_34 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_34 = x_27;
}
lean::cnstr_set(x_34, 0, x_33);
lean::cnstr_set(x_34, 1, x_25);
return x_34;
}
}
}
obj* _init_l_lean_parser_detail__ident__suffix_parser_lean_parser_has__view() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_23; obj* x_24; obj* x_25; obj* x_30; obj* x_31; 
x_0 = l_lean_parser_basic__parser__m_monad;
x_1 = l_reader__t_monad___rarg(x_0);
x_2 = l_lean_parser_basic__parser__m_monad__except;
x_3 = l_reader__t_monad__except___rarg(x_2);
x_4 = l_lean_parser_basic__parser__m_lean_parser_monad__parsec;
x_5 = l_lean_parser_rec__t_lean_parser_monad__parsec___rarg(x_0, lean::box(0), x_4);
x_6 = l_lean_parser_basic__parser__m_alternative;
x_7 = l_reader__t_alternative___rarg(x_0, x_6);
x_8 = lean::mk_string(".");
x_9 = l_string_quote(x_8);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_10, 0, x_9);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_with__trailing___rarg___lambda__1), 2, 0);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_lift___at_lean_parser_with__trailing___spec__1___rarg___boxed), 4, 1);
lean::closure_set(x_12, 0, x_11);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_lift___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__5___rarg___boxed), 5, 1);
lean::closure_set(x_13, 0, x_12);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_detail__ident__suffix_parser_lean_parser_has__view___lambda__2___boxed), 6, 1);
lean::closure_set(x_14, 0, x_10);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_bind___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__7___rarg), 6, 2);
lean::closure_set(x_15, 0, x_13);
lean::closure_set(x_15, 1, x_14);
x_16 = lean::box(0);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_rec__t_recurse___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__8), 5, 1);
lean::closure_set(x_17, 0, x_16);
x_18 = lean::box(0);
x_19 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_19, 0, x_17);
lean::cnstr_set(x_19, 1, x_18);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_15);
lean::cnstr_set(x_20, 1, x_19);
x_21 = l_lean_parser_detail__ident__suffix;
lean::inc(x_20);
x_23 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__9), 6, 2);
lean::closure_set(x_23, 0, x_21);
lean::closure_set(x_23, 1, x_20);
x_24 = l_lean_parser_detail__ident__suffix_has__view;
x_25 = l_lean_parser_combinators_node_view___rarg(x_1, x_3, x_5, x_7, x_21, x_20, x_24);
lean::dec(x_20);
lean::dec(x_5);
lean::dec(x_3);
lean::dec(x_1);
x_30 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_detail__ident__suffix_parser_lean_parser_has__view___lambda__1___boxed), 4, 0);
x_31 = l_lean_parser_combinators_seq__right_view___rarg(x_7, lean::box(0), lean::box(0), x_30, x_23, x_25);
lean::dec(x_23);
lean::dec(x_30);
lean::dec(x_7);
return x_31;
}
}
obj* l_lean_parser_parsec__t_lookahead___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__view___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_parser_parsec__t_lookahead___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__view___spec__1(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
return x_4;
}
}
obj* l_lean_parser_detail__ident__suffix_parser_lean_parser_has__view___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_parser_detail__ident__suffix_parser_lean_parser_has__view___lambda__1(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
return x_4;
}
}
obj* l_lean_parser_detail__ident__suffix_parser_lean_parser_has__view___lambda__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_lean_parser_detail__ident__suffix_parser_lean_parser_has__view___lambda__2(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_2);
lean::dec(x_3);
return x_6;
}
}
obj* l_lean_parser_parsec__t_lookahead___at_lean_parser_detail__ident__suffix_parser___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; uint32 x_7; obj* x_9; obj* x_10; 
x_7 = 46;
lean::inc(x_2);
x_9 = l_lean_parser_monad__parsec_ch___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__1(x_7, x_0, x_1, x_2, x_3);
x_10 = lean::cnstr_get(x_9, 0);
lean::inc(x_10);
if (lean::obj_tag(x_10) == 0)
{
obj* x_12; obj* x_15; obj* x_17; obj* x_19; uint32 x_20; obj* x_22; obj* x_23; 
x_12 = lean::cnstr_get(x_9, 1);
lean::inc(x_12);
lean::dec(x_9);
x_15 = lean::cnstr_get(x_10, 1);
x_17 = lean::cnstr_get(x_10, 2);
if (lean::is_exclusive(x_10)) {
 lean::cnstr_release(x_10, 0);
 lean::cnstr_set(x_10, 1, lean::box(0));
 lean::cnstr_set(x_10, 2, lean::box(0));
 x_19 = x_10;
} else {
 lean::inc(x_15);
 lean::inc(x_17);
 lean::dec(x_10);
 x_19 = lean::box(0);
}
x_20 = l_lean_id__begin__escape;
lean::inc(x_15);
x_22 = l_lean_parser_monad__parsec_ch___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__1(x_20, x_0, x_1, x_15, x_12);
x_23 = lean::cnstr_get(x_22, 0);
lean::inc(x_23);
if (lean::obj_tag(x_23) == 0)
{
obj* x_27; obj* x_30; 
lean::dec(x_15);
lean::dec(x_19);
x_27 = lean::cnstr_get(x_22, 1);
lean::inc(x_27);
lean::dec(x_22);
x_30 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_17, x_23);
x_4 = x_30;
x_5 = x_27;
goto lbl_6;
}
else
{
uint8 x_31; 
x_31 = lean::cnstr_get_scalar<uint8>(x_23, sizeof(void*)*1);
if (x_31 == 0)
{
obj* x_32; obj* x_35; uint8 x_38; 
x_32 = lean::cnstr_get(x_22, 1);
lean::inc(x_32);
lean::dec(x_22);
x_35 = lean::cnstr_get(x_23, 0);
lean::inc(x_35);
lean::dec(x_23);
x_38 = lean::string_iterator_has_next(x_15);
if (x_38 == 0)
{
obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_45; obj* x_47; obj* x_50; obj* x_51; obj* x_52; obj* x_53; 
lean::dec(x_19);
x_40 = lean::box(0);
x_41 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_42 = l_mjoin___rarg___closed__1;
x_43 = l_lean_parser_monad__parsec_error___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__3___rarg(x_41, x_42, x_40, x_40, x_0, x_1, x_15, x_32);
lean::dec(x_15);
x_45 = lean::cnstr_get(x_43, 0);
lean::inc(x_45);
x_47 = lean::cnstr_get(x_43, 1);
lean::inc(x_47);
lean::dec(x_43);
x_50 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_51 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_50, x_45);
x_52 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_35, x_51);
x_53 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_17, x_52);
x_4 = x_53;
x_5 = x_47;
goto lbl_6;
}
else
{
uint32 x_54; uint8 x_55; 
x_54 = lean::string_iterator_curr(x_15);
x_55 = l_lean_is__id__first(x_54);
if (x_55 == 0)
{
obj* x_57; obj* x_58; obj* x_59; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_66; obj* x_68; obj* x_71; obj* x_72; obj* x_73; obj* x_74; 
lean::dec(x_19);
x_57 = l_char_quote__core(x_54);
x_58 = l_char_has__repr___closed__1;
x_59 = lean::string_append(x_58, x_57);
lean::dec(x_57);
x_61 = lean::string_append(x_59, x_58);
x_62 = lean::box(0);
x_63 = l_mjoin___rarg___closed__1;
x_64 = l_lean_parser_monad__parsec_error___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__3___rarg(x_61, x_63, x_62, x_62, x_0, x_1, x_15, x_32);
lean::dec(x_15);
x_66 = lean::cnstr_get(x_64, 0);
lean::inc(x_66);
x_68 = lean::cnstr_get(x_64, 1);
lean::inc(x_68);
lean::dec(x_64);
x_71 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_72 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_71, x_66);
x_73 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_35, x_72);
x_74 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_17, x_73);
x_4 = x_74;
x_5 = x_68;
goto lbl_6;
}
else
{
obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; 
lean::dec(x_35);
x_76 = lean::string_iterator_next(x_15);
x_77 = lean::box(0);
x_78 = lean::box_uint32(x_54);
if (lean::is_scalar(x_19)) {
 x_79 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_79 = x_19;
}
lean::cnstr_set(x_79, 0, x_78);
lean::cnstr_set(x_79, 1, x_76);
lean::cnstr_set(x_79, 2, x_77);
x_80 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_17, x_79);
x_4 = x_80;
x_5 = x_32;
goto lbl_6;
}
}
}
else
{
obj* x_83; obj* x_86; 
lean::dec(x_15);
lean::dec(x_19);
x_83 = lean::cnstr_get(x_22, 1);
lean::inc(x_83);
lean::dec(x_22);
x_86 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_17, x_23);
x_4 = x_86;
x_5 = x_83;
goto lbl_6;
}
}
}
else
{
obj* x_87; obj* x_90; uint8 x_92; obj* x_93; obj* x_94; obj* x_95; 
x_87 = lean::cnstr_get(x_9, 1);
lean::inc(x_87);
lean::dec(x_9);
x_90 = lean::cnstr_get(x_10, 0);
x_92 = lean::cnstr_get_scalar<uint8>(x_10, sizeof(void*)*1);
if (lean::is_exclusive(x_10)) {
 x_93 = x_10;
} else {
 lean::inc(x_90);
 lean::dec(x_10);
 x_93 = lean::box(0);
}
if (lean::is_scalar(x_93)) {
 x_94 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_94 = x_93;
}
lean::cnstr_set(x_94, 0, x_90);
lean::cnstr_set_scalar(x_94, sizeof(void*)*1, x_92);
x_95 = x_94;
x_4 = x_95;
x_5 = x_87;
goto lbl_6;
}
lbl_6:
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_96; obj* x_98; obj* x_99; obj* x_100; obj* x_101; 
x_96 = lean::cnstr_get(x_4, 0);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 1);
 lean::cnstr_release(x_4, 2);
 x_98 = x_4;
} else {
 lean::inc(x_96);
 lean::dec(x_4);
 x_98 = lean::box(0);
}
x_99 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_98)) {
 x_100 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_100 = x_98;
}
lean::cnstr_set(x_100, 0, x_96);
lean::cnstr_set(x_100, 1, x_2);
lean::cnstr_set(x_100, 2, x_99);
x_101 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_101, 0, x_100);
lean::cnstr_set(x_101, 1, x_5);
return x_101;
}
else
{
obj* x_103; 
lean::dec(x_2);
x_103 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_103, 0, x_4);
lean::cnstr_set(x_103, 1, x_5);
return x_103;
}
}
}
}
obj* _init_l_lean_parser_detail__ident__suffix_parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_0 = lean::mk_string(".");
x_1 = l_string_quote(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_2, 0, x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_with__trailing___rarg___lambda__1), 2, 0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_lift___at_lean_parser_with__trailing___spec__1___rarg___boxed), 4, 1);
lean::closure_set(x_4, 0, x_3);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_lift___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__5___rarg___boxed), 5, 1);
lean::closure_set(x_5, 0, x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_detail__ident__suffix_parser_lean_parser_has__view___lambda__2___boxed), 6, 1);
lean::closure_set(x_6, 0, x_2);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_bind___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__7___rarg), 6, 2);
lean::closure_set(x_7, 0, x_5);
lean::closure_set(x_7, 1, x_6);
x_8 = lean::box(0);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_rec__t_recurse___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__8), 5, 1);
lean::closure_set(x_9, 0, x_8);
x_10 = lean::box(0);
x_11 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_11, 0, x_9);
lean::cnstr_set(x_11, 1, x_10);
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_7);
lean::cnstr_set(x_12, 1, x_11);
return x_12;
}
}
obj* l_lean_parser_detail__ident__suffix_parser(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_7; obj* x_9; obj* x_10; 
x_4 = l_lean_parser_parsec__t_lookahead___at_lean_parser_detail__ident__suffix_parser___spec__1(x_0, x_1, x_2, x_3);
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
x_10 = l_lean_parser_parsec__t_try__mk__res___rarg(x_5);
if (lean::obj_tag(x_10) == 0)
{
obj* x_12; obj* x_14; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_22; obj* x_24; obj* x_25; obj* x_26; 
lean::dec(x_9);
x_12 = lean::cnstr_get(x_10, 1);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_10, 2);
lean::inc(x_14);
lean::dec(x_10);
x_17 = l_lean_parser_detail__ident__suffix;
x_18 = l_lean_parser_detail__ident__suffix_parser___closed__1;
x_19 = l_lean_parser_combinators_node___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__9(x_17, x_18, x_0, x_1, x_12, x_7);
x_20 = lean::cnstr_get(x_19, 0);
x_22 = lean::cnstr_get(x_19, 1);
if (lean::is_exclusive(x_19)) {
 x_24 = x_19;
} else {
 lean::inc(x_20);
 lean::inc(x_22);
 lean::dec(x_19);
 x_24 = lean::box(0);
}
x_25 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_14, x_20);
if (lean::is_scalar(x_24)) {
 x_26 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_26 = x_24;
}
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_22);
return x_26;
}
else
{
obj* x_29; uint8 x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; 
lean::dec(x_1);
lean::dec(x_0);
x_29 = lean::cnstr_get(x_10, 0);
x_31 = lean::cnstr_get_scalar<uint8>(x_10, sizeof(void*)*1);
if (lean::is_exclusive(x_10)) {
 x_32 = x_10;
} else {
 lean::inc(x_29);
 lean::dec(x_10);
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
if (lean::is_scalar(x_9)) {
 x_35 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_35 = x_9;
}
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_7);
return x_35;
}
}
}
obj* l_lean_parser_parsec__t_lookahead___at_lean_parser_detail__ident__suffix_parser___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_parser_parsec__t_lookahead___at_lean_parser_detail__ident__suffix_parser___spec__1(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
return x_4;
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
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; 
x_0 = l_lean_parser_detail__ident__suffix_has__view;
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
obj* x_5; obj* x_6; obj* x_9; 
x_5 = l_lean_parser_detail__ident__part_has__view;
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
lean::dec(x_5);
x_9 = lean::apply_1(x_6, x_1);
if (lean::obj_tag(x_0) == 0)
{
obj* x_10; obj* x_11; 
x_10 = lean::box(3);
x_11 = l_lean_parser_syntax_as__node___main(x_10);
if (lean::obj_tag(x_11) == 0)
{
obj* x_12; obj* x_13; 
x_12 = l_lean_parser_detail__ident_has__view_x_27___lambda__1___closed__1;
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_9);
lean::cnstr_set(x_13, 1, x_12);
return x_13;
}
else
{
obj* x_14; obj* x_16; obj* x_17; 
x_14 = lean::cnstr_get(x_11, 0);
if (lean::is_exclusive(x_11)) {
 lean::cnstr_set(x_11, 0, lean::box(0));
 x_16 = x_11;
} else {
 lean::inc(x_14);
 lean::dec(x_11);
 x_16 = lean::box(0);
}
x_17 = lean::cnstr_get(x_14, 1);
lean::inc(x_17);
lean::dec(x_14);
if (lean::obj_tag(x_17) == 0)
{
obj* x_21; obj* x_22; 
lean::dec(x_16);
x_21 = lean::box(0);
x_22 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_22, 0, x_9);
lean::cnstr_set(x_22, 1, x_21);
return x_22;
}
else
{
obj* x_23; 
x_23 = lean::cnstr_get(x_17, 1);
lean::inc(x_23);
if (lean::obj_tag(x_23) == 0)
{
obj* x_25; obj* x_28; obj* x_29; obj* x_32; obj* x_33; obj* x_34; 
x_25 = lean::cnstr_get(x_17, 0);
lean::inc(x_25);
lean::dec(x_17);
x_28 = l_lean_parser_detail__ident__suffix_has__view;
x_29 = lean::cnstr_get(x_28, 0);
lean::inc(x_29);
lean::dec(x_28);
x_32 = lean::apply_1(x_29, x_25);
if (lean::is_scalar(x_16)) {
 x_33 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_33 = x_16;
}
lean::cnstr_set(x_33, 0, x_32);
x_34 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_34, 0, x_9);
lean::cnstr_set(x_34, 1, x_33);
return x_34;
}
else
{
obj* x_38; obj* x_39; 
lean::dec(x_23);
lean::dec(x_16);
lean::dec(x_17);
x_38 = l_lean_parser_detail__ident_has__view_x_27___lambda__1___closed__1;
x_39 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_39, 0, x_9);
lean::cnstr_set(x_39, 1, x_38);
return x_39;
}
}
}
}
else
{
obj* x_40; obj* x_43; 
x_40 = lean::cnstr_get(x_0, 0);
lean::inc(x_40);
lean::dec(x_0);
x_43 = l_lean_parser_syntax_as__node___main(x_40);
if (lean::obj_tag(x_43) == 0)
{
obj* x_44; obj* x_45; 
x_44 = l_lean_parser_detail__ident_has__view_x_27___lambda__1___closed__1;
x_45 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_45, 0, x_9);
lean::cnstr_set(x_45, 1, x_44);
return x_45;
}
else
{
obj* x_46; obj* x_48; obj* x_49; 
x_46 = lean::cnstr_get(x_43, 0);
if (lean::is_exclusive(x_43)) {
 lean::cnstr_set(x_43, 0, lean::box(0));
 x_48 = x_43;
} else {
 lean::inc(x_46);
 lean::dec(x_43);
 x_48 = lean::box(0);
}
x_49 = lean::cnstr_get(x_46, 1);
lean::inc(x_49);
lean::dec(x_46);
if (lean::obj_tag(x_49) == 0)
{
obj* x_53; obj* x_54; 
lean::dec(x_48);
x_53 = lean::box(0);
x_54 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_54, 0, x_9);
lean::cnstr_set(x_54, 1, x_53);
return x_54;
}
else
{
obj* x_55; 
x_55 = lean::cnstr_get(x_49, 1);
lean::inc(x_55);
if (lean::obj_tag(x_55) == 0)
{
obj* x_57; obj* x_60; obj* x_61; obj* x_64; obj* x_65; obj* x_66; 
x_57 = lean::cnstr_get(x_49, 0);
lean::inc(x_57);
lean::dec(x_49);
x_60 = l_lean_parser_detail__ident__suffix_has__view;
x_61 = lean::cnstr_get(x_60, 0);
lean::inc(x_61);
lean::dec(x_60);
x_64 = lean::apply_1(x_61, x_57);
if (lean::is_scalar(x_48)) {
 x_65 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_65 = x_48;
}
lean::cnstr_set(x_65, 0, x_64);
x_66 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_66, 0, x_9);
lean::cnstr_set(x_66, 1, x_65);
return x_66;
}
else
{
obj* x_70; obj* x_71; 
lean::dec(x_48);
lean::dec(x_49);
lean::dec(x_55);
x_70 = l_lean_parser_detail__ident_has__view_x_27___lambda__1___closed__1;
x_71 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_71, 0, x_9);
lean::cnstr_set(x_71, 1, x_70);
return x_71;
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
obj* x_5; 
x_5 = l_lean_parser_detail__ident_has__view_x_27___lambda__1___closed__2;
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
obj* x_18; obj* x_19; obj* x_22; 
x_18 = l_lean_parser_detail__ident__part_has__view;
x_19 = lean::cnstr_get(x_18, 0);
lean::inc(x_19);
lean::dec(x_18);
x_22 = lean::apply_1(x_19, x_2);
if (lean::obj_tag(x_1) == 0)
{
obj* x_23; obj* x_24; 
x_23 = lean::box(3);
x_24 = l_lean_parser_syntax_as__node___main(x_23);
if (lean::obj_tag(x_24) == 0)
{
obj* x_25; obj* x_26; 
x_25 = l_lean_parser_detail__ident_has__view_x_27___lambda__1___closed__1;
x_26 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_26, 0, x_22);
lean::cnstr_set(x_26, 1, x_25);
return x_26;
}
else
{
obj* x_27; obj* x_29; obj* x_30; 
x_27 = lean::cnstr_get(x_24, 0);
if (lean::is_exclusive(x_24)) {
 lean::cnstr_set(x_24, 0, lean::box(0));
 x_29 = x_24;
} else {
 lean::inc(x_27);
 lean::dec(x_24);
 x_29 = lean::box(0);
}
x_30 = lean::cnstr_get(x_27, 1);
lean::inc(x_30);
lean::dec(x_27);
if (lean::obj_tag(x_30) == 0)
{
obj* x_34; obj* x_35; 
lean::dec(x_29);
x_34 = lean::box(0);
x_35 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_35, 0, x_22);
lean::cnstr_set(x_35, 1, x_34);
return x_35;
}
else
{
obj* x_36; 
x_36 = lean::cnstr_get(x_30, 1);
lean::inc(x_36);
if (lean::obj_tag(x_36) == 0)
{
obj* x_38; obj* x_41; obj* x_42; obj* x_45; obj* x_46; obj* x_47; 
x_38 = lean::cnstr_get(x_30, 0);
lean::inc(x_38);
lean::dec(x_30);
x_41 = l_lean_parser_detail__ident__suffix_has__view;
x_42 = lean::cnstr_get(x_41, 0);
lean::inc(x_42);
lean::dec(x_41);
x_45 = lean::apply_1(x_42, x_38);
if (lean::is_scalar(x_29)) {
 x_46 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_46 = x_29;
}
lean::cnstr_set(x_46, 0, x_45);
x_47 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_47, 0, x_22);
lean::cnstr_set(x_47, 1, x_46);
return x_47;
}
else
{
obj* x_51; obj* x_52; 
lean::dec(x_29);
lean::dec(x_30);
lean::dec(x_36);
x_51 = l_lean_parser_detail__ident_has__view_x_27___lambda__1___closed__1;
x_52 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_52, 0, x_22);
lean::cnstr_set(x_52, 1, x_51);
return x_52;
}
}
}
}
else
{
obj* x_53; obj* x_56; 
x_53 = lean::cnstr_get(x_1, 0);
lean::inc(x_53);
lean::dec(x_1);
x_56 = l_lean_parser_syntax_as__node___main(x_53);
if (lean::obj_tag(x_56) == 0)
{
obj* x_57; obj* x_58; 
x_57 = l_lean_parser_detail__ident_has__view_x_27___lambda__1___closed__1;
x_58 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_58, 0, x_22);
lean::cnstr_set(x_58, 1, x_57);
return x_58;
}
else
{
obj* x_59; obj* x_61; obj* x_62; 
x_59 = lean::cnstr_get(x_56, 0);
if (lean::is_exclusive(x_56)) {
 lean::cnstr_set(x_56, 0, lean::box(0));
 x_61 = x_56;
} else {
 lean::inc(x_59);
 lean::dec(x_56);
 x_61 = lean::box(0);
}
x_62 = lean::cnstr_get(x_59, 1);
lean::inc(x_62);
lean::dec(x_59);
if (lean::obj_tag(x_62) == 0)
{
obj* x_66; obj* x_67; 
lean::dec(x_61);
x_66 = lean::box(0);
x_67 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_67, 0, x_22);
lean::cnstr_set(x_67, 1, x_66);
return x_67;
}
else
{
obj* x_68; 
x_68 = lean::cnstr_get(x_62, 1);
lean::inc(x_68);
if (lean::obj_tag(x_68) == 0)
{
obj* x_70; obj* x_73; obj* x_74; obj* x_77; obj* x_78; obj* x_79; 
x_70 = lean::cnstr_get(x_62, 0);
lean::inc(x_70);
lean::dec(x_62);
x_73 = l_lean_parser_detail__ident__suffix_has__view;
x_74 = lean::cnstr_get(x_73, 0);
lean::inc(x_74);
lean::dec(x_73);
x_77 = lean::apply_1(x_74, x_70);
if (lean::is_scalar(x_61)) {
 x_78 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_78 = x_61;
}
lean::cnstr_set(x_78, 0, x_77);
x_79 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_79, 0, x_22);
lean::cnstr_set(x_79, 1, x_78);
return x_79;
}
else
{
obj* x_83; obj* x_84; 
lean::dec(x_68);
lean::dec(x_62);
lean::dec(x_61);
x_83 = l_lean_parser_detail__ident_has__view_x_27___lambda__1___closed__1;
x_84 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_84, 0, x_22);
lean::cnstr_set(x_84, 1, x_83);
return x_84;
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
obj* x_0; obj* x_1; obj* x_2; obj* x_3; 
x_0 = lean::box(0);
x_1 = l_lean_parser_no__kind;
x_2 = l_lean_parser_syntax_mk__node(x_1, x_0);
x_3 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_3, 0, x_2);
lean::cnstr_set(x_3, 1, x_0);
return x_3;
}
}
obj* l_lean_parser_detail__ident_has__view_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_6; obj* x_7; obj* x_10; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
x_6 = l_lean_parser_detail__ident__part_has__view;
x_7 = lean::cnstr_get(x_6, 1);
lean::inc(x_7);
lean::dec(x_6);
x_10 = lean::apply_1(x_7, x_1);
if (lean::obj_tag(x_3) == 0)
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_11 = l_lean_parser_detail__ident_has__view_x_27___lambda__2___closed__1;
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_10);
lean::cnstr_set(x_12, 1, x_11);
x_13 = l_lean_parser_detail__ident;
x_14 = l_lean_parser_syntax_mk__node(x_13, x_12);
return x_14;
}
else
{
obj* x_15; obj* x_18; obj* x_19; obj* x_20; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_15 = lean::cnstr_get(x_3, 0);
lean::inc(x_15);
lean::dec(x_3);
x_18 = lean::box(0);
x_19 = l_lean_parser_detail__ident__suffix_has__view;
x_20 = lean::cnstr_get(x_19, 1);
lean::inc(x_20);
lean::dec(x_19);
x_23 = lean::apply_1(x_20, x_15);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_18);
x_25 = l_lean_parser_no__kind;
x_26 = l_lean_parser_syntax_mk__node(x_25, x_24);
x_27 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_18);
x_28 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_28, 0, x_10);
lean::cnstr_set(x_28, 1, x_27);
x_29 = l_lean_parser_detail__ident;
x_30 = l_lean_parser_syntax_mk__node(x_29, x_28);
return x_30;
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
return x_0;
}
}
obj* l_reader__t_lift___at_lean_parser_detail__ident_x_27___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = lean::apply_3(x_0, x_2, x_3, x_4);
return x_5;
}
}
obj* l_reader__t_lift___at_lean_parser_detail__ident_x_27___spec__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_lift___at_lean_parser_detail__ident_x_27___spec__1___rarg___boxed), 5, 0);
return x_1;
}
}
obj* l_lean_parser_combinators_optional___at_lean_parser_detail__ident_x_27___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_13; obj* x_14; 
x_8 = lean::box(0);
lean::inc(x_3);
x_13 = lean::apply_4(x_0, x_1, x_2, x_3, x_4);
x_14 = lean::cnstr_get(x_13, 0);
lean::inc(x_14);
if (lean::obj_tag(x_14) == 0)
{
if (lean::obj_tag(x_14) == 0)
{
obj* x_16; obj* x_19; obj* x_21; obj* x_23; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
x_16 = lean::cnstr_get(x_13, 1);
lean::inc(x_16);
lean::dec(x_13);
x_19 = lean::cnstr_get(x_14, 0);
x_21 = lean::cnstr_get(x_14, 1);
x_23 = lean::cnstr_get(x_14, 2);
if (lean::is_exclusive(x_14)) {
 x_25 = x_14;
} else {
 lean::inc(x_19);
 lean::inc(x_21);
 lean::inc(x_23);
 lean::dec(x_14);
 x_25 = lean::box(0);
}
x_26 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_26, 0, x_19);
x_27 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_25)) {
 x_28 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_28 = x_25;
}
lean::cnstr_set(x_28, 0, x_26);
lean::cnstr_set(x_28, 1, x_21);
lean::cnstr_set(x_28, 2, x_27);
x_29 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_23, x_28);
x_9 = x_29;
x_10 = x_16;
goto lbl_11;
}
else
{
obj* x_30; obj* x_33; uint8 x_35; obj* x_36; obj* x_37; obj* x_38; 
x_30 = lean::cnstr_get(x_13, 1);
lean::inc(x_30);
lean::dec(x_13);
x_33 = lean::cnstr_get(x_14, 0);
x_35 = lean::cnstr_get_scalar<uint8>(x_14, sizeof(void*)*1);
if (lean::is_exclusive(x_14)) {
 x_36 = x_14;
} else {
 lean::inc(x_33);
 lean::dec(x_14);
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
x_9 = x_38;
x_10 = x_30;
goto lbl_11;
}
}
else
{
obj* x_39; obj* x_42; uint8 x_44; obj* x_45; obj* x_46; obj* x_48; obj* x_50; obj* x_52; obj* x_55; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; 
x_39 = lean::cnstr_get(x_13, 1);
lean::inc(x_39);
lean::dec(x_13);
x_42 = lean::cnstr_get(x_14, 0);
x_44 = lean::cnstr_get_scalar<uint8>(x_14, sizeof(void*)*1);
if (lean::is_exclusive(x_14)) {
 lean::cnstr_set(x_14, 0, lean::box(0));
 x_45 = x_14;
} else {
 lean::inc(x_42);
 lean::dec(x_14);
 x_45 = lean::box(0);
}
x_46 = lean::cnstr_get(x_42, 0);
lean::inc(x_46);
x_48 = lean::cnstr_get(x_42, 1);
lean::inc(x_48);
x_50 = lean::cnstr_get(x_42, 2);
lean::inc(x_50);
x_52 = lean::cnstr_get(x_42, 3);
lean::inc(x_52);
lean::dec(x_42);
x_55 = l_option_get___main___at_lean_parser_run___spec__2(x_52);
lean::dec(x_52);
x_57 = lean::box(0);
x_58 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_58, 0, x_55);
lean::cnstr_set(x_58, 1, x_57);
x_59 = l_lean_parser_no__kind;
x_60 = l_lean_parser_syntax_mk__node(x_59, x_58);
x_61 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_61, 0, x_60);
x_62 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_62, 0, x_46);
lean::cnstr_set(x_62, 1, x_48);
lean::cnstr_set(x_62, 2, x_50);
lean::cnstr_set(x_62, 3, x_61);
if (x_44 == 0)
{
uint8 x_63; obj* x_64; obj* x_65; 
x_63 = 0;
if (lean::is_scalar(x_45)) {
 x_64 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_64 = x_45;
}
lean::cnstr_set(x_64, 0, x_62);
lean::cnstr_set_scalar(x_64, sizeof(void*)*1, x_63);
x_65 = x_64;
x_9 = x_65;
x_10 = x_39;
goto lbl_11;
}
else
{
obj* x_66; obj* x_67; 
if (lean::is_scalar(x_45)) {
 x_66 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_66 = x_45;
}
lean::cnstr_set(x_66, 0, x_62);
lean::cnstr_set_scalar(x_66, sizeof(void*)*1, x_44);
x_67 = x_66;
x_9 = x_67;
x_10 = x_39;
goto lbl_11;
}
}
lbl_7:
{
if (lean::obj_tag(x_5) == 0)
{
obj* x_68; 
x_68 = lean::cnstr_get(x_5, 0);
lean::inc(x_68);
if (lean::obj_tag(x_68) == 0)
{
obj* x_70; obj* x_72; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; 
x_70 = lean::cnstr_get(x_5, 1);
x_72 = lean::cnstr_get(x_5, 2);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 x_74 = x_5;
} else {
 lean::inc(x_70);
 lean::inc(x_72);
 lean::dec(x_5);
 x_74 = lean::box(0);
}
x_75 = l_lean_parser_combinators_many___rarg___closed__1;
x_76 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_74)) {
 x_77 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_77 = x_74;
}
lean::cnstr_set(x_77, 0, x_75);
lean::cnstr_set(x_77, 1, x_70);
lean::cnstr_set(x_77, 2, x_76);
x_78 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_72, x_77);
x_79 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_79, 0, x_78);
lean::cnstr_set(x_79, 1, x_6);
return x_79;
}
else
{
obj* x_80; obj* x_82; obj* x_84; obj* x_85; obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_95; 
x_80 = lean::cnstr_get(x_5, 1);
x_82 = lean::cnstr_get(x_5, 2);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 x_84 = x_5;
} else {
 lean::inc(x_80);
 lean::inc(x_82);
 lean::dec(x_5);
 x_84 = lean::box(0);
}
x_85 = lean::cnstr_get(x_68, 0);
lean::inc(x_85);
lean::dec(x_68);
x_88 = lean::box(0);
x_89 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_89, 0, x_85);
lean::cnstr_set(x_89, 1, x_88);
x_90 = l_lean_parser_no__kind;
x_91 = l_lean_parser_syntax_mk__node(x_90, x_89);
x_92 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_84)) {
 x_93 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_93 = x_84;
}
lean::cnstr_set(x_93, 0, x_91);
lean::cnstr_set(x_93, 1, x_80);
lean::cnstr_set(x_93, 2, x_92);
x_94 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_82, x_93);
x_95 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_95, 0, x_94);
lean::cnstr_set(x_95, 1, x_6);
return x_95;
}
}
else
{
obj* x_96; uint8 x_98; obj* x_99; obj* x_100; obj* x_101; obj* x_102; 
x_96 = lean::cnstr_get(x_5, 0);
x_98 = lean::cnstr_get_scalar<uint8>(x_5, sizeof(void*)*1);
if (lean::is_exclusive(x_5)) {
 x_99 = x_5;
} else {
 lean::inc(x_96);
 lean::dec(x_5);
 x_99 = lean::box(0);
}
if (lean::is_scalar(x_99)) {
 x_100 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_100 = x_99;
}
lean::cnstr_set(x_100, 0, x_96);
lean::cnstr_set_scalar(x_100, sizeof(void*)*1, x_98);
x_101 = x_100;
x_102 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_102, 0, x_101);
lean::cnstr_set(x_102, 1, x_6);
return x_102;
}
}
lbl_11:
{
if (lean::obj_tag(x_9) == 0)
{
lean::dec(x_3);
x_5 = x_9;
x_6 = x_10;
goto lbl_7;
}
else
{
uint8 x_104; 
x_104 = lean::cnstr_get_scalar<uint8>(x_9, sizeof(void*)*1);
if (x_104 == 0)
{
obj* x_105; obj* x_108; obj* x_111; obj* x_112; obj* x_113; obj* x_114; 
x_105 = lean::cnstr_get(x_9, 0);
lean::inc(x_105);
lean::dec(x_9);
x_108 = lean::cnstr_get(x_105, 2);
lean::inc(x_108);
lean::dec(x_105);
x_111 = l_mjoin___rarg___closed__1;
x_112 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_112, 0, x_108);
lean::closure_set(x_112, 1, x_111);
x_113 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_113, 0, x_112);
x_114 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_114, 0, x_8);
lean::cnstr_set(x_114, 1, x_3);
lean::cnstr_set(x_114, 2, x_113);
x_5 = x_114;
x_6 = x_10;
goto lbl_7;
}
else
{
lean::dec(x_3);
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
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_lift___at_lean_parser_detail__ident_x_27___spec__1___rarg___boxed), 5, 1);
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
obj* x_4; obj* x_5; obj* x_6; 
x_4 = l_lean_parser_detail__ident;
x_5 = l_lean_parser_detail__ident_x_27___closed__1;
x_6 = l_lean_parser_combinators_node___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__9(x_4, x_5, x_0, x_1, x_2, x_3);
return x_6;
}
}
obj* l_reader__t_lift___at_lean_parser_detail__ident_x_27___spec__1___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_reader__t_lift___at_lean_parser_detail__ident_x_27___spec__1___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
return x_5;
}
}
obj* l_reader__t_lift___at_lean_parser_detail__ident_x_27___spec__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_reader__t_lift___at_lean_parser_detail__ident_x_27___spec__1(x_0);
lean::dec(x_0);
return x_1;
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
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_rec_1__run__aux___at_lean_parser_detail__ident_parser___spec__3___boxed), 7, 3);
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
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_4 = lean::box(0);
x_5 = l_lean_parser_rec__t_run__parsec___rarg___lambda__1___closed__1;
x_6 = l_mjoin___rarg___closed__1;
x_7 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_5, x_6, x_4, x_4, x_1, x_2, x_3);
return x_7;
}
}
obj* _init_l_lean_parser_rec__t_run__parsec___at_lean_parser_detail__ident_parser___spec__1___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_rec__t_run__parsec___at_lean_parser_detail__ident_parser___spec__1___lambda__1___boxed), 4, 0);
return x_0;
}
}
obj* l_lean_parser_rec__t_run__parsec___at_lean_parser_detail__ident_parser___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; obj* x_9; obj* x_10; obj* x_11; obj* x_13; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_5 = lean::string_iterator_remaining(x_3);
x_6 = lean::mk_nat_obj(1u);
x_7 = lean::nat_add(x_5, x_6);
lean::dec(x_5);
x_9 = l_lean_parser_rec__t_run__parsec___at_lean_parser_detail__ident_parser___spec__1___closed__1;
x_10 = l_lean_parser_rec__t_run___at_lean_parser_detail__ident_parser___spec__2(x_0, x_9, x_1, x_7, x_2, x_3, x_4);
x_11 = lean::cnstr_get(x_10, 0);
x_13 = lean::cnstr_get(x_10, 1);
if (lean::is_exclusive(x_10)) {
 x_15 = x_10;
} else {
 lean::inc(x_11);
 lean::inc(x_13);
 lean::dec(x_10);
 x_15 = lean::box(0);
}
x_16 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_17 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_11);
if (lean::is_scalar(x_15)) {
 x_18 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_18 = x_15;
}
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_13);
return x_18;
}
}
obj* l_lean_parser_detail__ident_parser___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = l_lean_parser_detail__ident;
x_6 = l_lean_parser_detail__ident_x_27___closed__1;
x_7 = l_lean_parser_combinators_node___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__9(x_5, x_6, x_1, x_2, x_3, x_4);
return x_7;
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
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_detail__ident_parser___lambda__1___boxed), 5, 0);
return x_0;
}
}
obj* l_lean_parser_detail__ident_parser(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = l_lean_parser_detail__ident_parser___closed__1;
x_4 = l_lean_parser_detail__ident_parser___closed__2;
x_5 = l_lean_parser_rec__t_run__parsec___at_lean_parser_detail__ident_parser___spec__1(x_3, x_4, x_0, x_1, x_2);
return x_5;
}
}
obj* l___private_init_lean_parser_rec_1__run__aux___at_lean_parser_detail__ident_parser___spec__3___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l___private_init_lean_parser_rec_1__run__aux___at_lean_parser_detail__ident_parser___spec__3(x_0, x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_2);
return x_7;
}
}
obj* l_lean_parser_rec__t_run__parsec___at_lean_parser_detail__ident_parser___spec__1___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_parser_rec__t_run__parsec___at_lean_parser_detail__ident_parser___spec__1___lambda__1(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_4;
}
}
obj* l_lean_parser_detail__ident_parser___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_lean_parser_detail__ident_parser___lambda__1(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
return x_5;
}
}
obj* l_lean_parser_monad__parsec_curr___at___private_init_lean_parser_token_4__ident_x_27___spec__2___rarg(obj* x_0, obj* x_1) {
_start:
{
uint32 x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_2 = lean::string_iterator_curr(x_0);
x_3 = l_lean_parser_finish__comment__block___closed__2;
x_4 = lean::box_uint32(x_2);
x_5 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_0);
lean::cnstr_set(x_5, 2, x_3);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_1);
return x_6;
}
}
obj* l_lean_parser_monad__parsec_curr___at___private_init_lean_parser_token_4__ident_x_27___spec__2(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_curr___at___private_init_lean_parser_token_4__ident_x_27___spec__2___rarg), 2, 0);
return x_1;
}
}
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__5(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = lean::string_iterator_has_next(x_2);
if (x_5 == 0)
{
obj* x_7; 
lean::dec(x_0);
x_7 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_7;
}
else
{
uint32 x_8; uint8 x_9; 
x_8 = lean::string_iterator_curr(x_2);
x_9 = l_lean_is__id__rest(x_8);
if (x_9 == 0)
{
obj* x_11; 
lean::dec(x_0);
x_11 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_11;
}
else
{
obj* x_12; obj* x_13; obj* x_15; obj* x_16; 
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_sub(x_0, x_12);
lean::dec(x_0);
x_15 = lean::string_push(x_1, x_8);
x_16 = lean::string_iterator_next(x_2);
x_0 = x_13;
x_1 = x_15;
x_2 = x_16;
goto _start;
}
}
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
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_init_lean_parser_token_4__ident_x_27___spec__4(uint32 x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_4 = l_string_join___closed__1;
x_5 = lean::string_push(x_4, x_0);
x_6 = lean::string_iterator_remaining(x_2);
x_7 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__5(x_6, x_5, x_2);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_3);
return x_8;
}
}
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__7(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = lean::string_iterator_has_next(x_2);
if (x_5 == 0)
{
obj* x_7; 
lean::dec(x_0);
x_7 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_7;
}
else
{
uint32 x_8; uint8 x_9; 
x_8 = lean::string_iterator_curr(x_2);
x_9 = l_lean_is__id__rest(x_8);
if (x_9 == 0)
{
obj* x_11; 
lean::dec(x_0);
x_11 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_11;
}
else
{
obj* x_12; obj* x_13; obj* x_15; obj* x_16; 
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_sub(x_0, x_12);
lean::dec(x_0);
x_15 = lean::string_push(x_1, x_8);
x_16 = lean::string_iterator_next(x_2);
x_0 = x_13;
x_1 = x_15;
x_2 = x_16;
goto _start;
}
}
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
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_init_lean_parser_token_4__ident_x_27___spec__6(uint32 x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_4 = l_string_join___closed__1;
x_5 = lean::string_push(x_4, x_0);
x_6 = lean::string_iterator_remaining(x_2);
x_7 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__7(x_6, x_5, x_2);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_3);
return x_8;
}
}
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__9(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = lean::string_iterator_has_next(x_2);
if (x_5 == 0)
{
obj* x_7; 
lean::dec(x_0);
x_7 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_7;
}
else
{
uint32 x_8; uint8 x_9; 
x_8 = lean::string_iterator_curr(x_2);
x_9 = l_lean_is__id__rest(x_8);
if (x_9 == 0)
{
obj* x_11; 
lean::dec(x_0);
x_11 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_11;
}
else
{
obj* x_12; obj* x_13; obj* x_15; obj* x_16; 
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_sub(x_0, x_12);
lean::dec(x_0);
x_15 = lean::string_push(x_1, x_8);
x_16 = lean::string_iterator_next(x_2);
x_0 = x_13;
x_1 = x_15;
x_2 = x_16;
goto _start;
}
}
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
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_init_lean_parser_token_4__ident_x_27___spec__8(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint32 x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_4 = lean::string_iterator_curr(x_0);
x_5 = l_string_join___closed__1;
x_6 = lean::string_push(x_5, x_4);
x_7 = lean::string_iterator_remaining(x_2);
x_8 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__9(x_7, x_6, x_2);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_3);
return x_9;
}
}
obj* l_lean_parser_id__part__default___at___private_init_lean_parser_token_4__ident_x_27___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = lean::string_iterator_has_next(x_1);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_14; obj* x_15; 
x_4 = lean::box(0);
x_5 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_6 = l_mjoin___rarg___closed__1;
x_7 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_5, x_6, x_4, x_4, x_0, x_1, x_2);
lean::dec(x_1);
x_9 = lean::cnstr_get(x_7, 0);
x_11 = lean::cnstr_get(x_7, 1);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_set(x_7, 0, lean::box(0));
 lean::cnstr_set(x_7, 1, lean::box(0));
 x_13 = x_7;
} else {
 lean::inc(x_9);
 lean::inc(x_11);
 lean::dec(x_7);
 x_13 = lean::box(0);
}
x_14 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_15 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_14, x_9);
if (lean::obj_tag(x_15) == 0)
{
obj* x_17; obj* x_19; obj* x_21; uint32 x_24; obj* x_25; obj* x_26; obj* x_28; obj* x_30; obj* x_31; obj* x_32; 
lean::dec(x_13);
x_17 = lean::cnstr_get(x_15, 0);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_15, 1);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_15, 2);
lean::inc(x_21);
lean::dec(x_15);
x_24 = lean::unbox_uint32(x_17);
x_25 = l_lean_parser_monad__parsec_take__while__cont___at___private_init_lean_parser_token_4__ident_x_27___spec__4(x_24, x_0, x_19, x_11);
x_26 = lean::cnstr_get(x_25, 0);
x_28 = lean::cnstr_get(x_25, 1);
if (lean::is_exclusive(x_25)) {
 x_30 = x_25;
} else {
 lean::inc(x_26);
 lean::inc(x_28);
 lean::dec(x_25);
 x_30 = lean::box(0);
}
x_31 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_21, x_26);
if (lean::is_scalar(x_30)) {
 x_32 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_32 = x_30;
}
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_28);
return x_32;
}
else
{
obj* x_33; uint8 x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; 
x_33 = lean::cnstr_get(x_15, 0);
x_35 = lean::cnstr_get_scalar<uint8>(x_15, sizeof(void*)*1);
if (lean::is_exclusive(x_15)) {
 x_36 = x_15;
} else {
 lean::inc(x_33);
 lean::dec(x_15);
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
if (lean::is_scalar(x_13)) {
 x_39 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_39 = x_13;
}
lean::cnstr_set(x_39, 0, x_38);
lean::cnstr_set(x_39, 1, x_11);
return x_39;
}
}
else
{
uint32 x_40; uint8 x_41; 
x_40 = lean::string_iterator_curr(x_1);
x_41 = l_lean_is__id__first(x_40);
if (x_41 == 0)
{
obj* x_42; obj* x_43; obj* x_44; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_51; obj* x_53; obj* x_55; obj* x_56; obj* x_57; 
x_42 = l_char_quote__core(x_40);
x_43 = l_char_has__repr___closed__1;
x_44 = lean::string_append(x_43, x_42);
lean::dec(x_42);
x_46 = lean::string_append(x_44, x_43);
x_47 = lean::box(0);
x_48 = l_mjoin___rarg___closed__1;
x_49 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_46, x_48, x_47, x_47, x_0, x_1, x_2);
lean::dec(x_1);
x_51 = lean::cnstr_get(x_49, 0);
x_53 = lean::cnstr_get(x_49, 1);
if (lean::is_exclusive(x_49)) {
 lean::cnstr_set(x_49, 0, lean::box(0));
 lean::cnstr_set(x_49, 1, lean::box(0));
 x_55 = x_49;
} else {
 lean::inc(x_51);
 lean::inc(x_53);
 lean::dec(x_49);
 x_55 = lean::box(0);
}
x_56 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_57 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_56, x_51);
if (lean::obj_tag(x_57) == 0)
{
obj* x_59; obj* x_61; obj* x_63; uint32 x_66; obj* x_67; obj* x_68; obj* x_70; obj* x_72; obj* x_73; obj* x_74; 
lean::dec(x_55);
x_59 = lean::cnstr_get(x_57, 0);
lean::inc(x_59);
x_61 = lean::cnstr_get(x_57, 1);
lean::inc(x_61);
x_63 = lean::cnstr_get(x_57, 2);
lean::inc(x_63);
lean::dec(x_57);
x_66 = lean::unbox_uint32(x_59);
x_67 = l_lean_parser_monad__parsec_take__while__cont___at___private_init_lean_parser_token_4__ident_x_27___spec__6(x_66, x_0, x_61, x_53);
x_68 = lean::cnstr_get(x_67, 0);
x_70 = lean::cnstr_get(x_67, 1);
if (lean::is_exclusive(x_67)) {
 x_72 = x_67;
} else {
 lean::inc(x_68);
 lean::inc(x_70);
 lean::dec(x_67);
 x_72 = lean::box(0);
}
x_73 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_63, x_68);
if (lean::is_scalar(x_72)) {
 x_74 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_74 = x_72;
}
lean::cnstr_set(x_74, 0, x_73);
lean::cnstr_set(x_74, 1, x_70);
return x_74;
}
else
{
obj* x_75; uint8 x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; 
x_75 = lean::cnstr_get(x_57, 0);
x_77 = lean::cnstr_get_scalar<uint8>(x_57, sizeof(void*)*1);
if (lean::is_exclusive(x_57)) {
 x_78 = x_57;
} else {
 lean::inc(x_75);
 lean::dec(x_57);
 x_78 = lean::box(0);
}
if (lean::is_scalar(x_78)) {
 x_79 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_79 = x_78;
}
lean::cnstr_set(x_79, 0, x_75);
lean::cnstr_set_scalar(x_79, sizeof(void*)*1, x_77);
x_80 = x_79;
if (lean::is_scalar(x_55)) {
 x_81 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_81 = x_55;
}
lean::cnstr_set(x_81, 0, x_80);
lean::cnstr_set(x_81, 1, x_53);
return x_81;
}
}
else
{
obj* x_83; obj* x_84; obj* x_86; obj* x_88; obj* x_90; obj* x_91; obj* x_92; obj* x_93; 
lean::inc(x_1);
x_83 = lean::string_iterator_next(x_1);
x_84 = l_lean_parser_monad__parsec_take__while__cont___at___private_init_lean_parser_token_4__ident_x_27___spec__8(x_1, x_0, x_83, x_2);
lean::dec(x_1);
x_86 = lean::cnstr_get(x_84, 0);
x_88 = lean::cnstr_get(x_84, 1);
if (lean::is_exclusive(x_84)) {
 x_90 = x_84;
} else {
 lean::inc(x_86);
 lean::inc(x_88);
 lean::dec(x_84);
 x_90 = lean::box(0);
}
x_91 = lean::box(0);
x_92 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_91, x_86);
if (lean::is_scalar(x_90)) {
 x_93 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_93 = x_90;
}
lean::cnstr_set(x_93, 0, x_92);
lean::cnstr_set(x_93, 1, x_88);
return x_93;
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
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_5 = lean::box(0);
x_6 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_7 = l_mjoin___rarg___closed__1;
x_8 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_6, x_7, x_5, x_5, x_1, x_2, x_3);
lean::dec(x_2);
x_10 = lean::cnstr_get(x_8, 0);
x_12 = lean::cnstr_get(x_8, 1);
if (lean::is_exclusive(x_8)) {
 x_14 = x_8;
} else {
 lean::inc(x_10);
 lean::inc(x_12);
 lean::dec(x_8);
 x_14 = lean::box(0);
}
x_15 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_16 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_10);
if (lean::is_scalar(x_14)) {
 x_17 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_17 = x_14;
}
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_12);
return x_17;
}
else
{
uint32 x_18; uint8 x_19; 
x_18 = lean::string_iterator_curr(x_2);
x_19 = x_18 == x_0;
if (x_19 == 0)
{
obj* x_20; obj* x_21; obj* x_22; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_29; obj* x_31; obj* x_33; obj* x_34; obj* x_35; obj* x_36; 
x_20 = l_char_quote__core(x_18);
x_21 = l_char_has__repr___closed__1;
x_22 = lean::string_append(x_21, x_20);
lean::dec(x_20);
x_24 = lean::string_append(x_22, x_21);
x_25 = lean::box(0);
x_26 = l_mjoin___rarg___closed__1;
x_27 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_24, x_26, x_25, x_25, x_1, x_2, x_3);
lean::dec(x_2);
x_29 = lean::cnstr_get(x_27, 0);
x_31 = lean::cnstr_get(x_27, 1);
if (lean::is_exclusive(x_27)) {
 x_33 = x_27;
} else {
 lean::inc(x_29);
 lean::inc(x_31);
 lean::dec(x_27);
 x_33 = lean::box(0);
}
x_34 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_35 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_34, x_29);
if (lean::is_scalar(x_33)) {
 x_36 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_36 = x_33;
}
lean::cnstr_set(x_36, 0, x_35);
lean::cnstr_set(x_36, 1, x_31);
return x_36;
}
else
{
obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; 
x_37 = lean::string_iterator_next(x_2);
x_38 = lean::box(0);
x_39 = lean::box_uint32(x_18);
x_40 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_40, 0, x_39);
lean::cnstr_set(x_40, 1, x_37);
lean::cnstr_set(x_40, 2, x_38);
x_41 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_41, 0, x_40);
lean::cnstr_set(x_41, 1, x_3);
return x_41;
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
if (x_4 == 0)
{
uint8 x_5; 
x_5 = lean::string_iterator_has_next(x_2);
if (x_5 == 0)
{
obj* x_7; 
lean::dec(x_0);
x_7 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_7;
}
else
{
uint32 x_8; uint8 x_9; 
x_8 = lean::string_iterator_curr(x_2);
x_9 = l_lean_is__id__end__escape(x_8);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_13; obj* x_14; 
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_sub(x_0, x_10);
lean::dec(x_0);
x_13 = lean::string_push(x_1, x_8);
x_14 = lean::string_iterator_next(x_2);
x_0 = x_11;
x_1 = x_13;
x_2 = x_14;
goto _start;
}
else
{
obj* x_17; 
lean::dec(x_0);
x_17 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_17;
}
}
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
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_init_lean_parser_token_4__ident_x_27___spec__13(uint32 x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_4 = l_string_join___closed__1;
x_5 = lean::string_push(x_4, x_0);
x_6 = lean::string_iterator_remaining(x_2);
x_7 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__14(x_6, x_5, x_2);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_3);
return x_8;
}
}
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__16(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = lean::string_iterator_has_next(x_2);
if (x_5 == 0)
{
obj* x_7; 
lean::dec(x_0);
x_7 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_7;
}
else
{
uint32 x_8; uint8 x_9; 
x_8 = lean::string_iterator_curr(x_2);
x_9 = l_lean_is__id__end__escape(x_8);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_13; obj* x_14; 
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_sub(x_0, x_10);
lean::dec(x_0);
x_13 = lean::string_push(x_1, x_8);
x_14 = lean::string_iterator_next(x_2);
x_0 = x_11;
x_1 = x_13;
x_2 = x_14;
goto _start;
}
else
{
obj* x_17; 
lean::dec(x_0);
x_17 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_17;
}
}
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
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_init_lean_parser_token_4__ident_x_27___spec__15(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint32 x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_4 = lean::string_iterator_curr(x_0);
x_5 = l_string_join___closed__1;
x_6 = lean::string_push(x_5, x_4);
x_7 = lean::string_iterator_remaining(x_2);
x_8 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__16(x_7, x_6, x_2);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_3);
return x_9;
}
}
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__18(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = lean::string_iterator_has_next(x_2);
if (x_5 == 0)
{
obj* x_7; 
lean::dec(x_0);
x_7 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_7;
}
else
{
uint32 x_8; uint8 x_9; 
x_8 = lean::string_iterator_curr(x_2);
x_9 = l_lean_is__id__end__escape(x_8);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_13; obj* x_14; 
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_sub(x_0, x_10);
lean::dec(x_0);
x_13 = lean::string_push(x_1, x_8);
x_14 = lean::string_iterator_next(x_2);
x_0 = x_11;
x_1 = x_13;
x_2 = x_14;
goto _start;
}
else
{
obj* x_17; 
lean::dec(x_0);
x_17 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_17;
}
}
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
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_init_lean_parser_token_4__ident_x_27___spec__17(uint32 x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_4 = l_string_join___closed__1;
x_5 = lean::string_push(x_4, x_0);
x_6 = lean::string_iterator_remaining(x_2);
x_7 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__18(x_6, x_5, x_2);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_3);
return x_8;
}
}
obj* l_lean_parser_monad__parsec_take__while1___at___private_init_lean_parser_token_4__ident_x_27___spec__12(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = lean::string_iterator_has_next(x_1);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_14; obj* x_15; 
x_4 = lean::box(0);
x_5 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_6 = l_mjoin___rarg___closed__1;
x_7 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_5, x_6, x_4, x_4, x_0, x_1, x_2);
lean::dec(x_1);
x_9 = lean::cnstr_get(x_7, 0);
x_11 = lean::cnstr_get(x_7, 1);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_set(x_7, 0, lean::box(0));
 lean::cnstr_set(x_7, 1, lean::box(0));
 x_13 = x_7;
} else {
 lean::inc(x_9);
 lean::inc(x_11);
 lean::dec(x_7);
 x_13 = lean::box(0);
}
x_14 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_15 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_14, x_9);
if (lean::obj_tag(x_15) == 0)
{
obj* x_17; obj* x_19; obj* x_21; uint32 x_24; obj* x_25; obj* x_26; obj* x_28; obj* x_30; obj* x_31; obj* x_32; 
lean::dec(x_13);
x_17 = lean::cnstr_get(x_15, 0);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_15, 1);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_15, 2);
lean::inc(x_21);
lean::dec(x_15);
x_24 = lean::unbox_uint32(x_17);
x_25 = l_lean_parser_monad__parsec_take__while__cont___at___private_init_lean_parser_token_4__ident_x_27___spec__13(x_24, x_0, x_19, x_11);
x_26 = lean::cnstr_get(x_25, 0);
x_28 = lean::cnstr_get(x_25, 1);
if (lean::is_exclusive(x_25)) {
 x_30 = x_25;
} else {
 lean::inc(x_26);
 lean::inc(x_28);
 lean::dec(x_25);
 x_30 = lean::box(0);
}
x_31 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_21, x_26);
if (lean::is_scalar(x_30)) {
 x_32 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_32 = x_30;
}
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_28);
return x_32;
}
else
{
obj* x_33; uint8 x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; 
x_33 = lean::cnstr_get(x_15, 0);
x_35 = lean::cnstr_get_scalar<uint8>(x_15, sizeof(void*)*1);
if (lean::is_exclusive(x_15)) {
 x_36 = x_15;
} else {
 lean::inc(x_33);
 lean::dec(x_15);
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
if (lean::is_scalar(x_13)) {
 x_39 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_39 = x_13;
}
lean::cnstr_set(x_39, 0, x_38);
lean::cnstr_set(x_39, 1, x_11);
return x_39;
}
}
else
{
uint32 x_40; uint8 x_41; 
x_40 = lean::string_iterator_curr(x_1);
x_41 = l_lean_is__id__end__escape(x_40);
if (x_41 == 0)
{
obj* x_43; obj* x_44; obj* x_46; obj* x_48; obj* x_50; obj* x_51; obj* x_52; obj* x_53; 
lean::inc(x_1);
x_43 = lean::string_iterator_next(x_1);
x_44 = l_lean_parser_monad__parsec_take__while__cont___at___private_init_lean_parser_token_4__ident_x_27___spec__15(x_1, x_0, x_43, x_2);
lean::dec(x_1);
x_46 = lean::cnstr_get(x_44, 0);
x_48 = lean::cnstr_get(x_44, 1);
if (lean::is_exclusive(x_44)) {
 x_50 = x_44;
} else {
 lean::inc(x_46);
 lean::inc(x_48);
 lean::dec(x_44);
 x_50 = lean::box(0);
}
x_51 = lean::box(0);
x_52 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_51, x_46);
if (lean::is_scalar(x_50)) {
 x_53 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_53 = x_50;
}
lean::cnstr_set(x_53, 0, x_52);
lean::cnstr_set(x_53, 1, x_48);
return x_53;
}
else
{
obj* x_54; obj* x_55; obj* x_56; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_63; obj* x_65; obj* x_67; obj* x_68; obj* x_69; 
x_54 = l_char_quote__core(x_40);
x_55 = l_char_has__repr___closed__1;
x_56 = lean::string_append(x_55, x_54);
lean::dec(x_54);
x_58 = lean::string_append(x_56, x_55);
x_59 = lean::box(0);
x_60 = l_mjoin___rarg___closed__1;
x_61 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_58, x_60, x_59, x_59, x_0, x_1, x_2);
lean::dec(x_1);
x_63 = lean::cnstr_get(x_61, 0);
x_65 = lean::cnstr_get(x_61, 1);
if (lean::is_exclusive(x_61)) {
 lean::cnstr_set(x_61, 0, lean::box(0));
 lean::cnstr_set(x_61, 1, lean::box(0));
 x_67 = x_61;
} else {
 lean::inc(x_63);
 lean::inc(x_65);
 lean::dec(x_61);
 x_67 = lean::box(0);
}
x_68 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_69 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_68, x_63);
if (lean::obj_tag(x_69) == 0)
{
obj* x_71; obj* x_73; obj* x_75; uint32 x_78; obj* x_79; obj* x_80; obj* x_82; obj* x_84; obj* x_85; obj* x_86; 
lean::dec(x_67);
x_71 = lean::cnstr_get(x_69, 0);
lean::inc(x_71);
x_73 = lean::cnstr_get(x_69, 1);
lean::inc(x_73);
x_75 = lean::cnstr_get(x_69, 2);
lean::inc(x_75);
lean::dec(x_69);
x_78 = lean::unbox_uint32(x_71);
x_79 = l_lean_parser_monad__parsec_take__while__cont___at___private_init_lean_parser_token_4__ident_x_27___spec__17(x_78, x_0, x_73, x_65);
x_80 = lean::cnstr_get(x_79, 0);
x_82 = lean::cnstr_get(x_79, 1);
if (lean::is_exclusive(x_79)) {
 x_84 = x_79;
} else {
 lean::inc(x_80);
 lean::inc(x_82);
 lean::dec(x_79);
 x_84 = lean::box(0);
}
x_85 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_75, x_80);
if (lean::is_scalar(x_84)) {
 x_86 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_86 = x_84;
}
lean::cnstr_set(x_86, 0, x_85);
lean::cnstr_set(x_86, 1, x_82);
return x_86;
}
else
{
obj* x_87; uint8 x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; 
x_87 = lean::cnstr_get(x_69, 0);
x_89 = lean::cnstr_get_scalar<uint8>(x_69, sizeof(void*)*1);
if (lean::is_exclusive(x_69)) {
 x_90 = x_69;
} else {
 lean::inc(x_87);
 lean::dec(x_69);
 x_90 = lean::box(0);
}
if (lean::is_scalar(x_90)) {
 x_91 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_91 = x_90;
}
lean::cnstr_set(x_91, 0, x_87);
lean::cnstr_set_scalar(x_91, sizeof(void*)*1, x_89);
x_92 = x_91;
if (lean::is_scalar(x_67)) {
 x_93 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_93 = x_67;
}
lean::cnstr_set(x_93, 0, x_92);
lean::cnstr_set(x_93, 1, x_65);
return x_93;
}
}
}
}
}
obj* l_lean_parser_id__part__escaped___at___private_init_lean_parser_token_4__ident_x_27___spec__10(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint32 x_3; obj* x_4; obj* x_5; 
x_3 = l_lean_id__begin__escape;
x_4 = l_lean_parser_monad__parsec_ch___at___private_init_lean_parser_token_4__ident_x_27___spec__11(x_3, x_0, x_1, x_2);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
if (lean::obj_tag(x_5) == 0)
{
obj* x_7; obj* x_10; obj* x_12; obj* x_15; obj* x_16; obj* x_18; obj* x_20; obj* x_21; 
x_7 = lean::cnstr_get(x_4, 1);
lean::inc(x_7);
lean::dec(x_4);
x_10 = lean::cnstr_get(x_5, 1);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_5, 2);
lean::inc(x_12);
lean::dec(x_5);
x_15 = l_lean_parser_monad__parsec_take__while1___at___private_init_lean_parser_token_4__ident_x_27___spec__12(x_0, x_10, x_7);
x_16 = lean::cnstr_get(x_15, 0);
x_18 = lean::cnstr_get(x_15, 1);
if (lean::is_exclusive(x_15)) {
 lean::cnstr_set(x_15, 0, lean::box(0));
 lean::cnstr_set(x_15, 1, lean::box(0));
 x_20 = x_15;
} else {
 lean::inc(x_16);
 lean::inc(x_18);
 lean::dec(x_15);
 x_20 = lean::box(0);
}
x_21 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_12, x_16);
if (lean::obj_tag(x_21) == 0)
{
obj* x_23; obj* x_25; obj* x_27; uint32 x_30; obj* x_31; obj* x_32; 
lean::dec(x_20);
x_23 = lean::cnstr_get(x_21, 0);
lean::inc(x_23);
x_25 = lean::cnstr_get(x_21, 1);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_21, 2);
lean::inc(x_27);
lean::dec(x_21);
x_30 = l_lean_id__end__escape;
x_31 = l_lean_parser_monad__parsec_ch___at___private_init_lean_parser_token_4__ident_x_27___spec__11(x_30, x_0, x_25, x_18);
x_32 = lean::cnstr_get(x_31, 0);
lean::inc(x_32);
if (lean::obj_tag(x_32) == 0)
{
obj* x_34; obj* x_36; obj* x_37; obj* x_39; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; 
x_34 = lean::cnstr_get(x_31, 1);
if (lean::is_exclusive(x_31)) {
 lean::cnstr_release(x_31, 0);
 x_36 = x_31;
} else {
 lean::inc(x_34);
 lean::dec(x_31);
 x_36 = lean::box(0);
}
x_37 = lean::cnstr_get(x_32, 1);
x_39 = lean::cnstr_get(x_32, 2);
if (lean::is_exclusive(x_32)) {
 lean::cnstr_release(x_32, 0);
 x_41 = x_32;
} else {
 lean::inc(x_37);
 lean::inc(x_39);
 lean::dec(x_32);
 x_41 = lean::box(0);
}
x_42 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_41)) {
 x_43 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_43 = x_41;
}
lean::cnstr_set(x_43, 0, x_23);
lean::cnstr_set(x_43, 1, x_37);
lean::cnstr_set(x_43, 2, x_42);
x_44 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_39, x_43);
x_45 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_27, x_44);
if (lean::is_scalar(x_36)) {
 x_46 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_46 = x_36;
}
lean::cnstr_set(x_46, 0, x_45);
lean::cnstr_set(x_46, 1, x_34);
return x_46;
}
else
{
obj* x_48; obj* x_50; obj* x_51; uint8 x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; 
lean::dec(x_23);
x_48 = lean::cnstr_get(x_31, 1);
if (lean::is_exclusive(x_31)) {
 lean::cnstr_release(x_31, 0);
 x_50 = x_31;
} else {
 lean::inc(x_48);
 lean::dec(x_31);
 x_50 = lean::box(0);
}
x_51 = lean::cnstr_get(x_32, 0);
x_53 = lean::cnstr_get_scalar<uint8>(x_32, sizeof(void*)*1);
if (lean::is_exclusive(x_32)) {
 x_54 = x_32;
} else {
 lean::inc(x_51);
 lean::dec(x_32);
 x_54 = lean::box(0);
}
if (lean::is_scalar(x_54)) {
 x_55 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_55 = x_54;
}
lean::cnstr_set(x_55, 0, x_51);
lean::cnstr_set_scalar(x_55, sizeof(void*)*1, x_53);
x_56 = x_55;
x_57 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_27, x_56);
if (lean::is_scalar(x_50)) {
 x_58 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_58 = x_50;
}
lean::cnstr_set(x_58, 0, x_57);
lean::cnstr_set(x_58, 1, x_48);
return x_58;
}
}
else
{
obj* x_59; uint8 x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; 
x_59 = lean::cnstr_get(x_21, 0);
x_61 = lean::cnstr_get_scalar<uint8>(x_21, sizeof(void*)*1);
if (lean::is_exclusive(x_21)) {
 x_62 = x_21;
} else {
 lean::inc(x_59);
 lean::dec(x_21);
 x_62 = lean::box(0);
}
if (lean::is_scalar(x_62)) {
 x_63 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_63 = x_62;
}
lean::cnstr_set(x_63, 0, x_59);
lean::cnstr_set_scalar(x_63, sizeof(void*)*1, x_61);
x_64 = x_63;
if (lean::is_scalar(x_20)) {
 x_65 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_65 = x_20;
}
lean::cnstr_set(x_65, 0, x_64);
lean::cnstr_set(x_65, 1, x_18);
return x_65;
}
}
else
{
obj* x_66; obj* x_68; obj* x_69; uint8 x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; 
x_66 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_68 = x_4;
} else {
 lean::inc(x_66);
 lean::dec(x_4);
 x_68 = lean::box(0);
}
x_69 = lean::cnstr_get(x_5, 0);
x_71 = lean::cnstr_get_scalar<uint8>(x_5, sizeof(void*)*1);
if (lean::is_exclusive(x_5)) {
 x_72 = x_5;
} else {
 lean::inc(x_69);
 lean::dec(x_5);
 x_72 = lean::box(0);
}
if (lean::is_scalar(x_72)) {
 x_73 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_73 = x_72;
}
lean::cnstr_set(x_73, 0, x_69);
lean::cnstr_set_scalar(x_73, sizeof(void*)*1, x_71);
x_74 = x_73;
if (lean::is_scalar(x_68)) {
 x_75 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_75 = x_68;
}
lean::cnstr_set(x_75, 0, x_74);
lean::cnstr_set(x_75, 1, x_66);
return x_75;
}
}
}
obj* l_lean_parser_id__part___at___private_init_lean_parser_token_4__ident_x_27___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = l_lean_parser_monad__parsec_curr___at___private_init_lean_parser_token_4__ident_x_27___spec__2___rarg(x_1, x_2);
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; obj* x_8; obj* x_9; obj* x_11; obj* x_13; obj* x_15; uint32 x_16; uint8 x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_6 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_set(x_3, 1, lean::box(0));
 x_8 = x_3;
} else {
 lean::inc(x_6);
 lean::dec(x_3);
 x_8 = lean::box(0);
}
x_9 = lean::cnstr_get(x_4, 0);
x_11 = lean::cnstr_get(x_4, 1);
x_13 = lean::cnstr_get(x_4, 2);
if (lean::is_exclusive(x_4)) {
 x_15 = x_4;
} else {
 lean::inc(x_9);
 lean::inc(x_11);
 lean::inc(x_13);
 lean::dec(x_4);
 x_15 = lean::box(0);
}
x_16 = lean::unbox_uint32(x_9);
x_17 = l_lean_is__id__begin__escape(x_16);
x_18 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_19 = lean::box(x_17);
if (lean::is_scalar(x_15)) {
 x_20 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_20 = x_15;
}
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_11);
lean::cnstr_set(x_20, 2, x_18);
x_21 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_13, x_20);
if (lean::obj_tag(x_21) == 0)
{
obj* x_23; uint8 x_25; 
lean::dec(x_8);
x_23 = lean::cnstr_get(x_21, 0);
lean::inc(x_23);
x_25 = lean::unbox(x_23);
if (x_25 == 0)
{
obj* x_26; obj* x_28; obj* x_31; obj* x_32; obj* x_34; obj* x_36; obj* x_37; obj* x_38; 
x_26 = lean::cnstr_get(x_21, 1);
lean::inc(x_26);
x_28 = lean::cnstr_get(x_21, 2);
lean::inc(x_28);
lean::dec(x_21);
x_31 = l_lean_parser_id__part__default___at___private_init_lean_parser_token_4__ident_x_27___spec__3(x_0, x_26, x_6);
x_32 = lean::cnstr_get(x_31, 0);
x_34 = lean::cnstr_get(x_31, 1);
if (lean::is_exclusive(x_31)) {
 x_36 = x_31;
} else {
 lean::inc(x_32);
 lean::inc(x_34);
 lean::dec(x_31);
 x_36 = lean::box(0);
}
x_37 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_28, x_32);
if (lean::is_scalar(x_36)) {
 x_38 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_38 = x_36;
}
lean::cnstr_set(x_38, 0, x_37);
lean::cnstr_set(x_38, 1, x_34);
return x_38;
}
else
{
obj* x_39; obj* x_41; obj* x_44; obj* x_45; obj* x_47; obj* x_49; obj* x_50; obj* x_51; 
x_39 = lean::cnstr_get(x_21, 1);
lean::inc(x_39);
x_41 = lean::cnstr_get(x_21, 2);
lean::inc(x_41);
lean::dec(x_21);
x_44 = l_lean_parser_id__part__escaped___at___private_init_lean_parser_token_4__ident_x_27___spec__10(x_0, x_39, x_6);
x_45 = lean::cnstr_get(x_44, 0);
x_47 = lean::cnstr_get(x_44, 1);
if (lean::is_exclusive(x_44)) {
 x_49 = x_44;
} else {
 lean::inc(x_45);
 lean::inc(x_47);
 lean::dec(x_44);
 x_49 = lean::box(0);
}
x_50 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_41, x_45);
if (lean::is_scalar(x_49)) {
 x_51 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_51 = x_49;
}
lean::cnstr_set(x_51, 0, x_50);
lean::cnstr_set(x_51, 1, x_47);
return x_51;
}
}
else
{
obj* x_52; uint8 x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; 
x_52 = lean::cnstr_get(x_21, 0);
x_54 = lean::cnstr_get_scalar<uint8>(x_21, sizeof(void*)*1);
if (lean::is_exclusive(x_21)) {
 x_55 = x_21;
} else {
 lean::inc(x_52);
 lean::dec(x_21);
 x_55 = lean::box(0);
}
if (lean::is_scalar(x_55)) {
 x_56 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_56 = x_55;
}
lean::cnstr_set(x_56, 0, x_52);
lean::cnstr_set_scalar(x_56, sizeof(void*)*1, x_54);
x_57 = x_56;
if (lean::is_scalar(x_8)) {
 x_58 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_58 = x_8;
}
lean::cnstr_set(x_58, 0, x_57);
lean::cnstr_set(x_58, 1, x_6);
return x_58;
}
}
else
{
obj* x_59; obj* x_61; obj* x_62; uint8 x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; 
x_59 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 x_61 = x_3;
} else {
 lean::inc(x_59);
 lean::dec(x_3);
 x_61 = lean::box(0);
}
x_62 = lean::cnstr_get(x_4, 0);
x_64 = lean::cnstr_get_scalar<uint8>(x_4, sizeof(void*)*1);
if (lean::is_exclusive(x_4)) {
 x_65 = x_4;
} else {
 lean::inc(x_62);
 lean::dec(x_4);
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
if (lean::is_scalar(x_61)) {
 x_68 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_68 = x_61;
}
lean::cnstr_set(x_68, 0, x_67);
lean::cnstr_set(x_68, 1, x_59);
return x_68;
}
}
}
obj* l_lean_parser_parsec__t_lookahead___at___private_init_lean_parser_token_4__ident_x_27___spec__19(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; uint32 x_6; obj* x_8; obj* x_9; 
x_6 = 46;
lean::inc(x_1);
x_8 = l_lean_parser_monad__parsec_ch___at___private_init_lean_parser_token_4__ident_x_27___spec__11(x_6, x_0, x_1, x_2);
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
if (lean::obj_tag(x_9) == 0)
{
obj* x_11; obj* x_14; obj* x_16; obj* x_18; uint32 x_19; obj* x_21; obj* x_22; 
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
lean::dec(x_8);
x_14 = lean::cnstr_get(x_9, 1);
x_16 = lean::cnstr_get(x_9, 2);
if (lean::is_exclusive(x_9)) {
 lean::cnstr_release(x_9, 0);
 lean::cnstr_set(x_9, 1, lean::box(0));
 lean::cnstr_set(x_9, 2, lean::box(0));
 x_18 = x_9;
} else {
 lean::inc(x_14);
 lean::inc(x_16);
 lean::dec(x_9);
 x_18 = lean::box(0);
}
x_19 = l_lean_id__begin__escape;
lean::inc(x_14);
x_21 = l_lean_parser_monad__parsec_ch___at___private_init_lean_parser_token_4__ident_x_27___spec__11(x_19, x_0, x_14, x_11);
x_22 = lean::cnstr_get(x_21, 0);
lean::inc(x_22);
if (lean::obj_tag(x_22) == 0)
{
obj* x_26; obj* x_29; 
lean::dec(x_18);
lean::dec(x_14);
x_26 = lean::cnstr_get(x_21, 1);
lean::inc(x_26);
lean::dec(x_21);
x_29 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_22);
x_3 = x_29;
x_4 = x_26;
goto lbl_5;
}
else
{
uint8 x_30; 
x_30 = lean::cnstr_get_scalar<uint8>(x_22, sizeof(void*)*1);
if (x_30 == 0)
{
obj* x_31; obj* x_34; uint8 x_37; 
x_31 = lean::cnstr_get(x_21, 1);
lean::inc(x_31);
lean::dec(x_21);
x_34 = lean::cnstr_get(x_22, 0);
lean::inc(x_34);
lean::dec(x_22);
x_37 = lean::string_iterator_has_next(x_14);
if (x_37 == 0)
{
obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_44; obj* x_46; obj* x_49; obj* x_50; obj* x_51; obj* x_52; 
lean::dec(x_18);
x_39 = lean::box(0);
x_40 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_41 = l_mjoin___rarg___closed__1;
x_42 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_40, x_41, x_39, x_39, x_0, x_14, x_31);
lean::dec(x_14);
x_44 = lean::cnstr_get(x_42, 0);
lean::inc(x_44);
x_46 = lean::cnstr_get(x_42, 1);
lean::inc(x_46);
lean::dec(x_42);
x_49 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_50 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_49, x_44);
x_51 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_34, x_50);
x_52 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_51);
x_3 = x_52;
x_4 = x_46;
goto lbl_5;
}
else
{
uint32 x_53; uint8 x_54; 
x_53 = lean::string_iterator_curr(x_14);
x_54 = l_lean_is__id__first(x_53);
if (x_54 == 0)
{
obj* x_56; obj* x_57; obj* x_58; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_65; obj* x_67; obj* x_70; obj* x_71; obj* x_72; obj* x_73; 
lean::dec(x_18);
x_56 = l_char_quote__core(x_53);
x_57 = l_char_has__repr___closed__1;
x_58 = lean::string_append(x_57, x_56);
lean::dec(x_56);
x_60 = lean::string_append(x_58, x_57);
x_61 = lean::box(0);
x_62 = l_mjoin___rarg___closed__1;
x_63 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_60, x_62, x_61, x_61, x_0, x_14, x_31);
lean::dec(x_14);
x_65 = lean::cnstr_get(x_63, 0);
lean::inc(x_65);
x_67 = lean::cnstr_get(x_63, 1);
lean::inc(x_67);
lean::dec(x_63);
x_70 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_71 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_70, x_65);
x_72 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_34, x_71);
x_73 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_72);
x_3 = x_73;
x_4 = x_67;
goto lbl_5;
}
else
{
obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; 
lean::dec(x_34);
x_75 = lean::string_iterator_next(x_14);
x_76 = lean::box(0);
x_77 = lean::box_uint32(x_53);
if (lean::is_scalar(x_18)) {
 x_78 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_78 = x_18;
}
lean::cnstr_set(x_78, 0, x_77);
lean::cnstr_set(x_78, 1, x_75);
lean::cnstr_set(x_78, 2, x_76);
x_79 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_78);
x_3 = x_79;
x_4 = x_31;
goto lbl_5;
}
}
}
else
{
obj* x_82; obj* x_85; 
lean::dec(x_18);
lean::dec(x_14);
x_82 = lean::cnstr_get(x_21, 1);
lean::inc(x_82);
lean::dec(x_21);
x_85 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_22);
x_3 = x_85;
x_4 = x_82;
goto lbl_5;
}
}
}
else
{
obj* x_86; obj* x_89; uint8 x_91; obj* x_92; obj* x_93; obj* x_94; 
x_86 = lean::cnstr_get(x_8, 1);
lean::inc(x_86);
lean::dec(x_8);
x_89 = lean::cnstr_get(x_9, 0);
x_91 = lean::cnstr_get_scalar<uint8>(x_9, sizeof(void*)*1);
if (lean::is_exclusive(x_9)) {
 x_92 = x_9;
} else {
 lean::inc(x_89);
 lean::dec(x_9);
 x_92 = lean::box(0);
}
if (lean::is_scalar(x_92)) {
 x_93 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_93 = x_92;
}
lean::cnstr_set(x_93, 0, x_89);
lean::cnstr_set_scalar(x_93, sizeof(void*)*1, x_91);
x_94 = x_93;
x_3 = x_94;
x_4 = x_86;
goto lbl_5;
}
lbl_5:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_95; obj* x_97; obj* x_98; obj* x_99; obj* x_100; 
x_95 = lean::cnstr_get(x_3, 0);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 1);
 lean::cnstr_release(x_3, 2);
 x_97 = x_3;
} else {
 lean::inc(x_95);
 lean::dec(x_3);
 x_97 = lean::box(0);
}
x_98 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_97)) {
 x_99 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_99 = x_97;
}
lean::cnstr_set(x_99, 0, x_95);
lean::cnstr_set(x_99, 1, x_1);
lean::cnstr_set(x_99, 2, x_98);
x_100 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_100, 0, x_99);
lean::cnstr_set(x_100, 1, x_4);
return x_100;
}
else
{
obj* x_102; 
lean::dec(x_1);
x_102 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_102, 0, x_3);
lean::cnstr_set(x_102, 1, x_4);
return x_102;
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
x_6 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 x_8 = x_3;
} else {
 lean::inc(x_4);
 lean::inc(x_6);
 lean::dec(x_3);
 x_8 = lean::box(0);
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
obj* l_lean_parser_monad__parsec_foldl__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__21___lambda__2(uint32 x_0, uint32 x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; 
x_5 = l_lean_parser_monad__parsec_ch___at___private_init_lean_parser_token_4__ident_x_27___spec__11(x_0, x_2, x_3, x_4);
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
if (lean::obj_tag(x_6) == 0)
{
obj* x_8; obj* x_11; obj* x_13; obj* x_16; obj* x_17; obj* x_19; obj* x_21; obj* x_22; obj* x_23; 
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
lean::dec(x_5);
x_11 = lean::cnstr_get(x_6, 1);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_6, 2);
lean::inc(x_13);
lean::dec(x_6);
x_16 = l_lean_parser_id__part___at___private_init_lean_parser_token_4__ident_x_27___spec__1(x_2, x_11, x_8);
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
x_22 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_13, x_17);
if (lean::is_scalar(x_21)) {
 x_23 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_23 = x_21;
}
lean::cnstr_set(x_23, 0, x_22);
lean::cnstr_set(x_23, 1, x_19);
return x_23;
}
else
{
obj* x_24; obj* x_26; obj* x_27; uint8 x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; 
x_24 = lean::cnstr_get(x_5, 1);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 x_26 = x_5;
} else {
 lean::inc(x_24);
 lean::dec(x_5);
 x_26 = lean::box(0);
}
x_27 = lean::cnstr_get(x_6, 0);
x_29 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*1);
if (lean::is_exclusive(x_6)) {
 x_30 = x_6;
} else {
 lean::inc(x_27);
 lean::dec(x_6);
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
obj* _init_l_lean_parser_monad__parsec_foldl__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__21___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_foldl__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__21___lambda__1___boxed), 3, 0);
return x_0;
}
}
obj* _init_l_lean_parser_monad__parsec_foldl__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__21___closed__2() {
_start:
{
uint32 x_0; obj* x_1; obj* x_2; 
x_0 = 46;
x_1 = lean::box_uint32(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_foldl__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__21___lambda__2___boxed), 5, 1);
lean::closure_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_lean_parser_monad__parsec_foldl__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__21(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::mk_nat_obj(0u);
x_6 = lean::nat_dec_eq(x_1, x_5);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_11; obj* x_12; 
x_7 = l_lean_parser_monad__parsec_foldl__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__21___closed__1;
x_8 = l_lean_parser_monad__parsec_foldl__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__21___closed__2;
lean::inc(x_3);
lean::inc(x_2);
x_11 = l_reader__t_bind___at_lean_parser_with__trailing___spec__2___rarg(x_7, x_8, x_2, x_3, x_4);
x_12 = lean::cnstr_get(x_11, 0);
lean::inc(x_12);
if (lean::obj_tag(x_12) == 0)
{
obj* x_14; obj* x_17; obj* x_19; obj* x_21; obj* x_23; obj* x_24; obj* x_25; obj* x_27; obj* x_28; obj* x_30; obj* x_32; obj* x_34; obj* x_35; 
x_14 = lean::cnstr_get(x_11, 1);
lean::inc(x_14);
lean::dec(x_11);
x_17 = lean::cnstr_get(x_12, 0);
x_19 = lean::cnstr_get(x_12, 1);
x_21 = lean::cnstr_get(x_12, 2);
if (lean::is_exclusive(x_12)) {
 lean::cnstr_set(x_12, 0, lean::box(0));
 lean::cnstr_set(x_12, 1, lean::box(0));
 lean::cnstr_set(x_12, 2, lean::box(0));
 x_23 = x_12;
} else {
 lean::inc(x_17);
 lean::inc(x_19);
 lean::inc(x_21);
 lean::dec(x_12);
 x_23 = lean::box(0);
}
x_24 = lean::mk_nat_obj(1u);
x_25 = lean::nat_sub(x_1, x_24);
lean::inc(x_0);
x_27 = lean_name_mk_string(x_0, x_17);
x_28 = l_lean_parser_monad__parsec_foldl__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__21(x_27, x_25, x_2, x_19, x_14);
lean::dec(x_25);
x_30 = lean::cnstr_get(x_28, 0);
x_32 = lean::cnstr_get(x_28, 1);
if (lean::is_exclusive(x_28)) {
 lean::cnstr_set(x_28, 0, lean::box(0));
 lean::cnstr_set(x_28, 1, lean::box(0));
 x_34 = x_28;
} else {
 lean::inc(x_30);
 lean::inc(x_32);
 lean::dec(x_28);
 x_34 = lean::box(0);
}
x_35 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_21, x_30);
if (lean::obj_tag(x_35) == 0)
{
obj* x_39; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_23);
if (lean::is_scalar(x_34)) {
 x_39 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_39 = x_34;
}
lean::cnstr_set(x_39, 0, x_35);
lean::cnstr_set(x_39, 1, x_32);
return x_39;
}
else
{
uint8 x_40; 
x_40 = lean::cnstr_get_scalar<uint8>(x_35, sizeof(void*)*1);
if (x_40 == 0)
{
obj* x_41; obj* x_44; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; 
x_41 = lean::cnstr_get(x_35, 0);
lean::inc(x_41);
lean::dec(x_35);
x_44 = lean::cnstr_get(x_41, 2);
lean::inc(x_44);
lean::dec(x_41);
x_47 = l_mjoin___rarg___closed__1;
x_48 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_48, 0, x_44);
lean::closure_set(x_48, 1, x_47);
x_49 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_49, 0, x_48);
if (lean::is_scalar(x_23)) {
 x_50 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_50 = x_23;
}
lean::cnstr_set(x_50, 0, x_0);
lean::cnstr_set(x_50, 1, x_3);
lean::cnstr_set(x_50, 2, x_49);
if (lean::is_scalar(x_34)) {
 x_51 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_51 = x_34;
}
lean::cnstr_set(x_51, 0, x_50);
lean::cnstr_set(x_51, 1, x_32);
return x_51;
}
else
{
obj* x_55; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_23);
if (lean::is_scalar(x_34)) {
 x_55 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_55 = x_34;
}
lean::cnstr_set(x_55, 0, x_35);
lean::cnstr_set(x_55, 1, x_32);
return x_55;
}
}
}
else
{
uint8 x_57; 
lean::dec(x_2);
x_57 = lean::cnstr_get_scalar<uint8>(x_12, sizeof(void*)*1);
if (x_57 == 0)
{
obj* x_58; obj* x_60; obj* x_61; obj* x_64; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; 
x_58 = lean::cnstr_get(x_11, 1);
if (lean::is_exclusive(x_11)) {
 lean::cnstr_release(x_11, 0);
 x_60 = x_11;
} else {
 lean::inc(x_58);
 lean::dec(x_11);
 x_60 = lean::box(0);
}
x_61 = lean::cnstr_get(x_12, 0);
lean::inc(x_61);
lean::dec(x_12);
x_64 = lean::cnstr_get(x_61, 2);
lean::inc(x_64);
lean::dec(x_61);
x_67 = l_mjoin___rarg___closed__1;
x_68 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_68, 0, x_64);
lean::closure_set(x_68, 1, x_67);
x_69 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_69, 0, x_68);
x_70 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_70, 0, x_0);
lean::cnstr_set(x_70, 1, x_3);
lean::cnstr_set(x_70, 2, x_69);
if (lean::is_scalar(x_60)) {
 x_71 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_71 = x_60;
}
lean::cnstr_set(x_71, 0, x_70);
lean::cnstr_set(x_71, 1, x_58);
return x_71;
}
else
{
obj* x_74; obj* x_76; obj* x_77; obj* x_79; obj* x_80; obj* x_81; obj* x_82; 
lean::dec(x_3);
lean::dec(x_0);
x_74 = lean::cnstr_get(x_11, 1);
if (lean::is_exclusive(x_11)) {
 lean::cnstr_release(x_11, 0);
 x_76 = x_11;
} else {
 lean::inc(x_74);
 lean::dec(x_11);
 x_76 = lean::box(0);
}
x_77 = lean::cnstr_get(x_12, 0);
if (lean::is_exclusive(x_12)) {
 x_79 = x_12;
} else {
 lean::inc(x_77);
 lean::dec(x_12);
 x_79 = lean::box(0);
}
if (lean::is_scalar(x_79)) {
 x_80 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_80 = x_79;
}
lean::cnstr_set(x_80, 0, x_77);
lean::cnstr_set_scalar(x_80, sizeof(void*)*1, x_57);
x_81 = x_80;
if (lean::is_scalar(x_76)) {
 x_82 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_82 = x_76;
}
lean::cnstr_set(x_82, 0, x_81);
lean::cnstr_set(x_82, 1, x_74);
return x_82;
}
}
}
else
{
obj* x_84; obj* x_85; obj* x_86; 
lean::dec(x_2);
x_84 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_85 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_85, 0, x_0);
lean::cnstr_set(x_85, 1, x_3);
lean::cnstr_set(x_85, 2, x_84);
x_86 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_86, 0, x_85);
lean::cnstr_set(x_86, 1, x_4);
return x_86;
}
}
}
obj* l_lean_parser_monad__parsec_foldl___at___private_init_lean_parser_token_4__ident_x_27___spec__20(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_4 = lean::box(0);
x_5 = lean_name_mk_string(x_4, x_0);
x_6 = lean::string_iterator_remaining(x_2);
x_7 = l_lean_parser_monad__parsec_foldl__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__21(x_5, x_6, x_1, x_2, x_3);
lean::dec(x_6);
x_9 = lean::cnstr_get(x_7, 0);
x_11 = lean::cnstr_get(x_7, 1);
if (lean::is_exclusive(x_7)) {
 x_13 = x_7;
} else {
 lean::inc(x_9);
 lean::inc(x_11);
 lean::dec(x_7);
 x_13 = lean::box(0);
}
x_14 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_15 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_14, x_9);
if (lean::is_scalar(x_13)) {
 x_16 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_16 = x_13;
}
lean::cnstr_set(x_16, 0, x_15);
lean::cnstr_set(x_16, 1, x_11);
return x_16;
}
}
obj* l___private_init_lean_parser_token_4__ident_x_27(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_5; 
lean::inc(x_1);
x_4 = l_lean_parser_id__part___at___private_init_lean_parser_token_4__ident_x_27___spec__1(x_0, x_1, x_2);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
if (lean::obj_tag(x_5) == 0)
{
obj* x_7; obj* x_10; obj* x_12; obj* x_14; obj* x_17; obj* x_18; 
x_7 = lean::cnstr_get(x_4, 1);
lean::inc(x_7);
lean::dec(x_4);
x_10 = lean::cnstr_get(x_5, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_5, 1);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_5, 2);
lean::inc(x_14);
lean::dec(x_5);
x_17 = l_lean_parser_monad__parsec_foldl___at___private_init_lean_parser_token_4__ident_x_27___spec__20(x_10, x_0, x_12, x_7);
x_18 = lean::cnstr_get(x_17, 0);
lean::inc(x_18);
if (lean::obj_tag(x_18) == 0)
{
obj* x_20; obj* x_22; obj* x_23; obj* x_25; obj* x_27; obj* x_29; obj* x_32; obj* x_33; obj* x_36; obj* x_37; obj* x_38; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; 
x_20 = lean::cnstr_get(x_17, 1);
if (lean::is_exclusive(x_17)) {
 lean::cnstr_release(x_17, 0);
 x_22 = x_17;
} else {
 lean::inc(x_20);
 lean::dec(x_17);
 x_22 = lean::box(0);
}
x_23 = lean::cnstr_get(x_18, 0);
x_25 = lean::cnstr_get(x_18, 1);
x_27 = lean::cnstr_get(x_18, 2);
if (lean::is_exclusive(x_18)) {
 x_29 = x_18;
} else {
 lean::inc(x_23);
 lean::inc(x_25);
 lean::inc(x_27);
 lean::dec(x_18);
 x_29 = lean::box(0);
}
lean::inc(x_1);
lean::inc(x_1);
x_32 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_32, 0, x_1);
lean::cnstr_set(x_32, 1, x_1);
x_33 = lean::string_iterator_offset(x_1);
lean::inc(x_25);
lean::inc(x_25);
x_36 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_36, 0, x_25);
lean::cnstr_set(x_36, 1, x_25);
x_37 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_37, 0, x_32);
lean::cnstr_set(x_37, 1, x_33);
lean::cnstr_set(x_37, 2, x_36);
x_38 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_38, 0, x_37);
lean::inc(x_25);
x_40 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_40, 0, x_1);
lean::cnstr_set(x_40, 1, x_25);
x_41 = lean::box(0);
x_42 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_42, 0, x_38);
lean::cnstr_set(x_42, 1, x_40);
lean::cnstr_set(x_42, 2, x_23);
lean::cnstr_set(x_42, 3, x_41);
lean::cnstr_set(x_42, 4, x_41);
x_43 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_43, 0, x_42);
x_44 = l_lean_parser_finish__comment__block___closed__2;
if (lean::is_scalar(x_29)) {
 x_45 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_45 = x_29;
}
lean::cnstr_set(x_45, 0, x_43);
lean::cnstr_set(x_45, 1, x_25);
lean::cnstr_set(x_45, 2, x_44);
x_46 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_27, x_45);
x_47 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_14, x_46);
x_48 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_49 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_48, x_47);
if (lean::is_scalar(x_22)) {
 x_50 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_50 = x_22;
}
lean::cnstr_set(x_50, 0, x_49);
lean::cnstr_set(x_50, 1, x_20);
return x_50;
}
else
{
obj* x_52; obj* x_54; obj* x_55; uint8 x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; 
lean::dec(x_1);
x_52 = lean::cnstr_get(x_17, 1);
if (lean::is_exclusive(x_17)) {
 lean::cnstr_release(x_17, 0);
 x_54 = x_17;
} else {
 lean::inc(x_52);
 lean::dec(x_17);
 x_54 = lean::box(0);
}
x_55 = lean::cnstr_get(x_18, 0);
x_57 = lean::cnstr_get_scalar<uint8>(x_18, sizeof(void*)*1);
if (lean::is_exclusive(x_18)) {
 x_58 = x_18;
} else {
 lean::inc(x_55);
 lean::dec(x_18);
 x_58 = lean::box(0);
}
if (lean::is_scalar(x_58)) {
 x_59 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_59 = x_58;
}
lean::cnstr_set(x_59, 0, x_55);
lean::cnstr_set_scalar(x_59, sizeof(void*)*1, x_57);
x_60 = x_59;
x_61 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_14, x_60);
x_62 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_63 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_62, x_61);
if (lean::is_scalar(x_54)) {
 x_64 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_64 = x_54;
}
lean::cnstr_set(x_64, 0, x_63);
lean::cnstr_set(x_64, 1, x_52);
return x_64;
}
}
else
{
obj* x_67; obj* x_69; obj* x_70; uint8 x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; 
lean::dec(x_1);
lean::dec(x_0);
x_67 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_69 = x_4;
} else {
 lean::inc(x_67);
 lean::dec(x_4);
 x_69 = lean::box(0);
}
x_70 = lean::cnstr_get(x_5, 0);
x_72 = lean::cnstr_get_scalar<uint8>(x_5, sizeof(void*)*1);
if (lean::is_exclusive(x_5)) {
 x_73 = x_5;
} else {
 lean::inc(x_70);
 lean::dec(x_5);
 x_73 = lean::box(0);
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
x_77 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_76, x_75);
if (lean::is_scalar(x_69)) {
 x_78 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_78 = x_69;
}
lean::cnstr_set(x_78, 0, x_77);
lean::cnstr_set(x_78, 1, x_67);
return x_78;
}
}
}
obj* l_lean_parser_monad__parsec_curr___at___private_init_lean_parser_token_4__ident_x_27___spec__2___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_monad__parsec_curr___at___private_init_lean_parser_token_4__ident_x_27___spec__2(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_init_lean_parser_token_4__ident_x_27___spec__4___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint32 x_4; obj* x_5; 
x_4 = lean::unbox_uint32(x_0);
x_5 = l_lean_parser_monad__parsec_take__while__cont___at___private_init_lean_parser_token_4__ident_x_27___spec__4(x_4, x_1, x_2, x_3);
lean::dec(x_1);
return x_5;
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_init_lean_parser_token_4__ident_x_27___spec__6___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint32 x_4; obj* x_5; 
x_4 = lean::unbox_uint32(x_0);
x_5 = l_lean_parser_monad__parsec_take__while__cont___at___private_init_lean_parser_token_4__ident_x_27___spec__6(x_4, x_1, x_2, x_3);
lean::dec(x_1);
return x_5;
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_init_lean_parser_token_4__ident_x_27___spec__8___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_parser_monad__parsec_take__while__cont___at___private_init_lean_parser_token_4__ident_x_27___spec__8(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
return x_4;
}
}
obj* l_lean_parser_id__part__default___at___private_init_lean_parser_token_4__ident_x_27___spec__3___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_parser_id__part__default___at___private_init_lean_parser_token_4__ident_x_27___spec__3(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_lean_parser_monad__parsec_ch___at___private_init_lean_parser_token_4__ident_x_27___spec__11___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint32 x_4; obj* x_5; 
x_4 = lean::unbox_uint32(x_0);
x_5 = l_lean_parser_monad__parsec_ch___at___private_init_lean_parser_token_4__ident_x_27___spec__11(x_4, x_1, x_2, x_3);
lean::dec(x_1);
return x_5;
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_init_lean_parser_token_4__ident_x_27___spec__13___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint32 x_4; obj* x_5; 
x_4 = lean::unbox_uint32(x_0);
x_5 = l_lean_parser_monad__parsec_take__while__cont___at___private_init_lean_parser_token_4__ident_x_27___spec__13(x_4, x_1, x_2, x_3);
lean::dec(x_1);
return x_5;
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_init_lean_parser_token_4__ident_x_27___spec__15___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_parser_monad__parsec_take__while__cont___at___private_init_lean_parser_token_4__ident_x_27___spec__15(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
return x_4;
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_init_lean_parser_token_4__ident_x_27___spec__17___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint32 x_4; obj* x_5; 
x_4 = lean::unbox_uint32(x_0);
x_5 = l_lean_parser_monad__parsec_take__while__cont___at___private_init_lean_parser_token_4__ident_x_27___spec__17(x_4, x_1, x_2, x_3);
lean::dec(x_1);
return x_5;
}
}
obj* l_lean_parser_monad__parsec_take__while1___at___private_init_lean_parser_token_4__ident_x_27___spec__12___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_parser_monad__parsec_take__while1___at___private_init_lean_parser_token_4__ident_x_27___spec__12(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_lean_parser_id__part__escaped___at___private_init_lean_parser_token_4__ident_x_27___spec__10___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_parser_id__part__escaped___at___private_init_lean_parser_token_4__ident_x_27___spec__10(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_lean_parser_id__part___at___private_init_lean_parser_token_4__ident_x_27___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_parser_id__part___at___private_init_lean_parser_token_4__ident_x_27___spec__1(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_lean_parser_parsec__t_lookahead___at___private_init_lean_parser_token_4__ident_x_27___spec__19___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_parser_parsec__t_lookahead___at___private_init_lean_parser_token_4__ident_x_27___spec__19(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_lean_parser_monad__parsec_foldl__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__21___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_parser_monad__parsec_foldl__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__21___lambda__1(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_lean_parser_monad__parsec_foldl__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__21___lambda__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint32 x_5; uint32 x_6; obj* x_7; 
x_5 = lean::unbox_uint32(x_0);
x_6 = lean::unbox_uint32(x_1);
x_7 = l_lean_parser_monad__parsec_foldl__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__21___lambda__2(x_5, x_6, x_2, x_3, x_4);
lean::dec(x_2);
return x_7;
}
}
obj* l_lean_parser_monad__parsec_foldl__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__21___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_lean_parser_monad__parsec_foldl__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__21(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
return x_5;
}
}
obj* l_reader__t_orelse___at_lean_parser_parse__bin__lit___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_7; obj* x_8; 
lean::inc(x_3);
lean::inc(x_2);
x_7 = lean::apply_3(x_0, x_2, x_3, x_4);
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
if (lean::obj_tag(x_8) == 0)
{
obj* x_13; obj* x_15; obj* x_16; 
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_2);
x_13 = lean::cnstr_get(x_7, 1);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 x_15 = x_7;
} else {
 lean::inc(x_13);
 lean::dec(x_7);
 x_15 = lean::box(0);
}
if (lean::is_scalar(x_15)) {
 x_16 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_16 = x_15;
}
lean::cnstr_set(x_16, 0, x_8);
lean::cnstr_set(x_16, 1, x_13);
return x_16;
}
else
{
uint8 x_17; 
x_17 = lean::cnstr_get_scalar<uint8>(x_8, sizeof(void*)*1);
if (x_17 == 0)
{
obj* x_18; obj* x_21; obj* x_24; obj* x_25; obj* x_27; obj* x_29; obj* x_30; obj* x_31; 
x_18 = lean::cnstr_get(x_7, 1);
lean::inc(x_18);
lean::dec(x_7);
x_21 = lean::cnstr_get(x_8, 0);
lean::inc(x_21);
lean::dec(x_8);
x_24 = lean::apply_3(x_1, x_2, x_3, x_18);
x_25 = lean::cnstr_get(x_24, 0);
x_27 = lean::cnstr_get(x_24, 1);
if (lean::is_exclusive(x_24)) {
 x_29 = x_24;
} else {
 lean::inc(x_25);
 lean::inc(x_27);
 lean::dec(x_24);
 x_29 = lean::box(0);
}
x_30 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_21, x_25);
if (lean::is_scalar(x_29)) {
 x_31 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_31 = x_29;
}
lean::cnstr_set(x_31, 0, x_30);
lean::cnstr_set(x_31, 1, x_27);
return x_31;
}
else
{
obj* x_35; obj* x_37; obj* x_38; 
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_2);
x_35 = lean::cnstr_get(x_7, 1);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 x_37 = x_7;
} else {
 lean::inc(x_35);
 lean::dec(x_7);
 x_37 = lean::box(0);
}
if (lean::is_scalar(x_37)) {
 x_38 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_38 = x_37;
}
lean::cnstr_set(x_38, 0, x_8);
lean::cnstr_set(x_38, 1, x_35);
return x_38;
}
}
}
}
obj* l_reader__t_orelse___at_lean_parser_parse__bin__lit___spec__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_orelse___at_lean_parser_parse__bin__lit___spec__1___rarg), 5, 0);
return x_1;
}
}
obj* _init_l_lean_parser_monad__parsec_many1__aux_x_27___main___at_lean_parser_parse__bin__lit___spec__2___closed__1() {
_start:
{
uint32 x_0; obj* x_1; obj* x_2; 
x_0 = 48;
x_1 = lean::box_uint32(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_ch___at___private_init_lean_parser_token_4__ident_x_27___spec__11___boxed), 4, 1);
lean::closure_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_lean_parser_monad__parsec_many1__aux_x_27___main___at_lean_parser_parse__bin__lit___spec__2___closed__2() {
_start:
{
uint32 x_0; obj* x_1; obj* x_2; 
x_0 = 49;
x_1 = lean::box_uint32(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_ch___at___private_init_lean_parser_token_4__ident_x_27___spec__11___boxed), 4, 1);
lean::closure_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_lean_parser_monad__parsec_many1__aux_x_27___main___at_lean_parser_parse__bin__lit___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::nat_dec_eq(x_0, x_4);
if (x_5 == 0)
{
obj* x_6; obj* x_7; obj* x_9; obj* x_10; 
x_6 = l_lean_parser_monad__parsec_many1__aux_x_27___main___at_lean_parser_parse__bin__lit___spec__2___closed__1;
x_7 = l_lean_parser_monad__parsec_many1__aux_x_27___main___at_lean_parser_parse__bin__lit___spec__2___closed__2;
lean::inc(x_1);
x_9 = l_reader__t_orelse___at_lean_parser_parse__bin__lit___spec__1___rarg(x_6, x_7, x_1, x_2, x_3);
x_10 = lean::cnstr_get(x_9, 0);
lean::inc(x_10);
if (lean::obj_tag(x_10) == 0)
{
obj* x_12; obj* x_15; obj* x_17; obj* x_19; obj* x_20; obj* x_21; obj* x_23; obj* x_25; 
x_12 = lean::cnstr_get(x_9, 1);
lean::inc(x_12);
lean::dec(x_9);
x_15 = lean::cnstr_get(x_10, 1);
x_17 = lean::cnstr_get(x_10, 2);
if (lean::is_exclusive(x_10)) {
 lean::cnstr_release(x_10, 0);
 lean::cnstr_set(x_10, 1, lean::box(0));
 lean::cnstr_set(x_10, 2, lean::box(0));
 x_19 = x_10;
} else {
 lean::inc(x_15);
 lean::inc(x_17);
 lean::dec(x_10);
 x_19 = lean::box(0);
}
x_20 = lean::mk_nat_obj(1u);
x_21 = lean::nat_sub(x_0, x_20);
lean::inc(x_15);
x_23 = l_lean_parser_monad__parsec_many1__aux_x_27___main___at_lean_parser_parse__bin__lit___spec__2(x_21, x_1, x_15, x_12);
lean::dec(x_21);
x_25 = lean::cnstr_get(x_23, 0);
lean::inc(x_25);
if (lean::obj_tag(x_25) == 0)
{
obj* x_29; obj* x_31; obj* x_32; obj* x_33; 
lean::dec(x_19);
lean::dec(x_15);
x_29 = lean::cnstr_get(x_23, 1);
if (lean::is_exclusive(x_23)) {
 lean::cnstr_release(x_23, 0);
 x_31 = x_23;
} else {
 lean::inc(x_29);
 lean::dec(x_23);
 x_31 = lean::box(0);
}
x_32 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_17, x_25);
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
uint8 x_34; 
x_34 = lean::cnstr_get_scalar<uint8>(x_25, sizeof(void*)*1);
if (x_34 == 0)
{
obj* x_35; obj* x_37; obj* x_38; obj* x_41; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; 
x_35 = lean::cnstr_get(x_23, 1);
if (lean::is_exclusive(x_23)) {
 lean::cnstr_release(x_23, 0);
 x_37 = x_23;
} else {
 lean::inc(x_35);
 lean::dec(x_23);
 x_37 = lean::box(0);
}
x_38 = lean::cnstr_get(x_25, 0);
lean::inc(x_38);
lean::dec(x_25);
x_41 = lean::cnstr_get(x_38, 2);
lean::inc(x_41);
lean::dec(x_38);
x_44 = l_mjoin___rarg___closed__1;
x_45 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_45, 0, x_41);
lean::closure_set(x_45, 1, x_44);
x_46 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_46, 0, x_45);
x_47 = lean::box(0);
if (lean::is_scalar(x_19)) {
 x_48 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_48 = x_19;
}
lean::cnstr_set(x_48, 0, x_47);
lean::cnstr_set(x_48, 1, x_15);
lean::cnstr_set(x_48, 2, x_46);
x_49 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_17, x_48);
if (lean::is_scalar(x_37)) {
 x_50 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_50 = x_37;
}
lean::cnstr_set(x_50, 0, x_49);
lean::cnstr_set(x_50, 1, x_35);
return x_50;
}
else
{
obj* x_53; obj* x_55; obj* x_56; obj* x_57; 
lean::dec(x_19);
lean::dec(x_15);
x_53 = lean::cnstr_get(x_23, 1);
if (lean::is_exclusive(x_23)) {
 lean::cnstr_release(x_23, 0);
 x_55 = x_23;
} else {
 lean::inc(x_53);
 lean::dec(x_23);
 x_55 = lean::box(0);
}
x_56 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_17, x_25);
if (lean::is_scalar(x_55)) {
 x_57 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_57 = x_55;
}
lean::cnstr_set(x_57, 0, x_56);
lean::cnstr_set(x_57, 1, x_53);
return x_57;
}
}
}
else
{
obj* x_59; obj* x_61; obj* x_62; uint8 x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; 
lean::dec(x_1);
x_59 = lean::cnstr_get(x_9, 1);
if (lean::is_exclusive(x_9)) {
 lean::cnstr_release(x_9, 0);
 x_61 = x_9;
} else {
 lean::inc(x_59);
 lean::dec(x_9);
 x_61 = lean::box(0);
}
x_62 = lean::cnstr_get(x_10, 0);
x_64 = lean::cnstr_get_scalar<uint8>(x_10, sizeof(void*)*1);
if (lean::is_exclusive(x_10)) {
 x_65 = x_10;
} else {
 lean::inc(x_62);
 lean::dec(x_10);
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
if (lean::is_scalar(x_61)) {
 x_68 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_68 = x_61;
}
lean::cnstr_set(x_68, 0, x_67);
lean::cnstr_set(x_68, 1, x_59);
return x_68;
}
}
else
{
obj* x_69; obj* x_70; obj* x_71; obj* x_72; 
x_69 = l_lean_parser_monad__parsec_many1__aux_x_27___main___at_lean_parser_parse__bin__lit___spec__2___closed__1;
x_70 = l_lean_parser_monad__parsec_many1__aux_x_27___main___at_lean_parser_parse__bin__lit___spec__2___closed__2;
x_71 = l_reader__t_orelse___at_lean_parser_parse__bin__lit___spec__1___rarg(x_69, x_70, x_1, x_2, x_3);
x_72 = lean::cnstr_get(x_71, 0);
lean::inc(x_72);
if (lean::obj_tag(x_72) == 0)
{
obj* x_74; obj* x_76; obj* x_77; obj* x_79; obj* x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_86; 
x_74 = lean::cnstr_get(x_71, 1);
if (lean::is_exclusive(x_71)) {
 lean::cnstr_release(x_71, 0);
 x_76 = x_71;
} else {
 lean::inc(x_74);
 lean::dec(x_71);
 x_76 = lean::box(0);
}
x_77 = lean::cnstr_get(x_72, 1);
x_79 = lean::cnstr_get(x_72, 2);
if (lean::is_exclusive(x_72)) {
 lean::cnstr_release(x_72, 0);
 x_81 = x_72;
} else {
 lean::inc(x_77);
 lean::inc(x_79);
 lean::dec(x_72);
 x_81 = lean::box(0);
}
x_82 = lean::box(0);
x_83 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_81)) {
 x_84 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_84 = x_81;
}
lean::cnstr_set(x_84, 0, x_82);
lean::cnstr_set(x_84, 1, x_77);
lean::cnstr_set(x_84, 2, x_83);
x_85 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_79, x_84);
if (lean::is_scalar(x_76)) {
 x_86 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_86 = x_76;
}
lean::cnstr_set(x_86, 0, x_85);
lean::cnstr_set(x_86, 1, x_74);
return x_86;
}
else
{
obj* x_87; obj* x_89; obj* x_90; uint8 x_92; obj* x_93; obj* x_94; obj* x_95; obj* x_96; 
x_87 = lean::cnstr_get(x_71, 1);
if (lean::is_exclusive(x_71)) {
 lean::cnstr_release(x_71, 0);
 x_89 = x_71;
} else {
 lean::inc(x_87);
 lean::dec(x_71);
 x_89 = lean::box(0);
}
x_90 = lean::cnstr_get(x_72, 0);
x_92 = lean::cnstr_get_scalar<uint8>(x_72, sizeof(void*)*1);
if (lean::is_exclusive(x_72)) {
 x_93 = x_72;
} else {
 lean::inc(x_90);
 lean::dec(x_72);
 x_93 = lean::box(0);
}
if (lean::is_scalar(x_93)) {
 x_94 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_94 = x_93;
}
lean::cnstr_set(x_94, 0, x_90);
lean::cnstr_set_scalar(x_94, sizeof(void*)*1, x_92);
x_95 = x_94;
if (lean::is_scalar(x_89)) {
 x_96 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_96 = x_89;
}
lean::cnstr_set(x_96, 0, x_95);
lean::cnstr_set(x_96, 1, x_87);
return x_96;
}
}
}
}
obj* l_lean_parser_parse__bin__lit(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint32 x_3; obj* x_4; obj* x_5; obj* x_7; obj* x_8; 
x_3 = 48;
x_7 = l_lean_parser_monad__parsec_ch___at___private_init_lean_parser_token_4__ident_x_27___spec__11(x_3, x_0, x_1, x_2);
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
if (lean::obj_tag(x_8) == 0)
{
obj* x_10; obj* x_13; obj* x_15; uint32 x_18; obj* x_20; obj* x_21; 
x_10 = lean::cnstr_get(x_7, 1);
lean::inc(x_10);
lean::dec(x_7);
x_13 = lean::cnstr_get(x_8, 1);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_8, 2);
lean::inc(x_15);
lean::dec(x_8);
x_18 = 98;
lean::inc(x_13);
x_20 = l_lean_parser_monad__parsec_ch___at___private_init_lean_parser_token_4__ident_x_27___spec__11(x_18, x_0, x_13, x_10);
x_21 = lean::cnstr_get(x_20, 0);
lean::inc(x_21);
if (lean::obj_tag(x_21) == 0)
{
obj* x_24; obj* x_27; 
lean::dec(x_13);
x_24 = lean::cnstr_get(x_20, 1);
lean::inc(x_24);
lean::dec(x_20);
x_27 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_21);
x_4 = x_27;
x_5 = x_24;
goto lbl_6;
}
else
{
obj* x_28; obj* x_31; uint8 x_33; uint32 x_34; 
x_28 = lean::cnstr_get(x_20, 1);
lean::inc(x_28);
lean::dec(x_20);
x_31 = lean::cnstr_get(x_21, 0);
lean::inc(x_31);
x_33 = lean::cnstr_get_scalar<uint8>(x_21, sizeof(void*)*1);
x_34 = 66;
if (x_33 == 0)
{
obj* x_36; obj* x_37; obj* x_39; obj* x_42; obj* x_43; 
lean::dec(x_21);
x_36 = l_lean_parser_monad__parsec_ch___at___private_init_lean_parser_token_4__ident_x_27___spec__11(x_34, x_0, x_13, x_28);
x_37 = lean::cnstr_get(x_36, 0);
lean::inc(x_37);
x_39 = lean::cnstr_get(x_36, 1);
lean::inc(x_39);
lean::dec(x_36);
x_42 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_31, x_37);
x_43 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_42);
x_4 = x_43;
x_5 = x_39;
goto lbl_6;
}
else
{
obj* x_46; 
lean::dec(x_13);
lean::dec(x_31);
x_46 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_21);
x_4 = x_46;
x_5 = x_28;
goto lbl_6;
}
}
}
else
{
obj* x_47; obj* x_50; uint8 x_52; obj* x_53; obj* x_54; obj* x_55; 
x_47 = lean::cnstr_get(x_7, 1);
lean::inc(x_47);
lean::dec(x_7);
x_50 = lean::cnstr_get(x_8, 0);
x_52 = lean::cnstr_get_scalar<uint8>(x_8, sizeof(void*)*1);
if (lean::is_exclusive(x_8)) {
 x_53 = x_8;
} else {
 lean::inc(x_50);
 lean::dec(x_8);
 x_53 = lean::box(0);
}
if (lean::is_scalar(x_53)) {
 x_54 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_54 = x_53;
}
lean::cnstr_set(x_54, 0, x_50);
lean::cnstr_set_scalar(x_54, sizeof(void*)*1, x_52);
x_55 = x_54;
x_4 = x_55;
x_5 = x_47;
goto lbl_6;
}
lbl_6:
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_56; obj* x_58; obj* x_61; obj* x_62; obj* x_64; obj* x_66; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; 
x_56 = lean::cnstr_get(x_4, 1);
lean::inc(x_56);
x_58 = lean::cnstr_get(x_4, 2);
lean::inc(x_58);
lean::dec(x_4);
x_61 = lean::string_iterator_remaining(x_56);
x_62 = l_lean_parser_monad__parsec_many1__aux_x_27___main___at_lean_parser_parse__bin__lit___spec__2(x_61, x_0, x_56, x_5);
lean::dec(x_61);
x_64 = lean::cnstr_get(x_62, 0);
x_66 = lean::cnstr_get(x_62, 1);
if (lean::is_exclusive(x_62)) {
 x_68 = x_62;
} else {
 lean::inc(x_64);
 lean::inc(x_66);
 lean::dec(x_62);
 x_68 = lean::box(0);
}
x_69 = l_lean_parser_finish__comment__block___closed__2;
x_70 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_69, x_64);
x_71 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_58, x_70);
if (lean::is_scalar(x_68)) {
 x_72 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_72 = x_68;
}
lean::cnstr_set(x_72, 0, x_71);
lean::cnstr_set(x_72, 1, x_66);
return x_72;
}
else
{
obj* x_74; uint8 x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; 
lean::dec(x_0);
x_74 = lean::cnstr_get(x_4, 0);
x_76 = lean::cnstr_get_scalar<uint8>(x_4, sizeof(void*)*1);
if (lean::is_exclusive(x_4)) {
 x_77 = x_4;
} else {
 lean::inc(x_74);
 lean::dec(x_4);
 x_77 = lean::box(0);
}
if (lean::is_scalar(x_77)) {
 x_78 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_78 = x_77;
}
lean::cnstr_set(x_78, 0, x_74);
lean::cnstr_set_scalar(x_78, sizeof(void*)*1, x_76);
x_79 = x_78;
x_80 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_80, 0, x_79);
lean::cnstr_set(x_80, 1, x_5);
return x_80;
}
}
}
}
obj* l_reader__t_orelse___at_lean_parser_parse__bin__lit___spec__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_reader__t_orelse___at_lean_parser_parse__bin__lit___spec__1(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_parser_monad__parsec_many1__aux_x_27___main___at_lean_parser_parse__bin__lit___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_parser_monad__parsec_many1__aux_x_27___main___at_lean_parser_parse__bin__lit___spec__2(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_parse__oct__lit___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = lean::string_iterator_has_next(x_2);
if (x_5 == 0)
{
obj* x_7; 
lean::dec(x_0);
x_7 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_7;
}
else
{
uint32 x_8; uint32 x_9; uint8 x_10; 
x_8 = 48;
x_9 = lean::string_iterator_curr(x_2);
x_10 = x_8 <= x_9;
if (x_10 == 0)
{
obj* x_12; 
lean::dec(x_0);
x_12 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_12;
}
else
{
uint32 x_13; uint8 x_14; 
x_13 = 56;
x_14 = x_9 < x_13;
if (x_14 == 0)
{
obj* x_16; 
lean::dec(x_0);
x_16 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_16;
}
else
{
obj* x_17; obj* x_18; obj* x_20; obj* x_21; 
x_17 = lean::mk_nat_obj(1u);
x_18 = lean::nat_sub(x_0, x_17);
lean::dec(x_0);
x_20 = lean::string_push(x_1, x_9);
x_21 = lean::string_iterator_next(x_2);
x_0 = x_18;
x_1 = x_20;
x_2 = x_21;
goto _start;
}
}
}
}
else
{
obj* x_24; 
lean::dec(x_0);
x_24 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_24;
}
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_parse__oct__lit___spec__2(uint32 x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_4 = l_string_join___closed__1;
x_5 = lean::string_push(x_4, x_0);
x_6 = lean::string_iterator_remaining(x_2);
x_7 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_parse__oct__lit___spec__3(x_6, x_5, x_2);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_3);
return x_8;
}
}
obj* l_lean_parser_monad__parsec_take__while1___at_lean_parser_parse__oct__lit___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; uint8 x_6; 
x_6 = lean::string_iterator_has_next(x_1);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_12; obj* x_14; obj* x_17; obj* x_18; 
x_7 = lean::box(0);
x_8 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_9 = l_mjoin___rarg___closed__1;
x_10 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_8, x_9, x_7, x_7, x_0, x_1, x_2);
lean::dec(x_1);
x_12 = lean::cnstr_get(x_10, 0);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_10, 1);
lean::inc(x_14);
lean::dec(x_10);
x_17 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_18 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_17, x_12);
x_3 = x_18;
x_4 = x_14;
goto lbl_5;
}
else
{
uint32 x_19; uint32 x_20; uint8 x_21; 
x_19 = 48;
x_20 = lean::string_iterator_curr(x_1);
x_21 = x_19 <= x_20;
if (x_21 == 0)
{
obj* x_22; obj* x_23; obj* x_24; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_31; obj* x_33; obj* x_36; obj* x_37; 
x_22 = l_char_quote__core(x_20);
x_23 = l_char_has__repr___closed__1;
x_24 = lean::string_append(x_23, x_22);
lean::dec(x_22);
x_26 = lean::string_append(x_24, x_23);
x_27 = lean::box(0);
x_28 = l_mjoin___rarg___closed__1;
x_29 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_26, x_28, x_27, x_27, x_0, x_1, x_2);
lean::dec(x_1);
x_31 = lean::cnstr_get(x_29, 0);
lean::inc(x_31);
x_33 = lean::cnstr_get(x_29, 1);
lean::inc(x_33);
lean::dec(x_29);
x_36 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_37 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_36, x_31);
x_3 = x_37;
x_4 = x_33;
goto lbl_5;
}
else
{
uint32 x_38; uint8 x_39; 
x_38 = 56;
x_39 = x_20 < x_38;
if (x_39 == 0)
{
obj* x_40; obj* x_41; obj* x_42; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_49; obj* x_51; obj* x_54; obj* x_55; 
x_40 = l_char_quote__core(x_20);
x_41 = l_char_has__repr___closed__1;
x_42 = lean::string_append(x_41, x_40);
lean::dec(x_40);
x_44 = lean::string_append(x_42, x_41);
x_45 = lean::box(0);
x_46 = l_mjoin___rarg___closed__1;
x_47 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_44, x_46, x_45, x_45, x_0, x_1, x_2);
lean::dec(x_1);
x_49 = lean::cnstr_get(x_47, 0);
lean::inc(x_49);
x_51 = lean::cnstr_get(x_47, 1);
lean::inc(x_51);
lean::dec(x_47);
x_54 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_55 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_54, x_49);
x_3 = x_55;
x_4 = x_51;
goto lbl_5;
}
else
{
obj* x_56; obj* x_57; obj* x_58; obj* x_59; 
x_56 = lean::string_iterator_next(x_1);
x_57 = lean::box(0);
x_58 = lean::box_uint32(x_20);
x_59 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_59, 0, x_58);
lean::cnstr_set(x_59, 1, x_56);
lean::cnstr_set(x_59, 2, x_57);
x_3 = x_59;
x_4 = x_2;
goto lbl_5;
}
}
}
lbl_5:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_60; obj* x_62; obj* x_64; uint32 x_67; obj* x_68; obj* x_69; obj* x_71; obj* x_73; obj* x_74; obj* x_75; 
x_60 = lean::cnstr_get(x_3, 0);
lean::inc(x_60);
x_62 = lean::cnstr_get(x_3, 1);
lean::inc(x_62);
x_64 = lean::cnstr_get(x_3, 2);
lean::inc(x_64);
lean::dec(x_3);
x_67 = lean::unbox_uint32(x_60);
x_68 = l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_parse__oct__lit___spec__2(x_67, x_0, x_62, x_4);
x_69 = lean::cnstr_get(x_68, 0);
x_71 = lean::cnstr_get(x_68, 1);
if (lean::is_exclusive(x_68)) {
 x_73 = x_68;
} else {
 lean::inc(x_69);
 lean::inc(x_71);
 lean::dec(x_68);
 x_73 = lean::box(0);
}
x_74 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_64, x_69);
if (lean::is_scalar(x_73)) {
 x_75 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_75 = x_73;
}
lean::cnstr_set(x_75, 0, x_74);
lean::cnstr_set(x_75, 1, x_71);
return x_75;
}
else
{
obj* x_76; uint8 x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; 
x_76 = lean::cnstr_get(x_3, 0);
x_78 = lean::cnstr_get_scalar<uint8>(x_3, sizeof(void*)*1);
if (lean::is_exclusive(x_3)) {
 x_79 = x_3;
} else {
 lean::inc(x_76);
 lean::dec(x_3);
 x_79 = lean::box(0);
}
if (lean::is_scalar(x_79)) {
 x_80 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_80 = x_79;
}
lean::cnstr_set(x_80, 0, x_76);
lean::cnstr_set_scalar(x_80, sizeof(void*)*1, x_78);
x_81 = x_80;
x_82 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_82, 0, x_81);
lean::cnstr_set(x_82, 1, x_4);
return x_82;
}
}
}
}
obj* l_lean_parser_parse__oct__lit(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint32 x_3; obj* x_4; obj* x_5; obj* x_7; obj* x_8; 
x_3 = 48;
x_7 = l_lean_parser_monad__parsec_ch___at___private_init_lean_parser_token_4__ident_x_27___spec__11(x_3, x_0, x_1, x_2);
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
if (lean::obj_tag(x_8) == 0)
{
obj* x_10; obj* x_13; obj* x_15; uint32 x_18; obj* x_20; obj* x_21; 
x_10 = lean::cnstr_get(x_7, 1);
lean::inc(x_10);
lean::dec(x_7);
x_13 = lean::cnstr_get(x_8, 1);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_8, 2);
lean::inc(x_15);
lean::dec(x_8);
x_18 = 111;
lean::inc(x_13);
x_20 = l_lean_parser_monad__parsec_ch___at___private_init_lean_parser_token_4__ident_x_27___spec__11(x_18, x_0, x_13, x_10);
x_21 = lean::cnstr_get(x_20, 0);
lean::inc(x_21);
if (lean::obj_tag(x_21) == 0)
{
obj* x_24; obj* x_27; 
lean::dec(x_13);
x_24 = lean::cnstr_get(x_20, 1);
lean::inc(x_24);
lean::dec(x_20);
x_27 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_21);
x_4 = x_27;
x_5 = x_24;
goto lbl_6;
}
else
{
obj* x_28; obj* x_31; uint8 x_33; uint32 x_34; 
x_28 = lean::cnstr_get(x_20, 1);
lean::inc(x_28);
lean::dec(x_20);
x_31 = lean::cnstr_get(x_21, 0);
lean::inc(x_31);
x_33 = lean::cnstr_get_scalar<uint8>(x_21, sizeof(void*)*1);
x_34 = 79;
if (x_33 == 0)
{
obj* x_36; obj* x_37; obj* x_39; obj* x_42; obj* x_43; 
lean::dec(x_21);
x_36 = l_lean_parser_monad__parsec_ch___at___private_init_lean_parser_token_4__ident_x_27___spec__11(x_34, x_0, x_13, x_28);
x_37 = lean::cnstr_get(x_36, 0);
lean::inc(x_37);
x_39 = lean::cnstr_get(x_36, 1);
lean::inc(x_39);
lean::dec(x_36);
x_42 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_31, x_37);
x_43 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_42);
x_4 = x_43;
x_5 = x_39;
goto lbl_6;
}
else
{
obj* x_46; 
lean::dec(x_13);
lean::dec(x_31);
x_46 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_21);
x_4 = x_46;
x_5 = x_28;
goto lbl_6;
}
}
}
else
{
obj* x_47; obj* x_50; uint8 x_52; obj* x_53; obj* x_54; obj* x_55; 
x_47 = lean::cnstr_get(x_7, 1);
lean::inc(x_47);
lean::dec(x_7);
x_50 = lean::cnstr_get(x_8, 0);
x_52 = lean::cnstr_get_scalar<uint8>(x_8, sizeof(void*)*1);
if (lean::is_exclusive(x_8)) {
 x_53 = x_8;
} else {
 lean::inc(x_50);
 lean::dec(x_8);
 x_53 = lean::box(0);
}
if (lean::is_scalar(x_53)) {
 x_54 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_54 = x_53;
}
lean::cnstr_set(x_54, 0, x_50);
lean::cnstr_set_scalar(x_54, sizeof(void*)*1, x_52);
x_55 = x_54;
x_4 = x_55;
x_5 = x_47;
goto lbl_6;
}
lbl_6:
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_56; obj* x_58; obj* x_61; obj* x_62; obj* x_64; obj* x_66; obj* x_67; obj* x_68; 
x_56 = lean::cnstr_get(x_4, 1);
lean::inc(x_56);
x_58 = lean::cnstr_get(x_4, 2);
lean::inc(x_58);
lean::dec(x_4);
x_61 = l_lean_parser_monad__parsec_take__while1___at_lean_parser_parse__oct__lit___spec__1(x_0, x_56, x_5);
x_62 = lean::cnstr_get(x_61, 0);
x_64 = lean::cnstr_get(x_61, 1);
if (lean::is_exclusive(x_61)) {
 x_66 = x_61;
} else {
 lean::inc(x_62);
 lean::inc(x_64);
 lean::dec(x_61);
 x_66 = lean::box(0);
}
x_67 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_58, x_62);
if (lean::is_scalar(x_66)) {
 x_68 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_68 = x_66;
}
lean::cnstr_set(x_68, 0, x_67);
lean::cnstr_set(x_68, 1, x_64);
return x_68;
}
else
{
obj* x_69; uint8 x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; 
x_69 = lean::cnstr_get(x_4, 0);
x_71 = lean::cnstr_get_scalar<uint8>(x_4, sizeof(void*)*1);
if (lean::is_exclusive(x_4)) {
 x_72 = x_4;
} else {
 lean::inc(x_69);
 lean::dec(x_4);
 x_72 = lean::box(0);
}
if (lean::is_scalar(x_72)) {
 x_73 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_73 = x_72;
}
lean::cnstr_set(x_73, 0, x_69);
lean::cnstr_set_scalar(x_73, sizeof(void*)*1, x_71);
x_74 = x_73;
x_75 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_75, 0, x_74);
lean::cnstr_set(x_75, 1, x_5);
return x_75;
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
lean::dec(x_1);
return x_5;
}
}
obj* l_lean_parser_monad__parsec_take__while1___at_lean_parser_parse__oct__lit___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_parser_monad__parsec_take__while1___at_lean_parser_parse__oct__lit___spec__1(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_lean_parser_parse__oct__lit___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_parser_parse__oct__lit(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_parse__hex__lit___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = lean::string_iterator_has_next(x_2);
if (x_5 == 0)
{
obj* x_7; 
lean::dec(x_0);
x_7 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_7;
}
else
{
obj* x_8; obj* x_9; uint32 x_11; uint8 x_12; 
x_8 = lean::mk_nat_obj(1u);
x_9 = lean::nat_sub(x_0, x_8);
lean::dec(x_0);
x_11 = lean::string_iterator_curr(x_2);
x_12 = l_char_is__digit(x_11);
if (x_12 == 0)
{
uint8 x_13; 
x_13 = l_char_is__alpha(x_11);
if (x_13 == 0)
{
obj* x_15; 
lean::dec(x_9);
x_15 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_15;
}
else
{
obj* x_16; obj* x_17; 
x_16 = lean::string_push(x_1, x_11);
x_17 = lean::string_iterator_next(x_2);
x_0 = x_9;
x_1 = x_16;
x_2 = x_17;
goto _start;
}
}
else
{
if (x_12 == 0)
{
obj* x_20; 
lean::dec(x_9);
x_20 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_20;
}
else
{
obj* x_21; obj* x_22; 
x_21 = lean::string_push(x_1, x_11);
x_22 = lean::string_iterator_next(x_2);
x_0 = x_9;
x_1 = x_21;
x_2 = x_22;
goto _start;
}
}
}
}
else
{
obj* x_25; 
lean::dec(x_0);
x_25 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_25;
}
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_parse__hex__lit___spec__2(uint32 x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_4 = l_string_join___closed__1;
x_5 = lean::string_push(x_4, x_0);
x_6 = lean::string_iterator_remaining(x_2);
x_7 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_parse__hex__lit___spec__3(x_6, x_5, x_2);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_3);
return x_8;
}
}
obj* l_lean_parser_monad__parsec_take__while1___at_lean_parser_parse__hex__lit___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; uint8 x_6; 
x_6 = lean::string_iterator_has_next(x_1);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_12; obj* x_14; obj* x_17; obj* x_18; 
x_7 = lean::box(0);
x_8 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_9 = l_mjoin___rarg___closed__1;
x_10 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_8, x_9, x_7, x_7, x_0, x_1, x_2);
lean::dec(x_1);
x_12 = lean::cnstr_get(x_10, 0);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_10, 1);
lean::inc(x_14);
lean::dec(x_10);
x_17 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_18 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_17, x_12);
x_3 = x_18;
x_4 = x_14;
goto lbl_5;
}
else
{
uint32 x_19; uint8 x_20; 
x_19 = lean::string_iterator_curr(x_1);
x_20 = l_char_is__digit(x_19);
if (x_20 == 0)
{
uint8 x_21; 
x_21 = l_char_is__alpha(x_19);
if (x_21 == 0)
{
obj* x_22; obj* x_23; obj* x_24; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_31; obj* x_33; obj* x_36; obj* x_37; 
x_22 = l_char_quote__core(x_19);
x_23 = l_char_has__repr___closed__1;
x_24 = lean::string_append(x_23, x_22);
lean::dec(x_22);
x_26 = lean::string_append(x_24, x_23);
x_27 = lean::box(0);
x_28 = l_mjoin___rarg___closed__1;
x_29 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_26, x_28, x_27, x_27, x_0, x_1, x_2);
lean::dec(x_1);
x_31 = lean::cnstr_get(x_29, 0);
lean::inc(x_31);
x_33 = lean::cnstr_get(x_29, 1);
lean::inc(x_33);
lean::dec(x_29);
x_36 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_37 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_36, x_31);
x_3 = x_37;
x_4 = x_33;
goto lbl_5;
}
else
{
obj* x_38; obj* x_39; obj* x_40; obj* x_41; 
x_38 = lean::string_iterator_next(x_1);
x_39 = lean::box(0);
x_40 = lean::box_uint32(x_19);
x_41 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_41, 0, x_40);
lean::cnstr_set(x_41, 1, x_38);
lean::cnstr_set(x_41, 2, x_39);
x_3 = x_41;
x_4 = x_2;
goto lbl_5;
}
}
else
{
if (x_20 == 0)
{
obj* x_42; obj* x_43; obj* x_44; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_51; obj* x_53; obj* x_56; obj* x_57; 
x_42 = l_char_quote__core(x_19);
x_43 = l_char_has__repr___closed__1;
x_44 = lean::string_append(x_43, x_42);
lean::dec(x_42);
x_46 = lean::string_append(x_44, x_43);
x_47 = lean::box(0);
x_48 = l_mjoin___rarg___closed__1;
x_49 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_46, x_48, x_47, x_47, x_0, x_1, x_2);
lean::dec(x_1);
x_51 = lean::cnstr_get(x_49, 0);
lean::inc(x_51);
x_53 = lean::cnstr_get(x_49, 1);
lean::inc(x_53);
lean::dec(x_49);
x_56 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_57 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_56, x_51);
x_3 = x_57;
x_4 = x_53;
goto lbl_5;
}
else
{
obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
x_58 = lean::string_iterator_next(x_1);
x_59 = lean::box(0);
x_60 = lean::box_uint32(x_19);
x_61 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_61, 0, x_60);
lean::cnstr_set(x_61, 1, x_58);
lean::cnstr_set(x_61, 2, x_59);
x_3 = x_61;
x_4 = x_2;
goto lbl_5;
}
}
}
lbl_5:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_62; obj* x_64; obj* x_66; uint32 x_69; obj* x_70; obj* x_71; obj* x_73; obj* x_75; obj* x_76; obj* x_77; 
x_62 = lean::cnstr_get(x_3, 0);
lean::inc(x_62);
x_64 = lean::cnstr_get(x_3, 1);
lean::inc(x_64);
x_66 = lean::cnstr_get(x_3, 2);
lean::inc(x_66);
lean::dec(x_3);
x_69 = lean::unbox_uint32(x_62);
x_70 = l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_parse__hex__lit___spec__2(x_69, x_0, x_64, x_4);
x_71 = lean::cnstr_get(x_70, 0);
x_73 = lean::cnstr_get(x_70, 1);
if (lean::is_exclusive(x_70)) {
 x_75 = x_70;
} else {
 lean::inc(x_71);
 lean::inc(x_73);
 lean::dec(x_70);
 x_75 = lean::box(0);
}
x_76 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_66, x_71);
if (lean::is_scalar(x_75)) {
 x_77 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_77 = x_75;
}
lean::cnstr_set(x_77, 0, x_76);
lean::cnstr_set(x_77, 1, x_73);
return x_77;
}
else
{
obj* x_78; uint8 x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; 
x_78 = lean::cnstr_get(x_3, 0);
x_80 = lean::cnstr_get_scalar<uint8>(x_3, sizeof(void*)*1);
if (lean::is_exclusive(x_3)) {
 x_81 = x_3;
} else {
 lean::inc(x_78);
 lean::dec(x_3);
 x_81 = lean::box(0);
}
if (lean::is_scalar(x_81)) {
 x_82 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_82 = x_81;
}
lean::cnstr_set(x_82, 0, x_78);
lean::cnstr_set_scalar(x_82, sizeof(void*)*1, x_80);
x_83 = x_82;
x_84 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_84, 0, x_83);
lean::cnstr_set(x_84, 1, x_4);
return x_84;
}
}
}
}
obj* l_lean_parser_parse__hex__lit(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint32 x_3; obj* x_4; obj* x_5; obj* x_7; obj* x_8; 
x_3 = 48;
x_7 = l_lean_parser_monad__parsec_ch___at___private_init_lean_parser_token_4__ident_x_27___spec__11(x_3, x_0, x_1, x_2);
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
if (lean::obj_tag(x_8) == 0)
{
obj* x_10; obj* x_13; obj* x_15; uint32 x_18; obj* x_20; obj* x_21; 
x_10 = lean::cnstr_get(x_7, 1);
lean::inc(x_10);
lean::dec(x_7);
x_13 = lean::cnstr_get(x_8, 1);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_8, 2);
lean::inc(x_15);
lean::dec(x_8);
x_18 = 120;
lean::inc(x_13);
x_20 = l_lean_parser_monad__parsec_ch___at___private_init_lean_parser_token_4__ident_x_27___spec__11(x_18, x_0, x_13, x_10);
x_21 = lean::cnstr_get(x_20, 0);
lean::inc(x_21);
if (lean::obj_tag(x_21) == 0)
{
obj* x_24; obj* x_27; 
lean::dec(x_13);
x_24 = lean::cnstr_get(x_20, 1);
lean::inc(x_24);
lean::dec(x_20);
x_27 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_21);
x_4 = x_27;
x_5 = x_24;
goto lbl_6;
}
else
{
obj* x_28; obj* x_31; uint8 x_33; uint32 x_34; 
x_28 = lean::cnstr_get(x_20, 1);
lean::inc(x_28);
lean::dec(x_20);
x_31 = lean::cnstr_get(x_21, 0);
lean::inc(x_31);
x_33 = lean::cnstr_get_scalar<uint8>(x_21, sizeof(void*)*1);
x_34 = 88;
if (x_33 == 0)
{
obj* x_36; obj* x_37; obj* x_39; obj* x_42; obj* x_43; 
lean::dec(x_21);
x_36 = l_lean_parser_monad__parsec_ch___at___private_init_lean_parser_token_4__ident_x_27___spec__11(x_34, x_0, x_13, x_28);
x_37 = lean::cnstr_get(x_36, 0);
lean::inc(x_37);
x_39 = lean::cnstr_get(x_36, 1);
lean::inc(x_39);
lean::dec(x_36);
x_42 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_31, x_37);
x_43 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_42);
x_4 = x_43;
x_5 = x_39;
goto lbl_6;
}
else
{
obj* x_46; 
lean::dec(x_13);
lean::dec(x_31);
x_46 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_21);
x_4 = x_46;
x_5 = x_28;
goto lbl_6;
}
}
}
else
{
obj* x_47; obj* x_50; uint8 x_52; obj* x_53; obj* x_54; obj* x_55; 
x_47 = lean::cnstr_get(x_7, 1);
lean::inc(x_47);
lean::dec(x_7);
x_50 = lean::cnstr_get(x_8, 0);
x_52 = lean::cnstr_get_scalar<uint8>(x_8, sizeof(void*)*1);
if (lean::is_exclusive(x_8)) {
 x_53 = x_8;
} else {
 lean::inc(x_50);
 lean::dec(x_8);
 x_53 = lean::box(0);
}
if (lean::is_scalar(x_53)) {
 x_54 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_54 = x_53;
}
lean::cnstr_set(x_54, 0, x_50);
lean::cnstr_set_scalar(x_54, sizeof(void*)*1, x_52);
x_55 = x_54;
x_4 = x_55;
x_5 = x_47;
goto lbl_6;
}
lbl_6:
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_56; obj* x_58; obj* x_61; obj* x_62; obj* x_64; obj* x_66; obj* x_67; obj* x_68; 
x_56 = lean::cnstr_get(x_4, 1);
lean::inc(x_56);
x_58 = lean::cnstr_get(x_4, 2);
lean::inc(x_58);
lean::dec(x_4);
x_61 = l_lean_parser_monad__parsec_take__while1___at_lean_parser_parse__hex__lit___spec__1(x_0, x_56, x_5);
x_62 = lean::cnstr_get(x_61, 0);
x_64 = lean::cnstr_get(x_61, 1);
if (lean::is_exclusive(x_61)) {
 x_66 = x_61;
} else {
 lean::inc(x_62);
 lean::inc(x_64);
 lean::dec(x_61);
 x_66 = lean::box(0);
}
x_67 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_58, x_62);
if (lean::is_scalar(x_66)) {
 x_68 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_68 = x_66;
}
lean::cnstr_set(x_68, 0, x_67);
lean::cnstr_set(x_68, 1, x_64);
return x_68;
}
else
{
obj* x_69; uint8 x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; 
x_69 = lean::cnstr_get(x_4, 0);
x_71 = lean::cnstr_get_scalar<uint8>(x_4, sizeof(void*)*1);
if (lean::is_exclusive(x_4)) {
 x_72 = x_4;
} else {
 lean::inc(x_69);
 lean::dec(x_4);
 x_72 = lean::box(0);
}
if (lean::is_scalar(x_72)) {
 x_73 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_73 = x_72;
}
lean::cnstr_set(x_73, 0, x_69);
lean::cnstr_set_scalar(x_73, sizeof(void*)*1, x_71);
x_74 = x_73;
x_75 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_75, 0, x_74);
lean::cnstr_set(x_75, 1, x_5);
return x_75;
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
lean::dec(x_1);
return x_5;
}
}
obj* l_lean_parser_monad__parsec_take__while1___at_lean_parser_parse__hex__lit___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_parser_monad__parsec_take__while1___at_lean_parser_parse__hex__lit___spec__1(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_lean_parser_parse__hex__lit___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_parser_parse__hex__lit(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
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
if (x_6 == 0)
{
obj* x_7; uint8 x_8; 
x_7 = lean::mk_nat_obj(1u);
x_8 = lean::nat_dec_eq(x_1, x_7);
if (x_8 == 0)
{
obj* x_9; uint8 x_10; 
x_9 = lean::mk_nat_obj(2u);
x_10 = lean::nat_dec_eq(x_1, x_9);
lean::dec(x_1);
if (x_10 == 0)
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_12; obj* x_15; obj* x_16; 
x_12 = lean::cnstr_get(x_0, 0);
lean::inc(x_12);
lean::dec(x_0);
x_15 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_15, 0, x_12);
x_16 = lean::alloc_cnstr(3, 1, 0);
lean::cnstr_set(x_16, 0, x_15);
return x_16;
}
case 3:
{
obj* x_17; 
x_17 = l_lean_parser_number_has__view_x_27___lambda__1___closed__1;
return x_17;
}
default:
{
obj* x_19; 
lean::dec(x_0);
x_19 = l_lean_parser_number_has__view_x_27___lambda__1___closed__1;
return x_19;
}
}
}
else
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_20; obj* x_23; obj* x_24; 
x_20 = lean::cnstr_get(x_0, 0);
lean::inc(x_20);
lean::dec(x_0);
x_23 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_23, 0, x_20);
x_24 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_24, 0, x_23);
return x_24;
}
case 3:
{
obj* x_25; 
x_25 = l_lean_parser_number_has__view_x_27___lambda__1___closed__2;
return x_25;
}
default:
{
obj* x_27; 
lean::dec(x_0);
x_27 = l_lean_parser_number_has__view_x_27___lambda__1___closed__2;
return x_27;
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
obj* x_29; obj* x_32; obj* x_33; 
x_29 = lean::cnstr_get(x_0, 0);
lean::inc(x_29);
lean::dec(x_0);
x_32 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_32, 0, x_29);
x_33 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_33, 0, x_32);
return x_33;
}
case 3:
{
obj* x_34; 
x_34 = l_lean_parser_number_has__view_x_27___lambda__1___closed__3;
return x_34;
}
default:
{
obj* x_36; 
lean::dec(x_0);
x_36 = l_lean_parser_number_has__view_x_27___lambda__1___closed__3;
return x_36;
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
obj* x_38; obj* x_41; obj* x_42; 
x_38 = lean::cnstr_get(x_0, 0);
lean::inc(x_38);
lean::dec(x_0);
x_41 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_41, 0, x_38);
x_42 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_42, 0, x_41);
return x_42;
}
case 3:
{
obj* x_43; 
x_43 = l_lean_parser_number_has__view_x_27___lambda__1___closed__4;
return x_43;
}
default:
{
obj* x_45; 
lean::dec(x_0);
x_45 = l_lean_parser_number_has__view_x_27___lambda__1___closed__4;
return x_45;
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
obj* x_5; 
x_5 = l_lean_parser_number_has__view_x_27___lambda__1___closed__5;
return x_5;
}
else
{
obj* x_6; obj* x_9; obj* x_11; obj* x_14; uint8 x_15; 
x_6 = lean::cnstr_get(x_4, 0);
lean::inc(x_6);
lean::dec(x_4);
x_9 = lean::cnstr_get(x_6, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_6, 1);
lean::inc(x_11);
lean::dec(x_6);
x_14 = l_lean_parser_number_has__view_x_27___lambda__1___closed__6;
x_15 = lean_name_dec_eq(x_9, x_14);
lean::dec(x_9);
if (x_15 == 0)
{
obj* x_18; 
lean::dec(x_11);
x_18 = l_lean_parser_number_has__view_x_27___lambda__1___closed__5;
return x_18;
}
else
{
if (lean::obj_tag(x_11) == 0)
{
obj* x_19; 
x_19 = l_lean_parser_number_has__view_x_27___lambda__1___closed__5;
return x_19;
}
else
{
obj* x_20; 
x_20 = lean::cnstr_get(x_11, 1);
lean::inc(x_20);
if (lean::obj_tag(x_20) == 0)
{
obj* x_22; obj* x_25; 
x_22 = lean::cnstr_get(x_11, 0);
lean::inc(x_22);
lean::dec(x_11);
x_25 = l_lean_parser_syntax_as__node___main(x_22);
if (lean::obj_tag(x_25) == 0)
{
obj* x_26; 
x_26 = l_lean_parser_number_has__view_x_27___lambda__1___closed__5;
return x_26;
}
else
{
obj* x_27; obj* x_30; 
x_27 = lean::cnstr_get(x_25, 0);
lean::inc(x_27);
lean::dec(x_25);
x_30 = lean::cnstr_get(x_27, 0);
lean::inc(x_30);
switch (lean::obj_tag(x_30)) {
case 0:
{
obj* x_33; 
lean::dec(x_27);
x_33 = l_lean_parser_number_has__view_x_27___lambda__1___closed__5;
return x_33;
}
case 1:
{
obj* x_36; 
lean::dec(x_27);
lean::dec(x_30);
x_36 = l_lean_parser_number_has__view_x_27___lambda__1___closed__5;
return x_36;
}
default:
{
obj* x_37; obj* x_40; obj* x_42; obj* x_45; uint8 x_46; 
x_37 = lean::cnstr_get(x_27, 1);
lean::inc(x_37);
lean::dec(x_27);
x_40 = lean::cnstr_get(x_30, 0);
lean::inc(x_40);
x_42 = lean::cnstr_get(x_30, 1);
lean::inc(x_42);
lean::dec(x_30);
x_45 = lean::box(0);
x_46 = lean_name_dec_eq(x_40, x_45);
lean::dec(x_40);
if (x_46 == 0)
{
obj* x_50; 
lean::dec(x_42);
lean::dec(x_37);
x_50 = l_lean_parser_number_has__view_x_27___lambda__1___closed__5;
return x_50;
}
else
{
if (lean::obj_tag(x_37) == 0)
{
obj* x_52; 
lean::dec(x_42);
x_52 = l_lean_parser_number_has__view_x_27___lambda__1___closed__5;
return x_52;
}
else
{
obj* x_53; 
x_53 = lean::cnstr_get(x_37, 1);
lean::inc(x_53);
if (lean::obj_tag(x_53) == 0)
{
obj* x_55; 
x_55 = lean::cnstr_get(x_37, 0);
lean::inc(x_55);
lean::dec(x_37);
x_1 = x_55;
x_2 = x_42;
goto lbl_3;
}
else
{
obj* x_61; 
lean::dec(x_42);
lean::dec(x_53);
lean::dec(x_37);
x_61 = l_lean_parser_number_has__view_x_27___lambda__1___closed__5;
return x_61;
}
}
}
}
}
}
}
else
{
obj* x_64; 
lean::dec(x_11);
lean::dec(x_20);
x_64 = l_lean_parser_number_has__view_x_27___lambda__1___closed__5;
return x_64;
}
}
}
}
lbl_3:
{
obj* x_65; uint8 x_66; 
x_65 = lean::mk_nat_obj(0u);
x_66 = lean::nat_dec_eq(x_2, x_65);
if (x_66 == 0)
{
obj* x_67; uint8 x_68; 
x_67 = lean::mk_nat_obj(1u);
x_68 = lean::nat_dec_eq(x_2, x_67);
if (x_68 == 0)
{
obj* x_69; uint8 x_70; 
x_69 = lean::mk_nat_obj(2u);
x_70 = lean::nat_dec_eq(x_2, x_69);
lean::dec(x_2);
if (x_70 == 0)
{
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_72; obj* x_75; obj* x_76; 
x_72 = lean::cnstr_get(x_1, 0);
lean::inc(x_72);
lean::dec(x_1);
x_75 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_75, 0, x_72);
x_76 = lean::alloc_cnstr(3, 1, 0);
lean::cnstr_set(x_76, 0, x_75);
return x_76;
}
case 3:
{
obj* x_77; 
x_77 = l_lean_parser_number_has__view_x_27___lambda__1___closed__1;
return x_77;
}
default:
{
obj* x_79; 
lean::dec(x_1);
x_79 = l_lean_parser_number_has__view_x_27___lambda__1___closed__1;
return x_79;
}
}
}
else
{
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_80; obj* x_83; obj* x_84; 
x_80 = lean::cnstr_get(x_1, 0);
lean::inc(x_80);
lean::dec(x_1);
x_83 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_83, 0, x_80);
x_84 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_84, 0, x_83);
return x_84;
}
case 3:
{
obj* x_85; 
x_85 = l_lean_parser_number_has__view_x_27___lambda__1___closed__2;
return x_85;
}
default:
{
obj* x_87; 
lean::dec(x_1);
x_87 = l_lean_parser_number_has__view_x_27___lambda__1___closed__2;
return x_87;
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
obj* x_89; obj* x_92; obj* x_93; 
x_89 = lean::cnstr_get(x_1, 0);
lean::inc(x_89);
lean::dec(x_1);
x_92 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_92, 0, x_89);
x_93 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_93, 0, x_92);
return x_93;
}
case 3:
{
obj* x_94; 
x_94 = l_lean_parser_number_has__view_x_27___lambda__1___closed__3;
return x_94;
}
default:
{
obj* x_96; 
lean::dec(x_1);
x_96 = l_lean_parser_number_has__view_x_27___lambda__1___closed__3;
return x_96;
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
obj* x_98; obj* x_101; obj* x_102; 
x_98 = lean::cnstr_get(x_1, 0);
lean::inc(x_98);
lean::dec(x_1);
x_101 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_101, 0, x_98);
x_102 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_102, 0, x_101);
return x_102;
}
case 3:
{
obj* x_103; 
x_103 = l_lean_parser_number_has__view_x_27___lambda__1___closed__4;
return x_103;
}
default:
{
obj* x_105; 
lean::dec(x_1);
x_105 = l_lean_parser_number_has__view_x_27___lambda__1___closed__4;
return x_105;
}
}
}
}
}
}
obj* _init_l_lean_parser_number_has__view_x_27___lambda__2___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_0 = lean::box(0);
x_1 = lean::box(0);
x_2 = lean::mk_nat_obj(0u);
x_3 = lean_name_mk_numeral(x_1, x_2);
x_4 = lean::box(0);
x_5 = lean::box(3);
x_6 = l_option_get__or__else___main___rarg(x_4, x_5);
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_0);
x_8 = l_lean_parser_syntax_mk__node(x_3, x_7);
x_9 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_0);
x_10 = l_lean_parser_number;
x_11 = l_lean_parser_syntax_mk__node(x_10, x_9);
return x_11;
}
}
obj* _init_l_lean_parser_number_has__view_x_27___lambda__2___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_0 = lean::box(0);
x_1 = lean::box(0);
x_2 = lean::mk_nat_obj(1u);
x_3 = lean_name_mk_numeral(x_1, x_2);
x_4 = lean::box(0);
x_5 = lean::box(3);
x_6 = l_option_get__or__else___main___rarg(x_4, x_5);
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_0);
x_8 = l_lean_parser_syntax_mk__node(x_3, x_7);
x_9 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_0);
x_10 = l_lean_parser_number;
x_11 = l_lean_parser_syntax_mk__node(x_10, x_9);
return x_11;
}
}
obj* _init_l_lean_parser_number_has__view_x_27___lambda__2___closed__3() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_0 = lean::box(0);
x_1 = lean::box(0);
x_2 = lean::mk_nat_obj(2u);
x_3 = lean_name_mk_numeral(x_1, x_2);
x_4 = lean::box(0);
x_5 = lean::box(3);
x_6 = l_option_get__or__else___main___rarg(x_4, x_5);
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_0);
x_8 = l_lean_parser_syntax_mk__node(x_3, x_7);
x_9 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_0);
x_10 = l_lean_parser_number;
x_11 = l_lean_parser_syntax_mk__node(x_10, x_9);
return x_11;
}
}
obj* _init_l_lean_parser_number_has__view_x_27___lambda__2___closed__4() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_nat_obj(2u);
x_2 = lean_name_mk_numeral(x_0, x_1);
return x_2;
}
}
obj* _init_l_lean_parser_number_has__view_x_27___lambda__2___closed__5() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_0 = lean::box(0);
x_1 = lean::box(0);
x_2 = lean::mk_nat_obj(3u);
x_3 = lean_name_mk_numeral(x_1, x_2);
x_4 = lean::box(0);
x_5 = lean::box(3);
x_6 = l_option_get__or__else___main___rarg(x_4, x_5);
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_0);
x_8 = l_lean_parser_syntax_mk__node(x_3, x_7);
x_9 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_0);
x_10 = l_lean_parser_number;
x_11 = l_lean_parser_syntax_mk__node(x_10, x_9);
return x_11;
}
}
obj* _init_l_lean_parser_number_has__view_x_27___lambda__2___closed__6() {
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
obj* x_2; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
if (lean::obj_tag(x_2) == 0)
{
obj* x_5; 
x_5 = l_lean_parser_number_has__view_x_27___lambda__2___closed__1;
return x_5;
}
else
{
obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_6 = lean::cnstr_get(x_2, 0);
if (lean::is_exclusive(x_2)) {
 x_8 = x_2;
} else {
 lean::inc(x_6);
 lean::dec(x_2);
 x_8 = lean::box(0);
}
x_9 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_9, 0, x_6);
if (lean::is_scalar(x_8)) {
 x_10 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_10 = x_8;
}
lean::cnstr_set(x_10, 0, x_9);
x_11 = lean::box(3);
x_12 = l_option_get__or__else___main___rarg(x_10, x_11);
lean::dec(x_10);
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_12);
lean::cnstr_set(x_14, 1, x_1);
x_15 = l_lean_parser_detail__ident__part_has__view_x_27___lambda__2___closed__1;
x_16 = l_lean_parser_syntax_mk__node(x_15, x_14);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_1);
x_18 = l_lean_parser_number;
x_19 = l_lean_parser_syntax_mk__node(x_18, x_17);
return x_19;
}
}
case 1:
{
obj* x_20; 
x_20 = lean::cnstr_get(x_0, 0);
lean::inc(x_20);
lean::dec(x_0);
if (lean::obj_tag(x_20) == 0)
{
obj* x_23; 
x_23 = l_lean_parser_number_has__view_x_27___lambda__2___closed__2;
return x_23;
}
else
{
obj* x_24; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; 
x_24 = lean::cnstr_get(x_20, 0);
if (lean::is_exclusive(x_20)) {
 x_26 = x_20;
} else {
 lean::inc(x_24);
 lean::dec(x_20);
 x_26 = lean::box(0);
}
x_27 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_27, 0, x_24);
if (lean::is_scalar(x_26)) {
 x_28 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_28 = x_26;
}
lean::cnstr_set(x_28, 0, x_27);
x_29 = lean::box(3);
x_30 = l_option_get__or__else___main___rarg(x_28, x_29);
lean::dec(x_28);
x_32 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_32, 0, x_30);
lean::cnstr_set(x_32, 1, x_1);
x_33 = l_lean_parser_detail__ident__part_has__view_x_27___lambda__2___closed__3;
x_34 = l_lean_parser_syntax_mk__node(x_33, x_32);
x_35 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_1);
x_36 = l_lean_parser_number;
x_37 = l_lean_parser_syntax_mk__node(x_36, x_35);
return x_37;
}
}
case 2:
{
obj* x_38; 
x_38 = lean::cnstr_get(x_0, 0);
lean::inc(x_38);
lean::dec(x_0);
if (lean::obj_tag(x_38) == 0)
{
obj* x_41; 
x_41 = l_lean_parser_number_has__view_x_27___lambda__2___closed__3;
return x_41;
}
else
{
obj* x_42; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; 
x_42 = lean::cnstr_get(x_38, 0);
if (lean::is_exclusive(x_38)) {
 x_44 = x_38;
} else {
 lean::inc(x_42);
 lean::dec(x_38);
 x_44 = lean::box(0);
}
x_45 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_45, 0, x_42);
if (lean::is_scalar(x_44)) {
 x_46 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_46 = x_44;
}
lean::cnstr_set(x_46, 0, x_45);
x_47 = lean::box(3);
x_48 = l_option_get__or__else___main___rarg(x_46, x_47);
lean::dec(x_46);
x_50 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_50, 0, x_48);
lean::cnstr_set(x_50, 1, x_1);
x_51 = l_lean_parser_number_has__view_x_27___lambda__2___closed__4;
x_52 = l_lean_parser_syntax_mk__node(x_51, x_50);
x_53 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_53, 0, x_52);
lean::cnstr_set(x_53, 1, x_1);
x_54 = l_lean_parser_number;
x_55 = l_lean_parser_syntax_mk__node(x_54, x_53);
return x_55;
}
}
default:
{
obj* x_56; 
x_56 = lean::cnstr_get(x_0, 0);
lean::inc(x_56);
lean::dec(x_0);
if (lean::obj_tag(x_56) == 0)
{
obj* x_59; 
x_59 = l_lean_parser_number_has__view_x_27___lambda__2___closed__5;
return x_59;
}
else
{
obj* x_60; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; 
x_60 = lean::cnstr_get(x_56, 0);
if (lean::is_exclusive(x_56)) {
 x_62 = x_56;
} else {
 lean::inc(x_60);
 lean::dec(x_56);
 x_62 = lean::box(0);
}
x_63 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_63, 0, x_60);
if (lean::is_scalar(x_62)) {
 x_64 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_64 = x_62;
}
lean::cnstr_set(x_64, 0, x_63);
x_65 = lean::box(3);
x_66 = l_option_get__or__else___main___rarg(x_64, x_65);
lean::dec(x_64);
x_68 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_68, 0, x_66);
lean::cnstr_set(x_68, 1, x_1);
x_69 = l_lean_parser_number_has__view_x_27___lambda__2___closed__6;
x_70 = l_lean_parser_syntax_mk__node(x_69, x_68);
x_71 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_71, 0, x_70);
lean::cnstr_set(x_71, 1, x_1);
x_72 = l_lean_parser_number;
x_73 = l_lean_parser_syntax_mk__node(x_72, x_71);
return x_73;
}
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
return x_0;
}
}
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_number_x_27___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = lean::string_iterator_has_next(x_2);
if (x_5 == 0)
{
obj* x_7; 
lean::dec(x_0);
x_7 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_7;
}
else
{
uint32 x_8; uint8 x_9; 
x_8 = lean::string_iterator_curr(x_2);
x_9 = l_char_is__digit(x_8);
if (x_9 == 0)
{
obj* x_11; 
lean::dec(x_0);
x_11 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_11;
}
else
{
obj* x_12; obj* x_13; obj* x_15; obj* x_16; 
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_sub(x_0, x_12);
lean::dec(x_0);
x_15 = lean::string_push(x_1, x_8);
x_16 = lean::string_iterator_next(x_2);
x_0 = x_13;
x_1 = x_15;
x_2 = x_16;
goto _start;
}
}
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
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_number_x_27___spec__2(uint32 x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_4 = l_string_join___closed__1;
x_5 = lean::string_push(x_4, x_0);
x_6 = lean::string_iterator_remaining(x_2);
x_7 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_number_x_27___spec__3(x_6, x_5, x_2);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_3);
return x_8;
}
}
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_number_x_27___spec__5(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = lean::string_iterator_has_next(x_2);
if (x_5 == 0)
{
obj* x_7; 
lean::dec(x_0);
x_7 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_7;
}
else
{
uint32 x_8; uint8 x_9; 
x_8 = lean::string_iterator_curr(x_2);
x_9 = l_char_is__digit(x_8);
if (x_9 == 0)
{
obj* x_11; 
lean::dec(x_0);
x_11 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_11;
}
else
{
obj* x_12; obj* x_13; obj* x_15; obj* x_16; 
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_sub(x_0, x_12);
lean::dec(x_0);
x_15 = lean::string_push(x_1, x_8);
x_16 = lean::string_iterator_next(x_2);
x_0 = x_13;
x_1 = x_15;
x_2 = x_16;
goto _start;
}
}
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
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_number_x_27___spec__4(uint32 x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_4 = l_string_join___closed__1;
x_5 = lean::string_push(x_4, x_0);
x_6 = lean::string_iterator_remaining(x_2);
x_7 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_number_x_27___spec__5(x_6, x_5, x_2);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_3);
return x_8;
}
}
obj* l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_number_x_27___spec__7(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = lean::string_iterator_has_next(x_2);
if (x_5 == 0)
{
obj* x_7; 
lean::dec(x_0);
x_7 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_7;
}
else
{
uint32 x_8; uint8 x_9; 
x_8 = lean::string_iterator_curr(x_2);
x_9 = l_char_is__digit(x_8);
if (x_9 == 0)
{
obj* x_11; 
lean::dec(x_0);
x_11 = l___private_init_lean_parser_parsec_3__mk__string__result___rarg(x_1, x_2);
return x_11;
}
else
{
obj* x_12; obj* x_13; obj* x_15; obj* x_16; 
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_sub(x_0, x_12);
lean::dec(x_0);
x_15 = lean::string_push(x_1, x_8);
x_16 = lean::string_iterator_next(x_2);
x_0 = x_13;
x_1 = x_15;
x_2 = x_16;
goto _start;
}
}
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
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_number_x_27___spec__6(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint32 x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_4 = lean::string_iterator_curr(x_0);
x_5 = l_string_join___closed__1;
x_6 = lean::string_push(x_5, x_4);
x_7 = lean::string_iterator_remaining(x_2);
x_8 = l___private_init_lean_parser_parsec_4__take__while__aux___main___at_lean_parser_number_x_27___spec__7(x_7, x_6, x_2);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_3);
return x_9;
}
}
obj* l_lean_parser_monad__parsec_take__while1___at_lean_parser_number_x_27___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = lean::string_iterator_has_next(x_1);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_14; obj* x_15; 
x_4 = lean::box(0);
x_5 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_6 = l_mjoin___rarg___closed__1;
x_7 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_5, x_6, x_4, x_4, x_0, x_1, x_2);
lean::dec(x_1);
x_9 = lean::cnstr_get(x_7, 0);
x_11 = lean::cnstr_get(x_7, 1);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_set(x_7, 0, lean::box(0));
 lean::cnstr_set(x_7, 1, lean::box(0));
 x_13 = x_7;
} else {
 lean::inc(x_9);
 lean::inc(x_11);
 lean::dec(x_7);
 x_13 = lean::box(0);
}
x_14 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_15 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_14, x_9);
if (lean::obj_tag(x_15) == 0)
{
obj* x_17; obj* x_19; obj* x_21; uint32 x_24; obj* x_25; obj* x_26; obj* x_28; obj* x_30; obj* x_31; obj* x_32; 
lean::dec(x_13);
x_17 = lean::cnstr_get(x_15, 0);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_15, 1);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_15, 2);
lean::inc(x_21);
lean::dec(x_15);
x_24 = lean::unbox_uint32(x_17);
x_25 = l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_number_x_27___spec__2(x_24, x_0, x_19, x_11);
x_26 = lean::cnstr_get(x_25, 0);
x_28 = lean::cnstr_get(x_25, 1);
if (lean::is_exclusive(x_25)) {
 x_30 = x_25;
} else {
 lean::inc(x_26);
 lean::inc(x_28);
 lean::dec(x_25);
 x_30 = lean::box(0);
}
x_31 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_21, x_26);
if (lean::is_scalar(x_30)) {
 x_32 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_32 = x_30;
}
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_28);
return x_32;
}
else
{
obj* x_33; uint8 x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; 
x_33 = lean::cnstr_get(x_15, 0);
x_35 = lean::cnstr_get_scalar<uint8>(x_15, sizeof(void*)*1);
if (lean::is_exclusive(x_15)) {
 x_36 = x_15;
} else {
 lean::inc(x_33);
 lean::dec(x_15);
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
if (lean::is_scalar(x_13)) {
 x_39 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_39 = x_13;
}
lean::cnstr_set(x_39, 0, x_38);
lean::cnstr_set(x_39, 1, x_11);
return x_39;
}
}
else
{
uint32 x_40; uint8 x_41; 
x_40 = lean::string_iterator_curr(x_1);
x_41 = l_char_is__digit(x_40);
if (x_41 == 0)
{
obj* x_42; obj* x_43; obj* x_44; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_51; obj* x_53; obj* x_55; obj* x_56; obj* x_57; 
x_42 = l_char_quote__core(x_40);
x_43 = l_char_has__repr___closed__1;
x_44 = lean::string_append(x_43, x_42);
lean::dec(x_42);
x_46 = lean::string_append(x_44, x_43);
x_47 = lean::box(0);
x_48 = l_mjoin___rarg___closed__1;
x_49 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_46, x_48, x_47, x_47, x_0, x_1, x_2);
lean::dec(x_1);
x_51 = lean::cnstr_get(x_49, 0);
x_53 = lean::cnstr_get(x_49, 1);
if (lean::is_exclusive(x_49)) {
 lean::cnstr_set(x_49, 0, lean::box(0));
 lean::cnstr_set(x_49, 1, lean::box(0));
 x_55 = x_49;
} else {
 lean::inc(x_51);
 lean::inc(x_53);
 lean::dec(x_49);
 x_55 = lean::box(0);
}
x_56 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_57 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_56, x_51);
if (lean::obj_tag(x_57) == 0)
{
obj* x_59; obj* x_61; obj* x_63; uint32 x_66; obj* x_67; obj* x_68; obj* x_70; obj* x_72; obj* x_73; obj* x_74; 
lean::dec(x_55);
x_59 = lean::cnstr_get(x_57, 0);
lean::inc(x_59);
x_61 = lean::cnstr_get(x_57, 1);
lean::inc(x_61);
x_63 = lean::cnstr_get(x_57, 2);
lean::inc(x_63);
lean::dec(x_57);
x_66 = lean::unbox_uint32(x_59);
x_67 = l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_number_x_27___spec__4(x_66, x_0, x_61, x_53);
x_68 = lean::cnstr_get(x_67, 0);
x_70 = lean::cnstr_get(x_67, 1);
if (lean::is_exclusive(x_67)) {
 x_72 = x_67;
} else {
 lean::inc(x_68);
 lean::inc(x_70);
 lean::dec(x_67);
 x_72 = lean::box(0);
}
x_73 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_63, x_68);
if (lean::is_scalar(x_72)) {
 x_74 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_74 = x_72;
}
lean::cnstr_set(x_74, 0, x_73);
lean::cnstr_set(x_74, 1, x_70);
return x_74;
}
else
{
obj* x_75; uint8 x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; 
x_75 = lean::cnstr_get(x_57, 0);
x_77 = lean::cnstr_get_scalar<uint8>(x_57, sizeof(void*)*1);
if (lean::is_exclusive(x_57)) {
 x_78 = x_57;
} else {
 lean::inc(x_75);
 lean::dec(x_57);
 x_78 = lean::box(0);
}
if (lean::is_scalar(x_78)) {
 x_79 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_79 = x_78;
}
lean::cnstr_set(x_79, 0, x_75);
lean::cnstr_set_scalar(x_79, sizeof(void*)*1, x_77);
x_80 = x_79;
if (lean::is_scalar(x_55)) {
 x_81 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_81 = x_55;
}
lean::cnstr_set(x_81, 0, x_80);
lean::cnstr_set(x_81, 1, x_53);
return x_81;
}
}
else
{
obj* x_83; obj* x_84; obj* x_86; obj* x_88; obj* x_90; obj* x_91; obj* x_92; obj* x_93; 
lean::inc(x_1);
x_83 = lean::string_iterator_next(x_1);
x_84 = l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_number_x_27___spec__6(x_1, x_0, x_83, x_2);
lean::dec(x_1);
x_86 = lean::cnstr_get(x_84, 0);
x_88 = lean::cnstr_get(x_84, 1);
if (lean::is_exclusive(x_84)) {
 x_90 = x_84;
} else {
 lean::inc(x_86);
 lean::inc(x_88);
 lean::dec(x_84);
 x_90 = lean::box(0);
}
x_91 = lean::box(0);
x_92 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_91, x_86);
if (lean::is_scalar(x_90)) {
 x_93 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_93 = x_90;
}
lean::cnstr_set(x_93, 0, x_92);
lean::cnstr_set(x_93, 1, x_88);
return x_93;
}
}
}
}
obj* l_list_map___main___at_lean_parser_number_x_27___spec__9___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_6; obj* x_9; obj* x_10; 
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
lean::dec(x_0);
x_9 = lean::apply_3(x_6, x_1, x_2, x_3);
x_10 = lean::cnstr_get(x_9, 0);
lean::inc(x_10);
if (lean::obj_tag(x_10) == 0)
{
obj* x_12; obj* x_14; obj* x_15; obj* x_17; obj* x_19; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
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
x_22 = lean::box(0);
x_23 = lean_name_mk_numeral(x_22, x_4);
x_24 = lean::box(0);
x_25 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_25, 0, x_15);
lean::cnstr_set(x_25, 1, x_24);
x_26 = l_lean_parser_syntax_mk__node(x_23, x_25);
x_27 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_21)) {
 x_28 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_28 = x_21;
}
lean::cnstr_set(x_28, 0, x_26);
lean::cnstr_set(x_28, 1, x_17);
lean::cnstr_set(x_28, 2, x_27);
x_29 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_19, x_28);
if (lean::is_scalar(x_14)) {
 x_30 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_30 = x_14;
}
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_12);
return x_30;
}
else
{
obj* x_32; obj* x_34; obj* x_35; uint8 x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; 
lean::dec(x_4);
x_32 = lean::cnstr_get(x_9, 1);
if (lean::is_exclusive(x_9)) {
 lean::cnstr_release(x_9, 0);
 x_34 = x_9;
} else {
 lean::inc(x_32);
 lean::dec(x_9);
 x_34 = lean::box(0);
}
x_35 = lean::cnstr_get(x_10, 0);
x_37 = lean::cnstr_get_scalar<uint8>(x_10, sizeof(void*)*1);
if (lean::is_exclusive(x_10)) {
 x_38 = x_10;
} else {
 lean::inc(x_35);
 lean::dec(x_10);
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
return x_41;
}
}
}
obj* l_list_map___main___at_lean_parser_number_x_27___spec__9(obj* x_0) {
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
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_list_map___main___at_lean_parser_number_x_27___spec__9___lambda__1), 4, 1);
lean::closure_set(x_7, 0, x_2);
x_8 = l_list_map___main___at_lean_parser_number_x_27___spec__9(x_4);
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
obj* l_lean_parser_parsec__t_lookahead___at_lean_parser_number_x_27___spec__11(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_9; obj* x_10; obj* x_13; obj* x_14; 
lean::inc(x_4);
x_13 = lean::apply_3(x_1, x_3, x_4, x_5);
x_14 = lean::cnstr_get(x_13, 0);
lean::inc(x_14);
if (lean::obj_tag(x_14) == 0)
{
obj* x_16; obj* x_19; obj* x_21; obj* x_23; obj* x_25; obj* x_26; 
x_16 = lean::cnstr_get(x_13, 1);
lean::inc(x_16);
lean::dec(x_13);
x_19 = lean::cnstr_get(x_14, 0);
x_21 = lean::cnstr_get(x_14, 1);
x_23 = lean::cnstr_get(x_14, 2);
if (lean::is_exclusive(x_14)) {
 lean::cnstr_set(x_14, 0, lean::box(0));
 lean::cnstr_set(x_14, 1, lean::box(0));
 lean::cnstr_set(x_14, 2, lean::box(0));
 x_25 = x_14;
} else {
 lean::inc(x_19);
 lean::inc(x_21);
 lean::inc(x_23);
 lean::dec(x_14);
 x_25 = lean::box(0);
}
if (lean::obj_tag(x_2) == 0)
{
obj* x_28; 
x_28 = lean::cnstr_get(x_2, 2);
lean::inc(x_28);
if (lean::obj_tag(x_28) == 0)
{
obj* x_31; obj* x_33; obj* x_35; obj* x_36; uint8 x_38; 
lean::dec(x_25);
x_31 = lean::cnstr_get(x_2, 0);
lean::inc(x_31);
x_33 = lean::cnstr_get(x_2, 1);
lean::inc(x_33);
x_35 = lean::string_iterator_offset(x_21);
x_36 = lean::string_iterator_offset(x_33);
lean::dec(x_33);
x_38 = lean::nat_dec_lt(x_35, x_36);
if (x_38 == 0)
{
obj* x_40; uint8 x_41; 
lean::inc(x_2);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_release(x_2, 0);
 lean::cnstr_release(x_2, 1);
 lean::cnstr_release(x_2, 2);
 x_40 = x_2;
} else {
 lean::dec(x_2);
 x_40 = lean::box(0);
}
x_41 = lean::nat_dec_lt(x_36, x_35);
lean::dec(x_35);
lean::dec(x_36);
if (x_41 == 0)
{
obj* x_44; obj* x_46; obj* x_47; obj* x_48; obj* x_49; 
x_44 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_44, 0, x_19);
lean::cnstr_set(x_44, 1, x_31);
lean::inc(x_21);
if (lean::is_scalar(x_40)) {
 x_46 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_46 = x_40;
}
lean::cnstr_set(x_46, 0, x_44);
lean::cnstr_set(x_46, 1, x_21);
lean::cnstr_set(x_46, 2, x_28);
x_47 = l_lean_parser_finish__comment__block___closed__2;
x_48 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_48, 0, x_46);
lean::cnstr_set(x_48, 1, x_21);
lean::cnstr_set(x_48, 2, x_47);
x_49 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_23, x_48);
x_9 = x_49;
x_10 = x_16;
goto lbl_11;
}
else
{
obj* x_51; obj* x_52; obj* x_54; obj* x_55; obj* x_56; obj* x_57; 
lean::dec(x_31);
x_51 = lean::box(0);
x_52 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_52, 0, x_19);
lean::cnstr_set(x_52, 1, x_51);
lean::inc(x_21);
if (lean::is_scalar(x_40)) {
 x_54 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_54 = x_40;
}
lean::cnstr_set(x_54, 0, x_52);
lean::cnstr_set(x_54, 1, x_21);
lean::cnstr_set(x_54, 2, x_28);
x_55 = l_lean_parser_finish__comment__block___closed__2;
x_56 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_56, 0, x_54);
lean::cnstr_set(x_56, 1, x_21);
lean::cnstr_set(x_56, 2, x_55);
x_57 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_23, x_56);
x_9 = x_57;
x_10 = x_16;
goto lbl_11;
}
}
else
{
obj* x_62; obj* x_64; obj* x_65; 
lean::dec(x_35);
lean::dec(x_36);
lean::dec(x_19);
lean::dec(x_31);
x_62 = l_lean_parser_finish__comment__block___closed__2;
lean::inc(x_2);
x_64 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_64, 0, x_2);
lean::cnstr_set(x_64, 1, x_21);
lean::cnstr_set(x_64, 2, x_62);
x_65 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_23, x_64);
x_9 = x_65;
x_10 = x_16;
goto lbl_11;
}
}
else
{
obj* x_67; 
lean::dec(x_28);
x_67 = lean::box(0);
x_26 = x_67;
goto lbl_27;
}
}
else
{
obj* x_68; 
x_68 = lean::box(0);
x_26 = x_68;
goto lbl_27;
}
lbl_27:
{
obj* x_70; obj* x_71; obj* x_72; obj* x_74; obj* x_75; obj* x_76; obj* x_77; 
lean::dec(x_26);
x_70 = lean::box(0);
x_71 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_71, 0, x_19);
lean::cnstr_set(x_71, 1, x_70);
x_72 = lean::box(0);
lean::inc(x_21);
if (lean::is_scalar(x_25)) {
 x_74 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_74 = x_25;
}
lean::cnstr_set(x_74, 0, x_71);
lean::cnstr_set(x_74, 1, x_21);
lean::cnstr_set(x_74, 2, x_72);
x_75 = l_lean_parser_finish__comment__block___closed__2;
x_76 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_76, 0, x_74);
lean::cnstr_set(x_76, 1, x_21);
lean::cnstr_set(x_76, 2, x_75);
x_77 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_23, x_76);
x_9 = x_77;
x_10 = x_16;
goto lbl_11;
}
}
else
{
obj* x_78; obj* x_81; uint8 x_83; obj* x_84; obj* x_85; obj* x_86; 
x_78 = lean::cnstr_get(x_13, 1);
lean::inc(x_78);
lean::dec(x_13);
x_81 = lean::cnstr_get(x_14, 0);
x_83 = lean::cnstr_get_scalar<uint8>(x_14, sizeof(void*)*1);
if (lean::is_exclusive(x_14)) {
 x_84 = x_14;
} else {
 lean::inc(x_81);
 lean::dec(x_14);
 x_84 = lean::box(0);
}
if (lean::is_scalar(x_84)) {
 x_85 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_85 = x_84;
}
lean::cnstr_set(x_85, 0, x_81);
lean::cnstr_set_scalar(x_85, sizeof(void*)*1, x_83);
x_86 = x_85;
x_9 = x_86;
x_10 = x_78;
goto lbl_11;
}
lbl_8:
{
if (lean::obj_tag(x_6) == 0)
{
obj* x_87; obj* x_89; obj* x_90; obj* x_91; obj* x_92; 
x_87 = lean::cnstr_get(x_6, 0);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 1);
 lean::cnstr_release(x_6, 2);
 x_89 = x_6;
} else {
 lean::inc(x_87);
 lean::dec(x_6);
 x_89 = lean::box(0);
}
x_90 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_89)) {
 x_91 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_91 = x_89;
}
lean::cnstr_set(x_91, 0, x_87);
lean::cnstr_set(x_91, 1, x_4);
lean::cnstr_set(x_91, 2, x_90);
x_92 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_92, 0, x_91);
lean::cnstr_set(x_92, 1, x_7);
return x_92;
}
else
{
obj* x_94; 
lean::dec(x_4);
x_94 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_94, 0, x_6);
lean::cnstr_set(x_94, 1, x_7);
return x_94;
}
}
lbl_11:
{
if (lean::obj_tag(x_9) == 0)
{
lean::dec(x_2);
x_6 = x_9;
x_7 = x_10;
goto lbl_8;
}
else
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_96; obj* x_99; obj* x_102; obj* x_103; 
x_96 = lean::cnstr_get(x_9, 0);
lean::inc(x_96);
lean::dec(x_9);
x_99 = lean::cnstr_get(x_96, 0);
lean::inc(x_99);
lean::dec(x_96);
x_102 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_103 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_103, 0, x_2);
lean::cnstr_set(x_103, 1, x_99);
lean::cnstr_set(x_103, 2, x_102);
x_6 = x_103;
x_7 = x_10;
goto lbl_8;
}
else
{
obj* x_104; obj* x_107; obj* x_109; obj* x_111; obj* x_112; obj* x_114; uint8 x_116; 
x_104 = lean::cnstr_get(x_9, 0);
lean::inc(x_104);
lean::dec(x_9);
x_107 = lean::cnstr_get(x_104, 0);
lean::inc(x_107);
x_109 = lean::cnstr_get(x_2, 0);
lean::inc(x_109);
x_111 = lean::string_iterator_offset(x_107);
x_112 = lean::cnstr_get(x_109, 0);
lean::inc(x_112);
x_114 = lean::string_iterator_offset(x_112);
lean::dec(x_112);
x_116 = lean::nat_dec_lt(x_111, x_114);
if (x_116 == 0)
{
obj* x_117; uint8 x_118; 
if (lean::is_exclusive(x_2)) {
 lean::cnstr_release(x_2, 0);
 x_117 = x_2;
} else {
 lean::dec(x_2);
 x_117 = lean::box(0);
}
x_118 = lean::nat_dec_lt(x_114, x_111);
lean::dec(x_114);
if (x_118 == 0)
{
obj* x_120; obj* x_121; uint8 x_122; 
x_120 = l_lean_parser_parsec__t_merge___rarg(x_104, x_109);
x_121 = lean::string_iterator_offset(x_0);
x_122 = lean::nat_dec_lt(x_121, x_111);
lean::dec(x_111);
lean::dec(x_121);
if (x_122 == 0)
{
uint8 x_125; obj* x_126; obj* x_127; obj* x_128; obj* x_129; 
x_125 = 0;
if (lean::is_scalar(x_117)) {
 x_126 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_126 = x_117;
}
lean::cnstr_set(x_126, 0, x_120);
lean::cnstr_set_scalar(x_126, sizeof(void*)*1, x_125);
x_127 = x_126;
x_128 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_129 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_129, 0, x_127);
lean::cnstr_set(x_129, 1, x_107);
lean::cnstr_set(x_129, 2, x_128);
x_6 = x_129;
x_7 = x_10;
goto lbl_8;
}
else
{
uint8 x_130; obj* x_131; obj* x_132; obj* x_133; obj* x_134; 
x_130 = 1;
if (lean::is_scalar(x_117)) {
 x_131 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_131 = x_117;
}
lean::cnstr_set(x_131, 0, x_120);
lean::cnstr_set_scalar(x_131, sizeof(void*)*1, x_130);
x_132 = x_131;
x_133 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_134 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_134, 0, x_132);
lean::cnstr_set(x_134, 1, x_107);
lean::cnstr_set(x_134, 2, x_133);
x_6 = x_134;
x_7 = x_10;
goto lbl_8;
}
}
else
{
uint8 x_137; obj* x_138; obj* x_139; obj* x_140; obj* x_141; 
lean::dec(x_111);
lean::dec(x_109);
x_137 = 1;
if (lean::is_scalar(x_117)) {
 x_138 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_138 = x_117;
}
lean::cnstr_set(x_138, 0, x_104);
lean::cnstr_set_scalar(x_138, sizeof(void*)*1, x_137);
x_139 = x_138;
x_140 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_141 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_141, 0, x_139);
lean::cnstr_set(x_141, 1, x_107);
lean::cnstr_set(x_141, 2, x_140);
x_6 = x_141;
x_7 = x_10;
goto lbl_8;
}
}
else
{
obj* x_146; obj* x_147; 
lean::dec(x_111);
lean::dec(x_114);
lean::dec(x_104);
lean::dec(x_109);
x_146 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_147 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_147, 0, x_2);
lean::cnstr_set(x_147, 1, x_107);
lean::cnstr_set(x_147, 2, x_146);
x_6 = x_147;
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
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___at_lean_parser_number_x_27___spec__12___rarg___boxed), 5, 0);
return x_1;
}
}
obj* l_list_mfoldr___main___at_lean_parser_number_x_27___spec__13(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
lean::dec(x_2);
x_6 = lean::box(0);
x_7 = l_list_mfoldr___main___at_lean_parser_monad__parsec_longest__match___spec__2___rarg___closed__1;
x_8 = l_mjoin___rarg___closed__1;
x_9 = l_lean_parser_monad__parsec_error___at_lean_parser_number_x_27___spec__12___rarg(x_7, x_8, x_6, x_6, x_0);
x_10 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_11 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_11, 0, x_9);
lean::cnstr_set(x_11, 1, x_3);
lean::cnstr_set(x_11, 2, x_10);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_4);
return x_12;
}
else
{
obj* x_13; obj* x_15; obj* x_19; obj* x_20; 
x_13 = lean::cnstr_get(x_1, 0);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_1, 1);
lean::inc(x_15);
lean::dec(x_1);
lean::inc(x_2);
x_19 = l_list_mfoldr___main___at_lean_parser_number_x_27___spec__13(x_0, x_15, x_2, x_3, x_4);
x_20 = lean::cnstr_get(x_19, 0);
lean::inc(x_20);
if (lean::obj_tag(x_20) == 0)
{
obj* x_22; obj* x_25; obj* x_27; obj* x_29; obj* x_32; obj* x_33; obj* x_35; obj* x_37; obj* x_38; obj* x_39; 
x_22 = lean::cnstr_get(x_19, 1);
lean::inc(x_22);
lean::dec(x_19);
x_25 = lean::cnstr_get(x_20, 0);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_20, 1);
lean::inc(x_27);
x_29 = lean::cnstr_get(x_20, 2);
lean::inc(x_29);
lean::dec(x_20);
x_32 = l_lean_parser_parsec__t_lookahead___at_lean_parser_number_x_27___spec__11(x_0, x_13, x_25, x_2, x_27, x_22);
x_33 = lean::cnstr_get(x_32, 0);
x_35 = lean::cnstr_get(x_32, 1);
if (lean::is_exclusive(x_32)) {
 x_37 = x_32;
} else {
 lean::inc(x_33);
 lean::inc(x_35);
 lean::dec(x_32);
 x_37 = lean::box(0);
}
x_38 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_29, x_33);
if (lean::is_scalar(x_37)) {
 x_39 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_39 = x_37;
}
lean::cnstr_set(x_39, 0, x_38);
lean::cnstr_set(x_39, 1, x_35);
return x_39;
}
else
{
obj* x_42; obj* x_44; obj* x_45; uint8 x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; 
lean::dec(x_2);
lean::dec(x_13);
x_42 = lean::cnstr_get(x_19, 1);
if (lean::is_exclusive(x_19)) {
 lean::cnstr_release(x_19, 0);
 x_44 = x_19;
} else {
 lean::inc(x_42);
 lean::dec(x_19);
 x_44 = lean::box(0);
}
x_45 = lean::cnstr_get(x_20, 0);
x_47 = lean::cnstr_get_scalar<uint8>(x_20, sizeof(void*)*1);
if (lean::is_exclusive(x_20)) {
 x_48 = x_20;
} else {
 lean::inc(x_45);
 lean::dec(x_20);
 x_48 = lean::box(0);
}
if (lean::is_scalar(x_48)) {
 x_49 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_49 = x_48;
}
lean::cnstr_set(x_49, 0, x_45);
lean::cnstr_set_scalar(x_49, sizeof(void*)*1, x_47);
x_50 = x_49;
if (lean::is_scalar(x_44)) {
 x_51 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_51 = x_44;
}
lean::cnstr_set(x_51, 0, x_50);
lean::cnstr_set(x_51, 1, x_42);
return x_51;
}
}
}
}
obj* l_lean_parser_monad__parsec_longest__match___at_lean_parser_number_x_27___spec__10(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_8; obj* x_10; 
x_4 = lean::mk_nat_obj(0u);
x_5 = l_list_enum__from___main___rarg(x_4, x_0);
x_6 = l_list_map___main___at_lean_parser_number_x_27___spec__9(x_5);
lean::inc(x_2);
x_8 = l_list_mfoldr___main___at_lean_parser_number_x_27___spec__13(x_2, x_6, x_1, x_2, x_3);
lean::dec(x_2);
x_10 = lean::cnstr_get(x_8, 0);
lean::inc(x_10);
if (lean::obj_tag(x_10) == 0)
{
obj* x_12; obj* x_14; obj* x_15; obj* x_17; obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
x_12 = lean::cnstr_get(x_8, 1);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_release(x_8, 0);
 x_14 = x_8;
} else {
 lean::inc(x_12);
 lean::dec(x_8);
 x_14 = lean::box(0);
}
x_15 = lean::cnstr_get(x_10, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_10, 2);
lean::inc(x_17);
lean::dec(x_10);
x_20 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_17, x_15);
x_21 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_22 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_21, x_20);
if (lean::is_scalar(x_14)) {
 x_23 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_23 = x_14;
}
lean::cnstr_set(x_23, 0, x_22);
lean::cnstr_set(x_23, 1, x_12);
return x_23;
}
else
{
obj* x_24; obj* x_26; obj* x_27; uint8 x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; 
x_24 = lean::cnstr_get(x_8, 1);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_release(x_8, 0);
 x_26 = x_8;
} else {
 lean::inc(x_24);
 lean::dec(x_8);
 x_26 = lean::box(0);
}
x_27 = lean::cnstr_get(x_10, 0);
x_29 = lean::cnstr_get_scalar<uint8>(x_10, sizeof(void*)*1);
if (lean::is_exclusive(x_10)) {
 x_30 = x_10;
} else {
 lean::inc(x_27);
 lean::dec(x_10);
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
x_33 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_34 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_33, x_32);
if (lean::is_scalar(x_26)) {
 x_35 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_35 = x_26;
}
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_24);
return x_35;
}
}
}
obj* l_lean_parser_combinators_longest__choice___at_lean_parser_number_x_27___spec__8(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; obj* x_6; 
lean::inc(x_1);
x_5 = l_lean_parser_monad__parsec_longest__match___at_lean_parser_number_x_27___spec__10(x_0, x_1, x_2, x_3);
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
if (lean::obj_tag(x_6) == 0)
{
obj* x_8; 
x_8 = lean::cnstr_get(x_6, 0);
lean::inc(x_8);
if (lean::obj_tag(x_8) == 0)
{
obj* x_10; obj* x_13; obj* x_15; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_24; obj* x_26; obj* x_28; obj* x_29; obj* x_30; 
x_10 = lean::cnstr_get(x_5, 1);
lean::inc(x_10);
lean::dec(x_5);
x_13 = lean::cnstr_get(x_6, 1);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_6, 2);
lean::inc(x_15);
lean::dec(x_6);
x_18 = lean::box(0);
x_19 = l___private_init_lean_parser_combinators_1__many1__aux___main___rarg___closed__1;
x_20 = l_mjoin___rarg___closed__1;
x_21 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_19, x_20, x_18, x_18, x_1, x_13, x_10);
lean::dec(x_13);
lean::dec(x_1);
x_24 = lean::cnstr_get(x_21, 0);
x_26 = lean::cnstr_get(x_21, 1);
if (lean::is_exclusive(x_21)) {
 x_28 = x_21;
} else {
 lean::inc(x_24);
 lean::inc(x_26);
 lean::dec(x_21);
 x_28 = lean::box(0);
}
x_29 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_24);
if (lean::is_scalar(x_28)) {
 x_30 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_30 = x_28;
}
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_26);
return x_30;
}
else
{
obj* x_32; obj* x_34; obj* x_35; obj* x_37; obj* x_39; obj* x_40; obj* x_43; obj* x_44; obj* x_45; obj* x_46; 
lean::dec(x_1);
x_32 = lean::cnstr_get(x_5, 1);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 x_34 = x_5;
} else {
 lean::inc(x_32);
 lean::dec(x_5);
 x_34 = lean::box(0);
}
x_35 = lean::cnstr_get(x_6, 1);
x_37 = lean::cnstr_get(x_6, 2);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 x_39 = x_6;
} else {
 lean::inc(x_35);
 lean::inc(x_37);
 lean::dec(x_6);
 x_39 = lean::box(0);
}
x_40 = lean::cnstr_get(x_8, 0);
lean::inc(x_40);
lean::dec(x_8);
x_43 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_39)) {
 x_44 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_44 = x_39;
}
lean::cnstr_set(x_44, 0, x_40);
lean::cnstr_set(x_44, 1, x_35);
lean::cnstr_set(x_44, 2, x_43);
x_45 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_37, x_44);
if (lean::is_scalar(x_34)) {
 x_46 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_46 = x_34;
}
lean::cnstr_set(x_46, 0, x_45);
lean::cnstr_set(x_46, 1, x_32);
return x_46;
}
}
else
{
obj* x_48; obj* x_50; obj* x_51; uint8 x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; 
lean::dec(x_1);
x_48 = lean::cnstr_get(x_5, 1);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 x_50 = x_5;
} else {
 lean::inc(x_48);
 lean::dec(x_5);
 x_50 = lean::box(0);
}
x_51 = lean::cnstr_get(x_6, 0);
x_53 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*1);
if (lean::is_exclusive(x_6)) {
 x_54 = x_6;
} else {
 lean::inc(x_51);
 lean::dec(x_6);
 x_54 = lean::box(0);
}
if (lean::is_scalar(x_54)) {
 x_55 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_55 = x_54;
}
lean::cnstr_set(x_55, 0, x_51);
lean::cnstr_set_scalar(x_55, sizeof(void*)*1, x_53);
x_56 = x_55;
if (lean::is_scalar(x_50)) {
 x_57 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_57 = x_50;
}
lean::cnstr_set(x_57, 0, x_56);
lean::cnstr_set(x_57, 1, x_48);
return x_57;
}
}
}
obj* l_lean_parser_number_x_27___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = l_lean_parser_monad__parsec_take__while1___at_lean_parser_number_x_27___spec__1(x_1, x_2, x_3);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
if (lean::obj_tag(x_5) == 0)
{
obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_14; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_7 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_9 = x_4;
} else {
 lean::inc(x_7);
 lean::dec(x_4);
 x_9 = lean::box(0);
}
x_10 = lean::cnstr_get(x_5, 1);
x_12 = lean::cnstr_get(x_5, 2);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 x_14 = x_5;
} else {
 lean::inc(x_10);
 lean::inc(x_12);
 lean::dec(x_5);
 x_14 = lean::box(0);
}
lean::inc(x_10);
x_16 = l_lean_parser_mk__raw__res(x_0, x_10);
x_17 = l_lean_parser_finish__comment__block___closed__2;
if (lean::is_scalar(x_14)) {
 x_18 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_18 = x_14;
}
lean::cnstr_set(x_18, 0, x_16);
lean::cnstr_set(x_18, 1, x_10);
lean::cnstr_set(x_18, 2, x_17);
x_19 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_12, x_18);
if (lean::is_scalar(x_9)) {
 x_20 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_20 = x_9;
}
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_7);
return x_20;
}
else
{
obj* x_22; obj* x_24; obj* x_25; uint8 x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; 
lean::dec(x_0);
x_22 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_24 = x_4;
} else {
 lean::inc(x_22);
 lean::dec(x_4);
 x_24 = lean::box(0);
}
x_25 = lean::cnstr_get(x_5, 0);
x_27 = lean::cnstr_get_scalar<uint8>(x_5, sizeof(void*)*1);
if (lean::is_exclusive(x_5)) {
 x_28 = x_5;
} else {
 lean::inc(x_25);
 lean::dec(x_5);
 x_28 = lean::box(0);
}
if (lean::is_scalar(x_28)) {
 x_29 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_29 = x_28;
}
lean::cnstr_set(x_29, 0, x_25);
lean::cnstr_set_scalar(x_29, sizeof(void*)*1, x_27);
x_30 = x_29;
if (lean::is_scalar(x_24)) {
 x_31 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_31 = x_24;
}
lean::cnstr_set(x_31, 0, x_30);
lean::cnstr_set(x_31, 1, x_22);
return x_31;
}
}
}
obj* l_lean_parser_number_x_27___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = l_lean_parser_parse__bin__lit(x_1, x_2, x_3);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
if (lean::obj_tag(x_5) == 0)
{
obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_14; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_7 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_9 = x_4;
} else {
 lean::inc(x_7);
 lean::dec(x_4);
 x_9 = lean::box(0);
}
x_10 = lean::cnstr_get(x_5, 1);
x_12 = lean::cnstr_get(x_5, 2);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 x_14 = x_5;
} else {
 lean::inc(x_10);
 lean::inc(x_12);
 lean::dec(x_5);
 x_14 = lean::box(0);
}
lean::inc(x_10);
x_16 = l_lean_parser_mk__raw__res(x_0, x_10);
x_17 = l_lean_parser_finish__comment__block___closed__2;
if (lean::is_scalar(x_14)) {
 x_18 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_18 = x_14;
}
lean::cnstr_set(x_18, 0, x_16);
lean::cnstr_set(x_18, 1, x_10);
lean::cnstr_set(x_18, 2, x_17);
x_19 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_12, x_18);
if (lean::is_scalar(x_9)) {
 x_20 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_20 = x_9;
}
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_7);
return x_20;
}
else
{
obj* x_22; obj* x_24; obj* x_25; uint8 x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; 
lean::dec(x_0);
x_22 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_24 = x_4;
} else {
 lean::inc(x_22);
 lean::dec(x_4);
 x_24 = lean::box(0);
}
x_25 = lean::cnstr_get(x_5, 0);
x_27 = lean::cnstr_get_scalar<uint8>(x_5, sizeof(void*)*1);
if (lean::is_exclusive(x_5)) {
 x_28 = x_5;
} else {
 lean::inc(x_25);
 lean::dec(x_5);
 x_28 = lean::box(0);
}
if (lean::is_scalar(x_28)) {
 x_29 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_29 = x_28;
}
lean::cnstr_set(x_29, 0, x_25);
lean::cnstr_set_scalar(x_29, sizeof(void*)*1, x_27);
x_30 = x_29;
if (lean::is_scalar(x_24)) {
 x_31 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_31 = x_24;
}
lean::cnstr_set(x_31, 0, x_30);
lean::cnstr_set(x_31, 1, x_22);
return x_31;
}
}
}
obj* l_lean_parser_number_x_27___lambda__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = l_lean_parser_parse__oct__lit(x_1, x_2, x_3);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
if (lean::obj_tag(x_5) == 0)
{
obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_14; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_7 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_9 = x_4;
} else {
 lean::inc(x_7);
 lean::dec(x_4);
 x_9 = lean::box(0);
}
x_10 = lean::cnstr_get(x_5, 1);
x_12 = lean::cnstr_get(x_5, 2);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 x_14 = x_5;
} else {
 lean::inc(x_10);
 lean::inc(x_12);
 lean::dec(x_5);
 x_14 = lean::box(0);
}
lean::inc(x_10);
x_16 = l_lean_parser_mk__raw__res(x_0, x_10);
x_17 = l_lean_parser_finish__comment__block___closed__2;
if (lean::is_scalar(x_14)) {
 x_18 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_18 = x_14;
}
lean::cnstr_set(x_18, 0, x_16);
lean::cnstr_set(x_18, 1, x_10);
lean::cnstr_set(x_18, 2, x_17);
x_19 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_12, x_18);
if (lean::is_scalar(x_9)) {
 x_20 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_20 = x_9;
}
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_7);
return x_20;
}
else
{
obj* x_22; obj* x_24; obj* x_25; uint8 x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; 
lean::dec(x_0);
x_22 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_24 = x_4;
} else {
 lean::inc(x_22);
 lean::dec(x_4);
 x_24 = lean::box(0);
}
x_25 = lean::cnstr_get(x_5, 0);
x_27 = lean::cnstr_get_scalar<uint8>(x_5, sizeof(void*)*1);
if (lean::is_exclusive(x_5)) {
 x_28 = x_5;
} else {
 lean::inc(x_25);
 lean::dec(x_5);
 x_28 = lean::box(0);
}
if (lean::is_scalar(x_28)) {
 x_29 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_29 = x_28;
}
lean::cnstr_set(x_29, 0, x_25);
lean::cnstr_set_scalar(x_29, sizeof(void*)*1, x_27);
x_30 = x_29;
if (lean::is_scalar(x_24)) {
 x_31 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_31 = x_24;
}
lean::cnstr_set(x_31, 0, x_30);
lean::cnstr_set(x_31, 1, x_22);
return x_31;
}
}
}
obj* l_lean_parser_number_x_27___lambda__4(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = l_lean_parser_parse__hex__lit(x_1, x_2, x_3);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
if (lean::obj_tag(x_5) == 0)
{
obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_14; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_7 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_9 = x_4;
} else {
 lean::inc(x_7);
 lean::dec(x_4);
 x_9 = lean::box(0);
}
x_10 = lean::cnstr_get(x_5, 1);
x_12 = lean::cnstr_get(x_5, 2);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 x_14 = x_5;
} else {
 lean::inc(x_10);
 lean::inc(x_12);
 lean::dec(x_5);
 x_14 = lean::box(0);
}
lean::inc(x_10);
x_16 = l_lean_parser_mk__raw__res(x_0, x_10);
x_17 = l_lean_parser_finish__comment__block___closed__2;
if (lean::is_scalar(x_14)) {
 x_18 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_18 = x_14;
}
lean::cnstr_set(x_18, 0, x_16);
lean::cnstr_set(x_18, 1, x_10);
lean::cnstr_set(x_18, 2, x_17);
x_19 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_12, x_18);
if (lean::is_scalar(x_9)) {
 x_20 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_20 = x_9;
}
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_7);
return x_20;
}
else
{
obj* x_22; obj* x_24; obj* x_25; uint8 x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; 
lean::dec(x_0);
x_22 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_24 = x_4;
} else {
 lean::inc(x_22);
 lean::dec(x_4);
 x_24 = lean::box(0);
}
x_25 = lean::cnstr_get(x_5, 0);
x_27 = lean::cnstr_get_scalar<uint8>(x_5, sizeof(void*)*1);
if (lean::is_exclusive(x_5)) {
 x_28 = x_5;
} else {
 lean::inc(x_25);
 lean::dec(x_5);
 x_28 = lean::box(0);
}
if (lean::is_scalar(x_28)) {
 x_29 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_29 = x_28;
}
lean::cnstr_set(x_29, 0, x_25);
lean::cnstr_set_scalar(x_29, sizeof(void*)*1, x_27);
x_30 = x_29;
if (lean::is_scalar(x_24)) {
 x_31 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_31 = x_24;
}
lean::cnstr_set(x_31, 0, x_30);
lean::cnstr_set(x_31, 1, x_22);
return x_31;
}
}
}
obj* _init_l_lean_parser_number_x_27___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_4; obj* x_5; obj* x_7; obj* x_8; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_with__trailing___rarg___lambda__1), 2, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_lift___at_lean_parser_with__trailing___spec__1___rarg___boxed), 4, 1);
lean::closure_set(x_1, 0, x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_number_x_27___lambda__1___boxed), 4, 0);
lean::inc(x_1);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_bind___at_lean_parser_with__trailing___spec__2___rarg), 5, 2);
lean::closure_set(x_4, 0, x_1);
lean::closure_set(x_4, 1, x_2);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_number_x_27___lambda__2), 4, 0);
lean::inc(x_1);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_bind___at_lean_parser_with__trailing___spec__2___rarg), 5, 2);
lean::closure_set(x_7, 0, x_1);
lean::closure_set(x_7, 1, x_5);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_number_x_27___lambda__3___boxed), 4, 0);
lean::inc(x_1);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_bind___at_lean_parser_with__trailing___spec__2___rarg), 5, 2);
lean::closure_set(x_10, 0, x_1);
lean::closure_set(x_10, 1, x_8);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_number_x_27___lambda__4___boxed), 4, 0);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_bind___at_lean_parser_with__trailing___spec__2___rarg), 5, 2);
lean::closure_set(x_12, 0, x_1);
lean::closure_set(x_12, 1, x_11);
x_13 = lean::box(0);
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_12);
lean::cnstr_set(x_14, 1, x_13);
x_15 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_15, 0, x_10);
lean::cnstr_set(x_15, 1, x_14);
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_7);
lean::cnstr_set(x_16, 1, x_15);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_4);
lean::cnstr_set(x_17, 1, x_16);
x_18 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_longest__choice___at_lean_parser_number_x_27___spec__8), 4, 1);
lean::closure_set(x_18, 0, x_17);
x_19 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_19, 0, x_18);
lean::cnstr_set(x_19, 1, x_13);
return x_19;
}
}
obj* l_lean_parser_number_x_27(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = l_lean_parser_number;
x_4 = l_lean_parser_number_x_27___closed__1;
x_5 = l_lean_parser_combinators_node___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__15(x_3, x_4, x_0, x_1, x_2);
return x_5;
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_number_x_27___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint32 x_4; obj* x_5; 
x_4 = lean::unbox_uint32(x_0);
x_5 = l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_number_x_27___spec__2(x_4, x_1, x_2, x_3);
lean::dec(x_1);
return x_5;
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_number_x_27___spec__4___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint32 x_4; obj* x_5; 
x_4 = lean::unbox_uint32(x_0);
x_5 = l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_number_x_27___spec__4(x_4, x_1, x_2, x_3);
lean::dec(x_1);
return x_5;
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_number_x_27___spec__6___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_number_x_27___spec__6(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
return x_4;
}
}
obj* l_lean_parser_monad__parsec_take__while1___at_lean_parser_number_x_27___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_parser_monad__parsec_take__while1___at_lean_parser_number_x_27___spec__1(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_lean_parser_parsec__t_lookahead___at_lean_parser_number_x_27___spec__11___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_lean_parser_parsec__t_lookahead___at_lean_parser_number_x_27___spec__11(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_0);
return x_6;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_number_x_27___spec__12___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_lean_parser_monad__parsec_error___at_lean_parser_number_x_27___spec__12___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_2);
lean::dec(x_4);
return x_5;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_number_x_27___spec__12___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_monad__parsec_error___at_lean_parser_number_x_27___spec__12(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_list_mfoldr___main___at_lean_parser_number_x_27___spec__13___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_list_mfoldr___main___at_lean_parser_number_x_27___spec__13(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
return x_5;
}
}
obj* l_lean_parser_number_x_27___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_parser_number_x_27___lambda__1(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_lean_parser_number_x_27___lambda__3___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_parser_number_x_27___lambda__3(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_lean_parser_number_x_27___lambda__4___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_parser_number_x_27___lambda__4(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
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
obj* x_2; 
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_6; 
x_3 = lean::cnstr_get(x_1, 0);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 x_5 = x_1;
} else {
 lean::inc(x_3);
 lean::dec(x_1);
 x_5 = lean::box(0);
}
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
lean::dec(x_3);
if (lean::obj_tag(x_6) == 0)
{
obj* x_10; 
lean::dec(x_5);
x_10 = lean::box(0);
return x_10;
}
else
{
obj* x_11; 
x_11 = lean::cnstr_get(x_6, 0);
lean::inc(x_11);
lean::dec(x_6);
switch (lean::obj_tag(x_11)) {
case 0:
{
obj* x_14; obj* x_17; 
x_14 = lean::cnstr_get(x_11, 0);
lean::inc(x_14);
lean::dec(x_11);
if (lean::is_scalar(x_5)) {
 x_17 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_17 = x_5;
}
lean::cnstr_set(x_17, 0, x_14);
return x_17;
}
case 3:
{
obj* x_19; 
lean::dec(x_5);
x_19 = lean::box(0);
return x_19;
}
default:
{
obj* x_22; 
lean::dec(x_11);
lean::dec(x_5);
x_22 = lean::box(0);
return x_22;
}
}
}
}
}
}
obj* _init_l_lean_parser_string__lit_has__view_x_27___lambda__2___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_0 = lean::box(0);
x_1 = lean::box(0);
x_2 = lean::box(3);
x_3 = l_option_get__or__else___main___rarg(x_1, x_2);
x_4 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_0);
x_5 = l_lean_parser_string__lit;
x_6 = l_lean_parser_syntax_mk__node(x_5, x_4);
return x_6;
}
}
obj* l_lean_parser_string__lit_has__view_x_27___lambda__2(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_1; 
x_1 = l_lean_parser_string__lit_has__view_x_27___lambda__2___closed__1;
return x_1;
}
else
{
obj* x_2; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_11; obj* x_12; obj* x_13; 
x_2 = lean::cnstr_get(x_0, 0);
if (lean::is_exclusive(x_0)) {
 x_4 = x_0;
} else {
 lean::inc(x_2);
 lean::dec(x_0);
 x_4 = lean::box(0);
}
x_5 = lean::box(0);
x_6 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_6, 0, x_2);
if (lean::is_scalar(x_4)) {
 x_7 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_7 = x_4;
}
lean::cnstr_set(x_7, 0, x_6);
x_8 = lean::box(3);
x_9 = l_option_get__or__else___main___rarg(x_7, x_8);
lean::dec(x_7);
x_11 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_11, 0, x_9);
lean::cnstr_set(x_11, 1, x_5);
x_12 = l_lean_parser_string__lit;
x_13 = l_lean_parser_syntax_mk__node(x_12, x_11);
return x_13;
}
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
return x_0;
}
}
obj* l_lean_parser_monad__parsec_unexpected__at___at_lean_parser_string__lit_x_27___spec__4___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_1);
x_6 = lean::box(0);
x_7 = l_mjoin___rarg___closed__1;
x_8 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_0, x_7, x_5, x_6, x_2, x_3, x_4);
lean::dec(x_5);
return x_8;
}
}
obj* l_lean_parser_monad__parsec_unexpected__at___at_lean_parser_string__lit_x_27___spec__4(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_unexpected__at___at_lean_parser_string__lit_x_27___spec__4___rarg___boxed), 5, 0);
return x_1;
}
}
obj* l_lean_parser_monad__parsec_digit___at_lean_parser_string__lit_x_27___spec__6(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = lean::string_iterator_has_next(x_1);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_4 = lean::box(0);
x_5 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_6 = l_mjoin___rarg___closed__1;
x_7 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_5, x_6, x_4, x_4, x_0, x_1, x_2);
lean::dec(x_1);
x_9 = lean::cnstr_get(x_7, 0);
x_11 = lean::cnstr_get(x_7, 1);
if (lean::is_exclusive(x_7)) {
 x_13 = x_7;
} else {
 lean::inc(x_9);
 lean::inc(x_11);
 lean::dec(x_7);
 x_13 = lean::box(0);
}
x_14 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_15 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_14, x_9);
if (lean::is_scalar(x_13)) {
 x_16 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_16 = x_13;
}
lean::cnstr_set(x_16, 0, x_15);
lean::cnstr_set(x_16, 1, x_11);
return x_16;
}
else
{
uint32 x_17; uint8 x_18; 
x_17 = lean::string_iterator_curr(x_1);
x_18 = l_char_is__digit(x_17);
if (x_18 == 0)
{
obj* x_19; obj* x_20; obj* x_21; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_28; obj* x_30; obj* x_32; obj* x_33; obj* x_34; obj* x_35; 
x_19 = l_char_quote__core(x_17);
x_20 = l_char_has__repr___closed__1;
x_21 = lean::string_append(x_20, x_19);
lean::dec(x_19);
x_23 = lean::string_append(x_21, x_20);
x_24 = lean::box(0);
x_25 = l_mjoin___rarg___closed__1;
x_26 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_23, x_25, x_24, x_24, x_0, x_1, x_2);
lean::dec(x_1);
x_28 = lean::cnstr_get(x_26, 0);
x_30 = lean::cnstr_get(x_26, 1);
if (lean::is_exclusive(x_26)) {
 x_32 = x_26;
} else {
 lean::inc(x_28);
 lean::inc(x_30);
 lean::dec(x_26);
 x_32 = lean::box(0);
}
x_33 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_34 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_33, x_28);
if (lean::is_scalar(x_32)) {
 x_35 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_35 = x_32;
}
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_30);
return x_35;
}
else
{
obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; 
x_36 = lean::string_iterator_next(x_1);
x_37 = lean::box(0);
x_38 = lean::box_uint32(x_17);
x_39 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_39, 0, x_38);
lean::cnstr_set(x_39, 1, x_36);
lean::cnstr_set(x_39, 2, x_37);
x_40 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_40, 0, x_39);
lean::cnstr_set(x_40, 1, x_2);
return x_40;
}
}
}
}
obj* _init_l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__5___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("hexadecimal");
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__5(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_7; obj* x_8; 
lean::inc(x_1);
x_7 = l_lean_parser_monad__parsec_digit___at_lean_parser_string__lit_x_27___spec__6(x_0, x_1, x_2);
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
if (lean::obj_tag(x_8) == 0)
{
obj* x_10; obj* x_13; obj* x_15; obj* x_17; obj* x_19; uint32 x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_25; obj* x_26; obj* x_27; 
x_10 = lean::cnstr_get(x_7, 1);
lean::inc(x_10);
lean::dec(x_7);
x_13 = lean::cnstr_get(x_8, 0);
x_15 = lean::cnstr_get(x_8, 1);
x_17 = lean::cnstr_get(x_8, 2);
if (lean::is_exclusive(x_8)) {
 x_19 = x_8;
} else {
 lean::inc(x_13);
 lean::inc(x_15);
 lean::inc(x_17);
 lean::dec(x_8);
 x_19 = lean::box(0);
}
x_20 = lean::unbox_uint32(x_13);
x_21 = lean::uint32_to_nat(x_20);
x_22 = l___private_init_data_string_basic_4__to__nat__core___main___closed__1;
x_23 = lean::nat_sub(x_21, x_22);
lean::dec(x_21);
x_25 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_19)) {
 x_26 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_26 = x_19;
}
lean::cnstr_set(x_26, 0, x_23);
lean::cnstr_set(x_26, 1, x_15);
lean::cnstr_set(x_26, 2, x_25);
x_27 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_17, x_26);
x_3 = x_27;
x_4 = x_10;
goto lbl_5;
}
else
{
obj* x_28; obj* x_31; uint8 x_33; obj* x_34; obj* x_35; obj* x_36; 
x_28 = lean::cnstr_get(x_7, 1);
lean::inc(x_28);
lean::dec(x_7);
x_31 = lean::cnstr_get(x_8, 0);
x_33 = lean::cnstr_get_scalar<uint8>(x_8, sizeof(void*)*1);
if (lean::is_exclusive(x_8)) {
 x_34 = x_8;
} else {
 lean::inc(x_31);
 lean::dec(x_8);
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
x_3 = x_36;
x_4 = x_28;
goto lbl_5;
}
lbl_5:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_38; obj* x_39; obj* x_40; 
lean::dec(x_1);
x_38 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__5___closed__1;
x_39 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_3, x_38);
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
obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_58; obj* x_61; obj* x_62; 
x_52 = lean::box(0);
x_53 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_54 = l_mjoin___rarg___closed__1;
x_55 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_53, x_54, x_52, x_52, x_0, x_1, x_4);
x_56 = lean::cnstr_get(x_55, 0);
lean::inc(x_56);
x_58 = lean::cnstr_get(x_55, 1);
lean::inc(x_58);
lean::dec(x_55);
x_61 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_62 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_61, x_56);
x_47 = x_62;
x_48 = x_58;
goto lbl_49;
}
else
{
uint32 x_63; uint32 x_64; uint8 x_65; uint8 x_67; 
x_63 = lean::string_iterator_curr(x_1);
x_64 = 97;
x_67 = x_64 <= x_63;
if (x_67 == 0)
{
obj* x_68; obj* x_69; obj* x_70; obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_78; obj* x_81; obj* x_82; 
x_68 = l_char_quote__core(x_63);
x_69 = l_char_has__repr___closed__1;
x_70 = lean::string_append(x_69, x_68);
lean::dec(x_68);
x_72 = lean::string_append(x_70, x_69);
x_73 = lean::box(0);
x_74 = l_mjoin___rarg___closed__1;
x_75 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_72, x_74, x_73, x_73, x_0, x_1, x_4);
x_76 = lean::cnstr_get(x_75, 0);
lean::inc(x_76);
x_78 = lean::cnstr_get(x_75, 1);
lean::inc(x_78);
lean::dec(x_75);
x_81 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_82 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_81, x_76);
x_47 = x_82;
x_48 = x_78;
goto lbl_49;
}
else
{
uint8 x_83; 
x_83 = 1;
x_65 = x_83;
goto lbl_66;
}
lbl_66:
{
uint32 x_84; uint8 x_85; 
x_84 = 102;
x_85 = x_63 <= x_84;
if (x_85 == 0)
{
obj* x_86; obj* x_87; obj* x_88; obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_96; obj* x_99; obj* x_100; 
x_86 = l_char_quote__core(x_63);
x_87 = l_char_has__repr___closed__1;
x_88 = lean::string_append(x_87, x_86);
lean::dec(x_86);
x_90 = lean::string_append(x_88, x_87);
x_91 = lean::box(0);
x_92 = l_mjoin___rarg___closed__1;
x_93 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_90, x_92, x_91, x_91, x_0, x_1, x_4);
x_94 = lean::cnstr_get(x_93, 0);
lean::inc(x_94);
x_96 = lean::cnstr_get(x_93, 1);
lean::inc(x_96);
lean::dec(x_93);
x_99 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_100 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_99, x_94);
x_47 = x_100;
x_48 = x_96;
goto lbl_49;
}
else
{
if (x_65 == 0)
{
obj* x_101; obj* x_102; obj* x_103; obj* x_105; obj* x_106; obj* x_107; obj* x_108; obj* x_109; obj* x_111; obj* x_114; obj* x_115; 
x_101 = l_char_quote__core(x_63);
x_102 = l_char_has__repr___closed__1;
x_103 = lean::string_append(x_102, x_101);
lean::dec(x_101);
x_105 = lean::string_append(x_103, x_102);
x_106 = lean::box(0);
x_107 = l_mjoin___rarg___closed__1;
x_108 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_105, x_107, x_106, x_106, x_0, x_1, x_4);
x_109 = lean::cnstr_get(x_108, 0);
lean::inc(x_109);
x_111 = lean::cnstr_get(x_108, 1);
lean::inc(x_111);
lean::dec(x_108);
x_114 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_115 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_114, x_109);
x_47 = x_115;
x_48 = x_111;
goto lbl_49;
}
else
{
obj* x_117; obj* x_118; obj* x_119; obj* x_120; 
lean::inc(x_1);
x_117 = lean::string_iterator_next(x_1);
x_118 = lean::box(0);
x_119 = lean::box_uint32(x_63);
x_120 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_120, 0, x_119);
lean::cnstr_set(x_120, 1, x_117);
lean::cnstr_set(x_120, 2, x_118);
x_47 = x_120;
x_48 = x_4;
goto lbl_49;
}
}
}
}
}
else
{
obj* x_123; obj* x_124; obj* x_125; 
lean::dec(x_1);
lean::dec(x_41);
x_123 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__5___closed__1;
x_124 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_3, x_123);
x_125 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_125, 0, x_124);
lean::cnstr_set(x_125, 1, x_4);
return x_125;
}
lbl_46:
{
if (lean::obj_tag(x_44) == 0)
{
obj* x_127; obj* x_128; obj* x_129; obj* x_130; 
lean::dec(x_1);
x_127 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_41, x_44);
x_128 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__5___closed__1;
x_129 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_127, x_128);
x_130 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_130, 0, x_129);
lean::cnstr_set(x_130, 1, x_45);
return x_130;
}
else
{
obj* x_131; uint8 x_133; obj* x_134; obj* x_135; 
x_131 = lean::cnstr_get(x_44, 0);
lean::inc(x_131);
x_133 = lean::cnstr_get_scalar<uint8>(x_44, sizeof(void*)*1);
if (x_133 == 0)
{
uint8 x_138; 
lean::dec(x_44);
x_138 = lean::string_iterator_has_next(x_1);
if (x_138 == 0)
{
obj* x_139; obj* x_140; obj* x_141; obj* x_142; obj* x_144; obj* x_146; obj* x_149; obj* x_150; 
x_139 = lean::box(0);
x_140 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_141 = l_mjoin___rarg___closed__1;
x_142 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_140, x_141, x_139, x_139, x_0, x_1, x_45);
lean::dec(x_1);
x_144 = lean::cnstr_get(x_142, 0);
lean::inc(x_144);
x_146 = lean::cnstr_get(x_142, 1);
lean::inc(x_146);
lean::dec(x_142);
x_149 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_150 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_149, x_144);
x_134 = x_150;
x_135 = x_146;
goto lbl_136;
}
else
{
uint32 x_151; uint32 x_152; uint8 x_153; uint8 x_155; 
x_151 = lean::string_iterator_curr(x_1);
x_152 = 65;
x_155 = x_152 <= x_151;
if (x_155 == 0)
{
obj* x_156; obj* x_157; obj* x_158; obj* x_160; obj* x_161; obj* x_162; obj* x_163; obj* x_165; obj* x_167; obj* x_170; obj* x_171; 
x_156 = l_char_quote__core(x_151);
x_157 = l_char_has__repr___closed__1;
x_158 = lean::string_append(x_157, x_156);
lean::dec(x_156);
x_160 = lean::string_append(x_158, x_157);
x_161 = lean::box(0);
x_162 = l_mjoin___rarg___closed__1;
x_163 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_160, x_162, x_161, x_161, x_0, x_1, x_45);
lean::dec(x_1);
x_165 = lean::cnstr_get(x_163, 0);
lean::inc(x_165);
x_167 = lean::cnstr_get(x_163, 1);
lean::inc(x_167);
lean::dec(x_163);
x_170 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_171 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_170, x_165);
x_134 = x_171;
x_135 = x_167;
goto lbl_136;
}
else
{
uint8 x_172; 
x_172 = 1;
x_153 = x_172;
goto lbl_154;
}
lbl_154:
{
uint32 x_173; uint8 x_174; 
x_173 = 70;
x_174 = x_151 <= x_173;
if (x_174 == 0)
{
obj* x_175; obj* x_176; obj* x_177; obj* x_179; obj* x_180; obj* x_181; obj* x_182; obj* x_184; obj* x_186; obj* x_189; obj* x_190; 
x_175 = l_char_quote__core(x_151);
x_176 = l_char_has__repr___closed__1;
x_177 = lean::string_append(x_176, x_175);
lean::dec(x_175);
x_179 = lean::string_append(x_177, x_176);
x_180 = lean::box(0);
x_181 = l_mjoin___rarg___closed__1;
x_182 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_179, x_181, x_180, x_180, x_0, x_1, x_45);
lean::dec(x_1);
x_184 = lean::cnstr_get(x_182, 0);
lean::inc(x_184);
x_186 = lean::cnstr_get(x_182, 1);
lean::inc(x_186);
lean::dec(x_182);
x_189 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_190 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_189, x_184);
x_134 = x_190;
x_135 = x_186;
goto lbl_136;
}
else
{
if (x_153 == 0)
{
obj* x_191; obj* x_192; obj* x_193; obj* x_195; obj* x_196; obj* x_197; obj* x_198; obj* x_200; obj* x_202; obj* x_205; obj* x_206; 
x_191 = l_char_quote__core(x_151);
x_192 = l_char_has__repr___closed__1;
x_193 = lean::string_append(x_192, x_191);
lean::dec(x_191);
x_195 = lean::string_append(x_193, x_192);
x_196 = lean::box(0);
x_197 = l_mjoin___rarg___closed__1;
x_198 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_195, x_197, x_196, x_196, x_0, x_1, x_45);
lean::dec(x_1);
x_200 = lean::cnstr_get(x_198, 0);
lean::inc(x_200);
x_202 = lean::cnstr_get(x_198, 1);
lean::inc(x_202);
lean::dec(x_198);
x_205 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_206 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_205, x_200);
x_134 = x_206;
x_135 = x_202;
goto lbl_136;
}
else
{
obj* x_207; obj* x_208; obj* x_209; obj* x_210; 
x_207 = lean::string_iterator_next(x_1);
x_208 = lean::box(0);
x_209 = lean::box_uint32(x_151);
x_210 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_210, 0, x_209);
lean::cnstr_set(x_210, 1, x_207);
lean::cnstr_set(x_210, 2, x_208);
x_134 = x_210;
x_135 = x_45;
goto lbl_136;
}
}
}
}
}
else
{
obj* x_213; obj* x_214; obj* x_215; obj* x_216; 
lean::dec(x_131);
lean::dec(x_1);
x_213 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_41, x_44);
x_214 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__5___closed__1;
x_215 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_213, x_214);
x_216 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_216, 0, x_215);
lean::cnstr_set(x_216, 1, x_45);
return x_216;
}
lbl_136:
{
if (lean::obj_tag(x_134) == 0)
{
obj* x_217; obj* x_219; obj* x_221; obj* x_223; uint32 x_224; obj* x_225; obj* x_226; obj* x_227; obj* x_229; obj* x_230; obj* x_232; obj* x_233; obj* x_234; obj* x_235; obj* x_236; obj* x_237; obj* x_238; obj* x_239; 
x_217 = lean::cnstr_get(x_134, 0);
x_219 = lean::cnstr_get(x_134, 1);
x_221 = lean::cnstr_get(x_134, 2);
if (lean::is_exclusive(x_134)) {
 x_223 = x_134;
} else {
 lean::inc(x_217);
 lean::inc(x_219);
 lean::inc(x_221);
 lean::dec(x_134);
 x_223 = lean::box(0);
}
x_224 = lean::unbox_uint32(x_217);
x_225 = lean::uint32_to_nat(x_224);
x_226 = l_lean_parser_parse__hex__digit___rarg___lambda__5___closed__1;
x_227 = lean::nat_sub(x_225, x_226);
lean::dec(x_225);
x_229 = lean::mk_nat_obj(10u);
x_230 = lean::nat_add(x_229, x_227);
lean::dec(x_227);
x_232 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_223)) {
 x_233 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_233 = x_223;
}
lean::cnstr_set(x_233, 0, x_230);
lean::cnstr_set(x_233, 1, x_219);
lean::cnstr_set(x_233, 2, x_232);
x_234 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_221, x_233);
x_235 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_131, x_234);
x_236 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_41, x_235);
x_237 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__5___closed__1;
x_238 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_236, x_237);
x_239 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_239, 0, x_238);
lean::cnstr_set(x_239, 1, x_135);
return x_239;
}
else
{
obj* x_240; uint8 x_242; obj* x_243; obj* x_244; obj* x_245; obj* x_246; obj* x_247; obj* x_248; obj* x_249; obj* x_250; 
x_240 = lean::cnstr_get(x_134, 0);
x_242 = lean::cnstr_get_scalar<uint8>(x_134, sizeof(void*)*1);
if (lean::is_exclusive(x_134)) {
 x_243 = x_134;
} else {
 lean::inc(x_240);
 lean::dec(x_134);
 x_243 = lean::box(0);
}
if (lean::is_scalar(x_243)) {
 x_244 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_244 = x_243;
}
lean::cnstr_set(x_244, 0, x_240);
lean::cnstr_set_scalar(x_244, sizeof(void*)*1, x_242);
x_245 = x_244;
x_246 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_131, x_245);
x_247 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_41, x_246);
x_248 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__5___closed__1;
x_249 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_247, x_248);
x_250 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_250, 0, x_249);
lean::cnstr_set(x_250, 1, x_135);
return x_250;
}
}
}
}
lbl_49:
{
if (lean::obj_tag(x_47) == 0)
{
obj* x_251; obj* x_253; obj* x_255; obj* x_257; uint32 x_258; obj* x_259; obj* x_260; obj* x_261; obj* x_263; obj* x_264; obj* x_266; obj* x_267; obj* x_268; 
x_251 = lean::cnstr_get(x_47, 0);
x_253 = lean::cnstr_get(x_47, 1);
x_255 = lean::cnstr_get(x_47, 2);
if (lean::is_exclusive(x_47)) {
 x_257 = x_47;
} else {
 lean::inc(x_251);
 lean::inc(x_253);
 lean::inc(x_255);
 lean::dec(x_47);
 x_257 = lean::box(0);
}
x_258 = lean::unbox_uint32(x_251);
x_259 = lean::uint32_to_nat(x_258);
x_260 = l_lean_parser_parse__hex__digit___rarg___lambda__3___closed__1;
x_261 = lean::nat_sub(x_259, x_260);
lean::dec(x_259);
x_263 = lean::mk_nat_obj(10u);
x_264 = lean::nat_add(x_263, x_261);
lean::dec(x_261);
x_266 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_257)) {
 x_267 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_267 = x_257;
}
lean::cnstr_set(x_267, 0, x_264);
lean::cnstr_set(x_267, 1, x_253);
lean::cnstr_set(x_267, 2, x_266);
x_268 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_255, x_267);
x_44 = x_268;
x_45 = x_48;
goto lbl_46;
}
else
{
obj* x_269; uint8 x_271; obj* x_272; obj* x_273; obj* x_274; 
x_269 = lean::cnstr_get(x_47, 0);
x_271 = lean::cnstr_get_scalar<uint8>(x_47, sizeof(void*)*1);
if (lean::is_exclusive(x_47)) {
 x_272 = x_47;
} else {
 lean::inc(x_269);
 lean::dec(x_47);
 x_272 = lean::box(0);
}
if (lean::is_scalar(x_272)) {
 x_273 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_273 = x_272;
}
lean::cnstr_set(x_273, 0, x_269);
lean::cnstr_set_scalar(x_273, sizeof(void*)*1, x_271);
x_274 = x_273;
x_44 = x_274;
x_45 = x_48;
goto lbl_46;
}
}
}
}
}
}
obj* l_lean_parser_parse__quoted__char___at_lean_parser_string__lit_x_27___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_5; 
lean::inc(x_1);
x_4 = l_lean_parser_monad__parsec_any___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__2(x_0, x_1, x_2);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
if (lean::obj_tag(x_5) == 0)
{
obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_14; obj* x_16; obj* x_17; obj* x_19; obj* x_21; uint32 x_23; uint32 x_24; uint8 x_25; 
x_7 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_set(x_4, 1, lean::box(0));
 x_9 = x_4;
} else {
 lean::inc(x_7);
 lean::dec(x_4);
 x_9 = lean::box(0);
}
x_10 = lean::cnstr_get(x_5, 0);
x_12 = lean::cnstr_get(x_5, 1);
x_14 = lean::cnstr_get(x_5, 2);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_set(x_5, 0, lean::box(0));
 lean::cnstr_set(x_5, 1, lean::box(0));
 lean::cnstr_set(x_5, 2, lean::box(0));
 x_16 = x_5;
} else {
 lean::inc(x_10);
 lean::inc(x_12);
 lean::inc(x_14);
 lean::dec(x_5);
 x_16 = lean::box(0);
}
x_23 = 92;
x_24 = lean::unbox_uint32(x_10);
x_25 = x_24 == x_23;
if (x_25 == 0)
{
obj* x_26; 
x_26 = lean::box(0);
x_21 = x_26;
goto lbl_22;
}
else
{
obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; 
lean::dec(x_16);
lean::dec(x_9);
lean::dec(x_1);
x_30 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_31 = lean::box_uint32(x_23);
x_32 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_12);
lean::cnstr_set(x_32, 2, x_30);
x_33 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_14, x_32);
x_34 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_30, x_33);
x_35 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_7);
return x_35;
}
lbl_18:
{
uint32 x_37; uint32 x_38; uint8 x_39; 
lean::dec(x_17);
x_37 = 117;
x_38 = lean::unbox_uint32(x_10);
x_39 = x_38 == x_37;
if (x_39 == 0)
{
obj* x_40; obj* x_41; obj* x_43; obj* x_45; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; 
x_40 = l_lean_parser_parse__quoted__char___rarg___lambda__7___closed__1;
x_41 = l_lean_parser_monad__parsec_unexpected__at___at_lean_parser_string__lit_x_27___spec__4___rarg(x_40, x_1, x_0, x_12, x_7);
lean::dec(x_12);
x_43 = lean::cnstr_get(x_41, 0);
x_45 = lean::cnstr_get(x_41, 1);
if (lean::is_exclusive(x_41)) {
 x_47 = x_41;
} else {
 lean::inc(x_43);
 lean::inc(x_45);
 lean::dec(x_41);
 x_47 = lean::box(0);
}
x_48 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_14, x_43);
x_49 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_50 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_49, x_48);
if (lean::is_scalar(x_47)) {
 x_51 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_51 = x_47;
}
lean::cnstr_set(x_51, 0, x_50);
lean::cnstr_set(x_51, 1, x_45);
return x_51;
}
else
{
obj* x_53; obj* x_54; 
lean::dec(x_1);
x_53 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__5(x_0, x_12, x_7);
x_54 = lean::cnstr_get(x_53, 0);
lean::inc(x_54);
if (lean::obj_tag(x_54) == 0)
{
obj* x_56; obj* x_59; obj* x_61; obj* x_63; obj* x_66; obj* x_67; 
x_56 = lean::cnstr_get(x_53, 1);
lean::inc(x_56);
lean::dec(x_53);
x_59 = lean::cnstr_get(x_54, 0);
lean::inc(x_59);
x_61 = lean::cnstr_get(x_54, 1);
lean::inc(x_61);
x_63 = lean::cnstr_get(x_54, 2);
lean::inc(x_63);
lean::dec(x_54);
x_66 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__5(x_0, x_61, x_56);
x_67 = lean::cnstr_get(x_66, 0);
lean::inc(x_67);
if (lean::obj_tag(x_67) == 0)
{
obj* x_69; obj* x_72; obj* x_74; obj* x_76; obj* x_79; obj* x_80; 
x_69 = lean::cnstr_get(x_66, 1);
lean::inc(x_69);
lean::dec(x_66);
x_72 = lean::cnstr_get(x_67, 0);
lean::inc(x_72);
x_74 = lean::cnstr_get(x_67, 1);
lean::inc(x_74);
x_76 = lean::cnstr_get(x_67, 2);
lean::inc(x_76);
lean::dec(x_67);
x_79 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__5(x_0, x_74, x_69);
x_80 = lean::cnstr_get(x_79, 0);
lean::inc(x_80);
if (lean::obj_tag(x_80) == 0)
{
obj* x_82; obj* x_85; obj* x_87; obj* x_89; obj* x_92; obj* x_93; 
x_82 = lean::cnstr_get(x_79, 1);
lean::inc(x_82);
lean::dec(x_79);
x_85 = lean::cnstr_get(x_80, 0);
lean::inc(x_85);
x_87 = lean::cnstr_get(x_80, 1);
lean::inc(x_87);
x_89 = lean::cnstr_get(x_80, 2);
lean::inc(x_89);
lean::dec(x_80);
x_92 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__5(x_0, x_87, x_82);
x_93 = lean::cnstr_get(x_92, 0);
lean::inc(x_93);
if (lean::obj_tag(x_93) == 0)
{
obj* x_95; obj* x_97; obj* x_98; obj* x_100; obj* x_102; obj* x_104; obj* x_105; obj* x_106; obj* x_108; obj* x_111; obj* x_113; obj* x_116; obj* x_118; uint32 x_121; obj* x_123; obj* x_124; obj* x_125; obj* x_126; obj* x_127; obj* x_128; obj* x_129; obj* x_130; obj* x_131; obj* x_132; 
x_95 = lean::cnstr_get(x_92, 1);
if (lean::is_exclusive(x_92)) {
 lean::cnstr_release(x_92, 0);
 x_97 = x_92;
} else {
 lean::inc(x_95);
 lean::dec(x_92);
 x_97 = lean::box(0);
}
x_98 = lean::cnstr_get(x_93, 0);
x_100 = lean::cnstr_get(x_93, 1);
x_102 = lean::cnstr_get(x_93, 2);
if (lean::is_exclusive(x_93)) {
 x_104 = x_93;
} else {
 lean::inc(x_98);
 lean::inc(x_100);
 lean::inc(x_102);
 lean::dec(x_93);
 x_104 = lean::box(0);
}
x_105 = lean::mk_nat_obj(16u);
x_106 = lean::nat_mul(x_105, x_59);
lean::dec(x_59);
x_108 = lean::nat_add(x_106, x_72);
lean::dec(x_72);
lean::dec(x_106);
x_111 = lean::nat_mul(x_105, x_108);
lean::dec(x_108);
x_113 = lean::nat_add(x_111, x_85);
lean::dec(x_85);
lean::dec(x_111);
x_116 = lean::nat_mul(x_105, x_113);
lean::dec(x_113);
x_118 = lean::nat_add(x_116, x_98);
lean::dec(x_98);
lean::dec(x_116);
x_121 = l_char_of__nat(x_118);
lean::dec(x_118);
x_123 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_124 = lean::box_uint32(x_121);
if (lean::is_scalar(x_104)) {
 x_125 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_125 = x_104;
}
lean::cnstr_set(x_125, 0, x_124);
lean::cnstr_set(x_125, 1, x_100);
lean::cnstr_set(x_125, 2, x_123);
x_126 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_102, x_125);
x_127 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_89, x_126);
x_128 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_76, x_127);
x_129 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_63, x_128);
x_130 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_14, x_129);
x_131 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_123, x_130);
if (lean::is_scalar(x_97)) {
 x_132 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_132 = x_97;
}
lean::cnstr_set(x_132, 0, x_131);
lean::cnstr_set(x_132, 1, x_95);
return x_132;
}
else
{
obj* x_136; obj* x_138; obj* x_139; uint8 x_141; obj* x_142; obj* x_143; obj* x_144; obj* x_145; obj* x_146; obj* x_147; obj* x_148; obj* x_149; obj* x_150; obj* x_151; 
lean::dec(x_72);
lean::dec(x_59);
lean::dec(x_85);
x_136 = lean::cnstr_get(x_92, 1);
if (lean::is_exclusive(x_92)) {
 lean::cnstr_release(x_92, 0);
 x_138 = x_92;
} else {
 lean::inc(x_136);
 lean::dec(x_92);
 x_138 = lean::box(0);
}
x_139 = lean::cnstr_get(x_93, 0);
x_141 = lean::cnstr_get_scalar<uint8>(x_93, sizeof(void*)*1);
if (lean::is_exclusive(x_93)) {
 x_142 = x_93;
} else {
 lean::inc(x_139);
 lean::dec(x_93);
 x_142 = lean::box(0);
}
if (lean::is_scalar(x_142)) {
 x_143 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_143 = x_142;
}
lean::cnstr_set(x_143, 0, x_139);
lean::cnstr_set_scalar(x_143, sizeof(void*)*1, x_141);
x_144 = x_143;
x_145 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_89, x_144);
x_146 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_76, x_145);
x_147 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_63, x_146);
x_148 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_14, x_147);
x_149 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_150 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_149, x_148);
if (lean::is_scalar(x_138)) {
 x_151 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_151 = x_138;
}
lean::cnstr_set(x_151, 0, x_150);
lean::cnstr_set(x_151, 1, x_136);
return x_151;
}
}
else
{
obj* x_154; obj* x_156; obj* x_157; uint8 x_159; obj* x_160; obj* x_161; obj* x_162; obj* x_163; obj* x_164; obj* x_165; obj* x_166; obj* x_167; obj* x_168; 
lean::dec(x_72);
lean::dec(x_59);
x_154 = lean::cnstr_get(x_79, 1);
if (lean::is_exclusive(x_79)) {
 lean::cnstr_release(x_79, 0);
 x_156 = x_79;
} else {
 lean::inc(x_154);
 lean::dec(x_79);
 x_156 = lean::box(0);
}
x_157 = lean::cnstr_get(x_80, 0);
x_159 = lean::cnstr_get_scalar<uint8>(x_80, sizeof(void*)*1);
if (lean::is_exclusive(x_80)) {
 x_160 = x_80;
} else {
 lean::inc(x_157);
 lean::dec(x_80);
 x_160 = lean::box(0);
}
if (lean::is_scalar(x_160)) {
 x_161 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_161 = x_160;
}
lean::cnstr_set(x_161, 0, x_157);
lean::cnstr_set_scalar(x_161, sizeof(void*)*1, x_159);
x_162 = x_161;
x_163 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_76, x_162);
x_164 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_63, x_163);
x_165 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_14, x_164);
x_166 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_167 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_166, x_165);
if (lean::is_scalar(x_156)) {
 x_168 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_168 = x_156;
}
lean::cnstr_set(x_168, 0, x_167);
lean::cnstr_set(x_168, 1, x_154);
return x_168;
}
}
else
{
obj* x_170; obj* x_172; obj* x_173; uint8 x_175; obj* x_176; obj* x_177; obj* x_178; obj* x_179; obj* x_180; obj* x_181; obj* x_182; obj* x_183; 
lean::dec(x_59);
x_170 = lean::cnstr_get(x_66, 1);
if (lean::is_exclusive(x_66)) {
 lean::cnstr_release(x_66, 0);
 x_172 = x_66;
} else {
 lean::inc(x_170);
 lean::dec(x_66);
 x_172 = lean::box(0);
}
x_173 = lean::cnstr_get(x_67, 0);
x_175 = lean::cnstr_get_scalar<uint8>(x_67, sizeof(void*)*1);
if (lean::is_exclusive(x_67)) {
 x_176 = x_67;
} else {
 lean::inc(x_173);
 lean::dec(x_67);
 x_176 = lean::box(0);
}
if (lean::is_scalar(x_176)) {
 x_177 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_177 = x_176;
}
lean::cnstr_set(x_177, 0, x_173);
lean::cnstr_set_scalar(x_177, sizeof(void*)*1, x_175);
x_178 = x_177;
x_179 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_63, x_178);
x_180 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_14, x_179);
x_181 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_182 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_181, x_180);
if (lean::is_scalar(x_172)) {
 x_183 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_183 = x_172;
}
lean::cnstr_set(x_183, 0, x_182);
lean::cnstr_set(x_183, 1, x_170);
return x_183;
}
}
else
{
obj* x_184; obj* x_186; obj* x_187; uint8 x_189; obj* x_190; obj* x_191; obj* x_192; obj* x_193; obj* x_194; obj* x_195; obj* x_196; 
x_184 = lean::cnstr_get(x_53, 1);
if (lean::is_exclusive(x_53)) {
 lean::cnstr_release(x_53, 0);
 x_186 = x_53;
} else {
 lean::inc(x_184);
 lean::dec(x_53);
 x_186 = lean::box(0);
}
x_187 = lean::cnstr_get(x_54, 0);
x_189 = lean::cnstr_get_scalar<uint8>(x_54, sizeof(void*)*1);
if (lean::is_exclusive(x_54)) {
 x_190 = x_54;
} else {
 lean::inc(x_187);
 lean::dec(x_54);
 x_190 = lean::box(0);
}
if (lean::is_scalar(x_190)) {
 x_191 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_191 = x_190;
}
lean::cnstr_set(x_191, 0, x_187);
lean::cnstr_set_scalar(x_191, sizeof(void*)*1, x_189);
x_192 = x_191;
x_193 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_14, x_192);
x_194 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_195 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_194, x_193);
if (lean::is_scalar(x_186)) {
 x_196 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_196 = x_186;
}
lean::cnstr_set(x_196, 0, x_195);
lean::cnstr_set(x_196, 1, x_184);
return x_196;
}
}
}
lbl_20:
{
uint32 x_198; uint32 x_199; uint8 x_200; 
lean::dec(x_19);
x_198 = 116;
x_199 = lean::unbox_uint32(x_10);
x_200 = x_199 == x_198;
if (x_200 == 0)
{
uint32 x_203; uint8 x_204; 
lean::dec(x_16);
lean::dec(x_9);
x_203 = 120;
x_204 = x_199 == x_203;
if (x_204 == 0)
{
obj* x_205; 
x_205 = lean::box(0);
x_17 = x_205;
goto lbl_18;
}
else
{
obj* x_207; obj* x_208; 
lean::dec(x_1);
x_207 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__5(x_0, x_12, x_7);
x_208 = lean::cnstr_get(x_207, 0);
lean::inc(x_208);
if (lean::obj_tag(x_208) == 0)
{
obj* x_210; obj* x_213; obj* x_215; obj* x_217; obj* x_220; obj* x_221; 
x_210 = lean::cnstr_get(x_207, 1);
lean::inc(x_210);
lean::dec(x_207);
x_213 = lean::cnstr_get(x_208, 0);
lean::inc(x_213);
x_215 = lean::cnstr_get(x_208, 1);
lean::inc(x_215);
x_217 = lean::cnstr_get(x_208, 2);
lean::inc(x_217);
lean::dec(x_208);
x_220 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__5(x_0, x_215, x_210);
x_221 = lean::cnstr_get(x_220, 0);
lean::inc(x_221);
if (lean::obj_tag(x_221) == 0)
{
obj* x_223; obj* x_225; obj* x_226; obj* x_228; obj* x_230; obj* x_232; obj* x_233; obj* x_234; obj* x_236; uint32 x_239; obj* x_241; obj* x_242; obj* x_243; obj* x_244; obj* x_245; obj* x_246; obj* x_247; obj* x_248; 
x_223 = lean::cnstr_get(x_220, 1);
if (lean::is_exclusive(x_220)) {
 lean::cnstr_release(x_220, 0);
 x_225 = x_220;
} else {
 lean::inc(x_223);
 lean::dec(x_220);
 x_225 = lean::box(0);
}
x_226 = lean::cnstr_get(x_221, 0);
x_228 = lean::cnstr_get(x_221, 1);
x_230 = lean::cnstr_get(x_221, 2);
if (lean::is_exclusive(x_221)) {
 x_232 = x_221;
} else {
 lean::inc(x_226);
 lean::inc(x_228);
 lean::inc(x_230);
 lean::dec(x_221);
 x_232 = lean::box(0);
}
x_233 = lean::mk_nat_obj(16u);
x_234 = lean::nat_mul(x_233, x_213);
lean::dec(x_213);
x_236 = lean::nat_add(x_234, x_226);
lean::dec(x_226);
lean::dec(x_234);
x_239 = l_char_of__nat(x_236);
lean::dec(x_236);
x_241 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_242 = lean::box_uint32(x_239);
if (lean::is_scalar(x_232)) {
 x_243 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_243 = x_232;
}
lean::cnstr_set(x_243, 0, x_242);
lean::cnstr_set(x_243, 1, x_228);
lean::cnstr_set(x_243, 2, x_241);
x_244 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_230, x_243);
x_245 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_217, x_244);
x_246 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_14, x_245);
x_247 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_241, x_246);
if (lean::is_scalar(x_225)) {
 x_248 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_248 = x_225;
}
lean::cnstr_set(x_248, 0, x_247);
lean::cnstr_set(x_248, 1, x_223);
return x_248;
}
else
{
obj* x_250; obj* x_252; obj* x_253; uint8 x_255; obj* x_256; obj* x_257; obj* x_258; obj* x_259; obj* x_260; obj* x_261; obj* x_262; obj* x_263; 
lean::dec(x_213);
x_250 = lean::cnstr_get(x_220, 1);
if (lean::is_exclusive(x_220)) {
 lean::cnstr_release(x_220, 0);
 x_252 = x_220;
} else {
 lean::inc(x_250);
 lean::dec(x_220);
 x_252 = lean::box(0);
}
x_253 = lean::cnstr_get(x_221, 0);
x_255 = lean::cnstr_get_scalar<uint8>(x_221, sizeof(void*)*1);
if (lean::is_exclusive(x_221)) {
 x_256 = x_221;
} else {
 lean::inc(x_253);
 lean::dec(x_221);
 x_256 = lean::box(0);
}
if (lean::is_scalar(x_256)) {
 x_257 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_257 = x_256;
}
lean::cnstr_set(x_257, 0, x_253);
lean::cnstr_set_scalar(x_257, sizeof(void*)*1, x_255);
x_258 = x_257;
x_259 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_217, x_258);
x_260 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_14, x_259);
x_261 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_262 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_261, x_260);
if (lean::is_scalar(x_252)) {
 x_263 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_263 = x_252;
}
lean::cnstr_set(x_263, 0, x_262);
lean::cnstr_set(x_263, 1, x_250);
return x_263;
}
}
else
{
obj* x_264; obj* x_266; obj* x_267; uint8 x_269; obj* x_270; obj* x_271; obj* x_272; obj* x_273; obj* x_274; obj* x_275; obj* x_276; 
x_264 = lean::cnstr_get(x_207, 1);
if (lean::is_exclusive(x_207)) {
 lean::cnstr_release(x_207, 0);
 x_266 = x_207;
} else {
 lean::inc(x_264);
 lean::dec(x_207);
 x_266 = lean::box(0);
}
x_267 = lean::cnstr_get(x_208, 0);
x_269 = lean::cnstr_get_scalar<uint8>(x_208, sizeof(void*)*1);
if (lean::is_exclusive(x_208)) {
 x_270 = x_208;
} else {
 lean::inc(x_267);
 lean::dec(x_208);
 x_270 = lean::box(0);
}
if (lean::is_scalar(x_270)) {
 x_271 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_271 = x_270;
}
lean::cnstr_set(x_271, 0, x_267);
lean::cnstr_set_scalar(x_271, sizeof(void*)*1, x_269);
x_272 = x_271;
x_273 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_14, x_272);
x_274 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_275 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_274, x_273);
if (lean::is_scalar(x_266)) {
 x_276 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_276 = x_266;
}
lean::cnstr_set(x_276, 0, x_275);
lean::cnstr_set(x_276, 1, x_264);
return x_276;
}
}
}
else
{
uint32 x_278; obj* x_279; obj* x_280; obj* x_281; obj* x_282; obj* x_283; obj* x_284; 
lean::dec(x_1);
x_278 = 9;
x_279 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_280 = lean::box_uint32(x_278);
if (lean::is_scalar(x_16)) {
 x_281 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_281 = x_16;
}
lean::cnstr_set(x_281, 0, x_280);
lean::cnstr_set(x_281, 1, x_12);
lean::cnstr_set(x_281, 2, x_279);
x_282 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_14, x_281);
x_283 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_279, x_282);
if (lean::is_scalar(x_9)) {
 x_284 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_284 = x_9;
}
lean::cnstr_set(x_284, 0, x_283);
lean::cnstr_set(x_284, 1, x_7);
return x_284;
}
}
lbl_22:
{
uint32 x_286; uint32 x_287; uint8 x_288; 
lean::dec(x_21);
x_286 = 34;
x_287 = lean::unbox_uint32(x_10);
x_288 = x_287 == x_286;
if (x_288 == 0)
{
uint32 x_289; uint8 x_290; 
x_289 = 39;
x_290 = x_287 == x_289;
if (x_290 == 0)
{
uint32 x_291; uint8 x_292; 
x_291 = 110;
x_292 = x_287 == x_291;
if (x_292 == 0)
{
obj* x_293; 
x_293 = lean::box(0);
x_19 = x_293;
goto lbl_20;
}
else
{
uint32 x_297; obj* x_298; obj* x_299; obj* x_300; obj* x_301; obj* x_302; obj* x_303; 
lean::dec(x_16);
lean::dec(x_9);
lean::dec(x_1);
x_297 = 10;
x_298 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_299 = lean::box_uint32(x_297);
x_300 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_300, 0, x_299);
lean::cnstr_set(x_300, 1, x_12);
lean::cnstr_set(x_300, 2, x_298);
x_301 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_14, x_300);
x_302 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_298, x_301);
x_303 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_303, 0, x_302);
lean::cnstr_set(x_303, 1, x_7);
return x_303;
}
}
else
{
obj* x_307; obj* x_308; obj* x_309; obj* x_310; obj* x_311; obj* x_312; 
lean::dec(x_16);
lean::dec(x_9);
lean::dec(x_1);
x_307 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_308 = lean::box_uint32(x_289);
x_309 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_309, 0, x_308);
lean::cnstr_set(x_309, 1, x_12);
lean::cnstr_set(x_309, 2, x_307);
x_310 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_14, x_309);
x_311 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_307, x_310);
x_312 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_312, 0, x_311);
lean::cnstr_set(x_312, 1, x_7);
return x_312;
}
}
else
{
obj* x_316; obj* x_317; obj* x_318; obj* x_319; obj* x_320; obj* x_321; 
lean::dec(x_16);
lean::dec(x_9);
lean::dec(x_1);
x_316 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_317 = lean::box_uint32(x_286);
x_318 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_318, 0, x_317);
lean::cnstr_set(x_318, 1, x_12);
lean::cnstr_set(x_318, 2, x_316);
x_319 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_14, x_318);
x_320 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_316, x_319);
x_321 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_321, 0, x_320);
lean::cnstr_set(x_321, 1, x_7);
return x_321;
}
}
}
else
{
obj* x_323; obj* x_325; obj* x_326; uint8 x_328; obj* x_329; obj* x_330; obj* x_331; obj* x_332; obj* x_333; obj* x_334; 
lean::dec(x_1);
x_323 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_325 = x_4;
} else {
 lean::inc(x_323);
 lean::dec(x_4);
 x_325 = lean::box(0);
}
x_326 = lean::cnstr_get(x_5, 0);
x_328 = lean::cnstr_get_scalar<uint8>(x_5, sizeof(void*)*1);
if (lean::is_exclusive(x_5)) {
 x_329 = x_5;
} else {
 lean::inc(x_326);
 lean::dec(x_5);
 x_329 = lean::box(0);
}
if (lean::is_scalar(x_329)) {
 x_330 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_330 = x_329;
}
lean::cnstr_set(x_330, 0, x_326);
lean::cnstr_set_scalar(x_330, sizeof(void*)*1, x_328);
x_331 = x_330;
x_332 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_333 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_332, x_331);
if (lean::is_scalar(x_325)) {
 x_334 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_334 = x_325;
}
lean::cnstr_set(x_334, 0, x_333);
lean::cnstr_set(x_334, 1, x_323);
return x_334;
}
}
}
obj* l_lean_parser_parse__string__literal__aux___main___at_lean_parser_string__lit_x_27___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::mk_nat_obj(0u);
x_6 = lean::nat_dec_eq(x_0, x_5);
if (x_6 == 0)
{
obj* x_7; obj* x_8; 
x_7 = l_lean_parser_monad__parsec_any___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__2(x_2, x_3, x_4);
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
if (lean::obj_tag(x_8) == 0)
{
obj* x_10; obj* x_12; obj* x_13; obj* x_15; obj* x_17; obj* x_19; obj* x_20; obj* x_21; uint32 x_22; uint32 x_23; uint8 x_24; 
x_10 = lean::cnstr_get(x_7, 1);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 lean::cnstr_set(x_7, 1, lean::box(0));
 x_12 = x_7;
} else {
 lean::inc(x_10);
 lean::dec(x_7);
 x_12 = lean::box(0);
}
x_13 = lean::cnstr_get(x_8, 0);
x_15 = lean::cnstr_get(x_8, 1);
x_17 = lean::cnstr_get(x_8, 2);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_set(x_8, 0, lean::box(0));
 lean::cnstr_set(x_8, 1, lean::box(0));
 lean::cnstr_set(x_8, 2, lean::box(0));
 x_19 = x_8;
} else {
 lean::inc(x_13);
 lean::inc(x_15);
 lean::inc(x_17);
 lean::dec(x_8);
 x_19 = lean::box(0);
}
x_20 = lean::mk_nat_obj(1u);
x_21 = lean::nat_sub(x_0, x_20);
x_22 = 92;
x_23 = lean::unbox_uint32(x_13);
x_24 = x_23 == x_22;
if (x_24 == 0)
{
uint32 x_25; uint8 x_26; 
x_25 = 34;
x_26 = x_23 == x_25;
if (x_26 == 0)
{
obj* x_29; obj* x_30; obj* x_32; obj* x_34; obj* x_36; obj* x_37; obj* x_38; 
lean::dec(x_19);
lean::dec(x_12);
x_29 = lean::string_push(x_1, x_23);
x_30 = l_lean_parser_parse__string__literal__aux___main___at_lean_parser_string__lit_x_27___spec__2(x_21, x_29, x_2, x_15, x_10);
lean::dec(x_21);
x_32 = lean::cnstr_get(x_30, 0);
x_34 = lean::cnstr_get(x_30, 1);
if (lean::is_exclusive(x_30)) {
 x_36 = x_30;
} else {
 lean::inc(x_32);
 lean::inc(x_34);
 lean::dec(x_30);
 x_36 = lean::box(0);
}
x_37 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_17, x_32);
if (lean::is_scalar(x_36)) {
 x_38 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_38 = x_36;
}
lean::cnstr_set(x_38, 0, x_37);
lean::cnstr_set(x_38, 1, x_34);
return x_38;
}
else
{
obj* x_40; obj* x_41; obj* x_42; obj* x_43; 
lean::dec(x_21);
x_40 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_19)) {
 x_41 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_41 = x_19;
}
lean::cnstr_set(x_41, 0, x_1);
lean::cnstr_set(x_41, 1, x_15);
lean::cnstr_set(x_41, 2, x_40);
x_42 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_17, x_41);
if (lean::is_scalar(x_12)) {
 x_43 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_43 = x_12;
}
lean::cnstr_set(x_43, 0, x_42);
lean::cnstr_set(x_43, 1, x_10);
return x_43;
}
}
else
{
obj* x_46; obj* x_47; 
lean::dec(x_19);
lean::dec(x_12);
x_46 = l_lean_parser_parse__quoted__char___at_lean_parser_string__lit_x_27___spec__3(x_2, x_15, x_10);
x_47 = lean::cnstr_get(x_46, 0);
lean::inc(x_47);
if (lean::obj_tag(x_47) == 0)
{
obj* x_49; obj* x_52; obj* x_54; obj* x_56; uint32 x_59; obj* x_60; obj* x_61; obj* x_63; obj* x_65; obj* x_67; obj* x_68; obj* x_69; obj* x_70; 
x_49 = lean::cnstr_get(x_46, 1);
lean::inc(x_49);
lean::dec(x_46);
x_52 = lean::cnstr_get(x_47, 0);
lean::inc(x_52);
x_54 = lean::cnstr_get(x_47, 1);
lean::inc(x_54);
x_56 = lean::cnstr_get(x_47, 2);
lean::inc(x_56);
lean::dec(x_47);
x_59 = lean::unbox_uint32(x_52);
x_60 = lean::string_push(x_1, x_59);
x_61 = l_lean_parser_parse__string__literal__aux___main___at_lean_parser_string__lit_x_27___spec__2(x_21, x_60, x_2, x_54, x_49);
lean::dec(x_21);
x_63 = lean::cnstr_get(x_61, 0);
x_65 = lean::cnstr_get(x_61, 1);
if (lean::is_exclusive(x_61)) {
 x_67 = x_61;
} else {
 lean::inc(x_63);
 lean::inc(x_65);
 lean::dec(x_61);
 x_67 = lean::box(0);
}
x_68 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_56, x_63);
x_69 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_17, x_68);
if (lean::is_scalar(x_67)) {
 x_70 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_70 = x_67;
}
lean::cnstr_set(x_70, 0, x_69);
lean::cnstr_set(x_70, 1, x_65);
return x_70;
}
else
{
obj* x_73; obj* x_75; obj* x_76; uint8 x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; 
lean::dec(x_1);
lean::dec(x_21);
x_73 = lean::cnstr_get(x_46, 1);
if (lean::is_exclusive(x_46)) {
 lean::cnstr_release(x_46, 0);
 x_75 = x_46;
} else {
 lean::inc(x_73);
 lean::dec(x_46);
 x_75 = lean::box(0);
}
x_76 = lean::cnstr_get(x_47, 0);
x_78 = lean::cnstr_get_scalar<uint8>(x_47, sizeof(void*)*1);
if (lean::is_exclusive(x_47)) {
 x_79 = x_47;
} else {
 lean::inc(x_76);
 lean::dec(x_47);
 x_79 = lean::box(0);
}
if (lean::is_scalar(x_79)) {
 x_80 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_80 = x_79;
}
lean::cnstr_set(x_80, 0, x_76);
lean::cnstr_set_scalar(x_80, sizeof(void*)*1, x_78);
x_81 = x_80;
x_82 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_17, x_81);
if (lean::is_scalar(x_75)) {
 x_83 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_83 = x_75;
}
lean::cnstr_set(x_83, 0, x_82);
lean::cnstr_set(x_83, 1, x_73);
return x_83;
}
}
}
else
{
obj* x_85; obj* x_87; obj* x_88; uint8 x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; 
lean::dec(x_1);
x_85 = lean::cnstr_get(x_7, 1);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 x_87 = x_7;
} else {
 lean::inc(x_85);
 lean::dec(x_7);
 x_87 = lean::box(0);
}
x_88 = lean::cnstr_get(x_8, 0);
x_90 = lean::cnstr_get_scalar<uint8>(x_8, sizeof(void*)*1);
if (lean::is_exclusive(x_8)) {
 x_91 = x_8;
} else {
 lean::inc(x_88);
 lean::dec(x_8);
 x_91 = lean::box(0);
}
if (lean::is_scalar(x_91)) {
 x_92 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_92 = x_91;
}
lean::cnstr_set(x_92, 0, x_88);
lean::cnstr_set_scalar(x_92, sizeof(void*)*1, x_90);
x_93 = x_92;
if (lean::is_scalar(x_87)) {
 x_94 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_94 = x_87;
}
lean::cnstr_set(x_94, 0, x_93);
lean::cnstr_set(x_94, 1, x_85);
return x_94;
}
}
else
{
uint32 x_95; obj* x_96; obj* x_97; 
x_95 = 34;
x_96 = l_lean_parser_monad__parsec_ch___at___private_init_lean_parser_token_4__ident_x_27___spec__11(x_95, x_2, x_3, x_4);
x_97 = lean::cnstr_get(x_96, 0);
lean::inc(x_97);
if (lean::obj_tag(x_97) == 0)
{
obj* x_99; obj* x_101; obj* x_102; obj* x_104; obj* x_106; obj* x_107; obj* x_108; obj* x_109; obj* x_110; 
x_99 = lean::cnstr_get(x_96, 1);
if (lean::is_exclusive(x_96)) {
 lean::cnstr_release(x_96, 0);
 x_101 = x_96;
} else {
 lean::inc(x_99);
 lean::dec(x_96);
 x_101 = lean::box(0);
}
x_102 = lean::cnstr_get(x_97, 1);
x_104 = lean::cnstr_get(x_97, 2);
if (lean::is_exclusive(x_97)) {
 lean::cnstr_release(x_97, 0);
 x_106 = x_97;
} else {
 lean::inc(x_102);
 lean::inc(x_104);
 lean::dec(x_97);
 x_106 = lean::box(0);
}
x_107 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_106)) {
 x_108 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_108 = x_106;
}
lean::cnstr_set(x_108, 0, x_1);
lean::cnstr_set(x_108, 1, x_102);
lean::cnstr_set(x_108, 2, x_107);
x_109 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_104, x_108);
if (lean::is_scalar(x_101)) {
 x_110 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_110 = x_101;
}
lean::cnstr_set(x_110, 0, x_109);
lean::cnstr_set(x_110, 1, x_99);
return x_110;
}
else
{
obj* x_112; obj* x_114; obj* x_115; uint8 x_117; obj* x_118; obj* x_119; obj* x_120; obj* x_121; 
lean::dec(x_1);
x_112 = lean::cnstr_get(x_96, 1);
if (lean::is_exclusive(x_96)) {
 lean::cnstr_release(x_96, 0);
 x_114 = x_96;
} else {
 lean::inc(x_112);
 lean::dec(x_96);
 x_114 = lean::box(0);
}
x_115 = lean::cnstr_get(x_97, 0);
x_117 = lean::cnstr_get_scalar<uint8>(x_97, sizeof(void*)*1);
if (lean::is_exclusive(x_97)) {
 x_118 = x_97;
} else {
 lean::inc(x_115);
 lean::dec(x_97);
 x_118 = lean::box(0);
}
if (lean::is_scalar(x_118)) {
 x_119 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_119 = x_118;
}
lean::cnstr_set(x_119, 0, x_115);
lean::cnstr_set_scalar(x_119, sizeof(void*)*1, x_117);
x_120 = x_119;
if (lean::is_scalar(x_114)) {
 x_121 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_121 = x_114;
}
lean::cnstr_set(x_121, 0, x_120);
lean::cnstr_set(x_121, 1, x_112);
return x_121;
}
}
}
}
obj* l_lean_parser_parse__string__literal___at_lean_parser_string__lit_x_27___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint32 x_3; obj* x_4; obj* x_5; 
x_3 = 34;
x_4 = l_lean_parser_monad__parsec_ch___at___private_init_lean_parser_token_4__ident_x_27___spec__11(x_3, x_0, x_1, x_2);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
if (lean::obj_tag(x_5) == 0)
{
obj* x_7; obj* x_10; obj* x_12; obj* x_15; obj* x_16; obj* x_17; obj* x_19; obj* x_21; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; 
x_7 = lean::cnstr_get(x_4, 1);
lean::inc(x_7);
lean::dec(x_4);
x_10 = lean::cnstr_get(x_5, 1);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_5, 2);
lean::inc(x_12);
lean::dec(x_5);
x_15 = lean::string_iterator_remaining(x_10);
x_16 = l_string_join___closed__1;
x_17 = l_lean_parser_parse__string__literal__aux___main___at_lean_parser_string__lit_x_27___spec__2(x_15, x_16, x_0, x_10, x_7);
lean::dec(x_15);
x_19 = lean::cnstr_get(x_17, 0);
x_21 = lean::cnstr_get(x_17, 1);
if (lean::is_exclusive(x_17)) {
 x_23 = x_17;
} else {
 lean::inc(x_19);
 lean::inc(x_21);
 lean::dec(x_17);
 x_23 = lean::box(0);
}
x_24 = l_lean_parser_finish__comment__block___closed__2;
x_25 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_24, x_19);
x_26 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_12, x_25);
if (lean::is_scalar(x_23)) {
 x_27 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_27 = x_23;
}
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_21);
return x_27;
}
else
{
obj* x_28; obj* x_30; obj* x_31; uint8 x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; 
x_28 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_30 = x_4;
} else {
 lean::inc(x_28);
 lean::dec(x_4);
 x_30 = lean::box(0);
}
x_31 = lean::cnstr_get(x_5, 0);
x_33 = lean::cnstr_get_scalar<uint8>(x_5, sizeof(void*)*1);
if (lean::is_exclusive(x_5)) {
 x_34 = x_5;
} else {
 lean::inc(x_31);
 lean::dec(x_5);
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
return x_37;
}
}
}
obj* l_lean_parser_string__lit_x_27___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = l_lean_parser_parse__string__literal___at_lean_parser_string__lit_x_27___spec__1(x_1, x_2, x_3);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
if (lean::obj_tag(x_5) == 0)
{
obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_14; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_7 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_9 = x_4;
} else {
 lean::inc(x_7);
 lean::dec(x_4);
 x_9 = lean::box(0);
}
x_10 = lean::cnstr_get(x_5, 1);
x_12 = lean::cnstr_get(x_5, 2);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 x_14 = x_5;
} else {
 lean::inc(x_10);
 lean::inc(x_12);
 lean::dec(x_5);
 x_14 = lean::box(0);
}
lean::inc(x_10);
x_16 = l_lean_parser_mk__raw__res(x_0, x_10);
x_17 = l_lean_parser_finish__comment__block___closed__2;
if (lean::is_scalar(x_14)) {
 x_18 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_18 = x_14;
}
lean::cnstr_set(x_18, 0, x_16);
lean::cnstr_set(x_18, 1, x_10);
lean::cnstr_set(x_18, 2, x_17);
x_19 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_12, x_18);
if (lean::is_scalar(x_9)) {
 x_20 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_20 = x_9;
}
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_7);
return x_20;
}
else
{
obj* x_22; obj* x_24; obj* x_25; uint8 x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; 
lean::dec(x_0);
x_22 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_24 = x_4;
} else {
 lean::inc(x_22);
 lean::dec(x_4);
 x_24 = lean::box(0);
}
x_25 = lean::cnstr_get(x_5, 0);
x_27 = lean::cnstr_get_scalar<uint8>(x_5, sizeof(void*)*1);
if (lean::is_exclusive(x_5)) {
 x_28 = x_5;
} else {
 lean::inc(x_25);
 lean::dec(x_5);
 x_28 = lean::box(0);
}
if (lean::is_scalar(x_28)) {
 x_29 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_29 = x_28;
}
lean::cnstr_set(x_29, 0, x_25);
lean::cnstr_set_scalar(x_29, sizeof(void*)*1, x_27);
x_30 = x_29;
if (lean::is_scalar(x_24)) {
 x_31 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_31 = x_24;
}
lean::cnstr_set(x_31, 0, x_30);
lean::cnstr_set(x_31, 1, x_22);
return x_31;
}
}
}
obj* _init_l_lean_parser_string__lit_x_27___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_with__trailing___rarg___lambda__1), 2, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_lift___at_lean_parser_with__trailing___spec__1___rarg___boxed), 4, 1);
lean::closure_set(x_1, 0, x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_string__lit_x_27___lambda__1___boxed), 4, 0);
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
obj* x_3; obj* x_4; obj* x_5; 
x_3 = l_lean_parser_string__lit;
x_4 = l_lean_parser_string__lit_x_27___closed__1;
x_5 = l_lean_parser_combinators_node___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__15(x_3, x_4, x_0, x_1, x_2);
return x_5;
}
}
obj* l_lean_parser_monad__parsec_unexpected__at___at_lean_parser_string__lit_x_27___spec__4___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_lean_parser_monad__parsec_unexpected__at___at_lean_parser_string__lit_x_27___spec__4___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_2);
lean::dec(x_3);
return x_5;
}
}
obj* l_lean_parser_monad__parsec_unexpected__at___at_lean_parser_string__lit_x_27___spec__4___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_monad__parsec_unexpected__at___at_lean_parser_string__lit_x_27___spec__4(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_parser_monad__parsec_digit___at_lean_parser_string__lit_x_27___spec__6___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_parser_monad__parsec_digit___at_lean_parser_string__lit_x_27___spec__6(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__5___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__5(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_lean_parser_parse__quoted__char___at_lean_parser_string__lit_x_27___spec__3___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_parser_parse__quoted__char___at_lean_parser_string__lit_x_27___spec__3(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_lean_parser_parse__string__literal__aux___main___at_lean_parser_string__lit_x_27___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_lean_parser_parse__string__literal__aux___main___at_lean_parser_string__lit_x_27___spec__2(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_2);
return x_5;
}
}
obj* l_lean_parser_parse__string__literal___at_lean_parser_string__lit_x_27___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_parser_parse__string__literal___at_lean_parser_string__lit_x_27___spec__1(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_lean_parser_string__lit_x_27___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_parser_string__lit_x_27___lambda__1(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l___private_init_lean_parser_token_5__mk__consume__token(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_8; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_5 = lean::cnstr_get(x_0, 0);
x_6 = lean::string_length(x_5);
lean::inc(x_1);
x_8 = l_string_iterator_nextn___main(x_1, x_6);
lean::inc(x_8);
x_10 = l_lean_parser_mk__raw__res(x_1, x_8);
x_11 = lean::box(0);
x_12 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_12, 0, x_10);
lean::cnstr_set(x_12, 1, x_8);
lean::cnstr_set(x_12, 2, x_11);
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_4);
return x_13;
}
}
obj* l___private_init_lean_parser_token_5__mk__consume__token___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l___private_init_lean_parser_token_5__mk__consume__token(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_3);
return x_5;
}
}
obj* l_lean_parser_number__or__string__lit(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_7; obj* x_8; 
x_3 = l_lean_parser_number;
x_4 = l_lean_parser_number_x_27___closed__1;
lean::inc(x_1);
lean::inc(x_0);
x_7 = l_lean_parser_combinators_node___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__15(x_3, x_4, x_0, x_1, x_2);
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
if (lean::obj_tag(x_8) == 0)
{
obj* x_12; obj* x_14; obj* x_15; 
lean::dec(x_1);
lean::dec(x_0);
x_12 = lean::cnstr_get(x_7, 1);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 x_14 = x_7;
} else {
 lean::inc(x_12);
 lean::dec(x_7);
 x_14 = lean::box(0);
}
if (lean::is_scalar(x_14)) {
 x_15 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_15 = x_14;
}
lean::cnstr_set(x_15, 0, x_8);
lean::cnstr_set(x_15, 1, x_12);
return x_15;
}
else
{
uint8 x_16; 
x_16 = lean::cnstr_get_scalar<uint8>(x_8, sizeof(void*)*1);
if (x_16 == 0)
{
obj* x_17; obj* x_20; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_28; obj* x_30; obj* x_31; obj* x_32; 
x_17 = lean::cnstr_get(x_7, 1);
lean::inc(x_17);
lean::dec(x_7);
x_20 = lean::cnstr_get(x_8, 0);
lean::inc(x_20);
lean::dec(x_8);
x_23 = l_lean_parser_string__lit;
x_24 = l_lean_parser_string__lit_x_27___closed__1;
x_25 = l_lean_parser_combinators_node___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__15(x_23, x_24, x_0, x_1, x_17);
x_26 = lean::cnstr_get(x_25, 0);
x_28 = lean::cnstr_get(x_25, 1);
if (lean::is_exclusive(x_25)) {
 x_30 = x_25;
} else {
 lean::inc(x_26);
 lean::inc(x_28);
 lean::dec(x_25);
 x_30 = lean::box(0);
}
x_31 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_20, x_26);
if (lean::is_scalar(x_30)) {
 x_32 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_32 = x_30;
}
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_28);
return x_32;
}
else
{
obj* x_35; obj* x_37; obj* x_38; 
lean::dec(x_1);
lean::dec(x_0);
x_35 = lean::cnstr_get(x_7, 1);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 x_37 = x_7;
} else {
 lean::inc(x_35);
 lean::dec(x_7);
 x_37 = lean::box(0);
}
if (lean::is_scalar(x_37)) {
 x_38 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_38 = x_37;
}
lean::cnstr_set(x_38, 0, x_8);
lean::cnstr_set(x_38, 1, x_35);
return x_38;
}
}
}
}
obj* l_lean_parser_token__cont(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_6; obj* x_7; 
lean::inc(x_2);
x_6 = l___private_init_lean_parser_token_4__ident_x_27(x_2, x_3, x_4);
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
if (lean::obj_tag(x_7) == 0)
{
obj* x_9; obj* x_11; obj* x_12; obj* x_14; obj* x_16; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; uint8 x_26; 
x_9 = lean::cnstr_get(x_6, 1);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 lean::cnstr_set(x_6, 1, lean::box(0));
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
 lean::cnstr_set(x_7, 0, lean::box(0));
 lean::cnstr_set(x_7, 1, lean::box(0));
 lean::cnstr_set(x_7, 2, lean::box(0));
 x_18 = x_7;
} else {
 lean::inc(x_12);
 lean::inc(x_14);
 lean::inc(x_16);
 lean::dec(x_7);
 x_18 = lean::box(0);
}
x_19 = lean::string_iterator_offset(x_14);
x_20 = lean::string_iterator_offset(x_0);
x_21 = lean::cnstr_get(x_1, 0);
x_22 = lean::string_length(x_21);
x_23 = lean::nat_add(x_20, x_22);
lean::dec(x_22);
lean::dec(x_20);
x_26 = lean::nat_dec_le(x_19, x_23);
lean::dec(x_23);
lean::dec(x_19);
if (x_26 == 0)
{
obj* x_31; obj* x_32; obj* x_33; obj* x_34; 
lean::dec(x_0);
lean::dec(x_2);
x_31 = l_lean_parser_finish__comment__block___closed__2;
if (lean::is_scalar(x_18)) {
 x_32 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_32 = x_18;
}
lean::cnstr_set(x_32, 0, x_12);
lean::cnstr_set(x_32, 1, x_14);
lean::cnstr_set(x_32, 2, x_31);
x_33 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_32);
if (lean::is_scalar(x_11)) {
 x_34 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_34 = x_11;
}
lean::cnstr_set(x_34, 0, x_33);
lean::cnstr_set(x_34, 1, x_9);
return x_34;
}
else
{
obj* x_38; obj* x_41; obj* x_43; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; 
lean::dec(x_12);
lean::dec(x_11);
lean::dec(x_18);
x_38 = l___private_init_lean_parser_token_5__mk__consume__token(x_1, x_0, x_2, x_14, x_9);
lean::dec(x_14);
lean::dec(x_2);
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
x_46 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_47 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_46, x_41);
x_48 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_47);
if (lean::is_scalar(x_45)) {
 x_49 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_49 = x_45;
}
lean::cnstr_set(x_49, 0, x_48);
lean::cnstr_set(x_49, 1, x_43);
return x_49;
}
}
else
{
obj* x_52; obj* x_54; obj* x_55; uint8 x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
lean::dec(x_0);
lean::dec(x_2);
x_52 = lean::cnstr_get(x_6, 1);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 x_54 = x_6;
} else {
 lean::inc(x_52);
 lean::dec(x_6);
 x_54 = lean::box(0);
}
x_55 = lean::cnstr_get(x_7, 0);
x_57 = lean::cnstr_get_scalar<uint8>(x_7, sizeof(void*)*1);
if (lean::is_exclusive(x_7)) {
 x_58 = x_7;
} else {
 lean::inc(x_55);
 lean::dec(x_7);
 x_58 = lean::box(0);
}
if (lean::is_scalar(x_58)) {
 x_59 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_59 = x_58;
}
lean::cnstr_set(x_59, 0, x_55);
lean::cnstr_set_scalar(x_59, sizeof(void*)*1, x_57);
x_60 = x_59;
if (lean::is_scalar(x_54)) {
 x_61 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_61 = x_54;
}
lean::cnstr_set(x_61, 0, x_60);
lean::cnstr_set(x_61, 1, x_52);
return x_61;
}
}
}
obj* l_lean_parser_token__cont___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_lean_parser_token__cont(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
return x_5;
}
}
obj* l_lean_parser_parsec__t_lookahead___at_lean_parser_token___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; uint8 x_6; 
x_6 = lean::string_iterator_has_next(x_1);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_13; obj* x_16; obj* x_17; 
x_7 = lean::box(0);
x_8 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_9 = l_mjoin___rarg___closed__1;
x_10 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_8, x_9, x_7, x_7, x_0, x_1, x_2);
x_11 = lean::cnstr_get(x_10, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_10, 1);
lean::inc(x_13);
lean::dec(x_10);
x_16 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_17 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_11);
if (lean::obj_tag(x_17) == 0)
{
x_3 = x_17;
x_4 = x_13;
goto lbl_5;
}
else
{
uint8 x_18; 
x_18 = lean::cnstr_get_scalar<uint8>(x_17, sizeof(void*)*1);
if (x_18 == 0)
{
obj* x_19; uint32 x_22; obj* x_24; obj* x_25; obj* x_27; obj* x_30; 
x_19 = lean::cnstr_get(x_17, 0);
lean::inc(x_19);
lean::dec(x_17);
x_22 = l_lean_id__begin__escape;
lean::inc(x_1);
x_24 = l_lean_parser_monad__parsec_ch___at___private_init_lean_parser_token_4__ident_x_27___spec__11(x_22, x_0, x_1, x_13);
x_25 = lean::cnstr_get(x_24, 0);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_24, 1);
lean::inc(x_27);
lean::dec(x_24);
x_30 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_19, x_25);
x_3 = x_30;
x_4 = x_27;
goto lbl_5;
}
else
{
x_3 = x_17;
x_4 = x_13;
goto lbl_5;
}
}
}
else
{
uint32 x_31; uint8 x_32; 
x_31 = lean::string_iterator_curr(x_1);
x_32 = l_lean_is__id__first(x_31);
if (x_32 == 0)
{
obj* x_33; obj* x_34; obj* x_35; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_43; obj* x_46; obj* x_47; 
x_33 = l_char_quote__core(x_31);
x_34 = l_char_has__repr___closed__1;
x_35 = lean::string_append(x_34, x_33);
lean::dec(x_33);
x_37 = lean::string_append(x_35, x_34);
x_38 = lean::box(0);
x_39 = l_mjoin___rarg___closed__1;
x_40 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_37, x_39, x_38, x_38, x_0, x_1, x_2);
x_41 = lean::cnstr_get(x_40, 0);
lean::inc(x_41);
x_43 = lean::cnstr_get(x_40, 1);
lean::inc(x_43);
lean::dec(x_40);
x_46 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_47 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_46, x_41);
if (lean::obj_tag(x_47) == 0)
{
x_3 = x_47;
x_4 = x_43;
goto lbl_5;
}
else
{
uint8 x_48; 
x_48 = lean::cnstr_get_scalar<uint8>(x_47, sizeof(void*)*1);
if (x_48 == 0)
{
obj* x_49; uint32 x_52; obj* x_54; obj* x_55; obj* x_57; obj* x_60; 
x_49 = lean::cnstr_get(x_47, 0);
lean::inc(x_49);
lean::dec(x_47);
x_52 = l_lean_id__begin__escape;
lean::inc(x_1);
x_54 = l_lean_parser_monad__parsec_ch___at___private_init_lean_parser_token_4__ident_x_27___spec__11(x_52, x_0, x_1, x_43);
x_55 = lean::cnstr_get(x_54, 0);
lean::inc(x_55);
x_57 = lean::cnstr_get(x_54, 1);
lean::inc(x_57);
lean::dec(x_54);
x_60 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_49, x_55);
x_3 = x_60;
x_4 = x_57;
goto lbl_5;
}
else
{
x_3 = x_47;
x_4 = x_43;
goto lbl_5;
}
}
}
else
{
obj* x_62; obj* x_63; obj* x_64; obj* x_65; 
lean::inc(x_1);
x_62 = lean::string_iterator_next(x_1);
x_63 = lean::box(0);
x_64 = lean::box_uint32(x_31);
x_65 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_65, 0, x_64);
lean::cnstr_set(x_65, 1, x_62);
lean::cnstr_set(x_65, 2, x_63);
x_3 = x_65;
x_4 = x_2;
goto lbl_5;
}
}
lbl_5:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_66; obj* x_68; obj* x_69; obj* x_70; obj* x_71; 
x_66 = lean::cnstr_get(x_3, 0);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 1);
 lean::cnstr_release(x_3, 2);
 x_68 = x_3;
} else {
 lean::inc(x_66);
 lean::dec(x_3);
 x_68 = lean::box(0);
}
x_69 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_68)) {
 x_70 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_70 = x_68;
}
lean::cnstr_set(x_70, 0, x_66);
lean::cnstr_set(x_70, 1, x_1);
lean::cnstr_set(x_70, 2, x_69);
x_71 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_71, 0, x_70);
lean::cnstr_set(x_71, 1, x_4);
return x_71;
}
else
{
obj* x_73; 
lean::dec(x_1);
x_73 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_73, 0, x_3);
lean::cnstr_set(x_73, 1, x_4);
return x_73;
}
}
}
}
obj* l_lean_parser_monad__parsec_observing___at_lean_parser_token___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = l_lean_parser_parsec__t_lookahead___at_lean_parser_token___spec__1(x_0, x_1, x_2);
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; obj* x_8; obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_6 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_set(x_3, 1, lean::box(0));
 x_8 = x_3;
} else {
 lean::inc(x_6);
 lean::dec(x_3);
 x_8 = lean::box(0);
}
x_9 = lean::cnstr_get(x_4, 0);
x_11 = lean::cnstr_get(x_4, 1);
x_13 = lean::cnstr_get(x_4, 2);
if (lean::is_exclusive(x_4)) {
 x_15 = x_4;
} else {
 lean::inc(x_9);
 lean::inc(x_11);
 lean::inc(x_13);
 lean::dec(x_4);
 x_15 = lean::box(0);
}
x_16 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_16, 0, x_9);
x_17 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_15)) {
 x_18 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_18 = x_15;
}
lean::cnstr_set(x_18, 0, x_16);
lean::cnstr_set(x_18, 1, x_11);
lean::cnstr_set(x_18, 2, x_17);
x_19 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_13, x_18);
if (lean::obj_tag(x_19) == 0)
{
obj* x_20; 
if (lean::is_scalar(x_8)) {
 x_20 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_20 = x_8;
}
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_6);
return x_20;
}
else
{
obj* x_21; obj* x_24; obj* x_26; obj* x_27; obj* x_28; 
x_21 = lean::cnstr_get(x_19, 0);
lean::inc(x_21);
lean::dec(x_19);
x_24 = lean::cnstr_get(x_21, 0);
lean::inc(x_24);
x_26 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_26, 0, x_21);
x_27 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_24);
lean::cnstr_set(x_27, 2, x_17);
if (lean::is_scalar(x_8)) {
 x_28 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_28 = x_8;
}
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_6);
return x_28;
}
}
else
{
obj* x_29; obj* x_31; obj* x_32; obj* x_35; obj* x_37; obj* x_38; obj* x_39; obj* x_40; 
x_29 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 x_31 = x_3;
} else {
 lean::inc(x_29);
 lean::dec(x_3);
 x_31 = lean::box(0);
}
x_32 = lean::cnstr_get(x_4, 0);
lean::inc(x_32);
lean::dec(x_4);
x_35 = lean::cnstr_get(x_32, 0);
lean::inc(x_35);
x_37 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_37, 0, x_32);
x_38 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_39 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_39, 0, x_37);
lean::cnstr_set(x_39, 1, x_35);
lean::cnstr_set(x_39, 2, x_38);
if (lean::is_scalar(x_31)) {
 x_40 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_40 = x_31;
}
lean::cnstr_set(x_40, 0, x_39);
lean::cnstr_set(x_40, 1, x_29);
return x_40;
}
}
}
obj* l_lean_parser_with__trailing___at_lean_parser_token___spec__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; obj* x_6; 
lean::inc(x_2);
x_5 = l_lean_parser_whitespace(x_1, x_2, x_3);
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
if (lean::obj_tag(x_6) == 0)
{
obj* x_8; obj* x_10; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
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
x_11 = lean::cnstr_get(x_6, 1);
x_13 = lean::cnstr_get(x_6, 2);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 x_15 = x_6;
} else {
 lean::inc(x_11);
 lean::inc(x_13);
 lean::dec(x_6);
 x_15 = lean::box(0);
}
lean::inc(x_11);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_2);
lean::cnstr_set(x_17, 1, x_11);
x_18 = l_lean_parser_finish__comment__block___closed__2;
if (lean::is_scalar(x_15)) {
 x_19 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_19 = x_15;
}
lean::cnstr_set(x_19, 0, x_17);
lean::cnstr_set(x_19, 1, x_11);
lean::cnstr_set(x_19, 2, x_18);
x_20 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_13, x_19);
x_21 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_22 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_21, x_20);
if (lean::obj_tag(x_22) == 0)
{
obj* x_23; obj* x_25; obj* x_27; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; 
x_23 = lean::cnstr_get(x_22, 0);
x_25 = lean::cnstr_get(x_22, 1);
x_27 = lean::cnstr_get(x_22, 2);
if (lean::is_exclusive(x_22)) {
 x_29 = x_22;
} else {
 lean::inc(x_23);
 lean::inc(x_25);
 lean::inc(x_27);
 lean::dec(x_22);
 x_29 = lean::box(0);
}
x_30 = l___private_init_lean_parser_token_3__update__trailing___main(x_23, x_0);
if (lean::is_scalar(x_29)) {
 x_31 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_31 = x_29;
}
lean::cnstr_set(x_31, 0, x_30);
lean::cnstr_set(x_31, 1, x_25);
lean::cnstr_set(x_31, 2, x_21);
x_32 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_27, x_31);
if (lean::is_scalar(x_10)) {
 x_33 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_33 = x_10;
}
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_8);
return x_33;
}
else
{
obj* x_35; uint8 x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; 
lean::dec(x_0);
x_35 = lean::cnstr_get(x_22, 0);
x_37 = lean::cnstr_get_scalar<uint8>(x_22, sizeof(void*)*1);
if (lean::is_exclusive(x_22)) {
 x_38 = x_22;
} else {
 lean::inc(x_35);
 lean::dec(x_22);
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
if (lean::is_scalar(x_10)) {
 x_41 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_41 = x_10;
}
lean::cnstr_set(x_41, 0, x_40);
lean::cnstr_set(x_41, 1, x_8);
return x_41;
}
}
else
{
obj* x_43; obj* x_45; obj* x_46; uint8 x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; 
lean::dec(x_2);
x_43 = lean::cnstr_get(x_5, 1);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 lean::cnstr_set(x_5, 1, lean::box(0));
 x_45 = x_5;
} else {
 lean::inc(x_43);
 lean::dec(x_5);
 x_45 = lean::box(0);
}
x_46 = lean::cnstr_get(x_6, 0);
x_48 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*1);
if (lean::is_exclusive(x_6)) {
 x_49 = x_6;
} else {
 lean::inc(x_46);
 lean::dec(x_6);
 x_49 = lean::box(0);
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
x_53 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_52, x_51);
if (lean::obj_tag(x_53) == 0)
{
obj* x_54; obj* x_56; obj* x_58; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; 
x_54 = lean::cnstr_get(x_53, 0);
x_56 = lean::cnstr_get(x_53, 1);
x_58 = lean::cnstr_get(x_53, 2);
if (lean::is_exclusive(x_53)) {
 x_60 = x_53;
} else {
 lean::inc(x_54);
 lean::inc(x_56);
 lean::inc(x_58);
 lean::dec(x_53);
 x_60 = lean::box(0);
}
x_61 = l___private_init_lean_parser_token_3__update__trailing___main(x_54, x_0);
if (lean::is_scalar(x_60)) {
 x_62 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_62 = x_60;
}
lean::cnstr_set(x_62, 0, x_61);
lean::cnstr_set(x_62, 1, x_56);
lean::cnstr_set(x_62, 2, x_52);
x_63 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_58, x_62);
if (lean::is_scalar(x_45)) {
 x_64 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_64 = x_45;
}
lean::cnstr_set(x_64, 0, x_63);
lean::cnstr_set(x_64, 1, x_43);
return x_64;
}
else
{
obj* x_66; uint8 x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; 
lean::dec(x_0);
x_66 = lean::cnstr_get(x_53, 0);
x_68 = lean::cnstr_get_scalar<uint8>(x_53, sizeof(void*)*1);
if (lean::is_exclusive(x_53)) {
 x_69 = x_53;
} else {
 lean::inc(x_66);
 lean::dec(x_53);
 x_69 = lean::box(0);
}
if (lean::is_scalar(x_69)) {
 x_70 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_70 = x_69;
}
lean::cnstr_set(x_70, 0, x_66);
lean::cnstr_set_scalar(x_70, sizeof(void*)*1, x_68);
x_71 = x_70;
if (lean::is_scalar(x_45)) {
 x_72 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_72 = x_45;
}
lean::cnstr_set(x_72, 0, x_71);
lean::cnstr_set(x_72, 1, x_43);
return x_72;
}
}
}
}
obj* l_lean_parser_parsec__t_failure___at_lean_parser_token___spec__4___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; uint8 x_6; obj* x_7; obj* x_8; obj* x_9; 
x_2 = lean::box(0);
x_3 = l_lean_parser_parsec__t_failure___rarg___closed__1;
x_4 = l_mjoin___rarg___closed__1;
x_5 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_5, 0, x_0);
lean::cnstr_set(x_5, 1, x_3);
lean::cnstr_set(x_5, 2, x_4);
lean::cnstr_set(x_5, 3, x_2);
x_6 = 0;
x_7 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set_scalar(x_7, sizeof(void*)*1, x_6);
x_8 = x_7;
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_1);
return x_9;
}
}
obj* l_lean_parser_parsec__t_failure___at_lean_parser_token___spec__4(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parsec__t_failure___at_lean_parser_token___spec__4___rarg), 2, 0);
return x_2;
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
obj* x_10; obj* x_11; obj* x_13; obj* x_16; obj* x_17; 
lean::inc(x_2);
lean::inc(x_1);
x_10 = l_lean_parser_parsec__t_failure___at_lean_parser_token___spec__4___rarg(x_1, x_2);
x_11 = lean::cnstr_get(x_10, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_10, 1);
lean::inc(x_13);
lean::dec(x_10);
x_16 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_17 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_11);
x_3 = x_17;
x_4 = x_13;
goto lbl_5;
}
else
{
obj* x_18; obj* x_20; obj* x_21; obj* x_23; uint8 x_25; 
x_18 = lean::cnstr_get(x_6, 0);
lean::inc(x_18);
x_20 = lean::string_iterator_offset(x_1);
x_21 = lean::cnstr_get(x_18, 0);
lean::inc(x_21);
x_23 = lean::string_iterator_offset(x_21);
lean::dec(x_21);
x_25 = lean::nat_dec_eq(x_20, x_23);
lean::dec(x_23);
lean::dec(x_20);
if (x_25 == 0)
{
obj* x_30; obj* x_31; 
lean::inc(x_2);
lean::inc(x_1);
x_30 = l_lean_parser_parsec__t_failure___at_lean_parser_token___spec__4___rarg(x_1, x_2);
x_31 = lean::cnstr_get(x_30, 0);
lean::inc(x_31);
if (lean::obj_tag(x_31) == 0)
{
obj* x_34; obj* x_36; obj* x_37; obj* x_39; obj* x_40; obj* x_42; obj* x_43; obj* x_45; obj* x_47; obj* x_48; obj* x_51; obj* x_52; obj* x_53; obj* x_54; 
lean::dec(x_30);
x_34 = lean::cnstr_get(x_31, 2);
if (lean::is_exclusive(x_31)) {
 lean::cnstr_release(x_31, 0);
 lean::cnstr_release(x_31, 1);
 x_36 = x_31;
} else {
 lean::inc(x_34);
 lean::dec(x_31);
 x_36 = lean::box(0);
}
x_37 = lean::cnstr_get(x_18, 1);
lean::inc(x_37);
x_39 = lean::box(0);
x_40 = lean::cnstr_get(x_2, 1);
lean::inc(x_40);
x_42 = lean::mk_nat_obj(1u);
x_43 = lean::nat_add(x_40, x_42);
lean::dec(x_40);
x_45 = lean::cnstr_get(x_2, 2);
lean::inc(x_45);
x_47 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_47, 0, x_6);
lean::cnstr_set(x_47, 1, x_43);
lean::cnstr_set(x_47, 2, x_45);
x_48 = lean::cnstr_get(x_18, 2);
lean::inc(x_48);
lean::dec(x_18);
if (lean::is_scalar(x_36)) {
 x_51 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_51 = x_36;
}
lean::cnstr_set(x_51, 0, x_48);
lean::cnstr_set(x_51, 1, x_37);
lean::cnstr_set(x_51, 2, x_39);
x_52 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_34, x_51);
x_53 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_54 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_53, x_52);
x_3 = x_54;
x_4 = x_47;
goto lbl_5;
}
else
{
obj* x_57; obj* x_60; uint8 x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; 
lean::dec(x_6);
lean::dec(x_18);
x_57 = lean::cnstr_get(x_30, 1);
lean::inc(x_57);
lean::dec(x_30);
x_60 = lean::cnstr_get(x_31, 0);
x_62 = lean::cnstr_get_scalar<uint8>(x_31, sizeof(void*)*1);
if (lean::is_exclusive(x_31)) {
 x_63 = x_31;
} else {
 lean::inc(x_60);
 lean::dec(x_31);
 x_63 = lean::box(0);
}
if (lean::is_scalar(x_63)) {
 x_64 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_64 = x_63;
}
lean::cnstr_set(x_64, 0, x_60);
lean::cnstr_set_scalar(x_64, sizeof(void*)*1, x_62);
x_65 = x_64;
x_66 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_67 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_66, x_65);
x_3 = x_67;
x_4 = x_57;
goto lbl_5;
}
}
else
{
obj* x_68; obj* x_70; obj* x_71; obj* x_73; obj* x_74; obj* x_76; obj* x_78; obj* x_79; obj* x_82; 
x_68 = lean::cnstr_get(x_18, 1);
lean::inc(x_68);
x_70 = lean::box(0);
x_71 = lean::cnstr_get(x_2, 1);
lean::inc(x_71);
x_73 = lean::mk_nat_obj(1u);
x_74 = lean::nat_add(x_71, x_73);
lean::dec(x_71);
x_76 = lean::cnstr_get(x_2, 2);
lean::inc(x_76);
x_78 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_78, 0, x_6);
lean::cnstr_set(x_78, 1, x_74);
lean::cnstr_set(x_78, 2, x_76);
x_79 = lean::cnstr_get(x_18, 2);
lean::inc(x_79);
lean::dec(x_18);
x_82 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_82, 0, x_79);
lean::cnstr_set(x_82, 1, x_68);
lean::cnstr_set(x_82, 2, x_70);
x_3 = x_82;
x_4 = x_78;
goto lbl_5;
}
}
lbl_5:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_86; obj* x_87; obj* x_88; obj* x_89; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_86 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_87 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_86, x_3);
x_88 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_86, x_87);
x_89 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_89, 0, x_88);
lean::cnstr_set(x_89, 1, x_4);
return x_89;
}
else
{
obj* x_90; uint8 x_92; obj* x_94; obj* x_95; obj* x_97; obj* x_100; obj* x_101; 
x_90 = lean::cnstr_get(x_3, 0);
lean::inc(x_90);
x_92 = lean::cnstr_get_scalar<uint8>(x_3, sizeof(void*)*1);
lean::dec(x_3);
x_97 = lean::cnstr_get(x_90, 0);
lean::inc(x_97);
lean::dec(x_90);
x_100 = l_lean_parser_monad__parsec_observing___at_lean_parser_token___spec__2(x_0, x_97, x_4);
x_101 = lean::cnstr_get(x_100, 0);
lean::inc(x_101);
if (lean::obj_tag(x_101) == 0)
{
obj* x_103; obj* x_106; obj* x_108; obj* x_110; obj* x_114; obj* x_115; 
x_103 = lean::cnstr_get(x_100, 1);
lean::inc(x_103);
lean::dec(x_100);
x_106 = lean::cnstr_get(x_101, 0);
lean::inc(x_106);
x_108 = lean::cnstr_get(x_101, 1);
lean::inc(x_108);
x_110 = lean::cnstr_get(x_101, 2);
lean::inc(x_110);
lean::dec(x_101);
lean::inc(x_0);
x_114 = l_lean_parser_match__token(x_0, x_108, x_103);
x_115 = lean::cnstr_get(x_114, 0);
lean::inc(x_115);
if (lean::obj_tag(x_115) == 0)
{
obj* x_117; obj* x_120; obj* x_122; obj* x_124; obj* x_127; obj* x_128; 
x_117 = lean::cnstr_get(x_114, 1);
lean::inc(x_117);
lean::dec(x_114);
x_120 = lean::cnstr_get(x_115, 0);
lean::inc(x_120);
x_122 = lean::cnstr_get(x_115, 1);
lean::inc(x_122);
x_124 = lean::cnstr_get(x_115, 2);
lean::inc(x_124);
lean::dec(x_115);
if (lean::obj_tag(x_120) == 0)
{
if (lean::obj_tag(x_106) == 0)
{
obj* x_132; obj* x_133; obj* x_135; 
lean::dec(x_106);
lean::inc(x_0);
x_132 = l_lean_parser_number__or__string__lit(x_0, x_122, x_117);
x_133 = lean::cnstr_get(x_132, 0);
lean::inc(x_133);
x_135 = lean::cnstr_get(x_132, 1);
lean::inc(x_135);
lean::dec(x_132);
x_127 = x_133;
x_128 = x_135;
goto lbl_129;
}
else
{
obj* x_140; obj* x_141; obj* x_143; 
lean::dec(x_106);
lean::inc(x_0);
x_140 = l___private_init_lean_parser_token_4__ident_x_27(x_0, x_122, x_117);
x_141 = lean::cnstr_get(x_140, 0);
lean::inc(x_141);
x_143 = lean::cnstr_get(x_140, 1);
lean::inc(x_143);
lean::dec(x_140);
x_127 = x_141;
x_128 = x_143;
goto lbl_129;
}
}
else
{
obj* x_146; obj* x_149; 
x_146 = lean::cnstr_get(x_120, 0);
lean::inc(x_146);
lean::dec(x_120);
x_149 = lean::cnstr_get(x_146, 2);
lean::inc(x_149);
if (lean::obj_tag(x_149) == 0)
{
if (lean::obj_tag(x_106) == 0)
{
obj* x_153; obj* x_156; obj* x_158; 
lean::dec(x_106);
lean::inc(x_1);
x_153 = l___private_init_lean_parser_token_5__mk__consume__token(x_146, x_1, x_0, x_122, x_117);
lean::dec(x_122);
lean::dec(x_146);
x_156 = lean::cnstr_get(x_153, 0);
lean::inc(x_156);
x_158 = lean::cnstr_get(x_153, 1);
lean::inc(x_158);
lean::dec(x_153);
x_127 = x_156;
x_128 = x_158;
goto lbl_129;
}
else
{
obj* x_164; obj* x_166; obj* x_168; 
lean::dec(x_106);
lean::inc(x_0);
lean::inc(x_1);
x_164 = l_lean_parser_token__cont(x_1, x_146, x_0, x_122, x_117);
lean::dec(x_146);
x_166 = lean::cnstr_get(x_164, 0);
lean::inc(x_166);
x_168 = lean::cnstr_get(x_164, 1);
lean::inc(x_168);
lean::dec(x_164);
x_127 = x_166;
x_128 = x_168;
goto lbl_129;
}
}
else
{
obj* x_174; obj* x_175; obj* x_176; obj* x_177; obj* x_179; obj* x_181; 
lean::dec(x_146);
lean::dec(x_149);
lean::dec(x_106);
x_174 = lean::box(0);
x_175 = l_lean_parser_token___closed__1;
x_176 = l_mjoin___rarg___closed__1;
x_177 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_175, x_176, x_174, x_174, x_0, x_122, x_117);
lean::dec(x_122);
x_179 = lean::cnstr_get(x_177, 0);
lean::inc(x_179);
x_181 = lean::cnstr_get(x_177, 1);
lean::inc(x_181);
lean::dec(x_177);
x_127 = x_179;
x_128 = x_181;
goto lbl_129;
}
}
lbl_129:
{
if (lean::obj_tag(x_127) == 0)
{
obj* x_184; obj* x_186; obj* x_188; obj* x_191; obj* x_193; 
x_184 = lean::cnstr_get(x_127, 0);
lean::inc(x_184);
x_186 = lean::cnstr_get(x_127, 1);
lean::inc(x_186);
x_188 = lean::cnstr_get(x_127, 2);
lean::inc(x_188);
lean::dec(x_127);
x_191 = l_lean_parser_with__trailing___at_lean_parser_token___spec__3(x_184, x_0, x_186, x_128);
lean::dec(x_0);
x_193 = lean::cnstr_get(x_191, 0);
lean::inc(x_193);
if (lean::obj_tag(x_193) == 0)
{
obj* x_196; obj* x_198; obj* x_200; obj* x_202; obj* x_205; obj* x_206; obj* x_207; obj* x_209; obj* x_212; obj* x_213; obj* x_215; obj* x_216; obj* x_217; obj* x_218; obj* x_219; obj* x_220; obj* x_221; 
lean::dec(x_191);
x_196 = lean::cnstr_get(x_193, 0);
x_198 = lean::cnstr_get(x_193, 1);
x_200 = lean::cnstr_get(x_193, 2);
if (lean::is_exclusive(x_193)) {
 x_202 = x_193;
} else {
 lean::inc(x_196);
 lean::inc(x_198);
 lean::inc(x_200);
 lean::dec(x_193);
 x_202 = lean::box(0);
}
lean::inc(x_196);
lean::inc(x_198);
x_205 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_205, 0, x_1);
lean::cnstr_set(x_205, 1, x_198);
lean::cnstr_set(x_205, 2, x_196);
x_206 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_206, 0, x_205);
x_207 = lean::cnstr_get(x_2, 1);
lean::inc(x_207);
x_209 = lean::cnstr_get(x_2, 2);
lean::inc(x_209);
lean::dec(x_2);
x_212 = lean::mk_nat_obj(1u);
x_213 = lean::nat_add(x_209, x_212);
lean::dec(x_209);
x_215 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_215, 0, x_206);
lean::cnstr_set(x_215, 1, x_207);
lean::cnstr_set(x_215, 2, x_213);
x_216 = l_lean_parser_match__token___closed__1;
if (lean::is_scalar(x_202)) {
 x_217 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_217 = x_202;
}
lean::cnstr_set(x_217, 0, x_196);
lean::cnstr_set(x_217, 1, x_198);
lean::cnstr_set(x_217, 2, x_216);
x_218 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_200, x_217);
x_219 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_188, x_218);
x_220 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_124, x_219);
x_221 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_110, x_220);
x_94 = x_221;
x_95 = x_215;
goto lbl_96;
}
else
{
obj* x_224; obj* x_227; uint8 x_229; obj* x_230; obj* x_231; obj* x_232; obj* x_233; obj* x_234; obj* x_235; 
lean::dec(x_1);
lean::dec(x_2);
x_224 = lean::cnstr_get(x_191, 1);
lean::inc(x_224);
lean::dec(x_191);
x_227 = lean::cnstr_get(x_193, 0);
x_229 = lean::cnstr_get_scalar<uint8>(x_193, sizeof(void*)*1);
if (lean::is_exclusive(x_193)) {
 x_230 = x_193;
} else {
 lean::inc(x_227);
 lean::dec(x_193);
 x_230 = lean::box(0);
}
if (lean::is_scalar(x_230)) {
 x_231 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_231 = x_230;
}
lean::cnstr_set(x_231, 0, x_227);
lean::cnstr_set_scalar(x_231, sizeof(void*)*1, x_229);
x_232 = x_231;
x_233 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_188, x_232);
x_234 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_124, x_233);
x_235 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_110, x_234);
x_94 = x_235;
x_95 = x_224;
goto lbl_96;
}
}
else
{
obj* x_239; uint8 x_241; obj* x_242; obj* x_243; obj* x_244; obj* x_245; obj* x_246; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_239 = lean::cnstr_get(x_127, 0);
x_241 = lean::cnstr_get_scalar<uint8>(x_127, sizeof(void*)*1);
if (lean::is_exclusive(x_127)) {
 x_242 = x_127;
} else {
 lean::inc(x_239);
 lean::dec(x_127);
 x_242 = lean::box(0);
}
if (lean::is_scalar(x_242)) {
 x_243 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_243 = x_242;
}
lean::cnstr_set(x_243, 0, x_239);
lean::cnstr_set_scalar(x_243, sizeof(void*)*1, x_241);
x_244 = x_243;
x_245 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_124, x_244);
x_246 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_110, x_245);
x_94 = x_246;
x_95 = x_128;
goto lbl_96;
}
}
}
else
{
obj* x_251; obj* x_254; uint8 x_256; obj* x_257; obj* x_258; obj* x_259; obj* x_260; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_106);
x_251 = lean::cnstr_get(x_114, 1);
lean::inc(x_251);
lean::dec(x_114);
x_254 = lean::cnstr_get(x_115, 0);
x_256 = lean::cnstr_get_scalar<uint8>(x_115, sizeof(void*)*1);
if (lean::is_exclusive(x_115)) {
 x_257 = x_115;
} else {
 lean::inc(x_254);
 lean::dec(x_115);
 x_257 = lean::box(0);
}
if (lean::is_scalar(x_257)) {
 x_258 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_258 = x_257;
}
lean::cnstr_set(x_258, 0, x_254);
lean::cnstr_set_scalar(x_258, sizeof(void*)*1, x_256);
x_259 = x_258;
x_260 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_110, x_259);
x_94 = x_260;
x_95 = x_251;
goto lbl_96;
}
}
else
{
obj* x_264; obj* x_267; uint8 x_269; obj* x_270; obj* x_271; obj* x_272; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_264 = lean::cnstr_get(x_100, 1);
lean::inc(x_264);
lean::dec(x_100);
x_267 = lean::cnstr_get(x_101, 0);
x_269 = lean::cnstr_get_scalar<uint8>(x_101, sizeof(void*)*1);
if (lean::is_exclusive(x_101)) {
 x_270 = x_101;
} else {
 lean::inc(x_267);
 lean::dec(x_101);
 x_270 = lean::box(0);
}
if (lean::is_scalar(x_270)) {
 x_271 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_271 = x_270;
}
lean::cnstr_set(x_271, 0, x_267);
lean::cnstr_set_scalar(x_271, sizeof(void*)*1, x_269);
x_272 = x_271;
x_94 = x_272;
x_95 = x_264;
goto lbl_96;
}
lbl_96:
{
if (lean::obj_tag(x_94) == 0)
{
obj* x_273; obj* x_274; obj* x_275; obj* x_276; 
x_273 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_274 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_273, x_94);
x_275 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_273, x_274);
x_276 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_276, 0, x_275);
lean::cnstr_set(x_276, 1, x_95);
return x_276;
}
else
{
uint8 x_277; 
x_277 = lean::cnstr_get_scalar<uint8>(x_94, sizeof(void*)*1);
if (x_92 == 0)
{
obj* x_278; obj* x_280; obj* x_281; obj* x_282; obj* x_283; obj* x_284; obj* x_285; obj* x_286; 
x_278 = lean::cnstr_get(x_94, 0);
if (lean::is_exclusive(x_94)) {
 x_280 = x_94;
} else {
 lean::inc(x_278);
 lean::dec(x_94);
 x_280 = lean::box(0);
}
if (lean::is_scalar(x_280)) {
 x_281 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_281 = x_280;
}
lean::cnstr_set(x_281, 0, x_278);
lean::cnstr_set_scalar(x_281, sizeof(void*)*1, x_277);
x_282 = x_281;
x_283 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_284 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_283, x_282);
x_285 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_283, x_284);
x_286 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_286, 0, x_285);
lean::cnstr_set(x_286, 1, x_95);
return x_286;
}
else
{
obj* x_287; obj* x_289; obj* x_290; obj* x_291; obj* x_292; obj* x_293; obj* x_294; obj* x_295; 
x_287 = lean::cnstr_get(x_94, 0);
if (lean::is_exclusive(x_94)) {
 x_289 = x_94;
} else {
 lean::inc(x_287);
 lean::dec(x_94);
 x_289 = lean::box(0);
}
if (lean::is_scalar(x_289)) {
 x_290 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_290 = x_289;
}
lean::cnstr_set(x_290, 0, x_287);
lean::cnstr_set_scalar(x_290, sizeof(void*)*1, x_92);
x_291 = x_290;
x_292 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_293 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_292, x_291);
x_294 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_292, x_293);
x_295 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_295, 0, x_294);
lean::cnstr_set(x_295, 1, x_95);
return x_295;
}
}
}
}
}
}
}
obj* l_lean_parser_parsec__t_lookahead___at_lean_parser_token___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_parser_parsec__t_lookahead___at_lean_parser_token___spec__1(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_lean_parser_monad__parsec_observing___at_lean_parser_token___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_parser_monad__parsec_observing___at_lean_parser_token___spec__2(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_lean_parser_with__trailing___at_lean_parser_token___spec__3___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_parser_with__trailing___at_lean_parser_token___spec__3(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_lean_parser_parsec__t_failure___at_lean_parser_token___spec__4___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_parser_parsec__t_failure___at_lean_parser_token___spec__4(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_lean_parser_parsec__t_lookahead___at_lean_parser_peek__token___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_5; 
lean::inc(x_1);
x_4 = l_lean_parser_token(x_0, x_1, x_2);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
if (lean::obj_tag(x_5) == 0)
{
obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_7 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_9 = x_4;
} else {
 lean::inc(x_7);
 lean::dec(x_4);
 x_9 = lean::box(0);
}
x_10 = lean::cnstr_get(x_5, 0);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 1);
 lean::cnstr_release(x_5, 2);
 x_12 = x_5;
} else {
 lean::inc(x_10);
 lean::dec(x_5);
 x_12 = lean::box(0);
}
x_13 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_12)) {
 x_14 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_14 = x_12;
}
lean::cnstr_set(x_14, 0, x_10);
lean::cnstr_set(x_14, 1, x_1);
lean::cnstr_set(x_14, 2, x_13);
if (lean::is_scalar(x_9)) {
 x_15 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_15 = x_9;
}
lean::cnstr_set(x_15, 0, x_14);
lean::cnstr_set(x_15, 1, x_7);
return x_15;
}
else
{
obj* x_17; obj* x_19; obj* x_20; 
lean::dec(x_1);
x_17 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_19 = x_4;
} else {
 lean::inc(x_17);
 lean::dec(x_4);
 x_19 = lean::box(0);
}
if (lean::is_scalar(x_19)) {
 x_20 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_20 = x_19;
}
lean::cnstr_set(x_20, 0, x_5);
lean::cnstr_set(x_20, 1, x_17);
return x_20;
}
}
}
obj* l_lean_parser_monad__parsec_observing___at_lean_parser_peek__token___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_6; obj* x_8; obj* x_9; 
x_3 = l_lean_parser_parsec__t_lookahead___at_lean_parser_peek__token___spec__1(x_0, x_1, x_2);
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
x_9 = l_lean_parser_parsec__t_try__mk__res___rarg(x_4);
if (lean::obj_tag(x_9) == 0)
{
obj* x_10; obj* x_12; obj* x_14; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_10 = lean::cnstr_get(x_9, 0);
x_12 = lean::cnstr_get(x_9, 1);
x_14 = lean::cnstr_get(x_9, 2);
if (lean::is_exclusive(x_9)) {
 x_16 = x_9;
} else {
 lean::inc(x_10);
 lean::inc(x_12);
 lean::inc(x_14);
 lean::dec(x_9);
 x_16 = lean::box(0);
}
x_17 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_17, 0, x_10);
x_18 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_16)) {
 x_19 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_19 = x_16;
}
lean::cnstr_set(x_19, 0, x_17);
lean::cnstr_set(x_19, 1, x_12);
lean::cnstr_set(x_19, 2, x_18);
x_20 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_14, x_19);
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
obj* x_22; obj* x_25; obj* x_27; obj* x_28; obj* x_29; 
x_22 = lean::cnstr_get(x_20, 0);
lean::inc(x_22);
lean::dec(x_20);
x_25 = lean::cnstr_get(x_22, 0);
lean::inc(x_25);
x_27 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_27, 0, x_22);
x_28 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_25);
lean::cnstr_set(x_28, 2, x_18);
if (lean::is_scalar(x_8)) {
 x_29 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_29 = x_8;
}
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_6);
return x_29;
}
}
else
{
obj* x_30; obj* x_33; obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
x_30 = lean::cnstr_get(x_9, 0);
lean::inc(x_30);
lean::dec(x_9);
x_33 = lean::cnstr_get(x_30, 0);
lean::inc(x_33);
x_35 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_35, 0, x_30);
x_36 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_37 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_37, 0, x_35);
lean::cnstr_set(x_37, 1, x_33);
lean::cnstr_set(x_37, 2, x_36);
if (lean::is_scalar(x_8)) {
 x_38 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_38 = x_8;
}
lean::cnstr_set(x_38, 0, x_37);
lean::cnstr_set(x_38, 1, x_6);
return x_38;
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
obj* x_8; obj* x_9; 
lean::inc(x_4);
lean::inc(x_3);
x_8 = l_lean_parser_token(x_3, x_4, x_5);
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
if (lean::obj_tag(x_9) == 0)
{
obj* x_11; obj* x_13; obj* x_14; obj* x_16; obj* x_18; obj* x_20; obj* x_21; 
x_11 = lean::cnstr_get(x_8, 1);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_release(x_8, 0);
 lean::cnstr_set(x_8, 1, lean::box(0));
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
 lean::cnstr_set(x_9, 0, lean::box(0));
 lean::cnstr_set(x_9, 1, lean::box(0));
 lean::cnstr_set(x_9, 2, lean::box(0));
 x_20 = x_9;
} else {
 lean::inc(x_14);
 lean::inc(x_16);
 lean::inc(x_18);
 lean::dec(x_9);
 x_20 = lean::box(0);
}
switch (lean::obj_tag(x_14)) {
case 0:
{
obj* x_23; obj* x_25; uint8 x_28; 
x_23 = lean::cnstr_get(x_14, 0);
lean::inc(x_23);
x_25 = lean::cnstr_get(x_23, 1);
lean::inc(x_25);
lean::dec(x_23);
x_28 = lean::string_dec_eq(x_2, x_25);
if (x_28 == 0)
{
obj* x_31; obj* x_32; obj* x_33; obj* x_37; 
lean::dec(x_13);
lean::dec(x_20);
x_31 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_31, 0, x_4);
x_32 = lean::box(0);
x_33 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_25, x_0, x_31, x_32, x_3, x_16, x_11);
lean::dec(x_16);
lean::dec(x_3);
lean::dec(x_31);
x_37 = lean::cnstr_get(x_33, 0);
lean::inc(x_37);
if (lean::obj_tag(x_37) == 0)
{
obj* x_39; obj* x_41; obj* x_42; obj* x_44; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; 
x_39 = lean::cnstr_get(x_33, 1);
if (lean::is_exclusive(x_33)) {
 lean::cnstr_release(x_33, 0);
 x_41 = x_33;
} else {
 lean::inc(x_39);
 lean::dec(x_33);
 x_41 = lean::box(0);
}
x_42 = lean::cnstr_get(x_37, 1);
x_44 = lean::cnstr_get(x_37, 2);
if (lean::is_exclusive(x_37)) {
 lean::cnstr_release(x_37, 0);
 x_46 = x_37;
} else {
 lean::inc(x_42);
 lean::inc(x_44);
 lean::dec(x_37);
 x_46 = lean::box(0);
}
x_47 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_46)) {
 x_48 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_48 = x_46;
}
lean::cnstr_set(x_48, 0, x_14);
lean::cnstr_set(x_48, 1, x_42);
lean::cnstr_set(x_48, 2, x_47);
x_49 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_44, x_48);
x_50 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_18, x_49);
x_51 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_47, x_50);
x_52 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_51, x_1);
x_53 = l_lean_parser_parsec__t_try__mk__res___rarg(x_52);
if (lean::is_scalar(x_41)) {
 x_54 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_54 = x_41;
}
lean::cnstr_set(x_54, 0, x_53);
lean::cnstr_set(x_54, 1, x_39);
return x_54;
}
else
{
obj* x_56; obj* x_58; obj* x_59; uint8 x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; 
lean::dec(x_14);
x_56 = lean::cnstr_get(x_33, 1);
if (lean::is_exclusive(x_33)) {
 lean::cnstr_release(x_33, 0);
 x_58 = x_33;
} else {
 lean::inc(x_56);
 lean::dec(x_33);
 x_58 = lean::box(0);
}
x_59 = lean::cnstr_get(x_37, 0);
x_61 = lean::cnstr_get_scalar<uint8>(x_37, sizeof(void*)*1);
if (lean::is_exclusive(x_37)) {
 x_62 = x_37;
} else {
 lean::inc(x_59);
 lean::dec(x_37);
 x_62 = lean::box(0);
}
if (lean::is_scalar(x_62)) {
 x_63 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_63 = x_62;
}
lean::cnstr_set(x_63, 0, x_59);
lean::cnstr_set_scalar(x_63, sizeof(void*)*1, x_61);
x_64 = x_63;
x_65 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_18, x_64);
x_66 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_67 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_66, x_65);
x_68 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_67, x_1);
x_69 = l_lean_parser_parsec__t_try__mk__res___rarg(x_68);
if (lean::is_scalar(x_58)) {
 x_70 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_70 = x_58;
}
lean::cnstr_set(x_70, 0, x_69);
lean::cnstr_set(x_70, 1, x_56);
return x_70;
}
}
else
{
obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_25);
x_75 = l_lean_parser_finish__comment__block___closed__2;
if (lean::is_scalar(x_20)) {
 x_76 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_76 = x_20;
}
lean::cnstr_set(x_76, 0, x_14);
lean::cnstr_set(x_76, 1, x_16);
lean::cnstr_set(x_76, 2, x_75);
x_77 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_18, x_76);
x_78 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_79 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_78, x_77);
x_80 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_79, x_1);
x_81 = l_lean_parser_parsec__t_try__mk__res___rarg(x_80);
if (lean::is_scalar(x_13)) {
 x_82 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_82 = x_13;
}
lean::cnstr_set(x_82, 0, x_81);
lean::cnstr_set(x_82, 1, x_11);
return x_82;
}
}
case 3:
{
obj* x_85; 
lean::dec(x_13);
lean::dec(x_20);
x_85 = lean::box(0);
x_21 = x_85;
goto lbl_22;
}
default:
{
obj* x_89; 
lean::dec(x_13);
lean::dec(x_14);
lean::dec(x_20);
x_89 = lean::box(0);
x_21 = x_89;
goto lbl_22;
}
}
lbl_22:
{
obj* x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_98; obj* x_100; obj* x_102; obj* x_103; obj* x_104; obj* x_105; obj* x_106; obj* x_107; obj* x_108; 
lean::dec(x_21);
x_91 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_91, 0, x_4);
x_92 = lean::box(0);
x_93 = l_string_join___closed__1;
x_94 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_93, x_0, x_91, x_92, x_3, x_16, x_11);
lean::dec(x_16);
lean::dec(x_3);
lean::dec(x_91);
x_98 = lean::cnstr_get(x_94, 0);
x_100 = lean::cnstr_get(x_94, 1);
if (lean::is_exclusive(x_94)) {
 x_102 = x_94;
} else {
 lean::inc(x_98);
 lean::inc(x_100);
 lean::dec(x_94);
 x_102 = lean::box(0);
}
x_103 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_18, x_98);
x_104 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_105 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_104, x_103);
x_106 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_105, x_1);
x_107 = l_lean_parser_parsec__t_try__mk__res___rarg(x_106);
if (lean::is_scalar(x_102)) {
 x_108 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_108 = x_102;
}
lean::cnstr_set(x_108, 0, x_107);
lean::cnstr_set(x_108, 1, x_100);
return x_108;
}
}
else
{
obj* x_112; obj* x_114; obj* x_115; uint8 x_117; obj* x_118; obj* x_119; obj* x_120; obj* x_121; obj* x_122; obj* x_123; obj* x_124; obj* x_125; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_0);
x_112 = lean::cnstr_get(x_8, 1);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_release(x_8, 0);
 x_114 = x_8;
} else {
 lean::inc(x_112);
 lean::dec(x_8);
 x_114 = lean::box(0);
}
x_115 = lean::cnstr_get(x_9, 0);
x_117 = lean::cnstr_get_scalar<uint8>(x_9, sizeof(void*)*1);
if (lean::is_exclusive(x_9)) {
 x_118 = x_9;
} else {
 lean::inc(x_115);
 lean::dec(x_9);
 x_118 = lean::box(0);
}
if (lean::is_scalar(x_118)) {
 x_119 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_119 = x_118;
}
lean::cnstr_set(x_119, 0, x_115);
lean::cnstr_set_scalar(x_119, sizeof(void*)*1, x_117);
x_120 = x_119;
x_121 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_122 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_121, x_120);
x_123 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_122, x_1);
x_124 = l_lean_parser_parsec__t_try__mk__res___rarg(x_123);
if (lean::is_scalar(x_114)) {
 x_125 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_125 = x_114;
}
lean::cnstr_set(x_125, 0, x_124);
lean::cnstr_set(x_125, 1, x_112);
return x_125;
}
}
}
obj* l_lean_parser_symbol__core___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
lean::inc(x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_5, 0, x_1);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___rarg___lambda__1___boxed), 6, 3);
lean::closure_set(x_6, 0, x_3);
lean::closure_set(x_6, 1, x_5);
lean::closure_set(x_6, 2, x_1);
x_7 = lean::apply_2(x_0, lean::box(0), x_6);
return x_7;
}
}
obj* l_lean_parser_symbol__core(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___rarg___boxed), 4, 0);
return x_1;
}
}
obj* l_lean_parser_symbol__core___rarg___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_lean_parser_symbol__core___rarg___lambda__1(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_2);
return x_6;
}
}
obj* l_lean_parser_symbol__core___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_parser_symbol__core___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_lean_parser_symbol__core___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_symbol__core(x_0);
lean::dec(x_0);
return x_1;
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
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol___rarg___boxed), 3, 0);
return x_1;
}
}
obj* l_lean_parser_symbol___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_parser_symbol___rarg(x_0, x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_lean_parser_symbol___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_symbol(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_parser_symbol_tokens___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_2 = l_string_trim(x_0);
x_3 = lean::box(0);
x_4 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_4, 0, x_2);
lean::cnstr_set(x_4, 1, x_1);
lean::cnstr_set(x_4, 2, x_3);
x_5 = lean::box(0);
x_6 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_6, 0, x_4);
lean::cnstr_set(x_6, 1, x_5);
return x_6;
}
}
obj* l_lean_parser_symbol_tokens(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol_tokens___rarg), 2, 0);
return x_2;
}
}
obj* l_lean_parser_symbol_tokens___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_parser_symbol_tokens(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_lean_parser_symbol_view___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = l_lean_parser_raw_view___rarg___closed__1;
x_4 = l_lean_parser_raw_view___rarg___closed__2;
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_3);
lean::cnstr_set(x_5, 1, x_4);
return x_5;
}
}
obj* l_lean_parser_symbol_view(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol_view___rarg___boxed), 3, 0);
return x_1;
}
}
obj* l_lean_parser_symbol_view___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_parser_symbol_view___rarg(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_lean_parser_symbol_view___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_symbol_view(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_parser_symbol_view__default___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::box(0);
return x_3;
}
}
obj* l_lean_parser_symbol_view__default(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol_view__default___rarg___boxed), 3, 0);
return x_1;
}
}
obj* l_lean_parser_symbol_view__default___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_parser_symbol_view__default___rarg(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_lean_parser_symbol_view__default___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_symbol_view__default(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_parser_try__view___at_lean_parser_number_parser___spec__1(obj* x_0) {
_start:
{
obj* x_1; uint8 x_2; 
x_1 = l_lean_parser_number;
x_2 = l_lean_parser_syntax_is__of__kind___main(x_1, x_0);
if (x_2 == 0)
{
obj* x_4; 
lean::dec(x_0);
x_4 = lean::box(0);
return x_4;
}
else
{
obj* x_5; obj* x_6; obj* x_9; obj* x_10; 
x_5 = l_lean_parser_number_has__view;
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
lean::dec(x_5);
x_9 = lean::apply_1(x_6, x_0);
x_10 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_10, 0, x_9);
return x_10;
}
}
}
obj* l_lean_parser_number_parser___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_6; obj* x_7; 
lean::inc(x_2);
lean::inc(x_1);
x_6 = l_lean_parser_token(x_1, x_2, x_3);
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
if (lean::obj_tag(x_7) == 0)
{
obj* x_9; obj* x_11; obj* x_12; obj* x_14; obj* x_16; obj* x_18; obj* x_20; 
x_9 = lean::cnstr_get(x_6, 1);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 lean::cnstr_set(x_6, 1, lean::box(0));
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
 lean::cnstr_set(x_7, 0, lean::box(0));
 lean::cnstr_set(x_7, 1, lean::box(0));
 lean::cnstr_set(x_7, 2, lean::box(0));
 x_18 = x_7;
} else {
 lean::inc(x_12);
 lean::inc(x_14);
 lean::inc(x_16);
 lean::dec(x_7);
 x_18 = lean::box(0);
}
lean::inc(x_12);
x_20 = l_lean_parser_try__view___at_lean_parser_number_parser___spec__1(x_12);
if (lean::obj_tag(x_20) == 0)
{
obj* x_24; obj* x_25; obj* x_26; obj* x_28; obj* x_32; obj* x_34; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; 
lean::dec(x_11);
lean::dec(x_12);
lean::dec(x_18);
x_24 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_24, 0, x_2);
x_25 = lean::box(0);
x_26 = l_string_join___closed__1;
lean::inc(x_0);
x_28 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_26, x_0, x_24, x_25, x_1, x_14, x_9);
lean::dec(x_14);
lean::dec(x_1);
lean::dec(x_24);
x_32 = lean::cnstr_get(x_28, 0);
x_34 = lean::cnstr_get(x_28, 1);
if (lean::is_exclusive(x_28)) {
 x_36 = x_28;
} else {
 lean::inc(x_32);
 lean::inc(x_34);
 lean::dec(x_28);
 x_36 = lean::box(0);
}
x_37 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_38 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_37, x_32);
x_39 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_38);
x_40 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_37, x_39);
x_41 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_40, x_0);
x_42 = l_lean_parser_parsec__t_try__mk__res___rarg(x_41);
if (lean::is_scalar(x_36)) {
 x_43 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_43 = x_36;
}
lean::cnstr_set(x_43, 0, x_42);
lean::cnstr_set(x_43, 1, x_34);
return x_43;
}
else
{
obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; 
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_20);
x_47 = l_lean_parser_finish__comment__block___closed__2;
if (lean::is_scalar(x_18)) {
 x_48 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_48 = x_18;
}
lean::cnstr_set(x_48, 0, x_12);
lean::cnstr_set(x_48, 1, x_14);
lean::cnstr_set(x_48, 2, x_47);
x_49 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_48);
x_50 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_51 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_50, x_49);
x_52 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_51, x_0);
x_53 = l_lean_parser_parsec__t_try__mk__res___rarg(x_52);
if (lean::is_scalar(x_11)) {
 x_54 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_54 = x_11;
}
lean::cnstr_set(x_54, 0, x_53);
lean::cnstr_set(x_54, 1, x_9);
return x_54;
}
}
else
{
obj* x_57; obj* x_59; obj* x_60; uint8 x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; 
lean::dec(x_1);
lean::dec(x_2);
x_57 = lean::cnstr_get(x_6, 1);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 x_59 = x_6;
} else {
 lean::inc(x_57);
 lean::dec(x_6);
 x_59 = lean::box(0);
}
x_60 = lean::cnstr_get(x_7, 0);
x_62 = lean::cnstr_get_scalar<uint8>(x_7, sizeof(void*)*1);
if (lean::is_exclusive(x_7)) {
 x_63 = x_7;
} else {
 lean::inc(x_60);
 lean::dec(x_7);
 x_63 = lean::box(0);
}
if (lean::is_scalar(x_63)) {
 x_64 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_64 = x_63;
}
lean::cnstr_set(x_64, 0, x_60);
lean::cnstr_set_scalar(x_64, sizeof(void*)*1, x_62);
x_65 = x_64;
x_66 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_67 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_66, x_65);
x_68 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_67, x_0);
x_69 = l_lean_parser_parsec__t_try__mk__res___rarg(x_68);
if (lean::is_scalar(x_59)) {
 x_70 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_70 = x_59;
}
lean::cnstr_set(x_70, 0, x_69);
lean::cnstr_set(x_70, 1, x_57);
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
obj* x_1; obj* x_2; 
x_1 = l_lean_parser_number_parser___rarg___closed__1;
x_2 = lean::apply_2(x_0, lean::box(0), x_1);
return x_2;
}
}
obj* l_lean_parser_number_parser(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_number_parser___rarg), 1, 0);
return x_1;
}
}
obj* l_lean_parser_number_parser___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_number_parser(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_parser_number_parser_tokens(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::box(0);
return x_2;
}
}
obj* l_lean_parser_number_parser_tokens___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_parser_number_parser_tokens(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_lean_parser_number_parser_view___rarg___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = l_lean_parser_number_has__view;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
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
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_parser_number_parser_view___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_lean_parser_number_parser_view___rarg___closed__1;
x_2 = l_lean_parser_number_parser_view___rarg___closed__2;
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* l_lean_parser_number_parser_view(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_number_parser_view___rarg___boxed), 1, 0);
return x_1;
}
}
obj* l_lean_parser_number_parser_view___rarg___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_number_parser_view___rarg(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_parser_number_parser_view___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_number_parser_view(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l___private_init_lean_parser_token_7__to__nat__core___main(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::nat_dec_eq(x_2, x_4);
if (x_5 == 0)
{
obj* x_6; obj* x_7; uint32 x_9; uint8 x_10; obj* x_11; obj* x_13; obj* x_14; 
x_6 = lean::mk_nat_obj(1u);
x_7 = lean::nat_sub(x_2, x_6);
lean::dec(x_2);
x_9 = lean::string_iterator_curr(x_1);
x_10 = l_char_is__digit(x_9);
x_11 = lean::nat_mul(x_3, x_0);
lean::dec(x_3);
x_13 = lean::string_iterator_next(x_1);
if (x_10 == 0)
{
obj* x_16; 
x_16 = lean::box(0);
x_14 = x_16;
goto lbl_15;
}
else
{
obj* x_17; obj* x_18; obj* x_19; obj* x_21; 
x_17 = lean::uint32_to_nat(x_9);
x_18 = l___private_init_data_string_basic_4__to__nat__core___main___closed__1;
x_19 = lean::nat_sub(x_17, x_18);
lean::dec(x_17);
x_21 = lean::nat_add(x_11, x_19);
lean::dec(x_19);
lean::dec(x_11);
x_1 = x_13;
x_2 = x_7;
x_3 = x_21;
goto _start;
}
lbl_15:
{
uint32 x_26; uint8 x_27; 
lean::dec(x_14);
x_26 = 97;
x_27 = x_26 <= x_9;
if (x_27 == 0)
{
obj* x_28; obj* x_29; obj* x_30; obj* x_32; 
x_28 = lean::uint32_to_nat(x_9);
x_29 = l_lean_parser_parse__hex__digit___rarg___lambda__5___closed__1;
x_30 = lean::nat_sub(x_28, x_29);
lean::dec(x_28);
x_32 = lean::nat_add(x_11, x_30);
lean::dec(x_30);
lean::dec(x_11);
x_1 = x_13;
x_2 = x_7;
x_3 = x_32;
goto _start;
}
else
{
uint32 x_36; uint8 x_37; 
x_36 = 102;
x_37 = x_9 <= x_36;
if (x_37 == 0)
{
obj* x_38; obj* x_39; obj* x_40; obj* x_42; 
x_38 = lean::uint32_to_nat(x_9);
x_39 = l_lean_parser_parse__hex__digit___rarg___lambda__5___closed__1;
x_40 = lean::nat_sub(x_38, x_39);
lean::dec(x_38);
x_42 = lean::nat_add(x_11, x_40);
lean::dec(x_40);
lean::dec(x_11);
x_1 = x_13;
x_2 = x_7;
x_3 = x_42;
goto _start;
}
else
{
obj* x_46; obj* x_47; obj* x_48; obj* x_50; 
x_46 = lean::uint32_to_nat(x_9);
x_47 = l_lean_parser_parse__hex__digit___rarg___lambda__3___closed__1;
x_48 = lean::nat_sub(x_46, x_47);
lean::dec(x_46);
x_50 = lean::nat_add(x_11, x_48);
lean::dec(x_48);
lean::dec(x_11);
x_1 = x_13;
x_2 = x_7;
x_3 = x_50;
goto _start;
}
}
}
}
else
{
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
}
obj* l___private_init_lean_parser_token_7__to__nat__core___main___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_parser_token_7__to__nat__core___main(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
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
obj* l___private_init_lean_parser_token_7__to__nat__core___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_parser_token_7__to__nat__core(x_0, x_1, x_2, x_3);
lean::dec(x_0);
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
obj* l___private_init_lean_parser_token_8__to__nat__base___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_init_lean_parser_token_8__to__nat__base(x_0, x_1);
lean::dec(x_1);
return x_2;
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
obj* x_4; 
x_4 = lean::mk_nat_obj(1138u);
return x_4;
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
x_11 = l_string_to__nat(x_8);
return x_11;
}
}
case 1:
{
obj* x_12; 
x_12 = lean::cnstr_get(x_0, 0);
lean::inc(x_12);
lean::dec(x_0);
if (lean::obj_tag(x_12) == 0)
{
obj* x_15; 
x_15 = lean::mk_nat_obj(1138u);
return x_15;
}
else
{
obj* x_16; obj* x_19; obj* x_22; obj* x_23; 
x_16 = lean::cnstr_get(x_12, 0);
lean::inc(x_16);
lean::dec(x_12);
x_19 = lean::cnstr_get(x_16, 1);
lean::inc(x_19);
lean::dec(x_16);
x_22 = lean::mk_nat_obj(2u);
x_23 = l___private_init_lean_parser_token_8__to__nat__base(x_19, x_22);
return x_23;
}
}
case 2:
{
obj* x_24; 
x_24 = lean::cnstr_get(x_0, 0);
lean::inc(x_24);
lean::dec(x_0);
if (lean::obj_tag(x_24) == 0)
{
obj* x_27; 
x_27 = lean::mk_nat_obj(1138u);
return x_27;
}
else
{
obj* x_28; obj* x_31; obj* x_34; obj* x_35; 
x_28 = lean::cnstr_get(x_24, 0);
lean::inc(x_28);
lean::dec(x_24);
x_31 = lean::cnstr_get(x_28, 1);
lean::inc(x_31);
lean::dec(x_28);
x_34 = lean::mk_nat_obj(8u);
x_35 = l___private_init_lean_parser_token_8__to__nat__base(x_31, x_34);
return x_35;
}
}
default:
{
obj* x_36; 
x_36 = lean::cnstr_get(x_0, 0);
lean::inc(x_36);
lean::dec(x_0);
if (lean::obj_tag(x_36) == 0)
{
obj* x_39; 
x_39 = lean::mk_nat_obj(1138u);
return x_39;
}
else
{
obj* x_40; obj* x_43; obj* x_46; obj* x_47; 
x_40 = lean::cnstr_get(x_36, 0);
lean::inc(x_40);
lean::dec(x_36);
x_43 = lean::cnstr_get(x_40, 1);
lean::inc(x_43);
lean::dec(x_40);
x_46 = lean::mk_nat_obj(16u);
x_47 = l___private_init_lean_parser_token_8__to__nat__base(x_43, x_46);
return x_47;
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
obj* x_1; uint8 x_2; 
x_1 = l_lean_parser_string__lit;
x_2 = l_lean_parser_syntax_is__of__kind___main(x_1, x_0);
if (x_2 == 0)
{
obj* x_4; 
lean::dec(x_0);
x_4 = lean::box(0);
return x_4;
}
else
{
obj* x_5; obj* x_6; obj* x_9; obj* x_10; 
x_5 = l_lean_parser_string__lit_has__view;
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
lean::dec(x_5);
x_9 = lean::apply_1(x_6, x_0);
x_10 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_10, 0, x_9);
return x_10;
}
}
}
obj* l_lean_parser_string__lit_parser___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_6; obj* x_7; 
lean::inc(x_2);
lean::inc(x_1);
x_6 = l_lean_parser_token(x_1, x_2, x_3);
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
if (lean::obj_tag(x_7) == 0)
{
obj* x_9; obj* x_11; obj* x_12; obj* x_14; obj* x_16; obj* x_18; obj* x_20; 
x_9 = lean::cnstr_get(x_6, 1);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 lean::cnstr_set(x_6, 1, lean::box(0));
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
 lean::cnstr_set(x_7, 0, lean::box(0));
 lean::cnstr_set(x_7, 1, lean::box(0));
 lean::cnstr_set(x_7, 2, lean::box(0));
 x_18 = x_7;
} else {
 lean::inc(x_12);
 lean::inc(x_14);
 lean::inc(x_16);
 lean::dec(x_7);
 x_18 = lean::box(0);
}
lean::inc(x_12);
x_20 = l_lean_parser_try__view___at_lean_parser_string__lit_parser___spec__1(x_12);
if (lean::obj_tag(x_20) == 0)
{
obj* x_24; obj* x_25; obj* x_26; obj* x_28; obj* x_32; obj* x_34; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; 
lean::dec(x_11);
lean::dec(x_12);
lean::dec(x_18);
x_24 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_24, 0, x_2);
x_25 = lean::box(0);
x_26 = l_string_join___closed__1;
lean::inc(x_0);
x_28 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_26, x_0, x_24, x_25, x_1, x_14, x_9);
lean::dec(x_14);
lean::dec(x_1);
lean::dec(x_24);
x_32 = lean::cnstr_get(x_28, 0);
x_34 = lean::cnstr_get(x_28, 1);
if (lean::is_exclusive(x_28)) {
 x_36 = x_28;
} else {
 lean::inc(x_32);
 lean::inc(x_34);
 lean::dec(x_28);
 x_36 = lean::box(0);
}
x_37 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_38 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_37, x_32);
x_39 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_38);
x_40 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_37, x_39);
x_41 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_40, x_0);
x_42 = l_lean_parser_parsec__t_try__mk__res___rarg(x_41);
if (lean::is_scalar(x_36)) {
 x_43 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_43 = x_36;
}
lean::cnstr_set(x_43, 0, x_42);
lean::cnstr_set(x_43, 1, x_34);
return x_43;
}
else
{
obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; 
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_20);
x_47 = l_lean_parser_finish__comment__block___closed__2;
if (lean::is_scalar(x_18)) {
 x_48 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_48 = x_18;
}
lean::cnstr_set(x_48, 0, x_12);
lean::cnstr_set(x_48, 1, x_14);
lean::cnstr_set(x_48, 2, x_47);
x_49 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_48);
x_50 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_51 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_50, x_49);
x_52 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_51, x_0);
x_53 = l_lean_parser_parsec__t_try__mk__res___rarg(x_52);
if (lean::is_scalar(x_11)) {
 x_54 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_54 = x_11;
}
lean::cnstr_set(x_54, 0, x_53);
lean::cnstr_set(x_54, 1, x_9);
return x_54;
}
}
else
{
obj* x_57; obj* x_59; obj* x_60; uint8 x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; 
lean::dec(x_1);
lean::dec(x_2);
x_57 = lean::cnstr_get(x_6, 1);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 x_59 = x_6;
} else {
 lean::inc(x_57);
 lean::dec(x_6);
 x_59 = lean::box(0);
}
x_60 = lean::cnstr_get(x_7, 0);
x_62 = lean::cnstr_get_scalar<uint8>(x_7, sizeof(void*)*1);
if (lean::is_exclusive(x_7)) {
 x_63 = x_7;
} else {
 lean::inc(x_60);
 lean::dec(x_7);
 x_63 = lean::box(0);
}
if (lean::is_scalar(x_63)) {
 x_64 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_64 = x_63;
}
lean::cnstr_set(x_64, 0, x_60);
lean::cnstr_set_scalar(x_64, sizeof(void*)*1, x_62);
x_65 = x_64;
x_66 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_67 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_66, x_65);
x_68 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_67, x_0);
x_69 = l_lean_parser_parsec__t_try__mk__res___rarg(x_68);
if (lean::is_scalar(x_59)) {
 x_70 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_70 = x_59;
}
lean::cnstr_set(x_70, 0, x_69);
lean::cnstr_set(x_70, 1, x_57);
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
obj* x_1; obj* x_2; 
x_1 = l_lean_parser_string__lit_parser___rarg___closed__1;
x_2 = lean::apply_2(x_0, lean::box(0), x_1);
return x_2;
}
}
obj* l_lean_parser_string__lit_parser(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_string__lit_parser___rarg), 1, 0);
return x_1;
}
}
obj* l_lean_parser_string__lit_parser___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_string__lit_parser(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_parser_string__lit_parser_tokens(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::box(0);
return x_2;
}
}
obj* l_lean_parser_string__lit_parser_tokens___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_parser_string__lit_parser_tokens(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_lean_parser_string__lit_parser_view___rarg___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = l_lean_parser_string__lit_has__view;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
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
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_parser_string__lit_parser_view___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_lean_parser_string__lit_parser_view___rarg___closed__1;
x_2 = l_lean_parser_string__lit_parser_view___rarg___closed__2;
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* l_lean_parser_string__lit_parser_view(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_string__lit_parser_view___rarg___boxed), 1, 0);
return x_1;
}
}
obj* l_lean_parser_string__lit_parser_view___rarg___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_string__lit_parser_view___rarg(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_parser_string__lit_parser_view___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_string__lit_parser_view(x_0);
lean::dec(x_0);
return x_1;
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
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___at_lean_parser_string__lit_view_value___spec__3___rarg___boxed), 5, 0);
return x_1;
}
}
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_string__lit_view_value___spec__2(uint32 x_0, obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = lean::string_iterator_has_next(x_1);
if (x_2 == 0)
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_8; obj* x_9; 
x_3 = lean::box(0);
x_4 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_5 = l_mjoin___rarg___closed__1;
x_6 = l_lean_parser_monad__parsec_error___at_lean_parser_string__lit_view_value___spec__3___rarg(x_4, x_5, x_3, x_3, x_1);
lean::dec(x_1);
x_8 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_9 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_8, x_6);
return x_9;
}
else
{
uint32 x_10; uint8 x_11; 
x_10 = lean::string_iterator_curr(x_1);
x_11 = x_10 == x_0;
if (x_11 == 0)
{
obj* x_12; obj* x_13; obj* x_14; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_21; obj* x_22; 
x_12 = l_char_quote__core(x_10);
x_13 = l_char_has__repr___closed__1;
x_14 = lean::string_append(x_13, x_12);
lean::dec(x_12);
x_16 = lean::string_append(x_14, x_13);
x_17 = lean::box(0);
x_18 = l_mjoin___rarg___closed__1;
x_19 = l_lean_parser_monad__parsec_error___at_lean_parser_string__lit_view_value___spec__3___rarg(x_16, x_18, x_17, x_17, x_1);
lean::dec(x_1);
x_21 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_22 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_21, x_19);
return x_22;
}
else
{
obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
x_23 = lean::string_iterator_next(x_1);
x_24 = lean::box(0);
x_25 = lean::box_uint32(x_10);
x_26 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_23);
lean::cnstr_set(x_26, 2, x_24);
return x_26;
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
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_7; obj* x_8; 
x_2 = lean::box(0);
x_3 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_4 = l_mjoin___rarg___closed__1;
x_5 = l_lean_parser_monad__parsec_error___at_lean_parser_string__lit_view_value___spec__3___rarg(x_3, x_4, x_2, x_2, x_0);
lean::dec(x_0);
x_7 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_8 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_5);
return x_8;
}
else
{
uint32 x_9; uint8 x_10; 
x_9 = lean::string_iterator_curr(x_0);
x_10 = l_true_decidable;
if (x_10 == 0)
{
obj* x_11; obj* x_12; obj* x_13; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_20; obj* x_21; 
x_11 = l_char_quote__core(x_9);
x_12 = l_char_has__repr___closed__1;
x_13 = lean::string_append(x_12, x_11);
lean::dec(x_11);
x_15 = lean::string_append(x_13, x_12);
x_16 = lean::box(0);
x_17 = l_mjoin___rarg___closed__1;
x_18 = l_lean_parser_monad__parsec_error___at_lean_parser_string__lit_view_value___spec__3___rarg(x_15, x_17, x_16, x_16, x_0);
lean::dec(x_0);
x_20 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_21 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_20, x_18);
return x_21;
}
else
{
obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_22 = lean::string_iterator_next(x_0);
x_23 = lean::box(0);
x_24 = lean::box_uint32(x_9);
x_25 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_22);
lean::cnstr_set(x_25, 2, x_23);
return x_25;
}
}
}
}
obj* l_lean_parser_monad__parsec_unexpected__at___at_lean_parser_string__lit_view_value___spec__7___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_3 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_3, 0, x_1);
x_4 = lean::box(0);
x_5 = l_mjoin___rarg___closed__1;
x_6 = l_lean_parser_monad__parsec_error___at_lean_parser_string__lit_view_value___spec__3___rarg(x_0, x_5, x_3, x_4, x_2);
lean::dec(x_3);
return x_6;
}
}
obj* l_lean_parser_monad__parsec_unexpected__at___at_lean_parser_string__lit_view_value___spec__7(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_unexpected__at___at_lean_parser_string__lit_view_value___spec__7___rarg___boxed), 3, 0);
return x_1;
}
}
obj* l_lean_parser_monad__parsec_digit___at_lean_parser_string__lit_view_value___spec__9(obj* x_0) {
_start:
{
uint8 x_1; 
x_1 = lean::string_iterator_has_next(x_0);
if (x_1 == 0)
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_7; obj* x_8; 
x_2 = lean::box(0);
x_3 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_4 = l_mjoin___rarg___closed__1;
x_5 = l_lean_parser_monad__parsec_error___at_lean_parser_string__lit_view_value___spec__3___rarg(x_3, x_4, x_2, x_2, x_0);
lean::dec(x_0);
x_7 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_8 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_5);
return x_8;
}
else
{
uint32 x_9; uint8 x_10; 
x_9 = lean::string_iterator_curr(x_0);
x_10 = l_char_is__digit(x_9);
if (x_10 == 0)
{
obj* x_11; obj* x_12; obj* x_13; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_20; obj* x_21; 
x_11 = l_char_quote__core(x_9);
x_12 = l_char_has__repr___closed__1;
x_13 = lean::string_append(x_12, x_11);
lean::dec(x_11);
x_15 = lean::string_append(x_13, x_12);
x_16 = lean::box(0);
x_17 = l_mjoin___rarg___closed__1;
x_18 = l_lean_parser_monad__parsec_error___at_lean_parser_string__lit_view_value___spec__3___rarg(x_15, x_17, x_16, x_16, x_0);
lean::dec(x_0);
x_20 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_21 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_20, x_18);
return x_21;
}
else
{
obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_22 = lean::string_iterator_next(x_0);
x_23 = lean::box(0);
x_24 = lean::box_uint32(x_9);
x_25 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_22);
lean::cnstr_set(x_25, 2, x_23);
return x_25;
}
}
}
}
obj* l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_view_value___spec__8(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; uint8 x_3; obj* x_6; 
lean::inc(x_0);
x_6 = l_lean_parser_monad__parsec_digit___at_lean_parser_string__lit_view_value___spec__9(x_0);
if (lean::obj_tag(x_6) == 0)
{
obj* x_7; obj* x_9; obj* x_11; obj* x_13; uint32 x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_19; obj* x_20; obj* x_21; 
x_7 = lean::cnstr_get(x_6, 0);
x_9 = lean::cnstr_get(x_6, 1);
x_11 = lean::cnstr_get(x_6, 2);
if (lean::is_exclusive(x_6)) {
 x_13 = x_6;
} else {
 lean::inc(x_7);
 lean::inc(x_9);
 lean::inc(x_11);
 lean::dec(x_6);
 x_13 = lean::box(0);
}
x_14 = lean::unbox_uint32(x_7);
x_15 = lean::uint32_to_nat(x_14);
x_16 = l___private_init_data_string_basic_4__to__nat__core___main___closed__1;
x_17 = lean::nat_sub(x_15, x_16);
lean::dec(x_15);
x_19 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_13)) {
 x_20 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_20 = x_13;
}
lean::cnstr_set(x_20, 0, x_17);
lean::cnstr_set(x_20, 1, x_9);
lean::cnstr_set(x_20, 2, x_19);
x_21 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_11, x_20);
if (lean::obj_tag(x_21) == 0)
{
obj* x_23; obj* x_24; 
lean::dec(x_0);
x_23 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__5___closed__1;
x_24 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_21, x_23);
return x_24;
}
else
{
obj* x_25; uint8 x_27; 
x_25 = lean::cnstr_get(x_21, 0);
lean::inc(x_25);
x_27 = lean::cnstr_get_scalar<uint8>(x_21, sizeof(void*)*1);
x_1 = x_21;
x_2 = x_25;
x_3 = x_27;
goto lbl_4;
}
}
else
{
obj* x_28; uint8 x_30; obj* x_31; obj* x_33; obj* x_34; 
x_28 = lean::cnstr_get(x_6, 0);
x_30 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*1);
if (lean::is_exclusive(x_6)) {
 x_31 = x_6;
} else {
 lean::inc(x_28);
 lean::dec(x_6);
 x_31 = lean::box(0);
}
lean::inc(x_28);
if (lean::is_scalar(x_31)) {
 x_33 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_33 = x_31;
}
lean::cnstr_set(x_33, 0, x_28);
lean::cnstr_set_scalar(x_33, sizeof(void*)*1, x_30);
x_34 = x_33;
x_1 = x_34;
x_2 = x_28;
x_3 = x_30;
goto lbl_4;
}
lbl_4:
{
obj* x_35; obj* x_36; uint8 x_37; 
if (x_3 == 0)
{
obj* x_40; uint8 x_42; 
lean::dec(x_1);
x_42 = lean::string_iterator_has_next(x_0);
if (x_42 == 0)
{
obj* x_43; obj* x_44; obj* x_45; obj* x_46; 
x_43 = lean::box(0);
x_44 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_45 = l_mjoin___rarg___closed__1;
x_46 = l_lean_parser_monad__parsec_error___at_lean_parser_string__lit_view_value___spec__3___rarg(x_44, x_45, x_43, x_43, x_0);
x_40 = x_46;
goto lbl_41;
}
else
{
uint32 x_47; uint32 x_48; uint8 x_49; uint8 x_51; 
x_47 = lean::string_iterator_curr(x_0);
x_48 = 97;
x_51 = x_48 <= x_47;
if (x_51 == 0)
{
obj* x_52; obj* x_53; obj* x_54; obj* x_56; obj* x_57; obj* x_58; obj* x_59; 
x_52 = l_char_quote__core(x_47);
x_53 = l_char_has__repr___closed__1;
x_54 = lean::string_append(x_53, x_52);
lean::dec(x_52);
x_56 = lean::string_append(x_54, x_53);
x_57 = lean::box(0);
x_58 = l_mjoin___rarg___closed__1;
x_59 = l_lean_parser_monad__parsec_error___at_lean_parser_string__lit_view_value___spec__3___rarg(x_56, x_58, x_57, x_57, x_0);
x_40 = x_59;
goto lbl_41;
}
else
{
uint8 x_60; 
x_60 = 1;
x_49 = x_60;
goto lbl_50;
}
lbl_50:
{
uint32 x_61; uint8 x_62; 
x_61 = 102;
x_62 = x_47 <= x_61;
if (x_62 == 0)
{
obj* x_63; obj* x_64; obj* x_65; obj* x_67; obj* x_68; obj* x_69; obj* x_70; 
x_63 = l_char_quote__core(x_47);
x_64 = l_char_has__repr___closed__1;
x_65 = lean::string_append(x_64, x_63);
lean::dec(x_63);
x_67 = lean::string_append(x_65, x_64);
x_68 = lean::box(0);
x_69 = l_mjoin___rarg___closed__1;
x_70 = l_lean_parser_monad__parsec_error___at_lean_parser_string__lit_view_value___spec__3___rarg(x_67, x_69, x_68, x_68, x_0);
x_40 = x_70;
goto lbl_41;
}
else
{
if (x_49 == 0)
{
obj* x_71; obj* x_72; obj* x_73; obj* x_75; obj* x_76; obj* x_77; obj* x_78; 
x_71 = l_char_quote__core(x_47);
x_72 = l_char_has__repr___closed__1;
x_73 = lean::string_append(x_72, x_71);
lean::dec(x_71);
x_75 = lean::string_append(x_73, x_72);
x_76 = lean::box(0);
x_77 = l_mjoin___rarg___closed__1;
x_78 = l_lean_parser_monad__parsec_error___at_lean_parser_string__lit_view_value___spec__3___rarg(x_75, x_77, x_76, x_76, x_0);
x_40 = x_78;
goto lbl_41;
}
else
{
obj* x_80; obj* x_81; obj* x_82; obj* x_83; 
lean::inc(x_0);
x_80 = lean::string_iterator_next(x_0);
x_81 = lean::box(0);
x_82 = lean::box_uint32(x_47);
x_83 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_83, 0, x_82);
lean::cnstr_set(x_83, 1, x_80);
lean::cnstr_set(x_83, 2, x_81);
x_40 = x_83;
goto lbl_41;
}
}
}
}
lbl_41:
{
obj* x_84; obj* x_85; 
x_84 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_85 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_84, x_40);
if (lean::obj_tag(x_85) == 0)
{
obj* x_86; obj* x_88; obj* x_90; obj* x_92; uint32 x_93; obj* x_94; obj* x_95; obj* x_96; obj* x_98; obj* x_99; obj* x_101; obj* x_102; 
x_86 = lean::cnstr_get(x_85, 0);
x_88 = lean::cnstr_get(x_85, 1);
x_90 = lean::cnstr_get(x_85, 2);
if (lean::is_exclusive(x_85)) {
 x_92 = x_85;
} else {
 lean::inc(x_86);
 lean::inc(x_88);
 lean::inc(x_90);
 lean::dec(x_85);
 x_92 = lean::box(0);
}
x_93 = lean::unbox_uint32(x_86);
x_94 = lean::uint32_to_nat(x_93);
x_95 = l_lean_parser_parse__hex__digit___rarg___lambda__3___closed__1;
x_96 = lean::nat_sub(x_94, x_95);
lean::dec(x_94);
x_98 = lean::mk_nat_obj(10u);
x_99 = lean::nat_add(x_98, x_96);
lean::dec(x_96);
if (lean::is_scalar(x_92)) {
 x_101 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_101 = x_92;
}
lean::cnstr_set(x_101, 0, x_99);
lean::cnstr_set(x_101, 1, x_88);
lean::cnstr_set(x_101, 2, x_84);
x_102 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_90, x_101);
if (lean::obj_tag(x_102) == 0)
{
obj* x_104; obj* x_105; obj* x_106; 
lean::dec(x_0);
x_104 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_2, x_102);
x_105 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__5___closed__1;
x_106 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_104, x_105);
return x_106;
}
else
{
obj* x_107; uint8 x_109; 
x_107 = lean::cnstr_get(x_102, 0);
lean::inc(x_107);
x_109 = lean::cnstr_get_scalar<uint8>(x_102, sizeof(void*)*1);
x_35 = x_102;
x_36 = x_107;
x_37 = x_109;
goto lbl_38;
}
}
else
{
obj* x_110; uint8 x_112; obj* x_113; obj* x_115; obj* x_116; 
x_110 = lean::cnstr_get(x_85, 0);
x_112 = lean::cnstr_get_scalar<uint8>(x_85, sizeof(void*)*1);
if (lean::is_exclusive(x_85)) {
 x_113 = x_85;
} else {
 lean::inc(x_110);
 lean::dec(x_85);
 x_113 = lean::box(0);
}
lean::inc(x_110);
if (lean::is_scalar(x_113)) {
 x_115 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_115 = x_113;
}
lean::cnstr_set(x_115, 0, x_110);
lean::cnstr_set_scalar(x_115, sizeof(void*)*1, x_112);
x_116 = x_115;
x_35 = x_116;
x_36 = x_110;
x_37 = x_112;
goto lbl_38;
}
}
}
else
{
obj* x_119; obj* x_120; 
lean::dec(x_0);
lean::dec(x_2);
x_119 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__5___closed__1;
x_120 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_1, x_119);
return x_120;
}
lbl_38:
{
if (x_37 == 0)
{
obj* x_122; uint8 x_124; 
lean::dec(x_35);
x_124 = lean::string_iterator_has_next(x_0);
if (x_124 == 0)
{
obj* x_125; obj* x_126; obj* x_127; obj* x_128; 
x_125 = lean::box(0);
x_126 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_127 = l_mjoin___rarg___closed__1;
x_128 = l_lean_parser_monad__parsec_error___at_lean_parser_string__lit_view_value___spec__3___rarg(x_126, x_127, x_125, x_125, x_0);
lean::dec(x_0);
x_122 = x_128;
goto lbl_123;
}
else
{
uint32 x_130; uint32 x_131; uint8 x_132; uint8 x_134; 
x_130 = lean::string_iterator_curr(x_0);
x_131 = 65;
x_134 = x_131 <= x_130;
if (x_134 == 0)
{
obj* x_135; obj* x_136; obj* x_137; obj* x_139; obj* x_140; obj* x_141; obj* x_142; 
x_135 = l_char_quote__core(x_130);
x_136 = l_char_has__repr___closed__1;
x_137 = lean::string_append(x_136, x_135);
lean::dec(x_135);
x_139 = lean::string_append(x_137, x_136);
x_140 = lean::box(0);
x_141 = l_mjoin___rarg___closed__1;
x_142 = l_lean_parser_monad__parsec_error___at_lean_parser_string__lit_view_value___spec__3___rarg(x_139, x_141, x_140, x_140, x_0);
lean::dec(x_0);
x_122 = x_142;
goto lbl_123;
}
else
{
uint8 x_144; 
x_144 = 1;
x_132 = x_144;
goto lbl_133;
}
lbl_133:
{
uint32 x_145; uint8 x_146; 
x_145 = 70;
x_146 = x_130 <= x_145;
if (x_146 == 0)
{
obj* x_147; obj* x_148; obj* x_149; obj* x_151; obj* x_152; obj* x_153; obj* x_154; 
x_147 = l_char_quote__core(x_130);
x_148 = l_char_has__repr___closed__1;
x_149 = lean::string_append(x_148, x_147);
lean::dec(x_147);
x_151 = lean::string_append(x_149, x_148);
x_152 = lean::box(0);
x_153 = l_mjoin___rarg___closed__1;
x_154 = l_lean_parser_monad__parsec_error___at_lean_parser_string__lit_view_value___spec__3___rarg(x_151, x_153, x_152, x_152, x_0);
lean::dec(x_0);
x_122 = x_154;
goto lbl_123;
}
else
{
if (x_132 == 0)
{
obj* x_156; obj* x_157; obj* x_158; obj* x_160; obj* x_161; obj* x_162; obj* x_163; 
x_156 = l_char_quote__core(x_130);
x_157 = l_char_has__repr___closed__1;
x_158 = lean::string_append(x_157, x_156);
lean::dec(x_156);
x_160 = lean::string_append(x_158, x_157);
x_161 = lean::box(0);
x_162 = l_mjoin___rarg___closed__1;
x_163 = l_lean_parser_monad__parsec_error___at_lean_parser_string__lit_view_value___spec__3___rarg(x_160, x_162, x_161, x_161, x_0);
lean::dec(x_0);
x_122 = x_163;
goto lbl_123;
}
else
{
obj* x_165; obj* x_166; obj* x_167; obj* x_168; 
x_165 = lean::string_iterator_next(x_0);
x_166 = lean::box(0);
x_167 = lean::box_uint32(x_130);
x_168 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_168, 0, x_167);
lean::cnstr_set(x_168, 1, x_165);
lean::cnstr_set(x_168, 2, x_166);
x_122 = x_168;
goto lbl_123;
}
}
}
}
lbl_123:
{
obj* x_169; obj* x_170; 
x_169 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_170 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_169, x_122);
if (lean::obj_tag(x_170) == 0)
{
obj* x_171; obj* x_173; obj* x_175; obj* x_177; uint32 x_178; obj* x_179; obj* x_180; obj* x_181; obj* x_183; obj* x_184; obj* x_186; obj* x_187; obj* x_188; obj* x_189; obj* x_190; obj* x_191; 
x_171 = lean::cnstr_get(x_170, 0);
x_173 = lean::cnstr_get(x_170, 1);
x_175 = lean::cnstr_get(x_170, 2);
if (lean::is_exclusive(x_170)) {
 x_177 = x_170;
} else {
 lean::inc(x_171);
 lean::inc(x_173);
 lean::inc(x_175);
 lean::dec(x_170);
 x_177 = lean::box(0);
}
x_178 = lean::unbox_uint32(x_171);
x_179 = lean::uint32_to_nat(x_178);
x_180 = l_lean_parser_parse__hex__digit___rarg___lambda__5___closed__1;
x_181 = lean::nat_sub(x_179, x_180);
lean::dec(x_179);
x_183 = lean::mk_nat_obj(10u);
x_184 = lean::nat_add(x_183, x_181);
lean::dec(x_181);
if (lean::is_scalar(x_177)) {
 x_186 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_186 = x_177;
}
lean::cnstr_set(x_186, 0, x_184);
lean::cnstr_set(x_186, 1, x_173);
lean::cnstr_set(x_186, 2, x_169);
x_187 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_175, x_186);
x_188 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_36, x_187);
x_189 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_2, x_188);
x_190 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__5___closed__1;
x_191 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_189, x_190);
return x_191;
}
else
{
obj* x_192; uint8 x_194; obj* x_195; obj* x_196; obj* x_197; obj* x_198; obj* x_199; obj* x_200; obj* x_201; 
x_192 = lean::cnstr_get(x_170, 0);
x_194 = lean::cnstr_get_scalar<uint8>(x_170, sizeof(void*)*1);
if (lean::is_exclusive(x_170)) {
 x_195 = x_170;
} else {
 lean::inc(x_192);
 lean::dec(x_170);
 x_195 = lean::box(0);
}
if (lean::is_scalar(x_195)) {
 x_196 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_196 = x_195;
}
lean::cnstr_set(x_196, 0, x_192);
lean::cnstr_set_scalar(x_196, sizeof(void*)*1, x_194);
x_197 = x_196;
x_198 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_36, x_197);
x_199 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_2, x_198);
x_200 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__5___closed__1;
x_201 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_199, x_200);
return x_201;
}
}
}
else
{
obj* x_204; obj* x_205; obj* x_206; 
lean::dec(x_36);
lean::dec(x_0);
x_204 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_2, x_35);
x_205 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__5___closed__1;
x_206 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_204, x_205);
return x_206;
}
}
}
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
obj* x_3; obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_14; uint32 x_16; uint32 x_17; uint8 x_18; 
x_3 = lean::cnstr_get(x_2, 0);
x_5 = lean::cnstr_get(x_2, 1);
x_7 = lean::cnstr_get(x_2, 2);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_set(x_2, 0, lean::box(0));
 lean::cnstr_set(x_2, 1, lean::box(0));
 lean::cnstr_set(x_2, 2, lean::box(0));
 x_9 = x_2;
} else {
 lean::inc(x_3);
 lean::inc(x_5);
 lean::inc(x_7);
 lean::dec(x_2);
 x_9 = lean::box(0);
}
x_16 = 92;
x_17 = lean::unbox_uint32(x_3);
x_18 = x_17 == x_16;
if (x_18 == 0)
{
obj* x_19; 
x_19 = lean::box(0);
x_14 = x_19;
goto lbl_15;
}
else
{
obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
lean::dec(x_9);
lean::dec(x_0);
x_22 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_23 = lean::box_uint32(x_16);
x_24 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_5);
lean::cnstr_set(x_24, 2, x_22);
x_25 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_24);
x_26 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_22, x_25);
return x_26;
}
lbl_11:
{
uint32 x_28; uint32 x_29; uint8 x_30; 
lean::dec(x_10);
x_28 = 117;
x_29 = lean::unbox_uint32(x_3);
x_30 = x_29 == x_28;
if (x_30 == 0)
{
obj* x_31; obj* x_32; obj* x_34; obj* x_35; obj* x_36; 
x_31 = l_lean_parser_parse__quoted__char___rarg___lambda__7___closed__1;
x_32 = l_lean_parser_monad__parsec_unexpected__at___at_lean_parser_string__lit_view_value___spec__7___rarg(x_31, x_0, x_5);
lean::dec(x_5);
x_34 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_32);
x_35 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_36 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_35, x_34);
return x_36;
}
else
{
obj* x_38; 
lean::dec(x_0);
x_38 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_view_value___spec__8(x_5);
if (lean::obj_tag(x_38) == 0)
{
obj* x_39; obj* x_41; obj* x_43; obj* x_46; 
x_39 = lean::cnstr_get(x_38, 0);
lean::inc(x_39);
x_41 = lean::cnstr_get(x_38, 1);
lean::inc(x_41);
x_43 = lean::cnstr_get(x_38, 2);
lean::inc(x_43);
lean::dec(x_38);
x_46 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_view_value___spec__8(x_41);
if (lean::obj_tag(x_46) == 0)
{
obj* x_47; obj* x_49; obj* x_51; obj* x_54; 
x_47 = lean::cnstr_get(x_46, 0);
lean::inc(x_47);
x_49 = lean::cnstr_get(x_46, 1);
lean::inc(x_49);
x_51 = lean::cnstr_get(x_46, 2);
lean::inc(x_51);
lean::dec(x_46);
x_54 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_view_value___spec__8(x_49);
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
x_62 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_view_value___spec__8(x_57);
if (lean::obj_tag(x_62) == 0)
{
obj* x_63; obj* x_65; obj* x_67; obj* x_69; obj* x_70; obj* x_71; obj* x_73; obj* x_76; obj* x_78; obj* x_81; obj* x_83; uint32 x_86; obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_95; obj* x_96; 
x_63 = lean::cnstr_get(x_62, 0);
x_65 = lean::cnstr_get(x_62, 1);
x_67 = lean::cnstr_get(x_62, 2);
if (lean::is_exclusive(x_62)) {
 x_69 = x_62;
} else {
 lean::inc(x_63);
 lean::inc(x_65);
 lean::inc(x_67);
 lean::dec(x_62);
 x_69 = lean::box(0);
}
x_70 = lean::mk_nat_obj(16u);
x_71 = lean::nat_mul(x_70, x_39);
lean::dec(x_39);
x_73 = lean::nat_add(x_71, x_47);
lean::dec(x_47);
lean::dec(x_71);
x_76 = lean::nat_mul(x_70, x_73);
lean::dec(x_73);
x_78 = lean::nat_add(x_76, x_55);
lean::dec(x_55);
lean::dec(x_76);
x_81 = lean::nat_mul(x_70, x_78);
lean::dec(x_78);
x_83 = lean::nat_add(x_81, x_63);
lean::dec(x_63);
lean::dec(x_81);
x_86 = l_char_of__nat(x_83);
lean::dec(x_83);
x_88 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_89 = lean::box_uint32(x_86);
if (lean::is_scalar(x_69)) {
 x_90 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_90 = x_69;
}
lean::cnstr_set(x_90, 0, x_89);
lean::cnstr_set(x_90, 1, x_65);
lean::cnstr_set(x_90, 2, x_88);
x_91 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_67, x_90);
x_92 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_59, x_91);
x_93 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_51, x_92);
x_94 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_43, x_93);
x_95 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_94);
x_96 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_88, x_95);
return x_96;
}
else
{
obj* x_100; uint8 x_102; obj* x_103; obj* x_104; obj* x_105; obj* x_106; obj* x_107; obj* x_108; obj* x_109; obj* x_110; obj* x_111; 
lean::dec(x_47);
lean::dec(x_55);
lean::dec(x_39);
x_100 = lean::cnstr_get(x_62, 0);
x_102 = lean::cnstr_get_scalar<uint8>(x_62, sizeof(void*)*1);
if (lean::is_exclusive(x_62)) {
 x_103 = x_62;
} else {
 lean::inc(x_100);
 lean::dec(x_62);
 x_103 = lean::box(0);
}
if (lean::is_scalar(x_103)) {
 x_104 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_104 = x_103;
}
lean::cnstr_set(x_104, 0, x_100);
lean::cnstr_set_scalar(x_104, sizeof(void*)*1, x_102);
x_105 = x_104;
x_106 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_59, x_105);
x_107 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_51, x_106);
x_108 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_43, x_107);
x_109 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_108);
x_110 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_111 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_110, x_109);
return x_111;
}
}
else
{
obj* x_114; uint8 x_116; obj* x_117; obj* x_118; obj* x_119; obj* x_120; obj* x_121; obj* x_122; obj* x_123; obj* x_124; 
lean::dec(x_47);
lean::dec(x_39);
x_114 = lean::cnstr_get(x_54, 0);
x_116 = lean::cnstr_get_scalar<uint8>(x_54, sizeof(void*)*1);
if (lean::is_exclusive(x_54)) {
 x_117 = x_54;
} else {
 lean::inc(x_114);
 lean::dec(x_54);
 x_117 = lean::box(0);
}
if (lean::is_scalar(x_117)) {
 x_118 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_118 = x_117;
}
lean::cnstr_set(x_118, 0, x_114);
lean::cnstr_set_scalar(x_118, sizeof(void*)*1, x_116);
x_119 = x_118;
x_120 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_51, x_119);
x_121 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_43, x_120);
x_122 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_121);
x_123 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_124 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_123, x_122);
return x_124;
}
}
else
{
obj* x_126; uint8 x_128; obj* x_129; obj* x_130; obj* x_131; obj* x_132; obj* x_133; obj* x_134; obj* x_135; 
lean::dec(x_39);
x_126 = lean::cnstr_get(x_46, 0);
x_128 = lean::cnstr_get_scalar<uint8>(x_46, sizeof(void*)*1);
if (lean::is_exclusive(x_46)) {
 x_129 = x_46;
} else {
 lean::inc(x_126);
 lean::dec(x_46);
 x_129 = lean::box(0);
}
if (lean::is_scalar(x_129)) {
 x_130 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_130 = x_129;
}
lean::cnstr_set(x_130, 0, x_126);
lean::cnstr_set_scalar(x_130, sizeof(void*)*1, x_128);
x_131 = x_130;
x_132 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_43, x_131);
x_133 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_132);
x_134 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_135 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_134, x_133);
return x_135;
}
}
else
{
obj* x_136; uint8 x_138; obj* x_139; obj* x_140; obj* x_141; obj* x_142; obj* x_143; obj* x_144; 
x_136 = lean::cnstr_get(x_38, 0);
x_138 = lean::cnstr_get_scalar<uint8>(x_38, sizeof(void*)*1);
if (lean::is_exclusive(x_38)) {
 x_139 = x_38;
} else {
 lean::inc(x_136);
 lean::dec(x_38);
 x_139 = lean::box(0);
}
if (lean::is_scalar(x_139)) {
 x_140 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_140 = x_139;
}
lean::cnstr_set(x_140, 0, x_136);
lean::cnstr_set_scalar(x_140, sizeof(void*)*1, x_138);
x_141 = x_140;
x_142 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_141);
x_143 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_144 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_143, x_142);
return x_144;
}
}
}
lbl_13:
{
uint32 x_146; uint32 x_147; uint8 x_148; 
lean::dec(x_12);
x_146 = 116;
x_147 = lean::unbox_uint32(x_3);
x_148 = x_147 == x_146;
if (x_148 == 0)
{
uint32 x_150; uint8 x_151; 
lean::dec(x_9);
x_150 = 120;
x_151 = x_147 == x_150;
if (x_151 == 0)
{
obj* x_152; 
x_152 = lean::box(0);
x_10 = x_152;
goto lbl_11;
}
else
{
obj* x_154; 
lean::dec(x_0);
x_154 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_view_value___spec__8(x_5);
if (lean::obj_tag(x_154) == 0)
{
obj* x_155; obj* x_157; obj* x_159; obj* x_162; 
x_155 = lean::cnstr_get(x_154, 0);
lean::inc(x_155);
x_157 = lean::cnstr_get(x_154, 1);
lean::inc(x_157);
x_159 = lean::cnstr_get(x_154, 2);
lean::inc(x_159);
lean::dec(x_154);
x_162 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_view_value___spec__8(x_157);
if (lean::obj_tag(x_162) == 0)
{
obj* x_163; obj* x_165; obj* x_167; obj* x_169; obj* x_170; obj* x_171; obj* x_173; uint32 x_176; obj* x_178; obj* x_179; obj* x_180; obj* x_181; obj* x_182; obj* x_183; obj* x_184; 
x_163 = lean::cnstr_get(x_162, 0);
x_165 = lean::cnstr_get(x_162, 1);
x_167 = lean::cnstr_get(x_162, 2);
if (lean::is_exclusive(x_162)) {
 x_169 = x_162;
} else {
 lean::inc(x_163);
 lean::inc(x_165);
 lean::inc(x_167);
 lean::dec(x_162);
 x_169 = lean::box(0);
}
x_170 = lean::mk_nat_obj(16u);
x_171 = lean::nat_mul(x_170, x_155);
lean::dec(x_155);
x_173 = lean::nat_add(x_171, x_163);
lean::dec(x_163);
lean::dec(x_171);
x_176 = l_char_of__nat(x_173);
lean::dec(x_173);
x_178 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_179 = lean::box_uint32(x_176);
if (lean::is_scalar(x_169)) {
 x_180 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_180 = x_169;
}
lean::cnstr_set(x_180, 0, x_179);
lean::cnstr_set(x_180, 1, x_165);
lean::cnstr_set(x_180, 2, x_178);
x_181 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_167, x_180);
x_182 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_159, x_181);
x_183 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_182);
x_184 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_178, x_183);
return x_184;
}
else
{
obj* x_186; uint8 x_188; obj* x_189; obj* x_190; obj* x_191; obj* x_192; obj* x_193; obj* x_194; obj* x_195; 
lean::dec(x_155);
x_186 = lean::cnstr_get(x_162, 0);
x_188 = lean::cnstr_get_scalar<uint8>(x_162, sizeof(void*)*1);
if (lean::is_exclusive(x_162)) {
 x_189 = x_162;
} else {
 lean::inc(x_186);
 lean::dec(x_162);
 x_189 = lean::box(0);
}
if (lean::is_scalar(x_189)) {
 x_190 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_190 = x_189;
}
lean::cnstr_set(x_190, 0, x_186);
lean::cnstr_set_scalar(x_190, sizeof(void*)*1, x_188);
x_191 = x_190;
x_192 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_159, x_191);
x_193 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_192);
x_194 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_195 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_194, x_193);
return x_195;
}
}
else
{
obj* x_196; uint8 x_198; obj* x_199; obj* x_200; obj* x_201; obj* x_202; obj* x_203; obj* x_204; 
x_196 = lean::cnstr_get(x_154, 0);
x_198 = lean::cnstr_get_scalar<uint8>(x_154, sizeof(void*)*1);
if (lean::is_exclusive(x_154)) {
 x_199 = x_154;
} else {
 lean::inc(x_196);
 lean::dec(x_154);
 x_199 = lean::box(0);
}
if (lean::is_scalar(x_199)) {
 x_200 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_200 = x_199;
}
lean::cnstr_set(x_200, 0, x_196);
lean::cnstr_set_scalar(x_200, sizeof(void*)*1, x_198);
x_201 = x_200;
x_202 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_201);
x_203 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_204 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_203, x_202);
return x_204;
}
}
}
else
{
uint32 x_206; obj* x_207; obj* x_208; obj* x_209; obj* x_210; obj* x_211; 
lean::dec(x_0);
x_206 = 9;
x_207 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_208 = lean::box_uint32(x_206);
if (lean::is_scalar(x_9)) {
 x_209 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_209 = x_9;
}
lean::cnstr_set(x_209, 0, x_208);
lean::cnstr_set(x_209, 1, x_5);
lean::cnstr_set(x_209, 2, x_207);
x_210 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_209);
x_211 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_207, x_210);
return x_211;
}
}
lbl_15:
{
uint32 x_213; uint32 x_214; uint8 x_215; 
lean::dec(x_14);
x_213 = 34;
x_214 = lean::unbox_uint32(x_3);
x_215 = x_214 == x_213;
if (x_215 == 0)
{
uint32 x_216; uint8 x_217; 
x_216 = 39;
x_217 = x_214 == x_216;
if (x_217 == 0)
{
uint32 x_218; uint8 x_219; 
x_218 = 110;
x_219 = x_214 == x_218;
if (x_219 == 0)
{
obj* x_220; 
x_220 = lean::box(0);
x_12 = x_220;
goto lbl_13;
}
else
{
uint32 x_223; obj* x_224; obj* x_225; obj* x_226; obj* x_227; obj* x_228; 
lean::dec(x_9);
lean::dec(x_0);
x_223 = 10;
x_224 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_225 = lean::box_uint32(x_223);
x_226 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_226, 0, x_225);
lean::cnstr_set(x_226, 1, x_5);
lean::cnstr_set(x_226, 2, x_224);
x_227 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_226);
x_228 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_224, x_227);
return x_228;
}
}
else
{
obj* x_231; obj* x_232; obj* x_233; obj* x_234; obj* x_235; 
lean::dec(x_9);
lean::dec(x_0);
x_231 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_232 = lean::box_uint32(x_216);
x_233 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_233, 0, x_232);
lean::cnstr_set(x_233, 1, x_5);
lean::cnstr_set(x_233, 2, x_231);
x_234 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_233);
x_235 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_231, x_234);
return x_235;
}
}
else
{
obj* x_238; obj* x_239; obj* x_240; obj* x_241; obj* x_242; 
lean::dec(x_9);
lean::dec(x_0);
x_238 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_239 = lean::box_uint32(x_213);
x_240 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_240, 0, x_239);
lean::cnstr_set(x_240, 1, x_5);
lean::cnstr_set(x_240, 2, x_238);
x_241 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_240);
x_242 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_238, x_241);
return x_242;
}
}
}
else
{
obj* x_244; uint8 x_246; obj* x_247; obj* x_248; obj* x_249; obj* x_250; obj* x_251; 
lean::dec(x_0);
x_244 = lean::cnstr_get(x_2, 0);
x_246 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*1);
if (lean::is_exclusive(x_2)) {
 x_247 = x_2;
} else {
 lean::inc(x_244);
 lean::dec(x_2);
 x_247 = lean::box(0);
}
if (lean::is_scalar(x_247)) {
 x_248 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_248 = x_247;
}
lean::cnstr_set(x_248, 0, x_244);
lean::cnstr_set_scalar(x_248, sizeof(void*)*1, x_246);
x_249 = x_248;
x_250 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_251 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_250, x_249);
return x_251;
}
}
}
obj* l_lean_parser_parse__string__literal__aux___main___at_lean_parser_string__lit_view_value___spec__4(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
obj* x_5; 
x_5 = l_lean_parser_monad__parsec_any___at_lean_parser_string__lit_view_value___spec__5(x_2);
if (lean::obj_tag(x_5) == 0)
{
obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_13; obj* x_14; uint32 x_15; uint32 x_16; uint8 x_17; 
x_6 = lean::cnstr_get(x_5, 0);
x_8 = lean::cnstr_get(x_5, 1);
x_10 = lean::cnstr_get(x_5, 2);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_set(x_5, 0, lean::box(0));
 lean::cnstr_set(x_5, 1, lean::box(0));
 lean::cnstr_set(x_5, 2, lean::box(0));
 x_12 = x_5;
} else {
 lean::inc(x_6);
 lean::inc(x_8);
 lean::inc(x_10);
 lean::dec(x_5);
 x_12 = lean::box(0);
}
x_13 = lean::mk_nat_obj(1u);
x_14 = lean::nat_sub(x_0, x_13);
x_15 = 92;
x_16 = lean::unbox_uint32(x_6);
x_17 = x_16 == x_15;
if (x_17 == 0)
{
uint32 x_18; uint8 x_19; 
x_18 = 34;
x_19 = x_16 == x_18;
if (x_19 == 0)
{
obj* x_21; obj* x_22; obj* x_24; 
lean::dec(x_12);
x_21 = lean::string_push(x_1, x_16);
x_22 = l_lean_parser_parse__string__literal__aux___main___at_lean_parser_string__lit_view_value___spec__4(x_14, x_21, x_8);
lean::dec(x_14);
x_24 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_10, x_22);
return x_24;
}
else
{
obj* x_26; obj* x_27; obj* x_28; 
lean::dec(x_14);
x_26 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_12)) {
 x_27 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_27 = x_12;
}
lean::cnstr_set(x_27, 0, x_1);
lean::cnstr_set(x_27, 1, x_8);
lean::cnstr_set(x_27, 2, x_26);
x_28 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_10, x_27);
return x_28;
}
}
else
{
obj* x_30; 
lean::dec(x_12);
x_30 = l_lean_parser_parse__quoted__char___at_lean_parser_string__lit_view_value___spec__6(x_8);
if (lean::obj_tag(x_30) == 0)
{
obj* x_31; obj* x_33; obj* x_35; uint32 x_38; obj* x_39; obj* x_40; obj* x_42; obj* x_43; 
x_31 = lean::cnstr_get(x_30, 0);
lean::inc(x_31);
x_33 = lean::cnstr_get(x_30, 1);
lean::inc(x_33);
x_35 = lean::cnstr_get(x_30, 2);
lean::inc(x_35);
lean::dec(x_30);
x_38 = lean::unbox_uint32(x_31);
x_39 = lean::string_push(x_1, x_38);
x_40 = l_lean_parser_parse__string__literal__aux___main___at_lean_parser_string__lit_view_value___spec__4(x_14, x_39, x_33);
lean::dec(x_14);
x_42 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_35, x_40);
x_43 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_10, x_42);
return x_43;
}
else
{
obj* x_46; uint8 x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; 
lean::dec(x_1);
lean::dec(x_14);
x_46 = lean::cnstr_get(x_30, 0);
x_48 = lean::cnstr_get_scalar<uint8>(x_30, sizeof(void*)*1);
if (lean::is_exclusive(x_30)) {
 x_49 = x_30;
} else {
 lean::inc(x_46);
 lean::dec(x_30);
 x_49 = lean::box(0);
}
if (lean::is_scalar(x_49)) {
 x_50 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_50 = x_49;
}
lean::cnstr_set(x_50, 0, x_46);
lean::cnstr_set_scalar(x_50, sizeof(void*)*1, x_48);
x_51 = x_50;
x_52 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_10, x_51);
return x_52;
}
}
}
else
{
obj* x_54; uint8 x_56; obj* x_57; obj* x_58; obj* x_59; 
lean::dec(x_1);
x_54 = lean::cnstr_get(x_5, 0);
x_56 = lean::cnstr_get_scalar<uint8>(x_5, sizeof(void*)*1);
if (lean::is_exclusive(x_5)) {
 x_57 = x_5;
} else {
 lean::inc(x_54);
 lean::dec(x_5);
 x_57 = lean::box(0);
}
if (lean::is_scalar(x_57)) {
 x_58 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_58 = x_57;
}
lean::cnstr_set(x_58, 0, x_54);
lean::cnstr_set_scalar(x_58, sizeof(void*)*1, x_56);
x_59 = x_58;
return x_59;
}
}
else
{
uint32 x_60; obj* x_61; 
x_60 = 34;
x_61 = l_lean_parser_monad__parsec_ch___at_lean_parser_string__lit_view_value___spec__2(x_60, x_2);
if (lean::obj_tag(x_61) == 0)
{
obj* x_62; obj* x_64; obj* x_66; obj* x_67; obj* x_68; obj* x_69; 
x_62 = lean::cnstr_get(x_61, 1);
x_64 = lean::cnstr_get(x_61, 2);
if (lean::is_exclusive(x_61)) {
 lean::cnstr_release(x_61, 0);
 x_66 = x_61;
} else {
 lean::inc(x_62);
 lean::inc(x_64);
 lean::dec(x_61);
 x_66 = lean::box(0);
}
x_67 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_66)) {
 x_68 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_68 = x_66;
}
lean::cnstr_set(x_68, 0, x_1);
lean::cnstr_set(x_68, 1, x_62);
lean::cnstr_set(x_68, 2, x_67);
x_69 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_64, x_68);
return x_69;
}
else
{
obj* x_71; uint8 x_73; obj* x_74; obj* x_75; obj* x_76; 
lean::dec(x_1);
x_71 = lean::cnstr_get(x_61, 0);
x_73 = lean::cnstr_get_scalar<uint8>(x_61, sizeof(void*)*1);
if (lean::is_exclusive(x_61)) {
 x_74 = x_61;
} else {
 lean::inc(x_71);
 lean::dec(x_61);
 x_74 = lean::box(0);
}
if (lean::is_scalar(x_74)) {
 x_75 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_75 = x_74;
}
lean::cnstr_set(x_75, 0, x_71);
lean::cnstr_set_scalar(x_75, sizeof(void*)*1, x_73);
x_76 = x_75;
return x_76;
}
}
}
}
obj* l_lean_parser_parse__string__literal___at_lean_parser_string__lit_view_value___spec__1(obj* x_0) {
_start:
{
uint32 x_1; obj* x_2; 
x_1 = 34;
x_2 = l_lean_parser_monad__parsec_ch___at_lean_parser_string__lit_view_value___spec__2(x_1, x_0);
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; obj* x_5; obj* x_8; obj* x_9; obj* x_10; obj* x_12; obj* x_13; obj* x_14; 
x_3 = lean::cnstr_get(x_2, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_2, 2);
lean::inc(x_5);
lean::dec(x_2);
x_8 = lean::string_iterator_remaining(x_3);
x_9 = l_string_join___closed__1;
x_10 = l_lean_parser_parse__string__literal__aux___main___at_lean_parser_string__lit_view_value___spec__4(x_8, x_9, x_3);
lean::dec(x_8);
x_12 = l_lean_parser_finish__comment__block___closed__2;
x_13 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_12, x_10);
x_14 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_5, x_13);
return x_14;
}
else
{
obj* x_15; uint8 x_17; obj* x_18; obj* x_19; obj* x_20; 
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
return x_20;
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
obj* x_1; 
x_1 = lean::box(0);
return x_1;
}
else
{
obj* x_2; obj* x_4; obj* x_5; obj* x_8; obj* x_9; obj* x_10; 
x_2 = lean::cnstr_get(x_0, 0);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 x_4 = x_0;
} else {
 lean::inc(x_2);
 lean::dec(x_0);
 x_4 = lean::box(0);
}
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
lean::dec(x_2);
x_8 = l_lean_parser_string__lit_view_value___closed__1;
x_9 = l_string_join___closed__1;
x_10 = l_lean_parser_parsec__t_run___at_lean_parser_parsec_parse___spec__1___rarg(x_8, x_5, x_9);
if (lean::obj_tag(x_10) == 0)
{
obj* x_13; 
lean::dec(x_10);
lean::dec(x_4);
x_13 = lean::box(0);
return x_13;
}
else
{
obj* x_14; obj* x_17; 
x_14 = lean::cnstr_get(x_10, 0);
lean::inc(x_14);
lean::dec(x_10);
if (lean::is_scalar(x_4)) {
 x_17 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_17 = x_4;
}
lean::cnstr_set(x_17, 0, x_14);
return x_17;
}
}
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_string__lit_view_value___spec__3___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_lean_parser_monad__parsec_error___at_lean_parser_string__lit_view_value___spec__3___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_2);
lean::dec(x_4);
return x_5;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_string__lit_view_value___spec__3___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_monad__parsec_error___at_lean_parser_string__lit_view_value___spec__3(x_0);
lean::dec(x_0);
return x_1;
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
obj* l_lean_parser_monad__parsec_unexpected__at___at_lean_parser_string__lit_view_value___spec__7___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_parser_monad__parsec_unexpected__at___at_lean_parser_string__lit_view_value___spec__7___rarg(x_0, x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_lean_parser_monad__parsec_unexpected__at___at_lean_parser_string__lit_view_value___spec__7___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_monad__parsec_unexpected__at___at_lean_parser_string__lit_view_value___spec__7(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_parser_parse__string__literal__aux___main___at_lean_parser_string__lit_view_value___spec__4___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_parser_parse__string__literal__aux___main___at_lean_parser_string__lit_view_value___spec__4(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_lean_parser_ident_parser___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_6; obj* x_7; 
lean::inc(x_2);
lean::inc(x_1);
x_6 = l_lean_parser_token(x_1, x_2, x_3);
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
if (lean::obj_tag(x_7) == 0)
{
obj* x_9; obj* x_11; obj* x_12; obj* x_14; obj* x_16; obj* x_18; obj* x_19; 
x_9 = lean::cnstr_get(x_6, 1);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 lean::cnstr_set(x_6, 1, lean::box(0));
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
 lean::cnstr_set(x_7, 0, lean::box(0));
 lean::cnstr_set(x_7, 1, lean::box(0));
 lean::cnstr_set(x_7, 2, lean::box(0));
 x_18 = x_7;
} else {
 lean::inc(x_12);
 lean::inc(x_14);
 lean::inc(x_16);
 lean::dec(x_7);
 x_18 = lean::box(0);
}
switch (lean::obj_tag(x_12)) {
case 1:
{
obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
lean::dec(x_1);
lean::dec(x_2);
x_23 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_18)) {
 x_24 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_24 = x_18;
}
lean::cnstr_set(x_24, 0, x_12);
lean::cnstr_set(x_24, 1, x_14);
lean::cnstr_set(x_24, 2, x_23);
x_25 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_24);
x_26 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_23, x_25);
x_27 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_26, x_0);
x_28 = l_lean_parser_parsec__t_try__mk__res___rarg(x_27);
if (lean::is_scalar(x_11)) {
 x_29 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_29 = x_11;
}
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_9);
return x_29;
}
case 3:
{
obj* x_32; 
lean::dec(x_11);
lean::dec(x_18);
x_32 = lean::box(0);
x_19 = x_32;
goto lbl_20;
}
default:
{
obj* x_36; 
lean::dec(x_11);
lean::dec(x_12);
lean::dec(x_18);
x_36 = lean::box(0);
x_19 = x_36;
goto lbl_20;
}
}
lbl_20:
{
obj* x_38; obj* x_39; obj* x_40; obj* x_42; obj* x_46; obj* x_48; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; 
lean::dec(x_19);
x_38 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_38, 0, x_2);
x_39 = lean::box(0);
x_40 = l_string_join___closed__1;
lean::inc(x_0);
x_42 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_40, x_0, x_38, x_39, x_1, x_14, x_9);
lean::dec(x_14);
lean::dec(x_1);
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
x_51 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_46);
x_52 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_53 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_52, x_51);
x_54 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_53, x_0);
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
obj* x_59; obj* x_61; obj* x_62; uint8 x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; 
lean::dec(x_1);
lean::dec(x_2);
x_59 = lean::cnstr_get(x_6, 1);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 x_61 = x_6;
} else {
 lean::inc(x_59);
 lean::dec(x_6);
 x_61 = lean::box(0);
}
x_62 = lean::cnstr_get(x_7, 0);
x_64 = lean::cnstr_get_scalar<uint8>(x_7, sizeof(void*)*1);
if (lean::is_exclusive(x_7)) {
 x_65 = x_7;
} else {
 lean::inc(x_62);
 lean::dec(x_7);
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
x_70 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_69, x_0);
x_71 = l_lean_parser_parsec__t_try__mk__res___rarg(x_70);
if (lean::is_scalar(x_61)) {
 x_72 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_72 = x_61;
}
lean::cnstr_set(x_72, 0, x_71);
lean::cnstr_set(x_72, 1, x_59);
return x_72;
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
obj* x_1; obj* x_2; 
x_1 = l_lean_parser_ident_parser___rarg___closed__1;
x_2 = lean::apply_2(x_0, lean::box(0), x_1);
return x_2;
}
}
obj* l_lean_parser_ident_parser(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_ident_parser___rarg), 1, 0);
return x_1;
}
}
obj* l_lean_parser_ident_parser___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_ident_parser(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_parser_ident_parser_tokens(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::box(0);
return x_2;
}
}
obj* l_lean_parser_ident_parser_tokens___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_parser_ident_parser_tokens(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_0 = lean::box(0);
x_1 = lean::mk_string("NOT_AN_IDENT");
lean::inc(x_1);
x_3 = l_lean_parser_substring_of__string(x_1);
x_4 = lean::box(0);
x_5 = lean_name_mk_string(x_4, x_1);
x_6 = lean::box(0);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_0);
lean::cnstr_set(x_7, 1, x_3);
lean::cnstr_set(x_7, 2, x_5);
lean::cnstr_set(x_7, 3, x_6);
lean::cnstr_set(x_7, 4, x_6);
return x_7;
}
}
obj* _init_l_lean_parser_ident_parser_view___rarg___lambda__1___closed__2() {
_start:
{
obj* x_0; 
x_0 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1;
return x_0;
}
}
obj* l_lean_parser_ident_parser_view___rarg___lambda__1(obj* x_0) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 1:
{
obj* x_1; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
return x_1;
}
default:
{
obj* x_3; 
x_3 = l_lean_parser_ident_parser_view___rarg___lambda__1___closed__2;
return x_3;
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
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_ident_parser_view___rarg___lambda__1___boxed), 1, 0);
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
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_lean_parser_ident_parser_view___rarg___closed__1;
x_2 = l_lean_parser_ident_parser_view___rarg___closed__2;
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* l_lean_parser_ident_parser_view(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_ident_parser_view___rarg___boxed), 1, 0);
return x_1;
}
}
obj* l_lean_parser_ident_parser_view___rarg___lambda__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_ident_parser_view___rarg___lambda__1(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_parser_ident_parser_view___rarg___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_ident_parser_view___rarg(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_parser_ident_parser_view___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_ident_parser_view(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_lean_parser_raw__ident_parser___rarg___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_token_4__ident_x_27), 3, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_with__trailing___at_lean_parser_token___spec__3___boxed), 4, 0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_bind___at_lean_parser_with__trailing___spec__2___rarg), 5, 2);
lean::closure_set(x_2, 0, x_0);
lean::closure_set(x_2, 1, x_1);
return x_2;
}
}
obj* l_lean_parser_raw__ident_parser___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_lean_parser_raw__ident_parser___rarg___closed__1;
x_2 = lean::apply_2(x_0, lean::box(0), x_1);
return x_2;
}
}
obj* l_lean_parser_raw__ident_parser(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_raw__ident_parser___rarg), 1, 0);
return x_1;
}
}
obj* l_lean_parser_raw__ident_parser___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_raw__ident_parser(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_parser_raw__ident_parser_tokens(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::box(0);
return x_2;
}
}
obj* l_lean_parser_raw__ident_parser_tokens___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_parser_raw__ident_parser_tokens(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_lean_parser_raw__ident_parser_view___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_lean_parser_ident_parser_view___rarg___closed__1;
x_2 = l_lean_parser_ident_parser_view___rarg___closed__2;
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* l_lean_parser_raw__ident_parser_view(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_raw__ident_parser_view___rarg___boxed), 1, 0);
return x_1;
}
}
obj* l_lean_parser_raw__ident_parser_view___rarg___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_raw__ident_parser_view___rarg(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_parser_raw__ident_parser_view___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_raw__ident_parser_view(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_parser_symbol__or__ident___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_6; obj* x_7; 
lean::inc(x_2);
lean::inc(x_1);
x_6 = l_lean_parser_token(x_1, x_2, x_3);
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
if (lean::obj_tag(x_7) == 0)
{
obj* x_9; obj* x_11; obj* x_12; obj* x_14; obj* x_16; obj* x_18; obj* x_19; 
x_9 = lean::cnstr_get(x_6, 1);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 lean::cnstr_set(x_6, 1, lean::box(0));
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
 lean::cnstr_set(x_7, 0, lean::box(0));
 lean::cnstr_set(x_7, 1, lean::box(0));
 lean::cnstr_set(x_7, 2, lean::box(0));
 x_18 = x_7;
} else {
 lean::inc(x_12);
 lean::inc(x_14);
 lean::inc(x_16);
 lean::dec(x_7);
 x_18 = lean::box(0);
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
obj* x_27; obj* x_29; obj* x_32; obj* x_34; 
x_27 = lean::cnstr_get(x_12, 0);
lean::inc(x_27);
x_29 = lean::cnstr_get(x_27, 1);
lean::inc(x_29);
lean::dec(x_27);
x_32 = l_lean_parser_substring_to__string(x_29);
lean::dec(x_29);
x_34 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_34, 0, x_32);
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
uint8 x_38; 
x_38 = 1;
x_36 = x_38;
goto lbl_37;
}
else
{
obj* x_39; uint8 x_42; 
x_39 = lean::cnstr_get(x_19, 0);
lean::inc(x_39);
lean::dec(x_19);
x_42 = lean::string_dec_eq(x_39, x_0);
lean::dec(x_39);
if (x_42 == 0)
{
uint8 x_44; 
x_44 = 1;
x_36 = x_44;
goto lbl_37;
}
else
{
uint8 x_45; 
x_45 = 0;
x_36 = x_45;
goto lbl_37;
}
}
lbl_37:
{
if (x_36 == 0)
{
obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_49 = l_lean_parser_finish__comment__block___closed__2;
if (lean::is_scalar(x_18)) {
 x_50 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_50 = x_18;
}
lean::cnstr_set(x_50, 0, x_12);
lean::cnstr_set(x_50, 1, x_14);
lean::cnstr_set(x_50, 2, x_49);
x_51 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_50);
x_52 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_53 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_52, x_51);
x_54 = l_lean_parser_parsec__t_try__mk__res___rarg(x_53);
if (lean::is_scalar(x_11)) {
 x_55 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_55 = x_11;
}
lean::cnstr_set(x_55, 0, x_54);
lean::cnstr_set(x_55, 1, x_9);
return x_55;
}
else
{
obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_67; 
lean::dec(x_11);
lean::dec(x_18);
x_58 = l_string_quote(x_0);
x_59 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_59, 0, x_58);
x_60 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_60, 0, x_2);
x_61 = lean::box(0);
x_62 = l_string_join___closed__1;
x_63 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_62, x_59, x_60, x_61, x_1, x_14, x_9);
lean::dec(x_14);
lean::dec(x_1);
lean::dec(x_60);
x_67 = lean::cnstr_get(x_63, 0);
lean::inc(x_67);
if (lean::obj_tag(x_67) == 0)
{
obj* x_69; obj* x_71; obj* x_72; obj* x_74; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; 
x_69 = lean::cnstr_get(x_63, 1);
if (lean::is_exclusive(x_63)) {
 lean::cnstr_release(x_63, 0);
 x_71 = x_63;
} else {
 lean::inc(x_69);
 lean::dec(x_63);
 x_71 = lean::box(0);
}
x_72 = lean::cnstr_get(x_67, 1);
x_74 = lean::cnstr_get(x_67, 2);
if (lean::is_exclusive(x_67)) {
 lean::cnstr_release(x_67, 0);
 x_76 = x_67;
} else {
 lean::inc(x_72);
 lean::inc(x_74);
 lean::dec(x_67);
 x_76 = lean::box(0);
}
x_77 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_76)) {
 x_78 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_78 = x_76;
}
lean::cnstr_set(x_78, 0, x_12);
lean::cnstr_set(x_78, 1, x_72);
lean::cnstr_set(x_78, 2, x_77);
x_79 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_74, x_78);
x_80 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_79);
x_81 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_77, x_80);
x_82 = l_lean_parser_parsec__t_try__mk__res___rarg(x_81);
if (lean::is_scalar(x_71)) {
 x_83 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_83 = x_71;
}
lean::cnstr_set(x_83, 0, x_82);
lean::cnstr_set(x_83, 1, x_69);
return x_83;
}
else
{
obj* x_85; obj* x_87; obj* x_88; uint8 x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_95; obj* x_96; obj* x_97; obj* x_98; 
lean::dec(x_12);
x_85 = lean::cnstr_get(x_63, 1);
if (lean::is_exclusive(x_63)) {
 lean::cnstr_release(x_63, 0);
 x_87 = x_63;
} else {
 lean::inc(x_85);
 lean::dec(x_63);
 x_87 = lean::box(0);
}
x_88 = lean::cnstr_get(x_67, 0);
x_90 = lean::cnstr_get_scalar<uint8>(x_67, sizeof(void*)*1);
if (lean::is_exclusive(x_67)) {
 x_91 = x_67;
} else {
 lean::inc(x_88);
 lean::dec(x_67);
 x_91 = lean::box(0);
}
if (lean::is_scalar(x_91)) {
 x_92 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_92 = x_91;
}
lean::cnstr_set(x_92, 0, x_88);
lean::cnstr_set_scalar(x_92, sizeof(void*)*1, x_90);
x_93 = x_92;
x_94 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_93);
x_95 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_96 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_95, x_94);
x_97 = l_lean_parser_parsec__t_try__mk__res___rarg(x_96);
if (lean::is_scalar(x_87)) {
 x_98 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_98 = x_87;
}
lean::cnstr_set(x_98, 0, x_97);
lean::cnstr_set(x_98, 1, x_85);
return x_98;
}
}
}
}
}
else
{
obj* x_102; obj* x_104; obj* x_105; uint8 x_107; obj* x_108; obj* x_109; obj* x_110; obj* x_111; obj* x_112; obj* x_113; obj* x_114; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_102 = lean::cnstr_get(x_6, 1);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 x_104 = x_6;
} else {
 lean::inc(x_102);
 lean::dec(x_6);
 x_104 = lean::box(0);
}
x_105 = lean::cnstr_get(x_7, 0);
x_107 = lean::cnstr_get_scalar<uint8>(x_7, sizeof(void*)*1);
if (lean::is_exclusive(x_7)) {
 x_108 = x_7;
} else {
 lean::inc(x_105);
 lean::dec(x_7);
 x_108 = lean::box(0);
}
if (lean::is_scalar(x_108)) {
 x_109 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_109 = x_108;
}
lean::cnstr_set(x_109, 0, x_105);
lean::cnstr_set_scalar(x_109, sizeof(void*)*1, x_107);
x_110 = x_109;
x_111 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_112 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_111, x_110);
x_113 = l_lean_parser_parsec__t_try__mk__res___rarg(x_112);
if (lean::is_scalar(x_104)) {
 x_114 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_114 = x_104;
}
lean::cnstr_set(x_114, 0, x_113);
lean::cnstr_set(x_114, 1, x_102);
return x_114;
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
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__or__ident___rarg), 2, 0);
return x_1;
}
}
obj* l_lean_parser_symbol__or__ident___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_symbol__or__ident(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_parser_symbol__or__ident_tokens(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::box(0);
return x_3;
}
}
obj* l_lean_parser_symbol__or__ident_tokens___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_parser_symbol__or__ident_tokens(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_lean_parser_symbol__or__ident_view___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_mjoin___rarg___closed__1;
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_2);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* l_lean_parser_symbol__or__ident_view(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__or__ident_view___rarg___boxed), 2, 0);
return x_1;
}
}
obj* l_lean_parser_symbol__or__ident_view___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_parser_symbol__or__ident_view___rarg(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_lean_parser_symbol__or__ident_view___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_symbol__or__ident_view(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_parser_symbol__core___at_lean_parser_unicode__symbol_lean_parser_has__tokens___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_8; obj* x_9; obj* x_11; obj* x_13; obj* x_15; 
lean::inc(x_4);
lean::inc(x_3);
x_8 = l_lean_parser_token(x_3, x_4, x_5);
x_9 = lean::cnstr_get(x_8, 0);
x_11 = lean::cnstr_get(x_8, 1);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_set(x_8, 0, lean::box(0));
 lean::cnstr_set(x_8, 1, lean::box(0));
 x_13 = x_8;
} else {
 lean::inc(x_9);
 lean::inc(x_11);
 lean::dec(x_8);
 x_13 = lean::box(0);
}
lean::inc(x_0);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_15, 0, x_0);
if (lean::obj_tag(x_9) == 0)
{
obj* x_16; obj* x_18; obj* x_20; obj* x_22; obj* x_23; 
x_16 = lean::cnstr_get(x_9, 0);
x_18 = lean::cnstr_get(x_9, 1);
x_20 = lean::cnstr_get(x_9, 2);
if (lean::is_exclusive(x_9)) {
 lean::cnstr_set(x_9, 0, lean::box(0));
 lean::cnstr_set(x_9, 1, lean::box(0));
 lean::cnstr_set(x_9, 2, lean::box(0));
 x_22 = x_9;
} else {
 lean::inc(x_16);
 lean::inc(x_18);
 lean::inc(x_20);
 lean::dec(x_9);
 x_22 = lean::box(0);
}
switch (lean::obj_tag(x_16)) {
case 0:
{
obj* x_25; obj* x_27; uint8 x_30; 
x_25 = lean::cnstr_get(x_16, 0);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_25, 1);
lean::inc(x_27);
lean::dec(x_25);
x_30 = lean::string_dec_eq(x_0, x_27);
lean::dec(x_0);
if (x_30 == 0)
{
obj* x_34; obj* x_35; obj* x_36; obj* x_40; 
lean::dec(x_13);
lean::dec(x_22);
x_34 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_34, 0, x_4);
x_35 = lean::box(0);
x_36 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_27, x_2, x_34, x_35, x_3, x_18, x_11);
lean::dec(x_18);
lean::dec(x_3);
lean::dec(x_34);
x_40 = lean::cnstr_get(x_36, 0);
lean::inc(x_40);
if (lean::obj_tag(x_40) == 0)
{
obj* x_42; obj* x_44; obj* x_45; obj* x_47; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; 
x_42 = lean::cnstr_get(x_36, 1);
if (lean::is_exclusive(x_36)) {
 lean::cnstr_release(x_36, 0);
 x_44 = x_36;
} else {
 lean::inc(x_42);
 lean::dec(x_36);
 x_44 = lean::box(0);
}
x_45 = lean::cnstr_get(x_40, 1);
x_47 = lean::cnstr_get(x_40, 2);
if (lean::is_exclusive(x_40)) {
 lean::cnstr_release(x_40, 0);
 x_49 = x_40;
} else {
 lean::inc(x_45);
 lean::inc(x_47);
 lean::dec(x_40);
 x_49 = lean::box(0);
}
x_50 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_49)) {
 x_51 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_51 = x_49;
}
lean::cnstr_set(x_51, 0, x_16);
lean::cnstr_set(x_51, 1, x_45);
lean::cnstr_set(x_51, 2, x_50);
x_52 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_47, x_51);
x_53 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_20, x_52);
x_54 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_50, x_53);
x_55 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_54, x_15);
x_56 = l_lean_parser_parsec__t_try__mk__res___rarg(x_55);
if (lean::is_scalar(x_44)) {
 x_57 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_57 = x_44;
}
lean::cnstr_set(x_57, 0, x_56);
lean::cnstr_set(x_57, 1, x_42);
return x_57;
}
else
{
obj* x_59; obj* x_61; obj* x_62; uint8 x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; 
lean::dec(x_16);
x_59 = lean::cnstr_get(x_36, 1);
if (lean::is_exclusive(x_36)) {
 lean::cnstr_release(x_36, 0);
 x_61 = x_36;
} else {
 lean::inc(x_59);
 lean::dec(x_36);
 x_61 = lean::box(0);
}
x_62 = lean::cnstr_get(x_40, 0);
x_64 = lean::cnstr_get_scalar<uint8>(x_40, sizeof(void*)*1);
if (lean::is_exclusive(x_40)) {
 x_65 = x_40;
} else {
 lean::inc(x_62);
 lean::dec(x_40);
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
x_68 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_20, x_67);
x_69 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_70 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_69, x_68);
x_71 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_70, x_15);
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
else
{
obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_27);
x_78 = l_lean_parser_finish__comment__block___closed__2;
if (lean::is_scalar(x_22)) {
 x_79 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_79 = x_22;
}
lean::cnstr_set(x_79, 0, x_16);
lean::cnstr_set(x_79, 1, x_18);
lean::cnstr_set(x_79, 2, x_78);
x_80 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_20, x_79);
x_81 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_82 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_81, x_80);
x_83 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_82, x_15);
x_84 = l_lean_parser_parsec__t_try__mk__res___rarg(x_83);
if (lean::is_scalar(x_13)) {
 x_85 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_85 = x_13;
}
lean::cnstr_set(x_85, 0, x_84);
lean::cnstr_set(x_85, 1, x_11);
return x_85;
}
}
case 3:
{
obj* x_89; 
lean::dec(x_13);
lean::dec(x_0);
lean::dec(x_22);
x_89 = lean::box(0);
x_23 = x_89;
goto lbl_24;
}
default:
{
obj* x_94; 
lean::dec(x_13);
lean::dec(x_0);
lean::dec(x_16);
lean::dec(x_22);
x_94 = lean::box(0);
x_23 = x_94;
goto lbl_24;
}
}
lbl_24:
{
obj* x_96; obj* x_97; obj* x_98; obj* x_99; obj* x_103; obj* x_105; obj* x_107; obj* x_108; obj* x_109; obj* x_110; obj* x_111; obj* x_112; obj* x_113; 
lean::dec(x_23);
x_96 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_96, 0, x_4);
x_97 = lean::box(0);
x_98 = l_string_join___closed__1;
x_99 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_98, x_2, x_96, x_97, x_3, x_18, x_11);
lean::dec(x_18);
lean::dec(x_3);
lean::dec(x_96);
x_103 = lean::cnstr_get(x_99, 0);
x_105 = lean::cnstr_get(x_99, 1);
if (lean::is_exclusive(x_99)) {
 x_107 = x_99;
} else {
 lean::inc(x_103);
 lean::inc(x_105);
 lean::dec(x_99);
 x_107 = lean::box(0);
}
x_108 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_20, x_103);
x_109 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_110 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_109, x_108);
x_111 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_110, x_15);
x_112 = l_lean_parser_parsec__t_try__mk__res___rarg(x_111);
if (lean::is_scalar(x_107)) {
 x_113 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_113 = x_107;
}
lean::cnstr_set(x_113, 0, x_112);
lean::cnstr_set(x_113, 1, x_105);
return x_113;
}
}
else
{
obj* x_118; uint8 x_120; obj* x_121; obj* x_122; obj* x_123; obj* x_124; obj* x_125; obj* x_126; obj* x_127; obj* x_128; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
x_118 = lean::cnstr_get(x_9, 0);
x_120 = lean::cnstr_get_scalar<uint8>(x_9, sizeof(void*)*1);
if (lean::is_exclusive(x_9)) {
 x_121 = x_9;
} else {
 lean::inc(x_118);
 lean::dec(x_9);
 x_121 = lean::box(0);
}
if (lean::is_scalar(x_121)) {
 x_122 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_122 = x_121;
}
lean::cnstr_set(x_122, 0, x_118);
lean::cnstr_set_scalar(x_122, sizeof(void*)*1, x_120);
x_123 = x_122;
x_124 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_125 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_124, x_123);
x_126 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_125, x_15);
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
obj* l_list_foldl___main___at_lean_parser_unicode__symbol_lean_parser_has__tokens___spec__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_5; 
x_5 = lean::apply_3(x_0, x_2, x_3, x_4);
return x_5;
}
else
{
obj* x_6; obj* x_8; obj* x_11; 
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 1);
lean::inc(x_8);
lean::dec(x_1);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_orelse___at_lean_parser_parse__bin__lit___spec__1___rarg), 5, 2);
lean::closure_set(x_11, 0, x_0);
lean::closure_set(x_11, 1, x_6);
x_0 = x_11;
x_1 = x_8;
goto _start;
}
}
}
obj* l_lean_parser_combinators_any__of___at_lean_parser_unicode__symbol_lean_parser_has__tokens___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_4 = lean::box(0);
x_5 = l_lean_parser_combinators_any__of___rarg___closed__1;
x_6 = l_mjoin___rarg___closed__1;
x_7 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_5, x_6, x_4, x_4, x_1, x_2, x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_7;
}
else
{
obj* x_10; obj* x_12; obj* x_15; 
x_10 = lean::cnstr_get(x_0, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_0, 1);
lean::inc(x_12);
lean::dec(x_0);
x_15 = l_list_foldl___main___at_lean_parser_unicode__symbol_lean_parser_has__tokens___spec__3(x_10, x_12, x_1, x_2, x_3);
return x_15;
}
}
}
obj* l_lean_parser_unicode__symbol_lean_parser_has__tokens___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_9; obj* x_12; obj* x_14; 
lean::inc(x_2);
x_4 = l_lean_parser_symbol_tokens___rarg(x_0, x_2);
x_5 = l_lean_parser_symbol_tokens___rarg(x_1, x_2);
x_6 = lean::box(0);
x_7 = l_lean_parser_list_cons_tokens___rarg(x_5, x_6);
lean::dec(x_5);
x_9 = l_lean_parser_list_cons_tokens___rarg(x_4, x_7);
lean::dec(x_7);
lean::dec(x_4);
x_12 = l_lean_parser_tokens___rarg(x_9);
lean::dec(x_9);
x_14 = l_lean_parser_tokens___rarg(x_12);
lean::dec(x_12);
return x_14;
}
}
obj* l_lean_parser_unicode__symbol_lean_parser_has__tokens(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_unicode__symbol_lean_parser_has__tokens___rarg), 3, 0);
return x_2;
}
}
obj* l_lean_parser_symbol__core___at_lean_parser_unicode__symbol_lean_parser_has__tokens___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_lean_parser_symbol__core___at_lean_parser_unicode__symbol_lean_parser_has__tokens___spec__1(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_1);
return x_6;
}
}
obj* l_lean_parser_unicode__symbol_lean_parser_has__tokens___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_parser_unicode__symbol_lean_parser_has__tokens(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_lean_parser_unicode__symbol_lean_parser_has__view___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_24; 
x_4 = l_string_trim(x_1);
lean::inc(x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_6, 0, x_4);
lean::inc(x_3);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_unicode__symbol_lean_parser_has__tokens___spec__1___boxed), 6, 3);
lean::closure_set(x_8, 0, x_4);
lean::closure_set(x_8, 1, x_3);
lean::closure_set(x_8, 2, x_6);
x_9 = l_string_trim(x_2);
lean::inc(x_9);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_11, 0, x_9);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_unicode__symbol_lean_parser_has__tokens___spec__1___boxed), 6, 3);
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
x_22 = l_lean_parser_combinators_any__of_view___rarg(x_18, x_19, x_20, x_21, x_15);
lean::dec(x_15);
x_24 = l_lean_parser_combinators_monad__lift_view___rarg(x_0, x_17, x_22);
lean::dec(x_17);
return x_24;
}
}
obj* l_lean_parser_unicode__symbol_lean_parser_has__view(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_unicode__symbol_lean_parser_has__view___rarg___boxed), 4, 0);
return x_1;
}
}
obj* l_lean_parser_unicode__symbol_lean_parser_has__view___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_parser_unicode__symbol_lean_parser_has__view___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_lean_parser_unicode__symbol_lean_parser_has__view___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_unicode__symbol_lean_parser_has__view(x_0);
lean::dec(x_0);
return x_1;
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
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_unicode__symbol_lean_parser_has__tokens___spec__1___boxed), 6, 3);
lean::closure_set(x_8, 0, x_4);
lean::closure_set(x_8, 1, x_3);
lean::closure_set(x_8, 2, x_6);
x_9 = l_string_trim(x_2);
lean::inc(x_9);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_11, 0, x_9);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_unicode__symbol_lean_parser_has__tokens___spec__1___boxed), 6, 3);
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
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_unicode__symbol___rarg), 4, 0);
return x_1;
}
}
obj* l_lean_parser_unicode__symbol___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_unicode__symbol(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_parser_unicode__symbol_view__default___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::box(0);
return x_4;
}
}
obj* l_lean_parser_unicode__symbol_view__default(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_unicode__symbol_view__default___rarg___boxed), 4, 0);
return x_1;
}
}
obj* l_lean_parser_unicode__symbol_view__default___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_parser_unicode__symbol_view__default___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_lean_parser_unicode__symbol_view__default___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_unicode__symbol_view__default(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_rbmap_find___main___at_lean_parser_indexed___spec__1___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_find___main___at_lean_name__map_contains___spec__2___rarg(x_0, x_1);
return x_2;
}
}
obj* l_rbmap_find___main___at_lean_parser_indexed___spec__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_find___main___at_lean_parser_indexed___spec__1___rarg___boxed), 2, 0);
return x_1;
}
}
obj* l_option_to__monad___main___at_lean_parser_indexed___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_4; 
x_4 = l_lean_parser_parsec__t_failure___at_lean_parser_token___spec__4___rarg(x_2, x_3);
return x_4;
}
else
{
obj* x_5; obj* x_8; obj* x_9; obj* x_10; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
lean::dec(x_0);
x_8 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_9 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_9, 0, x_5);
lean::cnstr_set(x_9, 1, x_2);
lean::cnstr_set(x_9, 2, x_8);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_3);
return x_10;
}
}
}
obj* l_option_to__monad___main___at_lean_parser_indexed___spec__2(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_option_to__monad___main___at_lean_parser_indexed___spec__2___rarg___boxed), 4, 0);
return x_1;
}
}
obj* l_rbmap_find___main___at_lean_parser_indexed___spec__3___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_find___main___at_lean_name__map_contains___spec__2___rarg(x_0, x_1);
return x_2;
}
}
obj* l_rbmap_find___main___at_lean_parser_indexed___spec__3(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_find___main___at_lean_parser_indexed___spec__3___rarg___boxed), 2, 0);
return x_1;
}
}
obj* l_rbmap_find___main___at_lean_parser_indexed___spec__4___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_find___main___at_lean_name__map_contains___spec__2___rarg(x_0, x_1);
return x_2;
}
}
obj* l_rbmap_find___main___at_lean_parser_indexed___spec__4(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_find___main___at_lean_parser_indexed___spec__4___rarg___boxed), 2, 0);
return x_1;
}
}
obj* l_rbmap_find___main___at_lean_parser_indexed___spec__5___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_find___main___at_lean_name__map_contains___spec__2___rarg(x_0, x_1);
return x_2;
}
}
obj* l_rbmap_find___main___at_lean_parser_indexed___spec__5(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_find___main___at_lean_parser_indexed___spec__5___rarg___boxed), 2, 0);
return x_1;
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
obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
lean::dec(x_1);
lean::dec(x_0);
x_7 = lean::box(0);
x_8 = l_string_join___closed__1;
x_9 = l_mjoin___rarg___closed__1;
x_10 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_8, x_9, x_7, x_7, x_2, x_3, x_4);
lean::dec(x_3);
return x_10;
}
else
{
obj* x_12; 
x_12 = lean::cnstr_get(x_1, 0);
lean::inc(x_12);
lean::dec(x_1);
switch (lean::obj_tag(x_12)) {
case 0:
{
obj* x_15; obj* x_18; obj* x_21; obj* x_22; obj* x_23; obj* x_25; obj* x_26; obj* x_28; obj* x_30; obj* x_31; obj* x_32; obj* x_33; 
x_15 = lean::cnstr_get(x_12, 0);
lean::inc(x_15);
lean::dec(x_12);
x_18 = lean::cnstr_get(x_15, 1);
lean::inc(x_18);
lean::dec(x_15);
x_21 = lean::box(0);
x_22 = lean_name_mk_string(x_21, x_18);
x_23 = l_rbnode_find___main___at_lean_name__map_contains___spec__2___rarg(x_0, x_22);
lean::dec(x_22);
x_25 = l_option_to__monad___main___at_lean_parser_indexed___spec__2___rarg(x_23, x_2, x_3, x_4);
x_26 = lean::cnstr_get(x_25, 0);
x_28 = lean::cnstr_get(x_25, 1);
if (lean::is_exclusive(x_25)) {
 x_30 = x_25;
} else {
 lean::inc(x_26);
 lean::inc(x_28);
 lean::dec(x_25);
 x_30 = lean::box(0);
}
x_31 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_32 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_31, x_26);
if (lean::is_scalar(x_30)) {
 x_33 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_33 = x_30;
}
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_28);
return x_33;
}
case 1:
{
obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_40; obj* x_42; obj* x_43; obj* x_44; obj* x_45; 
lean::dec(x_12);
x_35 = l_lean_parser_indexed___rarg___lambda__1___closed__1;
x_36 = l_rbnode_find___main___at_lean_name__map_contains___spec__2___rarg(x_0, x_35);
x_37 = l_option_to__monad___main___at_lean_parser_indexed___spec__2___rarg(x_36, x_2, x_3, x_4);
x_38 = lean::cnstr_get(x_37, 0);
x_40 = lean::cnstr_get(x_37, 1);
if (lean::is_exclusive(x_37)) {
 x_42 = x_37;
} else {
 lean::inc(x_38);
 lean::inc(x_40);
 lean::dec(x_37);
 x_42 = lean::box(0);
}
x_43 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_44 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_43, x_38);
if (lean::is_scalar(x_42)) {
 x_45 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_45 = x_42;
}
lean::cnstr_set(x_45, 0, x_44);
lean::cnstr_set(x_45, 1, x_40);
return x_45;
}
case 2:
{
obj* x_46; obj* x_49; obj* x_52; obj* x_54; obj* x_55; obj* x_57; obj* x_59; obj* x_60; obj* x_61; obj* x_62; 
x_46 = lean::cnstr_get(x_12, 0);
lean::inc(x_46);
lean::dec(x_12);
x_49 = lean::cnstr_get(x_46, 0);
lean::inc(x_49);
lean::dec(x_46);
x_52 = l_rbnode_find___main___at_lean_name__map_contains___spec__2___rarg(x_0, x_49);
lean::dec(x_49);
x_54 = l_option_to__monad___main___at_lean_parser_indexed___spec__2___rarg(x_52, x_2, x_3, x_4);
x_55 = lean::cnstr_get(x_54, 0);
x_57 = lean::cnstr_get(x_54, 1);
if (lean::is_exclusive(x_54)) {
 x_59 = x_54;
} else {
 lean::inc(x_55);
 lean::inc(x_57);
 lean::dec(x_54);
 x_59 = lean::box(0);
}
x_60 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_61 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_60, x_55);
if (lean::is_scalar(x_59)) {
 x_62 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_62 = x_59;
}
lean::cnstr_set(x_62, 0, x_61);
lean::cnstr_set(x_62, 1, x_57);
return x_62;
}
default:
{
obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_68; 
x_63 = lean::box(0);
x_64 = l_string_join___closed__1;
x_65 = l_mjoin___rarg___closed__1;
x_66 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_64, x_65, x_63, x_63, x_2, x_3, x_4);
lean::dec(x_3);
x_68 = lean::cnstr_get(x_66, 0);
lean::inc(x_68);
if (lean::obj_tag(x_68) == 0)
{
obj* x_70; obj* x_73; obj* x_75; obj* x_77; obj* x_80; obj* x_82; obj* x_83; obj* x_85; obj* x_87; obj* x_88; obj* x_89; 
x_70 = lean::cnstr_get(x_66, 1);
lean::inc(x_70);
lean::dec(x_66);
x_73 = lean::cnstr_get(x_68, 0);
lean::inc(x_73);
x_75 = lean::cnstr_get(x_68, 1);
lean::inc(x_75);
x_77 = lean::cnstr_get(x_68, 2);
lean::inc(x_77);
lean::dec(x_68);
x_80 = l_rbnode_find___main___at_lean_name__map_contains___spec__2___rarg(x_0, x_73);
lean::dec(x_73);
x_82 = l_option_to__monad___main___at_lean_parser_indexed___spec__2___rarg(x_80, x_2, x_75, x_70);
x_83 = lean::cnstr_get(x_82, 0);
x_85 = lean::cnstr_get(x_82, 1);
if (lean::is_exclusive(x_82)) {
 x_87 = x_82;
} else {
 lean::inc(x_83);
 lean::inc(x_85);
 lean::dec(x_82);
 x_87 = lean::box(0);
}
x_88 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_77, x_83);
if (lean::is_scalar(x_87)) {
 x_89 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_89 = x_87;
}
lean::cnstr_set(x_89, 0, x_88);
lean::cnstr_set(x_89, 1, x_85);
return x_89;
}
else
{
obj* x_91; obj* x_93; obj* x_94; uint8 x_96; obj* x_97; obj* x_98; obj* x_99; obj* x_100; 
lean::dec(x_0);
x_91 = lean::cnstr_get(x_66, 1);
if (lean::is_exclusive(x_66)) {
 lean::cnstr_release(x_66, 0);
 x_93 = x_66;
} else {
 lean::inc(x_91);
 lean::dec(x_66);
 x_93 = lean::box(0);
}
x_94 = lean::cnstr_get(x_68, 0);
x_96 = lean::cnstr_get_scalar<uint8>(x_68, sizeof(void*)*1);
if (lean::is_exclusive(x_68)) {
 x_97 = x_68;
} else {
 lean::inc(x_94);
 lean::dec(x_68);
 x_97 = lean::box(0);
}
if (lean::is_scalar(x_97)) {
 x_98 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_98 = x_97;
}
lean::cnstr_set(x_98, 0, x_94);
lean::cnstr_set_scalar(x_98, sizeof(void*)*1, x_96);
x_99 = x_98;
if (lean::is_scalar(x_93)) {
 x_100 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_100 = x_93;
}
lean::cnstr_set(x_100, 0, x_99);
lean::cnstr_set(x_100, 1, x_91);
return x_100;
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
obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_indexed___rarg___lambda__1___boxed), 5, 1);
lean::closure_set(x_3, 0, x_2);
x_4 = l_lean_parser_indexed___rarg___closed__1;
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_bind___at_lean_parser_with__trailing___spec__2___rarg), 5, 2);
lean::closure_set(x_5, 0, x_4);
lean::closure_set(x_5, 1, x_3);
x_6 = lean::apply_2(x_0, lean::box(0), x_5);
return x_6;
}
}
obj* l_lean_parser_indexed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_indexed___rarg___boxed), 3, 0);
return x_1;
}
}
obj* l_rbmap_find___main___at_lean_parser_indexed___spec__1___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbmap_find___main___at_lean_parser_indexed___spec__1___rarg(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_rbmap_find___main___at_lean_parser_indexed___spec__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_rbmap_find___main___at_lean_parser_indexed___spec__1(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_option_to__monad___main___at_lean_parser_indexed___spec__2___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_option_to__monad___main___at_lean_parser_indexed___spec__2___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_option_to__monad___main___at_lean_parser_indexed___spec__2___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_option_to__monad___main___at_lean_parser_indexed___spec__2(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_rbmap_find___main___at_lean_parser_indexed___spec__3___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbmap_find___main___at_lean_parser_indexed___spec__3___rarg(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_rbmap_find___main___at_lean_parser_indexed___spec__3___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_rbmap_find___main___at_lean_parser_indexed___spec__3(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_rbmap_find___main___at_lean_parser_indexed___spec__4___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbmap_find___main___at_lean_parser_indexed___spec__4___rarg(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_rbmap_find___main___at_lean_parser_indexed___spec__4___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_rbmap_find___main___at_lean_parser_indexed___spec__4(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_rbmap_find___main___at_lean_parser_indexed___spec__5___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbmap_find___main___at_lean_parser_indexed___spec__5___rarg(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_rbmap_find___main___at_lean_parser_indexed___spec__5___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_rbmap_find___main___at_lean_parser_indexed___spec__5(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_parser_indexed___rarg___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_lean_parser_indexed___rarg___lambda__1(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* l_lean_parser_indexed___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_parser_indexed___rarg(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_lean_parser_indexed___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_indexed(x_0);
lean::dec(x_0);
return x_1;
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
lean::mark_persistent(l_lean_parser_match__token___closed__1);
 l___private_init_lean_parser_token_1__finish__comment__block__aux___main___closed__1 = _init_l___private_init_lean_parser_token_1__finish__comment__block__aux___main___closed__1();
lean::mark_persistent(l___private_init_lean_parser_token_1__finish__comment__block__aux___main___closed__1);
 l___private_init_lean_parser_token_1__finish__comment__block__aux___main___closed__2 = _init_l___private_init_lean_parser_token_1__finish__comment__block__aux___main___closed__2();
lean::mark_persistent(l___private_init_lean_parser_token_1__finish__comment__block__aux___main___closed__2);
 l___private_init_lean_parser_token_1__finish__comment__block__aux___main___closed__3 = _init_l___private_init_lean_parser_token_1__finish__comment__block__aux___main___closed__3();
lean::mark_persistent(l___private_init_lean_parser_token_1__finish__comment__block__aux___main___closed__3);
 l___private_init_lean_parser_token_1__finish__comment__block__aux___main___closed__4 = _init_l___private_init_lean_parser_token_1__finish__comment__block__aux___main___closed__4();
lean::mark_persistent(l___private_init_lean_parser_token_1__finish__comment__block__aux___main___closed__4);
 l_lean_parser_finish__comment__block___closed__1 = _init_l_lean_parser_finish__comment__block___closed__1();
lean::mark_persistent(l_lean_parser_finish__comment__block___closed__1);
 l_lean_parser_finish__comment__block___closed__2 = _init_l_lean_parser_finish__comment__block___closed__2();
lean::mark_persistent(l_lean_parser_finish__comment__block___closed__2);
 l_lean_parser_parsec__t_lookahead___at___private_init_lean_parser_token_2__whitespace__aux___main___spec__4___closed__1 = _init_l_lean_parser_parsec__t_lookahead___at___private_init_lean_parser_token_2__whitespace__aux___main___spec__4___closed__1();
lean::mark_persistent(l_lean_parser_parsec__t_lookahead___at___private_init_lean_parser_token_2__whitespace__aux___main___spec__4___closed__1);
 l_lean_parser_parsec__t_lookahead___at___private_init_lean_parser_token_2__whitespace__aux___main___spec__4___closed__2 = _init_l_lean_parser_parsec__t_lookahead___at___private_init_lean_parser_token_2__whitespace__aux___main___spec__4___closed__2();
lean::mark_persistent(l_lean_parser_parsec__t_lookahead___at___private_init_lean_parser_token_2__whitespace__aux___main___spec__4___closed__2);
 l___private_init_lean_parser_token_2__whitespace__aux___main___closed__1 = _init_l___private_init_lean_parser_token_2__whitespace__aux___main___closed__1();
lean::mark_persistent(l___private_init_lean_parser_token_2__whitespace__aux___main___closed__1);
 l___private_init_lean_parser_token_2__whitespace__aux___main___closed__2 = _init_l___private_init_lean_parser_token_2__whitespace__aux___main___closed__2();
lean::mark_persistent(l___private_init_lean_parser_token_2__whitespace__aux___main___closed__2);
 l___private_init_lean_parser_token_2__whitespace__aux___main___closed__3 = _init_l___private_init_lean_parser_token_2__whitespace__aux___main___closed__3();
lean::mark_persistent(l___private_init_lean_parser_token_2__whitespace__aux___main___closed__3);
 l_lean_parser_with__trailing___rarg___closed__1 = _init_l_lean_parser_with__trailing___rarg___closed__1();
lean::mark_persistent(l_lean_parser_with__trailing___rarg___closed__1);
 l_lean_parser_raw_view___rarg___lambda__2___closed__1 = _init_l_lean_parser_raw_view___rarg___lambda__2___closed__1();
lean::mark_persistent(l_lean_parser_raw_view___rarg___lambda__2___closed__1);
 l_lean_parser_raw_view___rarg___closed__1 = _init_l_lean_parser_raw_view___rarg___closed__1();
lean::mark_persistent(l_lean_parser_raw_view___rarg___closed__1);
 l_lean_parser_raw_view___rarg___closed__2 = _init_l_lean_parser_raw_view___rarg___closed__2();
lean::mark_persistent(l_lean_parser_raw_view___rarg___closed__2);
 l_lean_parser_detail__ident__part__escaped = _init_l_lean_parser_detail__ident__part__escaped();
lean::mark_persistent(l_lean_parser_detail__ident__part__escaped);
 l_lean_parser_detail__ident__part__escaped_has__view_x_27___lambda__1___closed__1 = _init_l_lean_parser_detail__ident__part__escaped_has__view_x_27___lambda__1___closed__1();
lean::mark_persistent(l_lean_parser_detail__ident__part__escaped_has__view_x_27___lambda__1___closed__1);
 l_lean_parser_detail__ident__part__escaped_has__view_x_27___lambda__2___closed__1 = _init_l_lean_parser_detail__ident__part__escaped_has__view_x_27___lambda__2___closed__1();
lean::mark_persistent(l_lean_parser_detail__ident__part__escaped_has__view_x_27___lambda__2___closed__1);
 l_lean_parser_detail__ident__part__escaped_has__view_x_27___lambda__2___closed__2 = _init_l_lean_parser_detail__ident__part__escaped_has__view_x_27___lambda__2___closed__2();
lean::mark_persistent(l_lean_parser_detail__ident__part__escaped_has__view_x_27___lambda__2___closed__2);
 l_lean_parser_detail__ident__part__escaped_has__view_x_27___lambda__2___closed__3 = _init_l_lean_parser_detail__ident__part__escaped_has__view_x_27___lambda__2___closed__3();
lean::mark_persistent(l_lean_parser_detail__ident__part__escaped_has__view_x_27___lambda__2___closed__3);
 l_lean_parser_detail__ident__part__escaped_has__view_x_27 = _init_l_lean_parser_detail__ident__part__escaped_has__view_x_27();
lean::mark_persistent(l_lean_parser_detail__ident__part__escaped_has__view_x_27);
 l_lean_parser_detail__ident__part__escaped_has__view = _init_l_lean_parser_detail__ident__part__escaped_has__view();
lean::mark_persistent(l_lean_parser_detail__ident__part__escaped_has__view);
 l_lean_parser_detail__ident__part = _init_l_lean_parser_detail__ident__part();
lean::mark_persistent(l_lean_parser_detail__ident__part);
 l_lean_parser_detail__ident__part_has__view_x_27___lambda__1___closed__1 = _init_l_lean_parser_detail__ident__part_has__view_x_27___lambda__1___closed__1();
lean::mark_persistent(l_lean_parser_detail__ident__part_has__view_x_27___lambda__1___closed__1);
 l_lean_parser_detail__ident__part_has__view_x_27___lambda__1___closed__2 = _init_l_lean_parser_detail__ident__part_has__view_x_27___lambda__1___closed__2();
lean::mark_persistent(l_lean_parser_detail__ident__part_has__view_x_27___lambda__1___closed__2);
 l_lean_parser_detail__ident__part_has__view_x_27___lambda__1___closed__3 = _init_l_lean_parser_detail__ident__part_has__view_x_27___lambda__1___closed__3();
lean::mark_persistent(l_lean_parser_detail__ident__part_has__view_x_27___lambda__1___closed__3);
 l_lean_parser_detail__ident__part_has__view_x_27___lambda__2___closed__1 = _init_l_lean_parser_detail__ident__part_has__view_x_27___lambda__2___closed__1();
lean::mark_persistent(l_lean_parser_detail__ident__part_has__view_x_27___lambda__2___closed__1);
 l_lean_parser_detail__ident__part_has__view_x_27___lambda__2___closed__2 = _init_l_lean_parser_detail__ident__part_has__view_x_27___lambda__2___closed__2();
lean::mark_persistent(l_lean_parser_detail__ident__part_has__view_x_27___lambda__2___closed__2);
 l_lean_parser_detail__ident__part_has__view_x_27___lambda__2___closed__3 = _init_l_lean_parser_detail__ident__part_has__view_x_27___lambda__2___closed__3();
lean::mark_persistent(l_lean_parser_detail__ident__part_has__view_x_27___lambda__2___closed__3);
 l_lean_parser_detail__ident__part_has__view_x_27 = _init_l_lean_parser_detail__ident__part_has__view_x_27();
lean::mark_persistent(l_lean_parser_detail__ident__part_has__view_x_27);
 l_lean_parser_detail__ident__part_has__view = _init_l_lean_parser_detail__ident__part_has__view();
lean::mark_persistent(l_lean_parser_detail__ident__part_has__view);
 l_lean_parser_detail__ident__part_parser_lean_parser_has__tokens = _init_l_lean_parser_detail__ident__part_parser_lean_parser_has__tokens();
lean::mark_persistent(l_lean_parser_detail__ident__part_parser_lean_parser_has__tokens);
 l_lean_parser_detail__ident__part_parser_lean_parser_has__view = _init_l_lean_parser_detail__ident__part_parser_lean_parser_has__view();
lean::mark_persistent(l_lean_parser_detail__ident__part_parser_lean_parser_has__view);
 l_lean_parser_detail__ident__part_parser___closed__1 = _init_l_lean_parser_detail__ident__part_parser___closed__1();
lean::mark_persistent(l_lean_parser_detail__ident__part_parser___closed__1);
 l_lean_parser_detail__ident__suffix = _init_l_lean_parser_detail__ident__suffix();
lean::mark_persistent(l_lean_parser_detail__ident__suffix);
 l_lean_parser_detail__ident__suffix_has__view_x_27___lambda__1___closed__1 = _init_l_lean_parser_detail__ident__suffix_has__view_x_27___lambda__1___closed__1();
lean::mark_persistent(l_lean_parser_detail__ident__suffix_has__view_x_27___lambda__1___closed__1);
 l_lean_parser_detail__ident__suffix_has__view_x_27 = _init_l_lean_parser_detail__ident__suffix_has__view_x_27();
lean::mark_persistent(l_lean_parser_detail__ident__suffix_has__view_x_27);
 l_lean_parser_detail__ident__suffix_has__view = _init_l_lean_parser_detail__ident__suffix_has__view();
lean::mark_persistent(l_lean_parser_detail__ident__suffix_has__view);
 l_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens = _init_l_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens();
lean::mark_persistent(l_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens);
 l_lean_parser_detail__ident__suffix_parser_lean_parser_has__view = _init_l_lean_parser_detail__ident__suffix_parser_lean_parser_has__view();
lean::mark_persistent(l_lean_parser_detail__ident__suffix_parser_lean_parser_has__view);
 l_lean_parser_detail__ident__suffix_parser___closed__1 = _init_l_lean_parser_detail__ident__suffix_parser___closed__1();
lean::mark_persistent(l_lean_parser_detail__ident__suffix_parser___closed__1);
 l_lean_parser_detail__ident = _init_l_lean_parser_detail__ident();
lean::mark_persistent(l_lean_parser_detail__ident);
 l_lean_parser_detail__ident_has__view_x_27___lambda__1___closed__1 = _init_l_lean_parser_detail__ident_has__view_x_27___lambda__1___closed__1();
lean::mark_persistent(l_lean_parser_detail__ident_has__view_x_27___lambda__1___closed__1);
 l_lean_parser_detail__ident_has__view_x_27___lambda__1___closed__2 = _init_l_lean_parser_detail__ident_has__view_x_27___lambda__1___closed__2();
lean::mark_persistent(l_lean_parser_detail__ident_has__view_x_27___lambda__1___closed__2);
 l_lean_parser_detail__ident_has__view_x_27___lambda__2___closed__1 = _init_l_lean_parser_detail__ident_has__view_x_27___lambda__2___closed__1();
lean::mark_persistent(l_lean_parser_detail__ident_has__view_x_27___lambda__2___closed__1);
 l_lean_parser_detail__ident_has__view_x_27 = _init_l_lean_parser_detail__ident_has__view_x_27();
lean::mark_persistent(l_lean_parser_detail__ident_has__view_x_27);
 l_lean_parser_detail__ident_has__view = _init_l_lean_parser_detail__ident_has__view();
lean::mark_persistent(l_lean_parser_detail__ident_has__view);
 l_lean_parser_detail__ident_x_27___closed__1 = _init_l_lean_parser_detail__ident_x_27___closed__1();
lean::mark_persistent(l_lean_parser_detail__ident_x_27___closed__1);
 l_lean_parser_rec__t_run__parsec___at_lean_parser_detail__ident_parser___spec__1___closed__1 = _init_l_lean_parser_rec__t_run__parsec___at_lean_parser_detail__ident_parser___spec__1___closed__1();
lean::mark_persistent(l_lean_parser_rec__t_run__parsec___at_lean_parser_detail__ident_parser___spec__1___closed__1);
 l_lean_parser_detail__ident_parser___closed__1 = _init_l_lean_parser_detail__ident_parser___closed__1();
lean::mark_persistent(l_lean_parser_detail__ident_parser___closed__1);
 l_lean_parser_detail__ident_parser___closed__2 = _init_l_lean_parser_detail__ident_parser___closed__2();
lean::mark_persistent(l_lean_parser_detail__ident_parser___closed__2);
 l_lean_parser_monad__parsec_foldl__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__21___closed__1 = _init_l_lean_parser_monad__parsec_foldl__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__21___closed__1();
lean::mark_persistent(l_lean_parser_monad__parsec_foldl__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__21___closed__1);
 l_lean_parser_monad__parsec_foldl__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__21___closed__2 = _init_l_lean_parser_monad__parsec_foldl__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__21___closed__2();
lean::mark_persistent(l_lean_parser_monad__parsec_foldl__aux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__21___closed__2);
 l_lean_parser_monad__parsec_many1__aux_x_27___main___at_lean_parser_parse__bin__lit___spec__2___closed__1 = _init_l_lean_parser_monad__parsec_many1__aux_x_27___main___at_lean_parser_parse__bin__lit___spec__2___closed__1();
lean::mark_persistent(l_lean_parser_monad__parsec_many1__aux_x_27___main___at_lean_parser_parse__bin__lit___spec__2___closed__1);
 l_lean_parser_monad__parsec_many1__aux_x_27___main___at_lean_parser_parse__bin__lit___spec__2___closed__2 = _init_l_lean_parser_monad__parsec_many1__aux_x_27___main___at_lean_parser_parse__bin__lit___spec__2___closed__2();
lean::mark_persistent(l_lean_parser_monad__parsec_many1__aux_x_27___main___at_lean_parser_parse__bin__lit___spec__2___closed__2);
 l_lean_parser_number = _init_l_lean_parser_number();
lean::mark_persistent(l_lean_parser_number);
 l_lean_parser_number_has__view_x_27___lambda__1___closed__1 = _init_l_lean_parser_number_has__view_x_27___lambda__1___closed__1();
lean::mark_persistent(l_lean_parser_number_has__view_x_27___lambda__1___closed__1);
 l_lean_parser_number_has__view_x_27___lambda__1___closed__2 = _init_l_lean_parser_number_has__view_x_27___lambda__1___closed__2();
lean::mark_persistent(l_lean_parser_number_has__view_x_27___lambda__1___closed__2);
 l_lean_parser_number_has__view_x_27___lambda__1___closed__3 = _init_l_lean_parser_number_has__view_x_27___lambda__1___closed__3();
lean::mark_persistent(l_lean_parser_number_has__view_x_27___lambda__1___closed__3);
 l_lean_parser_number_has__view_x_27___lambda__1___closed__4 = _init_l_lean_parser_number_has__view_x_27___lambda__1___closed__4();
lean::mark_persistent(l_lean_parser_number_has__view_x_27___lambda__1___closed__4);
 l_lean_parser_number_has__view_x_27___lambda__1___closed__5 = _init_l_lean_parser_number_has__view_x_27___lambda__1___closed__5();
lean::mark_persistent(l_lean_parser_number_has__view_x_27___lambda__1___closed__5);
 l_lean_parser_number_has__view_x_27___lambda__1___closed__6 = _init_l_lean_parser_number_has__view_x_27___lambda__1___closed__6();
lean::mark_persistent(l_lean_parser_number_has__view_x_27___lambda__1___closed__6);
 l_lean_parser_number_has__view_x_27___lambda__2___closed__1 = _init_l_lean_parser_number_has__view_x_27___lambda__2___closed__1();
lean::mark_persistent(l_lean_parser_number_has__view_x_27___lambda__2___closed__1);
 l_lean_parser_number_has__view_x_27___lambda__2___closed__2 = _init_l_lean_parser_number_has__view_x_27___lambda__2___closed__2();
lean::mark_persistent(l_lean_parser_number_has__view_x_27___lambda__2___closed__2);
 l_lean_parser_number_has__view_x_27___lambda__2___closed__3 = _init_l_lean_parser_number_has__view_x_27___lambda__2___closed__3();
lean::mark_persistent(l_lean_parser_number_has__view_x_27___lambda__2___closed__3);
 l_lean_parser_number_has__view_x_27___lambda__2___closed__4 = _init_l_lean_parser_number_has__view_x_27___lambda__2___closed__4();
lean::mark_persistent(l_lean_parser_number_has__view_x_27___lambda__2___closed__4);
 l_lean_parser_number_has__view_x_27___lambda__2___closed__5 = _init_l_lean_parser_number_has__view_x_27___lambda__2___closed__5();
lean::mark_persistent(l_lean_parser_number_has__view_x_27___lambda__2___closed__5);
 l_lean_parser_number_has__view_x_27___lambda__2___closed__6 = _init_l_lean_parser_number_has__view_x_27___lambda__2___closed__6();
lean::mark_persistent(l_lean_parser_number_has__view_x_27___lambda__2___closed__6);
 l_lean_parser_number_has__view_x_27 = _init_l_lean_parser_number_has__view_x_27();
lean::mark_persistent(l_lean_parser_number_has__view_x_27);
 l_lean_parser_number_has__view = _init_l_lean_parser_number_has__view();
lean::mark_persistent(l_lean_parser_number_has__view);
 l_lean_parser_number_x_27___closed__1 = _init_l_lean_parser_number_x_27___closed__1();
lean::mark_persistent(l_lean_parser_number_x_27___closed__1);
 l_lean_parser_string__lit = _init_l_lean_parser_string__lit();
lean::mark_persistent(l_lean_parser_string__lit);
 l_lean_parser_string__lit_has__view_x_27___lambda__2___closed__1 = _init_l_lean_parser_string__lit_has__view_x_27___lambda__2___closed__1();
lean::mark_persistent(l_lean_parser_string__lit_has__view_x_27___lambda__2___closed__1);
 l_lean_parser_string__lit_has__view_x_27 = _init_l_lean_parser_string__lit_has__view_x_27();
lean::mark_persistent(l_lean_parser_string__lit_has__view_x_27);
 l_lean_parser_string__lit_has__view = _init_l_lean_parser_string__lit_has__view();
lean::mark_persistent(l_lean_parser_string__lit_has__view);
 l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__5___closed__1 = _init_l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__5___closed__1();
lean::mark_persistent(l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__5___closed__1);
 l_lean_parser_string__lit_x_27___closed__1 = _init_l_lean_parser_string__lit_x_27___closed__1();
lean::mark_persistent(l_lean_parser_string__lit_x_27___closed__1);
 l_lean_parser_token___closed__1 = _init_l_lean_parser_token___closed__1();
lean::mark_persistent(l_lean_parser_token___closed__1);
 l_lean_parser_number_parser___rarg___closed__1 = _init_l_lean_parser_number_parser___rarg___closed__1();
lean::mark_persistent(l_lean_parser_number_parser___rarg___closed__1);
 l_lean_parser_number_parser_view___rarg___closed__1 = _init_l_lean_parser_number_parser_view___rarg___closed__1();
lean::mark_persistent(l_lean_parser_number_parser_view___rarg___closed__1);
 l_lean_parser_number_parser_view___rarg___closed__2 = _init_l_lean_parser_number_parser_view___rarg___closed__2();
lean::mark_persistent(l_lean_parser_number_parser_view___rarg___closed__2);
 l_lean_parser_string__lit_parser___rarg___closed__1 = _init_l_lean_parser_string__lit_parser___rarg___closed__1();
lean::mark_persistent(l_lean_parser_string__lit_parser___rarg___closed__1);
 l_lean_parser_string__lit_parser_view___rarg___closed__1 = _init_l_lean_parser_string__lit_parser_view___rarg___closed__1();
lean::mark_persistent(l_lean_parser_string__lit_parser_view___rarg___closed__1);
 l_lean_parser_string__lit_parser_view___rarg___closed__2 = _init_l_lean_parser_string__lit_parser_view___rarg___closed__2();
lean::mark_persistent(l_lean_parser_string__lit_parser_view___rarg___closed__2);
 l_lean_parser_string__lit_view_value___closed__1 = _init_l_lean_parser_string__lit_view_value___closed__1();
lean::mark_persistent(l_lean_parser_string__lit_view_value___closed__1);
 l_lean_parser_ident_parser___rarg___closed__1 = _init_l_lean_parser_ident_parser___rarg___closed__1();
lean::mark_persistent(l_lean_parser_ident_parser___rarg___closed__1);
 l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1 = _init_l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1();
lean::mark_persistent(l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1);
 l_lean_parser_ident_parser_view___rarg___lambda__1___closed__2 = _init_l_lean_parser_ident_parser_view___rarg___lambda__1___closed__2();
lean::mark_persistent(l_lean_parser_ident_parser_view___rarg___lambda__1___closed__2);
 l_lean_parser_ident_parser_view___rarg___closed__1 = _init_l_lean_parser_ident_parser_view___rarg___closed__1();
lean::mark_persistent(l_lean_parser_ident_parser_view___rarg___closed__1);
 l_lean_parser_ident_parser_view___rarg___closed__2 = _init_l_lean_parser_ident_parser_view___rarg___closed__2();
lean::mark_persistent(l_lean_parser_ident_parser_view___rarg___closed__2);
 l_lean_parser_raw__ident_parser___rarg___closed__1 = _init_l_lean_parser_raw__ident_parser___rarg___closed__1();
lean::mark_persistent(l_lean_parser_raw__ident_parser___rarg___closed__1);
 l_lean_parser_indexed___rarg___lambda__1___closed__1 = _init_l_lean_parser_indexed___rarg___lambda__1___closed__1();
lean::mark_persistent(l_lean_parser_indexed___rarg___lambda__1___closed__1);
 l_lean_parser_indexed___rarg___closed__1 = _init_l_lean_parser_indexed___rarg___closed__1();
lean::mark_persistent(l_lean_parser_indexed___rarg___closed__1);
}
