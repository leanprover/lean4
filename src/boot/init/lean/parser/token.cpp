// Lean compiler output
// Module: init.lean.parser.token
// Imports: init.lean.parser.combinators init.lean.parser.string_literal
#include "runtime/object.h"
#include "runtime/apply.h"
#include "runtime/io.h"
#include "kernel/builtin.h"
typedef lean::object obj;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#endif
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__11(obj*, obj*, obj*, obj*);
obj* l___private_2142412293__mk__string__result___rarg(obj*, obj*);
obj* l___private_31565857__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__26(obj*, obj*, obj*);
obj* l___private_31565857__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__3(obj*, obj*, obj*);
obj* l_lean_parser_detail__ident__part_parser_lean_parser_has__tokens;
obj* l___private_31565857__take__while__aux___main___at_lean_parser_parse__oct__lit___spec__3(unsigned, obj*, obj*, obj*);
obj* l_list_mfoldr___main___at_lean_parser_number_x_27___spec__13(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_parsec__t_lookahead___at_lean_parser_detail__ident__suffix_parser___spec__4___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser___spec__10(obj*);
obj* l_lean_parser_match__token___closed__2;
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_parse__oct__lit___spec__6___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__4(obj*, obj*, obj*, obj*);
obj* l_lean_parser_parsec__t_bind__mk__res___rarg(obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while1___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__1(obj*, obj*, obj*);
obj* l_reader__t_orelse___at_lean_parser_parse__bin__lit___spec__1(obj*);
obj* l_lean_parser_unicode__symbol_lean_parser_has__tokens(obj*, obj*);
obj* l_lean_parser_monad__parsec_many1__aux_x_27___main___at_lean_parser_parse__bin__lit___spec__2___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__6(unsigned, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__6___boxed(obj*, obj*, obj*, obj*);
unsigned char l_char_is__whitespace(unsigned);
obj* l_lean_parser_monad__parsec_take__while1___at_lean_parser_parse__oct__lit___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__19___rarg(obj*, obj*);
extern obj* l___private_1297690757__many1__aux___main___rarg___closed__1;
obj* l_lean_parser_trie_match__prefix___rarg(obj*, obj*);
obj* l_lean_parser_detail__ident__suffix_has__view;
obj* l_lean_parser_match__token(obj*, obj*, obj*);
obj* l_lean_parser_number_parser_view___rarg___closed__2;
extern unsigned char l_true_decidable;
obj* l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__4(obj*, obj*, obj*);
obj* l_lean_parser_number_x_27___closed__1;
obj* l_lean_parser_raw_view___rarg(obj*, obj*, obj*, obj*, obj*, unsigned char);
obj* l_lean_parser_detail__ident__part_has__view;
obj* l_lean_parser_detail__ident__part_has__view_x_27___lambda__1___closed__2;
obj* l_lean_parser_number_has__view_x_27___lambda__2___closed__1;
obj* l_lean_parser_monad__parsec_error___at_lean_parser_number_x_27___spec__12___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l___private_31565857__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__18(obj*, obj*, obj*);
obj* l___private_31565857__take__while__aux___main___at_lean_parser_detail__ident__part_parser___spec__13(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_detail__ident__suffix_parser___spec__3(obj*);
obj* l_lean_parser_raw___rarg___lambda__3(unsigned char, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_finish__comment__block___closed__1;
obj* l_lean_parser_monad__parsec_error___at_lean_parser_string__lit_view_value___spec__3(obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__2(unsigned, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_foldl__aux___main___at___private_3519775105__ident_x_27___spec__21___lambda__2(unsigned, unsigned, obj*, obj*, obj*);
obj* l_reader__t_bind___at_lean_parser_detail__ident__suffix_parser___spec__7___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l___private_2012034129__whitespace__aux___main(obj*, obj*, obj*, obj*);
obj* l_lean_parser_number;
obj* l_reader__t_orelse___at_lean_parser_parse__bin__lit___spec__1___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_detail__ident__suffix_parser_lean_parser_has__view___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_raw__str_view__default___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_combinators_many___rarg___closed__1;
obj* l_lean_parser_symbol__or__ident___rarg(obj*, obj*);
obj* l_lean_parser_raw__str_view__default(obj*);
obj* l_lean_parser_as__substring___rarg___lambda__2(obj*, obj*, obj*, obj*, obj*);
obj* l___private_31565857__take__while__aux___main___at_lean_parser_detail__ident__part_parser___spec__5(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__21(obj*);
obj* l_lean_parser_monad__parsec_take__while1___at_lean_parser_detail__ident__part_parser___spec__1(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_many1__aux_x_27___main___at_lean_parser_parse__bin__lit___spec__2(unsigned, unsigned, obj*, obj*, obj*, obj*);
obj* l___private_31565857__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__9(obj*, obj*, obj*);
obj* l_lean_parser_raw___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l___private_31565857__take__while__aux___main___at_lean_parser_detail__ident__part_parser___spec__15(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__19(obj*);
obj* l_lean_parser_ident_parser_view___rarg___lambda__1___closed__2;
obj* l_lean_parser_raw_view___rarg___lambda__2(obj*);
obj* l_lean_parser_detail__ident_parser___closed__1;
obj* l_list_mfoldl___main___at_lean_parser_detail__ident__suffix_parser___spec__10(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_detail__ident__suffix_parser___lambda__1(obj*, obj*, obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_parse__quoted__char___rarg___lambda__7___closed__1;
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__4(obj*, obj*, obj*, obj*);
obj* l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__4___closed__1;
obj* l_lean_parser_indexed(obj*);
obj* l_lean_parser_monad__parsec_unexpected__at___at_lean_parser_string__lit_x_27___spec__6(obj*);
obj* l_lean_parser_monad__parsec_foldl__aux___main___at___private_3519775105__ident_x_27___spec__21___lambda__1___boxed(obj*, obj*, obj*, obj*);
obj* l___private_1765190339__to__nat__core(obj*, obj*, obj*, obj*);
obj* l_lean_parser_string__lit_parser___rarg(obj*);
obj* l_lean_parser_symbol__core___rarg(obj*, obj*, obj*, obj*);
obj* l_reader__t_lift___at_lean_parser_with__trailing___spec__1___rarg(obj*, obj*, obj*, obj*);
extern obj* l_mjoin___rarg___closed__1;
obj* l_lean_parser_string__lit_parser_tokens(obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__15(obj*);
obj* l_lean_parser_string__lit_parser___rarg___closed__1;
extern obj* l_lean_id__end__escape;
obj* l_lean_parser_number_view_to__nat(obj*);
extern obj* l_lean_parser_basic__parser__m_monad;
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__6___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_ident_parser_view___rarg(obj*);
obj* l_lean_parser_symbol___rarg(obj*, obj*, obj*);
obj* l_lean_parser_with__trailing___rarg___lambda__1(obj*, obj*);
obj* l_lean_parser_monad__parsec_any___at___private_4089500695__finish__comment__block__aux___main___spec__2(obj*, obj*, obj*);
obj* l_lean_parser_detail__ident__part_has__view_x_27___lambda__1(obj*);
obj* l_lean_parser_string__lit_has__view_x_27___lambda__1(obj*);
obj* l_lean_parser_parse__hex__lit(obj*, obj*, obj*);
extern obj* l_lean_parser_rec__t_run__parsec___rarg___lambda__1___closed__1;
obj* l_lean_parser_as__substring___rarg___lambda__1(obj*, obj*, obj*);
obj* l_lean_parser_detail__ident_has__view_x_27___lambda__1(obj*);
obj* l_lean_parser_list_cons_tokens___rarg(obj*, obj*);
obj* l_lean_parser_number_parser___rarg___lambda__1(obj*, obj*, obj*, obj*);
obj* l_list_foldl___main___at_lean_parser_unicode__symbol___spec__3(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_with__trailing___at_lean_parser_token___spec__3(obj*, obj*, obj*, obj*);
obj* l_lean_parser_raw_view___rarg___closed__1;
obj* l_rbmap_find___main___at_lean_parser_indexed___spec__1(obj*);
obj* l_lean_parser_number_has__view_x_27___lambda__1(obj*);
obj* l___private_31565857__take__while__aux___main___at_lean_parser_parse__oct__lit___spec__5(unsigned, obj*, obj*, obj*);
obj* l_lean_parser_raw___rarg___lambda__1(obj*, unsigned char, obj*, obj*, obj*, obj*);
obj* l_lean_parser_rec__t_run__parsec___at_lean_parser_detail__ident_parser___spec__1___lambda__1(obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_digit___at_lean_parser_string__lit_view_value___spec__8(obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__2___boxed(obj*, obj*, obj*, obj*);
obj* l_option_to__monad___main___at_lean_parser_indexed___spec__2___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_parser_string__lit_parser___rarg___lambda__1(obj*, obj*, obj*, obj*);
obj* l_lean_parser_parsec__t_try__mk__res___rarg(obj*);
obj* l_lean_parser_raw__ident_parser_view___rarg(obj*);
obj* l___private_31565857__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__7(obj*, obj*, obj*);
obj* l_lean_parser_string__lit_x_27___closed__1;
obj* l_lean_parser_monad__parsec_foldl__aux___main___at___private_3519775105__ident_x_27___spec__21___lambda__2___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_detail__ident__suffix_has__view_x_27;
obj* l_lean_parser_parsec__t_lookahead___at___private_2012034129__whitespace__aux___main___spec__4___closed__2;
obj* l_list_reverse___rarg(obj*);
obj* l___private_31565857__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__20(obj*, obj*, obj*);
obj* l_lean_parser_ident_parser___rarg___closed__1;
obj* l_reader__t_alternative___rarg(obj*, obj*);
obj* l_lean_parser_unicode__symbol_view__default___rarg(obj*, obj*, obj*, obj*);
obj* l___private_31565857__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__13(obj*, obj*, obj*);
obj* l_list_enum__from___main___rarg(obj*, obj*);
obj* l_lean_parser_detail__ident__part_has__view_x_27___lambda__1___closed__1;
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_number_x_27___spec__4___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_detail__ident_has__view_x_27;
obj* l_lean_parser_raw__str___rarg(obj*, obj*, obj*, obj*, unsigned char);
obj* l_lean_parser_number_parser_view___rarg___closed__1;
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_string__lit_view_value___spec__2(unsigned, obj*);
obj* l_lean_parser_parsec__t_lookahead___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__1(unsigned, obj*, obj*, obj*, obj*);
obj* l_reader__t_lift___at_lean_parser_detail__ident__suffix_parser___spec__5(obj*);
unsigned char l_char_is__digit(unsigned);
obj* l___private_31565857__take__while__aux___main___at_lean_parser_detail__ident__part_parser___spec__7(obj*, obj*, obj*);
obj* l_lean_parser_number_view_to__nat___main(obj*);
obj* l_lean_parser_as__substring___rarg___lambda__3(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__8___rarg(obj*, obj*);
obj* l_lean_parser_parsec__t_labels__mk__res___rarg(obj*, obj*);
obj* l___private_3229416877__update__trailing___main(obj*, obj*);
obj* l___private_4089500695__finish__comment__block__aux___main___closed__2;
obj* l___private_31565857__take__while__aux___main___at_lean_parser_parse__oct__lit___spec__7(unsigned, obj*, obj*, obj*);
obj* l_lean_parser_parsec__t_lookahead___at_lean_parser_number_x_27___spec__11(obj*, obj*, obj*, obj*, obj*, obj*);
unsigned char l_lean_parser_syntax_is__of__kind___main(obj*, obj*);
obj* l___private_2038417741__mk__consumed__result___rarg(unsigned char, obj*);
obj* l_lean_parser_ident_parser(obj*);
obj* l_lean_parser_raw___rarg(obj*, obj*, obj*, obj*, obj*, unsigned char);
obj* l___private_31565857__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__3(obj*, obj*, obj*);
obj* l_string_quote(obj*);
extern obj* l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
obj* l_lean_parser_raw___rarg___lambda__3___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_parsec__t_lookahead___at___private_2012034129__whitespace__aux___main___spec__4___closed__1;
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_3519775105__ident_x_27___spec__17(unsigned, obj*, obj*, obj*);
obj* l_rbmap_find___main___at_lean_parser_indexed___spec__3___rarg(obj*, obj*);
obj* l_lean_parser_raw__str_lean_parser_has__tokens(obj*, obj*, obj*, obj*, obj*, unsigned char);
obj* l_lean_parser_ident_parser_view___rarg___closed__1;
obj* l_lean_parser_monad__parsec_foldl__aux___main___at___private_3519775105__ident_x_27___spec__21(unsigned, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_longest__match___at_lean_parser_number_x_27___spec__10(obj*, obj*, obj*, obj*);
obj* l___private_31565857__take__while__aux___main___at_lean_parser_parse__oct__lit___spec__5___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_3519775105__ident_x_27___spec__4___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_3519775105__ident_x_27___spec__8(obj*, obj*, obj*, obj*);
unsigned char l_lean_is__id__end__escape(unsigned);
obj* l_lean_parser_parsec__t_run___at_lean_parser_parsec_parse___spec__1___rarg(obj*, obj*, obj*);
obj* l___private_1695453085__take__while__aux_x_27___main___at___private_2012034129__whitespace__aux___main___spec__6(obj*, unsigned char, obj*);
obj* l___private_31565857__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__24(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_unexpected__at___at_lean_parser_string__lit_x_27___spec__6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_string__lit_has__view;
obj* l_lean_parser_parsec__t_failure___at_lean_parser_token___spec__4___rarg(obj*, obj*);
obj* l_lean_parser_parse__string__literal___at_lean_parser_string__lit_view_value___spec__1(obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_3519775105__ident_x_27___spec__17___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_observing___at_lean_parser_peek__token___spec__2(obj*, obj*, obj*);
obj* l_lean_parser_parsec__t_lookahead___at___private_3519775105__ident_x_27___spec__19___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_raw___rarg___lambda__2___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l___private_31565857__take__while__aux___main___at___private_3519775105__ident_x_27___spec__14(obj*, obj*, obj*);
obj* l_lean_parser_raw__ident_parser_tokens(obj*, obj*);
obj* l_list_map___main___at_lean_parser_number_x_27___spec__9(obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__13(unsigned, obj*, obj*, obj*);
obj* l_lean_parser_symbol__or__ident(obj*);
obj* l_lean_parser_string__lit_parser_view(obj*);
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__25___rarg(obj*, obj*);
obj* l_lean_parser_symbol__core(obj*);
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__15___rarg(obj*, obj*);
unsigned char l_string_is__empty(obj*);
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__10___rarg(obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__25(obj*);
obj* l_lean_parser_number_parser_tokens(obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while_x_27___at___private_2012034129__whitespace__aux___main___spec__5___rarg(obj*, obj*);
obj* l_lean_parser_detail__ident__part_has__view_x_27;
obj* l_lean_parser_detail__ident__suffix_parser_lean_parser_has__view___lambda__1(unsigned, obj*, obj*, obj*, obj*);
unsigned char l_char_is__alpha(unsigned);
obj* l_lean_parser_detail__ident_parser___lambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_parse__string__literal__aux___main___at_lean_parser_string__lit_x_27___spec__2(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__17___rarg(obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_parse__hex__lit___spec__2(unsigned, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_number_x_27___spec__2(unsigned, obj*, obj*, obj*);
extern obj* l_lean_name_to__string___closed__1;
obj* l_lean_parser_number_has__view_x_27___lambda__1___closed__5;
obj* l_lean_parser_monad__parsec_foldl__aux___main___at___private_3519775105__ident_x_27___spec__21___lambda__1(unsigned, obj*, obj*, obj*);
obj* l_lean_parser_symbol__or__ident_view___rarg(obj*, obj*);
obj* l___private_3693562977__run__aux___at_lean_parser_detail__ident_parser___spec__3(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l___private_31565857__take__while__aux___main___at___private_3519775105__ident_x_27___spec__5(obj*, obj*, obj*);
obj* l_function_comp___rarg(obj*, obj*, obj*);
obj* l_lean_parser_string__lit_parser_view___rarg___closed__2;
obj* l_lean_parser_monad__parsec_ch___at___private_3519775105__ident_x_27___spec__11___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_number_view_of__nat(obj*);
obj* l_lean_parser_try__view___at_lean_parser_number_parser___spec__1(obj*);
obj* l_lean_parser_number_parser___rarg___closed__1;
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_detail__ident__suffix_parser___spec__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_number_has__view_x_27;
obj* l_lean_parser_unicode__symbol_view__default(obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_3519775105__ident_x_27___spec__6(unsigned, obj*, obj*, obj*);
obj* l_rbmap_find___main___at_lean_parser_indexed___spec__4(obj*);
obj* l_lean_parser_symbol(obj*);
obj* l___private_31565857__take__while__aux___main___at_lean_parser_parse__hex__lit___spec__3(obj*, obj*, obj*);
obj* l_lean_parser_detail__ident__suffix;
extern obj* l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
obj* l_lean_parser_detail__ident__part_has__view_x_27___lambda__2___closed__1;
obj* l_lean_parser_raw__str(obj*);
obj* l_lean_parser_string__lit;
obj* l_lean_parser_match__token___closed__1;
obj* l___private_580269747__str__aux___main(obj*, obj*, obj*);
obj* l_lean_parser_raw__ident_parser___rarg(obj*);
obj* l___private_31565857__take__while__aux___main___at_lean_parser_number_x_27___spec__7(obj*, obj*, obj*);
obj* l_lean_parser_raw__ident_parser(obj*);
obj* l_lean_parser_monad__parsec_take__while1___at_lean_parser_parse__hex__lit___spec__1(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__21___rarg(obj*, obj*);
obj* l_rbnode_find___main___at_lean_parser_token__map_insert___spec__2___rarg(obj*, obj*);
obj* l_reader__t_bind___at_lean_parser_with__trailing___spec__2___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l___private_31565857__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__5(obj*, obj*, obj*);
obj* l_lean_parser_number_has__view_x_27___lambda__1___closed__4;
obj* l_option_to__monad___main___at_lean_parser_indexed___spec__2(obj*);
obj* l_lean_parser_number_has__view;
obj* l_lean_parser_combinators_node___at_lean_parser_detail__ident__suffix_parser___spec__9(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_detail__ident_x_27___closed__1;
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__23___rarg(obj*, obj*);
obj* l_reader__t_lift___at_lean_parser_with__trailing___spec__1(obj*);
obj* l_lean_parser_number_has__view_x_27___lambda__2___closed__2;
obj* l___private_4089500695__finish__comment__block__aux___main___closed__1;
obj* l_lean_parser_monad__parsec_foldl___at___private_3519775105__ident_x_27___spec__20(obj*, unsigned, obj*, obj*, obj*);
obj* l_lean_parser_unicode__symbol(obj*);
obj* l_lean_parser_peek__token(obj*, obj*, obj*);
obj* l___private_4089500695__finish__comment__block__aux___main___closed__4;
obj* l_lean_parser_tokens___rarg(obj*);
obj* l_option_get__or__else___main___rarg(obj*, obj*);
unsigned char l_lean_is__id__rest(unsigned);
obj* l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_view_value___spec__7(obj*);
obj* l_lean_parser_string__lit_x_27___lambda__1(obj*, obj*, obj*, obj*);
obj* l_lean_parser_raw__ident_parser_view(obj*);
obj* l_lean_parser_raw__str_lean_parser_has__view(obj*);
obj* l_lean_parser_string__lit_parser(obj*);
obj* l_lean_parser_with__trailing___rarg___lambda__3(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_3519775105__ident_x_27___spec__13(unsigned, obj*, obj*, obj*);
obj* l_lean_parser_parse__quoted__char___at_lean_parser_string__lit_view_value___spec__6(obj*);
extern obj* l_lean_parser_no__kind;
obj* l_lean_parser_syntax_as__node___main(obj*);
obj* l___private_2012034129__whitespace__aux___main___closed__1;
obj* l_lean_parser_string__lit_view_value___closed__1;
obj* l_string_to__nat(obj*);
obj* l_lean_parser_symbol_view___rarg(obj*, obj*, obj*);
obj* l_lean_parser_rec__t_run___at_lean_parser_detail__ident_parser___spec__2(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_parsec__t_lookahead___at___private_3519775105__ident_x_27___spec__19(unsigned, obj*, obj*, obj*);
obj* l_lean_parser_symbol_view__default___rarg(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_detail__ident__suffix_parser___spec__1(unsigned, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_number_x_27___spec__6(obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser___spec__2(unsigned, obj*, obj*, obj*);
obj* l___private_1741613153__to__nat__base(obj*, obj*);
obj* l_lean_parser_raw_tokens___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l___private_2012034129__whitespace__aux___main___closed__2;
obj* l___private_3229416877__update__trailing__lst(obj*, obj*);
obj* l_lean_parser_symbol_tokens___rarg(obj*, obj*);
obj* l___private_31565857__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__12(obj*, obj*, obj*);
obj* l___private_2012034129__whitespace__aux___main___closed__3;
obj* l_lean_parser_monad__parsec_error___at_lean_parser_number_x_27___spec__12(obj*);
obj* l_lean_parser_raw_view___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_combinators_optional___at_lean_parser_detail__ident_x_27___spec__2(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_raw_view___rarg___lambda__1(obj*);
obj* l_lean_parser_detail__ident_parser___closed__2;
obj* l___private_31565857__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__16(obj*, obj*, obj*);
obj* l___private_1695453085__take__while__aux_x_27___main___at___private_2012034129__whitespace__aux___main___spec__3___boxed(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while_x_27___at___private_2012034129__whitespace__aux___main___spec__5(obj*);
obj* l_lean_parser_mk__raw__res(obj*, obj*);
obj* l_lean_parser_detail__ident_has__view;
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_parse__oct__lit___spec__4___boxed(obj*, obj*, obj*, obj*, obj*);
extern obj* l_char_has__repr___closed__1;
obj* l_string_iterator_nextn___main(obj*, obj*);
obj* l_lean_parser_token__cont(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_parsec__t_lookahead___at_lean_parser_peek__token___spec__1(obj*, obj*, obj*);
obj* l_lean_parser_string__lit_has__view_x_27___lambda__2(obj*);
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__8(obj*);
obj* l_lean_parser_monad__parsec_whitespace___at___private_2012034129__whitespace__aux___main___spec__1(obj*, obj*, obj*);
obj* l_lean_parser_detail__ident_parser(obj*, obj*, obj*);
obj* l_lean_parser_detail__ident_has__view_x_27___lambda__2(obj*);
obj* l_lean_parser_monad__parsec_curr___at___private_3519775105__ident_x_27___spec__2(obj*);
obj* l_lean_parser_combinators_node_view___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while_x_27___at___private_2012034129__whitespace__aux___main___spec__2___rarg(obj*, obj*);
obj* l_lean_parser_detail__ident__part_has__view_x_27___lambda__1___closed__3;
obj* l_lean_parser_unicode__symbol___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_parser_detail__ident_has__view_x_27___lambda__1___closed__1;
extern obj* l_lean_parser_monad__parsec_left__over___rarg___closed__1;
obj* l___private_31565857__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__7(obj*, obj*, obj*);
obj* l_lean_parser_finish__comment__block___closed__2;
obj* l_lean_parser_detail__ident__suffix_has__view_x_27___lambda__2(obj*);
obj* l_lean_parser_symbol__core___at_lean_parser_unicode__symbol___spec__1(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_id__part__escaped___at___private_3519775105__ident_x_27___spec__10(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while_x_27___at___private_2012034129__whitespace__aux___main___spec__2(obj*);
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
obj* l_lean_parser_rec__t_lean_parser_monad__parsec___rarg(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_str__core___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_parser_raw__str_lean_parser_has__view___rarg(obj*, obj*, obj*, obj*, unsigned char);
obj* l_lean_parser_number_x_27___lambda__1(obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while1___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__8(obj*, obj*, obj*);
obj* l_rbmap_find___main___at_lean_parser_indexed___spec__1___rarg(obj*, obj*);
obj* l___private_31565857__take__while__aux___main___at_lean_parser_number_x_27___spec__5(obj*, obj*, obj*);
obj* l_lean_parser_syntax_mk__node(obj*, obj*);
obj* l___private_31565857__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__10(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_unexpected__at___at_lean_parser_string__lit_view_value___spec__9___rarg(obj*, obj*, obj*);
obj* l___private_3693562977__run__aux___main___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_parser_detail__ident_has__view_x_27___lambda__1___closed__2;
obj* l_lean_parser_match__token___lambda__1(obj*);
obj* l___private_31565857__take__while__aux___main___at_lean_parser_number_x_27___spec__3(obj*, obj*, obj*);
obj* l_lean_parser_detail__ident__part_parser(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__2(unsigned, obj*, obj*, obj*);
obj* l_lean_parser_rec__t_run__parsec___at_lean_parser_detail__ident_parser___spec__1___closed__1;
obj* l_lean_parser_number_parser(obj*);
obj* l_lean_parser_detail__ident__part_parser___lambda__2(obj*, obj*, obj*, obj*);
obj* l_lean_parser_finish__comment__block(obj*, obj*, obj*, obj*);
obj* l_lean_parser_indexed___rarg___closed__1;
obj* l_lean_parser_raw__ident_parser___rarg___closed__1;
obj* l_lean_parser_ident_parser___rarg___lambda__1(obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_parse__oct__lit___spec__2(unsigned, unsigned, obj*, obj*, obj*);
obj* l_list_map___main___at_lean_parser_number_x_27___spec__9___lambda__1(obj*, obj*, obj*, obj*);
obj* l_lean_parser_combinators_longest__choice___at_lean_parser_number_x_27___spec__8(obj*, obj*, obj*, obj*);
obj* l___private_31565857__take__while__aux___main___at___private_3519775105__ident_x_27___spec__9(obj*, obj*, obj*);
obj* l___private_3229416877__update__trailing(obj*, obj*);
extern obj* l_lean_parser_parsec__t_failure___rarg___closed__1;
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__13___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_token(obj*, obj*, obj*);
obj* l_lean_parser_whitespace(obj*, obj*, obj*);
obj* l_reader__t_monad__except___rarg(obj*);
obj* l_lean_parser_indexed___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_as__substring(obj*);
obj* l_lean_parser_ident_parser_view___rarg___lambda__2(obj*);
obj* l___private_3519775105__ident_x_27(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_ch___at___private_3519775105__ident_x_27___spec__11(unsigned, obj*, obj*, obj*);
obj* l_lean_parser_with__trailing___rarg(obj*, obj*, obj*, obj*);
extern obj* l_lean_id__begin__escape;
obj* l___private_31565857__take__while__aux___main___at___private_3519775105__ident_x_27___spec__18(obj*, obj*, obj*);
obj* l_lean_parser_combinators_node___at_lean_parser_detail__ident__part_parser___spec__8(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_str__core___at___private_4089500695__finish__comment__block__aux___main___spec__3(obj*, obj*, obj*, obj*, obj*);
obj* l_rbmap_find___main___at_lean_parser_indexed___spec__3(obj*);
obj* l_lean_parser_parsec__t_lookahead___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_detail__ident__suffix_parser___spec__2___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser___spec__14(obj*);
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser___spec__14___rarg(obj*, obj*);
obj* l_lean_parser_with__trailing___rarg___lambda__2(obj*, obj*, obj*, obj*);
obj* l_lean_parser_parsec__t_failure___at_lean_parser_token___spec__4(obj*, obj*);
obj* l_lean_parser_symbol__or__ident_view(obj*);
obj* l_lean_parser_raw(obj*);
obj* l_lean_parser_monad__parsec_take__while1___at_lean_parser_parse__oct__lit___spec__1(unsigned, obj*, obj*, obj*);
obj* l_lean_parser_raw_view___rarg___closed__2;
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_3519775105__ident_x_27___spec__13___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_foldl__aux___main___at___private_3519775105__ident_x_27___spec__21___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_detail__ident_has__view_x_27___lambda__2___closed__1;
obj* l___private_31565857__take__while__aux___main___at___private_3519775105__ident_x_27___spec__7(obj*, obj*, obj*);
obj* l_lean_parser_string__lit_parser_view___rarg___closed__1;
obj* l_lean_parser_id__part___at___private_3519775105__ident_x_27___spec__1(obj*, obj*, obj*);
obj* l_lean_parser_symbol_view__default(obj*);
obj* l_reader__t_lift___at_lean_parser_detail__ident__suffix_parser___spec__5___rarg(obj*, obj*, obj*, obj*, obj*);
extern obj* l_list_mfoldr___main___at_lean_parser_monad__parsec_longest__match___spec__2___rarg___closed__1;
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__17(obj*);
obj* l_lean_parser_detail__ident__part_parser___lambda__1(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_any___at_lean_parser_string__lit_view_value___spec__5(obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser___spec__6(unsigned, obj*, obj*, obj*);
obj* l_lean_parser_parsec__t_merge___rarg(obj*, obj*);
obj* l_lean_parser_indexed___rarg___lambda__1___closed__1;
obj* l_lean_parser_monad__parsec_observing___at_lean_parser_token___spec__2(obj*, obj*, obj*);
obj* l_lean_parser_substring_to__string(obj*);
obj* l_lean_parser_try__view___at_lean_parser_string__lit_parser___spec__1(obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_parse__oct__lit___spec__6(unsigned, obj*, obj*, obj*, obj*);
obj* l_lean_parser_unicode__symbol_lean_parser_has__view(obj*);
obj* l___private_31565857__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__22(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_unexpected__at___at_lean_parser_string__lit_view_value___spec__9(obj*);
obj* l___private_3229416877__update__trailing__lst___main(obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__12___rarg(obj*, obj*);
obj* l_lean_parser_detail__ident__suffix_has__view_x_27___lambda__1___closed__1;
obj* l_lean_parser_ident_parser_view___rarg___closed__2;
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__10(obj*);
obj* l_lean_parser_detail__ident__part__escaped_has__view;
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__2___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_raw__str_view__default___rarg(obj*, obj*, obj*, obj*, unsigned char);
obj* l_lean_parser_combinators_any__of_view___rarg(obj*, obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_combinators_choice__aux___main___rarg___closed__1;
obj* l_reader__t_bind___at_lean_parser_detail__ident__suffix_parser___spec__7(obj*, obj*);
obj* l_lean_parser_raw_view___rarg___lambda__3(obj*);
obj* l_lean_parser_indexed___rarg(obj*, obj*, obj*);
obj* l_lean_parser_detail__ident__part__escaped_has__view_x_27___lambda__1(obj*);
obj* l_lean_parser_number_has__view_x_27___lambda__1___closed__1;
obj* l_lean_parser_rec__t_recurse___at_lean_parser_detail__ident__suffix_parser___spec__8(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser___spec__12(obj*);
obj* l___private_31565857__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__11(obj*, obj*, obj*);
obj* l_lean_parser_symbol_tokens(obj*, obj*);
obj* l_lean_parser_detail__ident__part__escaped_has__view_x_27;
obj* l_lean_parser_number_has__view_x_27___lambda__1___closed__3;
obj* l_lean_parser_as__substring___rarg(obj*, obj*, obj*, obj*);
obj* l___private_31565857__take__while__aux___main___at_lean_parser_parse__oct__lit___spec__3___boxed(obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_basic__parser__m_alternative;
obj* l_lean_parser_with__trailing___rarg___closed__1;
obj* l_lean_parser_detail__ident__suffix_parser_lean_parser_has__view;
obj* l_rbmap_find___main___at_lean_parser_indexed___spec__4___rarg(obj*, obj*);
obj* l_lean_parser_parsec__t_lookahead___at___private_2012034129__whitespace__aux___main___spec__4(obj*, obj*, obj*);
obj* l_lean_parser_symbol__or__ident___rarg___lambda__1(obj*, obj*, obj*, obj*);
obj* l_lean_parser_parsec__t_lookahead___at_lean_parser_token___spec__1(obj*, obj*, obj*);
obj* l___private_31565857__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__14(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while1___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__1(obj*, obj*, obj*);
obj* l___private_1765190339__to__nat__core___main(obj*, obj*, obj*, obj*);
obj* l_string_trim(obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_number_x_27___spec__4(unsigned, obj*, obj*, obj*);
obj* l___private_31565857__take__while__aux___main___at_lean_parser_parse__oct__lit___spec__7___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_number__or__string__lit(obj*, obj*, obj*);
obj* l_lean_parser_raw___rarg___lambda__2(obj*, unsigned char, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_option_get___main___at_lean_parser_run___spec__2(obj*);
obj* l_lean_parser_combinators_any__of___at_lean_parser_unicode__symbol___spec__2(obj*, obj*, obj*, obj*);
obj* l_lean_parser_unicode__symbol_lean_parser_has__tokens___rarg(obj*, obj*, obj*);
obj* l___private_1695453085__take__while__aux_x_27___main___at___private_2012034129__whitespace__aux___main___spec__3(obj*, unsigned char, obj*);
obj* l___private_31565857__take__while__aux___main___at_lean_parser_detail__ident__part_parser___spec__3(obj*, obj*, obj*);
obj* l_lean_parser_raw___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at___private_4089500695__finish__comment__block__aux___main___spec__1(obj*);
obj* l_lean_parser_raw_view(obj*);
obj* l_lean_parser_ident_parser_view___rarg___lambda__1(obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_3519775105__ident_x_27___spec__6___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_number_parser_view(obj*);
obj* l_lean_parser_number_has__view_x_27___lambda__2(obj*);
obj* l_lean_parser_parse__string__literal__aux___main___at_lean_parser_string__lit_view_value___spec__4(obj*, obj*, obj*);
obj* l_lean_parser_combinators_monad__lift_view___rarg(obj*, obj*, obj*);
obj* l_lean_parser_parsec__t_lookahead___at_lean_parser_detail__ident__suffix_parser___spec__4(obj*, obj*, obj*, unsigned, obj*);
obj* l_lean_parser_combinators_seq__right_view___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_reader__t_monad___rarg(obj*);
obj* l_lean_parser_detail__ident;
obj* l_lean_parser_parsec__t_lookahead___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__view___spec__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_detail__ident__part_parser_lean_parser_has__view___lambda__2(obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_foldl___at___private_3519775105__ident_x_27___spec__20___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l___private_31565857__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__5(obj*, obj*, obj*);
obj* l_lean_parser_parsec__t_lookahead___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__view___spec__1(unsigned, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser___spec__2___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_number_x_27___lambda__2(obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser___spec__10___rarg(obj*, obj*);
obj* l_lean_parser_detail__ident__part__escaped;
unsigned char l_lean_is__id__first(unsigned);
obj* l___private_4089500695__finish__comment__block__aux___main(obj*, obj*, obj*, obj*, obj*);
obj* l_nat_repr(obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_parse__oct__lit___spec__4(unsigned, unsigned, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_3519775105__ident_x_27___spec__15(obj*, obj*, obj*, obj*);
obj* l_lean_parser_parse__string__literal___at_lean_parser_string__lit_x_27___spec__1(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser___spec__4(obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_parse__hex__lit___spec__2___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__23(obj*);
obj* l_lean_parser_symbol__or__ident_tokens(obj*, obj*, obj*);
obj* l_lean_parser_with__trailing(obj*);
unsigned char l_lean_is__id__begin__escape(unsigned);
obj* l_lean_parser_ident_parser_view(obj*);
obj* l_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens;
obj* l_lean_parser_id__part__default___at___private_3519775105__ident_x_27___spec__3(obj*, obj*, obj*);
obj* l_lean_parser_combinators_choice__aux___main___at_lean_parser_detail__ident__part_parser___spec__16(obj*, obj*, obj*, obj*, obj*);
obj* l___private_4089500695__finish__comment__block__aux___main___closed__3;
obj* l_lean_parser_number_has__view_x_27___lambda__1___closed__2;
obj* l_lean_parser_monad__parsec_take__while1___at___private_3519775105__ident_x_27___spec__12(obj*, obj*, obj*);
obj* l_lean_parser_detail__ident__part_has__view_x_27___lambda__2(obj*);
obj* l_lean_parser_string__lit_has__view_x_27;
obj* l_lean_parser_monad__parsec_str__core___at_lean_parser_detail__ident__suffix_parser___spec__6(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__6(unsigned, obj*, obj*, obj*);
obj* l_lean_parser_detail__ident__part__escaped_has__view_x_27___lambda__2(obj*);
obj* l_lean_parser_string__lit_x_27(obj*, obj*, obj*);
obj* l_lean_parser_detail__ident__part_parser___closed__1;
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_3519775105__ident_x_27___spec__4(unsigned, obj*, obj*, obj*);
obj* l_lean_parser_number_x_27___lambda__3(obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_parse__oct__lit___spec__2___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_curr___at___private_3519775105__ident_x_27___spec__2___rarg(obj*, obj*);
obj* l_lean_parser_detail__ident__part_parser_lean_parser_has__view;
obj* l_lean_parser_detail__ident__part_has__view_x_27___lambda__2___closed__2;
obj* l_lean_parser_parse__bin__lit(obj*, obj*, obj*);
extern obj* l_lean_parser_basic__parser__m_lean_parser_monad__parsec;
obj* l_reader__t_bind___at_lean_parser_with__trailing___spec__2(obj*, obj*);
obj* l_lean_parser_detail__ident_x_27(obj*, obj*, obj*, obj*);
obj* l_lean_parser_parse__oct__lit(obj*, obj*, obj*);
obj* l___private_4089500695__finish__comment__block__aux(obj*, obj*, obj*, obj*, obj*);
obj* l_dlist_singleton___rarg(obj*, obj*);
obj* l_lean_parser_symbol__core___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_basic__parser__m_monad__except;
obj* l_lean_parser_parsec__t_orelse__mk__res___rarg(obj*, obj*);
obj* l_lean_parser_symbol_view(obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_detail__ident__suffix_parser___spec__2(obj*);
obj* l_lean_parser_unicode__symbol_lean_parser_has__view___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_parser_detail__ident__part__escaped_has__view_x_27___lambda__1___closed__1;
obj* l_rbmap_find___main___at_lean_parser_indexed___spec__5___rarg(obj*, obj*);
obj* l_lean_parser_detail__ident__suffix_parser___closed__1;
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_string__lit_view_value___spec__2___boxed(obj*, obj*);
obj* l_lean_parser_number_has__view_x_27___lambda__1___closed__6;
obj* l_option_map___rarg(obj*, obj*);
obj* l_lean_parser_raw__str_lean_parser_has__view___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l___private_31565857__take__while__aux___main___at_lean_parser_detail__ident__part_parser___spec__11(obj*, obj*, obj*);
obj* l_lean_parser_rec__t_run__parsec___at_lean_parser_detail__ident_parser___spec__1(obj*, obj*, obj*, obj*, obj*);
obj* l___private_1695453085__take__while__aux_x_27___main___at___private_2012034129__whitespace__aux___main___spec__6___boxed(obj*, obj*, obj*);
extern obj* l_lean_parser_combinators_any__of___rarg___closed__1;
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser___spec__12___rarg(obj*, obj*);
obj* l_lean_parser_number_parser_view___rarg(obj*);
obj* l_lean_parser_detail__ident__part_parser___lambda__3(obj*, obj*, obj*, obj*);
obj* l_lean_parser_number_parser___rarg(obj*);
obj* l_lean_parser_raw__str_lean_parser_has__tokens___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_substring_of__string(obj*);
obj* l___private_2012034129__whitespace__aux(obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser___spec__6___boxed(obj*, obj*, obj*, obj*);
obj* l_list_mfoldl___main___at_lean_parser_detail__ident__part_parser___spec__9(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_string__lit_view_value(obj*);
obj* l_lean_parser_parse__quoted__char___at_lean_parser_string__lit_x_27___spec__3(obj*, obj*, obj*);
obj* l_lean_parser_ident_parser_tokens(obj*, obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_number_x_27___spec__2___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_detail__ident__suffix_parser(obj*, obj*, obj*, obj*);
obj* l_reader__t_lift___at_lean_parser_detail__ident_x_27___spec__1(obj*);
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__9(unsigned, obj*, obj*, obj*);
obj* l_lean_parser_number_x_27___lambda__4(obj*, obj*, obj*, obj*);
obj* l_lean_parser_string__lit_parser_view___rarg(obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_string__lit_view_value___spec__3___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_detail__ident__suffix_parser___spec__3___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_ident_parser___rarg(obj*);
obj* l_reader__t_lift___at_lean_parser_detail__ident_x_27___spec__1___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_detail__ident__suffix_has__view_x_27___lambda__1(obj*);
obj* l___private_3602054007__mk__consume__token(obj*, obj*, obj*, obj*, obj*);
obj* l___private_31565857__take__while__aux___main___at___private_3519775105__ident_x_27___spec__16(obj*, obj*, obj*);
obj* l_char_quote__core(unsigned);
obj* l_lean_parser_number_x_27(obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_digit___at_lean_parser_string__lit_x_27___spec__5(obj*, obj*, obj*);
obj* l_lean_parser_detail__ident__part_parser_lean_parser_has__view___lambda__1(obj*, obj*, obj*, obj*);
obj* l_lean_parser_raw_tokens(obj*, obj*, obj*, obj*, obj*, obj*, unsigned char);
obj* l_lean_parser_monad__parsec_error___at___private_4089500695__finish__comment__block__aux___main___spec__1___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_raw_view___rarg___lambda__3___closed__1;
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
obj* l___private_4089500695__finish__comment__block__aux___main(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; unsigned char x_6; 
x_5 = lean::mk_nat_obj(0u);
x_6 = lean::nat_dec_eq(x_1, x_5);
lean::dec(x_5);
if (x_6 == 0)
{
obj* x_8; obj* x_9; unsigned char x_11; obj* x_12; obj* x_13; obj* x_15; obj* x_16; obj* x_21; obj* x_22; obj* x_24; 
x_8 = lean::mk_nat_obj(1u);
x_9 = lean::nat_sub(x_1, x_8);
lean::dec(x_1);
x_11 = lean::nat_dec_eq(x_0, x_8);
x_15 = l___private_4089500695__finish__comment__block__aux___main___closed__3;
x_16 = l___private_4089500695__finish__comment__block__aux___main___closed__4;
lean::inc(x_3);
lean::inc(x_2);
lean::inc(x_16);
lean::inc(x_15);
x_21 = l_lean_parser_monad__parsec_str__core___at___private_4089500695__finish__comment__block__aux___main___spec__3(x_15, x_16, x_2, x_3, x_4);
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
x_35 = l___private_4089500695__finish__comment__block__aux___main(x_32, x_9, x_2, x_27, x_24);
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
obj* x_42; unsigned char x_44; obj* x_45; obj* x_46; obj* x_47; 
x_42 = lean::cnstr_get(x_22, 0);
lean::inc(x_42);
x_44 = lean::cnstr_get_scalar<unsigned char>(x_22, sizeof(void*)*1);
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
obj* x_54; unsigned char x_56; obj* x_57; obj* x_58; 
x_54 = lean::cnstr_get(x_12, 0);
lean::inc(x_54);
x_56 = lean::cnstr_get_scalar<unsigned char>(x_12, sizeof(void*)*1);
if (x_56 == 0)
{
obj* x_61; obj* x_62; obj* x_67; obj* x_68; obj* x_70; 
lean::dec(x_12);
x_61 = l___private_4089500695__finish__comment__block__aux___main___closed__1;
x_62 = l___private_4089500695__finish__comment__block__aux___main___closed__2;
lean::inc(x_3);
lean::inc(x_2);
lean::inc(x_62);
lean::inc(x_61);
x_67 = l_lean_parser_monad__parsec_str__core___at___private_4089500695__finish__comment__block__aux___main___spec__3(x_61, x_62, x_2, x_3, x_13);
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
x_83 = l___private_4089500695__finish__comment__block__aux___main(x_79, x_9, x_2, x_73, x_70);
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
obj* x_97; unsigned char x_99; obj* x_100; obj* x_101; obj* x_102; 
lean::dec(x_8);
x_97 = lean::cnstr_get(x_68, 0);
lean::inc(x_97);
x_99 = lean::cnstr_get_scalar<unsigned char>(x_68, sizeof(void*)*1);
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
obj* x_116; unsigned char x_118; 
x_116 = lean::cnstr_get(x_57, 0);
lean::inc(x_116);
x_118 = lean::cnstr_get_scalar<unsigned char>(x_57, sizeof(void*)*1);
if (x_118 == 0)
{
obj* x_121; obj* x_122; obj* x_124; obj* x_126; 
lean::dec(x_57);
lean::inc(x_2);
x_121 = l_lean_parser_monad__parsec_any___at___private_4089500695__finish__comment__block__aux___main___spec__2(x_2, x_3, x_58);
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
x_132 = l___private_4089500695__finish__comment__block__aux___main(x_0, x_9, x_2, x_127, x_124);
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
obj* x_145; unsigned char x_147; obj* x_148; obj* x_149; obj* x_150; obj* x_151; obj* x_152; obj* x_153; 
lean::dec(x_9);
lean::dec(x_0);
lean::dec(x_2);
x_145 = lean::cnstr_get(x_122, 0);
lean::inc(x_145);
x_147 = lean::cnstr_get_scalar<unsigned char>(x_122, sizeof(void*)*1);
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
x_164 = l___private_1297690757__many1__aux___main___rarg___closed__1;
x_165 = l_mjoin___rarg___closed__1;
lean::inc(x_163);
lean::inc(x_165);
lean::inc(x_164);
x_169 = l_lean_parser_monad__parsec_error___at___private_4089500695__finish__comment__block__aux___main___spec__1___rarg(x_164, x_165, x_163, x_163, x_2, x_3, x_4);
return x_169;
}
}
}
obj* _init_l___private_4089500695__finish__comment__block__aux___main___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("-/");
return x_0;
}
}
obj* _init_l___private_4089500695__finish__comment__block__aux___main___closed__2() {
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
obj* _init_l___private_4089500695__finish__comment__block__aux___main___closed__3() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("/-");
return x_0;
}
}
obj* _init_l___private_4089500695__finish__comment__block__aux___main___closed__4() {
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
obj* l_lean_parser_monad__parsec_error___at___private_4089500695__finish__comment__block__aux___main___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_8; obj* x_9; unsigned char x_10; obj* x_11; obj* x_12; obj* x_13; 
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
obj* l_lean_parser_monad__parsec_error___at___private_4089500695__finish__comment__block__aux___main___spec__1(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___at___private_4089500695__finish__comment__block__aux___main___spec__1___rarg), 7, 0);
return x_2;
}
}
obj* l_lean_parser_monad__parsec_any___at___private_4089500695__finish__comment__block__aux___main___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
unsigned char x_3; 
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
x_10 = l_lean_parser_monad__parsec_error___at___private_4089500695__finish__comment__block__aux___main___spec__1___rarg(x_5, x_6, x_4, x_4, x_0, x_1, x_2);
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
unsigned x_20; unsigned char x_21; 
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
x_32 = l_lean_parser_monad__parsec_error___at___private_4089500695__finish__comment__block__aux___main___spec__1___rarg(x_27, x_29, x_28, x_28, x_0, x_1, x_2);
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
obj* l_lean_parser_monad__parsec_str__core___at___private_4089500695__finish__comment__block__aux___main___spec__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
unsigned char x_7; 
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
x_12 = l___private_580269747__str__aux___main(x_8, x_10, x_3);
if (lean::obj_tag(x_12) == 0)
{
obj* x_15; obj* x_16; obj* x_18; unsigned char x_19; obj* x_20; obj* x_21; obj* x_22; 
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
obj* l___private_4089500695__finish__comment__block__aux(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l___private_4089500695__finish__comment__block__aux___main(x_0, x_1, x_2, x_3, x_4);
return x_5;
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
x_9 = l___private_4089500695__finish__comment__block__aux___main(x_0, x_6, x_1, x_2, x_3);
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
obj* l___private_2012034129__whitespace__aux___main(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; unsigned char x_5; 
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::nat_dec_eq(x_0, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
obj* x_8; obj* x_9; obj* x_11; obj* x_13; 
lean::inc(x_1);
x_8 = l_lean_parser_monad__parsec_whitespace___at___private_2012034129__whitespace__aux___main___spec__1(x_1, x_2, x_3);
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
x_25 = l___private_2012034129__whitespace__aux___main___closed__2;
x_26 = l___private_2012034129__whitespace__aux___main___closed__3;
lean::inc(x_14);
lean::inc(x_1);
lean::inc(x_26);
lean::inc(x_25);
x_31 = l_lean_parser_monad__parsec_str__core___at___private_4089500695__finish__comment__block__aux___main___spec__3(x_25, x_26, x_1, x_14, x_11);
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
x_42 = l_lean_parser_monad__parsec_take__while_x_27___at___private_2012034129__whitespace__aux___main___spec__5___rarg(x_37, x_34);
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
x_56 = l___private_2012034129__whitespace__aux___main(x_20, x_1, x_49, x_45);
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
obj* x_63; unsigned char x_65; obj* x_66; obj* x_67; obj* x_68; 
x_63 = lean::cnstr_get(x_48, 0);
lean::inc(x_63);
x_65 = lean::cnstr_get_scalar<unsigned char>(x_48, sizeof(void*)*1);
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
obj* x_69; unsigned char x_71; obj* x_72; obj* x_73; obj* x_74; 
x_69 = lean::cnstr_get(x_32, 0);
lean::inc(x_69);
x_71 = lean::cnstr_get_scalar<unsigned char>(x_32, sizeof(void*)*1);
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
obj* x_82; unsigned char x_84; obj* x_85; obj* x_86; 
x_82 = lean::cnstr_get(x_22, 0);
lean::inc(x_82);
x_84 = lean::cnstr_get_scalar<unsigned char>(x_22, sizeof(void*)*1);
if (x_84 == 0)
{
obj* x_89; obj* x_90; obj* x_95; obj* x_96; obj* x_98; 
lean::dec(x_22);
x_89 = l___private_4089500695__finish__comment__block__aux___main___closed__3;
x_90 = l___private_4089500695__finish__comment__block__aux___main___closed__4;
lean::inc(x_14);
lean::inc(x_1);
lean::inc(x_90);
lean::inc(x_89);
x_95 = l_lean_parser_monad__parsec_str__core___at___private_4089500695__finish__comment__block__aux___main___spec__3(x_89, x_90, x_1, x_14, x_23);
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
x_108 = l_lean_parser_parsec__t_lookahead___at___private_2012034129__whitespace__aux___main___spec__4(x_1, x_101, x_98);
x_109 = lean::cnstr_get(x_108, 0);
lean::inc(x_109);
x_111 = lean::cnstr_get(x_108, 1);
lean::inc(x_111);
lean::dec(x_108);
if (lean::obj_tag(x_109) == 0)
{
obj* x_114; obj* x_116; obj* x_118; unsigned char x_121; 
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
x_126 = l___private_2012034129__whitespace__aux___main___closed__1;
x_127 = l_mjoin___rarg___closed__1;
lean::inc(x_1);
lean::inc(x_127);
lean::inc(x_126);
x_131 = l_lean_parser_monad__parsec_error___at___private_4089500695__finish__comment__block__aux___main___spec__1___rarg(x_126, x_127, x_124, x_125, x_1, x_116, x_111);
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
obj* x_155; unsigned char x_157; obj* x_158; obj* x_159; obj* x_160; obj* x_161; obj* x_163; obj* x_164; obj* x_165; 
lean::dec(x_101);
lean::dec(x_105);
x_155 = lean::cnstr_get(x_109, 0);
lean::inc(x_155);
x_157 = lean::cnstr_get_scalar<unsigned char>(x_109, sizeof(void*)*1);
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
obj* x_166; obj* x_168; unsigned char x_169; obj* x_170; obj* x_171; 
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
x_199 = l___private_2012034129__whitespace__aux___main(x_20, x_1, x_194, x_190);
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
obj* x_211; unsigned char x_213; 
x_211 = lean::cnstr_get(x_205, 0);
lean::inc(x_211);
x_213 = lean::cnstr_get_scalar<unsigned char>(x_205, sizeof(void*)*1);
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
obj* x_238; unsigned char x_240; obj* x_241; 
lean::dec(x_20);
lean::dec(x_1);
x_238 = lean::cnstr_get(x_193, 0);
lean::inc(x_238);
x_240 = lean::cnstr_get_scalar<unsigned char>(x_193, sizeof(void*)*1);
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
obj* x_268; unsigned char x_270; obj* x_271; 
lean::dec(x_20);
lean::dec(x_1);
lean::dec(x_19);
x_268 = lean::cnstr_get(x_85, 0);
lean::inc(x_268);
x_270 = lean::cnstr_get_scalar<unsigned char>(x_85, sizeof(void*)*1);
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
obj* x_297; unsigned char x_299; obj* x_300; obj* x_301; obj* x_302; obj* x_303; 
lean::dec(x_1);
lean::dec(x_0);
x_297 = lean::cnstr_get(x_9, 0);
lean::inc(x_297);
x_299 = lean::cnstr_get_scalar<unsigned char>(x_9, sizeof(void*)*1);
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
x_306 = l___private_1297690757__many1__aux___main___rarg___closed__1;
x_307 = l_mjoin___rarg___closed__1;
lean::inc(x_305);
lean::inc(x_307);
lean::inc(x_306);
x_311 = l_lean_parser_monad__parsec_error___at___private_4089500695__finish__comment__block__aux___main___spec__1___rarg(x_306, x_307, x_305, x_305, x_1, x_2, x_3);
return x_311;
}
}
}
obj* _init_l___private_2012034129__whitespace__aux___main___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("input");
return x_0;
}
}
obj* _init_l___private_2012034129__whitespace__aux___main___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("--");
return x_0;
}
}
obj* _init_l___private_2012034129__whitespace__aux___main___closed__3() {
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
obj* l___private_1695453085__take__while__aux_x_27___main___at___private_2012034129__whitespace__aux___main___spec__3(obj* x_0, unsigned char x_1, obj* x_2) {
_start:
{
obj* x_3; unsigned char x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
unsigned char x_6; 
x_6 = lean::string_iterator_has_next(x_2);
if (x_6 == 0)
{
obj* x_8; 
lean::dec(x_0);
x_8 = l___private_2038417741__mk__consumed__result___rarg(x_1, x_2);
return x_8;
}
else
{
unsigned x_9; unsigned char x_10; 
x_9 = lean::string_iterator_curr(x_2);
x_10 = l_char_is__whitespace(x_9);
if (x_10 == 0)
{
obj* x_12; 
lean::dec(x_0);
x_12 = l___private_2038417741__mk__consumed__result___rarg(x_1, x_2);
return x_12;
}
else
{
obj* x_13; obj* x_14; obj* x_17; unsigned char x_18; 
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
x_21 = l___private_2038417741__mk__consumed__result___rarg(x_1, x_2);
return x_21;
}
}
}
obj* l_lean_parser_monad__parsec_take__while_x_27___at___private_2012034129__whitespace__aux___main___spec__2___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; unsigned char x_3; obj* x_4; obj* x_5; 
x_2 = lean::string_iterator_remaining(x_0);
x_3 = 0;
x_4 = l___private_1695453085__take__while__aux_x_27___main___at___private_2012034129__whitespace__aux___main___spec__3(x_2, x_3, x_0);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_1);
return x_5;
}
}
obj* l_lean_parser_monad__parsec_take__while_x_27___at___private_2012034129__whitespace__aux___main___spec__2(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_take__while_x_27___at___private_2012034129__whitespace__aux___main___spec__2___rarg), 2, 0);
return x_2;
}
}
obj* l_lean_parser_monad__parsec_whitespace___at___private_2012034129__whitespace__aux___main___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; 
lean::dec(x_0);
x_4 = l_lean_parser_monad__parsec_take__while_x_27___at___private_2012034129__whitespace__aux___main___spec__2___rarg(x_1, x_2);
return x_4;
}
}
obj* l_lean_parser_parsec__t_lookahead___at___private_2012034129__whitespace__aux___main___spec__4(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_8; obj* x_9; obj* x_11; obj* x_13; 
x_3 = l_lean_parser_parsec__t_lookahead___at___private_2012034129__whitespace__aux___main___spec__4___closed__1;
x_4 = l_lean_parser_parsec__t_lookahead___at___private_2012034129__whitespace__aux___main___spec__4___closed__2;
lean::inc(x_1);
lean::inc(x_4);
lean::inc(x_3);
x_8 = l_lean_parser_monad__parsec_str__core___at___private_4089500695__finish__comment__block__aux___main___spec__3(x_3, x_4, x_0, x_1, x_2);
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
obj* x_14; obj* x_16; obj* x_18; unsigned char x_19; obj* x_20; obj* x_21; obj* x_23; obj* x_24; 
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
unsigned char x_34; obj* x_35; obj* x_37; obj* x_38; 
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
unsigned char x_40; obj* x_41; obj* x_42; obj* x_44; obj* x_45; 
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
obj* _init_l_lean_parser_parsec__t_lookahead___at___private_2012034129__whitespace__aux___main___spec__4___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("-");
return x_0;
}
}
obj* _init_l_lean_parser_parsec__t_lookahead___at___private_2012034129__whitespace__aux___main___spec__4___closed__2() {
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
obj* l___private_1695453085__take__while__aux_x_27___main___at___private_2012034129__whitespace__aux___main___spec__6(obj* x_0, unsigned char x_1, obj* x_2) {
_start:
{
obj* x_3; unsigned char x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
unsigned char x_5; 
x_5 = lean::string_iterator_has_next(x_2);
if (x_5 == 0)
{
obj* x_8; 
lean::dec(x_3);
lean::dec(x_0);
x_8 = l___private_2038417741__mk__consumed__result___rarg(x_1, x_2);
return x_8;
}
else
{
obj* x_9; obj* x_10; unsigned x_13; obj* x_14; obj* x_15; unsigned char x_16; 
x_9 = lean::mk_nat_obj(1u);
x_10 = lean::nat_sub(x_0, x_9);
lean::dec(x_9);
lean::dec(x_0);
x_13 = lean::string_iterator_curr(x_2);
x_14 = lean::mk_nat_obj(10u);
x_15 = lean::mk_nat_obj(55296u);
x_16 = lean::nat_dec_lt(x_14, x_15);
lean::dec(x_15);
if (x_16 == 0)
{
obj* x_18; unsigned char x_19; 
x_18 = lean::mk_nat_obj(57343u);
x_19 = lean::nat_dec_lt(x_18, x_14);
lean::dec(x_18);
if (x_19 == 0)
{
obj* x_22; unsigned char x_23; 
lean::dec(x_14);
x_22 = lean::box_uint32(x_13);
x_23 = lean::nat_dec_eq(x_22, x_3);
lean::dec(x_3);
lean::dec(x_22);
if (x_23 == 0)
{
obj* x_26; unsigned char x_27; 
x_26 = lean::string_iterator_next(x_2);
x_27 = 1;
x_0 = x_10;
x_1 = x_27;
x_2 = x_26;
goto _start;
}
else
{
obj* x_30; 
lean::dec(x_10);
x_30 = l___private_2038417741__mk__consumed__result___rarg(x_1, x_2);
return x_30;
}
}
else
{
obj* x_31; unsigned char x_32; 
x_31 = lean::mk_nat_obj(1114112u);
x_32 = lean::nat_dec_lt(x_14, x_31);
lean::dec(x_31);
if (x_32 == 0)
{
obj* x_35; unsigned char x_36; 
lean::dec(x_14);
x_35 = lean::box_uint32(x_13);
x_36 = lean::nat_dec_eq(x_35, x_3);
lean::dec(x_3);
lean::dec(x_35);
if (x_36 == 0)
{
obj* x_39; unsigned char x_40; 
x_39 = lean::string_iterator_next(x_2);
x_40 = 1;
x_0 = x_10;
x_1 = x_40;
x_2 = x_39;
goto _start;
}
else
{
obj* x_43; 
lean::dec(x_10);
x_43 = l___private_2038417741__mk__consumed__result___rarg(x_1, x_2);
return x_43;
}
}
else
{
obj* x_45; unsigned char x_46; 
lean::dec(x_3);
x_45 = lean::box_uint32(x_13);
x_46 = lean::nat_dec_eq(x_45, x_14);
lean::dec(x_14);
lean::dec(x_45);
if (x_46 == 0)
{
obj* x_49; unsigned char x_50; 
x_49 = lean::string_iterator_next(x_2);
x_50 = 1;
x_0 = x_10;
x_1 = x_50;
x_2 = x_49;
goto _start;
}
else
{
obj* x_53; 
lean::dec(x_10);
x_53 = l___private_2038417741__mk__consumed__result___rarg(x_1, x_2);
return x_53;
}
}
}
}
else
{
obj* x_55; unsigned char x_56; 
lean::dec(x_3);
x_55 = lean::box_uint32(x_13);
x_56 = lean::nat_dec_eq(x_55, x_14);
lean::dec(x_14);
lean::dec(x_55);
if (x_56 == 0)
{
obj* x_59; unsigned char x_60; 
x_59 = lean::string_iterator_next(x_2);
x_60 = 1;
x_0 = x_10;
x_1 = x_60;
x_2 = x_59;
goto _start;
}
else
{
obj* x_63; 
lean::dec(x_10);
x_63 = l___private_2038417741__mk__consumed__result___rarg(x_1, x_2);
return x_63;
}
}
}
}
else
{
obj* x_66; 
lean::dec(x_3);
lean::dec(x_0);
x_66 = l___private_2038417741__mk__consumed__result___rarg(x_1, x_2);
return x_66;
}
}
}
obj* l_lean_parser_monad__parsec_take__while_x_27___at___private_2012034129__whitespace__aux___main___spec__5___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; unsigned char x_3; obj* x_4; obj* x_5; 
x_2 = lean::string_iterator_remaining(x_0);
x_3 = 0;
x_4 = l___private_1695453085__take__while__aux_x_27___main___at___private_2012034129__whitespace__aux___main___spec__6(x_2, x_3, x_0);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_1);
return x_5;
}
}
obj* l_lean_parser_monad__parsec_take__while_x_27___at___private_2012034129__whitespace__aux___main___spec__5(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_take__while_x_27___at___private_2012034129__whitespace__aux___main___spec__5___rarg), 2, 0);
return x_2;
}
}
obj* l___private_1695453085__take__while__aux_x_27___main___at___private_2012034129__whitespace__aux___main___spec__3___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
unsigned char x_3; obj* x_4; 
x_3 = lean::unbox(x_1);
x_4 = l___private_1695453085__take__while__aux_x_27___main___at___private_2012034129__whitespace__aux___main___spec__3(x_0, x_3, x_2);
return x_4;
}
}
obj* l___private_1695453085__take__while__aux_x_27___main___at___private_2012034129__whitespace__aux___main___spec__6___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
unsigned char x_3; obj* x_4; 
x_3 = lean::unbox(x_1);
x_4 = l___private_1695453085__take__while__aux_x_27___main___at___private_2012034129__whitespace__aux___main___spec__6(x_0, x_3, x_2);
return x_4;
}
}
obj* l___private_2012034129__whitespace__aux(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_2012034129__whitespace__aux___main(x_0, x_1, x_2, x_3);
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
x_8 = l___private_2012034129__whitespace__aux___main(x_5, x_0, x_1, x_2);
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
obj* l_lean_parser_as__substring(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_as__substring___rarg), 4, 0);
return x_2;
}
}
obj* l___private_3229416877__update__trailing___main(obj* x_0, obj* x_1) {
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
x_66 = l___private_3229416877__update__trailing__lst___main(x_0, x_64);
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
obj* l___private_3229416877__update__trailing__lst___main(obj* x_0, obj* x_1) {
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
x_8 = l___private_3229416877__update__trailing___main(x_0, x_3);
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
x_10 = l___private_3229416877__update__trailing__lst___main(x_0, x_5);
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
obj* l___private_3229416877__update__trailing(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_3229416877__update__trailing___main(x_0, x_1);
return x_2;
}
}
obj* l___private_3229416877__update__trailing__lst(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_3229416877__update__trailing__lst___main(x_0, x_1);
return x_2;
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
obj* x_23; unsigned char x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
lean::dec(x_0);
x_23 = lean::cnstr_get(x_5, 0);
lean::inc(x_23);
x_25 = lean::cnstr_get_scalar<unsigned char>(x_5, sizeof(void*)*1);
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
x_9 = l___private_3229416877__update__trailing___main(x_2, x_1);
x_10 = lean::apply_2(x_6, lean::box(0), x_9);
return x_10;
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
obj* x_29; unsigned char x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; 
lean::dec(x_1);
lean::dec(x_2);
x_29 = lean::cnstr_get(x_7, 0);
lean::inc(x_29);
x_31 = lean::cnstr_get_scalar<unsigned char>(x_7, sizeof(void*)*1);
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
obj* l_lean_parser_raw___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, unsigned char x_5) {
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
obj* l_lean_parser_raw___rarg___lambda__1(obj* x_0, unsigned char x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
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
obj* l_lean_parser_raw___rarg___lambda__2(obj* x_0, unsigned char x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
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
obj* l_lean_parser_raw___rarg___lambda__3(unsigned char x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
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
obj* l_lean_parser_raw(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_raw___rarg___boxed), 6, 0);
return x_2;
}
}
obj* l_lean_parser_raw___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
unsigned char x_6; obj* x_7; 
x_6 = lean::unbox(x_5);
x_7 = l_lean_parser_raw___rarg(x_0, x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
obj* l_lean_parser_raw___rarg___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
unsigned char x_6; obj* x_7; 
x_6 = lean::unbox(x_1);
x_7 = l_lean_parser_raw___rarg___lambda__1(x_0, x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
obj* l_lean_parser_raw___rarg___lambda__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
unsigned char x_8; obj* x_9; 
x_8 = lean::unbox(x_1);
x_9 = l_lean_parser_raw___rarg___lambda__2(x_0, x_8, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
obj* l_lean_parser_raw___rarg___lambda__3___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
unsigned char x_8; obj* x_9; 
x_8 = lean::unbox(x_0);
x_9 = l_lean_parser_raw___rarg___lambda__3(x_8, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
obj* l_lean_parser_raw_tokens(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, unsigned char x_6) {
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
unsigned char x_7; obj* x_8; 
x_7 = lean::unbox(x_6);
x_8 = l_lean_parser_raw_tokens(x_0, x_1, x_2, x_3, x_4, x_5, x_7);
return x_8;
}
}
obj* l_lean_parser_raw_view___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, unsigned char x_5) {
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
obj* _init_l_lean_parser_raw_view___rarg___lambda__3___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_raw_view___rarg___lambda__2), 1, 0);
return x_0;
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
unsigned char x_6; obj* x_7; 
x_6 = lean::unbox(x_5);
x_7 = l_lean_parser_raw_view___rarg(x_0, x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
obj* l_lean_parser_raw__str___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, unsigned char x_4) {
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
unsigned char x_5; obj* x_6; 
x_5 = lean::unbox(x_4);
x_6 = l_lean_parser_raw__str___rarg(x_0, x_1, x_2, x_3, x_5);
return x_6;
}
}
obj* l_lean_parser_raw__str_lean_parser_has__view___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, unsigned char x_4) {
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
unsigned char x_5; obj* x_6; 
x_5 = lean::unbox(x_4);
x_6 = l_lean_parser_raw__str_lean_parser_has__view___rarg(x_0, x_1, x_2, x_3, x_5);
return x_6;
}
}
obj* l_lean_parser_raw__str_lean_parser_has__tokens(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, unsigned char x_5) {
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
unsigned char x_6; obj* x_7; 
x_6 = lean::unbox(x_5);
x_7 = l_lean_parser_raw__str_lean_parser_has__tokens(x_0, x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
obj* l_lean_parser_raw__str_view__default___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, unsigned char x_4) {
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
unsigned char x_5; obj* x_6; 
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
x_2 = lean::name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean::name_mk_string(x_2, x_3);
x_5 = lean::mk_string("detail_ident_part_escaped");
x_6 = lean::name_mk_string(x_4, x_5);
return x_6;
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
x_2 = lean::name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean::name_mk_string(x_2, x_3);
x_5 = lean::mk_string("detail_ident_part");
x_6 = lean::name_mk_string(x_4, x_5);
return x_6;
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
obj* x_8; obj* x_11; obj* x_13; obj* x_16; unsigned char x_17; 
x_8 = lean::cnstr_get(x_4, 0);
lean::inc(x_8);
lean::dec(x_4);
x_11 = lean::cnstr_get(x_8, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_8, 1);
lean::inc(x_13);
lean::dec(x_8);
x_16 = l_lean_parser_detail__ident__part_has__view_x_27___lambda__1___closed__3;
x_17 = lean::name_dec_eq(x_11, x_16);
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
obj* x_51; obj* x_53; obj* x_56; unsigned char x_57; 
x_51 = lean::cnstr_get(x_38, 0);
lean::inc(x_51);
x_53 = lean::cnstr_get(x_38, 1);
lean::inc(x_53);
lean::dec(x_38);
x_56 = lean::box(0);
x_57 = lean::name_dec_eq(x_51, x_56);
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
obj* x_83; unsigned char x_84; 
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
obj* x_5; unsigned char x_6; 
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
x_2 = lean::name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean::name_mk_string(x_2, x_3);
x_5 = lean::mk_string("detail_ident_part");
x_6 = lean::name_mk_string(x_4, x_5);
return x_6;
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
obj* _init_l_lean_parser_detail__ident__part_has__view_x_27___lambda__2___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_nat_obj(0u);
x_2 = lean::name_mk_numeral(x_0, x_1);
return x_2;
}
}
obj* _init_l_lean_parser_detail__ident__part_has__view_x_27___lambda__2___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_nat_obj(1u);
x_2 = lean::name_mk_numeral(x_0, x_1);
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
obj* l_lean_parser_detail__ident__part_parser(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_7; 
x_3 = l_lean_parser_detail__ident__part;
x_4 = l_lean_parser_detail__ident__part_parser___closed__1;
lean::inc(x_4);
lean::inc(x_3);
x_7 = l_lean_parser_combinators_node___at_lean_parser_detail__ident__part_parser___spec__8(x_3, x_4, x_0, x_1, x_2);
return x_7;
}
}
obj* _init_l_lean_parser_detail__ident__part_parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; unsigned x_2; obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_12; obj* x_13; obj* x_15; obj* x_16; unsigned x_17; obj* x_18; obj* x_20; obj* x_21; obj* x_22; obj* x_24; obj* x_25; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_32; obj* x_33; obj* x_34; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; 
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
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_detail__ident__part_parser___lambda__1), 6, 2);
lean::closure_set(x_10, 0, x_4);
lean::closure_set(x_10, 1, x_7);
lean::inc(x_9);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_bind___at_lean_parser_with__trailing___spec__2___rarg), 5, 2);
lean::closure_set(x_12, 0, x_9);
lean::closure_set(x_12, 1, x_10);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_detail__ident__part_parser___lambda__2), 4, 0);
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
x_22 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_detail__ident__part_parser___lambda__1), 6, 2);
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
x_32 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_detail__ident__part_parser___spec__8), 5, 2);
lean::closure_set(x_32, 0, x_30);
lean::closure_set(x_32, 1, x_29);
x_33 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_detail__ident__part_parser___lambda__3), 4, 0);
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
x_39 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_choice__aux___main___at_lean_parser_detail__ident__part_parser___spec__16), 5, 2);
lean::closure_set(x_39, 0, x_37);
lean::closure_set(x_39, 1, x_38);
x_40 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_40, 0, x_39);
lean::cnstr_set(x_40, 1, x_25);
return x_40;
}
}
obj* l_lean_parser_detail__ident__part_parser___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_9; obj* x_11; 
x_6 = l_lean_parser_monad__parsec_str__core___at___private_4089500695__finish__comment__block__aux___main___spec__3(x_0, x_1, x_3, x_4, x_5);
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
obj* x_25; unsigned char x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; 
lean::dec(x_2);
x_25 = lean::cnstr_get(x_7, 0);
lean::inc(x_25);
x_27 = lean::cnstr_get_scalar<unsigned char>(x_7, sizeof(void*)*1);
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
obj* l_lean_parser_detail__ident__part_parser___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
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
obj* x_23; unsigned char x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
lean::dec(x_0);
x_23 = lean::cnstr_get(x_5, 0);
lean::inc(x_23);
x_25 = lean::cnstr_get_scalar<unsigned char>(x_5, sizeof(void*)*1);
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
obj* l_lean_parser_detail__ident__part_parser___lambda__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; unsigned char x_7; 
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
x_14 = l_lean_parser_monad__parsec_error___at___private_4089500695__finish__comment__block__aux___main___spec__1___rarg(x_9, x_10, x_8, x_8, x_1, x_2, x_3);
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
x_28 = l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser___spec__10___rarg(x_23, x_17);
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
obj* x_35; unsigned char x_37; obj* x_38; obj* x_39; obj* x_40; 
x_35 = lean::cnstr_get(x_22, 0);
lean::inc(x_35);
x_37 = lean::cnstr_get_scalar<unsigned char>(x_22, sizeof(void*)*1);
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
unsigned x_41; unsigned char x_42; 
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
x_53 = l_lean_parser_monad__parsec_error___at___private_4089500695__finish__comment__block__aux___main___spec__1___rarg(x_48, x_50, x_49, x_49, x_1, x_2, x_3);
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
x_67 = l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser___spec__12___rarg(x_62, x_56);
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
obj* x_74; unsigned char x_76; obj* x_77; obj* x_78; obj* x_79; 
x_74 = lean::cnstr_get(x_61, 0);
lean::inc(x_74);
x_76 = lean::cnstr_get_scalar<unsigned char>(x_61, sizeof(void*)*1);
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
x_82 = l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser___spec__14___rarg(x_81, x_3);
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
obj* x_103; unsigned char x_105; obj* x_106; obj* x_107; obj* x_108; obj* x_109; 
lean::dec(x_0);
x_103 = lean::cnstr_get(x_4, 0);
lean::inc(x_103);
x_105 = lean::cnstr_get_scalar<unsigned char>(x_4, sizeof(void*)*1);
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
obj* l___private_31565857__take__while__aux___main___at_lean_parser_detail__ident__part_parser___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; unsigned char x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
unsigned char x_6; 
x_6 = lean::string_iterator_has_next(x_2);
if (x_6 == 0)
{
obj* x_8; 
lean::dec(x_0);
x_8 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_8;
}
else
{
unsigned x_9; unsigned char x_10; 
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
x_19 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_19;
}
}
}
else
{
obj* x_21; 
lean::dec(x_0);
x_21 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_21;
}
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser___spec__2(unsigned x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
lean::dec(x_1);
x_5 = l_string_join___closed__1;
lean::inc(x_5);
x_7 = lean::string_push(x_5, x_0);
x_8 = lean::string_iterator_remaining(x_2);
x_9 = l___private_31565857__take__while__aux___main___at_lean_parser_detail__ident__part_parser___spec__3(x_8, x_7, x_2);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_3);
return x_10;
}
}
obj* l___private_31565857__take__while__aux___main___at_lean_parser_detail__ident__part_parser___spec__5(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; unsigned char x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
unsigned char x_6; 
x_6 = lean::string_iterator_has_next(x_2);
if (x_6 == 0)
{
obj* x_8; 
lean::dec(x_0);
x_8 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_8;
}
else
{
unsigned x_9; unsigned char x_10; 
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
x_19 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_19;
}
}
}
else
{
obj* x_21; 
lean::dec(x_0);
x_21 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_21;
}
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser___spec__4(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
unsigned x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
lean::dec(x_1);
x_5 = lean::string_iterator_curr(x_0);
lean::dec(x_0);
x_7 = l_string_join___closed__1;
lean::inc(x_7);
x_9 = lean::string_push(x_7, x_5);
x_10 = lean::string_iterator_remaining(x_2);
x_11 = l___private_31565857__take__while__aux___main___at_lean_parser_detail__ident__part_parser___spec__5(x_10, x_9, x_2);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_3);
return x_12;
}
}
obj* l___private_31565857__take__while__aux___main___at_lean_parser_detail__ident__part_parser___spec__7(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; unsigned char x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
unsigned char x_6; 
x_6 = lean::string_iterator_has_next(x_2);
if (x_6 == 0)
{
obj* x_8; 
lean::dec(x_0);
x_8 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_8;
}
else
{
unsigned x_9; unsigned char x_10; 
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
x_19 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_19;
}
}
}
else
{
obj* x_21; 
lean::dec(x_0);
x_21 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_21;
}
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser___spec__6(unsigned x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
lean::dec(x_1);
x_5 = l_string_join___closed__1;
lean::inc(x_5);
x_7 = lean::string_push(x_5, x_0);
x_8 = lean::string_iterator_remaining(x_2);
x_9 = l___private_31565857__take__while__aux___main___at_lean_parser_detail__ident__part_parser___spec__7(x_8, x_7, x_2);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_3);
return x_10;
}
}
obj* l_lean_parser_monad__parsec_take__while1___at_lean_parser_detail__ident__part_parser___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
unsigned char x_3; 
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
x_11 = l_lean_parser_monad__parsec_error___at___private_4089500695__finish__comment__block__aux___main___spec__1___rarg(x_5, x_6, x_4, x_4, x_0, x_1, x_2);
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
obj* x_20; obj* x_22; obj* x_24; unsigned x_27; obj* x_29; obj* x_30; obj* x_32; obj* x_35; obj* x_36; 
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
obj* x_38; unsigned char x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; 
lean::dec(x_0);
x_38 = lean::cnstr_get(x_19, 0);
lean::inc(x_38);
x_40 = lean::cnstr_get_scalar<unsigned char>(x_19, sizeof(void*)*1);
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
unsigned x_45; unsigned char x_46; 
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
x_69 = l_lean_parser_monad__parsec_error___at___private_4089500695__finish__comment__block__aux___main___spec__1___rarg(x_63, x_65, x_64, x_64, x_0, x_1, x_2);
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
obj* x_78; obj* x_80; obj* x_82; unsigned x_85; obj* x_87; obj* x_88; obj* x_90; obj* x_93; obj* x_94; 
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
obj* x_96; unsigned char x_98; obj* x_99; obj* x_100; obj* x_101; obj* x_102; 
lean::dec(x_0);
x_96 = lean::cnstr_get(x_77, 0);
lean::inc(x_96);
x_98 = lean::cnstr_get_scalar<unsigned char>(x_77, sizeof(void*)*1);
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
obj* l_list_mfoldl___main___at_lean_parser_detail__ident__part_parser___spec__9(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
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
obj* x_28; unsigned char x_30; obj* x_31; 
x_28 = lean::cnstr_get(x_23, 0);
lean::inc(x_28);
x_30 = lean::cnstr_get_scalar<unsigned char>(x_23, sizeof(void*)*1);
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
unsigned char x_32; obj* x_33; obj* x_34; 
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
unsigned char x_54; obj* x_55; obj* x_56; 
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
x_78 = l_list_mfoldl___main___at_lean_parser_detail__ident__part_parser___spec__9(x_0, x_71, x_15, x_3, x_73, x_19);
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
obj* x_89; unsigned char x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_95; 
lean::dec(x_15);
lean::dec(x_3);
lean::dec(x_0);
x_89 = lean::cnstr_get(x_70, 0);
lean::inc(x_89);
x_91 = lean::cnstr_get_scalar<unsigned char>(x_70, sizeof(void*)*1);
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
obj* x_101; unsigned char x_103; obj* x_104; obj* x_105; obj* x_106; obj* x_107; 
lean::dec(x_15);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_17);
x_101 = lean::cnstr_get(x_18, 0);
lean::inc(x_101);
x_103 = lean::cnstr_get_scalar<unsigned char>(x_18, sizeof(void*)*1);
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
obj* l_lean_parser_combinators_node___at_lean_parser_detail__ident__part_parser___spec__8(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_7; obj* x_8; obj* x_10; obj* x_12; 
x_5 = lean::box(0);
lean::inc(x_0);
x_7 = l_list_mfoldl___main___at_lean_parser_detail__ident__part_parser___spec__9(x_0, x_5, x_1, x_2, x_3, x_4);
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
obj* x_28; unsigned char x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; 
lean::dec(x_0);
x_28 = lean::cnstr_get(x_8, 0);
lean::inc(x_28);
x_30 = lean::cnstr_get_scalar<unsigned char>(x_8, sizeof(void*)*1);
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
obj* l___private_31565857__take__while__aux___main___at_lean_parser_detail__ident__part_parser___spec__11(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; unsigned char x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
unsigned char x_6; 
x_6 = lean::string_iterator_has_next(x_2);
if (x_6 == 0)
{
obj* x_8; 
lean::dec(x_0);
x_8 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_8;
}
else
{
unsigned x_9; unsigned char x_10; 
x_9 = lean::string_iterator_curr(x_2);
x_10 = l_lean_is__id__rest(x_9);
if (x_10 == 0)
{
obj* x_12; 
lean::dec(x_0);
x_12 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
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
x_21 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
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
x_5 = l___private_31565857__take__while__aux___main___at_lean_parser_detail__ident__part_parser___spec__11(x_2, x_3, x_0);
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
obj* l___private_31565857__take__while__aux___main___at_lean_parser_detail__ident__part_parser___spec__13(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; unsigned char x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
unsigned char x_6; 
x_6 = lean::string_iterator_has_next(x_2);
if (x_6 == 0)
{
obj* x_8; 
lean::dec(x_0);
x_8 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_8;
}
else
{
unsigned x_9; unsigned char x_10; 
x_9 = lean::string_iterator_curr(x_2);
x_10 = l_lean_is__id__rest(x_9);
if (x_10 == 0)
{
obj* x_12; 
lean::dec(x_0);
x_12 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
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
x_21 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
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
x_5 = l___private_31565857__take__while__aux___main___at_lean_parser_detail__ident__part_parser___spec__13(x_2, x_3, x_0);
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
obj* l___private_31565857__take__while__aux___main___at_lean_parser_detail__ident__part_parser___spec__15(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; unsigned char x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
unsigned char x_6; 
x_6 = lean::string_iterator_has_next(x_2);
if (x_6 == 0)
{
obj* x_8; 
lean::dec(x_0);
x_8 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_8;
}
else
{
unsigned x_9; unsigned char x_10; 
x_9 = lean::string_iterator_curr(x_2);
x_10 = l_lean_is__id__rest(x_9);
if (x_10 == 0)
{
obj* x_12; 
lean::dec(x_0);
x_12 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
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
x_21 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_21;
}
}
}
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser___spec__14___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_5; obj* x_6; 
x_2 = lean::string_iterator_remaining(x_0);
x_3 = l_string_join___closed__1;
lean::inc(x_3);
x_5 = l___private_31565857__take__while__aux___main___at_lean_parser_detail__ident__part_parser___spec__15(x_2, x_3, x_0);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_1);
return x_6;
}
}
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser___spec__14(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser___spec__14___rarg), 2, 0);
return x_2;
}
}
obj* l_lean_parser_combinators_choice__aux___main___at_lean_parser_detail__ident__part_parser___spec__16(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
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
x_13 = l_lean_parser_monad__parsec_error___at___private_4089500695__finish__comment__block__aux___main___spec__1___rarg(x_8, x_9, x_7, x_7, x_2, x_3, x_4);
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
x_39 = lean::name_mk_numeral(x_37, x_1);
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
obj* x_51; unsigned char x_53; 
x_51 = lean::cnstr_get(x_45, 0);
lean::inc(x_51);
x_53 = lean::cnstr_get_scalar<unsigned char>(x_45, sizeof(void*)*1);
if (x_53 == 0)
{
obj* x_55; obj* x_56; obj* x_58; obj* x_61; obj* x_62; 
lean::dec(x_45);
x_55 = l_lean_parser_combinators_choice__aux___main___at_lean_parser_detail__ident__part_parser___spec__16(x_16, x_28, x_2, x_3, x_24);
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
obj* x_71; unsigned char x_73; obj* x_74; 
lean::dec(x_18);
lean::dec(x_1);
x_71 = lean::cnstr_get(x_22, 0);
lean::inc(x_71);
x_73 = lean::cnstr_get_scalar<unsigned char>(x_22, sizeof(void*)*1);
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
x_76 = l_lean_parser_combinators_choice__aux___main___at_lean_parser_detail__ident__part_parser___spec__16(x_16, x_28, x_2, x_3, x_24);
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
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
unsigned x_4; obj* x_5; 
x_4 = lean::unbox_uint32(x_0);
x_5 = l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser___spec__2(x_4, x_1, x_2, x_3);
return x_5;
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser___spec__6___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
unsigned x_4; obj* x_5; 
x_4 = lean::unbox_uint32(x_0);
x_5 = l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser___spec__6(x_4, x_1, x_2, x_3);
return x_5;
}
}
obj* _init_l_lean_parser_detail__ident__part_parser_lean_parser_has__view() {
_start:
{
obj* x_0; obj* x_1; unsigned x_2; obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_12; obj* x_13; obj* x_15; obj* x_16; unsigned x_17; obj* x_18; obj* x_20; obj* x_21; obj* x_22; obj* x_24; obj* x_25; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_32; obj* x_33; obj* x_34; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_53; 
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
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_detail__ident__part_parser___lambda__1), 6, 2);
lean::closure_set(x_10, 0, x_4);
lean::closure_set(x_10, 1, x_7);
lean::inc(x_9);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_bind___at_lean_parser_with__trailing___spec__2___rarg), 5, 2);
lean::closure_set(x_12, 0, x_9);
lean::closure_set(x_12, 1, x_10);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_detail__ident__part_parser_lean_parser_has__view___lambda__1), 4, 0);
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
x_22 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_detail__ident__part_parser___lambda__1), 6, 2);
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
x_32 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_detail__ident__part_parser___spec__8), 5, 2);
lean::closure_set(x_32, 0, x_30);
lean::closure_set(x_32, 1, x_29);
x_33 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_detail__ident__part_parser_lean_parser_has__view___lambda__2), 4, 0);
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
x_39 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_choice__aux___main___at_lean_parser_detail__ident__part_parser___spec__16), 5, 2);
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
obj* l_lean_parser_detail__ident__part_parser_lean_parser_has__view___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
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
obj* x_23; unsigned char x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
lean::dec(x_0);
x_23 = lean::cnstr_get(x_5, 0);
lean::inc(x_23);
x_25 = lean::cnstr_get_scalar<unsigned char>(x_5, sizeof(void*)*1);
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
obj* l_lean_parser_detail__ident__part_parser_lean_parser_has__view___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; unsigned char x_7; 
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
x_14 = l_lean_parser_monad__parsec_error___at___private_4089500695__finish__comment__block__aux___main___spec__1___rarg(x_9, x_10, x_8, x_8, x_1, x_2, x_3);
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
obj* x_35; unsigned char x_37; obj* x_38; obj* x_39; obj* x_40; 
x_35 = lean::cnstr_get(x_22, 0);
lean::inc(x_35);
x_37 = lean::cnstr_get_scalar<unsigned char>(x_22, sizeof(void*)*1);
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
unsigned x_41; unsigned char x_42; 
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
x_53 = l_lean_parser_monad__parsec_error___at___private_4089500695__finish__comment__block__aux___main___spec__1___rarg(x_48, x_50, x_49, x_49, x_1, x_2, x_3);
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
obj* x_74; unsigned char x_76; obj* x_77; obj* x_78; obj* x_79; 
x_74 = lean::cnstr_get(x_61, 0);
lean::inc(x_74);
x_76 = lean::cnstr_get_scalar<unsigned char>(x_61, sizeof(void*)*1);
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
obj* x_103; unsigned char x_105; obj* x_106; obj* x_107; obj* x_108; obj* x_109; 
lean::dec(x_0);
x_103 = lean::cnstr_get(x_4, 0);
lean::inc(x_103);
x_105 = lean::cnstr_get_scalar<unsigned char>(x_4, sizeof(void*)*1);
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
obj* l___private_31565857__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; unsigned char x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
unsigned char x_6; 
x_6 = lean::string_iterator_has_next(x_2);
if (x_6 == 0)
{
obj* x_8; 
lean::dec(x_0);
x_8 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_8;
}
else
{
unsigned x_9; unsigned char x_10; 
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
x_19 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_19;
}
}
}
else
{
obj* x_21; 
lean::dec(x_0);
x_21 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_21;
}
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__2(unsigned x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
lean::dec(x_1);
x_5 = l_string_join___closed__1;
lean::inc(x_5);
x_7 = lean::string_push(x_5, x_0);
x_8 = lean::string_iterator_remaining(x_2);
x_9 = l___private_31565857__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__3(x_8, x_7, x_2);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_3);
return x_10;
}
}
obj* l___private_31565857__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__5(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; unsigned char x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
unsigned char x_6; 
x_6 = lean::string_iterator_has_next(x_2);
if (x_6 == 0)
{
obj* x_8; 
lean::dec(x_0);
x_8 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_8;
}
else
{
unsigned x_9; unsigned char x_10; 
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
x_19 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_19;
}
}
}
else
{
obj* x_21; 
lean::dec(x_0);
x_21 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_21;
}
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__4(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
unsigned x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
lean::dec(x_1);
x_5 = lean::string_iterator_curr(x_0);
lean::dec(x_0);
x_7 = l_string_join___closed__1;
lean::inc(x_7);
x_9 = lean::string_push(x_7, x_5);
x_10 = lean::string_iterator_remaining(x_2);
x_11 = l___private_31565857__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__5(x_10, x_9, x_2);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_3);
return x_12;
}
}
obj* l___private_31565857__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__7(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; unsigned char x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
unsigned char x_6; 
x_6 = lean::string_iterator_has_next(x_2);
if (x_6 == 0)
{
obj* x_8; 
lean::dec(x_0);
x_8 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_8;
}
else
{
unsigned x_9; unsigned char x_10; 
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
x_19 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_19;
}
}
}
else
{
obj* x_21; 
lean::dec(x_0);
x_21 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_21;
}
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__6(unsigned x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
lean::dec(x_1);
x_5 = l_string_join___closed__1;
lean::inc(x_5);
x_7 = lean::string_push(x_5, x_0);
x_8 = lean::string_iterator_remaining(x_2);
x_9 = l___private_31565857__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__7(x_8, x_7, x_2);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_3);
return x_10;
}
}
obj* l_lean_parser_monad__parsec_take__while1___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
unsigned char x_3; 
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
x_11 = l_lean_parser_monad__parsec_error___at___private_4089500695__finish__comment__block__aux___main___spec__1___rarg(x_5, x_6, x_4, x_4, x_0, x_1, x_2);
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
obj* x_20; obj* x_22; obj* x_24; unsigned x_27; obj* x_29; obj* x_30; obj* x_32; obj* x_35; obj* x_36; 
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
obj* x_38; unsigned char x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; 
lean::dec(x_0);
x_38 = lean::cnstr_get(x_19, 0);
lean::inc(x_38);
x_40 = lean::cnstr_get_scalar<unsigned char>(x_19, sizeof(void*)*1);
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
unsigned x_45; unsigned char x_46; 
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
x_69 = l_lean_parser_monad__parsec_error___at___private_4089500695__finish__comment__block__aux___main___spec__1___rarg(x_63, x_65, x_64, x_64, x_0, x_1, x_2);
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
obj* x_78; obj* x_80; obj* x_82; unsigned x_85; obj* x_87; obj* x_88; obj* x_90; obj* x_93; obj* x_94; 
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
obj* x_96; unsigned char x_98; obj* x_99; obj* x_100; obj* x_101; obj* x_102; 
lean::dec(x_0);
x_96 = lean::cnstr_get(x_77, 0);
lean::inc(x_96);
x_98 = lean::cnstr_get_scalar<unsigned char>(x_77, sizeof(void*)*1);
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
obj* l___private_31565857__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__9(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; unsigned char x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
unsigned char x_6; 
x_6 = lean::string_iterator_has_next(x_2);
if (x_6 == 0)
{
obj* x_8; 
lean::dec(x_0);
x_8 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_8;
}
else
{
unsigned x_9; unsigned char x_10; 
x_9 = lean::string_iterator_curr(x_2);
x_10 = l_lean_is__id__rest(x_9);
if (x_10 == 0)
{
obj* x_12; 
lean::dec(x_0);
x_12 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
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
x_21 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
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
x_5 = l___private_31565857__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__9(x_2, x_3, x_0);
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
obj* l___private_31565857__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__11(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; unsigned char x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
unsigned char x_6; 
x_6 = lean::string_iterator_has_next(x_2);
if (x_6 == 0)
{
obj* x_8; 
lean::dec(x_0);
x_8 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_8;
}
else
{
unsigned x_9; unsigned char x_10; 
x_9 = lean::string_iterator_curr(x_2);
x_10 = l_lean_is__id__rest(x_9);
if (x_10 == 0)
{
obj* x_12; 
lean::dec(x_0);
x_12 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
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
x_21 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
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
x_5 = l___private_31565857__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__11(x_2, x_3, x_0);
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
obj* l___private_31565857__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__13(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; unsigned char x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
unsigned char x_6; 
x_6 = lean::string_iterator_has_next(x_2);
if (x_6 == 0)
{
obj* x_8; 
lean::dec(x_0);
x_8 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_8;
}
else
{
unsigned x_9; unsigned char x_10; 
x_9 = lean::string_iterator_curr(x_2);
x_10 = l_lean_is__id__rest(x_9);
if (x_10 == 0)
{
obj* x_12; 
lean::dec(x_0);
x_12 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
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
x_21 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
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
x_5 = l___private_31565857__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__13(x_2, x_3, x_0);
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
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
unsigned x_4; obj* x_5; 
x_4 = lean::unbox_uint32(x_0);
x_5 = l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__2(x_4, x_1, x_2, x_3);
return x_5;
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__6___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
unsigned x_4; obj* x_5; 
x_4 = lean::unbox_uint32(x_0);
x_5 = l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__view___spec__6(x_4, x_1, x_2, x_3);
return x_5;
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
obj* l___private_31565857__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; unsigned char x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
unsigned char x_6; 
x_6 = lean::string_iterator_has_next(x_2);
if (x_6 == 0)
{
obj* x_8; 
lean::dec(x_0);
x_8 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_8;
}
else
{
unsigned x_9; unsigned char x_10; 
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
x_19 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_19;
}
}
}
else
{
obj* x_21; 
lean::dec(x_0);
x_21 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_21;
}
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__2(unsigned x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
lean::dec(x_1);
x_5 = l_string_join___closed__1;
lean::inc(x_5);
x_7 = lean::string_push(x_5, x_0);
x_8 = lean::string_iterator_remaining(x_2);
x_9 = l___private_31565857__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__3(x_8, x_7, x_2);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_3);
return x_10;
}
}
obj* l___private_31565857__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__5(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; unsigned char x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
unsigned char x_6; 
x_6 = lean::string_iterator_has_next(x_2);
if (x_6 == 0)
{
obj* x_8; 
lean::dec(x_0);
x_8 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_8;
}
else
{
unsigned x_9; unsigned char x_10; 
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
x_19 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_19;
}
}
}
else
{
obj* x_21; 
lean::dec(x_0);
x_21 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_21;
}
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__4(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
unsigned x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
lean::dec(x_1);
x_5 = lean::string_iterator_curr(x_0);
lean::dec(x_0);
x_7 = l_string_join___closed__1;
lean::inc(x_7);
x_9 = lean::string_push(x_7, x_5);
x_10 = lean::string_iterator_remaining(x_2);
x_11 = l___private_31565857__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__5(x_10, x_9, x_2);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_3);
return x_12;
}
}
obj* l___private_31565857__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__7(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; unsigned char x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
unsigned char x_6; 
x_6 = lean::string_iterator_has_next(x_2);
if (x_6 == 0)
{
obj* x_8; 
lean::dec(x_0);
x_8 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_8;
}
else
{
unsigned x_9; unsigned char x_10; 
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
x_19 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_19;
}
}
}
else
{
obj* x_21; 
lean::dec(x_0);
x_21 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_21;
}
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__6(unsigned x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
lean::dec(x_1);
x_5 = l_string_join___closed__1;
lean::inc(x_5);
x_7 = lean::string_push(x_5, x_0);
x_8 = lean::string_iterator_remaining(x_2);
x_9 = l___private_31565857__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__7(x_8, x_7, x_2);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_3);
return x_10;
}
}
obj* l_lean_parser_monad__parsec_take__while1___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
unsigned char x_3; 
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
x_11 = l_lean_parser_monad__parsec_error___at___private_4089500695__finish__comment__block__aux___main___spec__1___rarg(x_5, x_6, x_4, x_4, x_0, x_1, x_2);
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
obj* x_20; obj* x_22; obj* x_24; unsigned x_27; obj* x_29; obj* x_30; obj* x_32; obj* x_35; obj* x_36; 
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
obj* x_38; unsigned char x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; 
lean::dec(x_0);
x_38 = lean::cnstr_get(x_19, 0);
lean::inc(x_38);
x_40 = lean::cnstr_get_scalar<unsigned char>(x_19, sizeof(void*)*1);
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
unsigned x_45; unsigned char x_46; 
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
x_69 = l_lean_parser_monad__parsec_error___at___private_4089500695__finish__comment__block__aux___main___spec__1___rarg(x_63, x_65, x_64, x_64, x_0, x_1, x_2);
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
obj* x_78; obj* x_80; obj* x_82; unsigned x_85; obj* x_87; obj* x_88; obj* x_90; obj* x_93; obj* x_94; 
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
obj* x_96; unsigned char x_98; obj* x_99; obj* x_100; obj* x_101; obj* x_102; 
lean::dec(x_0);
x_96 = lean::cnstr_get(x_77, 0);
lean::inc(x_96);
x_98 = lean::cnstr_get_scalar<unsigned char>(x_77, sizeof(void*)*1);
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
obj* l___private_31565857__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__10(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; unsigned char x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
unsigned char x_6; 
x_6 = lean::string_iterator_has_next(x_2);
if (x_6 == 0)
{
obj* x_8; 
lean::dec(x_0);
x_8 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_8;
}
else
{
unsigned x_9; unsigned char x_10; 
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
x_19 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_19;
}
}
}
else
{
obj* x_21; 
lean::dec(x_0);
x_21 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_21;
}
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__9(unsigned x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
lean::dec(x_1);
x_5 = l_string_join___closed__1;
lean::inc(x_5);
x_7 = lean::string_push(x_5, x_0);
x_8 = lean::string_iterator_remaining(x_2);
x_9 = l___private_31565857__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__10(x_8, x_7, x_2);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_3);
return x_10;
}
}
obj* l___private_31565857__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__12(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; unsigned char x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
unsigned char x_6; 
x_6 = lean::string_iterator_has_next(x_2);
if (x_6 == 0)
{
obj* x_8; 
lean::dec(x_0);
x_8 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_8;
}
else
{
unsigned x_9; unsigned char x_10; 
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
x_19 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_19;
}
}
}
else
{
obj* x_21; 
lean::dec(x_0);
x_21 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_21;
}
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__11(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
unsigned x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
lean::dec(x_1);
x_5 = lean::string_iterator_curr(x_0);
lean::dec(x_0);
x_7 = l_string_join___closed__1;
lean::inc(x_7);
x_9 = lean::string_push(x_7, x_5);
x_10 = lean::string_iterator_remaining(x_2);
x_11 = l___private_31565857__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__12(x_10, x_9, x_2);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_3);
return x_12;
}
}
obj* l___private_31565857__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__14(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; unsigned char x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
unsigned char x_6; 
x_6 = lean::string_iterator_has_next(x_2);
if (x_6 == 0)
{
obj* x_8; 
lean::dec(x_0);
x_8 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_8;
}
else
{
unsigned x_9; unsigned char x_10; 
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
x_19 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_19;
}
}
}
else
{
obj* x_21; 
lean::dec(x_0);
x_21 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_21;
}
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__13(unsigned x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
lean::dec(x_1);
x_5 = l_string_join___closed__1;
lean::inc(x_5);
x_7 = lean::string_push(x_5, x_0);
x_8 = lean::string_iterator_remaining(x_2);
x_9 = l___private_31565857__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__14(x_8, x_7, x_2);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_3);
return x_10;
}
}
obj* l_lean_parser_monad__parsec_take__while1___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__8(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
unsigned char x_3; 
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
x_11 = l_lean_parser_monad__parsec_error___at___private_4089500695__finish__comment__block__aux___main___spec__1___rarg(x_5, x_6, x_4, x_4, x_0, x_1, x_2);
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
obj* x_20; obj* x_22; obj* x_24; unsigned x_27; obj* x_29; obj* x_30; obj* x_32; obj* x_35; obj* x_36; 
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
obj* x_38; unsigned char x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; 
lean::dec(x_0);
x_38 = lean::cnstr_get(x_19, 0);
lean::inc(x_38);
x_40 = lean::cnstr_get_scalar<unsigned char>(x_19, sizeof(void*)*1);
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
unsigned x_45; unsigned char x_46; 
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
x_69 = l_lean_parser_monad__parsec_error___at___private_4089500695__finish__comment__block__aux___main___spec__1___rarg(x_63, x_65, x_64, x_64, x_0, x_1, x_2);
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
obj* x_78; obj* x_80; obj* x_82; unsigned x_85; obj* x_87; obj* x_88; obj* x_90; obj* x_93; obj* x_94; 
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
obj* x_96; unsigned char x_98; obj* x_99; obj* x_100; obj* x_101; obj* x_102; 
lean::dec(x_0);
x_96 = lean::cnstr_get(x_77, 0);
lean::inc(x_96);
x_98 = lean::cnstr_get_scalar<unsigned char>(x_77, sizeof(void*)*1);
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
obj* l___private_31565857__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__16(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; unsigned char x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
unsigned char x_6; 
x_6 = lean::string_iterator_has_next(x_2);
if (x_6 == 0)
{
obj* x_8; 
lean::dec(x_0);
x_8 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_8;
}
else
{
unsigned x_9; unsigned char x_10; 
x_9 = lean::string_iterator_curr(x_2);
x_10 = l_lean_is__id__rest(x_9);
if (x_10 == 0)
{
obj* x_12; 
lean::dec(x_0);
x_12 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
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
x_21 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_21;
}
}
}
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__15___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_5; obj* x_6; 
x_2 = lean::string_iterator_remaining(x_0);
x_3 = l_string_join___closed__1;
lean::inc(x_3);
x_5 = l___private_31565857__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__16(x_2, x_3, x_0);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_1);
return x_6;
}
}
obj* l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__15(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_take__while___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__15___rarg), 2, 0);
return x_2;
}
}
obj* l___private_31565857__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__18(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; unsigned char x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
unsigned char x_6; 
x_6 = lean::string_iterator_has_next(x_2);
if (x_6 == 0)
{
obj* x_8; 
lean::dec(x_0);
x_8 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_8;
}
else
{
unsigned x_9; unsigned char x_10; 
x_9 = lean::string_iterator_curr(x_2);
x_10 = l_lean_is__id__rest(x_9);
if (x_10 == 0)
{
obj* x_12; 
lean::dec(x_0);
x_12 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
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
x_21 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
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
x_5 = l___private_31565857__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__18(x_2, x_3, x_0);
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
obj* l___private_31565857__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__20(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; unsigned char x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
unsigned char x_6; 
x_6 = lean::string_iterator_has_next(x_2);
if (x_6 == 0)
{
obj* x_8; 
lean::dec(x_0);
x_8 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_8;
}
else
{
unsigned x_9; unsigned char x_10; 
x_9 = lean::string_iterator_curr(x_2);
x_10 = l_lean_is__id__rest(x_9);
if (x_10 == 0)
{
obj* x_12; 
lean::dec(x_0);
x_12 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
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
x_21 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
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
x_5 = l___private_31565857__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__20(x_2, x_3, x_0);
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
obj* l___private_31565857__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__22(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; unsigned char x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
unsigned char x_6; 
x_6 = lean::string_iterator_has_next(x_2);
if (x_6 == 0)
{
obj* x_8; 
lean::dec(x_0);
x_8 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_8;
}
else
{
unsigned x_9; unsigned char x_10; 
x_9 = lean::string_iterator_curr(x_2);
x_10 = l_lean_is__id__rest(x_9);
if (x_10 == 0)
{
obj* x_12; 
lean::dec(x_0);
x_12 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
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
x_21 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
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
x_5 = l___private_31565857__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__22(x_2, x_3, x_0);
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
obj* l___private_31565857__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__24(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; unsigned char x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
unsigned char x_6; 
x_6 = lean::string_iterator_has_next(x_2);
if (x_6 == 0)
{
obj* x_8; 
lean::dec(x_0);
x_8 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_8;
}
else
{
unsigned x_9; unsigned char x_10; 
x_9 = lean::string_iterator_curr(x_2);
x_10 = l_lean_is__id__rest(x_9);
if (x_10 == 0)
{
obj* x_12; 
lean::dec(x_0);
x_12 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
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
x_21 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
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
x_5 = l___private_31565857__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__24(x_2, x_3, x_0);
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
obj* l___private_31565857__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__26(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; unsigned char x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
unsigned char x_6; 
x_6 = lean::string_iterator_has_next(x_2);
if (x_6 == 0)
{
obj* x_8; 
lean::dec(x_0);
x_8 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_8;
}
else
{
unsigned x_9; unsigned char x_10; 
x_9 = lean::string_iterator_curr(x_2);
x_10 = l_lean_is__id__rest(x_9);
if (x_10 == 0)
{
obj* x_12; 
lean::dec(x_0);
x_12 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
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
x_21 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
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
x_5 = l___private_31565857__take__while__aux___main___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__26(x_2, x_3, x_0);
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
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
unsigned x_4; obj* x_5; 
x_4 = lean::unbox_uint32(x_0);
x_5 = l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__2(x_4, x_1, x_2, x_3);
return x_5;
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__6___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
unsigned x_4; obj* x_5; 
x_4 = lean::unbox_uint32(x_0);
x_5 = l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__6(x_4, x_1, x_2, x_3);
return x_5;
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__9___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
unsigned x_4; obj* x_5; 
x_4 = lean::unbox_uint32(x_0);
x_5 = l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__9(x_4, x_1, x_2, x_3);
return x_5;
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__13___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
unsigned x_4; obj* x_5; 
x_4 = lean::unbox_uint32(x_0);
x_5 = l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_detail__ident__part_parser_lean_parser_has__tokens___spec__13(x_4, x_1, x_2, x_3);
return x_5;
}
}
obj* _init_l_lean_parser_detail__ident__suffix() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean::name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean::name_mk_string(x_2, x_3);
x_5 = lean::mk_string("detail_ident_suffix");
x_6 = lean::name_mk_string(x_4, x_5);
return x_6;
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
obj* _init_l_lean_parser_detail__ident__suffix_has__view() {
_start:
{
obj* x_0; 
x_0 = l_lean_parser_detail__ident__suffix_has__view_x_27;
lean::inc(x_0);
return x_0;
}
}
obj* l_lean_parser_detail__ident__suffix_parser(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; unsigned char x_6; unsigned x_8; 
x_4 = lean::mk_nat_obj(46u);
x_5 = lean::mk_nat_obj(55296u);
x_6 = lean::nat_dec_lt(x_4, x_5);
lean::dec(x_5);
if (x_6 == 0)
{
obj* x_10; unsigned char x_11; 
x_10 = lean::mk_nat_obj(57343u);
x_11 = lean::nat_dec_lt(x_10, x_4);
lean::dec(x_10);
if (x_11 == 0)
{
obj* x_14; unsigned x_15; 
lean::dec(x_4);
x_14 = lean::mk_nat_obj(0u);
x_15 = lean::unbox_uint32(x_14);
lean::dec(x_14);
x_8 = x_15;
goto lbl_9;
}
else
{
obj* x_17; unsigned char x_18; 
x_17 = lean::mk_nat_obj(1114112u);
x_18 = lean::nat_dec_lt(x_4, x_17);
lean::dec(x_17);
if (x_18 == 0)
{
obj* x_21; unsigned x_22; 
lean::dec(x_4);
x_21 = lean::mk_nat_obj(0u);
x_22 = lean::unbox_uint32(x_21);
lean::dec(x_21);
x_8 = x_22;
goto lbl_9;
}
else
{
unsigned x_24; 
x_24 = lean::unbox_uint32(x_4);
lean::dec(x_4);
x_8 = x_24;
goto lbl_9;
}
}
}
else
{
unsigned x_26; 
x_26 = lean::unbox_uint32(x_4);
lean::dec(x_4);
x_8 = x_26;
goto lbl_9;
}
lbl_9:
{
obj* x_30; obj* x_31; obj* x_33; obj* x_35; obj* x_36; 
lean::inc(x_1);
lean::inc(x_0);
x_30 = l_lean_parser_parsec__t_lookahead___at_lean_parser_detail__ident__suffix_parser___spec__4(x_0, x_1, x_2, x_8, x_3);
x_31 = lean::cnstr_get(x_30, 0);
lean::inc(x_31);
x_33 = lean::cnstr_get(x_30, 1);
lean::inc(x_33);
if (lean::is_shared(x_30)) {
 lean::dec(x_30);
 x_35 = lean::box(0);
} else {
 lean::cnstr_release(x_30, 0);
 lean::cnstr_release(x_30, 1);
 x_35 = x_30;
}
x_36 = l_lean_parser_parsec__t_try__mk__res___rarg(x_31);
if (lean::obj_tag(x_36) == 0)
{
obj* x_37; obj* x_39; obj* x_42; obj* x_43; obj* x_46; obj* x_47; obj* x_49; obj* x_52; obj* x_53; 
x_37 = lean::cnstr_get(x_36, 1);
lean::inc(x_37);
x_39 = lean::cnstr_get(x_36, 2);
lean::inc(x_39);
lean::dec(x_36);
x_42 = l_lean_parser_detail__ident__suffix;
x_43 = l_lean_parser_detail__ident__suffix_parser___closed__1;
lean::inc(x_43);
lean::inc(x_42);
x_46 = l_lean_parser_combinators_node___at_lean_parser_detail__ident__suffix_parser___spec__9(x_42, x_43, x_0, x_1, x_37, x_33);
x_47 = lean::cnstr_get(x_46, 0);
lean::inc(x_47);
x_49 = lean::cnstr_get(x_46, 1);
lean::inc(x_49);
lean::dec(x_46);
x_52 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_39, x_47);
if (lean::is_scalar(x_35)) {
 x_53 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_53 = x_35;
}
lean::cnstr_set(x_53, 0, x_52);
lean::cnstr_set(x_53, 1, x_49);
return x_53;
}
else
{
obj* x_56; unsigned char x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; 
lean::dec(x_1);
lean::dec(x_0);
x_56 = lean::cnstr_get(x_36, 0);
lean::inc(x_56);
x_58 = lean::cnstr_get_scalar<unsigned char>(x_36, sizeof(void*)*1);
if (lean::is_shared(x_36)) {
 lean::dec(x_36);
 x_59 = lean::box(0);
} else {
 lean::cnstr_release(x_36, 0);
 x_59 = x_36;
}
if (lean::is_scalar(x_59)) {
 x_60 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_60 = x_59;
}
lean::cnstr_set(x_60, 0, x_56);
lean::cnstr_set_scalar(x_60, sizeof(void*)*1, x_58);
x_61 = x_60;
if (lean::is_scalar(x_35)) {
 x_62 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_62 = x_35;
}
lean::cnstr_set(x_62, 0, x_61);
lean::cnstr_set(x_62, 1, x_33);
return x_62;
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
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_lift___at_lean_parser_detail__ident__suffix_parser___spec__5___rarg), 5, 1);
lean::closure_set(x_5, 0, x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_detail__ident__suffix_parser___lambda__1), 6, 1);
lean::closure_set(x_6, 0, x_2);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_bind___at_lean_parser_detail__ident__suffix_parser___spec__7___rarg), 6, 2);
lean::closure_set(x_7, 0, x_5);
lean::closure_set(x_7, 1, x_6);
x_8 = lean::box(0);
lean::inc(x_8);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_rec__t_recurse___at_lean_parser_detail__ident__suffix_parser___spec__8), 5, 1);
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
obj* l_lean_parser_detail__ident__suffix_parser___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_8; obj* x_9; obj* x_11; obj* x_13; 
x_6 = l_lean_name_to__string___closed__1;
lean::inc(x_6);
x_8 = l_lean_parser_monad__parsec_str__core___at_lean_parser_detail__ident__suffix_parser___spec__6(x_6, x_0, x_2, x_3, x_4, x_5);
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
obj* x_27; unsigned char x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; 
lean::dec(x_1);
x_27 = lean::cnstr_get(x_9, 0);
lean::inc(x_27);
x_29 = lean::cnstr_get_scalar<unsigned char>(x_9, sizeof(void*)*1);
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
obj* l_lean_parser_monad__parsec_error___at_lean_parser_detail__ident__suffix_parser___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_10; obj* x_11; unsigned char x_12; obj* x_13; obj* x_14; obj* x_15; 
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
obj* l_lean_parser_monad__parsec_error___at_lean_parser_detail__ident__suffix_parser___spec__2(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___at_lean_parser_detail__ident__suffix_parser___spec__2___rarg), 8, 0);
return x_2;
}
}
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_detail__ident__suffix_parser___spec__1(unsigned x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
unsigned char x_5; 
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
x_12 = l_lean_parser_monad__parsec_error___at_lean_parser_detail__ident__suffix_parser___spec__2___rarg(x_7, x_8, x_6, x_6, x_1, x_2, x_3, x_4);
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
unsigned x_22; obj* x_23; obj* x_24; unsigned char x_25; 
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
x_38 = l_lean_parser_monad__parsec_error___at_lean_parser_detail__ident__suffix_parser___spec__2___rarg(x_33, x_35, x_34, x_34, x_1, x_2, x_3, x_4);
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
obj* l_lean_parser_monad__parsec_error___at_lean_parser_detail__ident__suffix_parser___spec__3___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_10; obj* x_11; unsigned char x_12; obj* x_13; obj* x_14; obj* x_15; 
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
obj* l_lean_parser_monad__parsec_error___at_lean_parser_detail__ident__suffix_parser___spec__3(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___at_lean_parser_detail__ident__suffix_parser___spec__3___rarg), 8, 0);
return x_2;
}
}
obj* l_lean_parser_parsec__t_lookahead___at_lean_parser_detail__ident__suffix_parser___spec__4(obj* x_0, obj* x_1, obj* x_2, unsigned x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_11; obj* x_12; obj* x_14; 
lean::inc(x_2);
lean::inc(x_1);
lean::inc(x_0);
x_11 = l_lean_parser_monad__parsec_ch___at_lean_parser_detail__ident__suffix_parser___spec__1(x_3, x_0, x_1, x_2, x_4);
x_12 = lean::cnstr_get(x_11, 0);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_11, 1);
lean::inc(x_14);
lean::dec(x_11);
if (lean::obj_tag(x_12) == 0)
{
obj* x_17; obj* x_19; obj* x_21; obj* x_22; unsigned x_23; obj* x_27; obj* x_28; obj* x_30; 
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
lean::inc(x_1);
lean::inc(x_0);
x_27 = l_lean_parser_monad__parsec_ch___at_lean_parser_detail__ident__suffix_parser___spec__1(x_23, x_0, x_1, x_17, x_14);
x_28 = lean::cnstr_get(x_27, 0);
lean::inc(x_28);
x_30 = lean::cnstr_get(x_27, 1);
lean::inc(x_30);
lean::dec(x_27);
if (lean::obj_tag(x_28) == 0)
{
obj* x_37; 
lean::dec(x_17);
lean::dec(x_21);
lean::dec(x_1);
lean::dec(x_0);
x_37 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_19, x_28);
x_5 = x_37;
x_6 = x_30;
goto lbl_7;
}
else
{
obj* x_38; unsigned char x_40; 
x_38 = lean::cnstr_get(x_28, 0);
lean::inc(x_38);
x_40 = lean::cnstr_get_scalar<unsigned char>(x_28, sizeof(void*)*1);
if (x_40 == 0)
{
unsigned char x_42; 
lean::dec(x_28);
x_42 = lean::string_iterator_has_next(x_17);
if (x_42 == 0)
{
obj* x_44; obj* x_45; obj* x_46; obj* x_50; obj* x_51; obj* x_53; obj* x_56; obj* x_58; obj* x_59; obj* x_60; 
lean::dec(x_21);
x_44 = lean::box(0);
x_45 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_46 = l_mjoin___rarg___closed__1;
lean::inc(x_44);
lean::inc(x_46);
lean::inc(x_45);
x_50 = l_lean_parser_monad__parsec_error___at_lean_parser_detail__ident__suffix_parser___spec__3___rarg(x_45, x_46, x_44, x_44, x_0, x_1, x_17, x_30);
x_51 = lean::cnstr_get(x_50, 0);
lean::inc(x_51);
x_53 = lean::cnstr_get(x_50, 1);
lean::inc(x_53);
lean::dec(x_50);
x_56 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_56);
x_58 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_56, x_51);
x_59 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_38, x_58);
x_60 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_19, x_59);
x_5 = x_60;
x_6 = x_53;
goto lbl_7;
}
else
{
unsigned x_61; unsigned char x_62; 
x_61 = lean::string_iterator_curr(x_17);
x_62 = l_lean_is__id__first(x_61);
if (x_62 == 0)
{
obj* x_64; obj* x_65; obj* x_67; obj* x_69; obj* x_70; obj* x_71; obj* x_74; obj* x_75; obj* x_77; obj* x_80; obj* x_82; obj* x_83; obj* x_84; 
lean::dec(x_21);
x_64 = l_char_quote__core(x_61);
x_65 = l_char_has__repr___closed__1;
lean::inc(x_65);
x_67 = lean::string_append(x_65, x_64);
lean::dec(x_64);
x_69 = lean::string_append(x_67, x_65);
x_70 = lean::box(0);
x_71 = l_mjoin___rarg___closed__1;
lean::inc(x_70);
lean::inc(x_71);
x_74 = l_lean_parser_monad__parsec_error___at_lean_parser_detail__ident__suffix_parser___spec__3___rarg(x_69, x_71, x_70, x_70, x_0, x_1, x_17, x_30);
x_75 = lean::cnstr_get(x_74, 0);
lean::inc(x_75);
x_77 = lean::cnstr_get(x_74, 1);
lean::inc(x_77);
lean::dec(x_74);
x_80 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_80);
x_82 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_80, x_75);
x_83 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_38, x_82);
x_84 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_19, x_83);
x_5 = x_84;
x_6 = x_77;
goto lbl_7;
}
else
{
obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_38);
x_88 = lean::string_iterator_next(x_17);
x_89 = lean::box(0);
x_90 = lean::box_uint32(x_61);
if (lean::is_scalar(x_21)) {
 x_91 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_91 = x_21;
}
lean::cnstr_set(x_91, 0, x_90);
lean::cnstr_set(x_91, 1, x_88);
lean::cnstr_set(x_91, 2, x_89);
x_92 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_19, x_91);
x_5 = x_92;
x_6 = x_30;
goto lbl_7;
}
}
}
else
{
obj* x_98; 
lean::dec(x_17);
lean::dec(x_21);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_38);
x_98 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_19, x_28);
x_5 = x_98;
x_6 = x_30;
goto lbl_7;
}
}
}
else
{
obj* x_101; unsigned char x_103; obj* x_104; obj* x_105; obj* x_106; 
lean::dec(x_1);
lean::dec(x_0);
x_101 = lean::cnstr_get(x_12, 0);
lean::inc(x_101);
x_103 = lean::cnstr_get_scalar<unsigned char>(x_12, sizeof(void*)*1);
if (lean::is_shared(x_12)) {
 lean::dec(x_12);
 x_104 = lean::box(0);
} else {
 lean::cnstr_release(x_12, 0);
 x_104 = x_12;
}
if (lean::is_scalar(x_104)) {
 x_105 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_105 = x_104;
}
lean::cnstr_set(x_105, 0, x_101);
lean::cnstr_set_scalar(x_105, sizeof(void*)*1, x_103);
x_106 = x_105;
x_5 = x_106;
x_6 = x_14;
goto lbl_7;
}
lbl_7:
{
if (lean::obj_tag(x_5) == 0)
{
obj* x_107; obj* x_109; obj* x_110; obj* x_112; obj* x_113; 
x_107 = lean::cnstr_get(x_5, 0);
lean::inc(x_107);
if (lean::is_shared(x_5)) {
 lean::dec(x_5);
 x_109 = lean::box(0);
} else {
 lean::cnstr_release(x_5, 0);
 lean::cnstr_release(x_5, 1);
 lean::cnstr_release(x_5, 2);
 x_109 = x_5;
}
x_110 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_110);
if (lean::is_scalar(x_109)) {
 x_112 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_112 = x_109;
}
lean::cnstr_set(x_112, 0, x_107);
lean::cnstr_set(x_112, 1, x_2);
lean::cnstr_set(x_112, 2, x_110);
x_113 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_113, 0, x_112);
lean::cnstr_set(x_113, 1, x_6);
return x_113;
}
else
{
obj* x_115; 
lean::dec(x_2);
x_115 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_115, 0, x_5);
lean::cnstr_set(x_115, 1, x_6);
return x_115;
}
}
}
}
obj* l_reader__t_lift___at_lean_parser_detail__ident__suffix_parser___spec__5___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_6; 
lean::dec(x_1);
x_6 = lean::apply_3(x_0, x_2, x_3, x_4);
return x_6;
}
}
obj* l_reader__t_lift___at_lean_parser_detail__ident__suffix_parser___spec__5(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_lift___at_lean_parser_detail__ident__suffix_parser___spec__5___rarg), 5, 0);
return x_2;
}
}
obj* l_lean_parser_monad__parsec_str__core___at_lean_parser_detail__ident__suffix_parser___spec__6(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
unsigned char x_9; 
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
x_14 = l___private_580269747__str__aux___main(x_10, x_12, x_4);
if (lean::obj_tag(x_14) == 0)
{
obj* x_17; obj* x_18; obj* x_20; unsigned char x_21; obj* x_22; obj* x_23; obj* x_24; 
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
obj* l_reader__t_bind___at_lean_parser_detail__ident__suffix_parser___spec__7___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
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
obj* x_32; unsigned char x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_2);
x_32 = lean::cnstr_get(x_9, 0);
lean::inc(x_32);
x_34 = lean::cnstr_get_scalar<unsigned char>(x_9, sizeof(void*)*1);
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
obj* l_reader__t_bind___at_lean_parser_detail__ident__suffix_parser___spec__7(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_bind___at_lean_parser_detail__ident__suffix_parser___spec__7___rarg), 6, 0);
return x_4;
}
}
obj* l_lean_parser_rec__t_recurse___at_lean_parser_detail__ident__suffix_parser___spec__8(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
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
obj* l_list_mfoldl___main___at_lean_parser_detail__ident__suffix_parser___spec__10(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
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
obj* x_31; unsigned char x_33; obj* x_34; 
x_31 = lean::cnstr_get(x_26, 0);
lean::inc(x_31);
x_33 = lean::cnstr_get_scalar<unsigned char>(x_26, sizeof(void*)*1);
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
unsigned char x_35; obj* x_36; obj* x_37; 
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
unsigned char x_57; obj* x_58; obj* x_59; 
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
x_81 = l_list_mfoldl___main___at_lean_parser_detail__ident__suffix_parser___spec__10(x_0, x_74, x_17, x_3, x_4, x_76, x_21);
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
obj* x_93; unsigned char x_95; obj* x_96; obj* x_97; obj* x_98; obj* x_99; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_17);
x_93 = lean::cnstr_get(x_73, 0);
lean::inc(x_93);
x_95 = lean::cnstr_get_scalar<unsigned char>(x_73, sizeof(void*)*1);
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
obj* x_106; unsigned char x_108; obj* x_109; obj* x_110; obj* x_111; obj* x_112; 
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_17);
lean::dec(x_19);
x_106 = lean::cnstr_get(x_20, 0);
lean::inc(x_106);
x_108 = lean::cnstr_get_scalar<unsigned char>(x_20, sizeof(void*)*1);
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
obj* l_lean_parser_combinators_node___at_lean_parser_detail__ident__suffix_parser___spec__9(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_8; obj* x_9; obj* x_11; obj* x_13; 
x_6 = lean::box(0);
lean::inc(x_0);
x_8 = l_list_mfoldl___main___at_lean_parser_detail__ident__suffix_parser___spec__10(x_0, x_6, x_1, x_2, x_3, x_4, x_5);
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
obj* x_29; unsigned char x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; 
lean::dec(x_0);
x_29 = lean::cnstr_get(x_9, 0);
lean::inc(x_29);
x_31 = lean::cnstr_get_scalar<unsigned char>(x_9, sizeof(void*)*1);
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
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_detail__ident__suffix_parser___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
unsigned x_5; obj* x_6; 
x_5 = lean::unbox_uint32(x_0);
x_6 = l_lean_parser_monad__parsec_ch___at_lean_parser_detail__ident__suffix_parser___spec__1(x_5, x_1, x_2, x_3, x_4);
return x_6;
}
}
obj* l_lean_parser_parsec__t_lookahead___at_lean_parser_detail__ident__suffix_parser___spec__4___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
unsigned x_5; obj* x_6; 
x_5 = lean::unbox_uint32(x_3);
x_6 = l_lean_parser_parsec__t_lookahead___at_lean_parser_detail__ident__suffix_parser___spec__4(x_0, x_1, x_2, x_5, x_4);
return x_6;
}
}
obj* _init_l_lean_parser_detail__ident__suffix_parser_lean_parser_has__view() {
_start:
{
obj* x_0; obj* x_2; obj* x_3; obj* x_5; obj* x_6; obj* x_9; obj* x_10; obj* x_13; obj* x_14; obj* x_15; unsigned char x_16; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_34; obj* x_35; obj* x_39; 
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
x_14 = lean::mk_nat_obj(46u);
x_15 = lean::mk_nat_obj(55296u);
x_16 = lean::nat_dec_lt(x_14, x_15);
lean::dec(x_15);
x_18 = lean::mk_string(".");
x_19 = l_string_quote(x_18);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_20, 0, x_19);
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_with__trailing___rarg___lambda__1), 2, 0);
x_22 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_lift___at_lean_parser_with__trailing___spec__1___rarg), 4, 1);
lean::closure_set(x_22, 0, x_21);
x_23 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_lift___at_lean_parser_detail__ident__suffix_parser___spec__5___rarg), 5, 1);
lean::closure_set(x_23, 0, x_22);
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_detail__ident__suffix_parser___lambda__1), 6, 1);
lean::closure_set(x_24, 0, x_20);
x_25 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_bind___at_lean_parser_detail__ident__suffix_parser___spec__7___rarg), 6, 2);
lean::closure_set(x_25, 0, x_23);
lean::closure_set(x_25, 1, x_24);
x_26 = lean::box(0);
lean::inc(x_26);
x_28 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_rec__t_recurse___at_lean_parser_detail__ident__suffix_parser___spec__8), 5, 1);
lean::closure_set(x_28, 0, x_26);
x_29 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_26);
x_30 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_30, 0, x_25);
lean::cnstr_set(x_30, 1, x_29);
x_31 = l_lean_parser_detail__ident__suffix;
lean::inc(x_30);
lean::inc(x_31);
x_34 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_node___at_lean_parser_detail__ident__suffix_parser___spec__9), 6, 2);
lean::closure_set(x_34, 0, x_31);
lean::closure_set(x_34, 1, x_30);
x_35 = l_lean_parser_detail__ident__suffix_has__view;
lean::inc(x_35);
lean::inc(x_31);
lean::inc(x_13);
x_39 = l_lean_parser_combinators_node_view___rarg(x_2, x_5, x_9, x_13, x_31, x_30, x_35);
if (x_16 == 0)
{
obj* x_40; unsigned char x_41; 
x_40 = lean::mk_nat_obj(57343u);
x_41 = lean::nat_dec_lt(x_40, x_14);
lean::dec(x_40);
if (x_41 == 0)
{
obj* x_44; obj* x_45; obj* x_46; 
lean::dec(x_14);
x_44 = lean::mk_nat_obj(0u);
x_45 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_detail__ident__suffix_parser_lean_parser_has__view___lambda__1___boxed), 5, 1);
lean::closure_set(x_45, 0, x_44);
x_46 = l_lean_parser_combinators_seq__right_view___rarg(x_13, lean::box(0), lean::box(0), x_45, x_34, x_39);
return x_46;
}
else
{
obj* x_47; unsigned char x_48; 
x_47 = lean::mk_nat_obj(1114112u);
x_48 = lean::nat_dec_lt(x_14, x_47);
lean::dec(x_47);
if (x_48 == 0)
{
obj* x_51; obj* x_52; obj* x_53; 
lean::dec(x_14);
x_51 = lean::mk_nat_obj(0u);
x_52 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_detail__ident__suffix_parser_lean_parser_has__view___lambda__1___boxed), 5, 1);
lean::closure_set(x_52, 0, x_51);
x_53 = l_lean_parser_combinators_seq__right_view___rarg(x_13, lean::box(0), lean::box(0), x_52, x_34, x_39);
return x_53;
}
else
{
obj* x_54; obj* x_55; 
x_54 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_detail__ident__suffix_parser_lean_parser_has__view___lambda__1___boxed), 5, 1);
lean::closure_set(x_54, 0, x_14);
x_55 = l_lean_parser_combinators_seq__right_view___rarg(x_13, lean::box(0), lean::box(0), x_54, x_34, x_39);
return x_55;
}
}
}
else
{
obj* x_56; obj* x_57; 
x_56 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_detail__ident__suffix_parser_lean_parser_has__view___lambda__1___boxed), 5, 1);
lean::closure_set(x_56, 0, x_14);
x_57 = l_lean_parser_combinators_seq__right_view___rarg(x_13, lean::box(0), lean::box(0), x_56, x_34, x_39);
return x_57;
}
}
}
obj* l_lean_parser_detail__ident__suffix_parser_lean_parser_has__view___lambda__1(unsigned x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
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
obj* l_lean_parser_parsec__t_lookahead___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__view___spec__1(unsigned x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_11; obj* x_12; obj* x_14; 
lean::inc(x_3);
lean::inc(x_2);
lean::inc(x_1);
x_11 = l_lean_parser_monad__parsec_ch___at_lean_parser_detail__ident__suffix_parser___spec__1(x_0, x_1, x_2, x_3, x_4);
x_12 = lean::cnstr_get(x_11, 0);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_11, 1);
lean::inc(x_14);
lean::dec(x_11);
if (lean::obj_tag(x_12) == 0)
{
obj* x_17; obj* x_19; obj* x_21; obj* x_22; unsigned x_23; obj* x_27; obj* x_28; obj* x_30; 
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
lean::inc(x_2);
lean::inc(x_1);
x_27 = l_lean_parser_monad__parsec_ch___at_lean_parser_detail__ident__suffix_parser___spec__1(x_23, x_1, x_2, x_17, x_14);
x_28 = lean::cnstr_get(x_27, 0);
lean::inc(x_28);
x_30 = lean::cnstr_get(x_27, 1);
lean::inc(x_30);
lean::dec(x_27);
if (lean::obj_tag(x_28) == 0)
{
obj* x_37; 
lean::dec(x_17);
lean::dec(x_21);
lean::dec(x_1);
lean::dec(x_2);
x_37 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_19, x_28);
x_5 = x_37;
x_6 = x_30;
goto lbl_7;
}
else
{
obj* x_38; unsigned char x_40; 
x_38 = lean::cnstr_get(x_28, 0);
lean::inc(x_38);
x_40 = lean::cnstr_get_scalar<unsigned char>(x_28, sizeof(void*)*1);
if (x_40 == 0)
{
unsigned char x_42; 
lean::dec(x_28);
x_42 = lean::string_iterator_has_next(x_17);
if (x_42 == 0)
{
obj* x_44; obj* x_45; obj* x_46; obj* x_50; obj* x_51; obj* x_53; obj* x_56; obj* x_58; obj* x_59; obj* x_60; 
lean::dec(x_21);
x_44 = lean::box(0);
x_45 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_46 = l_mjoin___rarg___closed__1;
lean::inc(x_44);
lean::inc(x_46);
lean::inc(x_45);
x_50 = l_lean_parser_monad__parsec_error___at_lean_parser_detail__ident__suffix_parser___spec__3___rarg(x_45, x_46, x_44, x_44, x_1, x_2, x_17, x_30);
x_51 = lean::cnstr_get(x_50, 0);
lean::inc(x_51);
x_53 = lean::cnstr_get(x_50, 1);
lean::inc(x_53);
lean::dec(x_50);
x_56 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_56);
x_58 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_56, x_51);
x_59 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_38, x_58);
x_60 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_19, x_59);
x_5 = x_60;
x_6 = x_53;
goto lbl_7;
}
else
{
unsigned x_61; unsigned char x_62; 
x_61 = lean::string_iterator_curr(x_17);
x_62 = l_lean_is__id__first(x_61);
if (x_62 == 0)
{
obj* x_64; obj* x_65; obj* x_67; obj* x_69; obj* x_70; obj* x_71; obj* x_74; obj* x_75; obj* x_77; obj* x_80; obj* x_82; obj* x_83; obj* x_84; 
lean::dec(x_21);
x_64 = l_char_quote__core(x_61);
x_65 = l_char_has__repr___closed__1;
lean::inc(x_65);
x_67 = lean::string_append(x_65, x_64);
lean::dec(x_64);
x_69 = lean::string_append(x_67, x_65);
x_70 = lean::box(0);
x_71 = l_mjoin___rarg___closed__1;
lean::inc(x_70);
lean::inc(x_71);
x_74 = l_lean_parser_monad__parsec_error___at_lean_parser_detail__ident__suffix_parser___spec__3___rarg(x_69, x_71, x_70, x_70, x_1, x_2, x_17, x_30);
x_75 = lean::cnstr_get(x_74, 0);
lean::inc(x_75);
x_77 = lean::cnstr_get(x_74, 1);
lean::inc(x_77);
lean::dec(x_74);
x_80 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_80);
x_82 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_80, x_75);
x_83 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_38, x_82);
x_84 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_19, x_83);
x_5 = x_84;
x_6 = x_77;
goto lbl_7;
}
else
{
obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; 
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_38);
x_88 = lean::string_iterator_next(x_17);
x_89 = lean::box(0);
x_90 = lean::box_uint32(x_61);
if (lean::is_scalar(x_21)) {
 x_91 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_91 = x_21;
}
lean::cnstr_set(x_91, 0, x_90);
lean::cnstr_set(x_91, 1, x_88);
lean::cnstr_set(x_91, 2, x_89);
x_92 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_19, x_91);
x_5 = x_92;
x_6 = x_30;
goto lbl_7;
}
}
}
else
{
obj* x_98; 
lean::dec(x_17);
lean::dec(x_21);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_38);
x_98 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_19, x_28);
x_5 = x_98;
x_6 = x_30;
goto lbl_7;
}
}
}
else
{
obj* x_101; unsigned char x_103; obj* x_104; obj* x_105; obj* x_106; 
lean::dec(x_1);
lean::dec(x_2);
x_101 = lean::cnstr_get(x_12, 0);
lean::inc(x_101);
x_103 = lean::cnstr_get_scalar<unsigned char>(x_12, sizeof(void*)*1);
if (lean::is_shared(x_12)) {
 lean::dec(x_12);
 x_104 = lean::box(0);
} else {
 lean::cnstr_release(x_12, 0);
 x_104 = x_12;
}
if (lean::is_scalar(x_104)) {
 x_105 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_105 = x_104;
}
lean::cnstr_set(x_105, 0, x_101);
lean::cnstr_set_scalar(x_105, sizeof(void*)*1, x_103);
x_106 = x_105;
x_5 = x_106;
x_6 = x_14;
goto lbl_7;
}
lbl_7:
{
if (lean::obj_tag(x_5) == 0)
{
obj* x_107; obj* x_109; obj* x_110; obj* x_112; obj* x_113; 
x_107 = lean::cnstr_get(x_5, 0);
lean::inc(x_107);
if (lean::is_shared(x_5)) {
 lean::dec(x_5);
 x_109 = lean::box(0);
} else {
 lean::cnstr_release(x_5, 0);
 lean::cnstr_release(x_5, 1);
 lean::cnstr_release(x_5, 2);
 x_109 = x_5;
}
x_110 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_110);
if (lean::is_scalar(x_109)) {
 x_112 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_112 = x_109;
}
lean::cnstr_set(x_112, 0, x_107);
lean::cnstr_set(x_112, 1, x_3);
lean::cnstr_set(x_112, 2, x_110);
x_113 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_113, 0, x_112);
lean::cnstr_set(x_113, 1, x_6);
return x_113;
}
else
{
obj* x_115; 
lean::dec(x_3);
x_115 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_115, 0, x_5);
lean::cnstr_set(x_115, 1, x_6);
return x_115;
}
}
}
}
obj* l_lean_parser_detail__ident__suffix_parser_lean_parser_has__view___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
unsigned x_5; obj* x_6; 
x_5 = lean::unbox_uint32(x_0);
x_6 = l_lean_parser_detail__ident__suffix_parser_lean_parser_has__view___lambda__1(x_5, x_1, x_2, x_3, x_4);
return x_6;
}
}
obj* l_lean_parser_parsec__t_lookahead___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__view___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
unsigned x_5; obj* x_6; 
x_5 = lean::unbox_uint32(x_0);
x_6 = l_lean_parser_parsec__t_lookahead___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__view___spec__1(x_5, x_1, x_2, x_3, x_4);
return x_6;
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
obj* l_lean_parser_parsec__t_lookahead___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__1(unsigned x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_11; obj* x_12; obj* x_14; 
lean::inc(x_3);
lean::inc(x_2);
lean::inc(x_1);
x_11 = l_lean_parser_monad__parsec_ch___at_lean_parser_detail__ident__suffix_parser___spec__1(x_0, x_1, x_2, x_3, x_4);
x_12 = lean::cnstr_get(x_11, 0);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_11, 1);
lean::inc(x_14);
lean::dec(x_11);
if (lean::obj_tag(x_12) == 0)
{
obj* x_17; obj* x_19; obj* x_21; obj* x_22; unsigned x_23; obj* x_27; obj* x_28; obj* x_30; 
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
lean::inc(x_2);
lean::inc(x_1);
x_27 = l_lean_parser_monad__parsec_ch___at_lean_parser_detail__ident__suffix_parser___spec__1(x_23, x_1, x_2, x_17, x_14);
x_28 = lean::cnstr_get(x_27, 0);
lean::inc(x_28);
x_30 = lean::cnstr_get(x_27, 1);
lean::inc(x_30);
lean::dec(x_27);
if (lean::obj_tag(x_28) == 0)
{
obj* x_37; 
lean::dec(x_17);
lean::dec(x_21);
lean::dec(x_1);
lean::dec(x_2);
x_37 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_19, x_28);
x_5 = x_37;
x_6 = x_30;
goto lbl_7;
}
else
{
obj* x_38; unsigned char x_40; 
x_38 = lean::cnstr_get(x_28, 0);
lean::inc(x_38);
x_40 = lean::cnstr_get_scalar<unsigned char>(x_28, sizeof(void*)*1);
if (x_40 == 0)
{
unsigned char x_42; 
lean::dec(x_28);
x_42 = lean::string_iterator_has_next(x_17);
if (x_42 == 0)
{
obj* x_44; obj* x_45; obj* x_46; obj* x_50; obj* x_51; obj* x_53; obj* x_56; obj* x_58; obj* x_59; obj* x_60; 
lean::dec(x_21);
x_44 = lean::box(0);
x_45 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_46 = l_mjoin___rarg___closed__1;
lean::inc(x_44);
lean::inc(x_46);
lean::inc(x_45);
x_50 = l_lean_parser_monad__parsec_error___at_lean_parser_detail__ident__suffix_parser___spec__3___rarg(x_45, x_46, x_44, x_44, x_1, x_2, x_17, x_30);
x_51 = lean::cnstr_get(x_50, 0);
lean::inc(x_51);
x_53 = lean::cnstr_get(x_50, 1);
lean::inc(x_53);
lean::dec(x_50);
x_56 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_56);
x_58 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_56, x_51);
x_59 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_38, x_58);
x_60 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_19, x_59);
x_5 = x_60;
x_6 = x_53;
goto lbl_7;
}
else
{
unsigned x_61; unsigned char x_62; 
x_61 = lean::string_iterator_curr(x_17);
x_62 = l_lean_is__id__first(x_61);
if (x_62 == 0)
{
obj* x_64; obj* x_65; obj* x_67; obj* x_69; obj* x_70; obj* x_71; obj* x_74; obj* x_75; obj* x_77; obj* x_80; obj* x_82; obj* x_83; obj* x_84; 
lean::dec(x_21);
x_64 = l_char_quote__core(x_61);
x_65 = l_char_has__repr___closed__1;
lean::inc(x_65);
x_67 = lean::string_append(x_65, x_64);
lean::dec(x_64);
x_69 = lean::string_append(x_67, x_65);
x_70 = lean::box(0);
x_71 = l_mjoin___rarg___closed__1;
lean::inc(x_70);
lean::inc(x_71);
x_74 = l_lean_parser_monad__parsec_error___at_lean_parser_detail__ident__suffix_parser___spec__3___rarg(x_69, x_71, x_70, x_70, x_1, x_2, x_17, x_30);
x_75 = lean::cnstr_get(x_74, 0);
lean::inc(x_75);
x_77 = lean::cnstr_get(x_74, 1);
lean::inc(x_77);
lean::dec(x_74);
x_80 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_80);
x_82 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_80, x_75);
x_83 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_38, x_82);
x_84 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_19, x_83);
x_5 = x_84;
x_6 = x_77;
goto lbl_7;
}
else
{
obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; 
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_38);
x_88 = lean::string_iterator_next(x_17);
x_89 = lean::box(0);
x_90 = lean::box_uint32(x_61);
if (lean::is_scalar(x_21)) {
 x_91 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_91 = x_21;
}
lean::cnstr_set(x_91, 0, x_90);
lean::cnstr_set(x_91, 1, x_88);
lean::cnstr_set(x_91, 2, x_89);
x_92 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_19, x_91);
x_5 = x_92;
x_6 = x_30;
goto lbl_7;
}
}
}
else
{
obj* x_98; 
lean::dec(x_17);
lean::dec(x_21);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_38);
x_98 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_19, x_28);
x_5 = x_98;
x_6 = x_30;
goto lbl_7;
}
}
}
else
{
obj* x_101; unsigned char x_103; obj* x_104; obj* x_105; obj* x_106; 
lean::dec(x_1);
lean::dec(x_2);
x_101 = lean::cnstr_get(x_12, 0);
lean::inc(x_101);
x_103 = lean::cnstr_get_scalar<unsigned char>(x_12, sizeof(void*)*1);
if (lean::is_shared(x_12)) {
 lean::dec(x_12);
 x_104 = lean::box(0);
} else {
 lean::cnstr_release(x_12, 0);
 x_104 = x_12;
}
if (lean::is_scalar(x_104)) {
 x_105 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_105 = x_104;
}
lean::cnstr_set(x_105, 0, x_101);
lean::cnstr_set_scalar(x_105, sizeof(void*)*1, x_103);
x_106 = x_105;
x_5 = x_106;
x_6 = x_14;
goto lbl_7;
}
lbl_7:
{
if (lean::obj_tag(x_5) == 0)
{
obj* x_107; obj* x_109; obj* x_110; obj* x_112; obj* x_113; 
x_107 = lean::cnstr_get(x_5, 0);
lean::inc(x_107);
if (lean::is_shared(x_5)) {
 lean::dec(x_5);
 x_109 = lean::box(0);
} else {
 lean::cnstr_release(x_5, 0);
 lean::cnstr_release(x_5, 1);
 lean::cnstr_release(x_5, 2);
 x_109 = x_5;
}
x_110 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_110);
if (lean::is_scalar(x_109)) {
 x_112 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_112 = x_109;
}
lean::cnstr_set(x_112, 0, x_107);
lean::cnstr_set(x_112, 1, x_3);
lean::cnstr_set(x_112, 2, x_110);
x_113 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_113, 0, x_112);
lean::cnstr_set(x_113, 1, x_6);
return x_113;
}
else
{
obj* x_115; 
lean::dec(x_3);
x_115 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_115, 0, x_5);
lean::cnstr_set(x_115, 1, x_6);
return x_115;
}
}
}
}
obj* l_lean_parser_parsec__t_lookahead___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
unsigned x_5; obj* x_6; 
x_5 = lean::unbox_uint32(x_0);
x_6 = l_lean_parser_parsec__t_lookahead___at_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens___spec__1(x_5, x_1, x_2, x_3, x_4);
return x_6;
}
}
obj* _init_l_lean_parser_detail__ident() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean::name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean::name_mk_string(x_2, x_3);
x_5 = lean::mk_string("detail_ident");
x_6 = lean::name_mk_string(x_4, x_5);
return x_6;
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
obj* _init_l_lean_parser_detail__ident_has__view() {
_start:
{
obj* x_0; 
x_0 = l_lean_parser_detail__ident_has__view_x_27;
lean::inc(x_0);
return x_0;
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
x_8 = l_lean_parser_combinators_node___at_lean_parser_detail__ident__suffix_parser___spec__9(x_4, x_5, x_0, x_1, x_2, x_3);
return x_8;
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
obj* x_31; unsigned char x_33; obj* x_34; obj* x_35; obj* x_36; 
x_31 = lean::cnstr_get(x_14, 0);
lean::inc(x_31);
x_33 = lean::cnstr_get_scalar<unsigned char>(x_14, sizeof(void*)*1);
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
obj* x_37; unsigned char x_39; obj* x_40; obj* x_41; obj* x_43; obj* x_45; obj* x_47; obj* x_50; obj* x_52; obj* x_53; obj* x_55; obj* x_56; obj* x_57; 
x_37 = lean::cnstr_get(x_14, 0);
lean::inc(x_37);
x_39 = lean::cnstr_get_scalar<unsigned char>(x_14, sizeof(void*)*1);
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
unsigned char x_58; obj* x_59; obj* x_60; 
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
obj* x_91; unsigned char x_93; obj* x_94; obj* x_95; obj* x_96; obj* x_97; 
x_91 = lean::cnstr_get(x_5, 0);
lean::inc(x_91);
x_93 = lean::cnstr_get_scalar<unsigned char>(x_5, sizeof(void*)*1);
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
obj* x_100; unsigned char x_102; 
x_100 = lean::cnstr_get(x_9, 0);
lean::inc(x_100);
x_102 = lean::cnstr_get_scalar<unsigned char>(x_9, sizeof(void*)*1);
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
obj* l_lean_parser_detail__ident_parser___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_6; obj* x_7; obj* x_10; 
lean::dec(x_0);
x_6 = l_lean_parser_detail__ident;
x_7 = l_lean_parser_detail__ident_x_27___closed__1;
lean::inc(x_7);
lean::inc(x_6);
x_10 = l_lean_parser_combinators_node___at_lean_parser_detail__ident__suffix_parser___spec__9(x_6, x_7, x_1, x_2, x_3, x_4);
return x_10;
}
}
obj* l___private_3693562977__run__aux___at_lean_parser_detail__ident_parser___spec__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_8; 
x_7 = l___private_3693562977__run__aux___main___rarg(x_0, x_1, x_2, x_3);
x_8 = lean::apply_3(x_7, x_4, x_5, x_6);
return x_8;
}
}
obj* l_lean_parser_rec__t_run___at_lean_parser_detail__ident_parser___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_8; 
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l___private_3693562977__run__aux___at_lean_parser_detail__ident_parser___spec__3), 7, 3);
lean::closure_set(x_7, 0, x_1);
lean::closure_set(x_7, 1, x_2);
lean::closure_set(x_7, 2, x_3);
x_8 = lean::apply_4(x_0, x_7, x_4, x_5, x_6);
return x_8;
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
obj* _init_l_lean_parser_rec__t_run__parsec___at_lean_parser_detail__ident_parser___spec__1___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_rec__t_run__parsec___at_lean_parser_detail__ident_parser___spec__1___lambda__1), 4, 0);
return x_0;
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
x_11 = l_lean_parser_monad__parsec_error___at___private_4089500695__finish__comment__block__aux___main___spec__1___rarg(x_6, x_7, x_5, x_5, x_1, x_2, x_3);
return x_11;
}
}
obj* l___private_3519775105__ident_x_27(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_5; obj* x_6; obj* x_8; obj* x_10; 
lean::inc(x_1);
lean::inc(x_0);
x_5 = l_lean_parser_id__part___at___private_3519775105__ident_x_27___spec__1(x_0, x_1, x_2);
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
obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_18; obj* x_19; unsigned char x_20; unsigned x_22; 
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
x_18 = lean::mk_nat_obj(46u);
x_19 = lean::mk_nat_obj(55296u);
x_20 = lean::nat_dec_lt(x_18, x_19);
lean::dec(x_19);
if (x_20 == 0)
{
obj* x_24; unsigned char x_25; 
x_24 = lean::mk_nat_obj(57343u);
x_25 = lean::nat_dec_lt(x_24, x_18);
lean::dec(x_24);
if (x_25 == 0)
{
obj* x_28; unsigned x_29; 
lean::dec(x_18);
x_28 = lean::mk_nat_obj(0u);
x_29 = lean::unbox_uint32(x_28);
lean::dec(x_28);
x_22 = x_29;
goto lbl_23;
}
else
{
obj* x_31; unsigned char x_32; 
x_31 = lean::mk_nat_obj(1114112u);
x_32 = lean::nat_dec_lt(x_18, x_31);
lean::dec(x_31);
if (x_32 == 0)
{
obj* x_35; unsigned x_36; 
lean::dec(x_18);
x_35 = lean::mk_nat_obj(0u);
x_36 = lean::unbox_uint32(x_35);
lean::dec(x_35);
x_22 = x_36;
goto lbl_23;
}
else
{
unsigned x_38; 
x_38 = lean::unbox_uint32(x_18);
lean::dec(x_18);
x_22 = x_38;
goto lbl_23;
}
}
}
else
{
unsigned x_40; 
x_40 = lean::unbox_uint32(x_18);
lean::dec(x_18);
x_22 = x_40;
goto lbl_23;
}
lbl_23:
{
obj* x_42; obj* x_43; obj* x_45; 
x_42 = l_lean_parser_monad__parsec_foldl___at___private_3519775105__ident_x_27___spec__20(x_11, x_22, x_0, x_13, x_8);
x_43 = lean::cnstr_get(x_42, 0);
lean::inc(x_43);
x_45 = lean::cnstr_get(x_42, 1);
lean::inc(x_45);
lean::dec(x_42);
if (lean::obj_tag(x_43) == 0)
{
obj* x_48; obj* x_50; obj* x_52; obj* x_57; obj* x_58; obj* x_61; obj* x_62; obj* x_63; obj* x_65; obj* x_66; obj* x_68; obj* x_69; obj* x_70; obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_77; obj* x_78; 
x_48 = lean::cnstr_get(x_43, 0);
lean::inc(x_48);
x_50 = lean::cnstr_get(x_43, 1);
lean::inc(x_50);
x_52 = lean::cnstr_get(x_43, 2);
lean::inc(x_52);
lean::dec(x_43);
lean::inc(x_1);
lean::inc(x_1);
x_57 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_57, 0, x_1);
lean::cnstr_set(x_57, 1, x_1);
x_58 = lean::string_iterator_offset(x_1);
lean::inc(x_50);
lean::inc(x_50);
x_61 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_61, 0, x_50);
lean::cnstr_set(x_61, 1, x_50);
x_62 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_62, 0, x_57);
lean::cnstr_set(x_62, 1, x_58);
lean::cnstr_set(x_62, 2, x_61);
x_63 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_63, 0, x_62);
lean::inc(x_50);
x_65 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_65, 0, x_1);
lean::cnstr_set(x_65, 1, x_50);
x_66 = lean::box(0);
lean::inc(x_66);
x_68 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_68, 0, x_63);
lean::cnstr_set(x_68, 1, x_65);
lean::cnstr_set(x_68, 2, x_48);
lean::cnstr_set(x_68, 3, x_66);
lean::cnstr_set(x_68, 4, x_66);
x_69 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_69, 0, x_68);
x_70 = l_lean_parser_finish__comment__block___closed__2;
lean::inc(x_70);
if (lean::is_scalar(x_17)) {
 x_72 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_72 = x_17;
}
lean::cnstr_set(x_72, 0, x_69);
lean::cnstr_set(x_72, 1, x_50);
lean::cnstr_set(x_72, 2, x_70);
x_73 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_52, x_72);
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
lean::cnstr_set(x_78, 1, x_45);
return x_78;
}
else
{
obj* x_81; unsigned char x_83; obj* x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_88; obj* x_90; obj* x_91; 
lean::dec(x_17);
lean::dec(x_1);
x_81 = lean::cnstr_get(x_43, 0);
lean::inc(x_81);
x_83 = lean::cnstr_get_scalar<unsigned char>(x_43, sizeof(void*)*1);
if (lean::is_shared(x_43)) {
 lean::dec(x_43);
 x_84 = lean::box(0);
} else {
 lean::cnstr_release(x_43, 0);
 x_84 = x_43;
}
if (lean::is_scalar(x_84)) {
 x_85 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_85 = x_84;
}
lean::cnstr_set(x_85, 0, x_81);
lean::cnstr_set_scalar(x_85, sizeof(void*)*1, x_83);
x_86 = x_85;
x_87 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_86);
x_88 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_88);
x_90 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_88, x_87);
if (lean::is_scalar(x_10)) {
 x_91 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_91 = x_10;
}
lean::cnstr_set(x_91, 0, x_90);
lean::cnstr_set(x_91, 1, x_45);
return x_91;
}
}
}
else
{
obj* x_94; unsigned char x_96; obj* x_97; obj* x_98; obj* x_99; obj* x_100; obj* x_102; obj* x_103; 
lean::dec(x_1);
lean::dec(x_0);
x_94 = lean::cnstr_get(x_6, 0);
lean::inc(x_94);
x_96 = lean::cnstr_get_scalar<unsigned char>(x_6, sizeof(void*)*1);
if (lean::is_shared(x_6)) {
 lean::dec(x_6);
 x_97 = lean::box(0);
} else {
 lean::cnstr_release(x_6, 0);
 x_97 = x_6;
}
if (lean::is_scalar(x_97)) {
 x_98 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_98 = x_97;
}
lean::cnstr_set(x_98, 0, x_94);
lean::cnstr_set_scalar(x_98, sizeof(void*)*1, x_96);
x_99 = x_98;
x_100 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_100);
x_102 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_100, x_99);
if (lean::is_scalar(x_10)) {
 x_103 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_103 = x_10;
}
lean::cnstr_set(x_103, 0, x_102);
lean::cnstr_set(x_103, 1, x_8);
return x_103;
}
}
}
obj* l_lean_parser_monad__parsec_curr___at___private_3519775105__ident_x_27___spec__2___rarg(obj* x_0, obj* x_1) {
_start:
{
unsigned x_2; obj* x_3; obj* x_4; obj* x_6; obj* x_7; 
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
obj* l_lean_parser_monad__parsec_curr___at___private_3519775105__ident_x_27___spec__2(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_curr___at___private_3519775105__ident_x_27___spec__2___rarg), 2, 0);
return x_2;
}
}
obj* l___private_31565857__take__while__aux___main___at___private_3519775105__ident_x_27___spec__5(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; unsigned char x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
unsigned char x_6; 
x_6 = lean::string_iterator_has_next(x_2);
if (x_6 == 0)
{
obj* x_8; 
lean::dec(x_0);
x_8 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_8;
}
else
{
unsigned x_9; unsigned char x_10; 
x_9 = lean::string_iterator_curr(x_2);
x_10 = l_lean_is__id__rest(x_9);
if (x_10 == 0)
{
obj* x_12; 
lean::dec(x_0);
x_12 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
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
x_21 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_21;
}
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_3519775105__ident_x_27___spec__4(unsigned x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
lean::dec(x_1);
x_5 = l_string_join___closed__1;
lean::inc(x_5);
x_7 = lean::string_push(x_5, x_0);
x_8 = lean::string_iterator_remaining(x_2);
x_9 = l___private_31565857__take__while__aux___main___at___private_3519775105__ident_x_27___spec__5(x_8, x_7, x_2);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_3);
return x_10;
}
}
obj* l___private_31565857__take__while__aux___main___at___private_3519775105__ident_x_27___spec__7(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; unsigned char x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
unsigned char x_6; 
x_6 = lean::string_iterator_has_next(x_2);
if (x_6 == 0)
{
obj* x_8; 
lean::dec(x_0);
x_8 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_8;
}
else
{
unsigned x_9; unsigned char x_10; 
x_9 = lean::string_iterator_curr(x_2);
x_10 = l_lean_is__id__rest(x_9);
if (x_10 == 0)
{
obj* x_12; 
lean::dec(x_0);
x_12 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
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
x_21 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_21;
}
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_3519775105__ident_x_27___spec__6(unsigned x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
lean::dec(x_1);
x_5 = l_string_join___closed__1;
lean::inc(x_5);
x_7 = lean::string_push(x_5, x_0);
x_8 = lean::string_iterator_remaining(x_2);
x_9 = l___private_31565857__take__while__aux___main___at___private_3519775105__ident_x_27___spec__7(x_8, x_7, x_2);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_3);
return x_10;
}
}
obj* l___private_31565857__take__while__aux___main___at___private_3519775105__ident_x_27___spec__9(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; unsigned char x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
unsigned char x_6; 
x_6 = lean::string_iterator_has_next(x_2);
if (x_6 == 0)
{
obj* x_8; 
lean::dec(x_0);
x_8 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_8;
}
else
{
unsigned x_9; unsigned char x_10; 
x_9 = lean::string_iterator_curr(x_2);
x_10 = l_lean_is__id__rest(x_9);
if (x_10 == 0)
{
obj* x_12; 
lean::dec(x_0);
x_12 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
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
x_21 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_21;
}
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_3519775105__ident_x_27___spec__8(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
unsigned x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
lean::dec(x_1);
x_5 = lean::string_iterator_curr(x_0);
lean::dec(x_0);
x_7 = l_string_join___closed__1;
lean::inc(x_7);
x_9 = lean::string_push(x_7, x_5);
x_10 = lean::string_iterator_remaining(x_2);
x_11 = l___private_31565857__take__while__aux___main___at___private_3519775105__ident_x_27___spec__9(x_10, x_9, x_2);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_3);
return x_12;
}
}
obj* l_lean_parser_id__part__default___at___private_3519775105__ident_x_27___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
unsigned char x_3; 
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
x_11 = l_lean_parser_monad__parsec_error___at___private_4089500695__finish__comment__block__aux___main___spec__1___rarg(x_5, x_6, x_4, x_4, x_0, x_1, x_2);
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
obj* x_20; obj* x_22; obj* x_24; unsigned x_27; obj* x_29; obj* x_30; obj* x_32; obj* x_35; obj* x_36; 
x_20 = lean::cnstr_get(x_19, 0);
lean::inc(x_20);
x_22 = lean::cnstr_get(x_19, 1);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_19, 2);
lean::inc(x_24);
lean::dec(x_19);
x_27 = lean::unbox_uint32(x_20);
lean::dec(x_20);
x_29 = l_lean_parser_monad__parsec_take__while__cont___at___private_3519775105__ident_x_27___spec__4(x_27, x_0, x_22, x_14);
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
obj* x_38; unsigned char x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; 
lean::dec(x_0);
x_38 = lean::cnstr_get(x_19, 0);
lean::inc(x_38);
x_40 = lean::cnstr_get_scalar<unsigned char>(x_19, sizeof(void*)*1);
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
unsigned x_45; unsigned char x_46; 
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
x_58 = l_lean_parser_monad__parsec_error___at___private_4089500695__finish__comment__block__aux___main___spec__1___rarg(x_52, x_54, x_53, x_53, x_0, x_1, x_2);
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
obj* x_67; obj* x_69; obj* x_71; unsigned x_74; obj* x_76; obj* x_77; obj* x_79; obj* x_82; obj* x_83; 
x_67 = lean::cnstr_get(x_66, 0);
lean::inc(x_67);
x_69 = lean::cnstr_get(x_66, 1);
lean::inc(x_69);
x_71 = lean::cnstr_get(x_66, 2);
lean::inc(x_71);
lean::dec(x_66);
x_74 = lean::unbox_uint32(x_67);
lean::dec(x_67);
x_76 = l_lean_parser_monad__parsec_take__while__cont___at___private_3519775105__ident_x_27___spec__6(x_74, x_0, x_69, x_61);
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
obj* x_85; unsigned char x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; 
lean::dec(x_0);
x_85 = lean::cnstr_get(x_66, 0);
lean::inc(x_85);
x_87 = lean::cnstr_get_scalar<unsigned char>(x_66, sizeof(void*)*1);
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
x_94 = l_lean_parser_monad__parsec_take__while__cont___at___private_3519775105__ident_x_27___spec__8(x_1, x_0, x_93, x_2);
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
obj* l_lean_parser_monad__parsec_ch___at___private_3519775105__ident_x_27___spec__11(unsigned x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
unsigned char x_4; 
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
x_11 = l_lean_parser_monad__parsec_error___at___private_4089500695__finish__comment__block__aux___main___spec__1___rarg(x_6, x_7, x_5, x_5, x_1, x_2, x_3);
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
unsigned x_21; obj* x_22; obj* x_23; unsigned char x_24; 
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
x_37 = l_lean_parser_monad__parsec_error___at___private_4089500695__finish__comment__block__aux___main___spec__1___rarg(x_32, x_34, x_33, x_33, x_1, x_2, x_3);
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
obj* l___private_31565857__take__while__aux___main___at___private_3519775105__ident_x_27___spec__14(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; unsigned char x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
unsigned char x_6; 
x_6 = lean::string_iterator_has_next(x_2);
if (x_6 == 0)
{
obj* x_8; 
lean::dec(x_0);
x_8 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_8;
}
else
{
unsigned x_9; unsigned char x_10; 
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
x_19 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_19;
}
}
}
else
{
obj* x_21; 
lean::dec(x_0);
x_21 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_21;
}
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_3519775105__ident_x_27___spec__13(unsigned x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
lean::dec(x_1);
x_5 = l_string_join___closed__1;
lean::inc(x_5);
x_7 = lean::string_push(x_5, x_0);
x_8 = lean::string_iterator_remaining(x_2);
x_9 = l___private_31565857__take__while__aux___main___at___private_3519775105__ident_x_27___spec__14(x_8, x_7, x_2);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_3);
return x_10;
}
}
obj* l___private_31565857__take__while__aux___main___at___private_3519775105__ident_x_27___spec__16(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; unsigned char x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
unsigned char x_6; 
x_6 = lean::string_iterator_has_next(x_2);
if (x_6 == 0)
{
obj* x_8; 
lean::dec(x_0);
x_8 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_8;
}
else
{
unsigned x_9; unsigned char x_10; 
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
x_19 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_19;
}
}
}
else
{
obj* x_21; 
lean::dec(x_0);
x_21 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_21;
}
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_3519775105__ident_x_27___spec__15(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
unsigned x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
lean::dec(x_1);
x_5 = lean::string_iterator_curr(x_0);
lean::dec(x_0);
x_7 = l_string_join___closed__1;
lean::inc(x_7);
x_9 = lean::string_push(x_7, x_5);
x_10 = lean::string_iterator_remaining(x_2);
x_11 = l___private_31565857__take__while__aux___main___at___private_3519775105__ident_x_27___spec__16(x_10, x_9, x_2);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_3);
return x_12;
}
}
obj* l___private_31565857__take__while__aux___main___at___private_3519775105__ident_x_27___spec__18(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; unsigned char x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
unsigned char x_6; 
x_6 = lean::string_iterator_has_next(x_2);
if (x_6 == 0)
{
obj* x_8; 
lean::dec(x_0);
x_8 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_8;
}
else
{
unsigned x_9; unsigned char x_10; 
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
x_19 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_19;
}
}
}
else
{
obj* x_21; 
lean::dec(x_0);
x_21 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_21;
}
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_3519775105__ident_x_27___spec__17(unsigned x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
lean::dec(x_1);
x_5 = l_string_join___closed__1;
lean::inc(x_5);
x_7 = lean::string_push(x_5, x_0);
x_8 = lean::string_iterator_remaining(x_2);
x_9 = l___private_31565857__take__while__aux___main___at___private_3519775105__ident_x_27___spec__18(x_8, x_7, x_2);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_3);
return x_10;
}
}
obj* l_lean_parser_monad__parsec_take__while1___at___private_3519775105__ident_x_27___spec__12(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
unsigned char x_3; 
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
x_11 = l_lean_parser_monad__parsec_error___at___private_4089500695__finish__comment__block__aux___main___spec__1___rarg(x_5, x_6, x_4, x_4, x_0, x_1, x_2);
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
obj* x_20; obj* x_22; obj* x_24; unsigned x_27; obj* x_29; obj* x_30; obj* x_32; obj* x_35; obj* x_36; 
x_20 = lean::cnstr_get(x_19, 0);
lean::inc(x_20);
x_22 = lean::cnstr_get(x_19, 1);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_19, 2);
lean::inc(x_24);
lean::dec(x_19);
x_27 = lean::unbox_uint32(x_20);
lean::dec(x_20);
x_29 = l_lean_parser_monad__parsec_take__while__cont___at___private_3519775105__ident_x_27___spec__13(x_27, x_0, x_22, x_14);
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
obj* x_38; unsigned char x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; 
lean::dec(x_0);
x_38 = lean::cnstr_get(x_19, 0);
lean::inc(x_38);
x_40 = lean::cnstr_get_scalar<unsigned char>(x_19, sizeof(void*)*1);
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
unsigned x_45; unsigned char x_46; 
x_45 = lean::string_iterator_curr(x_1);
x_46 = l_lean_is__id__end__escape(x_45);
if (x_46 == 0)
{
obj* x_48; obj* x_49; obj* x_50; obj* x_52; obj* x_54; obj* x_55; obj* x_56; obj* x_57; 
lean::inc(x_1);
x_48 = lean::string_iterator_next(x_1);
x_49 = l_lean_parser_monad__parsec_take__while__cont___at___private_3519775105__ident_x_27___spec__15(x_1, x_0, x_48, x_2);
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
x_69 = l_lean_parser_monad__parsec_error___at___private_4089500695__finish__comment__block__aux___main___spec__1___rarg(x_63, x_65, x_64, x_64, x_0, x_1, x_2);
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
obj* x_78; obj* x_80; obj* x_82; unsigned x_85; obj* x_87; obj* x_88; obj* x_90; obj* x_93; obj* x_94; 
x_78 = lean::cnstr_get(x_77, 0);
lean::inc(x_78);
x_80 = lean::cnstr_get(x_77, 1);
lean::inc(x_80);
x_82 = lean::cnstr_get(x_77, 2);
lean::inc(x_82);
lean::dec(x_77);
x_85 = lean::unbox_uint32(x_78);
lean::dec(x_78);
x_87 = l_lean_parser_monad__parsec_take__while__cont___at___private_3519775105__ident_x_27___spec__17(x_85, x_0, x_80, x_72);
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
obj* x_96; unsigned char x_98; obj* x_99; obj* x_100; obj* x_101; obj* x_102; 
lean::dec(x_0);
x_96 = lean::cnstr_get(x_77, 0);
lean::inc(x_96);
x_98 = lean::cnstr_get_scalar<unsigned char>(x_77, sizeof(void*)*1);
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
obj* l_lean_parser_id__part__escaped___at___private_3519775105__ident_x_27___spec__10(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; unsigned x_4; obj* x_6; obj* x_7; obj* x_9; obj* x_11; 
x_3 = l_lean_id__begin__escape;
x_4 = lean::unbox_uint32(x_3);
lean::inc(x_0);
x_6 = l_lean_parser_monad__parsec_ch___at___private_3519775105__ident_x_27___spec__11(x_4, x_0, x_1, x_2);
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
x_18 = l_lean_parser_monad__parsec_take__while1___at___private_3519775105__ident_x_27___spec__12(x_0, x_12, x_9);
x_19 = lean::cnstr_get(x_18, 0);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_18, 1);
lean::inc(x_21);
lean::dec(x_18);
x_24 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_14, x_19);
if (lean::obj_tag(x_24) == 0)
{
obj* x_25; obj* x_27; obj* x_29; obj* x_32; unsigned x_33; obj* x_34; obj* x_35; obj* x_37; 
x_25 = lean::cnstr_get(x_24, 0);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_24, 1);
lean::inc(x_27);
x_29 = lean::cnstr_get(x_24, 2);
lean::inc(x_29);
lean::dec(x_24);
x_32 = l_lean_id__end__escape;
x_33 = lean::unbox_uint32(x_32);
x_34 = l_lean_parser_monad__parsec_ch___at___private_3519775105__ident_x_27___spec__11(x_33, x_0, x_27, x_21);
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
obj* x_53; unsigned char x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; 
lean::dec(x_16);
lean::dec(x_25);
x_53 = lean::cnstr_get(x_35, 0);
lean::inc(x_53);
x_55 = lean::cnstr_get_scalar<unsigned char>(x_35, sizeof(void*)*1);
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
obj* x_63; unsigned char x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; 
lean::dec(x_16);
lean::dec(x_0);
x_63 = lean::cnstr_get(x_24, 0);
lean::inc(x_63);
x_65 = lean::cnstr_get_scalar<unsigned char>(x_24, sizeof(void*)*1);
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
obj* x_71; unsigned char x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; 
lean::dec(x_0);
x_71 = lean::cnstr_get(x_7, 0);
lean::inc(x_71);
x_73 = lean::cnstr_get_scalar<unsigned char>(x_7, sizeof(void*)*1);
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
obj* l_lean_parser_id__part___at___private_3519775105__ident_x_27___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_6; obj* x_8; 
x_3 = l_lean_parser_monad__parsec_curr___at___private_3519775105__ident_x_27___spec__2___rarg(x_1, x_2);
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
obj* x_9; obj* x_11; obj* x_13; obj* x_15; unsigned x_16; unsigned char x_18; obj* x_19; obj* x_20; obj* x_22; obj* x_23; 
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
obj* x_24; obj* x_26; obj* x_28; unsigned char x_31; 
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
x_33 = l_lean_parser_id__part__default___at___private_3519775105__ident_x_27___spec__3(x_0, x_26, x_6);
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
x_41 = l_lean_parser_id__part__escaped___at___private_3519775105__ident_x_27___spec__10(x_0, x_26, x_6);
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
obj* x_50; unsigned char x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; 
lean::dec(x_0);
x_50 = lean::cnstr_get(x_23, 0);
lean::inc(x_50);
x_52 = lean::cnstr_get_scalar<unsigned char>(x_23, sizeof(void*)*1);
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
obj* x_58; unsigned char x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; 
lean::dec(x_0);
x_58 = lean::cnstr_get(x_4, 0);
lean::inc(x_58);
x_60 = lean::cnstr_get_scalar<unsigned char>(x_4, sizeof(void*)*1);
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
obj* l_lean_parser_parsec__t_lookahead___at___private_3519775105__ident_x_27___spec__19(unsigned x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_9; obj* x_10; obj* x_12; 
lean::inc(x_2);
lean::inc(x_1);
x_9 = l_lean_parser_monad__parsec_ch___at___private_3519775105__ident_x_27___spec__11(x_0, x_1, x_2, x_3);
x_10 = lean::cnstr_get(x_9, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_9, 1);
lean::inc(x_12);
lean::dec(x_9);
if (lean::obj_tag(x_10) == 0)
{
obj* x_15; obj* x_17; obj* x_19; obj* x_20; unsigned x_21; obj* x_24; obj* x_25; obj* x_27; 
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
x_21 = lean::unbox_uint32(x_20);
lean::inc(x_15);
lean::inc(x_1);
x_24 = l_lean_parser_monad__parsec_ch___at___private_3519775105__ident_x_27___spec__11(x_21, x_1, x_15, x_12);
x_25 = lean::cnstr_get(x_24, 0);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_24, 1);
lean::inc(x_27);
lean::dec(x_24);
if (lean::obj_tag(x_25) == 0)
{
obj* x_33; 
lean::dec(x_15);
lean::dec(x_19);
lean::dec(x_1);
x_33 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_17, x_25);
x_4 = x_33;
x_5 = x_27;
goto lbl_6;
}
else
{
obj* x_34; unsigned char x_36; 
x_34 = lean::cnstr_get(x_25, 0);
lean::inc(x_34);
x_36 = lean::cnstr_get_scalar<unsigned char>(x_25, sizeof(void*)*1);
if (x_36 == 0)
{
unsigned char x_38; 
lean::dec(x_25);
x_38 = lean::string_iterator_has_next(x_15);
if (x_38 == 0)
{
obj* x_40; obj* x_41; obj* x_42; obj* x_46; obj* x_47; obj* x_49; obj* x_52; obj* x_54; obj* x_55; obj* x_56; 
lean::dec(x_19);
x_40 = lean::box(0);
x_41 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_42 = l_mjoin___rarg___closed__1;
lean::inc(x_40);
lean::inc(x_42);
lean::inc(x_41);
x_46 = l_lean_parser_monad__parsec_error___at___private_4089500695__finish__comment__block__aux___main___spec__1___rarg(x_41, x_42, x_40, x_40, x_1, x_15, x_27);
x_47 = lean::cnstr_get(x_46, 0);
lean::inc(x_47);
x_49 = lean::cnstr_get(x_46, 1);
lean::inc(x_49);
lean::dec(x_46);
x_52 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_52);
x_54 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_52, x_47);
x_55 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_34, x_54);
x_56 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_17, x_55);
x_4 = x_56;
x_5 = x_49;
goto lbl_6;
}
else
{
unsigned x_57; unsigned char x_58; 
x_57 = lean::string_iterator_curr(x_15);
x_58 = l_lean_is__id__first(x_57);
if (x_58 == 0)
{
obj* x_60; obj* x_61; obj* x_63; obj* x_65; obj* x_66; obj* x_67; obj* x_70; obj* x_71; obj* x_73; obj* x_76; obj* x_78; obj* x_79; obj* x_80; 
lean::dec(x_19);
x_60 = l_char_quote__core(x_57);
x_61 = l_char_has__repr___closed__1;
lean::inc(x_61);
x_63 = lean::string_append(x_61, x_60);
lean::dec(x_60);
x_65 = lean::string_append(x_63, x_61);
x_66 = lean::box(0);
x_67 = l_mjoin___rarg___closed__1;
lean::inc(x_66);
lean::inc(x_67);
x_70 = l_lean_parser_monad__parsec_error___at___private_4089500695__finish__comment__block__aux___main___spec__1___rarg(x_65, x_67, x_66, x_66, x_1, x_15, x_27);
x_71 = lean::cnstr_get(x_70, 0);
lean::inc(x_71);
x_73 = lean::cnstr_get(x_70, 1);
lean::inc(x_73);
lean::dec(x_70);
x_76 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_76);
x_78 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_76, x_71);
x_79 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_34, x_78);
x_80 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_17, x_79);
x_4 = x_80;
x_5 = x_73;
goto lbl_6;
}
else
{
obj* x_83; obj* x_84; obj* x_85; obj* x_86; obj* x_87; 
lean::dec(x_1);
lean::dec(x_34);
x_83 = lean::string_iterator_next(x_15);
x_84 = lean::box(0);
x_85 = lean::box_uint32(x_57);
if (lean::is_scalar(x_19)) {
 x_86 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_86 = x_19;
}
lean::cnstr_set(x_86, 0, x_85);
lean::cnstr_set(x_86, 1, x_83);
lean::cnstr_set(x_86, 2, x_84);
x_87 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_17, x_86);
x_4 = x_87;
x_5 = x_27;
goto lbl_6;
}
}
}
else
{
obj* x_92; 
lean::dec(x_15);
lean::dec(x_19);
lean::dec(x_1);
lean::dec(x_34);
x_92 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_17, x_25);
x_4 = x_92;
x_5 = x_27;
goto lbl_6;
}
}
}
else
{
obj* x_94; unsigned char x_96; obj* x_97; obj* x_98; obj* x_99; 
lean::dec(x_1);
x_94 = lean::cnstr_get(x_10, 0);
lean::inc(x_94);
x_96 = lean::cnstr_get_scalar<unsigned char>(x_10, sizeof(void*)*1);
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
x_4 = x_99;
x_5 = x_12;
goto lbl_6;
}
lbl_6:
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_100; obj* x_102; obj* x_103; obj* x_105; obj* x_106; 
x_100 = lean::cnstr_get(x_4, 0);
lean::inc(x_100);
if (lean::is_shared(x_4)) {
 lean::dec(x_4);
 x_102 = lean::box(0);
} else {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_release(x_4, 1);
 lean::cnstr_release(x_4, 2);
 x_102 = x_4;
}
x_103 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_103);
if (lean::is_scalar(x_102)) {
 x_105 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_105 = x_102;
}
lean::cnstr_set(x_105, 0, x_100);
lean::cnstr_set(x_105, 1, x_2);
lean::cnstr_set(x_105, 2, x_103);
x_106 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_106, 0, x_105);
lean::cnstr_set(x_106, 1, x_5);
return x_106;
}
else
{
obj* x_108; 
lean::dec(x_2);
x_108 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_108, 0, x_4);
lean::cnstr_set(x_108, 1, x_5);
return x_108;
}
}
}
}
obj* l_lean_parser_monad__parsec_foldl__aux___main___at___private_3519775105__ident_x_27___spec__21(unsigned x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; unsigned char x_7; 
x_6 = lean::mk_nat_obj(0u);
x_7 = lean::nat_dec_eq(x_2, x_6);
lean::dec(x_6);
if (x_7 == 0)
{
obj* x_9; obj* x_11; obj* x_12; obj* x_15; obj* x_16; obj* x_18; obj* x_20; 
x_9 = lean::box_uint32(x_0);
lean::inc(x_9);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_foldl__aux___main___at___private_3519775105__ident_x_27___spec__21___lambda__1___boxed), 4, 1);
lean::closure_set(x_11, 0, x_9);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_foldl__aux___main___at___private_3519775105__ident_x_27___spec__21___lambda__2___boxed), 5, 1);
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
x_33 = lean::name_mk_string(x_1, x_21);
x_34 = l_lean_parser_monad__parsec_foldl__aux___main___at___private_3519775105__ident_x_27___spec__21(x_0, x_33, x_29, x_3, x_23, x_18);
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
obj* x_45; unsigned char x_47; 
x_45 = lean::cnstr_get(x_40, 0);
lean::inc(x_45);
x_47 = lean::cnstr_get_scalar<unsigned char>(x_40, sizeof(void*)*1);
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
obj* x_65; unsigned char x_67; obj* x_68; 
lean::dec(x_3);
lean::dec(x_2);
x_65 = lean::cnstr_get(x_16, 0);
lean::inc(x_65);
x_67 = lean::cnstr_get_scalar<unsigned char>(x_16, sizeof(void*)*1);
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
obj* l_lean_parser_monad__parsec_foldl__aux___main___at___private_3519775105__ident_x_27___spec__21___lambda__1(unsigned x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_11; 
x_4 = l_lean_parser_parsec__t_lookahead___at___private_3519775105__ident_x_27___spec__19(x_0, x_1, x_2, x_3);
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
obj* l_lean_parser_monad__parsec_foldl__aux___main___at___private_3519775105__ident_x_27___spec__21___lambda__2(unsigned x_0, unsigned x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_6; obj* x_7; obj* x_9; obj* x_11; 
lean::inc(x_2);
x_6 = l_lean_parser_monad__parsec_ch___at___private_3519775105__ident_x_27___spec__11(x_0, x_2, x_3, x_4);
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
x_17 = l_lean_parser_id__part___at___private_3519775105__ident_x_27___spec__1(x_2, x_12, x_9);
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
obj* x_26; unsigned char x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; 
lean::dec(x_2);
x_26 = lean::cnstr_get(x_7, 0);
lean::inc(x_26);
x_28 = lean::cnstr_get_scalar<unsigned char>(x_7, sizeof(void*)*1);
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
obj* l_lean_parser_monad__parsec_foldl___at___private_3519775105__ident_x_27___spec__20(obj* x_0, unsigned x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_11; obj* x_13; obj* x_14; obj* x_16; obj* x_17; 
x_5 = lean::box(0);
x_6 = lean::name_mk_string(x_5, x_0);
x_7 = lean::string_iterator_remaining(x_3);
x_8 = l_lean_parser_monad__parsec_foldl__aux___main___at___private_3519775105__ident_x_27___spec__21(x_1, x_6, x_7, x_2, x_3, x_4);
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
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_3519775105__ident_x_27___spec__4___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
unsigned x_4; obj* x_5; 
x_4 = lean::unbox_uint32(x_0);
x_5 = l_lean_parser_monad__parsec_take__while__cont___at___private_3519775105__ident_x_27___spec__4(x_4, x_1, x_2, x_3);
return x_5;
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_3519775105__ident_x_27___spec__6___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
unsigned x_4; obj* x_5; 
x_4 = lean::unbox_uint32(x_0);
x_5 = l_lean_parser_monad__parsec_take__while__cont___at___private_3519775105__ident_x_27___spec__6(x_4, x_1, x_2, x_3);
return x_5;
}
}
obj* l_lean_parser_monad__parsec_ch___at___private_3519775105__ident_x_27___spec__11___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
unsigned x_4; obj* x_5; 
x_4 = lean::unbox_uint32(x_0);
x_5 = l_lean_parser_monad__parsec_ch___at___private_3519775105__ident_x_27___spec__11(x_4, x_1, x_2, x_3);
return x_5;
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_3519775105__ident_x_27___spec__13___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
unsigned x_4; obj* x_5; 
x_4 = lean::unbox_uint32(x_0);
x_5 = l_lean_parser_monad__parsec_take__while__cont___at___private_3519775105__ident_x_27___spec__13(x_4, x_1, x_2, x_3);
return x_5;
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at___private_3519775105__ident_x_27___spec__17___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
unsigned x_4; obj* x_5; 
x_4 = lean::unbox_uint32(x_0);
x_5 = l_lean_parser_monad__parsec_take__while__cont___at___private_3519775105__ident_x_27___spec__17(x_4, x_1, x_2, x_3);
return x_5;
}
}
obj* l_lean_parser_parsec__t_lookahead___at___private_3519775105__ident_x_27___spec__19___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
unsigned x_4; obj* x_5; 
x_4 = lean::unbox_uint32(x_0);
x_5 = l_lean_parser_parsec__t_lookahead___at___private_3519775105__ident_x_27___spec__19(x_4, x_1, x_2, x_3);
return x_5;
}
}
obj* l_lean_parser_monad__parsec_foldl__aux___main___at___private_3519775105__ident_x_27___spec__21___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
unsigned x_6; obj* x_7; 
x_6 = lean::unbox_uint32(x_0);
x_7 = l_lean_parser_monad__parsec_foldl__aux___main___at___private_3519775105__ident_x_27___spec__21(x_6, x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
obj* l_lean_parser_monad__parsec_foldl__aux___main___at___private_3519775105__ident_x_27___spec__21___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
unsigned x_4; obj* x_5; 
x_4 = lean::unbox_uint32(x_0);
x_5 = l_lean_parser_monad__parsec_foldl__aux___main___at___private_3519775105__ident_x_27___spec__21___lambda__1(x_4, x_1, x_2, x_3);
return x_5;
}
}
obj* l_lean_parser_monad__parsec_foldl__aux___main___at___private_3519775105__ident_x_27___spec__21___lambda__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
unsigned x_5; unsigned x_6; obj* x_7; 
x_5 = lean::unbox_uint32(x_0);
x_6 = lean::unbox_uint32(x_1);
x_7 = l_lean_parser_monad__parsec_foldl__aux___main___at___private_3519775105__ident_x_27___spec__21___lambda__2(x_5, x_6, x_2, x_3, x_4);
return x_7;
}
}
obj* l_lean_parser_monad__parsec_foldl___at___private_3519775105__ident_x_27___spec__20___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
unsigned x_5; obj* x_6; 
x_5 = lean::unbox_uint32(x_1);
x_6 = l_lean_parser_monad__parsec_foldl___at___private_3519775105__ident_x_27___spec__20(x_0, x_5, x_2, x_3, x_4);
return x_6;
}
}
obj* l_lean_parser_parse__bin__lit(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; unsigned char x_5; obj* x_6; unsigned char x_7; obj* x_8; unsigned char x_9; obj* x_10; unsigned char x_11; unsigned x_13; 
x_3 = lean::mk_nat_obj(48u);
x_4 = lean::mk_nat_obj(55296u);
x_5 = lean::nat_dec_lt(x_3, x_4);
x_6 = lean::mk_nat_obj(98u);
x_7 = lean::nat_dec_lt(x_6, x_4);
x_8 = lean::mk_nat_obj(66u);
x_9 = lean::nat_dec_lt(x_8, x_4);
x_10 = lean::mk_nat_obj(49u);
x_11 = lean::nat_dec_lt(x_10, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
obj* x_15; unsigned char x_16; 
x_15 = lean::mk_nat_obj(57343u);
x_16 = lean::nat_dec_lt(x_15, x_3);
lean::dec(x_15);
if (x_16 == 0)
{
obj* x_19; unsigned x_20; 
lean::dec(x_3);
x_19 = lean::mk_nat_obj(0u);
x_20 = lean::unbox_uint32(x_19);
lean::dec(x_19);
x_13 = x_20;
goto lbl_14;
}
else
{
obj* x_22; unsigned char x_23; 
x_22 = lean::mk_nat_obj(1114112u);
x_23 = lean::nat_dec_lt(x_3, x_22);
lean::dec(x_22);
if (x_23 == 0)
{
obj* x_26; unsigned x_27; 
lean::dec(x_3);
x_26 = lean::mk_nat_obj(0u);
x_27 = lean::unbox_uint32(x_26);
lean::dec(x_26);
x_13 = x_27;
goto lbl_14;
}
else
{
unsigned x_29; 
x_29 = lean::unbox_uint32(x_3);
lean::dec(x_3);
x_13 = x_29;
goto lbl_14;
}
}
}
else
{
unsigned x_31; 
x_31 = lean::unbox_uint32(x_3);
lean::dec(x_3);
x_13 = x_31;
goto lbl_14;
}
lbl_14:
{
obj* x_34; unsigned x_35; 
lean::inc(x_0);
x_34 = l_lean_parser_monad__parsec_ch___at___private_3519775105__ident_x_27___spec__11(x_13, x_0, x_1, x_2);
if (x_7 == 0)
{
obj* x_37; unsigned char x_38; 
x_37 = lean::mk_nat_obj(57343u);
x_38 = lean::nat_dec_lt(x_37, x_6);
lean::dec(x_37);
if (x_38 == 0)
{
obj* x_41; unsigned x_42; 
lean::dec(x_6);
x_41 = lean::mk_nat_obj(0u);
x_42 = lean::unbox_uint32(x_41);
lean::dec(x_41);
x_35 = x_42;
goto lbl_36;
}
else
{
obj* x_44; unsigned char x_45; 
x_44 = lean::mk_nat_obj(1114112u);
x_45 = lean::nat_dec_lt(x_6, x_44);
lean::dec(x_44);
if (x_45 == 0)
{
obj* x_48; unsigned x_49; 
lean::dec(x_6);
x_48 = lean::mk_nat_obj(0u);
x_49 = lean::unbox_uint32(x_48);
lean::dec(x_48);
x_35 = x_49;
goto lbl_36;
}
else
{
unsigned x_51; 
x_51 = lean::unbox_uint32(x_6);
lean::dec(x_6);
x_35 = x_51;
goto lbl_36;
}
}
}
else
{
unsigned x_53; 
x_53 = lean::unbox_uint32(x_6);
lean::dec(x_6);
x_35 = x_53;
goto lbl_36;
}
lbl_36:
{
unsigned x_55; 
if (x_9 == 0)
{
obj* x_57; unsigned char x_58; 
x_57 = lean::mk_nat_obj(57343u);
x_58 = lean::nat_dec_lt(x_57, x_8);
lean::dec(x_57);
if (x_58 == 0)
{
obj* x_61; unsigned x_62; 
lean::dec(x_8);
x_61 = lean::mk_nat_obj(0u);
x_62 = lean::unbox_uint32(x_61);
lean::dec(x_61);
x_55 = x_62;
goto lbl_56;
}
else
{
obj* x_64; unsigned char x_65; 
x_64 = lean::mk_nat_obj(1114112u);
x_65 = lean::nat_dec_lt(x_8, x_64);
lean::dec(x_64);
if (x_65 == 0)
{
obj* x_68; unsigned x_69; 
lean::dec(x_8);
x_68 = lean::mk_nat_obj(0u);
x_69 = lean::unbox_uint32(x_68);
lean::dec(x_68);
x_55 = x_69;
goto lbl_56;
}
else
{
unsigned x_71; 
x_71 = lean::unbox_uint32(x_8);
lean::dec(x_8);
x_55 = x_71;
goto lbl_56;
}
}
}
else
{
unsigned x_73; 
x_73 = lean::unbox_uint32(x_8);
lean::dec(x_8);
x_55 = x_73;
goto lbl_56;
}
lbl_56:
{
unsigned x_75; 
if (x_11 == 0)
{
obj* x_77; unsigned char x_78; 
x_77 = lean::mk_nat_obj(57343u);
x_78 = lean::nat_dec_lt(x_77, x_10);
lean::dec(x_77);
if (x_78 == 0)
{
obj* x_81; unsigned x_82; 
lean::dec(x_10);
x_81 = lean::mk_nat_obj(0u);
x_82 = lean::unbox_uint32(x_81);
lean::dec(x_81);
x_75 = x_82;
goto lbl_76;
}
else
{
obj* x_84; unsigned char x_85; 
x_84 = lean::mk_nat_obj(1114112u);
x_85 = lean::nat_dec_lt(x_10, x_84);
lean::dec(x_84);
if (x_85 == 0)
{
obj* x_88; unsigned x_89; 
lean::dec(x_10);
x_88 = lean::mk_nat_obj(0u);
x_89 = lean::unbox_uint32(x_88);
lean::dec(x_88);
x_75 = x_89;
goto lbl_76;
}
else
{
unsigned x_91; 
x_91 = lean::unbox_uint32(x_10);
lean::dec(x_10);
x_75 = x_91;
goto lbl_76;
}
}
}
else
{
unsigned x_93; 
x_93 = lean::unbox_uint32(x_10);
lean::dec(x_10);
x_75 = x_93;
goto lbl_76;
}
lbl_76:
{
obj* x_95; obj* x_96; obj* x_98; obj* x_100; 
x_98 = lean::cnstr_get(x_34, 0);
lean::inc(x_98);
x_100 = lean::cnstr_get(x_34, 1);
lean::inc(x_100);
lean::dec(x_34);
if (lean::obj_tag(x_98) == 0)
{
obj* x_103; obj* x_105; obj* x_110; obj* x_111; obj* x_113; 
x_103 = lean::cnstr_get(x_98, 1);
lean::inc(x_103);
x_105 = lean::cnstr_get(x_98, 2);
lean::inc(x_105);
lean::dec(x_98);
lean::inc(x_103);
lean::inc(x_0);
x_110 = l_lean_parser_monad__parsec_ch___at___private_3519775105__ident_x_27___spec__11(x_35, x_0, x_103, x_100);
x_111 = lean::cnstr_get(x_110, 0);
lean::inc(x_111);
x_113 = lean::cnstr_get(x_110, 1);
lean::inc(x_113);
lean::dec(x_110);
if (lean::obj_tag(x_111) == 0)
{
obj* x_117; 
lean::dec(x_103);
x_117 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_105, x_111);
x_95 = x_117;
x_96 = x_113;
goto lbl_97;
}
else
{
obj* x_118; unsigned char x_120; 
x_118 = lean::cnstr_get(x_111, 0);
lean::inc(x_118);
x_120 = lean::cnstr_get_scalar<unsigned char>(x_111, sizeof(void*)*1);
if (x_120 == 0)
{
obj* x_123; obj* x_124; obj* x_126; obj* x_129; obj* x_130; 
lean::dec(x_111);
lean::inc(x_0);
x_123 = l_lean_parser_monad__parsec_ch___at___private_3519775105__ident_x_27___spec__11(x_55, x_0, x_103, x_113);
x_124 = lean::cnstr_get(x_123, 0);
lean::inc(x_124);
x_126 = lean::cnstr_get(x_123, 1);
lean::inc(x_126);
lean::dec(x_123);
x_129 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_118, x_124);
x_130 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_105, x_129);
x_95 = x_130;
x_96 = x_126;
goto lbl_97;
}
else
{
obj* x_133; 
lean::dec(x_103);
lean::dec(x_118);
x_133 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_105, x_111);
x_95 = x_133;
x_96 = x_113;
goto lbl_97;
}
}
}
else
{
obj* x_134; unsigned char x_136; obj* x_137; obj* x_138; obj* x_139; 
x_134 = lean::cnstr_get(x_98, 0);
lean::inc(x_134);
x_136 = lean::cnstr_get_scalar<unsigned char>(x_98, sizeof(void*)*1);
if (lean::is_shared(x_98)) {
 lean::dec(x_98);
 x_137 = lean::box(0);
} else {
 lean::cnstr_release(x_98, 0);
 x_137 = x_98;
}
if (lean::is_scalar(x_137)) {
 x_138 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_138 = x_137;
}
lean::cnstr_set(x_138, 0, x_134);
lean::cnstr_set_scalar(x_138, sizeof(void*)*1, x_136);
x_139 = x_138;
x_95 = x_139;
x_96 = x_100;
goto lbl_97;
}
lbl_97:
{
if (lean::obj_tag(x_95) == 0)
{
obj* x_140; obj* x_142; obj* x_145; obj* x_146; obj* x_147; obj* x_149; obj* x_151; obj* x_152; obj* x_154; obj* x_155; obj* x_156; 
x_140 = lean::cnstr_get(x_95, 1);
lean::inc(x_140);
x_142 = lean::cnstr_get(x_95, 2);
lean::inc(x_142);
lean::dec(x_95);
x_145 = lean::string_iterator_remaining(x_140);
x_146 = l_lean_parser_monad__parsec_many1__aux_x_27___main___at_lean_parser_parse__bin__lit___spec__2(x_13, x_75, x_145, x_0, x_140, x_96);
x_147 = lean::cnstr_get(x_146, 0);
lean::inc(x_147);
x_149 = lean::cnstr_get(x_146, 1);
lean::inc(x_149);
if (lean::is_shared(x_146)) {
 lean::dec(x_146);
 x_151 = lean::box(0);
} else {
 lean::cnstr_release(x_146, 0);
 lean::cnstr_release(x_146, 1);
 x_151 = x_146;
}
x_152 = l_lean_parser_finish__comment__block___closed__2;
lean::inc(x_152);
x_154 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_152, x_147);
x_155 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_142, x_154);
if (lean::is_scalar(x_151)) {
 x_156 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_156 = x_151;
}
lean::cnstr_set(x_156, 0, x_155);
lean::cnstr_set(x_156, 1, x_149);
return x_156;
}
else
{
obj* x_158; unsigned char x_160; obj* x_161; obj* x_162; obj* x_163; obj* x_164; 
lean::dec(x_0);
x_158 = lean::cnstr_get(x_95, 0);
lean::inc(x_158);
x_160 = lean::cnstr_get_scalar<unsigned char>(x_95, sizeof(void*)*1);
if (lean::is_shared(x_95)) {
 lean::dec(x_95);
 x_161 = lean::box(0);
} else {
 lean::cnstr_release(x_95, 0);
 x_161 = x_95;
}
if (lean::is_scalar(x_161)) {
 x_162 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_162 = x_161;
}
lean::cnstr_set(x_162, 0, x_158);
lean::cnstr_set_scalar(x_162, sizeof(void*)*1, x_160);
x_163 = x_162;
x_164 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_164, 0, x_163);
lean::cnstr_set(x_164, 1, x_96);
return x_164;
}
}
}
}
}
}
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
obj* x_17; unsigned char x_19; 
x_17 = lean::cnstr_get(x_8, 0);
lean::inc(x_17);
x_19 = lean::cnstr_get_scalar<unsigned char>(x_8, sizeof(void*)*1);
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
obj* l_lean_parser_monad__parsec_many1__aux_x_27___main___at_lean_parser_parse__bin__lit___spec__2(unsigned x_0, unsigned x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; unsigned char x_11; 
x_6 = lean::box_uint32(x_0);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_ch___at___private_3519775105__ident_x_27___spec__11___boxed), 4, 1);
lean::closure_set(x_7, 0, x_6);
x_8 = lean::box_uint32(x_1);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_ch___at___private_3519775105__ident_x_27___spec__11___boxed), 4, 1);
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
obj* x_40; unsigned char x_42; 
x_40 = lean::cnstr_get(x_31, 0);
lean::inc(x_40);
x_42 = lean::cnstr_get_scalar<unsigned char>(x_31, sizeof(void*)*1);
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
obj* x_62; unsigned char x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; 
lean::dec(x_3);
lean::dec(x_2);
x_62 = lean::cnstr_get(x_15, 0);
lean::inc(x_62);
x_64 = lean::cnstr_get_scalar<unsigned char>(x_15, sizeof(void*)*1);
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
obj* x_87; unsigned char x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; 
x_87 = lean::cnstr_get(x_71, 0);
lean::inc(x_87);
x_89 = lean::cnstr_get_scalar<unsigned char>(x_71, sizeof(void*)*1);
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
obj* l_lean_parser_monad__parsec_many1__aux_x_27___main___at_lean_parser_parse__bin__lit___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
unsigned x_6; unsigned x_7; obj* x_8; 
x_6 = lean::unbox_uint32(x_0);
x_7 = lean::unbox_uint32(x_1);
x_8 = l_lean_parser_monad__parsec_many1__aux_x_27___main___at_lean_parser_parse__bin__lit___spec__2(x_6, x_7, x_2, x_3, x_4, x_5);
return x_8;
}
}
obj* l_lean_parser_parse__oct__lit(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; unsigned char x_5; obj* x_6; unsigned char x_7; obj* x_8; unsigned char x_9; unsigned x_11; 
x_3 = lean::mk_nat_obj(48u);
x_4 = lean::mk_nat_obj(55296u);
x_5 = lean::nat_dec_lt(x_3, x_4);
x_6 = lean::mk_nat_obj(111u);
x_7 = lean::nat_dec_lt(x_6, x_4);
x_8 = lean::mk_nat_obj(79u);
x_9 = lean::nat_dec_lt(x_8, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
obj* x_13; unsigned char x_14; 
x_13 = lean::mk_nat_obj(57343u);
x_14 = lean::nat_dec_lt(x_13, x_3);
lean::dec(x_13);
if (x_14 == 0)
{
obj* x_17; unsigned x_18; 
lean::dec(x_3);
x_17 = lean::mk_nat_obj(0u);
x_18 = lean::unbox_uint32(x_17);
lean::dec(x_17);
x_11 = x_18;
goto lbl_12;
}
else
{
obj* x_20; unsigned char x_21; 
x_20 = lean::mk_nat_obj(1114112u);
x_21 = lean::nat_dec_lt(x_3, x_20);
lean::dec(x_20);
if (x_21 == 0)
{
obj* x_24; unsigned x_25; 
lean::dec(x_3);
x_24 = lean::mk_nat_obj(0u);
x_25 = lean::unbox_uint32(x_24);
lean::dec(x_24);
x_11 = x_25;
goto lbl_12;
}
else
{
unsigned x_27; 
x_27 = lean::unbox_uint32(x_3);
lean::dec(x_3);
x_11 = x_27;
goto lbl_12;
}
}
}
else
{
unsigned x_29; 
x_29 = lean::unbox_uint32(x_3);
lean::dec(x_3);
x_11 = x_29;
goto lbl_12;
}
lbl_12:
{
obj* x_31; obj* x_32; obj* x_35; unsigned x_36; 
lean::inc(x_0);
x_35 = l_lean_parser_monad__parsec_ch___at___private_3519775105__ident_x_27___spec__11(x_11, x_0, x_1, x_2);
if (x_7 == 0)
{
obj* x_38; unsigned char x_39; 
x_38 = lean::mk_nat_obj(57343u);
x_39 = lean::nat_dec_lt(x_38, x_6);
lean::dec(x_38);
if (x_39 == 0)
{
obj* x_42; unsigned x_43; 
lean::dec(x_6);
x_42 = lean::mk_nat_obj(0u);
x_43 = lean::unbox_uint32(x_42);
lean::dec(x_42);
x_36 = x_43;
goto lbl_37;
}
else
{
obj* x_45; unsigned char x_46; 
x_45 = lean::mk_nat_obj(1114112u);
x_46 = lean::nat_dec_lt(x_6, x_45);
lean::dec(x_45);
if (x_46 == 0)
{
obj* x_49; unsigned x_50; 
lean::dec(x_6);
x_49 = lean::mk_nat_obj(0u);
x_50 = lean::unbox_uint32(x_49);
lean::dec(x_49);
x_36 = x_50;
goto lbl_37;
}
else
{
unsigned x_52; 
x_52 = lean::unbox_uint32(x_6);
lean::dec(x_6);
x_36 = x_52;
goto lbl_37;
}
}
}
else
{
unsigned x_54; 
x_54 = lean::unbox_uint32(x_6);
lean::dec(x_6);
x_36 = x_54;
goto lbl_37;
}
lbl_33:
{
if (lean::obj_tag(x_31) == 0)
{
obj* x_56; obj* x_58; obj* x_61; obj* x_62; obj* x_64; obj* x_66; obj* x_67; obj* x_68; 
x_56 = lean::cnstr_get(x_31, 1);
lean::inc(x_56);
x_58 = lean::cnstr_get(x_31, 2);
lean::inc(x_58);
lean::dec(x_31);
x_61 = l_lean_parser_monad__parsec_take__while1___at_lean_parser_parse__oct__lit___spec__1(x_11, x_0, x_56, x_32);
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
obj* x_70; unsigned char x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; 
lean::dec(x_0);
x_70 = lean::cnstr_get(x_31, 0);
lean::inc(x_70);
x_72 = lean::cnstr_get_scalar<unsigned char>(x_31, sizeof(void*)*1);
if (lean::is_shared(x_31)) {
 lean::dec(x_31);
 x_73 = lean::box(0);
} else {
 lean::cnstr_release(x_31, 0);
 x_73 = x_31;
}
if (lean::is_scalar(x_73)) {
 x_74 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_74 = x_73;
}
lean::cnstr_set(x_74, 0, x_70);
lean::cnstr_set_scalar(x_74, sizeof(void*)*1, x_72);
x_75 = x_74;
x_76 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_76, 0, x_75);
lean::cnstr_set(x_76, 1, x_32);
return x_76;
}
}
lbl_37:
{
unsigned x_77; obj* x_78; obj* x_79; 
if (x_9 == 0)
{
obj* x_81; unsigned char x_82; 
x_81 = lean::mk_nat_obj(57343u);
x_82 = lean::nat_dec_lt(x_81, x_8);
lean::dec(x_81);
if (x_82 == 0)
{
obj* x_85; obj* x_87; obj* x_90; unsigned x_91; 
lean::dec(x_8);
x_85 = lean::cnstr_get(x_35, 0);
lean::inc(x_85);
x_87 = lean::cnstr_get(x_35, 1);
lean::inc(x_87);
lean::dec(x_35);
x_90 = lean::mk_nat_obj(0u);
x_91 = lean::unbox_uint32(x_90);
lean::dec(x_90);
x_77 = x_91;
x_78 = x_85;
x_79 = x_87;
goto lbl_80;
}
else
{
obj* x_93; unsigned char x_94; 
x_93 = lean::mk_nat_obj(1114112u);
x_94 = lean::nat_dec_lt(x_8, x_93);
lean::dec(x_93);
if (x_94 == 0)
{
obj* x_97; obj* x_99; obj* x_102; unsigned x_103; 
lean::dec(x_8);
x_97 = lean::cnstr_get(x_35, 0);
lean::inc(x_97);
x_99 = lean::cnstr_get(x_35, 1);
lean::inc(x_99);
lean::dec(x_35);
x_102 = lean::mk_nat_obj(0u);
x_103 = lean::unbox_uint32(x_102);
lean::dec(x_102);
x_77 = x_103;
x_78 = x_97;
x_79 = x_99;
goto lbl_80;
}
else
{
obj* x_105; obj* x_107; unsigned x_110; 
x_105 = lean::cnstr_get(x_35, 0);
lean::inc(x_105);
x_107 = lean::cnstr_get(x_35, 1);
lean::inc(x_107);
lean::dec(x_35);
x_110 = lean::unbox_uint32(x_8);
lean::dec(x_8);
x_77 = x_110;
x_78 = x_105;
x_79 = x_107;
goto lbl_80;
}
}
}
else
{
obj* x_112; obj* x_114; unsigned x_117; 
x_112 = lean::cnstr_get(x_35, 0);
lean::inc(x_112);
x_114 = lean::cnstr_get(x_35, 1);
lean::inc(x_114);
lean::dec(x_35);
x_117 = lean::unbox_uint32(x_8);
lean::dec(x_8);
x_77 = x_117;
x_78 = x_112;
x_79 = x_114;
goto lbl_80;
}
lbl_80:
{
if (lean::obj_tag(x_78) == 0)
{
obj* x_119; obj* x_121; obj* x_126; obj* x_127; obj* x_129; 
x_119 = lean::cnstr_get(x_78, 1);
lean::inc(x_119);
x_121 = lean::cnstr_get(x_78, 2);
lean::inc(x_121);
lean::dec(x_78);
lean::inc(x_119);
lean::inc(x_0);
x_126 = l_lean_parser_monad__parsec_ch___at___private_3519775105__ident_x_27___spec__11(x_36, x_0, x_119, x_79);
x_127 = lean::cnstr_get(x_126, 0);
lean::inc(x_127);
x_129 = lean::cnstr_get(x_126, 1);
lean::inc(x_129);
lean::dec(x_126);
if (lean::obj_tag(x_127) == 0)
{
obj* x_133; 
lean::dec(x_119);
x_133 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_121, x_127);
x_31 = x_133;
x_32 = x_129;
goto lbl_33;
}
else
{
obj* x_134; unsigned char x_136; 
x_134 = lean::cnstr_get(x_127, 0);
lean::inc(x_134);
x_136 = lean::cnstr_get_scalar<unsigned char>(x_127, sizeof(void*)*1);
if (x_136 == 0)
{
obj* x_139; obj* x_140; obj* x_142; obj* x_145; obj* x_146; 
lean::dec(x_127);
lean::inc(x_0);
x_139 = l_lean_parser_monad__parsec_ch___at___private_3519775105__ident_x_27___spec__11(x_77, x_0, x_119, x_129);
x_140 = lean::cnstr_get(x_139, 0);
lean::inc(x_140);
x_142 = lean::cnstr_get(x_139, 1);
lean::inc(x_142);
lean::dec(x_139);
x_145 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_134, x_140);
x_146 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_121, x_145);
x_31 = x_146;
x_32 = x_142;
goto lbl_33;
}
else
{
obj* x_149; 
lean::dec(x_119);
lean::dec(x_134);
x_149 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_121, x_127);
x_31 = x_149;
x_32 = x_129;
goto lbl_33;
}
}
}
else
{
obj* x_150; unsigned char x_152; obj* x_153; obj* x_154; obj* x_155; 
x_150 = lean::cnstr_get(x_78, 0);
lean::inc(x_150);
x_152 = lean::cnstr_get_scalar<unsigned char>(x_78, sizeof(void*)*1);
if (lean::is_shared(x_78)) {
 lean::dec(x_78);
 x_153 = lean::box(0);
} else {
 lean::cnstr_release(x_78, 0);
 x_153 = x_78;
}
if (lean::is_scalar(x_153)) {
 x_154 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_154 = x_153;
}
lean::cnstr_set(x_154, 0, x_150);
lean::cnstr_set_scalar(x_154, sizeof(void*)*1, x_152);
x_155 = x_154;
x_31 = x_155;
x_32 = x_79;
goto lbl_33;
}
}
}
}
}
}
obj* l___private_31565857__take__while__aux___main___at_lean_parser_parse__oct__lit___spec__3(unsigned x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; unsigned char x_5; 
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::nat_dec_eq(x_1, x_4);
if (x_5 == 0)
{
unsigned char x_6; 
x_6 = lean::string_iterator_has_next(x_3);
if (x_6 == 0)
{
obj* x_9; 
lean::dec(x_4);
lean::dec(x_1);
x_9 = l___private_2142412293__mk__string__result___rarg(x_2, x_3);
return x_9;
}
else
{
obj* x_10; obj* x_11; unsigned x_14; obj* x_15; unsigned char x_17; obj* x_19; obj* x_20; unsigned char x_21; 
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_sub(x_1, x_10);
lean::dec(x_10);
lean::dec(x_1);
x_14 = lean::string_iterator_curr(x_3);
x_19 = lean::box_uint32(x_0);
x_20 = lean::box_uint32(x_14);
x_21 = lean::nat_dec_le(x_19, x_20);
lean::dec(x_20);
lean::dec(x_19);
if (x_21 == 0)
{
obj* x_26; 
lean::dec(x_11);
lean::dec(x_4);
x_26 = l___private_2142412293__mk__string__result___rarg(x_2, x_3);
return x_26;
}
else
{
unsigned char x_27; 
x_27 = 1;
x_17 = x_27;
goto lbl_18;
}
lbl_16:
{
obj* x_29; obj* x_30; 
lean::dec(x_15);
x_29 = lean::string_push(x_2, x_14);
x_30 = lean::string_iterator_next(x_3);
x_1 = x_11;
x_2 = x_29;
x_3 = x_30;
goto _start;
}
lbl_18:
{
obj* x_32; obj* x_33; unsigned char x_34; 
x_32 = lean::mk_nat_obj(56u);
x_33 = lean::mk_nat_obj(55296u);
x_34 = lean::nat_dec_lt(x_32, x_33);
lean::dec(x_33);
if (x_34 == 0)
{
obj* x_36; unsigned char x_37; 
x_36 = lean::mk_nat_obj(57343u);
x_37 = lean::nat_dec_lt(x_36, x_32);
lean::dec(x_36);
if (x_37 == 0)
{
obj* x_40; unsigned char x_41; 
lean::dec(x_32);
x_40 = lean::box_uint32(x_14);
x_41 = lean::nat_dec_lt(x_40, x_4);
lean::dec(x_4);
lean::dec(x_40);
if (x_41 == 0)
{
obj* x_45; 
lean::dec(x_11);
x_45 = l___private_2142412293__mk__string__result___rarg(x_2, x_3);
return x_45;
}
else
{
if (x_17 == 0)
{
obj* x_47; 
lean::dec(x_11);
x_47 = l___private_2142412293__mk__string__result___rarg(x_2, x_3);
return x_47;
}
else
{
obj* x_48; 
x_48 = lean::box(0);
x_15 = x_48;
goto lbl_16;
}
}
}
else
{
obj* x_49; unsigned char x_50; 
x_49 = lean::mk_nat_obj(1114112u);
x_50 = lean::nat_dec_lt(x_32, x_49);
lean::dec(x_49);
if (x_50 == 0)
{
obj* x_53; unsigned char x_54; 
lean::dec(x_32);
x_53 = lean::box_uint32(x_14);
x_54 = lean::nat_dec_lt(x_53, x_4);
lean::dec(x_4);
lean::dec(x_53);
if (x_54 == 0)
{
obj* x_58; 
lean::dec(x_11);
x_58 = l___private_2142412293__mk__string__result___rarg(x_2, x_3);
return x_58;
}
else
{
if (x_17 == 0)
{
obj* x_60; 
lean::dec(x_11);
x_60 = l___private_2142412293__mk__string__result___rarg(x_2, x_3);
return x_60;
}
else
{
obj* x_61; 
x_61 = lean::box(0);
x_15 = x_61;
goto lbl_16;
}
}
}
else
{
obj* x_63; unsigned char x_64; 
lean::dec(x_4);
x_63 = lean::box_uint32(x_14);
x_64 = lean::nat_dec_lt(x_63, x_32);
lean::dec(x_32);
lean::dec(x_63);
if (x_64 == 0)
{
obj* x_68; 
lean::dec(x_11);
x_68 = l___private_2142412293__mk__string__result___rarg(x_2, x_3);
return x_68;
}
else
{
if (x_17 == 0)
{
obj* x_70; 
lean::dec(x_11);
x_70 = l___private_2142412293__mk__string__result___rarg(x_2, x_3);
return x_70;
}
else
{
obj* x_71; 
x_71 = lean::box(0);
x_15 = x_71;
goto lbl_16;
}
}
}
}
}
else
{
obj* x_73; unsigned char x_74; 
lean::dec(x_4);
x_73 = lean::box_uint32(x_14);
x_74 = lean::nat_dec_lt(x_73, x_32);
lean::dec(x_32);
lean::dec(x_73);
if (x_74 == 0)
{
obj* x_78; 
lean::dec(x_11);
x_78 = l___private_2142412293__mk__string__result___rarg(x_2, x_3);
return x_78;
}
else
{
if (x_17 == 0)
{
obj* x_80; 
lean::dec(x_11);
x_80 = l___private_2142412293__mk__string__result___rarg(x_2, x_3);
return x_80;
}
else
{
obj* x_81; 
x_81 = lean::box(0);
x_15 = x_81;
goto lbl_16;
}
}
}
}
}
}
else
{
obj* x_84; 
lean::dec(x_4);
lean::dec(x_1);
x_84 = l___private_2142412293__mk__string__result___rarg(x_2, x_3);
return x_84;
}
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_parse__oct__lit___spec__2(unsigned x_0, unsigned x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
lean::dec(x_2);
x_6 = l_string_join___closed__1;
lean::inc(x_6);
x_8 = lean::string_push(x_6, x_1);
x_9 = lean::string_iterator_remaining(x_3);
x_10 = l___private_31565857__take__while__aux___main___at_lean_parser_parse__oct__lit___spec__3(x_0, x_9, x_8, x_3);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_4);
return x_11;
}
}
obj* l___private_31565857__take__while__aux___main___at_lean_parser_parse__oct__lit___spec__5(unsigned x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; unsigned char x_5; 
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::nat_dec_eq(x_1, x_4);
if (x_5 == 0)
{
unsigned char x_6; 
x_6 = lean::string_iterator_has_next(x_3);
if (x_6 == 0)
{
obj* x_9; 
lean::dec(x_4);
lean::dec(x_1);
x_9 = l___private_2142412293__mk__string__result___rarg(x_2, x_3);
return x_9;
}
else
{
obj* x_10; obj* x_11; unsigned x_14; obj* x_15; unsigned char x_17; obj* x_19; obj* x_20; unsigned char x_21; 
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_sub(x_1, x_10);
lean::dec(x_10);
lean::dec(x_1);
x_14 = lean::string_iterator_curr(x_3);
x_19 = lean::box_uint32(x_0);
x_20 = lean::box_uint32(x_14);
x_21 = lean::nat_dec_le(x_19, x_20);
lean::dec(x_20);
lean::dec(x_19);
if (x_21 == 0)
{
obj* x_26; 
lean::dec(x_11);
lean::dec(x_4);
x_26 = l___private_2142412293__mk__string__result___rarg(x_2, x_3);
return x_26;
}
else
{
unsigned char x_27; 
x_27 = 1;
x_17 = x_27;
goto lbl_18;
}
lbl_16:
{
obj* x_29; obj* x_30; 
lean::dec(x_15);
x_29 = lean::string_push(x_2, x_14);
x_30 = lean::string_iterator_next(x_3);
x_1 = x_11;
x_2 = x_29;
x_3 = x_30;
goto _start;
}
lbl_18:
{
obj* x_32; obj* x_33; unsigned char x_34; 
x_32 = lean::mk_nat_obj(56u);
x_33 = lean::mk_nat_obj(55296u);
x_34 = lean::nat_dec_lt(x_32, x_33);
lean::dec(x_33);
if (x_34 == 0)
{
obj* x_36; unsigned char x_37; 
x_36 = lean::mk_nat_obj(57343u);
x_37 = lean::nat_dec_lt(x_36, x_32);
lean::dec(x_36);
if (x_37 == 0)
{
obj* x_40; unsigned char x_41; 
lean::dec(x_32);
x_40 = lean::box_uint32(x_14);
x_41 = lean::nat_dec_lt(x_40, x_4);
lean::dec(x_4);
lean::dec(x_40);
if (x_41 == 0)
{
obj* x_45; 
lean::dec(x_11);
x_45 = l___private_2142412293__mk__string__result___rarg(x_2, x_3);
return x_45;
}
else
{
if (x_17 == 0)
{
obj* x_47; 
lean::dec(x_11);
x_47 = l___private_2142412293__mk__string__result___rarg(x_2, x_3);
return x_47;
}
else
{
obj* x_48; 
x_48 = lean::box(0);
x_15 = x_48;
goto lbl_16;
}
}
}
else
{
obj* x_49; unsigned char x_50; 
x_49 = lean::mk_nat_obj(1114112u);
x_50 = lean::nat_dec_lt(x_32, x_49);
lean::dec(x_49);
if (x_50 == 0)
{
obj* x_53; unsigned char x_54; 
lean::dec(x_32);
x_53 = lean::box_uint32(x_14);
x_54 = lean::nat_dec_lt(x_53, x_4);
lean::dec(x_4);
lean::dec(x_53);
if (x_54 == 0)
{
obj* x_58; 
lean::dec(x_11);
x_58 = l___private_2142412293__mk__string__result___rarg(x_2, x_3);
return x_58;
}
else
{
if (x_17 == 0)
{
obj* x_60; 
lean::dec(x_11);
x_60 = l___private_2142412293__mk__string__result___rarg(x_2, x_3);
return x_60;
}
else
{
obj* x_61; 
x_61 = lean::box(0);
x_15 = x_61;
goto lbl_16;
}
}
}
else
{
obj* x_63; unsigned char x_64; 
lean::dec(x_4);
x_63 = lean::box_uint32(x_14);
x_64 = lean::nat_dec_lt(x_63, x_32);
lean::dec(x_32);
lean::dec(x_63);
if (x_64 == 0)
{
obj* x_68; 
lean::dec(x_11);
x_68 = l___private_2142412293__mk__string__result___rarg(x_2, x_3);
return x_68;
}
else
{
if (x_17 == 0)
{
obj* x_70; 
lean::dec(x_11);
x_70 = l___private_2142412293__mk__string__result___rarg(x_2, x_3);
return x_70;
}
else
{
obj* x_71; 
x_71 = lean::box(0);
x_15 = x_71;
goto lbl_16;
}
}
}
}
}
else
{
obj* x_73; unsigned char x_74; 
lean::dec(x_4);
x_73 = lean::box_uint32(x_14);
x_74 = lean::nat_dec_lt(x_73, x_32);
lean::dec(x_32);
lean::dec(x_73);
if (x_74 == 0)
{
obj* x_78; 
lean::dec(x_11);
x_78 = l___private_2142412293__mk__string__result___rarg(x_2, x_3);
return x_78;
}
else
{
if (x_17 == 0)
{
obj* x_80; 
lean::dec(x_11);
x_80 = l___private_2142412293__mk__string__result___rarg(x_2, x_3);
return x_80;
}
else
{
obj* x_81; 
x_81 = lean::box(0);
x_15 = x_81;
goto lbl_16;
}
}
}
}
}
}
else
{
obj* x_84; 
lean::dec(x_4);
lean::dec(x_1);
x_84 = l___private_2142412293__mk__string__result___rarg(x_2, x_3);
return x_84;
}
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_parse__oct__lit___spec__4(unsigned x_0, unsigned x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
lean::dec(x_2);
x_6 = l_string_join___closed__1;
lean::inc(x_6);
x_8 = lean::string_push(x_6, x_1);
x_9 = lean::string_iterator_remaining(x_3);
x_10 = l___private_31565857__take__while__aux___main___at_lean_parser_parse__oct__lit___spec__5(x_0, x_9, x_8, x_3);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_4);
return x_11;
}
}
obj* l___private_31565857__take__while__aux___main___at_lean_parser_parse__oct__lit___spec__7(unsigned x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; unsigned char x_5; 
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::nat_dec_eq(x_1, x_4);
if (x_5 == 0)
{
unsigned char x_6; 
x_6 = lean::string_iterator_has_next(x_3);
if (x_6 == 0)
{
obj* x_9; 
lean::dec(x_4);
lean::dec(x_1);
x_9 = l___private_2142412293__mk__string__result___rarg(x_2, x_3);
return x_9;
}
else
{
obj* x_10; obj* x_11; unsigned x_14; obj* x_15; unsigned char x_17; obj* x_19; obj* x_20; unsigned char x_21; 
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_sub(x_1, x_10);
lean::dec(x_10);
lean::dec(x_1);
x_14 = lean::string_iterator_curr(x_3);
x_19 = lean::box_uint32(x_0);
x_20 = lean::box_uint32(x_14);
x_21 = lean::nat_dec_le(x_19, x_20);
lean::dec(x_20);
lean::dec(x_19);
if (x_21 == 0)
{
obj* x_26; 
lean::dec(x_11);
lean::dec(x_4);
x_26 = l___private_2142412293__mk__string__result___rarg(x_2, x_3);
return x_26;
}
else
{
unsigned char x_27; 
x_27 = 1;
x_17 = x_27;
goto lbl_18;
}
lbl_16:
{
obj* x_29; obj* x_30; 
lean::dec(x_15);
x_29 = lean::string_push(x_2, x_14);
x_30 = lean::string_iterator_next(x_3);
x_1 = x_11;
x_2 = x_29;
x_3 = x_30;
goto _start;
}
lbl_18:
{
obj* x_32; obj* x_33; unsigned char x_34; 
x_32 = lean::mk_nat_obj(56u);
x_33 = lean::mk_nat_obj(55296u);
x_34 = lean::nat_dec_lt(x_32, x_33);
lean::dec(x_33);
if (x_34 == 0)
{
obj* x_36; unsigned char x_37; 
x_36 = lean::mk_nat_obj(57343u);
x_37 = lean::nat_dec_lt(x_36, x_32);
lean::dec(x_36);
if (x_37 == 0)
{
obj* x_40; unsigned char x_41; 
lean::dec(x_32);
x_40 = lean::box_uint32(x_14);
x_41 = lean::nat_dec_lt(x_40, x_4);
lean::dec(x_4);
lean::dec(x_40);
if (x_41 == 0)
{
obj* x_45; 
lean::dec(x_11);
x_45 = l___private_2142412293__mk__string__result___rarg(x_2, x_3);
return x_45;
}
else
{
if (x_17 == 0)
{
obj* x_47; 
lean::dec(x_11);
x_47 = l___private_2142412293__mk__string__result___rarg(x_2, x_3);
return x_47;
}
else
{
obj* x_48; 
x_48 = lean::box(0);
x_15 = x_48;
goto lbl_16;
}
}
}
else
{
obj* x_49; unsigned char x_50; 
x_49 = lean::mk_nat_obj(1114112u);
x_50 = lean::nat_dec_lt(x_32, x_49);
lean::dec(x_49);
if (x_50 == 0)
{
obj* x_53; unsigned char x_54; 
lean::dec(x_32);
x_53 = lean::box_uint32(x_14);
x_54 = lean::nat_dec_lt(x_53, x_4);
lean::dec(x_4);
lean::dec(x_53);
if (x_54 == 0)
{
obj* x_58; 
lean::dec(x_11);
x_58 = l___private_2142412293__mk__string__result___rarg(x_2, x_3);
return x_58;
}
else
{
if (x_17 == 0)
{
obj* x_60; 
lean::dec(x_11);
x_60 = l___private_2142412293__mk__string__result___rarg(x_2, x_3);
return x_60;
}
else
{
obj* x_61; 
x_61 = lean::box(0);
x_15 = x_61;
goto lbl_16;
}
}
}
else
{
obj* x_63; unsigned char x_64; 
lean::dec(x_4);
x_63 = lean::box_uint32(x_14);
x_64 = lean::nat_dec_lt(x_63, x_32);
lean::dec(x_32);
lean::dec(x_63);
if (x_64 == 0)
{
obj* x_68; 
lean::dec(x_11);
x_68 = l___private_2142412293__mk__string__result___rarg(x_2, x_3);
return x_68;
}
else
{
if (x_17 == 0)
{
obj* x_70; 
lean::dec(x_11);
x_70 = l___private_2142412293__mk__string__result___rarg(x_2, x_3);
return x_70;
}
else
{
obj* x_71; 
x_71 = lean::box(0);
x_15 = x_71;
goto lbl_16;
}
}
}
}
}
else
{
obj* x_73; unsigned char x_74; 
lean::dec(x_4);
x_73 = lean::box_uint32(x_14);
x_74 = lean::nat_dec_lt(x_73, x_32);
lean::dec(x_32);
lean::dec(x_73);
if (x_74 == 0)
{
obj* x_78; 
lean::dec(x_11);
x_78 = l___private_2142412293__mk__string__result___rarg(x_2, x_3);
return x_78;
}
else
{
if (x_17 == 0)
{
obj* x_80; 
lean::dec(x_11);
x_80 = l___private_2142412293__mk__string__result___rarg(x_2, x_3);
return x_80;
}
else
{
obj* x_81; 
x_81 = lean::box(0);
x_15 = x_81;
goto lbl_16;
}
}
}
}
}
}
else
{
obj* x_84; 
lean::dec(x_4);
lean::dec(x_1);
x_84 = l___private_2142412293__mk__string__result___rarg(x_2, x_3);
return x_84;
}
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_parse__oct__lit___spec__6(unsigned x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
unsigned x_6; obj* x_8; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
lean::dec(x_2);
x_6 = lean::string_iterator_curr(x_1);
lean::dec(x_1);
x_8 = l_string_join___closed__1;
lean::inc(x_8);
x_10 = lean::string_push(x_8, x_6);
x_11 = lean::string_iterator_remaining(x_3);
x_12 = l___private_31565857__take__while__aux___main___at_lean_parser_parse__oct__lit___spec__7(x_0, x_11, x_10, x_3);
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_4);
return x_13;
}
}
obj* l_lean_parser_monad__parsec_take__while1___at_lean_parser_parse__oct__lit___spec__1(unsigned x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
unsigned char x_4; 
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
x_12 = l_lean_parser_monad__parsec_error___at___private_4089500695__finish__comment__block__aux___main___spec__1___rarg(x_6, x_7, x_5, x_5, x_1, x_2, x_3);
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
obj* x_21; obj* x_23; obj* x_25; unsigned x_28; obj* x_30; obj* x_31; obj* x_33; obj* x_36; obj* x_37; 
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
obj* x_39; unsigned char x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; 
lean::dec(x_1);
x_39 = lean::cnstr_get(x_20, 0);
lean::inc(x_39);
x_41 = lean::cnstr_get_scalar<unsigned char>(x_20, sizeof(void*)*1);
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
unsigned x_46; obj* x_47; obj* x_49; unsigned char x_51; obj* x_53; obj* x_54; unsigned char x_55; 
x_46 = lean::string_iterator_curr(x_2);
x_53 = lean::box_uint32(x_0);
x_54 = lean::box_uint32(x_46);
x_55 = lean::nat_dec_le(x_53, x_54);
lean::dec(x_54);
lean::dec(x_53);
if (x_55 == 0)
{
obj* x_58; 
x_58 = lean::box(0);
x_47 = x_58;
goto lbl_48;
}
else
{
unsigned char x_59; 
x_59 = 1;
x_51 = x_59;
goto lbl_52;
}
lbl_48:
{
obj* x_61; obj* x_62; obj* x_64; obj* x_66; obj* x_67; obj* x_68; obj* x_72; obj* x_73; obj* x_75; obj* x_77; obj* x_78; obj* x_80; 
lean::dec(x_47);
x_61 = l_char_quote__core(x_46);
x_62 = l_char_has__repr___closed__1;
lean::inc(x_62);
x_64 = lean::string_append(x_62, x_61);
lean::dec(x_61);
x_66 = lean::string_append(x_64, x_62);
x_67 = lean::box(0);
x_68 = l_mjoin___rarg___closed__1;
lean::inc(x_1);
lean::inc(x_67);
lean::inc(x_68);
x_72 = l_lean_parser_monad__parsec_error___at___private_4089500695__finish__comment__block__aux___main___spec__1___rarg(x_66, x_68, x_67, x_67, x_1, x_2, x_3);
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
x_78 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_78);
x_80 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_78, x_73);
if (lean::obj_tag(x_80) == 0)
{
obj* x_81; obj* x_83; obj* x_85; unsigned x_88; obj* x_90; obj* x_91; obj* x_93; obj* x_96; obj* x_97; 
x_81 = lean::cnstr_get(x_80, 0);
lean::inc(x_81);
x_83 = lean::cnstr_get(x_80, 1);
lean::inc(x_83);
x_85 = lean::cnstr_get(x_80, 2);
lean::inc(x_85);
lean::dec(x_80);
x_88 = lean::unbox_uint32(x_81);
lean::dec(x_81);
x_90 = l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_parse__oct__lit___spec__4(x_0, x_88, x_1, x_83, x_75);
x_91 = lean::cnstr_get(x_90, 0);
lean::inc(x_91);
x_93 = lean::cnstr_get(x_90, 1);
lean::inc(x_93);
lean::dec(x_90);
x_96 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_85, x_91);
if (lean::is_scalar(x_77)) {
 x_97 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_97 = x_77;
}
lean::cnstr_set(x_97, 0, x_96);
lean::cnstr_set(x_97, 1, x_93);
return x_97;
}
else
{
obj* x_99; unsigned char x_101; obj* x_102; obj* x_103; obj* x_104; obj* x_105; 
lean::dec(x_1);
x_99 = lean::cnstr_get(x_80, 0);
lean::inc(x_99);
x_101 = lean::cnstr_get_scalar<unsigned char>(x_80, sizeof(void*)*1);
if (lean::is_shared(x_80)) {
 lean::dec(x_80);
 x_102 = lean::box(0);
} else {
 lean::cnstr_release(x_80, 0);
 x_102 = x_80;
}
if (lean::is_scalar(x_102)) {
 x_103 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_103 = x_102;
}
lean::cnstr_set(x_103, 0, x_99);
lean::cnstr_set_scalar(x_103, sizeof(void*)*1, x_101);
x_104 = x_103;
if (lean::is_scalar(x_77)) {
 x_105 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_105 = x_77;
}
lean::cnstr_set(x_105, 0, x_104);
lean::cnstr_set(x_105, 1, x_75);
return x_105;
}
}
lbl_50:
{
obj* x_108; obj* x_109; obj* x_110; obj* x_112; obj* x_114; obj* x_115; obj* x_116; obj* x_117; 
lean::dec(x_49);
lean::inc(x_2);
x_108 = lean::string_iterator_next(x_2);
x_109 = l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_parse__oct__lit___spec__6(x_0, x_2, x_1, x_108, x_3);
x_110 = lean::cnstr_get(x_109, 0);
lean::inc(x_110);
x_112 = lean::cnstr_get(x_109, 1);
lean::inc(x_112);
if (lean::is_shared(x_109)) {
 lean::dec(x_109);
 x_114 = lean::box(0);
} else {
 lean::cnstr_release(x_109, 0);
 lean::cnstr_release(x_109, 1);
 x_114 = x_109;
}
x_115 = lean::box(0);
x_116 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_115, x_110);
if (lean::is_scalar(x_114)) {
 x_117 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_117 = x_114;
}
lean::cnstr_set(x_117, 0, x_116);
lean::cnstr_set(x_117, 1, x_112);
return x_117;
}
lbl_52:
{
obj* x_118; obj* x_119; unsigned char x_120; 
x_118 = lean::mk_nat_obj(56u);
x_119 = lean::mk_nat_obj(55296u);
x_120 = lean::nat_dec_lt(x_118, x_119);
lean::dec(x_119);
if (x_120 == 0)
{
obj* x_122; unsigned char x_123; 
x_122 = lean::mk_nat_obj(57343u);
x_123 = lean::nat_dec_lt(x_122, x_118);
lean::dec(x_122);
if (x_123 == 0)
{
obj* x_126; obj* x_127; unsigned char x_128; 
lean::dec(x_118);
x_126 = lean::mk_nat_obj(0u);
x_127 = lean::box_uint32(x_46);
x_128 = lean::nat_dec_lt(x_127, x_126);
lean::dec(x_126);
lean::dec(x_127);
if (x_128 == 0)
{
obj* x_131; 
x_131 = lean::box(0);
x_47 = x_131;
goto lbl_48;
}
else
{
if (x_51 == 0)
{
obj* x_132; 
x_132 = lean::box(0);
x_47 = x_132;
goto lbl_48;
}
else
{
obj* x_133; 
x_133 = lean::box(0);
x_49 = x_133;
goto lbl_50;
}
}
}
else
{
obj* x_134; unsigned char x_135; 
x_134 = lean::mk_nat_obj(1114112u);
x_135 = lean::nat_dec_lt(x_118, x_134);
lean::dec(x_134);
if (x_135 == 0)
{
obj* x_138; obj* x_139; unsigned char x_140; 
lean::dec(x_118);
x_138 = lean::mk_nat_obj(0u);
x_139 = lean::box_uint32(x_46);
x_140 = lean::nat_dec_lt(x_139, x_138);
lean::dec(x_138);
lean::dec(x_139);
if (x_140 == 0)
{
obj* x_143; 
x_143 = lean::box(0);
x_47 = x_143;
goto lbl_48;
}
else
{
if (x_51 == 0)
{
obj* x_144; 
x_144 = lean::box(0);
x_47 = x_144;
goto lbl_48;
}
else
{
obj* x_145; 
x_145 = lean::box(0);
x_49 = x_145;
goto lbl_50;
}
}
}
else
{
obj* x_146; unsigned char x_147; 
x_146 = lean::box_uint32(x_46);
x_147 = lean::nat_dec_lt(x_146, x_118);
lean::dec(x_118);
lean::dec(x_146);
if (x_147 == 0)
{
obj* x_150; 
x_150 = lean::box(0);
x_47 = x_150;
goto lbl_48;
}
else
{
if (x_51 == 0)
{
obj* x_151; 
x_151 = lean::box(0);
x_47 = x_151;
goto lbl_48;
}
else
{
obj* x_152; 
x_152 = lean::box(0);
x_49 = x_152;
goto lbl_50;
}
}
}
}
}
else
{
obj* x_153; unsigned char x_154; 
x_153 = lean::box_uint32(x_46);
x_154 = lean::nat_dec_lt(x_153, x_118);
lean::dec(x_118);
lean::dec(x_153);
if (x_154 == 0)
{
obj* x_157; 
x_157 = lean::box(0);
x_47 = x_157;
goto lbl_48;
}
else
{
if (x_51 == 0)
{
obj* x_158; 
x_158 = lean::box(0);
x_47 = x_158;
goto lbl_48;
}
else
{
obj* x_159; 
x_159 = lean::box(0);
x_49 = x_159;
goto lbl_50;
}
}
}
}
}
}
}
obj* l___private_31565857__take__while__aux___main___at_lean_parser_parse__oct__lit___spec__3___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
unsigned x_4; obj* x_5; 
x_4 = lean::unbox_uint32(x_0);
x_5 = l___private_31565857__take__while__aux___main___at_lean_parser_parse__oct__lit___spec__3(x_4, x_1, x_2, x_3);
return x_5;
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_parse__oct__lit___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
unsigned x_5; unsigned x_6; obj* x_7; 
x_5 = lean::unbox_uint32(x_0);
x_6 = lean::unbox_uint32(x_1);
x_7 = l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_parse__oct__lit___spec__2(x_5, x_6, x_2, x_3, x_4);
return x_7;
}
}
obj* l___private_31565857__take__while__aux___main___at_lean_parser_parse__oct__lit___spec__5___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
unsigned x_4; obj* x_5; 
x_4 = lean::unbox_uint32(x_0);
x_5 = l___private_31565857__take__while__aux___main___at_lean_parser_parse__oct__lit___spec__5(x_4, x_1, x_2, x_3);
return x_5;
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_parse__oct__lit___spec__4___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
unsigned x_5; unsigned x_6; obj* x_7; 
x_5 = lean::unbox_uint32(x_0);
x_6 = lean::unbox_uint32(x_1);
x_7 = l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_parse__oct__lit___spec__4(x_5, x_6, x_2, x_3, x_4);
return x_7;
}
}
obj* l___private_31565857__take__while__aux___main___at_lean_parser_parse__oct__lit___spec__7___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
unsigned x_4; obj* x_5; 
x_4 = lean::unbox_uint32(x_0);
x_5 = l___private_31565857__take__while__aux___main___at_lean_parser_parse__oct__lit___spec__7(x_4, x_1, x_2, x_3);
return x_5;
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_parse__oct__lit___spec__6___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
unsigned x_5; obj* x_6; 
x_5 = lean::unbox_uint32(x_0);
x_6 = l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_parse__oct__lit___spec__6(x_5, x_1, x_2, x_3, x_4);
return x_6;
}
}
obj* l_lean_parser_monad__parsec_take__while1___at_lean_parser_parse__oct__lit___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
unsigned x_4; obj* x_5; 
x_4 = lean::unbox_uint32(x_0);
x_5 = l_lean_parser_monad__parsec_take__while1___at_lean_parser_parse__oct__lit___spec__1(x_4, x_1, x_2, x_3);
return x_5;
}
}
obj* l_lean_parser_parse__hex__lit(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; unsigned char x_5; obj* x_6; unsigned char x_7; obj* x_8; unsigned char x_9; obj* x_11; obj* x_12; unsigned x_14; 
x_3 = lean::mk_nat_obj(48u);
x_4 = lean::mk_nat_obj(55296u);
x_5 = lean::nat_dec_lt(x_3, x_4);
x_6 = lean::mk_nat_obj(120u);
x_7 = lean::nat_dec_lt(x_6, x_4);
x_8 = lean::mk_nat_obj(88u);
x_9 = lean::nat_dec_lt(x_8, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
obj* x_16; unsigned char x_17; 
x_16 = lean::mk_nat_obj(57343u);
x_17 = lean::nat_dec_lt(x_16, x_3);
lean::dec(x_16);
if (x_17 == 0)
{
obj* x_20; unsigned x_21; 
lean::dec(x_3);
x_20 = lean::mk_nat_obj(0u);
x_21 = lean::unbox_uint32(x_20);
lean::dec(x_20);
x_14 = x_21;
goto lbl_15;
}
else
{
obj* x_23; unsigned char x_24; 
x_23 = lean::mk_nat_obj(1114112u);
x_24 = lean::nat_dec_lt(x_3, x_23);
lean::dec(x_23);
if (x_24 == 0)
{
obj* x_27; unsigned x_28; 
lean::dec(x_3);
x_27 = lean::mk_nat_obj(0u);
x_28 = lean::unbox_uint32(x_27);
lean::dec(x_27);
x_14 = x_28;
goto lbl_15;
}
else
{
unsigned x_30; 
x_30 = lean::unbox_uint32(x_3);
lean::dec(x_3);
x_14 = x_30;
goto lbl_15;
}
}
}
else
{
unsigned x_32; 
x_32 = lean::unbox_uint32(x_3);
lean::dec(x_3);
x_14 = x_32;
goto lbl_15;
}
lbl_13:
{
if (lean::obj_tag(x_11) == 0)
{
obj* x_34; obj* x_36; obj* x_39; obj* x_40; obj* x_42; obj* x_44; obj* x_45; obj* x_46; 
x_34 = lean::cnstr_get(x_11, 1);
lean::inc(x_34);
x_36 = lean::cnstr_get(x_11, 2);
lean::inc(x_36);
lean::dec(x_11);
x_39 = l_lean_parser_monad__parsec_take__while1___at_lean_parser_parse__hex__lit___spec__1(x_0, x_34, x_12);
x_40 = lean::cnstr_get(x_39, 0);
lean::inc(x_40);
x_42 = lean::cnstr_get(x_39, 1);
lean::inc(x_42);
if (lean::is_shared(x_39)) {
 lean::dec(x_39);
 x_44 = lean::box(0);
} else {
 lean::cnstr_release(x_39, 0);
 lean::cnstr_release(x_39, 1);
 x_44 = x_39;
}
x_45 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_36, x_40);
if (lean::is_scalar(x_44)) {
 x_46 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_46 = x_44;
}
lean::cnstr_set(x_46, 0, x_45);
lean::cnstr_set(x_46, 1, x_42);
return x_46;
}
else
{
obj* x_48; unsigned char x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; 
lean::dec(x_0);
x_48 = lean::cnstr_get(x_11, 0);
lean::inc(x_48);
x_50 = lean::cnstr_get_scalar<unsigned char>(x_11, sizeof(void*)*1);
if (lean::is_shared(x_11)) {
 lean::dec(x_11);
 x_51 = lean::box(0);
} else {
 lean::cnstr_release(x_11, 0);
 x_51 = x_11;
}
if (lean::is_scalar(x_51)) {
 x_52 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_52 = x_51;
}
lean::cnstr_set(x_52, 0, x_48);
lean::cnstr_set_scalar(x_52, sizeof(void*)*1, x_50);
x_53 = x_52;
x_54 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_54, 0, x_53);
lean::cnstr_set(x_54, 1, x_12);
return x_54;
}
}
lbl_15:
{
obj* x_56; unsigned x_57; 
lean::inc(x_0);
x_56 = l_lean_parser_monad__parsec_ch___at___private_3519775105__ident_x_27___spec__11(x_14, x_0, x_1, x_2);
if (x_7 == 0)
{
obj* x_59; unsigned char x_60; 
x_59 = lean::mk_nat_obj(57343u);
x_60 = lean::nat_dec_lt(x_59, x_6);
lean::dec(x_59);
if (x_60 == 0)
{
obj* x_63; unsigned x_64; 
lean::dec(x_6);
x_63 = lean::mk_nat_obj(0u);
x_64 = lean::unbox_uint32(x_63);
lean::dec(x_63);
x_57 = x_64;
goto lbl_58;
}
else
{
obj* x_66; unsigned char x_67; 
x_66 = lean::mk_nat_obj(1114112u);
x_67 = lean::nat_dec_lt(x_6, x_66);
lean::dec(x_66);
if (x_67 == 0)
{
obj* x_70; unsigned x_71; 
lean::dec(x_6);
x_70 = lean::mk_nat_obj(0u);
x_71 = lean::unbox_uint32(x_70);
lean::dec(x_70);
x_57 = x_71;
goto lbl_58;
}
else
{
unsigned x_73; 
x_73 = lean::unbox_uint32(x_6);
lean::dec(x_6);
x_57 = x_73;
goto lbl_58;
}
}
}
else
{
unsigned x_75; 
x_75 = lean::unbox_uint32(x_6);
lean::dec(x_6);
x_57 = x_75;
goto lbl_58;
}
lbl_58:
{
unsigned x_77; obj* x_78; obj* x_79; 
if (x_9 == 0)
{
obj* x_81; unsigned char x_82; 
x_81 = lean::mk_nat_obj(57343u);
x_82 = lean::nat_dec_lt(x_81, x_8);
lean::dec(x_81);
if (x_82 == 0)
{
obj* x_85; obj* x_87; obj* x_90; unsigned x_91; 
lean::dec(x_8);
x_85 = lean::cnstr_get(x_56, 0);
lean::inc(x_85);
x_87 = lean::cnstr_get(x_56, 1);
lean::inc(x_87);
lean::dec(x_56);
x_90 = lean::mk_nat_obj(0u);
x_91 = lean::unbox_uint32(x_90);
lean::dec(x_90);
x_77 = x_91;
x_78 = x_85;
x_79 = x_87;
goto lbl_80;
}
else
{
obj* x_93; unsigned char x_94; 
x_93 = lean::mk_nat_obj(1114112u);
x_94 = lean::nat_dec_lt(x_8, x_93);
lean::dec(x_93);
if (x_94 == 0)
{
obj* x_97; obj* x_99; obj* x_102; unsigned x_103; 
lean::dec(x_8);
x_97 = lean::cnstr_get(x_56, 0);
lean::inc(x_97);
x_99 = lean::cnstr_get(x_56, 1);
lean::inc(x_99);
lean::dec(x_56);
x_102 = lean::mk_nat_obj(0u);
x_103 = lean::unbox_uint32(x_102);
lean::dec(x_102);
x_77 = x_103;
x_78 = x_97;
x_79 = x_99;
goto lbl_80;
}
else
{
obj* x_105; obj* x_107; unsigned x_110; 
x_105 = lean::cnstr_get(x_56, 0);
lean::inc(x_105);
x_107 = lean::cnstr_get(x_56, 1);
lean::inc(x_107);
lean::dec(x_56);
x_110 = lean::unbox_uint32(x_8);
lean::dec(x_8);
x_77 = x_110;
x_78 = x_105;
x_79 = x_107;
goto lbl_80;
}
}
}
else
{
obj* x_112; obj* x_114; unsigned x_117; 
x_112 = lean::cnstr_get(x_56, 0);
lean::inc(x_112);
x_114 = lean::cnstr_get(x_56, 1);
lean::inc(x_114);
lean::dec(x_56);
x_117 = lean::unbox_uint32(x_8);
lean::dec(x_8);
x_77 = x_117;
x_78 = x_112;
x_79 = x_114;
goto lbl_80;
}
lbl_80:
{
if (lean::obj_tag(x_78) == 0)
{
obj* x_119; obj* x_121; obj* x_126; obj* x_127; obj* x_129; 
x_119 = lean::cnstr_get(x_78, 1);
lean::inc(x_119);
x_121 = lean::cnstr_get(x_78, 2);
lean::inc(x_121);
lean::dec(x_78);
lean::inc(x_119);
lean::inc(x_0);
x_126 = l_lean_parser_monad__parsec_ch___at___private_3519775105__ident_x_27___spec__11(x_57, x_0, x_119, x_79);
x_127 = lean::cnstr_get(x_126, 0);
lean::inc(x_127);
x_129 = lean::cnstr_get(x_126, 1);
lean::inc(x_129);
lean::dec(x_126);
if (lean::obj_tag(x_127) == 0)
{
obj* x_133; 
lean::dec(x_119);
x_133 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_121, x_127);
x_11 = x_133;
x_12 = x_129;
goto lbl_13;
}
else
{
obj* x_134; unsigned char x_136; 
x_134 = lean::cnstr_get(x_127, 0);
lean::inc(x_134);
x_136 = lean::cnstr_get_scalar<unsigned char>(x_127, sizeof(void*)*1);
if (x_136 == 0)
{
obj* x_139; obj* x_140; obj* x_142; obj* x_145; obj* x_146; 
lean::dec(x_127);
lean::inc(x_0);
x_139 = l_lean_parser_monad__parsec_ch___at___private_3519775105__ident_x_27___spec__11(x_77, x_0, x_119, x_129);
x_140 = lean::cnstr_get(x_139, 0);
lean::inc(x_140);
x_142 = lean::cnstr_get(x_139, 1);
lean::inc(x_142);
lean::dec(x_139);
x_145 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_134, x_140);
x_146 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_121, x_145);
x_11 = x_146;
x_12 = x_142;
goto lbl_13;
}
else
{
obj* x_149; 
lean::dec(x_119);
lean::dec(x_134);
x_149 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_121, x_127);
x_11 = x_149;
x_12 = x_129;
goto lbl_13;
}
}
}
else
{
obj* x_150; unsigned char x_152; obj* x_153; obj* x_154; obj* x_155; 
x_150 = lean::cnstr_get(x_78, 0);
lean::inc(x_150);
x_152 = lean::cnstr_get_scalar<unsigned char>(x_78, sizeof(void*)*1);
if (lean::is_shared(x_78)) {
 lean::dec(x_78);
 x_153 = lean::box(0);
} else {
 lean::cnstr_release(x_78, 0);
 x_153 = x_78;
}
if (lean::is_scalar(x_153)) {
 x_154 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_154 = x_153;
}
lean::cnstr_set(x_154, 0, x_150);
lean::cnstr_set_scalar(x_154, sizeof(void*)*1, x_152);
x_155 = x_154;
x_11 = x_155;
x_12 = x_79;
goto lbl_13;
}
}
}
}
}
}
obj* l___private_31565857__take__while__aux___main___at_lean_parser_parse__hex__lit___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; unsigned char x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
unsigned char x_6; 
x_6 = lean::string_iterator_has_next(x_2);
if (x_6 == 0)
{
obj* x_8; 
lean::dec(x_0);
x_8 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_8;
}
else
{
obj* x_9; obj* x_10; unsigned x_13; unsigned char x_14; 
x_9 = lean::mk_nat_obj(1u);
x_10 = lean::nat_sub(x_0, x_9);
lean::dec(x_9);
lean::dec(x_0);
x_13 = lean::string_iterator_curr(x_2);
x_14 = l_char_is__digit(x_13);
if (x_14 == 0)
{
unsigned char x_15; 
x_15 = l_char_is__alpha(x_13);
if (x_15 == 0)
{
obj* x_17; 
lean::dec(x_10);
x_17 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
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
x_22 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
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
x_27 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_27;
}
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_parse__hex__lit___spec__2(unsigned x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
lean::dec(x_1);
x_5 = l_string_join___closed__1;
lean::inc(x_5);
x_7 = lean::string_push(x_5, x_0);
x_8 = lean::string_iterator_remaining(x_2);
x_9 = l___private_31565857__take__while__aux___main___at_lean_parser_parse__hex__lit___spec__3(x_8, x_7, x_2);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_3);
return x_10;
}
}
obj* l_lean_parser_monad__parsec_take__while1___at_lean_parser_parse__hex__lit___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; unsigned char x_6; 
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
x_14 = l_lean_parser_monad__parsec_error___at___private_4089500695__finish__comment__block__aux___main___spec__1___rarg(x_8, x_9, x_7, x_7, x_0, x_1, x_2);
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
unsigned x_23; unsigned char x_24; 
x_23 = lean::string_iterator_curr(x_1);
x_24 = l_char_is__digit(x_23);
if (x_24 == 0)
{
unsigned char x_25; 
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
x_37 = l_lean_parser_monad__parsec_error___at___private_4089500695__finish__comment__block__aux___main___spec__1___rarg(x_31, x_33, x_32, x_32, x_0, x_1, x_2);
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
x_61 = l_lean_parser_monad__parsec_error___at___private_4089500695__finish__comment__block__aux___main___spec__1___rarg(x_55, x_57, x_56, x_56, x_0, x_1, x_2);
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
obj* x_74; obj* x_76; obj* x_78; unsigned x_81; obj* x_83; obj* x_84; obj* x_86; obj* x_88; obj* x_89; obj* x_90; 
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
obj* x_92; unsigned char x_94; obj* x_95; obj* x_96; obj* x_97; obj* x_98; 
lean::dec(x_0);
x_92 = lean::cnstr_get(x_3, 0);
lean::inc(x_92);
x_94 = lean::cnstr_get_scalar<unsigned char>(x_3, sizeof(void*)*1);
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
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_parse__hex__lit___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
unsigned x_4; obj* x_5; 
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
x_2 = lean::name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean::name_mk_string(x_2, x_3);
x_5 = lean::mk_string("number");
x_6 = lean::name_mk_string(x_4, x_5);
return x_6;
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
obj* x_8; obj* x_11; obj* x_13; obj* x_16; unsigned char x_17; 
x_8 = lean::cnstr_get(x_4, 0);
lean::inc(x_8);
lean::dec(x_4);
x_11 = lean::cnstr_get(x_8, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_8, 1);
lean::inc(x_13);
lean::dec(x_8);
x_16 = l_lean_parser_number_has__view_x_27___lambda__1___closed__6;
x_17 = lean::name_dec_eq(x_11, x_16);
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
obj* x_51; obj* x_53; obj* x_56; unsigned char x_57; 
x_51 = lean::cnstr_get(x_38, 0);
lean::inc(x_51);
x_53 = lean::cnstr_get(x_38, 1);
lean::inc(x_53);
lean::dec(x_38);
x_56 = lean::box(0);
x_57 = lean::name_dec_eq(x_51, x_56);
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
obj* x_83; unsigned char x_84; 
x_83 = lean::mk_nat_obj(0u);
x_84 = lean::nat_dec_eq(x_2, x_83);
lean::dec(x_83);
if (x_84 == 0)
{
obj* x_86; unsigned char x_87; 
x_86 = lean::mk_nat_obj(1u);
x_87 = lean::nat_dec_eq(x_2, x_86);
lean::dec(x_86);
if (x_87 == 0)
{
obj* x_89; unsigned char x_90; 
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
obj* x_5; unsigned char x_6; 
x_5 = lean::mk_nat_obj(0u);
x_6 = lean::nat_dec_eq(x_1, x_5);
lean::dec(x_5);
if (x_6 == 0)
{
obj* x_8; unsigned char x_9; 
x_8 = lean::mk_nat_obj(1u);
x_9 = lean::nat_dec_eq(x_1, x_8);
lean::dec(x_8);
if (x_9 == 0)
{
obj* x_11; unsigned char x_12; 
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
x_2 = lean::name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean::name_mk_string(x_2, x_3);
x_5 = lean::mk_string("number");
x_6 = lean::name_mk_string(x_4, x_5);
return x_6;
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
obj* _init_l_lean_parser_number_has__view_x_27___lambda__2___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_nat_obj(2u);
x_2 = lean::name_mk_numeral(x_0, x_1);
return x_2;
}
}
obj* _init_l_lean_parser_number_has__view_x_27___lambda__2___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_nat_obj(3u);
x_2 = lean::name_mk_numeral(x_0, x_1);
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
obj* l_lean_parser_number_x_27(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_7; 
x_3 = l_lean_parser_number;
x_4 = l_lean_parser_number_x_27___closed__1;
lean::inc(x_4);
lean::inc(x_3);
x_7 = l_lean_parser_combinators_node___at_lean_parser_detail__ident__part_parser___spec__8(x_3, x_4, x_0, x_1, x_2);
return x_7;
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
obj* x_23; unsigned char x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
lean::dec(x_0);
x_23 = lean::cnstr_get(x_5, 0);
lean::inc(x_23);
x_25 = lean::cnstr_get_scalar<unsigned char>(x_5, sizeof(void*)*1);
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
obj* x_23; unsigned char x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
lean::dec(x_0);
x_23 = lean::cnstr_get(x_5, 0);
lean::inc(x_23);
x_25 = lean::cnstr_get_scalar<unsigned char>(x_5, sizeof(void*)*1);
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
obj* x_23; unsigned char x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
lean::dec(x_0);
x_23 = lean::cnstr_get(x_5, 0);
lean::inc(x_23);
x_25 = lean::cnstr_get_scalar<unsigned char>(x_5, sizeof(void*)*1);
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
obj* x_23; unsigned char x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
lean::dec(x_0);
x_23 = lean::cnstr_get(x_5, 0);
lean::inc(x_23);
x_25 = lean::cnstr_get_scalar<unsigned char>(x_5, sizeof(void*)*1);
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
obj* l___private_31565857__take__while__aux___main___at_lean_parser_number_x_27___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; unsigned char x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
unsigned char x_6; 
x_6 = lean::string_iterator_has_next(x_2);
if (x_6 == 0)
{
obj* x_8; 
lean::dec(x_0);
x_8 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_8;
}
else
{
unsigned x_9; unsigned char x_10; 
x_9 = lean::string_iterator_curr(x_2);
x_10 = l_char_is__digit(x_9);
if (x_10 == 0)
{
obj* x_12; 
lean::dec(x_0);
x_12 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
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
x_21 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_21;
}
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_number_x_27___spec__2(unsigned x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
lean::dec(x_1);
x_5 = l_string_join___closed__1;
lean::inc(x_5);
x_7 = lean::string_push(x_5, x_0);
x_8 = lean::string_iterator_remaining(x_2);
x_9 = l___private_31565857__take__while__aux___main___at_lean_parser_number_x_27___spec__3(x_8, x_7, x_2);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_3);
return x_10;
}
}
obj* l___private_31565857__take__while__aux___main___at_lean_parser_number_x_27___spec__5(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; unsigned char x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
unsigned char x_6; 
x_6 = lean::string_iterator_has_next(x_2);
if (x_6 == 0)
{
obj* x_8; 
lean::dec(x_0);
x_8 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_8;
}
else
{
unsigned x_9; unsigned char x_10; 
x_9 = lean::string_iterator_curr(x_2);
x_10 = l_char_is__digit(x_9);
if (x_10 == 0)
{
obj* x_12; 
lean::dec(x_0);
x_12 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
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
x_21 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_21;
}
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_number_x_27___spec__4(unsigned x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
lean::dec(x_1);
x_5 = l_string_join___closed__1;
lean::inc(x_5);
x_7 = lean::string_push(x_5, x_0);
x_8 = lean::string_iterator_remaining(x_2);
x_9 = l___private_31565857__take__while__aux___main___at_lean_parser_number_x_27___spec__5(x_8, x_7, x_2);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_3);
return x_10;
}
}
obj* l___private_31565857__take__while__aux___main___at_lean_parser_number_x_27___spec__7(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; unsigned char x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
unsigned char x_6; 
x_6 = lean::string_iterator_has_next(x_2);
if (x_6 == 0)
{
obj* x_8; 
lean::dec(x_0);
x_8 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_8;
}
else
{
unsigned x_9; unsigned char x_10; 
x_9 = lean::string_iterator_curr(x_2);
x_10 = l_char_is__digit(x_9);
if (x_10 == 0)
{
obj* x_12; 
lean::dec(x_0);
x_12 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
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
x_21 = l___private_2142412293__mk__string__result___rarg(x_1, x_2);
return x_21;
}
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_number_x_27___spec__6(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
unsigned x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
lean::dec(x_1);
x_5 = lean::string_iterator_curr(x_0);
lean::dec(x_0);
x_7 = l_string_join___closed__1;
lean::inc(x_7);
x_9 = lean::string_push(x_7, x_5);
x_10 = lean::string_iterator_remaining(x_2);
x_11 = l___private_31565857__take__while__aux___main___at_lean_parser_number_x_27___spec__7(x_10, x_9, x_2);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_3);
return x_12;
}
}
obj* l_lean_parser_monad__parsec_take__while1___at_lean_parser_number_x_27___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
unsigned char x_3; 
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
x_11 = l_lean_parser_monad__parsec_error___at___private_4089500695__finish__comment__block__aux___main___spec__1___rarg(x_5, x_6, x_4, x_4, x_0, x_1, x_2);
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
obj* x_20; obj* x_22; obj* x_24; unsigned x_27; obj* x_29; obj* x_30; obj* x_32; obj* x_35; obj* x_36; 
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
obj* x_38; unsigned char x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; 
lean::dec(x_0);
x_38 = lean::cnstr_get(x_19, 0);
lean::inc(x_38);
x_40 = lean::cnstr_get_scalar<unsigned char>(x_19, sizeof(void*)*1);
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
unsigned x_45; unsigned char x_46; 
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
x_58 = l_lean_parser_monad__parsec_error___at___private_4089500695__finish__comment__block__aux___main___spec__1___rarg(x_52, x_54, x_53, x_53, x_0, x_1, x_2);
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
obj* x_67; obj* x_69; obj* x_71; unsigned x_74; obj* x_76; obj* x_77; obj* x_79; obj* x_82; obj* x_83; 
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
obj* x_85; unsigned char x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; 
lean::dec(x_0);
x_85 = lean::cnstr_get(x_66, 0);
lean::inc(x_85);
x_87 = lean::cnstr_get_scalar<unsigned char>(x_66, sizeof(void*)*1);
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
x_24 = lean::name_mk_numeral(x_22, x_4);
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
obj* x_33; unsigned char x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; 
lean::dec(x_4);
x_33 = lean::cnstr_get(x_10, 0);
lean::inc(x_33);
x_35 = lean::cnstr_get_scalar<unsigned char>(x_10, sizeof(void*)*1);
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
obj* x_35; obj* x_36; unsigned char x_38; 
lean::dec(x_25);
x_35 = lean::string_iterator_offset(x_21);
x_36 = lean::string_iterator_offset(x_30);
lean::dec(x_30);
x_38 = lean::nat_dec_lt(x_35, x_36);
if (x_38 == 0)
{
unsigned char x_39; 
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
obj* x_83; unsigned char x_85; obj* x_86; obj* x_87; obj* x_88; 
x_83 = lean::cnstr_get(x_14, 0);
lean::inc(x_83);
x_85 = lean::cnstr_get_scalar<unsigned char>(x_14, sizeof(void*)*1);
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
obj* x_111; obj* x_113; obj* x_114; obj* x_116; unsigned char x_118; 
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
unsigned char x_120; 
lean::dec(x_2);
x_120 = lean::nat_dec_lt(x_116, x_113);
lean::dec(x_116);
if (x_120 == 0)
{
obj* x_122; obj* x_123; unsigned char x_125; 
x_122 = l_lean_parser_parsec__t_merge___rarg(x_100, x_111);
x_123 = lean::string_iterator_offset(x_0);
lean::dec(x_0);
x_125 = lean::nat_dec_lt(x_123, x_113);
lean::dec(x_113);
lean::dec(x_123);
if (x_125 == 0)
{
unsigned char x_128; obj* x_129; obj* x_130; obj* x_131; obj* x_133; 
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
unsigned char x_134; obj* x_135; obj* x_136; obj* x_137; obj* x_139; 
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
unsigned char x_143; obj* x_144; obj* x_145; obj* x_146; obj* x_148; 
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
obj* x_5; obj* x_6; unsigned char x_7; obj* x_8; obj* x_9; 
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
obj* x_49; unsigned char x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; 
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_18);
x_49 = lean::cnstr_get(x_26, 0);
lean::inc(x_49);
x_51 = lean::cnstr_get_scalar<unsigned char>(x_26, sizeof(void*)*1);
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
obj* x_24; unsigned char x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_32; obj* x_33; 
x_24 = lean::cnstr_get(x_9, 0);
lean::inc(x_24);
x_26 = lean::cnstr_get_scalar<unsigned char>(x_9, sizeof(void*)*1);
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
x_21 = l___private_1297690757__many1__aux___main___rarg___closed__1;
x_22 = l_mjoin___rarg___closed__1;
lean::inc(x_20);
lean::inc(x_22);
lean::inc(x_21);
x_26 = l_lean_parser_monad__parsec_error___at___private_4089500695__finish__comment__block__aux___main___spec__1___rarg(x_21, x_22, x_20, x_20, x_1, x_13, x_8);
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
obj* x_44; unsigned char x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; 
lean::dec(x_1);
x_44 = lean::cnstr_get(x_6, 0);
lean::inc(x_44);
x_46 = lean::cnstr_get_scalar<unsigned char>(x_6, sizeof(void*)*1);
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
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_number_x_27___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
unsigned x_4; obj* x_5; 
x_4 = lean::unbox_uint32(x_0);
x_5 = l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_number_x_27___spec__2(x_4, x_1, x_2, x_3);
return x_5;
}
}
obj* l_lean_parser_monad__parsec_take__while__cont___at_lean_parser_number_x_27___spec__4___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
unsigned x_4; obj* x_5; 
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
x_2 = lean::name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean::name_mk_string(x_2, x_3);
x_5 = lean::mk_string("string_lit");
x_6 = lean::name_mk_string(x_4, x_5);
return x_6;
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
obj* _init_l_lean_parser_string__lit_has__view() {
_start:
{
obj* x_0; 
x_0 = l_lean_parser_string__lit_has__view_x_27;
lean::inc(x_0);
return x_0;
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
x_7 = l_lean_parser_combinators_node___at_lean_parser_detail__ident__part_parser___spec__8(x_3, x_4, x_0, x_1, x_2);
return x_7;
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
obj* x_23; unsigned char x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
lean::dec(x_0);
x_23 = lean::cnstr_get(x_5, 0);
lean::inc(x_23);
x_25 = lean::cnstr_get_scalar<unsigned char>(x_5, sizeof(void*)*1);
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
obj* l_lean_parser_monad__parsec_digit___at_lean_parser_string__lit_x_27___spec__5(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
unsigned char x_3; 
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
x_10 = l_lean_parser_monad__parsec_error___at___private_4089500695__finish__comment__block__aux___main___spec__1___rarg(x_5, x_6, x_4, x_4, x_0, x_1, x_2);
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
unsigned x_20; unsigned char x_21; 
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
x_32 = l_lean_parser_monad__parsec_error___at___private_4089500695__finish__comment__block__aux___main___spec__1___rarg(x_27, x_29, x_28, x_28, x_0, x_1, x_2);
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
obj* x_16; obj* x_18; obj* x_20; obj* x_22; obj* x_23; obj* x_24; unsigned char x_25; 
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
x_23 = lean::mk_nat_obj(48u);
x_24 = lean::mk_nat_obj(55296u);
x_25 = lean::nat_dec_lt(x_23, x_24);
lean::dec(x_24);
if (x_25 == 0)
{
obj* x_27; unsigned char x_28; 
x_27 = lean::mk_nat_obj(57343u);
x_28 = lean::nat_dec_lt(x_27, x_23);
lean::dec(x_27);
if (x_28 == 0)
{
obj* x_31; obj* x_32; obj* x_35; obj* x_37; obj* x_38; 
lean::dec(x_23);
x_31 = lean::mk_nat_obj(0u);
x_32 = lean::nat_sub(x_16, x_31);
lean::dec(x_31);
lean::dec(x_16);
x_35 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_35);
if (lean::is_scalar(x_22)) {
 x_37 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_37 = x_22;
}
lean::cnstr_set(x_37, 0, x_32);
lean::cnstr_set(x_37, 1, x_18);
lean::cnstr_set(x_37, 2, x_35);
x_38 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_20, x_37);
x_5 = x_38;
x_6 = x_13;
goto lbl_7;
}
else
{
obj* x_39; unsigned char x_40; 
x_39 = lean::mk_nat_obj(1114112u);
x_40 = lean::nat_dec_lt(x_23, x_39);
lean::dec(x_39);
if (x_40 == 0)
{
obj* x_43; obj* x_44; obj* x_47; obj* x_49; obj* x_50; 
lean::dec(x_23);
x_43 = lean::mk_nat_obj(0u);
x_44 = lean::nat_sub(x_16, x_43);
lean::dec(x_43);
lean::dec(x_16);
x_47 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_47);
if (lean::is_scalar(x_22)) {
 x_49 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_49 = x_22;
}
lean::cnstr_set(x_49, 0, x_44);
lean::cnstr_set(x_49, 1, x_18);
lean::cnstr_set(x_49, 2, x_47);
x_50 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_20, x_49);
x_5 = x_50;
x_6 = x_13;
goto lbl_7;
}
else
{
obj* x_51; obj* x_54; obj* x_56; obj* x_57; 
x_51 = lean::nat_sub(x_16, x_23);
lean::dec(x_23);
lean::dec(x_16);
x_54 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_54);
if (lean::is_scalar(x_22)) {
 x_56 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_56 = x_22;
}
lean::cnstr_set(x_56, 0, x_51);
lean::cnstr_set(x_56, 1, x_18);
lean::cnstr_set(x_56, 2, x_54);
x_57 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_20, x_56);
x_5 = x_57;
x_6 = x_13;
goto lbl_7;
}
}
}
else
{
obj* x_58; obj* x_61; obj* x_63; obj* x_64; 
x_58 = lean::nat_sub(x_16, x_23);
lean::dec(x_23);
lean::dec(x_16);
x_61 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_61);
if (lean::is_scalar(x_22)) {
 x_63 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_63 = x_22;
}
lean::cnstr_set(x_63, 0, x_58);
lean::cnstr_set(x_63, 1, x_18);
lean::cnstr_set(x_63, 2, x_61);
x_64 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_20, x_63);
x_5 = x_64;
x_6 = x_13;
goto lbl_7;
}
}
else
{
obj* x_65; unsigned char x_67; obj* x_68; obj* x_69; obj* x_70; 
x_65 = lean::cnstr_get(x_11, 0);
lean::inc(x_65);
x_67 = lean::cnstr_get_scalar<unsigned char>(x_11, sizeof(void*)*1);
if (lean::is_shared(x_11)) {
 lean::dec(x_11);
 x_68 = lean::box(0);
} else {
 lean::cnstr_release(x_11, 0);
 x_68 = x_11;
}
if (lean::is_scalar(x_68)) {
 x_69 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_69 = x_68;
}
lean::cnstr_set(x_69, 0, x_65);
lean::cnstr_set_scalar(x_69, sizeof(void*)*1, x_67);
x_70 = x_69;
x_5 = x_70;
x_6 = x_13;
goto lbl_7;
}
lbl_4:
{
obj* x_71; obj* x_73; obj* x_75; obj* x_76; obj* x_78; obj* x_79; 
x_71 = lean::cnstr_get(x_3, 0);
lean::inc(x_71);
x_73 = lean::cnstr_get(x_3, 1);
lean::inc(x_73);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_75 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 1);
 x_75 = x_3;
}
x_76 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__4___closed__1;
lean::inc(x_76);
x_78 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_71, x_76);
if (lean::is_scalar(x_75)) {
 x_79 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_79 = x_75;
}
lean::cnstr_set(x_79, 0, x_78);
lean::cnstr_set(x_79, 1, x_73);
return x_79;
}
lbl_7:
{
if (lean::obj_tag(x_5) == 0)
{
obj* x_82; obj* x_84; obj* x_85; 
lean::dec(x_1);
lean::dec(x_0);
x_82 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__4___closed__1;
lean::inc(x_82);
x_84 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_5, x_82);
x_85 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_85, 0, x_84);
lean::cnstr_set(x_85, 1, x_6);
return x_85;
}
else
{
obj* x_86; unsigned char x_88; obj* x_89; obj* x_91; obj* x_92; obj* x_94; obj* x_95; 
x_86 = lean::cnstr_get(x_5, 0);
lean::inc(x_86);
x_88 = lean::cnstr_get_scalar<unsigned char>(x_5, sizeof(void*)*1);
if (x_88 == 0)
{
unsigned char x_98; 
lean::dec(x_5);
x_98 = lean::string_iterator_has_next(x_1);
if (x_98 == 0)
{
obj* x_99; obj* x_100; obj* x_101; obj* x_107; obj* x_108; obj* x_110; obj* x_113; obj* x_115; 
x_99 = lean::box(0);
x_100 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_101 = l_mjoin___rarg___closed__1;
lean::inc(x_1);
lean::inc(x_0);
lean::inc(x_99);
lean::inc(x_101);
lean::inc(x_100);
x_107 = l_lean_parser_monad__parsec_error___at___private_4089500695__finish__comment__block__aux___main___spec__1___rarg(x_100, x_101, x_99, x_99, x_0, x_1, x_6);
x_108 = lean::cnstr_get(x_107, 0);
lean::inc(x_108);
x_110 = lean::cnstr_get(x_107, 1);
lean::inc(x_110);
lean::dec(x_107);
x_113 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_113);
x_115 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_113, x_108);
x_94 = x_115;
x_95 = x_110;
goto lbl_96;
}
else
{
unsigned x_116; obj* x_117; obj* x_119; obj* x_121; obj* x_122; unsigned char x_123; unsigned char x_124; 
x_116 = lean::string_iterator_curr(x_1);
x_121 = lean::mk_nat_obj(97u);
x_122 = lean::mk_nat_obj(55296u);
x_123 = lean::nat_dec_lt(x_121, x_122);
if (x_123 == 0)
{
obj* x_126; unsigned char x_127; 
x_126 = lean::mk_nat_obj(57343u);
x_127 = lean::nat_dec_lt(x_126, x_121);
lean::dec(x_126);
if (x_127 == 0)
{
obj* x_130; obj* x_131; unsigned char x_132; 
lean::dec(x_121);
x_130 = lean::mk_nat_obj(0u);
x_131 = lean::box_uint32(x_116);
x_132 = lean::nat_dec_le(x_130, x_131);
lean::dec(x_131);
lean::dec(x_130);
if (x_132 == 0)
{
obj* x_136; 
lean::dec(x_122);
x_136 = lean::box(0);
x_117 = x_136;
goto lbl_118;
}
else
{
unsigned char x_137; 
x_137 = 1;
x_124 = x_137;
goto lbl_125;
}
}
else
{
obj* x_138; unsigned char x_139; 
x_138 = lean::mk_nat_obj(1114112u);
x_139 = lean::nat_dec_lt(x_121, x_138);
lean::dec(x_138);
if (x_139 == 0)
{
obj* x_142; obj* x_143; unsigned char x_144; 
lean::dec(x_121);
x_142 = lean::mk_nat_obj(0u);
x_143 = lean::box_uint32(x_116);
x_144 = lean::nat_dec_le(x_142, x_143);
lean::dec(x_143);
lean::dec(x_142);
if (x_144 == 0)
{
obj* x_148; 
lean::dec(x_122);
x_148 = lean::box(0);
x_117 = x_148;
goto lbl_118;
}
else
{
unsigned char x_149; 
x_149 = 1;
x_124 = x_149;
goto lbl_125;
}
}
else
{
obj* x_150; unsigned char x_151; 
x_150 = lean::box_uint32(x_116);
x_151 = lean::nat_dec_le(x_121, x_150);
lean::dec(x_150);
lean::dec(x_121);
if (x_151 == 0)
{
obj* x_155; 
lean::dec(x_122);
x_155 = lean::box(0);
x_117 = x_155;
goto lbl_118;
}
else
{
unsigned char x_156; 
x_156 = 1;
x_124 = x_156;
goto lbl_125;
}
}
}
}
else
{
obj* x_157; unsigned char x_158; 
x_157 = lean::box_uint32(x_116);
x_158 = lean::nat_dec_le(x_121, x_157);
lean::dec(x_157);
lean::dec(x_121);
if (x_158 == 0)
{
obj* x_162; 
lean::dec(x_122);
x_162 = lean::box(0);
x_117 = x_162;
goto lbl_118;
}
else
{
unsigned char x_163; 
x_163 = 1;
x_124 = x_163;
goto lbl_125;
}
}
lbl_118:
{
obj* x_165; obj* x_166; obj* x_168; obj* x_170; obj* x_171; obj* x_172; obj* x_177; obj* x_178; obj* x_180; obj* x_183; obj* x_185; 
lean::dec(x_117);
x_165 = l_char_quote__core(x_116);
x_166 = l_char_has__repr___closed__1;
lean::inc(x_166);
x_168 = lean::string_append(x_166, x_165);
lean::dec(x_165);
x_170 = lean::string_append(x_168, x_166);
x_171 = lean::box(0);
x_172 = l_mjoin___rarg___closed__1;
lean::inc(x_1);
lean::inc(x_0);
lean::inc(x_171);
lean::inc(x_172);
x_177 = l_lean_parser_monad__parsec_error___at___private_4089500695__finish__comment__block__aux___main___spec__1___rarg(x_170, x_172, x_171, x_171, x_0, x_1, x_6);
x_178 = lean::cnstr_get(x_177, 0);
lean::inc(x_178);
x_180 = lean::cnstr_get(x_177, 1);
lean::inc(x_180);
lean::dec(x_177);
x_183 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_183);
x_185 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_183, x_178);
x_94 = x_185;
x_95 = x_180;
goto lbl_96;
}
lbl_120:
{
obj* x_188; obj* x_189; obj* x_190; obj* x_191; 
lean::dec(x_119);
lean::inc(x_1);
x_188 = lean::string_iterator_next(x_1);
x_189 = lean::box(0);
x_190 = lean::box_uint32(x_116);
x_191 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_191, 0, x_190);
lean::cnstr_set(x_191, 1, x_188);
lean::cnstr_set(x_191, 2, x_189);
x_94 = x_191;
x_95 = x_6;
goto lbl_96;
}
lbl_125:
{
obj* x_192; unsigned char x_193; 
x_192 = lean::mk_nat_obj(102u);
x_193 = lean::nat_dec_lt(x_192, x_122);
lean::dec(x_122);
if (x_193 == 0)
{
obj* x_195; unsigned char x_196; 
x_195 = lean::mk_nat_obj(57343u);
x_196 = lean::nat_dec_lt(x_195, x_192);
lean::dec(x_195);
if (x_196 == 0)
{
obj* x_199; obj* x_200; unsigned char x_201; 
lean::dec(x_192);
x_199 = lean::mk_nat_obj(0u);
x_200 = lean::box_uint32(x_116);
x_201 = lean::nat_dec_le(x_200, x_199);
lean::dec(x_199);
lean::dec(x_200);
if (x_201 == 0)
{
obj* x_204; 
x_204 = lean::box(0);
x_117 = x_204;
goto lbl_118;
}
else
{
if (x_124 == 0)
{
obj* x_205; 
x_205 = lean::box(0);
x_117 = x_205;
goto lbl_118;
}
else
{
obj* x_206; 
x_206 = lean::box(0);
x_119 = x_206;
goto lbl_120;
}
}
}
else
{
obj* x_207; unsigned char x_208; 
x_207 = lean::mk_nat_obj(1114112u);
x_208 = lean::nat_dec_lt(x_192, x_207);
lean::dec(x_207);
if (x_208 == 0)
{
obj* x_211; obj* x_212; unsigned char x_213; 
lean::dec(x_192);
x_211 = lean::mk_nat_obj(0u);
x_212 = lean::box_uint32(x_116);
x_213 = lean::nat_dec_le(x_212, x_211);
lean::dec(x_211);
lean::dec(x_212);
if (x_213 == 0)
{
obj* x_216; 
x_216 = lean::box(0);
x_117 = x_216;
goto lbl_118;
}
else
{
if (x_124 == 0)
{
obj* x_217; 
x_217 = lean::box(0);
x_117 = x_217;
goto lbl_118;
}
else
{
obj* x_218; 
x_218 = lean::box(0);
x_119 = x_218;
goto lbl_120;
}
}
}
else
{
obj* x_219; unsigned char x_220; 
x_219 = lean::box_uint32(x_116);
x_220 = lean::nat_dec_le(x_219, x_192);
lean::dec(x_192);
lean::dec(x_219);
if (x_220 == 0)
{
obj* x_223; 
x_223 = lean::box(0);
x_117 = x_223;
goto lbl_118;
}
else
{
if (x_124 == 0)
{
obj* x_224; 
x_224 = lean::box(0);
x_117 = x_224;
goto lbl_118;
}
else
{
obj* x_225; 
x_225 = lean::box(0);
x_119 = x_225;
goto lbl_120;
}
}
}
}
}
else
{
obj* x_226; unsigned char x_227; 
x_226 = lean::box_uint32(x_116);
x_227 = lean::nat_dec_le(x_226, x_192);
lean::dec(x_192);
lean::dec(x_226);
if (x_227 == 0)
{
obj* x_230; 
x_230 = lean::box(0);
x_117 = x_230;
goto lbl_118;
}
else
{
if (x_124 == 0)
{
obj* x_231; 
x_231 = lean::box(0);
x_117 = x_231;
goto lbl_118;
}
else
{
obj* x_232; 
x_232 = lean::box(0);
x_119 = x_232;
goto lbl_120;
}
}
}
}
}
}
else
{
obj* x_236; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_86);
x_236 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_236, 0, x_5);
lean::cnstr_set(x_236, 1, x_6);
x_3 = x_236;
goto lbl_4;
}
lbl_90:
{
obj* x_237; obj* x_239; obj* x_241; obj* x_242; obj* x_243; 
x_237 = lean::cnstr_get(x_89, 0);
lean::inc(x_237);
x_239 = lean::cnstr_get(x_89, 1);
lean::inc(x_239);
if (lean::is_shared(x_89)) {
 lean::dec(x_89);
 x_241 = lean::box(0);
} else {
 lean::cnstr_release(x_89, 0);
 lean::cnstr_release(x_89, 1);
 x_241 = x_89;
}
x_242 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_86, x_237);
if (lean::is_scalar(x_241)) {
 x_243 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_243 = x_241;
}
lean::cnstr_set(x_243, 0, x_242);
lean::cnstr_set(x_243, 1, x_239);
x_3 = x_243;
goto lbl_4;
}
lbl_93:
{
if (lean::obj_tag(x_91) == 0)
{
obj* x_246; 
lean::dec(x_1);
lean::dec(x_0);
x_246 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_246, 0, x_91);
lean::cnstr_set(x_246, 1, x_92);
x_89 = x_246;
goto lbl_90;
}
else
{
obj* x_247; unsigned char x_249; obj* x_250; obj* x_251; 
x_247 = lean::cnstr_get(x_91, 0);
lean::inc(x_247);
x_249 = lean::cnstr_get_scalar<unsigned char>(x_91, sizeof(void*)*1);
if (x_249 == 0)
{
unsigned char x_254; 
lean::dec(x_91);
x_254 = lean::string_iterator_has_next(x_1);
if (x_254 == 0)
{
obj* x_255; obj* x_256; obj* x_257; obj* x_261; obj* x_262; obj* x_264; obj* x_267; obj* x_269; 
x_255 = lean::box(0);
x_256 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_257 = l_mjoin___rarg___closed__1;
lean::inc(x_255);
lean::inc(x_257);
lean::inc(x_256);
x_261 = l_lean_parser_monad__parsec_error___at___private_4089500695__finish__comment__block__aux___main___spec__1___rarg(x_256, x_257, x_255, x_255, x_0, x_1, x_92);
x_262 = lean::cnstr_get(x_261, 0);
lean::inc(x_262);
x_264 = lean::cnstr_get(x_261, 1);
lean::inc(x_264);
lean::dec(x_261);
x_267 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_267);
x_269 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_267, x_262);
x_250 = x_269;
x_251 = x_264;
goto lbl_252;
}
else
{
unsigned x_270; obj* x_271; obj* x_273; obj* x_275; obj* x_276; unsigned char x_277; unsigned char x_278; 
x_270 = lean::string_iterator_curr(x_1);
x_275 = lean::mk_nat_obj(65u);
x_276 = lean::mk_nat_obj(55296u);
x_277 = lean::nat_dec_lt(x_275, x_276);
if (x_277 == 0)
{
obj* x_280; unsigned char x_281; 
x_280 = lean::mk_nat_obj(57343u);
x_281 = lean::nat_dec_lt(x_280, x_275);
lean::dec(x_280);
if (x_281 == 0)
{
obj* x_284; obj* x_285; unsigned char x_286; 
lean::dec(x_275);
x_284 = lean::mk_nat_obj(0u);
x_285 = lean::box_uint32(x_270);
x_286 = lean::nat_dec_le(x_284, x_285);
lean::dec(x_285);
lean::dec(x_284);
if (x_286 == 0)
{
obj* x_290; 
lean::dec(x_276);
x_290 = lean::box(0);
x_271 = x_290;
goto lbl_272;
}
else
{
unsigned char x_291; 
x_291 = 1;
x_278 = x_291;
goto lbl_279;
}
}
else
{
obj* x_292; unsigned char x_293; 
x_292 = lean::mk_nat_obj(1114112u);
x_293 = lean::nat_dec_lt(x_275, x_292);
lean::dec(x_292);
if (x_293 == 0)
{
obj* x_296; obj* x_297; unsigned char x_298; 
lean::dec(x_275);
x_296 = lean::mk_nat_obj(0u);
x_297 = lean::box_uint32(x_270);
x_298 = lean::nat_dec_le(x_296, x_297);
lean::dec(x_297);
lean::dec(x_296);
if (x_298 == 0)
{
obj* x_302; 
lean::dec(x_276);
x_302 = lean::box(0);
x_271 = x_302;
goto lbl_272;
}
else
{
unsigned char x_303; 
x_303 = 1;
x_278 = x_303;
goto lbl_279;
}
}
else
{
obj* x_304; unsigned char x_305; 
x_304 = lean::box_uint32(x_270);
x_305 = lean::nat_dec_le(x_275, x_304);
lean::dec(x_304);
lean::dec(x_275);
if (x_305 == 0)
{
obj* x_309; 
lean::dec(x_276);
x_309 = lean::box(0);
x_271 = x_309;
goto lbl_272;
}
else
{
unsigned char x_310; 
x_310 = 1;
x_278 = x_310;
goto lbl_279;
}
}
}
}
else
{
obj* x_311; unsigned char x_312; 
x_311 = lean::box_uint32(x_270);
x_312 = lean::nat_dec_le(x_275, x_311);
lean::dec(x_311);
lean::dec(x_275);
if (x_312 == 0)
{
obj* x_316; 
lean::dec(x_276);
x_316 = lean::box(0);
x_271 = x_316;
goto lbl_272;
}
else
{
unsigned char x_317; 
x_317 = 1;
x_278 = x_317;
goto lbl_279;
}
}
lbl_272:
{
obj* x_319; obj* x_320; obj* x_322; obj* x_324; obj* x_325; obj* x_326; obj* x_329; obj* x_330; obj* x_332; obj* x_335; obj* x_337; 
lean::dec(x_271);
x_319 = l_char_quote__core(x_270);
x_320 = l_char_has__repr___closed__1;
lean::inc(x_320);
x_322 = lean::string_append(x_320, x_319);
lean::dec(x_319);
x_324 = lean::string_append(x_322, x_320);
x_325 = lean::box(0);
x_326 = l_mjoin___rarg___closed__1;
lean::inc(x_325);
lean::inc(x_326);
x_329 = l_lean_parser_monad__parsec_error___at___private_4089500695__finish__comment__block__aux___main___spec__1___rarg(x_324, x_326, x_325, x_325, x_0, x_1, x_92);
x_330 = lean::cnstr_get(x_329, 0);
lean::inc(x_330);
x_332 = lean::cnstr_get(x_329, 1);
lean::inc(x_332);
lean::dec(x_329);
x_335 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_335);
x_337 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_335, x_330);
x_250 = x_337;
x_251 = x_332;
goto lbl_252;
}
lbl_274:
{
obj* x_339; obj* x_340; obj* x_341; obj* x_342; 
lean::dec(x_273);
x_339 = lean::string_iterator_next(x_1);
x_340 = lean::box(0);
x_341 = lean::box_uint32(x_270);
x_342 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_342, 0, x_341);
lean::cnstr_set(x_342, 1, x_339);
lean::cnstr_set(x_342, 2, x_340);
x_250 = x_342;
x_251 = x_92;
goto lbl_252;
}
lbl_279:
{
obj* x_343; unsigned char x_344; 
x_343 = lean::mk_nat_obj(70u);
x_344 = lean::nat_dec_lt(x_343, x_276);
lean::dec(x_276);
if (x_344 == 0)
{
obj* x_346; unsigned char x_347; 
x_346 = lean::mk_nat_obj(57343u);
x_347 = lean::nat_dec_lt(x_346, x_343);
lean::dec(x_346);
if (x_347 == 0)
{
obj* x_350; obj* x_351; unsigned char x_352; 
lean::dec(x_343);
x_350 = lean::mk_nat_obj(0u);
x_351 = lean::box_uint32(x_270);
x_352 = lean::nat_dec_le(x_351, x_350);
lean::dec(x_350);
lean::dec(x_351);
if (x_352 == 0)
{
obj* x_355; 
x_355 = lean::box(0);
x_271 = x_355;
goto lbl_272;
}
else
{
if (x_278 == 0)
{
obj* x_356; 
x_356 = lean::box(0);
x_271 = x_356;
goto lbl_272;
}
else
{
obj* x_358; 
lean::dec(x_0);
x_358 = lean::box(0);
x_273 = x_358;
goto lbl_274;
}
}
}
else
{
obj* x_359; unsigned char x_360; 
x_359 = lean::mk_nat_obj(1114112u);
x_360 = lean::nat_dec_lt(x_343, x_359);
lean::dec(x_359);
if (x_360 == 0)
{
obj* x_363; obj* x_364; unsigned char x_365; 
lean::dec(x_343);
x_363 = lean::mk_nat_obj(0u);
x_364 = lean::box_uint32(x_270);
x_365 = lean::nat_dec_le(x_364, x_363);
lean::dec(x_363);
lean::dec(x_364);
if (x_365 == 0)
{
obj* x_368; 
x_368 = lean::box(0);
x_271 = x_368;
goto lbl_272;
}
else
{
if (x_278 == 0)
{
obj* x_369; 
x_369 = lean::box(0);
x_271 = x_369;
goto lbl_272;
}
else
{
obj* x_371; 
lean::dec(x_0);
x_371 = lean::box(0);
x_273 = x_371;
goto lbl_274;
}
}
}
else
{
obj* x_372; unsigned char x_373; 
x_372 = lean::box_uint32(x_270);
x_373 = lean::nat_dec_le(x_372, x_343);
lean::dec(x_343);
lean::dec(x_372);
if (x_373 == 0)
{
obj* x_376; 
x_376 = lean::box(0);
x_271 = x_376;
goto lbl_272;
}
else
{
if (x_278 == 0)
{
obj* x_377; 
x_377 = lean::box(0);
x_271 = x_377;
goto lbl_272;
}
else
{
obj* x_379; 
lean::dec(x_0);
x_379 = lean::box(0);
x_273 = x_379;
goto lbl_274;
}
}
}
}
}
else
{
obj* x_380; unsigned char x_381; 
x_380 = lean::box_uint32(x_270);
x_381 = lean::nat_dec_le(x_380, x_343);
lean::dec(x_343);
lean::dec(x_380);
if (x_381 == 0)
{
obj* x_384; 
x_384 = lean::box(0);
x_271 = x_384;
goto lbl_272;
}
else
{
if (x_278 == 0)
{
obj* x_385; 
x_385 = lean::box(0);
x_271 = x_385;
goto lbl_272;
}
else
{
obj* x_387; 
lean::dec(x_0);
x_387 = lean::box(0);
x_273 = x_387;
goto lbl_274;
}
}
}
}
}
}
else
{
obj* x_391; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_247);
x_391 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_391, 0, x_91);
lean::cnstr_set(x_391, 1, x_92);
x_89 = x_391;
goto lbl_90;
}
lbl_252:
{
if (lean::obj_tag(x_250) == 0)
{
obj* x_392; obj* x_394; obj* x_396; obj* x_398; obj* x_399; obj* x_400; unsigned char x_401; 
x_392 = lean::cnstr_get(x_250, 0);
lean::inc(x_392);
x_394 = lean::cnstr_get(x_250, 1);
lean::inc(x_394);
x_396 = lean::cnstr_get(x_250, 2);
lean::inc(x_396);
if (lean::is_shared(x_250)) {
 lean::dec(x_250);
 x_398 = lean::box(0);
} else {
 lean::cnstr_release(x_250, 0);
 lean::cnstr_release(x_250, 1);
 lean::cnstr_release(x_250, 2);
 x_398 = x_250;
}
x_399 = lean::mk_nat_obj(65u);
x_400 = lean::mk_nat_obj(55296u);
x_401 = lean::nat_dec_lt(x_399, x_400);
lean::dec(x_400);
if (x_401 == 0)
{
obj* x_403; unsigned char x_404; 
x_403 = lean::mk_nat_obj(57343u);
x_404 = lean::nat_dec_lt(x_403, x_399);
lean::dec(x_403);
if (x_404 == 0)
{
obj* x_407; obj* x_408; obj* x_411; obj* x_412; obj* x_415; obj* x_417; obj* x_418; obj* x_419; obj* x_420; 
lean::dec(x_399);
x_407 = lean::mk_nat_obj(0u);
x_408 = lean::nat_sub(x_392, x_407);
lean::dec(x_407);
lean::dec(x_392);
x_411 = lean::mk_nat_obj(10u);
x_412 = lean::nat_add(x_411, x_408);
lean::dec(x_408);
lean::dec(x_411);
x_415 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_415);
if (lean::is_scalar(x_398)) {
 x_417 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_417 = x_398;
}
lean::cnstr_set(x_417, 0, x_412);
lean::cnstr_set(x_417, 1, x_394);
lean::cnstr_set(x_417, 2, x_415);
x_418 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_396, x_417);
x_419 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_247, x_418);
x_420 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_420, 0, x_419);
lean::cnstr_set(x_420, 1, x_251);
x_89 = x_420;
goto lbl_90;
}
else
{
obj* x_421; unsigned char x_422; 
x_421 = lean::mk_nat_obj(1114112u);
x_422 = lean::nat_dec_lt(x_399, x_421);
lean::dec(x_421);
if (x_422 == 0)
{
obj* x_425; obj* x_426; obj* x_429; obj* x_430; obj* x_433; obj* x_435; obj* x_436; obj* x_437; obj* x_438; 
lean::dec(x_399);
x_425 = lean::mk_nat_obj(0u);
x_426 = lean::nat_sub(x_392, x_425);
lean::dec(x_425);
lean::dec(x_392);
x_429 = lean::mk_nat_obj(10u);
x_430 = lean::nat_add(x_429, x_426);
lean::dec(x_426);
lean::dec(x_429);
x_433 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_433);
if (lean::is_scalar(x_398)) {
 x_435 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_435 = x_398;
}
lean::cnstr_set(x_435, 0, x_430);
lean::cnstr_set(x_435, 1, x_394);
lean::cnstr_set(x_435, 2, x_433);
x_436 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_396, x_435);
x_437 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_247, x_436);
x_438 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_438, 0, x_437);
lean::cnstr_set(x_438, 1, x_251);
x_89 = x_438;
goto lbl_90;
}
else
{
obj* x_439; obj* x_442; obj* x_443; obj* x_446; obj* x_448; obj* x_449; obj* x_450; obj* x_451; 
x_439 = lean::nat_sub(x_392, x_399);
lean::dec(x_399);
lean::dec(x_392);
x_442 = lean::mk_nat_obj(10u);
x_443 = lean::nat_add(x_442, x_439);
lean::dec(x_439);
lean::dec(x_442);
x_446 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_446);
if (lean::is_scalar(x_398)) {
 x_448 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_448 = x_398;
}
lean::cnstr_set(x_448, 0, x_443);
lean::cnstr_set(x_448, 1, x_394);
lean::cnstr_set(x_448, 2, x_446);
x_449 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_396, x_448);
x_450 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_247, x_449);
x_451 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_451, 0, x_450);
lean::cnstr_set(x_451, 1, x_251);
x_89 = x_451;
goto lbl_90;
}
}
}
else
{
obj* x_452; obj* x_455; obj* x_456; obj* x_459; obj* x_461; obj* x_462; obj* x_463; obj* x_464; 
x_452 = lean::nat_sub(x_392, x_399);
lean::dec(x_399);
lean::dec(x_392);
x_455 = lean::mk_nat_obj(10u);
x_456 = lean::nat_add(x_455, x_452);
lean::dec(x_452);
lean::dec(x_455);
x_459 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_459);
if (lean::is_scalar(x_398)) {
 x_461 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_461 = x_398;
}
lean::cnstr_set(x_461, 0, x_456);
lean::cnstr_set(x_461, 1, x_394);
lean::cnstr_set(x_461, 2, x_459);
x_462 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_396, x_461);
x_463 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_247, x_462);
x_464 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_464, 0, x_463);
lean::cnstr_set(x_464, 1, x_251);
x_89 = x_464;
goto lbl_90;
}
}
else
{
obj* x_465; unsigned char x_467; obj* x_468; obj* x_469; obj* x_470; obj* x_471; obj* x_472; 
x_465 = lean::cnstr_get(x_250, 0);
lean::inc(x_465);
x_467 = lean::cnstr_get_scalar<unsigned char>(x_250, sizeof(void*)*1);
if (lean::is_shared(x_250)) {
 lean::dec(x_250);
 x_468 = lean::box(0);
} else {
 lean::cnstr_release(x_250, 0);
 x_468 = x_250;
}
if (lean::is_scalar(x_468)) {
 x_469 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_469 = x_468;
}
lean::cnstr_set(x_469, 0, x_465);
lean::cnstr_set_scalar(x_469, sizeof(void*)*1, x_467);
x_470 = x_469;
x_471 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_247, x_470);
x_472 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_472, 0, x_471);
lean::cnstr_set(x_472, 1, x_251);
x_89 = x_472;
goto lbl_90;
}
}
}
}
lbl_96:
{
if (lean::obj_tag(x_94) == 0)
{
obj* x_473; obj* x_475; obj* x_477; obj* x_479; obj* x_480; obj* x_481; unsigned char x_482; 
x_473 = lean::cnstr_get(x_94, 0);
lean::inc(x_473);
x_475 = lean::cnstr_get(x_94, 1);
lean::inc(x_475);
x_477 = lean::cnstr_get(x_94, 2);
lean::inc(x_477);
if (lean::is_shared(x_94)) {
 lean::dec(x_94);
 x_479 = lean::box(0);
} else {
 lean::cnstr_release(x_94, 0);
 lean::cnstr_release(x_94, 1);
 lean::cnstr_release(x_94, 2);
 x_479 = x_94;
}
x_480 = lean::mk_nat_obj(97u);
x_481 = lean::mk_nat_obj(55296u);
x_482 = lean::nat_dec_lt(x_480, x_481);
lean::dec(x_481);
if (x_482 == 0)
{
obj* x_484; unsigned char x_485; 
x_484 = lean::mk_nat_obj(57343u);
x_485 = lean::nat_dec_lt(x_484, x_480);
lean::dec(x_484);
if (x_485 == 0)
{
obj* x_488; obj* x_489; obj* x_492; obj* x_493; obj* x_496; obj* x_498; obj* x_499; 
lean::dec(x_480);
x_488 = lean::mk_nat_obj(0u);
x_489 = lean::nat_sub(x_473, x_488);
lean::dec(x_488);
lean::dec(x_473);
x_492 = lean::mk_nat_obj(10u);
x_493 = lean::nat_add(x_492, x_489);
lean::dec(x_489);
lean::dec(x_492);
x_496 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_496);
if (lean::is_scalar(x_479)) {
 x_498 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_498 = x_479;
}
lean::cnstr_set(x_498, 0, x_493);
lean::cnstr_set(x_498, 1, x_475);
lean::cnstr_set(x_498, 2, x_496);
x_499 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_477, x_498);
x_91 = x_499;
x_92 = x_95;
goto lbl_93;
}
else
{
obj* x_500; unsigned char x_501; 
x_500 = lean::mk_nat_obj(1114112u);
x_501 = lean::nat_dec_lt(x_480, x_500);
lean::dec(x_500);
if (x_501 == 0)
{
obj* x_504; obj* x_505; obj* x_508; obj* x_509; obj* x_512; obj* x_514; obj* x_515; 
lean::dec(x_480);
x_504 = lean::mk_nat_obj(0u);
x_505 = lean::nat_sub(x_473, x_504);
lean::dec(x_504);
lean::dec(x_473);
x_508 = lean::mk_nat_obj(10u);
x_509 = lean::nat_add(x_508, x_505);
lean::dec(x_505);
lean::dec(x_508);
x_512 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_512);
if (lean::is_scalar(x_479)) {
 x_514 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_514 = x_479;
}
lean::cnstr_set(x_514, 0, x_509);
lean::cnstr_set(x_514, 1, x_475);
lean::cnstr_set(x_514, 2, x_512);
x_515 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_477, x_514);
x_91 = x_515;
x_92 = x_95;
goto lbl_93;
}
else
{
obj* x_516; obj* x_519; obj* x_520; obj* x_523; obj* x_525; obj* x_526; 
x_516 = lean::nat_sub(x_473, x_480);
lean::dec(x_480);
lean::dec(x_473);
x_519 = lean::mk_nat_obj(10u);
x_520 = lean::nat_add(x_519, x_516);
lean::dec(x_516);
lean::dec(x_519);
x_523 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_523);
if (lean::is_scalar(x_479)) {
 x_525 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_525 = x_479;
}
lean::cnstr_set(x_525, 0, x_520);
lean::cnstr_set(x_525, 1, x_475);
lean::cnstr_set(x_525, 2, x_523);
x_526 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_477, x_525);
x_91 = x_526;
x_92 = x_95;
goto lbl_93;
}
}
}
else
{
obj* x_527; obj* x_530; obj* x_531; obj* x_534; obj* x_536; obj* x_537; 
x_527 = lean::nat_sub(x_473, x_480);
lean::dec(x_480);
lean::dec(x_473);
x_530 = lean::mk_nat_obj(10u);
x_531 = lean::nat_add(x_530, x_527);
lean::dec(x_527);
lean::dec(x_530);
x_534 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_534);
if (lean::is_scalar(x_479)) {
 x_536 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_536 = x_479;
}
lean::cnstr_set(x_536, 0, x_531);
lean::cnstr_set(x_536, 1, x_475);
lean::cnstr_set(x_536, 2, x_534);
x_537 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_477, x_536);
x_91 = x_537;
x_92 = x_95;
goto lbl_93;
}
}
else
{
obj* x_538; unsigned char x_540; obj* x_541; obj* x_542; obj* x_543; 
x_538 = lean::cnstr_get(x_94, 0);
lean::inc(x_538);
x_540 = lean::cnstr_get_scalar<unsigned char>(x_94, sizeof(void*)*1);
if (lean::is_shared(x_94)) {
 lean::dec(x_94);
 x_541 = lean::box(0);
} else {
 lean::cnstr_release(x_94, 0);
 x_541 = x_94;
}
if (lean::is_scalar(x_541)) {
 x_542 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_542 = x_541;
}
lean::cnstr_set(x_542, 0, x_538);
lean::cnstr_set_scalar(x_542, sizeof(void*)*1, x_540);
x_543 = x_542;
x_91 = x_543;
x_92 = x_95;
goto lbl_93;
}
}
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
obj* l_lean_parser_monad__parsec_unexpected__at___at_lean_parser_string__lit_x_27___spec__6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; obj* x_9; 
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_1);
x_6 = lean::box(0);
x_7 = l_mjoin___rarg___closed__1;
lean::inc(x_7);
x_9 = l_lean_parser_monad__parsec_error___at___private_4089500695__finish__comment__block__aux___main___spec__1___rarg(x_0, x_7, x_5, x_6, x_2, x_3, x_4);
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
x_5 = l_lean_parser_monad__parsec_any___at___private_4089500695__finish__comment__block__aux___main___spec__2(x_0, x_1, x_2);
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
obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_18; obj* x_20; obj* x_22; obj* x_24; obj* x_26; obj* x_28; obj* x_30; obj* x_32; obj* x_34; obj* x_35; unsigned char x_36; unsigned x_38; 
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
x_34 = lean::mk_nat_obj(92u);
x_35 = lean::mk_nat_obj(55296u);
x_36 = lean::nat_dec_lt(x_34, x_35);
lean::dec(x_35);
if (x_36 == 0)
{
obj* x_40; unsigned char x_41; 
x_40 = lean::mk_nat_obj(57343u);
x_41 = lean::nat_dec_lt(x_40, x_34);
lean::dec(x_40);
if (x_41 == 0)
{
obj* x_44; unsigned x_45; 
lean::dec(x_34);
x_44 = lean::mk_nat_obj(0u);
x_45 = lean::unbox_uint32(x_44);
lean::dec(x_44);
x_38 = x_45;
goto lbl_39;
}
else
{
obj* x_47; unsigned char x_48; 
x_47 = lean::mk_nat_obj(1114112u);
x_48 = lean::nat_dec_lt(x_34, x_47);
lean::dec(x_47);
if (x_48 == 0)
{
obj* x_51; unsigned x_52; 
lean::dec(x_34);
x_51 = lean::mk_nat_obj(0u);
x_52 = lean::unbox_uint32(x_51);
lean::dec(x_51);
x_38 = x_52;
goto lbl_39;
}
else
{
unsigned x_54; 
x_54 = lean::unbox_uint32(x_34);
lean::dec(x_34);
x_38 = x_54;
goto lbl_39;
}
}
}
else
{
unsigned x_56; 
x_56 = lean::unbox_uint32(x_34);
lean::dec(x_34);
x_38 = x_56;
goto lbl_39;
}
lbl_19:
{
obj* x_60; obj* x_61; obj* x_63; 
lean::dec(x_18);
lean::inc(x_0);
x_60 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__4(x_0, x_13, x_8);
x_61 = lean::cnstr_get(x_60, 0);
lean::inc(x_61);
x_63 = lean::cnstr_get(x_60, 1);
lean::inc(x_63);
lean::dec(x_60);
if (lean::obj_tag(x_61) == 0)
{
obj* x_66; obj* x_68; obj* x_70; obj* x_74; obj* x_75; obj* x_77; 
x_66 = lean::cnstr_get(x_61, 0);
lean::inc(x_66);
x_68 = lean::cnstr_get(x_61, 1);
lean::inc(x_68);
x_70 = lean::cnstr_get(x_61, 2);
lean::inc(x_70);
lean::dec(x_61);
lean::inc(x_0);
x_74 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__4(x_0, x_68, x_63);
x_75 = lean::cnstr_get(x_74, 0);
lean::inc(x_75);
x_77 = lean::cnstr_get(x_74, 1);
lean::inc(x_77);
lean::dec(x_74);
if (lean::obj_tag(x_75) == 0)
{
obj* x_80; obj* x_82; obj* x_84; obj* x_88; obj* x_89; obj* x_91; 
x_80 = lean::cnstr_get(x_75, 0);
lean::inc(x_80);
x_82 = lean::cnstr_get(x_75, 1);
lean::inc(x_82);
x_84 = lean::cnstr_get(x_75, 2);
lean::inc(x_84);
lean::dec(x_75);
lean::inc(x_0);
x_88 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__4(x_0, x_82, x_77);
x_89 = lean::cnstr_get(x_88, 0);
lean::inc(x_89);
x_91 = lean::cnstr_get(x_88, 1);
lean::inc(x_91);
lean::dec(x_88);
if (lean::obj_tag(x_89) == 0)
{
obj* x_94; obj* x_96; obj* x_98; obj* x_101; obj* x_102; obj* x_104; 
x_94 = lean::cnstr_get(x_89, 0);
lean::inc(x_94);
x_96 = lean::cnstr_get(x_89, 1);
lean::inc(x_96);
x_98 = lean::cnstr_get(x_89, 2);
lean::inc(x_98);
lean::dec(x_89);
x_101 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__4(x_0, x_96, x_91);
x_102 = lean::cnstr_get(x_101, 0);
lean::inc(x_102);
x_104 = lean::cnstr_get(x_101, 1);
lean::inc(x_104);
lean::dec(x_101);
if (lean::obj_tag(x_102) == 0)
{
obj* x_107; obj* x_109; obj* x_111; obj* x_114; obj* x_115; obj* x_117; obj* x_120; obj* x_122; obj* x_125; obj* x_128; obj* x_131; unsigned char x_132; 
x_107 = lean::cnstr_get(x_102, 0);
lean::inc(x_107);
x_109 = lean::cnstr_get(x_102, 1);
lean::inc(x_109);
x_111 = lean::cnstr_get(x_102, 2);
lean::inc(x_111);
lean::dec(x_102);
x_114 = lean::mk_nat_obj(16u);
x_115 = lean::nat_mul(x_114, x_66);
lean::dec(x_66);
x_117 = lean::nat_add(x_115, x_80);
lean::dec(x_80);
lean::dec(x_115);
x_120 = lean::nat_mul(x_114, x_117);
lean::dec(x_117);
x_122 = lean::nat_add(x_120, x_94);
lean::dec(x_94);
lean::dec(x_120);
x_125 = lean::nat_mul(x_114, x_122);
lean::dec(x_122);
lean::dec(x_114);
x_128 = lean::nat_add(x_125, x_107);
lean::dec(x_107);
lean::dec(x_125);
x_131 = lean::mk_nat_obj(55296u);
x_132 = lean::nat_dec_lt(x_128, x_131);
lean::dec(x_131);
if (x_132 == 0)
{
obj* x_134; unsigned char x_135; 
x_134 = lean::mk_nat_obj(57343u);
x_135 = lean::nat_dec_lt(x_134, x_128);
lean::dec(x_134);
if (x_135 == 0)
{
obj* x_138; obj* x_139; obj* x_141; obj* x_142; obj* x_143; obj* x_144; obj* x_145; obj* x_146; obj* x_148; obj* x_149; 
lean::dec(x_128);
x_138 = lean::mk_nat_obj(0u);
x_139 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_139);
if (lean::is_scalar(x_17)) {
 x_141 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_141 = x_17;
}
lean::cnstr_set(x_141, 0, x_138);
lean::cnstr_set(x_141, 1, x_109);
lean::cnstr_set(x_141, 2, x_139);
x_142 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_111, x_141);
x_143 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_98, x_142);
x_144 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_84, x_143);
x_145 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_70, x_144);
x_146 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_145);
lean::inc(x_139);
x_148 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_139, x_146);
if (lean::is_scalar(x_10)) {
 x_149 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_149 = x_10;
}
lean::cnstr_set(x_149, 0, x_148);
lean::cnstr_set(x_149, 1, x_104);
return x_149;
}
else
{
obj* x_150; unsigned char x_151; 
x_150 = lean::mk_nat_obj(1114112u);
x_151 = lean::nat_dec_lt(x_128, x_150);
lean::dec(x_150);
if (x_151 == 0)
{
obj* x_154; obj* x_155; obj* x_157; obj* x_158; obj* x_159; obj* x_160; obj* x_161; obj* x_162; obj* x_164; obj* x_165; 
lean::dec(x_128);
x_154 = lean::mk_nat_obj(0u);
x_155 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_155);
if (lean::is_scalar(x_17)) {
 x_157 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_157 = x_17;
}
lean::cnstr_set(x_157, 0, x_154);
lean::cnstr_set(x_157, 1, x_109);
lean::cnstr_set(x_157, 2, x_155);
x_158 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_111, x_157);
x_159 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_98, x_158);
x_160 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_84, x_159);
x_161 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_70, x_160);
x_162 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_161);
lean::inc(x_155);
x_164 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_155, x_162);
if (lean::is_scalar(x_10)) {
 x_165 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_165 = x_10;
}
lean::cnstr_set(x_165, 0, x_164);
lean::cnstr_set(x_165, 1, x_104);
return x_165;
}
else
{
obj* x_166; obj* x_168; obj* x_169; obj* x_170; obj* x_171; obj* x_172; obj* x_173; obj* x_175; obj* x_176; 
x_166 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_166);
if (lean::is_scalar(x_17)) {
 x_168 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_168 = x_17;
}
lean::cnstr_set(x_168, 0, x_128);
lean::cnstr_set(x_168, 1, x_109);
lean::cnstr_set(x_168, 2, x_166);
x_169 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_111, x_168);
x_170 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_98, x_169);
x_171 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_84, x_170);
x_172 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_70, x_171);
x_173 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_172);
lean::inc(x_166);
x_175 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_166, x_173);
if (lean::is_scalar(x_10)) {
 x_176 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_176 = x_10;
}
lean::cnstr_set(x_176, 0, x_175);
lean::cnstr_set(x_176, 1, x_104);
return x_176;
}
}
}
else
{
obj* x_177; obj* x_179; obj* x_180; obj* x_181; obj* x_182; obj* x_183; obj* x_184; obj* x_186; obj* x_187; 
x_177 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_177);
if (lean::is_scalar(x_17)) {
 x_179 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_179 = x_17;
}
lean::cnstr_set(x_179, 0, x_128);
lean::cnstr_set(x_179, 1, x_109);
lean::cnstr_set(x_179, 2, x_177);
x_180 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_111, x_179);
x_181 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_98, x_180);
x_182 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_84, x_181);
x_183 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_70, x_182);
x_184 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_183);
lean::inc(x_177);
x_186 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_177, x_184);
if (lean::is_scalar(x_10)) {
 x_187 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_187 = x_10;
}
lean::cnstr_set(x_187, 0, x_186);
lean::cnstr_set(x_187, 1, x_104);
return x_187;
}
}
else
{
obj* x_192; unsigned char x_194; obj* x_195; obj* x_196; obj* x_197; obj* x_198; obj* x_199; obj* x_200; obj* x_201; obj* x_202; obj* x_204; obj* x_205; 
lean::dec(x_17);
lean::dec(x_80);
lean::dec(x_66);
lean::dec(x_94);
x_192 = lean::cnstr_get(x_102, 0);
lean::inc(x_192);
x_194 = lean::cnstr_get_scalar<unsigned char>(x_102, sizeof(void*)*1);
if (lean::is_shared(x_102)) {
 lean::dec(x_102);
 x_195 = lean::box(0);
} else {
 lean::cnstr_release(x_102, 0);
 x_195 = x_102;
}
if (lean::is_scalar(x_195)) {
 x_196 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_196 = x_195;
}
lean::cnstr_set(x_196, 0, x_192);
lean::cnstr_set_scalar(x_196, sizeof(void*)*1, x_194);
x_197 = x_196;
x_198 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_98, x_197);
x_199 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_84, x_198);
x_200 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_70, x_199);
x_201 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_200);
x_202 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_202);
x_204 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_202, x_201);
if (lean::is_scalar(x_10)) {
 x_205 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_205 = x_10;
}
lean::cnstr_set(x_205, 0, x_204);
lean::cnstr_set(x_205, 1, x_104);
return x_205;
}
}
else
{
obj* x_210; unsigned char x_212; obj* x_213; obj* x_214; obj* x_215; obj* x_216; obj* x_217; obj* x_218; obj* x_219; obj* x_221; obj* x_222; 
lean::dec(x_17);
lean::dec(x_0);
lean::dec(x_80);
lean::dec(x_66);
x_210 = lean::cnstr_get(x_89, 0);
lean::inc(x_210);
x_212 = lean::cnstr_get_scalar<unsigned char>(x_89, sizeof(void*)*1);
if (lean::is_shared(x_89)) {
 lean::dec(x_89);
 x_213 = lean::box(0);
} else {
 lean::cnstr_release(x_89, 0);
 x_213 = x_89;
}
if (lean::is_scalar(x_213)) {
 x_214 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_214 = x_213;
}
lean::cnstr_set(x_214, 0, x_210);
lean::cnstr_set_scalar(x_214, sizeof(void*)*1, x_212);
x_215 = x_214;
x_216 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_84, x_215);
x_217 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_70, x_216);
x_218 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_217);
x_219 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_219);
x_221 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_219, x_218);
if (lean::is_scalar(x_10)) {
 x_222 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_222 = x_10;
}
lean::cnstr_set(x_222, 0, x_221);
lean::cnstr_set(x_222, 1, x_91);
return x_222;
}
}
else
{
obj* x_226; unsigned char x_228; obj* x_229; obj* x_230; obj* x_231; obj* x_232; obj* x_233; obj* x_234; obj* x_236; obj* x_237; 
lean::dec(x_17);
lean::dec(x_0);
lean::dec(x_66);
x_226 = lean::cnstr_get(x_75, 0);
lean::inc(x_226);
x_228 = lean::cnstr_get_scalar<unsigned char>(x_75, sizeof(void*)*1);
if (lean::is_shared(x_75)) {
 lean::dec(x_75);
 x_229 = lean::box(0);
} else {
 lean::cnstr_release(x_75, 0);
 x_229 = x_75;
}
if (lean::is_scalar(x_229)) {
 x_230 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_230 = x_229;
}
lean::cnstr_set(x_230, 0, x_226);
lean::cnstr_set_scalar(x_230, sizeof(void*)*1, x_228);
x_231 = x_230;
x_232 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_70, x_231);
x_233 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_232);
x_234 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_234);
x_236 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_234, x_233);
if (lean::is_scalar(x_10)) {
 x_237 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_237 = x_10;
}
lean::cnstr_set(x_237, 0, x_236);
lean::cnstr_set(x_237, 1, x_77);
return x_237;
}
}
else
{
obj* x_240; unsigned char x_242; obj* x_243; obj* x_244; obj* x_245; obj* x_246; obj* x_247; obj* x_249; obj* x_250; 
lean::dec(x_17);
lean::dec(x_0);
x_240 = lean::cnstr_get(x_61, 0);
lean::inc(x_240);
x_242 = lean::cnstr_get_scalar<unsigned char>(x_61, sizeof(void*)*1);
if (lean::is_shared(x_61)) {
 lean::dec(x_61);
 x_243 = lean::box(0);
} else {
 lean::cnstr_release(x_61, 0);
 x_243 = x_61;
}
if (lean::is_scalar(x_243)) {
 x_244 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_244 = x_243;
}
lean::cnstr_set(x_244, 0, x_240);
lean::cnstr_set_scalar(x_244, sizeof(void*)*1, x_242);
x_245 = x_244;
x_246 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_245);
x_247 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_247);
x_249 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_247, x_246);
if (lean::is_scalar(x_10)) {
 x_250 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_250 = x_10;
}
lean::cnstr_set(x_250, 0, x_249);
lean::cnstr_set(x_250, 1, x_63);
return x_250;
}
}
lbl_21:
{
obj* x_252; obj* x_253; unsigned char x_254; 
lean::dec(x_20);
x_252 = lean::mk_nat_obj(117u);
x_253 = lean::mk_nat_obj(55296u);
x_254 = lean::nat_dec_lt(x_252, x_253);
lean::dec(x_253);
if (x_254 == 0)
{
obj* x_256; unsigned char x_257; 
x_256 = lean::mk_nat_obj(57343u);
x_257 = lean::nat_dec_lt(x_256, x_252);
lean::dec(x_256);
if (x_257 == 0)
{
obj* x_260; unsigned char x_261; 
lean::dec(x_252);
x_260 = lean::mk_nat_obj(0u);
x_261 = lean::nat_dec_eq(x_11, x_260);
lean::dec(x_260);
lean::dec(x_11);
if (x_261 == 0)
{
obj* x_266; obj* x_268; obj* x_269; obj* x_271; obj* x_273; obj* x_274; obj* x_275; obj* x_277; obj* x_278; 
lean::dec(x_17);
lean::dec(x_10);
x_266 = l_lean_parser_parse__quoted__char___rarg___lambda__7___closed__1;
lean::inc(x_266);
x_268 = l_lean_parser_monad__parsec_unexpected__at___at_lean_parser_string__lit_x_27___spec__6___rarg(x_266, x_1, x_0, x_13, x_8);
x_269 = lean::cnstr_get(x_268, 0);
lean::inc(x_269);
x_271 = lean::cnstr_get(x_268, 1);
lean::inc(x_271);
if (lean::is_shared(x_268)) {
 lean::dec(x_268);
 x_273 = lean::box(0);
} else {
 lean::cnstr_release(x_268, 0);
 lean::cnstr_release(x_268, 1);
 x_273 = x_268;
}
x_274 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_269);
x_275 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_275);
x_277 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_275, x_274);
if (lean::is_scalar(x_273)) {
 x_278 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_278 = x_273;
}
lean::cnstr_set(x_278, 0, x_277);
lean::cnstr_set(x_278, 1, x_271);
return x_278;
}
else
{
obj* x_280; 
lean::dec(x_1);
x_280 = lean::box(0);
x_18 = x_280;
goto lbl_19;
}
}
else
{
obj* x_281; unsigned char x_282; 
x_281 = lean::mk_nat_obj(1114112u);
x_282 = lean::nat_dec_lt(x_252, x_281);
lean::dec(x_281);
if (x_282 == 0)
{
obj* x_285; unsigned char x_286; 
lean::dec(x_252);
x_285 = lean::mk_nat_obj(0u);
x_286 = lean::nat_dec_eq(x_11, x_285);
lean::dec(x_285);
lean::dec(x_11);
if (x_286 == 0)
{
obj* x_291; obj* x_293; obj* x_294; obj* x_296; obj* x_298; obj* x_299; obj* x_300; obj* x_302; obj* x_303; 
lean::dec(x_17);
lean::dec(x_10);
x_291 = l_lean_parser_parse__quoted__char___rarg___lambda__7___closed__1;
lean::inc(x_291);
x_293 = l_lean_parser_monad__parsec_unexpected__at___at_lean_parser_string__lit_x_27___spec__6___rarg(x_291, x_1, x_0, x_13, x_8);
x_294 = lean::cnstr_get(x_293, 0);
lean::inc(x_294);
x_296 = lean::cnstr_get(x_293, 1);
lean::inc(x_296);
if (lean::is_shared(x_293)) {
 lean::dec(x_293);
 x_298 = lean::box(0);
} else {
 lean::cnstr_release(x_293, 0);
 lean::cnstr_release(x_293, 1);
 x_298 = x_293;
}
x_299 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_294);
x_300 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_300);
x_302 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_300, x_299);
if (lean::is_scalar(x_298)) {
 x_303 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_303 = x_298;
}
lean::cnstr_set(x_303, 0, x_302);
lean::cnstr_set(x_303, 1, x_296);
return x_303;
}
else
{
obj* x_305; 
lean::dec(x_1);
x_305 = lean::box(0);
x_18 = x_305;
goto lbl_19;
}
}
else
{
unsigned char x_306; 
x_306 = lean::nat_dec_eq(x_11, x_252);
lean::dec(x_252);
lean::dec(x_11);
if (x_306 == 0)
{
obj* x_311; obj* x_313; obj* x_314; obj* x_316; obj* x_318; obj* x_319; obj* x_320; obj* x_322; obj* x_323; 
lean::dec(x_17);
lean::dec(x_10);
x_311 = l_lean_parser_parse__quoted__char___rarg___lambda__7___closed__1;
lean::inc(x_311);
x_313 = l_lean_parser_monad__parsec_unexpected__at___at_lean_parser_string__lit_x_27___spec__6___rarg(x_311, x_1, x_0, x_13, x_8);
x_314 = lean::cnstr_get(x_313, 0);
lean::inc(x_314);
x_316 = lean::cnstr_get(x_313, 1);
lean::inc(x_316);
if (lean::is_shared(x_313)) {
 lean::dec(x_313);
 x_318 = lean::box(0);
} else {
 lean::cnstr_release(x_313, 0);
 lean::cnstr_release(x_313, 1);
 x_318 = x_313;
}
x_319 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_314);
x_320 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_320);
x_322 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_320, x_319);
if (lean::is_scalar(x_318)) {
 x_323 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_323 = x_318;
}
lean::cnstr_set(x_323, 0, x_322);
lean::cnstr_set(x_323, 1, x_316);
return x_323;
}
else
{
obj* x_325; 
lean::dec(x_1);
x_325 = lean::box(0);
x_18 = x_325;
goto lbl_19;
}
}
}
}
else
{
unsigned char x_326; 
x_326 = lean::nat_dec_eq(x_11, x_252);
lean::dec(x_252);
lean::dec(x_11);
if (x_326 == 0)
{
obj* x_331; obj* x_333; obj* x_334; obj* x_336; obj* x_338; obj* x_339; obj* x_340; obj* x_342; obj* x_343; 
lean::dec(x_17);
lean::dec(x_10);
x_331 = l_lean_parser_parse__quoted__char___rarg___lambda__7___closed__1;
lean::inc(x_331);
x_333 = l_lean_parser_monad__parsec_unexpected__at___at_lean_parser_string__lit_x_27___spec__6___rarg(x_331, x_1, x_0, x_13, x_8);
x_334 = lean::cnstr_get(x_333, 0);
lean::inc(x_334);
x_336 = lean::cnstr_get(x_333, 1);
lean::inc(x_336);
if (lean::is_shared(x_333)) {
 lean::dec(x_333);
 x_338 = lean::box(0);
} else {
 lean::cnstr_release(x_333, 0);
 lean::cnstr_release(x_333, 1);
 x_338 = x_333;
}
x_339 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_334);
x_340 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_340);
x_342 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_340, x_339);
if (lean::is_scalar(x_338)) {
 x_343 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_343 = x_338;
}
lean::cnstr_set(x_343, 0, x_342);
lean::cnstr_set(x_343, 1, x_336);
return x_343;
}
else
{
obj* x_345; 
lean::dec(x_1);
x_345 = lean::box(0);
x_18 = x_345;
goto lbl_19;
}
}
}
lbl_23:
{
obj* x_348; obj* x_349; obj* x_351; obj* x_353; 
lean::dec(x_22);
lean::inc(x_0);
x_348 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__4(x_0, x_13, x_8);
x_349 = lean::cnstr_get(x_348, 0);
lean::inc(x_349);
x_351 = lean::cnstr_get(x_348, 1);
lean::inc(x_351);
if (lean::is_shared(x_348)) {
 lean::dec(x_348);
 x_353 = lean::box(0);
} else {
 lean::cnstr_release(x_348, 0);
 lean::cnstr_release(x_348, 1);
 x_353 = x_348;
}
if (lean::obj_tag(x_349) == 0)
{
obj* x_354; obj* x_356; obj* x_358; obj* x_360; obj* x_361; obj* x_362; obj* x_364; 
x_354 = lean::cnstr_get(x_349, 0);
lean::inc(x_354);
x_356 = lean::cnstr_get(x_349, 1);
lean::inc(x_356);
x_358 = lean::cnstr_get(x_349, 2);
lean::inc(x_358);
if (lean::is_shared(x_349)) {
 lean::dec(x_349);
 x_360 = lean::box(0);
} else {
 lean::cnstr_release(x_349, 0);
 lean::cnstr_release(x_349, 1);
 lean::cnstr_release(x_349, 2);
 x_360 = x_349;
}
x_361 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__4(x_0, x_356, x_351);
x_362 = lean::cnstr_get(x_361, 0);
lean::inc(x_362);
x_364 = lean::cnstr_get(x_361, 1);
lean::inc(x_364);
lean::dec(x_361);
if (lean::obj_tag(x_362) == 0)
{
obj* x_367; obj* x_369; obj* x_371; obj* x_374; obj* x_375; obj* x_378; obj* x_381; unsigned char x_382; 
x_367 = lean::cnstr_get(x_362, 0);
lean::inc(x_367);
x_369 = lean::cnstr_get(x_362, 1);
lean::inc(x_369);
x_371 = lean::cnstr_get(x_362, 2);
lean::inc(x_371);
lean::dec(x_362);
x_374 = lean::mk_nat_obj(16u);
x_375 = lean::nat_mul(x_374, x_354);
lean::dec(x_354);
lean::dec(x_374);
x_378 = lean::nat_add(x_375, x_367);
lean::dec(x_367);
lean::dec(x_375);
x_381 = lean::mk_nat_obj(55296u);
x_382 = lean::nat_dec_lt(x_378, x_381);
lean::dec(x_381);
if (x_382 == 0)
{
obj* x_384; unsigned char x_385; 
x_384 = lean::mk_nat_obj(57343u);
x_385 = lean::nat_dec_lt(x_384, x_378);
lean::dec(x_384);
if (x_385 == 0)
{
obj* x_388; obj* x_389; obj* x_391; obj* x_392; obj* x_393; obj* x_394; obj* x_396; obj* x_397; 
lean::dec(x_378);
x_388 = lean::mk_nat_obj(0u);
x_389 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_389);
if (lean::is_scalar(x_360)) {
 x_391 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_391 = x_360;
}
lean::cnstr_set(x_391, 0, x_388);
lean::cnstr_set(x_391, 1, x_369);
lean::cnstr_set(x_391, 2, x_389);
x_392 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_371, x_391);
x_393 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_358, x_392);
x_394 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_393);
lean::inc(x_389);
x_396 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_389, x_394);
if (lean::is_scalar(x_353)) {
 x_397 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_397 = x_353;
}
lean::cnstr_set(x_397, 0, x_396);
lean::cnstr_set(x_397, 1, x_364);
return x_397;
}
else
{
obj* x_398; unsigned char x_399; 
x_398 = lean::mk_nat_obj(1114112u);
x_399 = lean::nat_dec_lt(x_378, x_398);
lean::dec(x_398);
if (x_399 == 0)
{
obj* x_402; obj* x_403; obj* x_405; obj* x_406; obj* x_407; obj* x_408; obj* x_410; obj* x_411; 
lean::dec(x_378);
x_402 = lean::mk_nat_obj(0u);
x_403 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_403);
if (lean::is_scalar(x_360)) {
 x_405 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_405 = x_360;
}
lean::cnstr_set(x_405, 0, x_402);
lean::cnstr_set(x_405, 1, x_369);
lean::cnstr_set(x_405, 2, x_403);
x_406 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_371, x_405);
x_407 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_358, x_406);
x_408 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_407);
lean::inc(x_403);
x_410 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_403, x_408);
if (lean::is_scalar(x_353)) {
 x_411 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_411 = x_353;
}
lean::cnstr_set(x_411, 0, x_410);
lean::cnstr_set(x_411, 1, x_364);
return x_411;
}
else
{
obj* x_412; obj* x_414; obj* x_415; obj* x_416; obj* x_417; obj* x_419; obj* x_420; 
x_412 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_412);
if (lean::is_scalar(x_360)) {
 x_414 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_414 = x_360;
}
lean::cnstr_set(x_414, 0, x_378);
lean::cnstr_set(x_414, 1, x_369);
lean::cnstr_set(x_414, 2, x_412);
x_415 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_371, x_414);
x_416 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_358, x_415);
x_417 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_416);
lean::inc(x_412);
x_419 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_412, x_417);
if (lean::is_scalar(x_353)) {
 x_420 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_420 = x_353;
}
lean::cnstr_set(x_420, 0, x_419);
lean::cnstr_set(x_420, 1, x_364);
return x_420;
}
}
}
else
{
obj* x_421; obj* x_423; obj* x_424; obj* x_425; obj* x_426; obj* x_428; obj* x_429; 
x_421 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_421);
if (lean::is_scalar(x_360)) {
 x_423 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_423 = x_360;
}
lean::cnstr_set(x_423, 0, x_378);
lean::cnstr_set(x_423, 1, x_369);
lean::cnstr_set(x_423, 2, x_421);
x_424 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_371, x_423);
x_425 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_358, x_424);
x_426 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_425);
lean::inc(x_421);
x_428 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_421, x_426);
if (lean::is_scalar(x_353)) {
 x_429 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_429 = x_353;
}
lean::cnstr_set(x_429, 0, x_428);
lean::cnstr_set(x_429, 1, x_364);
return x_429;
}
}
else
{
obj* x_432; unsigned char x_434; obj* x_435; obj* x_436; obj* x_437; obj* x_438; obj* x_439; obj* x_440; obj* x_442; obj* x_443; 
lean::dec(x_360);
lean::dec(x_354);
x_432 = lean::cnstr_get(x_362, 0);
lean::inc(x_432);
x_434 = lean::cnstr_get_scalar<unsigned char>(x_362, sizeof(void*)*1);
if (lean::is_shared(x_362)) {
 lean::dec(x_362);
 x_435 = lean::box(0);
} else {
 lean::cnstr_release(x_362, 0);
 x_435 = x_362;
}
if (lean::is_scalar(x_435)) {
 x_436 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_436 = x_435;
}
lean::cnstr_set(x_436, 0, x_432);
lean::cnstr_set_scalar(x_436, sizeof(void*)*1, x_434);
x_437 = x_436;
x_438 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_358, x_437);
x_439 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_438);
x_440 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_440);
x_442 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_440, x_439);
if (lean::is_scalar(x_353)) {
 x_443 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_443 = x_353;
}
lean::cnstr_set(x_443, 0, x_442);
lean::cnstr_set(x_443, 1, x_364);
return x_443;
}
}
else
{
obj* x_445; unsigned char x_447; obj* x_448; obj* x_449; obj* x_450; obj* x_451; obj* x_452; obj* x_454; obj* x_455; 
lean::dec(x_0);
x_445 = lean::cnstr_get(x_349, 0);
lean::inc(x_445);
x_447 = lean::cnstr_get_scalar<unsigned char>(x_349, sizeof(void*)*1);
if (lean::is_shared(x_349)) {
 lean::dec(x_349);
 x_448 = lean::box(0);
} else {
 lean::cnstr_release(x_349, 0);
 x_448 = x_349;
}
if (lean::is_scalar(x_448)) {
 x_449 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_449 = x_448;
}
lean::cnstr_set(x_449, 0, x_445);
lean::cnstr_set_scalar(x_449, sizeof(void*)*1, x_447);
x_450 = x_449;
x_451 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_450);
x_452 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_452);
x_454 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_452, x_451);
if (lean::is_scalar(x_353)) {
 x_455 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_455 = x_353;
}
lean::cnstr_set(x_455, 0, x_454);
lean::cnstr_set(x_455, 1, x_351);
return x_455;
}
}
lbl_25:
{
obj* x_457; obj* x_458; unsigned char x_459; 
lean::dec(x_24);
x_457 = lean::mk_nat_obj(120u);
x_458 = lean::mk_nat_obj(55296u);
x_459 = lean::nat_dec_lt(x_457, x_458);
lean::dec(x_458);
if (x_459 == 0)
{
obj* x_461; unsigned char x_462; 
x_461 = lean::mk_nat_obj(57343u);
x_462 = lean::nat_dec_lt(x_461, x_457);
lean::dec(x_461);
if (x_462 == 0)
{
obj* x_465; unsigned char x_466; 
lean::dec(x_457);
x_465 = lean::mk_nat_obj(0u);
x_466 = lean::nat_dec_eq(x_11, x_465);
lean::dec(x_465);
if (x_466 == 0)
{
obj* x_468; 
x_468 = lean::box(0);
x_20 = x_468;
goto lbl_21;
}
else
{
obj* x_473; 
lean::dec(x_17);
lean::dec(x_11);
lean::dec(x_1);
lean::dec(x_10);
x_473 = lean::box(0);
x_22 = x_473;
goto lbl_23;
}
}
else
{
obj* x_474; unsigned char x_475; 
x_474 = lean::mk_nat_obj(1114112u);
x_475 = lean::nat_dec_lt(x_457, x_474);
lean::dec(x_474);
if (x_475 == 0)
{
obj* x_478; unsigned char x_479; 
lean::dec(x_457);
x_478 = lean::mk_nat_obj(0u);
x_479 = lean::nat_dec_eq(x_11, x_478);
lean::dec(x_478);
if (x_479 == 0)
{
obj* x_481; 
x_481 = lean::box(0);
x_20 = x_481;
goto lbl_21;
}
else
{
obj* x_486; 
lean::dec(x_17);
lean::dec(x_11);
lean::dec(x_1);
lean::dec(x_10);
x_486 = lean::box(0);
x_22 = x_486;
goto lbl_23;
}
}
else
{
unsigned char x_487; 
x_487 = lean::nat_dec_eq(x_11, x_457);
lean::dec(x_457);
if (x_487 == 0)
{
obj* x_489; 
x_489 = lean::box(0);
x_20 = x_489;
goto lbl_21;
}
else
{
obj* x_494; 
lean::dec(x_17);
lean::dec(x_11);
lean::dec(x_1);
lean::dec(x_10);
x_494 = lean::box(0);
x_22 = x_494;
goto lbl_23;
}
}
}
}
else
{
unsigned char x_495; 
x_495 = lean::nat_dec_eq(x_11, x_457);
lean::dec(x_457);
if (x_495 == 0)
{
obj* x_497; 
x_497 = lean::box(0);
x_20 = x_497;
goto lbl_21;
}
else
{
obj* x_502; 
lean::dec(x_17);
lean::dec(x_11);
lean::dec(x_1);
lean::dec(x_10);
x_502 = lean::box(0);
x_22 = x_502;
goto lbl_23;
}
}
}
lbl_27:
{
obj* x_504; obj* x_505; unsigned char x_506; unsigned x_507; 
lean::dec(x_26);
x_504 = lean::mk_nat_obj(116u);
x_505 = lean::mk_nat_obj(55296u);
x_506 = lean::nat_dec_lt(x_504, x_505);
if (x_506 == 0)
{
obj* x_509; unsigned char x_510; 
x_509 = lean::mk_nat_obj(57343u);
x_510 = lean::nat_dec_lt(x_509, x_504);
lean::dec(x_509);
if (x_510 == 0)
{
obj* x_513; unsigned x_514; 
lean::dec(x_504);
x_513 = lean::mk_nat_obj(0u);
x_514 = lean::unbox_uint32(x_513);
lean::dec(x_513);
x_507 = x_514;
goto lbl_508;
}
else
{
obj* x_516; unsigned char x_517; 
x_516 = lean::mk_nat_obj(1114112u);
x_517 = lean::nat_dec_lt(x_504, x_516);
lean::dec(x_516);
if (x_517 == 0)
{
obj* x_520; unsigned x_521; 
lean::dec(x_504);
x_520 = lean::mk_nat_obj(0u);
x_521 = lean::unbox_uint32(x_520);
lean::dec(x_520);
x_507 = x_521;
goto lbl_508;
}
else
{
unsigned x_523; 
x_523 = lean::unbox_uint32(x_504);
lean::dec(x_504);
x_507 = x_523;
goto lbl_508;
}
}
}
else
{
unsigned x_525; 
x_525 = lean::unbox_uint32(x_504);
lean::dec(x_504);
x_507 = x_525;
goto lbl_508;
}
lbl_508:
{
obj* x_527; unsigned char x_528; 
x_527 = lean::box_uint32(x_507);
x_528 = lean::nat_dec_eq(x_11, x_527);
lean::dec(x_527);
if (x_528 == 0)
{
obj* x_531; 
lean::dec(x_505);
x_531 = lean::box(0);
x_24 = x_531;
goto lbl_25;
}
else
{
obj* x_537; unsigned char x_538; 
lean::dec(x_17);
lean::dec(x_11);
lean::dec(x_1);
lean::dec(x_10);
lean::dec(x_0);
x_537 = lean::mk_nat_obj(9u);
x_538 = lean::nat_dec_lt(x_537, x_505);
lean::dec(x_505);
if (x_538 == 0)
{
obj* x_540; unsigned char x_541; 
x_540 = lean::mk_nat_obj(57343u);
x_541 = lean::nat_dec_lt(x_540, x_537);
lean::dec(x_540);
if (x_541 == 0)
{
obj* x_544; obj* x_545; obj* x_547; obj* x_548; obj* x_550; obj* x_551; 
lean::dec(x_537);
x_544 = lean::mk_nat_obj(0u);
x_545 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_545);
x_547 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_547, 0, x_544);
lean::cnstr_set(x_547, 1, x_13);
lean::cnstr_set(x_547, 2, x_545);
x_548 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_547);
lean::inc(x_545);
x_550 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_545, x_548);
x_551 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_551, 0, x_550);
lean::cnstr_set(x_551, 1, x_8);
return x_551;
}
else
{
obj* x_552; unsigned char x_553; 
x_552 = lean::mk_nat_obj(1114112u);
x_553 = lean::nat_dec_lt(x_537, x_552);
lean::dec(x_552);
if (x_553 == 0)
{
obj* x_556; obj* x_557; obj* x_559; obj* x_560; obj* x_562; obj* x_563; 
lean::dec(x_537);
x_556 = lean::mk_nat_obj(0u);
x_557 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_557);
x_559 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_559, 0, x_556);
lean::cnstr_set(x_559, 1, x_13);
lean::cnstr_set(x_559, 2, x_557);
x_560 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_559);
lean::inc(x_557);
x_562 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_557, x_560);
x_563 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_563, 0, x_562);
lean::cnstr_set(x_563, 1, x_8);
return x_563;
}
else
{
obj* x_564; obj* x_566; obj* x_567; obj* x_569; obj* x_570; 
x_564 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_564);
x_566 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_566, 0, x_537);
lean::cnstr_set(x_566, 1, x_13);
lean::cnstr_set(x_566, 2, x_564);
x_567 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_566);
lean::inc(x_564);
x_569 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_564, x_567);
x_570 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_570, 0, x_569);
lean::cnstr_set(x_570, 1, x_8);
return x_570;
}
}
}
else
{
obj* x_571; obj* x_573; obj* x_574; obj* x_576; obj* x_577; 
x_571 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_571);
x_573 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_573, 0, x_537);
lean::cnstr_set(x_573, 1, x_13);
lean::cnstr_set(x_573, 2, x_571);
x_574 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_573);
lean::inc(x_571);
x_576 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_571, x_574);
x_577 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_577, 0, x_576);
lean::cnstr_set(x_577, 1, x_8);
return x_577;
}
}
}
}
lbl_29:
{
obj* x_579; obj* x_580; unsigned char x_581; unsigned x_582; 
lean::dec(x_28);
x_579 = lean::mk_nat_obj(110u);
x_580 = lean::mk_nat_obj(55296u);
x_581 = lean::nat_dec_lt(x_579, x_580);
if (x_581 == 0)
{
obj* x_584; unsigned char x_585; 
x_584 = lean::mk_nat_obj(57343u);
x_585 = lean::nat_dec_lt(x_584, x_579);
lean::dec(x_584);
if (x_585 == 0)
{
obj* x_588; unsigned x_589; 
lean::dec(x_579);
x_588 = lean::mk_nat_obj(0u);
x_589 = lean::unbox_uint32(x_588);
lean::dec(x_588);
x_582 = x_589;
goto lbl_583;
}
else
{
obj* x_591; unsigned char x_592; 
x_591 = lean::mk_nat_obj(1114112u);
x_592 = lean::nat_dec_lt(x_579, x_591);
lean::dec(x_591);
if (x_592 == 0)
{
obj* x_595; unsigned x_596; 
lean::dec(x_579);
x_595 = lean::mk_nat_obj(0u);
x_596 = lean::unbox_uint32(x_595);
lean::dec(x_595);
x_582 = x_596;
goto lbl_583;
}
else
{
unsigned x_598; 
x_598 = lean::unbox_uint32(x_579);
lean::dec(x_579);
x_582 = x_598;
goto lbl_583;
}
}
}
else
{
unsigned x_600; 
x_600 = lean::unbox_uint32(x_579);
lean::dec(x_579);
x_582 = x_600;
goto lbl_583;
}
lbl_583:
{
obj* x_602; unsigned char x_603; 
x_602 = lean::box_uint32(x_582);
x_603 = lean::nat_dec_eq(x_11, x_602);
lean::dec(x_602);
if (x_603 == 0)
{
obj* x_606; 
lean::dec(x_580);
x_606 = lean::box(0);
x_26 = x_606;
goto lbl_27;
}
else
{
obj* x_612; unsigned char x_613; 
lean::dec(x_17);
lean::dec(x_11);
lean::dec(x_1);
lean::dec(x_10);
lean::dec(x_0);
x_612 = lean::mk_nat_obj(10u);
x_613 = lean::nat_dec_lt(x_612, x_580);
lean::dec(x_580);
if (x_613 == 0)
{
obj* x_615; unsigned char x_616; 
x_615 = lean::mk_nat_obj(57343u);
x_616 = lean::nat_dec_lt(x_615, x_612);
lean::dec(x_615);
if (x_616 == 0)
{
obj* x_619; obj* x_620; obj* x_622; obj* x_623; obj* x_625; obj* x_626; 
lean::dec(x_612);
x_619 = lean::mk_nat_obj(0u);
x_620 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_620);
x_622 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_622, 0, x_619);
lean::cnstr_set(x_622, 1, x_13);
lean::cnstr_set(x_622, 2, x_620);
x_623 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_622);
lean::inc(x_620);
x_625 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_620, x_623);
x_626 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_626, 0, x_625);
lean::cnstr_set(x_626, 1, x_8);
return x_626;
}
else
{
obj* x_627; unsigned char x_628; 
x_627 = lean::mk_nat_obj(1114112u);
x_628 = lean::nat_dec_lt(x_612, x_627);
lean::dec(x_627);
if (x_628 == 0)
{
obj* x_631; obj* x_632; obj* x_634; obj* x_635; obj* x_637; obj* x_638; 
lean::dec(x_612);
x_631 = lean::mk_nat_obj(0u);
x_632 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_632);
x_634 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_634, 0, x_631);
lean::cnstr_set(x_634, 1, x_13);
lean::cnstr_set(x_634, 2, x_632);
x_635 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_634);
lean::inc(x_632);
x_637 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_632, x_635);
x_638 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_638, 0, x_637);
lean::cnstr_set(x_638, 1, x_8);
return x_638;
}
else
{
obj* x_639; obj* x_641; obj* x_642; obj* x_644; obj* x_645; 
x_639 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_639);
x_641 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_641, 0, x_612);
lean::cnstr_set(x_641, 1, x_13);
lean::cnstr_set(x_641, 2, x_639);
x_642 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_641);
lean::inc(x_639);
x_644 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_639, x_642);
x_645 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_645, 0, x_644);
lean::cnstr_set(x_645, 1, x_8);
return x_645;
}
}
}
else
{
obj* x_646; obj* x_648; obj* x_649; obj* x_651; obj* x_652; 
x_646 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_646);
x_648 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_648, 0, x_612);
lean::cnstr_set(x_648, 1, x_13);
lean::cnstr_set(x_648, 2, x_646);
x_649 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_648);
lean::inc(x_646);
x_651 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_646, x_649);
x_652 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_652, 0, x_651);
lean::cnstr_set(x_652, 1, x_8);
return x_652;
}
}
}
}
lbl_31:
{
obj* x_654; obj* x_655; unsigned char x_656; unsigned x_658; 
lean::dec(x_30);
x_654 = lean::mk_nat_obj(39u);
x_655 = lean::mk_nat_obj(55296u);
x_656 = lean::nat_dec_lt(x_654, x_655);
lean::dec(x_655);
if (x_656 == 0)
{
obj* x_660; unsigned char x_661; 
x_660 = lean::mk_nat_obj(57343u);
x_661 = lean::nat_dec_lt(x_660, x_654);
lean::dec(x_660);
if (x_661 == 0)
{
obj* x_664; unsigned x_665; 
lean::dec(x_654);
x_664 = lean::mk_nat_obj(0u);
x_665 = lean::unbox_uint32(x_664);
lean::dec(x_664);
x_658 = x_665;
goto lbl_659;
}
else
{
obj* x_667; unsigned char x_668; 
x_667 = lean::mk_nat_obj(1114112u);
x_668 = lean::nat_dec_lt(x_654, x_667);
lean::dec(x_667);
if (x_668 == 0)
{
obj* x_671; unsigned x_672; 
lean::dec(x_654);
x_671 = lean::mk_nat_obj(0u);
x_672 = lean::unbox_uint32(x_671);
lean::dec(x_671);
x_658 = x_672;
goto lbl_659;
}
else
{
unsigned x_674; 
x_674 = lean::unbox_uint32(x_654);
lean::dec(x_654);
x_658 = x_674;
goto lbl_659;
}
}
}
else
{
unsigned x_676; 
x_676 = lean::unbox_uint32(x_654);
lean::dec(x_654);
x_658 = x_676;
goto lbl_659;
}
lbl_659:
{
obj* x_678; unsigned char x_679; 
x_678 = lean::box_uint32(x_658);
x_679 = lean::nat_dec_eq(x_11, x_678);
if (x_679 == 0)
{
obj* x_681; 
lean::dec(x_678);
x_681 = lean::box(0);
x_28 = x_681;
goto lbl_29;
}
else
{
obj* x_687; obj* x_689; obj* x_690; obj* x_692; obj* x_693; 
lean::dec(x_17);
lean::dec(x_11);
lean::dec(x_1);
lean::dec(x_10);
lean::dec(x_0);
x_687 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_687);
x_689 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_689, 0, x_678);
lean::cnstr_set(x_689, 1, x_13);
lean::cnstr_set(x_689, 2, x_687);
x_690 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_689);
lean::inc(x_687);
x_692 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_687, x_690);
x_693 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_693, 0, x_692);
lean::cnstr_set(x_693, 1, x_8);
return x_693;
}
}
}
lbl_33:
{
obj* x_695; obj* x_696; unsigned char x_697; unsigned x_699; 
lean::dec(x_32);
x_695 = lean::mk_nat_obj(34u);
x_696 = lean::mk_nat_obj(55296u);
x_697 = lean::nat_dec_lt(x_695, x_696);
lean::dec(x_696);
if (x_697 == 0)
{
obj* x_701; unsigned char x_702; 
x_701 = lean::mk_nat_obj(57343u);
x_702 = lean::nat_dec_lt(x_701, x_695);
lean::dec(x_701);
if (x_702 == 0)
{
obj* x_705; unsigned x_706; 
lean::dec(x_695);
x_705 = lean::mk_nat_obj(0u);
x_706 = lean::unbox_uint32(x_705);
lean::dec(x_705);
x_699 = x_706;
goto lbl_700;
}
else
{
obj* x_708; unsigned char x_709; 
x_708 = lean::mk_nat_obj(1114112u);
x_709 = lean::nat_dec_lt(x_695, x_708);
lean::dec(x_708);
if (x_709 == 0)
{
obj* x_712; unsigned x_713; 
lean::dec(x_695);
x_712 = lean::mk_nat_obj(0u);
x_713 = lean::unbox_uint32(x_712);
lean::dec(x_712);
x_699 = x_713;
goto lbl_700;
}
else
{
unsigned x_715; 
x_715 = lean::unbox_uint32(x_695);
lean::dec(x_695);
x_699 = x_715;
goto lbl_700;
}
}
}
else
{
unsigned x_717; 
x_717 = lean::unbox_uint32(x_695);
lean::dec(x_695);
x_699 = x_717;
goto lbl_700;
}
lbl_700:
{
obj* x_719; unsigned char x_720; 
x_719 = lean::box_uint32(x_699);
x_720 = lean::nat_dec_eq(x_11, x_719);
if (x_720 == 0)
{
obj* x_722; 
lean::dec(x_719);
x_722 = lean::box(0);
x_30 = x_722;
goto lbl_31;
}
else
{
obj* x_728; obj* x_730; obj* x_731; obj* x_733; obj* x_734; 
lean::dec(x_17);
lean::dec(x_11);
lean::dec(x_1);
lean::dec(x_10);
lean::dec(x_0);
x_728 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_728);
x_730 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_730, 0, x_719);
lean::cnstr_set(x_730, 1, x_13);
lean::cnstr_set(x_730, 2, x_728);
x_731 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_730);
lean::inc(x_728);
x_733 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_728, x_731);
x_734 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_734, 0, x_733);
lean::cnstr_set(x_734, 1, x_8);
return x_734;
}
}
}
lbl_39:
{
obj* x_735; unsigned char x_736; 
x_735 = lean::box_uint32(x_38);
x_736 = lean::nat_dec_eq(x_11, x_735);
if (x_736 == 0)
{
obj* x_738; 
lean::dec(x_735);
x_738 = lean::box(0);
x_32 = x_738;
goto lbl_33;
}
else
{
obj* x_744; obj* x_746; obj* x_747; obj* x_749; obj* x_750; 
lean::dec(x_17);
lean::dec(x_11);
lean::dec(x_1);
lean::dec(x_10);
lean::dec(x_0);
x_744 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_744);
x_746 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_746, 0, x_735);
lean::cnstr_set(x_746, 1, x_13);
lean::cnstr_set(x_746, 2, x_744);
x_747 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_746);
lean::inc(x_744);
x_749 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_744, x_747);
x_750 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_750, 0, x_749);
lean::cnstr_set(x_750, 1, x_8);
return x_750;
}
}
}
else
{
obj* x_753; unsigned char x_755; obj* x_756; obj* x_757; obj* x_758; obj* x_759; obj* x_761; obj* x_762; 
lean::dec(x_1);
lean::dec(x_0);
x_753 = lean::cnstr_get(x_6, 0);
lean::inc(x_753);
x_755 = lean::cnstr_get_scalar<unsigned char>(x_6, sizeof(void*)*1);
if (lean::is_shared(x_6)) {
 lean::dec(x_6);
 x_756 = lean::box(0);
} else {
 lean::cnstr_release(x_6, 0);
 x_756 = x_6;
}
if (lean::is_scalar(x_756)) {
 x_757 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_757 = x_756;
}
lean::cnstr_set(x_757, 0, x_753);
lean::cnstr_set_scalar(x_757, sizeof(void*)*1, x_755);
x_758 = x_757;
x_759 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_759);
x_761 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_759, x_758);
if (lean::is_scalar(x_10)) {
 x_762 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_762 = x_10;
}
lean::cnstr_set(x_762, 0, x_761);
lean::cnstr_set(x_762, 1, x_8);
return x_762;
}
}
}
obj* l_lean_parser_parse__string__literal__aux___main___at_lean_parser_string__lit_x_27___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; unsigned char x_6; 
x_5 = lean::mk_nat_obj(0u);
x_6 = lean::nat_dec_eq(x_0, x_5);
if (x_6 == 0)
{
obj* x_8; obj* x_9; obj* x_11; obj* x_13; 
lean::inc(x_2);
x_8 = l_lean_parser_monad__parsec_any___at___private_4089500695__finish__comment__block__aux___main___spec__2(x_2, x_3, x_4);
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
obj* x_14; obj* x_16; obj* x_18; obj* x_20; obj* x_21; obj* x_22; obj* x_25; obj* x_27; obj* x_28; unsigned char x_29; unsigned x_31; 
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
x_21 = lean::mk_nat_obj(1u);
x_22 = lean::nat_sub(x_0, x_21);
lean::dec(x_21);
lean::dec(x_0);
x_27 = lean::mk_nat_obj(92u);
x_28 = lean::mk_nat_obj(55296u);
x_29 = lean::nat_dec_lt(x_27, x_28);
lean::dec(x_28);
if (x_29 == 0)
{
obj* x_33; unsigned char x_34; 
x_33 = lean::mk_nat_obj(57343u);
x_34 = lean::nat_dec_lt(x_33, x_27);
lean::dec(x_33);
if (x_34 == 0)
{
unsigned x_37; 
lean::dec(x_27);
x_37 = lean::unbox_uint32(x_5);
x_31 = x_37;
goto lbl_32;
}
else
{
obj* x_38; unsigned char x_39; 
x_38 = lean::mk_nat_obj(1114112u);
x_39 = lean::nat_dec_lt(x_27, x_38);
lean::dec(x_38);
if (x_39 == 0)
{
unsigned x_42; 
lean::dec(x_27);
x_42 = lean::unbox_uint32(x_5);
x_31 = x_42;
goto lbl_32;
}
else
{
unsigned x_43; 
x_43 = lean::unbox_uint32(x_27);
lean::dec(x_27);
x_31 = x_43;
goto lbl_32;
}
}
}
else
{
unsigned x_45; 
x_45 = lean::unbox_uint32(x_27);
lean::dec(x_27);
x_31 = x_45;
goto lbl_32;
}
lbl_26:
{
obj* x_48; obj* x_49; unsigned char x_50; unsigned x_52; 
lean::dec(x_25);
x_48 = lean::mk_nat_obj(34u);
x_49 = lean::mk_nat_obj(55296u);
x_50 = lean::nat_dec_lt(x_48, x_49);
lean::dec(x_49);
if (x_50 == 0)
{
obj* x_54; unsigned char x_55; 
x_54 = lean::mk_nat_obj(57343u);
x_55 = lean::nat_dec_lt(x_54, x_48);
lean::dec(x_54);
if (x_55 == 0)
{
unsigned x_58; 
lean::dec(x_48);
x_58 = lean::unbox_uint32(x_5);
lean::dec(x_5);
x_52 = x_58;
goto lbl_53;
}
else
{
obj* x_60; unsigned char x_61; 
x_60 = lean::mk_nat_obj(1114112u);
x_61 = lean::nat_dec_lt(x_48, x_60);
lean::dec(x_60);
if (x_61 == 0)
{
unsigned x_64; 
lean::dec(x_48);
x_64 = lean::unbox_uint32(x_5);
lean::dec(x_5);
x_52 = x_64;
goto lbl_53;
}
else
{
unsigned x_67; 
lean::dec(x_5);
x_67 = lean::unbox_uint32(x_48);
lean::dec(x_48);
x_52 = x_67;
goto lbl_53;
}
}
}
else
{
unsigned x_70; 
lean::dec(x_5);
x_70 = lean::unbox_uint32(x_48);
lean::dec(x_48);
x_52 = x_70;
goto lbl_53;
}
lbl_53:
{
obj* x_72; unsigned char x_73; 
x_72 = lean::box_uint32(x_52);
x_73 = lean::nat_dec_eq(x_14, x_72);
lean::dec(x_72);
if (x_73 == 0)
{
unsigned x_76; obj* x_78; obj* x_79; obj* x_80; obj* x_82; obj* x_85; obj* x_86; 
lean::dec(x_20);
x_76 = lean::unbox_uint32(x_14);
lean::dec(x_14);
x_78 = lean::string_push(x_1, x_76);
x_79 = l_lean_parser_parse__string__literal__aux___main___at_lean_parser_string__lit_x_27___spec__2(x_22, x_78, x_2, x_16, x_11);
x_80 = lean::cnstr_get(x_79, 0);
lean::inc(x_80);
x_82 = lean::cnstr_get(x_79, 1);
lean::inc(x_82);
lean::dec(x_79);
x_85 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_18, x_80);
if (lean::is_scalar(x_13)) {
 x_86 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_86 = x_13;
}
lean::cnstr_set(x_86, 0, x_85);
lean::cnstr_set(x_86, 1, x_82);
return x_86;
}
else
{
obj* x_90; obj* x_92; obj* x_93; obj* x_94; 
lean::dec(x_14);
lean::dec(x_2);
lean::dec(x_22);
x_90 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_90);
if (lean::is_scalar(x_20)) {
 x_92 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_92 = x_20;
}
lean::cnstr_set(x_92, 0, x_1);
lean::cnstr_set(x_92, 1, x_16);
lean::cnstr_set(x_92, 2, x_90);
x_93 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_18, x_92);
if (lean::is_scalar(x_13)) {
 x_94 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_94 = x_13;
}
lean::cnstr_set(x_94, 0, x_93);
lean::cnstr_set(x_94, 1, x_11);
return x_94;
}
}
}
lbl_32:
{
obj* x_95; unsigned char x_96; 
x_95 = lean::box_uint32(x_31);
x_96 = lean::nat_dec_eq(x_14, x_95);
lean::dec(x_95);
if (x_96 == 0)
{
obj* x_98; 
x_98 = lean::box(0);
x_25 = x_98;
goto lbl_26;
}
else
{
obj* x_104; obj* x_105; obj* x_107; obj* x_109; 
lean::dec(x_5);
lean::dec(x_20);
lean::dec(x_14);
lean::dec(x_13);
lean::inc(x_2);
x_104 = l_lean_parser_parse__quoted__char___at_lean_parser_string__lit_x_27___spec__3(x_2, x_16, x_11);
x_105 = lean::cnstr_get(x_104, 0);
lean::inc(x_105);
x_107 = lean::cnstr_get(x_104, 1);
lean::inc(x_107);
if (lean::is_shared(x_104)) {
 lean::dec(x_104);
 x_109 = lean::box(0);
} else {
 lean::cnstr_release(x_104, 0);
 lean::cnstr_release(x_104, 1);
 x_109 = x_104;
}
if (lean::obj_tag(x_105) == 0)
{
obj* x_110; obj* x_112; obj* x_114; unsigned x_117; obj* x_119; obj* x_120; obj* x_121; obj* x_123; obj* x_126; obj* x_127; obj* x_128; 
x_110 = lean::cnstr_get(x_105, 0);
lean::inc(x_110);
x_112 = lean::cnstr_get(x_105, 1);
lean::inc(x_112);
x_114 = lean::cnstr_get(x_105, 2);
lean::inc(x_114);
lean::dec(x_105);
x_117 = lean::unbox_uint32(x_110);
lean::dec(x_110);
x_119 = lean::string_push(x_1, x_117);
x_120 = l_lean_parser_parse__string__literal__aux___main___at_lean_parser_string__lit_x_27___spec__2(x_22, x_119, x_2, x_112, x_107);
x_121 = lean::cnstr_get(x_120, 0);
lean::inc(x_121);
x_123 = lean::cnstr_get(x_120, 1);
lean::inc(x_123);
lean::dec(x_120);
x_126 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_114, x_121);
x_127 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_18, x_126);
if (lean::is_scalar(x_109)) {
 x_128 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_128 = x_109;
}
lean::cnstr_set(x_128, 0, x_127);
lean::cnstr_set(x_128, 1, x_123);
return x_128;
}
else
{
obj* x_132; unsigned char x_134; obj* x_135; obj* x_136; obj* x_137; obj* x_138; obj* x_139; 
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_22);
x_132 = lean::cnstr_get(x_105, 0);
lean::inc(x_132);
x_134 = lean::cnstr_get_scalar<unsigned char>(x_105, sizeof(void*)*1);
if (lean::is_shared(x_105)) {
 lean::dec(x_105);
 x_135 = lean::box(0);
} else {
 lean::cnstr_release(x_105, 0);
 x_135 = x_105;
}
if (lean::is_scalar(x_135)) {
 x_136 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_136 = x_135;
}
lean::cnstr_set(x_136, 0, x_132);
lean::cnstr_set_scalar(x_136, sizeof(void*)*1, x_134);
x_137 = x_136;
x_138 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_18, x_137);
if (lean::is_scalar(x_109)) {
 x_139 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_139 = x_109;
}
lean::cnstr_set(x_139, 0, x_138);
lean::cnstr_set(x_139, 1, x_107);
return x_139;
}
}
}
}
else
{
obj* x_144; unsigned char x_146; obj* x_147; obj* x_148; obj* x_149; obj* x_150; 
lean::dec(x_5);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_144 = lean::cnstr_get(x_9, 0);
lean::inc(x_144);
x_146 = lean::cnstr_get_scalar<unsigned char>(x_9, sizeof(void*)*1);
if (lean::is_shared(x_9)) {
 lean::dec(x_9);
 x_147 = lean::box(0);
} else {
 lean::cnstr_release(x_9, 0);
 x_147 = x_9;
}
if (lean::is_scalar(x_147)) {
 x_148 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_148 = x_147;
}
lean::cnstr_set(x_148, 0, x_144);
lean::cnstr_set_scalar(x_148, sizeof(void*)*1, x_146);
x_149 = x_148;
if (lean::is_scalar(x_13)) {
 x_150 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_150 = x_13;
}
lean::cnstr_set(x_150, 0, x_149);
lean::cnstr_set(x_150, 1, x_11);
return x_150;
}
}
else
{
obj* x_152; obj* x_153; unsigned char x_154; 
lean::dec(x_0);
x_152 = lean::mk_nat_obj(34u);
x_153 = lean::mk_nat_obj(55296u);
x_154 = lean::nat_dec_lt(x_152, x_153);
lean::dec(x_153);
if (x_154 == 0)
{
obj* x_156; unsigned char x_157; 
x_156 = lean::mk_nat_obj(57343u);
x_157 = lean::nat_dec_lt(x_156, x_152);
lean::dec(x_156);
if (x_157 == 0)
{
unsigned x_160; obj* x_162; obj* x_163; obj* x_165; obj* x_167; 
lean::dec(x_152);
x_160 = lean::unbox_uint32(x_5);
lean::dec(x_5);
x_162 = l_lean_parser_monad__parsec_ch___at___private_3519775105__ident_x_27___spec__11(x_160, x_2, x_3, x_4);
x_163 = lean::cnstr_get(x_162, 0);
lean::inc(x_163);
x_165 = lean::cnstr_get(x_162, 1);
lean::inc(x_165);
if (lean::is_shared(x_162)) {
 lean::dec(x_162);
 x_167 = lean::box(0);
} else {
 lean::cnstr_release(x_162, 0);
 lean::cnstr_release(x_162, 1);
 x_167 = x_162;
}
if (lean::obj_tag(x_163) == 0)
{
obj* x_168; obj* x_170; obj* x_172; obj* x_173; obj* x_175; obj* x_176; obj* x_177; 
x_168 = lean::cnstr_get(x_163, 1);
lean::inc(x_168);
x_170 = lean::cnstr_get(x_163, 2);
lean::inc(x_170);
if (lean::is_shared(x_163)) {
 lean::dec(x_163);
 x_172 = lean::box(0);
} else {
 lean::cnstr_release(x_163, 0);
 lean::cnstr_release(x_163, 1);
 lean::cnstr_release(x_163, 2);
 x_172 = x_163;
}
x_173 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_173);
if (lean::is_scalar(x_172)) {
 x_175 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_175 = x_172;
}
lean::cnstr_set(x_175, 0, x_1);
lean::cnstr_set(x_175, 1, x_168);
lean::cnstr_set(x_175, 2, x_173);
x_176 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_170, x_175);
if (lean::is_scalar(x_167)) {
 x_177 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_177 = x_167;
}
lean::cnstr_set(x_177, 0, x_176);
lean::cnstr_set(x_177, 1, x_165);
return x_177;
}
else
{
obj* x_179; unsigned char x_181; obj* x_182; obj* x_183; obj* x_184; obj* x_185; 
lean::dec(x_1);
x_179 = lean::cnstr_get(x_163, 0);
lean::inc(x_179);
x_181 = lean::cnstr_get_scalar<unsigned char>(x_163, sizeof(void*)*1);
if (lean::is_shared(x_163)) {
 lean::dec(x_163);
 x_182 = lean::box(0);
} else {
 lean::cnstr_release(x_163, 0);
 x_182 = x_163;
}
if (lean::is_scalar(x_182)) {
 x_183 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_183 = x_182;
}
lean::cnstr_set(x_183, 0, x_179);
lean::cnstr_set_scalar(x_183, sizeof(void*)*1, x_181);
x_184 = x_183;
if (lean::is_scalar(x_167)) {
 x_185 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_185 = x_167;
}
lean::cnstr_set(x_185, 0, x_184);
lean::cnstr_set(x_185, 1, x_165);
return x_185;
}
}
else
{
obj* x_186; unsigned char x_187; 
x_186 = lean::mk_nat_obj(1114112u);
x_187 = lean::nat_dec_lt(x_152, x_186);
lean::dec(x_186);
if (x_187 == 0)
{
unsigned x_190; obj* x_192; obj* x_193; obj* x_195; obj* x_197; 
lean::dec(x_152);
x_190 = lean::unbox_uint32(x_5);
lean::dec(x_5);
x_192 = l_lean_parser_monad__parsec_ch___at___private_3519775105__ident_x_27___spec__11(x_190, x_2, x_3, x_4);
x_193 = lean::cnstr_get(x_192, 0);
lean::inc(x_193);
x_195 = lean::cnstr_get(x_192, 1);
lean::inc(x_195);
if (lean::is_shared(x_192)) {
 lean::dec(x_192);
 x_197 = lean::box(0);
} else {
 lean::cnstr_release(x_192, 0);
 lean::cnstr_release(x_192, 1);
 x_197 = x_192;
}
if (lean::obj_tag(x_193) == 0)
{
obj* x_198; obj* x_200; obj* x_202; obj* x_203; obj* x_205; obj* x_206; obj* x_207; 
x_198 = lean::cnstr_get(x_193, 1);
lean::inc(x_198);
x_200 = lean::cnstr_get(x_193, 2);
lean::inc(x_200);
if (lean::is_shared(x_193)) {
 lean::dec(x_193);
 x_202 = lean::box(0);
} else {
 lean::cnstr_release(x_193, 0);
 lean::cnstr_release(x_193, 1);
 lean::cnstr_release(x_193, 2);
 x_202 = x_193;
}
x_203 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_203);
if (lean::is_scalar(x_202)) {
 x_205 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_205 = x_202;
}
lean::cnstr_set(x_205, 0, x_1);
lean::cnstr_set(x_205, 1, x_198);
lean::cnstr_set(x_205, 2, x_203);
x_206 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_200, x_205);
if (lean::is_scalar(x_197)) {
 x_207 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_207 = x_197;
}
lean::cnstr_set(x_207, 0, x_206);
lean::cnstr_set(x_207, 1, x_195);
return x_207;
}
else
{
obj* x_209; unsigned char x_211; obj* x_212; obj* x_213; obj* x_214; obj* x_215; 
lean::dec(x_1);
x_209 = lean::cnstr_get(x_193, 0);
lean::inc(x_209);
x_211 = lean::cnstr_get_scalar<unsigned char>(x_193, sizeof(void*)*1);
if (lean::is_shared(x_193)) {
 lean::dec(x_193);
 x_212 = lean::box(0);
} else {
 lean::cnstr_release(x_193, 0);
 x_212 = x_193;
}
if (lean::is_scalar(x_212)) {
 x_213 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_213 = x_212;
}
lean::cnstr_set(x_213, 0, x_209);
lean::cnstr_set_scalar(x_213, sizeof(void*)*1, x_211);
x_214 = x_213;
if (lean::is_scalar(x_197)) {
 x_215 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_215 = x_197;
}
lean::cnstr_set(x_215, 0, x_214);
lean::cnstr_set(x_215, 1, x_195);
return x_215;
}
}
else
{
unsigned x_217; obj* x_219; obj* x_220; obj* x_222; obj* x_224; 
lean::dec(x_5);
x_217 = lean::unbox_uint32(x_152);
lean::dec(x_152);
x_219 = l_lean_parser_monad__parsec_ch___at___private_3519775105__ident_x_27___spec__11(x_217, x_2, x_3, x_4);
x_220 = lean::cnstr_get(x_219, 0);
lean::inc(x_220);
x_222 = lean::cnstr_get(x_219, 1);
lean::inc(x_222);
if (lean::is_shared(x_219)) {
 lean::dec(x_219);
 x_224 = lean::box(0);
} else {
 lean::cnstr_release(x_219, 0);
 lean::cnstr_release(x_219, 1);
 x_224 = x_219;
}
if (lean::obj_tag(x_220) == 0)
{
obj* x_225; obj* x_227; obj* x_229; obj* x_230; obj* x_232; obj* x_233; obj* x_234; 
x_225 = lean::cnstr_get(x_220, 1);
lean::inc(x_225);
x_227 = lean::cnstr_get(x_220, 2);
lean::inc(x_227);
if (lean::is_shared(x_220)) {
 lean::dec(x_220);
 x_229 = lean::box(0);
} else {
 lean::cnstr_release(x_220, 0);
 lean::cnstr_release(x_220, 1);
 lean::cnstr_release(x_220, 2);
 x_229 = x_220;
}
x_230 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_230);
if (lean::is_scalar(x_229)) {
 x_232 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_232 = x_229;
}
lean::cnstr_set(x_232, 0, x_1);
lean::cnstr_set(x_232, 1, x_225);
lean::cnstr_set(x_232, 2, x_230);
x_233 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_227, x_232);
if (lean::is_scalar(x_224)) {
 x_234 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_234 = x_224;
}
lean::cnstr_set(x_234, 0, x_233);
lean::cnstr_set(x_234, 1, x_222);
return x_234;
}
else
{
obj* x_236; unsigned char x_238; obj* x_239; obj* x_240; obj* x_241; obj* x_242; 
lean::dec(x_1);
x_236 = lean::cnstr_get(x_220, 0);
lean::inc(x_236);
x_238 = lean::cnstr_get_scalar<unsigned char>(x_220, sizeof(void*)*1);
if (lean::is_shared(x_220)) {
 lean::dec(x_220);
 x_239 = lean::box(0);
} else {
 lean::cnstr_release(x_220, 0);
 x_239 = x_220;
}
if (lean::is_scalar(x_239)) {
 x_240 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_240 = x_239;
}
lean::cnstr_set(x_240, 0, x_236);
lean::cnstr_set_scalar(x_240, sizeof(void*)*1, x_238);
x_241 = x_240;
if (lean::is_scalar(x_224)) {
 x_242 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_242 = x_224;
}
lean::cnstr_set(x_242, 0, x_241);
lean::cnstr_set(x_242, 1, x_222);
return x_242;
}
}
}
}
else
{
unsigned x_244; obj* x_246; obj* x_247; obj* x_249; obj* x_251; 
lean::dec(x_5);
x_244 = lean::unbox_uint32(x_152);
lean::dec(x_152);
x_246 = l_lean_parser_monad__parsec_ch___at___private_3519775105__ident_x_27___spec__11(x_244, x_2, x_3, x_4);
x_247 = lean::cnstr_get(x_246, 0);
lean::inc(x_247);
x_249 = lean::cnstr_get(x_246, 1);
lean::inc(x_249);
if (lean::is_shared(x_246)) {
 lean::dec(x_246);
 x_251 = lean::box(0);
} else {
 lean::cnstr_release(x_246, 0);
 lean::cnstr_release(x_246, 1);
 x_251 = x_246;
}
if (lean::obj_tag(x_247) == 0)
{
obj* x_252; obj* x_254; obj* x_256; obj* x_257; obj* x_259; obj* x_260; obj* x_261; 
x_252 = lean::cnstr_get(x_247, 1);
lean::inc(x_252);
x_254 = lean::cnstr_get(x_247, 2);
lean::inc(x_254);
if (lean::is_shared(x_247)) {
 lean::dec(x_247);
 x_256 = lean::box(0);
} else {
 lean::cnstr_release(x_247, 0);
 lean::cnstr_release(x_247, 1);
 lean::cnstr_release(x_247, 2);
 x_256 = x_247;
}
x_257 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_257);
if (lean::is_scalar(x_256)) {
 x_259 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_259 = x_256;
}
lean::cnstr_set(x_259, 0, x_1);
lean::cnstr_set(x_259, 1, x_252);
lean::cnstr_set(x_259, 2, x_257);
x_260 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_254, x_259);
if (lean::is_scalar(x_251)) {
 x_261 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_261 = x_251;
}
lean::cnstr_set(x_261, 0, x_260);
lean::cnstr_set(x_261, 1, x_249);
return x_261;
}
else
{
obj* x_263; unsigned char x_265; obj* x_266; obj* x_267; obj* x_268; obj* x_269; 
lean::dec(x_1);
x_263 = lean::cnstr_get(x_247, 0);
lean::inc(x_263);
x_265 = lean::cnstr_get_scalar<unsigned char>(x_247, sizeof(void*)*1);
if (lean::is_shared(x_247)) {
 lean::dec(x_247);
 x_266 = lean::box(0);
} else {
 lean::cnstr_release(x_247, 0);
 x_266 = x_247;
}
if (lean::is_scalar(x_266)) {
 x_267 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_267 = x_266;
}
lean::cnstr_set(x_267, 0, x_263);
lean::cnstr_set_scalar(x_267, sizeof(void*)*1, x_265);
x_268 = x_267;
if (lean::is_scalar(x_251)) {
 x_269 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_269 = x_251;
}
lean::cnstr_set(x_269, 0, x_268);
lean::cnstr_set(x_269, 1, x_249);
return x_269;
}
}
}
}
}
obj* l_lean_parser_parse__string__literal___at_lean_parser_string__lit_x_27___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; unsigned char x_5; 
x_3 = lean::mk_nat_obj(34u);
x_4 = lean::mk_nat_obj(55296u);
x_5 = lean::nat_dec_lt(x_3, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
obj* x_7; unsigned char x_8; 
x_7 = lean::mk_nat_obj(57343u);
x_8 = lean::nat_dec_lt(x_7, x_3);
lean::dec(x_7);
if (x_8 == 0)
{
obj* x_11; unsigned x_12; obj* x_15; obj* x_16; obj* x_18; obj* x_20; 
lean::dec(x_3);
x_11 = lean::mk_nat_obj(0u);
x_12 = lean::unbox_uint32(x_11);
lean::dec(x_11);
lean::inc(x_0);
x_15 = l_lean_parser_monad__parsec_ch___at___private_3519775105__ident_x_27___spec__11(x_12, x_0, x_1, x_2);
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
obj* x_21; obj* x_23; obj* x_26; obj* x_27; obj* x_29; obj* x_30; obj* x_32; obj* x_35; obj* x_37; obj* x_38; obj* x_39; 
x_21 = lean::cnstr_get(x_16, 1);
lean::inc(x_21);
x_23 = lean::cnstr_get(x_16, 2);
lean::inc(x_23);
lean::dec(x_16);
x_26 = lean::string_iterator_remaining(x_21);
x_27 = l_string_join___closed__1;
lean::inc(x_27);
x_29 = l_lean_parser_parse__string__literal__aux___main___at_lean_parser_string__lit_x_27___spec__2(x_26, x_27, x_0, x_21, x_18);
x_30 = lean::cnstr_get(x_29, 0);
lean::inc(x_30);
x_32 = lean::cnstr_get(x_29, 1);
lean::inc(x_32);
lean::dec(x_29);
x_35 = l_lean_parser_finish__comment__block___closed__2;
lean::inc(x_35);
x_37 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_35, x_30);
x_38 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_23, x_37);
if (lean::is_scalar(x_20)) {
 x_39 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_39 = x_20;
}
lean::cnstr_set(x_39, 0, x_38);
lean::cnstr_set(x_39, 1, x_32);
return x_39;
}
else
{
obj* x_41; unsigned char x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; 
lean::dec(x_0);
x_41 = lean::cnstr_get(x_16, 0);
lean::inc(x_41);
x_43 = lean::cnstr_get_scalar<unsigned char>(x_16, sizeof(void*)*1);
if (lean::is_shared(x_16)) {
 lean::dec(x_16);
 x_44 = lean::box(0);
} else {
 lean::cnstr_release(x_16, 0);
 x_44 = x_16;
}
if (lean::is_scalar(x_44)) {
 x_45 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_45 = x_44;
}
lean::cnstr_set(x_45, 0, x_41);
lean::cnstr_set_scalar(x_45, sizeof(void*)*1, x_43);
x_46 = x_45;
if (lean::is_scalar(x_20)) {
 x_47 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_47 = x_20;
}
lean::cnstr_set(x_47, 0, x_46);
lean::cnstr_set(x_47, 1, x_18);
return x_47;
}
}
else
{
obj* x_48; unsigned char x_49; 
x_48 = lean::mk_nat_obj(1114112u);
x_49 = lean::nat_dec_lt(x_3, x_48);
lean::dec(x_48);
if (x_49 == 0)
{
obj* x_52; unsigned x_53; obj* x_56; obj* x_57; obj* x_59; obj* x_61; 
lean::dec(x_3);
x_52 = lean::mk_nat_obj(0u);
x_53 = lean::unbox_uint32(x_52);
lean::dec(x_52);
lean::inc(x_0);
x_56 = l_lean_parser_monad__parsec_ch___at___private_3519775105__ident_x_27___spec__11(x_53, x_0, x_1, x_2);
x_57 = lean::cnstr_get(x_56, 0);
lean::inc(x_57);
x_59 = lean::cnstr_get(x_56, 1);
lean::inc(x_59);
if (lean::is_shared(x_56)) {
 lean::dec(x_56);
 x_61 = lean::box(0);
} else {
 lean::cnstr_release(x_56, 0);
 lean::cnstr_release(x_56, 1);
 x_61 = x_56;
}
if (lean::obj_tag(x_57) == 0)
{
obj* x_62; obj* x_64; obj* x_67; obj* x_68; obj* x_70; obj* x_71; obj* x_73; obj* x_76; obj* x_78; obj* x_79; obj* x_80; 
x_62 = lean::cnstr_get(x_57, 1);
lean::inc(x_62);
x_64 = lean::cnstr_get(x_57, 2);
lean::inc(x_64);
lean::dec(x_57);
x_67 = lean::string_iterator_remaining(x_62);
x_68 = l_string_join___closed__1;
lean::inc(x_68);
x_70 = l_lean_parser_parse__string__literal__aux___main___at_lean_parser_string__lit_x_27___spec__2(x_67, x_68, x_0, x_62, x_59);
x_71 = lean::cnstr_get(x_70, 0);
lean::inc(x_71);
x_73 = lean::cnstr_get(x_70, 1);
lean::inc(x_73);
lean::dec(x_70);
x_76 = l_lean_parser_finish__comment__block___closed__2;
lean::inc(x_76);
x_78 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_76, x_71);
x_79 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_64, x_78);
if (lean::is_scalar(x_61)) {
 x_80 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_80 = x_61;
}
lean::cnstr_set(x_80, 0, x_79);
lean::cnstr_set(x_80, 1, x_73);
return x_80;
}
else
{
obj* x_82; unsigned char x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_88; 
lean::dec(x_0);
x_82 = lean::cnstr_get(x_57, 0);
lean::inc(x_82);
x_84 = lean::cnstr_get_scalar<unsigned char>(x_57, sizeof(void*)*1);
if (lean::is_shared(x_57)) {
 lean::dec(x_57);
 x_85 = lean::box(0);
} else {
 lean::cnstr_release(x_57, 0);
 x_85 = x_57;
}
if (lean::is_scalar(x_85)) {
 x_86 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_86 = x_85;
}
lean::cnstr_set(x_86, 0, x_82);
lean::cnstr_set_scalar(x_86, sizeof(void*)*1, x_84);
x_87 = x_86;
if (lean::is_scalar(x_61)) {
 x_88 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_88 = x_61;
}
lean::cnstr_set(x_88, 0, x_87);
lean::cnstr_set(x_88, 1, x_59);
return x_88;
}
}
else
{
unsigned x_89; obj* x_92; obj* x_93; obj* x_95; obj* x_97; 
x_89 = lean::unbox_uint32(x_3);
lean::dec(x_3);
lean::inc(x_0);
x_92 = l_lean_parser_monad__parsec_ch___at___private_3519775105__ident_x_27___spec__11(x_89, x_0, x_1, x_2);
x_93 = lean::cnstr_get(x_92, 0);
lean::inc(x_93);
x_95 = lean::cnstr_get(x_92, 1);
lean::inc(x_95);
if (lean::is_shared(x_92)) {
 lean::dec(x_92);
 x_97 = lean::box(0);
} else {
 lean::cnstr_release(x_92, 0);
 lean::cnstr_release(x_92, 1);
 x_97 = x_92;
}
if (lean::obj_tag(x_93) == 0)
{
obj* x_98; obj* x_100; obj* x_103; obj* x_104; obj* x_106; obj* x_107; obj* x_109; obj* x_112; obj* x_114; obj* x_115; obj* x_116; 
x_98 = lean::cnstr_get(x_93, 1);
lean::inc(x_98);
x_100 = lean::cnstr_get(x_93, 2);
lean::inc(x_100);
lean::dec(x_93);
x_103 = lean::string_iterator_remaining(x_98);
x_104 = l_string_join___closed__1;
lean::inc(x_104);
x_106 = l_lean_parser_parse__string__literal__aux___main___at_lean_parser_string__lit_x_27___spec__2(x_103, x_104, x_0, x_98, x_95);
x_107 = lean::cnstr_get(x_106, 0);
lean::inc(x_107);
x_109 = lean::cnstr_get(x_106, 1);
lean::inc(x_109);
lean::dec(x_106);
x_112 = l_lean_parser_finish__comment__block___closed__2;
lean::inc(x_112);
x_114 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_112, x_107);
x_115 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_100, x_114);
if (lean::is_scalar(x_97)) {
 x_116 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_116 = x_97;
}
lean::cnstr_set(x_116, 0, x_115);
lean::cnstr_set(x_116, 1, x_109);
return x_116;
}
else
{
obj* x_118; unsigned char x_120; obj* x_121; obj* x_122; obj* x_123; obj* x_124; 
lean::dec(x_0);
x_118 = lean::cnstr_get(x_93, 0);
lean::inc(x_118);
x_120 = lean::cnstr_get_scalar<unsigned char>(x_93, sizeof(void*)*1);
if (lean::is_shared(x_93)) {
 lean::dec(x_93);
 x_121 = lean::box(0);
} else {
 lean::cnstr_release(x_93, 0);
 x_121 = x_93;
}
if (lean::is_scalar(x_121)) {
 x_122 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_122 = x_121;
}
lean::cnstr_set(x_122, 0, x_118);
lean::cnstr_set_scalar(x_122, sizeof(void*)*1, x_120);
x_123 = x_122;
if (lean::is_scalar(x_97)) {
 x_124 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_124 = x_97;
}
lean::cnstr_set(x_124, 0, x_123);
lean::cnstr_set(x_124, 1, x_95);
return x_124;
}
}
}
}
else
{
unsigned x_125; obj* x_128; obj* x_129; obj* x_131; obj* x_133; 
x_125 = lean::unbox_uint32(x_3);
lean::dec(x_3);
lean::inc(x_0);
x_128 = l_lean_parser_monad__parsec_ch___at___private_3519775105__ident_x_27___spec__11(x_125, x_0, x_1, x_2);
x_129 = lean::cnstr_get(x_128, 0);
lean::inc(x_129);
x_131 = lean::cnstr_get(x_128, 1);
lean::inc(x_131);
if (lean::is_shared(x_128)) {
 lean::dec(x_128);
 x_133 = lean::box(0);
} else {
 lean::cnstr_release(x_128, 0);
 lean::cnstr_release(x_128, 1);
 x_133 = x_128;
}
if (lean::obj_tag(x_129) == 0)
{
obj* x_134; obj* x_136; obj* x_139; obj* x_140; obj* x_142; obj* x_143; obj* x_145; obj* x_148; obj* x_150; obj* x_151; obj* x_152; 
x_134 = lean::cnstr_get(x_129, 1);
lean::inc(x_134);
x_136 = lean::cnstr_get(x_129, 2);
lean::inc(x_136);
lean::dec(x_129);
x_139 = lean::string_iterator_remaining(x_134);
x_140 = l_string_join___closed__1;
lean::inc(x_140);
x_142 = l_lean_parser_parse__string__literal__aux___main___at_lean_parser_string__lit_x_27___spec__2(x_139, x_140, x_0, x_134, x_131);
x_143 = lean::cnstr_get(x_142, 0);
lean::inc(x_143);
x_145 = lean::cnstr_get(x_142, 1);
lean::inc(x_145);
lean::dec(x_142);
x_148 = l_lean_parser_finish__comment__block___closed__2;
lean::inc(x_148);
x_150 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_148, x_143);
x_151 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_136, x_150);
if (lean::is_scalar(x_133)) {
 x_152 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_152 = x_133;
}
lean::cnstr_set(x_152, 0, x_151);
lean::cnstr_set(x_152, 1, x_145);
return x_152;
}
else
{
obj* x_154; unsigned char x_156; obj* x_157; obj* x_158; obj* x_159; obj* x_160; 
lean::dec(x_0);
x_154 = lean::cnstr_get(x_129, 0);
lean::inc(x_154);
x_156 = lean::cnstr_get_scalar<unsigned char>(x_129, sizeof(void*)*1);
if (lean::is_shared(x_129)) {
 lean::dec(x_129);
 x_157 = lean::box(0);
} else {
 lean::cnstr_release(x_129, 0);
 x_157 = x_129;
}
if (lean::is_scalar(x_157)) {
 x_158 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_158 = x_157;
}
lean::cnstr_set(x_158, 0, x_154);
lean::cnstr_set_scalar(x_158, sizeof(void*)*1, x_156);
x_159 = x_158;
if (lean::is_scalar(x_133)) {
 x_160 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_160 = x_133;
}
lean::cnstr_set(x_160, 0, x_159);
lean::cnstr_set(x_160, 1, x_131);
return x_160;
}
}
}
}
obj* l___private_3602054007__mk__consume__token(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
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
x_9 = l_lean_parser_combinators_node___at_lean_parser_detail__ident__part_parser___spec__8(x_3, x_4, x_0, x_1, x_2);
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
obj* x_18; unsigned char x_20; 
x_18 = lean::cnstr_get(x_10, 0);
lean::inc(x_18);
x_20 = lean::cnstr_get_scalar<unsigned char>(x_10, sizeof(void*)*1);
if (x_20 == 0)
{
obj* x_22; obj* x_23; obj* x_26; obj* x_27; obj* x_29; obj* x_32; obj* x_33; 
lean::dec(x_10);
x_22 = l_lean_parser_string__lit;
x_23 = l_lean_parser_string__lit_x_27___closed__1;
lean::inc(x_23);
lean::inc(x_22);
x_26 = l_lean_parser_combinators_node___at_lean_parser_detail__ident__part_parser___spec__8(x_22, x_23, x_0, x_1, x_12);
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
x_6 = l___private_3519775105__ident_x_27(x_2, x_3, x_4);
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
obj* x_12; obj* x_14; obj* x_16; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_23; obj* x_25; unsigned char x_28; 
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
x_41 = l___private_3602054007__mk__consume__token(x_1, x_0, x_2, x_14, x_9);
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
obj* x_55; unsigned char x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_55 = lean::cnstr_get(x_7, 0);
lean::inc(x_55);
x_57 = lean::cnstr_get_scalar<unsigned char>(x_7, sizeof(void*)*1);
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
obj* x_20; obj* x_22; obj* x_23; obj* x_25; unsigned char x_27; 
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
obj* x_64; unsigned char x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_72; 
lean::dec(x_6);
lean::dec(x_20);
x_64 = lean::cnstr_get(x_33, 0);
lean::inc(x_64);
x_66 = lean::cnstr_get_scalar<unsigned char>(x_33, sizeof(void*)*1);
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
obj* x_98; unsigned char x_100; obj* x_101; obj* x_102; obj* x_103; obj* x_105; obj* x_109; obj* x_110; obj* x_112; 
x_98 = lean::cnstr_get(x_3, 0);
lean::inc(x_98);
x_100 = lean::cnstr_get_scalar<unsigned char>(x_3, sizeof(void*)*1);
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
x_152 = l___private_3519775105__ident_x_27(x_0, x_131, x_126);
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
x_167 = l___private_3602054007__mk__consume__token(x_158, x_1, x_0, x_131, x_126);
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
obj* x_231; unsigned char x_233; obj* x_234; obj* x_235; obj* x_236; obj* x_237; obj* x_238; obj* x_239; 
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_121);
x_231 = lean::cnstr_get(x_194, 0);
lean::inc(x_231);
x_233 = lean::cnstr_get_scalar<unsigned char>(x_194, sizeof(void*)*1);
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
obj* x_244; unsigned char x_246; obj* x_247; obj* x_248; obj* x_249; obj* x_250; obj* x_251; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_121);
x_244 = lean::cnstr_get(x_136, 0);
lean::inc(x_244);
x_246 = lean::cnstr_get_scalar<unsigned char>(x_136, sizeof(void*)*1);
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
x_260 = l_lean_parser_monad__parsec_error___at___private_4089500695__finish__comment__block__aux___main___spec__1___rarg(x_254, x_255, x_253, x_253, x_0, x_131, x_126);
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
obj* x_271; unsigned char x_273; obj* x_274; obj* x_275; obj* x_276; obj* x_277; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_115);
lean::dec(x_121);
x_271 = lean::cnstr_get(x_124, 0);
lean::inc(x_271);
x_273 = lean::cnstr_get_scalar<unsigned char>(x_124, sizeof(void*)*1);
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
obj* x_281; unsigned char x_283; obj* x_284; obj* x_285; obj* x_286; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_281 = lean::cnstr_get(x_110, 0);
lean::inc(x_281);
x_283 = lean::cnstr_get_scalar<unsigned char>(x_110, sizeof(void*)*1);
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
obj* x_294; unsigned char x_296; 
x_294 = lean::cnstr_get(x_102, 0);
lean::inc(x_294);
x_296 = lean::cnstr_get_scalar<unsigned char>(x_102, sizeof(void*)*1);
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
obj* _init_l_lean_parser_token___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("token: not implemented");
return x_0;
}
}
obj* l_lean_parser_parsec__t_lookahead___at_lean_parser_token___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; unsigned char x_6; 
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
x_15 = l_lean_parser_monad__parsec_error___at___private_4089500695__finish__comment__block__aux___main___spec__1___rarg(x_8, x_9, x_7, x_7, x_0, x_1, x_2);
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
obj* x_25; unsigned char x_27; 
x_25 = lean::cnstr_get(x_23, 0);
lean::inc(x_25);
x_27 = lean::cnstr_get_scalar<unsigned char>(x_23, sizeof(void*)*1);
if (x_27 == 0)
{
obj* x_29; unsigned x_30; obj* x_32; obj* x_33; obj* x_35; obj* x_38; 
lean::dec(x_23);
x_29 = l_lean_id__begin__escape;
x_30 = lean::unbox_uint32(x_29);
lean::inc(x_1);
x_32 = l_lean_parser_monad__parsec_ch___at___private_3519775105__ident_x_27___spec__11(x_30, x_0, x_1, x_18);
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
unsigned x_41; unsigned char x_42; 
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
x_55 = l_lean_parser_monad__parsec_error___at___private_4089500695__finish__comment__block__aux___main___spec__1___rarg(x_48, x_50, x_49, x_49, x_0, x_1, x_2);
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
obj* x_65; unsigned char x_67; 
x_65 = lean::cnstr_get(x_63, 0);
lean::inc(x_65);
x_67 = lean::cnstr_get_scalar<unsigned char>(x_63, sizeof(void*)*1);
if (x_67 == 0)
{
obj* x_69; unsigned x_70; obj* x_72; obj* x_73; obj* x_75; obj* x_78; 
lean::dec(x_63);
x_69 = l_lean_id__begin__escape;
x_70 = lean::unbox_uint32(x_69);
lean::inc(x_1);
x_72 = l_lean_parser_monad__parsec_ch___at___private_3519775105__ident_x_27___spec__11(x_70, x_0, x_1, x_58);
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
x_32 = l___private_3229416877__update__trailing___main(x_25, x_0);
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
obj* x_38; unsigned char x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; 
lean::dec(x_0);
x_38 = lean::cnstr_get(x_24, 0);
lean::inc(x_38);
x_40 = lean::cnstr_get_scalar<unsigned char>(x_24, sizeof(void*)*1);
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
obj* x_46; unsigned char x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_54; 
lean::dec(x_2);
x_46 = lean::cnstr_get(x_6, 0);
lean::inc(x_46);
x_48 = lean::cnstr_get_scalar<unsigned char>(x_6, sizeof(void*)*1);
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
x_62 = l___private_3229416877__update__trailing___main(x_55, x_0);
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
obj* x_68; unsigned char x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; 
lean::dec(x_0);
x_68 = lean::cnstr_get(x_54, 0);
lean::inc(x_68);
x_70 = lean::cnstr_get_scalar<unsigned char>(x_54, sizeof(void*)*1);
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
obj* x_2; obj* x_3; obj* x_4; obj* x_7; unsigned char x_8; obj* x_9; obj* x_10; obj* x_11; 
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
obj* l_lean_parser_peek__token(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_parser_monad__parsec_observing___at_lean_parser_peek__token___spec__2(x_0, x_1, x_2);
return x_3;
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
obj* x_24; obj* x_26; unsigned char x_29; 
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
x_33 = l_lean_parser_monad__parsec_error___at___private_4089500695__finish__comment__block__aux___main___spec__1___rarg(x_26, x_0, x_31, x_32, x_3, x_16, x_11);
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
obj* x_56; unsigned char x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_65; obj* x_66; obj* x_67; obj* x_68; 
lean::dec(x_14);
lean::dec(x_20);
x_56 = lean::cnstr_get(x_34, 0);
lean::inc(x_56);
x_58 = lean::cnstr_get_scalar<unsigned char>(x_34, sizeof(void*)*1);
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
x_100 = l_lean_parser_monad__parsec_error___at___private_4089500695__finish__comment__block__aux___main___spec__1___rarg(x_98, x_0, x_96, x_97, x_3, x_16, x_11);
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
obj* x_117; unsigned char x_119; obj* x_120; obj* x_121; obj* x_122; obj* x_123; obj* x_125; obj* x_126; obj* x_127; obj* x_128; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
x_117 = lean::cnstr_get(x_9, 0);
lean::inc(x_117);
x_119 = lean::cnstr_get_scalar<unsigned char>(x_9, sizeof(void*)*1);
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
x_29 = l_lean_parser_monad__parsec_error___at___private_4089500695__finish__comment__block__aux___main___spec__1___rarg(x_26, x_0, x_24, x_25, x_1, x_14, x_9);
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
obj* x_59; unsigned char x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_67; obj* x_68; obj* x_69; obj* x_70; 
lean::dec(x_1);
lean::dec(x_2);
x_59 = lean::cnstr_get(x_7, 0);
lean::inc(x_59);
x_61 = lean::cnstr_get_scalar<unsigned char>(x_7, sizeof(void*)*1);
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
obj* l_lean_parser_number_parser(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_number_parser___rarg), 1, 0);
return x_2;
}
}
obj* l_lean_parser_try__view___at_lean_parser_number_parser___spec__1(obj* x_0) {
_start:
{
obj* x_1; unsigned char x_4; 
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
obj* l_lean_parser_number_parser_view(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_number_parser_view___rarg), 1, 0);
return x_2;
}
}
obj* l___private_1765190339__to__nat__core___main(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; unsigned char x_5; 
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::nat_dec_eq(x_2, x_4);
if (x_5 == 0)
{
obj* x_6; obj* x_7; unsigned x_10; unsigned char x_11; obj* x_12; obj* x_14; obj* x_15; unsigned x_17; 
x_6 = lean::mk_nat_obj(1u);
x_7 = lean::nat_sub(x_2, x_6);
lean::dec(x_6);
lean::dec(x_2);
x_10 = lean::string_iterator_curr(x_1);
x_11 = l_char_is__digit(x_10);
x_12 = lean::nat_mul(x_3, x_0);
lean::dec(x_3);
x_14 = lean::string_iterator_next(x_1);
if (x_11 == 0)
{
obj* x_19; obj* x_20; unsigned char x_21; 
x_19 = lean::mk_nat_obj(97u);
x_20 = lean::mk_nat_obj(55296u);
x_21 = lean::nat_dec_lt(x_19, x_20);
lean::dec(x_20);
if (x_21 == 0)
{
obj* x_23; unsigned char x_24; 
x_23 = lean::mk_nat_obj(57343u);
x_24 = lean::nat_dec_lt(x_23, x_19);
lean::dec(x_23);
if (x_24 == 0)
{
unsigned x_27; 
lean::dec(x_19);
x_27 = lean::unbox_uint32(x_4);
x_17 = x_27;
goto lbl_18;
}
else
{
obj* x_28; unsigned char x_29; 
x_28 = lean::mk_nat_obj(1114112u);
x_29 = lean::nat_dec_lt(x_19, x_28);
lean::dec(x_28);
if (x_29 == 0)
{
unsigned x_32; 
lean::dec(x_19);
x_32 = lean::unbox_uint32(x_4);
x_17 = x_32;
goto lbl_18;
}
else
{
unsigned x_33; 
x_33 = lean::unbox_uint32(x_19);
lean::dec(x_19);
x_17 = x_33;
goto lbl_18;
}
}
}
else
{
unsigned x_35; 
x_35 = lean::unbox_uint32(x_19);
lean::dec(x_19);
x_17 = x_35;
goto lbl_18;
}
}
else
{
obj* x_37; obj* x_38; unsigned char x_39; 
x_37 = lean::mk_nat_obj(48u);
x_38 = lean::mk_nat_obj(55296u);
x_39 = lean::nat_dec_lt(x_37, x_38);
lean::dec(x_38);
if (x_39 == 0)
{
obj* x_41; unsigned char x_42; 
x_41 = lean::mk_nat_obj(57343u);
x_42 = lean::nat_dec_lt(x_41, x_37);
lean::dec(x_41);
if (x_42 == 0)
{
obj* x_45; obj* x_46; obj* x_49; 
lean::dec(x_37);
x_45 = lean::box_uint32(x_10);
x_46 = lean::nat_sub(x_45, x_4);
lean::dec(x_4);
lean::dec(x_45);
x_49 = lean::nat_add(x_12, x_46);
lean::dec(x_46);
lean::dec(x_12);
x_1 = x_14;
x_2 = x_7;
x_3 = x_49;
goto _start;
}
else
{
obj* x_53; unsigned char x_54; 
x_53 = lean::mk_nat_obj(1114112u);
x_54 = lean::nat_dec_lt(x_37, x_53);
lean::dec(x_53);
if (x_54 == 0)
{
obj* x_57; obj* x_58; obj* x_61; 
lean::dec(x_37);
x_57 = lean::box_uint32(x_10);
x_58 = lean::nat_sub(x_57, x_4);
lean::dec(x_4);
lean::dec(x_57);
x_61 = lean::nat_add(x_12, x_58);
lean::dec(x_58);
lean::dec(x_12);
x_1 = x_14;
x_2 = x_7;
x_3 = x_61;
goto _start;
}
else
{
obj* x_66; obj* x_67; obj* x_70; 
lean::dec(x_4);
x_66 = lean::box_uint32(x_10);
x_67 = lean::nat_sub(x_66, x_37);
lean::dec(x_37);
lean::dec(x_66);
x_70 = lean::nat_add(x_12, x_67);
lean::dec(x_67);
lean::dec(x_12);
x_1 = x_14;
x_2 = x_7;
x_3 = x_70;
goto _start;
}
}
}
else
{
obj* x_75; obj* x_76; obj* x_79; 
lean::dec(x_4);
x_75 = lean::box_uint32(x_10);
x_76 = lean::nat_sub(x_75, x_37);
lean::dec(x_37);
lean::dec(x_75);
x_79 = lean::nat_add(x_12, x_76);
lean::dec(x_76);
lean::dec(x_12);
x_1 = x_14;
x_2 = x_7;
x_3 = x_79;
goto _start;
}
}
lbl_16:
{
obj* x_84; obj* x_85; unsigned char x_86; 
lean::dec(x_15);
x_84 = lean::mk_nat_obj(65u);
x_85 = lean::mk_nat_obj(55296u);
x_86 = lean::nat_dec_lt(x_84, x_85);
lean::dec(x_85);
if (x_86 == 0)
{
obj* x_88; unsigned char x_89; 
x_88 = lean::mk_nat_obj(57343u);
x_89 = lean::nat_dec_lt(x_88, x_84);
lean::dec(x_88);
if (x_89 == 0)
{
obj* x_92; obj* x_93; obj* x_96; 
lean::dec(x_84);
x_92 = lean::box_uint32(x_10);
x_93 = lean::nat_sub(x_92, x_4);
lean::dec(x_4);
lean::dec(x_92);
x_96 = lean::nat_add(x_12, x_93);
lean::dec(x_93);
lean::dec(x_12);
x_1 = x_14;
x_2 = x_7;
x_3 = x_96;
goto _start;
}
else
{
obj* x_100; unsigned char x_101; 
x_100 = lean::mk_nat_obj(1114112u);
x_101 = lean::nat_dec_lt(x_84, x_100);
lean::dec(x_100);
if (x_101 == 0)
{
obj* x_104; obj* x_105; obj* x_108; 
lean::dec(x_84);
x_104 = lean::box_uint32(x_10);
x_105 = lean::nat_sub(x_104, x_4);
lean::dec(x_4);
lean::dec(x_104);
x_108 = lean::nat_add(x_12, x_105);
lean::dec(x_105);
lean::dec(x_12);
x_1 = x_14;
x_2 = x_7;
x_3 = x_108;
goto _start;
}
else
{
obj* x_113; obj* x_114; obj* x_117; 
lean::dec(x_4);
x_113 = lean::box_uint32(x_10);
x_114 = lean::nat_sub(x_113, x_84);
lean::dec(x_84);
lean::dec(x_113);
x_117 = lean::nat_add(x_12, x_114);
lean::dec(x_114);
lean::dec(x_12);
x_1 = x_14;
x_2 = x_7;
x_3 = x_117;
goto _start;
}
}
}
else
{
obj* x_122; obj* x_123; obj* x_126; 
lean::dec(x_4);
x_122 = lean::box_uint32(x_10);
x_123 = lean::nat_sub(x_122, x_84);
lean::dec(x_84);
lean::dec(x_122);
x_126 = lean::nat_add(x_12, x_123);
lean::dec(x_123);
lean::dec(x_12);
x_1 = x_14;
x_2 = x_7;
x_3 = x_126;
goto _start;
}
}
lbl_18:
{
unsigned x_130; obj* x_132; obj* x_133; unsigned char x_134; 
x_132 = lean::box_uint32(x_17);
x_133 = lean::box_uint32(x_10);
x_134 = lean::nat_dec_le(x_132, x_133);
lean::dec(x_133);
lean::dec(x_132);
if (x_134 == 0)
{
obj* x_137; 
x_137 = lean::box(0);
x_15 = x_137;
goto lbl_16;
}
else
{
obj* x_138; obj* x_139; unsigned char x_140; 
x_138 = lean::mk_nat_obj(102u);
x_139 = lean::mk_nat_obj(55296u);
x_140 = lean::nat_dec_lt(x_138, x_139);
lean::dec(x_139);
if (x_140 == 0)
{
obj* x_142; unsigned char x_143; 
x_142 = lean::mk_nat_obj(57343u);
x_143 = lean::nat_dec_lt(x_142, x_138);
lean::dec(x_142);
if (x_143 == 0)
{
unsigned x_146; 
lean::dec(x_138);
x_146 = lean::unbox_uint32(x_4);
x_130 = x_146;
goto lbl_131;
}
else
{
obj* x_147; unsigned char x_148; 
x_147 = lean::mk_nat_obj(1114112u);
x_148 = lean::nat_dec_lt(x_138, x_147);
lean::dec(x_147);
if (x_148 == 0)
{
unsigned x_151; 
lean::dec(x_138);
x_151 = lean::unbox_uint32(x_4);
x_130 = x_151;
goto lbl_131;
}
else
{
unsigned x_152; 
x_152 = lean::unbox_uint32(x_138);
lean::dec(x_138);
x_130 = x_152;
goto lbl_131;
}
}
}
else
{
unsigned x_154; 
x_154 = lean::unbox_uint32(x_138);
lean::dec(x_138);
x_130 = x_154;
goto lbl_131;
}
}
lbl_131:
{
obj* x_156; obj* x_157; unsigned char x_158; 
x_156 = lean::box_uint32(x_10);
x_157 = lean::box_uint32(x_130);
x_158 = lean::nat_dec_le(x_156, x_157);
lean::dec(x_157);
if (x_158 == 0)
{
obj* x_161; 
lean::dec(x_156);
x_161 = lean::box(0);
x_15 = x_161;
goto lbl_16;
}
else
{
obj* x_163; obj* x_164; obj* x_167; 
lean::dec(x_4);
x_163 = lean::box_uint32(x_17);
x_164 = lean::nat_sub(x_156, x_163);
lean::dec(x_163);
lean::dec(x_156);
x_167 = lean::nat_add(x_12, x_164);
lean::dec(x_164);
lean::dec(x_12);
x_1 = x_14;
x_2 = x_7;
x_3 = x_167;
goto _start;
}
}
}
}
else
{
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
return x_3;
}
}
}
obj* l___private_1765190339__to__nat__core(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_1765190339__to__nat__core___main(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l___private_1741613153__to__nat__base(obj* x_0, obj* x_1) {
_start:
{
obj* x_3; obj* x_4; obj* x_6; obj* x_7; 
lean::inc(x_0);
x_3 = lean::string_mk_iterator(x_0);
x_4 = lean::string_length(x_0);
lean::dec(x_0);
x_6 = lean::mk_nat_obj(0u);
x_7 = l___private_1765190339__to__nat__core___main(x_1, x_3, x_4, x_6);
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
x_25 = l___private_1741613153__to__nat__base(x_21, x_24);
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
x_38 = l___private_1741613153__to__nat__base(x_34, x_37);
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
x_51 = l___private_1741613153__to__nat__base(x_47, x_50);
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
x_29 = l_lean_parser_monad__parsec_error___at___private_4089500695__finish__comment__block__aux___main___spec__1___rarg(x_26, x_0, x_24, x_25, x_1, x_14, x_9);
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
obj* x_59; unsigned char x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_67; obj* x_68; obj* x_69; obj* x_70; 
lean::dec(x_1);
lean::dec(x_2);
x_59 = lean::cnstr_get(x_7, 0);
lean::inc(x_59);
x_61 = lean::cnstr_get_scalar<unsigned char>(x_7, sizeof(void*)*1);
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
obj* l_lean_parser_string__lit_parser(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_string__lit_parser___rarg), 1, 0);
return x_2;
}
}
obj* l_lean_parser_try__view___at_lean_parser_string__lit_parser___spec__1(obj* x_0) {
_start:
{
obj* x_1; unsigned char x_4; 
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
obj* l_lean_parser_string__lit_parser_view(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_string__lit_parser_view___rarg), 1, 0);
return x_2;
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
obj* _init_l_lean_parser_string__lit_view_value___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parse__string__literal___at_lean_parser_string__lit_view_value___spec__1), 1, 0);
return x_0;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_string__lit_view_value___spec__3___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; unsigned char x_7; obj* x_8; obj* x_9; 
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
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_string__lit_view_value___spec__2(unsigned x_0, obj* x_1) {
_start:
{
unsigned char x_2; 
x_2 = lean::string_iterator_has_next(x_1);
if (x_2 == 0)
{
obj* x_3; obj* x_4; obj* x_5; obj* x_9; 
x_3 = lean::box(0);
x_4 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_5 = l_mjoin___rarg___closed__1;
lean::inc(x_3);
lean::inc(x_5);
lean::inc(x_4);
x_9 = l_lean_parser_monad__parsec_error___at_lean_parser_string__lit_view_value___spec__3___rarg(x_4, x_5, x_3, x_3, x_1);
if (lean::obj_tag(x_9) == 0)
{
obj* x_10; obj* x_12; obj* x_14; 
x_10 = lean::cnstr_get(x_9, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_9, 1);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_9, 2);
lean::inc(x_14);
if (lean::obj_tag(x_14) == 0)
{
lean::dec(x_14);
lean::dec(x_12);
lean::dec(x_10);
return x_9;
}
else
{
obj* x_20; obj* x_22; obj* x_24; obj* x_25; obj* x_26; 
lean::dec(x_9);
x_20 = lean::cnstr_get(x_14, 0);
lean::inc(x_20);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_22 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 x_22 = x_14;
}
lean::inc(x_5);
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_24, 0, x_5);
lean::closure_set(x_24, 1, x_20);
if (lean::is_scalar(x_22)) {
 x_25 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_25 = x_22;
}
lean::cnstr_set(x_25, 0, x_24);
x_26 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_26, 0, x_10);
lean::cnstr_set(x_26, 1, x_12);
lean::cnstr_set(x_26, 2, x_25);
return x_26;
}
}
else
{
obj* x_27; unsigned char x_29; 
x_27 = lean::cnstr_get(x_9, 0);
lean::inc(x_27);
x_29 = lean::cnstr_get_scalar<unsigned char>(x_9, sizeof(void*)*1);
if (x_29 == 0)
{
obj* x_31; obj* x_33; obj* x_35; obj* x_38; obj* x_39; obj* x_42; obj* x_43; obj* x_44; 
lean::dec(x_9);
x_31 = lean::cnstr_get(x_27, 0);
lean::inc(x_31);
x_33 = lean::cnstr_get(x_27, 1);
lean::inc(x_33);
x_35 = lean::cnstr_get(x_27, 2);
lean::inc(x_35);
lean::inc(x_5);
x_38 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_38, 0, x_5);
lean::closure_set(x_38, 1, x_35);
x_39 = lean::cnstr_get(x_27, 3);
lean::inc(x_39);
lean::dec(x_27);
x_42 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_42, 0, x_31);
lean::cnstr_set(x_42, 1, x_33);
lean::cnstr_set(x_42, 2, x_38);
lean::cnstr_set(x_42, 3, x_39);
x_43 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_43, 0, x_42);
lean::cnstr_set_scalar(x_43, sizeof(void*)*1, x_29);
x_44 = x_43;
return x_44;
}
else
{
lean::dec(x_27);
return x_9;
}
}
}
else
{
unsigned x_46; obj* x_47; obj* x_48; unsigned char x_49; 
x_46 = lean::string_iterator_curr(x_1);
x_47 = lean::box_uint32(x_46);
x_48 = lean::box_uint32(x_0);
x_49 = lean::nat_dec_eq(x_47, x_48);
lean::dec(x_48);
if (x_49 == 0)
{
obj* x_52; obj* x_53; obj* x_55; obj* x_57; obj* x_58; obj* x_59; obj* x_62; 
lean::dec(x_47);
x_52 = l_char_quote__core(x_46);
x_53 = l_char_has__repr___closed__1;
lean::inc(x_53);
x_55 = lean::string_append(x_53, x_52);
lean::dec(x_52);
x_57 = lean::string_append(x_55, x_53);
x_58 = lean::box(0);
x_59 = l_mjoin___rarg___closed__1;
lean::inc(x_58);
lean::inc(x_59);
x_62 = l_lean_parser_monad__parsec_error___at_lean_parser_string__lit_view_value___spec__3___rarg(x_57, x_59, x_58, x_58, x_1);
if (lean::obj_tag(x_62) == 0)
{
obj* x_63; obj* x_65; obj* x_67; 
x_63 = lean::cnstr_get(x_62, 0);
lean::inc(x_63);
x_65 = lean::cnstr_get(x_62, 1);
lean::inc(x_65);
x_67 = lean::cnstr_get(x_62, 2);
lean::inc(x_67);
if (lean::obj_tag(x_67) == 0)
{
lean::dec(x_65);
lean::dec(x_63);
lean::dec(x_67);
return x_62;
}
else
{
obj* x_73; obj* x_75; obj* x_77; obj* x_78; obj* x_79; 
lean::dec(x_62);
x_73 = lean::cnstr_get(x_67, 0);
lean::inc(x_73);
if (lean::is_shared(x_67)) {
 lean::dec(x_67);
 x_75 = lean::box(0);
} else {
 lean::cnstr_release(x_67, 0);
 x_75 = x_67;
}
lean::inc(x_59);
x_77 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_77, 0, x_59);
lean::closure_set(x_77, 1, x_73);
if (lean::is_scalar(x_75)) {
 x_78 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_78 = x_75;
}
lean::cnstr_set(x_78, 0, x_77);
x_79 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_79, 0, x_63);
lean::cnstr_set(x_79, 1, x_65);
lean::cnstr_set(x_79, 2, x_78);
return x_79;
}
}
else
{
obj* x_80; unsigned char x_82; 
x_80 = lean::cnstr_get(x_62, 0);
lean::inc(x_80);
x_82 = lean::cnstr_get_scalar<unsigned char>(x_62, sizeof(void*)*1);
if (x_82 == 0)
{
obj* x_84; obj* x_86; obj* x_88; obj* x_91; obj* x_92; obj* x_95; obj* x_96; obj* x_97; 
lean::dec(x_62);
x_84 = lean::cnstr_get(x_80, 0);
lean::inc(x_84);
x_86 = lean::cnstr_get(x_80, 1);
lean::inc(x_86);
x_88 = lean::cnstr_get(x_80, 2);
lean::inc(x_88);
lean::inc(x_59);
x_91 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_91, 0, x_59);
lean::closure_set(x_91, 1, x_88);
x_92 = lean::cnstr_get(x_80, 3);
lean::inc(x_92);
lean::dec(x_80);
x_95 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_95, 0, x_84);
lean::cnstr_set(x_95, 1, x_86);
lean::cnstr_set(x_95, 2, x_91);
lean::cnstr_set(x_95, 3, x_92);
x_96 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_96, 0, x_95);
lean::cnstr_set_scalar(x_96, sizeof(void*)*1, x_82);
x_97 = x_96;
return x_97;
}
else
{
lean::dec(x_80);
return x_62;
}
}
}
else
{
obj* x_99; obj* x_100; obj* x_101; 
x_99 = lean::string_iterator_next(x_1);
x_100 = lean::box(0);
x_101 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_101, 0, x_47);
lean::cnstr_set(x_101, 1, x_99);
lean::cnstr_set(x_101, 2, x_100);
return x_101;
}
}
}
}
obj* l_lean_parser_monad__parsec_any___at_lean_parser_string__lit_view_value___spec__5(obj* x_0) {
_start:
{
unsigned char x_1; 
x_1 = lean::string_iterator_has_next(x_0);
if (x_1 == 0)
{
obj* x_2; obj* x_3; obj* x_4; obj* x_8; 
x_2 = lean::box(0);
x_3 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_4 = l_mjoin___rarg___closed__1;
lean::inc(x_2);
lean::inc(x_4);
lean::inc(x_3);
x_8 = l_lean_parser_monad__parsec_error___at_lean_parser_string__lit_view_value___spec__3___rarg(x_3, x_4, x_2, x_2, x_0);
if (lean::obj_tag(x_8) == 0)
{
obj* x_9; obj* x_11; obj* x_13; 
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_8, 2);
lean::inc(x_13);
if (lean::obj_tag(x_13) == 0)
{
lean::dec(x_13);
lean::dec(x_11);
lean::dec(x_9);
return x_8;
}
else
{
obj* x_19; obj* x_21; obj* x_23; obj* x_24; obj* x_25; 
lean::dec(x_8);
x_19 = lean::cnstr_get(x_13, 0);
lean::inc(x_19);
if (lean::is_shared(x_13)) {
 lean::dec(x_13);
 x_21 = lean::box(0);
} else {
 lean::cnstr_release(x_13, 0);
 x_21 = x_13;
}
lean::inc(x_4);
x_23 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_23, 0, x_4);
lean::closure_set(x_23, 1, x_19);
if (lean::is_scalar(x_21)) {
 x_24 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_24 = x_21;
}
lean::cnstr_set(x_24, 0, x_23);
x_25 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_25, 0, x_9);
lean::cnstr_set(x_25, 1, x_11);
lean::cnstr_set(x_25, 2, x_24);
return x_25;
}
}
else
{
obj* x_26; unsigned char x_28; 
x_26 = lean::cnstr_get(x_8, 0);
lean::inc(x_26);
x_28 = lean::cnstr_get_scalar<unsigned char>(x_8, sizeof(void*)*1);
if (x_28 == 0)
{
obj* x_30; obj* x_32; obj* x_34; obj* x_37; obj* x_38; obj* x_41; obj* x_42; obj* x_43; 
lean::dec(x_8);
x_30 = lean::cnstr_get(x_26, 0);
lean::inc(x_30);
x_32 = lean::cnstr_get(x_26, 1);
lean::inc(x_32);
x_34 = lean::cnstr_get(x_26, 2);
lean::inc(x_34);
lean::inc(x_4);
x_37 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_37, 0, x_4);
lean::closure_set(x_37, 1, x_34);
x_38 = lean::cnstr_get(x_26, 3);
lean::inc(x_38);
lean::dec(x_26);
x_41 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_41, 0, x_30);
lean::cnstr_set(x_41, 1, x_32);
lean::cnstr_set(x_41, 2, x_37);
lean::cnstr_set(x_41, 3, x_38);
x_42 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_42, 0, x_41);
lean::cnstr_set_scalar(x_42, sizeof(void*)*1, x_28);
x_43 = x_42;
return x_43;
}
else
{
lean::dec(x_26);
return x_8;
}
}
}
else
{
unsigned x_45; unsigned char x_46; 
x_45 = lean::string_iterator_curr(x_0);
x_46 = l_true_decidable;
if (x_46 == 0)
{
obj* x_47; obj* x_48; obj* x_50; obj* x_52; obj* x_53; obj* x_54; obj* x_57; 
x_47 = l_char_quote__core(x_45);
x_48 = l_char_has__repr___closed__1;
lean::inc(x_48);
x_50 = lean::string_append(x_48, x_47);
lean::dec(x_47);
x_52 = lean::string_append(x_50, x_48);
x_53 = lean::box(0);
x_54 = l_mjoin___rarg___closed__1;
lean::inc(x_53);
lean::inc(x_54);
x_57 = l_lean_parser_monad__parsec_error___at_lean_parser_string__lit_view_value___spec__3___rarg(x_52, x_54, x_53, x_53, x_0);
if (lean::obj_tag(x_57) == 0)
{
obj* x_58; obj* x_60; obj* x_62; 
x_58 = lean::cnstr_get(x_57, 0);
lean::inc(x_58);
x_60 = lean::cnstr_get(x_57, 1);
lean::inc(x_60);
x_62 = lean::cnstr_get(x_57, 2);
lean::inc(x_62);
if (lean::obj_tag(x_62) == 0)
{
lean::dec(x_58);
lean::dec(x_60);
lean::dec(x_62);
return x_57;
}
else
{
obj* x_68; obj* x_70; obj* x_72; obj* x_73; obj* x_74; 
lean::dec(x_57);
x_68 = lean::cnstr_get(x_62, 0);
lean::inc(x_68);
if (lean::is_shared(x_62)) {
 lean::dec(x_62);
 x_70 = lean::box(0);
} else {
 lean::cnstr_release(x_62, 0);
 x_70 = x_62;
}
lean::inc(x_54);
x_72 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_72, 0, x_54);
lean::closure_set(x_72, 1, x_68);
if (lean::is_scalar(x_70)) {
 x_73 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_73 = x_70;
}
lean::cnstr_set(x_73, 0, x_72);
x_74 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_74, 0, x_58);
lean::cnstr_set(x_74, 1, x_60);
lean::cnstr_set(x_74, 2, x_73);
return x_74;
}
}
else
{
obj* x_75; unsigned char x_77; 
x_75 = lean::cnstr_get(x_57, 0);
lean::inc(x_75);
x_77 = lean::cnstr_get_scalar<unsigned char>(x_57, sizeof(void*)*1);
if (x_77 == 0)
{
obj* x_79; obj* x_81; obj* x_83; obj* x_86; obj* x_87; obj* x_90; obj* x_91; obj* x_92; 
lean::dec(x_57);
x_79 = lean::cnstr_get(x_75, 0);
lean::inc(x_79);
x_81 = lean::cnstr_get(x_75, 1);
lean::inc(x_81);
x_83 = lean::cnstr_get(x_75, 2);
lean::inc(x_83);
lean::inc(x_54);
x_86 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_86, 0, x_54);
lean::closure_set(x_86, 1, x_83);
x_87 = lean::cnstr_get(x_75, 3);
lean::inc(x_87);
lean::dec(x_75);
x_90 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_90, 0, x_79);
lean::cnstr_set(x_90, 1, x_81);
lean::cnstr_set(x_90, 2, x_86);
lean::cnstr_set(x_90, 3, x_87);
x_91 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_91, 0, x_90);
lean::cnstr_set_scalar(x_91, sizeof(void*)*1, x_77);
x_92 = x_91;
return x_92;
}
else
{
lean::dec(x_75);
return x_57;
}
}
}
else
{
obj* x_94; obj* x_95; obj* x_96; obj* x_97; 
x_94 = lean::string_iterator_next(x_0);
x_95 = lean::box(0);
x_96 = lean::box_uint32(x_45);
x_97 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_97, 0, x_96);
lean::cnstr_set(x_97, 1, x_94);
lean::cnstr_set(x_97, 2, x_95);
return x_97;
}
}
}
}
obj* l_lean_parser_monad__parsec_digit___at_lean_parser_string__lit_view_value___spec__8(obj* x_0) {
_start:
{
unsigned char x_1; 
x_1 = lean::string_iterator_has_next(x_0);
if (x_1 == 0)
{
obj* x_2; obj* x_3; obj* x_4; obj* x_8; 
x_2 = lean::box(0);
x_3 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_4 = l_mjoin___rarg___closed__1;
lean::inc(x_2);
lean::inc(x_4);
lean::inc(x_3);
x_8 = l_lean_parser_monad__parsec_error___at_lean_parser_string__lit_view_value___spec__3___rarg(x_3, x_4, x_2, x_2, x_0);
if (lean::obj_tag(x_8) == 0)
{
obj* x_9; obj* x_11; obj* x_13; 
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_8, 2);
lean::inc(x_13);
if (lean::obj_tag(x_13) == 0)
{
lean::dec(x_13);
lean::dec(x_11);
lean::dec(x_9);
return x_8;
}
else
{
obj* x_19; obj* x_21; obj* x_23; obj* x_24; obj* x_25; 
lean::dec(x_8);
x_19 = lean::cnstr_get(x_13, 0);
lean::inc(x_19);
if (lean::is_shared(x_13)) {
 lean::dec(x_13);
 x_21 = lean::box(0);
} else {
 lean::cnstr_release(x_13, 0);
 x_21 = x_13;
}
lean::inc(x_4);
x_23 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_23, 0, x_4);
lean::closure_set(x_23, 1, x_19);
if (lean::is_scalar(x_21)) {
 x_24 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_24 = x_21;
}
lean::cnstr_set(x_24, 0, x_23);
x_25 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_25, 0, x_9);
lean::cnstr_set(x_25, 1, x_11);
lean::cnstr_set(x_25, 2, x_24);
return x_25;
}
}
else
{
obj* x_26; unsigned char x_28; 
x_26 = lean::cnstr_get(x_8, 0);
lean::inc(x_26);
x_28 = lean::cnstr_get_scalar<unsigned char>(x_8, sizeof(void*)*1);
if (x_28 == 0)
{
obj* x_30; obj* x_32; obj* x_34; obj* x_37; obj* x_38; obj* x_41; obj* x_42; obj* x_43; 
lean::dec(x_8);
x_30 = lean::cnstr_get(x_26, 0);
lean::inc(x_30);
x_32 = lean::cnstr_get(x_26, 1);
lean::inc(x_32);
x_34 = lean::cnstr_get(x_26, 2);
lean::inc(x_34);
lean::inc(x_4);
x_37 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_37, 0, x_4);
lean::closure_set(x_37, 1, x_34);
x_38 = lean::cnstr_get(x_26, 3);
lean::inc(x_38);
lean::dec(x_26);
x_41 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_41, 0, x_30);
lean::cnstr_set(x_41, 1, x_32);
lean::cnstr_set(x_41, 2, x_37);
lean::cnstr_set(x_41, 3, x_38);
x_42 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_42, 0, x_41);
lean::cnstr_set_scalar(x_42, sizeof(void*)*1, x_28);
x_43 = x_42;
return x_43;
}
else
{
lean::dec(x_26);
return x_8;
}
}
}
else
{
unsigned x_45; unsigned char x_46; 
x_45 = lean::string_iterator_curr(x_0);
x_46 = l_char_is__digit(x_45);
if (x_46 == 0)
{
obj* x_47; obj* x_48; obj* x_50; obj* x_52; obj* x_53; obj* x_54; obj* x_57; 
x_47 = l_char_quote__core(x_45);
x_48 = l_char_has__repr___closed__1;
lean::inc(x_48);
x_50 = lean::string_append(x_48, x_47);
lean::dec(x_47);
x_52 = lean::string_append(x_50, x_48);
x_53 = lean::box(0);
x_54 = l_mjoin___rarg___closed__1;
lean::inc(x_53);
lean::inc(x_54);
x_57 = l_lean_parser_monad__parsec_error___at_lean_parser_string__lit_view_value___spec__3___rarg(x_52, x_54, x_53, x_53, x_0);
if (lean::obj_tag(x_57) == 0)
{
obj* x_58; obj* x_60; obj* x_62; 
x_58 = lean::cnstr_get(x_57, 0);
lean::inc(x_58);
x_60 = lean::cnstr_get(x_57, 1);
lean::inc(x_60);
x_62 = lean::cnstr_get(x_57, 2);
lean::inc(x_62);
if (lean::obj_tag(x_62) == 0)
{
lean::dec(x_58);
lean::dec(x_60);
lean::dec(x_62);
return x_57;
}
else
{
obj* x_68; obj* x_70; obj* x_72; obj* x_73; obj* x_74; 
lean::dec(x_57);
x_68 = lean::cnstr_get(x_62, 0);
lean::inc(x_68);
if (lean::is_shared(x_62)) {
 lean::dec(x_62);
 x_70 = lean::box(0);
} else {
 lean::cnstr_release(x_62, 0);
 x_70 = x_62;
}
lean::inc(x_54);
x_72 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_72, 0, x_54);
lean::closure_set(x_72, 1, x_68);
if (lean::is_scalar(x_70)) {
 x_73 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_73 = x_70;
}
lean::cnstr_set(x_73, 0, x_72);
x_74 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_74, 0, x_58);
lean::cnstr_set(x_74, 1, x_60);
lean::cnstr_set(x_74, 2, x_73);
return x_74;
}
}
else
{
obj* x_75; unsigned char x_77; 
x_75 = lean::cnstr_get(x_57, 0);
lean::inc(x_75);
x_77 = lean::cnstr_get_scalar<unsigned char>(x_57, sizeof(void*)*1);
if (x_77 == 0)
{
obj* x_79; obj* x_81; obj* x_83; obj* x_86; obj* x_87; obj* x_90; obj* x_91; obj* x_92; 
lean::dec(x_57);
x_79 = lean::cnstr_get(x_75, 0);
lean::inc(x_79);
x_81 = lean::cnstr_get(x_75, 1);
lean::inc(x_81);
x_83 = lean::cnstr_get(x_75, 2);
lean::inc(x_83);
lean::inc(x_54);
x_86 = lean::alloc_closure(reinterpret_cast<void*>(l_function_comp___rarg), 3, 2);
lean::closure_set(x_86, 0, x_54);
lean::closure_set(x_86, 1, x_83);
x_87 = lean::cnstr_get(x_75, 3);
lean::inc(x_87);
lean::dec(x_75);
x_90 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_90, 0, x_79);
lean::cnstr_set(x_90, 1, x_81);
lean::cnstr_set(x_90, 2, x_86);
lean::cnstr_set(x_90, 3, x_87);
x_91 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_91, 0, x_90);
lean::cnstr_set_scalar(x_91, sizeof(void*)*1, x_77);
x_92 = x_91;
return x_92;
}
else
{
lean::dec(x_75);
return x_57;
}
}
}
else
{
obj* x_94; obj* x_95; obj* x_96; obj* x_97; 
x_94 = lean::string_iterator_next(x_0);
x_95 = lean::box(0);
x_96 = lean::box_uint32(x_45);
x_97 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_97, 0, x_96);
lean::cnstr_set(x_97, 1, x_94);
lean::cnstr_set(x_97, 2, x_95);
return x_97;
}
}
}
}
obj* l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_view_value___spec__7(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; unsigned char x_3; obj* x_6; 
lean::inc(x_0);
x_6 = l_lean_parser_monad__parsec_digit___at_lean_parser_string__lit_view_value___spec__8(x_0);
if (lean::obj_tag(x_6) == 0)
{
obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_14; obj* x_15; unsigned char x_16; 
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
x_15 = lean::mk_nat_obj(55296u);
x_16 = lean::nat_dec_lt(x_14, x_15);
lean::dec(x_15);
if (x_16 == 0)
{
obj* x_18; unsigned char x_19; 
x_18 = lean::mk_nat_obj(57343u);
x_19 = lean::nat_dec_lt(x_18, x_14);
lean::dec(x_18);
if (x_19 == 0)
{
obj* x_22; obj* x_23; obj* x_26; obj* x_28; obj* x_29; 
lean::dec(x_14);
x_22 = lean::mk_nat_obj(0u);
x_23 = lean::nat_sub(x_7, x_22);
lean::dec(x_22);
lean::dec(x_7);
x_26 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_26);
if (lean::is_scalar(x_13)) {
 x_28 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_28 = x_13;
}
lean::cnstr_set(x_28, 0, x_23);
lean::cnstr_set(x_28, 1, x_9);
lean::cnstr_set(x_28, 2, x_26);
x_29 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_11, x_28);
if (lean::obj_tag(x_29) == 0)
{
obj* x_31; obj* x_33; 
lean::dec(x_0);
x_31 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__4___closed__1;
lean::inc(x_31);
x_33 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_29, x_31);
return x_33;
}
else
{
obj* x_34; unsigned char x_36; 
x_34 = lean::cnstr_get(x_29, 0);
lean::inc(x_34);
x_36 = lean::cnstr_get_scalar<unsigned char>(x_29, sizeof(void*)*1);
x_1 = x_29;
x_2 = x_34;
x_3 = x_36;
goto lbl_4;
}
}
else
{
obj* x_37; unsigned char x_38; 
x_37 = lean::mk_nat_obj(1114112u);
x_38 = lean::nat_dec_lt(x_14, x_37);
lean::dec(x_37);
if (x_38 == 0)
{
obj* x_41; obj* x_42; obj* x_45; obj* x_47; obj* x_48; 
lean::dec(x_14);
x_41 = lean::mk_nat_obj(0u);
x_42 = lean::nat_sub(x_7, x_41);
lean::dec(x_41);
lean::dec(x_7);
x_45 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_45);
if (lean::is_scalar(x_13)) {
 x_47 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_47 = x_13;
}
lean::cnstr_set(x_47, 0, x_42);
lean::cnstr_set(x_47, 1, x_9);
lean::cnstr_set(x_47, 2, x_45);
x_48 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_11, x_47);
if (lean::obj_tag(x_48) == 0)
{
obj* x_50; obj* x_52; 
lean::dec(x_0);
x_50 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__4___closed__1;
lean::inc(x_50);
x_52 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_48, x_50);
return x_52;
}
else
{
obj* x_53; unsigned char x_55; 
x_53 = lean::cnstr_get(x_48, 0);
lean::inc(x_53);
x_55 = lean::cnstr_get_scalar<unsigned char>(x_48, sizeof(void*)*1);
x_1 = x_48;
x_2 = x_53;
x_3 = x_55;
goto lbl_4;
}
}
else
{
obj* x_56; obj* x_59; obj* x_61; obj* x_62; 
x_56 = lean::nat_sub(x_7, x_14);
lean::dec(x_14);
lean::dec(x_7);
x_59 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_59);
if (lean::is_scalar(x_13)) {
 x_61 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_61 = x_13;
}
lean::cnstr_set(x_61, 0, x_56);
lean::cnstr_set(x_61, 1, x_9);
lean::cnstr_set(x_61, 2, x_59);
x_62 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_11, x_61);
if (lean::obj_tag(x_62) == 0)
{
obj* x_64; obj* x_66; 
lean::dec(x_0);
x_64 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__4___closed__1;
lean::inc(x_64);
x_66 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_62, x_64);
return x_66;
}
else
{
obj* x_67; unsigned char x_69; 
x_67 = lean::cnstr_get(x_62, 0);
lean::inc(x_67);
x_69 = lean::cnstr_get_scalar<unsigned char>(x_62, sizeof(void*)*1);
x_1 = x_62;
x_2 = x_67;
x_3 = x_69;
goto lbl_4;
}
}
}
}
else
{
obj* x_70; obj* x_73; obj* x_75; obj* x_76; 
x_70 = lean::nat_sub(x_7, x_14);
lean::dec(x_14);
lean::dec(x_7);
x_73 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_73);
if (lean::is_scalar(x_13)) {
 x_75 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_75 = x_13;
}
lean::cnstr_set(x_75, 0, x_70);
lean::cnstr_set(x_75, 1, x_9);
lean::cnstr_set(x_75, 2, x_73);
x_76 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_11, x_75);
if (lean::obj_tag(x_76) == 0)
{
obj* x_78; obj* x_80; 
lean::dec(x_0);
x_78 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__4___closed__1;
lean::inc(x_78);
x_80 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_76, x_78);
return x_80;
}
else
{
obj* x_81; unsigned char x_83; 
x_81 = lean::cnstr_get(x_76, 0);
lean::inc(x_81);
x_83 = lean::cnstr_get_scalar<unsigned char>(x_76, sizeof(void*)*1);
x_1 = x_76;
x_2 = x_81;
x_3 = x_83;
goto lbl_4;
}
}
}
else
{
obj* x_84; unsigned char x_86; obj* x_87; obj* x_89; obj* x_90; 
x_84 = lean::cnstr_get(x_6, 0);
lean::inc(x_84);
x_86 = lean::cnstr_get_scalar<unsigned char>(x_6, sizeof(void*)*1);
if (lean::is_shared(x_6)) {
 lean::dec(x_6);
 x_87 = lean::box(0);
} else {
 lean::cnstr_release(x_6, 0);
 x_87 = x_6;
}
lean::inc(x_84);
if (lean::is_scalar(x_87)) {
 x_89 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_89 = x_87;
}
lean::cnstr_set(x_89, 0, x_84);
lean::cnstr_set_scalar(x_89, sizeof(void*)*1, x_86);
x_90 = x_89;
x_1 = x_90;
x_2 = x_84;
x_3 = x_86;
goto lbl_4;
}
lbl_4:
{
obj* x_91; obj* x_92; unsigned char x_93; 
if (x_3 == 0)
{
obj* x_96; unsigned char x_98; 
lean::dec(x_1);
x_98 = lean::string_iterator_has_next(x_0);
if (x_98 == 0)
{
obj* x_99; obj* x_100; obj* x_101; obj* x_106; 
x_99 = lean::box(0);
x_100 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_101 = l_mjoin___rarg___closed__1;
lean::inc(x_0);
lean::inc(x_99);
lean::inc(x_101);
lean::inc(x_100);
x_106 = l_lean_parser_monad__parsec_error___at_lean_parser_string__lit_view_value___spec__3___rarg(x_100, x_101, x_99, x_99, x_0);
x_96 = x_106;
goto lbl_97;
}
else
{
unsigned x_107; obj* x_108; obj* x_110; obj* x_112; obj* x_113; unsigned char x_114; unsigned char x_115; 
x_107 = lean::string_iterator_curr(x_0);
x_112 = lean::mk_nat_obj(97u);
x_113 = lean::mk_nat_obj(55296u);
x_114 = lean::nat_dec_lt(x_112, x_113);
if (x_114 == 0)
{
obj* x_117; unsigned char x_118; 
x_117 = lean::mk_nat_obj(57343u);
x_118 = lean::nat_dec_lt(x_117, x_112);
lean::dec(x_117);
if (x_118 == 0)
{
obj* x_121; obj* x_122; unsigned char x_123; 
lean::dec(x_112);
x_121 = lean::mk_nat_obj(0u);
x_122 = lean::box_uint32(x_107);
x_123 = lean::nat_dec_le(x_121, x_122);
lean::dec(x_122);
lean::dec(x_121);
if (x_123 == 0)
{
obj* x_127; 
lean::dec(x_113);
x_127 = lean::box(0);
x_108 = x_127;
goto lbl_109;
}
else
{
unsigned char x_128; 
x_128 = 1;
x_115 = x_128;
goto lbl_116;
}
}
else
{
obj* x_129; unsigned char x_130; 
x_129 = lean::mk_nat_obj(1114112u);
x_130 = lean::nat_dec_lt(x_112, x_129);
lean::dec(x_129);
if (x_130 == 0)
{
obj* x_133; obj* x_134; unsigned char x_135; 
lean::dec(x_112);
x_133 = lean::mk_nat_obj(0u);
x_134 = lean::box_uint32(x_107);
x_135 = lean::nat_dec_le(x_133, x_134);
lean::dec(x_134);
lean::dec(x_133);
if (x_135 == 0)
{
obj* x_139; 
lean::dec(x_113);
x_139 = lean::box(0);
x_108 = x_139;
goto lbl_109;
}
else
{
unsigned char x_140; 
x_140 = 1;
x_115 = x_140;
goto lbl_116;
}
}
else
{
obj* x_141; unsigned char x_142; 
x_141 = lean::box_uint32(x_107);
x_142 = lean::nat_dec_le(x_112, x_141);
lean::dec(x_141);
lean::dec(x_112);
if (x_142 == 0)
{
obj* x_146; 
lean::dec(x_113);
x_146 = lean::box(0);
x_108 = x_146;
goto lbl_109;
}
else
{
unsigned char x_147; 
x_147 = 1;
x_115 = x_147;
goto lbl_116;
}
}
}
}
else
{
obj* x_148; unsigned char x_149; 
x_148 = lean::box_uint32(x_107);
x_149 = lean::nat_dec_le(x_112, x_148);
lean::dec(x_148);
lean::dec(x_112);
if (x_149 == 0)
{
obj* x_153; 
lean::dec(x_113);
x_153 = lean::box(0);
x_108 = x_153;
goto lbl_109;
}
else
{
unsigned char x_154; 
x_154 = 1;
x_115 = x_154;
goto lbl_116;
}
}
lbl_109:
{
obj* x_156; obj* x_157; obj* x_159; obj* x_161; obj* x_162; obj* x_163; obj* x_167; 
lean::dec(x_108);
x_156 = l_char_quote__core(x_107);
x_157 = l_char_has__repr___closed__1;
lean::inc(x_157);
x_159 = lean::string_append(x_157, x_156);
lean::dec(x_156);
x_161 = lean::string_append(x_159, x_157);
x_162 = lean::box(0);
x_163 = l_mjoin___rarg___closed__1;
lean::inc(x_0);
lean::inc(x_162);
lean::inc(x_163);
x_167 = l_lean_parser_monad__parsec_error___at_lean_parser_string__lit_view_value___spec__3___rarg(x_161, x_163, x_162, x_162, x_0);
x_96 = x_167;
goto lbl_97;
}
lbl_111:
{
obj* x_170; obj* x_171; obj* x_172; obj* x_173; 
lean::dec(x_110);
lean::inc(x_0);
x_170 = lean::string_iterator_next(x_0);
x_171 = lean::box(0);
x_172 = lean::box_uint32(x_107);
x_173 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_173, 0, x_172);
lean::cnstr_set(x_173, 1, x_170);
lean::cnstr_set(x_173, 2, x_171);
x_96 = x_173;
goto lbl_97;
}
lbl_116:
{
obj* x_174; unsigned char x_175; 
x_174 = lean::mk_nat_obj(102u);
x_175 = lean::nat_dec_lt(x_174, x_113);
lean::dec(x_113);
if (x_175 == 0)
{
obj* x_177; unsigned char x_178; 
x_177 = lean::mk_nat_obj(57343u);
x_178 = lean::nat_dec_lt(x_177, x_174);
lean::dec(x_177);
if (x_178 == 0)
{
obj* x_181; obj* x_182; unsigned char x_183; 
lean::dec(x_174);
x_181 = lean::mk_nat_obj(0u);
x_182 = lean::box_uint32(x_107);
x_183 = lean::nat_dec_le(x_182, x_181);
lean::dec(x_181);
lean::dec(x_182);
if (x_183 == 0)
{
obj* x_186; 
x_186 = lean::box(0);
x_108 = x_186;
goto lbl_109;
}
else
{
if (x_115 == 0)
{
obj* x_187; 
x_187 = lean::box(0);
x_108 = x_187;
goto lbl_109;
}
else
{
obj* x_188; 
x_188 = lean::box(0);
x_110 = x_188;
goto lbl_111;
}
}
}
else
{
obj* x_189; unsigned char x_190; 
x_189 = lean::mk_nat_obj(1114112u);
x_190 = lean::nat_dec_lt(x_174, x_189);
lean::dec(x_189);
if (x_190 == 0)
{
obj* x_193; obj* x_194; unsigned char x_195; 
lean::dec(x_174);
x_193 = lean::mk_nat_obj(0u);
x_194 = lean::box_uint32(x_107);
x_195 = lean::nat_dec_le(x_194, x_193);
lean::dec(x_193);
lean::dec(x_194);
if (x_195 == 0)
{
obj* x_198; 
x_198 = lean::box(0);
x_108 = x_198;
goto lbl_109;
}
else
{
if (x_115 == 0)
{
obj* x_199; 
x_199 = lean::box(0);
x_108 = x_199;
goto lbl_109;
}
else
{
obj* x_200; 
x_200 = lean::box(0);
x_110 = x_200;
goto lbl_111;
}
}
}
else
{
obj* x_201; unsigned char x_202; 
x_201 = lean::box_uint32(x_107);
x_202 = lean::nat_dec_le(x_201, x_174);
lean::dec(x_174);
lean::dec(x_201);
if (x_202 == 0)
{
obj* x_205; 
x_205 = lean::box(0);
x_108 = x_205;
goto lbl_109;
}
else
{
if (x_115 == 0)
{
obj* x_206; 
x_206 = lean::box(0);
x_108 = x_206;
goto lbl_109;
}
else
{
obj* x_207; 
x_207 = lean::box(0);
x_110 = x_207;
goto lbl_111;
}
}
}
}
}
else
{
obj* x_208; unsigned char x_209; 
x_208 = lean::box_uint32(x_107);
x_209 = lean::nat_dec_le(x_208, x_174);
lean::dec(x_174);
lean::dec(x_208);
if (x_209 == 0)
{
obj* x_212; 
x_212 = lean::box(0);
x_108 = x_212;
goto lbl_109;
}
else
{
if (x_115 == 0)
{
obj* x_213; 
x_213 = lean::box(0);
x_108 = x_213;
goto lbl_109;
}
else
{
obj* x_214; 
x_214 = lean::box(0);
x_110 = x_214;
goto lbl_111;
}
}
}
}
}
lbl_97:
{
obj* x_215; obj* x_217; 
x_215 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_215);
x_217 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_215, x_96);
if (lean::obj_tag(x_217) == 0)
{
obj* x_218; obj* x_220; obj* x_222; obj* x_224; obj* x_225; obj* x_226; unsigned char x_227; 
x_218 = lean::cnstr_get(x_217, 0);
lean::inc(x_218);
x_220 = lean::cnstr_get(x_217, 1);
lean::inc(x_220);
x_222 = lean::cnstr_get(x_217, 2);
lean::inc(x_222);
if (lean::is_shared(x_217)) {
 lean::dec(x_217);
 x_224 = lean::box(0);
} else {
 lean::cnstr_release(x_217, 0);
 lean::cnstr_release(x_217, 1);
 lean::cnstr_release(x_217, 2);
 x_224 = x_217;
}
x_225 = lean::mk_nat_obj(97u);
x_226 = lean::mk_nat_obj(55296u);
x_227 = lean::nat_dec_lt(x_225, x_226);
lean::dec(x_226);
if (x_227 == 0)
{
obj* x_229; unsigned char x_230; 
x_229 = lean::mk_nat_obj(57343u);
x_230 = lean::nat_dec_lt(x_229, x_225);
lean::dec(x_229);
if (x_230 == 0)
{
obj* x_233; obj* x_234; obj* x_237; obj* x_238; obj* x_242; obj* x_243; 
lean::dec(x_225);
x_233 = lean::mk_nat_obj(0u);
x_234 = lean::nat_sub(x_218, x_233);
lean::dec(x_233);
lean::dec(x_218);
x_237 = lean::mk_nat_obj(10u);
x_238 = lean::nat_add(x_237, x_234);
lean::dec(x_234);
lean::dec(x_237);
lean::inc(x_215);
if (lean::is_scalar(x_224)) {
 x_242 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_242 = x_224;
}
lean::cnstr_set(x_242, 0, x_238);
lean::cnstr_set(x_242, 1, x_220);
lean::cnstr_set(x_242, 2, x_215);
x_243 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_222, x_242);
if (lean::obj_tag(x_243) == 0)
{
obj* x_245; obj* x_246; obj* x_248; 
lean::dec(x_0);
x_245 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_2, x_243);
x_246 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__4___closed__1;
lean::inc(x_246);
x_248 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_245, x_246);
return x_248;
}
else
{
obj* x_249; unsigned char x_251; 
x_249 = lean::cnstr_get(x_243, 0);
lean::inc(x_249);
x_251 = lean::cnstr_get_scalar<unsigned char>(x_243, sizeof(void*)*1);
x_91 = x_243;
x_92 = x_249;
x_93 = x_251;
goto lbl_94;
}
}
else
{
obj* x_252; unsigned char x_253; 
x_252 = lean::mk_nat_obj(1114112u);
x_253 = lean::nat_dec_lt(x_225, x_252);
lean::dec(x_252);
if (x_253 == 0)
{
obj* x_256; obj* x_257; obj* x_260; obj* x_261; obj* x_265; obj* x_266; 
lean::dec(x_225);
x_256 = lean::mk_nat_obj(0u);
x_257 = lean::nat_sub(x_218, x_256);
lean::dec(x_256);
lean::dec(x_218);
x_260 = lean::mk_nat_obj(10u);
x_261 = lean::nat_add(x_260, x_257);
lean::dec(x_257);
lean::dec(x_260);
lean::inc(x_215);
if (lean::is_scalar(x_224)) {
 x_265 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_265 = x_224;
}
lean::cnstr_set(x_265, 0, x_261);
lean::cnstr_set(x_265, 1, x_220);
lean::cnstr_set(x_265, 2, x_215);
x_266 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_222, x_265);
if (lean::obj_tag(x_266) == 0)
{
obj* x_268; obj* x_269; obj* x_271; 
lean::dec(x_0);
x_268 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_2, x_266);
x_269 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__4___closed__1;
lean::inc(x_269);
x_271 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_268, x_269);
return x_271;
}
else
{
obj* x_272; unsigned char x_274; 
x_272 = lean::cnstr_get(x_266, 0);
lean::inc(x_272);
x_274 = lean::cnstr_get_scalar<unsigned char>(x_266, sizeof(void*)*1);
x_91 = x_266;
x_92 = x_272;
x_93 = x_274;
goto lbl_94;
}
}
else
{
obj* x_275; obj* x_278; obj* x_279; obj* x_283; obj* x_284; 
x_275 = lean::nat_sub(x_218, x_225);
lean::dec(x_225);
lean::dec(x_218);
x_278 = lean::mk_nat_obj(10u);
x_279 = lean::nat_add(x_278, x_275);
lean::dec(x_275);
lean::dec(x_278);
lean::inc(x_215);
if (lean::is_scalar(x_224)) {
 x_283 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_283 = x_224;
}
lean::cnstr_set(x_283, 0, x_279);
lean::cnstr_set(x_283, 1, x_220);
lean::cnstr_set(x_283, 2, x_215);
x_284 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_222, x_283);
if (lean::obj_tag(x_284) == 0)
{
obj* x_286; obj* x_287; obj* x_289; 
lean::dec(x_0);
x_286 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_2, x_284);
x_287 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__4___closed__1;
lean::inc(x_287);
x_289 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_286, x_287);
return x_289;
}
else
{
obj* x_290; unsigned char x_292; 
x_290 = lean::cnstr_get(x_284, 0);
lean::inc(x_290);
x_292 = lean::cnstr_get_scalar<unsigned char>(x_284, sizeof(void*)*1);
x_91 = x_284;
x_92 = x_290;
x_93 = x_292;
goto lbl_94;
}
}
}
}
else
{
obj* x_293; obj* x_296; obj* x_297; obj* x_301; obj* x_302; 
x_293 = lean::nat_sub(x_218, x_225);
lean::dec(x_225);
lean::dec(x_218);
x_296 = lean::mk_nat_obj(10u);
x_297 = lean::nat_add(x_296, x_293);
lean::dec(x_293);
lean::dec(x_296);
lean::inc(x_215);
if (lean::is_scalar(x_224)) {
 x_301 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_301 = x_224;
}
lean::cnstr_set(x_301, 0, x_297);
lean::cnstr_set(x_301, 1, x_220);
lean::cnstr_set(x_301, 2, x_215);
x_302 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_222, x_301);
if (lean::obj_tag(x_302) == 0)
{
obj* x_304; obj* x_305; obj* x_307; 
lean::dec(x_0);
x_304 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_2, x_302);
x_305 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__4___closed__1;
lean::inc(x_305);
x_307 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_304, x_305);
return x_307;
}
else
{
obj* x_308; unsigned char x_310; 
x_308 = lean::cnstr_get(x_302, 0);
lean::inc(x_308);
x_310 = lean::cnstr_get_scalar<unsigned char>(x_302, sizeof(void*)*1);
x_91 = x_302;
x_92 = x_308;
x_93 = x_310;
goto lbl_94;
}
}
}
else
{
obj* x_311; unsigned char x_313; obj* x_314; obj* x_316; obj* x_317; 
x_311 = lean::cnstr_get(x_217, 0);
lean::inc(x_311);
x_313 = lean::cnstr_get_scalar<unsigned char>(x_217, sizeof(void*)*1);
if (lean::is_shared(x_217)) {
 lean::dec(x_217);
 x_314 = lean::box(0);
} else {
 lean::cnstr_release(x_217, 0);
 x_314 = x_217;
}
lean::inc(x_311);
if (lean::is_scalar(x_314)) {
 x_316 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_316 = x_314;
}
lean::cnstr_set(x_316, 0, x_311);
lean::cnstr_set_scalar(x_316, sizeof(void*)*1, x_313);
x_317 = x_316;
x_91 = x_317;
x_92 = x_311;
x_93 = x_313;
goto lbl_94;
}
}
}
else
{
obj* x_320; obj* x_322; 
lean::dec(x_0);
lean::dec(x_2);
x_320 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__4___closed__1;
lean::inc(x_320);
x_322 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_1, x_320);
return x_322;
}
lbl_94:
{
if (x_93 == 0)
{
obj* x_324; unsigned char x_326; 
lean::dec(x_91);
x_326 = lean::string_iterator_has_next(x_0);
if (x_326 == 0)
{
obj* x_327; obj* x_328; obj* x_329; obj* x_333; 
x_327 = lean::box(0);
x_328 = l_lean_parser_monad__parsec_eoi__error___rarg___closed__1;
x_329 = l_mjoin___rarg___closed__1;
lean::inc(x_327);
lean::inc(x_329);
lean::inc(x_328);
x_333 = l_lean_parser_monad__parsec_error___at_lean_parser_string__lit_view_value___spec__3___rarg(x_328, x_329, x_327, x_327, x_0);
x_324 = x_333;
goto lbl_325;
}
else
{
unsigned x_334; obj* x_335; obj* x_337; obj* x_339; obj* x_340; unsigned char x_341; unsigned char x_342; 
x_334 = lean::string_iterator_curr(x_0);
x_339 = lean::mk_nat_obj(65u);
x_340 = lean::mk_nat_obj(55296u);
x_341 = lean::nat_dec_lt(x_339, x_340);
if (x_341 == 0)
{
obj* x_344; unsigned char x_345; 
x_344 = lean::mk_nat_obj(57343u);
x_345 = lean::nat_dec_lt(x_344, x_339);
lean::dec(x_344);
if (x_345 == 0)
{
obj* x_348; obj* x_349; unsigned char x_350; 
lean::dec(x_339);
x_348 = lean::mk_nat_obj(0u);
x_349 = lean::box_uint32(x_334);
x_350 = lean::nat_dec_le(x_348, x_349);
lean::dec(x_349);
lean::dec(x_348);
if (x_350 == 0)
{
obj* x_354; 
lean::dec(x_340);
x_354 = lean::box(0);
x_335 = x_354;
goto lbl_336;
}
else
{
unsigned char x_355; 
x_355 = 1;
x_342 = x_355;
goto lbl_343;
}
}
else
{
obj* x_356; unsigned char x_357; 
x_356 = lean::mk_nat_obj(1114112u);
x_357 = lean::nat_dec_lt(x_339, x_356);
lean::dec(x_356);
if (x_357 == 0)
{
obj* x_360; obj* x_361; unsigned char x_362; 
lean::dec(x_339);
x_360 = lean::mk_nat_obj(0u);
x_361 = lean::box_uint32(x_334);
x_362 = lean::nat_dec_le(x_360, x_361);
lean::dec(x_361);
lean::dec(x_360);
if (x_362 == 0)
{
obj* x_366; 
lean::dec(x_340);
x_366 = lean::box(0);
x_335 = x_366;
goto lbl_336;
}
else
{
unsigned char x_367; 
x_367 = 1;
x_342 = x_367;
goto lbl_343;
}
}
else
{
obj* x_368; unsigned char x_369; 
x_368 = lean::box_uint32(x_334);
x_369 = lean::nat_dec_le(x_339, x_368);
lean::dec(x_368);
lean::dec(x_339);
if (x_369 == 0)
{
obj* x_373; 
lean::dec(x_340);
x_373 = lean::box(0);
x_335 = x_373;
goto lbl_336;
}
else
{
unsigned char x_374; 
x_374 = 1;
x_342 = x_374;
goto lbl_343;
}
}
}
}
else
{
obj* x_375; unsigned char x_376; 
x_375 = lean::box_uint32(x_334);
x_376 = lean::nat_dec_le(x_339, x_375);
lean::dec(x_375);
lean::dec(x_339);
if (x_376 == 0)
{
obj* x_380; 
lean::dec(x_340);
x_380 = lean::box(0);
x_335 = x_380;
goto lbl_336;
}
else
{
unsigned char x_381; 
x_381 = 1;
x_342 = x_381;
goto lbl_343;
}
}
lbl_336:
{
obj* x_383; obj* x_384; obj* x_386; obj* x_388; obj* x_389; obj* x_390; obj* x_393; 
lean::dec(x_335);
x_383 = l_char_quote__core(x_334);
x_384 = l_char_has__repr___closed__1;
lean::inc(x_384);
x_386 = lean::string_append(x_384, x_383);
lean::dec(x_383);
x_388 = lean::string_append(x_386, x_384);
x_389 = lean::box(0);
x_390 = l_mjoin___rarg___closed__1;
lean::inc(x_389);
lean::inc(x_390);
x_393 = l_lean_parser_monad__parsec_error___at_lean_parser_string__lit_view_value___spec__3___rarg(x_388, x_390, x_389, x_389, x_0);
x_324 = x_393;
goto lbl_325;
}
lbl_338:
{
obj* x_395; obj* x_396; obj* x_397; obj* x_398; 
lean::dec(x_337);
x_395 = lean::string_iterator_next(x_0);
x_396 = lean::box(0);
x_397 = lean::box_uint32(x_334);
x_398 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_398, 0, x_397);
lean::cnstr_set(x_398, 1, x_395);
lean::cnstr_set(x_398, 2, x_396);
x_324 = x_398;
goto lbl_325;
}
lbl_343:
{
obj* x_399; unsigned char x_400; 
x_399 = lean::mk_nat_obj(70u);
x_400 = lean::nat_dec_lt(x_399, x_340);
lean::dec(x_340);
if (x_400 == 0)
{
obj* x_402; unsigned char x_403; 
x_402 = lean::mk_nat_obj(57343u);
x_403 = lean::nat_dec_lt(x_402, x_399);
lean::dec(x_402);
if (x_403 == 0)
{
obj* x_406; obj* x_407; unsigned char x_408; 
lean::dec(x_399);
x_406 = lean::mk_nat_obj(0u);
x_407 = lean::box_uint32(x_334);
x_408 = lean::nat_dec_le(x_407, x_406);
lean::dec(x_406);
lean::dec(x_407);
if (x_408 == 0)
{
obj* x_411; 
x_411 = lean::box(0);
x_335 = x_411;
goto lbl_336;
}
else
{
if (x_342 == 0)
{
obj* x_412; 
x_412 = lean::box(0);
x_335 = x_412;
goto lbl_336;
}
else
{
obj* x_413; 
x_413 = lean::box(0);
x_337 = x_413;
goto lbl_338;
}
}
}
else
{
obj* x_414; unsigned char x_415; 
x_414 = lean::mk_nat_obj(1114112u);
x_415 = lean::nat_dec_lt(x_399, x_414);
lean::dec(x_414);
if (x_415 == 0)
{
obj* x_418; obj* x_419; unsigned char x_420; 
lean::dec(x_399);
x_418 = lean::mk_nat_obj(0u);
x_419 = lean::box_uint32(x_334);
x_420 = lean::nat_dec_le(x_419, x_418);
lean::dec(x_418);
lean::dec(x_419);
if (x_420 == 0)
{
obj* x_423; 
x_423 = lean::box(0);
x_335 = x_423;
goto lbl_336;
}
else
{
if (x_342 == 0)
{
obj* x_424; 
x_424 = lean::box(0);
x_335 = x_424;
goto lbl_336;
}
else
{
obj* x_425; 
x_425 = lean::box(0);
x_337 = x_425;
goto lbl_338;
}
}
}
else
{
obj* x_426; unsigned char x_427; 
x_426 = lean::box_uint32(x_334);
x_427 = lean::nat_dec_le(x_426, x_399);
lean::dec(x_399);
lean::dec(x_426);
if (x_427 == 0)
{
obj* x_430; 
x_430 = lean::box(0);
x_335 = x_430;
goto lbl_336;
}
else
{
if (x_342 == 0)
{
obj* x_431; 
x_431 = lean::box(0);
x_335 = x_431;
goto lbl_336;
}
else
{
obj* x_432; 
x_432 = lean::box(0);
x_337 = x_432;
goto lbl_338;
}
}
}
}
}
else
{
obj* x_433; unsigned char x_434; 
x_433 = lean::box_uint32(x_334);
x_434 = lean::nat_dec_le(x_433, x_399);
lean::dec(x_399);
lean::dec(x_433);
if (x_434 == 0)
{
obj* x_437; 
x_437 = lean::box(0);
x_335 = x_437;
goto lbl_336;
}
else
{
if (x_342 == 0)
{
obj* x_438; 
x_438 = lean::box(0);
x_335 = x_438;
goto lbl_336;
}
else
{
obj* x_439; 
x_439 = lean::box(0);
x_337 = x_439;
goto lbl_338;
}
}
}
}
}
lbl_325:
{
obj* x_440; obj* x_442; 
x_440 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_440);
x_442 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_440, x_324);
if (lean::obj_tag(x_442) == 0)
{
obj* x_443; obj* x_445; obj* x_447; obj* x_449; obj* x_450; obj* x_451; unsigned char x_452; 
x_443 = lean::cnstr_get(x_442, 0);
lean::inc(x_443);
x_445 = lean::cnstr_get(x_442, 1);
lean::inc(x_445);
x_447 = lean::cnstr_get(x_442, 2);
lean::inc(x_447);
if (lean::is_shared(x_442)) {
 lean::dec(x_442);
 x_449 = lean::box(0);
} else {
 lean::cnstr_release(x_442, 0);
 lean::cnstr_release(x_442, 1);
 lean::cnstr_release(x_442, 2);
 x_449 = x_442;
}
x_450 = lean::mk_nat_obj(65u);
x_451 = lean::mk_nat_obj(55296u);
x_452 = lean::nat_dec_lt(x_450, x_451);
lean::dec(x_451);
if (x_452 == 0)
{
obj* x_454; unsigned char x_455; 
x_454 = lean::mk_nat_obj(57343u);
x_455 = lean::nat_dec_lt(x_454, x_450);
lean::dec(x_454);
if (x_455 == 0)
{
obj* x_458; obj* x_459; obj* x_462; obj* x_463; obj* x_467; obj* x_468; obj* x_469; obj* x_470; obj* x_471; obj* x_473; 
lean::dec(x_450);
x_458 = lean::mk_nat_obj(0u);
x_459 = lean::nat_sub(x_443, x_458);
lean::dec(x_458);
lean::dec(x_443);
x_462 = lean::mk_nat_obj(10u);
x_463 = lean::nat_add(x_462, x_459);
lean::dec(x_459);
lean::dec(x_462);
lean::inc(x_440);
if (lean::is_scalar(x_449)) {
 x_467 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_467 = x_449;
}
lean::cnstr_set(x_467, 0, x_463);
lean::cnstr_set(x_467, 1, x_445);
lean::cnstr_set(x_467, 2, x_440);
x_468 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_447, x_467);
x_469 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_92, x_468);
x_470 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_2, x_469);
x_471 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__4___closed__1;
lean::inc(x_471);
x_473 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_470, x_471);
return x_473;
}
else
{
obj* x_474; unsigned char x_475; 
x_474 = lean::mk_nat_obj(1114112u);
x_475 = lean::nat_dec_lt(x_450, x_474);
lean::dec(x_474);
if (x_475 == 0)
{
obj* x_478; obj* x_479; obj* x_482; obj* x_483; obj* x_487; obj* x_488; obj* x_489; obj* x_490; obj* x_491; obj* x_493; 
lean::dec(x_450);
x_478 = lean::mk_nat_obj(0u);
x_479 = lean::nat_sub(x_443, x_478);
lean::dec(x_478);
lean::dec(x_443);
x_482 = lean::mk_nat_obj(10u);
x_483 = lean::nat_add(x_482, x_479);
lean::dec(x_479);
lean::dec(x_482);
lean::inc(x_440);
if (lean::is_scalar(x_449)) {
 x_487 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_487 = x_449;
}
lean::cnstr_set(x_487, 0, x_483);
lean::cnstr_set(x_487, 1, x_445);
lean::cnstr_set(x_487, 2, x_440);
x_488 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_447, x_487);
x_489 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_92, x_488);
x_490 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_2, x_489);
x_491 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__4___closed__1;
lean::inc(x_491);
x_493 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_490, x_491);
return x_493;
}
else
{
obj* x_494; obj* x_497; obj* x_498; obj* x_502; obj* x_503; obj* x_504; obj* x_505; obj* x_506; obj* x_508; 
x_494 = lean::nat_sub(x_443, x_450);
lean::dec(x_450);
lean::dec(x_443);
x_497 = lean::mk_nat_obj(10u);
x_498 = lean::nat_add(x_497, x_494);
lean::dec(x_494);
lean::dec(x_497);
lean::inc(x_440);
if (lean::is_scalar(x_449)) {
 x_502 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_502 = x_449;
}
lean::cnstr_set(x_502, 0, x_498);
lean::cnstr_set(x_502, 1, x_445);
lean::cnstr_set(x_502, 2, x_440);
x_503 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_447, x_502);
x_504 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_92, x_503);
x_505 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_2, x_504);
x_506 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__4___closed__1;
lean::inc(x_506);
x_508 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_505, x_506);
return x_508;
}
}
}
else
{
obj* x_509; obj* x_512; obj* x_513; obj* x_517; obj* x_518; obj* x_519; obj* x_520; obj* x_521; obj* x_523; 
x_509 = lean::nat_sub(x_443, x_450);
lean::dec(x_450);
lean::dec(x_443);
x_512 = lean::mk_nat_obj(10u);
x_513 = lean::nat_add(x_512, x_509);
lean::dec(x_509);
lean::dec(x_512);
lean::inc(x_440);
if (lean::is_scalar(x_449)) {
 x_517 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_517 = x_449;
}
lean::cnstr_set(x_517, 0, x_513);
lean::cnstr_set(x_517, 1, x_445);
lean::cnstr_set(x_517, 2, x_440);
x_518 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_447, x_517);
x_519 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_92, x_518);
x_520 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_2, x_519);
x_521 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__4___closed__1;
lean::inc(x_521);
x_523 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_520, x_521);
return x_523;
}
}
else
{
obj* x_524; unsigned char x_526; obj* x_527; obj* x_528; obj* x_529; obj* x_530; obj* x_531; obj* x_532; obj* x_534; 
x_524 = lean::cnstr_get(x_442, 0);
lean::inc(x_524);
x_526 = lean::cnstr_get_scalar<unsigned char>(x_442, sizeof(void*)*1);
if (lean::is_shared(x_442)) {
 lean::dec(x_442);
 x_527 = lean::box(0);
} else {
 lean::cnstr_release(x_442, 0);
 x_527 = x_442;
}
if (lean::is_scalar(x_527)) {
 x_528 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_528 = x_527;
}
lean::cnstr_set(x_528, 0, x_524);
lean::cnstr_set_scalar(x_528, sizeof(void*)*1, x_526);
x_529 = x_528;
x_530 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_92, x_529);
x_531 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_2, x_530);
x_532 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__4___closed__1;
lean::inc(x_532);
x_534 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_531, x_532);
return x_534;
}
}
}
else
{
obj* x_537; obj* x_538; obj* x_540; 
lean::dec(x_0);
lean::dec(x_92);
x_537 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_2, x_91);
x_538 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__4___closed__1;
lean::inc(x_538);
x_540 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_537, x_538);
return x_540;
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
obj* x_3; obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_14; obj* x_16; obj* x_18; obj* x_20; obj* x_22; obj* x_24; obj* x_26; obj* x_27; unsigned char x_28; unsigned x_30; 
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
x_26 = lean::mk_nat_obj(92u);
x_27 = lean::mk_nat_obj(55296u);
x_28 = lean::nat_dec_lt(x_26, x_27);
lean::dec(x_27);
if (x_28 == 0)
{
obj* x_32; unsigned char x_33; 
x_32 = lean::mk_nat_obj(57343u);
x_33 = lean::nat_dec_lt(x_32, x_26);
lean::dec(x_32);
if (x_33 == 0)
{
obj* x_36; unsigned x_37; 
lean::dec(x_26);
x_36 = lean::mk_nat_obj(0u);
x_37 = lean::unbox_uint32(x_36);
lean::dec(x_36);
x_30 = x_37;
goto lbl_31;
}
else
{
obj* x_39; unsigned char x_40; 
x_39 = lean::mk_nat_obj(1114112u);
x_40 = lean::nat_dec_lt(x_26, x_39);
lean::dec(x_39);
if (x_40 == 0)
{
obj* x_43; unsigned x_44; 
lean::dec(x_26);
x_43 = lean::mk_nat_obj(0u);
x_44 = lean::unbox_uint32(x_43);
lean::dec(x_43);
x_30 = x_44;
goto lbl_31;
}
else
{
unsigned x_46; 
x_46 = lean::unbox_uint32(x_26);
lean::dec(x_26);
x_30 = x_46;
goto lbl_31;
}
}
}
else
{
unsigned x_48; 
x_48 = lean::unbox_uint32(x_26);
lean::dec(x_26);
x_30 = x_48;
goto lbl_31;
}
lbl_11:
{
obj* x_51; 
lean::dec(x_10);
x_51 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_view_value___spec__7(x_5);
if (lean::obj_tag(x_51) == 0)
{
obj* x_52; obj* x_54; obj* x_56; obj* x_59; 
x_52 = lean::cnstr_get(x_51, 0);
lean::inc(x_52);
x_54 = lean::cnstr_get(x_51, 1);
lean::inc(x_54);
x_56 = lean::cnstr_get(x_51, 2);
lean::inc(x_56);
lean::dec(x_51);
x_59 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_view_value___spec__7(x_54);
if (lean::obj_tag(x_59) == 0)
{
obj* x_60; obj* x_62; obj* x_64; obj* x_67; 
x_60 = lean::cnstr_get(x_59, 0);
lean::inc(x_60);
x_62 = lean::cnstr_get(x_59, 1);
lean::inc(x_62);
x_64 = lean::cnstr_get(x_59, 2);
lean::inc(x_64);
lean::dec(x_59);
x_67 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_view_value___spec__7(x_62);
if (lean::obj_tag(x_67) == 0)
{
obj* x_68; obj* x_70; obj* x_72; obj* x_75; 
x_68 = lean::cnstr_get(x_67, 0);
lean::inc(x_68);
x_70 = lean::cnstr_get(x_67, 1);
lean::inc(x_70);
x_72 = lean::cnstr_get(x_67, 2);
lean::inc(x_72);
lean::dec(x_67);
x_75 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_view_value___spec__7(x_70);
if (lean::obj_tag(x_75) == 0)
{
obj* x_76; obj* x_78; obj* x_80; obj* x_83; obj* x_84; obj* x_86; obj* x_89; obj* x_91; obj* x_94; obj* x_97; obj* x_100; unsigned char x_101; 
x_76 = lean::cnstr_get(x_75, 0);
lean::inc(x_76);
x_78 = lean::cnstr_get(x_75, 1);
lean::inc(x_78);
x_80 = lean::cnstr_get(x_75, 2);
lean::inc(x_80);
lean::dec(x_75);
x_83 = lean::mk_nat_obj(16u);
x_84 = lean::nat_mul(x_83, x_52);
lean::dec(x_52);
x_86 = lean::nat_add(x_84, x_60);
lean::dec(x_60);
lean::dec(x_84);
x_89 = lean::nat_mul(x_83, x_86);
lean::dec(x_86);
x_91 = lean::nat_add(x_89, x_68);
lean::dec(x_68);
lean::dec(x_89);
x_94 = lean::nat_mul(x_83, x_91);
lean::dec(x_91);
lean::dec(x_83);
x_97 = lean::nat_add(x_94, x_76);
lean::dec(x_76);
lean::dec(x_94);
x_100 = lean::mk_nat_obj(55296u);
x_101 = lean::nat_dec_lt(x_97, x_100);
lean::dec(x_100);
if (x_101 == 0)
{
obj* x_103; unsigned char x_104; 
x_103 = lean::mk_nat_obj(57343u);
x_104 = lean::nat_dec_lt(x_103, x_97);
lean::dec(x_103);
if (x_104 == 0)
{
obj* x_107; obj* x_108; obj* x_110; obj* x_111; obj* x_112; obj* x_113; obj* x_114; obj* x_115; obj* x_117; 
lean::dec(x_97);
x_107 = lean::mk_nat_obj(0u);
x_108 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_108);
if (lean::is_scalar(x_9)) {
 x_110 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_110 = x_9;
}
lean::cnstr_set(x_110, 0, x_107);
lean::cnstr_set(x_110, 1, x_78);
lean::cnstr_set(x_110, 2, x_108);
x_111 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_80, x_110);
x_112 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_72, x_111);
x_113 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_64, x_112);
x_114 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_56, x_113);
x_115 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_114);
lean::inc(x_108);
x_117 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_108, x_115);
return x_117;
}
else
{
obj* x_118; unsigned char x_119; 
x_118 = lean::mk_nat_obj(1114112u);
x_119 = lean::nat_dec_lt(x_97, x_118);
lean::dec(x_118);
if (x_119 == 0)
{
obj* x_122; obj* x_123; obj* x_125; obj* x_126; obj* x_127; obj* x_128; obj* x_129; obj* x_130; obj* x_132; 
lean::dec(x_97);
x_122 = lean::mk_nat_obj(0u);
x_123 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_123);
if (lean::is_scalar(x_9)) {
 x_125 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_125 = x_9;
}
lean::cnstr_set(x_125, 0, x_122);
lean::cnstr_set(x_125, 1, x_78);
lean::cnstr_set(x_125, 2, x_123);
x_126 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_80, x_125);
x_127 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_72, x_126);
x_128 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_64, x_127);
x_129 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_56, x_128);
x_130 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_129);
lean::inc(x_123);
x_132 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_123, x_130);
return x_132;
}
else
{
obj* x_133; obj* x_135; obj* x_136; obj* x_137; obj* x_138; obj* x_139; obj* x_140; obj* x_142; 
x_133 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_133);
if (lean::is_scalar(x_9)) {
 x_135 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_135 = x_9;
}
lean::cnstr_set(x_135, 0, x_97);
lean::cnstr_set(x_135, 1, x_78);
lean::cnstr_set(x_135, 2, x_133);
x_136 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_80, x_135);
x_137 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_72, x_136);
x_138 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_64, x_137);
x_139 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_56, x_138);
x_140 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_139);
lean::inc(x_133);
x_142 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_133, x_140);
return x_142;
}
}
}
else
{
obj* x_143; obj* x_145; obj* x_146; obj* x_147; obj* x_148; obj* x_149; obj* x_150; obj* x_152; 
x_143 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_143);
if (lean::is_scalar(x_9)) {
 x_145 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_145 = x_9;
}
lean::cnstr_set(x_145, 0, x_97);
lean::cnstr_set(x_145, 1, x_78);
lean::cnstr_set(x_145, 2, x_143);
x_146 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_80, x_145);
x_147 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_72, x_146);
x_148 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_64, x_147);
x_149 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_56, x_148);
x_150 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_149);
lean::inc(x_143);
x_152 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_143, x_150);
return x_152;
}
}
else
{
obj* x_157; unsigned char x_159; obj* x_160; obj* x_161; obj* x_162; obj* x_163; obj* x_164; obj* x_165; obj* x_166; obj* x_167; obj* x_169; 
lean::dec(x_60);
lean::dec(x_52);
lean::dec(x_68);
lean::dec(x_9);
x_157 = lean::cnstr_get(x_75, 0);
lean::inc(x_157);
x_159 = lean::cnstr_get_scalar<unsigned char>(x_75, sizeof(void*)*1);
if (lean::is_shared(x_75)) {
 lean::dec(x_75);
 x_160 = lean::box(0);
} else {
 lean::cnstr_release(x_75, 0);
 x_160 = x_75;
}
if (lean::is_scalar(x_160)) {
 x_161 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_161 = x_160;
}
lean::cnstr_set(x_161, 0, x_157);
lean::cnstr_set_scalar(x_161, sizeof(void*)*1, x_159);
x_162 = x_161;
x_163 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_72, x_162);
x_164 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_64, x_163);
x_165 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_56, x_164);
x_166 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_165);
x_167 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_167);
x_169 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_167, x_166);
return x_169;
}
}
else
{
obj* x_173; unsigned char x_175; obj* x_176; obj* x_177; obj* x_178; obj* x_179; obj* x_180; obj* x_181; obj* x_182; obj* x_184; 
lean::dec(x_60);
lean::dec(x_52);
lean::dec(x_9);
x_173 = lean::cnstr_get(x_67, 0);
lean::inc(x_173);
x_175 = lean::cnstr_get_scalar<unsigned char>(x_67, sizeof(void*)*1);
if (lean::is_shared(x_67)) {
 lean::dec(x_67);
 x_176 = lean::box(0);
} else {
 lean::cnstr_release(x_67, 0);
 x_176 = x_67;
}
if (lean::is_scalar(x_176)) {
 x_177 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_177 = x_176;
}
lean::cnstr_set(x_177, 0, x_173);
lean::cnstr_set_scalar(x_177, sizeof(void*)*1, x_175);
x_178 = x_177;
x_179 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_64, x_178);
x_180 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_56, x_179);
x_181 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_180);
x_182 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_182);
x_184 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_182, x_181);
return x_184;
}
}
else
{
obj* x_187; unsigned char x_189; obj* x_190; obj* x_191; obj* x_192; obj* x_193; obj* x_194; obj* x_195; obj* x_197; 
lean::dec(x_52);
lean::dec(x_9);
x_187 = lean::cnstr_get(x_59, 0);
lean::inc(x_187);
x_189 = lean::cnstr_get_scalar<unsigned char>(x_59, sizeof(void*)*1);
if (lean::is_shared(x_59)) {
 lean::dec(x_59);
 x_190 = lean::box(0);
} else {
 lean::cnstr_release(x_59, 0);
 x_190 = x_59;
}
if (lean::is_scalar(x_190)) {
 x_191 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_191 = x_190;
}
lean::cnstr_set(x_191, 0, x_187);
lean::cnstr_set_scalar(x_191, sizeof(void*)*1, x_189);
x_192 = x_191;
x_193 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_56, x_192);
x_194 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_193);
x_195 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_195);
x_197 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_195, x_194);
return x_197;
}
}
else
{
obj* x_199; unsigned char x_201; obj* x_202; obj* x_203; obj* x_204; obj* x_205; obj* x_206; obj* x_208; 
lean::dec(x_9);
x_199 = lean::cnstr_get(x_51, 0);
lean::inc(x_199);
x_201 = lean::cnstr_get_scalar<unsigned char>(x_51, sizeof(void*)*1);
if (lean::is_shared(x_51)) {
 lean::dec(x_51);
 x_202 = lean::box(0);
} else {
 lean::cnstr_release(x_51, 0);
 x_202 = x_51;
}
if (lean::is_scalar(x_202)) {
 x_203 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_203 = x_202;
}
lean::cnstr_set(x_203, 0, x_199);
lean::cnstr_set_scalar(x_203, sizeof(void*)*1, x_201);
x_204 = x_203;
x_205 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_204);
x_206 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_206);
x_208 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_206, x_205);
return x_208;
}
}
lbl_13:
{
obj* x_210; obj* x_211; unsigned char x_212; 
lean::dec(x_12);
x_210 = lean::mk_nat_obj(117u);
x_211 = lean::mk_nat_obj(55296u);
x_212 = lean::nat_dec_lt(x_210, x_211);
lean::dec(x_211);
if (x_212 == 0)
{
obj* x_214; unsigned char x_215; 
x_214 = lean::mk_nat_obj(57343u);
x_215 = lean::nat_dec_lt(x_214, x_210);
lean::dec(x_214);
if (x_215 == 0)
{
obj* x_218; unsigned char x_219; 
lean::dec(x_210);
x_218 = lean::mk_nat_obj(0u);
x_219 = lean::nat_dec_eq(x_3, x_218);
lean::dec(x_218);
lean::dec(x_3);
if (x_219 == 0)
{
obj* x_223; obj* x_225; obj* x_226; obj* x_227; obj* x_229; 
lean::dec(x_9);
x_223 = l_lean_parser_parse__quoted__char___rarg___lambda__7___closed__1;
lean::inc(x_223);
x_225 = l_lean_parser_monad__parsec_unexpected__at___at_lean_parser_string__lit_view_value___spec__9___rarg(x_223, x_0, x_5);
x_226 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_225);
x_227 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_227);
x_229 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_227, x_226);
return x_229;
}
else
{
obj* x_231; 
lean::dec(x_0);
x_231 = lean::box(0);
x_10 = x_231;
goto lbl_11;
}
}
else
{
obj* x_232; unsigned char x_233; 
x_232 = lean::mk_nat_obj(1114112u);
x_233 = lean::nat_dec_lt(x_210, x_232);
lean::dec(x_232);
if (x_233 == 0)
{
obj* x_236; unsigned char x_237; 
lean::dec(x_210);
x_236 = lean::mk_nat_obj(0u);
x_237 = lean::nat_dec_eq(x_3, x_236);
lean::dec(x_236);
lean::dec(x_3);
if (x_237 == 0)
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
else
{
unsigned char x_250; 
x_250 = lean::nat_dec_eq(x_3, x_210);
lean::dec(x_210);
lean::dec(x_3);
if (x_250 == 0)
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
}
else
{
unsigned char x_263; 
x_263 = lean::nat_dec_eq(x_3, x_210);
lean::dec(x_210);
lean::dec(x_3);
if (x_263 == 0)
{
obj* x_267; obj* x_269; obj* x_270; obj* x_271; obj* x_273; 
lean::dec(x_9);
x_267 = l_lean_parser_parse__quoted__char___rarg___lambda__7___closed__1;
lean::inc(x_267);
x_269 = l_lean_parser_monad__parsec_unexpected__at___at_lean_parser_string__lit_view_value___spec__9___rarg(x_267, x_0, x_5);
x_270 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_269);
x_271 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_271);
x_273 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_271, x_270);
return x_273;
}
else
{
obj* x_275; 
lean::dec(x_0);
x_275 = lean::box(0);
x_10 = x_275;
goto lbl_11;
}
}
}
lbl_15:
{
obj* x_277; 
lean::dec(x_14);
x_277 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_view_value___spec__7(x_5);
if (lean::obj_tag(x_277) == 0)
{
obj* x_278; obj* x_280; obj* x_282; obj* x_284; obj* x_285; 
x_278 = lean::cnstr_get(x_277, 0);
lean::inc(x_278);
x_280 = lean::cnstr_get(x_277, 1);
lean::inc(x_280);
x_282 = lean::cnstr_get(x_277, 2);
lean::inc(x_282);
if (lean::is_shared(x_277)) {
 lean::dec(x_277);
 x_284 = lean::box(0);
} else {
 lean::cnstr_release(x_277, 0);
 lean::cnstr_release(x_277, 1);
 lean::cnstr_release(x_277, 2);
 x_284 = x_277;
}
x_285 = l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_view_value___spec__7(x_280);
if (lean::obj_tag(x_285) == 0)
{
obj* x_286; obj* x_288; obj* x_290; obj* x_293; obj* x_294; obj* x_297; obj* x_300; unsigned char x_301; 
x_286 = lean::cnstr_get(x_285, 0);
lean::inc(x_286);
x_288 = lean::cnstr_get(x_285, 1);
lean::inc(x_288);
x_290 = lean::cnstr_get(x_285, 2);
lean::inc(x_290);
lean::dec(x_285);
x_293 = lean::mk_nat_obj(16u);
x_294 = lean::nat_mul(x_293, x_278);
lean::dec(x_278);
lean::dec(x_293);
x_297 = lean::nat_add(x_294, x_286);
lean::dec(x_286);
lean::dec(x_294);
x_300 = lean::mk_nat_obj(55296u);
x_301 = lean::nat_dec_lt(x_297, x_300);
lean::dec(x_300);
if (x_301 == 0)
{
obj* x_303; unsigned char x_304; 
x_303 = lean::mk_nat_obj(57343u);
x_304 = lean::nat_dec_lt(x_303, x_297);
lean::dec(x_303);
if (x_304 == 0)
{
obj* x_307; obj* x_308; obj* x_310; obj* x_311; obj* x_312; obj* x_313; obj* x_315; 
lean::dec(x_297);
x_307 = lean::mk_nat_obj(0u);
x_308 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_308);
if (lean::is_scalar(x_284)) {
 x_310 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_310 = x_284;
}
lean::cnstr_set(x_310, 0, x_307);
lean::cnstr_set(x_310, 1, x_288);
lean::cnstr_set(x_310, 2, x_308);
x_311 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_290, x_310);
x_312 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_282, x_311);
x_313 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_312);
lean::inc(x_308);
x_315 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_308, x_313);
return x_315;
}
else
{
obj* x_316; unsigned char x_317; 
x_316 = lean::mk_nat_obj(1114112u);
x_317 = lean::nat_dec_lt(x_297, x_316);
lean::dec(x_316);
if (x_317 == 0)
{
obj* x_320; obj* x_321; obj* x_323; obj* x_324; obj* x_325; obj* x_326; obj* x_328; 
lean::dec(x_297);
x_320 = lean::mk_nat_obj(0u);
x_321 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_321);
if (lean::is_scalar(x_284)) {
 x_323 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_323 = x_284;
}
lean::cnstr_set(x_323, 0, x_320);
lean::cnstr_set(x_323, 1, x_288);
lean::cnstr_set(x_323, 2, x_321);
x_324 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_290, x_323);
x_325 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_282, x_324);
x_326 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_325);
lean::inc(x_321);
x_328 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_321, x_326);
return x_328;
}
else
{
obj* x_329; obj* x_331; obj* x_332; obj* x_333; obj* x_334; obj* x_336; 
x_329 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_329);
if (lean::is_scalar(x_284)) {
 x_331 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_331 = x_284;
}
lean::cnstr_set(x_331, 0, x_297);
lean::cnstr_set(x_331, 1, x_288);
lean::cnstr_set(x_331, 2, x_329);
x_332 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_290, x_331);
x_333 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_282, x_332);
x_334 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_333);
lean::inc(x_329);
x_336 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_329, x_334);
return x_336;
}
}
}
else
{
obj* x_337; obj* x_339; obj* x_340; obj* x_341; obj* x_342; obj* x_344; 
x_337 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_337);
if (lean::is_scalar(x_284)) {
 x_339 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_339 = x_284;
}
lean::cnstr_set(x_339, 0, x_297);
lean::cnstr_set(x_339, 1, x_288);
lean::cnstr_set(x_339, 2, x_337);
x_340 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_290, x_339);
x_341 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_282, x_340);
x_342 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_341);
lean::inc(x_337);
x_344 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_337, x_342);
return x_344;
}
}
else
{
obj* x_347; unsigned char x_349; obj* x_350; obj* x_351; obj* x_352; obj* x_353; obj* x_354; obj* x_355; obj* x_357; 
lean::dec(x_284);
lean::dec(x_278);
x_347 = lean::cnstr_get(x_285, 0);
lean::inc(x_347);
x_349 = lean::cnstr_get_scalar<unsigned char>(x_285, sizeof(void*)*1);
if (lean::is_shared(x_285)) {
 lean::dec(x_285);
 x_350 = lean::box(0);
} else {
 lean::cnstr_release(x_285, 0);
 x_350 = x_285;
}
if (lean::is_scalar(x_350)) {
 x_351 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_351 = x_350;
}
lean::cnstr_set(x_351, 0, x_347);
lean::cnstr_set_scalar(x_351, sizeof(void*)*1, x_349);
x_352 = x_351;
x_353 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_282, x_352);
x_354 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_353);
x_355 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_355);
x_357 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_355, x_354);
return x_357;
}
}
else
{
obj* x_358; unsigned char x_360; obj* x_361; obj* x_362; obj* x_363; obj* x_364; obj* x_365; obj* x_367; 
x_358 = lean::cnstr_get(x_277, 0);
lean::inc(x_358);
x_360 = lean::cnstr_get_scalar<unsigned char>(x_277, sizeof(void*)*1);
if (lean::is_shared(x_277)) {
 lean::dec(x_277);
 x_361 = lean::box(0);
} else {
 lean::cnstr_release(x_277, 0);
 x_361 = x_277;
}
if (lean::is_scalar(x_361)) {
 x_362 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_362 = x_361;
}
lean::cnstr_set(x_362, 0, x_358);
lean::cnstr_set_scalar(x_362, sizeof(void*)*1, x_360);
x_363 = x_362;
x_364 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_363);
x_365 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_365);
x_367 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_365, x_364);
return x_367;
}
}
lbl_17:
{
obj* x_369; obj* x_370; unsigned char x_371; 
lean::dec(x_16);
x_369 = lean::mk_nat_obj(120u);
x_370 = lean::mk_nat_obj(55296u);
x_371 = lean::nat_dec_lt(x_369, x_370);
lean::dec(x_370);
if (x_371 == 0)
{
obj* x_373; unsigned char x_374; 
x_373 = lean::mk_nat_obj(57343u);
x_374 = lean::nat_dec_lt(x_373, x_369);
lean::dec(x_373);
if (x_374 == 0)
{
obj* x_377; unsigned char x_378; 
lean::dec(x_369);
x_377 = lean::mk_nat_obj(0u);
x_378 = lean::nat_dec_eq(x_3, x_377);
lean::dec(x_377);
if (x_378 == 0)
{
obj* x_380; 
x_380 = lean::box(0);
x_12 = x_380;
goto lbl_13;
}
else
{
obj* x_384; 
lean::dec(x_9);
lean::dec(x_0);
lean::dec(x_3);
x_384 = lean::box(0);
x_14 = x_384;
goto lbl_15;
}
}
else
{
obj* x_385; unsigned char x_386; 
x_385 = lean::mk_nat_obj(1114112u);
x_386 = lean::nat_dec_lt(x_369, x_385);
lean::dec(x_385);
if (x_386 == 0)
{
obj* x_389; unsigned char x_390; 
lean::dec(x_369);
x_389 = lean::mk_nat_obj(0u);
x_390 = lean::nat_dec_eq(x_3, x_389);
lean::dec(x_389);
if (x_390 == 0)
{
obj* x_392; 
x_392 = lean::box(0);
x_12 = x_392;
goto lbl_13;
}
else
{
obj* x_396; 
lean::dec(x_9);
lean::dec(x_0);
lean::dec(x_3);
x_396 = lean::box(0);
x_14 = x_396;
goto lbl_15;
}
}
else
{
unsigned char x_397; 
x_397 = lean::nat_dec_eq(x_3, x_369);
lean::dec(x_369);
if (x_397 == 0)
{
obj* x_399; 
x_399 = lean::box(0);
x_12 = x_399;
goto lbl_13;
}
else
{
obj* x_403; 
lean::dec(x_9);
lean::dec(x_0);
lean::dec(x_3);
x_403 = lean::box(0);
x_14 = x_403;
goto lbl_15;
}
}
}
}
else
{
unsigned char x_404; 
x_404 = lean::nat_dec_eq(x_3, x_369);
lean::dec(x_369);
if (x_404 == 0)
{
obj* x_406; 
x_406 = lean::box(0);
x_12 = x_406;
goto lbl_13;
}
else
{
obj* x_410; 
lean::dec(x_9);
lean::dec(x_0);
lean::dec(x_3);
x_410 = lean::box(0);
x_14 = x_410;
goto lbl_15;
}
}
}
lbl_19:
{
obj* x_412; obj* x_413; unsigned char x_414; unsigned x_415; 
lean::dec(x_18);
x_412 = lean::mk_nat_obj(116u);
x_413 = lean::mk_nat_obj(55296u);
x_414 = lean::nat_dec_lt(x_412, x_413);
if (x_414 == 0)
{
obj* x_417; unsigned char x_418; 
x_417 = lean::mk_nat_obj(57343u);
x_418 = lean::nat_dec_lt(x_417, x_412);
lean::dec(x_417);
if (x_418 == 0)
{
obj* x_421; unsigned x_422; 
lean::dec(x_412);
x_421 = lean::mk_nat_obj(0u);
x_422 = lean::unbox_uint32(x_421);
lean::dec(x_421);
x_415 = x_422;
goto lbl_416;
}
else
{
obj* x_424; unsigned char x_425; 
x_424 = lean::mk_nat_obj(1114112u);
x_425 = lean::nat_dec_lt(x_412, x_424);
lean::dec(x_424);
if (x_425 == 0)
{
obj* x_428; unsigned x_429; 
lean::dec(x_412);
x_428 = lean::mk_nat_obj(0u);
x_429 = lean::unbox_uint32(x_428);
lean::dec(x_428);
x_415 = x_429;
goto lbl_416;
}
else
{
unsigned x_431; 
x_431 = lean::unbox_uint32(x_412);
lean::dec(x_412);
x_415 = x_431;
goto lbl_416;
}
}
}
else
{
unsigned x_433; 
x_433 = lean::unbox_uint32(x_412);
lean::dec(x_412);
x_415 = x_433;
goto lbl_416;
}
lbl_416:
{
obj* x_435; unsigned char x_436; 
x_435 = lean::box_uint32(x_415);
x_436 = lean::nat_dec_eq(x_3, x_435);
lean::dec(x_435);
if (x_436 == 0)
{
obj* x_439; 
lean::dec(x_413);
x_439 = lean::box(0);
x_16 = x_439;
goto lbl_17;
}
else
{
obj* x_443; unsigned char x_444; 
lean::dec(x_9);
lean::dec(x_0);
lean::dec(x_3);
x_443 = lean::mk_nat_obj(9u);
x_444 = lean::nat_dec_lt(x_443, x_413);
lean::dec(x_413);
if (x_444 == 0)
{
obj* x_446; unsigned char x_447; 
x_446 = lean::mk_nat_obj(57343u);
x_447 = lean::nat_dec_lt(x_446, x_443);
lean::dec(x_446);
if (x_447 == 0)
{
obj* x_450; obj* x_451; obj* x_453; obj* x_454; obj* x_456; 
lean::dec(x_443);
x_450 = lean::mk_nat_obj(0u);
x_451 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_451);
x_453 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_453, 0, x_450);
lean::cnstr_set(x_453, 1, x_5);
lean::cnstr_set(x_453, 2, x_451);
x_454 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_453);
lean::inc(x_451);
x_456 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_451, x_454);
return x_456;
}
else
{
obj* x_457; unsigned char x_458; 
x_457 = lean::mk_nat_obj(1114112u);
x_458 = lean::nat_dec_lt(x_443, x_457);
lean::dec(x_457);
if (x_458 == 0)
{
obj* x_461; obj* x_462; obj* x_464; obj* x_465; obj* x_467; 
lean::dec(x_443);
x_461 = lean::mk_nat_obj(0u);
x_462 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_462);
x_464 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_464, 0, x_461);
lean::cnstr_set(x_464, 1, x_5);
lean::cnstr_set(x_464, 2, x_462);
x_465 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_464);
lean::inc(x_462);
x_467 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_462, x_465);
return x_467;
}
else
{
obj* x_468; obj* x_470; obj* x_471; obj* x_473; 
x_468 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_468);
x_470 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_470, 0, x_443);
lean::cnstr_set(x_470, 1, x_5);
lean::cnstr_set(x_470, 2, x_468);
x_471 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_470);
lean::inc(x_468);
x_473 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_468, x_471);
return x_473;
}
}
}
else
{
obj* x_474; obj* x_476; obj* x_477; obj* x_479; 
x_474 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_474);
x_476 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_476, 0, x_443);
lean::cnstr_set(x_476, 1, x_5);
lean::cnstr_set(x_476, 2, x_474);
x_477 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_476);
lean::inc(x_474);
x_479 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_474, x_477);
return x_479;
}
}
}
}
lbl_21:
{
obj* x_481; obj* x_482; unsigned char x_483; unsigned x_484; 
lean::dec(x_20);
x_481 = lean::mk_nat_obj(110u);
x_482 = lean::mk_nat_obj(55296u);
x_483 = lean::nat_dec_lt(x_481, x_482);
if (x_483 == 0)
{
obj* x_486; unsigned char x_487; 
x_486 = lean::mk_nat_obj(57343u);
x_487 = lean::nat_dec_lt(x_486, x_481);
lean::dec(x_486);
if (x_487 == 0)
{
obj* x_490; unsigned x_491; 
lean::dec(x_481);
x_490 = lean::mk_nat_obj(0u);
x_491 = lean::unbox_uint32(x_490);
lean::dec(x_490);
x_484 = x_491;
goto lbl_485;
}
else
{
obj* x_493; unsigned char x_494; 
x_493 = lean::mk_nat_obj(1114112u);
x_494 = lean::nat_dec_lt(x_481, x_493);
lean::dec(x_493);
if (x_494 == 0)
{
obj* x_497; unsigned x_498; 
lean::dec(x_481);
x_497 = lean::mk_nat_obj(0u);
x_498 = lean::unbox_uint32(x_497);
lean::dec(x_497);
x_484 = x_498;
goto lbl_485;
}
else
{
unsigned x_500; 
x_500 = lean::unbox_uint32(x_481);
lean::dec(x_481);
x_484 = x_500;
goto lbl_485;
}
}
}
else
{
unsigned x_502; 
x_502 = lean::unbox_uint32(x_481);
lean::dec(x_481);
x_484 = x_502;
goto lbl_485;
}
lbl_485:
{
obj* x_504; unsigned char x_505; 
x_504 = lean::box_uint32(x_484);
x_505 = lean::nat_dec_eq(x_3, x_504);
lean::dec(x_504);
if (x_505 == 0)
{
obj* x_508; 
lean::dec(x_482);
x_508 = lean::box(0);
x_18 = x_508;
goto lbl_19;
}
else
{
obj* x_512; unsigned char x_513; 
lean::dec(x_9);
lean::dec(x_0);
lean::dec(x_3);
x_512 = lean::mk_nat_obj(10u);
x_513 = lean::nat_dec_lt(x_512, x_482);
lean::dec(x_482);
if (x_513 == 0)
{
obj* x_515; unsigned char x_516; 
x_515 = lean::mk_nat_obj(57343u);
x_516 = lean::nat_dec_lt(x_515, x_512);
lean::dec(x_515);
if (x_516 == 0)
{
obj* x_519; obj* x_520; obj* x_522; obj* x_523; obj* x_525; 
lean::dec(x_512);
x_519 = lean::mk_nat_obj(0u);
x_520 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_520);
x_522 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_522, 0, x_519);
lean::cnstr_set(x_522, 1, x_5);
lean::cnstr_set(x_522, 2, x_520);
x_523 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_522);
lean::inc(x_520);
x_525 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_520, x_523);
return x_525;
}
else
{
obj* x_526; unsigned char x_527; 
x_526 = lean::mk_nat_obj(1114112u);
x_527 = lean::nat_dec_lt(x_512, x_526);
lean::dec(x_526);
if (x_527 == 0)
{
obj* x_530; obj* x_531; obj* x_533; obj* x_534; obj* x_536; 
lean::dec(x_512);
x_530 = lean::mk_nat_obj(0u);
x_531 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_531);
x_533 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_533, 0, x_530);
lean::cnstr_set(x_533, 1, x_5);
lean::cnstr_set(x_533, 2, x_531);
x_534 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_533);
lean::inc(x_531);
x_536 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_531, x_534);
return x_536;
}
else
{
obj* x_537; obj* x_539; obj* x_540; obj* x_542; 
x_537 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_537);
x_539 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_539, 0, x_512);
lean::cnstr_set(x_539, 1, x_5);
lean::cnstr_set(x_539, 2, x_537);
x_540 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_539);
lean::inc(x_537);
x_542 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_537, x_540);
return x_542;
}
}
}
else
{
obj* x_543; obj* x_545; obj* x_546; obj* x_548; 
x_543 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_543);
x_545 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_545, 0, x_512);
lean::cnstr_set(x_545, 1, x_5);
lean::cnstr_set(x_545, 2, x_543);
x_546 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_545);
lean::inc(x_543);
x_548 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_543, x_546);
return x_548;
}
}
}
}
lbl_23:
{
obj* x_550; obj* x_551; unsigned char x_552; unsigned x_554; 
lean::dec(x_22);
x_550 = lean::mk_nat_obj(39u);
x_551 = lean::mk_nat_obj(55296u);
x_552 = lean::nat_dec_lt(x_550, x_551);
lean::dec(x_551);
if (x_552 == 0)
{
obj* x_556; unsigned char x_557; 
x_556 = lean::mk_nat_obj(57343u);
x_557 = lean::nat_dec_lt(x_556, x_550);
lean::dec(x_556);
if (x_557 == 0)
{
obj* x_560; unsigned x_561; 
lean::dec(x_550);
x_560 = lean::mk_nat_obj(0u);
x_561 = lean::unbox_uint32(x_560);
lean::dec(x_560);
x_554 = x_561;
goto lbl_555;
}
else
{
obj* x_563; unsigned char x_564; 
x_563 = lean::mk_nat_obj(1114112u);
x_564 = lean::nat_dec_lt(x_550, x_563);
lean::dec(x_563);
if (x_564 == 0)
{
obj* x_567; unsigned x_568; 
lean::dec(x_550);
x_567 = lean::mk_nat_obj(0u);
x_568 = lean::unbox_uint32(x_567);
lean::dec(x_567);
x_554 = x_568;
goto lbl_555;
}
else
{
unsigned x_570; 
x_570 = lean::unbox_uint32(x_550);
lean::dec(x_550);
x_554 = x_570;
goto lbl_555;
}
}
}
else
{
unsigned x_572; 
x_572 = lean::unbox_uint32(x_550);
lean::dec(x_550);
x_554 = x_572;
goto lbl_555;
}
lbl_555:
{
obj* x_574; unsigned char x_575; 
x_574 = lean::box_uint32(x_554);
x_575 = lean::nat_dec_eq(x_3, x_574);
if (x_575 == 0)
{
obj* x_577; 
lean::dec(x_574);
x_577 = lean::box(0);
x_20 = x_577;
goto lbl_21;
}
else
{
obj* x_581; obj* x_583; obj* x_584; obj* x_586; 
lean::dec(x_9);
lean::dec(x_0);
lean::dec(x_3);
x_581 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_581);
x_583 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_583, 0, x_574);
lean::cnstr_set(x_583, 1, x_5);
lean::cnstr_set(x_583, 2, x_581);
x_584 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_583);
lean::inc(x_581);
x_586 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_581, x_584);
return x_586;
}
}
}
lbl_25:
{
obj* x_588; obj* x_589; unsigned char x_590; unsigned x_592; 
lean::dec(x_24);
x_588 = lean::mk_nat_obj(34u);
x_589 = lean::mk_nat_obj(55296u);
x_590 = lean::nat_dec_lt(x_588, x_589);
lean::dec(x_589);
if (x_590 == 0)
{
obj* x_594; unsigned char x_595; 
x_594 = lean::mk_nat_obj(57343u);
x_595 = lean::nat_dec_lt(x_594, x_588);
lean::dec(x_594);
if (x_595 == 0)
{
obj* x_598; unsigned x_599; 
lean::dec(x_588);
x_598 = lean::mk_nat_obj(0u);
x_599 = lean::unbox_uint32(x_598);
lean::dec(x_598);
x_592 = x_599;
goto lbl_593;
}
else
{
obj* x_601; unsigned char x_602; 
x_601 = lean::mk_nat_obj(1114112u);
x_602 = lean::nat_dec_lt(x_588, x_601);
lean::dec(x_601);
if (x_602 == 0)
{
obj* x_605; unsigned x_606; 
lean::dec(x_588);
x_605 = lean::mk_nat_obj(0u);
x_606 = lean::unbox_uint32(x_605);
lean::dec(x_605);
x_592 = x_606;
goto lbl_593;
}
else
{
unsigned x_608; 
x_608 = lean::unbox_uint32(x_588);
lean::dec(x_588);
x_592 = x_608;
goto lbl_593;
}
}
}
else
{
unsigned x_610; 
x_610 = lean::unbox_uint32(x_588);
lean::dec(x_588);
x_592 = x_610;
goto lbl_593;
}
lbl_593:
{
obj* x_612; unsigned char x_613; 
x_612 = lean::box_uint32(x_592);
x_613 = lean::nat_dec_eq(x_3, x_612);
if (x_613 == 0)
{
obj* x_615; 
lean::dec(x_612);
x_615 = lean::box(0);
x_22 = x_615;
goto lbl_23;
}
else
{
obj* x_619; obj* x_621; obj* x_622; obj* x_624; 
lean::dec(x_9);
lean::dec(x_0);
lean::dec(x_3);
x_619 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_619);
x_621 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_621, 0, x_612);
lean::cnstr_set(x_621, 1, x_5);
lean::cnstr_set(x_621, 2, x_619);
x_622 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_621);
lean::inc(x_619);
x_624 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_619, x_622);
return x_624;
}
}
}
lbl_31:
{
obj* x_625; unsigned char x_626; 
x_625 = lean::box_uint32(x_30);
x_626 = lean::nat_dec_eq(x_3, x_625);
if (x_626 == 0)
{
obj* x_628; 
lean::dec(x_625);
x_628 = lean::box(0);
x_24 = x_628;
goto lbl_25;
}
else
{
obj* x_632; obj* x_634; obj* x_635; obj* x_637; 
lean::dec(x_9);
lean::dec(x_0);
lean::dec(x_3);
x_632 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_632);
x_634 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_634, 0, x_625);
lean::cnstr_set(x_634, 1, x_5);
lean::cnstr_set(x_634, 2, x_632);
x_635 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_7, x_634);
lean::inc(x_632);
x_637 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_632, x_635);
return x_637;
}
}
}
else
{
obj* x_639; unsigned char x_641; obj* x_642; obj* x_643; obj* x_644; obj* x_645; obj* x_647; 
lean::dec(x_0);
x_639 = lean::cnstr_get(x_2, 0);
lean::inc(x_639);
x_641 = lean::cnstr_get_scalar<unsigned char>(x_2, sizeof(void*)*1);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_642 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 x_642 = x_2;
}
if (lean::is_scalar(x_642)) {
 x_643 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_643 = x_642;
}
lean::cnstr_set(x_643, 0, x_639);
lean::cnstr_set_scalar(x_643, sizeof(void*)*1, x_641);
x_644 = x_643;
x_645 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_645);
x_647 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_645, x_644);
return x_647;
}
}
}
obj* l_lean_parser_parse__string__literal__aux___main___at_lean_parser_string__lit_view_value___spec__4(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; unsigned char x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
obj* x_5; 
x_5 = l_lean_parser_monad__parsec_any___at_lean_parser_string__lit_view_value___spec__5(x_2);
if (lean::obj_tag(x_5) == 0)
{
obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_13; obj* x_14; obj* x_17; obj* x_19; obj* x_20; unsigned char x_21; unsigned x_23; 
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_5, 2);
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
x_13 = lean::mk_nat_obj(1u);
x_14 = lean::nat_sub(x_0, x_13);
lean::dec(x_13);
lean::dec(x_0);
x_19 = lean::mk_nat_obj(92u);
x_20 = lean::mk_nat_obj(55296u);
x_21 = lean::nat_dec_lt(x_19, x_20);
lean::dec(x_20);
if (x_21 == 0)
{
obj* x_25; unsigned char x_26; 
x_25 = lean::mk_nat_obj(57343u);
x_26 = lean::nat_dec_lt(x_25, x_19);
lean::dec(x_25);
if (x_26 == 0)
{
unsigned x_29; 
lean::dec(x_19);
x_29 = lean::unbox_uint32(x_3);
x_23 = x_29;
goto lbl_24;
}
else
{
obj* x_30; unsigned char x_31; 
x_30 = lean::mk_nat_obj(1114112u);
x_31 = lean::nat_dec_lt(x_19, x_30);
lean::dec(x_30);
if (x_31 == 0)
{
unsigned x_34; 
lean::dec(x_19);
x_34 = lean::unbox_uint32(x_3);
x_23 = x_34;
goto lbl_24;
}
else
{
unsigned x_35; 
x_35 = lean::unbox_uint32(x_19);
lean::dec(x_19);
x_23 = x_35;
goto lbl_24;
}
}
}
else
{
unsigned x_37; 
x_37 = lean::unbox_uint32(x_19);
lean::dec(x_19);
x_23 = x_37;
goto lbl_24;
}
lbl_18:
{
obj* x_40; obj* x_41; unsigned char x_42; unsigned x_44; 
lean::dec(x_17);
x_40 = lean::mk_nat_obj(34u);
x_41 = lean::mk_nat_obj(55296u);
x_42 = lean::nat_dec_lt(x_40, x_41);
lean::dec(x_41);
if (x_42 == 0)
{
obj* x_46; unsigned char x_47; 
x_46 = lean::mk_nat_obj(57343u);
x_47 = lean::nat_dec_lt(x_46, x_40);
lean::dec(x_46);
if (x_47 == 0)
{
unsigned x_50; 
lean::dec(x_40);
x_50 = lean::unbox_uint32(x_3);
lean::dec(x_3);
x_44 = x_50;
goto lbl_45;
}
else
{
obj* x_52; unsigned char x_53; 
x_52 = lean::mk_nat_obj(1114112u);
x_53 = lean::nat_dec_lt(x_40, x_52);
lean::dec(x_52);
if (x_53 == 0)
{
unsigned x_56; 
lean::dec(x_40);
x_56 = lean::unbox_uint32(x_3);
lean::dec(x_3);
x_44 = x_56;
goto lbl_45;
}
else
{
unsigned x_59; 
lean::dec(x_3);
x_59 = lean::unbox_uint32(x_40);
lean::dec(x_40);
x_44 = x_59;
goto lbl_45;
}
}
}
else
{
unsigned x_62; 
lean::dec(x_3);
x_62 = lean::unbox_uint32(x_40);
lean::dec(x_40);
x_44 = x_62;
goto lbl_45;
}
lbl_45:
{
obj* x_64; unsigned char x_65; 
x_64 = lean::box_uint32(x_44);
x_65 = lean::nat_dec_eq(x_6, x_64);
lean::dec(x_64);
if (x_65 == 0)
{
unsigned x_68; obj* x_70; obj* x_71; obj* x_72; 
lean::dec(x_12);
x_68 = lean::unbox_uint32(x_6);
lean::dec(x_6);
x_70 = lean::string_push(x_1, x_68);
x_71 = l_lean_parser_parse__string__literal__aux___main___at_lean_parser_string__lit_view_value___spec__4(x_14, x_70, x_8);
x_72 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_10, x_71);
return x_72;
}
else
{
obj* x_75; obj* x_77; obj* x_78; 
lean::dec(x_14);
lean::dec(x_6);
x_75 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_75);
if (lean::is_scalar(x_12)) {
 x_77 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_77 = x_12;
}
lean::cnstr_set(x_77, 0, x_1);
lean::cnstr_set(x_77, 1, x_8);
lean::cnstr_set(x_77, 2, x_75);
x_78 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_10, x_77);
return x_78;
}
}
}
lbl_24:
{
obj* x_79; unsigned char x_80; 
x_79 = lean::box_uint32(x_23);
x_80 = lean::nat_dec_eq(x_6, x_79);
lean::dec(x_79);
if (x_80 == 0)
{
obj* x_82; 
x_82 = lean::box(0);
x_17 = x_82;
goto lbl_18;
}
else
{
obj* x_86; 
lean::dec(x_12);
lean::dec(x_6);
lean::dec(x_3);
x_86 = l_lean_parser_parse__quoted__char___at_lean_parser_string__lit_view_value___spec__6(x_8);
if (lean::obj_tag(x_86) == 0)
{
obj* x_87; obj* x_89; obj* x_91; unsigned x_94; obj* x_96; obj* x_97; obj* x_98; obj* x_99; 
x_87 = lean::cnstr_get(x_86, 0);
lean::inc(x_87);
x_89 = lean::cnstr_get(x_86, 1);
lean::inc(x_89);
x_91 = lean::cnstr_get(x_86, 2);
lean::inc(x_91);
lean::dec(x_86);
x_94 = lean::unbox_uint32(x_87);
lean::dec(x_87);
x_96 = lean::string_push(x_1, x_94);
x_97 = l_lean_parser_parse__string__literal__aux___main___at_lean_parser_string__lit_view_value___spec__4(x_14, x_96, x_89);
x_98 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_91, x_97);
x_99 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_10, x_98);
return x_99;
}
else
{
obj* x_102; unsigned char x_104; obj* x_105; obj* x_106; obj* x_107; obj* x_108; 
lean::dec(x_14);
lean::dec(x_1);
x_102 = lean::cnstr_get(x_86, 0);
lean::inc(x_102);
x_104 = lean::cnstr_get_scalar<unsigned char>(x_86, sizeof(void*)*1);
if (lean::is_shared(x_86)) {
 lean::dec(x_86);
 x_105 = lean::box(0);
} else {
 lean::cnstr_release(x_86, 0);
 x_105 = x_86;
}
if (lean::is_scalar(x_105)) {
 x_106 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_106 = x_105;
}
lean::cnstr_set(x_106, 0, x_102);
lean::cnstr_set_scalar(x_106, sizeof(void*)*1, x_104);
x_107 = x_106;
x_108 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_10, x_107);
return x_108;
}
}
}
}
else
{
obj* x_112; unsigned char x_114; obj* x_115; obj* x_116; obj* x_117; 
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
x_112 = lean::cnstr_get(x_5, 0);
lean::inc(x_112);
x_114 = lean::cnstr_get_scalar<unsigned char>(x_5, sizeof(void*)*1);
if (lean::is_shared(x_5)) {
 lean::dec(x_5);
 x_115 = lean::box(0);
} else {
 lean::cnstr_release(x_5, 0);
 x_115 = x_5;
}
if (lean::is_scalar(x_115)) {
 x_116 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_116 = x_115;
}
lean::cnstr_set(x_116, 0, x_112);
lean::cnstr_set_scalar(x_116, sizeof(void*)*1, x_114);
x_117 = x_116;
return x_117;
}
}
else
{
obj* x_119; obj* x_120; unsigned char x_121; 
lean::dec(x_0);
x_119 = lean::mk_nat_obj(34u);
x_120 = lean::mk_nat_obj(55296u);
x_121 = lean::nat_dec_lt(x_119, x_120);
lean::dec(x_120);
if (x_121 == 0)
{
obj* x_123; unsigned char x_124; 
x_123 = lean::mk_nat_obj(57343u);
x_124 = lean::nat_dec_lt(x_123, x_119);
lean::dec(x_123);
if (x_124 == 0)
{
unsigned x_127; obj* x_129; 
lean::dec(x_119);
x_127 = lean::unbox_uint32(x_3);
lean::dec(x_3);
x_129 = l_lean_parser_monad__parsec_ch___at_lean_parser_string__lit_view_value___spec__2(x_127, x_2);
if (lean::obj_tag(x_129) == 0)
{
obj* x_130; obj* x_132; obj* x_134; obj* x_135; obj* x_137; obj* x_138; 
x_130 = lean::cnstr_get(x_129, 1);
lean::inc(x_130);
x_132 = lean::cnstr_get(x_129, 2);
lean::inc(x_132);
if (lean::is_shared(x_129)) {
 lean::dec(x_129);
 x_134 = lean::box(0);
} else {
 lean::cnstr_release(x_129, 0);
 lean::cnstr_release(x_129, 1);
 lean::cnstr_release(x_129, 2);
 x_134 = x_129;
}
x_135 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_135);
if (lean::is_scalar(x_134)) {
 x_137 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_137 = x_134;
}
lean::cnstr_set(x_137, 0, x_1);
lean::cnstr_set(x_137, 1, x_130);
lean::cnstr_set(x_137, 2, x_135);
x_138 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_132, x_137);
return x_138;
}
else
{
obj* x_140; unsigned char x_142; obj* x_143; obj* x_144; obj* x_145; 
lean::dec(x_1);
x_140 = lean::cnstr_get(x_129, 0);
lean::inc(x_140);
x_142 = lean::cnstr_get_scalar<unsigned char>(x_129, sizeof(void*)*1);
if (lean::is_shared(x_129)) {
 lean::dec(x_129);
 x_143 = lean::box(0);
} else {
 lean::cnstr_release(x_129, 0);
 x_143 = x_129;
}
if (lean::is_scalar(x_143)) {
 x_144 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_144 = x_143;
}
lean::cnstr_set(x_144, 0, x_140);
lean::cnstr_set_scalar(x_144, sizeof(void*)*1, x_142);
x_145 = x_144;
return x_145;
}
}
else
{
obj* x_146; unsigned char x_147; 
x_146 = lean::mk_nat_obj(1114112u);
x_147 = lean::nat_dec_lt(x_119, x_146);
lean::dec(x_146);
if (x_147 == 0)
{
unsigned x_150; obj* x_152; 
lean::dec(x_119);
x_150 = lean::unbox_uint32(x_3);
lean::dec(x_3);
x_152 = l_lean_parser_monad__parsec_ch___at_lean_parser_string__lit_view_value___spec__2(x_150, x_2);
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
obj* x_163; unsigned char x_165; obj* x_166; obj* x_167; obj* x_168; 
lean::dec(x_1);
x_163 = lean::cnstr_get(x_152, 0);
lean::inc(x_163);
x_165 = lean::cnstr_get_scalar<unsigned char>(x_152, sizeof(void*)*1);
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
else
{
unsigned x_170; obj* x_172; 
lean::dec(x_3);
x_170 = lean::unbox_uint32(x_119);
lean::dec(x_119);
x_172 = l_lean_parser_monad__parsec_ch___at_lean_parser_string__lit_view_value___spec__2(x_170, x_2);
if (lean::obj_tag(x_172) == 0)
{
obj* x_173; obj* x_175; obj* x_177; obj* x_178; obj* x_180; obj* x_181; 
x_173 = lean::cnstr_get(x_172, 1);
lean::inc(x_173);
x_175 = lean::cnstr_get(x_172, 2);
lean::inc(x_175);
if (lean::is_shared(x_172)) {
 lean::dec(x_172);
 x_177 = lean::box(0);
} else {
 lean::cnstr_release(x_172, 0);
 lean::cnstr_release(x_172, 1);
 lean::cnstr_release(x_172, 2);
 x_177 = x_172;
}
x_178 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_178);
if (lean::is_scalar(x_177)) {
 x_180 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_180 = x_177;
}
lean::cnstr_set(x_180, 0, x_1);
lean::cnstr_set(x_180, 1, x_173);
lean::cnstr_set(x_180, 2, x_178);
x_181 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_175, x_180);
return x_181;
}
else
{
obj* x_183; unsigned char x_185; obj* x_186; obj* x_187; obj* x_188; 
lean::dec(x_1);
x_183 = lean::cnstr_get(x_172, 0);
lean::inc(x_183);
x_185 = lean::cnstr_get_scalar<unsigned char>(x_172, sizeof(void*)*1);
if (lean::is_shared(x_172)) {
 lean::dec(x_172);
 x_186 = lean::box(0);
} else {
 lean::cnstr_release(x_172, 0);
 x_186 = x_172;
}
if (lean::is_scalar(x_186)) {
 x_187 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_187 = x_186;
}
lean::cnstr_set(x_187, 0, x_183);
lean::cnstr_set_scalar(x_187, sizeof(void*)*1, x_185);
x_188 = x_187;
return x_188;
}
}
}
}
else
{
unsigned x_190; obj* x_192; 
lean::dec(x_3);
x_190 = lean::unbox_uint32(x_119);
lean::dec(x_119);
x_192 = l_lean_parser_monad__parsec_ch___at_lean_parser_string__lit_view_value___spec__2(x_190, x_2);
if (lean::obj_tag(x_192) == 0)
{
obj* x_193; obj* x_195; obj* x_197; obj* x_198; obj* x_200; obj* x_201; 
x_193 = lean::cnstr_get(x_192, 1);
lean::inc(x_193);
x_195 = lean::cnstr_get(x_192, 2);
lean::inc(x_195);
if (lean::is_shared(x_192)) {
 lean::dec(x_192);
 x_197 = lean::box(0);
} else {
 lean::cnstr_release(x_192, 0);
 lean::cnstr_release(x_192, 1);
 lean::cnstr_release(x_192, 2);
 x_197 = x_192;
}
x_198 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_198);
if (lean::is_scalar(x_197)) {
 x_200 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_200 = x_197;
}
lean::cnstr_set(x_200, 0, x_1);
lean::cnstr_set(x_200, 1, x_193);
lean::cnstr_set(x_200, 2, x_198);
x_201 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_195, x_200);
return x_201;
}
else
{
obj* x_203; unsigned char x_205; obj* x_206; obj* x_207; obj* x_208; 
lean::dec(x_1);
x_203 = lean::cnstr_get(x_192, 0);
lean::inc(x_203);
x_205 = lean::cnstr_get_scalar<unsigned char>(x_192, sizeof(void*)*1);
if (lean::is_shared(x_192)) {
 lean::dec(x_192);
 x_206 = lean::box(0);
} else {
 lean::cnstr_release(x_192, 0);
 x_206 = x_192;
}
if (lean::is_scalar(x_206)) {
 x_207 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_207 = x_206;
}
lean::cnstr_set(x_207, 0, x_203);
lean::cnstr_set_scalar(x_207, sizeof(void*)*1, x_205);
x_208 = x_207;
return x_208;
}
}
}
}
}
obj* l_lean_parser_parse__string__literal___at_lean_parser_string__lit_view_value___spec__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; unsigned char x_3; 
x_1 = lean::mk_nat_obj(34u);
x_2 = lean::mk_nat_obj(55296u);
x_3 = lean::nat_dec_lt(x_1, x_2);
lean::dec(x_2);
if (x_3 == 0)
{
obj* x_5; unsigned char x_6; 
x_5 = lean::mk_nat_obj(57343u);
x_6 = lean::nat_dec_lt(x_5, x_1);
lean::dec(x_5);
if (x_6 == 0)
{
obj* x_9; unsigned x_10; obj* x_12; 
lean::dec(x_1);
x_9 = lean::mk_nat_obj(0u);
x_10 = lean::unbox_uint32(x_9);
lean::dec(x_9);
x_12 = l_lean_parser_monad__parsec_ch___at_lean_parser_string__lit_view_value___spec__2(x_10, x_0);
if (lean::obj_tag(x_12) == 0)
{
obj* x_13; obj* x_15; obj* x_18; obj* x_19; obj* x_21; obj* x_22; obj* x_24; obj* x_25; 
x_13 = lean::cnstr_get(x_12, 1);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_12, 2);
lean::inc(x_15);
lean::dec(x_12);
x_18 = lean::string_iterator_remaining(x_13);
x_19 = l_string_join___closed__1;
lean::inc(x_19);
x_21 = l_lean_parser_parse__string__literal__aux___main___at_lean_parser_string__lit_view_value___spec__4(x_18, x_19, x_13);
x_22 = l_lean_parser_finish__comment__block___closed__2;
lean::inc(x_22);
x_24 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_22, x_21);
x_25 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_24);
return x_25;
}
else
{
obj* x_26; unsigned char x_28; obj* x_29; obj* x_30; obj* x_31; 
x_26 = lean::cnstr_get(x_12, 0);
lean::inc(x_26);
x_28 = lean::cnstr_get_scalar<unsigned char>(x_12, sizeof(void*)*1);
if (lean::is_shared(x_12)) {
 lean::dec(x_12);
 x_29 = lean::box(0);
} else {
 lean::cnstr_release(x_12, 0);
 x_29 = x_12;
}
if (lean::is_scalar(x_29)) {
 x_30 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_30 = x_29;
}
lean::cnstr_set(x_30, 0, x_26);
lean::cnstr_set_scalar(x_30, sizeof(void*)*1, x_28);
x_31 = x_30;
return x_31;
}
}
else
{
obj* x_32; unsigned char x_33; 
x_32 = lean::mk_nat_obj(1114112u);
x_33 = lean::nat_dec_lt(x_1, x_32);
lean::dec(x_32);
if (x_33 == 0)
{
obj* x_36; unsigned x_37; obj* x_39; 
lean::dec(x_1);
x_36 = lean::mk_nat_obj(0u);
x_37 = lean::unbox_uint32(x_36);
lean::dec(x_36);
x_39 = l_lean_parser_monad__parsec_ch___at_lean_parser_string__lit_view_value___spec__2(x_37, x_0);
if (lean::obj_tag(x_39) == 0)
{
obj* x_40; obj* x_42; obj* x_45; obj* x_46; obj* x_48; obj* x_49; obj* x_51; obj* x_52; 
x_40 = lean::cnstr_get(x_39, 1);
lean::inc(x_40);
x_42 = lean::cnstr_get(x_39, 2);
lean::inc(x_42);
lean::dec(x_39);
x_45 = lean::string_iterator_remaining(x_40);
x_46 = l_string_join___closed__1;
lean::inc(x_46);
x_48 = l_lean_parser_parse__string__literal__aux___main___at_lean_parser_string__lit_view_value___spec__4(x_45, x_46, x_40);
x_49 = l_lean_parser_finish__comment__block___closed__2;
lean::inc(x_49);
x_51 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_49, x_48);
x_52 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_42, x_51);
return x_52;
}
else
{
obj* x_53; unsigned char x_55; obj* x_56; obj* x_57; obj* x_58; 
x_53 = lean::cnstr_get(x_39, 0);
lean::inc(x_53);
x_55 = lean::cnstr_get_scalar<unsigned char>(x_39, sizeof(void*)*1);
if (lean::is_shared(x_39)) {
 lean::dec(x_39);
 x_56 = lean::box(0);
} else {
 lean::cnstr_release(x_39, 0);
 x_56 = x_39;
}
if (lean::is_scalar(x_56)) {
 x_57 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_57 = x_56;
}
lean::cnstr_set(x_57, 0, x_53);
lean::cnstr_set_scalar(x_57, sizeof(void*)*1, x_55);
x_58 = x_57;
return x_58;
}
}
else
{
unsigned x_59; obj* x_61; 
x_59 = lean::unbox_uint32(x_1);
lean::dec(x_1);
x_61 = l_lean_parser_monad__parsec_ch___at_lean_parser_string__lit_view_value___spec__2(x_59, x_0);
if (lean::obj_tag(x_61) == 0)
{
obj* x_62; obj* x_64; obj* x_67; obj* x_68; obj* x_70; obj* x_71; obj* x_73; obj* x_74; 
x_62 = lean::cnstr_get(x_61, 1);
lean::inc(x_62);
x_64 = lean::cnstr_get(x_61, 2);
lean::inc(x_64);
lean::dec(x_61);
x_67 = lean::string_iterator_remaining(x_62);
x_68 = l_string_join___closed__1;
lean::inc(x_68);
x_70 = l_lean_parser_parse__string__literal__aux___main___at_lean_parser_string__lit_view_value___spec__4(x_67, x_68, x_62);
x_71 = l_lean_parser_finish__comment__block___closed__2;
lean::inc(x_71);
x_73 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_71, x_70);
x_74 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_64, x_73);
return x_74;
}
else
{
obj* x_75; unsigned char x_77; obj* x_78; obj* x_79; obj* x_80; 
x_75 = lean::cnstr_get(x_61, 0);
lean::inc(x_75);
x_77 = lean::cnstr_get_scalar<unsigned char>(x_61, sizeof(void*)*1);
if (lean::is_shared(x_61)) {
 lean::dec(x_61);
 x_78 = lean::box(0);
} else {
 lean::cnstr_release(x_61, 0);
 x_78 = x_61;
}
if (lean::is_scalar(x_78)) {
 x_79 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_79 = x_78;
}
lean::cnstr_set(x_79, 0, x_75);
lean::cnstr_set_scalar(x_79, sizeof(void*)*1, x_77);
x_80 = x_79;
return x_80;
}
}
}
}
else
{
unsigned x_81; obj* x_83; 
x_81 = lean::unbox_uint32(x_1);
lean::dec(x_1);
x_83 = l_lean_parser_monad__parsec_ch___at_lean_parser_string__lit_view_value___spec__2(x_81, x_0);
if (lean::obj_tag(x_83) == 0)
{
obj* x_84; obj* x_86; obj* x_89; obj* x_90; obj* x_92; obj* x_93; obj* x_95; obj* x_96; 
x_84 = lean::cnstr_get(x_83, 1);
lean::inc(x_84);
x_86 = lean::cnstr_get(x_83, 2);
lean::inc(x_86);
lean::dec(x_83);
x_89 = lean::string_iterator_remaining(x_84);
x_90 = l_string_join___closed__1;
lean::inc(x_90);
x_92 = l_lean_parser_parse__string__literal__aux___main___at_lean_parser_string__lit_view_value___spec__4(x_89, x_90, x_84);
x_93 = l_lean_parser_finish__comment__block___closed__2;
lean::inc(x_93);
x_95 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_93, x_92);
x_96 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_86, x_95);
return x_96;
}
else
{
obj* x_97; unsigned char x_99; obj* x_100; obj* x_101; obj* x_102; 
x_97 = lean::cnstr_get(x_83, 0);
lean::inc(x_97);
x_99 = lean::cnstr_get_scalar<unsigned char>(x_83, sizeof(void*)*1);
if (lean::is_shared(x_83)) {
 lean::dec(x_83);
 x_100 = lean::box(0);
} else {
 lean::cnstr_release(x_83, 0);
 x_100 = x_83;
}
if (lean::is_scalar(x_100)) {
 x_101 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_101 = x_100;
}
lean::cnstr_set(x_101, 0, x_97);
lean::cnstr_set_scalar(x_101, sizeof(void*)*1, x_99);
x_102 = x_101;
return x_102;
}
}
}
}
obj* l_lean_parser_monad__parsec_ch___at_lean_parser_string__lit_view_value___spec__2___boxed(obj* x_0, obj* x_1) {
_start:
{
unsigned x_2; obj* x_3; 
x_2 = lean::unbox_uint32(x_0);
x_3 = l_lean_parser_monad__parsec_ch___at_lean_parser_string__lit_view_value___spec__2(x_2, x_1);
return x_3;
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
x_48 = l_lean_parser_monad__parsec_error___at___private_4089500695__finish__comment__block__aux___main___spec__1___rarg(x_45, x_0, x_43, x_44, x_1, x_14, x_9);
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
obj* x_63; unsigned char x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_71; obj* x_72; obj* x_73; obj* x_74; 
lean::dec(x_1);
lean::dec(x_2);
x_63 = lean::cnstr_get(x_7, 0);
lean::inc(x_63);
x_65 = lean::cnstr_get_scalar<unsigned char>(x_7, sizeof(void*)*1);
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
obj* _init_l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_5; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("NOT_AN_IDENT");
lean::inc(x_1);
x_3 = l_lean_parser_substring_of__string(x_1);
lean::inc(x_0);
x_5 = lean::name_mk_string(x_0, x_1);
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
obj* l_lean_parser_ident_parser_view___rarg___lambda__2(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
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
obj* _init_l_lean_parser_raw__ident_parser___rarg___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l___private_3519775105__ident_x_27), 3, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_with__trailing___at_lean_parser_token___spec__3), 4, 0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_bind___at_lean_parser_with__trailing___spec__2___rarg), 5, 2);
lean::closure_set(x_2, 0, x_0);
lean::closure_set(x_2, 1, x_1);
return x_2;
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
obj* x_36; 
if (lean::obj_tag(x_19) == 0)
{
unsigned char x_39; obj* x_40; 
lean::dec(x_19);
x_39 = 1;
x_40 = lean::box(x_39);
x_36 = x_40;
goto lbl_37;
}
else
{
obj* x_41; unsigned char x_44; 
x_41 = lean::cnstr_get(x_19, 0);
lean::inc(x_41);
lean::dec(x_19);
x_44 = lean::string_dec_eq(x_41, x_0);
lean::dec(x_41);
if (x_44 == 0)
{
unsigned char x_46; obj* x_47; 
x_46 = 1;
x_47 = lean::box(x_46);
x_36 = x_47;
goto lbl_37;
}
else
{
unsigned char x_48; obj* x_49; 
x_48 = 0;
x_49 = lean::box(x_48);
x_36 = x_49;
goto lbl_37;
}
}
lbl_37:
{
unsigned char x_50; 
x_50 = lean::unbox(x_36);
lean::dec(x_36);
if (x_50 == 0)
{
obj* x_55; obj* x_57; obj* x_58; obj* x_59; obj* x_61; obj* x_62; obj* x_63; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_55 = l_lean_parser_finish__comment__block___closed__2;
lean::inc(x_55);
if (lean::is_scalar(x_18)) {
 x_57 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_57 = x_18;
}
lean::cnstr_set(x_57, 0, x_12);
lean::cnstr_set(x_57, 1, x_14);
lean::cnstr_set(x_57, 2, x_55);
x_58 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_57);
x_59 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_59);
x_61 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_59, x_58);
x_62 = l_lean_parser_parsec__t_try__mk__res___rarg(x_61);
if (lean::is_scalar(x_11)) {
 x_63 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_63 = x_11;
}
lean::cnstr_set(x_63, 0, x_62);
lean::cnstr_set(x_63, 1, x_9);
return x_63;
}
else
{
obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_70; obj* x_71; obj* x_73; 
x_64 = l_string_quote(x_0);
x_65 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_65, 0, x_64);
x_66 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_66, 0, x_2);
x_67 = lean::box(0);
x_68 = l_string_join___closed__1;
lean::inc(x_68);
x_70 = l_lean_parser_monad__parsec_error___at___private_4089500695__finish__comment__block__aux___main___spec__1___rarg(x_68, x_65, x_66, x_67, x_1, x_14, x_9);
x_71 = lean::cnstr_get(x_70, 0);
lean::inc(x_71);
x_73 = lean::cnstr_get(x_70, 1);
lean::inc(x_73);
lean::dec(x_70);
if (lean::obj_tag(x_71) == 0)
{
obj* x_76; obj* x_78; obj* x_81; obj* x_83; obj* x_84; obj* x_85; obj* x_87; obj* x_88; obj* x_89; 
x_76 = lean::cnstr_get(x_71, 1);
lean::inc(x_76);
x_78 = lean::cnstr_get(x_71, 2);
lean::inc(x_78);
lean::dec(x_71);
x_81 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_81);
if (lean::is_scalar(x_18)) {
 x_83 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_83 = x_18;
}
lean::cnstr_set(x_83, 0, x_12);
lean::cnstr_set(x_83, 1, x_76);
lean::cnstr_set(x_83, 2, x_81);
x_84 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_78, x_83);
x_85 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_84);
lean::inc(x_81);
x_87 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_81, x_85);
x_88 = l_lean_parser_parsec__t_try__mk__res___rarg(x_87);
if (lean::is_scalar(x_11)) {
 x_89 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_89 = x_11;
}
lean::cnstr_set(x_89, 0, x_88);
lean::cnstr_set(x_89, 1, x_73);
return x_89;
}
else
{
obj* x_92; unsigned char x_94; obj* x_95; obj* x_96; obj* x_97; obj* x_98; obj* x_99; obj* x_101; obj* x_102; obj* x_103; 
lean::dec(x_18);
lean::dec(x_12);
x_92 = lean::cnstr_get(x_71, 0);
lean::inc(x_92);
x_94 = lean::cnstr_get_scalar<unsigned char>(x_71, sizeof(void*)*1);
if (lean::is_shared(x_71)) {
 lean::dec(x_71);
 x_95 = lean::box(0);
} else {
 lean::cnstr_release(x_71, 0);
 x_95 = x_71;
}
if (lean::is_scalar(x_95)) {
 x_96 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_96 = x_95;
}
lean::cnstr_set(x_96, 0, x_92);
lean::cnstr_set_scalar(x_96, sizeof(void*)*1, x_94);
x_97 = x_96;
x_98 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_16, x_97);
x_99 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_99);
x_101 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_99, x_98);
x_102 = l_lean_parser_parsec__t_try__mk__res___rarg(x_101);
if (lean::is_scalar(x_11)) {
 x_103 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_103 = x_11;
}
lean::cnstr_set(x_103, 0, x_102);
lean::cnstr_set(x_103, 1, x_73);
return x_103;
}
}
}
}
}
else
{
obj* x_107; unsigned char x_109; obj* x_110; obj* x_111; obj* x_112; obj* x_113; obj* x_115; obj* x_116; obj* x_117; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_107 = lean::cnstr_get(x_7, 0);
lean::inc(x_107);
x_109 = lean::cnstr_get_scalar<unsigned char>(x_7, sizeof(void*)*1);
if (lean::is_shared(x_7)) {
 lean::dec(x_7);
 x_110 = lean::box(0);
} else {
 lean::cnstr_release(x_7, 0);
 x_110 = x_7;
}
if (lean::is_scalar(x_110)) {
 x_111 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_111 = x_110;
}
lean::cnstr_set(x_111, 0, x_107);
lean::cnstr_set_scalar(x_111, sizeof(void*)*1, x_109);
x_112 = x_111;
x_113 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_113);
x_115 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_113, x_112);
x_116 = l_lean_parser_parsec__t_try__mk__res___rarg(x_115);
if (lean::is_scalar(x_11)) {
 x_117 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_117 = x_11;
}
lean::cnstr_set(x_117, 0, x_116);
lean::cnstr_set(x_117, 1, x_9);
return x_117;
}
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
obj* l_lean_parser_unicode__symbol___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_4 = l_string_trim(x_1);
lean::inc(x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_6, 0, x_4);
lean::inc(x_3);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_unicode__symbol___spec__1), 6, 3);
lean::closure_set(x_8, 0, x_4);
lean::closure_set(x_8, 1, x_3);
lean::closure_set(x_8, 2, x_6);
x_9 = l_string_trim(x_2);
lean::inc(x_9);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_11, 0, x_9);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_unicode__symbol___spec__1), 6, 3);
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
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_any__of___at_lean_parser_unicode__symbol___spec__2), 4, 1);
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
obj* l_lean_parser_symbol__core___at_lean_parser_unicode__symbol___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
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
obj* x_27; obj* x_29; unsigned char x_32; 
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
x_36 = l_lean_parser_monad__parsec_error___at___private_4089500695__finish__comment__block__aux___main___spec__1___rarg(x_29, x_2, x_34, x_35, x_3, x_19, x_12);
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
obj* x_59; unsigned char x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_68; obj* x_69; obj* x_70; obj* x_71; 
lean::dec(x_23);
lean::dec(x_17);
x_59 = lean::cnstr_get(x_37, 0);
lean::inc(x_59);
x_61 = lean::cnstr_get_scalar<unsigned char>(x_37, sizeof(void*)*1);
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
x_103 = l_lean_parser_monad__parsec_error___at___private_4089500695__finish__comment__block__aux___main___spec__1___rarg(x_101, x_2, x_99, x_100, x_3, x_19, x_12);
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
obj* x_120; unsigned char x_122; obj* x_123; obj* x_124; obj* x_125; obj* x_126; obj* x_128; obj* x_129; obj* x_130; obj* x_131; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
x_120 = lean::cnstr_get(x_10, 0);
lean::inc(x_120);
x_122 = lean::cnstr_get_scalar<unsigned char>(x_10, sizeof(void*)*1);
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
obj* l_list_foldl___main___at_lean_parser_unicode__symbol___spec__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
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
obj* l_lean_parser_combinators_any__of___at_lean_parser_unicode__symbol___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
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
x_11 = l_lean_parser_monad__parsec_error___at___private_4089500695__finish__comment__block__aux___main___spec__1___rarg(x_6, x_7, x_5, x_5, x_1, x_2, x_3);
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
x_17 = l_list_foldl___main___at_lean_parser_unicode__symbol___spec__3(x_12, x_14, x_1, x_2, x_3);
return x_17;
}
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
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_unicode__symbol___spec__1), 6, 3);
lean::closure_set(x_8, 0, x_4);
lean::closure_set(x_8, 1, x_3);
lean::closure_set(x_8, 2, x_6);
x_9 = l_string_trim(x_2);
lean::inc(x_9);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_11, 0, x_9);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_unicode__symbol___spec__1), 6, 3);
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
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_any__of___at_lean_parser_unicode__symbol___spec__2), 4, 1);
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
obj* _init_l_lean_parser_indexed___rarg___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_peek__token), 3, 0);
return x_0;
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
x_13 = l_lean_parser_monad__parsec_error___at___private_4089500695__finish__comment__block__aux___main___spec__1___rarg(x_8, x_9, x_7, x_7, x_2, x_3, x_4);
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
x_24 = lean::name_mk_string(x_23, x_20);
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
x_75 = l_lean_parser_monad__parsec_error___at___private_4089500695__finish__comment__block__aux___main___spec__1___rarg(x_69, x_70, x_68, x_68, x_2, x_3, x_4);
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
obj* x_99; unsigned char x_101; obj* x_102; obj* x_103; obj* x_104; obj* x_105; 
lean::dec(x_0);
lean::dec(x_2);
x_99 = lean::cnstr_get(x_76, 0);
lean::inc(x_99);
x_101 = lean::cnstr_get_scalar<unsigned char>(x_76, sizeof(void*)*1);
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
obj* _init_l_lean_parser_indexed___rarg___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("ident");
x_2 = lean::name_mk_string(x_0, x_1);
return x_2;
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
 l___private_4089500695__finish__comment__block__aux___main___closed__1 = _init_l___private_4089500695__finish__comment__block__aux___main___closed__1();
 l___private_4089500695__finish__comment__block__aux___main___closed__2 = _init_l___private_4089500695__finish__comment__block__aux___main___closed__2();
 l___private_4089500695__finish__comment__block__aux___main___closed__3 = _init_l___private_4089500695__finish__comment__block__aux___main___closed__3();
 l___private_4089500695__finish__comment__block__aux___main___closed__4 = _init_l___private_4089500695__finish__comment__block__aux___main___closed__4();
 l_lean_parser_finish__comment__block___closed__1 = _init_l_lean_parser_finish__comment__block___closed__1();
 l_lean_parser_finish__comment__block___closed__2 = _init_l_lean_parser_finish__comment__block___closed__2();
 l___private_2012034129__whitespace__aux___main___closed__1 = _init_l___private_2012034129__whitespace__aux___main___closed__1();
 l___private_2012034129__whitespace__aux___main___closed__2 = _init_l___private_2012034129__whitespace__aux___main___closed__2();
 l___private_2012034129__whitespace__aux___main___closed__3 = _init_l___private_2012034129__whitespace__aux___main___closed__3();
 l_lean_parser_parsec__t_lookahead___at___private_2012034129__whitespace__aux___main___spec__4___closed__1 = _init_l_lean_parser_parsec__t_lookahead___at___private_2012034129__whitespace__aux___main___spec__4___closed__1();
 l_lean_parser_parsec__t_lookahead___at___private_2012034129__whitespace__aux___main___spec__4___closed__2 = _init_l_lean_parser_parsec__t_lookahead___at___private_2012034129__whitespace__aux___main___spec__4___closed__2();
 l_lean_parser_with__trailing___rarg___closed__1 = _init_l_lean_parser_with__trailing___rarg___closed__1();
 l_lean_parser_raw_view___rarg___closed__1 = _init_l_lean_parser_raw_view___rarg___closed__1();
 l_lean_parser_raw_view___rarg___closed__2 = _init_l_lean_parser_raw_view___rarg___closed__2();
 l_lean_parser_raw_view___rarg___lambda__3___closed__1 = _init_l_lean_parser_raw_view___rarg___lambda__3___closed__1();
 l_lean_parser_detail__ident__part__escaped = _init_l_lean_parser_detail__ident__part__escaped();
 l_lean_parser_detail__ident__part__escaped_has__view_x_27 = _init_l_lean_parser_detail__ident__part__escaped_has__view_x_27();
 l_lean_parser_detail__ident__part__escaped_has__view_x_27___lambda__1___closed__1 = _init_l_lean_parser_detail__ident__part__escaped_has__view_x_27___lambda__1___closed__1();
 l_lean_parser_detail__ident__part__escaped_has__view = _init_l_lean_parser_detail__ident__part__escaped_has__view();
 l_lean_parser_detail__ident__part = _init_l_lean_parser_detail__ident__part();
 l_lean_parser_detail__ident__part_has__view_x_27 = _init_l_lean_parser_detail__ident__part_has__view_x_27();
 l_lean_parser_detail__ident__part_has__view_x_27___lambda__1___closed__1 = _init_l_lean_parser_detail__ident__part_has__view_x_27___lambda__1___closed__1();
 l_lean_parser_detail__ident__part_has__view_x_27___lambda__1___closed__2 = _init_l_lean_parser_detail__ident__part_has__view_x_27___lambda__1___closed__2();
 l_lean_parser_detail__ident__part_has__view_x_27___lambda__1___closed__3 = _init_l_lean_parser_detail__ident__part_has__view_x_27___lambda__1___closed__3();
 l_lean_parser_detail__ident__part_has__view_x_27___lambda__2___closed__1 = _init_l_lean_parser_detail__ident__part_has__view_x_27___lambda__2___closed__1();
 l_lean_parser_detail__ident__part_has__view_x_27___lambda__2___closed__2 = _init_l_lean_parser_detail__ident__part_has__view_x_27___lambda__2___closed__2();
 l_lean_parser_detail__ident__part_has__view = _init_l_lean_parser_detail__ident__part_has__view();
 l_lean_parser_detail__ident__part_parser___closed__1 = _init_l_lean_parser_detail__ident__part_parser___closed__1();
 l_lean_parser_detail__ident__part_parser_lean_parser_has__view = _init_l_lean_parser_detail__ident__part_parser_lean_parser_has__view();
 l_lean_parser_detail__ident__part_parser_lean_parser_has__tokens = _init_l_lean_parser_detail__ident__part_parser_lean_parser_has__tokens();
 l_lean_parser_detail__ident__suffix = _init_l_lean_parser_detail__ident__suffix();
 l_lean_parser_detail__ident__suffix_has__view_x_27 = _init_l_lean_parser_detail__ident__suffix_has__view_x_27();
 l_lean_parser_detail__ident__suffix_has__view_x_27___lambda__1___closed__1 = _init_l_lean_parser_detail__ident__suffix_has__view_x_27___lambda__1___closed__1();
 l_lean_parser_detail__ident__suffix_has__view = _init_l_lean_parser_detail__ident__suffix_has__view();
 l_lean_parser_detail__ident__suffix_parser___closed__1 = _init_l_lean_parser_detail__ident__suffix_parser___closed__1();
 l_lean_parser_detail__ident__suffix_parser_lean_parser_has__view = _init_l_lean_parser_detail__ident__suffix_parser_lean_parser_has__view();
 l_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens = _init_l_lean_parser_detail__ident__suffix_parser_lean_parser_has__tokens();
 l_lean_parser_detail__ident = _init_l_lean_parser_detail__ident();
 l_lean_parser_detail__ident_has__view_x_27 = _init_l_lean_parser_detail__ident_has__view_x_27();
 l_lean_parser_detail__ident_has__view_x_27___lambda__1___closed__1 = _init_l_lean_parser_detail__ident_has__view_x_27___lambda__1___closed__1();
 l_lean_parser_detail__ident_has__view_x_27___lambda__1___closed__2 = _init_l_lean_parser_detail__ident_has__view_x_27___lambda__1___closed__2();
 l_lean_parser_detail__ident_has__view_x_27___lambda__2___closed__1 = _init_l_lean_parser_detail__ident_has__view_x_27___lambda__2___closed__1();
 l_lean_parser_detail__ident_has__view = _init_l_lean_parser_detail__ident_has__view();
 l_lean_parser_detail__ident_x_27___closed__1 = _init_l_lean_parser_detail__ident_x_27___closed__1();
 l_lean_parser_detail__ident_parser___closed__1 = _init_l_lean_parser_detail__ident_parser___closed__1();
 l_lean_parser_detail__ident_parser___closed__2 = _init_l_lean_parser_detail__ident_parser___closed__2();
 l_lean_parser_rec__t_run__parsec___at_lean_parser_detail__ident_parser___spec__1___closed__1 = _init_l_lean_parser_rec__t_run__parsec___at_lean_parser_detail__ident_parser___spec__1___closed__1();
 l_lean_parser_number = _init_l_lean_parser_number();
 l_lean_parser_number_has__view_x_27 = _init_l_lean_parser_number_has__view_x_27();
 l_lean_parser_number_has__view_x_27___lambda__1___closed__1 = _init_l_lean_parser_number_has__view_x_27___lambda__1___closed__1();
 l_lean_parser_number_has__view_x_27___lambda__1___closed__2 = _init_l_lean_parser_number_has__view_x_27___lambda__1___closed__2();
 l_lean_parser_number_has__view_x_27___lambda__1___closed__3 = _init_l_lean_parser_number_has__view_x_27___lambda__1___closed__3();
 l_lean_parser_number_has__view_x_27___lambda__1___closed__4 = _init_l_lean_parser_number_has__view_x_27___lambda__1___closed__4();
 l_lean_parser_number_has__view_x_27___lambda__1___closed__5 = _init_l_lean_parser_number_has__view_x_27___lambda__1___closed__5();
 l_lean_parser_number_has__view_x_27___lambda__1___closed__6 = _init_l_lean_parser_number_has__view_x_27___lambda__1___closed__6();
 l_lean_parser_number_has__view_x_27___lambda__2___closed__1 = _init_l_lean_parser_number_has__view_x_27___lambda__2___closed__1();
 l_lean_parser_number_has__view_x_27___lambda__2___closed__2 = _init_l_lean_parser_number_has__view_x_27___lambda__2___closed__2();
 l_lean_parser_number_has__view = _init_l_lean_parser_number_has__view();
 l_lean_parser_number_x_27___closed__1 = _init_l_lean_parser_number_x_27___closed__1();
 l_lean_parser_string__lit = _init_l_lean_parser_string__lit();
 l_lean_parser_string__lit_has__view_x_27 = _init_l_lean_parser_string__lit_has__view_x_27();
 l_lean_parser_string__lit_has__view = _init_l_lean_parser_string__lit_has__view();
 l_lean_parser_string__lit_x_27___closed__1 = _init_l_lean_parser_string__lit_x_27___closed__1();
 l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__4___closed__1 = _init_l_lean_parser_parse__hex__digit___at_lean_parser_string__lit_x_27___spec__4___closed__1();
 l_lean_parser_token___closed__1 = _init_l_lean_parser_token___closed__1();
 l_lean_parser_number_parser___rarg___closed__1 = _init_l_lean_parser_number_parser___rarg___closed__1();
 l_lean_parser_number_parser_view___rarg___closed__1 = _init_l_lean_parser_number_parser_view___rarg___closed__1();
 l_lean_parser_number_parser_view___rarg___closed__2 = _init_l_lean_parser_number_parser_view___rarg___closed__2();
 l_lean_parser_string__lit_parser___rarg___closed__1 = _init_l_lean_parser_string__lit_parser___rarg___closed__1();
 l_lean_parser_string__lit_parser_view___rarg___closed__1 = _init_l_lean_parser_string__lit_parser_view___rarg___closed__1();
 l_lean_parser_string__lit_parser_view___rarg___closed__2 = _init_l_lean_parser_string__lit_parser_view___rarg___closed__2();
 l_lean_parser_string__lit_view_value___closed__1 = _init_l_lean_parser_string__lit_view_value___closed__1();
 l_lean_parser_ident_parser___rarg___closed__1 = _init_l_lean_parser_ident_parser___rarg___closed__1();
 l_lean_parser_ident_parser_view___rarg___closed__1 = _init_l_lean_parser_ident_parser_view___rarg___closed__1();
 l_lean_parser_ident_parser_view___rarg___closed__2 = _init_l_lean_parser_ident_parser_view___rarg___closed__2();
 l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1 = _init_l_lean_parser_ident_parser_view___rarg___lambda__1___closed__1();
 l_lean_parser_ident_parser_view___rarg___lambda__1___closed__2 = _init_l_lean_parser_ident_parser_view___rarg___lambda__1___closed__2();
 l_lean_parser_raw__ident_parser___rarg___closed__1 = _init_l_lean_parser_raw__ident_parser___rarg___closed__1();
 l_lean_parser_indexed___rarg___closed__1 = _init_l_lean_parser_indexed___rarg___closed__1();
 l_lean_parser_indexed___rarg___lambda__1___closed__1 = _init_l_lean_parser_indexed___rarg___lambda__1___closed__1();
}
