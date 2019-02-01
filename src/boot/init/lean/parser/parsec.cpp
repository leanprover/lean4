// Lean compiler output
// Module: init.lean.parser.parsec
// Imports: init.data.to_string init.data.string.basic init.data.list.basic init.control.except init.data.repr init.lean.name init.data.dlist init.control.monad_fail init.control.combinators
#include "runtime/object.h"
#include "runtime/apply.h"
typedef lean::object obj;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#endif
obj* _l_s9___private_2142412293__s18_mk__string__result_s6___rarg(obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s12_take__while1_s6___rarg_s11___lambda__2_s7___boxed(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s3_eoi_s4___at_s4_lean_s6_parser_s9_parsec__t_s16_parse__with__eoi_s9___spec__1(obj*, obj*);
obj* _l_s4_lean_s6_parser_s9_parsec__t_s9_lookahead(obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s14_unexpected__at_s9___spec__1(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s12_take__while1_s4___at_s4_lean_s6_parser_s13_monad__parsec_s3_num_s9___spec__1_s6___rarg(obj*, obj*);
obj* _l_s4_lean_s6_parser_s9_parsec__t_s11_alternative_s6___rarg_s11___lambda__2(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s4_lean_s6_parser_s13_monad__parsec_s6___rarg(obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_lower_s6___rarg(obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s3_try(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s3_any(obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s11_take__until(obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s7_satisfy(obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s5_upper_s9___spec__1_s6___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s17_take__while__cont_s4___at_s4_lean_s6_parser_s13_monad__parsec_s12_take__until1_s9___spec__4(obj*, obj*, obj*);
obj* _l_s8_function_s4_comp_s6___rarg(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s11_take__while_s4___at_s4_lean_s6_parser_s13_monad__parsec_s11_take__until_s9___spec__1(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s10_many1__aux_s6___main_s6___rarg_s11___lambda__3(obj*, obj*);
obj* _l_s4_lean_s6_parser_s9_parsec__t_s3_run_s6___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s9_parsec__t;
obj* _l_s6_string_s7_to__nat(obj*);
obj* _l_s4_lean_s6_parser_s9_parsec__t_s5_monad_s6___rarg_s12___lambda__11(obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s17_not__followed__by_s9___spec__1_s6___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s4_cond(obj*, obj*);
obj* _l_s9_except__t_s5_monad_s6___rarg_s11___lambda__8(obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s8_sep__by1_s6___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s4_many(obj*, obj*);
obj* _l_s4_lean_s6_parser_s9_parsec__t_s4_bind_s6___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_many1_s6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* _l_s9___private_1695453085__s20_take__while__aux_x27_s6___main_s4___at_s4_lean_s6_parser_s13_monad__parsec_s10_whitespace_s9___spec__2_s6___rarg_s7___boxed(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_digit_s6___rarg(obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_foldl_s6___rarg_s11___lambda__1(obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s9_parsec__t_s13_bind__mk__res_s6___rarg(obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s4_curr_s6___rarg(obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s3_eoi_s6___rarg(obj*, obj*);
obj* _l_s9___private_127590107__s9_take__aux_s6___main(obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s9_observing_s6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s10_foldl__aux_s6___main_s6___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s6_parsec_s7_message_s10_to__string_s6___rarg_s11___closed__3;
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s3_num_s9___spec__3(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s4_lean_s6_parser_s13_monad__parsec_s6___rarg_s11___lambda__1(obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s3_num_s9___spec__2_s6___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s10_many1__aux_s6___main_s6___rarg_s11___lambda__1(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s10_left__over_s6___rarg(obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s4_many_s6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s14_many1__aux_x27(obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s3_str_s6___rarg(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s16_take__while1_x27_s6___rarg(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s5_lower_s9___spec__1(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s6_parsec_s5_parse_s6___rarg(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s12_take__while1_s6___rarg(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s14_longest__match_s9___spec__1(obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s3_eoi_s9___spec__1_s6___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s9_parsec__t_s16_has__monad__lift(obj*);
obj* _l_s4_lean_s6_parser_s9_parsec__t_s5_monad_s6___rarg_s12___lambda__14(obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s3_try_s6___rarg(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s9_parsec__t_s23_parse__with__left__over(obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_alpha_s6___rarg(obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s22_not__followed__by__sat(obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s8_sep__by1_s6___rarg_s11___closed__1;
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_many1(obj*, obj*);
obj* _l_s4_lean_s6_parser_s9_parsec__t_s6_orelse(obj*);
obj* _l_s4_lean_s6_parser_s6_parsec_s6_result_s7_mk__eps(obj*, obj*);
obj* _l_s4_lean_s6_parser_s9_parsec__t_s5_monad(obj*);
obj* _l_s9___private_580269747__s8_str__aux_s6___main(obj*, obj*, obj*);
obj* _l_s4_list_s6_mfoldr_s6___main_s4___at_s4_lean_s6_parser_s13_monad__parsec_s14_longest__match_s9___spec__2(obj*, obj*);
obj* _l_s4_lean_s6_parser_s9_parsec__t_s3_try_s6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s6_hidden_s6___rarg_s11___lambda__2(obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s6_parsec_s7_message_s4_text_s6___rarg_s11___closed__2;
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s3_any_s9___spec__1_s6___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_label_s6___rarg(obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s6_ensure_s6___rarg(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s2_ch_s6___rarg_s11___lambda__1_s7___boxed(obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s14_many1__aux_x27_s6___main_s6___rarg(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s3_num_s6___rarg(obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s11_take__until_s6___rarg(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s6_parsec_s8_expected_s10_to__string_s6___main(obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s17_not__followed__by_s9___spec__1(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s17_take__while__cont_s6___rarg_s11___lambda__1(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s6_ensure_s6___rarg_s11___lambda__1_s11___closed__1;
obj* _l_s4_lean_s6_parser_s6_parsec_s7_message_s4_text_s6___rarg(obj*);
obj* _l_s4_lean_s6_parser_s9_parsec__t_s7_failure(obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s10_eoi__error_s6___rarg(obj*);
obj* _l_s4_list_s6_mfoldr_s6___main_s4___at_s4_lean_s6_parser_s13_monad__parsec_s14_longest__match_s9___spec__2_s6___rarg_s11___lambda__4(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s9_parsec__t_s5_monad_s6___rarg_s12___lambda__12(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s16_take__while1_x27(obj*, obj*);
obj* _l_s9___private_1695453085__s20_take__while__aux_x27_s6___rarg(obj*, obj*, unsigned char, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s10_foldl__aux_s6___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s8_sep__by1_s6___rarg_s11___lambda__1(obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s10_foldl__aux(obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s2_ch_s6___rarg(obj*, obj*, unsigned);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s3_any_s6___rarg(obj*, obj*);
obj* _l_s4_lean_s6_parser_s6_parsec_s6_result_s7_mk__eps_s6___rarg_s11___closed__1;
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s8_fix__aux_s6___main_s6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* _l_s9___private_31565857__s16_take__while__aux_s6___main_s4___at_s4_lean_s6_parser_s13_monad__parsec_s12_take__until1_s9___spec__5_s6___rarg(obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s17_take__while__cont_s4___at_s4_lean_s6_parser_s13_monad__parsec_s12_take__until1_s9___spec__4_s6___rarg_s11___lambda__1(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s3_fix(obj*, obj*);
obj* _l_s4_lean_s6_parser_s9_parsec__t_s5_monad_s6___rarg(obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_foldr_s6___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s9_parsec__t_s12_try__mk__res(obj*, obj*);
obj* _l_s4_lean_s6_parser_s9_parsec__t_s23_parse__with__left__over_s6___rarg_s11___lambda__3(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s9_parsec__t_s16_parse__with__eoi_s9___spec__2(obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s2_ch(obj*, obj*);
obj* _l_s4_lean_s6_parser_s9_parsec__t_s6_labels_s6___rarg_s11___lambda__1(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s6_parsec_s7_message_s10_to__string(obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s7_satisfy_s6___rarg_s11___lambda__1(obj*, unsigned, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s17_not__followed__by_s6___rarg_s11___lambda__1(obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s14_many1__aux_x27_s6___main(obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s3_fix_s6___rarg_s11___lambda__1(obj*, obj*, obj*, obj*);
obj* _l_s4_char_s11_quote__core(unsigned);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s9_lookahead_s6___rarg_s11___lambda__1(obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_alpha(obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s3_eoi_s9___spec__1(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s11_take__while_s4___at_s4_lean_s6_parser_s13_monad__parsec_s11_take__until_s9___spec__1_s6___rarg_s11___lambda__1(obj*, obj*);
obj* _l_s9___private_127590107__s9_take__aux_s6___main_s6___rarg(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s22_not__followed__by__sat_s9___spec__1_s6___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s14_longest__match(obj*, obj*);
obj* _l_s4_true_s9_decidable;
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s8_many_x27_s6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_upper_s6___rarg_s11___lambda__1(obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s17_take__while__cont_s4___at_s4_lean_s6_parser_s13_monad__parsec_s12_take__until1_s9___spec__4_s6___rarg_s7___boxed(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s9_parsec__t_s3_run_s4___at_s4_lean_s6_parser_s6_parsec_s5_parse_s9___spec__1(obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s16_take__while1_x27_s9___spec__2_s6___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s15_take__while_x27_s4___at_s4_lean_s6_parser_s13_monad__parsec_s10_whitespace_s9___spec__1_s6___rarg(obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s12_take__while1_s9___spec__2_s6___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s3_eoi(obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s6_ensure_s9___spec__1_s6___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s9___private_1695453085__s20_take__while__aux_x27(obj*);
obj* _l_s4_lean_s6_parser_s9_parsec__t_s3_run_s6___rarg_s11___lambda__1(obj*, obj*);
obj* _l_s5_mjoin_s6___rarg_s11___closed__1;
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s3_num_s6___rarg_s11___closed__1;
obj* _l_s4_lean_s6_parser_s9_parsec__t_s23_parse__with__left__over_s6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s20_monad__parsec__trans_s6___rarg_s11___lambda__2(obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s5_upper_s9___spec__1(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_digit(obj*, obj*);
obj* _l_s4_lean_s6_parser_s9_parsec__t_s13_monad__except(obj*);
obj* _l_s4_lean_s6_parser_s9_parsec__t_s15_orelse__mk__res_s6___rarg(obj*, obj*);
obj* _l_s9___private_31565857__s16_take__while__aux_s6___main_s4___at_s4_lean_s6_parser_s13_monad__parsec_s11_take__until_s9___spec__2(obj*);
obj* _l_s9___private_31565857__s16_take__while__aux_s6___main_s4___at_s4_lean_s6_parser_s13_monad__parsec_s3_num_s9___spec__5_s6___rarg(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s3_any_s9___spec__2(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s9_remaining_s6___rarg(obj*, obj*);
obj* _l_s4_list_s12_has__dec__eq_s6___main_s4___at_s4_lean_s6_parser_s6_parsec_s7_message_s4_text_s9___spec__1(obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_foldr(obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s8_fix__aux_s6___main_s9___spec__1_s6___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s5_digit_s9___spec__1(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_foldl_s6___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s6_ensure_s9___spec__1(obj*, obj*, obj*);
obj* _l_s2_id_s6___rarg(obj*);
obj* _l_s4_lean_s6_parser_s9_parsec__t_s5_parse(obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s4_cond_s6___rarg_s11___lambda__1(obj*, obj*, unsigned char);
obj* _l_s4_lean_s6_parser_s9_parsec__t_s16_parse__with__eoi_s6___rarg_s11___lambda__1(obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s9_parsec__t_s3_run_s4___at_s4_lean_s6_parser_s9_parsec__t_s16_parse__with__eoi_s9___spec__3_s6___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s9___private_1695453085__s20_take__while__aux_x27_s6___main_s4___at_s4_lean_s6_parser_s13_monad__parsec_s10_whitespace_s9___spec__2(obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s7_satisfy_s9___spec__1(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s14_unexpected__at(obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s14_unexpected__at_s6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s3_eoi_s4___at_s4_lean_s6_parser_s9_parsec__t_s16_parse__with__eoi_s9___spec__1_s6___rarg(obj*, obj*);
obj* _l_s4_lean_s6_parser_s9_parsec__t_s3_run_s4___at_s4_lean_s6_parser_s9_parsec__t_s23_parse__with__left__over_s9___spec__1(obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s12_take__while1(obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s22_not__followed__by__sat_s6___rarg_s11___lambda__1(obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s6_lexeme_s6___rarg(obj*, obj*, obj*, obj*);
unsigned char _l_s4_char_s9_is__digit(unsigned);
obj* _l_s4_lean_s6_parser_s6_parsec_s5_parse(obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s4_cond_s6___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s7_satisfy_s6___rarg_s11___lambda__2(obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_lower_s6___rarg_s11___lambda__1(obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s9_parsec__t_s9_lookahead_s6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s10_unexpected(obj*, obj*);
obj* _l_s4_lean_s6_parser_s9_parsec__t_s6_labels(obj*);
obj* _l_s4_lean_s6_parser_s9_parsec__t_s5_monad_s6___rarg_s11___lambda__8(obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s9_parsec__t_s3_try_s6___rarg_s11___lambda__1(obj*, obj*);
obj* _l_s4_lean_s6_parser_s6_parsec_s9_has__lift(obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s7_satisfy_s6___rarg_s11___lambda__1_s7___boxed(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s16_take__while1_x27_s9___spec__1_s6___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s6_string_s8_iterator_s4_curr_s7___boxed(obj*);
obj* _l_s4_lean_s6_parser_s6_parsec_s7_message_s10_to__string_s6___rarg_s11___closed__1;
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s4_cond_s6___rarg_s11___lambda__1_s7___boxed(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s9_parsec__t_s5_monad_s6___rarg_s11___lambda__1(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s9_parsec__t_s4_bind_s6___rarg_s11___lambda__1(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s9_parsec__t_s5_monad_s6___rarg_s11___lambda__5(obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_upper(obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s6___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s9_str__core(obj*, obj*);
obj* _l_s9___private_2038417741__s20_mk__consumed__result(obj*);
obj* _l_s4_lean_s6_parser_s9_parsec__t_s16_has__monad__lift_s6___rarg_s11___lambda__1(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s9_parsec__t_s6_expect(obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_digit_s6___rarg_s11___lambda__1(obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s9_parsec__t_s3_try(obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s3_eoi_s6___rarg_s11___lambda__1_s11___closed__1;
obj* _l_s4_list_s9_repr__aux_s6___main_s6___rarg_s11___closed__1;
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s12_take__while1_s6___rarg_s11___lambda__1(obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s10_foldl__aux_s6___main(obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s9_lookahead_s6___rarg(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s9_observing_s6___rarg_s11___lambda__1(obj*, obj*);
obj* _l_s6_option_s13_get__or__else_s6___main_s6___rarg(obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s7_sep__by_s6___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s17_not__followed__by(obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s6_hidden_s6___rarg(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s6_hidden_s6___rarg_s11___lambda__1(obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s9_lookahead(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s10_whitespace_s6___rarg(obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s10_foldr__aux_s6___main(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s20_monad__parsec__trans_s6___rarg(obj*, obj*, obj*);
obj* _l_s9___private_31565857__s16_take__while__aux_s6___main_s4___at_s4_lean_s6_parser_s13_monad__parsec_s12_take__until1_s9___spec__5(obj*);
obj* _l_s4_lean_s6_parser_s9_parsec__t_s23_parse__with__left__over_s6___rarg_s11___lambda__4(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s20_monad__parsec__trans(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s16_take__while1_x27_s6___rarg_s11___lambda__1(obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s6_ensure_s6___rarg_s11___lambda__1_s11___closed__2;
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s3_eoi_s6___rarg_s11___lambda__1(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s16_take__while1_x27_s9___spec__2(obj*, obj*, obj*);
obj* _l_s9___private_31565857__s16_take__while__aux_s6___main_s4___at_s4_lean_s6_parser_s13_monad__parsec_s3_num_s9___spec__5(obj*);
obj* _l_s4_lean_s6_parser_s9_parsec__t_s5_monad_s6___rarg_s12___lambda__13(obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s5_alpha_s9___spec__1(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s9_parsec__t_s15_orelse__mk__res(obj*, obj*);
obj* _l_s4_lean_s6_parser_s6_parsec_s6_result_s7_mk__eps_s6___rarg(obj*, obj*);
obj* _l_s4_lean_s6_parser_s9_parsec__t_s12_try__mk__res_s6___rarg(obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s11_take__while_s6___rarg_s11___lambda__1(obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s8_fix__aux(obj*, obj*);
obj* _l_s4_lean_s6_parser_s20_monad__parsec__trans_s6___rarg_s11___lambda__3(obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s10_left__over_s6___rarg_s11___lambda__1(obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s14_unexpected__at_s9___spec__1_s6___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s12_take__until1(obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s3_num_s9___spec__3_s6___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s9_str__core_s6___rarg(obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s6_ensure_s6___rarg_s11___lambda__1(obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s10_many1__aux_s6___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
unsigned char _l_s4_char_s9_is__alpha(unsigned);
unsigned char _l_s4_char_s9_is__upper(unsigned);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s5_alpha_s9___spec__2_s6___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s3_any_s6___rarg_s11___lambda__1(obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s9_lookahead_s6___rarg_s11___closed__1;
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s17_not__followed__by_s6___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s9___private_2142412293__s18_mk__string__result(obj*);
obj* _l_s4_list_s3_zip_s6___rarg_s11___lambda__1(obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s15_take__while_x27_s6___rarg(obj*, obj*);
obj* _l_s4_lean_s6_parser_s9_parsec__t_s5_parse_s6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_char_s9_has__repr_s11___closed__1;
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s10_unexpected_s9___spec__1(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s9_parsec__t_s3_run(obj*);
obj* _l_s4_lean_s6_parser_s9_parsec__t_s9_lookahead_s6___rarg_s11___lambda__1(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s9_parsec__t_s5_monad_s6___rarg_s11___lambda__9(obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s3_eoi_s4___at_s4_lean_s6_parser_s9_parsec__t_s16_parse__with__eoi_s9___spec__1_s6___rarg_s11___lambda__1(obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s9_parsec__t_s16_parse__with__eoi_s6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s9_parsec__t_s5_monad_s6___rarg_s11___lambda__6(obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s14_many1__aux_x27_s6___rarg(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s6_parsec_s8_expected_s10_to__string(obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s9_parsec__t_s16_parse__with__eoi_s9___spec__2_s6___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s4_lean_s6_parser_s13_monad__parsec_s6___rarg_s11___lambda__2(obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s9_parsec__t_s13_monad__except_s6___rarg_s11___lambda__3(obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s9_parsec__t_s11_monad__fail(obj*);
obj* _l_s4_lean_s6_parser_s9_parsec__t_s3_run_s4___at_s4_lean_s6_parser_s9_parsec__t_s16_parse__with__eoi_s9___spec__3(obj*);
obj* _l_s4_lean_s6_parser_s9_parsec__t_s11_alternative(obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s8_fix__aux_s6___main(obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s6_lexeme(obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_lower(obj*, obj*);
obj* _l_s4_lean_s6_parser_s9_parsec__t_s13_bind__mk__res(obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s7_satisfy_s9___spec__1_s6___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
unsigned char _l_s6_string_s9_is__empty(obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_foldl(obj*, obj*);
obj* _l_s4_lean_s6_parser_s9_parsec__t_s13_monad__except_s6___rarg_s11___lambda__2_s7___boxed(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s3_any_s9___spec__2_s6___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s6_ensure(obj*, obj*);
obj* _l_s9___private_1695453085__s20_take__while__aux_x27_s6___main(obj*);
obj* _l_s4_lean_s6_parser_s9_parsec__t_s3_run_s4___at_s4_lean_s6_parser_s9_parsec__t_s23_parse__with__left__over_s9___spec__1_s6___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s6_hidden_s6___rarg_s11___closed__1;
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s2_ch_s9___spec__2_s6___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s6_string_s11_intercalate(obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s12_take__while1_s6___rarg_s11___lambda__2(obj*, obj*, unsigned);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s6_labels_s6___rarg(obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s16_take__while1_x27_s9___spec__1(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s11_take__while(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s9_parsec__t_s4_pure_s6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s9_parsec__t_s11_alternative_s6___rarg_s11___lambda__1(obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s10_foldl__aux_s6___main_s6___rarg_s11___lambda__1(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s5_digit_s9___spec__2_s6___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s14_longest__match_s6___rarg_s11___lambda__1(obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s5_upper_s9___spec__2_s6___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s10_many1__aux_s6___main_s6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s10_unexpected_s9___spec__1_s6___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s15_take__while_x27_s4___at_s4_lean_s6_parser_s13_monad__parsec_s10_whitespace_s9___spec__1(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s17_take__while__cont_s4___at_s4_lean_s6_parser_s13_monad__parsec_s3_num_s9___spec__4_s6___rarg_s7___boxed(obj*, obj*);
obj* _l_s4_lean_s6_parser_s9_parsec__t_s5_monad_s6___rarg_s11___lambda__3(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_label(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s9_parsec__t_s6_orelse_s6___rarg_s11___lambda__1(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s9_parsec__t_s6_labels_s6___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s3_str(obj*, obj*);
obj* _l_s4_lean_s6_format_s2_be_s6___main_s11___closed__1;
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s10_many1__aux_s6___main(obj*);
obj* _l_s4_lean_s6_parser_s20_monad__parsec__trans_s6___rarg_s11___lambda__1(obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s6_parsec_s8_expected_s10_to__string_s6___main_s11___closed__1;
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s10_foldr__aux_s6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s12_take__until1_s6___rarg(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_upper_s6___rarg(obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s7_satisfy_s9___spec__2_s6___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s9___private_31565857__s16_take__while__aux_s6___main(obj*);
obj* _l_s6_string_s4_join_s11___closed__1;
obj* _l_s4_lean_s6_parser_s9_parsec__t_s4_pure(obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s5_lower_s9___spec__2_s6___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s6___rarg_s11___lambda__1(obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s8_fix__aux_s6___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s9_parsec__t_s13_monad__except_s6___rarg_s11___lambda__4(obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s17_not__followed__by_s6___rarg_s11___lambda__2(obj*, obj*, obj*, obj*, obj*, unsigned char);
obj* _l_s4_lean_s6_parser_s9_parsec__t_s4_bind(obj*);
obj* _l_s4_lean_s6_parser_s6_parsec_s7_message_s4_text_s6___rarg_s11___closed__3;
obj* _l_s4_list_s6_mfoldr_s6___main_s4___at_s4_lean_s6_parser_s13_monad__parsec_s14_longest__match_s9___spec__2_s6___rarg_s11___lambda__3(obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s12_take__while1_s4___at_s4_lean_s6_parser_s13_monad__parsec_s3_num_s9___spec__1_s6___rarg_s11___lambda__1(obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s4_curr_s6___rarg_s11___closed__1;
obj* _l_s4_lean_s6_parser_s9_parsec__t_s5_merge_s6___rarg(obj*, obj*);
obj* _l_s4_lean_s6_parser_s9_parsec__t_s11_monad__fail_s6___rarg_s11___closed__1;
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s9_remaining(obj*, obj*);
obj* _l_s6_string_s12_line__column(obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s4_take(obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s14_longest__match_s9___spec__1_s6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s6_labels_s6___rarg_s11___lambda__1(obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s9_parsec__t_s16_parse__with__eoi_s6___rarg_s11___lambda__2(obj*, obj*, obj*);
unsigned char _l_s4_char_s9_is__lower(unsigned);
obj* _l_s9___private_127590107__s9_take__aux_s6___rarg(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s5_lower_s9___spec__1_s6___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s8_fix__aux_s6___main_s9___spec__1(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s11_take__while_s4___at_s4_lean_s6_parser_s13_monad__parsec_s11_take__until_s9___spec__1_s6___rarg(obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s8_many_x27(obj*, obj*);
obj* _l_s9___private_31565857__s16_take__while__aux(obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s17_take__while__cont_s4___at_s4_lean_s6_parser_s13_monad__parsec_s3_num_s9___spec__4(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s15_take__while_x27_s4___at_s4_lean_s6_parser_s13_monad__parsec_s10_whitespace_s9___spec__1_s6___rarg_s11___lambda__1(obj*);
obj* _l_s4_lean_s6_parser_s9_parsec__t_s3_eps(obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s15_take__while_x27_s4___at_s4_lean_s6_parser_s13_monad__parsec_s10_whitespace_s9___spec__1_s6___rarg_s11___closed__1;
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s12_take__while1_s4___at_s4_lean_s6_parser_s13_monad__parsec_s12_take__until1_s9___spec__1(obj*, obj*);
obj* _l_s4_lean_s6_parser_s6_parsec_s15_has__to__string(obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s9_many1_x27(obj*, obj*);
obj* _l_s4_list_s6_mfoldr_s6___main_s4___at_s4_lean_s6_parser_s13_monad__parsec_s14_longest__match_s9___spec__2_s6___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s12_take__until1_s9___spec__2(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s9_str__core_s6___rarg_s11___lambda__1(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s9_remaining_s6___rarg_s11___closed__1;
obj* _l_s4_lean_s6_parser_s4_lean_s6_parser_s13_monad__parsec(obj*, obj*);
obj* _l_s3_nat_s4_repr(obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s9_observing(obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s10_foldr__aux(obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s17_take__while__cont(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s9_parsec__t_s5_monad_s6___rarg_s12___lambda__10(obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s3_fix_s6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s9_parsec__t_s3_eps_s6___rarg(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s12_take__while1_s4___at_s4_lean_s6_parser_s13_monad__parsec_s12_take__until1_s9___spec__1_s6___rarg_s11___lambda__1(obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s9_parsec__t_s5_merge(obj*);
obj* _l_s9___private_31565857__s16_take__while__aux_s6___main_s6___rarg(obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error(obj*, obj*, obj*);
obj* _l_s4_list_s6_append_s6___main_s6___rarg(obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s9_many1_x27_s6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s3_pos_s6___rarg(obj*, obj*);
obj* _l_s9___private_2038417741__s20_mk__consumed__result_s6___rarg(unsigned char, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s15_take__while_x27(obj*, obj*, obj*);
unsigned char _l_s4_char_s14_is__whitespace(unsigned);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s5_digit_s9___spec__1_s6___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s10_left__over_s6___rarg_s11___closed__1;
obj* _l_s4_lean_s6_parser_s9_parsec__t_s13_monad__except_s6___rarg_s11___lambda__2(obj*, unsigned char, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s10_eoi__error(obj*, obj*);
obj* _l_s4_lean_s6_parser_s9_parsec__t_s7_failure_s6___rarg(obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s17_not__followed__by_s6___rarg_s11___lambda__2_s7___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s3_try_s6___rarg_s11___closed__1;
obj* _l_s4_lean_s6_parser_s6_parsec;
obj* _l_s9___private_127590107__s9_take__aux(obj*);
obj* _l_s4_lean_s6_parser_s9_parsec__t_s11_monad__fail_s6___rarg(obj*, obj*);
obj* _l_s4_lean_s6_parser_s9_parsec__t_s6_orelse_s6___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s9_parsec__t_s6_orelse_s6___rarg_s11___lambda__2(obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s4_take_s6___rarg(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s9_parsec__t_s5_monad_s6___rarg_s11___lambda__7(obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s12_take__while1_s9___spec__1(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s2_ch_s6___rarg_s7___boxed(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s22_not__followed__by__sat_s6___rarg(obj*, obj*, obj*);
obj* _l_s4_list_s6_mfoldr_s6___main_s4___at_s4_lean_s6_parser_s13_monad__parsec_s14_longest__match_s9___spec__2_s6___rarg_s11___closed__1;
obj* _l_s4_lean_s6_parser_s6_parsec_s7_message_s10_to__string_s6___rarg(obj*);
obj* _l_s4_lean_s6_parser_s9_parsec__t_s3_run_s4___at_s4_lean_s6_parser_s6_parsec_s5_parse_s9___spec__1_s6___rarg(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s10_many1__aux(obj*, obj*);
obj* _l_s4_lean_s6_parser_s9_parsec__t_s15_labels__mk__res(obj*, obj*);
obj* _l_s4_lean_s6_parser_s9_parsec__t_s13_monad__except_s6___rarg(obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s7_satisfy_s9___spec__2(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s3_any_s9___spec__1(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_alpha_s6___rarg_s11___lambda__1(obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s5_lower_s9___spec__2(obj*, obj*, obj*);
obj* _l_s4_list_s6_mfoldr_s6___main_s4___at_s4_lean_s6_parser_s13_monad__parsec_s14_longest__match_s9___spec__2_s6___rarg_s11___lambda__2(obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s10_many1__aux_s6___main_s6___rarg_s11___lambda__2(obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s6_parsec_s8_position;
obj* _l_s4_lean_s6_parser_s6_parsec_s7_message_s4_text(obj*);
obj* _l_s4_lean_s6_parser_s9_parsec__t_s23_parse__with__left__over_s6___rarg_s11___lambda__2(obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s12_take__while1_s9___spec__2(obj*, obj*, obj*);
obj* _l_s9___private_1695453085__s20_take__while__aux_x27_s6___main_s4___at_s4_lean_s6_parser_s13_monad__parsec_s10_whitespace_s9___spec__2_s6___rarg(obj*, unsigned char, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s10_eoi__error_s6___rarg_s11___closed__1;
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s17_take__while__cont_s6___rarg(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s12_take__while1_s9___spec__1_s6___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s3_try_s6___rarg_s11___lambda__1(obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s2_ch_s9___spec__1_s6___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s14_longest__match_s6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* _l_s9___private_2038417741__s20_mk__consumed__result_s6___rarg_s7___boxed(obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s6_labels(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s2_ch_s6___rarg_s11___lambda__1(obj*, obj*, unsigned, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s7_sep__by(obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_foldr_s6___rarg_s11___lambda__1(obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s9_parsec__t_s16_parse__with__eoi_s6___rarg_s11___lambda__3(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s2_ch_s9___spec__1(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s10_foldr__aux_s6___main_s6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s10_whitespace(obj*, obj*);
obj* _l_s9___private_580269747__s8_str__aux(obj*, obj*, obj*);
obj* _l_s9___private_1695453085__s20_take__while__aux_x27_s6___main_s6___rarg(obj*, obj*, unsigned char, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s8_fix__aux_s6___main_s6___rarg_s11___closed__1;
obj* _l_s9___private_1695453085__s20_take__while__aux_x27_s6___main_s6___rarg_s7___boxed(obj*, obj*, obj*, obj*);
obj* _l_s5_dlist_s8_to__list_s6___main_s6___rarg(obj*);
obj* _l_s9___private_1695453085__s20_take__while__aux_x27_s6___rarg_s7___boxed(obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s9_parsec__t_s6_expect_s6___rarg(obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s12_take__while1_s4___at_s4_lean_s6_parser_s13_monad__parsec_s12_take__until1_s9___spec__1_s6___rarg(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s3_num(obj*, obj*);
obj* _l_s4_lean_s6_parser_s9_parsec__t_s16_parse__with__eoi(obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s10_left__over(obj*, obj*, obj*);
obj* _l_s4_list_s6_mfoldr_s6___main_s4___at_s4_lean_s6_parser_s13_monad__parsec_s14_longest__match_s9___spec__2_s6___rarg_s11___lambda__1(obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s3_num_s9___spec__2(obj*, obj*, obj*);
obj* _l_s9___private_31565857__s16_take__while__aux_s6___main_s4___at_s4_lean_s6_parser_s13_monad__parsec_s11_take__until_s9___spec__2_s6___rarg(obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s14_longest__match_s6___rarg_s11___lambda__2(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s9___private_31565857__s16_take__while__aux_s6___rarg(obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s12_take__until1_s9___spec__2_s6___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s17_take__while__cont_s4___at_s4_lean_s6_parser_s13_monad__parsec_s3_num_s9___spec__4_s6___rarg(obj*, unsigned);
obj* _l_s4_lean_s6_parser_s9_parsec__t_s13_monad__except_s6___rarg_s11___lambda__1(obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s9_parsec__t_s11_alternative_s6___rarg(obj*, obj*);
obj* _l_s4_lean_s6_parser_s6_parsec_s7_message_s4_text_s6___rarg_s11___closed__1;
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s10_unexpected_s6___rarg(obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s3_pos(obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s7_satisfy_s6___rarg(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s3_pos_s6___rarg_s11___closed__1;
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s5_alpha_s9___spec__1_s6___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s17_not__followed__by_s6___rarg_s11___lambda__3(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s9_parsec__t_s5_monad_s6___rarg_s11___lambda__4(obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s12_take__until1_s9___spec__3_s6___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s5_upper_s9___spec__2(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s8_sep__by1(obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s2_ch_s9___spec__2(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s6_parsec_s7_message_s10_to__string_s6___rarg_s11___closed__2;
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s6_hidden(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s5_digit_s9___spec__2(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s11_take__while_s6___rarg(obj*, obj*);
obj* _l_s4_lean_s6_parser_s9_parsec__t_s7_failure_s6___rarg_s11___closed__1;
obj* _l_s4_lean_s6_parser_s9_parsec__t_s16_has__monad__lift_s6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s17_take__while__cont_s4___at_s4_lean_s6_parser_s13_monad__parsec_s3_num_s9___spec__4_s6___rarg_s11___lambda__1(obj*, obj*);
obj* _l_s4_lean_s6_parser_s9_parsec__t_s23_parse__with__left__over_s6___rarg_s11___lambda__1(obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s12_take__while1_s4___at_s4_lean_s6_parser_s13_monad__parsec_s3_num_s9___spec__1(obj*, obj*);
obj* _l_s4_lean_s6_parser_s17_monad__parsec_x27;
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s4_curr(obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s5_alpha_s9___spec__2(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s10_parsec_x27;
obj* _l_s4_lean_s6_parser_s9_parsec__t_s15_labels__mk__res_s6___rarg(obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s15_take__while_x27_s6___rarg_s11___lambda__1(obj*, obj*);
obj* _l_s4_lean_s6_parser_s9_parsec__t_s5_monad_s6___rarg_s11___lambda__2(obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s9_except__t_s4_lift_s6___rarg_s11___closed__1;
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s12_take__until1_s9___spec__3(obj*, obj*, obj*);
obj* _l_s6_string_s5_quote(obj*);
obj* _l_s5_dlist_s9_singleton_s6___rarg(obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s17_take__while__cont_s4___at_s4_lean_s6_parser_s13_monad__parsec_s12_take__until1_s9___spec__4_s6___rarg(obj*, obj*, unsigned);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s22_not__followed__by__sat_s9___spec__1(obj*, obj*, obj*);
obj* _init__l_s4_lean_s6_parser_s6_parsec_s8_position() {
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _l_s4_lean_s6_parser_s6_parsec_s8_expected_s10_to__string_s6___main(obj* x_0) {
{

if (lean::obj_tag(x_0) == 0)
{
obj* x_2; 
lean::dec(x_0);
x_2 = _l_s6_string_s4_join_s11___closed__1;
lean::inc(x_2);
return x_2;
}
else
{
obj* x_4; obj* x_6; 
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
lean::dec(x_0);
if (lean::obj_tag(x_6) == 0)
{

lean::dec(x_6);
return x_4;
}
else
{
obj* x_10; obj* x_12; 
x_10 = lean::cnstr_get(x_6, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_6, 1);
lean::inc(x_12);
if (lean::obj_tag(x_12) == 0)
{
obj* x_16; obj* x_17; obj* x_18; 
lean::dec(x_6);
lean::dec(x_12);
x_16 = _l_s4_lean_s6_parser_s6_parsec_s8_expected_s10_to__string_s6___main_s11___closed__1;
x_17 = lean::string_append(x_4, x_16);
x_18 = lean::string_append(x_17, x_10);
lean::dec(x_10);
return x_18;
}
else
{
obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
lean::dec(x_10);
lean::dec(x_12);
x_22 = _l_s4_list_s9_repr__aux_s6___main_s6___rarg_s11___closed__1;
x_23 = lean::string_append(x_4, x_22);
x_24 = _l_s4_lean_s6_parser_s6_parsec_s8_expected_s10_to__string_s6___main(x_6);
x_25 = lean::string_append(x_23, x_24);
lean::dec(x_24);
return x_25;
}
}
}
}
}
obj* _init__l_s4_lean_s6_parser_s6_parsec_s8_expected_s10_to__string_s6___main_s11___closed__1() {
{
obj* x_0; 
x_0 = lean::mk_string(" or ");
return x_0;
}
}
obj* _l_s4_lean_s6_parser_s6_parsec_s8_expected_s10_to__string(obj* x_0) {
{
obj* x_1; 
x_1 = _l_s4_lean_s6_parser_s6_parsec_s8_expected_s10_to__string_s6___main(x_0);
return x_1;
}
}
obj* _l_s4_lean_s6_parser_s6_parsec_s7_message_s4_text_s6___rarg(obj* x_0) {
{
obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_8; obj* x_9; obj* x_12; 
x_1 = lean::cnstr_get(x_0, 1);
lean::inc(x_1);
x_3 = _l_s6_string_s4_join_s11___closed__1;
x_4 = lean::string_dec_eq(x_1, x_3);
x_5 = lean::cnstr_get(x_0, 2);
lean::inc(x_5);
lean::dec(x_0);
x_8 = _l_s5_dlist_s8_to__list_s6___main_s6___rarg(x_5);
x_9 = lean::box(0);
lean::inc(x_9);
lean::inc(x_8);
x_12 = _l_s4_list_s12_has__dec__eq_s6___main_s4___at_s4_lean_s6_parser_s6_parsec_s7_message_s4_text_s9___spec__1(x_8, x_9);
if (lean::obj_tag(x_4) == 0)
{
obj* x_14; obj* x_16; obj* x_19; 
lean::dec(x_4);
x_14 = _l_s4_lean_s6_parser_s6_parsec_s7_message_s4_text_s6___rarg_s11___closed__1;
lean::inc(x_14);
x_16 = lean::string_append(x_14, x_1);
lean::dec(x_1);
lean::inc(x_9);
x_19 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_19, 0, x_16);
lean::cnstr_set(x_19, 1, x_9);
if (lean::obj_tag(x_12) == 0)
{
obj* x_21; obj* x_22; obj* x_24; obj* x_26; obj* x_27; obj* x_28; obj* x_30; 
lean::dec(x_12);
x_21 = _l_s4_lean_s6_parser_s6_parsec_s8_expected_s10_to__string_s6___main(x_8);
x_22 = _l_s4_lean_s6_parser_s6_parsec_s7_message_s4_text_s6___rarg_s11___closed__2;
lean::inc(x_22);
x_24 = lean::string_append(x_22, x_21);
lean::dec(x_21);
x_26 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_26, 0, x_24);
lean::cnstr_set(x_26, 1, x_9);
x_27 = _l_s4_list_s6_append_s6___main_s6___rarg(x_19, x_26);
x_28 = _l_s4_lean_s6_format_s2_be_s6___main_s11___closed__1;
lean::inc(x_28);
x_30 = _l_s6_string_s11_intercalate(x_28, x_27);
return x_30;
}
else
{
obj* x_33; obj* x_34; obj* x_36; 
lean::dec(x_8);
lean::dec(x_12);
x_33 = _l_s4_list_s6_append_s6___main_s6___rarg(x_19, x_9);
x_34 = _l_s4_lean_s6_format_s2_be_s6___main_s11___closed__1;
lean::inc(x_34);
x_36 = _l_s6_string_s11_intercalate(x_34, x_33);
return x_36;
}
}
else
{

lean::dec(x_1);
lean::dec(x_4);
if (lean::obj_tag(x_12) == 0)
{
obj* x_40; obj* x_41; obj* x_43; obj* x_46; obj* x_47; obj* x_48; obj* x_50; 
lean::dec(x_12);
x_40 = _l_s4_lean_s6_parser_s6_parsec_s8_expected_s10_to__string_s6___main(x_8);
x_41 = _l_s4_lean_s6_parser_s6_parsec_s7_message_s4_text_s6___rarg_s11___closed__2;
lean::inc(x_41);
x_43 = lean::string_append(x_41, x_40);
lean::dec(x_40);
lean::inc(x_9);
x_46 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_46, 0, x_43);
lean::cnstr_set(x_46, 1, x_9);
x_47 = _l_s4_list_s6_append_s6___main_s6___rarg(x_9, x_46);
x_48 = _l_s4_lean_s6_format_s2_be_s6___main_s11___closed__1;
lean::inc(x_48);
x_50 = _l_s6_string_s11_intercalate(x_48, x_47);
return x_50;
}
else
{
obj* x_54; 
lean::dec(x_8);
lean::dec(x_9);
lean::dec(x_12);
x_54 = _l_s4_lean_s6_parser_s6_parsec_s7_message_s4_text_s6___rarg_s11___closed__3;
lean::inc(x_54);
return x_54;
}
}
}
}
obj* _init__l_s4_lean_s6_parser_s6_parsec_s7_message_s4_text_s6___rarg_s11___closed__1() {
{
obj* x_0; 
x_0 = lean::mk_string("unexpected ");
return x_0;
}
}
obj* _init__l_s4_lean_s6_parser_s6_parsec_s7_message_s4_text_s6___rarg_s11___closed__2() {
{
obj* x_0; 
x_0 = lean::mk_string("expected ");
return x_0;
}
}
obj* _init__l_s4_lean_s6_parser_s6_parsec_s7_message_s4_text_s6___rarg_s11___closed__3() {
{
obj* x_0; obj* x_2; obj* x_3; obj* x_4; 
x_0 = lean::box(0);
lean::inc(x_0);
x_2 = _l_s4_list_s6_append_s6___main_s6___rarg(x_0, x_0);
x_3 = lean::mk_string("\n");
x_4 = _l_s6_string_s11_intercalate(x_3, x_2);
return x_4;
}
}
obj* _l_s4_lean_s6_parser_s6_parsec_s7_message_s4_text(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s6_parsec_s7_message_s4_text_s6___rarg), 1, 0);
return x_2;
}
}
obj* _l_s4_list_s12_has__dec__eq_s6___main_s4___at_s4_lean_s6_parser_s6_parsec_s7_message_s4_text_s9___spec__1(obj* x_0, obj* x_1) {
{

if (lean::obj_tag(x_0) == 0)
{

lean::dec(x_0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_4; 
lean::dec(x_1);
x_4 = lean::box(1);
return x_4;
}
else
{
obj* x_6; 
lean::dec(x_1);
x_6 = lean::box(0);
return x_6;
}
}
else
{
obj* x_7; obj* x_9; 
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 1);
lean::inc(x_9);
lean::dec(x_0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_15; 
lean::dec(x_7);
lean::dec(x_9);
lean::dec(x_1);
x_15 = lean::box(0);
return x_15;
}
else
{
obj* x_16; obj* x_18; obj* x_21; 
x_16 = lean::cnstr_get(x_1, 0);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_1, 1);
lean::inc(x_18);
lean::dec(x_1);
x_21 = lean::string_dec_eq(x_7, x_16);
lean::dec(x_16);
lean::dec(x_7);
if (lean::obj_tag(x_21) == 0)
{
obj* x_27; 
lean::dec(x_18);
lean::dec(x_21);
lean::dec(x_9);
x_27 = lean::box(0);
return x_27;
}
else
{
obj* x_29; 
lean::dec(x_21);
x_29 = _l_s4_list_s12_has__dec__eq_s6___main_s4___at_s4_lean_s6_parser_s6_parsec_s7_message_s4_text_s9___spec__1(x_9, x_18);
return x_29;
}
}
}
}
}
obj* _l_s4_lean_s6_parser_s6_parsec_s7_message_s10_to__string_s6___rarg(obj* x_0) {
{
obj* x_1; obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_9; obj* x_12; obj* x_13; obj* x_15; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::string_iterator_to_string(x_1);
x_4 = lean::string_iterator_offset(x_1);
lean::dec(x_1);
x_6 = _l_s6_string_s12_line__column(x_3, x_4);
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_6, 1);
lean::inc(x_9);
lean::dec(x_6);
x_12 = _l_s3_nat_s4_repr(x_7);
x_13 = _l_s4_lean_s6_parser_s6_parsec_s7_message_s10_to__string_s6___rarg_s11___closed__1;
lean::inc(x_13);
x_15 = lean::string_append(x_13, x_12);
lean::dec(x_12);
x_17 = _l_s4_lean_s6_parser_s6_parsec_s7_message_s10_to__string_s6___rarg_s11___closed__2;
x_18 = lean::string_append(x_15, x_17);
x_19 = _l_s3_nat_s4_repr(x_9);
x_20 = lean::string_append(x_18, x_19);
lean::dec(x_19);
x_22 = _l_s4_lean_s6_parser_s6_parsec_s7_message_s10_to__string_s6___rarg_s11___closed__3;
x_23 = lean::string_append(x_20, x_22);
x_24 = _l_s4_lean_s6_parser_s6_parsec_s7_message_s4_text_s6___rarg(x_0);
x_25 = lean::string_append(x_23, x_24);
lean::dec(x_24);
return x_25;
}
}
obj* _init__l_s4_lean_s6_parser_s6_parsec_s7_message_s10_to__string_s6___rarg_s11___closed__1() {
{
obj* x_0; 
x_0 = lean::mk_string("error at line ");
return x_0;
}
}
obj* _init__l_s4_lean_s6_parser_s6_parsec_s7_message_s10_to__string_s6___rarg_s11___closed__2() {
{
obj* x_0; 
x_0 = lean::mk_string(", column ");
return x_0;
}
}
obj* _init__l_s4_lean_s6_parser_s6_parsec_s7_message_s10_to__string_s6___rarg_s11___closed__3() {
{
obj* x_0; 
x_0 = lean::mk_string(":\n");
return x_0;
}
}
obj* _l_s4_lean_s6_parser_s6_parsec_s7_message_s10_to__string(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s6_parsec_s7_message_s10_to__string_s6___rarg), 1, 0);
return x_2;
}
}
obj* _l_s4_lean_s6_parser_s6_parsec_s15_has__to__string(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s6_parsec_s7_message_s10_to__string_s6___rarg), 1, 0);
return x_2;
}
}
obj* _l_s4_lean_s6_parser_s6_parsec_s9_has__lift(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s6_parsec_s7_message_s10_to__string_s6___rarg), 1, 0);
return x_2;
}
}
obj* _l_s4_lean_s6_parser_s6_parsec_s6_result_s7_mk__eps_s6___rarg(obj* x_0, obj* x_1) {
{
obj* x_2; obj* x_4; 
x_2 = _l_s4_lean_s6_parser_s6_parsec_s6_result_s7_mk__eps_s6___rarg_s11___closed__1;
lean::inc(x_2);
x_4 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
lean::cnstr_set(x_4, 2, x_2);
return x_4;
}
}
obj* _init__l_s4_lean_s6_parser_s6_parsec_s6_result_s7_mk__eps_s6___rarg_s11___closed__1() {
{
obj* x_0; obj* x_1; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id_s6___rarg), 1, 0);
x_1 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _l_s4_lean_s6_parser_s6_parsec_s6_result_s7_mk__eps(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s6_parsec_s6_result_s7_mk__eps_s6___rarg), 2, 0);
return x_4;
}
}
obj* _init__l_s4_lean_s6_parser_s9_parsec__t() {
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init__l_s4_lean_s6_parser_s6_parsec() {
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init__l_s4_lean_s6_parser_s10_parsec_x27() {
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _l_s4_lean_s6_parser_s9_parsec__t_s3_run_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
{
obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
lean::dec(x_5);
lean::dec(x_2);
lean::dec(x_1);
x_9 = lean::cnstr_get(x_0, 1);
lean::inc(x_9);
x_11 = lean::string_mk_iterator(x_4);
x_12 = lean::apply_1(x_3, x_11);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s9_parsec__t_s3_run_s6___rarg_s11___lambda__1), 2, 1);
lean::closure_set(x_13, 0, x_0);
x_14 = lean::apply_4(x_9, lean::box(0), lean::box(0), x_12, x_13);
return x_14;
}
}
obj* _l_s4_lean_s6_parser_s9_parsec__t_s3_run_s6___rarg_s11___lambda__1(obj* x_0, obj* x_1) {
{
obj* x_2; obj* x_5; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
lean::dec(x_2);
if (lean::obj_tag(x_1) == 0)
{
obj* x_8; obj* x_11; obj* x_12; 
x_8 = lean::cnstr_get(x_1, 0);
lean::inc(x_8);
lean::dec(x_1);
x_11 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_11, 0, x_8);
x_12 = lean::apply_2(x_5, lean::box(0), x_11);
return x_12;
}
else
{
obj* x_13; obj* x_16; obj* x_17; 
x_13 = lean::cnstr_get(x_1, 0);
lean::inc(x_13);
lean::dec(x_1);
x_16 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_16, 0, x_13);
x_17 = lean::apply_2(x_5, lean::box(0), x_16);
return x_17;
}
}
}
obj* _l_s4_lean_s6_parser_s9_parsec__t_s3_run(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s9_parsec__t_s3_run_s6___rarg), 6, 0);
return x_2;
}
}
obj* _l_s4_lean_s6_parser_s9_parsec__t_s4_pure_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{
obj* x_7; obj* x_10; obj* x_13; obj* x_15; obj* x_16; 
lean::dec(x_2);
lean::dec(x_1);
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::cnstr_get(x_7, 1);
lean::inc(x_10);
lean::dec(x_7);
x_13 = _l_s4_lean_s6_parser_s6_parsec_s6_result_s7_mk__eps_s6___rarg_s11___closed__1;
lean::inc(x_13);
x_15 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_15, 0, x_3);
lean::cnstr_set(x_15, 1, x_4);
lean::cnstr_set(x_15, 2, x_13);
x_16 = lean::apply_2(x_10, lean::box(0), x_15);
return x_16;
}
}
obj* _l_s4_lean_s6_parser_s9_parsec__t_s4_pure(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s9_parsec__t_s4_pure_s6___rarg), 5, 0);
return x_2;
}
}
obj* _l_s4_lean_s6_parser_s9_parsec__t_s3_eps_s6___rarg(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_4; obj* x_7; unsigned char x_10; obj* x_11; obj* x_12; obj* x_14; obj* x_15; 
lean::dec(x_1);
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
lean::dec(x_0);
x_7 = lean::cnstr_get(x_4, 1);
lean::inc(x_7);
lean::dec(x_4);
x_10 = 0;
x_11 = _l_s4_lean_s6_parser_s6_parsec_s6_result_s7_mk__eps_s6___rarg_s11___closed__1;
x_12 = lean::box(x_10);
lean::inc(x_11);
x_14 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_14, 0, x_12);
lean::cnstr_set(x_14, 1, x_2);
lean::cnstr_set(x_14, 2, x_11);
x_15 = lean::apply_2(x_7, lean::box(0), x_14);
return x_15;
}
}
obj* _l_s4_lean_s6_parser_s9_parsec__t_s3_eps(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s9_parsec__t_s3_eps_s6___rarg), 3, 0);
return x_2;
}
}
obj* _l_s4_lean_s6_parser_s9_parsec__t_s7_failure_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{
obj* x_6; obj* x_9; obj* x_12; obj* x_13; obj* x_14; obj* x_17; unsigned char x_18; obj* x_19; obj* x_20; obj* x_21; 
lean::dec(x_2);
lean::dec(x_1);
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
lean::dec(x_0);
x_9 = lean::cnstr_get(x_6, 1);
lean::inc(x_9);
lean::dec(x_6);
x_12 = lean::box(0);
x_13 = _l_s4_lean_s6_parser_s9_parsec__t_s7_failure_s6___rarg_s11___closed__1;
x_14 = _l_s5_mjoin_s6___rarg_s11___closed__1;
lean::inc(x_14);
lean::inc(x_13);
x_17 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_17, 0, x_3);
lean::cnstr_set(x_17, 1, x_13);
lean::cnstr_set(x_17, 2, x_14);
lean::cnstr_set(x_17, 3, x_12);
x_18 = 0;
x_19 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_19, 0, x_17);
lean::cnstr_set_scalar(x_19, sizeof(void*)*1, x_18);
x_20 = x_19;
x_21 = lean::apply_2(x_9, lean::box(0), x_20);
return x_21;
}
}
obj* _init__l_s4_lean_s6_parser_s9_parsec__t_s7_failure_s6___rarg_s11___closed__1() {
{
obj* x_0; 
x_0 = lean::mk_string("failure");
return x_0;
}
}
obj* _l_s4_lean_s6_parser_s9_parsec__t_s7_failure(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s9_parsec__t_s7_failure_s6___rarg), 4, 0);
return x_2;
}
}
obj* _l_s4_lean_s6_parser_s9_parsec__t_s5_merge_s6___rarg(obj* x_0, obj* x_1) {
{
obj* x_2; obj* x_4; obj* x_6; obj* x_8; obj* x_11; obj* x_12; obj* x_15; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_0, 2);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 2);
lean::inc(x_8);
lean::dec(x_1);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(_l_s8_function_s4_comp_s6___rarg), 3, 2);
lean::closure_set(x_11, 0, x_6);
lean::closure_set(x_11, 1, x_8);
x_12 = lean::cnstr_get(x_0, 3);
lean::inc(x_12);
lean::dec(x_0);
x_15 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_15, 0, x_2);
lean::cnstr_set(x_15, 1, x_4);
lean::cnstr_set(x_15, 2, x_11);
lean::cnstr_set(x_15, 3, x_12);
return x_15;
}
}
obj* _l_s4_lean_s6_parser_s9_parsec__t_s5_merge(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s9_parsec__t_s5_merge_s6___rarg), 2, 0);
return x_2;
}
}
obj* _l_s4_lean_s6_parser_s9_parsec__t_s13_bind__mk__res_s6___rarg(obj* x_0, obj* x_1) {
{

if (lean::obj_tag(x_0) == 0)
{

if (lean::obj_tag(x_1) == 0)
{
obj* x_2; obj* x_4; obj* x_6; obj* x_7; 
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
 lean::cnstr_release(x_1, 2);
 x_6 = x_1;
}
if (lean::is_scalar(x_6)) {
 x_7 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_7 = x_6;
}
lean::cnstr_set(x_7, 0, x_2);
lean::cnstr_set(x_7, 1, x_4);
lean::cnstr_set(x_7, 2, x_0);
return x_7;
}
else
{
obj* x_9; obj* x_11; unsigned char x_12; obj* x_13; obj* x_14; 
lean::dec(x_0);
x_9 = lean::cnstr_get(x_1, 0);
lean::inc(x_9);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_11 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 x_11 = x_1;
}
x_12 = 1;
if (lean::is_scalar(x_11)) {
 x_13 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_13 = x_11;
}
lean::cnstr_set(x_13, 0, x_9);
lean::cnstr_set_scalar(x_13, sizeof(void*)*1, x_12);
x_14 = x_13;
return x_14;
}
}
else
{
obj* x_15; obj* x_17; 
x_15 = lean::cnstr_get(x_0, 0);
lean::inc(x_15);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_17 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 x_17 = x_0;
}
if (lean::obj_tag(x_1) == 0)
{
obj* x_18; obj* x_20; obj* x_22; 
x_18 = lean::cnstr_get(x_1, 0);
lean::inc(x_18);
x_20 = lean::cnstr_get(x_1, 1);
lean::inc(x_20);
x_22 = lean::cnstr_get(x_1, 2);
lean::inc(x_22);
if (lean::obj_tag(x_22) == 0)
{

lean::dec(x_17);
lean::dec(x_15);
lean::dec(x_18);
lean::dec(x_20);
lean::dec(x_22);
return x_1;
}
else
{
obj* x_30; obj* x_33; obj* x_34; obj* x_35; 
lean::dec(x_1);
x_30 = lean::cnstr_get(x_22, 0);
lean::inc(x_30);
lean::dec(x_22);
x_33 = lean::alloc_closure(reinterpret_cast<void*>(_l_s8_function_s4_comp_s6___rarg), 3, 2);
lean::closure_set(x_33, 0, x_15);
lean::closure_set(x_33, 1, x_30);
if (lean::is_scalar(x_17)) {
 x_34 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_34 = x_17;
}
lean::cnstr_set(x_34, 0, x_33);
x_35 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_35, 0, x_18);
lean::cnstr_set(x_35, 1, x_20);
lean::cnstr_set(x_35, 2, x_34);
return x_35;
}
}
else
{
obj* x_37; unsigned char x_39; 
lean::dec(x_17);
x_37 = lean::cnstr_get(x_1, 0);
lean::inc(x_37);
x_39 = lean::cnstr_get_scalar<unsigned char>(x_1, sizeof(void*)*1);
if (x_39 == 0)
{
obj* x_41; obj* x_43; obj* x_45; obj* x_47; obj* x_48; obj* x_51; obj* x_52; obj* x_53; 
lean::dec(x_1);
x_41 = lean::cnstr_get(x_37, 0);
lean::inc(x_41);
x_43 = lean::cnstr_get(x_37, 1);
lean::inc(x_43);
x_45 = lean::cnstr_get(x_37, 2);
lean::inc(x_45);
x_47 = lean::alloc_closure(reinterpret_cast<void*>(_l_s8_function_s4_comp_s6___rarg), 3, 2);
lean::closure_set(x_47, 0, x_15);
lean::closure_set(x_47, 1, x_45);
x_48 = lean::cnstr_get(x_37, 3);
lean::inc(x_48);
lean::dec(x_37);
x_51 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_51, 0, x_41);
lean::cnstr_set(x_51, 1, x_43);
lean::cnstr_set(x_51, 2, x_47);
lean::cnstr_set(x_51, 3, x_48);
x_52 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_52, 0, x_51);
lean::cnstr_set_scalar(x_52, sizeof(void*)*1, x_39);
x_53 = x_52;
return x_53;
}
else
{

lean::dec(x_15);
lean::dec(x_37);
return x_1;
}
}
}
}
}
obj* _l_s4_lean_s6_parser_s9_parsec__t_s13_bind__mk__res(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s9_parsec__t_s13_bind__mk__res_s6___rarg), 2, 0);
return x_4;
}
}
obj* _l_s4_lean_s6_parser_s9_parsec__t_s4_bind_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
{
obj* x_10; obj* x_12; obj* x_13; obj* x_14; 
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
x_10 = lean::cnstr_get(x_0, 1);
lean::inc(x_10);
x_12 = lean::apply_1(x_4, x_6);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s9_parsec__t_s4_bind_s6___rarg_s11___lambda__1), 3, 2);
lean::closure_set(x_13, 0, x_0);
lean::closure_set(x_13, 1, x_5);
x_14 = lean::apply_4(x_10, lean::box(0), lean::box(0), x_12, x_13);
return x_14;
}
}
obj* _l_s4_lean_s6_parser_s9_parsec__t_s4_bind_s6___rarg_s11___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
{

if (lean::obj_tag(x_2) == 0)
{
obj* x_3; obj* x_5; obj* x_7; obj* x_10; obj* x_13; obj* x_16; obj* x_19; obj* x_20; obj* x_21; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_2, 2);
lean::inc(x_7);
lean::dec(x_2);
x_10 = lean::cnstr_get(x_0, 0);
lean::inc(x_10);
lean::dec(x_0);
x_13 = lean::cnstr_get(x_10, 0);
lean::inc(x_13);
lean::dec(x_10);
x_16 = lean::cnstr_get(x_13, 0);
lean::inc(x_16);
lean::dec(x_13);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s9_parsec__t_s13_bind__mk__res_s6___rarg), 2, 1);
lean::closure_set(x_19, 0, x_7);
x_20 = lean::apply_2(x_1, x_3, x_5);
x_21 = lean::apply_4(x_16, lean::box(0), lean::box(0), x_19, x_20);
return x_21;
}
else
{
obj* x_23; unsigned char x_25; obj* x_26; obj* x_27; obj* x_30; obj* x_33; obj* x_34; obj* x_35; 
lean::dec(x_1);
x_23 = lean::cnstr_get(x_2, 0);
lean::inc(x_23);
x_25 = lean::cnstr_get_scalar<unsigned char>(x_2, sizeof(void*)*1);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_26 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 x_26 = x_2;
}
x_27 = lean::cnstr_get(x_0, 0);
lean::inc(x_27);
lean::dec(x_0);
x_30 = lean::cnstr_get(x_27, 1);
lean::inc(x_30);
lean::dec(x_27);
if (lean::is_scalar(x_26)) {
 x_33 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_33 = x_26;
}
lean::cnstr_set(x_33, 0, x_23);
lean::cnstr_set_scalar(x_33, sizeof(void*)*1, x_25);
x_34 = x_33;
x_35 = lean::apply_2(x_30, lean::box(0), x_34);
return x_35;
}
}
}
obj* _l_s4_lean_s6_parser_s9_parsec__t_s4_bind(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s9_parsec__t_s4_bind_s6___rarg), 7, 0);
return x_2;
}
}
obj* _l_s4_lean_s6_parser_s9_parsec__t_s5_monad_s6___rarg(obj* x_0, obj* x_1) {
{
obj* x_4; obj* x_6; obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
lean::dec(x_1);
lean::inc(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s9_parsec__t_s5_monad_s6___rarg_s11___lambda__2), 6, 1);
lean::closure_set(x_4, 0, x_0);
lean::inc(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s9_parsec__t_s5_monad_s6___rarg_s11___lambda__4), 6, 1);
lean::closure_set(x_6, 0, x_0);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_4);
lean::cnstr_set(x_7, 1, x_6);
lean::inc(x_0);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s9_parsec__t_s5_monad_s6___rarg_s11___lambda__5), 4, 1);
lean::closure_set(x_9, 0, x_0);
lean::inc(x_0);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s9_parsec__t_s5_monad_s6___rarg_s11___lambda__8), 6, 1);
lean::closure_set(x_11, 0, x_0);
lean::inc(x_0);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s9_parsec__t_s5_monad_s6___rarg_s12___lambda__11), 6, 1);
lean::closure_set(x_13, 0, x_0);
lean::inc(x_0);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s9_parsec__t_s5_monad_s6___rarg_s12___lambda__13), 6, 1);
lean::closure_set(x_15, 0, x_0);
x_16 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_16, 0, x_7);
lean::cnstr_set(x_16, 1, x_9);
lean::cnstr_set(x_16, 2, x_11);
lean::cnstr_set(x_16, 3, x_13);
lean::cnstr_set(x_16, 4, x_15);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s9_parsec__t_s5_monad_s6___rarg_s12___lambda__14), 6, 1);
lean::closure_set(x_17, 0, x_0);
x_18 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_18, 0, x_16);
lean::cnstr_set(x_18, 1, x_17);
return x_18;
}
}
obj* _l_s4_lean_s6_parser_s9_parsec__t_s5_monad_s6___rarg_s11___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
{

if (lean::obj_tag(x_2) == 0)
{
obj* x_3; obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_13; obj* x_15; obj* x_18; obj* x_19; obj* x_20; obj* x_23; obj* x_25; obj* x_26; obj* x_27; 
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
x_10 = lean::cnstr_get(x_0, 0);
lean::inc(x_10);
lean::dec(x_0);
x_13 = lean::cnstr_get(x_10, 0);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_13, 0);
lean::inc(x_15);
lean::dec(x_13);
x_18 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s9_parsec__t_s13_bind__mk__res_s6___rarg), 2, 1);
lean::closure_set(x_18, 0, x_7);
x_19 = lean::apply_1(x_1, x_3);
x_20 = lean::cnstr_get(x_10, 1);
lean::inc(x_20);
lean::dec(x_10);
x_23 = _l_s4_lean_s6_parser_s6_parsec_s6_result_s7_mk__eps_s6___rarg_s11___closed__1;
lean::inc(x_23);
if (lean::is_scalar(x_9)) {
 x_25 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_25 = x_9;
}
lean::cnstr_set(x_25, 0, x_19);
lean::cnstr_set(x_25, 1, x_5);
lean::cnstr_set(x_25, 2, x_23);
x_26 = lean::apply_2(x_20, lean::box(0), x_25);
x_27 = lean::apply_4(x_15, lean::box(0), lean::box(0), x_18, x_26);
return x_27;
}
else
{
obj* x_29; unsigned char x_31; obj* x_32; obj* x_33; obj* x_36; obj* x_39; obj* x_40; obj* x_41; 
lean::dec(x_1);
x_29 = lean::cnstr_get(x_2, 0);
lean::inc(x_29);
x_31 = lean::cnstr_get_scalar<unsigned char>(x_2, sizeof(void*)*1);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_32 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 x_32 = x_2;
}
x_33 = lean::cnstr_get(x_0, 0);
lean::inc(x_33);
lean::dec(x_0);
x_36 = lean::cnstr_get(x_33, 1);
lean::inc(x_36);
lean::dec(x_33);
if (lean::is_scalar(x_32)) {
 x_39 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_39 = x_32;
}
lean::cnstr_set(x_39, 0, x_29);
lean::cnstr_set_scalar(x_39, sizeof(void*)*1, x_31);
x_40 = x_39;
x_41 = lean::apply_2(x_36, lean::box(0), x_40);
return x_41;
}
}
}
obj* _l_s4_lean_s6_parser_s9_parsec__t_s5_monad_s6___rarg_s11___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
{
obj* x_8; obj* x_10; obj* x_11; obj* x_12; 
lean::dec(x_2);
lean::dec(x_1);
x_8 = lean::cnstr_get(x_0, 1);
lean::inc(x_8);
x_10 = lean::apply_1(x_4, x_5);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s9_parsec__t_s5_monad_s6___rarg_s11___lambda__1), 3, 2);
lean::closure_set(x_11, 0, x_0);
lean::closure_set(x_11, 1, x_3);
x_12 = lean::apply_4(x_8, lean::box(0), lean::box(0), x_10, x_11);
return x_12;
}
}
obj* _l_s4_lean_s6_parser_s9_parsec__t_s5_monad_s6___rarg_s11___lambda__3(obj* x_0, obj* x_1, obj* x_2) {
{

if (lean::obj_tag(x_2) == 0)
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_11; obj* x_13; obj* x_16; obj* x_17; obj* x_20; obj* x_22; obj* x_23; obj* x_24; 
x_3 = lean::cnstr_get(x_2, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_2, 2);
lean::inc(x_5);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_7 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 lean::cnstr_release(x_2, 1);
 lean::cnstr_release(x_2, 2);
 x_7 = x_2;
}
x_8 = lean::cnstr_get(x_0, 0);
lean::inc(x_8);
lean::dec(x_0);
x_11 = lean::cnstr_get(x_8, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_11, 0);
lean::inc(x_13);
lean::dec(x_11);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s9_parsec__t_s13_bind__mk__res_s6___rarg), 2, 1);
lean::closure_set(x_16, 0, x_5);
x_17 = lean::cnstr_get(x_8, 1);
lean::inc(x_17);
lean::dec(x_8);
x_20 = _l_s4_lean_s6_parser_s6_parsec_s6_result_s7_mk__eps_s6___rarg_s11___closed__1;
lean::inc(x_20);
if (lean::is_scalar(x_7)) {
 x_22 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_22 = x_7;
}
lean::cnstr_set(x_22, 0, x_1);
lean::cnstr_set(x_22, 1, x_3);
lean::cnstr_set(x_22, 2, x_20);
x_23 = lean::apply_2(x_17, lean::box(0), x_22);
x_24 = lean::apply_4(x_13, lean::box(0), lean::box(0), x_16, x_23);
return x_24;
}
else
{
obj* x_26; unsigned char x_28; obj* x_29; obj* x_30; obj* x_33; obj* x_36; obj* x_37; obj* x_38; 
lean::dec(x_1);
x_26 = lean::cnstr_get(x_2, 0);
lean::inc(x_26);
x_28 = lean::cnstr_get_scalar<unsigned char>(x_2, sizeof(void*)*1);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_29 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 x_29 = x_2;
}
x_30 = lean::cnstr_get(x_0, 0);
lean::inc(x_30);
lean::dec(x_0);
x_33 = lean::cnstr_get(x_30, 1);
lean::inc(x_33);
lean::dec(x_30);
if (lean::is_scalar(x_29)) {
 x_36 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_36 = x_29;
}
lean::cnstr_set(x_36, 0, x_26);
lean::cnstr_set_scalar(x_36, sizeof(void*)*1, x_28);
x_37 = x_36;
x_38 = lean::apply_2(x_33, lean::box(0), x_37);
return x_38;
}
}
}
obj* _l_s4_lean_s6_parser_s9_parsec__t_s5_monad_s6___rarg_s11___lambda__4(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
{
obj* x_8; obj* x_10; obj* x_11; obj* x_12; 
lean::dec(x_2);
lean::dec(x_1);
x_8 = lean::cnstr_get(x_0, 1);
lean::inc(x_8);
x_10 = lean::apply_1(x_4, x_5);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s9_parsec__t_s5_monad_s6___rarg_s11___lambda__3), 3, 2);
lean::closure_set(x_11, 0, x_0);
lean::closure_set(x_11, 1, x_3);
x_12 = lean::apply_4(x_8, lean::box(0), lean::box(0), x_10, x_11);
return x_12;
}
}
obj* _l_s4_lean_s6_parser_s9_parsec__t_s5_monad_s6___rarg_s11___lambda__5(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{
obj* x_5; obj* x_8; obj* x_11; obj* x_13; obj* x_14; 
lean::dec(x_1);
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
lean::dec(x_0);
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
lean::dec(x_5);
x_11 = _l_s4_lean_s6_parser_s6_parsec_s6_result_s7_mk__eps_s6___rarg_s11___closed__1;
lean::inc(x_11);
x_13 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_13, 0, x_2);
lean::cnstr_set(x_13, 1, x_3);
lean::cnstr_set(x_13, 2, x_11);
x_14 = lean::apply_2(x_8, lean::box(0), x_13);
return x_14;
}
}
obj* _l_s4_lean_s6_parser_s9_parsec__t_s5_monad_s6___rarg_s11___lambda__6(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{

if (lean::obj_tag(x_3) == 0)
{
obj* x_4; obj* x_6; obj* x_8; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_16; obj* x_18; obj* x_19; obj* x_20; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_3, 2);
lean::inc(x_8);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_10 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 1);
 lean::cnstr_release(x_3, 2);
 x_10 = x_3;
}
x_11 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s9_parsec__t_s13_bind__mk__res_s6___rarg), 2, 1);
lean::closure_set(x_11, 0, x_8);
x_12 = lean::apply_1(x_0, x_4);
x_13 = lean::cnstr_get(x_1, 1);
lean::inc(x_13);
lean::dec(x_1);
x_16 = _l_s4_lean_s6_parser_s6_parsec_s6_result_s7_mk__eps_s6___rarg_s11___closed__1;
lean::inc(x_16);
if (lean::is_scalar(x_10)) {
 x_18 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_18 = x_10;
}
lean::cnstr_set(x_18, 0, x_12);
lean::cnstr_set(x_18, 1, x_6);
lean::cnstr_set(x_18, 2, x_16);
x_19 = lean::apply_2(x_13, lean::box(0), x_18);
x_20 = lean::apply_4(x_2, lean::box(0), lean::box(0), x_11, x_19);
return x_20;
}
else
{
obj* x_23; unsigned char x_25; obj* x_26; obj* x_27; obj* x_30; obj* x_31; obj* x_32; 
lean::dec(x_0);
lean::dec(x_2);
x_23 = lean::cnstr_get(x_3, 0);
lean::inc(x_23);
x_25 = lean::cnstr_get_scalar<unsigned char>(x_3, sizeof(void*)*1);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_26 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 x_26 = x_3;
}
x_27 = lean::cnstr_get(x_1, 1);
lean::inc(x_27);
lean::dec(x_1);
if (lean::is_scalar(x_26)) {
 x_30 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_30 = x_26;
}
lean::cnstr_set(x_30, 0, x_23);
lean::cnstr_set_scalar(x_30, sizeof(void*)*1, x_25);
x_31 = x_30;
x_32 = lean::apply_2(x_27, lean::box(0), x_31);
return x_32;
}
}
}
obj* _l_s4_lean_s6_parser_s9_parsec__t_s5_monad_s6___rarg_s11___lambda__7(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{

if (lean::obj_tag(x_3) == 0)
{
obj* x_4; obj* x_6; obj* x_8; obj* x_11; obj* x_14; obj* x_16; obj* x_19; obj* x_20; obj* x_22; obj* x_23; obj* x_24; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_3, 2);
lean::inc(x_8);
lean::dec(x_3);
x_11 = lean::cnstr_get(x_0, 0);
lean::inc(x_11);
lean::dec(x_0);
x_14 = lean::cnstr_get(x_11, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_14, 0);
lean::inc(x_16);
lean::dec(x_14);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s9_parsec__t_s13_bind__mk__res_s6___rarg), 2, 1);
lean::closure_set(x_19, 0, x_8);
x_20 = lean::apply_1(x_1, x_6);
lean::inc(x_16);
x_22 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s9_parsec__t_s5_monad_s6___rarg_s11___lambda__6), 4, 3);
lean::closure_set(x_22, 0, x_4);
lean::closure_set(x_22, 1, x_11);
lean::closure_set(x_22, 2, x_16);
x_23 = lean::apply_4(x_2, lean::box(0), lean::box(0), x_20, x_22);
x_24 = lean::apply_4(x_16, lean::box(0), lean::box(0), x_19, x_23);
return x_24;
}
else
{
obj* x_27; unsigned char x_29; obj* x_30; obj* x_31; obj* x_34; obj* x_37; obj* x_38; obj* x_39; 
lean::dec(x_1);
lean::dec(x_2);
x_27 = lean::cnstr_get(x_3, 0);
lean::inc(x_27);
x_29 = lean::cnstr_get_scalar<unsigned char>(x_3, sizeof(void*)*1);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_30 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 x_30 = x_3;
}
x_31 = lean::cnstr_get(x_0, 0);
lean::inc(x_31);
lean::dec(x_0);
x_34 = lean::cnstr_get(x_31, 1);
lean::inc(x_34);
lean::dec(x_31);
if (lean::is_scalar(x_30)) {
 x_37 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_37 = x_30;
}
lean::cnstr_set(x_37, 0, x_27);
lean::cnstr_set_scalar(x_37, sizeof(void*)*1, x_29);
x_38 = x_37;
x_39 = lean::apply_2(x_34, lean::box(0), x_38);
return x_39;
}
}
}
obj* _l_s4_lean_s6_parser_s9_parsec__t_s5_monad_s6___rarg_s11___lambda__8(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
{
obj* x_8; obj* x_10; obj* x_12; obj* x_13; 
lean::dec(x_2);
lean::dec(x_1);
x_8 = lean::cnstr_get(x_0, 1);
lean::inc(x_8);
x_10 = lean::apply_1(x_3, x_5);
lean::inc(x_8);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s9_parsec__t_s5_monad_s6___rarg_s11___lambda__7), 4, 3);
lean::closure_set(x_12, 0, x_0);
lean::closure_set(x_12, 1, x_4);
lean::closure_set(x_12, 2, x_8);
x_13 = lean::apply_4(x_8, lean::box(0), lean::box(0), x_10, x_12);
return x_13;
}
}
obj* _l_s4_lean_s6_parser_s9_parsec__t_s5_monad_s6___rarg_s11___lambda__9(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{

if (lean::obj_tag(x_3) == 0)
{
obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_13; obj* x_15; obj* x_16; obj* x_17; 
x_4 = lean::cnstr_get(x_3, 1);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_3, 2);
lean::inc(x_6);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_8 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 1);
 lean::cnstr_release(x_3, 2);
 x_8 = x_3;
}
x_9 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s9_parsec__t_s13_bind__mk__res_s6___rarg), 2, 1);
lean::closure_set(x_9, 0, x_6);
x_10 = lean::cnstr_get(x_0, 1);
lean::inc(x_10);
lean::dec(x_0);
x_13 = _l_s4_lean_s6_parser_s6_parsec_s6_result_s7_mk__eps_s6___rarg_s11___closed__1;
lean::inc(x_13);
if (lean::is_scalar(x_8)) {
 x_15 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_15 = x_8;
}
lean::cnstr_set(x_15, 0, x_1);
lean::cnstr_set(x_15, 1, x_4);
lean::cnstr_set(x_15, 2, x_13);
x_16 = lean::apply_2(x_10, lean::box(0), x_15);
x_17 = lean::apply_4(x_2, lean::box(0), lean::box(0), x_9, x_16);
return x_17;
}
else
{
obj* x_20; unsigned char x_22; obj* x_23; obj* x_24; obj* x_27; obj* x_28; obj* x_29; 
lean::dec(x_1);
lean::dec(x_2);
x_20 = lean::cnstr_get(x_3, 0);
lean::inc(x_20);
x_22 = lean::cnstr_get_scalar<unsigned char>(x_3, sizeof(void*)*1);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_23 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 x_23 = x_3;
}
x_24 = lean::cnstr_get(x_0, 1);
lean::inc(x_24);
lean::dec(x_0);
if (lean::is_scalar(x_23)) {
 x_27 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_27 = x_23;
}
lean::cnstr_set(x_27, 0, x_20);
lean::cnstr_set_scalar(x_27, sizeof(void*)*1, x_22);
x_28 = x_27;
x_29 = lean::apply_2(x_24, lean::box(0), x_28);
return x_29;
}
}
}
obj* _l_s4_lean_s6_parser_s9_parsec__t_s5_monad_s6___rarg_s12___lambda__10(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{

if (lean::obj_tag(x_3) == 0)
{
obj* x_4; obj* x_6; obj* x_8; obj* x_11; obj* x_14; obj* x_16; obj* x_19; obj* x_20; obj* x_22; obj* x_23; obj* x_24; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_3, 2);
lean::inc(x_8);
lean::dec(x_3);
x_11 = lean::cnstr_get(x_0, 0);
lean::inc(x_11);
lean::dec(x_0);
x_14 = lean::cnstr_get(x_11, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_14, 0);
lean::inc(x_16);
lean::dec(x_14);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s9_parsec__t_s13_bind__mk__res_s6___rarg), 2, 1);
lean::closure_set(x_19, 0, x_8);
x_20 = lean::apply_1(x_1, x_6);
lean::inc(x_16);
x_22 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s9_parsec__t_s5_monad_s6___rarg_s11___lambda__9), 4, 3);
lean::closure_set(x_22, 0, x_11);
lean::closure_set(x_22, 1, x_4);
lean::closure_set(x_22, 2, x_16);
x_23 = lean::apply_4(x_2, lean::box(0), lean::box(0), x_20, x_22);
x_24 = lean::apply_4(x_16, lean::box(0), lean::box(0), x_19, x_23);
return x_24;
}
else
{
obj* x_27; unsigned char x_29; obj* x_30; obj* x_31; obj* x_34; obj* x_37; obj* x_38; obj* x_39; 
lean::dec(x_1);
lean::dec(x_2);
x_27 = lean::cnstr_get(x_3, 0);
lean::inc(x_27);
x_29 = lean::cnstr_get_scalar<unsigned char>(x_3, sizeof(void*)*1);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_30 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 x_30 = x_3;
}
x_31 = lean::cnstr_get(x_0, 0);
lean::inc(x_31);
lean::dec(x_0);
x_34 = lean::cnstr_get(x_31, 1);
lean::inc(x_34);
lean::dec(x_31);
if (lean::is_scalar(x_30)) {
 x_37 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_37 = x_30;
}
lean::cnstr_set(x_37, 0, x_27);
lean::cnstr_set_scalar(x_37, sizeof(void*)*1, x_29);
x_38 = x_37;
x_39 = lean::apply_2(x_34, lean::box(0), x_38);
return x_39;
}
}
}
obj* _l_s4_lean_s6_parser_s9_parsec__t_s5_monad_s6___rarg_s12___lambda__11(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
{
obj* x_8; obj* x_10; obj* x_12; obj* x_13; 
lean::dec(x_2);
lean::dec(x_1);
x_8 = lean::cnstr_get(x_0, 1);
lean::inc(x_8);
x_10 = lean::apply_1(x_3, x_5);
lean::inc(x_8);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s9_parsec__t_s5_monad_s6___rarg_s12___lambda__10), 4, 3);
lean::closure_set(x_12, 0, x_0);
lean::closure_set(x_12, 1, x_4);
lean::closure_set(x_12, 2, x_8);
x_13 = lean::apply_4(x_8, lean::box(0), lean::box(0), x_10, x_12);
return x_13;
}
}
obj* _l_s4_lean_s6_parser_s9_parsec__t_s5_monad_s6___rarg_s12___lambda__12(obj* x_0, obj* x_1, obj* x_2) {
{

if (lean::obj_tag(x_2) == 0)
{
obj* x_3; obj* x_5; obj* x_8; obj* x_11; obj* x_14; obj* x_17; obj* x_18; obj* x_19; 
x_3 = lean::cnstr_get(x_2, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_2, 2);
lean::inc(x_5);
lean::dec(x_2);
x_8 = lean::cnstr_get(x_0, 0);
lean::inc(x_8);
lean::dec(x_0);
x_11 = lean::cnstr_get(x_8, 0);
lean::inc(x_11);
lean::dec(x_8);
x_14 = lean::cnstr_get(x_11, 0);
lean::inc(x_14);
lean::dec(x_11);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s9_parsec__t_s13_bind__mk__res_s6___rarg), 2, 1);
lean::closure_set(x_17, 0, x_5);
x_18 = lean::apply_1(x_1, x_3);
x_19 = lean::apply_4(x_14, lean::box(0), lean::box(0), x_17, x_18);
return x_19;
}
else
{
obj* x_21; unsigned char x_23; obj* x_24; obj* x_25; obj* x_28; obj* x_31; obj* x_32; obj* x_33; 
lean::dec(x_1);
x_21 = lean::cnstr_get(x_2, 0);
lean::inc(x_21);
x_23 = lean::cnstr_get_scalar<unsigned char>(x_2, sizeof(void*)*1);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_24 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 x_24 = x_2;
}
x_25 = lean::cnstr_get(x_0, 0);
lean::inc(x_25);
lean::dec(x_0);
x_28 = lean::cnstr_get(x_25, 1);
lean::inc(x_28);
lean::dec(x_25);
if (lean::is_scalar(x_24)) {
 x_31 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_31 = x_24;
}
lean::cnstr_set(x_31, 0, x_21);
lean::cnstr_set_scalar(x_31, sizeof(void*)*1, x_23);
x_32 = x_31;
x_33 = lean::apply_2(x_28, lean::box(0), x_32);
return x_33;
}
}
}
obj* _l_s4_lean_s6_parser_s9_parsec__t_s5_monad_s6___rarg_s12___lambda__13(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
{
obj* x_8; obj* x_10; obj* x_11; obj* x_12; 
lean::dec(x_2);
lean::dec(x_1);
x_8 = lean::cnstr_get(x_0, 1);
lean::inc(x_8);
x_10 = lean::apply_1(x_3, x_5);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s9_parsec__t_s5_monad_s6___rarg_s12___lambda__12), 3, 2);
lean::closure_set(x_11, 0, x_0);
lean::closure_set(x_11, 1, x_4);
x_12 = lean::apply_4(x_8, lean::box(0), lean::box(0), x_10, x_11);
return x_12;
}
}
obj* _l_s4_lean_s6_parser_s9_parsec__t_s5_monad_s6___rarg_s12___lambda__14(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
{
obj* x_8; obj* x_10; obj* x_11; obj* x_12; 
lean::dec(x_2);
lean::dec(x_1);
x_8 = lean::cnstr_get(x_0, 1);
lean::inc(x_8);
x_10 = lean::apply_1(x_3, x_5);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s9_parsec__t_s4_bind_s6___rarg_s11___lambda__1), 3, 2);
lean::closure_set(x_11, 0, x_0);
lean::closure_set(x_11, 1, x_4);
x_12 = lean::apply_4(x_8, lean::box(0), lean::box(0), x_10, x_11);
return x_12;
}
}
obj* _l_s4_lean_s6_parser_s9_parsec__t_s5_monad(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s9_parsec__t_s5_monad_s6___rarg), 2, 0);
return x_2;
}
}
obj* _l_s4_lean_s6_parser_s9_parsec__t_s11_monad__fail_s6___rarg(obj* x_0, obj* x_1) {
{
obj* x_2; obj* x_3; obj* x_6; unsigned char x_7; obj* x_8; obj* x_9; 
x_2 = _l_s5_mjoin_s6___rarg_s11___closed__1;
x_3 = _l_s4_lean_s6_parser_s9_parsec__t_s11_monad__fail_s6___rarg_s11___closed__1;
lean::inc(x_3);
lean::inc(x_2);
x_6 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_6, 0, x_1);
lean::cnstr_set(x_6, 1, x_0);
lean::cnstr_set(x_6, 2, x_2);
lean::cnstr_set(x_6, 3, x_3);
x_7 = 0;
x_8 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set_scalar(x_8, sizeof(void*)*1, x_7);
x_9 = x_8;
return x_9;
}
}
obj* _init__l_s4_lean_s6_parser_s9_parsec__t_s11_monad__fail_s6___rarg_s11___closed__1() {
{
unsigned char x_0; obj* x_1; obj* x_2; 
x_0 = 0;
x_1 = lean::box(x_0);
x_2 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _l_s4_lean_s6_parser_s9_parsec__t_s11_monad__fail(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s9_parsec__t_s11_monad__fail_s6___rarg), 2, 0);
return x_2;
}
}
obj* _l_s4_lean_s6_parser_s9_parsec__t_s13_monad__except_s6___rarg(obj* x_0, obj* x_1) {
{
obj* x_4; obj* x_5; obj* x_6; 
lean::dec(x_1);
lean::inc(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s9_parsec__t_s13_monad__except_s6___rarg_s11___lambda__1), 4, 1);
lean::closure_set(x_4, 0, x_0);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s9_parsec__t_s13_monad__except_s6___rarg_s11___lambda__4), 5, 1);
lean::closure_set(x_5, 0, x_0);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_4);
lean::cnstr_set(x_6, 1, x_5);
return x_6;
}
}
obj* _l_s4_lean_s6_parser_s9_parsec__t_s13_monad__except_s6___rarg_s11___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{
obj* x_6; obj* x_9; unsigned char x_12; obj* x_13; obj* x_14; obj* x_15; 
lean::dec(x_3);
lean::dec(x_1);
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
lean::dec(x_0);
x_9 = lean::cnstr_get(x_6, 1);
lean::inc(x_9);
lean::dec(x_6);
x_12 = 0;
x_13 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_13, 0, x_2);
lean::cnstr_set_scalar(x_13, sizeof(void*)*1, x_12);
x_14 = x_13;
x_15 = lean::apply_2(x_9, lean::box(0), x_14);
return x_15;
}
}
obj* _l_s4_lean_s6_parser_s9_parsec__t_s13_monad__except_s6___rarg_s11___lambda__2(obj* x_0, unsigned char x_1, obj* x_2) {
{
obj* x_3; obj* x_6; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
lean::dec(x_0);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
lean::dec(x_3);
if (lean::obj_tag(x_2) == 0)
{
obj* x_9; 
x_9 = lean::apply_2(x_6, lean::box(0), x_2);
return x_9;
}
else
{
obj* x_10; unsigned char x_12; obj* x_13; 
x_10 = lean::cnstr_get(x_2, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get_scalar<unsigned char>(x_2, sizeof(void*)*1);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_13 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 x_13 = x_2;
}
if (x_1 == 0)
{
obj* x_14; obj* x_15; obj* x_16; 
if (lean::is_scalar(x_13)) {
 x_14 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_14 = x_13;
}
lean::cnstr_set(x_14, 0, x_10);
lean::cnstr_set_scalar(x_14, sizeof(void*)*1, x_12);
x_15 = x_14;
x_16 = lean::apply_2(x_6, lean::box(0), x_15);
return x_16;
}
else
{
obj* x_17; obj* x_18; obj* x_19; 
if (lean::is_scalar(x_13)) {
 x_17 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_17 = x_13;
}
lean::cnstr_set(x_17, 0, x_10);
lean::cnstr_set_scalar(x_17, sizeof(void*)*1, x_1);
x_18 = x_17;
x_19 = lean::apply_2(x_6, lean::box(0), x_18);
return x_19;
}
}
}
}
obj* _l_s4_lean_s6_parser_s9_parsec__t_s13_monad__except_s6___rarg_s11___lambda__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{

if (lean::obj_tag(x_3) == 0)
{
obj* x_6; obj* x_9; obj* x_12; 
lean::dec(x_1);
lean::dec(x_2);
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
lean::dec(x_0);
x_9 = lean::cnstr_get(x_6, 1);
lean::inc(x_9);
lean::dec(x_6);
x_12 = lean::apply_2(x_9, lean::box(0), x_3);
return x_12;
}
else
{
obj* x_13; unsigned char x_15; obj* x_17; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_13 = lean::cnstr_get(x_3, 0);
lean::inc(x_13);
x_15 = lean::cnstr_get_scalar<unsigned char>(x_3, sizeof(void*)*1);
lean::dec(x_3);
x_17 = lean::cnstr_get(x_13, 0);
lean::inc(x_17);
x_19 = lean::apply_2(x_1, x_13, x_17);
x_20 = lean::box(x_15);
x_21 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s9_parsec__t_s13_monad__except_s6___rarg_s11___lambda__2_s7___boxed), 3, 2);
lean::closure_set(x_21, 0, x_0);
lean::closure_set(x_21, 1, x_20);
x_22 = lean::apply_4(x_2, lean::box(0), lean::box(0), x_19, x_21);
return x_22;
}
}
}
obj* _l_s4_lean_s6_parser_s9_parsec__t_s13_monad__except_s6___rarg_s11___lambda__4(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{
obj* x_6; obj* x_8; obj* x_10; obj* x_11; 
lean::dec(x_1);
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
x_8 = lean::apply_1(x_2, x_4);
lean::inc(x_6);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s9_parsec__t_s13_monad__except_s6___rarg_s11___lambda__3), 4, 3);
lean::closure_set(x_10, 0, x_0);
lean::closure_set(x_10, 1, x_3);
lean::closure_set(x_10, 2, x_6);
x_11 = lean::apply_4(x_6, lean::box(0), lean::box(0), x_8, x_10);
return x_11;
}
}
obj* _l_s4_lean_s6_parser_s9_parsec__t_s13_monad__except(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s9_parsec__t_s13_monad__except_s6___rarg), 2, 0);
return x_2;
}
}
obj* _l_s4_lean_s6_parser_s9_parsec__t_s13_monad__except_s6___rarg_s11___lambda__2_s7___boxed(obj* x_0, obj* x_1, obj* x_2) {
{
unsigned char x_3; obj* x_4; 
x_3 = lean::unbox(x_1);
x_4 = _l_s4_lean_s6_parser_s9_parsec__t_s13_monad__except_s6___rarg_s11___lambda__2(x_0, x_3, x_2);
return x_4;
}
}
obj* _l_s4_lean_s6_parser_s9_parsec__t_s16_has__monad__lift_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{
obj* x_7; obj* x_9; obj* x_10; 
lean::dec(x_2);
lean::dec(x_1);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s9_parsec__t_s16_has__monad__lift_s6___rarg_s11___lambda__1), 3, 2);
lean::closure_set(x_9, 0, x_0);
lean::closure_set(x_9, 1, x_4);
x_10 = lean::apply_4(x_7, lean::box(0), lean::box(0), x_3, x_9);
return x_10;
}
}
obj* _l_s4_lean_s6_parser_s9_parsec__t_s16_has__monad__lift_s6___rarg_s11___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_3; obj* x_6; obj* x_9; obj* x_11; obj* x_12; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
lean::dec(x_0);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
lean::dec(x_3);
x_9 = _l_s4_lean_s6_parser_s6_parsec_s6_result_s7_mk__eps_s6___rarg_s11___closed__1;
lean::inc(x_9);
x_11 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_11, 0, x_2);
lean::cnstr_set(x_11, 1, x_1);
lean::cnstr_set(x_11, 2, x_9);
x_12 = lean::apply_2(x_6, lean::box(0), x_11);
return x_12;
}
}
obj* _l_s4_lean_s6_parser_s9_parsec__t_s16_has__monad__lift(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s9_parsec__t_s16_has__monad__lift_s6___rarg), 5, 0);
return x_2;
}
}
obj* _l_s4_lean_s6_parser_s9_parsec__t_s6_expect_s6___rarg(obj* x_0, obj* x_1) {
{
obj* x_2; obj* x_4; obj* x_6; obj* x_7; obj* x_10; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s5_dlist_s9_singleton_s6___rarg), 2, 1);
lean::closure_set(x_6, 0, x_1);
x_7 = lean::cnstr_get(x_0, 3);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_10, 0, x_2);
lean::cnstr_set(x_10, 1, x_4);
lean::cnstr_set(x_10, 2, x_6);
lean::cnstr_set(x_10, 3, x_7);
return x_10;
}
}
obj* _l_s4_lean_s6_parser_s9_parsec__t_s6_expect(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s9_parsec__t_s6_expect_s6___rarg), 2, 0);
return x_2;
}
}
obj* _l_s4_lean_s6_parser_s9_parsec__t_s15_labels__mk__res_s6___rarg(obj* x_0, obj* x_1) {
{

if (lean::obj_tag(x_0) == 0)
{
obj* x_2; obj* x_4; obj* x_6; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_0, 2);
lean::inc(x_6);
if (lean::obj_tag(x_6) == 0)
{

lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_4);
return x_0;
}
else
{
obj* x_13; obj* x_14; obj* x_15; 
lean::dec(x_0);
if (lean::is_shared(x_6)) {
 lean::dec(x_6);
 x_13 = lean::box(0);
} else {
 lean::cnstr_release(x_6, 0);
 x_13 = x_6;
}
if (lean::is_scalar(x_13)) {
 x_14 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_14 = x_13;
}
lean::cnstr_set(x_14, 0, x_1);
x_15 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_15, 0, x_2);
lean::cnstr_set(x_15, 1, x_4);
lean::cnstr_set(x_15, 2, x_14);
return x_15;
}
}
else
{
obj* x_16; unsigned char x_18; 
x_16 = lean::cnstr_get(x_0, 0);
lean::inc(x_16);
x_18 = lean::cnstr_get_scalar<unsigned char>(x_0, sizeof(void*)*1);
if (x_18 == 0)
{
obj* x_20; obj* x_22; obj* x_24; obj* x_27; obj* x_28; obj* x_29; 
lean::dec(x_0);
x_20 = lean::cnstr_get(x_16, 0);
lean::inc(x_20);
x_22 = lean::cnstr_get(x_16, 1);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_16, 3);
lean::inc(x_24);
lean::dec(x_16);
x_27 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_27, 0, x_20);
lean::cnstr_set(x_27, 1, x_22);
lean::cnstr_set(x_27, 2, x_1);
lean::cnstr_set(x_27, 3, x_24);
x_28 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set_scalar(x_28, sizeof(void*)*1, x_18);
x_29 = x_28;
return x_29;
}
else
{

lean::dec(x_16);
lean::dec(x_1);
return x_0;
}
}
}
}
obj* _l_s4_lean_s6_parser_s9_parsec__t_s15_labels__mk__res(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s9_parsec__t_s15_labels__mk__res_s6___rarg), 2, 0);
return x_4;
}
}
obj* _l_s4_lean_s6_parser_s9_parsec__t_s6_labels_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
{
obj* x_8; obj* x_10; obj* x_11; obj* x_12; 
lean::dec(x_2);
lean::dec(x_1);
x_8 = lean::cnstr_get(x_0, 1);
lean::inc(x_8);
x_10 = lean::apply_1(x_3, x_5);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s9_parsec__t_s6_labels_s6___rarg_s11___lambda__1), 3, 2);
lean::closure_set(x_11, 0, x_0);
lean::closure_set(x_11, 1, x_4);
x_12 = lean::apply_4(x_8, lean::box(0), lean::box(0), x_10, x_11);
return x_12;
}
}
obj* _l_s4_lean_s6_parser_s9_parsec__t_s6_labels_s6___rarg_s11___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_3; obj* x_6; obj* x_9; obj* x_10; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
lean::dec(x_0);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
lean::dec(x_3);
x_9 = _l_s4_lean_s6_parser_s9_parsec__t_s15_labels__mk__res_s6___rarg(x_2, x_1);
x_10 = lean::apply_2(x_6, lean::box(0), x_9);
return x_10;
}
}
obj* _l_s4_lean_s6_parser_s9_parsec__t_s6_labels(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s9_parsec__t_s6_labels_s6___rarg), 6, 0);
return x_2;
}
}
obj* _l_s4_lean_s6_parser_s9_parsec__t_s12_try__mk__res_s6___rarg(obj* x_0) {
{

if (lean::obj_tag(x_0) == 0)
{

return x_0;
}
else
{
obj* x_1; obj* x_3; unsigned char x_4; obj* x_5; obj* x_6; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_3 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 x_3 = x_0;
}
x_4 = 0;
if (lean::is_scalar(x_3)) {
 x_5 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_5 = x_3;
}
lean::cnstr_set(x_5, 0, x_1);
lean::cnstr_set_scalar(x_5, sizeof(void*)*1, x_4);
x_6 = x_5;
return x_6;
}
}
}
obj* _l_s4_lean_s6_parser_s9_parsec__t_s12_try__mk__res(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s9_parsec__t_s12_try__mk__res_s6___rarg), 1, 0);
return x_4;
}
}
obj* _l_s4_lean_s6_parser_s9_parsec__t_s3_try_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{
obj* x_7; obj* x_9; obj* x_10; obj* x_11; 
lean::dec(x_2);
lean::dec(x_1);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
x_9 = lean::apply_1(x_3, x_4);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s9_parsec__t_s3_try_s6___rarg_s11___lambda__1), 2, 1);
lean::closure_set(x_10, 0, x_0);
x_11 = lean::apply_4(x_7, lean::box(0), lean::box(0), x_9, x_10);
return x_11;
}
}
obj* _l_s4_lean_s6_parser_s9_parsec__t_s3_try_s6___rarg_s11___lambda__1(obj* x_0, obj* x_1) {
{
obj* x_2; obj* x_5; obj* x_8; obj* x_9; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
lean::dec(x_2);
x_8 = _l_s4_lean_s6_parser_s9_parsec__t_s12_try__mk__res_s6___rarg(x_1);
x_9 = lean::apply_2(x_5, lean::box(0), x_8);
return x_9;
}
}
obj* _l_s4_lean_s6_parser_s9_parsec__t_s3_try(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s9_parsec__t_s3_try_s6___rarg), 5, 0);
return x_2;
}
}
obj* _l_s4_lean_s6_parser_s9_parsec__t_s15_orelse__mk__res_s6___rarg(obj* x_0, obj* x_1) {
{

if (lean::obj_tag(x_1) == 0)
{
obj* x_2; obj* x_4; obj* x_6; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_1, 2);
lean::inc(x_6);
if (lean::obj_tag(x_6) == 0)
{

lean::dec(x_6);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_4);
return x_1;
}
else
{
obj* x_13; obj* x_15; obj* x_16; obj* x_19; obj* x_20; obj* x_21; 
lean::dec(x_1);
x_13 = lean::cnstr_get(x_6, 0);
lean::inc(x_13);
if (lean::is_shared(x_6)) {
 lean::dec(x_6);
 x_15 = lean::box(0);
} else {
 lean::cnstr_release(x_6, 0);
 x_15 = x_6;
}
x_16 = lean::cnstr_get(x_0, 2);
lean::inc(x_16);
lean::dec(x_0);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(_l_s8_function_s4_comp_s6___rarg), 3, 2);
lean::closure_set(x_19, 0, x_16);
lean::closure_set(x_19, 1, x_13);
if (lean::is_scalar(x_15)) {
 x_20 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_20 = x_15;
}
lean::cnstr_set(x_20, 0, x_19);
x_21 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_21, 0, x_2);
lean::cnstr_set(x_21, 1, x_4);
lean::cnstr_set(x_21, 2, x_20);
return x_21;
}
}
else
{
obj* x_22; unsigned char x_24; 
x_22 = lean::cnstr_get(x_1, 0);
lean::inc(x_22);
x_24 = lean::cnstr_get_scalar<unsigned char>(x_1, sizeof(void*)*1);
if (x_24 == 0)
{
obj* x_26; obj* x_27; obj* x_28; 
lean::dec(x_1);
x_26 = _l_s4_lean_s6_parser_s9_parsec__t_s5_merge_s6___rarg(x_0, x_22);
x_27 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set_scalar(x_27, sizeof(void*)*1, x_24);
x_28 = x_27;
return x_28;
}
else
{

lean::dec(x_0);
lean::dec(x_22);
return x_1;
}
}
}
}
obj* _l_s4_lean_s6_parser_s9_parsec__t_s15_orelse__mk__res(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s9_parsec__t_s15_orelse__mk__res_s6___rarg), 2, 0);
return x_4;
}
}
obj* _l_s4_lean_s6_parser_s9_parsec__t_s6_orelse_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
{
obj* x_8; obj* x_11; obj* x_13; obj* x_14; 
lean::dec(x_2);
lean::dec(x_1);
x_8 = lean::cnstr_get(x_0, 1);
lean::inc(x_8);
lean::inc(x_5);
x_11 = lean::apply_1(x_3, x_5);
lean::inc(x_8);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s9_parsec__t_s6_orelse_s6___rarg_s11___lambda__2), 5, 4);
lean::closure_set(x_13, 0, x_0);
lean::closure_set(x_13, 1, x_4);
lean::closure_set(x_13, 2, x_5);
lean::closure_set(x_13, 3, x_8);
x_14 = lean::apply_4(x_8, lean::box(0), lean::box(0), x_11, x_13);
return x_14;
}
}
obj* _l_s4_lean_s6_parser_s9_parsec__t_s6_orelse_s6___rarg_s11___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_3; obj* x_6; obj* x_9; obj* x_10; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
lean::dec(x_0);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
lean::dec(x_3);
x_9 = _l_s4_lean_s6_parser_s9_parsec__t_s15_orelse__mk__res_s6___rarg(x_1, x_2);
x_10 = lean::apply_2(x_6, lean::box(0), x_9);
return x_10;
}
}
obj* _l_s4_lean_s6_parser_s9_parsec__t_s6_orelse_s6___rarg_s11___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{
unsigned char x_5; 
if (lean::obj_tag(x_4) == 0)
{
unsigned char x_10; 
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
x_10 = 0;
x_5 = x_10;
goto lbl_6;
}
else
{
obj* x_11; unsigned char x_13; 
x_11 = lean::cnstr_get(x_4, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get_scalar<unsigned char>(x_4, sizeof(void*)*1);
if (x_13 == 0)
{
obj* x_15; obj* x_16; obj* x_17; 
lean::dec(x_4);
x_15 = lean::apply_1(x_1, x_2);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s9_parsec__t_s6_orelse_s6___rarg_s11___lambda__1), 3, 2);
lean::closure_set(x_16, 0, x_0);
lean::closure_set(x_16, 1, x_11);
x_17 = lean::apply_4(x_3, lean::box(0), lean::box(0), x_15, x_16);
return x_17;
}
else
{
unsigned char x_22; 
lean::dec(x_11);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
x_22 = 0;
x_5 = x_22;
goto lbl_6;
}
}
lbl_6:
{
obj* x_23; obj* x_26; obj* x_29; 
x_23 = lean::cnstr_get(x_0, 0);
lean::inc(x_23);
lean::dec(x_0);
x_26 = lean::cnstr_get(x_23, 1);
lean::inc(x_26);
lean::dec(x_23);
x_29 = lean::apply_2(x_26, lean::box(0), x_4);
return x_29;
}
}
}
obj* _l_s4_lean_s6_parser_s9_parsec__t_s6_orelse(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s9_parsec__t_s6_orelse_s6___rarg), 6, 0);
return x_2;
}
}
obj* _l_s4_lean_s6_parser_s9_parsec__t_s11_alternative_s6___rarg(obj* x_0, obj* x_1) {
{
obj* x_4; obj* x_6; obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_16; obj* x_18; obj* x_19; obj* x_20; 
lean::dec(x_1);
lean::inc(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s9_parsec__t_s5_monad_s6___rarg_s11___lambda__2), 6, 1);
lean::closure_set(x_4, 0, x_0);
lean::inc(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s9_parsec__t_s5_monad_s6___rarg_s11___lambda__4), 6, 1);
lean::closure_set(x_6, 0, x_0);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_4);
lean::cnstr_set(x_7, 1, x_6);
lean::inc(x_0);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s9_parsec__t_s5_monad_s6___rarg_s11___lambda__5), 4, 1);
lean::closure_set(x_9, 0, x_0);
lean::inc(x_0);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s9_parsec__t_s5_monad_s6___rarg_s11___lambda__8), 6, 1);
lean::closure_set(x_11, 0, x_0);
lean::inc(x_0);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s9_parsec__t_s5_monad_s6___rarg_s12___lambda__11), 6, 1);
lean::closure_set(x_13, 0, x_0);
lean::inc(x_0);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s9_parsec__t_s5_monad_s6___rarg_s12___lambda__13), 6, 1);
lean::closure_set(x_15, 0, x_0);
x_16 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_16, 0, x_7);
lean::cnstr_set(x_16, 1, x_9);
lean::cnstr_set(x_16, 2, x_11);
lean::cnstr_set(x_16, 3, x_13);
lean::cnstr_set(x_16, 4, x_15);
lean::inc(x_0);
x_18 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s9_parsec__t_s11_alternative_s6___rarg_s11___lambda__1), 5, 1);
lean::closure_set(x_18, 0, x_0);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s9_parsec__t_s11_alternative_s6___rarg_s11___lambda__2), 3, 1);
lean::closure_set(x_19, 0, x_0);
x_20 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_20, 0, x_16);
lean::cnstr_set(x_20, 1, x_18);
lean::cnstr_set(x_20, 2, x_19);
return x_20;
}
}
obj* _l_s4_lean_s6_parser_s9_parsec__t_s11_alternative_s6___rarg_s11___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{
obj* x_6; obj* x_9; obj* x_11; obj* x_12; 
lean::dec(x_1);
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
lean::inc(x_4);
x_9 = lean::apply_1(x_2, x_4);
lean::inc(x_6);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s9_parsec__t_s6_orelse_s6___rarg_s11___lambda__2), 5, 4);
lean::closure_set(x_11, 0, x_0);
lean::closure_set(x_11, 1, x_3);
lean::closure_set(x_11, 2, x_4);
lean::closure_set(x_11, 3, x_6);
x_12 = lean::apply_4(x_6, lean::box(0), lean::box(0), x_9, x_11);
return x_12;
}
}
obj* _l_s4_lean_s6_parser_s9_parsec__t_s11_alternative_s6___rarg_s11___lambda__2(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_4; 
lean::dec(x_1);
x_4 = _l_s4_lean_s6_parser_s9_parsec__t_s7_failure_s6___rarg(x_0, lean::box(0), lean::box(0), x_2);
return x_4;
}
}
obj* _l_s4_lean_s6_parser_s9_parsec__t_s11_alternative(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s9_parsec__t_s11_alternative_s6___rarg), 2, 0);
return x_2;
}
}
obj* _l_s4_lean_s6_parser_s9_parsec__t_s9_lookahead_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{
obj* x_7; obj* x_10; obj* x_11; obj* x_12; 
lean::dec(x_2);
lean::dec(x_1);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
lean::inc(x_4);
x_10 = lean::apply_1(x_3, x_4);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s9_parsec__t_s9_lookahead_s6___rarg_s11___lambda__1), 3, 2);
lean::closure_set(x_11, 0, x_0);
lean::closure_set(x_11, 1, x_4);
x_12 = lean::apply_4(x_7, lean::box(0), lean::box(0), x_10, x_11);
return x_12;
}
}
obj* _l_s4_lean_s6_parser_s9_parsec__t_s9_lookahead_s6___rarg_s11___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_3; obj* x_6; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
lean::dec(x_0);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
lean::dec(x_3);
if (lean::obj_tag(x_2) == 0)
{
obj* x_9; obj* x_11; obj* x_12; obj* x_14; obj* x_15; 
x_9 = lean::cnstr_get(x_2, 0);
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
x_12 = _l_s4_lean_s6_parser_s6_parsec_s6_result_s7_mk__eps_s6___rarg_s11___closed__1;
lean::inc(x_12);
if (lean::is_scalar(x_11)) {
 x_14 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_14 = x_11;
}
lean::cnstr_set(x_14, 0, x_9);
lean::cnstr_set(x_14, 1, x_1);
lean::cnstr_set(x_14, 2, x_12);
x_15 = lean::apply_2(x_6, lean::box(0), x_14);
return x_15;
}
else
{
obj* x_17; 
lean::dec(x_1);
x_17 = lean::apply_2(x_6, lean::box(0), x_2);
return x_17;
}
}
}
obj* _l_s4_lean_s6_parser_s9_parsec__t_s9_lookahead(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s9_parsec__t_s9_lookahead_s6___rarg), 5, 0);
return x_2;
}
}
obj* _init__l_s4_lean_s6_parser_s17_monad__parsec_x27() {
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _l_s4_lean_s6_parser_s4_lean_s6_parser_s13_monad__parsec_s6___rarg(obj* x_0) {
{
obj* x_2; obj* x_3; obj* x_4; 
lean::inc(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s4_lean_s6_parser_s13_monad__parsec_s6___rarg_s11___lambda__1), 4, 1);
lean::closure_set(x_2, 0, x_0);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s4_lean_s6_parser_s13_monad__parsec_s6___rarg_s11___lambda__2), 5, 1);
lean::closure_set(x_3, 0, x_0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_2);
lean::cnstr_set(x_4, 1, x_3);
return x_4;
}
}
obj* _l_s4_lean_s6_parser_s4_lean_s6_parser_s13_monad__parsec_s6___rarg_s11___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{
obj* x_5; obj* x_8; obj* x_11; obj* x_12; 
lean::dec(x_1);
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
lean::dec(x_0);
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
lean::dec(x_5);
x_11 = lean::apply_1(x_2, x_3);
x_12 = lean::apply_2(x_8, lean::box(0), x_11);
return x_12;
}
}
obj* _l_s4_lean_s6_parser_s4_lean_s6_parser_s13_monad__parsec_s6___rarg_s11___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{
obj* x_6; 
lean::dec(x_1);
x_6 = lean::apply_5(x_2, lean::box(0), x_0, lean::box(0), x_3, x_4);
return x_6;
}
}
obj* _l_s4_lean_s6_parser_s4_lean_s6_parser_s13_monad__parsec(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s4_lean_s6_parser_s13_monad__parsec_s6___rarg), 1, 0);
return x_4;
}
}
obj* _l_s4_lean_s6_parser_s20_monad__parsec__trans_s6___rarg(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_4; obj* x_5; obj* x_6; 
lean::inc(x_2);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s20_monad__parsec__trans_s6___rarg_s11___lambda__1), 4, 2);
lean::closure_set(x_4, 0, x_2);
lean::closure_set(x_4, 1, x_0);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s20_monad__parsec__trans_s6___rarg_s11___lambda__3), 5, 2);
lean::closure_set(x_5, 0, x_2);
lean::closure_set(x_5, 1, x_1);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_4);
lean::cnstr_set(x_6, 1, x_5);
return x_6;
}
}
obj* _l_s4_lean_s6_parser_s20_monad__parsec__trans_s6___rarg_s11___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{
obj* x_5; obj* x_8; obj* x_9; 
lean::dec(x_2);
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
lean::dec(x_0);
x_8 = lean::apply_2(x_5, lean::box(0), x_3);
x_9 = lean::apply_2(x_1, lean::box(0), x_8);
return x_9;
}
}
obj* _l_s4_lean_s6_parser_s20_monad__parsec__trans_s6___rarg_s11___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{
obj* x_5; obj* x_8; 
lean::dec(x_2);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
lean::dec(x_0);
x_8 = lean::apply_3(x_5, lean::box(0), x_1, x_3);
return x_8;
}
}
obj* _l_s4_lean_s6_parser_s20_monad__parsec__trans_s6___rarg_s11___lambda__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{
obj* x_6; obj* x_7; 
lean::dec(x_2);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s20_monad__parsec__trans_s6___rarg_s11___lambda__2), 4, 2);
lean::closure_set(x_6, 0, x_0);
lean::closure_set(x_6, 1, x_3);
x_7 = lean::apply_3(x_1, lean::box(0), x_6, x_4);
return x_7;
}
}
obj* _l_s4_lean_s6_parser_s20_monad__parsec__trans(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s20_monad__parsec__trans_s6___rarg), 3, 0);
return x_6;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
{
obj* x_7; obj* x_10; obj* x_11; 
lean::dec(x_1);
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s6___rarg_s11___lambda__1), 5, 4);
lean::closure_set(x_10, 0, x_4);
lean::closure_set(x_10, 1, x_2);
lean::closure_set(x_10, 2, x_3);
lean::closure_set(x_10, 3, x_5);
x_11 = lean::apply_2(x_7, lean::box(0), x_10);
return x_11;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s6___rarg_s11___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{
obj* x_5; obj* x_6; unsigned char x_7; obj* x_8; obj* x_9; 
x_5 = _l_s6_option_s13_get__or__else_s6___main_s6___rarg(x_0, x_4);
x_6 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_1);
lean::cnstr_set(x_6, 2, x_2);
lean::cnstr_set(x_6, 3, x_3);
x_7 = 0;
x_8 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set_scalar(x_8, sizeof(void*)*1, x_7);
x_9 = x_8;
return x_9;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s6___rarg), 6, 0);
return x_6;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s10_left__over_s6___rarg(obj* x_0) {
{
obj* x_1; obj* x_4; obj* x_6; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
x_4 = _l_s4_lean_s6_parser_s13_monad__parsec_s10_left__over_s6___rarg_s11___closed__1;
lean::inc(x_4);
x_6 = lean::apply_2(x_1, lean::box(0), x_4);
return x_6;
}
}
obj* _init__l_s4_lean_s6_parser_s13_monad__parsec_s10_left__over_s6___rarg_s11___closed__1() {
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s10_left__over_s6___rarg_s11___lambda__1), 1, 0);
return x_0;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s10_left__over_s6___rarg_s11___lambda__1(obj* x_0) {
{
obj* x_1; obj* x_4; 
x_1 = _l_s4_lean_s6_parser_s6_parsec_s6_result_s7_mk__eps_s6___rarg_s11___closed__1;
lean::inc(x_1);
lean::inc(x_0);
x_4 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_0);
lean::cnstr_set(x_4, 2, x_1);
return x_4;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s10_left__over(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s10_left__over_s6___rarg), 1, 0);
return x_6;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s9_remaining_s6___rarg(obj* x_0, obj* x_1) {
{
obj* x_2; obj* x_5; obj* x_8; obj* x_11; obj* x_14; obj* x_16; obj* x_17; obj* x_19; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
x_5 = lean::cnstr_get(x_2, 0);
lean::inc(x_5);
lean::dec(x_2);
x_8 = lean::cnstr_get(x_5, 0);
lean::inc(x_8);
lean::dec(x_5);
x_11 = lean::cnstr_get(x_1, 0);
lean::inc(x_11);
lean::dec(x_1);
x_14 = _l_s4_lean_s6_parser_s13_monad__parsec_s10_left__over_s6___rarg_s11___closed__1;
lean::inc(x_14);
x_16 = lean::apply_2(x_11, lean::box(0), x_14);
x_17 = _l_s4_lean_s6_parser_s13_monad__parsec_s9_remaining_s6___rarg_s11___closed__1;
lean::inc(x_17);
x_19 = lean::apply_4(x_8, lean::box(0), lean::box(0), x_17, x_16);
return x_19;
}
}
obj* _init__l_s4_lean_s6_parser_s13_monad__parsec_s9_remaining_s6___rarg_s11___closed__1() {
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(lean::string_iterator_remaining), 1, 0);
return x_0;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s9_remaining(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s9_remaining_s6___rarg), 2, 0);
return x_4;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s6_labels_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{
obj* x_5; obj* x_8; obj* x_9; 
lean::dec(x_1);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
lean::dec(x_0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s6_labels_s6___rarg_s11___lambda__1), 6, 1);
lean::closure_set(x_8, 0, x_3);
x_9 = lean::apply_3(x_5, lean::box(0), x_8, x_2);
return x_9;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s6_labels_s6___rarg_s11___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
{
obj* x_8; obj* x_10; obj* x_11; obj* x_12; 
lean::dec(x_3);
lean::dec(x_1);
x_8 = lean::cnstr_get(x_2, 1);
lean::inc(x_8);
x_10 = lean::apply_1(x_4, x_5);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s9_parsec__t_s6_labels_s6___rarg_s11___lambda__1), 3, 2);
lean::closure_set(x_11, 0, x_2);
lean::closure_set(x_11, 1, x_0);
x_12 = lean::apply_4(x_8, lean::box(0), lean::box(0), x_10, x_11);
return x_12;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s6_labels(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s6_labels_s6___rarg), 4, 0);
return x_6;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_label_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{
obj* x_5; obj* x_6; obj* x_9; obj* x_10; 
lean::dec(x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(_l_s5_dlist_s9_singleton_s6___rarg), 2, 1);
lean::closure_set(x_5, 0, x_3);
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
lean::dec(x_0);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s6_labels_s6___rarg_s11___lambda__1), 6, 1);
lean::closure_set(x_9, 0, x_5);
x_10 = lean::apply_3(x_6, lean::box(0), x_9, x_2);
return x_10;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_label(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s5_label_s6___rarg), 4, 0);
return x_6;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s6_hidden_s6___rarg(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_4; obj* x_7; obj* x_9; 
lean::dec(x_1);
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
lean::dec(x_0);
x_7 = _l_s4_lean_s6_parser_s13_monad__parsec_s6_hidden_s6___rarg_s11___closed__1;
lean::inc(x_7);
x_9 = lean::apply_3(x_4, lean::box(0), x_7, x_2);
return x_9;
}
}
obj* _init__l_s4_lean_s6_parser_s13_monad__parsec_s6_hidden_s6___rarg_s11___closed__1() {
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s6_hidden_s6___rarg_s11___lambda__2), 5, 0);
return x_0;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s6_hidden_s6___rarg_s11___lambda__1(obj* x_0, obj* x_1) {
{
obj* x_2; obj* x_5; obj* x_8; obj* x_10; obj* x_11; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
lean::dec(x_2);
x_8 = _l_s5_mjoin_s6___rarg_s11___closed__1;
lean::inc(x_8);
x_10 = _l_s4_lean_s6_parser_s9_parsec__t_s15_labels__mk__res_s6___rarg(x_1, x_8);
x_11 = lean::apply_2(x_5, lean::box(0), x_10);
return x_11;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s6_hidden_s6___rarg_s11___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{
obj* x_7; obj* x_9; obj* x_10; obj* x_11; 
lean::dec(x_2);
lean::dec(x_0);
x_7 = lean::cnstr_get(x_1, 1);
lean::inc(x_7);
x_9 = lean::apply_1(x_3, x_4);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s6_hidden_s6___rarg_s11___lambda__1), 2, 1);
lean::closure_set(x_10, 0, x_1);
x_11 = lean::apply_4(x_7, lean::box(0), lean::box(0), x_9, x_10);
return x_11;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s6_hidden(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s6_hidden_s6___rarg), 3, 0);
return x_6;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s3_try_s6___rarg(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_4; obj* x_7; obj* x_9; 
lean::dec(x_1);
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
lean::dec(x_0);
x_7 = _l_s4_lean_s6_parser_s13_monad__parsec_s3_try_s6___rarg_s11___closed__1;
lean::inc(x_7);
x_9 = lean::apply_3(x_4, lean::box(0), x_7, x_2);
return x_9;
}
}
obj* _init__l_s4_lean_s6_parser_s13_monad__parsec_s3_try_s6___rarg_s11___closed__1() {
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s3_try_s6___rarg_s11___lambda__1), 5, 0);
return x_0;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s3_try_s6___rarg_s11___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{
obj* x_7; obj* x_9; obj* x_10; obj* x_11; 
lean::dec(x_2);
lean::dec(x_0);
x_7 = lean::cnstr_get(x_1, 1);
lean::inc(x_7);
x_9 = lean::apply_1(x_3, x_4);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s9_parsec__t_s3_try_s6___rarg_s11___lambda__1), 2, 1);
lean::closure_set(x_10, 0, x_1);
x_11 = lean::apply_4(x_7, lean::box(0), lean::box(0), x_9, x_10);
return x_11;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s3_try(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s3_try_s6___rarg), 3, 0);
return x_6;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s9_lookahead_s6___rarg(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_4; obj* x_7; obj* x_9; 
lean::dec(x_1);
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
lean::dec(x_0);
x_7 = _l_s4_lean_s6_parser_s13_monad__parsec_s9_lookahead_s6___rarg_s11___closed__1;
lean::inc(x_7);
x_9 = lean::apply_3(x_4, lean::box(0), x_7, x_2);
return x_9;
}
}
obj* _init__l_s4_lean_s6_parser_s13_monad__parsec_s9_lookahead_s6___rarg_s11___closed__1() {
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s9_lookahead_s6___rarg_s11___lambda__1), 5, 0);
return x_0;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s9_lookahead_s6___rarg_s11___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{
obj* x_7; 
lean::dec(x_2);
lean::dec(x_0);
x_7 = _l_s4_lean_s6_parser_s9_parsec__t_s9_lookahead_s6___rarg(x_1, lean::box(0), lean::box(0), x_3, x_4);
return x_7;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s9_lookahead(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s9_lookahead_s6___rarg), 3, 0);
return x_6;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s22_not__followed__by__sat_s6___rarg(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_3; obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_11; 
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
x_7 = _l_s4_lean_s6_parser_s13_monad__parsec_s10_left__over_s6___rarg_s11___closed__1;
lean::inc(x_7);
x_9 = lean::apply_2(x_5, lean::box(0), x_7);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s22_not__followed__by__sat_s6___rarg_s11___lambda__1), 4, 3);
lean::closure_set(x_10, 0, x_0);
lean::closure_set(x_10, 1, x_2);
lean::closure_set(x_10, 2, x_1);
x_11 = lean::apply_4(x_3, lean::box(0), lean::box(0), x_9, x_10);
return x_11;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s22_not__followed__by__sat_s6___rarg_s11___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{
unsigned char x_4; 
x_4 = lean::string_iterator_has_next(x_3);
if (x_4 == 0)
{
obj* x_8; obj* x_11; unsigned char x_14; obj* x_15; obj* x_16; 
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
x_8 = lean::cnstr_get(x_0, 0);
lean::inc(x_8);
lean::dec(x_0);
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
lean::dec(x_8);
x_14 = 0;
x_15 = lean::box(x_14);
x_16 = lean::apply_2(x_11, lean::box(0), x_15);
return x_16;
}
else
{
unsigned x_17; obj* x_19; obj* x_20; unsigned char x_21; 
x_17 = lean::string_iterator_curr(x_3);
lean::dec(x_3);
x_19 = lean::box_uint32(x_17);
x_20 = lean::apply_1(x_1, x_19);
x_21 = lean::unbox(x_20);
lean::dec(x_20);
if (x_21 == 0)
{
obj* x_24; obj* x_27; unsigned char x_30; obj* x_31; obj* x_32; 
lean::dec(x_2);
x_24 = lean::cnstr_get(x_0, 0);
lean::inc(x_24);
lean::dec(x_0);
x_27 = lean::cnstr_get(x_24, 1);
lean::inc(x_27);
lean::dec(x_24);
x_30 = 0;
x_31 = lean::box(x_30);
x_32 = lean::apply_2(x_27, lean::box(0), x_31);
return x_32;
}
else
{
obj* x_34; obj* x_35; obj* x_37; obj* x_39; obj* x_40; obj* x_41; obj* x_44; 
lean::dec(x_0);
x_34 = _l_s4_char_s11_quote__core(x_17);
x_35 = _l_s4_char_s9_has__repr_s11___closed__1;
lean::inc(x_35);
x_37 = lean::string_append(x_35, x_34);
lean::dec(x_34);
x_39 = lean::string_append(x_37, x_35);
x_40 = lean::box(0);
x_41 = _l_s5_mjoin_s6___rarg_s11___closed__1;
lean::inc(x_40);
lean::inc(x_41);
x_44 = _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s22_not__followed__by__sat_s9___spec__1_s6___rarg(x_2, lean::box(0), x_39, x_41, x_40, x_40);
return x_44;
}
}
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s22_not__followed__by__sat(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s22_not__followed__by__sat_s6___rarg), 3, 0);
return x_4;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s22_not__followed__by__sat_s9___spec__1_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
{
obj* x_7; obj* x_10; obj* x_11; 
lean::dec(x_1);
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s6___rarg_s11___lambda__1), 5, 4);
lean::closure_set(x_10, 0, x_4);
lean::closure_set(x_10, 1, x_2);
lean::closure_set(x_10, 2, x_3);
lean::closure_set(x_10, 3, x_5);
x_11 = lean::apply_2(x_7, lean::box(0), x_10);
return x_11;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s22_not__followed__by__sat_s9___spec__1(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s22_not__followed__by__sat_s9___spec__1_s6___rarg), 6, 0);
return x_6;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s10_eoi__error_s6___rarg(obj* x_0) {
{
obj* x_1; obj* x_2; obj* x_3; obj* x_6; unsigned char x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = _l_s4_lean_s6_parser_s13_monad__parsec_s10_eoi__error_s6___rarg_s11___closed__1;
x_3 = _l_s5_mjoin_s6___rarg_s11___closed__1;
lean::inc(x_3);
lean::inc(x_2);
x_6 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_6, 0, x_0);
lean::cnstr_set(x_6, 1, x_2);
lean::cnstr_set(x_6, 2, x_3);
lean::cnstr_set(x_6, 3, x_1);
x_7 = 0;
x_8 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set_scalar(x_8, sizeof(void*)*1, x_7);
x_9 = x_8;
return x_9;
}
}
obj* _init__l_s4_lean_s6_parser_s13_monad__parsec_s10_eoi__error_s6___rarg_s11___closed__1() {
{
obj* x_0; 
x_0 = lean::mk_string("end of input");
return x_0;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s10_eoi__error(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s10_eoi__error_s6___rarg), 1, 0);
return x_4;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s4_curr_s6___rarg(obj* x_0, obj* x_1) {
{
obj* x_2; obj* x_5; obj* x_8; obj* x_11; obj* x_14; obj* x_16; obj* x_17; obj* x_19; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
x_5 = lean::cnstr_get(x_2, 0);
lean::inc(x_5);
lean::dec(x_2);
x_8 = lean::cnstr_get(x_5, 0);
lean::inc(x_8);
lean::dec(x_5);
x_11 = lean::cnstr_get(x_1, 0);
lean::inc(x_11);
lean::dec(x_1);
x_14 = _l_s4_lean_s6_parser_s13_monad__parsec_s10_left__over_s6___rarg_s11___closed__1;
lean::inc(x_14);
x_16 = lean::apply_2(x_11, lean::box(0), x_14);
x_17 = _l_s4_lean_s6_parser_s13_monad__parsec_s4_curr_s6___rarg_s11___closed__1;
lean::inc(x_17);
x_19 = lean::apply_4(x_8, lean::box(0), lean::box(0), x_17, x_16);
return x_19;
}
}
obj* _init__l_s4_lean_s6_parser_s13_monad__parsec_s4_curr_s6___rarg_s11___closed__1() {
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s6_string_s8_iterator_s4_curr_s7___boxed), 1, 0);
return x_0;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s4_curr(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s4_curr_s6___rarg), 2, 0);
return x_4;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s4_cond_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
{
obj* x_7; obj* x_9; obj* x_11; obj* x_14; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
lean::dec(x_2);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_9, 0);
lean::inc(x_11);
lean::dec(x_9);
x_14 = lean::cnstr_get(x_11, 0);
lean::inc(x_14);
lean::dec(x_11);
x_17 = _l_s4_lean_s6_parser_s13_monad__parsec_s4_curr_s6___rarg(x_0, x_1);
x_18 = lean::apply_4(x_14, lean::box(0), lean::box(0), x_3, x_17);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s4_cond_s6___rarg_s11___lambda__1_s7___boxed), 3, 2);
lean::closure_set(x_19, 0, x_5);
lean::closure_set(x_19, 1, x_4);
x_20 = lean::apply_4(x_7, lean::box(0), lean::box(0), x_18, x_19);
return x_20;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s4_cond_s6___rarg_s11___lambda__1(obj* x_0, obj* x_1, unsigned char x_2) {
{

if (x_2 == 0)
{

lean::dec(x_1);
return x_0;
}
else
{

lean::dec(x_0);
return x_1;
}
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s4_cond(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s4_cond_s6___rarg), 6, 0);
return x_4;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s4_cond_s6___rarg_s11___lambda__1_s7___boxed(obj* x_0, obj* x_1, obj* x_2) {
{
unsigned char x_3; obj* x_4; 
x_3 = lean::unbox(x_2);
x_4 = _l_s4_lean_s6_parser_s13_monad__parsec_s4_cond_s6___rarg_s11___lambda__1(x_0, x_1, x_3);
return x_4;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s7_satisfy_s6___rarg(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_3; obj* x_5; obj* x_7; obj* x_10; obj* x_11; obj* x_12; 
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
x_7 = _l_s4_lean_s6_parser_s13_monad__parsec_s10_left__over_s6___rarg_s11___closed__1;
lean::inc(x_7);
lean::inc(x_5);
x_10 = lean::apply_2(x_5, lean::box(0), x_7);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s7_satisfy_s6___rarg_s11___lambda__2), 5, 4);
lean::closure_set(x_11, 0, x_0);
lean::closure_set(x_11, 1, x_1);
lean::closure_set(x_11, 2, x_2);
lean::closure_set(x_11, 3, x_5);
x_12 = lean::apply_4(x_3, lean::box(0), lean::box(0), x_10, x_11);
return x_12;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s7_satisfy_s6___rarg_s11___lambda__1(obj* x_0, unsigned x_1, obj* x_2) {
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
lean::dec(x_2);
x_4 = lean::string_iterator_next(x_0);
x_5 = lean::box(0);
x_6 = lean::box_uint32(x_1);
x_7 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_4);
lean::cnstr_set(x_7, 2, x_5);
return x_7;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s7_satisfy_s6___rarg_s11___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{
unsigned char x_6; 
lean::dec(x_0);
x_6 = lean::string_iterator_has_next(x_4);
if (x_6 == 0)
{
obj* x_10; obj* x_11; obj* x_12; obj* x_16; 
lean::dec(x_4);
lean::dec(x_2);
lean::dec(x_3);
x_10 = lean::box(0);
x_11 = _l_s4_lean_s6_parser_s13_monad__parsec_s10_eoi__error_s6___rarg_s11___closed__1;
x_12 = _l_s5_mjoin_s6___rarg_s11___closed__1;
lean::inc(x_10);
lean::inc(x_12);
lean::inc(x_11);
x_16 = _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s7_satisfy_s9___spec__1_s6___rarg(x_1, lean::box(0), x_11, x_12, x_10, x_10);
return x_16;
}
else
{
unsigned x_17; obj* x_18; obj* x_20; unsigned char x_21; 
x_17 = lean::string_iterator_curr(x_4);
x_18 = lean::box_uint32(x_17);
lean::inc(x_18);
x_20 = lean::apply_1(x_2, x_18);
x_21 = lean::unbox(x_20);
lean::dec(x_20);
if (x_21 == 0)
{
obj* x_26; obj* x_27; obj* x_29; obj* x_31; obj* x_32; obj* x_33; obj* x_36; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_18);
x_26 = _l_s4_char_s11_quote__core(x_17);
x_27 = _l_s4_char_s9_has__repr_s11___closed__1;
lean::inc(x_27);
x_29 = lean::string_append(x_27, x_26);
lean::dec(x_26);
x_31 = lean::string_append(x_29, x_27);
x_32 = lean::box(0);
x_33 = _l_s5_mjoin_s6___rarg_s11___closed__1;
lean::inc(x_32);
lean::inc(x_33);
x_36 = _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s7_satisfy_s9___spec__2_s6___rarg(x_1, lean::box(0), x_31, x_33, x_32, x_32);
return x_36;
}
else
{
obj* x_38; obj* x_39; 
lean::dec(x_1);
x_38 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s7_satisfy_s6___rarg_s11___lambda__1_s7___boxed), 3, 2);
lean::closure_set(x_38, 0, x_4);
lean::closure_set(x_38, 1, x_18);
x_39 = lean::apply_2(x_3, lean::box(0), x_38);
return x_39;
}
}
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s7_satisfy(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s7_satisfy_s6___rarg), 3, 0);
return x_4;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s7_satisfy_s9___spec__1_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
{
obj* x_7; obj* x_10; obj* x_11; 
lean::dec(x_1);
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s6___rarg_s11___lambda__1), 5, 4);
lean::closure_set(x_10, 0, x_4);
lean::closure_set(x_10, 1, x_2);
lean::closure_set(x_10, 2, x_3);
lean::closure_set(x_10, 3, x_5);
x_11 = lean::apply_2(x_7, lean::box(0), x_10);
return x_11;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s7_satisfy_s9___spec__1(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s7_satisfy_s9___spec__1_s6___rarg), 6, 0);
return x_6;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s7_satisfy_s9___spec__2_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
{
obj* x_7; obj* x_10; obj* x_11; 
lean::dec(x_1);
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s6___rarg_s11___lambda__1), 5, 4);
lean::closure_set(x_10, 0, x_4);
lean::closure_set(x_10, 1, x_2);
lean::closure_set(x_10, 2, x_3);
lean::closure_set(x_10, 3, x_5);
x_11 = lean::apply_2(x_7, lean::box(0), x_10);
return x_11;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s7_satisfy_s9___spec__2(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s7_satisfy_s9___spec__2_s6___rarg), 6, 0);
return x_6;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s7_satisfy_s6___rarg_s11___lambda__1_s7___boxed(obj* x_0, obj* x_1, obj* x_2) {
{
unsigned x_3; obj* x_4; 
x_3 = lean::unbox_uint32(x_1);
x_4 = _l_s4_lean_s6_parser_s13_monad__parsec_s7_satisfy_s6___rarg_s11___lambda__1(x_0, x_3, x_2);
return x_4;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s2_ch_s6___rarg(obj* x_0, obj* x_1, unsigned x_2) {
{
obj* x_3; obj* x_5; obj* x_7; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
x_7 = _l_s4_lean_s6_parser_s13_monad__parsec_s10_left__over_s6___rarg_s11___closed__1;
lean::inc(x_7);
lean::inc(x_5);
x_10 = lean::apply_2(x_5, lean::box(0), x_7);
x_11 = lean::box_uint32(x_2);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s2_ch_s6___rarg_s11___lambda__1_s7___boxed), 5, 4);
lean::closure_set(x_12, 0, x_0);
lean::closure_set(x_12, 1, x_1);
lean::closure_set(x_12, 2, x_11);
lean::closure_set(x_12, 3, x_5);
x_13 = lean::apply_4(x_3, lean::box(0), lean::box(0), x_10, x_12);
return x_13;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s2_ch_s6___rarg_s11___lambda__1(obj* x_0, obj* x_1, unsigned x_2, obj* x_3, obj* x_4) {
{
unsigned char x_6; 
lean::dec(x_0);
x_6 = lean::string_iterator_has_next(x_4);
if (x_6 == 0)
{
obj* x_9; obj* x_10; obj* x_11; obj* x_15; 
lean::dec(x_4);
lean::dec(x_3);
x_9 = lean::box(0);
x_10 = _l_s4_lean_s6_parser_s13_monad__parsec_s10_eoi__error_s6___rarg_s11___closed__1;
x_11 = _l_s5_mjoin_s6___rarg_s11___closed__1;
lean::inc(x_9);
lean::inc(x_11);
lean::inc(x_10);
x_15 = _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s2_ch_s9___spec__1_s6___rarg(x_1, lean::box(0), x_10, x_11, x_9, x_9);
return x_15;
}
else
{
unsigned x_16; obj* x_17; obj* x_18; obj* x_19; 
x_16 = lean::string_iterator_curr(x_4);
x_17 = lean::box_uint32(x_16);
x_18 = lean::box_uint32(x_2);
x_19 = lean::nat_dec_eq(x_17, x_18);
lean::dec(x_18);
if (lean::obj_tag(x_19) == 0)
{
obj* x_25; obj* x_26; obj* x_28; obj* x_30; obj* x_31; obj* x_32; obj* x_35; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_17);
lean::dec(x_19);
x_25 = _l_s4_char_s11_quote__core(x_16);
x_26 = _l_s4_char_s9_has__repr_s11___closed__1;
lean::inc(x_26);
x_28 = lean::string_append(x_26, x_25);
lean::dec(x_25);
x_30 = lean::string_append(x_28, x_26);
x_31 = lean::box(0);
x_32 = _l_s5_mjoin_s6___rarg_s11___closed__1;
lean::inc(x_31);
lean::inc(x_32);
x_35 = _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s2_ch_s9___spec__2_s6___rarg(x_1, lean::box(0), x_30, x_32, x_31, x_31);
return x_35;
}
else
{
obj* x_38; obj* x_39; 
lean::dec(x_1);
lean::dec(x_19);
x_38 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s7_satisfy_s6___rarg_s11___lambda__1_s7___boxed), 3, 2);
lean::closure_set(x_38, 0, x_4);
lean::closure_set(x_38, 1, x_17);
x_39 = lean::apply_2(x_3, lean::box(0), x_38);
return x_39;
}
}
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s2_ch(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s2_ch_s6___rarg_s7___boxed), 3, 0);
return x_4;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s2_ch_s9___spec__1_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
{
obj* x_7; obj* x_10; obj* x_11; 
lean::dec(x_1);
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s6___rarg_s11___lambda__1), 5, 4);
lean::closure_set(x_10, 0, x_4);
lean::closure_set(x_10, 1, x_2);
lean::closure_set(x_10, 2, x_3);
lean::closure_set(x_10, 3, x_5);
x_11 = lean::apply_2(x_7, lean::box(0), x_10);
return x_11;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s2_ch_s9___spec__1(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s2_ch_s9___spec__1_s6___rarg), 6, 0);
return x_6;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s2_ch_s9___spec__2_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
{
obj* x_7; obj* x_10; obj* x_11; 
lean::dec(x_1);
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s6___rarg_s11___lambda__1), 5, 4);
lean::closure_set(x_10, 0, x_4);
lean::closure_set(x_10, 1, x_2);
lean::closure_set(x_10, 2, x_3);
lean::closure_set(x_10, 3, x_5);
x_11 = lean::apply_2(x_7, lean::box(0), x_10);
return x_11;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s2_ch_s9___spec__2(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s2_ch_s9___spec__2_s6___rarg), 6, 0);
return x_6;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s2_ch_s6___rarg_s7___boxed(obj* x_0, obj* x_1, obj* x_2) {
{
unsigned x_3; obj* x_4; 
x_3 = lean::unbox_uint32(x_2);
x_4 = _l_s4_lean_s6_parser_s13_monad__parsec_s2_ch_s6___rarg(x_0, x_1, x_3);
return x_4;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s2_ch_s6___rarg_s11___lambda__1_s7___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{
unsigned x_5; obj* x_6; 
x_5 = lean::unbox_uint32(x_2);
x_6 = _l_s4_lean_s6_parser_s13_monad__parsec_s2_ch_s6___rarg_s11___lambda__1(x_0, x_1, x_5, x_3, x_4);
return x_6;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_alpha_s6___rarg(obj* x_0, obj* x_1) {
{
obj* x_2; obj* x_4; obj* x_6; obj* x_9; obj* x_10; obj* x_11; 
x_2 = lean::cnstr_get(x_0, 1);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
x_6 = _l_s4_lean_s6_parser_s13_monad__parsec_s10_left__over_s6___rarg_s11___closed__1;
lean::inc(x_6);
lean::inc(x_4);
x_9 = lean::apply_2(x_4, lean::box(0), x_6);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s5_alpha_s6___rarg_s11___lambda__1), 4, 3);
lean::closure_set(x_10, 0, x_0);
lean::closure_set(x_10, 1, x_1);
lean::closure_set(x_10, 2, x_4);
x_11 = lean::apply_4(x_2, lean::box(0), lean::box(0), x_9, x_10);
return x_11;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_alpha_s6___rarg_s11___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{
unsigned char x_5; 
lean::dec(x_0);
x_5 = lean::string_iterator_has_next(x_3);
if (x_5 == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_14; 
lean::dec(x_2);
lean::dec(x_3);
x_8 = lean::box(0);
x_9 = _l_s4_lean_s6_parser_s13_monad__parsec_s10_eoi__error_s6___rarg_s11___closed__1;
x_10 = _l_s5_mjoin_s6___rarg_s11___closed__1;
lean::inc(x_8);
lean::inc(x_10);
lean::inc(x_9);
x_14 = _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s5_alpha_s9___spec__1_s6___rarg(x_1, lean::box(0), x_9, x_10, x_8, x_8);
return x_14;
}
else
{
unsigned x_15; unsigned char x_16; 
x_15 = lean::string_iterator_curr(x_3);
x_16 = _l_s4_char_s9_is__alpha(x_15);
if (x_16 == 0)
{
obj* x_19; obj* x_20; obj* x_22; obj* x_24; obj* x_25; obj* x_26; obj* x_29; 
lean::dec(x_2);
lean::dec(x_3);
x_19 = _l_s4_char_s11_quote__core(x_15);
x_20 = _l_s4_char_s9_has__repr_s11___closed__1;
lean::inc(x_20);
x_22 = lean::string_append(x_20, x_19);
lean::dec(x_19);
x_24 = lean::string_append(x_22, x_20);
x_25 = lean::box(0);
x_26 = _l_s5_mjoin_s6___rarg_s11___closed__1;
lean::inc(x_25);
lean::inc(x_26);
x_29 = _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s5_alpha_s9___spec__2_s6___rarg(x_1, lean::box(0), x_24, x_26, x_25, x_25);
return x_29;
}
else
{
obj* x_31; obj* x_32; obj* x_33; 
lean::dec(x_1);
x_31 = lean::box_uint32(x_15);
x_32 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s7_satisfy_s6___rarg_s11___lambda__1_s7___boxed), 3, 2);
lean::closure_set(x_32, 0, x_3);
lean::closure_set(x_32, 1, x_31);
x_33 = lean::apply_2(x_2, lean::box(0), x_32);
return x_33;
}
}
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_alpha(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s5_alpha_s6___rarg), 2, 0);
return x_4;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s5_alpha_s9___spec__1_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
{
obj* x_7; obj* x_10; obj* x_11; 
lean::dec(x_1);
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s6___rarg_s11___lambda__1), 5, 4);
lean::closure_set(x_10, 0, x_4);
lean::closure_set(x_10, 1, x_2);
lean::closure_set(x_10, 2, x_3);
lean::closure_set(x_10, 3, x_5);
x_11 = lean::apply_2(x_7, lean::box(0), x_10);
return x_11;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s5_alpha_s9___spec__1(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s5_alpha_s9___spec__1_s6___rarg), 6, 0);
return x_6;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s5_alpha_s9___spec__2_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
{
obj* x_7; obj* x_10; obj* x_11; 
lean::dec(x_1);
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s6___rarg_s11___lambda__1), 5, 4);
lean::closure_set(x_10, 0, x_4);
lean::closure_set(x_10, 1, x_2);
lean::closure_set(x_10, 2, x_3);
lean::closure_set(x_10, 3, x_5);
x_11 = lean::apply_2(x_7, lean::box(0), x_10);
return x_11;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s5_alpha_s9___spec__2(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s5_alpha_s9___spec__2_s6___rarg), 6, 0);
return x_6;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_digit_s6___rarg(obj* x_0, obj* x_1) {
{
obj* x_2; obj* x_4; obj* x_6; obj* x_9; obj* x_10; obj* x_11; 
x_2 = lean::cnstr_get(x_0, 1);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
x_6 = _l_s4_lean_s6_parser_s13_monad__parsec_s10_left__over_s6___rarg_s11___closed__1;
lean::inc(x_6);
lean::inc(x_4);
x_9 = lean::apply_2(x_4, lean::box(0), x_6);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s5_digit_s6___rarg_s11___lambda__1), 4, 3);
lean::closure_set(x_10, 0, x_0);
lean::closure_set(x_10, 1, x_1);
lean::closure_set(x_10, 2, x_4);
x_11 = lean::apply_4(x_2, lean::box(0), lean::box(0), x_9, x_10);
return x_11;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_digit_s6___rarg_s11___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{
unsigned char x_5; 
lean::dec(x_0);
x_5 = lean::string_iterator_has_next(x_3);
if (x_5 == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_14; 
lean::dec(x_2);
lean::dec(x_3);
x_8 = lean::box(0);
x_9 = _l_s4_lean_s6_parser_s13_monad__parsec_s10_eoi__error_s6___rarg_s11___closed__1;
x_10 = _l_s5_mjoin_s6___rarg_s11___closed__1;
lean::inc(x_8);
lean::inc(x_10);
lean::inc(x_9);
x_14 = _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s5_digit_s9___spec__1_s6___rarg(x_1, lean::box(0), x_9, x_10, x_8, x_8);
return x_14;
}
else
{
unsigned x_15; unsigned char x_16; 
x_15 = lean::string_iterator_curr(x_3);
x_16 = _l_s4_char_s9_is__digit(x_15);
if (x_16 == 0)
{
obj* x_19; obj* x_20; obj* x_22; obj* x_24; obj* x_25; obj* x_26; obj* x_29; 
lean::dec(x_2);
lean::dec(x_3);
x_19 = _l_s4_char_s11_quote__core(x_15);
x_20 = _l_s4_char_s9_has__repr_s11___closed__1;
lean::inc(x_20);
x_22 = lean::string_append(x_20, x_19);
lean::dec(x_19);
x_24 = lean::string_append(x_22, x_20);
x_25 = lean::box(0);
x_26 = _l_s5_mjoin_s6___rarg_s11___closed__1;
lean::inc(x_25);
lean::inc(x_26);
x_29 = _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s5_digit_s9___spec__2_s6___rarg(x_1, lean::box(0), x_24, x_26, x_25, x_25);
return x_29;
}
else
{
obj* x_31; obj* x_32; obj* x_33; 
lean::dec(x_1);
x_31 = lean::box_uint32(x_15);
x_32 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s7_satisfy_s6___rarg_s11___lambda__1_s7___boxed), 3, 2);
lean::closure_set(x_32, 0, x_3);
lean::closure_set(x_32, 1, x_31);
x_33 = lean::apply_2(x_2, lean::box(0), x_32);
return x_33;
}
}
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_digit(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s5_digit_s6___rarg), 2, 0);
return x_4;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s5_digit_s9___spec__1_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
{
obj* x_7; obj* x_10; obj* x_11; 
lean::dec(x_1);
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s6___rarg_s11___lambda__1), 5, 4);
lean::closure_set(x_10, 0, x_4);
lean::closure_set(x_10, 1, x_2);
lean::closure_set(x_10, 2, x_3);
lean::closure_set(x_10, 3, x_5);
x_11 = lean::apply_2(x_7, lean::box(0), x_10);
return x_11;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s5_digit_s9___spec__1(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s5_digit_s9___spec__1_s6___rarg), 6, 0);
return x_6;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s5_digit_s9___spec__2_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
{
obj* x_7; obj* x_10; obj* x_11; 
lean::dec(x_1);
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s6___rarg_s11___lambda__1), 5, 4);
lean::closure_set(x_10, 0, x_4);
lean::closure_set(x_10, 1, x_2);
lean::closure_set(x_10, 2, x_3);
lean::closure_set(x_10, 3, x_5);
x_11 = lean::apply_2(x_7, lean::box(0), x_10);
return x_11;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s5_digit_s9___spec__2(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s5_digit_s9___spec__2_s6___rarg), 6, 0);
return x_6;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_upper_s6___rarg(obj* x_0, obj* x_1) {
{
obj* x_2; obj* x_4; obj* x_6; obj* x_9; obj* x_10; obj* x_11; 
x_2 = lean::cnstr_get(x_0, 1);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
x_6 = _l_s4_lean_s6_parser_s13_monad__parsec_s10_left__over_s6___rarg_s11___closed__1;
lean::inc(x_6);
lean::inc(x_4);
x_9 = lean::apply_2(x_4, lean::box(0), x_6);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s5_upper_s6___rarg_s11___lambda__1), 4, 3);
lean::closure_set(x_10, 0, x_0);
lean::closure_set(x_10, 1, x_1);
lean::closure_set(x_10, 2, x_4);
x_11 = lean::apply_4(x_2, lean::box(0), lean::box(0), x_9, x_10);
return x_11;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_upper_s6___rarg_s11___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{
unsigned char x_5; 
lean::dec(x_0);
x_5 = lean::string_iterator_has_next(x_3);
if (x_5 == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_14; 
lean::dec(x_2);
lean::dec(x_3);
x_8 = lean::box(0);
x_9 = _l_s4_lean_s6_parser_s13_monad__parsec_s10_eoi__error_s6___rarg_s11___closed__1;
x_10 = _l_s5_mjoin_s6___rarg_s11___closed__1;
lean::inc(x_8);
lean::inc(x_10);
lean::inc(x_9);
x_14 = _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s5_upper_s9___spec__1_s6___rarg(x_1, lean::box(0), x_9, x_10, x_8, x_8);
return x_14;
}
else
{
unsigned x_15; unsigned char x_16; 
x_15 = lean::string_iterator_curr(x_3);
x_16 = _l_s4_char_s9_is__upper(x_15);
if (x_16 == 0)
{
obj* x_19; obj* x_20; obj* x_22; obj* x_24; obj* x_25; obj* x_26; obj* x_29; 
lean::dec(x_2);
lean::dec(x_3);
x_19 = _l_s4_char_s11_quote__core(x_15);
x_20 = _l_s4_char_s9_has__repr_s11___closed__1;
lean::inc(x_20);
x_22 = lean::string_append(x_20, x_19);
lean::dec(x_19);
x_24 = lean::string_append(x_22, x_20);
x_25 = lean::box(0);
x_26 = _l_s5_mjoin_s6___rarg_s11___closed__1;
lean::inc(x_25);
lean::inc(x_26);
x_29 = _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s5_upper_s9___spec__2_s6___rarg(x_1, lean::box(0), x_24, x_26, x_25, x_25);
return x_29;
}
else
{
obj* x_31; obj* x_32; obj* x_33; 
lean::dec(x_1);
x_31 = lean::box_uint32(x_15);
x_32 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s7_satisfy_s6___rarg_s11___lambda__1_s7___boxed), 3, 2);
lean::closure_set(x_32, 0, x_3);
lean::closure_set(x_32, 1, x_31);
x_33 = lean::apply_2(x_2, lean::box(0), x_32);
return x_33;
}
}
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_upper(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s5_upper_s6___rarg), 2, 0);
return x_4;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s5_upper_s9___spec__1_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
{
obj* x_7; obj* x_10; obj* x_11; 
lean::dec(x_1);
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s6___rarg_s11___lambda__1), 5, 4);
lean::closure_set(x_10, 0, x_4);
lean::closure_set(x_10, 1, x_2);
lean::closure_set(x_10, 2, x_3);
lean::closure_set(x_10, 3, x_5);
x_11 = lean::apply_2(x_7, lean::box(0), x_10);
return x_11;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s5_upper_s9___spec__1(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s5_upper_s9___spec__1_s6___rarg), 6, 0);
return x_6;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s5_upper_s9___spec__2_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
{
obj* x_7; obj* x_10; obj* x_11; 
lean::dec(x_1);
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s6___rarg_s11___lambda__1), 5, 4);
lean::closure_set(x_10, 0, x_4);
lean::closure_set(x_10, 1, x_2);
lean::closure_set(x_10, 2, x_3);
lean::closure_set(x_10, 3, x_5);
x_11 = lean::apply_2(x_7, lean::box(0), x_10);
return x_11;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s5_upper_s9___spec__2(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s5_upper_s9___spec__2_s6___rarg), 6, 0);
return x_6;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_lower_s6___rarg(obj* x_0, obj* x_1) {
{
obj* x_2; obj* x_4; obj* x_6; obj* x_9; obj* x_10; obj* x_11; 
x_2 = lean::cnstr_get(x_0, 1);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
x_6 = _l_s4_lean_s6_parser_s13_monad__parsec_s10_left__over_s6___rarg_s11___closed__1;
lean::inc(x_6);
lean::inc(x_4);
x_9 = lean::apply_2(x_4, lean::box(0), x_6);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s5_lower_s6___rarg_s11___lambda__1), 4, 3);
lean::closure_set(x_10, 0, x_0);
lean::closure_set(x_10, 1, x_1);
lean::closure_set(x_10, 2, x_4);
x_11 = lean::apply_4(x_2, lean::box(0), lean::box(0), x_9, x_10);
return x_11;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_lower_s6___rarg_s11___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{
unsigned char x_5; 
lean::dec(x_0);
x_5 = lean::string_iterator_has_next(x_3);
if (x_5 == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_14; 
lean::dec(x_2);
lean::dec(x_3);
x_8 = lean::box(0);
x_9 = _l_s4_lean_s6_parser_s13_monad__parsec_s10_eoi__error_s6___rarg_s11___closed__1;
x_10 = _l_s5_mjoin_s6___rarg_s11___closed__1;
lean::inc(x_8);
lean::inc(x_10);
lean::inc(x_9);
x_14 = _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s5_lower_s9___spec__1_s6___rarg(x_1, lean::box(0), x_9, x_10, x_8, x_8);
return x_14;
}
else
{
unsigned x_15; unsigned char x_16; 
x_15 = lean::string_iterator_curr(x_3);
x_16 = _l_s4_char_s9_is__lower(x_15);
if (x_16 == 0)
{
obj* x_19; obj* x_20; obj* x_22; obj* x_24; obj* x_25; obj* x_26; obj* x_29; 
lean::dec(x_2);
lean::dec(x_3);
x_19 = _l_s4_char_s11_quote__core(x_15);
x_20 = _l_s4_char_s9_has__repr_s11___closed__1;
lean::inc(x_20);
x_22 = lean::string_append(x_20, x_19);
lean::dec(x_19);
x_24 = lean::string_append(x_22, x_20);
x_25 = lean::box(0);
x_26 = _l_s5_mjoin_s6___rarg_s11___closed__1;
lean::inc(x_25);
lean::inc(x_26);
x_29 = _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s5_lower_s9___spec__2_s6___rarg(x_1, lean::box(0), x_24, x_26, x_25, x_25);
return x_29;
}
else
{
obj* x_31; obj* x_32; obj* x_33; 
lean::dec(x_1);
x_31 = lean::box_uint32(x_15);
x_32 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s7_satisfy_s6___rarg_s11___lambda__1_s7___boxed), 3, 2);
lean::closure_set(x_32, 0, x_3);
lean::closure_set(x_32, 1, x_31);
x_33 = lean::apply_2(x_2, lean::box(0), x_32);
return x_33;
}
}
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_lower(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s5_lower_s6___rarg), 2, 0);
return x_4;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s5_lower_s9___spec__1_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
{
obj* x_7; obj* x_10; obj* x_11; 
lean::dec(x_1);
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s6___rarg_s11___lambda__1), 5, 4);
lean::closure_set(x_10, 0, x_4);
lean::closure_set(x_10, 1, x_2);
lean::closure_set(x_10, 2, x_3);
lean::closure_set(x_10, 3, x_5);
x_11 = lean::apply_2(x_7, lean::box(0), x_10);
return x_11;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s5_lower_s9___spec__1(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s5_lower_s9___spec__1_s6___rarg), 6, 0);
return x_6;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s5_lower_s9___spec__2_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
{
obj* x_7; obj* x_10; obj* x_11; 
lean::dec(x_1);
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s6___rarg_s11___lambda__1), 5, 4);
lean::closure_set(x_10, 0, x_4);
lean::closure_set(x_10, 1, x_2);
lean::closure_set(x_10, 2, x_3);
lean::closure_set(x_10, 3, x_5);
x_11 = lean::apply_2(x_7, lean::box(0), x_10);
return x_11;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s5_lower_s9___spec__2(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s5_lower_s9___spec__2_s6___rarg), 6, 0);
return x_6;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s3_any_s6___rarg(obj* x_0, obj* x_1) {
{
obj* x_2; obj* x_4; obj* x_6; obj* x_9; obj* x_10; obj* x_11; 
x_2 = lean::cnstr_get(x_0, 1);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
x_6 = _l_s4_lean_s6_parser_s13_monad__parsec_s10_left__over_s6___rarg_s11___closed__1;
lean::inc(x_6);
lean::inc(x_4);
x_9 = lean::apply_2(x_4, lean::box(0), x_6);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s3_any_s6___rarg_s11___lambda__1), 4, 3);
lean::closure_set(x_10, 0, x_0);
lean::closure_set(x_10, 1, x_1);
lean::closure_set(x_10, 2, x_4);
x_11 = lean::apply_4(x_2, lean::box(0), lean::box(0), x_9, x_10);
return x_11;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s3_any_s6___rarg_s11___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{
unsigned char x_5; 
lean::dec(x_0);
x_5 = lean::string_iterator_has_next(x_3);
if (x_5 == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_14; 
lean::dec(x_2);
lean::dec(x_3);
x_8 = lean::box(0);
x_9 = _l_s4_lean_s6_parser_s13_monad__parsec_s10_eoi__error_s6___rarg_s11___closed__1;
x_10 = _l_s5_mjoin_s6___rarg_s11___closed__1;
lean::inc(x_8);
lean::inc(x_10);
lean::inc(x_9);
x_14 = _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s3_any_s9___spec__1_s6___rarg(x_1, lean::box(0), x_9, x_10, x_8, x_8);
return x_14;
}
else
{
unsigned x_15; obj* x_16; 
x_15 = lean::string_iterator_curr(x_3);
x_16 = _l_s4_true_s9_decidable;
if (lean::obj_tag(x_16) == 0)
{
obj* x_20; obj* x_21; obj* x_23; obj* x_25; obj* x_26; obj* x_27; obj* x_30; 
lean::dec(x_2);
lean::dec(x_3);
lean::dec(x_16);
x_20 = _l_s4_char_s11_quote__core(x_15);
x_21 = _l_s4_char_s9_has__repr_s11___closed__1;
lean::inc(x_21);
x_23 = lean::string_append(x_21, x_20);
lean::dec(x_20);
x_25 = lean::string_append(x_23, x_21);
x_26 = lean::box(0);
x_27 = _l_s5_mjoin_s6___rarg_s11___closed__1;
lean::inc(x_26);
lean::inc(x_27);
x_30 = _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s3_any_s9___spec__2_s6___rarg(x_1, lean::box(0), x_25, x_27, x_26, x_26);
return x_30;
}
else
{
obj* x_33; obj* x_34; obj* x_35; 
lean::dec(x_1);
lean::dec(x_16);
x_33 = lean::box_uint32(x_15);
x_34 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s7_satisfy_s6___rarg_s11___lambda__1_s7___boxed), 3, 2);
lean::closure_set(x_34, 0, x_3);
lean::closure_set(x_34, 1, x_33);
x_35 = lean::apply_2(x_2, lean::box(0), x_34);
return x_35;
}
}
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s3_any(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s3_any_s6___rarg), 2, 0);
return x_4;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s3_any_s9___spec__1_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
{
obj* x_7; obj* x_10; obj* x_11; 
lean::dec(x_1);
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s6___rarg_s11___lambda__1), 5, 4);
lean::closure_set(x_10, 0, x_4);
lean::closure_set(x_10, 1, x_2);
lean::closure_set(x_10, 2, x_3);
lean::closure_set(x_10, 3, x_5);
x_11 = lean::apply_2(x_7, lean::box(0), x_10);
return x_11;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s3_any_s9___spec__1(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s3_any_s9___spec__1_s6___rarg), 6, 0);
return x_6;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s3_any_s9___spec__2_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
{
obj* x_7; obj* x_10; obj* x_11; 
lean::dec(x_1);
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s6___rarg_s11___lambda__1), 5, 4);
lean::closure_set(x_10, 0, x_4);
lean::closure_set(x_10, 1, x_2);
lean::closure_set(x_10, 2, x_3);
lean::closure_set(x_10, 3, x_5);
x_11 = lean::apply_2(x_7, lean::box(0), x_10);
return x_11;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s3_any_s9___spec__2(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s3_any_s9___spec__2_s6___rarg), 6, 0);
return x_6;
}
}
obj* _l_s9___private_580269747__s8_str__aux_s6___main(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_3; obj* x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
lean::dec(x_3);
if (lean::obj_tag(x_4) == 0)
{
unsigned char x_7; 
lean::dec(x_4);
x_7 = lean::string_iterator_has_next(x_2);
if (x_7 == 0)
{
obj* x_11; 
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
x_11 = lean::box(0);
return x_11;
}
else
{
unsigned x_12; unsigned x_13; obj* x_14; obj* x_15; obj* x_16; 
x_12 = lean::string_iterator_curr(x_1);
x_13 = lean::string_iterator_curr(x_2);
x_14 = lean::box_uint32(x_12);
x_15 = lean::box_uint32(x_13);
x_16 = lean::nat_dec_eq(x_14, x_15);
lean::dec(x_15);
lean::dec(x_14);
if (lean::obj_tag(x_16) == 0)
{
obj* x_23; 
lean::dec(x_16);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
x_23 = lean::box(0);
return x_23;
}
else
{
obj* x_25; obj* x_26; obj* x_29; obj* x_30; obj* x_31; 
lean::dec(x_16);
x_25 = lean::mk_nat_obj(1u);
x_26 = lean::nat_sub(x_0, x_25);
lean::dec(x_25);
lean::dec(x_0);
x_29 = lean::string_iterator_next(x_1);
x_30 = lean::string_iterator_next(x_2);
x_31 = _l_s9___private_580269747__s8_str__aux_s6___main(x_26, x_29, x_30);
return x_31;
}
}
}
else
{
obj* x_35; 
lean::dec(x_4);
lean::dec(x_0);
lean::dec(x_1);
x_35 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_35, 0, x_2);
return x_35;
}
}
}
obj* _l_s9___private_580269747__s8_str__aux(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_3; 
x_3 = _l_s9___private_580269747__s8_str__aux_s6___main(x_0, x_1, x_2);
return x_3;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s9_str__core_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{
unsigned char x_5; 
lean::inc(x_2);
x_5 = _l_s6_string_s9_is__empty(x_2);
if (x_5 == 0)
{
obj* x_7; obj* x_10; obj* x_11; 
lean::dec(x_0);
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
lean::dec(x_1);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s9_str__core_s6___rarg_s11___lambda__1), 3, 2);
lean::closure_set(x_10, 0, x_2);
lean::closure_set(x_10, 1, x_3);
x_11 = lean::apply_2(x_7, lean::box(0), x_10);
return x_11;
}
else
{
obj* x_15; obj* x_18; obj* x_21; obj* x_23; 
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
x_15 = lean::cnstr_get(x_0, 0);
lean::inc(x_15);
lean::dec(x_0);
x_18 = lean::cnstr_get(x_15, 1);
lean::inc(x_18);
lean::dec(x_15);
x_21 = _l_s6_string_s4_join_s11___closed__1;
lean::inc(x_21);
x_23 = lean::apply_2(x_18, lean::box(0), x_21);
return x_23;
}
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s9_str__core_s6___rarg_s11___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_3; obj* x_5; obj* x_7; 
x_3 = lean::string_length(x_0);
lean::inc(x_0);
x_5 = lean::string_mk_iterator(x_0);
lean::inc(x_2);
x_7 = _l_s9___private_580269747__s8_str__aux_s6___main(x_3, x_5, x_2);
if (lean::obj_tag(x_7) == 0)
{
obj* x_10; obj* x_11; obj* x_13; unsigned char x_14; obj* x_15; obj* x_16; 
lean::dec(x_7);
lean::dec(x_0);
x_10 = lean::box(0);
x_11 = _l_s6_string_s4_join_s11___closed__1;
lean::inc(x_11);
x_13 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_13, 0, x_2);
lean::cnstr_set(x_13, 1, x_11);
lean::cnstr_set(x_13, 2, x_1);
lean::cnstr_set(x_13, 3, x_10);
x_14 = 0;
x_15 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_15, 0, x_13);
lean::cnstr_set_scalar(x_15, sizeof(void*)*1, x_14);
x_16 = x_15;
return x_16;
}
else
{
obj* x_19; obj* x_22; obj* x_23; 
lean::dec(x_1);
lean::dec(x_2);
x_19 = lean::cnstr_get(x_7, 0);
lean::inc(x_19);
lean::dec(x_7);
x_22 = lean::box(0);
x_23 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_23, 0, x_0);
lean::cnstr_set(x_23, 1, x_19);
lean::cnstr_set(x_23, 2, x_22);
return x_23;
}
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s9_str__core(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s9_str__core_s6___rarg), 4, 0);
return x_4;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s3_str_s6___rarg(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_4; obj* x_5; obj* x_6; 
lean::inc(x_2);
x_4 = _l_s6_string_s5_quote(x_2);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(_l_s5_dlist_s9_singleton_s6___rarg), 2, 1);
lean::closure_set(x_5, 0, x_4);
x_6 = _l_s4_lean_s6_parser_s13_monad__parsec_s9_str__core_s6___rarg(x_0, x_1, x_2, x_5);
return x_6;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s3_str(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s3_str_s6___rarg), 3, 0);
return x_4;
}
}
obj* _l_s9___private_127590107__s9_take__aux_s6___main_s6___rarg(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_3; obj* x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
lean::dec(x_3);
if (lean::obj_tag(x_4) == 0)
{
unsigned char x_7; 
lean::dec(x_4);
x_7 = lean::string_iterator_has_next(x_2);
if (x_7 == 0)
{
obj* x_10; 
lean::dec(x_0);
lean::dec(x_1);
x_10 = _l_s4_lean_s6_parser_s13_monad__parsec_s10_eoi__error_s6___rarg(x_2);
return x_10;
}
else
{
obj* x_11; obj* x_12; unsigned x_15; obj* x_16; obj* x_17; obj* x_18; 
x_11 = lean::mk_nat_obj(1u);
x_12 = lean::nat_sub(x_0, x_11);
lean::dec(x_11);
lean::dec(x_0);
x_15 = lean::string_iterator_curr(x_2);
x_16 = lean::string_push(x_1, x_15);
x_17 = lean::string_iterator_next(x_2);
x_18 = _l_s9___private_127590107__s9_take__aux_s6___main_s6___rarg(x_12, x_16, x_17);
return x_18;
}
}
else
{
obj* x_21; obj* x_22; 
lean::dec(x_4);
lean::dec(x_0);
x_21 = lean::box(0);
x_22 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_22, 0, x_1);
lean::cnstr_set(x_22, 1, x_2);
lean::cnstr_set(x_22, 2, x_21);
return x_22;
}
}
}
obj* _l_s9___private_127590107__s9_take__aux_s6___main(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9___private_127590107__s9_take__aux_s6___main_s6___rarg), 3, 0);
return x_2;
}
}
obj* _l_s9___private_127590107__s9_take__aux_s6___rarg(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_3; 
x_3 = _l_s9___private_127590107__s9_take__aux_s6___main_s6___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* _l_s9___private_127590107__s9_take__aux(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9___private_127590107__s9_take__aux_s6___rarg), 3, 0);
return x_2;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s4_take_s6___rarg(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_3; obj* x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_2, x_3);
lean::dec(x_3);
if (lean::obj_tag(x_4) == 0)
{
obj* x_8; obj* x_11; obj* x_13; obj* x_14; 
lean::dec(x_4);
lean::dec(x_0);
x_8 = lean::cnstr_get(x_1, 0);
lean::inc(x_8);
lean::dec(x_1);
x_11 = _l_s6_string_s4_join_s11___closed__1;
lean::inc(x_11);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9___private_127590107__s9_take__aux_s6___rarg), 3, 2);
lean::closure_set(x_13, 0, x_2);
lean::closure_set(x_13, 1, x_11);
x_14 = lean::apply_2(x_8, lean::box(0), x_13);
return x_14;
}
else
{
obj* x_18; obj* x_21; obj* x_24; obj* x_26; 
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_2);
x_18 = lean::cnstr_get(x_0, 0);
lean::inc(x_18);
lean::dec(x_0);
x_21 = lean::cnstr_get(x_18, 1);
lean::inc(x_21);
lean::dec(x_18);
x_24 = _l_s6_string_s4_join_s11___closed__1;
lean::inc(x_24);
x_26 = lean::apply_2(x_21, lean::box(0), x_24);
return x_26;
}
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s4_take(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s4_take_s6___rarg), 3, 0);
return x_4;
}
}
obj* _l_s9___private_2142412293__s18_mk__string__result_s6___rarg(obj* x_0, obj* x_1) {
{
unsigned char x_3; 
lean::inc(x_0);
x_3 = _l_s6_string_s9_is__empty(x_0);
if (x_3 == 0)
{
obj* x_4; obj* x_5; 
x_4 = lean::box(0);
x_5 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_5, 0, x_0);
lean::cnstr_set(x_5, 1, x_1);
lean::cnstr_set(x_5, 2, x_4);
return x_5;
}
else
{
obj* x_6; obj* x_8; 
x_6 = _l_s4_lean_s6_parser_s6_parsec_s6_result_s7_mk__eps_s6___rarg_s11___closed__1;
lean::inc(x_6);
x_8 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_8, 0, x_0);
lean::cnstr_set(x_8, 1, x_1);
lean::cnstr_set(x_8, 2, x_6);
return x_8;
}
}
}
obj* _l_s9___private_2142412293__s18_mk__string__result(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9___private_2142412293__s18_mk__string__result_s6___rarg), 2, 0);
return x_2;
}
}
obj* _l_s9___private_31565857__s16_take__while__aux_s6___main_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{
obj* x_4; obj* x_5; 
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::nat_dec_eq(x_1, x_4);
lean::dec(x_4);
if (lean::obj_tag(x_5) == 0)
{
unsigned char x_8; 
lean::dec(x_5);
x_8 = lean::string_iterator_has_next(x_3);
if (x_8 == 0)
{
obj* x_11; 
lean::dec(x_0);
lean::dec(x_1);
x_11 = _l_s9___private_2142412293__s18_mk__string__result_s6___rarg(x_2, x_3);
return x_11;
}
else
{
unsigned x_12; obj* x_13; obj* x_15; unsigned char x_16; 
x_12 = lean::string_iterator_curr(x_3);
x_13 = lean::box_uint32(x_12);
lean::inc(x_0);
x_15 = lean::apply_1(x_0, x_13);
x_16 = lean::unbox(x_15);
lean::dec(x_15);
if (x_16 == 0)
{
obj* x_20; 
lean::dec(x_0);
lean::dec(x_1);
x_20 = _l_s9___private_2142412293__s18_mk__string__result_s6___rarg(x_2, x_3);
return x_20;
}
else
{
obj* x_21; obj* x_22; obj* x_25; obj* x_26; obj* x_27; 
x_21 = lean::mk_nat_obj(1u);
x_22 = lean::nat_sub(x_1, x_21);
lean::dec(x_21);
lean::dec(x_1);
x_25 = lean::string_push(x_2, x_12);
x_26 = lean::string_iterator_next(x_3);
x_27 = _l_s9___private_31565857__s16_take__while__aux_s6___main_s6___rarg(x_0, x_22, x_25, x_26);
return x_27;
}
}
}
else
{
obj* x_31; 
lean::dec(x_5);
lean::dec(x_0);
lean::dec(x_1);
x_31 = _l_s9___private_2142412293__s18_mk__string__result_s6___rarg(x_2, x_3);
return x_31;
}
}
}
obj* _l_s9___private_31565857__s16_take__while__aux_s6___main(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9___private_31565857__s16_take__while__aux_s6___main_s6___rarg), 4, 0);
return x_2;
}
}
obj* _l_s9___private_31565857__s16_take__while__aux_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{
obj* x_4; 
x_4 = _l_s9___private_31565857__s16_take__while__aux_s6___main_s6___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* _l_s9___private_31565857__s16_take__while__aux(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9___private_31565857__s16_take__while__aux_s6___rarg), 4, 0);
return x_2;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s11_take__while_s6___rarg(obj* x_0, obj* x_1) {
{
obj* x_2; obj* x_5; obj* x_6; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s11_take__while_s6___rarg_s11___lambda__1), 2, 1);
lean::closure_set(x_5, 0, x_1);
x_6 = lean::apply_2(x_2, lean::box(0), x_5);
return x_6;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s11_take__while_s6___rarg_s11___lambda__1(obj* x_0, obj* x_1) {
{
obj* x_2; obj* x_3; obj* x_5; 
x_2 = lean::string_iterator_remaining(x_1);
x_3 = _l_s6_string_s4_join_s11___closed__1;
lean::inc(x_3);
x_5 = _l_s9___private_31565857__s16_take__while__aux_s6___main_s6___rarg(x_0, x_2, x_3, x_1);
return x_5;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s11_take__while(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s11_take__while_s6___rarg), 2, 0);
return x_6;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s17_take__while__cont_s6___rarg(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_3; obj* x_6; obj* x_7; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s17_take__while__cont_s6___rarg_s11___lambda__1), 3, 2);
lean::closure_set(x_6, 0, x_1);
lean::closure_set(x_6, 1, x_2);
x_7 = lean::apply_2(x_3, lean::box(0), x_6);
return x_7;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s17_take__while__cont_s6___rarg_s11___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_3; obj* x_4; 
x_3 = lean::string_iterator_remaining(x_2);
x_4 = _l_s9___private_31565857__s16_take__while__aux_s6___main_s6___rarg(x_0, x_3, x_1, x_2);
return x_4;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s17_take__while__cont(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s17_take__while__cont_s6___rarg), 3, 0);
return x_6;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s12_take__while1_s6___rarg(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_3; obj* x_5; obj* x_7; obj* x_10; obj* x_13; obj* x_15; obj* x_16; obj* x_17; 
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
x_7 = _l_s4_lean_s6_parser_s13_monad__parsec_s10_left__over_s6___rarg_s11___closed__1;
lean::inc(x_7);
lean::inc(x_5);
x_10 = lean::apply_2(x_5, lean::box(0), x_7);
lean::inc(x_2);
lean::inc(x_1);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s12_take__while1_s6___rarg_s11___lambda__1), 5, 4);
lean::closure_set(x_13, 0, x_0);
lean::closure_set(x_13, 1, x_1);
lean::closure_set(x_13, 2, x_2);
lean::closure_set(x_13, 3, x_5);
lean::inc(x_3);
x_15 = lean::apply_4(x_3, lean::box(0), lean::box(0), x_10, x_13);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s12_take__while1_s6___rarg_s11___lambda__2_s7___boxed), 3, 2);
lean::closure_set(x_16, 0, x_1);
lean::closure_set(x_16, 1, x_2);
x_17 = lean::apply_4(x_3, lean::box(0), lean::box(0), x_15, x_16);
return x_17;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s12_take__while1_s6___rarg_s11___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{
unsigned char x_6; 
lean::dec(x_0);
x_6 = lean::string_iterator_has_next(x_4);
if (x_6 == 0)
{
obj* x_10; obj* x_11; obj* x_12; obj* x_16; 
lean::dec(x_4);
lean::dec(x_2);
lean::dec(x_3);
x_10 = lean::box(0);
x_11 = _l_s4_lean_s6_parser_s13_monad__parsec_s10_eoi__error_s6___rarg_s11___closed__1;
x_12 = _l_s5_mjoin_s6___rarg_s11___closed__1;
lean::inc(x_10);
lean::inc(x_12);
lean::inc(x_11);
x_16 = _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s12_take__while1_s9___spec__1_s6___rarg(x_1, lean::box(0), x_11, x_12, x_10, x_10);
return x_16;
}
else
{
unsigned x_17; obj* x_18; obj* x_20; unsigned char x_21; 
x_17 = lean::string_iterator_curr(x_4);
x_18 = lean::box_uint32(x_17);
lean::inc(x_18);
x_20 = lean::apply_1(x_2, x_18);
x_21 = lean::unbox(x_20);
lean::dec(x_20);
if (x_21 == 0)
{
obj* x_26; obj* x_27; obj* x_29; obj* x_31; obj* x_32; obj* x_33; obj* x_36; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_18);
x_26 = _l_s4_char_s11_quote__core(x_17);
x_27 = _l_s4_char_s9_has__repr_s11___closed__1;
lean::inc(x_27);
x_29 = lean::string_append(x_27, x_26);
lean::dec(x_26);
x_31 = lean::string_append(x_29, x_27);
x_32 = lean::box(0);
x_33 = _l_s5_mjoin_s6___rarg_s11___closed__1;
lean::inc(x_32);
lean::inc(x_33);
x_36 = _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s12_take__while1_s9___spec__2_s6___rarg(x_1, lean::box(0), x_31, x_33, x_32, x_32);
return x_36;
}
else
{
obj* x_38; obj* x_39; 
lean::dec(x_1);
x_38 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s7_satisfy_s6___rarg_s11___lambda__1_s7___boxed), 3, 2);
lean::closure_set(x_38, 0, x_4);
lean::closure_set(x_38, 1, x_18);
x_39 = lean::apply_2(x_3, lean::box(0), x_38);
return x_39;
}
}
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s12_take__while1_s6___rarg_s11___lambda__2(obj* x_0, obj* x_1, unsigned x_2) {
{
obj* x_3; obj* x_5; obj* x_6; 
x_3 = _l_s6_string_s4_join_s11___closed__1;
lean::inc(x_3);
x_5 = lean::string_push(x_3, x_2);
x_6 = _l_s4_lean_s6_parser_s13_monad__parsec_s17_take__while__cont_s6___rarg(x_0, x_1, x_5);
return x_6;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s12_take__while1(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s12_take__while1_s6___rarg), 3, 0);
return x_4;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s12_take__while1_s9___spec__1_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
{
obj* x_7; obj* x_10; obj* x_11; 
lean::dec(x_1);
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s6___rarg_s11___lambda__1), 5, 4);
lean::closure_set(x_10, 0, x_4);
lean::closure_set(x_10, 1, x_2);
lean::closure_set(x_10, 2, x_3);
lean::closure_set(x_10, 3, x_5);
x_11 = lean::apply_2(x_7, lean::box(0), x_10);
return x_11;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s12_take__while1_s9___spec__1(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s12_take__while1_s9___spec__1_s6___rarg), 6, 0);
return x_6;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s12_take__while1_s9___spec__2_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
{
obj* x_7; obj* x_10; obj* x_11; 
lean::dec(x_1);
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s6___rarg_s11___lambda__1), 5, 4);
lean::closure_set(x_10, 0, x_4);
lean::closure_set(x_10, 1, x_2);
lean::closure_set(x_10, 2, x_3);
lean::closure_set(x_10, 3, x_5);
x_11 = lean::apply_2(x_7, lean::box(0), x_10);
return x_11;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s12_take__while1_s9___spec__2(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s12_take__while1_s9___spec__2_s6___rarg), 6, 0);
return x_6;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s12_take__while1_s6___rarg_s11___lambda__2_s7___boxed(obj* x_0, obj* x_1, obj* x_2) {
{
unsigned x_3; obj* x_4; 
x_3 = lean::unbox_uint32(x_2);
x_4 = _l_s4_lean_s6_parser_s13_monad__parsec_s12_take__while1_s6___rarg_s11___lambda__2(x_0, x_1, x_3);
return x_4;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s11_take__until_s6___rarg(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_4; 
lean::dec(x_0);
x_4 = _l_s4_lean_s6_parser_s13_monad__parsec_s11_take__while_s4___at_s4_lean_s6_parser_s13_monad__parsec_s11_take__until_s9___spec__1_s6___rarg(x_1, x_2);
return x_4;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s11_take__until(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s11_take__until_s6___rarg), 3, 0);
return x_4;
}
}
obj* _l_s9___private_31565857__s16_take__while__aux_s6___main_s4___at_s4_lean_s6_parser_s13_monad__parsec_s11_take__until_s9___spec__2_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{
obj* x_4; obj* x_5; 
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::nat_dec_eq(x_1, x_4);
lean::dec(x_4);
if (lean::obj_tag(x_5) == 0)
{
unsigned char x_8; 
lean::dec(x_5);
x_8 = lean::string_iterator_has_next(x_3);
if (x_8 == 0)
{
obj* x_11; 
lean::dec(x_0);
lean::dec(x_1);
x_11 = _l_s9___private_2142412293__s18_mk__string__result_s6___rarg(x_2, x_3);
return x_11;
}
else
{
unsigned x_12; obj* x_13; obj* x_15; unsigned char x_16; 
x_12 = lean::string_iterator_curr(x_3);
x_13 = lean::box_uint32(x_12);
lean::inc(x_0);
x_15 = lean::apply_1(x_0, x_13);
x_16 = lean::unbox(x_15);
lean::dec(x_15);
if (x_16 == 0)
{
obj* x_18; obj* x_19; obj* x_22; obj* x_23; obj* x_24; 
x_18 = lean::mk_nat_obj(1u);
x_19 = lean::nat_sub(x_1, x_18);
lean::dec(x_18);
lean::dec(x_1);
x_22 = lean::string_push(x_2, x_12);
x_23 = lean::string_iterator_next(x_3);
x_24 = _l_s9___private_31565857__s16_take__while__aux_s6___main_s4___at_s4_lean_s6_parser_s13_monad__parsec_s11_take__until_s9___spec__2_s6___rarg(x_0, x_19, x_22, x_23);
return x_24;
}
else
{
obj* x_27; 
lean::dec(x_0);
lean::dec(x_1);
x_27 = _l_s9___private_2142412293__s18_mk__string__result_s6___rarg(x_2, x_3);
return x_27;
}
}
}
else
{
obj* x_31; 
lean::dec(x_5);
lean::dec(x_0);
lean::dec(x_1);
x_31 = _l_s9___private_2142412293__s18_mk__string__result_s6___rarg(x_2, x_3);
return x_31;
}
}
}
obj* _l_s9___private_31565857__s16_take__while__aux_s6___main_s4___at_s4_lean_s6_parser_s13_monad__parsec_s11_take__until_s9___spec__2(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9___private_31565857__s16_take__while__aux_s6___main_s4___at_s4_lean_s6_parser_s13_monad__parsec_s11_take__until_s9___spec__2_s6___rarg), 4, 0);
return x_2;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s11_take__while_s4___at_s4_lean_s6_parser_s13_monad__parsec_s11_take__until_s9___spec__1_s6___rarg(obj* x_0, obj* x_1) {
{
obj* x_2; obj* x_5; obj* x_6; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s11_take__while_s4___at_s4_lean_s6_parser_s13_monad__parsec_s11_take__until_s9___spec__1_s6___rarg_s11___lambda__1), 2, 1);
lean::closure_set(x_5, 0, x_1);
x_6 = lean::apply_2(x_2, lean::box(0), x_5);
return x_6;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s11_take__while_s4___at_s4_lean_s6_parser_s13_monad__parsec_s11_take__until_s9___spec__1_s6___rarg_s11___lambda__1(obj* x_0, obj* x_1) {
{
obj* x_2; obj* x_3; obj* x_5; 
x_2 = lean::string_iterator_remaining(x_1);
x_3 = _l_s6_string_s4_join_s11___closed__1;
lean::inc(x_3);
x_5 = _l_s9___private_31565857__s16_take__while__aux_s6___main_s4___at_s4_lean_s6_parser_s13_monad__parsec_s11_take__until_s9___spec__2_s6___rarg(x_0, x_2, x_3, x_1);
return x_5;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s11_take__while_s4___at_s4_lean_s6_parser_s13_monad__parsec_s11_take__until_s9___spec__1(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s11_take__while_s4___at_s4_lean_s6_parser_s13_monad__parsec_s11_take__until_s9___spec__1_s6___rarg), 2, 0);
return x_6;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s12_take__until1_s6___rarg(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_3; 
x_3 = _l_s4_lean_s6_parser_s13_monad__parsec_s12_take__while1_s4___at_s4_lean_s6_parser_s13_monad__parsec_s12_take__until1_s9___spec__1_s6___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s12_take__until1(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s12_take__until1_s6___rarg), 3, 0);
return x_4;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s12_take__until1_s9___spec__2_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
{
obj* x_7; obj* x_10; obj* x_11; 
lean::dec(x_1);
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s6___rarg_s11___lambda__1), 5, 4);
lean::closure_set(x_10, 0, x_4);
lean::closure_set(x_10, 1, x_2);
lean::closure_set(x_10, 2, x_3);
lean::closure_set(x_10, 3, x_5);
x_11 = lean::apply_2(x_7, lean::box(0), x_10);
return x_11;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s12_take__until1_s9___spec__2(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s12_take__until1_s9___spec__2_s6___rarg), 6, 0);
return x_6;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s12_take__until1_s9___spec__3_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
{
obj* x_7; obj* x_10; obj* x_11; 
lean::dec(x_1);
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s6___rarg_s11___lambda__1), 5, 4);
lean::closure_set(x_10, 0, x_4);
lean::closure_set(x_10, 1, x_2);
lean::closure_set(x_10, 2, x_3);
lean::closure_set(x_10, 3, x_5);
x_11 = lean::apply_2(x_7, lean::box(0), x_10);
return x_11;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s12_take__until1_s9___spec__3(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s12_take__until1_s9___spec__3_s6___rarg), 6, 0);
return x_6;
}
}
obj* _l_s9___private_31565857__s16_take__while__aux_s6___main_s4___at_s4_lean_s6_parser_s13_monad__parsec_s12_take__until1_s9___spec__5_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{
obj* x_4; obj* x_5; 
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::nat_dec_eq(x_1, x_4);
lean::dec(x_4);
if (lean::obj_tag(x_5) == 0)
{
unsigned char x_8; 
lean::dec(x_5);
x_8 = lean::string_iterator_has_next(x_3);
if (x_8 == 0)
{
obj* x_11; 
lean::dec(x_0);
lean::dec(x_1);
x_11 = _l_s9___private_2142412293__s18_mk__string__result_s6___rarg(x_2, x_3);
return x_11;
}
else
{
unsigned x_12; obj* x_13; obj* x_15; unsigned char x_16; 
x_12 = lean::string_iterator_curr(x_3);
x_13 = lean::box_uint32(x_12);
lean::inc(x_0);
x_15 = lean::apply_1(x_0, x_13);
x_16 = lean::unbox(x_15);
lean::dec(x_15);
if (x_16 == 0)
{
obj* x_18; obj* x_19; obj* x_22; obj* x_23; obj* x_24; 
x_18 = lean::mk_nat_obj(1u);
x_19 = lean::nat_sub(x_1, x_18);
lean::dec(x_18);
lean::dec(x_1);
x_22 = lean::string_push(x_2, x_12);
x_23 = lean::string_iterator_next(x_3);
x_24 = _l_s9___private_31565857__s16_take__while__aux_s6___main_s4___at_s4_lean_s6_parser_s13_monad__parsec_s12_take__until1_s9___spec__5_s6___rarg(x_0, x_19, x_22, x_23);
return x_24;
}
else
{
obj* x_27; 
lean::dec(x_0);
lean::dec(x_1);
x_27 = _l_s9___private_2142412293__s18_mk__string__result_s6___rarg(x_2, x_3);
return x_27;
}
}
}
else
{
obj* x_31; 
lean::dec(x_5);
lean::dec(x_0);
lean::dec(x_1);
x_31 = _l_s9___private_2142412293__s18_mk__string__result_s6___rarg(x_2, x_3);
return x_31;
}
}
}
obj* _l_s9___private_31565857__s16_take__while__aux_s6___main_s4___at_s4_lean_s6_parser_s13_monad__parsec_s12_take__until1_s9___spec__5(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9___private_31565857__s16_take__while__aux_s6___main_s4___at_s4_lean_s6_parser_s13_monad__parsec_s12_take__until1_s9___spec__5_s6___rarg), 4, 0);
return x_2;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s17_take__while__cont_s4___at_s4_lean_s6_parser_s13_monad__parsec_s12_take__until1_s9___spec__4_s6___rarg(obj* x_0, obj* x_1, unsigned x_2) {
{
obj* x_3; obj* x_5; obj* x_6; obj* x_9; obj* x_10; 
x_3 = _l_s6_string_s4_join_s11___closed__1;
lean::inc(x_3);
x_5 = lean::string_push(x_3, x_2);
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
lean::dec(x_0);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s17_take__while__cont_s4___at_s4_lean_s6_parser_s13_monad__parsec_s12_take__until1_s9___spec__4_s6___rarg_s11___lambda__1), 3, 2);
lean::closure_set(x_9, 0, x_1);
lean::closure_set(x_9, 1, x_5);
x_10 = lean::apply_2(x_6, lean::box(0), x_9);
return x_10;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s17_take__while__cont_s4___at_s4_lean_s6_parser_s13_monad__parsec_s12_take__until1_s9___spec__4_s6___rarg_s11___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_3; obj* x_4; 
x_3 = lean::string_iterator_remaining(x_2);
x_4 = _l_s9___private_31565857__s16_take__while__aux_s6___main_s4___at_s4_lean_s6_parser_s13_monad__parsec_s12_take__until1_s9___spec__5_s6___rarg(x_0, x_3, x_1, x_2);
return x_4;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s17_take__while__cont_s4___at_s4_lean_s6_parser_s13_monad__parsec_s12_take__until1_s9___spec__4(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s17_take__while__cont_s4___at_s4_lean_s6_parser_s13_monad__parsec_s12_take__until1_s9___spec__4_s6___rarg_s7___boxed), 3, 0);
return x_6;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s12_take__while1_s4___at_s4_lean_s6_parser_s13_monad__parsec_s12_take__until1_s9___spec__1_s6___rarg(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_3; obj* x_5; obj* x_7; obj* x_10; obj* x_13; obj* x_15; obj* x_16; obj* x_17; 
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
x_7 = _l_s4_lean_s6_parser_s13_monad__parsec_s10_left__over_s6___rarg_s11___closed__1;
lean::inc(x_7);
lean::inc(x_5);
x_10 = lean::apply_2(x_5, lean::box(0), x_7);
lean::inc(x_2);
lean::inc(x_1);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s12_take__while1_s4___at_s4_lean_s6_parser_s13_monad__parsec_s12_take__until1_s9___spec__1_s6___rarg_s11___lambda__1), 5, 4);
lean::closure_set(x_13, 0, x_0);
lean::closure_set(x_13, 1, x_1);
lean::closure_set(x_13, 2, x_2);
lean::closure_set(x_13, 3, x_5);
lean::inc(x_3);
x_15 = lean::apply_4(x_3, lean::box(0), lean::box(0), x_10, x_13);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s17_take__while__cont_s4___at_s4_lean_s6_parser_s13_monad__parsec_s12_take__until1_s9___spec__4_s6___rarg_s7___boxed), 3, 2);
lean::closure_set(x_16, 0, x_1);
lean::closure_set(x_16, 1, x_2);
x_17 = lean::apply_4(x_3, lean::box(0), lean::box(0), x_15, x_16);
return x_17;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s12_take__while1_s4___at_s4_lean_s6_parser_s13_monad__parsec_s12_take__until1_s9___spec__1_s6___rarg_s11___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{
unsigned char x_6; 
lean::dec(x_0);
x_6 = lean::string_iterator_has_next(x_4);
if (x_6 == 0)
{
obj* x_10; obj* x_11; obj* x_12; obj* x_16; 
lean::dec(x_4);
lean::dec(x_2);
lean::dec(x_3);
x_10 = lean::box(0);
x_11 = _l_s4_lean_s6_parser_s13_monad__parsec_s10_eoi__error_s6___rarg_s11___closed__1;
x_12 = _l_s5_mjoin_s6___rarg_s11___closed__1;
lean::inc(x_10);
lean::inc(x_12);
lean::inc(x_11);
x_16 = _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s12_take__until1_s9___spec__2_s6___rarg(x_1, lean::box(0), x_11, x_12, x_10, x_10);
return x_16;
}
else
{
unsigned x_17; obj* x_18; obj* x_20; unsigned char x_21; 
x_17 = lean::string_iterator_curr(x_4);
x_18 = lean::box_uint32(x_17);
lean::inc(x_18);
x_20 = lean::apply_1(x_2, x_18);
x_21 = lean::unbox(x_20);
lean::dec(x_20);
if (x_21 == 0)
{
obj* x_24; obj* x_25; 
lean::dec(x_1);
x_24 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s7_satisfy_s6___rarg_s11___lambda__1_s7___boxed), 3, 2);
lean::closure_set(x_24, 0, x_4);
lean::closure_set(x_24, 1, x_18);
x_25 = lean::apply_2(x_3, lean::box(0), x_24);
return x_25;
}
else
{
obj* x_29; obj* x_30; obj* x_32; obj* x_34; obj* x_35; obj* x_36; obj* x_39; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_18);
x_29 = _l_s4_char_s11_quote__core(x_17);
x_30 = _l_s4_char_s9_has__repr_s11___closed__1;
lean::inc(x_30);
x_32 = lean::string_append(x_30, x_29);
lean::dec(x_29);
x_34 = lean::string_append(x_32, x_30);
x_35 = lean::box(0);
x_36 = _l_s5_mjoin_s6___rarg_s11___closed__1;
lean::inc(x_35);
lean::inc(x_36);
x_39 = _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s12_take__until1_s9___spec__3_s6___rarg(x_1, lean::box(0), x_34, x_36, x_35, x_35);
return x_39;
}
}
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s12_take__while1_s4___at_s4_lean_s6_parser_s13_monad__parsec_s12_take__until1_s9___spec__1(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s12_take__while1_s4___at_s4_lean_s6_parser_s13_monad__parsec_s12_take__until1_s9___spec__1_s6___rarg), 3, 0);
return x_4;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s17_take__while__cont_s4___at_s4_lean_s6_parser_s13_monad__parsec_s12_take__until1_s9___spec__4_s6___rarg_s7___boxed(obj* x_0, obj* x_1, obj* x_2) {
{
unsigned x_3; obj* x_4; 
x_3 = lean::unbox_uint32(x_2);
x_4 = _l_s4_lean_s6_parser_s13_monad__parsec_s17_take__while__cont_s4___at_s4_lean_s6_parser_s13_monad__parsec_s12_take__until1_s9___spec__4_s6___rarg(x_0, x_1, x_3);
return x_4;
}
}
obj* _l_s9___private_2038417741__s20_mk__consumed__result_s6___rarg(unsigned char x_0, obj* x_1) {
{

if (x_0 == 0)
{
unsigned char x_2; obj* x_3; obj* x_4; obj* x_6; 
x_2 = 0;
x_3 = _l_s4_lean_s6_parser_s6_parsec_s6_result_s7_mk__eps_s6___rarg_s11___closed__1;
x_4 = lean::box(x_2);
lean::inc(x_3);
x_6 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_6, 0, x_4);
lean::cnstr_set(x_6, 1, x_1);
lean::cnstr_set(x_6, 2, x_3);
return x_6;
}
else
{
obj* x_7; unsigned char x_8; obj* x_9; obj* x_10; 
x_7 = lean::box(0);
x_8 = 0;
x_9 = lean::box(x_8);
x_10 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_1);
lean::cnstr_set(x_10, 2, x_7);
return x_10;
}
}
}
obj* _l_s9___private_2038417741__s20_mk__consumed__result(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9___private_2038417741__s20_mk__consumed__result_s6___rarg_s7___boxed), 2, 0);
return x_2;
}
}
obj* _l_s9___private_2038417741__s20_mk__consumed__result_s6___rarg_s7___boxed(obj* x_0, obj* x_1) {
{
unsigned char x_2; obj* x_3; 
x_2 = lean::unbox(x_0);
x_3 = _l_s9___private_2038417741__s20_mk__consumed__result_s6___rarg(x_2, x_1);
return x_3;
}
}
obj* _l_s9___private_1695453085__s20_take__while__aux_x27_s6___main_s6___rarg(obj* x_0, obj* x_1, unsigned char x_2, obj* x_3) {
{
obj* x_4; obj* x_5; 
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::nat_dec_eq(x_1, x_4);
lean::dec(x_4);
if (lean::obj_tag(x_5) == 0)
{
unsigned char x_8; 
lean::dec(x_5);
x_8 = lean::string_iterator_has_next(x_3);
if (x_8 == 0)
{
obj* x_11; 
lean::dec(x_0);
lean::dec(x_1);
x_11 = _l_s9___private_2038417741__s20_mk__consumed__result_s6___rarg(x_2, x_3);
return x_11;
}
else
{
unsigned x_12; obj* x_13; obj* x_15; unsigned char x_16; 
x_12 = lean::string_iterator_curr(x_3);
x_13 = lean::box_uint32(x_12);
lean::inc(x_0);
x_15 = lean::apply_1(x_0, x_13);
x_16 = lean::unbox(x_15);
lean::dec(x_15);
if (x_16 == 0)
{
obj* x_20; 
lean::dec(x_0);
lean::dec(x_1);
x_20 = _l_s9___private_2038417741__s20_mk__consumed__result_s6___rarg(x_2, x_3);
return x_20;
}
else
{
obj* x_21; obj* x_22; obj* x_25; unsigned char x_26; obj* x_27; 
x_21 = lean::mk_nat_obj(1u);
x_22 = lean::nat_sub(x_1, x_21);
lean::dec(x_21);
lean::dec(x_1);
x_25 = lean::string_iterator_next(x_3);
x_26 = 1;
x_27 = _l_s9___private_1695453085__s20_take__while__aux_x27_s6___main_s6___rarg(x_0, x_22, x_26, x_25);
return x_27;
}
}
}
else
{
obj* x_31; 
lean::dec(x_5);
lean::dec(x_0);
lean::dec(x_1);
x_31 = _l_s9___private_2038417741__s20_mk__consumed__result_s6___rarg(x_2, x_3);
return x_31;
}
}
}
obj* _l_s9___private_1695453085__s20_take__while__aux_x27_s6___main(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9___private_1695453085__s20_take__while__aux_x27_s6___main_s6___rarg_s7___boxed), 4, 0);
return x_2;
}
}
obj* _l_s9___private_1695453085__s20_take__while__aux_x27_s6___main_s6___rarg_s7___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{
unsigned char x_4; obj* x_5; 
x_4 = lean::unbox(x_2);
x_5 = _l_s9___private_1695453085__s20_take__while__aux_x27_s6___main_s6___rarg(x_0, x_1, x_4, x_3);
return x_5;
}
}
obj* _l_s9___private_1695453085__s20_take__while__aux_x27_s6___rarg(obj* x_0, obj* x_1, unsigned char x_2, obj* x_3) {
{
obj* x_4; 
x_4 = _l_s9___private_1695453085__s20_take__while__aux_x27_s6___main_s6___rarg(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* _l_s9___private_1695453085__s20_take__while__aux_x27(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9___private_1695453085__s20_take__while__aux_x27_s6___rarg_s7___boxed), 4, 0);
return x_2;
}
}
obj* _l_s9___private_1695453085__s20_take__while__aux_x27_s6___rarg_s7___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{
unsigned char x_4; obj* x_5; 
x_4 = lean::unbox(x_2);
x_5 = _l_s9___private_1695453085__s20_take__while__aux_x27_s6___rarg(x_0, x_1, x_4, x_3);
return x_5;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s15_take__while_x27_s6___rarg(obj* x_0, obj* x_1) {
{
obj* x_2; obj* x_5; obj* x_6; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s15_take__while_x27_s6___rarg_s11___lambda__1), 2, 1);
lean::closure_set(x_5, 0, x_1);
x_6 = lean::apply_2(x_2, lean::box(0), x_5);
return x_6;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s15_take__while_x27_s6___rarg_s11___lambda__1(obj* x_0, obj* x_1) {
{
obj* x_2; unsigned char x_3; obj* x_4; 
x_2 = lean::string_iterator_remaining(x_1);
x_3 = 0;
x_4 = _l_s9___private_1695453085__s20_take__while__aux_x27_s6___main_s6___rarg(x_0, x_2, x_3, x_1);
return x_4;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s15_take__while_x27(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s15_take__while_x27_s6___rarg), 2, 0);
return x_6;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s16_take__while1_x27_s6___rarg(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_3; obj* x_5; obj* x_8; obj* x_10; obj* x_12; obj* x_15; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_3, 4);
lean::inc(x_5);
lean::dec(x_3);
x_8 = lean::cnstr_get(x_0, 1);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_1, 0);
lean::inc(x_10);
x_12 = _l_s4_lean_s6_parser_s13_monad__parsec_s10_left__over_s6___rarg_s11___closed__1;
lean::inc(x_12);
lean::inc(x_10);
x_15 = lean::apply_2(x_10, lean::box(0), x_12);
lean::inc(x_2);
lean::inc(x_1);
x_18 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s16_take__while1_x27_s6___rarg_s11___lambda__1), 5, 4);
lean::closure_set(x_18, 0, x_0);
lean::closure_set(x_18, 1, x_1);
lean::closure_set(x_18, 2, x_2);
lean::closure_set(x_18, 3, x_10);
x_19 = lean::apply_4(x_8, lean::box(0), lean::box(0), x_15, x_18);
x_20 = _l_s4_lean_s6_parser_s13_monad__parsec_s15_take__while_x27_s6___rarg(x_1, x_2);
x_21 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_19, x_20);
return x_21;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s16_take__while1_x27_s6___rarg_s11___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{
unsigned char x_6; 
lean::dec(x_0);
x_6 = lean::string_iterator_has_next(x_4);
if (x_6 == 0)
{
obj* x_10; obj* x_11; obj* x_12; obj* x_16; 
lean::dec(x_4);
lean::dec(x_2);
lean::dec(x_3);
x_10 = lean::box(0);
x_11 = _l_s4_lean_s6_parser_s13_monad__parsec_s10_eoi__error_s6___rarg_s11___closed__1;
x_12 = _l_s5_mjoin_s6___rarg_s11___closed__1;
lean::inc(x_10);
lean::inc(x_12);
lean::inc(x_11);
x_16 = _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s16_take__while1_x27_s9___spec__1_s6___rarg(x_1, lean::box(0), x_11, x_12, x_10, x_10);
return x_16;
}
else
{
unsigned x_17; obj* x_18; obj* x_20; unsigned char x_21; 
x_17 = lean::string_iterator_curr(x_4);
x_18 = lean::box_uint32(x_17);
lean::inc(x_18);
x_20 = lean::apply_1(x_2, x_18);
x_21 = lean::unbox(x_20);
lean::dec(x_20);
if (x_21 == 0)
{
obj* x_26; obj* x_27; obj* x_29; obj* x_31; obj* x_32; obj* x_33; obj* x_36; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_18);
x_26 = _l_s4_char_s11_quote__core(x_17);
x_27 = _l_s4_char_s9_has__repr_s11___closed__1;
lean::inc(x_27);
x_29 = lean::string_append(x_27, x_26);
lean::dec(x_26);
x_31 = lean::string_append(x_29, x_27);
x_32 = lean::box(0);
x_33 = _l_s5_mjoin_s6___rarg_s11___closed__1;
lean::inc(x_32);
lean::inc(x_33);
x_36 = _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s16_take__while1_x27_s9___spec__2_s6___rarg(x_1, lean::box(0), x_31, x_33, x_32, x_32);
return x_36;
}
else
{
obj* x_38; obj* x_39; 
lean::dec(x_1);
x_38 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s7_satisfy_s6___rarg_s11___lambda__1_s7___boxed), 3, 2);
lean::closure_set(x_38, 0, x_4);
lean::closure_set(x_38, 1, x_18);
x_39 = lean::apply_2(x_3, lean::box(0), x_38);
return x_39;
}
}
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s16_take__while1_x27(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s16_take__while1_x27_s6___rarg), 3, 0);
return x_4;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s16_take__while1_x27_s9___spec__1_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
{
obj* x_7; obj* x_10; obj* x_11; 
lean::dec(x_1);
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s6___rarg_s11___lambda__1), 5, 4);
lean::closure_set(x_10, 0, x_4);
lean::closure_set(x_10, 1, x_2);
lean::closure_set(x_10, 2, x_3);
lean::closure_set(x_10, 3, x_5);
x_11 = lean::apply_2(x_7, lean::box(0), x_10);
return x_11;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s16_take__while1_x27_s9___spec__1(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s16_take__while1_x27_s9___spec__1_s6___rarg), 6, 0);
return x_6;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s16_take__while1_x27_s9___spec__2_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
{
obj* x_7; obj* x_10; obj* x_11; 
lean::dec(x_1);
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s6___rarg_s11___lambda__1), 5, 4);
lean::closure_set(x_10, 0, x_4);
lean::closure_set(x_10, 1, x_2);
lean::closure_set(x_10, 2, x_3);
lean::closure_set(x_10, 3, x_5);
x_11 = lean::apply_2(x_7, lean::box(0), x_10);
return x_11;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s16_take__while1_x27_s9___spec__2(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s16_take__while1_x27_s9___spec__2_s6___rarg), 6, 0);
return x_6;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s10_whitespace_s6___rarg(obj* x_0, obj* x_1) {
{
obj* x_3; 
lean::dec(x_0);
x_3 = _l_s4_lean_s6_parser_s13_monad__parsec_s15_take__while_x27_s4___at_s4_lean_s6_parser_s13_monad__parsec_s10_whitespace_s9___spec__1_s6___rarg(x_1);
return x_3;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s10_whitespace(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s10_whitespace_s6___rarg), 2, 0);
return x_4;
}
}
obj* _l_s9___private_1695453085__s20_take__while__aux_x27_s6___main_s4___at_s4_lean_s6_parser_s13_monad__parsec_s10_whitespace_s9___spec__2_s6___rarg(obj* x_0, unsigned char x_1, obj* x_2) {
{
obj* x_3; obj* x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
lean::dec(x_3);
if (lean::obj_tag(x_4) == 0)
{
unsigned char x_7; 
lean::dec(x_4);
x_7 = lean::string_iterator_has_next(x_2);
if (x_7 == 0)
{
obj* x_9; 
lean::dec(x_0);
x_9 = _l_s9___private_2038417741__s20_mk__consumed__result_s6___rarg(x_1, x_2);
return x_9;
}
else
{
unsigned x_10; unsigned char x_11; 
x_10 = lean::string_iterator_curr(x_2);
x_11 = _l_s4_char_s14_is__whitespace(x_10);
if (x_11 == 0)
{
obj* x_13; 
lean::dec(x_0);
x_13 = _l_s9___private_2038417741__s20_mk__consumed__result_s6___rarg(x_1, x_2);
return x_13;
}
else
{
obj* x_14; obj* x_15; obj* x_18; unsigned char x_19; obj* x_20; 
x_14 = lean::mk_nat_obj(1u);
x_15 = lean::nat_sub(x_0, x_14);
lean::dec(x_14);
lean::dec(x_0);
x_18 = lean::string_iterator_next(x_2);
x_19 = 1;
x_20 = _l_s9___private_1695453085__s20_take__while__aux_x27_s6___main_s4___at_s4_lean_s6_parser_s13_monad__parsec_s10_whitespace_s9___spec__2_s6___rarg(x_15, x_19, x_18);
return x_20;
}
}
}
else
{
obj* x_23; 
lean::dec(x_4);
lean::dec(x_0);
x_23 = _l_s9___private_2038417741__s20_mk__consumed__result_s6___rarg(x_1, x_2);
return x_23;
}
}
}
obj* _l_s9___private_1695453085__s20_take__while__aux_x27_s6___main_s4___at_s4_lean_s6_parser_s13_monad__parsec_s10_whitespace_s9___spec__2(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9___private_1695453085__s20_take__while__aux_x27_s6___main_s4___at_s4_lean_s6_parser_s13_monad__parsec_s10_whitespace_s9___spec__2_s6___rarg_s7___boxed), 3, 0);
return x_2;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s15_take__while_x27_s4___at_s4_lean_s6_parser_s13_monad__parsec_s10_whitespace_s9___spec__1_s6___rarg(obj* x_0) {
{
obj* x_1; obj* x_4; obj* x_6; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
x_4 = _l_s4_lean_s6_parser_s13_monad__parsec_s15_take__while_x27_s4___at_s4_lean_s6_parser_s13_monad__parsec_s10_whitespace_s9___spec__1_s6___rarg_s11___closed__1;
lean::inc(x_4);
x_6 = lean::apply_2(x_1, lean::box(0), x_4);
return x_6;
}
}
obj* _init__l_s4_lean_s6_parser_s13_monad__parsec_s15_take__while_x27_s4___at_s4_lean_s6_parser_s13_monad__parsec_s10_whitespace_s9___spec__1_s6___rarg_s11___closed__1() {
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s15_take__while_x27_s4___at_s4_lean_s6_parser_s13_monad__parsec_s10_whitespace_s9___spec__1_s6___rarg_s11___lambda__1), 1, 0);
return x_0;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s15_take__while_x27_s4___at_s4_lean_s6_parser_s13_monad__parsec_s10_whitespace_s9___spec__1_s6___rarg_s11___lambda__1(obj* x_0) {
{
obj* x_1; unsigned char x_2; obj* x_3; 
x_1 = lean::string_iterator_remaining(x_0);
x_2 = 0;
x_3 = _l_s9___private_1695453085__s20_take__while__aux_x27_s6___main_s4___at_s4_lean_s6_parser_s13_monad__parsec_s10_whitespace_s9___spec__2_s6___rarg(x_1, x_2, x_0);
return x_3;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s15_take__while_x27_s4___at_s4_lean_s6_parser_s13_monad__parsec_s10_whitespace_s9___spec__1(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s15_take__while_x27_s4___at_s4_lean_s6_parser_s13_monad__parsec_s10_whitespace_s9___spec__1_s6___rarg), 1, 0);
return x_6;
}
}
obj* _l_s9___private_1695453085__s20_take__while__aux_x27_s6___main_s4___at_s4_lean_s6_parser_s13_monad__parsec_s10_whitespace_s9___spec__2_s6___rarg_s7___boxed(obj* x_0, obj* x_1, obj* x_2) {
{
unsigned char x_3; obj* x_4; 
x_3 = lean::unbox(x_1);
x_4 = _l_s9___private_1695453085__s20_take__while__aux_x27_s6___main_s4___at_s4_lean_s6_parser_s13_monad__parsec_s10_whitespace_s9___spec__2_s6___rarg(x_0, x_3, x_2);
return x_4;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s6_lexeme_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{
obj* x_5; obj* x_7; obj* x_10; obj* x_11; obj* x_12; 
lean::dec(x_2);
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_5, 3);
lean::inc(x_7);
lean::dec(x_5);
x_10 = _l_s4_lean_s6_parser_s13_monad__parsec_s10_whitespace(lean::box(0), lean::box(0));
x_11 = lean::apply_2(x_10, x_0, x_1);
x_12 = lean::apply_4(x_7, lean::box(0), lean::box(0), x_3, x_11);
return x_12;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s6_lexeme(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s6_lexeme_s6___rarg), 4, 0);
return x_4;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s3_num_s6___rarg(obj* x_0, obj* x_1) {
{
obj* x_2; obj* x_4; obj* x_7; obj* x_10; obj* x_11; obj* x_13; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
lean::dec(x_2);
x_7 = lean::cnstr_get(x_4, 0);
lean::inc(x_7);
lean::dec(x_4);
x_10 = _l_s4_lean_s6_parser_s13_monad__parsec_s12_take__while1_s4___at_s4_lean_s6_parser_s13_monad__parsec_s3_num_s9___spec__1_s6___rarg(x_0, x_1);
x_11 = _l_s4_lean_s6_parser_s13_monad__parsec_s3_num_s6___rarg_s11___closed__1;
lean::inc(x_11);
x_13 = lean::apply_4(x_7, lean::box(0), lean::box(0), x_11, x_10);
return x_13;
}
}
obj* _init__l_s4_lean_s6_parser_s13_monad__parsec_s3_num_s6___rarg_s11___closed__1() {
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s6_string_s7_to__nat), 1, 0);
return x_0;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s3_num(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s3_num_s6___rarg), 2, 0);
return x_4;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s3_num_s9___spec__2_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
{
obj* x_7; obj* x_10; obj* x_11; 
lean::dec(x_1);
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s6___rarg_s11___lambda__1), 5, 4);
lean::closure_set(x_10, 0, x_4);
lean::closure_set(x_10, 1, x_2);
lean::closure_set(x_10, 2, x_3);
lean::closure_set(x_10, 3, x_5);
x_11 = lean::apply_2(x_7, lean::box(0), x_10);
return x_11;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s3_num_s9___spec__2(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s3_num_s9___spec__2_s6___rarg), 6, 0);
return x_6;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s3_num_s9___spec__3_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
{
obj* x_7; obj* x_10; obj* x_11; 
lean::dec(x_1);
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s6___rarg_s11___lambda__1), 5, 4);
lean::closure_set(x_10, 0, x_4);
lean::closure_set(x_10, 1, x_2);
lean::closure_set(x_10, 2, x_3);
lean::closure_set(x_10, 3, x_5);
x_11 = lean::apply_2(x_7, lean::box(0), x_10);
return x_11;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s3_num_s9___spec__3(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s3_num_s9___spec__3_s6___rarg), 6, 0);
return x_6;
}
}
obj* _l_s9___private_31565857__s16_take__while__aux_s6___main_s4___at_s4_lean_s6_parser_s13_monad__parsec_s3_num_s9___spec__5_s6___rarg(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_3; obj* x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
lean::dec(x_3);
if (lean::obj_tag(x_4) == 0)
{
unsigned char x_7; 
lean::dec(x_4);
x_7 = lean::string_iterator_has_next(x_2);
if (x_7 == 0)
{
obj* x_9; 
lean::dec(x_0);
x_9 = _l_s9___private_2142412293__s18_mk__string__result_s6___rarg(x_1, x_2);
return x_9;
}
else
{
unsigned x_10; unsigned char x_11; 
x_10 = lean::string_iterator_curr(x_2);
x_11 = _l_s4_char_s9_is__digit(x_10);
if (x_11 == 0)
{
obj* x_13; 
lean::dec(x_0);
x_13 = _l_s9___private_2142412293__s18_mk__string__result_s6___rarg(x_1, x_2);
return x_13;
}
else
{
obj* x_14; obj* x_15; obj* x_18; obj* x_19; obj* x_20; 
x_14 = lean::mk_nat_obj(1u);
x_15 = lean::nat_sub(x_0, x_14);
lean::dec(x_14);
lean::dec(x_0);
x_18 = lean::string_push(x_1, x_10);
x_19 = lean::string_iterator_next(x_2);
x_20 = _l_s9___private_31565857__s16_take__while__aux_s6___main_s4___at_s4_lean_s6_parser_s13_monad__parsec_s3_num_s9___spec__5_s6___rarg(x_15, x_18, x_19);
return x_20;
}
}
}
else
{
obj* x_23; 
lean::dec(x_4);
lean::dec(x_0);
x_23 = _l_s9___private_2142412293__s18_mk__string__result_s6___rarg(x_1, x_2);
return x_23;
}
}
}
obj* _l_s9___private_31565857__s16_take__while__aux_s6___main_s4___at_s4_lean_s6_parser_s13_monad__parsec_s3_num_s9___spec__5(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9___private_31565857__s16_take__while__aux_s6___main_s4___at_s4_lean_s6_parser_s13_monad__parsec_s3_num_s9___spec__5_s6___rarg), 3, 0);
return x_2;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s17_take__while__cont_s4___at_s4_lean_s6_parser_s13_monad__parsec_s3_num_s9___spec__4_s6___rarg(obj* x_0, unsigned x_1) {
{
obj* x_2; obj* x_4; obj* x_5; obj* x_8; obj* x_9; 
x_2 = _l_s6_string_s4_join_s11___closed__1;
lean::inc(x_2);
x_4 = lean::string_push(x_2, x_1);
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
lean::dec(x_0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s17_take__while__cont_s4___at_s4_lean_s6_parser_s13_monad__parsec_s3_num_s9___spec__4_s6___rarg_s11___lambda__1), 2, 1);
lean::closure_set(x_8, 0, x_4);
x_9 = lean::apply_2(x_5, lean::box(0), x_8);
return x_9;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s17_take__while__cont_s4___at_s4_lean_s6_parser_s13_monad__parsec_s3_num_s9___spec__4_s6___rarg_s11___lambda__1(obj* x_0, obj* x_1) {
{
obj* x_2; obj* x_3; 
x_2 = lean::string_iterator_remaining(x_1);
x_3 = _l_s9___private_31565857__s16_take__while__aux_s6___main_s4___at_s4_lean_s6_parser_s13_monad__parsec_s3_num_s9___spec__5_s6___rarg(x_2, x_0, x_1);
return x_3;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s17_take__while__cont_s4___at_s4_lean_s6_parser_s13_monad__parsec_s3_num_s9___spec__4(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s17_take__while__cont_s4___at_s4_lean_s6_parser_s13_monad__parsec_s3_num_s9___spec__4_s6___rarg_s7___boxed), 2, 0);
return x_6;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s12_take__while1_s4___at_s4_lean_s6_parser_s13_monad__parsec_s3_num_s9___spec__1_s6___rarg(obj* x_0, obj* x_1) {
{
obj* x_2; obj* x_4; obj* x_6; obj* x_9; obj* x_11; obj* x_13; obj* x_14; obj* x_15; 
x_2 = lean::cnstr_get(x_0, 1);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
x_6 = _l_s4_lean_s6_parser_s13_monad__parsec_s10_left__over_s6___rarg_s11___closed__1;
lean::inc(x_6);
lean::inc(x_4);
x_9 = lean::apply_2(x_4, lean::box(0), x_6);
lean::inc(x_1);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s12_take__while1_s4___at_s4_lean_s6_parser_s13_monad__parsec_s3_num_s9___spec__1_s6___rarg_s11___lambda__1), 4, 3);
lean::closure_set(x_11, 0, x_0);
lean::closure_set(x_11, 1, x_1);
lean::closure_set(x_11, 2, x_4);
lean::inc(x_2);
x_13 = lean::apply_4(x_2, lean::box(0), lean::box(0), x_9, x_11);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s17_take__while__cont_s4___at_s4_lean_s6_parser_s13_monad__parsec_s3_num_s9___spec__4_s6___rarg_s7___boxed), 2, 1);
lean::closure_set(x_14, 0, x_1);
x_15 = lean::apply_4(x_2, lean::box(0), lean::box(0), x_13, x_14);
return x_15;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s12_take__while1_s4___at_s4_lean_s6_parser_s13_monad__parsec_s3_num_s9___spec__1_s6___rarg_s11___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{
unsigned char x_5; 
lean::dec(x_0);
x_5 = lean::string_iterator_has_next(x_3);
if (x_5 == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_14; 
lean::dec(x_2);
lean::dec(x_3);
x_8 = lean::box(0);
x_9 = _l_s4_lean_s6_parser_s13_monad__parsec_s10_eoi__error_s6___rarg_s11___closed__1;
x_10 = _l_s5_mjoin_s6___rarg_s11___closed__1;
lean::inc(x_8);
lean::inc(x_10);
lean::inc(x_9);
x_14 = _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s3_num_s9___spec__2_s6___rarg(x_1, lean::box(0), x_9, x_10, x_8, x_8);
return x_14;
}
else
{
unsigned x_15; unsigned char x_16; 
x_15 = lean::string_iterator_curr(x_3);
x_16 = _l_s4_char_s9_is__digit(x_15);
if (x_16 == 0)
{
obj* x_19; obj* x_20; obj* x_22; obj* x_24; obj* x_25; obj* x_26; obj* x_29; 
lean::dec(x_2);
lean::dec(x_3);
x_19 = _l_s4_char_s11_quote__core(x_15);
x_20 = _l_s4_char_s9_has__repr_s11___closed__1;
lean::inc(x_20);
x_22 = lean::string_append(x_20, x_19);
lean::dec(x_19);
x_24 = lean::string_append(x_22, x_20);
x_25 = lean::box(0);
x_26 = _l_s5_mjoin_s6___rarg_s11___closed__1;
lean::inc(x_25);
lean::inc(x_26);
x_29 = _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s3_num_s9___spec__3_s6___rarg(x_1, lean::box(0), x_24, x_26, x_25, x_25);
return x_29;
}
else
{
obj* x_31; obj* x_32; obj* x_33; 
lean::dec(x_1);
x_31 = lean::box_uint32(x_15);
x_32 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s7_satisfy_s6___rarg_s11___lambda__1_s7___boxed), 3, 2);
lean::closure_set(x_32, 0, x_3);
lean::closure_set(x_32, 1, x_31);
x_33 = lean::apply_2(x_2, lean::box(0), x_32);
return x_33;
}
}
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s12_take__while1_s4___at_s4_lean_s6_parser_s13_monad__parsec_s3_num_s9___spec__1(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s12_take__while1_s4___at_s4_lean_s6_parser_s13_monad__parsec_s3_num_s9___spec__1_s6___rarg), 2, 0);
return x_4;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s17_take__while__cont_s4___at_s4_lean_s6_parser_s13_monad__parsec_s3_num_s9___spec__4_s6___rarg_s7___boxed(obj* x_0, obj* x_1) {
{
unsigned x_2; obj* x_3; 
x_2 = lean::unbox_uint32(x_1);
x_3 = _l_s4_lean_s6_parser_s13_monad__parsec_s17_take__while__cont_s4___at_s4_lean_s6_parser_s13_monad__parsec_s3_num_s9___spec__4_s6___rarg(x_0, x_2);
return x_3;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s6_ensure_s6___rarg(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_3; obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_11; 
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
x_7 = _l_s4_lean_s6_parser_s13_monad__parsec_s10_left__over_s6___rarg_s11___closed__1;
lean::inc(x_7);
x_9 = lean::apply_2(x_5, lean::box(0), x_7);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s6_ensure_s6___rarg_s11___lambda__1), 4, 3);
lean::closure_set(x_10, 0, x_2);
lean::closure_set(x_10, 1, x_0);
lean::closure_set(x_10, 2, x_1);
x_11 = lean::apply_4(x_3, lean::box(0), lean::box(0), x_9, x_10);
return x_11;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s6_ensure_s6___rarg_s11___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{
obj* x_4; obj* x_6; 
x_4 = lean::string_iterator_remaining(x_3);
lean::dec(x_3);
x_6 = lean::nat_dec_le(x_0, x_4);
lean::dec(x_4);
if (lean::obj_tag(x_6) == 0)
{
obj* x_10; obj* x_11; obj* x_13; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_22; 
lean::dec(x_6);
lean::dec(x_1);
x_10 = _l_s3_nat_s4_repr(x_0);
x_11 = _l_s4_lean_s6_parser_s13_monad__parsec_s6_ensure_s6___rarg_s11___lambda__1_s11___closed__1;
lean::inc(x_11);
x_13 = lean::string_append(x_11, x_10);
lean::dec(x_10);
x_15 = _l_s4_lean_s6_parser_s13_monad__parsec_s6_ensure_s6___rarg_s11___lambda__1_s11___closed__2;
x_16 = lean::string_append(x_13, x_15);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(_l_s5_dlist_s9_singleton_s6___rarg), 2, 1);
lean::closure_set(x_17, 0, x_16);
x_18 = lean::box(0);
x_19 = _l_s4_lean_s6_parser_s13_monad__parsec_s10_eoi__error_s6___rarg_s11___closed__1;
lean::inc(x_18);
lean::inc(x_19);
x_22 = _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s6_ensure_s9___spec__1_s6___rarg(x_2, lean::box(0), x_19, x_17, x_18, x_18);
return x_22;
}
else
{
obj* x_26; obj* x_29; unsigned char x_32; obj* x_33; obj* x_34; 
lean::dec(x_6);
lean::dec(x_0);
lean::dec(x_2);
x_26 = lean::cnstr_get(x_1, 0);
lean::inc(x_26);
lean::dec(x_1);
x_29 = lean::cnstr_get(x_26, 1);
lean::inc(x_29);
lean::dec(x_26);
x_32 = 0;
x_33 = lean::box(x_32);
x_34 = lean::apply_2(x_29, lean::box(0), x_33);
return x_34;
}
}
}
obj* _init__l_s4_lean_s6_parser_s13_monad__parsec_s6_ensure_s6___rarg_s11___lambda__1_s11___closed__1() {
{
obj* x_0; 
x_0 = lean::mk_string("at least ");
return x_0;
}
}
obj* _init__l_s4_lean_s6_parser_s13_monad__parsec_s6_ensure_s6___rarg_s11___lambda__1_s11___closed__2() {
{
obj* x_0; 
x_0 = lean::mk_string(" characters");
return x_0;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s6_ensure(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s6_ensure_s6___rarg), 3, 0);
return x_4;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s6_ensure_s9___spec__1_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
{
obj* x_7; obj* x_10; obj* x_11; 
lean::dec(x_1);
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s6___rarg_s11___lambda__1), 5, 4);
lean::closure_set(x_10, 0, x_4);
lean::closure_set(x_10, 1, x_2);
lean::closure_set(x_10, 2, x_3);
lean::closure_set(x_10, 3, x_5);
x_11 = lean::apply_2(x_7, lean::box(0), x_10);
return x_11;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s6_ensure_s9___spec__1(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s6_ensure_s9___spec__1_s6___rarg), 6, 0);
return x_6;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s3_pos_s6___rarg(obj* x_0, obj* x_1) {
{
obj* x_2; obj* x_5; obj* x_8; obj* x_11; obj* x_14; obj* x_16; obj* x_17; obj* x_19; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
x_5 = lean::cnstr_get(x_2, 0);
lean::inc(x_5);
lean::dec(x_2);
x_8 = lean::cnstr_get(x_5, 0);
lean::inc(x_8);
lean::dec(x_5);
x_11 = lean::cnstr_get(x_1, 0);
lean::inc(x_11);
lean::dec(x_1);
x_14 = _l_s4_lean_s6_parser_s13_monad__parsec_s10_left__over_s6___rarg_s11___closed__1;
lean::inc(x_14);
x_16 = lean::apply_2(x_11, lean::box(0), x_14);
x_17 = _l_s4_lean_s6_parser_s13_monad__parsec_s3_pos_s6___rarg_s11___closed__1;
lean::inc(x_17);
x_19 = lean::apply_4(x_8, lean::box(0), lean::box(0), x_17, x_16);
return x_19;
}
}
obj* _init__l_s4_lean_s6_parser_s13_monad__parsec_s3_pos_s6___rarg_s11___closed__1() {
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(lean::string_iterator_offset), 1, 0);
return x_0;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s3_pos(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s3_pos_s6___rarg), 2, 0);
return x_4;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s17_not__followed__by_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
{
obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_16; 
lean::dec(x_2);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_1, 0);
lean::inc(x_9);
x_11 = _l_s4_lean_s6_parser_s13_monad__parsec_s10_left__over_s6___rarg_s11___closed__1;
lean::inc(x_11);
x_13 = lean::apply_2(x_9, lean::box(0), x_11);
lean::inc(x_7);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s17_not__followed__by_s6___rarg_s11___lambda__3), 7, 6);
lean::closure_set(x_15, 0, x_3);
lean::closure_set(x_15, 1, x_0);
lean::closure_set(x_15, 2, x_4);
lean::closure_set(x_15, 3, x_1);
lean::closure_set(x_15, 4, x_5);
lean::closure_set(x_15, 5, x_7);
x_16 = lean::apply_4(x_7, lean::box(0), lean::box(0), x_13, x_15);
return x_16;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s17_not__followed__by_s6___rarg_s11___lambda__1(obj* x_0, obj* x_1) {
{
unsigned char x_3; obj* x_4; obj* x_5; 
lean::dec(x_1);
x_3 = 1;
x_4 = lean::box(x_3);
x_5 = lean::apply_2(x_0, lean::box(0), x_4);
return x_5;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s17_not__followed__by_s6___rarg_s11___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, unsigned char x_5) {
{

lean::dec(x_1);
if (x_5 == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_12; 
lean::dec(x_4);
x_8 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_8, 0, x_0);
x_9 = lean::box(0);
x_10 = _l_s5_mjoin_s6___rarg_s11___closed__1;
lean::inc(x_10);
x_12 = _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s17_not__followed__by_s9___spec__1_s6___rarg(x_2, lean::box(0), x_3, x_10, x_8, x_9);
return x_12;
}
else
{
unsigned char x_16; obj* x_17; obj* x_18; 
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_3);
x_16 = 0;
x_17 = lean::box(x_16);
x_18 = lean::apply_2(x_4, lean::box(0), x_17);
return x_18;
}
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s17_not__followed__by_s6___rarg_s11___lambda__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
{
obj* x_7; obj* x_10; obj* x_12; obj* x_14; unsigned char x_17; obj* x_18; obj* x_20; obj* x_21; obj* x_23; obj* x_24; obj* x_25; obj* x_27; obj* x_29; obj* x_30; obj* x_31; 
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::cnstr_get(x_1, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_10, 4);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_10, 1);
lean::inc(x_14);
lean::dec(x_10);
x_17 = 0;
x_18 = lean::box(x_17);
lean::inc(x_14);
x_20 = lean::apply_2(x_14, lean::box(0), x_18);
x_21 = lean::apply_4(x_12, lean::box(0), lean::box(0), x_2, x_20);
lean::inc(x_14);
x_23 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s17_not__followed__by_s6___rarg_s11___lambda__1), 2, 1);
lean::closure_set(x_23, 0, x_14);
x_24 = lean::apply_3(x_7, lean::box(0), x_21, x_23);
x_25 = lean::cnstr_get(x_3, 1);
lean::inc(x_25);
x_27 = _l_s4_lean_s6_parser_s13_monad__parsec_s9_lookahead_s6___rarg_s11___closed__1;
lean::inc(x_27);
x_29 = lean::apply_3(x_25, lean::box(0), x_27, x_24);
x_30 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s17_not__followed__by_s6___rarg_s11___lambda__2_s7___boxed), 6, 5);
lean::closure_set(x_30, 0, x_6);
lean::closure_set(x_30, 1, x_1);
lean::closure_set(x_30, 2, x_3);
lean::closure_set(x_30, 3, x_4);
lean::closure_set(x_30, 4, x_14);
x_31 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_29, x_30);
return x_31;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s17_not__followed__by(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s17_not__followed__by_s6___rarg), 6, 0);
return x_4;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s17_not__followed__by_s9___spec__1_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
{
obj* x_7; obj* x_10; obj* x_11; 
lean::dec(x_1);
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s6___rarg_s11___lambda__1), 5, 4);
lean::closure_set(x_10, 0, x_4);
lean::closure_set(x_10, 1, x_2);
lean::closure_set(x_10, 2, x_3);
lean::closure_set(x_10, 3, x_5);
x_11 = lean::apply_2(x_7, lean::box(0), x_10);
return x_11;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s17_not__followed__by_s9___spec__1(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s17_not__followed__by_s9___spec__1_s6___rarg), 6, 0);
return x_6;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s17_not__followed__by_s6___rarg_s11___lambda__2_s7___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
{
unsigned char x_6; obj* x_7; 
x_6 = lean::unbox(x_5);
x_7 = _l_s4_lean_s6_parser_s13_monad__parsec_s17_not__followed__by_s6___rarg_s11___lambda__2(x_0, x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s3_eoi_s6___rarg(obj* x_0, obj* x_1) {
{
obj* x_2; obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_10; 
x_2 = lean::cnstr_get(x_0, 1);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
x_6 = _l_s4_lean_s6_parser_s13_monad__parsec_s10_left__over_s6___rarg_s11___closed__1;
lean::inc(x_6);
x_8 = lean::apply_2(x_4, lean::box(0), x_6);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s3_eoi_s6___rarg_s11___lambda__1), 3, 2);
lean::closure_set(x_9, 0, x_0);
lean::closure_set(x_9, 1, x_1);
x_10 = lean::apply_4(x_2, lean::box(0), lean::box(0), x_8, x_9);
return x_10;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s3_eoi_s6___rarg_s11___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = lean::string_iterator_remaining(x_2);
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::nat_dec_eq(x_3, x_4);
lean::dec(x_4);
lean::dec(x_3);
if (lean::obj_tag(x_5) == 0)
{
unsigned x_10; obj* x_12; obj* x_13; obj* x_15; obj* x_17; obj* x_18; obj* x_19; obj* x_22; 
lean::dec(x_5);
lean::dec(x_0);
x_10 = lean::string_iterator_curr(x_2);
lean::dec(x_2);
x_12 = _l_s4_char_s11_quote__core(x_10);
x_13 = _l_s4_char_s9_has__repr_s11___closed__1;
lean::inc(x_13);
x_15 = lean::string_append(x_13, x_12);
lean::dec(x_12);
x_17 = lean::string_append(x_15, x_13);
x_18 = lean::box(0);
x_19 = _l_s4_lean_s6_parser_s13_monad__parsec_s3_eoi_s6___rarg_s11___lambda__1_s11___closed__1;
lean::inc(x_18);
lean::inc(x_19);
x_22 = _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s3_eoi_s9___spec__1_s6___rarg(x_1, lean::box(0), x_17, x_19, x_18, x_18);
return x_22;
}
else
{
obj* x_26; obj* x_29; unsigned char x_32; obj* x_33; obj* x_34; 
lean::dec(x_5);
lean::dec(x_1);
lean::dec(x_2);
x_26 = lean::cnstr_get(x_0, 0);
lean::inc(x_26);
lean::dec(x_0);
x_29 = lean::cnstr_get(x_26, 1);
lean::inc(x_29);
lean::dec(x_26);
x_32 = 0;
x_33 = lean::box(x_32);
x_34 = lean::apply_2(x_29, lean::box(0), x_33);
return x_34;
}
}
}
obj* _init__l_s4_lean_s6_parser_s13_monad__parsec_s3_eoi_s6___rarg_s11___lambda__1_s11___closed__1() {
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("end of input");
x_1 = lean::alloc_closure(reinterpret_cast<void*>(_l_s5_dlist_s9_singleton_s6___rarg), 2, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s3_eoi(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s3_eoi_s6___rarg), 2, 0);
return x_4;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s3_eoi_s9___spec__1_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
{
obj* x_7; obj* x_10; obj* x_11; 
lean::dec(x_1);
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s6___rarg_s11___lambda__1), 5, 4);
lean::closure_set(x_10, 0, x_4);
lean::closure_set(x_10, 1, x_2);
lean::closure_set(x_10, 2, x_3);
lean::closure_set(x_10, 3, x_5);
x_11 = lean::apply_2(x_7, lean::box(0), x_10);
return x_11;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s3_eoi_s9___spec__1(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s3_eoi_s9___spec__1_s6___rarg), 6, 0);
return x_6;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s10_many1__aux_s6___main_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{
obj* x_6; obj* x_7; 
lean::dec(x_1);
x_6 = lean::mk_nat_obj(0u);
x_7 = lean::nat_dec_eq(x_4, x_6);
lean::dec(x_6);
if (lean::obj_tag(x_7) == 0)
{
obj* x_10; obj* x_11; obj* x_14; obj* x_18; obj* x_19; 
lean::dec(x_7);
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_sub(x_4, x_10);
lean::dec(x_10);
lean::dec(x_4);
x_14 = lean::cnstr_get(x_0, 1);
lean::inc(x_14);
lean::inc(x_14);
lean::inc(x_3);
x_18 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s10_many1__aux_s6___main_s6___rarg_s11___lambda__2), 6, 5);
lean::closure_set(x_18, 0, x_2);
lean::closure_set(x_18, 1, x_0);
lean::closure_set(x_18, 2, x_3);
lean::closure_set(x_18, 3, x_11);
lean::closure_set(x_18, 4, x_14);
x_19 = lean::apply_4(x_14, lean::box(0), lean::box(0), x_3, x_18);
return x_19;
}
else
{
obj* x_22; obj* x_25; obj* x_26; 
lean::dec(x_4);
lean::dec(x_7);
x_22 = lean::cnstr_get(x_0, 1);
lean::inc(x_22);
lean::dec(x_0);
x_25 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s10_many1__aux_s6___main_s6___rarg_s11___lambda__3), 2, 1);
lean::closure_set(x_25, 0, x_2);
x_26 = lean::apply_4(x_22, lean::box(0), lean::box(0), x_3, x_25);
return x_26;
}
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s10_many1__aux_s6___main_s6___rarg_s11___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_3; obj* x_4; 
x_3 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_2);
x_4 = lean::apply_2(x_1, lean::box(0), x_3);
return x_4;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s10_many1__aux_s6___main_s6___rarg_s11___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
{
obj* x_6; obj* x_9; obj* x_10; obj* x_13; obj* x_16; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
lean::inc(x_0);
x_9 = _l_s4_lean_s6_parser_s13_monad__parsec_s10_many1__aux_s6___main_s6___rarg(x_1, lean::box(0), x_0, x_2, x_3);
x_10 = lean::cnstr_get(x_0, 0);
lean::inc(x_10);
lean::dec(x_0);
x_13 = lean::cnstr_get(x_10, 1);
lean::inc(x_13);
lean::dec(x_10);
x_16 = lean::box(0);
lean::inc(x_13);
x_18 = lean::apply_2(x_13, lean::box(0), x_16);
x_19 = lean::apply_3(x_6, lean::box(0), x_9, x_18);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s10_many1__aux_s6___main_s6___rarg_s11___lambda__1), 3, 2);
lean::closure_set(x_20, 0, x_5);
lean::closure_set(x_20, 1, x_13);
x_21 = lean::apply_4(x_4, lean::box(0), lean::box(0), x_19, x_20);
return x_21;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s10_many1__aux_s6___main_s6___rarg_s11___lambda__3(obj* x_0, obj* x_1) {
{
obj* x_2; obj* x_5; obj* x_8; obj* x_9; obj* x_10; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
lean::dec(x_2);
x_8 = lean::box(0);
x_9 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_9, 0, x_1);
lean::cnstr_set(x_9, 1, x_8);
x_10 = lean::apply_2(x_5, lean::box(0), x_9);
return x_10;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s10_many1__aux_s6___main(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s10_many1__aux_s6___main_s6___rarg), 5, 0);
return x_2;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s10_many1__aux_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
{
obj* x_8; 
lean::dec(x_2);
lean::dec(x_1);
x_8 = _l_s4_lean_s6_parser_s13_monad__parsec_s10_many1__aux_s6___main_s6___rarg(x_0, lean::box(0), x_3, x_4, x_5);
return x_8;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s10_many1__aux(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s10_many1__aux_s6___rarg), 6, 0);
return x_4;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_many1_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{
obj* x_6; obj* x_8; obj* x_10; obj* x_13; obj* x_16; obj* x_19; obj* x_21; obj* x_22; obj* x_24; obj* x_25; obj* x_26; 
lean::dec(x_2);
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_0, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_8, 0);
lean::inc(x_10);
lean::dec(x_8);
x_13 = lean::cnstr_get(x_10, 0);
lean::inc(x_13);
lean::dec(x_10);
x_16 = lean::cnstr_get(x_1, 0);
lean::inc(x_16);
lean::dec(x_1);
x_19 = _l_s4_lean_s6_parser_s13_monad__parsec_s10_left__over_s6___rarg_s11___closed__1;
lean::inc(x_19);
x_21 = lean::apply_2(x_16, lean::box(0), x_19);
x_22 = _l_s4_lean_s6_parser_s13_monad__parsec_s9_remaining_s6___rarg_s11___closed__1;
lean::inc(x_22);
x_24 = lean::apply_4(x_13, lean::box(0), lean::box(0), x_22, x_21);
x_25 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s10_many1__aux_s6___main_s6___rarg), 5, 4);
lean::closure_set(x_25, 0, x_0);
lean::closure_set(x_25, 1, lean::box(0));
lean::closure_set(x_25, 2, x_3);
lean::closure_set(x_25, 3, x_4);
x_26 = lean::apply_4(x_6, lean::box(0), lean::box(0), x_24, x_25);
return x_26;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_many1(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s5_many1_s6___rarg), 5, 0);
return x_4;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s4_many_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{
obj* x_6; obj* x_9; obj* x_10; obj* x_13; obj* x_16; obj* x_17; obj* x_18; 
lean::dec(x_2);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
lean::inc(x_3);
x_9 = _l_s4_lean_s6_parser_s13_monad__parsec_s5_many1_s6___rarg(x_0, x_1, lean::box(0), x_3, x_4);
x_10 = lean::cnstr_get(x_3, 0);
lean::inc(x_10);
lean::dec(x_3);
x_13 = lean::cnstr_get(x_10, 1);
lean::inc(x_13);
lean::dec(x_10);
x_16 = lean::box(0);
x_17 = lean::apply_2(x_13, lean::box(0), x_16);
x_18 = lean::apply_3(x_6, lean::box(0), x_9, x_17);
return x_18;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s4_many(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s4_many_s6___rarg), 5, 0);
return x_4;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s14_many1__aux_x27_s6___main_s6___rarg(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_3; obj* x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_2, x_3);
lean::dec(x_3);
if (lean::obj_tag(x_4) == 0)
{
obj* x_7; obj* x_8; obj* x_11; obj* x_13; obj* x_15; obj* x_18; obj* x_19; unsigned char x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
lean::dec(x_4);
x_7 = lean::mk_nat_obj(1u);
x_8 = lean::nat_sub(x_2, x_7);
lean::dec(x_7);
lean::dec(x_2);
x_11 = lean::cnstr_get(x_0, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_11, 4);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_0, 1);
lean::inc(x_15);
lean::inc(x_1);
x_18 = _l_s4_lean_s6_parser_s13_monad__parsec_s14_many1__aux_x27_s6___main_s6___rarg(x_0, x_1, x_8);
x_19 = lean::cnstr_get(x_11, 1);
lean::inc(x_19);
lean::dec(x_11);
x_22 = 0;
x_23 = lean::box(x_22);
x_24 = lean::apply_2(x_19, lean::box(0), x_23);
x_25 = lean::apply_3(x_15, lean::box(0), x_18, x_24);
x_26 = lean::apply_4(x_13, lean::box(0), lean::box(0), x_1, x_25);
return x_26;
}
else
{
obj* x_29; obj* x_32; obj* x_34; unsigned char x_37; obj* x_38; obj* x_39; obj* x_40; 
lean::dec(x_4);
lean::dec(x_2);
x_29 = lean::cnstr_get(x_0, 0);
lean::inc(x_29);
lean::dec(x_0);
x_32 = lean::cnstr_get(x_29, 4);
lean::inc(x_32);
x_34 = lean::cnstr_get(x_29, 1);
lean::inc(x_34);
lean::dec(x_29);
x_37 = 0;
x_38 = lean::box(x_37);
x_39 = lean::apply_2(x_34, lean::box(0), x_38);
x_40 = lean::apply_4(x_32, lean::box(0), lean::box(0), x_1, x_39);
return x_40;
}
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s14_many1__aux_x27_s6___main(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s14_many1__aux_x27_s6___main_s6___rarg), 3, 0);
return x_4;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s14_many1__aux_x27_s6___rarg(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_3; 
x_3 = _l_s4_lean_s6_parser_s13_monad__parsec_s14_many1__aux_x27_s6___main_s6___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s14_many1__aux_x27(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{
obj* x_10; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s14_many1__aux_x27_s6___rarg), 3, 0);
return x_10;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s9_many1_x27_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{
obj* x_6; obj* x_8; obj* x_11; obj* x_14; obj* x_17; obj* x_20; obj* x_22; obj* x_23; obj* x_25; obj* x_26; obj* x_27; 
lean::dec(x_2);
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_0, 0);
lean::inc(x_8);
lean::dec(x_0);
x_11 = lean::cnstr_get(x_8, 0);
lean::inc(x_11);
lean::dec(x_8);
x_14 = lean::cnstr_get(x_11, 0);
lean::inc(x_14);
lean::dec(x_11);
x_17 = lean::cnstr_get(x_1, 0);
lean::inc(x_17);
lean::dec(x_1);
x_20 = _l_s4_lean_s6_parser_s13_monad__parsec_s10_left__over_s6___rarg_s11___closed__1;
lean::inc(x_20);
x_22 = lean::apply_2(x_17, lean::box(0), x_20);
x_23 = _l_s4_lean_s6_parser_s13_monad__parsec_s9_remaining_s6___rarg_s11___closed__1;
lean::inc(x_23);
x_25 = lean::apply_4(x_14, lean::box(0), lean::box(0), x_23, x_22);
x_26 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s14_many1__aux_x27_s6___main_s6___rarg), 3, 2);
lean::closure_set(x_26, 0, x_3);
lean::closure_set(x_26, 1, x_4);
x_27 = lean::apply_4(x_6, lean::box(0), lean::box(0), x_25, x_26);
return x_27;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s9_many1_x27(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s9_many1_x27_s6___rarg), 5, 0);
return x_4;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s8_many_x27_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{
obj* x_6; obj* x_8; obj* x_10; obj* x_13; obj* x_16; obj* x_19; obj* x_22; obj* x_24; obj* x_25; obj* x_27; obj* x_29; obj* x_30; obj* x_31; obj* x_34; unsigned char x_37; obj* x_38; obj* x_39; obj* x_40; 
lean::dec(x_2);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_0, 1);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_0, 0);
lean::inc(x_10);
lean::dec(x_0);
x_13 = lean::cnstr_get(x_10, 0);
lean::inc(x_13);
lean::dec(x_10);
x_16 = lean::cnstr_get(x_13, 0);
lean::inc(x_16);
lean::dec(x_13);
x_19 = lean::cnstr_get(x_1, 0);
lean::inc(x_19);
lean::dec(x_1);
x_22 = _l_s4_lean_s6_parser_s13_monad__parsec_s10_left__over_s6___rarg_s11___closed__1;
lean::inc(x_22);
x_24 = lean::apply_2(x_19, lean::box(0), x_22);
x_25 = _l_s4_lean_s6_parser_s13_monad__parsec_s9_remaining_s6___rarg_s11___closed__1;
lean::inc(x_25);
x_27 = lean::apply_4(x_16, lean::box(0), lean::box(0), x_25, x_24);
lean::inc(x_3);
x_29 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s14_many1__aux_x27_s6___main_s6___rarg), 3, 2);
lean::closure_set(x_29, 0, x_3);
lean::closure_set(x_29, 1, x_4);
x_30 = lean::apply_4(x_8, lean::box(0), lean::box(0), x_27, x_29);
x_31 = lean::cnstr_get(x_3, 0);
lean::inc(x_31);
lean::dec(x_3);
x_34 = lean::cnstr_get(x_31, 1);
lean::inc(x_34);
lean::dec(x_31);
x_37 = 0;
x_38 = lean::box(x_37);
x_39 = lean::apply_2(x_34, lean::box(0), x_38);
x_40 = lean::apply_3(x_6, lean::box(0), x_30, x_39);
return x_40;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s8_many_x27(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s8_many_x27_s6___rarg), 5, 0);
return x_4;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s8_sep__by1_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
{
obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_18; obj* x_21; obj* x_22; obj* x_25; obj* x_26; obj* x_27; 
lean::dec(x_3);
lean::dec(x_2);
x_9 = lean::cnstr_get(x_4, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_9, 2);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_9, 0);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_13, 0);
lean::inc(x_15);
lean::dec(x_13);
x_18 = _l_s4_lean_s6_parser_s13_monad__parsec_s8_sep__by1_s6___rarg_s11___closed__1;
lean::inc(x_5);
lean::inc(x_18);
x_21 = lean::apply_4(x_15, lean::box(0), lean::box(0), x_18, x_5);
x_22 = lean::cnstr_get(x_9, 4);
lean::inc(x_22);
lean::dec(x_9);
x_25 = lean::apply_4(x_22, lean::box(0), lean::box(0), x_6, x_5);
x_26 = _l_s4_lean_s6_parser_s13_monad__parsec_s4_many_s6___rarg(x_0, x_1, lean::box(0), x_4, x_25);
x_27 = lean::apply_4(x_11, lean::box(0), lean::box(0), x_21, x_26);
return x_27;
}
}
obj* _init__l_s4_lean_s6_parser_s13_monad__parsec_s8_sep__by1_s6___rarg_s11___closed__1() {
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s8_sep__by1_s6___rarg_s11___lambda__1), 2, 0);
return x_0;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s8_sep__by1_s6___rarg_s11___lambda__1(obj* x_0, obj* x_1) {
{
obj* x_2; 
x_2 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s8_sep__by1(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s8_sep__by1_s6___rarg), 7, 0);
return x_4;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s7_sep__by_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
{
obj* x_9; obj* x_12; obj* x_13; obj* x_16; obj* x_19; obj* x_20; obj* x_21; 
lean::dec(x_3);
lean::dec(x_2);
x_9 = lean::cnstr_get(x_4, 1);
lean::inc(x_9);
lean::inc(x_4);
x_12 = _l_s4_lean_s6_parser_s13_monad__parsec_s8_sep__by1_s6___rarg(x_0, x_1, lean::box(0), lean::box(0), x_4, x_5, x_6);
x_13 = lean::cnstr_get(x_4, 0);
lean::inc(x_13);
lean::dec(x_4);
x_16 = lean::cnstr_get(x_13, 1);
lean::inc(x_16);
lean::dec(x_13);
x_19 = lean::box(0);
x_20 = lean::apply_2(x_16, lean::box(0), x_19);
x_21 = lean::apply_3(x_9, lean::box(0), x_12, x_20);
return x_21;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s7_sep__by(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s7_sep__by_s6___rarg), 7, 0);
return x_4;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s8_fix__aux_s6___main_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{
obj* x_6; obj* x_7; 
lean::dec(x_2);
x_6 = lean::mk_nat_obj(0u);
x_7 = lean::nat_dec_eq(x_4, x_6);
lean::dec(x_6);
if (lean::obj_tag(x_7) == 0)
{
obj* x_10; obj* x_11; obj* x_15; obj* x_16; 
lean::dec(x_7);
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_sub(x_4, x_10);
lean::dec(x_10);
lean::dec(x_4);
lean::inc(x_3);
x_15 = _l_s4_lean_s6_parser_s13_monad__parsec_s8_fix__aux_s6___main_s6___rarg(x_0, x_1, lean::box(0), x_3, x_11);
x_16 = lean::apply_1(x_3, x_15);
return x_16;
}
else
{
obj* x_21; obj* x_22; obj* x_23; obj* x_27; 
lean::dec(x_4);
lean::dec(x_7);
lean::dec(x_0);
lean::dec(x_3);
x_21 = lean::box(0);
x_22 = _l_s4_lean_s6_parser_s13_monad__parsec_s8_fix__aux_s6___main_s6___rarg_s11___closed__1;
x_23 = _l_s5_mjoin_s6___rarg_s11___closed__1;
lean::inc(x_21);
lean::inc(x_23);
lean::inc(x_22);
x_27 = _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s8_fix__aux_s6___main_s9___spec__1_s6___rarg(x_1, lean::box(0), x_22, x_23, x_21, x_21);
return x_27;
}
}
}
obj* _init__l_s4_lean_s6_parser_s13_monad__parsec_s8_fix__aux_s6___main_s6___rarg_s11___closed__1() {
{
obj* x_0; 
x_0 = lean::mk_string("fix_aux: no progress");
return x_0;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s8_fix__aux_s6___main(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s8_fix__aux_s6___main_s6___rarg), 5, 0);
return x_4;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s8_fix__aux_s6___main_s9___spec__1_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
{
obj* x_7; obj* x_10; obj* x_11; 
lean::dec(x_1);
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s6___rarg_s11___lambda__1), 5, 4);
lean::closure_set(x_10, 0, x_4);
lean::closure_set(x_10, 1, x_2);
lean::closure_set(x_10, 2, x_3);
lean::closure_set(x_10, 3, x_5);
x_11 = lean::apply_2(x_7, lean::box(0), x_10);
return x_11;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s8_fix__aux_s6___main_s9___spec__1(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s8_fix__aux_s6___main_s9___spec__1_s6___rarg), 6, 0);
return x_6;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s8_fix__aux_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
{
obj* x_8; 
lean::dec(x_3);
lean::dec(x_2);
x_8 = _l_s4_lean_s6_parser_s13_monad__parsec_s8_fix__aux_s6___main_s6___rarg(x_0, x_1, lean::box(0), x_4, x_5);
return x_8;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s8_fix__aux(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s8_fix__aux_s6___rarg), 6, 0);
return x_4;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s3_fix_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{
obj* x_7; obj* x_9; obj* x_11; obj* x_14; obj* x_17; obj* x_19; obj* x_21; obj* x_22; obj* x_24; obj* x_25; obj* x_26; 
lean::dec(x_3);
lean::dec(x_2);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_9, 0);
lean::inc(x_11);
lean::dec(x_9);
x_14 = lean::cnstr_get(x_11, 0);
lean::inc(x_14);
lean::dec(x_11);
x_17 = lean::cnstr_get(x_1, 0);
lean::inc(x_17);
x_19 = _l_s4_lean_s6_parser_s13_monad__parsec_s10_left__over_s6___rarg_s11___closed__1;
lean::inc(x_19);
x_21 = lean::apply_2(x_17, lean::box(0), x_19);
x_22 = _l_s4_lean_s6_parser_s13_monad__parsec_s9_remaining_s6___rarg_s11___closed__1;
lean::inc(x_22);
x_24 = lean::apply_4(x_14, lean::box(0), lean::box(0), x_22, x_21);
x_25 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s3_fix_s6___rarg_s11___lambda__1), 4, 3);
lean::closure_set(x_25, 0, x_0);
lean::closure_set(x_25, 1, x_1);
lean::closure_set(x_25, 2, x_4);
x_26 = lean::apply_4(x_7, lean::box(0), lean::box(0), x_24, x_25);
return x_26;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s3_fix_s6___rarg_s11___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{
obj* x_4; obj* x_5; obj* x_8; 
x_4 = lean::mk_nat_obj(1u);
x_5 = lean::nat_add(x_3, x_4);
lean::dec(x_4);
lean::dec(x_3);
x_8 = _l_s4_lean_s6_parser_s13_monad__parsec_s8_fix__aux_s6___main_s6___rarg(x_0, x_1, lean::box(0), x_2, x_5);
return x_8;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s3_fix(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s3_fix_s6___rarg), 5, 0);
return x_4;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s10_foldr__aux_s6___main_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{
obj* x_5; obj* x_6; 
x_5 = lean::mk_nat_obj(0u);
x_6 = lean::nat_dec_eq(x_4, x_5);
lean::dec(x_5);
if (lean::obj_tag(x_6) == 0)
{
obj* x_9; obj* x_10; obj* x_13; obj* x_15; obj* x_17; obj* x_19; obj* x_21; obj* x_26; obj* x_28; obj* x_29; obj* x_30; obj* x_33; obj* x_34; 
lean::dec(x_6);
x_9 = lean::mk_nat_obj(1u);
x_10 = lean::nat_sub(x_4, x_9);
lean::dec(x_9);
lean::dec(x_4);
x_13 = lean::cnstr_get(x_0, 1);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_0, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_15, 2);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_15, 0);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_19, 0);
lean::inc(x_21);
lean::dec(x_19);
lean::inc(x_2);
lean::inc(x_1);
x_26 = lean::apply_4(x_21, lean::box(0), lean::box(0), x_1, x_2);
lean::inc(x_3);
x_28 = _l_s4_lean_s6_parser_s13_monad__parsec_s10_foldr__aux_s6___main_s6___rarg(x_0, x_1, x_2, x_3, x_10);
x_29 = lean::apply_4(x_17, lean::box(0), lean::box(0), x_26, x_28);
x_30 = lean::cnstr_get(x_15, 1);
lean::inc(x_30);
lean::dec(x_15);
x_33 = lean::apply_2(x_30, lean::box(0), x_3);
x_34 = lean::apply_3(x_13, lean::box(0), x_29, x_33);
return x_34;
}
else
{
obj* x_39; obj* x_42; obj* x_45; 
lean::dec(x_4);
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
x_39 = lean::cnstr_get(x_0, 0);
lean::inc(x_39);
lean::dec(x_0);
x_42 = lean::cnstr_get(x_39, 1);
lean::inc(x_42);
lean::dec(x_39);
x_45 = lean::apply_2(x_42, lean::box(0), x_3);
return x_45;
}
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s10_foldr__aux_s6___main(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s10_foldr__aux_s6___main_s6___rarg), 5, 0);
return x_6;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s10_foldr__aux_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{
obj* x_5; 
x_5 = _l_s4_lean_s6_parser_s13_monad__parsec_s10_foldr__aux_s6___main_s6___rarg(x_0, x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s10_foldr__aux(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
{
obj* x_12; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s10_foldr__aux_s6___rarg), 5, 0);
return x_12;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_foldr_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
{
obj* x_10; obj* x_13; obj* x_16; obj* x_18; obj* x_19; obj* x_20; 
lean::dec(x_3);
lean::dec(x_2);
x_10 = lean::cnstr_get(x_0, 1);
lean::inc(x_10);
lean::dec(x_0);
x_13 = lean::cnstr_get(x_1, 0);
lean::inc(x_13);
lean::dec(x_1);
x_16 = _l_s4_lean_s6_parser_s13_monad__parsec_s10_left__over_s6___rarg_s11___closed__1;
lean::inc(x_16);
x_18 = lean::apply_2(x_13, lean::box(0), x_16);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s5_foldr_s6___rarg_s11___lambda__1), 5, 4);
lean::closure_set(x_19, 0, x_4);
lean::closure_set(x_19, 1, x_5);
lean::closure_set(x_19, 2, x_6);
lean::closure_set(x_19, 3, x_7);
x_20 = lean::apply_4(x_10, lean::box(0), lean::box(0), x_18, x_19);
return x_20;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_foldr_s6___rarg_s11___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{
obj* x_5; obj* x_7; 
x_5 = lean::string_iterator_remaining(x_4);
lean::dec(x_4);
x_7 = _l_s4_lean_s6_parser_s13_monad__parsec_s10_foldr__aux_s6___main_s6___rarg(x_0, x_1, x_2, x_3, x_5);
return x_7;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_foldr(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s5_foldr_s6___rarg), 8, 0);
return x_4;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s10_foldl__aux_s6___main_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
{
obj* x_10; obj* x_11; 
lean::dec(x_2);
lean::dec(x_1);
x_10 = lean::mk_nat_obj(0u);
x_11 = lean::nat_dec_eq(x_7, x_10);
lean::dec(x_10);
if (lean::obj_tag(x_11) == 0)
{
obj* x_14; obj* x_15; obj* x_18; obj* x_20; obj* x_25; obj* x_26; obj* x_27; obj* x_30; obj* x_33; obj* x_34; 
lean::dec(x_11);
x_14 = lean::mk_nat_obj(1u);
x_15 = lean::nat_sub(x_7, x_14);
lean::dec(x_14);
lean::dec(x_7);
x_18 = lean::cnstr_get(x_3, 1);
lean::inc(x_18);
x_20 = lean::cnstr_get(x_0, 1);
lean::inc(x_20);
lean::inc(x_5);
lean::inc(x_3);
lean::inc(x_6);
x_25 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s10_foldl__aux_s6___main_s6___rarg_s11___lambda__1), 7, 6);
lean::closure_set(x_25, 0, x_4);
lean::closure_set(x_25, 1, x_6);
lean::closure_set(x_25, 2, x_0);
lean::closure_set(x_25, 3, x_3);
lean::closure_set(x_25, 4, x_5);
lean::closure_set(x_25, 5, x_15);
x_26 = lean::apply_4(x_20, lean::box(0), lean::box(0), x_5, x_25);
x_27 = lean::cnstr_get(x_3, 0);
lean::inc(x_27);
lean::dec(x_3);
x_30 = lean::cnstr_get(x_27, 1);
lean::inc(x_30);
lean::dec(x_27);
x_33 = lean::apply_2(x_30, lean::box(0), x_6);
x_34 = lean::apply_3(x_18, lean::box(0), x_26, x_33);
return x_34;
}
else
{
obj* x_40; obj* x_43; obj* x_46; 
lean::dec(x_11);
lean::dec(x_4);
lean::dec(x_5);
lean::dec(x_7);
lean::dec(x_0);
x_40 = lean::cnstr_get(x_3, 0);
lean::inc(x_40);
lean::dec(x_3);
x_43 = lean::cnstr_get(x_40, 1);
lean::inc(x_43);
lean::dec(x_40);
x_46 = lean::apply_2(x_43, lean::box(0), x_6);
return x_46;
}
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s10_foldl__aux_s6___main_s6___rarg_s11___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
{
obj* x_8; obj* x_9; 
lean::inc(x_0);
x_8 = lean::apply_2(x_0, x_1, x_6);
x_9 = _l_s4_lean_s6_parser_s13_monad__parsec_s10_foldl__aux_s6___main_s6___rarg(x_2, lean::box(0), lean::box(0), x_3, x_0, x_4, x_8, x_5);
return x_9;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s10_foldl__aux_s6___main(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s10_foldl__aux_s6___main_s6___rarg), 8, 0);
return x_2;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s10_foldl__aux_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
{
obj* x_12; 
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
x_12 = _l_s4_lean_s6_parser_s13_monad__parsec_s10_foldl__aux_s6___main_s6___rarg(x_0, lean::box(0), lean::box(0), x_4, x_5, x_6, x_7, x_8);
return x_12;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s10_foldl__aux(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s10_foldl__aux_s6___rarg), 9, 0);
return x_4;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_foldl_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
{
obj* x_10; obj* x_12; obj* x_15; obj* x_17; obj* x_18; obj* x_19; 
lean::dec(x_3);
lean::dec(x_2);
x_10 = lean::cnstr_get(x_0, 1);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_1, 0);
lean::inc(x_12);
lean::dec(x_1);
x_15 = _l_s4_lean_s6_parser_s13_monad__parsec_s10_left__over_s6___rarg_s11___closed__1;
lean::inc(x_15);
x_17 = lean::apply_2(x_12, lean::box(0), x_15);
x_18 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s5_foldl_s6___rarg_s11___lambda__1), 6, 5);
lean::closure_set(x_18, 0, x_0);
lean::closure_set(x_18, 1, x_4);
lean::closure_set(x_18, 2, x_5);
lean::closure_set(x_18, 3, x_7);
lean::closure_set(x_18, 4, x_6);
x_19 = lean::apply_4(x_10, lean::box(0), lean::box(0), x_17, x_18);
return x_19;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_foldl_s6___rarg_s11___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
{
obj* x_6; obj* x_8; 
x_6 = lean::string_iterator_remaining(x_5);
lean::dec(x_5);
x_8 = _l_s4_lean_s6_parser_s13_monad__parsec_s10_foldl__aux_s6___main_s6___rarg(x_0, lean::box(0), lean::box(0), x_1, x_2, x_3, x_4, x_6);
return x_8;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_foldl(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s5_foldl_s6___rarg), 8, 0);
return x_4;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s10_unexpected_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{
obj* x_6; obj* x_7; obj* x_10; 
lean::dec(x_2);
lean::dec(x_0);
x_6 = lean::box(0);
x_7 = _l_s5_mjoin_s6___rarg_s11___closed__1;
lean::inc(x_6);
lean::inc(x_7);
x_10 = _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s10_unexpected_s9___spec__1_s6___rarg(x_1, lean::box(0), x_3, x_7, x_6, x_6);
return x_10;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s10_unexpected(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s10_unexpected_s6___rarg), 4, 0);
return x_4;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s10_unexpected_s9___spec__1_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
{
obj* x_7; obj* x_10; obj* x_11; 
lean::dec(x_1);
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s6___rarg_s11___lambda__1), 5, 4);
lean::closure_set(x_10, 0, x_4);
lean::closure_set(x_10, 1, x_2);
lean::closure_set(x_10, 2, x_3);
lean::closure_set(x_10, 3, x_5);
x_11 = lean::apply_2(x_7, lean::box(0), x_10);
return x_11;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s10_unexpected_s9___spec__1(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s10_unexpected_s9___spec__1_s6___rarg), 6, 0);
return x_6;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s14_unexpected__at_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{
obj* x_7; obj* x_8; obj* x_9; obj* x_11; 
lean::dec(x_2);
lean::dec(x_0);
x_7 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_7, 0, x_4);
x_8 = lean::box(0);
x_9 = _l_s5_mjoin_s6___rarg_s11___closed__1;
lean::inc(x_9);
x_11 = _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s14_unexpected__at_s9___spec__1_s6___rarg(x_1, lean::box(0), x_3, x_9, x_7, x_8);
return x_11;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s14_unexpected__at(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s14_unexpected__at_s6___rarg), 5, 0);
return x_4;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s14_unexpected__at_s9___spec__1_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
{
obj* x_7; obj* x_10; obj* x_11; 
lean::dec(x_1);
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s6___rarg_s11___lambda__1), 5, 4);
lean::closure_set(x_10, 0, x_4);
lean::closure_set(x_10, 1, x_2);
lean::closure_set(x_10, 2, x_3);
lean::closure_set(x_10, 3, x_5);
x_11 = lean::apply_2(x_7, lean::box(0), x_10);
return x_11;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s14_unexpected__at_s9___spec__1(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s14_unexpected__at_s9___spec__1_s6___rarg), 6, 0);
return x_6;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s14_longest__match_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{
obj* x_6; obj* x_8; obj* x_10; obj* x_13; obj* x_15; obj* x_16; 
lean::dec(x_2);
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 0);
lean::inc(x_8);
x_10 = _l_s4_lean_s6_parser_s13_monad__parsec_s10_left__over_s6___rarg_s11___closed__1;
lean::inc(x_10);
lean::inc(x_8);
x_13 = lean::apply_2(x_8, lean::box(0), x_10);
lean::inc(x_6);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s14_longest__match_s6___rarg_s11___lambda__2), 7, 6);
lean::closure_set(x_15, 0, x_0);
lean::closure_set(x_15, 1, x_1);
lean::closure_set(x_15, 2, x_3);
lean::closure_set(x_15, 3, x_4);
lean::closure_set(x_15, 4, x_8);
lean::closure_set(x_15, 5, x_6);
x_16 = lean::apply_4(x_6, lean::box(0), lean::box(0), x_13, x_15);
return x_16;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s14_longest__match_s6___rarg_s11___lambda__1(obj* x_0, obj* x_1) {
{
obj* x_2; obj* x_3; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_except__t_s5_monad_s6___rarg_s11___lambda__8), 2, 1);
lean::closure_set(x_2, 0, x_1);
x_3 = lean::apply_2(x_0, lean::box(0), x_2);
return x_3;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s14_longest__match_s6___rarg_s11___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
{
obj* x_7; obj* x_8; obj* x_9; 
x_7 = _l_s4_list_s6_mfoldr_s6___main_s4___at_s4_lean_s6_parser_s13_monad__parsec_s14_longest__match_s9___spec__2_s6___rarg(x_0, x_1, lean::box(0), x_2, x_6, x_3);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s14_longest__match_s6___rarg_s11___lambda__1), 2, 1);
lean::closure_set(x_8, 0, x_4);
x_9 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_7, x_8);
return x_9;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s14_longest__match(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s14_longest__match_s6___rarg), 5, 0);
return x_4;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s14_longest__match_s9___spec__1_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{
obj* x_5; obj* x_6; unsigned char x_7; obj* x_8; obj* x_9; 
x_5 = _l_s6_option_s13_get__or__else_s6___main_s6___rarg(x_2, x_4);
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
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s14_longest__match_s9___spec__1(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s14_longest__match_s9___spec__1_s6___rarg), 5, 0);
return x_4;
}
}
obj* _l_s4_list_s6_mfoldr_s6___main_s4___at_s4_lean_s6_parser_s13_monad__parsec_s14_longest__match_s9___spec__2_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
{

lean::dec(x_2);
if (lean::obj_tag(x_5) == 0)
{
obj* x_10; obj* x_11; obj* x_12; obj* x_16; obj* x_17; obj* x_20; obj* x_23; 
lean::dec(x_5);
lean::dec(x_1);
lean::dec(x_3);
x_10 = lean::box(0);
x_11 = _l_s4_list_s6_mfoldr_s6___main_s4___at_s4_lean_s6_parser_s13_monad__parsec_s14_longest__match_s9___spec__2_s6___rarg_s11___closed__1;
x_12 = _l_s5_mjoin_s6___rarg_s11___closed__1;
lean::inc(x_10);
lean::inc(x_12);
lean::inc(x_11);
x_16 = _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_monad__parsec_s14_longest__match_s9___spec__1_s6___rarg(x_11, x_12, x_10, x_10, x_4);
x_17 = lean::cnstr_get(x_0, 0);
lean::inc(x_17);
lean::dec(x_0);
x_20 = lean::cnstr_get(x_17, 1);
lean::inc(x_20);
lean::dec(x_17);
x_23 = lean::apply_2(x_20, lean::box(0), x_16);
return x_23;
}
else
{
obj* x_24; obj* x_26; obj* x_29; obj* x_31; obj* x_33; obj* x_35; obj* x_40; obj* x_42; obj* x_43; 
x_24 = lean::cnstr_get(x_5, 0);
lean::inc(x_24);
x_26 = lean::cnstr_get(x_5, 1);
lean::inc(x_26);
lean::dec(x_5);
x_29 = lean::cnstr_get(x_0, 1);
lean::inc(x_29);
x_31 = lean::cnstr_get(x_1, 0);
lean::inc(x_31);
x_33 = _l_s4_lean_s6_parser_s13_monad__parsec_s10_left__over_s6___rarg_s11___closed__1;
lean::inc(x_33);
x_35 = lean::apply_2(x_31, lean::box(0), x_33);
lean::inc(x_4);
lean::inc(x_3);
lean::inc(x_1);
lean::inc(x_0);
x_40 = _l_s4_list_s6_mfoldr_s6___main_s4___at_s4_lean_s6_parser_s13_monad__parsec_s14_longest__match_s9___spec__2_s6___rarg(x_0, x_1, lean::box(0), x_3, x_4, x_26);
lean::inc(x_29);
x_42 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_list_s6_mfoldr_s6___main_s4___at_s4_lean_s6_parser_s13_monad__parsec_s14_longest__match_s9___spec__2_s6___rarg_s11___lambda__4), 8, 7);
lean::closure_set(x_42, 0, x_3);
lean::closure_set(x_42, 1, x_0);
lean::closure_set(x_42, 2, x_29);
lean::closure_set(x_42, 3, x_35);
lean::closure_set(x_42, 4, x_24);
lean::closure_set(x_42, 5, x_4);
lean::closure_set(x_42, 6, x_1);
x_43 = lean::apply_4(x_29, lean::box(0), lean::box(0), x_40, x_42);
return x_43;
}
}
}
obj* _init__l_s4_list_s6_mfoldr_s6___main_s4___at_s4_lean_s6_parser_s13_monad__parsec_s14_longest__match_s9___spec__2_s6___rarg_s11___closed__1() {
{
obj* x_0; 
x_0 = lean::mk_string("longest_match: empty list");
return x_0;
}
}
obj* _l_s4_list_s6_mfoldr_s6___main_s4___at_s4_lean_s6_parser_s13_monad__parsec_s14_longest__match_s9___spec__2_s6___rarg_s11___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{
obj* x_4; obj* x_7; unsigned char x_10; 
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
lean::dec(x_0);
x_7 = lean::cnstr_get(x_4, 1);
lean::inc(x_7);
lean::dec(x_4);
if (lean::obj_tag(x_2) == 0)
{
obj* x_12; obj* x_14; obj* x_16; 
x_12 = lean::cnstr_get(x_2, 0);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_2, 1);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_2, 2);
lean::inc(x_16);
if (lean::obj_tag(x_16) == 0)
{
obj* x_18; obj* x_19; obj* x_21; 
x_18 = lean::string_iterator_offset(x_3);
x_19 = lean::string_iterator_offset(x_14);
lean::dec(x_14);
x_21 = lean::nat_dec_lt(x_18, x_19);
if (lean::obj_tag(x_21) == 0)
{
obj* x_24; 
lean::dec(x_2);
lean::dec(x_21);
x_24 = lean::nat_dec_lt(x_19, x_18);
lean::dec(x_18);
lean::dec(x_19);
if (lean::obj_tag(x_24) == 0)
{
obj* x_28; obj* x_29; obj* x_30; 
lean::dec(x_24);
x_28 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_28, 0, x_1);
lean::cnstr_set(x_28, 1, x_12);
x_29 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_3);
lean::cnstr_set(x_29, 2, x_16);
x_30 = lean::apply_2(x_7, lean::box(0), x_29);
return x_30;
}
else
{
obj* x_33; obj* x_34; obj* x_35; obj* x_36; 
lean::dec(x_12);
lean::dec(x_24);
x_33 = lean::box(0);
x_34 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_34, 0, x_1);
lean::cnstr_set(x_34, 1, x_33);
x_35 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_3);
lean::cnstr_set(x_35, 2, x_16);
x_36 = lean::apply_2(x_7, lean::box(0), x_35);
return x_36;
}
}
else
{
obj* x_44; 
lean::dec(x_16);
lean::dec(x_18);
lean::dec(x_19);
lean::dec(x_12);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_21);
x_44 = lean::apply_2(x_7, lean::box(0), x_2);
return x_44;
}
}
else
{
unsigned char x_49; 
lean::dec(x_14);
lean::dec(x_16);
lean::dec(x_12);
lean::dec(x_2);
x_49 = 0;
x_10 = x_49;
goto lbl_11;
}
}
else
{
unsigned char x_51; 
lean::dec(x_2);
x_51 = 0;
x_10 = x_51;
goto lbl_11;
}
lbl_11:
{
obj* x_52; obj* x_54; obj* x_55; obj* x_56; 
x_52 = lean::box(0);
lean::inc(x_52);
x_54 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_54, 0, x_1);
lean::cnstr_set(x_54, 1, x_52);
x_55 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_55, 0, x_54);
lean::cnstr_set(x_55, 1, x_3);
lean::cnstr_set(x_55, 2, x_52);
x_56 = lean::apply_2(x_7, lean::box(0), x_55);
return x_56;
}
}
}
obj* _l_s4_list_s6_mfoldr_s6___main_s4___at_s4_lean_s6_parser_s13_monad__parsec_s14_longest__match_s9___spec__2_s6___rarg_s11___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{
obj* x_5; obj* x_6; 
x_5 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_list_s6_mfoldr_s6___main_s4___at_s4_lean_s6_parser_s13_monad__parsec_s14_longest__match_s9___spec__2_s6___rarg_s11___lambda__1), 4, 3);
lean::closure_set(x_5, 0, x_0);
lean::closure_set(x_5, 1, x_4);
lean::closure_set(x_5, 2, x_1);
x_6 = lean::apply_4(x_2, lean::box(0), lean::box(0), x_3, x_5);
return x_6;
}
}
obj* _l_s4_list_s6_mfoldr_s6___main_s4___at_s4_lean_s6_parser_s13_monad__parsec_s14_longest__match_s9___spec__2_s6___rarg_s11___lambda__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{
obj* x_4; obj* x_7; 
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
lean::dec(x_0);
x_7 = lean::cnstr_get(x_4, 1);
lean::inc(x_7);
lean::dec(x_4);
if (lean::obj_tag(x_1) == 0)
{
obj* x_12; 
lean::dec(x_2);
lean::dec(x_3);
x_12 = lean::apply_2(x_7, lean::box(0), x_1);
return x_12;
}
else
{
obj* x_13; obj* x_15; obj* x_17; obj* x_19; obj* x_21; obj* x_23; 
x_13 = lean::cnstr_get(x_1, 0);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_3, 0);
lean::inc(x_15);
x_17 = lean::string_iterator_offset(x_15);
lean::dec(x_15);
x_19 = lean::cnstr_get(x_13, 0);
lean::inc(x_19);
x_21 = lean::string_iterator_offset(x_19);
lean::dec(x_19);
x_23 = lean::nat_dec_lt(x_17, x_21);
if (lean::obj_tag(x_23) == 0)
{
obj* x_26; 
lean::dec(x_1);
lean::dec(x_23);
x_26 = lean::nat_dec_lt(x_21, x_17);
lean::dec(x_21);
if (lean::obj_tag(x_26) == 0)
{
obj* x_29; obj* x_30; obj* x_32; 
lean::dec(x_26);
x_29 = _l_s4_lean_s6_parser_s9_parsec__t_s5_merge_s6___rarg(x_3, x_13);
x_30 = lean::string_iterator_offset(x_2);
lean::dec(x_2);
x_32 = lean::nat_dec_lt(x_30, x_17);
lean::dec(x_17);
lean::dec(x_30);
if (lean::obj_tag(x_32) == 0)
{
unsigned char x_36; obj* x_37; obj* x_38; obj* x_39; 
lean::dec(x_32);
x_36 = 0;
x_37 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_37, 0, x_29);
lean::cnstr_set_scalar(x_37, sizeof(void*)*1, x_36);
x_38 = x_37;
x_39 = lean::apply_2(x_7, lean::box(0), x_38);
return x_39;
}
else
{
unsigned char x_41; obj* x_42; obj* x_43; obj* x_44; 
lean::dec(x_32);
x_41 = 1;
x_42 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_42, 0, x_29);
lean::cnstr_set_scalar(x_42, sizeof(void*)*1, x_41);
x_43 = x_42;
x_44 = lean::apply_2(x_7, lean::box(0), x_43);
return x_44;
}
}
else
{
unsigned char x_49; obj* x_50; obj* x_51; obj* x_52; 
lean::dec(x_17);
lean::dec(x_13);
lean::dec(x_2);
lean::dec(x_26);
x_49 = 1;
x_50 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_50, 0, x_3);
lean::cnstr_set_scalar(x_50, sizeof(void*)*1, x_49);
x_51 = x_50;
x_52 = lean::apply_2(x_7, lean::box(0), x_51);
return x_52;
}
}
else
{
obj* x_59; 
lean::dec(x_17);
lean::dec(x_21);
lean::dec(x_13);
lean::dec(x_2);
lean::dec(x_3);
lean::dec(x_23);
x_59 = lean::apply_2(x_7, lean::box(0), x_1);
return x_59;
}
}
}
}
obj* _l_s4_list_s6_mfoldr_s6___main_s4___at_s4_lean_s6_parser_s13_monad__parsec_s14_longest__match_s9___spec__2_s6___rarg_s11___lambda__4(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
{
obj* x_8; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_21; obj* x_23; 
x_8 = lean::cnstr_get(x_0, 1);
lean::inc(x_8);
lean::dec(x_0);
lean::inc(x_2);
lean::inc(x_7);
lean::inc(x_1);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_list_s6_mfoldr_s6___main_s4___at_s4_lean_s6_parser_s13_monad__parsec_s14_longest__match_s9___spec__2_s6___rarg_s11___lambda__2), 5, 4);
lean::closure_set(x_14, 0, x_1);
lean::closure_set(x_14, 1, x_7);
lean::closure_set(x_14, 2, x_2);
lean::closure_set(x_14, 3, x_3);
x_15 = lean::apply_4(x_2, lean::box(0), lean::box(0), x_4, x_14);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_list_s6_mfoldr_s6___main_s4___at_s4_lean_s6_parser_s13_monad__parsec_s14_longest__match_s9___spec__2_s6___rarg_s11___lambda__3), 4, 3);
lean::closure_set(x_16, 0, x_1);
lean::closure_set(x_16, 1, x_7);
lean::closure_set(x_16, 2, x_5);
x_17 = lean::apply_3(x_8, lean::box(0), x_15, x_16);
x_18 = lean::cnstr_get(x_6, 1);
lean::inc(x_18);
lean::dec(x_6);
x_21 = _l_s4_lean_s6_parser_s13_monad__parsec_s9_lookahead_s6___rarg_s11___closed__1;
lean::inc(x_21);
x_23 = lean::apply_3(x_18, lean::box(0), x_21, x_17);
return x_23;
}
}
obj* _l_s4_list_s6_mfoldr_s6___main_s4___at_s4_lean_s6_parser_s13_monad__parsec_s14_longest__match_s9___spec__2(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_list_s6_mfoldr_s6___main_s4___at_s4_lean_s6_parser_s13_monad__parsec_s14_longest__match_s9___spec__2_s6___rarg), 6, 0);
return x_4;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s9_observing_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{
obj* x_7; obj* x_10; obj* x_13; obj* x_15; obj* x_18; obj* x_20; obj* x_21; obj* x_22; 
lean::dec(x_2);
lean::dec(x_1);
x_7 = lean::cnstr_get(x_3, 1);
lean::inc(x_7);
lean::dec(x_3);
x_10 = lean::cnstr_get(x_0, 0);
lean::inc(x_10);
lean::dec(x_0);
x_13 = lean::cnstr_get(x_10, 0);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_13, 0);
lean::inc(x_15);
lean::dec(x_13);
x_18 = _l_s9_except__t_s4_lift_s6___rarg_s11___closed__1;
lean::inc(x_18);
x_20 = lean::apply_4(x_15, lean::box(0), lean::box(0), x_18, x_4);
x_21 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s9_observing_s6___rarg_s11___lambda__1), 2, 1);
lean::closure_set(x_21, 0, x_10);
x_22 = lean::apply_3(x_7, lean::box(0), x_20, x_21);
return x_22;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s9_observing_s6___rarg_s11___lambda__1(obj* x_0, obj* x_1) {
{
obj* x_2; obj* x_5; obj* x_6; 
x_2 = lean::cnstr_get(x_0, 1);
lean::inc(x_2);
lean::dec(x_0);
x_5 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_5, 0, x_1);
x_6 = lean::apply_2(x_2, lean::box(0), x_5);
return x_6;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s9_observing(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s9_observing_s6___rarg), 5, 0);
return x_4;
}
}
obj* _l_s4_lean_s6_parser_s9_parsec__t_s5_parse_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{
obj* x_6; 
lean::dec(x_1);
x_6 = _l_s4_lean_s6_parser_s9_parsec__t_s3_run_s6___rarg(x_0, lean::box(0), lean::box(0), x_2, x_3, x_4);
return x_6;
}
}
obj* _l_s4_lean_s6_parser_s9_parsec__t_s5_parse(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s9_parsec__t_s5_parse_s6___rarg), 5, 0);
return x_4;
}
}
obj* _l_s4_lean_s6_parser_s9_parsec__t_s16_parse__with__eoi_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{
obj* x_7; obj* x_8; 
lean::dec(x_1);
lean::inc(x_0);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s9_parsec__t_s16_parse__with__eoi_s6___rarg_s11___lambda__3), 3, 2);
lean::closure_set(x_7, 0, x_0);
lean::closure_set(x_7, 1, x_2);
x_8 = _l_s4_lean_s6_parser_s9_parsec__t_s3_run_s4___at_s4_lean_s6_parser_s9_parsec__t_s16_parse__with__eoi_s9___spec__3_s6___rarg(x_0, lean::box(0), lean::box(0), x_7, x_3, x_4);
return x_8;
}
}
obj* _l_s4_lean_s6_parser_s9_parsec__t_s16_parse__with__eoi_s6___rarg_s11___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
{

if (lean::obj_tag(x_3) == 0)
{
obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_13; obj* x_15; obj* x_16; obj* x_17; 
x_4 = lean::cnstr_get(x_3, 1);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_3, 2);
lean::inc(x_6);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_8 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 1);
 lean::cnstr_release(x_3, 2);
 x_8 = x_3;
}
x_9 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s9_parsec__t_s13_bind__mk__res_s6___rarg), 2, 1);
lean::closure_set(x_9, 0, x_6);
x_10 = lean::cnstr_get(x_0, 1);
lean::inc(x_10);
lean::dec(x_0);
x_13 = _l_s4_lean_s6_parser_s6_parsec_s6_result_s7_mk__eps_s6___rarg_s11___closed__1;
lean::inc(x_13);
if (lean::is_scalar(x_8)) {
 x_15 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_15 = x_8;
}
lean::cnstr_set(x_15, 0, x_1);
lean::cnstr_set(x_15, 1, x_4);
lean::cnstr_set(x_15, 2, x_13);
x_16 = lean::apply_2(x_10, lean::box(0), x_15);
x_17 = lean::apply_4(x_2, lean::box(0), lean::box(0), x_9, x_16);
return x_17;
}
else
{
obj* x_20; unsigned char x_22; obj* x_23; obj* x_24; obj* x_27; obj* x_28; obj* x_29; 
lean::dec(x_1);
lean::dec(x_2);
x_20 = lean::cnstr_get(x_3, 0);
lean::inc(x_20);
x_22 = lean::cnstr_get_scalar<unsigned char>(x_3, sizeof(void*)*1);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_23 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 x_23 = x_3;
}
x_24 = lean::cnstr_get(x_0, 1);
lean::inc(x_24);
lean::dec(x_0);
if (lean::is_scalar(x_23)) {
 x_27 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_27 = x_23;
}
lean::cnstr_set(x_27, 0, x_20);
lean::cnstr_set_scalar(x_27, sizeof(void*)*1, x_22);
x_28 = x_27;
x_29 = lean::apply_2(x_24, lean::box(0), x_28);
return x_29;
}
}
}
obj* _l_s4_lean_s6_parser_s9_parsec__t_s16_parse__with__eoi_s6___rarg_s11___lambda__2(obj* x_0, obj* x_1, obj* x_2) {
{

if (lean::obj_tag(x_2) == 0)
{
obj* x_3; obj* x_5; obj* x_7; obj* x_10; obj* x_12; obj* x_14; obj* x_17; obj* x_18; obj* x_20; obj* x_21; obj* x_22; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_2, 2);
lean::inc(x_7);
lean::dec(x_2);
x_10 = lean::cnstr_get(x_0, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_10, 0);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_12, 0);
lean::inc(x_14);
lean::dec(x_12);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s9_parsec__t_s13_bind__mk__res_s6___rarg), 2, 1);
lean::closure_set(x_17, 0, x_7);
x_18 = _l_s4_lean_s6_parser_s13_monad__parsec_s3_eoi_s4___at_s4_lean_s6_parser_s9_parsec__t_s16_parse__with__eoi_s9___spec__1_s6___rarg(x_0, x_5);
lean::inc(x_14);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s9_parsec__t_s16_parse__with__eoi_s6___rarg_s11___lambda__1), 4, 3);
lean::closure_set(x_20, 0, x_10);
lean::closure_set(x_20, 1, x_3);
lean::closure_set(x_20, 2, x_14);
x_21 = lean::apply_4(x_1, lean::box(0), lean::box(0), x_18, x_20);
x_22 = lean::apply_4(x_14, lean::box(0), lean::box(0), x_17, x_21);
return x_22;
}
else
{
obj* x_24; unsigned char x_26; obj* x_27; obj* x_28; obj* x_31; obj* x_34; obj* x_35; obj* x_36; 
lean::dec(x_1);
x_24 = lean::cnstr_get(x_2, 0);
lean::inc(x_24);
x_26 = lean::cnstr_get_scalar<unsigned char>(x_2, sizeof(void*)*1);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_27 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 x_27 = x_2;
}
x_28 = lean::cnstr_get(x_0, 0);
lean::inc(x_28);
lean::dec(x_0);
x_31 = lean::cnstr_get(x_28, 1);
lean::inc(x_31);
lean::dec(x_28);
if (lean::is_scalar(x_27)) {
 x_34 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_34 = x_27;
}
lean::cnstr_set(x_34, 0, x_24);
lean::cnstr_set_scalar(x_34, sizeof(void*)*1, x_26);
x_35 = x_34;
x_36 = lean::apply_2(x_31, lean::box(0), x_35);
return x_36;
}
}
}
obj* _l_s4_lean_s6_parser_s9_parsec__t_s16_parse__with__eoi_s6___rarg_s11___lambda__3(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; 
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::apply_1(x_1, x_2);
lean::inc(x_3);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s9_parsec__t_s16_parse__with__eoi_s6___rarg_s11___lambda__2), 3, 2);
lean::closure_set(x_7, 0, x_0);
lean::closure_set(x_7, 1, x_3);
x_8 = lean::apply_4(x_3, lean::box(0), lean::box(0), x_5, x_7);
return x_8;
}
}
obj* _l_s4_lean_s6_parser_s9_parsec__t_s16_parse__with__eoi(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s9_parsec__t_s16_parse__with__eoi_s6___rarg), 5, 0);
return x_4;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s9_parsec__t_s16_parse__with__eoi_s9___spec__2_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
{
obj* x_8; obj* x_11; obj* x_14; obj* x_15; unsigned char x_16; obj* x_17; obj* x_18; obj* x_19; 
lean::dec(x_1);
x_8 = lean::cnstr_get(x_0, 0);
lean::inc(x_8);
lean::dec(x_0);
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
lean::dec(x_8);
x_14 = _l_s6_option_s13_get__or__else_s6___main_s6___rarg(x_4, x_6);
x_15 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_15, 0, x_14);
lean::cnstr_set(x_15, 1, x_2);
lean::cnstr_set(x_15, 2, x_3);
lean::cnstr_set(x_15, 3, x_5);
x_16 = 0;
x_17 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set_scalar(x_17, sizeof(void*)*1, x_16);
x_18 = x_17;
x_19 = lean::apply_2(x_11, lean::box(0), x_18);
return x_19;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s9_parsec__t_s16_parse__with__eoi_s9___spec__2(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s9_parsec__t_s16_parse__with__eoi_s9___spec__2_s6___rarg), 7, 0);
return x_4;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s3_eoi_s4___at_s4_lean_s6_parser_s9_parsec__t_s16_parse__with__eoi_s9___spec__1_s6___rarg(obj* x_0, obj* x_1) {
{
obj* x_2; obj* x_4; obj* x_6; obj* x_8; obj* x_11; obj* x_13; obj* x_15; obj* x_16; 
x_2 = lean::cnstr_get(x_0, 1);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_4, 1);
lean::inc(x_6);
x_8 = _l_s4_lean_s6_parser_s6_parsec_s6_result_s7_mk__eps_s6___rarg_s11___closed__1;
lean::inc(x_8);
lean::inc(x_1);
x_11 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_11, 0, x_1);
lean::cnstr_set(x_11, 1, x_1);
lean::cnstr_set(x_11, 2, x_8);
lean::inc(x_6);
x_13 = lean::apply_2(x_6, lean::box(0), x_11);
lean::inc(x_8);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s3_eoi_s4___at_s4_lean_s6_parser_s9_parsec__t_s16_parse__with__eoi_s9___spec__1_s6___rarg_s11___lambda__1), 5, 4);
lean::closure_set(x_15, 0, x_4);
lean::closure_set(x_15, 1, x_0);
lean::closure_set(x_15, 2, x_8);
lean::closure_set(x_15, 3, x_6);
x_16 = lean::apply_4(x_2, lean::box(0), lean::box(0), x_13, x_15);
return x_16;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s3_eoi_s4___at_s4_lean_s6_parser_s9_parsec__t_s16_parse__with__eoi_s9___spec__1_s6___rarg_s11___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{

if (lean::obj_tag(x_4) == 0)
{
obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_12; obj* x_15; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_4, 1);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_4, 2);
lean::inc(x_9);
if (lean::is_shared(x_4)) {
 lean::dec(x_4);
 x_11 = lean::box(0);
} else {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_release(x_4, 1);
 lean::cnstr_release(x_4, 2);
 x_11 = x_4;
}
x_12 = lean::cnstr_get(x_0, 0);
lean::inc(x_12);
lean::dec(x_0);
x_15 = lean::cnstr_get(x_12, 0);
lean::inc(x_15);
lean::dec(x_12);
x_18 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s9_parsec__t_s13_bind__mk__res_s6___rarg), 2, 1);
lean::closure_set(x_18, 0, x_9);
x_19 = lean::string_iterator_remaining(x_5);
x_20 = lean::mk_nat_obj(0u);
x_21 = lean::nat_dec_eq(x_19, x_20);
lean::dec(x_20);
lean::dec(x_19);
if (lean::obj_tag(x_21) == 0)
{
unsigned x_28; obj* x_30; obj* x_31; obj* x_33; obj* x_35; obj* x_36; obj* x_37; obj* x_40; obj* x_41; 
lean::dec(x_11);
lean::dec(x_2);
lean::dec(x_3);
lean::dec(x_21);
x_28 = lean::string_iterator_curr(x_5);
lean::dec(x_5);
x_30 = _l_s4_char_s11_quote__core(x_28);
x_31 = _l_s4_char_s9_has__repr_s11___closed__1;
lean::inc(x_31);
x_33 = lean::string_append(x_31, x_30);
lean::dec(x_30);
x_35 = lean::string_append(x_33, x_31);
x_36 = lean::box(0);
x_37 = _l_s4_lean_s6_parser_s13_monad__parsec_s3_eoi_s6___rarg_s11___lambda__1_s11___closed__1;
lean::inc(x_36);
lean::inc(x_37);
x_40 = _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s9_parsec__t_s16_parse__with__eoi_s9___spec__2_s6___rarg(x_1, lean::box(0), x_35, x_37, x_36, x_36, x_7);
x_41 = lean::apply_4(x_15, lean::box(0), lean::box(0), x_18, x_40);
return x_41;
}
else
{
unsigned char x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; 
lean::dec(x_5);
lean::dec(x_1);
lean::dec(x_21);
x_45 = 0;
x_46 = lean::box(x_45);
if (lean::is_scalar(x_11)) {
 x_47 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_47 = x_11;
}
lean::cnstr_set(x_47, 0, x_46);
lean::cnstr_set(x_47, 1, x_7);
lean::cnstr_set(x_47, 2, x_2);
x_48 = lean::apply_2(x_3, lean::box(0), x_47);
x_49 = lean::apply_4(x_15, lean::box(0), lean::box(0), x_18, x_48);
return x_49;
}
}
else
{
obj* x_53; unsigned char x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; 
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
x_53 = lean::cnstr_get(x_4, 0);
lean::inc(x_53);
x_55 = lean::cnstr_get_scalar<unsigned char>(x_4, sizeof(void*)*1);
if (lean::is_shared(x_4)) {
 lean::dec(x_4);
 x_56 = lean::box(0);
} else {
 lean::cnstr_release(x_4, 0);
 x_56 = x_4;
}
if (lean::is_scalar(x_56)) {
 x_57 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_57 = x_56;
}
lean::cnstr_set(x_57, 0, x_53);
lean::cnstr_set_scalar(x_57, sizeof(void*)*1, x_55);
x_58 = x_57;
x_59 = lean::apply_2(x_3, lean::box(0), x_58);
return x_59;
}
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s3_eoi_s4___at_s4_lean_s6_parser_s9_parsec__t_s16_parse__with__eoi_s9___spec__1(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s3_eoi_s4___at_s4_lean_s6_parser_s9_parsec__t_s16_parse__with__eoi_s9___spec__1_s6___rarg), 2, 0);
return x_4;
}
}
obj* _l_s4_lean_s6_parser_s9_parsec__t_s3_run_s4___at_s4_lean_s6_parser_s9_parsec__t_s16_parse__with__eoi_s9___spec__3_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
{
obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
lean::dec(x_5);
lean::dec(x_2);
lean::dec(x_1);
x_9 = lean::cnstr_get(x_0, 1);
lean::inc(x_9);
x_11 = lean::string_mk_iterator(x_4);
x_12 = lean::apply_1(x_3, x_11);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s9_parsec__t_s3_run_s6___rarg_s11___lambda__1), 2, 1);
lean::closure_set(x_13, 0, x_0);
x_14 = lean::apply_4(x_9, lean::box(0), lean::box(0), x_12, x_13);
return x_14;
}
}
obj* _l_s4_lean_s6_parser_s9_parsec__t_s3_run_s4___at_s4_lean_s6_parser_s9_parsec__t_s16_parse__with__eoi_s9___spec__3(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s9_parsec__t_s3_run_s4___at_s4_lean_s6_parser_s9_parsec__t_s16_parse__with__eoi_s9___spec__3_s6___rarg), 6, 0);
return x_2;
}
}
obj* _l_s4_lean_s6_parser_s9_parsec__t_s23_parse__with__left__over_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{
obj* x_7; obj* x_8; 
lean::dec(x_1);
lean::inc(x_0);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s9_parsec__t_s23_parse__with__left__over_s6___rarg_s11___lambda__4), 3, 2);
lean::closure_set(x_7, 0, x_0);
lean::closure_set(x_7, 1, x_2);
x_8 = _l_s4_lean_s6_parser_s9_parsec__t_s3_run_s4___at_s4_lean_s6_parser_s9_parsec__t_s23_parse__with__left__over_s9___spec__1_s6___rarg(x_0, lean::box(0), lean::box(0), x_7, x_3, x_4);
return x_8;
}
}
obj* _l_s4_lean_s6_parser_s9_parsec__t_s23_parse__with__left__over_s6___rarg_s11___lambda__1(obj* x_0, obj* x_1) {
{

if (lean::obj_tag(x_1) == 0)
{
obj* x_2; obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_12; obj* x_14; obj* x_17; obj* x_18; obj* x_19; obj* x_22; obj* x_24; obj* x_25; obj* x_26; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_1, 2);
lean::inc(x_6);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_8 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 lean::cnstr_release(x_1, 1);
 lean::cnstr_release(x_1, 2);
 x_8 = x_1;
}
x_9 = lean::cnstr_get(x_0, 0);
lean::inc(x_9);
lean::dec(x_0);
x_12 = lean::cnstr_get(x_9, 0);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_12, 0);
lean::inc(x_14);
lean::dec(x_12);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s9_parsec__t_s13_bind__mk__res_s6___rarg), 2, 1);
lean::closure_set(x_17, 0, x_6);
x_18 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_list_s3_zip_s6___rarg_s11___lambda__1), 2, 1);
lean::closure_set(x_18, 0, x_2);
x_19 = lean::cnstr_get(x_9, 1);
lean::inc(x_19);
lean::dec(x_9);
x_22 = _l_s4_lean_s6_parser_s6_parsec_s6_result_s7_mk__eps_s6___rarg_s11___closed__1;
lean::inc(x_22);
if (lean::is_scalar(x_8)) {
 x_24 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_24 = x_8;
}
lean::cnstr_set(x_24, 0, x_18);
lean::cnstr_set(x_24, 1, x_4);
lean::cnstr_set(x_24, 2, x_22);
x_25 = lean::apply_2(x_19, lean::box(0), x_24);
x_26 = lean::apply_4(x_14, lean::box(0), lean::box(0), x_17, x_25);
return x_26;
}
else
{
obj* x_27; unsigned char x_29; obj* x_30; obj* x_31; obj* x_34; obj* x_37; obj* x_38; obj* x_39; 
x_27 = lean::cnstr_get(x_1, 0);
lean::inc(x_27);
x_29 = lean::cnstr_get_scalar<unsigned char>(x_1, sizeof(void*)*1);
if (lean::is_shared(x_1)) {
 lean::dec(x_1);
 x_30 = lean::box(0);
} else {
 lean::cnstr_release(x_1, 0);
 x_30 = x_1;
}
x_31 = lean::cnstr_get(x_0, 0);
lean::inc(x_31);
lean::dec(x_0);
x_34 = lean::cnstr_get(x_31, 1);
lean::inc(x_34);
lean::dec(x_31);
if (lean::is_scalar(x_30)) {
 x_37 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_37 = x_30;
}
lean::cnstr_set(x_37, 0, x_27);
lean::cnstr_set_scalar(x_37, sizeof(void*)*1, x_29);
x_38 = x_37;
x_39 = lean::apply_2(x_34, lean::box(0), x_38);
return x_39;
}
}
}
obj* _l_s4_lean_s6_parser_s9_parsec__t_s23_parse__with__left__over_s6___rarg_s11___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
{

if (lean::obj_tag(x_4) == 0)
{
obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_4, 1);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_4, 2);
lean::inc(x_9);
if (lean::is_shared(x_4)) {
 lean::dec(x_4);
 x_11 = lean::box(0);
} else {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_release(x_4, 1);
 lean::cnstr_release(x_4, 2);
 x_11 = x_4;
}
x_12 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s9_parsec__t_s13_bind__mk__res_s6___rarg), 2, 1);
lean::closure_set(x_12, 0, x_9);
x_13 = lean::apply_1(x_0, x_5);
if (lean::is_scalar(x_11)) {
 x_14 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_14 = x_11;
}
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_7);
lean::cnstr_set(x_14, 2, x_1);
x_15 = lean::apply_2(x_2, lean::box(0), x_14);
x_16 = lean::apply_4(x_3, lean::box(0), lean::box(0), x_12, x_15);
return x_16;
}
else
{
obj* x_20; unsigned char x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_3);
x_20 = lean::cnstr_get(x_4, 0);
lean::inc(x_20);
x_22 = lean::cnstr_get_scalar<unsigned char>(x_4, sizeof(void*)*1);
if (lean::is_shared(x_4)) {
 lean::dec(x_4);
 x_23 = lean::box(0);
} else {
 lean::cnstr_release(x_4, 0);
 x_23 = x_4;
}
if (lean::is_scalar(x_23)) {
 x_24 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_24 = x_23;
}
lean::cnstr_set(x_24, 0, x_20);
lean::cnstr_set_scalar(x_24, sizeof(void*)*1, x_22);
x_25 = x_24;
x_26 = lean::apply_2(x_2, lean::box(0), x_25);
return x_26;
}
}
}
obj* _l_s4_lean_s6_parser_s9_parsec__t_s23_parse__with__left__over_s6___rarg_s11___lambda__3(obj* x_0, obj* x_1, obj* x_2) {
{

if (lean::obj_tag(x_2) == 0)
{
obj* x_3; obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_13; obj* x_15; obj* x_18; obj* x_19; obj* x_22; obj* x_25; obj* x_27; obj* x_30; obj* x_31; obj* x_32; 
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
x_10 = lean::cnstr_get(x_0, 0);
lean::inc(x_10);
lean::dec(x_0);
x_13 = lean::cnstr_get(x_10, 0);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_13, 0);
lean::inc(x_15);
lean::dec(x_13);
x_18 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s9_parsec__t_s13_bind__mk__res_s6___rarg), 2, 1);
lean::closure_set(x_18, 0, x_7);
x_19 = lean::cnstr_get(x_10, 1);
lean::inc(x_19);
lean::dec(x_10);
x_22 = _l_s4_lean_s6_parser_s6_parsec_s6_result_s7_mk__eps_s6___rarg_s11___closed__1;
lean::inc(x_22);
lean::inc(x_5);
if (lean::is_scalar(x_9)) {
 x_25 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_25 = x_9;
}
lean::cnstr_set(x_25, 0, x_5);
lean::cnstr_set(x_25, 1, x_5);
lean::cnstr_set(x_25, 2, x_22);
lean::inc(x_19);
x_27 = lean::apply_2(x_19, lean::box(0), x_25);
lean::inc(x_15);
lean::inc(x_22);
x_30 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s9_parsec__t_s23_parse__with__left__over_s6___rarg_s11___lambda__2), 5, 4);
lean::closure_set(x_30, 0, x_3);
lean::closure_set(x_30, 1, x_22);
lean::closure_set(x_30, 2, x_19);
lean::closure_set(x_30, 3, x_15);
x_31 = lean::apply_4(x_1, lean::box(0), lean::box(0), x_27, x_30);
x_32 = lean::apply_4(x_15, lean::box(0), lean::box(0), x_18, x_31);
return x_32;
}
else
{
obj* x_34; unsigned char x_36; obj* x_37; obj* x_38; obj* x_41; obj* x_44; obj* x_45; obj* x_46; 
lean::dec(x_1);
x_34 = lean::cnstr_get(x_2, 0);
lean::inc(x_34);
x_36 = lean::cnstr_get_scalar<unsigned char>(x_2, sizeof(void*)*1);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_37 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 x_37 = x_2;
}
x_38 = lean::cnstr_get(x_0, 0);
lean::inc(x_38);
lean::dec(x_0);
x_41 = lean::cnstr_get(x_38, 1);
lean::inc(x_41);
lean::dec(x_38);
if (lean::is_scalar(x_37)) {
 x_44 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_44 = x_37;
}
lean::cnstr_set(x_44, 0, x_34);
lean::cnstr_set_scalar(x_44, sizeof(void*)*1, x_36);
x_45 = x_44;
x_46 = lean::apply_2(x_41, lean::box(0), x_45);
return x_46;
}
}
}
obj* _l_s4_lean_s6_parser_s9_parsec__t_s23_parse__with__left__over_s6___rarg_s11___lambda__4(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_3; obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_12; 
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::apply_1(x_1, x_2);
lean::inc(x_0);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s9_parsec__t_s23_parse__with__left__over_s6___rarg_s11___lambda__1), 2, 1);
lean::closure_set(x_7, 0, x_0);
lean::inc(x_3);
x_9 = lean::apply_4(x_3, lean::box(0), lean::box(0), x_5, x_7);
lean::inc(x_3);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s9_parsec__t_s23_parse__with__left__over_s6___rarg_s11___lambda__3), 3, 2);
lean::closure_set(x_11, 0, x_0);
lean::closure_set(x_11, 1, x_3);
x_12 = lean::apply_4(x_3, lean::box(0), lean::box(0), x_9, x_11);
return x_12;
}
}
obj* _l_s4_lean_s6_parser_s9_parsec__t_s23_parse__with__left__over(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s9_parsec__t_s23_parse__with__left__over_s6___rarg), 5, 0);
return x_4;
}
}
obj* _l_s4_lean_s6_parser_s9_parsec__t_s3_run_s4___at_s4_lean_s6_parser_s9_parsec__t_s23_parse__with__left__over_s9___spec__1_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
{
obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
lean::dec(x_5);
lean::dec(x_2);
lean::dec(x_1);
x_9 = lean::cnstr_get(x_0, 1);
lean::inc(x_9);
x_11 = lean::string_mk_iterator(x_4);
x_12 = lean::apply_1(x_3, x_11);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s9_parsec__t_s3_run_s6___rarg_s11___lambda__1), 2, 1);
lean::closure_set(x_13, 0, x_0);
x_14 = lean::apply_4(x_9, lean::box(0), lean::box(0), x_12, x_13);
return x_14;
}
}
obj* _l_s4_lean_s6_parser_s9_parsec__t_s3_run_s4___at_s4_lean_s6_parser_s9_parsec__t_s23_parse__with__left__over_s9___spec__1(obj* x_0) {
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s9_parsec__t_s3_run_s4___at_s4_lean_s6_parser_s9_parsec__t_s23_parse__with__left__over_s9___spec__1_s6___rarg), 6, 0);
return x_2;
}
}
obj* _l_s4_lean_s6_parser_s6_parsec_s5_parse_s6___rarg(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_3; 
x_3 = _l_s4_lean_s6_parser_s9_parsec__t_s3_run_s4___at_s4_lean_s6_parser_s6_parsec_s5_parse_s9___spec__1_s6___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* _l_s4_lean_s6_parser_s6_parsec_s5_parse(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s6_parsec_s5_parse_s6___rarg), 3, 0);
return x_4;
}
}
obj* _l_s4_lean_s6_parser_s9_parsec__t_s3_run_s4___at_s4_lean_s6_parser_s6_parsec_s5_parse_s9___spec__1_s6___rarg(obj* x_0, obj* x_1, obj* x_2) {
{
obj* x_4; obj* x_5; 
lean::dec(x_2);
x_4 = lean::string_mk_iterator(x_1);
x_5 = lean::apply_1(x_0, x_4);
if (lean::obj_tag(x_5) == 0)
{
obj* x_6; obj* x_9; 
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
lean::dec(x_5);
x_9 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_9, 0, x_6);
return x_9;
}
else
{
obj* x_10; obj* x_13; 
x_10 = lean::cnstr_get(x_5, 0);
lean::inc(x_10);
lean::dec(x_5);
x_13 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_13, 0, x_10);
return x_13;
}
}
}
obj* _l_s4_lean_s6_parser_s9_parsec__t_s3_run_s4___at_s4_lean_s6_parser_s6_parsec_s5_parse_s9___spec__1(obj* x_0, obj* x_1) {
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s9_parsec__t_s3_run_s4___at_s4_lean_s6_parser_s6_parsec_s5_parse_s9___spec__1_s6___rarg), 3, 0);
return x_4;
}
}
void _l_initialize__l_s4_init_s4_data_s10_to__string();
void _l_initialize__l_s4_init_s4_data_s6_string_s5_basic();
void _l_initialize__l_s4_init_s4_data_s4_list_s5_basic();
void _l_initialize__l_s4_init_s7_control_s6_except();
void _l_initialize__l_s4_init_s4_data_s4_repr();
void _l_initialize__l_s4_init_s4_lean_s4_name();
void _l_initialize__l_s4_init_s4_data_s5_dlist();
void _l_initialize__l_s4_init_s7_control_s11_monad__fail();
void _l_initialize__l_s4_init_s7_control_s11_combinators();
static bool _G_initialized = false;
void _l_initialize__l_s4_init_s4_lean_s6_parser_s6_parsec() {
 if (_G_initialized) return;
 _G_initialized = true;
 _l_initialize__l_s4_init_s4_data_s10_to__string();
 _l_initialize__l_s4_init_s4_data_s6_string_s5_basic();
 _l_initialize__l_s4_init_s4_data_s4_list_s5_basic();
 _l_initialize__l_s4_init_s7_control_s6_except();
 _l_initialize__l_s4_init_s4_data_s4_repr();
 _l_initialize__l_s4_init_s4_lean_s4_name();
 _l_initialize__l_s4_init_s4_data_s5_dlist();
 _l_initialize__l_s4_init_s7_control_s11_monad__fail();
 _l_initialize__l_s4_init_s7_control_s11_combinators();
 _l_s4_lean_s6_parser_s6_parsec_s8_position = _init__l_s4_lean_s6_parser_s6_parsec_s8_position();
 _l_s4_lean_s6_parser_s6_parsec_s8_expected_s10_to__string_s6___main_s11___closed__1 = _init__l_s4_lean_s6_parser_s6_parsec_s8_expected_s10_to__string_s6___main_s11___closed__1();
 _l_s4_lean_s6_parser_s6_parsec_s7_message_s4_text_s6___rarg_s11___closed__1 = _init__l_s4_lean_s6_parser_s6_parsec_s7_message_s4_text_s6___rarg_s11___closed__1();
 _l_s4_lean_s6_parser_s6_parsec_s7_message_s4_text_s6___rarg_s11___closed__2 = _init__l_s4_lean_s6_parser_s6_parsec_s7_message_s4_text_s6___rarg_s11___closed__2();
 _l_s4_lean_s6_parser_s6_parsec_s7_message_s4_text_s6___rarg_s11___closed__3 = _init__l_s4_lean_s6_parser_s6_parsec_s7_message_s4_text_s6___rarg_s11___closed__3();
 _l_s4_lean_s6_parser_s6_parsec_s7_message_s10_to__string_s6___rarg_s11___closed__1 = _init__l_s4_lean_s6_parser_s6_parsec_s7_message_s10_to__string_s6___rarg_s11___closed__1();
 _l_s4_lean_s6_parser_s6_parsec_s7_message_s10_to__string_s6___rarg_s11___closed__2 = _init__l_s4_lean_s6_parser_s6_parsec_s7_message_s10_to__string_s6___rarg_s11___closed__2();
 _l_s4_lean_s6_parser_s6_parsec_s7_message_s10_to__string_s6___rarg_s11___closed__3 = _init__l_s4_lean_s6_parser_s6_parsec_s7_message_s10_to__string_s6___rarg_s11___closed__3();
 _l_s4_lean_s6_parser_s6_parsec_s6_result_s7_mk__eps_s6___rarg_s11___closed__1 = _init__l_s4_lean_s6_parser_s6_parsec_s6_result_s7_mk__eps_s6___rarg_s11___closed__1();
 _l_s4_lean_s6_parser_s9_parsec__t = _init__l_s4_lean_s6_parser_s9_parsec__t();
 _l_s4_lean_s6_parser_s6_parsec = _init__l_s4_lean_s6_parser_s6_parsec();
 _l_s4_lean_s6_parser_s10_parsec_x27 = _init__l_s4_lean_s6_parser_s10_parsec_x27();
 _l_s4_lean_s6_parser_s9_parsec__t_s7_failure_s6___rarg_s11___closed__1 = _init__l_s4_lean_s6_parser_s9_parsec__t_s7_failure_s6___rarg_s11___closed__1();
 _l_s4_lean_s6_parser_s9_parsec__t_s11_monad__fail_s6___rarg_s11___closed__1 = _init__l_s4_lean_s6_parser_s9_parsec__t_s11_monad__fail_s6___rarg_s11___closed__1();
 _l_s4_lean_s6_parser_s17_monad__parsec_x27 = _init__l_s4_lean_s6_parser_s17_monad__parsec_x27();
 _l_s4_lean_s6_parser_s13_monad__parsec_s10_left__over_s6___rarg_s11___closed__1 = _init__l_s4_lean_s6_parser_s13_monad__parsec_s10_left__over_s6___rarg_s11___closed__1();
 _l_s4_lean_s6_parser_s13_monad__parsec_s9_remaining_s6___rarg_s11___closed__1 = _init__l_s4_lean_s6_parser_s13_monad__parsec_s9_remaining_s6___rarg_s11___closed__1();
 _l_s4_lean_s6_parser_s13_monad__parsec_s6_hidden_s6___rarg_s11___closed__1 = _init__l_s4_lean_s6_parser_s13_monad__parsec_s6_hidden_s6___rarg_s11___closed__1();
 _l_s4_lean_s6_parser_s13_monad__parsec_s3_try_s6___rarg_s11___closed__1 = _init__l_s4_lean_s6_parser_s13_monad__parsec_s3_try_s6___rarg_s11___closed__1();
 _l_s4_lean_s6_parser_s13_monad__parsec_s9_lookahead_s6___rarg_s11___closed__1 = _init__l_s4_lean_s6_parser_s13_monad__parsec_s9_lookahead_s6___rarg_s11___closed__1();
 _l_s4_lean_s6_parser_s13_monad__parsec_s10_eoi__error_s6___rarg_s11___closed__1 = _init__l_s4_lean_s6_parser_s13_monad__parsec_s10_eoi__error_s6___rarg_s11___closed__1();
 _l_s4_lean_s6_parser_s13_monad__parsec_s4_curr_s6___rarg_s11___closed__1 = _init__l_s4_lean_s6_parser_s13_monad__parsec_s4_curr_s6___rarg_s11___closed__1();
 _l_s4_lean_s6_parser_s13_monad__parsec_s15_take__while_x27_s4___at_s4_lean_s6_parser_s13_monad__parsec_s10_whitespace_s9___spec__1_s6___rarg_s11___closed__1 = _init__l_s4_lean_s6_parser_s13_monad__parsec_s15_take__while_x27_s4___at_s4_lean_s6_parser_s13_monad__parsec_s10_whitespace_s9___spec__1_s6___rarg_s11___closed__1();
 _l_s4_lean_s6_parser_s13_monad__parsec_s3_num_s6___rarg_s11___closed__1 = _init__l_s4_lean_s6_parser_s13_monad__parsec_s3_num_s6___rarg_s11___closed__1();
 _l_s4_lean_s6_parser_s13_monad__parsec_s6_ensure_s6___rarg_s11___lambda__1_s11___closed__1 = _init__l_s4_lean_s6_parser_s13_monad__parsec_s6_ensure_s6___rarg_s11___lambda__1_s11___closed__1();
 _l_s4_lean_s6_parser_s13_monad__parsec_s6_ensure_s6___rarg_s11___lambda__1_s11___closed__2 = _init__l_s4_lean_s6_parser_s13_monad__parsec_s6_ensure_s6___rarg_s11___lambda__1_s11___closed__2();
 _l_s4_lean_s6_parser_s13_monad__parsec_s3_pos_s6___rarg_s11___closed__1 = _init__l_s4_lean_s6_parser_s13_monad__parsec_s3_pos_s6___rarg_s11___closed__1();
 _l_s4_lean_s6_parser_s13_monad__parsec_s3_eoi_s6___rarg_s11___lambda__1_s11___closed__1 = _init__l_s4_lean_s6_parser_s13_monad__parsec_s3_eoi_s6___rarg_s11___lambda__1_s11___closed__1();
 _l_s4_lean_s6_parser_s13_monad__parsec_s8_sep__by1_s6___rarg_s11___closed__1 = _init__l_s4_lean_s6_parser_s13_monad__parsec_s8_sep__by1_s6___rarg_s11___closed__1();
 _l_s4_lean_s6_parser_s13_monad__parsec_s8_fix__aux_s6___main_s6___rarg_s11___closed__1 = _init__l_s4_lean_s6_parser_s13_monad__parsec_s8_fix__aux_s6___main_s6___rarg_s11___closed__1();
 _l_s4_list_s6_mfoldr_s6___main_s4___at_s4_lean_s6_parser_s13_monad__parsec_s14_longest__match_s9___spec__2_s6___rarg_s11___closed__1 = _init__l_s4_list_s6_mfoldr_s6___main_s4___at_s4_lean_s6_parser_s13_monad__parsec_s14_longest__match_s9___spec__2_s6___rarg_s11___closed__1();
}
