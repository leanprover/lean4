// Lean compiler output
// Module: init.lean.parser.identifier
// Imports: init.data.char.basic init.lean.parser.parsec
#include "runtime/object.h"
#include "runtime/apply.h"
#include "runtime/io.h"
#include "kernel/builtin.h"
typedef lean::object obj;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#endif
obj* _l_s9___private_2142412293__s18_mk__string__result_s6___rarg(obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_c__identifier_s9___spec__1_s6___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s10_foldl__aux_s6___main_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__10_s6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s2_ch_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__16_s6___rarg_s11___lambda__1_s7___boxed(obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__12(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s8_id__part(obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s10_foldl__aux_s6___main_s4___at_s4_lean_s6_parser_s10_identifier_s9___spec__5(obj*, obj*);
obj* _l_s4_lean_s6_parser_s8_id__part_s6___rarg(obj*, obj*, obj*);
obj* _l_s4_lean_s22_is__sub__script__alnum_s7___boxed(obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s17_id__part__default_s9___spec__2(obj*, obj*, obj*);
unsigned char _l_s4_lean_s13_is__id__first(unsigned);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s2_ch_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__11_s6___rarg_s11___lambda__1_s7___boxed(obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s2_ch_s4___at_s4_lean_s6_parser_s10_identifier_s9___spec__1_s6___rarg_s7___boxed(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s15_cpp__identifier(obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s4_curr_s6___rarg(obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s10_foldl__aux_s6___main_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__10(obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s2_ch_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__11_s6___rarg_s7___boxed(obj*, obj*, obj*);
obj* _l_s4_lean_s9_is__greek_s7___boxed(obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__18_s6___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s4_many_s6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_c__identifier_s9___spec__2(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s17_take__while__cont_s4___at_s4_lean_s6_parser_s13_c__identifier_s9___spec__3_s6___rarg_s7___boxed(obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s9_str__core_s4___at_s4_lean_s6_parser_s15_cpp__identifier_s9___spec__1(obj*, obj*);
obj* _l_s4_list_s5_foldl_s6___main_s4___at_s6_string_s4_join_s9___spec__1(obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_foldl_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__14_s6___rarg(obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_foldl_s4___at_s4_lean_s6_parser_s10_identifier_s9___spec__4_s6___rarg_s11___lambda__1(obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__18(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s10_identifier_s6___rarg_s11___closed__1;
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s17_take__while__cont_s4___at_s4_lean_s6_parser_s17_id__part__escaped_s9___spec__4(obj*, obj*, obj*);
obj* _l_s4_lean_s21_is__id__begin__escape_s7___boxed(obj*);
unsigned char _l_s4_lean_s21_is__id__begin__escape(unsigned);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s10_identifier_s9___spec__3(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s17_take__while__cont_s4___at_s4_lean_s6_parser_s13_c__identifier_s9___spec__3_s6___rarg_s11___lambda__1(obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s2_ch_s6___rarg(obj*, obj*, unsigned);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_foldl_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__14(obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_foldl_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__19(obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s17_take__while__cont_s4___at_s4_lean_s6_parser_s13_c__identifier_s9___spec__3_s6___rarg(obj*, unsigned);
obj* _l_s9___private_31565857__s16_take__while__aux_s6___main_s4___at_s4_lean_s6_parser_s17_id__part__escaped_s9___spec__5(obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s10_identifier_s9___spec__7_s6___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s2_ch_s4___at_s4_lean_s6_parser_s10_identifier_s9___spec__1_s6___rarg(obj*, obj*, unsigned);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s17_id__part__default_s9___spec__1(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_foldl_s4___at_s4_lean_s6_parser_s10_identifier_s9___spec__9(obj*, obj*);
obj* _l_s4_char_s11_quote__core(unsigned);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s2_ch_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__11(obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_c__identifier_s6___rarg_s11___lambda__1(obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s17_id__part__escaped_s9___spec__2(obj*, obj*, obj*);
obj* _l_s9___private_31565857__s16_take__while__aux_s6___main_s4___at_s4_lean_s6_parser_s17_id__part__default_s9___spec__4(obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_foldl_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__19_s6___rarg_s11___lambda__1(obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s10_foldl__aux_s6___main_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__15_s6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__17(obj*, obj*, obj*);
extern obj* _l_s5_mjoin_s6___rarg_s11___closed__1;
obj* _l_s4_lean_s6_parser_s17_id__part__escaped_s6___rarg(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_foldl_s4___at_s4_lean_s6_parser_s10_identifier_s9___spec__9_s6___rarg_s11___lambda__1(obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s2_ch_s4___at_s4_lean_s6_parser_s10_identifier_s9___spec__1(obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s2_ch_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__11_s6___rarg_s11___lambda__1(obj*, obj*, unsigned, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_foldl_s4___at_s4_lean_s6_parser_s10_identifier_s9___spec__4_s6___rarg(obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__17_s6___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__13_s6___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s15_cpp__identifier_s6___rarg_s11___lambda__2_s11___closed__3;
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s2_ch_s4___at_s4_lean_s6_parser_s10_identifier_s9___spec__1_s6___rarg_s11___lambda__1_s7___boxed(obj*, obj*, obj*, obj*, obj*);
unsigned char _l_s4_char_s12_is__alphanum(unsigned);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s17_take__while__cont_s4___at_s4_lean_s6_parser_s17_id__part__escaped_s9___spec__4_s6___rarg(obj*, unsigned);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s2_ch_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__16_s6___rarg_s7___boxed(obj*, obj*, obj*);
obj* _l_s4_lean_s13_is__id__first_s7___boxed(obj*);
unsigned char _l_s4_lean_s12_is__id__rest(unsigned);
obj* _l_s4_lean_s6_parser_s10_identifier_s6___rarg(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s17_take__while__cont_s4___at_s4_lean_s6_parser_s17_id__part__escaped_s9___spec__4_s6___rarg_s7___boxed(obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s10_identifier_s9___spec__8(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s17_take__while__cont_s4___at_s4_lean_s6_parser_s13_c__identifier_s9___spec__3(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s7_satisfy_s6___rarg_s11___lambda__1_s7___boxed(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s10_foldl__aux_s6___main_s4___at_s4_lean_s6_parser_s10_identifier_s9___spec__5_s6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s4_cond_s6___rarg_s11___lambda__1_s7___boxed(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s17_take__while__cont_s4___at_s4_lean_s6_parser_s17_id__part__default_s9___spec__3_s6___rarg_s7___boxed(obj*, obj*);
obj* _l_s9___private_31565857__s16_take__while__aux_s6___main_s4___at_s4_lean_s6_parser_s13_c__identifier_s9___spec__4(obj*);
obj* _l_s4_lean_s6_parser_s8_id__part_s6___rarg_s11___closed__1;
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s2_ch_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__11_s6___rarg(obj*, obj*, unsigned);
obj* _l_s4_lean_s6_parser_s15_cpp__identifier_s6___rarg_s11___closed__1;
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_foldl_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__14_s6___rarg_s11___lambda__1(obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__13(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s10_identifier_s9___spec__2(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__12_s6___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s17_take__while__cont_s4___at_s4_lean_s6_parser_s17_id__part__default_s9___spec__3(obj*, obj*, obj*);
unsigned char _l_s4_lean_s19_is__id__end__escape(unsigned);
unsigned char _l_s4_char_s9_is__alpha(unsigned);
obj* _l_s4_lean_s6_parser_s17_id__part__escaped(obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_foldl_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__19_s6___rarg(obj*, obj*, obj*, obj*);
extern obj* _l_s4_char_s9_has__repr_s11___closed__1;
obj* _l_s4_lean_s17_id__begin__escape;
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s17_id__part__escaped_s9___spec__2_s6___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s17_id__part__default_s6___rarg_s11___lambda__1(obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s10_foldl__aux_s6___main_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__15_s6___rarg_s11___lambda__1(obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_foldl_s4___at_s4_lean_s6_parser_s10_identifier_s9___spec__9_s6___rarg(obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s10_identifier_s9___spec__3_s6___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s15_cpp__identifier_s6___rarg_s11___lambda__2(obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s2_ch_s4___at_s4_lean_s6_parser_s10_identifier_s9___spec__6(obj*, obj*);
obj* _l_s4_lean_s6_parser_s10_identifier(obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s10_foldl__aux_s6___main_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__10_s6___rarg_s11___lambda__1(obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s9___private_31565857__s16_take__while__aux_s6___main_s4___at_s4_lean_s6_parser_s13_c__identifier_s9___spec__4_s6___rarg(obj*, obj*, obj*);
unsigned char _l_s6_string_s9_is__empty(obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s10_identifier_s9___spec__7(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s15_cpp__identifier_s6___rarg_s11___lambda__2_s11___closed__1;
obj* _l_s4_lean_s6_parser_s17_id__part__default_s6___rarg(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s2_ch_s4___at_s4_lean_s6_parser_s10_identifier_s9___spec__6_s6___rarg_s7___boxed(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_c__identifier_s9___spec__2_s6___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_c__identifier_s9___spec__1(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_c__identifier_s6___rarg_s11___closed__1;
extern obj* _l_s6_string_s4_join_s11___closed__1;
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s6___rarg_s11___lambda__1(obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s12_is__id__rest_s7___boxed(obj*);
obj* _l_s9___private_31565857__s16_take__while__aux_s6___main_s4___at_s4_lean_s6_parser_s17_id__part__escaped_s9___spec__5_s6___rarg(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s6_labels_s6___rarg_s11___lambda__1(obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s15_cpp__identifier_s6___rarg_s11___lambda__1(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s17_take__while__cont_s4___at_s4_lean_s6_parser_s17_id__part__default_s9___spec__3_s6___rarg_s11___lambda__1(obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s17_id__part__escaped_s9___spec__3_s6___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s2_ch_s4___at_s4_lean_s6_parser_s10_identifier_s9___spec__6_s6___rarg(obj*, obj*, unsigned);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s10_foldl__aux_s6___main_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__20_s6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_foldl_s4___at_s4_lean_s6_parser_s10_identifier_s9___spec__4(obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s9_str__core_s6___rarg_s11___lambda__1(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s12_take__while1_s4___at_s4_lean_s6_parser_s17_id__part__escaped_s9___spec__1_s6___rarg(obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_c__identifier_s6___rarg(obj*, obj*, obj*);
obj* _l_s9___private_31565857__s16_take__while__aux_s6___main_s4___at_s4_lean_s6_parser_s17_id__part__default_s9___spec__4_s6___rarg(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s15_cpp__identifier_s6___rarg(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_c__identifier(obj*, obj*);
obj* _l_s4_lean_s15_id__end__escape;
obj* _l_s4_lean_s19_is__id__end__escape_s7___boxed(obj*);
extern obj* _l_s4_lean_s6_parser_s13_monad__parsec_s10_left__over_s6___rarg_s11___closed__1;
unsigned char _l_s4_lean_s16_is__letter__like(unsigned);
extern obj* _l_s4_lean_s6_parser_s13_monad__parsec_s3_try_s6___rarg_s11___closed__1;
obj* _l_s4_lean_s6_parser_s15_cpp__identifier_s6___rarg_s11___lambda__2_s11___closed__2;
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s2_ch_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__16_s6___rarg(obj*, obj*, unsigned);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s10_foldl__aux_s6___main_s4___at_s4_lean_s6_parser_s10_identifier_s9___spec__5_s6___rarg_s11___lambda__1(obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s17_id__part__default_s9___spec__2_s6___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
extern obj* _l_s4_lean_s6_parser_s13_monad__parsec_s10_eoi__error_s6___rarg_s11___closed__1;
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s2_ch_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__16_s6___rarg_s11___lambda__1(obj*, obj*, unsigned, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s2_ch_s4___at_s4_lean_s6_parser_s10_identifier_s9___spec__6_s6___rarg_s11___lambda__1(obj*, obj*, unsigned, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s2_ch_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__16(obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s10_foldl__aux_s6___main_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__20_s6___rarg_s11___lambda__1(obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s16_is__letter__like_s7___boxed(obj*);
obj* _l_s4_lean_s6_parser_s17_id__part__default(obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s17_take__while__cont_s4___at_s4_lean_s6_parser_s17_id__part__escaped_s9___spec__4_s6___rarg_s11___lambda__1(obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s10_foldl__aux_s6___main_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__15(obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s2_ch_s4___at_s4_lean_s6_parser_s10_identifier_s9___spec__1_s6___rarg_s11___lambda__1(obj*, obj*, unsigned, obj*, obj*);
obj* _l_s4_lean_s6_parser_s10_identifier_s6___rarg_s11___lambda__1(obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s12_take__while1_s4___at_s4_lean_s6_parser_s17_id__part__escaped_s9___spec__1(obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s17_id__part__escaped_s9___spec__3(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s17_take__while__cont_s4___at_s4_lean_s6_parser_s17_id__part__default_s9___spec__3_s6___rarg(obj*, unsigned);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s10_identifier_s9___spec__8_s6___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
unsigned char _l_s4_lean_s9_is__greek(unsigned);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s2_ch_s4___at_s4_lean_s6_parser_s10_identifier_s9___spec__6_s6___rarg_s11___lambda__1_s7___boxed(obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s10_foldl__aux_s6___main_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__20(obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s12_take__while1_s4___at_s4_lean_s6_parser_s17_id__part__escaped_s9___spec__1_s6___rarg_s11___lambda__1(obj*, obj*, obj*, obj*);
obj* _l_s6_string_s5_quote(obj*);
obj* _l_s5_dlist_s9_singleton_s6___rarg(obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s9_str__core_s4___at_s4_lean_s6_parser_s15_cpp__identifier_s9___spec__1_s6___rarg(obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s10_identifier_s9___spec__2_s6___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
unsigned char _l_s4_lean_s22_is__sub__script__alnum(unsigned);
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s17_id__part__default_s9___spec__1_s6___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
unsigned char _l_s4_lean_s9_is__greek(unsigned x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::mk_nat_obj(913u);
x_2 = lean::box_uint32(x_0);
x_3 = lean::nat_dec_le(x_1, x_2);
lean::dec(x_1);
if (lean::obj_tag(x_3) == 0)
{
unsigned char x_7; 
lean::dec(x_2);
lean::dec(x_3);
x_7 = 0;
return x_7;
}
else
{
obj* x_9; obj* x_10; 
lean::dec(x_3);
x_9 = lean::mk_nat_obj(989u);
x_10 = lean::nat_dec_le(x_2, x_9);
lean::dec(x_9);
lean::dec(x_2);
if (lean::obj_tag(x_10) == 0)
{
unsigned char x_14; 
lean::dec(x_10);
x_14 = 0;
return x_14;
}
else
{
unsigned char x_16; 
lean::dec(x_10);
x_16 = 1;
return x_16;
}
}
}
}
obj* _l_s4_lean_s9_is__greek_s7___boxed(obj* x_0) {
_start:
{
unsigned x_1; unsigned char x_2; obj* x_3; 
x_1 = lean::unbox_uint32(x_0);
x_2 = _l_s4_lean_s9_is__greek(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
unsigned char _l_s4_lean_s16_is__letter__like(unsigned x_0) {
_start:
{
unsigned char x_1; unsigned char x_3; unsigned char x_5; unsigned char x_7; unsigned char x_9; unsigned char x_11; obj* x_13; obj* x_14; obj* x_15; 
x_13 = lean::mk_nat_obj(945u);
x_14 = lean::box_uint32(x_0);
x_15 = lean::nat_dec_le(x_13, x_14);
lean::dec(x_13);
if (lean::obj_tag(x_15) == 0)
{
unsigned char x_19; 
lean::dec(x_14);
lean::dec(x_15);
x_19 = 0;
x_11 = x_19;
goto lbl_12;
}
else
{
obj* x_21; obj* x_22; 
lean::dec(x_15);
x_21 = lean::mk_nat_obj(969u);
x_22 = lean::nat_dec_le(x_14, x_21);
lean::dec(x_21);
if (lean::obj_tag(x_22) == 0)
{
unsigned char x_26; 
lean::dec(x_14);
lean::dec(x_22);
x_26 = 0;
x_11 = x_26;
goto lbl_12;
}
else
{
obj* x_28; obj* x_29; 
lean::dec(x_22);
x_28 = lean::mk_nat_obj(955u);
x_29 = lean::nat_dec_eq(x_14, x_28);
lean::dec(x_28);
lean::dec(x_14);
if (lean::obj_tag(x_29) == 0)
{
unsigned char x_33; 
lean::dec(x_29);
x_33 = 1;
x_11 = x_33;
goto lbl_12;
}
else
{
unsigned char x_35; 
lean::dec(x_29);
x_35 = 0;
x_11 = x_35;
goto lbl_12;
}
}
}
lbl_2:
{
obj* x_36; obj* x_37; obj* x_38; 
x_36 = lean::mk_nat_obj(119964u);
x_37 = lean::box_uint32(x_0);
x_38 = lean::nat_dec_le(x_36, x_37);
lean::dec(x_36);
if (lean::obj_tag(x_38) == 0)
{
lean::dec(x_37);
lean::dec(x_38);
return x_1;
}
else
{
obj* x_43; obj* x_44; 
lean::dec(x_38);
x_43 = lean::mk_nat_obj(120223u);
x_44 = lean::nat_dec_le(x_37, x_43);
lean::dec(x_43);
lean::dec(x_37);
if (lean::obj_tag(x_44) == 0)
{
lean::dec(x_44);
return x_1;
}
else
{
unsigned char x_49; 
lean::dec(x_44);
x_49 = 1;
return x_49;
}
}
}
lbl_4:
{
obj* x_50; obj* x_51; obj* x_52; 
x_50 = lean::mk_nat_obj(8448u);
x_51 = lean::box_uint32(x_0);
x_52 = lean::nat_dec_le(x_50, x_51);
lean::dec(x_50);
if (lean::obj_tag(x_52) == 0)
{
lean::dec(x_51);
lean::dec(x_52);
if (x_3 == 0)
{
x_1 = x_3;
goto lbl_2;
}
else
{
return x_3;
}
}
else
{
obj* x_57; obj* x_58; 
lean::dec(x_52);
x_57 = lean::mk_nat_obj(8527u);
x_58 = lean::nat_dec_le(x_51, x_57);
lean::dec(x_57);
lean::dec(x_51);
if (lean::obj_tag(x_58) == 0)
{
lean::dec(x_58);
if (x_3 == 0)
{
x_1 = x_3;
goto lbl_2;
}
else
{
return x_3;
}
}
else
{
unsigned char x_63; 
lean::dec(x_58);
x_63 = 1;
return x_63;
}
}
}
lbl_6:
{
obj* x_64; obj* x_65; obj* x_66; 
x_64 = lean::mk_nat_obj(7936u);
x_65 = lean::box_uint32(x_0);
x_66 = lean::nat_dec_le(x_64, x_65);
lean::dec(x_64);
if (lean::obj_tag(x_66) == 0)
{
lean::dec(x_65);
lean::dec(x_66);
if (x_5 == 0)
{
x_3 = x_5;
goto lbl_4;
}
else
{
if (x_5 == 0)
{
x_1 = x_5;
goto lbl_2;
}
else
{
return x_5;
}
}
}
else
{
obj* x_71; obj* x_72; 
lean::dec(x_66);
x_71 = lean::mk_nat_obj(8190u);
x_72 = lean::nat_dec_le(x_65, x_71);
lean::dec(x_71);
lean::dec(x_65);
if (lean::obj_tag(x_72) == 0)
{
lean::dec(x_72);
if (x_5 == 0)
{
x_3 = x_5;
goto lbl_4;
}
else
{
if (x_5 == 0)
{
x_1 = x_5;
goto lbl_2;
}
else
{
return x_5;
}
}
}
else
{
unsigned char x_77; 
lean::dec(x_72);
x_77 = 1;
return x_77;
}
}
}
lbl_8:
{
obj* x_78; obj* x_79; obj* x_80; 
x_78 = lean::mk_nat_obj(970u);
x_79 = lean::box_uint32(x_0);
x_80 = lean::nat_dec_le(x_78, x_79);
lean::dec(x_78);
if (lean::obj_tag(x_80) == 0)
{
lean::dec(x_79);
lean::dec(x_80);
if (x_7 == 0)
{
x_5 = x_7;
goto lbl_6;
}
else
{
if (x_7 == 0)
{
x_3 = x_7;
goto lbl_4;
}
else
{
if (x_7 == 0)
{
x_1 = x_7;
goto lbl_2;
}
else
{
return x_7;
}
}
}
}
else
{
obj* x_85; obj* x_86; 
lean::dec(x_80);
x_85 = lean::mk_nat_obj(1019u);
x_86 = lean::nat_dec_le(x_79, x_85);
lean::dec(x_85);
lean::dec(x_79);
if (lean::obj_tag(x_86) == 0)
{
lean::dec(x_86);
if (x_7 == 0)
{
x_5 = x_7;
goto lbl_6;
}
else
{
if (x_7 == 0)
{
x_3 = x_7;
goto lbl_4;
}
else
{
if (x_7 == 0)
{
x_1 = x_7;
goto lbl_2;
}
else
{
return x_7;
}
}
}
}
else
{
unsigned char x_91; 
lean::dec(x_86);
x_91 = 1;
return x_91;
}
}
}
lbl_10:
{
if (x_9 == 0)
{
x_5 = x_9;
goto lbl_6;
}
else
{
if (x_9 == 0)
{
x_3 = x_9;
goto lbl_4;
}
else
{
if (x_9 == 0)
{
x_1 = x_9;
goto lbl_2;
}
else
{
return x_9;
}
}
}
}
lbl_12:
{
unsigned char x_92; unsigned char x_94; 
if (x_11 == 0)
{
obj* x_96; obj* x_97; obj* x_98; 
x_96 = lean::mk_nat_obj(913u);
x_97 = lean::box_uint32(x_0);
x_98 = lean::nat_dec_le(x_96, x_97);
lean::dec(x_96);
if (lean::obj_tag(x_98) == 0)
{
lean::dec(x_97);
lean::dec(x_98);
if (x_11 == 0)
{
x_92 = x_11;
goto lbl_93;
}
else
{
x_94 = x_11;
goto lbl_95;
}
}
else
{
obj* x_103; obj* x_104; 
lean::dec(x_98);
x_103 = lean::mk_nat_obj(937u);
x_104 = lean::nat_dec_le(x_97, x_103);
lean::dec(x_103);
lean::dec(x_97);
if (lean::obj_tag(x_104) == 0)
{
lean::dec(x_104);
if (x_11 == 0)
{
x_92 = x_11;
goto lbl_93;
}
else
{
x_94 = x_11;
goto lbl_95;
}
}
else
{
unsigned char x_109; 
lean::dec(x_104);
x_109 = 1;
x_94 = x_109;
goto lbl_95;
}
}
}
else
{
if (x_11 == 0)
{
x_7 = x_11;
goto lbl_8;
}
else
{
x_9 = x_11;
goto lbl_10;
}
}
lbl_93:
{
if (x_92 == 0)
{
if (x_92 == 0)
{
x_7 = x_92;
goto lbl_8;
}
else
{
x_9 = x_92;
goto lbl_10;
}
}
else
{
obj* x_110; obj* x_111; obj* x_112; 
x_110 = lean::mk_nat_obj(931u);
x_111 = lean::box_uint32(x_0);
x_112 = lean::nat_dec_eq(x_111, x_110);
lean::dec(x_110);
lean::dec(x_111);
if (lean::obj_tag(x_112) == 0)
{
lean::dec(x_112);
if (x_92 == 0)
{
x_7 = x_92;
goto lbl_8;
}
else
{
x_9 = x_92;
goto lbl_10;
}
}
else
{
lean::dec(x_112);
if (x_11 == 0)
{
x_7 = x_11;
goto lbl_8;
}
else
{
x_9 = x_11;
goto lbl_10;
}
}
}
}
lbl_95:
{
obj* x_117; obj* x_118; obj* x_119; 
x_117 = lean::mk_nat_obj(928u);
x_118 = lean::box_uint32(x_0);
x_119 = lean::nat_dec_eq(x_118, x_117);
lean::dec(x_117);
if (lean::obj_tag(x_119) == 0)
{
lean::dec(x_119);
if (x_94 == 0)
{
lean::dec(x_118);
if (x_94 == 0)
{
x_7 = x_94;
goto lbl_8;
}
else
{
x_9 = x_94;
goto lbl_10;
}
}
else
{
obj* x_123; obj* x_124; 
x_123 = lean::mk_nat_obj(931u);
x_124 = lean::nat_dec_eq(x_118, x_123);
lean::dec(x_123);
lean::dec(x_118);
if (lean::obj_tag(x_124) == 0)
{
lean::dec(x_124);
if (x_94 == 0)
{
x_7 = x_94;
goto lbl_8;
}
else
{
x_9 = x_94;
goto lbl_10;
}
}
else
{
lean::dec(x_124);
if (x_11 == 0)
{
x_7 = x_11;
goto lbl_8;
}
else
{
x_9 = x_11;
goto lbl_10;
}
}
}
}
else
{
lean::dec(x_118);
lean::dec(x_119);
if (x_11 == 0)
{
x_7 = x_11;
goto lbl_8;
}
else
{
x_9 = x_11;
goto lbl_10;
}
}
}
}
}
}
obj* _l_s4_lean_s16_is__letter__like_s7___boxed(obj* x_0) {
_start:
{
unsigned x_1; unsigned char x_2; obj* x_3; 
x_1 = lean::unbox_uint32(x_0);
x_2 = _l_s4_lean_s16_is__letter__like(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
unsigned char _l_s4_lean_s22_is__sub__script__alnum(unsigned x_0) {
_start:
{
unsigned char x_1; unsigned char x_3; obj* x_5; obj* x_6; obj* x_7; 
x_5 = lean::mk_nat_obj(8319u);
x_6 = lean::box_uint32(x_0);
x_7 = lean::nat_dec_le(x_5, x_6);
lean::dec(x_5);
if (lean::obj_tag(x_7) == 0)
{
unsigned char x_11; 
lean::dec(x_6);
lean::dec(x_7);
x_11 = 0;
x_3 = x_11;
goto lbl_4;
}
else
{
obj* x_13; obj* x_14; 
lean::dec(x_7);
x_13 = lean::mk_nat_obj(8329u);
x_14 = lean::nat_dec_le(x_6, x_13);
lean::dec(x_13);
lean::dec(x_6);
if (lean::obj_tag(x_14) == 0)
{
unsigned char x_18; 
lean::dec(x_14);
x_18 = 0;
x_3 = x_18;
goto lbl_4;
}
else
{
unsigned char x_20; 
lean::dec(x_14);
x_20 = 1;
return x_20;
}
}
lbl_2:
{
obj* x_21; obj* x_22; obj* x_23; 
x_21 = lean::mk_nat_obj(7522u);
x_22 = lean::box_uint32(x_0);
x_23 = lean::nat_dec_le(x_21, x_22);
lean::dec(x_21);
if (lean::obj_tag(x_23) == 0)
{
lean::dec(x_22);
lean::dec(x_23);
return x_1;
}
else
{
obj* x_28; obj* x_29; 
lean::dec(x_23);
x_28 = lean::mk_nat_obj(7530u);
x_29 = lean::nat_dec_le(x_22, x_28);
lean::dec(x_28);
lean::dec(x_22);
if (lean::obj_tag(x_29) == 0)
{
lean::dec(x_29);
return x_1;
}
else
{
unsigned char x_34; 
lean::dec(x_29);
x_34 = 1;
return x_34;
}
}
}
lbl_4:
{
obj* x_35; obj* x_36; obj* x_37; 
x_35 = lean::mk_nat_obj(8336u);
x_36 = lean::box_uint32(x_0);
x_37 = lean::nat_dec_le(x_35, x_36);
lean::dec(x_35);
if (lean::obj_tag(x_37) == 0)
{
lean::dec(x_36);
lean::dec(x_37);
if (x_3 == 0)
{
x_1 = x_3;
goto lbl_2;
}
else
{
return x_3;
}
}
else
{
obj* x_42; obj* x_43; 
lean::dec(x_37);
x_42 = lean::mk_nat_obj(8348u);
x_43 = lean::nat_dec_le(x_36, x_42);
lean::dec(x_42);
lean::dec(x_36);
if (lean::obj_tag(x_43) == 0)
{
lean::dec(x_43);
if (x_3 == 0)
{
x_1 = x_3;
goto lbl_2;
}
else
{
return x_3;
}
}
else
{
unsigned char x_48; 
lean::dec(x_43);
x_48 = 1;
return x_48;
}
}
}
}
}
obj* _l_s4_lean_s22_is__sub__script__alnum_s7___boxed(obj* x_0) {
_start:
{
unsigned x_1; unsigned char x_2; obj* x_3; 
x_1 = lean::unbox_uint32(x_0);
x_2 = _l_s4_lean_s22_is__sub__script__alnum(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
unsigned char _l_s4_lean_s13_is__id__first(unsigned x_0) {
_start:
{
unsigned char x_1; 
x_1 = _l_s4_char_s9_is__alpha(x_0);
if (x_1 == 0)
{
obj* x_2; obj* x_3; obj* x_4; unsigned x_6; 
x_2 = lean::mk_nat_obj(95u);
x_3 = lean::mk_nat_obj(55296u);
x_4 = lean::nat_dec_lt(x_2, x_3);
lean::dec(x_3);
if (lean::obj_tag(x_4) == 0)
{
obj* x_9; obj* x_10; 
lean::dec(x_4);
x_9 = lean::mk_nat_obj(57343u);
x_10 = lean::nat_dec_lt(x_9, x_2);
lean::dec(x_9);
if (lean::obj_tag(x_10) == 0)
{
obj* x_14; unsigned x_15; 
lean::dec(x_10);
lean::dec(x_2);
x_14 = lean::mk_nat_obj(0u);
x_15 = lean::unbox_uint32(x_14);
lean::dec(x_14);
x_6 = x_15;
goto lbl_7;
}
else
{
obj* x_18; obj* x_19; 
lean::dec(x_10);
x_18 = lean::mk_nat_obj(1114112u);
x_19 = lean::nat_dec_lt(x_2, x_18);
lean::dec(x_18);
if (lean::obj_tag(x_19) == 0)
{
obj* x_23; unsigned x_24; 
lean::dec(x_2);
lean::dec(x_19);
x_23 = lean::mk_nat_obj(0u);
x_24 = lean::unbox_uint32(x_23);
lean::dec(x_23);
x_6 = x_24;
goto lbl_7;
}
else
{
unsigned x_27; 
lean::dec(x_19);
x_27 = lean::unbox_uint32(x_2);
lean::dec(x_2);
x_6 = x_27;
goto lbl_7;
}
}
}
else
{
unsigned x_30; 
lean::dec(x_4);
x_30 = lean::unbox_uint32(x_2);
lean::dec(x_2);
x_6 = x_30;
goto lbl_7;
}
lbl_7:
{
obj* x_32; obj* x_33; obj* x_34; 
x_32 = lean::box_uint32(x_0);
x_33 = lean::box_uint32(x_6);
x_34 = lean::nat_dec_eq(x_32, x_33);
lean::dec(x_33);
lean::dec(x_32);
if (lean::obj_tag(x_34) == 0)
{
lean::dec(x_34);
if (x_1 == 0)
{
unsigned char x_38; 
x_38 = _l_s4_lean_s16_is__letter__like(x_0);
return x_38;
}
else
{
return x_1;
}
}
else
{
unsigned char x_40; 
lean::dec(x_34);
x_40 = 1;
return x_40;
}
}
}
else
{
if (x_1 == 0)
{
unsigned char x_41; 
x_41 = _l_s4_lean_s16_is__letter__like(x_0);
return x_41;
}
else
{
return x_1;
}
}
}
}
obj* _l_s4_lean_s13_is__id__first_s7___boxed(obj* x_0) {
_start:
{
unsigned x_1; unsigned char x_2; obj* x_3; 
x_1 = lean::unbox_uint32(x_0);
x_2 = _l_s4_lean_s13_is__id__first(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
unsigned char _l_s4_lean_s12_is__id__rest(unsigned x_0) {
_start:
{
unsigned char x_1; unsigned char x_3; 
x_3 = _l_s4_char_s12_is__alphanum(x_0);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; unsigned x_8; 
x_4 = lean::mk_nat_obj(95u);
x_5 = lean::mk_nat_obj(55296u);
x_6 = lean::nat_dec_lt(x_4, x_5);
lean::dec(x_5);
if (lean::obj_tag(x_6) == 0)
{
obj* x_11; obj* x_12; 
lean::dec(x_6);
x_11 = lean::mk_nat_obj(57343u);
x_12 = lean::nat_dec_lt(x_11, x_4);
lean::dec(x_11);
if (lean::obj_tag(x_12) == 0)
{
obj* x_16; unsigned x_17; 
lean::dec(x_12);
lean::dec(x_4);
x_16 = lean::mk_nat_obj(0u);
x_17 = lean::unbox_uint32(x_16);
lean::dec(x_16);
x_8 = x_17;
goto lbl_9;
}
else
{
obj* x_20; obj* x_21; 
lean::dec(x_12);
x_20 = lean::mk_nat_obj(1114112u);
x_21 = lean::nat_dec_lt(x_4, x_20);
lean::dec(x_20);
if (lean::obj_tag(x_21) == 0)
{
obj* x_25; unsigned x_26; 
lean::dec(x_4);
lean::dec(x_21);
x_25 = lean::mk_nat_obj(0u);
x_26 = lean::unbox_uint32(x_25);
lean::dec(x_25);
x_8 = x_26;
goto lbl_9;
}
else
{
unsigned x_29; 
lean::dec(x_21);
x_29 = lean::unbox_uint32(x_4);
lean::dec(x_4);
x_8 = x_29;
goto lbl_9;
}
}
}
else
{
unsigned x_32; 
lean::dec(x_6);
x_32 = lean::unbox_uint32(x_4);
lean::dec(x_4);
x_8 = x_32;
goto lbl_9;
}
lbl_9:
{
obj* x_34; obj* x_35; obj* x_36; 
x_34 = lean::box_uint32(x_0);
x_35 = lean::box_uint32(x_8);
x_36 = lean::nat_dec_eq(x_34, x_35);
lean::dec(x_35);
lean::dec(x_34);
if (lean::obj_tag(x_36) == 0)
{
lean::dec(x_36);
if (x_3 == 0)
{
x_1 = x_3;
goto lbl_2;
}
else
{
if (x_3 == 0)
{
unsigned char x_40; 
x_40 = _l_s4_lean_s16_is__letter__like(x_0);
if (x_40 == 0)
{
unsigned char x_41; 
x_41 = _l_s4_lean_s22_is__sub__script__alnum(x_0);
return x_41;
}
else
{
return x_40;
}
}
else
{
if (x_3 == 0)
{
unsigned char x_42; 
x_42 = _l_s4_lean_s22_is__sub__script__alnum(x_0);
return x_42;
}
else
{
return x_3;
}
}
}
}
else
{
unsigned char x_44; 
lean::dec(x_36);
x_44 = 1;
return x_44;
}
}
}
else
{
if (x_3 == 0)
{
x_1 = x_3;
goto lbl_2;
}
else
{
if (x_3 == 0)
{
unsigned char x_45; 
x_45 = _l_s4_lean_s16_is__letter__like(x_0);
if (x_45 == 0)
{
unsigned char x_46; 
x_46 = _l_s4_lean_s22_is__sub__script__alnum(x_0);
return x_46;
}
else
{
return x_45;
}
}
else
{
if (x_3 == 0)
{
unsigned char x_47; 
x_47 = _l_s4_lean_s22_is__sub__script__alnum(x_0);
return x_47;
}
else
{
return x_3;
}
}
}
}
lbl_2:
{
obj* x_48; obj* x_49; obj* x_50; unsigned x_52; 
x_48 = lean::mk_nat_obj(39u);
x_49 = lean::mk_nat_obj(55296u);
x_50 = lean::nat_dec_lt(x_48, x_49);
lean::dec(x_49);
if (lean::obj_tag(x_50) == 0)
{
obj* x_55; obj* x_56; 
lean::dec(x_50);
x_55 = lean::mk_nat_obj(57343u);
x_56 = lean::nat_dec_lt(x_55, x_48);
lean::dec(x_55);
if (lean::obj_tag(x_56) == 0)
{
obj* x_60; unsigned x_61; 
lean::dec(x_48);
lean::dec(x_56);
x_60 = lean::mk_nat_obj(0u);
x_61 = lean::unbox_uint32(x_60);
lean::dec(x_60);
x_52 = x_61;
goto lbl_53;
}
else
{
obj* x_64; obj* x_65; 
lean::dec(x_56);
x_64 = lean::mk_nat_obj(1114112u);
x_65 = lean::nat_dec_lt(x_48, x_64);
lean::dec(x_64);
if (lean::obj_tag(x_65) == 0)
{
obj* x_69; unsigned x_70; 
lean::dec(x_48);
lean::dec(x_65);
x_69 = lean::mk_nat_obj(0u);
x_70 = lean::unbox_uint32(x_69);
lean::dec(x_69);
x_52 = x_70;
goto lbl_53;
}
else
{
unsigned x_73; 
lean::dec(x_65);
x_73 = lean::unbox_uint32(x_48);
lean::dec(x_48);
x_52 = x_73;
goto lbl_53;
}
}
}
else
{
unsigned x_76; 
lean::dec(x_50);
x_76 = lean::unbox_uint32(x_48);
lean::dec(x_48);
x_52 = x_76;
goto lbl_53;
}
lbl_53:
{
obj* x_78; obj* x_79; obj* x_80; 
x_78 = lean::box_uint32(x_0);
x_79 = lean::box_uint32(x_52);
x_80 = lean::nat_dec_eq(x_78, x_79);
lean::dec(x_79);
lean::dec(x_78);
if (lean::obj_tag(x_80) == 0)
{
lean::dec(x_80);
if (x_1 == 0)
{
unsigned char x_84; 
x_84 = _l_s4_lean_s16_is__letter__like(x_0);
if (x_84 == 0)
{
unsigned char x_85; 
x_85 = _l_s4_lean_s22_is__sub__script__alnum(x_0);
return x_85;
}
else
{
return x_84;
}
}
else
{
if (x_1 == 0)
{
unsigned char x_86; 
x_86 = _l_s4_lean_s22_is__sub__script__alnum(x_0);
return x_86;
}
else
{
return x_1;
}
}
}
else
{
unsigned char x_88; 
lean::dec(x_80);
x_88 = 1;
return x_88;
}
}
}
}
}
obj* _l_s4_lean_s12_is__id__rest_s7___boxed(obj* x_0) {
_start:
{
unsigned x_1; unsigned char x_2; obj* x_3; 
x_1 = lean::unbox_uint32(x_0);
x_2 = _l_s4_lean_s12_is__id__rest(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* _init__l_s4_lean_s17_id__begin__escape() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_nat_obj(171u);
x_1 = lean::mk_nat_obj(55296u);
x_2 = lean::nat_dec_lt(x_0, x_1);
lean::dec(x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_5; obj* x_6; 
lean::dec(x_2);
x_5 = lean::mk_nat_obj(57343u);
x_6 = lean::nat_dec_lt(x_5, x_0);
lean::dec(x_5);
if (lean::obj_tag(x_6) == 0)
{
obj* x_10; 
lean::dec(x_6);
lean::dec(x_0);
x_10 = lean::mk_nat_obj(0u);
return x_10;
}
else
{
obj* x_12; obj* x_13; 
lean::dec(x_6);
x_12 = lean::mk_nat_obj(1114112u);
x_13 = lean::nat_dec_lt(x_0, x_12);
lean::dec(x_12);
lean::dec(x_0);
if (lean::obj_tag(x_13) == 0)
{
obj* x_17; 
lean::dec(x_13);
x_17 = lean::mk_nat_obj(0u);
return x_17;
}
else
{
obj* x_19; 
lean::dec(x_13);
x_19 = lean::mk_nat_obj(171u);
return x_19;
}
}
}
else
{
obj* x_22; 
lean::dec(x_0);
lean::dec(x_2);
x_22 = lean::mk_nat_obj(171u);
return x_22;
}
}
}
obj* _init__l_s4_lean_s15_id__end__escape() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_nat_obj(187u);
x_1 = lean::mk_nat_obj(55296u);
x_2 = lean::nat_dec_lt(x_0, x_1);
lean::dec(x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_5; obj* x_6; 
lean::dec(x_2);
x_5 = lean::mk_nat_obj(57343u);
x_6 = lean::nat_dec_lt(x_5, x_0);
lean::dec(x_5);
if (lean::obj_tag(x_6) == 0)
{
obj* x_10; 
lean::dec(x_6);
lean::dec(x_0);
x_10 = lean::mk_nat_obj(0u);
return x_10;
}
else
{
obj* x_12; obj* x_13; 
lean::dec(x_6);
x_12 = lean::mk_nat_obj(1114112u);
x_13 = lean::nat_dec_lt(x_0, x_12);
lean::dec(x_12);
lean::dec(x_0);
if (lean::obj_tag(x_13) == 0)
{
obj* x_17; 
lean::dec(x_13);
x_17 = lean::mk_nat_obj(0u);
return x_17;
}
else
{
obj* x_19; 
lean::dec(x_13);
x_19 = lean::mk_nat_obj(187u);
return x_19;
}
}
}
else
{
obj* x_22; 
lean::dec(x_0);
lean::dec(x_2);
x_22 = lean::mk_nat_obj(187u);
return x_22;
}
}
}
unsigned char _l_s4_lean_s21_is__id__begin__escape(unsigned x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = _l_s4_lean_s17_id__begin__escape;
x_2 = lean::box_uint32(x_0);
x_3 = lean::nat_dec_eq(x_2, x_1);
lean::dec(x_2);
if (lean::obj_tag(x_3) == 0)
{
unsigned char x_6; 
lean::dec(x_3);
x_6 = 0;
return x_6;
}
else
{
unsigned char x_8; 
lean::dec(x_3);
x_8 = 1;
return x_8;
}
}
}
obj* _l_s4_lean_s21_is__id__begin__escape_s7___boxed(obj* x_0) {
_start:
{
unsigned x_1; unsigned char x_2; obj* x_3; 
x_1 = lean::unbox_uint32(x_0);
x_2 = _l_s4_lean_s21_is__id__begin__escape(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
unsigned char _l_s4_lean_s19_is__id__end__escape(unsigned x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = _l_s4_lean_s15_id__end__escape;
x_2 = lean::box_uint32(x_0);
x_3 = lean::nat_dec_eq(x_2, x_1);
lean::dec(x_2);
if (lean::obj_tag(x_3) == 0)
{
unsigned char x_6; 
lean::dec(x_3);
x_6 = 0;
return x_6;
}
else
{
unsigned char x_8; 
lean::dec(x_3);
x_8 = 1;
return x_8;
}
}
}
obj* _l_s4_lean_s19_is__id__end__escape_s7___boxed(obj* x_0) {
_start:
{
unsigned x_1; unsigned char x_2; obj* x_3; 
x_1 = lean::unbox_uint32(x_0);
x_2 = _l_s4_lean_s19_is__id__end__escape(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* _l_s4_lean_s6_parser_s17_id__part__default_s6___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_6; obj* x_8; obj* x_11; obj* x_13; obj* x_15; obj* x_16; obj* x_17; 
lean::dec(x_2);
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
x_8 = _l_s4_lean_s6_parser_s13_monad__parsec_s10_left__over_s6___rarg_s11___closed__1;
lean::inc(x_8);
lean::inc(x_6);
x_11 = lean::apply_2(x_6, lean::box(0), x_8);
lean::inc(x_1);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s17_id__part__default_s6___rarg_s11___lambda__1), 4, 3);
lean::closure_set(x_13, 0, x_0);
lean::closure_set(x_13, 1, x_1);
lean::closure_set(x_13, 2, x_6);
lean::inc(x_4);
x_15 = lean::apply_4(x_4, lean::box(0), lean::box(0), x_11, x_13);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s17_take__while__cont_s4___at_s4_lean_s6_parser_s17_id__part__default_s9___spec__3_s6___rarg_s7___boxed), 2, 1);
lean::closure_set(x_16, 0, x_1);
x_17 = lean::apply_4(x_4, lean::box(0), lean::box(0), x_15, x_16);
return x_17;
}
}
obj* _l_s4_lean_s6_parser_s17_id__part__default_s6___rarg_s11___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
unsigned char x_5; 
lean::dec(x_0);
x_5 = lean::string_iterator_has_next(x_3);
if (x_5 == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_14; 
lean::dec(x_2);
lean::dec(x_3);
x_8 = lean::alloc_cnstr(0, 0, 0);
;
x_9 = _l_s4_lean_s6_parser_s13_monad__parsec_s10_eoi__error_s6___rarg_s11___closed__1;
x_10 = _l_s5_mjoin_s6___rarg_s11___closed__1;
lean::inc(x_8);
lean::inc(x_10);
lean::inc(x_9);
x_14 = _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s17_id__part__default_s9___spec__1_s6___rarg(x_1, lean::box(0), x_9, x_10, x_8, x_8);
return x_14;
}
else
{
unsigned x_15; unsigned char x_16; 
x_15 = lean::string_iterator_curr(x_3);
x_16 = _l_s4_lean_s13_is__id__first(x_15);
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
x_25 = lean::alloc_cnstr(0, 0, 0);
;
x_26 = _l_s5_mjoin_s6___rarg_s11___closed__1;
lean::inc(x_25);
lean::inc(x_26);
x_29 = _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s17_id__part__default_s9___spec__2_s6___rarg(x_1, lean::box(0), x_24, x_26, x_25, x_25);
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
obj* _l_s4_lean_s6_parser_s17_id__part__default(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s17_id__part__default_s6___rarg), 3, 0);
return x_4;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s17_id__part__default_s9___spec__1_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
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
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s17_id__part__default_s9___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s17_id__part__default_s9___spec__1_s6___rarg), 6, 0);
return x_6;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s17_id__part__default_s9___spec__2_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
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
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s17_id__part__default_s9___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s17_id__part__default_s9___spec__2_s6___rarg), 6, 0);
return x_6;
}
}
obj* _l_s9___private_31565857__s16_take__while__aux_s6___main_s4___at_s4_lean_s6_parser_s17_id__part__default_s9___spec__4_s6___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
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
x_11 = _l_s4_lean_s12_is__id__rest(x_10);
if (x_11 == 0)
{
obj* x_13; 
lean::dec(x_0);
x_13 = _l_s9___private_2142412293__s18_mk__string__result_s6___rarg(x_1, x_2);
return x_13;
}
else
{
obj* x_14; obj* x_15; obj* x_18; obj* x_19; 
x_14 = lean::mk_nat_obj(1u);
x_15 = lean::nat_sub(x_0, x_14);
lean::dec(x_14);
lean::dec(x_0);
x_18 = lean::string_push(x_1, x_10);
x_19 = lean::string_iterator_next(x_2);
x_0 = x_15;
x_1 = x_18;
x_2 = x_19;
goto _start;
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
obj* _l_s9___private_31565857__s16_take__while__aux_s6___main_s4___at_s4_lean_s6_parser_s17_id__part__default_s9___spec__4(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9___private_31565857__s16_take__while__aux_s6___main_s4___at_s4_lean_s6_parser_s17_id__part__default_s9___spec__4_s6___rarg), 3, 0);
return x_2;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s17_take__while__cont_s4___at_s4_lean_s6_parser_s17_id__part__default_s9___spec__3_s6___rarg(obj* x_0, unsigned x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_5; obj* x_8; obj* x_9; 
x_2 = _l_s6_string_s4_join_s11___closed__1;
lean::inc(x_2);
x_4 = lean::string_push(x_2, x_1);
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
lean::dec(x_0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s17_take__while__cont_s4___at_s4_lean_s6_parser_s17_id__part__default_s9___spec__3_s6___rarg_s11___lambda__1), 2, 1);
lean::closure_set(x_8, 0, x_4);
x_9 = lean::apply_2(x_5, lean::box(0), x_8);
return x_9;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s17_take__while__cont_s4___at_s4_lean_s6_parser_s17_id__part__default_s9___spec__3_s6___rarg_s11___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::string_iterator_remaining(x_1);
x_3 = _l_s9___private_31565857__s16_take__while__aux_s6___main_s4___at_s4_lean_s6_parser_s17_id__part__default_s9___spec__4_s6___rarg(x_2, x_0, x_1);
return x_3;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s17_take__while__cont_s4___at_s4_lean_s6_parser_s17_id__part__default_s9___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s17_take__while__cont_s4___at_s4_lean_s6_parser_s17_id__part__default_s9___spec__3_s6___rarg_s7___boxed), 2, 0);
return x_6;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s17_take__while__cont_s4___at_s4_lean_s6_parser_s17_id__part__default_s9___spec__3_s6___rarg_s7___boxed(obj* x_0, obj* x_1) {
_start:
{
unsigned x_2; obj* x_3; 
x_2 = lean::unbox_uint32(x_1);
x_3 = _l_s4_lean_s6_parser_s13_monad__parsec_s17_take__while__cont_s4___at_s4_lean_s6_parser_s17_id__part__default_s9___spec__3_s6___rarg(x_0, x_2);
return x_3;
}
}
obj* _l_s4_lean_s6_parser_s17_id__part__escaped_s6___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_6; obj* x_8; obj* x_11; unsigned x_12; obj* x_15; obj* x_18; obj* x_19; obj* x_20; unsigned x_21; obj* x_22; obj* x_23; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
lean::dec(x_2);
x_6 = lean::cnstr_get(x_3, 3);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_3, 4);
lean::inc(x_8);
lean::dec(x_3);
x_11 = _l_s4_lean_s17_id__begin__escape;
x_12 = lean::unbox_uint32(x_11);
lean::inc(x_1);
lean::inc(x_0);
x_15 = _l_s4_lean_s6_parser_s13_monad__parsec_s2_ch_s6___rarg(x_0, x_1, x_12);
lean::inc(x_1);
lean::inc(x_0);
x_18 = _l_s4_lean_s6_parser_s13_monad__parsec_s12_take__while1_s4___at_s4_lean_s6_parser_s17_id__part__escaped_s9___spec__1_s6___rarg(x_0, x_1);
x_19 = lean::apply_4(x_8, lean::box(0), lean::box(0), x_15, x_18);
x_20 = _l_s4_lean_s15_id__end__escape;
x_21 = lean::unbox_uint32(x_20);
x_22 = _l_s4_lean_s6_parser_s13_monad__parsec_s2_ch_s6___rarg(x_0, x_1, x_21);
x_23 = lean::apply_4(x_6, lean::box(0), lean::box(0), x_19, x_22);
return x_23;
}
}
obj* _l_s4_lean_s6_parser_s17_id__part__escaped(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s17_id__part__escaped_s6___rarg), 3, 0);
return x_4;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s17_id__part__escaped_s9___spec__2_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
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
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s17_id__part__escaped_s9___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s17_id__part__escaped_s9___spec__2_s6___rarg), 6, 0);
return x_6;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s17_id__part__escaped_s9___spec__3_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
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
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s17_id__part__escaped_s9___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s17_id__part__escaped_s9___spec__3_s6___rarg), 6, 0);
return x_6;
}
}
obj* _l_s9___private_31565857__s16_take__while__aux_s6___main_s4___at_s4_lean_s6_parser_s17_id__part__escaped_s9___spec__5_s6___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
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
x_11 = _l_s4_lean_s19_is__id__end__escape(x_10);
if (x_11 == 0)
{
obj* x_12; obj* x_13; obj* x_16; obj* x_17; 
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_sub(x_0, x_12);
lean::dec(x_12);
lean::dec(x_0);
x_16 = lean::string_push(x_1, x_10);
x_17 = lean::string_iterator_next(x_2);
x_0 = x_13;
x_1 = x_16;
x_2 = x_17;
goto _start;
}
else
{
obj* x_20; 
lean::dec(x_0);
x_20 = _l_s9___private_2142412293__s18_mk__string__result_s6___rarg(x_1, x_2);
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
obj* _l_s9___private_31565857__s16_take__while__aux_s6___main_s4___at_s4_lean_s6_parser_s17_id__part__escaped_s9___spec__5(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9___private_31565857__s16_take__while__aux_s6___main_s4___at_s4_lean_s6_parser_s17_id__part__escaped_s9___spec__5_s6___rarg), 3, 0);
return x_2;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s17_take__while__cont_s4___at_s4_lean_s6_parser_s17_id__part__escaped_s9___spec__4_s6___rarg(obj* x_0, unsigned x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_5; obj* x_8; obj* x_9; 
x_2 = _l_s6_string_s4_join_s11___closed__1;
lean::inc(x_2);
x_4 = lean::string_push(x_2, x_1);
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
lean::dec(x_0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s17_take__while__cont_s4___at_s4_lean_s6_parser_s17_id__part__escaped_s9___spec__4_s6___rarg_s11___lambda__1), 2, 1);
lean::closure_set(x_8, 0, x_4);
x_9 = lean::apply_2(x_5, lean::box(0), x_8);
return x_9;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s17_take__while__cont_s4___at_s4_lean_s6_parser_s17_id__part__escaped_s9___spec__4_s6___rarg_s11___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::string_iterator_remaining(x_1);
x_3 = _l_s9___private_31565857__s16_take__while__aux_s6___main_s4___at_s4_lean_s6_parser_s17_id__part__escaped_s9___spec__5_s6___rarg(x_2, x_0, x_1);
return x_3;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s17_take__while__cont_s4___at_s4_lean_s6_parser_s17_id__part__escaped_s9___spec__4(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s17_take__while__cont_s4___at_s4_lean_s6_parser_s17_id__part__escaped_s9___spec__4_s6___rarg_s7___boxed), 2, 0);
return x_6;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s12_take__while1_s4___at_s4_lean_s6_parser_s17_id__part__escaped_s9___spec__1_s6___rarg(obj* x_0, obj* x_1) {
_start:
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
x_11 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s12_take__while1_s4___at_s4_lean_s6_parser_s17_id__part__escaped_s9___spec__1_s6___rarg_s11___lambda__1), 4, 3);
lean::closure_set(x_11, 0, x_0);
lean::closure_set(x_11, 1, x_1);
lean::closure_set(x_11, 2, x_4);
lean::inc(x_2);
x_13 = lean::apply_4(x_2, lean::box(0), lean::box(0), x_9, x_11);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s17_take__while__cont_s4___at_s4_lean_s6_parser_s17_id__part__escaped_s9___spec__4_s6___rarg_s7___boxed), 2, 1);
lean::closure_set(x_14, 0, x_1);
x_15 = lean::apply_4(x_2, lean::box(0), lean::box(0), x_13, x_14);
return x_15;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s12_take__while1_s4___at_s4_lean_s6_parser_s17_id__part__escaped_s9___spec__1_s6___rarg_s11___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
unsigned char x_5; 
lean::dec(x_0);
x_5 = lean::string_iterator_has_next(x_3);
if (x_5 == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_14; 
lean::dec(x_2);
lean::dec(x_3);
x_8 = lean::alloc_cnstr(0, 0, 0);
;
x_9 = _l_s4_lean_s6_parser_s13_monad__parsec_s10_eoi__error_s6___rarg_s11___closed__1;
x_10 = _l_s5_mjoin_s6___rarg_s11___closed__1;
lean::inc(x_8);
lean::inc(x_10);
lean::inc(x_9);
x_14 = _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s17_id__part__escaped_s9___spec__2_s6___rarg(x_1, lean::box(0), x_9, x_10, x_8, x_8);
return x_14;
}
else
{
unsigned x_15; unsigned char x_16; 
x_15 = lean::string_iterator_curr(x_3);
x_16 = _l_s4_lean_s19_is__id__end__escape(x_15);
if (x_16 == 0)
{
obj* x_18; obj* x_19; obj* x_20; 
lean::dec(x_1);
x_18 = lean::box_uint32(x_15);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s7_satisfy_s6___rarg_s11___lambda__1_s7___boxed), 3, 2);
lean::closure_set(x_19, 0, x_3);
lean::closure_set(x_19, 1, x_18);
x_20 = lean::apply_2(x_2, lean::box(0), x_19);
return x_20;
}
else
{
obj* x_23; obj* x_24; obj* x_26; obj* x_28; obj* x_29; obj* x_30; obj* x_33; 
lean::dec(x_2);
lean::dec(x_3);
x_23 = _l_s4_char_s11_quote__core(x_15);
x_24 = _l_s4_char_s9_has__repr_s11___closed__1;
lean::inc(x_24);
x_26 = lean::string_append(x_24, x_23);
lean::dec(x_23);
x_28 = lean::string_append(x_26, x_24);
x_29 = lean::alloc_cnstr(0, 0, 0);
;
x_30 = _l_s5_mjoin_s6___rarg_s11___closed__1;
lean::inc(x_29);
lean::inc(x_30);
x_33 = _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s17_id__part__escaped_s9___spec__3_s6___rarg(x_1, lean::box(0), x_28, x_30, x_29, x_29);
return x_33;
}
}
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s12_take__while1_s4___at_s4_lean_s6_parser_s17_id__part__escaped_s9___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s12_take__while1_s4___at_s4_lean_s6_parser_s17_id__part__escaped_s9___spec__1_s6___rarg), 2, 0);
return x_4;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s17_take__while__cont_s4___at_s4_lean_s6_parser_s17_id__part__escaped_s9___spec__4_s6___rarg_s7___boxed(obj* x_0, obj* x_1) {
_start:
{
unsigned x_2; obj* x_3; 
x_2 = lean::unbox_uint32(x_1);
x_3 = _l_s4_lean_s6_parser_s13_monad__parsec_s17_take__while__cont_s4___at_s4_lean_s6_parser_s17_id__part__escaped_s9___spec__4_s6___rarg(x_0, x_2);
return x_3;
}
}
obj* _l_s4_lean_s6_parser_s8_id__part_s6___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; obj* x_9; obj* x_10; obj* x_12; obj* x_14; obj* x_17; obj* x_20; obj* x_21; obj* x_23; obj* x_24; obj* x_25; 
lean::inc(x_2);
lean::inc(x_1);
lean::inc(x_0);
x_6 = _l_s4_lean_s6_parser_s17_id__part__escaped_s6___rarg(x_0, x_1, x_2);
lean::inc(x_1);
lean::inc(x_0);
x_9 = _l_s4_lean_s6_parser_s17_id__part__default_s6___rarg(x_0, x_1, x_2);
x_10 = lean::cnstr_get(x_0, 1);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_0, 0);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_12, 0);
lean::inc(x_14);
lean::dec(x_12);
x_17 = lean::cnstr_get(x_14, 0);
lean::inc(x_17);
lean::dec(x_14);
x_20 = _l_s4_lean_s6_parser_s13_monad__parsec_s4_curr_s6___rarg(x_0, x_1);
x_21 = _l_s4_lean_s6_parser_s8_id__part_s6___rarg_s11___closed__1;
lean::inc(x_21);
x_23 = lean::apply_4(x_17, lean::box(0), lean::box(0), x_21, x_20);
x_24 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s4_cond_s6___rarg_s11___lambda__1_s7___boxed), 3, 2);
lean::closure_set(x_24, 0, x_9);
lean::closure_set(x_24, 1, x_6);
x_25 = lean::apply_4(x_10, lean::box(0), lean::box(0), x_23, x_24);
return x_25;
}
}
obj* _init__l_s4_lean_s6_parser_s8_id__part_s6___rarg_s11___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s21_is__id__begin__escape_s7___boxed), 1, 0);
return x_0;
}
}
obj* _l_s4_lean_s6_parser_s8_id__part(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s8_id__part_s6___rarg), 3, 0);
return x_4;
}
}
obj* _l_s4_lean_s6_parser_s10_identifier_s6___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_8; obj* x_10; obj* x_11; obj* x_12; obj* x_15; obj* x_18; obj* x_19; obj* x_21; 
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::inc(x_2);
lean::inc(x_1);
lean::inc(x_0);
x_8 = _l_s4_lean_s6_parser_s8_id__part_s6___rarg(x_0, x_1, x_2);
lean::inc(x_1);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s10_identifier_s6___rarg_s11___lambda__1), 4, 3);
lean::closure_set(x_10, 0, x_0);
lean::closure_set(x_10, 1, x_1);
lean::closure_set(x_10, 2, x_2);
x_11 = lean::apply_4(x_3, lean::box(0), lean::box(0), x_8, x_10);
x_12 = lean::cnstr_get(x_1, 1);
lean::inc(x_12);
lean::dec(x_1);
x_15 = _l_s4_lean_s6_parser_s13_monad__parsec_s3_try_s6___rarg_s11___closed__1;
lean::inc(x_15);
lean::inc(x_12);
x_18 = lean::apply_3(x_12, lean::box(0), x_15, x_11);
x_19 = _l_s4_lean_s6_parser_s10_identifier_s6___rarg_s11___closed__1;
lean::inc(x_19);
x_21 = lean::apply_3(x_12, lean::box(0), x_19, x_18);
return x_21;
}
}
obj* _init__l_s4_lean_s6_parser_s10_identifier_s6___rarg_s11___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_string("identifier");
x_1 = lean::alloc_closure(reinterpret_cast<void*>(_l_s5_dlist_s9_singleton_s6___rarg), 2, 1);
lean::closure_set(x_1, 0, x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s6_labels_s6___rarg_s11___lambda__1), 6, 1);
lean::closure_set(x_2, 0, x_1);
return x_2;
}
}
obj* _l_s4_lean_s6_parser_s10_identifier_s6___rarg_s11___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = lean::mk_nat_obj(46u);
x_5 = lean::mk_nat_obj(55296u);
x_6 = lean::nat_dec_lt(x_4, x_5);
lean::dec(x_5);
if (lean::obj_tag(x_6) == 0)
{
obj* x_9; obj* x_10; 
lean::dec(x_6);
x_9 = lean::mk_nat_obj(57343u);
x_10 = lean::nat_dec_lt(x_9, x_4);
lean::dec(x_9);
if (lean::obj_tag(x_10) == 0)
{
obj* x_14; 
lean::dec(x_10);
lean::dec(x_4);
x_14 = _l_s4_lean_s6_parser_s13_monad__parsec_s5_foldl_s4___at_s4_lean_s6_parser_s10_identifier_s9___spec__4_s6___rarg(x_0, x_1, x_2, x_3);
return x_14;
}
else
{
obj* x_16; obj* x_17; 
lean::dec(x_10);
x_16 = lean::mk_nat_obj(1114112u);
x_17 = lean::nat_dec_lt(x_4, x_16);
lean::dec(x_16);
lean::dec(x_4);
if (lean::obj_tag(x_17) == 0)
{
obj* x_21; 
lean::dec(x_17);
x_21 = _l_s4_lean_s6_parser_s13_monad__parsec_s5_foldl_s4___at_s4_lean_s6_parser_s10_identifier_s9___spec__9_s6___rarg(x_0, x_1, x_2, x_3);
return x_21;
}
else
{
obj* x_23; 
lean::dec(x_17);
x_23 = _l_s4_lean_s6_parser_s13_monad__parsec_s5_foldl_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__14_s6___rarg(x_0, x_1, x_2, x_3);
return x_23;
}
}
}
else
{
obj* x_26; 
lean::dec(x_4);
lean::dec(x_6);
x_26 = _l_s4_lean_s6_parser_s13_monad__parsec_s5_foldl_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__19_s6___rarg(x_0, x_1, x_2, x_3);
return x_26;
}
}
}
obj* _l_s4_lean_s6_parser_s10_identifier(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s10_identifier_s6___rarg), 3, 0);
return x_4;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s10_identifier_s9___spec__2_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
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
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s10_identifier_s9___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s10_identifier_s9___spec__2_s6___rarg), 6, 0);
return x_6;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s10_identifier_s9___spec__3_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
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
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s10_identifier_s9___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s10_identifier_s9___spec__3_s6___rarg), 6, 0);
return x_6;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s2_ch_s4___at_s4_lean_s6_parser_s10_identifier_s9___spec__1_s6___rarg(obj* x_0, obj* x_1, unsigned x_2) {
_start:
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
x_12 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s2_ch_s4___at_s4_lean_s6_parser_s10_identifier_s9___spec__1_s6___rarg_s11___lambda__1_s7___boxed), 5, 4);
lean::closure_set(x_12, 0, x_0);
lean::closure_set(x_12, 1, x_1);
lean::closure_set(x_12, 2, x_11);
lean::closure_set(x_12, 3, x_5);
x_13 = lean::apply_4(x_3, lean::box(0), lean::box(0), x_10, x_12);
return x_13;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s2_ch_s4___at_s4_lean_s6_parser_s10_identifier_s9___spec__1_s6___rarg_s11___lambda__1(obj* x_0, obj* x_1, unsigned x_2, obj* x_3, obj* x_4) {
_start:
{
unsigned char x_6; 
lean::dec(x_0);
x_6 = lean::string_iterator_has_next(x_4);
if (x_6 == 0)
{
obj* x_9; obj* x_10; obj* x_11; obj* x_15; 
lean::dec(x_4);
lean::dec(x_3);
x_9 = lean::alloc_cnstr(0, 0, 0);
;
x_10 = _l_s4_lean_s6_parser_s13_monad__parsec_s10_eoi__error_s6___rarg_s11___closed__1;
x_11 = _l_s5_mjoin_s6___rarg_s11___closed__1;
lean::inc(x_9);
lean::inc(x_11);
lean::inc(x_10);
x_15 = _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s10_identifier_s9___spec__2_s6___rarg(x_1, lean::box(0), x_10, x_11, x_9, x_9);
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
x_31 = lean::alloc_cnstr(0, 0, 0);
;
x_32 = _l_s5_mjoin_s6___rarg_s11___closed__1;
lean::inc(x_31);
lean::inc(x_32);
x_35 = _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s10_identifier_s9___spec__3_s6___rarg(x_1, lean::box(0), x_30, x_32, x_31, x_31);
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
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s2_ch_s4___at_s4_lean_s6_parser_s10_identifier_s9___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s2_ch_s4___at_s4_lean_s6_parser_s10_identifier_s9___spec__1_s6___rarg_s7___boxed), 3, 0);
return x_4;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s10_foldl__aux_s6___main_s4___at_s4_lean_s6_parser_s10_identifier_s9___spec__5_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; 
x_5 = lean::mk_nat_obj(0u);
x_6 = lean::nat_dec_eq(x_4, x_5);
if (lean::obj_tag(x_6) == 0)
{
obj* x_8; obj* x_9; obj* x_15; obj* x_16; obj* x_18; unsigned x_20; obj* x_24; obj* x_25; obj* x_26; obj* x_28; obj* x_31; obj* x_32; obj* x_33; obj* x_36; obj* x_37; 
lean::dec(x_6);
x_8 = lean::mk_nat_obj(1u);
x_9 = lean::nat_sub(x_4, x_8);
lean::dec(x_8);
lean::dec(x_4);
lean::inc(x_2);
lean::inc(x_1);
lean::inc(x_0);
x_15 = _l_s4_lean_s6_parser_s8_id__part_s6___rarg(x_0, x_1, x_2);
x_16 = lean::cnstr_get(x_2, 0);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_16, 4);
lean::inc(x_18);
x_20 = lean::unbox_uint32(x_5);
lean::dec(x_5);
lean::inc(x_1);
lean::inc(x_0);
x_24 = _l_s4_lean_s6_parser_s13_monad__parsec_s2_ch_s4___at_s4_lean_s6_parser_s10_identifier_s9___spec__1_s6___rarg(x_0, x_1, x_20);
x_25 = lean::apply_4(x_18, lean::box(0), lean::box(0), x_24, x_15);
x_26 = lean::cnstr_get(x_2, 1);
lean::inc(x_26);
x_28 = lean::cnstr_get(x_0, 1);
lean::inc(x_28);
lean::inc(x_3);
x_31 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s10_foldl__aux_s6___main_s4___at_s4_lean_s6_parser_s10_identifier_s9___spec__5_s6___rarg_s11___lambda__1), 6, 5);
lean::closure_set(x_31, 0, x_3);
lean::closure_set(x_31, 1, x_0);
lean::closure_set(x_31, 2, x_1);
lean::closure_set(x_31, 3, x_2);
lean::closure_set(x_31, 4, x_9);
x_32 = lean::apply_4(x_28, lean::box(0), lean::box(0), x_25, x_31);
x_33 = lean::cnstr_get(x_16, 1);
lean::inc(x_33);
lean::dec(x_16);
x_36 = lean::apply_2(x_33, lean::box(0), x_3);
x_37 = lean::apply_3(x_26, lean::box(0), x_32, x_36);
return x_37;
}
else
{
obj* x_43; obj* x_46; obj* x_49; 
lean::dec(x_4);
lean::dec(x_5);
lean::dec(x_6);
lean::dec(x_0);
lean::dec(x_1);
x_43 = lean::cnstr_get(x_2, 0);
lean::inc(x_43);
lean::dec(x_2);
x_46 = lean::cnstr_get(x_43, 1);
lean::inc(x_46);
lean::dec(x_43);
x_49 = lean::apply_2(x_46, lean::box(0), x_3);
return x_49;
}
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s10_foldl__aux_s6___main_s4___at_s4_lean_s6_parser_s10_identifier_s9___spec__5_s6___rarg_s11___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; 
x_6 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_6, 0, x_0);
lean::cnstr_set(x_6, 1, x_5);
x_7 = _l_s4_lean_s6_parser_s13_monad__parsec_s10_foldl__aux_s6___main_s4___at_s4_lean_s6_parser_s10_identifier_s9___spec__5_s6___rarg(x_1, x_2, x_3, x_6, x_4);
return x_7;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s10_foldl__aux_s6___main_s4___at_s4_lean_s6_parser_s10_identifier_s9___spec__5(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s10_foldl__aux_s6___main_s4___at_s4_lean_s6_parser_s10_identifier_s9___spec__5_s6___rarg), 5, 0);
return x_4;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_foldl_s4___at_s4_lean_s6_parser_s10_identifier_s9___spec__4_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_13; obj* x_14; 
x_4 = lean::alloc_cnstr(0, 0, 0);
;
x_5 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_3);
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 0);
lean::inc(x_8);
x_10 = _l_s4_lean_s6_parser_s13_monad__parsec_s10_left__over_s6___rarg_s11___closed__1;
lean::inc(x_10);
x_12 = lean::apply_2(x_8, lean::box(0), x_10);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s5_foldl_s4___at_s4_lean_s6_parser_s10_identifier_s9___spec__4_s6___rarg_s11___lambda__1), 5, 4);
lean::closure_set(x_13, 0, x_0);
lean::closure_set(x_13, 1, x_1);
lean::closure_set(x_13, 2, x_2);
lean::closure_set(x_13, 3, x_5);
x_14 = lean::apply_4(x_6, lean::box(0), lean::box(0), x_12, x_13);
return x_14;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_foldl_s4___at_s4_lean_s6_parser_s10_identifier_s9___spec__4_s6___rarg_s11___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_7; 
x_5 = lean::string_iterator_remaining(x_4);
lean::dec(x_4);
x_7 = _l_s4_lean_s6_parser_s13_monad__parsec_s10_foldl__aux_s6___main_s4___at_s4_lean_s6_parser_s10_identifier_s9___spec__5_s6___rarg(x_0, x_1, x_2, x_3, x_5);
return x_7;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_foldl_s4___at_s4_lean_s6_parser_s10_identifier_s9___spec__4(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s5_foldl_s4___at_s4_lean_s6_parser_s10_identifier_s9___spec__4_s6___rarg), 4, 0);
return x_4;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s10_identifier_s9___spec__7_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
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
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s10_identifier_s9___spec__7(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s10_identifier_s9___spec__7_s6___rarg), 6, 0);
return x_6;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s10_identifier_s9___spec__8_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
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
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s10_identifier_s9___spec__8(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s10_identifier_s9___spec__8_s6___rarg), 6, 0);
return x_6;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s2_ch_s4___at_s4_lean_s6_parser_s10_identifier_s9___spec__6_s6___rarg(obj* x_0, obj* x_1, unsigned x_2) {
_start:
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
x_12 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s2_ch_s4___at_s4_lean_s6_parser_s10_identifier_s9___spec__6_s6___rarg_s11___lambda__1_s7___boxed), 5, 4);
lean::closure_set(x_12, 0, x_0);
lean::closure_set(x_12, 1, x_1);
lean::closure_set(x_12, 2, x_11);
lean::closure_set(x_12, 3, x_5);
x_13 = lean::apply_4(x_3, lean::box(0), lean::box(0), x_10, x_12);
return x_13;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s2_ch_s4___at_s4_lean_s6_parser_s10_identifier_s9___spec__6_s6___rarg_s11___lambda__1(obj* x_0, obj* x_1, unsigned x_2, obj* x_3, obj* x_4) {
_start:
{
unsigned char x_6; 
lean::dec(x_0);
x_6 = lean::string_iterator_has_next(x_4);
if (x_6 == 0)
{
obj* x_9; obj* x_10; obj* x_11; obj* x_15; 
lean::dec(x_4);
lean::dec(x_3);
x_9 = lean::alloc_cnstr(0, 0, 0);
;
x_10 = _l_s4_lean_s6_parser_s13_monad__parsec_s10_eoi__error_s6___rarg_s11___closed__1;
x_11 = _l_s5_mjoin_s6___rarg_s11___closed__1;
lean::inc(x_9);
lean::inc(x_11);
lean::inc(x_10);
x_15 = _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s10_identifier_s9___spec__7_s6___rarg(x_1, lean::box(0), x_10, x_11, x_9, x_9);
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
x_31 = lean::alloc_cnstr(0, 0, 0);
;
x_32 = _l_s5_mjoin_s6___rarg_s11___closed__1;
lean::inc(x_31);
lean::inc(x_32);
x_35 = _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s10_identifier_s9___spec__8_s6___rarg(x_1, lean::box(0), x_30, x_32, x_31, x_31);
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
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s2_ch_s4___at_s4_lean_s6_parser_s10_identifier_s9___spec__6(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s2_ch_s4___at_s4_lean_s6_parser_s10_identifier_s9___spec__6_s6___rarg_s7___boxed), 3, 0);
return x_4;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s10_foldl__aux_s6___main_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__10_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; 
x_5 = lean::mk_nat_obj(0u);
x_6 = lean::nat_dec_eq(x_4, x_5);
if (lean::obj_tag(x_6) == 0)
{
obj* x_8; obj* x_9; obj* x_15; obj* x_16; obj* x_18; unsigned x_20; obj* x_24; obj* x_25; obj* x_26; obj* x_28; obj* x_31; obj* x_32; obj* x_33; obj* x_36; obj* x_37; 
lean::dec(x_6);
x_8 = lean::mk_nat_obj(1u);
x_9 = lean::nat_sub(x_4, x_8);
lean::dec(x_8);
lean::dec(x_4);
lean::inc(x_2);
lean::inc(x_1);
lean::inc(x_0);
x_15 = _l_s4_lean_s6_parser_s8_id__part_s6___rarg(x_0, x_1, x_2);
x_16 = lean::cnstr_get(x_2, 0);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_16, 4);
lean::inc(x_18);
x_20 = lean::unbox_uint32(x_5);
lean::dec(x_5);
lean::inc(x_1);
lean::inc(x_0);
x_24 = _l_s4_lean_s6_parser_s13_monad__parsec_s2_ch_s4___at_s4_lean_s6_parser_s10_identifier_s9___spec__6_s6___rarg(x_0, x_1, x_20);
x_25 = lean::apply_4(x_18, lean::box(0), lean::box(0), x_24, x_15);
x_26 = lean::cnstr_get(x_2, 1);
lean::inc(x_26);
x_28 = lean::cnstr_get(x_0, 1);
lean::inc(x_28);
lean::inc(x_3);
x_31 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s10_foldl__aux_s6___main_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__10_s6___rarg_s11___lambda__1), 6, 5);
lean::closure_set(x_31, 0, x_3);
lean::closure_set(x_31, 1, x_0);
lean::closure_set(x_31, 2, x_1);
lean::closure_set(x_31, 3, x_2);
lean::closure_set(x_31, 4, x_9);
x_32 = lean::apply_4(x_28, lean::box(0), lean::box(0), x_25, x_31);
x_33 = lean::cnstr_get(x_16, 1);
lean::inc(x_33);
lean::dec(x_16);
x_36 = lean::apply_2(x_33, lean::box(0), x_3);
x_37 = lean::apply_3(x_26, lean::box(0), x_32, x_36);
return x_37;
}
else
{
obj* x_43; obj* x_46; obj* x_49; 
lean::dec(x_4);
lean::dec(x_5);
lean::dec(x_6);
lean::dec(x_0);
lean::dec(x_1);
x_43 = lean::cnstr_get(x_2, 0);
lean::inc(x_43);
lean::dec(x_2);
x_46 = lean::cnstr_get(x_43, 1);
lean::inc(x_46);
lean::dec(x_43);
x_49 = lean::apply_2(x_46, lean::box(0), x_3);
return x_49;
}
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s10_foldl__aux_s6___main_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__10_s6___rarg_s11___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; 
x_6 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_6, 0, x_0);
lean::cnstr_set(x_6, 1, x_5);
x_7 = _l_s4_lean_s6_parser_s13_monad__parsec_s10_foldl__aux_s6___main_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__10_s6___rarg(x_1, x_2, x_3, x_6, x_4);
return x_7;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s10_foldl__aux_s6___main_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__10(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s10_foldl__aux_s6___main_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__10_s6___rarg), 5, 0);
return x_4;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_foldl_s4___at_s4_lean_s6_parser_s10_identifier_s9___spec__9_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_13; obj* x_14; 
x_4 = lean::alloc_cnstr(0, 0, 0);
;
x_5 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_3);
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 0);
lean::inc(x_8);
x_10 = _l_s4_lean_s6_parser_s13_monad__parsec_s10_left__over_s6___rarg_s11___closed__1;
lean::inc(x_10);
x_12 = lean::apply_2(x_8, lean::box(0), x_10);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s5_foldl_s4___at_s4_lean_s6_parser_s10_identifier_s9___spec__9_s6___rarg_s11___lambda__1), 5, 4);
lean::closure_set(x_13, 0, x_0);
lean::closure_set(x_13, 1, x_1);
lean::closure_set(x_13, 2, x_2);
lean::closure_set(x_13, 3, x_5);
x_14 = lean::apply_4(x_6, lean::box(0), lean::box(0), x_12, x_13);
return x_14;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_foldl_s4___at_s4_lean_s6_parser_s10_identifier_s9___spec__9_s6___rarg_s11___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_7; 
x_5 = lean::string_iterator_remaining(x_4);
lean::dec(x_4);
x_7 = _l_s4_lean_s6_parser_s13_monad__parsec_s10_foldl__aux_s6___main_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__10_s6___rarg(x_0, x_1, x_2, x_3, x_5);
return x_7;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_foldl_s4___at_s4_lean_s6_parser_s10_identifier_s9___spec__9(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s5_foldl_s4___at_s4_lean_s6_parser_s10_identifier_s9___spec__9_s6___rarg), 4, 0);
return x_4;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__12_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
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
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__12(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__12_s6___rarg), 6, 0);
return x_6;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__13_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
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
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__13(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__13_s6___rarg), 6, 0);
return x_6;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s2_ch_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__11_s6___rarg(obj* x_0, obj* x_1, unsigned x_2) {
_start:
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
x_12 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s2_ch_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__11_s6___rarg_s11___lambda__1_s7___boxed), 5, 4);
lean::closure_set(x_12, 0, x_0);
lean::closure_set(x_12, 1, x_1);
lean::closure_set(x_12, 2, x_11);
lean::closure_set(x_12, 3, x_5);
x_13 = lean::apply_4(x_3, lean::box(0), lean::box(0), x_10, x_12);
return x_13;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s2_ch_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__11_s6___rarg_s11___lambda__1(obj* x_0, obj* x_1, unsigned x_2, obj* x_3, obj* x_4) {
_start:
{
unsigned char x_6; 
lean::dec(x_0);
x_6 = lean::string_iterator_has_next(x_4);
if (x_6 == 0)
{
obj* x_9; obj* x_10; obj* x_11; obj* x_15; 
lean::dec(x_4);
lean::dec(x_3);
x_9 = lean::alloc_cnstr(0, 0, 0);
;
x_10 = _l_s4_lean_s6_parser_s13_monad__parsec_s10_eoi__error_s6___rarg_s11___closed__1;
x_11 = _l_s5_mjoin_s6___rarg_s11___closed__1;
lean::inc(x_9);
lean::inc(x_11);
lean::inc(x_10);
x_15 = _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__12_s6___rarg(x_1, lean::box(0), x_10, x_11, x_9, x_9);
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
x_31 = lean::alloc_cnstr(0, 0, 0);
;
x_32 = _l_s5_mjoin_s6___rarg_s11___closed__1;
lean::inc(x_31);
lean::inc(x_32);
x_35 = _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__13_s6___rarg(x_1, lean::box(0), x_30, x_32, x_31, x_31);
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
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s2_ch_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__11(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s2_ch_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__11_s6___rarg_s7___boxed), 3, 0);
return x_4;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s10_foldl__aux_s6___main_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__15_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; 
x_5 = lean::mk_nat_obj(0u);
x_6 = lean::nat_dec_eq(x_4, x_5);
lean::dec(x_5);
if (lean::obj_tag(x_6) == 0)
{
obj* x_9; obj* x_10; obj* x_16; obj* x_17; obj* x_19; obj* x_21; unsigned x_22; obj* x_26; obj* x_27; obj* x_28; obj* x_30; obj* x_33; obj* x_34; obj* x_35; obj* x_38; obj* x_39; 
lean::dec(x_6);
x_9 = lean::mk_nat_obj(1u);
x_10 = lean::nat_sub(x_4, x_9);
lean::dec(x_9);
lean::dec(x_4);
lean::inc(x_2);
lean::inc(x_1);
lean::inc(x_0);
x_16 = _l_s4_lean_s6_parser_s8_id__part_s6___rarg(x_0, x_1, x_2);
x_17 = lean::cnstr_get(x_2, 0);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_17, 4);
lean::inc(x_19);
x_21 = lean::mk_nat_obj(46u);
x_22 = lean::unbox_uint32(x_21);
lean::dec(x_21);
lean::inc(x_1);
lean::inc(x_0);
x_26 = _l_s4_lean_s6_parser_s13_monad__parsec_s2_ch_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__11_s6___rarg(x_0, x_1, x_22);
x_27 = lean::apply_4(x_19, lean::box(0), lean::box(0), x_26, x_16);
x_28 = lean::cnstr_get(x_2, 1);
lean::inc(x_28);
x_30 = lean::cnstr_get(x_0, 1);
lean::inc(x_30);
lean::inc(x_3);
x_33 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s10_foldl__aux_s6___main_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__15_s6___rarg_s11___lambda__1), 6, 5);
lean::closure_set(x_33, 0, x_3);
lean::closure_set(x_33, 1, x_0);
lean::closure_set(x_33, 2, x_1);
lean::closure_set(x_33, 3, x_2);
lean::closure_set(x_33, 4, x_10);
x_34 = lean::apply_4(x_30, lean::box(0), lean::box(0), x_27, x_33);
x_35 = lean::cnstr_get(x_17, 1);
lean::inc(x_35);
lean::dec(x_17);
x_38 = lean::apply_2(x_35, lean::box(0), x_3);
x_39 = lean::apply_3(x_28, lean::box(0), x_34, x_38);
return x_39;
}
else
{
obj* x_44; obj* x_47; obj* x_50; 
lean::dec(x_4);
lean::dec(x_6);
lean::dec(x_0);
lean::dec(x_1);
x_44 = lean::cnstr_get(x_2, 0);
lean::inc(x_44);
lean::dec(x_2);
x_47 = lean::cnstr_get(x_44, 1);
lean::inc(x_47);
lean::dec(x_44);
x_50 = lean::apply_2(x_47, lean::box(0), x_3);
return x_50;
}
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s10_foldl__aux_s6___main_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__15_s6___rarg_s11___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; 
x_6 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_6, 0, x_0);
lean::cnstr_set(x_6, 1, x_5);
x_7 = _l_s4_lean_s6_parser_s13_monad__parsec_s10_foldl__aux_s6___main_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__15_s6___rarg(x_1, x_2, x_3, x_6, x_4);
return x_7;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s10_foldl__aux_s6___main_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__15(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s10_foldl__aux_s6___main_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__15_s6___rarg), 5, 0);
return x_4;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_foldl_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__14_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_13; obj* x_14; 
x_4 = lean::alloc_cnstr(0, 0, 0);
;
x_5 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_3);
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 0);
lean::inc(x_8);
x_10 = _l_s4_lean_s6_parser_s13_monad__parsec_s10_left__over_s6___rarg_s11___closed__1;
lean::inc(x_10);
x_12 = lean::apply_2(x_8, lean::box(0), x_10);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s5_foldl_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__14_s6___rarg_s11___lambda__1), 5, 4);
lean::closure_set(x_13, 0, x_0);
lean::closure_set(x_13, 1, x_1);
lean::closure_set(x_13, 2, x_2);
lean::closure_set(x_13, 3, x_5);
x_14 = lean::apply_4(x_6, lean::box(0), lean::box(0), x_12, x_13);
return x_14;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_foldl_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__14_s6___rarg_s11___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_7; 
x_5 = lean::string_iterator_remaining(x_4);
lean::dec(x_4);
x_7 = _l_s4_lean_s6_parser_s13_monad__parsec_s10_foldl__aux_s6___main_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__15_s6___rarg(x_0, x_1, x_2, x_3, x_5);
return x_7;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_foldl_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__14(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s5_foldl_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__14_s6___rarg), 4, 0);
return x_4;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__17_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
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
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__17(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__17_s6___rarg), 6, 0);
return x_6;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__18_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
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
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__18(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__18_s6___rarg), 6, 0);
return x_6;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s2_ch_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__16_s6___rarg(obj* x_0, obj* x_1, unsigned x_2) {
_start:
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
x_12 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s2_ch_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__16_s6___rarg_s11___lambda__1_s7___boxed), 5, 4);
lean::closure_set(x_12, 0, x_0);
lean::closure_set(x_12, 1, x_1);
lean::closure_set(x_12, 2, x_11);
lean::closure_set(x_12, 3, x_5);
x_13 = lean::apply_4(x_3, lean::box(0), lean::box(0), x_10, x_12);
return x_13;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s2_ch_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__16_s6___rarg_s11___lambda__1(obj* x_0, obj* x_1, unsigned x_2, obj* x_3, obj* x_4) {
_start:
{
unsigned char x_6; 
lean::dec(x_0);
x_6 = lean::string_iterator_has_next(x_4);
if (x_6 == 0)
{
obj* x_9; obj* x_10; obj* x_11; obj* x_15; 
lean::dec(x_4);
lean::dec(x_3);
x_9 = lean::alloc_cnstr(0, 0, 0);
;
x_10 = _l_s4_lean_s6_parser_s13_monad__parsec_s10_eoi__error_s6___rarg_s11___closed__1;
x_11 = _l_s5_mjoin_s6___rarg_s11___closed__1;
lean::inc(x_9);
lean::inc(x_11);
lean::inc(x_10);
x_15 = _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__17_s6___rarg(x_1, lean::box(0), x_10, x_11, x_9, x_9);
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
x_31 = lean::alloc_cnstr(0, 0, 0);
;
x_32 = _l_s5_mjoin_s6___rarg_s11___closed__1;
lean::inc(x_31);
lean::inc(x_32);
x_35 = _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__18_s6___rarg(x_1, lean::box(0), x_30, x_32, x_31, x_31);
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
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s2_ch_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__16(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s2_ch_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__16_s6___rarg_s7___boxed), 3, 0);
return x_4;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s10_foldl__aux_s6___main_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__20_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; 
x_5 = lean::mk_nat_obj(0u);
x_6 = lean::nat_dec_eq(x_4, x_5);
lean::dec(x_5);
if (lean::obj_tag(x_6) == 0)
{
obj* x_9; obj* x_10; obj* x_16; obj* x_17; obj* x_19; obj* x_21; unsigned x_22; obj* x_26; obj* x_27; obj* x_28; obj* x_30; obj* x_33; obj* x_34; obj* x_35; obj* x_38; obj* x_39; 
lean::dec(x_6);
x_9 = lean::mk_nat_obj(1u);
x_10 = lean::nat_sub(x_4, x_9);
lean::dec(x_9);
lean::dec(x_4);
lean::inc(x_2);
lean::inc(x_1);
lean::inc(x_0);
x_16 = _l_s4_lean_s6_parser_s8_id__part_s6___rarg(x_0, x_1, x_2);
x_17 = lean::cnstr_get(x_2, 0);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_17, 4);
lean::inc(x_19);
x_21 = lean::mk_nat_obj(46u);
x_22 = lean::unbox_uint32(x_21);
lean::dec(x_21);
lean::inc(x_1);
lean::inc(x_0);
x_26 = _l_s4_lean_s6_parser_s13_monad__parsec_s2_ch_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__16_s6___rarg(x_0, x_1, x_22);
x_27 = lean::apply_4(x_19, lean::box(0), lean::box(0), x_26, x_16);
x_28 = lean::cnstr_get(x_2, 1);
lean::inc(x_28);
x_30 = lean::cnstr_get(x_0, 1);
lean::inc(x_30);
lean::inc(x_3);
x_33 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s10_foldl__aux_s6___main_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__20_s6___rarg_s11___lambda__1), 6, 5);
lean::closure_set(x_33, 0, x_3);
lean::closure_set(x_33, 1, x_0);
lean::closure_set(x_33, 2, x_1);
lean::closure_set(x_33, 3, x_2);
lean::closure_set(x_33, 4, x_10);
x_34 = lean::apply_4(x_30, lean::box(0), lean::box(0), x_27, x_33);
x_35 = lean::cnstr_get(x_17, 1);
lean::inc(x_35);
lean::dec(x_17);
x_38 = lean::apply_2(x_35, lean::box(0), x_3);
x_39 = lean::apply_3(x_28, lean::box(0), x_34, x_38);
return x_39;
}
else
{
obj* x_44; obj* x_47; obj* x_50; 
lean::dec(x_4);
lean::dec(x_6);
lean::dec(x_0);
lean::dec(x_1);
x_44 = lean::cnstr_get(x_2, 0);
lean::inc(x_44);
lean::dec(x_2);
x_47 = lean::cnstr_get(x_44, 1);
lean::inc(x_47);
lean::dec(x_44);
x_50 = lean::apply_2(x_47, lean::box(0), x_3);
return x_50;
}
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s10_foldl__aux_s6___main_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__20_s6___rarg_s11___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; 
x_6 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_6, 0, x_0);
lean::cnstr_set(x_6, 1, x_5);
x_7 = _l_s4_lean_s6_parser_s13_monad__parsec_s10_foldl__aux_s6___main_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__20_s6___rarg(x_1, x_2, x_3, x_6, x_4);
return x_7;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s10_foldl__aux_s6___main_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__20(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s10_foldl__aux_s6___main_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__20_s6___rarg), 5, 0);
return x_4;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_foldl_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__19_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_13; obj* x_14; 
x_4 = lean::alloc_cnstr(0, 0, 0);
;
x_5 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_3);
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 0);
lean::inc(x_8);
x_10 = _l_s4_lean_s6_parser_s13_monad__parsec_s10_left__over_s6___rarg_s11___closed__1;
lean::inc(x_10);
x_12 = lean::apply_2(x_8, lean::box(0), x_10);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s5_foldl_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__19_s6___rarg_s11___lambda__1), 5, 4);
lean::closure_set(x_13, 0, x_0);
lean::closure_set(x_13, 1, x_1);
lean::closure_set(x_13, 2, x_2);
lean::closure_set(x_13, 3, x_5);
x_14 = lean::apply_4(x_6, lean::box(0), lean::box(0), x_12, x_13);
return x_14;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_foldl_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__19_s6___rarg_s11___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_7; 
x_5 = lean::string_iterator_remaining(x_4);
lean::dec(x_4);
x_7 = _l_s4_lean_s6_parser_s13_monad__parsec_s10_foldl__aux_s6___main_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__20_s6___rarg(x_0, x_1, x_2, x_3, x_5);
return x_7;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_foldl_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__19(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s5_foldl_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__19_s6___rarg), 4, 0);
return x_4;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s2_ch_s4___at_s4_lean_s6_parser_s10_identifier_s9___spec__1_s6___rarg_s7___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
unsigned x_3; obj* x_4; 
x_3 = lean::unbox_uint32(x_2);
x_4 = _l_s4_lean_s6_parser_s13_monad__parsec_s2_ch_s4___at_s4_lean_s6_parser_s10_identifier_s9___spec__1_s6___rarg(x_0, x_1, x_3);
return x_4;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s2_ch_s4___at_s4_lean_s6_parser_s10_identifier_s9___spec__1_s6___rarg_s11___lambda__1_s7___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
unsigned x_5; obj* x_6; 
x_5 = lean::unbox_uint32(x_2);
x_6 = _l_s4_lean_s6_parser_s13_monad__parsec_s2_ch_s4___at_s4_lean_s6_parser_s10_identifier_s9___spec__1_s6___rarg_s11___lambda__1(x_0, x_1, x_5, x_3, x_4);
return x_6;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s2_ch_s4___at_s4_lean_s6_parser_s10_identifier_s9___spec__6_s6___rarg_s7___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
unsigned x_3; obj* x_4; 
x_3 = lean::unbox_uint32(x_2);
x_4 = _l_s4_lean_s6_parser_s13_monad__parsec_s2_ch_s4___at_s4_lean_s6_parser_s10_identifier_s9___spec__6_s6___rarg(x_0, x_1, x_3);
return x_4;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s2_ch_s4___at_s4_lean_s6_parser_s10_identifier_s9___spec__6_s6___rarg_s11___lambda__1_s7___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
unsigned x_5; obj* x_6; 
x_5 = lean::unbox_uint32(x_2);
x_6 = _l_s4_lean_s6_parser_s13_monad__parsec_s2_ch_s4___at_s4_lean_s6_parser_s10_identifier_s9___spec__6_s6___rarg_s11___lambda__1(x_0, x_1, x_5, x_3, x_4);
return x_6;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s2_ch_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__11_s6___rarg_s7___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
unsigned x_3; obj* x_4; 
x_3 = lean::unbox_uint32(x_2);
x_4 = _l_s4_lean_s6_parser_s13_monad__parsec_s2_ch_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__11_s6___rarg(x_0, x_1, x_3);
return x_4;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s2_ch_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__11_s6___rarg_s11___lambda__1_s7___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
unsigned x_5; obj* x_6; 
x_5 = lean::unbox_uint32(x_2);
x_6 = _l_s4_lean_s6_parser_s13_monad__parsec_s2_ch_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__11_s6___rarg_s11___lambda__1(x_0, x_1, x_5, x_3, x_4);
return x_6;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s2_ch_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__16_s6___rarg_s7___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
unsigned x_3; obj* x_4; 
x_3 = lean::unbox_uint32(x_2);
x_4 = _l_s4_lean_s6_parser_s13_monad__parsec_s2_ch_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__16_s6___rarg(x_0, x_1, x_3);
return x_4;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s2_ch_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__16_s6___rarg_s11___lambda__1_s7___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
unsigned x_5; obj* x_6; 
x_5 = lean::unbox_uint32(x_2);
x_6 = _l_s4_lean_s6_parser_s13_monad__parsec_s2_ch_s4___at_s4_lean_s6_parser_s10_identifier_s10___spec__16_s6___rarg_s11___lambda__1(x_0, x_1, x_5, x_3, x_4);
return x_6;
}
}
obj* _l_s4_lean_s6_parser_s13_c__identifier_s6___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_6; obj* x_8; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_18; obj* x_19; obj* x_22; obj* x_25; obj* x_26; obj* x_28; 
lean::dec(x_2);
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
x_8 = _l_s4_lean_s6_parser_s13_monad__parsec_s10_left__over_s6___rarg_s11___closed__1;
lean::inc(x_8);
lean::inc(x_6);
x_11 = lean::apply_2(x_6, lean::box(0), x_8);
lean::inc(x_1);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_c__identifier_s6___rarg_s11___lambda__1), 4, 3);
lean::closure_set(x_13, 0, x_0);
lean::closure_set(x_13, 1, x_1);
lean::closure_set(x_13, 2, x_6);
lean::inc(x_4);
x_15 = lean::apply_4(x_4, lean::box(0), lean::box(0), x_11, x_13);
lean::inc(x_1);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s17_take__while__cont_s4___at_s4_lean_s6_parser_s13_c__identifier_s9___spec__3_s6___rarg_s7___boxed), 2, 1);
lean::closure_set(x_17, 0, x_1);
x_18 = lean::apply_4(x_4, lean::box(0), lean::box(0), x_15, x_17);
x_19 = lean::cnstr_get(x_1, 1);
lean::inc(x_19);
lean::dec(x_1);
x_22 = _l_s4_lean_s6_parser_s13_monad__parsec_s3_try_s6___rarg_s11___closed__1;
lean::inc(x_22);
lean::inc(x_19);
x_25 = lean::apply_3(x_19, lean::box(0), x_22, x_18);
x_26 = _l_s4_lean_s6_parser_s13_c__identifier_s6___rarg_s11___closed__1;
lean::inc(x_26);
x_28 = lean::apply_3(x_19, lean::box(0), x_26, x_25);
return x_28;
}
}
obj* _init__l_s4_lean_s6_parser_s13_c__identifier_s6___rarg_s11___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_string("C identifier");
x_1 = lean::alloc_closure(reinterpret_cast<void*>(_l_s5_dlist_s9_singleton_s6___rarg), 2, 1);
lean::closure_set(x_1, 0, x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s6_labels_s6___rarg_s11___lambda__1), 6, 1);
lean::closure_set(x_2, 0, x_1);
return x_2;
}
}
obj* _l_s4_lean_s6_parser_s13_c__identifier_s6___rarg_s11___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
unsigned char x_5; 
lean::dec(x_0);
x_5 = lean::string_iterator_has_next(x_3);
if (x_5 == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_14; 
lean::dec(x_2);
lean::dec(x_3);
x_8 = lean::alloc_cnstr(0, 0, 0);
;
x_9 = _l_s4_lean_s6_parser_s13_monad__parsec_s10_eoi__error_s6___rarg_s11___closed__1;
x_10 = _l_s5_mjoin_s6___rarg_s11___closed__1;
lean::inc(x_8);
lean::inc(x_10);
lean::inc(x_9);
x_14 = _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_c__identifier_s9___spec__1_s6___rarg(x_1, lean::box(0), x_9, x_10, x_8, x_8);
return x_14;
}
else
{
unsigned x_15; unsigned char x_16; unsigned char x_18; 
x_15 = lean::string_iterator_curr(x_3);
x_18 = _l_s4_char_s9_is__alpha(x_15);
if (x_18 == 0)
{
obj* x_19; obj* x_20; obj* x_21; 
x_19 = lean::mk_nat_obj(95u);
x_20 = lean::mk_nat_obj(55296u);
x_21 = lean::nat_dec_lt(x_19, x_20);
lean::dec(x_20);
if (lean::obj_tag(x_21) == 0)
{
obj* x_24; obj* x_25; 
lean::dec(x_21);
x_24 = lean::mk_nat_obj(57343u);
x_25 = lean::nat_dec_lt(x_24, x_19);
lean::dec(x_24);
if (lean::obj_tag(x_25) == 0)
{
obj* x_29; obj* x_30; obj* x_31; 
lean::dec(x_19);
lean::dec(x_25);
x_29 = lean::mk_nat_obj(0u);
x_30 = lean::box_uint32(x_15);
x_31 = lean::nat_dec_eq(x_30, x_29);
lean::dec(x_29);
if (lean::obj_tag(x_31) == 0)
{
lean::dec(x_31);
if (x_18 == 0)
{
unsigned char x_37; 
lean::dec(x_2);
lean::dec(x_3);
lean::dec(x_30);
x_37 = 0;
x_16 = x_37;
goto lbl_17;
}
else
{
obj* x_39; obj* x_40; 
lean::dec(x_1);
x_39 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s7_satisfy_s6___rarg_s11___lambda__1_s7___boxed), 3, 2);
lean::closure_set(x_39, 0, x_3);
lean::closure_set(x_39, 1, x_30);
x_40 = lean::apply_2(x_2, lean::box(0), x_39);
return x_40;
}
}
else
{
obj* x_43; obj* x_44; 
lean::dec(x_1);
lean::dec(x_31);
x_43 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s7_satisfy_s6___rarg_s11___lambda__1_s7___boxed), 3, 2);
lean::closure_set(x_43, 0, x_3);
lean::closure_set(x_43, 1, x_30);
x_44 = lean::apply_2(x_2, lean::box(0), x_43);
return x_44;
}
}
else
{
obj* x_46; obj* x_47; 
lean::dec(x_25);
x_46 = lean::mk_nat_obj(1114112u);
x_47 = lean::nat_dec_lt(x_19, x_46);
lean::dec(x_46);
if (lean::obj_tag(x_47) == 0)
{
obj* x_51; obj* x_52; obj* x_53; 
lean::dec(x_19);
lean::dec(x_47);
x_51 = lean::mk_nat_obj(0u);
x_52 = lean::box_uint32(x_15);
x_53 = lean::nat_dec_eq(x_52, x_51);
lean::dec(x_51);
if (lean::obj_tag(x_53) == 0)
{
lean::dec(x_53);
if (x_18 == 0)
{
unsigned char x_59; 
lean::dec(x_52);
lean::dec(x_2);
lean::dec(x_3);
x_59 = 0;
x_16 = x_59;
goto lbl_17;
}
else
{
obj* x_61; obj* x_62; 
lean::dec(x_1);
x_61 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s7_satisfy_s6___rarg_s11___lambda__1_s7___boxed), 3, 2);
lean::closure_set(x_61, 0, x_3);
lean::closure_set(x_61, 1, x_52);
x_62 = lean::apply_2(x_2, lean::box(0), x_61);
return x_62;
}
}
else
{
obj* x_65; obj* x_66; 
lean::dec(x_53);
lean::dec(x_1);
x_65 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s7_satisfy_s6___rarg_s11___lambda__1_s7___boxed), 3, 2);
lean::closure_set(x_65, 0, x_3);
lean::closure_set(x_65, 1, x_52);
x_66 = lean::apply_2(x_2, lean::box(0), x_65);
return x_66;
}
}
else
{
obj* x_68; obj* x_69; 
lean::dec(x_47);
x_68 = lean::box_uint32(x_15);
x_69 = lean::nat_dec_eq(x_68, x_19);
lean::dec(x_19);
if (lean::obj_tag(x_69) == 0)
{
lean::dec(x_69);
if (x_18 == 0)
{
unsigned char x_75; 
lean::dec(x_2);
lean::dec(x_3);
lean::dec(x_68);
x_75 = 0;
x_16 = x_75;
goto lbl_17;
}
else
{
obj* x_77; obj* x_78; 
lean::dec(x_1);
x_77 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s7_satisfy_s6___rarg_s11___lambda__1_s7___boxed), 3, 2);
lean::closure_set(x_77, 0, x_3);
lean::closure_set(x_77, 1, x_68);
x_78 = lean::apply_2(x_2, lean::box(0), x_77);
return x_78;
}
}
else
{
obj* x_81; obj* x_82; 
lean::dec(x_1);
lean::dec(x_69);
x_81 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s7_satisfy_s6___rarg_s11___lambda__1_s7___boxed), 3, 2);
lean::closure_set(x_81, 0, x_3);
lean::closure_set(x_81, 1, x_68);
x_82 = lean::apply_2(x_2, lean::box(0), x_81);
return x_82;
}
}
}
}
else
{
obj* x_84; obj* x_85; 
lean::dec(x_21);
x_84 = lean::box_uint32(x_15);
x_85 = lean::nat_dec_eq(x_84, x_19);
lean::dec(x_19);
if (lean::obj_tag(x_85) == 0)
{
lean::dec(x_85);
if (x_18 == 0)
{
unsigned char x_91; 
lean::dec(x_84);
lean::dec(x_2);
lean::dec(x_3);
x_91 = 0;
x_16 = x_91;
goto lbl_17;
}
else
{
obj* x_93; obj* x_94; 
lean::dec(x_1);
x_93 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s7_satisfy_s6___rarg_s11___lambda__1_s7___boxed), 3, 2);
lean::closure_set(x_93, 0, x_3);
lean::closure_set(x_93, 1, x_84);
x_94 = lean::apply_2(x_2, lean::box(0), x_93);
return x_94;
}
}
else
{
obj* x_97; obj* x_98; 
lean::dec(x_85);
lean::dec(x_1);
x_97 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s7_satisfy_s6___rarg_s11___lambda__1_s7___boxed), 3, 2);
lean::closure_set(x_97, 0, x_3);
lean::closure_set(x_97, 1, x_84);
x_98 = lean::apply_2(x_2, lean::box(0), x_97);
return x_98;
}
}
}
else
{
if (x_18 == 0)
{
unsigned char x_101; 
lean::dec(x_2);
lean::dec(x_3);
x_101 = 0;
x_16 = x_101;
goto lbl_17;
}
else
{
obj* x_103; obj* x_104; obj* x_105; 
lean::dec(x_1);
x_103 = lean::box_uint32(x_15);
x_104 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s7_satisfy_s6___rarg_s11___lambda__1_s7___boxed), 3, 2);
lean::closure_set(x_104, 0, x_3);
lean::closure_set(x_104, 1, x_103);
x_105 = lean::apply_2(x_2, lean::box(0), x_104);
return x_105;
}
}
lbl_17:
{
obj* x_106; obj* x_107; obj* x_109; obj* x_111; obj* x_112; obj* x_113; obj* x_116; 
x_106 = _l_s4_char_s11_quote__core(x_15);
x_107 = _l_s4_char_s9_has__repr_s11___closed__1;
lean::inc(x_107);
x_109 = lean::string_append(x_107, x_106);
lean::dec(x_106);
x_111 = lean::string_append(x_109, x_107);
x_112 = lean::alloc_cnstr(0, 0, 0);
;
x_113 = _l_s5_mjoin_s6___rarg_s11___closed__1;
lean::inc(x_112);
lean::inc(x_113);
x_116 = _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_c__identifier_s9___spec__2_s6___rarg(x_1, lean::box(0), x_111, x_113, x_112, x_112);
return x_116;
}
}
}
}
obj* _l_s4_lean_s6_parser_s13_c__identifier(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_c__identifier_s6___rarg), 3, 0);
return x_4;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_c__identifier_s9___spec__1_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
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
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_c__identifier_s9___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_c__identifier_s9___spec__1_s6___rarg), 6, 0);
return x_6;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_c__identifier_s9___spec__2_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
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
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_c__identifier_s9___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s5_error_s4___at_s4_lean_s6_parser_s13_c__identifier_s9___spec__2_s6___rarg), 6, 0);
return x_6;
}
}
obj* _l_s9___private_31565857__s16_take__while__aux_s6___main_s4___at_s4_lean_s6_parser_s13_c__identifier_s9___spec__4_s6___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (lean::obj_tag(x_4) == 0)
{
unsigned char x_6; 
lean::dec(x_4);
x_6 = lean::string_iterator_has_next(x_2);
if (x_6 == 0)
{
obj* x_9; 
lean::dec(x_0);
lean::dec(x_3);
x_9 = _l_s9___private_2142412293__s18_mk__string__result_s6___rarg(x_1, x_2);
return x_9;
}
else
{
obj* x_10; obj* x_11; unsigned x_14; unsigned char x_15; unsigned char x_17; 
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_sub(x_0, x_10);
lean::dec(x_10);
lean::dec(x_0);
x_14 = lean::string_iterator_curr(x_2);
x_17 = _l_s4_char_s12_is__alphanum(x_14);
if (x_17 == 0)
{
obj* x_18; obj* x_19; obj* x_20; 
x_18 = lean::mk_nat_obj(95u);
x_19 = lean::mk_nat_obj(55296u);
x_20 = lean::nat_dec_lt(x_18, x_19);
lean::dec(x_19);
if (lean::obj_tag(x_20) == 0)
{
obj* x_23; obj* x_24; 
lean::dec(x_20);
x_23 = lean::mk_nat_obj(57343u);
x_24 = lean::nat_dec_lt(x_23, x_18);
lean::dec(x_23);
if (lean::obj_tag(x_24) == 0)
{
obj* x_28; obj* x_29; 
lean::dec(x_18);
lean::dec(x_24);
x_28 = lean::box_uint32(x_14);
x_29 = lean::nat_dec_eq(x_28, x_3);
lean::dec(x_3);
lean::dec(x_28);
if (lean::obj_tag(x_29) == 0)
{
lean::dec(x_29);
if (x_17 == 0)
{
obj* x_34; 
lean::dec(x_11);
x_34 = _l_s9___private_2142412293__s18_mk__string__result_s6___rarg(x_1, x_2);
return x_34;
}
else
{
unsigned char x_35; 
x_35 = 0;
x_15 = x_35;
goto lbl_16;
}
}
else
{
unsigned char x_37; 
lean::dec(x_29);
x_37 = 0;
x_15 = x_37;
goto lbl_16;
}
}
else
{
obj* x_39; obj* x_40; 
lean::dec(x_24);
x_39 = lean::mk_nat_obj(1114112u);
x_40 = lean::nat_dec_lt(x_18, x_39);
lean::dec(x_39);
if (lean::obj_tag(x_40) == 0)
{
obj* x_44; obj* x_45; 
lean::dec(x_40);
lean::dec(x_18);
x_44 = lean::box_uint32(x_14);
x_45 = lean::nat_dec_eq(x_44, x_3);
lean::dec(x_3);
lean::dec(x_44);
if (lean::obj_tag(x_45) == 0)
{
lean::dec(x_45);
if (x_17 == 0)
{
obj* x_50; 
lean::dec(x_11);
x_50 = _l_s9___private_2142412293__s18_mk__string__result_s6___rarg(x_1, x_2);
return x_50;
}
else
{
unsigned char x_51; 
x_51 = 0;
x_15 = x_51;
goto lbl_16;
}
}
else
{
unsigned char x_53; 
lean::dec(x_45);
x_53 = 0;
x_15 = x_53;
goto lbl_16;
}
}
else
{
obj* x_56; obj* x_57; 
lean::dec(x_40);
lean::dec(x_3);
x_56 = lean::box_uint32(x_14);
x_57 = lean::nat_dec_eq(x_56, x_18);
lean::dec(x_18);
lean::dec(x_56);
if (lean::obj_tag(x_57) == 0)
{
lean::dec(x_57);
if (x_17 == 0)
{
obj* x_62; 
lean::dec(x_11);
x_62 = _l_s9___private_2142412293__s18_mk__string__result_s6___rarg(x_1, x_2);
return x_62;
}
else
{
unsigned char x_63; 
x_63 = 0;
x_15 = x_63;
goto lbl_16;
}
}
else
{
unsigned char x_65; 
lean::dec(x_57);
x_65 = 0;
x_15 = x_65;
goto lbl_16;
}
}
}
}
else
{
obj* x_68; obj* x_69; 
lean::dec(x_3);
lean::dec(x_20);
x_68 = lean::box_uint32(x_14);
x_69 = lean::nat_dec_eq(x_68, x_18);
lean::dec(x_18);
lean::dec(x_68);
if (lean::obj_tag(x_69) == 0)
{
lean::dec(x_69);
if (x_17 == 0)
{
obj* x_74; 
lean::dec(x_11);
x_74 = _l_s9___private_2142412293__s18_mk__string__result_s6___rarg(x_1, x_2);
return x_74;
}
else
{
unsigned char x_75; 
x_75 = 0;
x_15 = x_75;
goto lbl_16;
}
}
else
{
unsigned char x_77; 
lean::dec(x_69);
x_77 = 0;
x_15 = x_77;
goto lbl_16;
}
}
}
else
{
lean::dec(x_3);
if (x_17 == 0)
{
obj* x_80; 
lean::dec(x_11);
x_80 = _l_s9___private_2142412293__s18_mk__string__result_s6___rarg(x_1, x_2);
return x_80;
}
else
{
unsigned char x_81; 
x_81 = 0;
x_15 = x_81;
goto lbl_16;
}
}
lbl_16:
{
obj* x_82; obj* x_83; 
x_82 = lean::string_push(x_1, x_14);
x_83 = lean::string_iterator_next(x_2);
x_0 = x_11;
x_1 = x_82;
x_2 = x_83;
goto _start;
}
}
}
else
{
obj* x_88; 
lean::dec(x_4);
lean::dec(x_0);
lean::dec(x_3);
x_88 = _l_s9___private_2142412293__s18_mk__string__result_s6___rarg(x_1, x_2);
return x_88;
}
}
}
obj* _l_s9___private_31565857__s16_take__while__aux_s6___main_s4___at_s4_lean_s6_parser_s13_c__identifier_s9___spec__4(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9___private_31565857__s16_take__while__aux_s6___main_s4___at_s4_lean_s6_parser_s13_c__identifier_s9___spec__4_s6___rarg), 3, 0);
return x_2;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s17_take__while__cont_s4___at_s4_lean_s6_parser_s13_c__identifier_s9___spec__3_s6___rarg(obj* x_0, unsigned x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_5; obj* x_8; obj* x_9; 
x_2 = _l_s6_string_s4_join_s11___closed__1;
lean::inc(x_2);
x_4 = lean::string_push(x_2, x_1);
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
lean::dec(x_0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s17_take__while__cont_s4___at_s4_lean_s6_parser_s13_c__identifier_s9___spec__3_s6___rarg_s11___lambda__1), 2, 1);
lean::closure_set(x_8, 0, x_4);
x_9 = lean::apply_2(x_5, lean::box(0), x_8);
return x_9;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s17_take__while__cont_s4___at_s4_lean_s6_parser_s13_c__identifier_s9___spec__3_s6___rarg_s11___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::string_iterator_remaining(x_1);
x_3 = _l_s9___private_31565857__s16_take__while__aux_s6___main_s4___at_s4_lean_s6_parser_s13_c__identifier_s9___spec__4_s6___rarg(x_2, x_0, x_1);
return x_3;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s17_take__while__cont_s4___at_s4_lean_s6_parser_s13_c__identifier_s9___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s17_take__while__cont_s4___at_s4_lean_s6_parser_s13_c__identifier_s9___spec__3_s6___rarg_s7___boxed), 2, 0);
return x_6;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s17_take__while__cont_s4___at_s4_lean_s6_parser_s13_c__identifier_s9___spec__3_s6___rarg_s7___boxed(obj* x_0, obj* x_1) {
_start:
{
unsigned x_2; obj* x_3; 
x_2 = lean::unbox_uint32(x_1);
x_3 = _l_s4_lean_s6_parser_s13_monad__parsec_s17_take__while__cont_s4___at_s4_lean_s6_parser_s13_c__identifier_s9___spec__3_s6___rarg(x_0, x_2);
return x_3;
}
}
obj* _l_s4_lean_s6_parser_s15_cpp__identifier_s6___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_8; obj* x_12; obj* x_13; obj* x_14; obj* x_17; obj* x_20; obj* x_21; obj* x_23; 
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::inc(x_2);
lean::inc(x_1);
lean::inc(x_0);
x_8 = _l_s4_lean_s6_parser_s13_c__identifier_s6___rarg(x_0, x_1, x_2);
lean::inc(x_3);
lean::inc(x_8);
lean::inc(x_1);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s15_cpp__identifier_s6___rarg_s11___lambda__2), 6, 5);
lean::closure_set(x_12, 0, x_2);
lean::closure_set(x_12, 1, x_0);
lean::closure_set(x_12, 2, x_1);
lean::closure_set(x_12, 3, x_8);
lean::closure_set(x_12, 4, x_3);
x_13 = lean::apply_4(x_3, lean::box(0), lean::box(0), x_8, x_12);
x_14 = lean::cnstr_get(x_1, 1);
lean::inc(x_14);
lean::dec(x_1);
x_17 = _l_s4_lean_s6_parser_s13_monad__parsec_s3_try_s6___rarg_s11___closed__1;
lean::inc(x_17);
lean::inc(x_14);
x_20 = lean::apply_3(x_14, lean::box(0), x_17, x_13);
x_21 = _l_s4_lean_s6_parser_s15_cpp__identifier_s6___rarg_s11___closed__1;
lean::inc(x_21);
x_23 = lean::apply_3(x_14, lean::box(0), x_21, x_20);
return x_23;
}
}
obj* _init__l_s4_lean_s6_parser_s15_cpp__identifier_s6___rarg_s11___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_string("C++ identifier");
x_1 = lean::alloc_closure(reinterpret_cast<void*>(_l_s5_dlist_s9_singleton_s6___rarg), 2, 1);
lean::closure_set(x_1, 0, x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s6_labels_s6___rarg_s11___lambda__1), 6, 1);
lean::closure_set(x_2, 0, x_1);
return x_2;
}
}
obj* _l_s4_lean_s6_parser_s15_cpp__identifier_s6___rarg_s11___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_6; obj* x_7; obj* x_9; obj* x_10; 
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
x_6 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_6, 0, x_1);
lean::cnstr_set(x_6, 1, x_2);
x_7 = _l_s6_string_s4_join_s11___closed__1;
lean::inc(x_7);
x_9 = _l_s4_list_s5_foldl_s6___main_s4___at_s6_string_s4_join_s9___spec__1(x_7, x_6);
x_10 = lean::apply_2(x_3, lean::box(0), x_9);
return x_10;
}
}
obj* _l_s4_lean_s6_parser_s15_cpp__identifier_s6___rarg_s11___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_15; obj* x_16; obj* x_21; obj* x_22; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
x_6 = lean::cnstr_get(x_0, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_6, 2);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_6, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_10, 0);
lean::inc(x_12);
lean::dec(x_10);
x_15 = _l_s4_lean_s6_parser_s15_cpp__identifier_s6___rarg_s11___lambda__2_s11___closed__1;
x_16 = _l_s4_lean_s6_parser_s15_cpp__identifier_s6___rarg_s11___lambda__2_s11___closed__2;
lean::inc(x_16);
lean::inc(x_15);
lean::inc(x_2);
lean::inc(x_1);
x_21 = _l_s4_lean_s6_parser_s13_monad__parsec_s9_str__core_s4___at_s4_lean_s6_parser_s15_cpp__identifier_s9___spec__1_s6___rarg(x_1, x_2, x_15, x_16);
x_22 = _l_s4_lean_s6_parser_s15_cpp__identifier_s6___rarg_s11___lambda__2_s11___closed__3;
lean::inc(x_22);
x_24 = lean::apply_4(x_12, lean::box(0), lean::box(0), x_22, x_21);
x_25 = lean::apply_4(x_8, lean::box(0), lean::box(0), x_24, x_3);
x_26 = _l_s4_lean_s6_parser_s13_monad__parsec_s4_many_s6___rarg(x_1, x_2, lean::box(0), x_0, x_25);
x_27 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s15_cpp__identifier_s6___rarg_s11___lambda__1), 3, 2);
lean::closure_set(x_27, 0, x_6);
lean::closure_set(x_27, 1, x_5);
x_28 = lean::apply_4(x_4, lean::box(0), lean::box(0), x_26, x_27);
return x_28;
}
}
obj* _init__l_s4_lean_s6_parser_s15_cpp__identifier_s6___rarg_s11___lambda__2_s11___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("::");
return x_0;
}
}
obj* _init__l_s4_lean_s6_parser_s15_cpp__identifier_s6___rarg_s11___lambda__2_s11___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_string("::");
x_1 = _l_s6_string_s5_quote(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s5_dlist_s9_singleton_s6___rarg), 2, 1);
lean::closure_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init__l_s4_lean_s6_parser_s15_cpp__identifier_s6___rarg_s11___lambda__2_s11___closed__3() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(lean::string_append), 2, 0);
return x_0;
}
}
obj* _l_s4_lean_s6_parser_s15_cpp__identifier(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s15_cpp__identifier_s6___rarg), 3, 0);
return x_4;
}
}
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s9_str__core_s4___at_s4_lean_s6_parser_s15_cpp__identifier_s9___spec__1_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
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
obj* _l_s4_lean_s6_parser_s13_monad__parsec_s9_str__core_s4___at_s4_lean_s6_parser_s15_cpp__identifier_s9___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s13_monad__parsec_s9_str__core_s4___at_s4_lean_s6_parser_s15_cpp__identifier_s9___spec__1_s6___rarg), 4, 0);
return x_4;
}
}
void _l_initialize__l_s4_init_s4_data_s4_char_s5_basic();
void _l_initialize__l_s4_init_s4_lean_s6_parser_s6_parsec();
static bool _G_initialized = false;
void _l_initialize__l_s4_init_s4_lean_s6_parser_s10_identifier() {
 if (_G_initialized) return;
 _G_initialized = true;
 _l_initialize__l_s4_init_s4_data_s4_char_s5_basic();
 _l_initialize__l_s4_init_s4_lean_s6_parser_s6_parsec();
 _l_s4_lean_s17_id__begin__escape = _init__l_s4_lean_s17_id__begin__escape();
 _l_s4_lean_s15_id__end__escape = _init__l_s4_lean_s15_id__end__escape();
 _l_s4_lean_s6_parser_s8_id__part_s6___rarg_s11___closed__1 = _init__l_s4_lean_s6_parser_s8_id__part_s6___rarg_s11___closed__1();
 _l_s4_lean_s6_parser_s10_identifier_s6___rarg_s11___closed__1 = _init__l_s4_lean_s6_parser_s10_identifier_s6___rarg_s11___closed__1();
 _l_s4_lean_s6_parser_s13_c__identifier_s6___rarg_s11___closed__1 = _init__l_s4_lean_s6_parser_s13_c__identifier_s6___rarg_s11___closed__1();
 _l_s4_lean_s6_parser_s15_cpp__identifier_s6___rarg_s11___closed__1 = _init__l_s4_lean_s6_parser_s15_cpp__identifier_s6___rarg_s11___closed__1();
 _l_s4_lean_s6_parser_s15_cpp__identifier_s6___rarg_s11___lambda__2_s11___closed__1 = _init__l_s4_lean_s6_parser_s15_cpp__identifier_s6___rarg_s11___lambda__2_s11___closed__1();
 _l_s4_lean_s6_parser_s15_cpp__identifier_s6___rarg_s11___lambda__2_s11___closed__2 = _init__l_s4_lean_s6_parser_s15_cpp__identifier_s6___rarg_s11___lambda__2_s11___closed__2();
 _l_s4_lean_s6_parser_s15_cpp__identifier_s6___rarg_s11___lambda__2_s11___closed__3 = _init__l_s4_lean_s6_parser_s15_cpp__identifier_s6___rarg_s11___lambda__2_s11___closed__3();
}
