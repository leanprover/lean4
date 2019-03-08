// Lean compiler output
// Module: init.lean.parser.level
// Imports: init.lean.parser.pratt
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
obj* l_lean_parser_monad__parsec_error___at_lean_parser_level_trailing_parser_lean_parser_has__tokens___spec__2___boxed(obj*);
obj* l_lean_parser_trailing__level__parser__m_monad__except;
obj* l_lean_parser_parsec__t_bind__mk__res___rarg(obj*, obj*);
obj* l_lean_parser_trie_match__prefix___rarg(obj*, obj*);
obj* l_lean_parser_level_parser_lean_parser_has__view(obj*);
obj* l_lean_parser_level__parser_run_lean_parser_has__view(obj*);
obj* l_lean_parser_level_app_has__view_x_27___lambda__2(obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_level_trailing_parser_lean_parser_has__tokens___spec__2(obj*);
obj* l_lean_parser_number_parser___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__2___rarg(obj*, obj*, obj*);
obj* l_has__monad__lift__t__refl___boxed(obj*, obj*);
obj* l_lean_parser_trailing__level__parser__m_lean_parser_monad__parsec;
obj* l_lean_parser_level_add__lit_parser_lean_parser_has__tokens;
obj* l_lean_parser_monad__parsec_observing___at_lean_parser_peek__token___spec__2___rarg(obj*, obj*, obj*);
obj* l_lean_parser_level_trailing_has__view_x_27___lambda__1___closed__1;
obj* l_lean_parser_level_paren_has__view_x_27___lambda__2(obj*);
obj* l_lean_parser_level_leading_has__view;
namespace lean {
obj* nat_add(obj*, obj*);
}
obj* l_lean_parser_level__parser__m_lean_parser_monad__parsec;
obj* l_lean_parser_curr__lbp___at_lean_parser_level__parser_run___spec__4___boxed(obj*, obj*, obj*, obj*);
extern obj* l_mjoin___rarg___closed__1;
extern obj* l_lean_parser_basic__parser__m_monad;
obj* l_lean_parser_level_app;
obj* l_lean_parser_number_parser___at_lean_parser_level_add__lit_parser_lean_parser_has__tokens___spec__2(obj*, obj*);
obj* l_list_mfoldl___main___at_lean_parser_level_paren_parser___spec__2(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_trailing__level__parser__coe___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_rec_1__run__aux___at_lean_parser_level__parser_run___spec__7___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_level_parser(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_level_leading_has__view_x_27___lambda__1(obj*);
obj* l_lean_parser_list_cons_tokens___rarg(obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_level__parser_run___spec__3___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_number_parser___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__2(obj*);
obj* l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_reader__t_lift___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__2;
obj* l_lean_parser_parsec__t_try__mk__res___rarg(obj*);
obj* l_lean_parser_level_add__lit_parser(obj*, obj*, obj*, obj*, obj*);
obj* l_list_reverse___rarg(obj*);
extern "C" obj* lean_name_mk_string(obj*, obj*);
obj* l_reader__t_alternative___rarg(obj*, obj*);
obj* l_lean_parser_rec__t_recurse___at_lean_parser_level_parser_lean_parser_has__tokens___spec__1(obj*, obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_number_has__view_x_27___lambda__2___closed__6;
obj* l_lean_parser_combinators_node___at_lean_parser_level_paren_parser___spec__1(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_level_parser___closed__1;
obj* l_lean_parser_level__parser__m_monad__reader;
obj* l_lean_parser_parsec__t_labels__mk__res___rarg(obj*, obj*);
obj* l_lean_parser_level_add__lit_has__view_x_27___lambda__1___closed__1;
extern obj* l___private_init_lean_parser_combinators_1__many1__aux___main___rarg___closed__1;
obj* l_lean_parser_combinators_choice__aux___main___at_lean_parser_level_trailing_parser_lean_parser_has__tokens___spec__1(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_level_trailing_parser_lean_parser_has__tokens;
obj* l_id___rarg___boxed(obj*);
obj* l_lean_parser_level_paren_has__view_x_27___lambda__1___closed__1;
obj* l_lean_parser_curr__lbp___at_lean_parser_level__parser_run___spec__4(obj*, obj*, obj*, obj*);
obj* l_lean_parser_combinators_choice__aux___main___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__4(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_string_quote(obj*);
obj* l_lean_parser_symbol__or__ident___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__1;
obj* l_lean_parser_level__parser__coe;
obj* l_lean_parser_level_leading;
obj* l_lean_parser_level_get__leading(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_level_app_has__view;
obj* l_lean_parser_level_parser_lean_parser_has__view___closed__1;
obj* l_lean_parser_level__parser_run_lean_parser_has__tokens(obj*);
obj* l_lean_parser_level_app_parser_lean_parser_has__view;
obj* l_lean_parser_level__parser__m_alternative;
obj* l_lean_parser_trailing__level__parser__m_lean_parser_monad__rec;
obj* l_lean_parser_level_app_has__view_x_27___lambda__1(obj*);
obj* l_lean_parser_trailing__level__parser__m_monad;
obj* l_lean_parser_monad__parsec_error___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__5___boxed(obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__5(obj*);
obj* l_lean_parser_level_app_parser___closed__1;
obj* l_lean_parser_level_parser_lean_parser_has__tokens___closed__1;
obj* l_lean_parser_combinators_label_view___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_try__view___at_lean_parser_number_parser___spec__1(obj*);
obj* l_lean_parser_level_add__lit;
obj* l_lean_parser_level_paren;
obj* l_lean_parser_level_leading_has__view_x_27;
obj* l_lean_parser_pratt__parser___at_lean_parser_level__parser_run___spec__1___lambda__1(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
obj* l_lean_parser_level_trailing_has__view_x_27___lambda__1(obj*);
extern obj* l_lean_parser_detail__ident__part_has__view_x_27___lambda__2___closed__1;
extern obj* l_lean_parser_curr__lbp___rarg___lambda__1___closed__1;
obj* l___private_init_lean_parser_rec_1__run__aux___at_lean_parser_level__parser_run___spec__7(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_match__token___closed__1;
obj* l_lean_parser_level_trailing_has__view_x_27___lambda__2(obj*);
obj* l_lean_parser_level_leading_has__view_x_27___lambda__2___closed__1;
extern obj* l_lean_parser_detail__ident__part_has__view_x_27___lambda__2___closed__3;
extern obj* l_lean_parser_number_has__view;
obj* l_lean_parser_level__parser_run(obj*, obj*, obj*, obj*);
obj* l_lean_parser_level__parser__m_monad;
obj* l_lean_parser_level_leading_has__view_x_27___lambda__2___closed__2;
obj* l_lean_parser_tokens___rarg(obj*);
obj* l_option_get__or__else___main___rarg(obj*, obj*);
obj* l_lean_parser_level__parser_run_lean_parser_has__view___closed__1;
obj* l_lean_parser_level_trailing_parser___closed__1;
obj* l_lean_parser_syntax_as__node___main(obj*);
obj* l_lean_parser_level__parser_run_lean_parser_has__view___boxed(obj*);
obj* l_lean_parser_level_add__lit_has__view_x_27___lambda__1___closed__2;
obj* l_lean_parser_level_trailing;
obj* l_lean_parser_symbol__or__ident___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__1(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_symbol_tokens___rarg(obj*, obj*);
obj* l_lean_parser_pratt__parser___at_lean_parser_level__parser_run___spec__1(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_level_leading_parser_lean_parser_has__view;
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_level__parser_run___spec__3___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_level_lean_parser_has__tokens;
extern obj* l_lean_parser_basic__parser__m_monad__reader;
obj* l_lean_parser_trailing__level__parser__coe(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_level__parser__m_monad__except;
obj* l_lean_parser_level_trailing_parser(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_combinators_node___at_lean_parser_level_app_parser___spec__1(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_level__parser__m_lean_parser_monad__basic__parser;
obj* l_lean_parser_level_app_parser_lean_parser_has__view___lambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_combinators_node_view___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_level_app_parser_lean_parser_has__tokens;
obj* l_lean_parser_level_paren_parser___closed__1;
obj* l_lean_parser_trailing__level__parser__m_alternative;
obj* l_lean_parser_monad__parsec_error___at_lean_parser_level_trailing_parser_lean_parser_has__tokens___spec__2___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_symbol__core___at_lean_parser_level_add__lit_parser_lean_parser_has__tokens___spec__1(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_ident_parser___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__3(obj*);
extern obj* l_lean_parser_finish__comment__block___closed__2;
obj* l_lean_parser_number_parser___at_lean_parser_level_add__lit_parser_lean_parser_has__tokens___spec__2___boxed(obj*, obj*);
extern obj* l_string_join___closed__1;
obj* l_lean_parser_level_leading_parser(obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__rec_trans___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_reader__t_read___rarg(obj*, obj*);
extern obj* l_lean_parser_max__prec;
obj* l_lean_parser_rec__t_lean_parser_monad__parsec___rarg(obj*, obj*, obj*);
obj* l_lean_parser_level_app_has__view_x_27___lambda__1___closed__1;
obj* l_lean_parser_syntax_mk__node(obj*, obj*);
obj* l_lean_parser_level_add__lit_parser_lean_parser_has__view;
extern obj* l_lean_parser_detail__ident__part__escaped_has__view_x_27___lambda__2___closed__2;
obj* l_lean_parser_level_parser_lean_parser_has__tokens(obj*);
extern obj* l_lean_parser_rec__t_run__parsec___at_lean_parser_detail__ident_parser___spec__1___closed__1;
obj* l_lean_parser_symbol__core___at_lean_parser_level_paren_parser_lean_parser_has__tokens___spec__1(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_combinators_recurse_view___rarg(obj*, obj*);
obj* l_lean_parser_level_paren_parser_lean_parser_has__view;
obj* l_lean_parser_token(obj*, obj*, obj*);
obj* l_reader__t_monad__except___rarg(obj*);
obj* l_lean_parser_level_get__leading___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec__trans___rarg(obj*, obj*, obj*);
obj* l_lean_parser_level_add__lit_has__view_x_27;
obj* l_lean_parser_level_leading_parser_lean_parser_has__tokens;
obj* l_lean_parser_level_trailing_has__view_x_27___lambda__1___closed__2;
extern obj* l_lean_parser_curr__lbp___rarg___lambda__3___closed__2;
obj* l_lean_parser_level__parser__m_lean_parser_monad__rec;
obj* l_lean_parser_symbol__core___at_lean_parser_level_paren_parser_lean_parser_has__tokens___spec__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_substring_to__string(obj*);
obj* l_lean_parser_level__parser_run_lean_parser_has__view___closed__3;
obj* l_lean_parser_level_paren_parser(obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_level__parser_run___spec__3___boxed(obj*);
extern "C" uint8 lean_name_dec_eq(obj*, obj*);
obj* l_lean_parser_level__parser_run_lean_parser_has__tokens___boxed(obj*);
obj* l_lean_parser_rec__t_recurse___rarg(obj*, obj*, obj*);
namespace lean {
uint8 string_dec_eq(obj*, obj*);
}
obj* l_lean_parser_level_paren_has__view;
extern obj* l_lean_parser_combinators_choice__aux___main___rarg___closed__1;
obj* l_lean_parser_level_leading_has__view_x_27___lambda__2___closed__3;
obj* l_lean_parser_level_leading_has__view_x_27___lambda__2(obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_level__parser_run___spec__3(obj*);
obj* l_lean_parser_level__parser_run_lean_parser_has__view___closed__2;
obj* l_reader__t_monad__functor___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_number_parser___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__2___rarg___closed__1;
namespace lean {
obj* string_iterator_remaining(obj*);
}
namespace lean {
obj* string_mk_iterator(obj*);
}
extern obj* l_lean_parser_basic__parser__m_alternative;
obj* l_reader__t_lift___rarg___boxed(obj*, obj*);
obj* l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__4;
obj* l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__3;
obj* l_lean_parser_trailing__level__parser__m_monad__reader;
obj* l_lean_parser_level_add__lit_parser___closed__1;
obj* l_string_trim(obj*);
obj* l_list_mfoldl___main___at_lean_parser_level_app_parser___spec__2(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_option_get___main___at_lean_parser_run___spec__2(obj*);
extern obj* l_lean_parser_curr__lbp___rarg___lambda__3___closed__1;
obj* l_has__monad__lift__t__trans___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_ident_parser___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__3___rarg(obj*, obj*, obj*);
obj* l_reader__t_monad___rarg(obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__5___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__5;
extern "C" obj* lean_name_mk_numeral(obj*, obj*);
obj* l_lean_parser_level_add__lit_has__view;
obj* l_lean_parser_monad__parsec_error___at_lean_parser_level_trailing_parser_lean_parser_has__tokens___spec__2___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_level_app_parser(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_rec__t_run___at_lean_parser_level__parser_run___spec__6(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_pratt_1__trailing__loop___main___at_lean_parser_level__parser_run___spec__2(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_trailing__level__parser__m_lean_parser_monad__basic__parser;
obj* l_lean_parser_level_paren_has__view_x_27;
obj* l_lean_parser_pratt__parser_view___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_level_add__lit_has__view_x_27___lambda__1(obj*);
obj* l_lean_parser_level_parser_lean_parser_has__tokens___boxed(obj*);
obj* l_lean_parser_level_trailing_parser_lean_parser_has__view;
namespace lean {
obj* nat_sub(obj*, obj*);
}
obj* l_lean_parser_level_app_has__view_x_27;
obj* l_lean_parser_monad__parsec_error___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__5___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_pratt__parser___at_lean_parser_level__parser_run___spec__1___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_number_parser___at_lean_parser_level_add__lit_parser_lean_parser_has__tokens___spec__2___rarg(obj*, obj*, obj*);
extern obj* l_lean_parser_basic__parser__m_lean_parser_monad__parsec;
obj* l_lean_parser_level_add__lit_has__view_x_27___lambda__2(obj*);
obj* l_lean_parser_level_lean_parser_has__view;
obj* l_dlist_singleton___rarg(obj*, obj*);
extern obj* l_lean_parser_basic__parser__m_monad__except;
obj* l_lean_parser_level_trailing_has__view;
obj* l_lean_parser_parsec__t_orelse__mk__res___rarg(obj*, obj*);
obj* l_list_append___rarg(obj*, obj*);
obj* l_lean_parser_symbol__core___at_lean_parser_level_add__lit_parser_lean_parser_has__tokens___spec__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_level_app_parser_lean_parser_has__view___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_level_paren_has__view_x_27___lambda__1(obj*);
extern obj* l_lean_parser_number_has__view_x_27___lambda__1___closed__6;
obj* l_lean_parser_rec__t_run__parsec___at_lean_parser_level__parser_run___spec__5(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_ident_parser___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__3___rarg___closed__1;
extern obj* l_lean_parser_raw_view___rarg___lambda__2___closed__1;
obj* l_lean_parser_level_leading_parser___closed__1;
obj* l_lean_parser_substring_of__string(obj*);
obj* l___private_init_lean_parser_pratt_1__trailing__loop___main___at_lean_parser_level__parser_run___spec__2___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_number_has__view_x_27___lambda__2___closed__4;
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
obj* l_lean_parser_level_paren_parser_lean_parser_has__tokens;
obj* l_lean_parser_level_trailing_has__view_x_27;
obj* l___private_init_lean_parser_rec_1__run__aux___main___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_parser_number_parser___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__2___boxed(obj*);
obj* l_lean_parser_ident_parser___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__3___boxed(obj*);
obj* _init_l_lean_parser_level__parser__m_monad() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = l_lean_parser_basic__parser__m_monad;
x_1 = l_reader__t_monad___rarg(x_0);
return x_1;
}
}
obj* _init_l_lean_parser_level__parser__m_alternative() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = l_lean_parser_basic__parser__m_monad;
x_1 = l_lean_parser_basic__parser__m_alternative;
x_2 = l_reader__t_alternative___rarg(x_0, x_1);
return x_2;
}
}
obj* _init_l_lean_parser_level__parser__m_monad__reader() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = l_lean_parser_basic__parser__m_monad__reader;
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_lift___rarg___boxed), 2, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_lean_parser_level__parser__m_lean_parser_monad__parsec() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = l_lean_parser_basic__parser__m_monad;
x_1 = l_lean_parser_basic__parser__m_lean_parser_monad__parsec;
x_2 = l_lean_parser_rec__t_lean_parser_monad__parsec___rarg(x_0, lean::box(0), x_1);
return x_2;
}
}
obj* _init_l_lean_parser_level__parser__m_monad__except() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = l_lean_parser_basic__parser__m_monad__except;
x_1 = l_reader__t_monad__except___rarg(x_0);
return x_1;
}
}
obj* _init_l_lean_parser_level__parser__m_lean_parser_monad__rec() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = l_lean_parser_basic__parser__m_monad;
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_rec__t_recurse___rarg), 3, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_lean_parser_level__parser__m_lean_parser_monad__basic__parser() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; 
x_0 = l_lean_parser_basic__parser__m_monad;
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_lift___boxed), 4, 3);
lean::closure_set(x_1, 0, lean::box(0));
lean::closure_set(x_1, 1, lean::box(0));
lean::closure_set(x_1, 2, x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_has__monad__lift__t__refl___boxed), 2, 1);
lean::closure_set(x_2, 0, lean::box(0));
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_has__monad__lift__t__trans___rarg___boxed), 4, 2);
lean::closure_set(x_3, 0, x_1);
lean::closure_set(x_3, 1, x_2);
return x_3;
}
}
obj* _init_l_lean_parser_trailing__level__parser__m_monad() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = l_lean_parser_level__parser__m_monad;
x_1 = l_reader__t_monad___rarg(x_0);
return x_1;
}
}
obj* _init_l_lean_parser_trailing__level__parser__m_alternative() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = l_lean_parser_level__parser__m_monad;
x_1 = l_lean_parser_level__parser__m_alternative;
x_2 = l_reader__t_alternative___rarg(x_0, x_1);
return x_2;
}
}
obj* _init_l_lean_parser_trailing__level__parser__m_monad__reader() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = l_lean_parser_level__parser__m_monad;
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_read___rarg), 2, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_lean_parser_trailing__level__parser__m_lean_parser_monad__parsec() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = l_lean_parser_level__parser__m_monad;
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_lift___boxed), 4, 3);
lean::closure_set(x_1, 0, lean::box(0));
lean::closure_set(x_1, 1, lean::box(0));
lean::closure_set(x_1, 2, x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_monad__functor___boxed), 6, 5);
lean::closure_set(x_2, 0, lean::box(0));
lean::closure_set(x_2, 1, lean::box(0));
lean::closure_set(x_2, 2, lean::box(0));
lean::closure_set(x_2, 3, x_0);
lean::closure_set(x_2, 4, x_0);
x_3 = l_lean_parser_level__parser__m_lean_parser_monad__parsec;
x_4 = l_lean_parser_monad__parsec__trans___rarg(x_1, x_2, x_3);
return x_4;
}
}
obj* _init_l_lean_parser_trailing__level__parser__m_monad__except() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = l_lean_parser_level__parser__m_monad__except;
x_1 = l_reader__t_monad__except___rarg(x_0);
return x_1;
}
}
obj* _init_l_lean_parser_trailing__level__parser__m_lean_parser_monad__rec() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; 
x_0 = l_lean_parser_level__parser__m_monad;
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_lift___boxed), 4, 3);
lean::closure_set(x_1, 0, lean::box(0));
lean::closure_set(x_1, 1, lean::box(0));
lean::closure_set(x_1, 2, x_0);
x_2 = l_lean_parser_level__parser__m_lean_parser_monad__rec;
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__rec_trans___rarg___boxed), 4, 3);
lean::closure_set(x_3, 0, x_1);
lean::closure_set(x_3, 1, x_2);
lean::closure_set(x_3, 2, x_0);
return x_3;
}
}
obj* _init_l_lean_parser_trailing__level__parser__m_lean_parser_monad__basic__parser() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; 
x_0 = l_lean_parser_level__parser__m_monad;
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_lift___boxed), 4, 3);
lean::closure_set(x_1, 0, lean::box(0));
lean::closure_set(x_1, 1, lean::box(0));
lean::closure_set(x_1, 2, x_0);
x_2 = l_lean_parser_level__parser__m_lean_parser_monad__basic__parser;
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_has__monad__lift__t__trans___rarg___boxed), 4, 2);
lean::closure_set(x_3, 0, x_1);
lean::closure_set(x_3, 1, x_2);
return x_3;
}
}
obj* l_lean_parser_trailing__level__parser__coe(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = lean::apply_4(x_0, x_2, x_3, x_4, x_5);
return x_6;
}
}
obj* l_lean_parser_trailing__level__parser__coe___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_lean_parser_trailing__level__parser__coe(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_1);
return x_6;
}
}
obj* l_lean_parser_rec__t_recurse___at_lean_parser_level_parser_lean_parser_has__tokens___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
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
obj* _init_l_lean_parser_level_parser_lean_parser_has__tokens___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(0);
x_1 = l_lean_parser_tokens___rarg(x_0);
return x_1;
}
}
obj* l_lean_parser_level_parser_lean_parser_has__tokens(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_level_parser_lean_parser_has__tokens___closed__1;
return x_1;
}
}
obj* l_lean_parser_level_parser_lean_parser_has__tokens___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_level_parser_lean_parser_has__tokens(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_lean_parser_level_parser_lean_parser_has__view___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("universe level");
return x_0;
}
}
obj* l_lean_parser_level_parser_lean_parser_has__view(obj* x_0) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
lean::inc(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_rec__t_recurse___at_lean_parser_level_parser_lean_parser_has__tokens___spec__1), 5, 1);
lean::closure_set(x_2, 0, x_0);
x_3 = l_lean_parser_level__parser__m_lean_parser_monad__rec;
x_4 = l_lean_parser_combinators_recurse_view___rarg(x_0, x_3);
lean::dec(x_0);
x_6 = l_lean_parser_level__parser__m_lean_parser_monad__parsec;
x_7 = l_lean_parser_level__parser__m_alternative;
x_8 = l_lean_parser_level_parser_lean_parser_has__view___closed__1;
x_9 = l_lean_parser_combinators_label_view___rarg(x_6, x_7, x_2, x_8, x_4);
lean::dec(x_2);
return x_9;
}
}
obj* _init_l_lean_parser_level_parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("universe level");
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_lean_parser_level_parser(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_8; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_5 = l_lean_parser_rec__t_recurse___at_lean_parser_level_parser_lean_parser_has__tokens___spec__1(x_0, x_1, x_2, x_3, x_4);
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
x_11 = l_lean_parser_level_parser___closed__1;
x_12 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_6, x_11);
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
obj* l_lean_parser_level_get__leading(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_6 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_6, 0, x_0);
lean::cnstr_set(x_6, 1, x_3);
lean::cnstr_set(x_6, 2, x_5);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_4);
return x_7;
}
}
obj* l_lean_parser_level_get__leading___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_lean_parser_level_get__leading(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
lean::dec(x_2);
return x_5;
}
}
obj* _init_l_lean_parser_level_lean_parser_has__tokens() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* _init_l_lean_parser_level_lean_parser_has__view() {
_start:
{
obj* x_0; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_id___rarg___boxed), 1, 0);
lean::inc(x_0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_0);
return x_2;
}
}
obj* _init_l_lean_parser_level_paren() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("level");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("paren");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_lean_parser_level_paren_has__view_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_4; obj* x_5; obj* x_7; obj* x_8; 
x_7 = lean::box(0);
x_8 = lean::box(3);
x_4 = x_7;
x_5 = x_8;
goto lbl_6;
lbl_3:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_9; obj* x_10; 
x_9 = lean::box(0);
x_10 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_10, 0, x_0);
lean::cnstr_set(x_10, 1, x_1);
lean::cnstr_set(x_10, 2, x_9);
return x_10;
}
else
{
obj* x_11; 
x_11 = lean::cnstr_get(x_2, 0);
lean::inc(x_11);
lean::dec(x_2);
switch (lean::obj_tag(x_11)) {
case 0:
{
obj* x_14; obj* x_17; obj* x_18; 
x_14 = lean::cnstr_get(x_11, 0);
lean::inc(x_14);
lean::dec(x_11);
x_17 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_17, 0, x_14);
x_18 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_18, 0, x_0);
lean::cnstr_set(x_18, 1, x_1);
lean::cnstr_set(x_18, 2, x_17);
return x_18;
}
case 3:
{
obj* x_19; obj* x_20; 
x_19 = lean::box(0);
x_20 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_20, 0, x_0);
lean::cnstr_set(x_20, 1, x_1);
lean::cnstr_set(x_20, 2, x_19);
return x_20;
}
default:
{
obj* x_22; obj* x_23; 
lean::dec(x_11);
x_22 = lean::box(0);
x_23 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_23, 0, x_0);
lean::cnstr_set(x_23, 1, x_1);
lean::cnstr_set(x_23, 2, x_22);
return x_23;
}
}
}
}
lbl_6:
{
obj* x_24; 
switch (lean::obj_tag(x_5)) {
case 0:
{
obj* x_26; obj* x_29; 
x_26 = lean::cnstr_get(x_5, 0);
lean::inc(x_26);
lean::dec(x_5);
x_29 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_29, 0, x_26);
if (lean::obj_tag(x_4) == 0)
{
x_24 = x_29;
goto lbl_25;
}
else
{
obj* x_30; obj* x_32; 
x_30 = lean::cnstr_get(x_4, 0);
lean::inc(x_30);
x_32 = lean::cnstr_get(x_4, 1);
lean::inc(x_32);
lean::dec(x_4);
x_0 = x_29;
x_1 = x_30;
x_2 = x_32;
goto lbl_3;
}
}
case 3:
{
obj* x_35; 
x_35 = lean::box(0);
if (lean::obj_tag(x_4) == 0)
{
x_24 = x_35;
goto lbl_25;
}
else
{
obj* x_36; obj* x_38; 
x_36 = lean::cnstr_get(x_4, 0);
lean::inc(x_36);
x_38 = lean::cnstr_get(x_4, 1);
lean::inc(x_38);
lean::dec(x_4);
x_0 = x_35;
x_1 = x_36;
x_2 = x_38;
goto lbl_3;
}
}
default:
{
obj* x_42; 
lean::dec(x_5);
x_42 = lean::box(0);
if (lean::obj_tag(x_4) == 0)
{
x_24 = x_42;
goto lbl_25;
}
else
{
obj* x_43; obj* x_45; 
x_43 = lean::cnstr_get(x_4, 0);
lean::inc(x_43);
x_45 = lean::cnstr_get(x_4, 1);
lean::inc(x_45);
lean::dec(x_4);
x_0 = x_42;
x_1 = x_43;
x_2 = x_45;
goto lbl_3;
}
}
}
lbl_25:
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_48; obj* x_49; obj* x_50; 
x_48 = lean::box(0);
x_49 = lean::box(3);
x_50 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_50, 0, x_24);
lean::cnstr_set(x_50, 1, x_49);
lean::cnstr_set(x_50, 2, x_48);
return x_50;
}
else
{
obj* x_51; 
x_51 = lean::cnstr_get(x_4, 0);
lean::inc(x_51);
lean::dec(x_4);
switch (lean::obj_tag(x_51)) {
case 0:
{
obj* x_54; obj* x_57; obj* x_58; obj* x_59; 
x_54 = lean::cnstr_get(x_51, 0);
lean::inc(x_54);
lean::dec(x_51);
x_57 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_57, 0, x_54);
x_58 = lean::box(3);
x_59 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_59, 0, x_24);
lean::cnstr_set(x_59, 1, x_58);
lean::cnstr_set(x_59, 2, x_57);
return x_59;
}
case 3:
{
obj* x_60; obj* x_61; obj* x_62; 
x_60 = lean::box(0);
x_61 = lean::box(3);
x_62 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_62, 0, x_24);
lean::cnstr_set(x_62, 1, x_61);
lean::cnstr_set(x_62, 2, x_60);
return x_62;
}
default:
{
obj* x_64; obj* x_65; obj* x_66; 
lean::dec(x_51);
x_64 = lean::box(0);
x_65 = lean::box(3);
x_66 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_66, 0, x_24);
lean::cnstr_set(x_66, 1, x_65);
lean::cnstr_set(x_66, 2, x_64);
return x_66;
}
}
}
}
}
}
}
obj* l_lean_parser_level_paren_has__view_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_5; obj* x_6; obj* x_8; 
x_8 = l_lean_parser_syntax_as__node___main(x_0);
if (lean::obj_tag(x_8) == 0)
{
obj* x_9; 
x_9 = l_lean_parser_level_paren_has__view_x_27___lambda__1___closed__1;
return x_9;
}
else
{
obj* x_10; obj* x_13; 
x_10 = lean::cnstr_get(x_8, 0);
lean::inc(x_10);
lean::dec(x_8);
x_13 = lean::cnstr_get(x_10, 1);
lean::inc(x_13);
lean::dec(x_10);
if (lean::obj_tag(x_13) == 0)
{
obj* x_16; 
x_16 = lean::box(3);
x_5 = x_13;
x_6 = x_16;
goto lbl_7;
}
else
{
obj* x_17; obj* x_19; 
x_17 = lean::cnstr_get(x_13, 0);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_13, 1);
lean::inc(x_19);
lean::dec(x_13);
x_5 = x_19;
x_6 = x_17;
goto lbl_7;
}
}
lbl_4:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_22; obj* x_23; 
x_22 = lean::box(0);
x_23 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_23, 0, x_1);
lean::cnstr_set(x_23, 1, x_2);
lean::cnstr_set(x_23, 2, x_22);
return x_23;
}
else
{
obj* x_24; 
x_24 = lean::cnstr_get(x_3, 0);
lean::inc(x_24);
lean::dec(x_3);
switch (lean::obj_tag(x_24)) {
case 0:
{
obj* x_27; obj* x_30; obj* x_31; 
x_27 = lean::cnstr_get(x_24, 0);
lean::inc(x_27);
lean::dec(x_24);
x_30 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_30, 0, x_27);
x_31 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_31, 0, x_1);
lean::cnstr_set(x_31, 1, x_2);
lean::cnstr_set(x_31, 2, x_30);
return x_31;
}
case 3:
{
obj* x_32; obj* x_33; 
x_32 = lean::box(0);
x_33 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_33, 0, x_1);
lean::cnstr_set(x_33, 1, x_2);
lean::cnstr_set(x_33, 2, x_32);
return x_33;
}
default:
{
obj* x_35; obj* x_36; 
lean::dec(x_24);
x_35 = lean::box(0);
x_36 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_36, 0, x_1);
lean::cnstr_set(x_36, 1, x_2);
lean::cnstr_set(x_36, 2, x_35);
return x_36;
}
}
}
}
lbl_7:
{
obj* x_37; 
switch (lean::obj_tag(x_6)) {
case 0:
{
obj* x_39; obj* x_42; 
x_39 = lean::cnstr_get(x_6, 0);
lean::inc(x_39);
lean::dec(x_6);
x_42 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_42, 0, x_39);
if (lean::obj_tag(x_5) == 0)
{
x_37 = x_42;
goto lbl_38;
}
else
{
obj* x_43; obj* x_45; 
x_43 = lean::cnstr_get(x_5, 0);
lean::inc(x_43);
x_45 = lean::cnstr_get(x_5, 1);
lean::inc(x_45);
lean::dec(x_5);
x_1 = x_42;
x_2 = x_43;
x_3 = x_45;
goto lbl_4;
}
}
case 3:
{
obj* x_48; 
x_48 = lean::box(0);
if (lean::obj_tag(x_5) == 0)
{
x_37 = x_48;
goto lbl_38;
}
else
{
obj* x_49; obj* x_51; 
x_49 = lean::cnstr_get(x_5, 0);
lean::inc(x_49);
x_51 = lean::cnstr_get(x_5, 1);
lean::inc(x_51);
lean::dec(x_5);
x_1 = x_48;
x_2 = x_49;
x_3 = x_51;
goto lbl_4;
}
}
default:
{
obj* x_55; 
lean::dec(x_6);
x_55 = lean::box(0);
if (lean::obj_tag(x_5) == 0)
{
x_37 = x_55;
goto lbl_38;
}
else
{
obj* x_56; obj* x_58; 
x_56 = lean::cnstr_get(x_5, 0);
lean::inc(x_56);
x_58 = lean::cnstr_get(x_5, 1);
lean::inc(x_58);
lean::dec(x_5);
x_1 = x_55;
x_2 = x_56;
x_3 = x_58;
goto lbl_4;
}
}
}
lbl_38:
{
if (lean::obj_tag(x_5) == 0)
{
obj* x_61; obj* x_62; obj* x_63; 
x_61 = lean::box(0);
x_62 = lean::box(3);
x_63 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_63, 0, x_37);
lean::cnstr_set(x_63, 1, x_62);
lean::cnstr_set(x_63, 2, x_61);
return x_63;
}
else
{
obj* x_64; 
x_64 = lean::cnstr_get(x_5, 0);
lean::inc(x_64);
lean::dec(x_5);
switch (lean::obj_tag(x_64)) {
case 0:
{
obj* x_67; obj* x_70; obj* x_71; obj* x_72; 
x_67 = lean::cnstr_get(x_64, 0);
lean::inc(x_67);
lean::dec(x_64);
x_70 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_70, 0, x_67);
x_71 = lean::box(3);
x_72 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_72, 0, x_37);
lean::cnstr_set(x_72, 1, x_71);
lean::cnstr_set(x_72, 2, x_70);
return x_72;
}
case 3:
{
obj* x_73; obj* x_74; obj* x_75; 
x_73 = lean::box(0);
x_74 = lean::box(3);
x_75 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_75, 0, x_37);
lean::cnstr_set(x_75, 1, x_74);
lean::cnstr_set(x_75, 2, x_73);
return x_75;
}
default:
{
obj* x_77; obj* x_78; obj* x_79; 
lean::dec(x_64);
x_77 = lean::box(0);
x_78 = lean::box(3);
x_79 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_79, 0, x_37);
lean::cnstr_set(x_79, 1, x_78);
lean::cnstr_set(x_79, 2, x_77);
return x_79;
}
}
}
}
}
}
}
obj* l_lean_parser_level_paren_has__view_x_27___lambda__2(obj* x_0) {
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
if (lean::obj_tag(x_5) == 0)
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_9 = l_lean_parser_detail__ident__part__escaped_has__view_x_27___lambda__2___closed__2;
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_3);
lean::cnstr_set(x_10, 1, x_9);
x_11 = l_lean_parser_raw_view___rarg___lambda__2___closed__1;
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_10);
x_13 = l_lean_parser_level_paren;
x_14 = l_lean_parser_syntax_mk__node(x_13, x_12);
return x_14;
}
else
{
obj* x_15; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
x_15 = lean::cnstr_get(x_5, 0);
if (lean::is_exclusive(x_5)) {
 x_17 = x_5;
} else {
 lean::inc(x_15);
 lean::dec(x_5);
 x_17 = lean::box(0);
}
x_18 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_18, 0, x_15);
if (lean::is_scalar(x_17)) {
 x_19 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_19 = x_17;
}
lean::cnstr_set(x_19, 0, x_18);
x_20 = lean::box(3);
x_21 = l_option_get__or__else___main___rarg(x_19, x_20);
lean::dec(x_19);
x_23 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_23, 0, x_21);
lean::cnstr_set(x_23, 1, x_8);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_3);
lean::cnstr_set(x_24, 1, x_23);
x_25 = l_lean_parser_raw_view___rarg___lambda__2___closed__1;
x_26 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_24);
x_27 = l_lean_parser_level_paren;
x_28 = l_lean_parser_syntax_mk__node(x_27, x_26);
return x_28;
}
}
else
{
obj* x_29; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; 
x_29 = lean::cnstr_get(x_1, 0);
if (lean::is_exclusive(x_1)) {
 x_31 = x_1;
} else {
 lean::inc(x_29);
 lean::dec(x_1);
 x_31 = lean::box(0);
}
x_32 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_32, 0, x_29);
if (lean::is_scalar(x_31)) {
 x_33 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_33 = x_31;
}
lean::cnstr_set(x_33, 0, x_32);
x_34 = lean::box(3);
x_35 = l_option_get__or__else___main___rarg(x_33, x_34);
lean::dec(x_33);
if (lean::obj_tag(x_5) == 0)
{
obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; 
x_37 = l_lean_parser_detail__ident__part__escaped_has__view_x_27___lambda__2___closed__2;
x_38 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_38, 0, x_3);
lean::cnstr_set(x_38, 1, x_37);
x_39 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_39, 0, x_35);
lean::cnstr_set(x_39, 1, x_38);
x_40 = l_lean_parser_level_paren;
x_41 = l_lean_parser_syntax_mk__node(x_40, x_39);
return x_41;
}
else
{
obj* x_42; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; 
x_42 = lean::cnstr_get(x_5, 0);
if (lean::is_exclusive(x_5)) {
 x_44 = x_5;
} else {
 lean::inc(x_42);
 lean::dec(x_5);
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
x_47 = l_option_get__or__else___main___rarg(x_46, x_34);
lean::dec(x_46);
x_49 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_49, 0, x_47);
lean::cnstr_set(x_49, 1, x_8);
x_50 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_50, 0, x_3);
lean::cnstr_set(x_50, 1, x_49);
x_51 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_51, 0, x_35);
lean::cnstr_set(x_51, 1, x_50);
x_52 = l_lean_parser_level_paren;
x_53 = l_lean_parser_syntax_mk__node(x_52, x_51);
return x_53;
}
}
}
}
obj* _init_l_lean_parser_level_paren_has__view_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_level_paren_has__view_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_level_paren_has__view_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_lean_parser_level_paren_has__view() {
_start:
{
obj* x_0; 
x_0 = l_lean_parser_level_paren_has__view_x_27;
return x_0;
}
}
obj* l_lean_parser_symbol__core___at_lean_parser_level_paren_parser_lean_parser_has__tokens___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_9; obj* x_10; obj* x_12; obj* x_14; obj* x_16; 
lean::inc(x_5);
lean::inc(x_4);
x_9 = l_lean_parser_token(x_4, x_5, x_6);
x_10 = lean::cnstr_get(x_9, 0);
x_12 = lean::cnstr_get(x_9, 1);
if (lean::is_exclusive(x_9)) {
 lean::cnstr_set(x_9, 0, lean::box(0));
 lean::cnstr_set(x_9, 1, lean::box(0));
 x_14 = x_9;
} else {
 lean::inc(x_10);
 lean::inc(x_12);
 lean::dec(x_9);
 x_14 = lean::box(0);
}
lean::inc(x_0);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_16, 0, x_0);
if (lean::obj_tag(x_10) == 0)
{
obj* x_17; obj* x_19; obj* x_21; obj* x_23; obj* x_24; 
x_17 = lean::cnstr_get(x_10, 0);
x_19 = lean::cnstr_get(x_10, 1);
x_21 = lean::cnstr_get(x_10, 2);
if (lean::is_exclusive(x_10)) {
 lean::cnstr_set(x_10, 0, lean::box(0));
 lean::cnstr_set(x_10, 1, lean::box(0));
 lean::cnstr_set(x_10, 2, lean::box(0));
 x_23 = x_10;
} else {
 lean::inc(x_17);
 lean::inc(x_19);
 lean::inc(x_21);
 lean::dec(x_10);
 x_23 = lean::box(0);
}
switch (lean::obj_tag(x_17)) {
case 0:
{
obj* x_26; obj* x_28; uint8 x_31; 
x_26 = lean::cnstr_get(x_17, 0);
lean::inc(x_26);
x_28 = lean::cnstr_get(x_26, 1);
lean::inc(x_28);
lean::dec(x_26);
x_31 = lean::string_dec_eq(x_0, x_28);
lean::dec(x_0);
if (x_31 == 0)
{
obj* x_35; obj* x_36; obj* x_37; obj* x_41; 
lean::dec(x_23);
lean::dec(x_14);
x_35 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_35, 0, x_5);
x_36 = lean::box(0);
x_37 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_28, x_2, x_35, x_36, x_4, x_19, x_12);
lean::dec(x_19);
lean::dec(x_4);
lean::dec(x_35);
x_41 = lean::cnstr_get(x_37, 0);
lean::inc(x_41);
if (lean::obj_tag(x_41) == 0)
{
obj* x_43; obj* x_45; obj* x_46; obj* x_48; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; 
x_43 = lean::cnstr_get(x_37, 1);
if (lean::is_exclusive(x_37)) {
 lean::cnstr_release(x_37, 0);
 x_45 = x_37;
} else {
 lean::inc(x_43);
 lean::dec(x_37);
 x_45 = lean::box(0);
}
x_46 = lean::cnstr_get(x_41, 1);
x_48 = lean::cnstr_get(x_41, 2);
if (lean::is_exclusive(x_41)) {
 lean::cnstr_release(x_41, 0);
 x_50 = x_41;
} else {
 lean::inc(x_46);
 lean::inc(x_48);
 lean::dec(x_41);
 x_50 = lean::box(0);
}
x_51 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_50)) {
 x_52 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_52 = x_50;
}
lean::cnstr_set(x_52, 0, x_17);
lean::cnstr_set(x_52, 1, x_46);
lean::cnstr_set(x_52, 2, x_51);
x_53 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_48, x_52);
x_54 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_21, x_53);
x_55 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_51, x_54);
x_56 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_55, x_16);
x_57 = l_lean_parser_parsec__t_try__mk__res___rarg(x_56);
if (lean::is_scalar(x_45)) {
 x_58 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_58 = x_45;
}
lean::cnstr_set(x_58, 0, x_57);
lean::cnstr_set(x_58, 1, x_43);
return x_58;
}
else
{
obj* x_60; obj* x_62; obj* x_63; uint8 x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; 
lean::dec(x_17);
x_60 = lean::cnstr_get(x_37, 1);
if (lean::is_exclusive(x_37)) {
 lean::cnstr_release(x_37, 0);
 x_62 = x_37;
} else {
 lean::inc(x_60);
 lean::dec(x_37);
 x_62 = lean::box(0);
}
x_63 = lean::cnstr_get(x_41, 0);
x_65 = lean::cnstr_get_scalar<uint8>(x_41, sizeof(void*)*1);
if (lean::is_exclusive(x_41)) {
 x_66 = x_41;
} else {
 lean::inc(x_63);
 lean::dec(x_41);
 x_66 = lean::box(0);
}
if (lean::is_scalar(x_66)) {
 x_67 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_67 = x_66;
}
lean::cnstr_set(x_67, 0, x_63);
lean::cnstr_set_scalar(x_67, sizeof(void*)*1, x_65);
x_68 = x_67;
x_69 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_21, x_68);
x_70 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_71 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_70, x_69);
x_72 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_71, x_16);
x_73 = l_lean_parser_parsec__t_try__mk__res___rarg(x_72);
if (lean::is_scalar(x_62)) {
 x_74 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_74 = x_62;
}
lean::cnstr_set(x_74, 0, x_73);
lean::cnstr_set(x_74, 1, x_60);
return x_74;
}
}
else
{
obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_86; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_2);
lean::dec(x_28);
x_79 = l_lean_parser_finish__comment__block___closed__2;
if (lean::is_scalar(x_23)) {
 x_80 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_80 = x_23;
}
lean::cnstr_set(x_80, 0, x_17);
lean::cnstr_set(x_80, 1, x_19);
lean::cnstr_set(x_80, 2, x_79);
x_81 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_21, x_80);
x_82 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_83 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_82, x_81);
x_84 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_83, x_16);
x_85 = l_lean_parser_parsec__t_try__mk__res___rarg(x_84);
if (lean::is_scalar(x_14)) {
 x_86 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_86 = x_14;
}
lean::cnstr_set(x_86, 0, x_85);
lean::cnstr_set(x_86, 1, x_12);
return x_86;
}
}
case 3:
{
obj* x_90; 
lean::dec(x_23);
lean::dec(x_14);
lean::dec(x_0);
x_90 = lean::box(0);
x_24 = x_90;
goto lbl_25;
}
default:
{
obj* x_95; 
lean::dec(x_23);
lean::dec(x_14);
lean::dec(x_0);
lean::dec(x_17);
x_95 = lean::box(0);
x_24 = x_95;
goto lbl_25;
}
}
lbl_25:
{
obj* x_97; obj* x_98; obj* x_99; obj* x_100; obj* x_104; obj* x_106; obj* x_108; obj* x_109; obj* x_110; obj* x_111; obj* x_112; obj* x_113; obj* x_114; 
lean::dec(x_24);
x_97 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_97, 0, x_5);
x_98 = lean::box(0);
x_99 = l_string_join___closed__1;
x_100 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_99, x_2, x_97, x_98, x_4, x_19, x_12);
lean::dec(x_19);
lean::dec(x_4);
lean::dec(x_97);
x_104 = lean::cnstr_get(x_100, 0);
x_106 = lean::cnstr_get(x_100, 1);
if (lean::is_exclusive(x_100)) {
 x_108 = x_100;
} else {
 lean::inc(x_104);
 lean::inc(x_106);
 lean::dec(x_100);
 x_108 = lean::box(0);
}
x_109 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_21, x_104);
x_110 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_111 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_110, x_109);
x_112 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_111, x_16);
x_113 = l_lean_parser_parsec__t_try__mk__res___rarg(x_112);
if (lean::is_scalar(x_108)) {
 x_114 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_114 = x_108;
}
lean::cnstr_set(x_114, 0, x_113);
lean::cnstr_set(x_114, 1, x_106);
return x_114;
}
}
else
{
obj* x_119; uint8 x_121; obj* x_122; obj* x_123; obj* x_124; obj* x_125; obj* x_126; obj* x_127; obj* x_128; obj* x_129; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_0);
lean::dec(x_2);
x_119 = lean::cnstr_get(x_10, 0);
x_121 = lean::cnstr_get_scalar<uint8>(x_10, sizeof(void*)*1);
if (lean::is_exclusive(x_10)) {
 x_122 = x_10;
} else {
 lean::inc(x_119);
 lean::dec(x_10);
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
x_125 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_126 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_125, x_124);
x_127 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_126, x_16);
x_128 = l_lean_parser_parsec__t_try__mk__res___rarg(x_127);
if (lean::is_scalar(x_14)) {
 x_129 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_129 = x_14;
}
lean::cnstr_set(x_129, 0, x_128);
lean::cnstr_set(x_129, 1, x_12);
return x_129;
}
}
}
obj* _init_l_lean_parser_level_paren_parser_lean_parser_has__tokens() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_15; 
x_0 = lean::mk_string("(");
x_1 = l_lean_parser_max__prec;
x_2 = l_lean_parser_symbol_tokens___rarg(x_0, x_1);
x_3 = lean::mk_string(")");
x_4 = lean::mk_nat_obj(0u);
x_5 = l_lean_parser_symbol_tokens___rarg(x_3, x_4);
x_6 = lean::box(0);
x_7 = l_lean_parser_list_cons_tokens___rarg(x_5, x_6);
lean::dec(x_5);
x_9 = l_lean_parser_level_parser_lean_parser_has__tokens___closed__1;
x_10 = l_lean_parser_list_cons_tokens___rarg(x_9, x_7);
lean::dec(x_7);
x_12 = l_lean_parser_list_cons_tokens___rarg(x_2, x_10);
lean::dec(x_10);
lean::dec(x_2);
x_15 = l_lean_parser_tokens___rarg(x_12);
lean::dec(x_12);
return x_15;
}
}
obj* l_lean_parser_symbol__core___at_lean_parser_level_paren_parser_lean_parser_has__tokens___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_lean_parser_symbol__core___at_lean_parser_level_paren_parser_lean_parser_has__tokens___spec__1(x_0, x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_1);
lean::dec(x_3);
return x_7;
}
}
obj* _init_l_lean_parser_level_paren_parser_lean_parser_has__view() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
x_0 = lean::mk_string("(");
x_1 = l_string_trim(x_0);
lean::inc(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_3, 0, x_1);
x_4 = l_lean_parser_max__prec;
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_level_paren_parser_lean_parser_has__tokens___spec__1___boxed), 7, 3);
lean::closure_set(x_5, 0, x_1);
lean::closure_set(x_5, 1, x_4);
lean::closure_set(x_5, 2, x_3);
x_6 = lean::mk_nat_obj(0u);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_level_parser), 5, 1);
lean::closure_set(x_7, 0, x_6);
x_8 = lean::mk_string(")");
x_9 = l_string_trim(x_8);
lean::inc(x_9);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_11, 0, x_9);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_level_paren_parser_lean_parser_has__tokens___spec__1___boxed), 7, 3);
lean::closure_set(x_12, 0, x_9);
lean::closure_set(x_12, 1, x_6);
lean::closure_set(x_12, 2, x_11);
x_13 = lean::box(0);
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_12);
lean::cnstr_set(x_14, 1, x_13);
x_15 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_15, 0, x_7);
lean::cnstr_set(x_15, 1, x_14);
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_5);
lean::cnstr_set(x_16, 1, x_15);
x_17 = l_lean_parser_level__parser__m_monad;
x_18 = l_lean_parser_level__parser__m_monad__except;
x_19 = l_lean_parser_level__parser__m_lean_parser_monad__parsec;
x_20 = l_lean_parser_level__parser__m_alternative;
x_21 = l_lean_parser_level_paren;
x_22 = l_lean_parser_level_paren_has__view;
x_23 = l_lean_parser_combinators_node_view___rarg(x_17, x_18, x_19, x_20, x_21, x_16, x_22);
lean::dec(x_16);
return x_23;
}
}
obj* l_list_mfoldl___main___at_lean_parser_level_paren_parser___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
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
x_94 = l_list_mfoldl___main___at_lean_parser_level_paren_parser___spec__2(x_0, x_87, x_15, x_3, x_4, x_89, x_19);
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
obj* l_lean_parser_combinators_node___at_lean_parser_level_paren_parser___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_8; obj* x_9; 
x_6 = lean::box(0);
lean::inc(x_0);
x_8 = l_list_mfoldl___main___at_lean_parser_level_paren_parser___spec__2(x_0, x_6, x_1, x_2, x_3, x_4, x_5);
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
obj* _init_l_lean_parser_level_paren_parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_0 = lean::mk_string("(");
x_1 = l_string_trim(x_0);
lean::inc(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_3, 0, x_1);
x_4 = l_lean_parser_max__prec;
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_level_paren_parser_lean_parser_has__tokens___spec__1___boxed), 7, 3);
lean::closure_set(x_5, 0, x_1);
lean::closure_set(x_5, 1, x_4);
lean::closure_set(x_5, 2, x_3);
x_6 = lean::mk_nat_obj(0u);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_level_parser), 5, 1);
lean::closure_set(x_7, 0, x_6);
x_8 = lean::mk_string(")");
x_9 = l_string_trim(x_8);
lean::inc(x_9);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_11, 0, x_9);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_level_paren_parser_lean_parser_has__tokens___spec__1___boxed), 7, 3);
lean::closure_set(x_12, 0, x_9);
lean::closure_set(x_12, 1, x_6);
lean::closure_set(x_12, 2, x_11);
x_13 = lean::box(0);
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_12);
lean::cnstr_set(x_14, 1, x_13);
x_15 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_15, 0, x_7);
lean::cnstr_set(x_15, 1, x_14);
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_5);
lean::cnstr_set(x_16, 1, x_15);
return x_16;
}
}
obj* l_lean_parser_level_paren_parser(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = l_lean_parser_level_paren;
x_5 = l_lean_parser_level_paren_parser___closed__1;
x_6 = l_lean_parser_combinators_node___at_lean_parser_level_paren_parser___spec__1(x_4, x_5, x_0, x_1, x_2, x_3);
return x_6;
}
}
obj* _init_l_lean_parser_level_leading() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("level");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("leading");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
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
x_8 = lean::alloc_cnstr(5, 1, 0);
lean::cnstr_set(x_8, 0, x_7);
return x_8;
}
}
obj* _init_l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; 
x_0 = l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__1;
return x_0;
}
}
obj* _init_l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__3() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(0);
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__4() {
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
if (x_10 == 0)
{
obj* x_11; uint8 x_12; 
x_11 = lean::mk_nat_obj(3u);
x_12 = lean::nat_dec_eq(x_1, x_11);
if (x_12 == 0)
{
obj* x_13; uint8 x_14; 
x_13 = lean::mk_nat_obj(4u);
x_14 = lean::nat_dec_eq(x_1, x_13);
lean::dec(x_1);
if (x_14 == 0)
{
switch (lean::obj_tag(x_0)) {
case 1:
{
obj* x_16; obj* x_19; 
x_16 = lean::cnstr_get(x_0, 0);
lean::inc(x_16);
lean::dec(x_0);
x_19 = lean::alloc_cnstr(5, 1, 0);
lean::cnstr_set(x_19, 0, x_16);
return x_19;
}
case 3:
{
obj* x_20; 
x_20 = l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__2;
return x_20;
}
default:
{
obj* x_22; 
lean::dec(x_0);
x_22 = l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__2;
return x_22;
}
}
}
else
{
obj* x_23; obj* x_24; obj* x_27; obj* x_28; 
x_23 = l_lean_parser_number_has__view;
x_24 = lean::cnstr_get(x_23, 0);
lean::inc(x_24);
lean::dec(x_23);
x_27 = lean::apply_1(x_24, x_0);
x_28 = lean::alloc_cnstr(4, 1, 0);
lean::cnstr_set(x_28, 0, x_27);
return x_28;
}
}
else
{
obj* x_30; obj* x_31; obj* x_34; obj* x_35; 
lean::dec(x_1);
x_30 = l_lean_parser_level_paren_has__view;
x_31 = lean::cnstr_get(x_30, 0);
lean::inc(x_31);
lean::dec(x_30);
x_34 = lean::apply_1(x_31, x_0);
x_35 = lean::alloc_cnstr(3, 1, 0);
lean::cnstr_set(x_35, 0, x_34);
return x_35;
}
}
else
{
lean::dec(x_1);
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_37; obj* x_40; obj* x_41; 
x_37 = lean::cnstr_get(x_0, 0);
lean::inc(x_37);
lean::dec(x_0);
x_40 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_40, 0, x_37);
x_41 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_41, 0, x_40);
return x_41;
}
case 3:
{
obj* x_42; 
x_42 = l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__3;
return x_42;
}
default:
{
obj* x_44; 
lean::dec(x_0);
x_44 = l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__3;
return x_44;
}
}
}
}
else
{
obj* x_46; 
lean::dec(x_1);
x_46 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_46, 0, x_0);
return x_46;
}
}
else
{
obj* x_48; 
lean::dec(x_1);
x_48 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_48, 0, x_0);
return x_48;
}
}
}
}
obj* _init_l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__5() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("level");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("leading");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* l_lean_parser_level_leading_has__view_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_4 = l_lean_parser_syntax_as__node___main(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; 
x_5 = l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__4;
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
x_14 = l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__5;
x_15 = lean_name_dec_eq(x_9, x_14);
lean::dec(x_9);
if (x_15 == 0)
{
obj* x_18; 
lean::dec(x_11);
x_18 = l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__4;
return x_18;
}
else
{
if (lean::obj_tag(x_11) == 0)
{
obj* x_19; 
x_19 = l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__4;
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
x_26 = l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__4;
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
x_33 = l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__4;
return x_33;
}
case 1:
{
obj* x_36; 
lean::dec(x_27);
lean::dec(x_30);
x_36 = l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__4;
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
x_50 = l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__4;
return x_50;
}
else
{
if (lean::obj_tag(x_37) == 0)
{
obj* x_52; 
lean::dec(x_42);
x_52 = l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__4;
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
x_61 = l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__4;
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
x_64 = l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__4;
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
if (x_70 == 0)
{
obj* x_71; uint8 x_72; 
x_71 = lean::mk_nat_obj(3u);
x_72 = lean::nat_dec_eq(x_2, x_71);
if (x_72 == 0)
{
obj* x_73; uint8 x_74; 
x_73 = lean::mk_nat_obj(4u);
x_74 = lean::nat_dec_eq(x_2, x_73);
lean::dec(x_2);
if (x_74 == 0)
{
switch (lean::obj_tag(x_1)) {
case 1:
{
obj* x_76; obj* x_79; 
x_76 = lean::cnstr_get(x_1, 0);
lean::inc(x_76);
lean::dec(x_1);
x_79 = lean::alloc_cnstr(5, 1, 0);
lean::cnstr_set(x_79, 0, x_76);
return x_79;
}
case 3:
{
obj* x_80; 
x_80 = l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__2;
return x_80;
}
default:
{
obj* x_82; 
lean::dec(x_1);
x_82 = l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__2;
return x_82;
}
}
}
else
{
obj* x_83; obj* x_84; obj* x_87; obj* x_88; 
x_83 = l_lean_parser_number_has__view;
x_84 = lean::cnstr_get(x_83, 0);
lean::inc(x_84);
lean::dec(x_83);
x_87 = lean::apply_1(x_84, x_1);
x_88 = lean::alloc_cnstr(4, 1, 0);
lean::cnstr_set(x_88, 0, x_87);
return x_88;
}
}
else
{
obj* x_90; obj* x_91; obj* x_94; obj* x_95; 
lean::dec(x_2);
x_90 = l_lean_parser_level_paren_has__view;
x_91 = lean::cnstr_get(x_90, 0);
lean::inc(x_91);
lean::dec(x_90);
x_94 = lean::apply_1(x_91, x_1);
x_95 = lean::alloc_cnstr(3, 1, 0);
lean::cnstr_set(x_95, 0, x_94);
return x_95;
}
}
else
{
lean::dec(x_2);
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_97; obj* x_100; obj* x_101; 
x_97 = lean::cnstr_get(x_1, 0);
lean::inc(x_97);
lean::dec(x_1);
x_100 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_100, 0, x_97);
x_101 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_101, 0, x_100);
return x_101;
}
case 3:
{
obj* x_102; 
x_102 = l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__3;
return x_102;
}
default:
{
obj* x_104; 
lean::dec(x_1);
x_104 = l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__3;
return x_104;
}
}
}
}
else
{
obj* x_106; 
lean::dec(x_2);
x_106 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_106, 0, x_1);
return x_106;
}
}
else
{
obj* x_108; 
lean::dec(x_2);
x_108 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_108, 0, x_1);
return x_108;
}
}
}
}
obj* _init_l_lean_parser_level_leading_has__view_x_27___lambda__2___closed__1() {
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
x_10 = l_lean_parser_level_leading;
x_11 = l_lean_parser_syntax_mk__node(x_10, x_9);
return x_11;
}
}
obj* _init_l_lean_parser_level_leading_has__view_x_27___lambda__2___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_nat_obj(4u);
x_2 = lean_name_mk_numeral(x_0, x_1);
return x_2;
}
}
obj* _init_l_lean_parser_level_leading_has__view_x_27___lambda__2___closed__3() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_nat_obj(5u);
x_2 = lean_name_mk_numeral(x_0, x_1);
return x_2;
}
}
obj* l_lean_parser_level_leading_has__view_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::box(0);
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_2; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
x_5 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_5, 0, x_2);
lean::cnstr_set(x_5, 1, x_1);
x_6 = l_lean_parser_detail__ident__part_has__view_x_27___lambda__2___closed__1;
x_7 = l_lean_parser_syntax_mk__node(x_6, x_5);
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_1);
x_9 = l_lean_parser_level_leading;
x_10 = l_lean_parser_syntax_mk__node(x_9, x_8);
return x_10;
}
case 1:
{
obj* x_11; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_11 = lean::cnstr_get(x_0, 0);
lean::inc(x_11);
lean::dec(x_0);
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_11);
lean::cnstr_set(x_14, 1, x_1);
x_15 = l_lean_parser_detail__ident__part_has__view_x_27___lambda__2___closed__3;
x_16 = l_lean_parser_syntax_mk__node(x_15, x_14);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_1);
x_18 = l_lean_parser_level_leading;
x_19 = l_lean_parser_syntax_mk__node(x_18, x_17);
return x_19;
}
case 2:
{
obj* x_20; 
x_20 = lean::cnstr_get(x_0, 0);
lean::inc(x_20);
lean::dec(x_0);
if (lean::obj_tag(x_20) == 0)
{
obj* x_23; 
x_23 = l_lean_parser_level_leading_has__view_x_27___lambda__2___closed__1;
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
x_33 = l_lean_parser_number_has__view_x_27___lambda__2___closed__4;
x_34 = l_lean_parser_syntax_mk__node(x_33, x_32);
x_35 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_1);
x_36 = l_lean_parser_level_leading;
x_37 = l_lean_parser_syntax_mk__node(x_36, x_35);
return x_37;
}
}
case 3:
{
obj* x_38; obj* x_41; obj* x_42; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; 
x_38 = lean::cnstr_get(x_0, 0);
lean::inc(x_38);
lean::dec(x_0);
x_41 = l_lean_parser_level_paren_has__view;
x_42 = lean::cnstr_get(x_41, 1);
lean::inc(x_42);
lean::dec(x_41);
x_45 = lean::apply_1(x_42, x_38);
x_46 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_46, 0, x_45);
lean::cnstr_set(x_46, 1, x_1);
x_47 = l_lean_parser_number_has__view_x_27___lambda__2___closed__6;
x_48 = l_lean_parser_syntax_mk__node(x_47, x_46);
x_49 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_49, 0, x_48);
lean::cnstr_set(x_49, 1, x_1);
x_50 = l_lean_parser_level_leading;
x_51 = l_lean_parser_syntax_mk__node(x_50, x_49);
return x_51;
}
case 4:
{
obj* x_52; obj* x_55; obj* x_56; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; 
x_52 = lean::cnstr_get(x_0, 0);
lean::inc(x_52);
lean::dec(x_0);
x_55 = l_lean_parser_number_has__view;
x_56 = lean::cnstr_get(x_55, 1);
lean::inc(x_56);
lean::dec(x_55);
x_59 = lean::apply_1(x_56, x_52);
x_60 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_60, 0, x_59);
lean::cnstr_set(x_60, 1, x_1);
x_61 = l_lean_parser_level_leading_has__view_x_27___lambda__2___closed__2;
x_62 = l_lean_parser_syntax_mk__node(x_61, x_60);
x_63 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_63, 0, x_62);
lean::cnstr_set(x_63, 1, x_1);
x_64 = l_lean_parser_level_leading;
x_65 = l_lean_parser_syntax_mk__node(x_64, x_63);
return x_65;
}
default:
{
obj* x_66; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; 
x_66 = lean::cnstr_get(x_0, 0);
lean::inc(x_66);
lean::dec(x_0);
x_69 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_69, 0, x_66);
x_70 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_70, 0, x_69);
lean::cnstr_set(x_70, 1, x_1);
x_71 = l_lean_parser_level_leading_has__view_x_27___lambda__2___closed__3;
x_72 = l_lean_parser_syntax_mk__node(x_71, x_70);
x_73 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_73, 0, x_72);
lean::cnstr_set(x_73, 1, x_1);
x_74 = l_lean_parser_level_leading;
x_75 = l_lean_parser_syntax_mk__node(x_74, x_73);
return x_75;
}
}
}
}
obj* _init_l_lean_parser_level_leading_has__view_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_level_leading_has__view_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_level_leading_has__view_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_lean_parser_level_leading_has__view() {
_start:
{
obj* x_0; 
x_0 = l_lean_parser_level_leading_has__view_x_27;
return x_0;
}
}
obj* l_lean_parser_symbol__or__ident___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_7; obj* x_8; 
lean::inc(x_3);
lean::inc(x_2);
x_7 = l_lean_parser_token(x_2, x_3, x_4);
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
if (lean::obj_tag(x_8) == 0)
{
obj* x_10; obj* x_12; obj* x_13; obj* x_15; obj* x_17; obj* x_19; obj* x_20; 
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
switch (lean::obj_tag(x_13)) {
case 0:
{
obj* x_22; obj* x_24; obj* x_27; 
x_22 = lean::cnstr_get(x_13, 0);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_22, 1);
lean::inc(x_24);
lean::dec(x_22);
x_27 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_27, 0, x_24);
x_20 = x_27;
goto lbl_21;
}
case 1:
{
obj* x_28; obj* x_30; obj* x_33; obj* x_35; 
x_28 = lean::cnstr_get(x_13, 0);
lean::inc(x_28);
x_30 = lean::cnstr_get(x_28, 1);
lean::inc(x_30);
lean::dec(x_28);
x_33 = l_lean_parser_substring_to__string(x_30);
lean::dec(x_30);
x_35 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_35, 0, x_33);
x_20 = x_35;
goto lbl_21;
}
default:
{
obj* x_36; 
x_36 = lean::box(0);
x_20 = x_36;
goto lbl_21;
}
}
lbl_21:
{
uint8 x_37; 
if (lean::obj_tag(x_20) == 0)
{
uint8 x_39; 
x_39 = 1;
x_37 = x_39;
goto lbl_38;
}
else
{
obj* x_40; uint8 x_43; 
x_40 = lean::cnstr_get(x_20, 0);
lean::inc(x_40);
lean::dec(x_20);
x_43 = lean::string_dec_eq(x_40, x_0);
lean::dec(x_40);
if (x_43 == 0)
{
uint8 x_45; 
x_45 = 1;
x_37 = x_45;
goto lbl_38;
}
else
{
uint8 x_46; 
x_46 = 0;
x_37 = x_46;
goto lbl_38;
}
}
lbl_38:
{
if (x_37 == 0)
{
obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
x_50 = l_lean_parser_finish__comment__block___closed__2;
if (lean::is_scalar(x_19)) {
 x_51 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_51 = x_19;
}
lean::cnstr_set(x_51, 0, x_13);
lean::cnstr_set(x_51, 1, x_15);
lean::cnstr_set(x_51, 2, x_50);
x_52 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_17, x_51);
x_53 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_54 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_53, x_52);
x_55 = l_lean_parser_parsec__t_try__mk__res___rarg(x_54);
if (lean::is_scalar(x_12)) {
 x_56 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_56 = x_12;
}
lean::cnstr_set(x_56, 0, x_55);
lean::cnstr_set(x_56, 1, x_10);
return x_56;
}
else
{
obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_68; 
lean::dec(x_12);
lean::dec(x_19);
x_59 = l_string_quote(x_0);
x_60 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_60, 0, x_59);
x_61 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_61, 0, x_3);
x_62 = lean::box(0);
x_63 = l_string_join___closed__1;
x_64 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_63, x_60, x_61, x_62, x_2, x_15, x_10);
lean::dec(x_15);
lean::dec(x_2);
lean::dec(x_61);
x_68 = lean::cnstr_get(x_64, 0);
lean::inc(x_68);
if (lean::obj_tag(x_68) == 0)
{
obj* x_70; obj* x_72; obj* x_73; obj* x_75; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; 
x_70 = lean::cnstr_get(x_64, 1);
if (lean::is_exclusive(x_64)) {
 lean::cnstr_release(x_64, 0);
 x_72 = x_64;
} else {
 lean::inc(x_70);
 lean::dec(x_64);
 x_72 = lean::box(0);
}
x_73 = lean::cnstr_get(x_68, 1);
x_75 = lean::cnstr_get(x_68, 2);
if (lean::is_exclusive(x_68)) {
 lean::cnstr_release(x_68, 0);
 x_77 = x_68;
} else {
 lean::inc(x_73);
 lean::inc(x_75);
 lean::dec(x_68);
 x_77 = lean::box(0);
}
x_78 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_77)) {
 x_79 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_79 = x_77;
}
lean::cnstr_set(x_79, 0, x_13);
lean::cnstr_set(x_79, 1, x_73);
lean::cnstr_set(x_79, 2, x_78);
x_80 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_75, x_79);
x_81 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_17, x_80);
x_82 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_78, x_81);
x_83 = l_lean_parser_parsec__t_try__mk__res___rarg(x_82);
if (lean::is_scalar(x_72)) {
 x_84 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_84 = x_72;
}
lean::cnstr_set(x_84, 0, x_83);
lean::cnstr_set(x_84, 1, x_70);
return x_84;
}
else
{
obj* x_86; obj* x_88; obj* x_89; uint8 x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_95; obj* x_96; obj* x_97; obj* x_98; obj* x_99; 
lean::dec(x_13);
x_86 = lean::cnstr_get(x_64, 1);
if (lean::is_exclusive(x_64)) {
 lean::cnstr_release(x_64, 0);
 x_88 = x_64;
} else {
 lean::inc(x_86);
 lean::dec(x_64);
 x_88 = lean::box(0);
}
x_89 = lean::cnstr_get(x_68, 0);
x_91 = lean::cnstr_get_scalar<uint8>(x_68, sizeof(void*)*1);
if (lean::is_exclusive(x_68)) {
 x_92 = x_68;
} else {
 lean::inc(x_89);
 lean::dec(x_68);
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
x_95 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_17, x_94);
x_96 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_97 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_96, x_95);
x_98 = l_lean_parser_parsec__t_try__mk__res___rarg(x_97);
if (lean::is_scalar(x_88)) {
 x_99 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_99 = x_88;
}
lean::cnstr_set(x_99, 0, x_98);
lean::cnstr_set(x_99, 1, x_86);
return x_99;
}
}
}
}
}
else
{
obj* x_103; obj* x_105; obj* x_106; uint8 x_108; obj* x_109; obj* x_110; obj* x_111; obj* x_112; obj* x_113; obj* x_114; obj* x_115; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
x_103 = lean::cnstr_get(x_7, 1);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 x_105 = x_7;
} else {
 lean::inc(x_103);
 lean::dec(x_7);
 x_105 = lean::box(0);
}
x_106 = lean::cnstr_get(x_8, 0);
x_108 = lean::cnstr_get_scalar<uint8>(x_8, sizeof(void*)*1);
if (lean::is_exclusive(x_8)) {
 x_109 = x_8;
} else {
 lean::inc(x_106);
 lean::dec(x_8);
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
x_112 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_113 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_112, x_111);
x_114 = l_lean_parser_parsec__t_try__mk__res___rarg(x_113);
if (lean::is_scalar(x_105)) {
 x_115 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_115 = x_105;
}
lean::cnstr_set(x_115, 0, x_114);
lean::cnstr_set(x_115, 1, x_103);
return x_115;
}
}
}
obj* _init_l_lean_parser_number_parser___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__2___rarg___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("number");
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_lean_parser_number_parser___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2) {
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
obj* x_8; obj* x_10; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_19; 
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
lean::inc(x_11);
x_19 = l_lean_parser_try__view___at_lean_parser_number_parser___spec__1(x_11);
if (lean::obj_tag(x_19) == 0)
{
obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_31; obj* x_33; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; 
lean::dec(x_17);
lean::dec(x_10);
lean::dec(x_11);
x_23 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_23, 0, x_1);
x_24 = lean::box(0);
x_25 = l_string_join___closed__1;
x_26 = l_lean_parser_number_parser___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__2___rarg___closed__1;
x_27 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_25, x_26, x_23, x_24, x_0, x_13, x_8);
lean::dec(x_13);
lean::dec(x_0);
lean::dec(x_23);
x_31 = lean::cnstr_get(x_27, 0);
x_33 = lean::cnstr_get(x_27, 1);
if (lean::is_exclusive(x_27)) {
 x_35 = x_27;
} else {
 lean::inc(x_31);
 lean::inc(x_33);
 lean::dec(x_27);
 x_35 = lean::box(0);
}
x_36 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_37 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_36, x_31);
x_38 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_37);
x_39 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_36, x_38);
x_40 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_39, x_26);
x_41 = l_lean_parser_parsec__t_try__mk__res___rarg(x_40);
if (lean::is_scalar(x_35)) {
 x_42 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_42 = x_35;
}
lean::cnstr_set(x_42, 0, x_41);
lean::cnstr_set(x_42, 1, x_33);
return x_42;
}
else
{
obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_19);
x_46 = l_lean_parser_finish__comment__block___closed__2;
if (lean::is_scalar(x_17)) {
 x_47 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_47 = x_17;
}
lean::cnstr_set(x_47, 0, x_11);
lean::cnstr_set(x_47, 1, x_13);
lean::cnstr_set(x_47, 2, x_46);
x_48 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_47);
x_49 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_50 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_49, x_48);
x_51 = l_lean_parser_number_parser___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__2___rarg___closed__1;
x_52 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_50, x_51);
x_53 = l_lean_parser_parsec__t_try__mk__res___rarg(x_52);
if (lean::is_scalar(x_10)) {
 x_54 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_54 = x_10;
}
lean::cnstr_set(x_54, 0, x_53);
lean::cnstr_set(x_54, 1, x_8);
return x_54;
}
}
else
{
obj* x_57; obj* x_59; obj* x_60; uint8 x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; 
lean::dec(x_1);
lean::dec(x_0);
x_57 = lean::cnstr_get(x_5, 1);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 x_59 = x_5;
} else {
 lean::inc(x_57);
 lean::dec(x_5);
 x_59 = lean::box(0);
}
x_60 = lean::cnstr_get(x_6, 0);
x_62 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*1);
if (lean::is_exclusive(x_6)) {
 x_63 = x_6;
} else {
 lean::inc(x_60);
 lean::dec(x_6);
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
x_68 = l_lean_parser_number_parser___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__2___rarg___closed__1;
x_69 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_67, x_68);
x_70 = l_lean_parser_parsec__t_try__mk__res___rarg(x_69);
if (lean::is_scalar(x_59)) {
 x_71 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_71 = x_59;
}
lean::cnstr_set(x_71, 0, x_70);
lean::cnstr_set(x_71, 1, x_57);
return x_71;
}
}
}
obj* l_lean_parser_number_parser___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__2(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_number_parser___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__2___rarg), 3, 0);
return x_1;
}
}
obj* _init_l_lean_parser_ident_parser___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__3___rarg___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("identifier");
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_lean_parser_ident_parser___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__3___rarg(obj* x_0, obj* x_1, obj* x_2) {
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
x_26 = l_lean_parser_ident_parser___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__3___rarg___closed__1;
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
x_41 = l_lean_parser_ident_parser___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__3___rarg___closed__1;
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
x_70 = l_lean_parser_ident_parser___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__3___rarg___closed__1;
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
obj* l_lean_parser_ident_parser___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__3(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_ident_parser___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__3___rarg), 3, 0);
return x_1;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__5___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
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
obj* l_lean_parser_monad__parsec_error___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__5(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__5___rarg___boxed), 8, 0);
return x_1;
}
}
obj* l_lean_parser_combinators_choice__aux___main___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__4(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
lean::dec(x_1);
x_7 = lean::box(0);
x_8 = l_lean_parser_combinators_choice__aux___main___rarg___closed__1;
x_9 = l_mjoin___rarg___closed__1;
x_10 = l_lean_parser_monad__parsec_error___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__5___rarg(x_8, x_9, x_7, x_7, x_2, x_3, x_4, x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
return x_10;
}
else
{
obj* x_14; obj* x_16; obj* x_18; obj* x_22; obj* x_23; obj* x_25; obj* x_27; obj* x_28; obj* x_29; 
x_14 = lean::cnstr_get(x_0, 0);
x_16 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 x_18 = x_0;
} else {
 lean::inc(x_14);
 lean::inc(x_16);
 lean::dec(x_0);
 x_18 = lean::box(0);
}
lean::inc(x_4);
lean::inc(x_3);
lean::inc(x_2);
x_22 = lean::apply_4(x_14, x_2, x_3, x_4, x_5);
x_23 = lean::cnstr_get(x_22, 0);
x_25 = lean::cnstr_get(x_22, 1);
if (lean::is_exclusive(x_22)) {
 lean::cnstr_set(x_22, 0, lean::box(0));
 lean::cnstr_set(x_22, 1, lean::box(0));
 x_27 = x_22;
} else {
 lean::inc(x_23);
 lean::inc(x_25);
 lean::dec(x_22);
 x_27 = lean::box(0);
}
x_28 = lean::mk_nat_obj(1u);
x_29 = lean::nat_add(x_1, x_28);
if (lean::obj_tag(x_23) == 0)
{
obj* x_30; obj* x_32; obj* x_34; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; 
x_30 = lean::cnstr_get(x_23, 0);
x_32 = lean::cnstr_get(x_23, 1);
x_34 = lean::cnstr_get(x_23, 2);
if (lean::is_exclusive(x_23)) {
 x_36 = x_23;
} else {
 lean::inc(x_30);
 lean::inc(x_32);
 lean::inc(x_34);
 lean::dec(x_23);
 x_36 = lean::box(0);
}
x_37 = lean::box(0);
x_38 = lean_name_mk_numeral(x_37, x_1);
x_39 = lean::box(0);
if (lean::is_scalar(x_18)) {
 x_40 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_40 = x_18;
}
lean::cnstr_set(x_40, 0, x_30);
lean::cnstr_set(x_40, 1, x_39);
x_41 = l_lean_parser_syntax_mk__node(x_38, x_40);
x_42 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_36)) {
 x_43 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_43 = x_36;
}
lean::cnstr_set(x_43, 0, x_41);
lean::cnstr_set(x_43, 1, x_32);
lean::cnstr_set(x_43, 2, x_42);
x_44 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_34, x_43);
if (lean::obj_tag(x_44) == 0)
{
obj* x_50; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_29);
lean::dec(x_16);
if (lean::is_scalar(x_27)) {
 x_50 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_50 = x_27;
}
lean::cnstr_set(x_50, 0, x_44);
lean::cnstr_set(x_50, 1, x_25);
return x_50;
}
else
{
uint8 x_51; 
x_51 = lean::cnstr_get_scalar<uint8>(x_44, sizeof(void*)*1);
if (x_51 == 0)
{
obj* x_53; obj* x_56; obj* x_57; obj* x_59; obj* x_61; obj* x_62; obj* x_63; 
lean::dec(x_27);
x_53 = lean::cnstr_get(x_44, 0);
lean::inc(x_53);
lean::dec(x_44);
x_56 = l_lean_parser_combinators_choice__aux___main___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__4(x_16, x_29, x_2, x_3, x_4, x_25);
x_57 = lean::cnstr_get(x_56, 0);
x_59 = lean::cnstr_get(x_56, 1);
if (lean::is_exclusive(x_56)) {
 x_61 = x_56;
} else {
 lean::inc(x_57);
 lean::inc(x_59);
 lean::dec(x_56);
 x_61 = lean::box(0);
}
x_62 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_53, x_57);
if (lean::is_scalar(x_61)) {
 x_63 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_63 = x_61;
}
lean::cnstr_set(x_63, 0, x_62);
lean::cnstr_set(x_63, 1, x_59);
return x_63;
}
else
{
obj* x_69; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_29);
lean::dec(x_16);
if (lean::is_scalar(x_27)) {
 x_69 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_69 = x_27;
}
lean::cnstr_set(x_69, 0, x_44);
lean::cnstr_set(x_69, 1, x_25);
return x_69;
}
}
}
else
{
uint8 x_72; 
lean::dec(x_1);
lean::dec(x_18);
x_72 = lean::cnstr_get_scalar<uint8>(x_23, sizeof(void*)*1);
if (x_72 == 0)
{
obj* x_74; obj* x_77; obj* x_78; obj* x_80; obj* x_82; obj* x_83; obj* x_84; 
lean::dec(x_27);
x_74 = lean::cnstr_get(x_23, 0);
lean::inc(x_74);
lean::dec(x_23);
x_77 = l_lean_parser_combinators_choice__aux___main___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__4(x_16, x_29, x_2, x_3, x_4, x_25);
x_78 = lean::cnstr_get(x_77, 0);
x_80 = lean::cnstr_get(x_77, 1);
if (lean::is_exclusive(x_77)) {
 x_82 = x_77;
} else {
 lean::inc(x_78);
 lean::inc(x_80);
 lean::dec(x_77);
 x_82 = lean::box(0);
}
x_83 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_74, x_78);
if (lean::is_scalar(x_82)) {
 x_84 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_84 = x_82;
}
lean::cnstr_set(x_84, 0, x_83);
lean::cnstr_set(x_84, 1, x_80);
return x_84;
}
else
{
obj* x_90; obj* x_92; obj* x_93; obj* x_94; obj* x_95; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_29);
lean::dec(x_16);
x_90 = lean::cnstr_get(x_23, 0);
if (lean::is_exclusive(x_23)) {
 x_92 = x_23;
} else {
 lean::inc(x_90);
 lean::dec(x_23);
 x_92 = lean::box(0);
}
if (lean::is_scalar(x_92)) {
 x_93 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_93 = x_92;
}
lean::cnstr_set(x_93, 0, x_90);
lean::cnstr_set_scalar(x_93, sizeof(void*)*1, x_72);
x_94 = x_93;
if (lean::is_scalar(x_27)) {
 x_95 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_95 = x_27;
}
lean::cnstr_set(x_95, 0, x_94);
lean::cnstr_set(x_95, 1, x_25);
return x_95;
}
}
}
}
}
obj* _init_l_lean_parser_level_leading_parser_lean_parser_has__tokens() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_7; obj* x_8; obj* x_10; obj* x_13; obj* x_15; obj* x_17; obj* x_19; obj* x_21; 
x_0 = lean::box(0);
x_1 = lean::mk_string("_");
x_2 = l_lean_parser_max__prec;
x_3 = l_lean_parser_symbol_tokens___rarg(x_1, x_2);
x_4 = l_lean_parser_list_cons_tokens___rarg(x_0, x_0);
x_5 = l_lean_parser_list_cons_tokens___rarg(x_0, x_4);
lean::dec(x_4);
x_7 = l_lean_parser_level_paren_parser_lean_parser_has__tokens;
x_8 = l_lean_parser_list_cons_tokens___rarg(x_7, x_5);
lean::dec(x_5);
x_10 = l_lean_parser_list_cons_tokens___rarg(x_3, x_8);
lean::dec(x_8);
lean::dec(x_3);
x_13 = l_lean_parser_list_cons_tokens___rarg(x_0, x_10);
lean::dec(x_10);
x_15 = l_lean_parser_list_cons_tokens___rarg(x_0, x_13);
lean::dec(x_13);
x_17 = l_lean_parser_tokens___rarg(x_15);
lean::dec(x_15);
x_19 = l_lean_parser_list_cons_tokens___rarg(x_17, x_0);
lean::dec(x_17);
x_21 = l_lean_parser_tokens___rarg(x_19);
lean::dec(x_19);
return x_21;
}
}
obj* l_lean_parser_symbol__or__ident___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_lean_parser_symbol__or__ident___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__1(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
return x_5;
}
}
obj* l_lean_parser_number_parser___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__2___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_number_parser___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__2(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_parser_ident_parser___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__3___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_ident_parser___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__3(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__5___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = l_lean_parser_monad__parsec_error___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__5___rarg(x_0, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean::dec(x_2);
lean::dec(x_4);
lean::dec(x_5);
lean::dec(x_6);
return x_8;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__5___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_monad__parsec_error___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__5(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_lean_parser_level_leading_parser_lean_parser_has__view() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
x_0 = lean::mk_string("max");
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__or__ident___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__1___boxed), 5, 1);
lean::closure_set(x_1, 0, x_0);
x_2 = lean::mk_string("imax");
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__or__ident___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__1___boxed), 5, 1);
lean::closure_set(x_3, 0, x_2);
x_4 = lean::mk_string("_");
x_5 = l_string_trim(x_4);
lean::inc(x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_7, 0, x_5);
x_8 = l_lean_parser_max__prec;
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_level_paren_parser_lean_parser_has__tokens___spec__1___boxed), 7, 3);
lean::closure_set(x_9, 0, x_5);
lean::closure_set(x_9, 1, x_8);
lean::closure_set(x_9, 2, x_7);
x_10 = lean::box(0);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_ident_parser___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__3___boxed), 1, 0);
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_10);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_number_parser___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__2___boxed), 1, 0);
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_12);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_level_paren_parser), 4, 0);
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_15);
lean::cnstr_set(x_16, 1, x_14);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_9);
lean::cnstr_set(x_17, 1, x_16);
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_3);
lean::cnstr_set(x_18, 1, x_17);
x_19 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_19, 0, x_1);
lean::cnstr_set(x_19, 1, x_18);
x_20 = lean::mk_nat_obj(0u);
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_choice__aux___main___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__4), 6, 2);
lean::closure_set(x_21, 0, x_19);
lean::closure_set(x_21, 1, x_20);
x_22 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_10);
x_23 = l_lean_parser_level__parser__m_monad;
x_24 = l_lean_parser_level__parser__m_monad__except;
x_25 = l_lean_parser_level__parser__m_lean_parser_monad__parsec;
x_26 = l_lean_parser_level__parser__m_alternative;
x_27 = l_lean_parser_level_leading;
x_28 = l_lean_parser_level_leading_has__view;
x_29 = l_lean_parser_combinators_node_view___rarg(x_23, x_24, x_25, x_26, x_27, x_22, x_28);
lean::dec(x_22);
return x_29;
}
}
obj* _init_l_lean_parser_level_leading_parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_0 = lean::mk_string("max");
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__or__ident___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__1___boxed), 5, 1);
lean::closure_set(x_1, 0, x_0);
x_2 = lean::mk_string("imax");
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__or__ident___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__1___boxed), 5, 1);
lean::closure_set(x_3, 0, x_2);
x_4 = lean::mk_string("_");
x_5 = l_string_trim(x_4);
lean::inc(x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_7, 0, x_5);
x_8 = l_lean_parser_max__prec;
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_level_paren_parser_lean_parser_has__tokens___spec__1___boxed), 7, 3);
lean::closure_set(x_9, 0, x_5);
lean::closure_set(x_9, 1, x_8);
lean::closure_set(x_9, 2, x_7);
x_10 = lean::box(0);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_ident_parser___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__3___boxed), 1, 0);
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_10);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_number_parser___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__2___boxed), 1, 0);
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_12);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_level_paren_parser), 4, 0);
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_15);
lean::cnstr_set(x_16, 1, x_14);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_9);
lean::cnstr_set(x_17, 1, x_16);
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_3);
lean::cnstr_set(x_18, 1, x_17);
x_19 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_19, 0, x_1);
lean::cnstr_set(x_19, 1, x_18);
x_20 = lean::mk_nat_obj(0u);
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_choice__aux___main___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__4), 6, 2);
lean::closure_set(x_21, 0, x_19);
lean::closure_set(x_21, 1, x_20);
x_22 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_10);
return x_22;
}
}
obj* l_lean_parser_level_leading_parser(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = l_lean_parser_level_leading;
x_5 = l_lean_parser_level_leading_parser___closed__1;
x_6 = l_lean_parser_combinators_node___at_lean_parser_level_paren_parser___spec__1(x_4, x_5, x_0, x_1, x_2, x_3);
return x_6;
}
}
obj* _init_l_lean_parser_level_app() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("level");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("app");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_lean_parser_level_app_has__view_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(3);
x_1 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_1, 0, x_0);
lean::cnstr_set(x_1, 1, x_0);
return x_1;
}
}
obj* l_lean_parser_level_app_has__view_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_syntax_as__node___main(x_0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; 
x_2 = l_lean_parser_level_app_has__view_x_27___lambda__1___closed__1;
return x_2;
}
else
{
obj* x_3; obj* x_6; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
lean::dec(x_1);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
lean::dec(x_3);
if (lean::obj_tag(x_6) == 0)
{
if (lean::obj_tag(x_6) == 0)
{
obj* x_9; 
x_9 = l_lean_parser_level_app_has__view_x_27___lambda__1___closed__1;
return x_9;
}
else
{
obj* x_10; obj* x_13; obj* x_14; 
x_10 = lean::cnstr_get(x_6, 0);
lean::inc(x_10);
lean::dec(x_6);
x_13 = lean::box(3);
x_14 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_10);
return x_14;
}
}
else
{
obj* x_15; 
x_15 = lean::cnstr_get(x_6, 1);
lean::inc(x_15);
if (lean::obj_tag(x_15) == 0)
{
obj* x_17; obj* x_20; obj* x_21; 
x_17 = lean::cnstr_get(x_6, 0);
lean::inc(x_17);
lean::dec(x_6);
x_20 = lean::box(3);
x_21 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_21, 0, x_17);
lean::cnstr_set(x_21, 1, x_20);
return x_21;
}
else
{
obj* x_22; obj* x_25; obj* x_28; 
x_22 = lean::cnstr_get(x_6, 0);
lean::inc(x_22);
lean::dec(x_6);
x_25 = lean::cnstr_get(x_15, 0);
lean::inc(x_25);
lean::dec(x_15);
x_28 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_28, 0, x_22);
lean::cnstr_set(x_28, 1, x_25);
return x_28;
}
}
}
}
}
obj* l_lean_parser_level_app_has__view_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
x_6 = lean::box(0);
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_3);
lean::cnstr_set(x_7, 1, x_6);
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_1);
lean::cnstr_set(x_8, 1, x_7);
x_9 = l_lean_parser_level_app;
x_10 = l_lean_parser_syntax_mk__node(x_9, x_8);
return x_10;
}
}
obj* _init_l_lean_parser_level_app_has__view_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_level_app_has__view_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_level_app_has__view_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_lean_parser_level_app_has__view() {
_start:
{
obj* x_0; 
x_0 = l_lean_parser_level_app_has__view_x_27;
return x_0;
}
}
obj* _init_l_lean_parser_level_app_parser_lean_parser_has__tokens() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_5; obj* x_6; obj* x_8; 
x_0 = l_lean_parser_level_parser_lean_parser_has__tokens___closed__1;
x_1 = l_lean_parser_tokens___rarg(x_0);
x_2 = lean::box(0);
x_3 = l_lean_parser_list_cons_tokens___rarg(x_1, x_2);
lean::dec(x_1);
x_5 = l_lean_parser_level_lean_parser_has__tokens;
x_6 = l_lean_parser_list_cons_tokens___rarg(x_5, x_3);
lean::dec(x_3);
x_8 = l_lean_parser_tokens___rarg(x_6);
lean::dec(x_6);
return x_8;
}
}
obj* l_lean_parser_level_app_parser_lean_parser_has__view___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; 
x_5 = l_lean_parser_max__prec;
x_6 = l_lean_parser_level_parser(x_5, x_1, x_2, x_3, x_4);
return x_6;
}
}
obj* _init_l_lean_parser_level_app_parser_lean_parser_has__view() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_0 = lean::box(0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_level_app_parser_lean_parser_has__view___lambda__1___boxed), 5, 0);
x_2 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_2, 0, x_1);
lean::cnstr_set(x_2, 1, x_0);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_level_get__leading___boxed), 5, 0);
x_4 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_2);
x_5 = l_lean_parser_trailing__level__parser__m_monad;
x_6 = l_lean_parser_trailing__level__parser__m_monad__except;
x_7 = l_lean_parser_trailing__level__parser__m_lean_parser_monad__parsec;
x_8 = l_lean_parser_trailing__level__parser__m_alternative;
x_9 = l_lean_parser_level_app;
x_10 = l_lean_parser_level_app_has__view;
x_11 = l_lean_parser_combinators_node_view___rarg(x_5, x_6, x_7, x_8, x_9, x_4, x_10);
lean::dec(x_4);
return x_11;
}
}
obj* l_lean_parser_level_app_parser_lean_parser_has__view___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_lean_parser_level_app_parser_lean_parser_has__view___lambda__1(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
return x_5;
}
}
obj* l_list_mfoldl___main___at_lean_parser_level_app_parser___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_12; obj* x_13; obj* x_14; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_0);
x_12 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_13 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_13, 0, x_1);
lean::cnstr_set(x_13, 1, x_6);
lean::cnstr_set(x_13, 2, x_12);
x_14 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_7);
return x_14;
}
else
{
obj* x_15; obj* x_17; obj* x_19; obj* x_20; obj* x_21; obj* x_26; obj* x_27; 
x_15 = lean::cnstr_get(x_2, 0);
x_17 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_set(x_2, 0, lean::box(0));
 lean::cnstr_set(x_2, 1, lean::box(0));
 x_19 = x_2;
} else {
 lean::inc(x_15);
 lean::inc(x_17);
 lean::dec(x_2);
 x_19 = lean::box(0);
}
lean::inc(x_5);
lean::inc(x_4);
lean::inc(x_3);
x_26 = lean::apply_5(x_15, x_3, x_4, x_5, x_6, x_7);
x_27 = lean::cnstr_get(x_26, 0);
lean::inc(x_27);
if (lean::obj_tag(x_27) == 0)
{
obj* x_29; 
x_29 = lean::cnstr_get(x_26, 1);
lean::inc(x_29);
lean::dec(x_26);
x_20 = x_27;
x_21 = x_29;
goto lbl_22;
}
else
{
uint8 x_32; 
x_32 = lean::cnstr_get_scalar<uint8>(x_27, sizeof(void*)*1);
if (lean::obj_tag(x_1) == 0)
{
if (x_32 == 0)
{
obj* x_33; obj* x_36; obj* x_38; uint8 x_39; obj* x_40; obj* x_41; 
x_33 = lean::cnstr_get(x_26, 1);
lean::inc(x_33);
lean::dec(x_26);
x_36 = lean::cnstr_get(x_27, 0);
if (lean::is_exclusive(x_27)) {
 x_38 = x_27;
} else {
 lean::inc(x_36);
 lean::dec(x_27);
 x_38 = lean::box(0);
}
x_39 = 0;
if (lean::is_scalar(x_38)) {
 x_40 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_40 = x_38;
}
lean::cnstr_set(x_40, 0, x_36);
lean::cnstr_set_scalar(x_40, sizeof(void*)*1, x_39);
x_41 = x_40;
x_20 = x_41;
x_21 = x_33;
goto lbl_22;
}
else
{
obj* x_42; obj* x_45; obj* x_47; obj* x_48; obj* x_49; 
x_42 = lean::cnstr_get(x_26, 1);
lean::inc(x_42);
lean::dec(x_26);
x_45 = lean::cnstr_get(x_27, 0);
if (lean::is_exclusive(x_27)) {
 x_47 = x_27;
} else {
 lean::inc(x_45);
 lean::dec(x_27);
 x_47 = lean::box(0);
}
if (lean::is_scalar(x_47)) {
 x_48 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_48 = x_47;
}
lean::cnstr_set(x_48, 0, x_45);
lean::cnstr_set_scalar(x_48, sizeof(void*)*1, x_32);
x_49 = x_48;
x_20 = x_49;
x_21 = x_42;
goto lbl_22;
}
}
else
{
obj* x_50; obj* x_53; obj* x_55; obj* x_56; obj* x_58; obj* x_61; obj* x_62; obj* x_64; obj* x_66; obj* x_69; obj* x_71; obj* x_72; obj* x_73; 
x_50 = lean::cnstr_get(x_26, 1);
lean::inc(x_50);
lean::dec(x_26);
x_53 = lean::cnstr_get(x_27, 0);
if (lean::is_exclusive(x_27)) {
 lean::cnstr_set(x_27, 0, lean::box(0));
 x_55 = x_27;
} else {
 lean::inc(x_53);
 lean::dec(x_27);
 x_55 = lean::box(0);
}
x_56 = lean::cnstr_get(x_53, 3);
lean::inc(x_56);
x_58 = l_option_get___main___at_lean_parser_run___spec__2(x_56);
lean::dec(x_56);
lean::inc(x_1);
x_61 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_61, 0, x_58);
lean::cnstr_set(x_61, 1, x_1);
x_62 = lean::cnstr_get(x_53, 0);
lean::inc(x_62);
x_64 = lean::cnstr_get(x_53, 1);
lean::inc(x_64);
x_66 = lean::cnstr_get(x_53, 2);
lean::inc(x_66);
lean::dec(x_53);
x_69 = l_list_reverse___rarg(x_61);
lean::inc(x_0);
x_71 = l_lean_parser_syntax_mk__node(x_0, x_69);
x_72 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_72, 0, x_71);
x_73 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_73, 0, x_62);
lean::cnstr_set(x_73, 1, x_64);
lean::cnstr_set(x_73, 2, x_66);
lean::cnstr_set(x_73, 3, x_72);
if (x_32 == 0)
{
uint8 x_74; obj* x_75; obj* x_76; 
x_74 = 0;
if (lean::is_scalar(x_55)) {
 x_75 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_75 = x_55;
}
lean::cnstr_set(x_75, 0, x_73);
lean::cnstr_set_scalar(x_75, sizeof(void*)*1, x_74);
x_76 = x_75;
x_20 = x_76;
x_21 = x_50;
goto lbl_22;
}
else
{
obj* x_77; obj* x_78; 
if (lean::is_scalar(x_55)) {
 x_77 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_77 = x_55;
}
lean::cnstr_set(x_77, 0, x_73);
lean::cnstr_set_scalar(x_77, sizeof(void*)*1, x_32);
x_78 = x_77;
x_20 = x_78;
x_21 = x_50;
goto lbl_22;
}
}
}
lbl_22:
{
if (lean::obj_tag(x_20) == 0)
{
obj* x_79; obj* x_81; obj* x_83; obj* x_85; obj* x_86; obj* x_87; obj* x_88; obj* x_89; 
x_79 = lean::cnstr_get(x_20, 0);
x_81 = lean::cnstr_get(x_20, 1);
x_83 = lean::cnstr_get(x_20, 2);
if (lean::is_exclusive(x_20)) {
 x_85 = x_20;
} else {
 lean::inc(x_79);
 lean::inc(x_81);
 lean::inc(x_83);
 lean::dec(x_20);
 x_85 = lean::box(0);
}
if (lean::is_scalar(x_19)) {
 x_86 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_86 = x_19;
}
lean::cnstr_set(x_86, 0, x_79);
lean::cnstr_set(x_86, 1, x_1);
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
if (lean::obj_tag(x_89) == 0)
{
obj* x_90; obj* x_92; obj* x_94; obj* x_97; obj* x_98; obj* x_100; obj* x_102; obj* x_103; obj* x_104; 
x_90 = lean::cnstr_get(x_89, 0);
lean::inc(x_90);
x_92 = lean::cnstr_get(x_89, 1);
lean::inc(x_92);
x_94 = lean::cnstr_get(x_89, 2);
lean::inc(x_94);
lean::dec(x_89);
x_97 = l_list_mfoldl___main___at_lean_parser_level_app_parser___spec__2(x_0, x_90, x_17, x_3, x_4, x_5, x_92, x_21);
x_98 = lean::cnstr_get(x_97, 0);
x_100 = lean::cnstr_get(x_97, 1);
if (lean::is_exclusive(x_97)) {
 x_102 = x_97;
} else {
 lean::inc(x_98);
 lean::inc(x_100);
 lean::dec(x_97);
 x_102 = lean::box(0);
}
x_103 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_94, x_98);
if (lean::is_scalar(x_102)) {
 x_104 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_104 = x_102;
}
lean::cnstr_set(x_104, 0, x_103);
lean::cnstr_set(x_104, 1, x_100);
return x_104;
}
else
{
obj* x_110; uint8 x_112; obj* x_113; obj* x_114; obj* x_115; obj* x_116; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_17);
x_110 = lean::cnstr_get(x_89, 0);
x_112 = lean::cnstr_get_scalar<uint8>(x_89, sizeof(void*)*1);
if (lean::is_exclusive(x_89)) {
 x_113 = x_89;
} else {
 lean::inc(x_110);
 lean::dec(x_89);
 x_113 = lean::box(0);
}
if (lean::is_scalar(x_113)) {
 x_114 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_114 = x_113;
}
lean::cnstr_set(x_114, 0, x_110);
lean::cnstr_set_scalar(x_114, sizeof(void*)*1, x_112);
x_115 = x_114;
x_116 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_116, 0, x_115);
lean::cnstr_set(x_116, 1, x_21);
return x_116;
}
}
else
{
obj* x_124; uint8 x_126; obj* x_127; obj* x_128; obj* x_129; obj* x_130; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_17);
lean::dec(x_19);
x_124 = lean::cnstr_get(x_20, 0);
x_126 = lean::cnstr_get_scalar<uint8>(x_20, sizeof(void*)*1);
if (lean::is_exclusive(x_20)) {
 x_127 = x_20;
} else {
 lean::inc(x_124);
 lean::dec(x_20);
 x_127 = lean::box(0);
}
if (lean::is_scalar(x_127)) {
 x_128 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_128 = x_127;
}
lean::cnstr_set(x_128, 0, x_124);
lean::cnstr_set_scalar(x_128, sizeof(void*)*1, x_126);
x_129 = x_128;
x_130 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_130, 0, x_129);
lean::cnstr_set(x_130, 1, x_21);
return x_130;
}
}
}
}
}
obj* l_lean_parser_combinators_node___at_lean_parser_level_app_parser___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_9; obj* x_10; 
x_7 = lean::box(0);
lean::inc(x_0);
x_9 = l_list_mfoldl___main___at_lean_parser_level_app_parser___spec__2(x_0, x_7, x_1, x_2, x_3, x_4, x_5, x_6);
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
x_22 = l_list_reverse___rarg(x_15);
x_23 = l_lean_parser_syntax_mk__node(x_0, x_22);
x_24 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_21)) {
 x_25 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_25 = x_21;
}
lean::cnstr_set(x_25, 0, x_23);
lean::cnstr_set(x_25, 1, x_17);
lean::cnstr_set(x_25, 2, x_24);
x_26 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_19, x_25);
if (lean::is_scalar(x_14)) {
 x_27 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_27 = x_14;
}
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_12);
return x_27;
}
else
{
obj* x_29; obj* x_31; obj* x_32; uint8 x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
lean::dec(x_0);
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
return x_38;
}
}
}
obj* _init_l_lean_parser_level_app_parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = lean::box(0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_level_app_parser_lean_parser_has__view___lambda__1___boxed), 5, 0);
x_2 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_2, 0, x_1);
lean::cnstr_set(x_2, 1, x_0);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_level_get__leading___boxed), 5, 0);
x_4 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_2);
return x_4;
}
}
obj* l_lean_parser_level_app_parser(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = l_lean_parser_level_app;
x_6 = l_lean_parser_level_app_parser___closed__1;
x_7 = l_lean_parser_combinators_node___at_lean_parser_level_app_parser___spec__1(x_5, x_6, x_0, x_1, x_2, x_3, x_4);
return x_7;
}
}
obj* _init_l_lean_parser_level_add__lit() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("level");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("add_lit");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_lean_parser_level_add__lit_has__view_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; 
x_0 = l_lean_parser_number_has__view;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
x_4 = lean::box(3);
x_5 = lean::apply_1(x_1, x_4);
return x_5;
}
}
obj* _init_l_lean_parser_level_add__lit_has__view_x_27___lambda__1___closed__2() {
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
obj* x_5; obj* x_6; 
if (lean::obj_tag(x_0) == 0)
{
obj* x_8; 
x_8 = lean::box(3);
x_5 = x_0;
x_6 = x_8;
goto lbl_7;
}
else
{
obj* x_9; obj* x_11; 
x_9 = lean::cnstr_get(x_0, 0);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_0, 1);
lean::inc(x_11);
lean::dec(x_0);
x_5 = x_11;
x_6 = x_9;
goto lbl_7;
}
lbl_7:
{
switch (lean::obj_tag(x_6)) {
case 0:
{
obj* x_14; obj* x_17; 
x_14 = lean::cnstr_get(x_6, 0);
lean::inc(x_14);
lean::dec(x_6);
x_17 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_17, 0, x_14);
if (lean::obj_tag(x_5) == 0)
{
obj* x_18; obj* x_19; 
x_18 = l_lean_parser_level_add__lit_has__view_x_27___lambda__1___closed__1;
x_19 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_19, 0, x_1);
lean::cnstr_set(x_19, 1, x_17);
lean::cnstr_set(x_19, 2, x_18);
return x_19;
}
else
{
obj* x_20; obj* x_23; obj* x_24; obj* x_27; obj* x_28; 
x_20 = lean::cnstr_get(x_5, 0);
lean::inc(x_20);
lean::dec(x_5);
x_23 = l_lean_parser_number_has__view;
x_24 = lean::cnstr_get(x_23, 0);
lean::inc(x_24);
lean::dec(x_23);
x_27 = lean::apply_1(x_24, x_20);
x_28 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_28, 0, x_1);
lean::cnstr_set(x_28, 1, x_17);
lean::cnstr_set(x_28, 2, x_27);
return x_28;
}
}
case 3:
{
obj* x_29; 
x_29 = lean::box(0);
if (lean::obj_tag(x_5) == 0)
{
obj* x_30; obj* x_31; 
x_30 = l_lean_parser_level_add__lit_has__view_x_27___lambda__1___closed__1;
x_31 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_31, 0, x_1);
lean::cnstr_set(x_31, 1, x_29);
lean::cnstr_set(x_31, 2, x_30);
return x_31;
}
else
{
obj* x_32; obj* x_35; obj* x_36; obj* x_39; obj* x_40; 
x_32 = lean::cnstr_get(x_5, 0);
lean::inc(x_32);
lean::dec(x_5);
x_35 = l_lean_parser_number_has__view;
x_36 = lean::cnstr_get(x_35, 0);
lean::inc(x_36);
lean::dec(x_35);
x_39 = lean::apply_1(x_36, x_32);
x_40 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_40, 0, x_1);
lean::cnstr_set(x_40, 1, x_29);
lean::cnstr_set(x_40, 2, x_39);
return x_40;
}
}
default:
{
obj* x_42; 
lean::dec(x_6);
x_42 = lean::box(0);
if (lean::obj_tag(x_5) == 0)
{
obj* x_43; obj* x_44; 
x_43 = l_lean_parser_level_add__lit_has__view_x_27___lambda__1___closed__1;
x_44 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_44, 0, x_1);
lean::cnstr_set(x_44, 1, x_42);
lean::cnstr_set(x_44, 2, x_43);
return x_44;
}
else
{
obj* x_45; obj* x_48; obj* x_49; obj* x_52; obj* x_53; 
x_45 = lean::cnstr_get(x_5, 0);
lean::inc(x_45);
lean::dec(x_5);
x_48 = l_lean_parser_number_has__view;
x_49 = lean::cnstr_get(x_48, 0);
lean::inc(x_49);
lean::dec(x_48);
x_52 = lean::apply_1(x_49, x_45);
x_53 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_53, 0, x_1);
lean::cnstr_set(x_53, 1, x_42);
lean::cnstr_set(x_53, 2, x_52);
return x_53;
}
}
}
}
}
}
}
obj* l_lean_parser_level_add__lit_has__view_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_4 = l_lean_parser_syntax_as__node___main(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; 
x_5 = l_lean_parser_level_add__lit_has__view_x_27___lambda__1___closed__2;
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
obj* x_18; obj* x_19; 
if (lean::obj_tag(x_1) == 0)
{
obj* x_21; 
x_21 = lean::box(3);
x_18 = x_1;
x_19 = x_21;
goto lbl_20;
}
else
{
obj* x_22; obj* x_24; 
x_22 = lean::cnstr_get(x_1, 0);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_1, 1);
lean::inc(x_24);
lean::dec(x_1);
x_18 = x_24;
x_19 = x_22;
goto lbl_20;
}
lbl_20:
{
switch (lean::obj_tag(x_19)) {
case 0:
{
obj* x_27; obj* x_30; 
x_27 = lean::cnstr_get(x_19, 0);
lean::inc(x_27);
lean::dec(x_19);
x_30 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_30, 0, x_27);
if (lean::obj_tag(x_18) == 0)
{
obj* x_31; obj* x_32; 
x_31 = l_lean_parser_level_add__lit_has__view_x_27___lambda__1___closed__1;
x_32 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_32, 0, x_2);
lean::cnstr_set(x_32, 1, x_30);
lean::cnstr_set(x_32, 2, x_31);
return x_32;
}
else
{
obj* x_33; obj* x_36; obj* x_37; obj* x_40; obj* x_41; 
x_33 = lean::cnstr_get(x_18, 0);
lean::inc(x_33);
lean::dec(x_18);
x_36 = l_lean_parser_number_has__view;
x_37 = lean::cnstr_get(x_36, 0);
lean::inc(x_37);
lean::dec(x_36);
x_40 = lean::apply_1(x_37, x_33);
x_41 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_41, 0, x_2);
lean::cnstr_set(x_41, 1, x_30);
lean::cnstr_set(x_41, 2, x_40);
return x_41;
}
}
case 3:
{
obj* x_42; 
x_42 = lean::box(0);
if (lean::obj_tag(x_18) == 0)
{
obj* x_43; obj* x_44; 
x_43 = l_lean_parser_level_add__lit_has__view_x_27___lambda__1___closed__1;
x_44 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_44, 0, x_2);
lean::cnstr_set(x_44, 1, x_42);
lean::cnstr_set(x_44, 2, x_43);
return x_44;
}
else
{
obj* x_45; obj* x_48; obj* x_49; obj* x_52; obj* x_53; 
x_45 = lean::cnstr_get(x_18, 0);
lean::inc(x_45);
lean::dec(x_18);
x_48 = l_lean_parser_number_has__view;
x_49 = lean::cnstr_get(x_48, 0);
lean::inc(x_49);
lean::dec(x_48);
x_52 = lean::apply_1(x_49, x_45);
x_53 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_53, 0, x_2);
lean::cnstr_set(x_53, 1, x_42);
lean::cnstr_set(x_53, 2, x_52);
return x_53;
}
}
default:
{
obj* x_55; 
lean::dec(x_19);
x_55 = lean::box(0);
if (lean::obj_tag(x_18) == 0)
{
obj* x_56; obj* x_57; 
x_56 = l_lean_parser_level_add__lit_has__view_x_27___lambda__1___closed__1;
x_57 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_57, 0, x_2);
lean::cnstr_set(x_57, 1, x_55);
lean::cnstr_set(x_57, 2, x_56);
return x_57;
}
else
{
obj* x_58; obj* x_61; obj* x_62; obj* x_65; obj* x_66; 
x_58 = lean::cnstr_get(x_18, 0);
lean::inc(x_58);
lean::dec(x_18);
x_61 = l_lean_parser_number_has__view;
x_62 = lean::cnstr_get(x_61, 0);
lean::inc(x_62);
lean::dec(x_61);
x_65 = lean::apply_1(x_62, x_58);
x_66 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_66, 0, x_2);
lean::cnstr_set(x_66, 1, x_55);
lean::cnstr_set(x_66, 2, x_65);
return x_66;
}
}
}
}
}
}
}
obj* l_lean_parser_level_add__lit_has__view_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_5; obj* x_8; obj* x_9; obj* x_12; obj* x_13; obj* x_14; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 2);
lean::inc(x_5);
lean::dec(x_0);
x_8 = l_lean_parser_number_has__view;
x_9 = lean::cnstr_get(x_8, 1);
lean::inc(x_9);
lean::dec(x_8);
x_12 = lean::apply_1(x_9, x_5);
x_13 = lean::box(0);
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_12);
lean::cnstr_set(x_14, 1, x_13);
if (lean::obj_tag(x_3) == 0)
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_15 = l_lean_parser_raw_view___rarg___lambda__2___closed__1;
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_15);
lean::cnstr_set(x_16, 1, x_14);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_1);
lean::cnstr_set(x_17, 1, x_16);
x_18 = l_lean_parser_level_add__lit;
x_19 = l_lean_parser_syntax_mk__node(x_18, x_17);
return x_19;
}
else
{
obj* x_20; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_28; obj* x_29; obj* x_30; obj* x_31; 
x_20 = lean::cnstr_get(x_3, 0);
if (lean::is_exclusive(x_3)) {
 x_22 = x_3;
} else {
 lean::inc(x_20);
 lean::dec(x_3);
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
lean::cnstr_set(x_28, 1, x_14);
x_29 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_29, 0, x_1);
lean::cnstr_set(x_29, 1, x_28);
x_30 = l_lean_parser_level_add__lit;
x_31 = l_lean_parser_syntax_mk__node(x_30, x_29);
return x_31;
}
}
}
obj* _init_l_lean_parser_level_add__lit_has__view_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_level_add__lit_has__view_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_level_add__lit_has__view_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_lean_parser_level_add__lit_has__view() {
_start:
{
obj* x_0; 
x_0 = l_lean_parser_level_add__lit_has__view_x_27;
return x_0;
}
}
obj* l_lean_parser_symbol__core___at_lean_parser_level_add__lit_parser_lean_parser_has__tokens___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_10; obj* x_11; obj* x_13; obj* x_15; obj* x_17; 
lean::inc(x_6);
lean::inc(x_5);
x_10 = l_lean_parser_token(x_5, x_6, x_7);
x_11 = lean::cnstr_get(x_10, 0);
x_13 = lean::cnstr_get(x_10, 1);
if (lean::is_exclusive(x_10)) {
 lean::cnstr_set(x_10, 0, lean::box(0));
 lean::cnstr_set(x_10, 1, lean::box(0));
 x_15 = x_10;
} else {
 lean::inc(x_11);
 lean::inc(x_13);
 lean::dec(x_10);
 x_15 = lean::box(0);
}
lean::inc(x_0);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_17, 0, x_0);
if (lean::obj_tag(x_11) == 0)
{
obj* x_18; obj* x_20; obj* x_22; obj* x_24; obj* x_25; 
x_18 = lean::cnstr_get(x_11, 0);
x_20 = lean::cnstr_get(x_11, 1);
x_22 = lean::cnstr_get(x_11, 2);
if (lean::is_exclusive(x_11)) {
 lean::cnstr_set(x_11, 0, lean::box(0));
 lean::cnstr_set(x_11, 1, lean::box(0));
 lean::cnstr_set(x_11, 2, lean::box(0));
 x_24 = x_11;
} else {
 lean::inc(x_18);
 lean::inc(x_20);
 lean::inc(x_22);
 lean::dec(x_11);
 x_24 = lean::box(0);
}
switch (lean::obj_tag(x_18)) {
case 0:
{
obj* x_27; obj* x_29; uint8 x_32; 
x_27 = lean::cnstr_get(x_18, 0);
lean::inc(x_27);
x_29 = lean::cnstr_get(x_27, 1);
lean::inc(x_29);
lean::dec(x_27);
x_32 = lean::string_dec_eq(x_0, x_29);
lean::dec(x_0);
if (x_32 == 0)
{
obj* x_36; obj* x_37; obj* x_38; obj* x_42; 
lean::dec(x_15);
lean::dec(x_24);
x_36 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_36, 0, x_6);
x_37 = lean::box(0);
x_38 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_29, x_2, x_36, x_37, x_5, x_20, x_13);
lean::dec(x_20);
lean::dec(x_5);
lean::dec(x_36);
x_42 = lean::cnstr_get(x_38, 0);
lean::inc(x_42);
if (lean::obj_tag(x_42) == 0)
{
obj* x_44; obj* x_46; obj* x_47; obj* x_49; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; 
x_44 = lean::cnstr_get(x_38, 1);
if (lean::is_exclusive(x_38)) {
 lean::cnstr_release(x_38, 0);
 x_46 = x_38;
} else {
 lean::inc(x_44);
 lean::dec(x_38);
 x_46 = lean::box(0);
}
x_47 = lean::cnstr_get(x_42, 1);
x_49 = lean::cnstr_get(x_42, 2);
if (lean::is_exclusive(x_42)) {
 lean::cnstr_release(x_42, 0);
 x_51 = x_42;
} else {
 lean::inc(x_47);
 lean::inc(x_49);
 lean::dec(x_42);
 x_51 = lean::box(0);
}
x_52 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_51)) {
 x_53 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_53 = x_51;
}
lean::cnstr_set(x_53, 0, x_18);
lean::cnstr_set(x_53, 1, x_47);
lean::cnstr_set(x_53, 2, x_52);
x_54 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_49, x_53);
x_55 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_22, x_54);
x_56 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_52, x_55);
x_57 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_56, x_17);
x_58 = l_lean_parser_parsec__t_try__mk__res___rarg(x_57);
if (lean::is_scalar(x_46)) {
 x_59 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_59 = x_46;
}
lean::cnstr_set(x_59, 0, x_58);
lean::cnstr_set(x_59, 1, x_44);
return x_59;
}
else
{
obj* x_61; obj* x_63; obj* x_64; uint8 x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; 
lean::dec(x_18);
x_61 = lean::cnstr_get(x_38, 1);
if (lean::is_exclusive(x_38)) {
 lean::cnstr_release(x_38, 0);
 x_63 = x_38;
} else {
 lean::inc(x_61);
 lean::dec(x_38);
 x_63 = lean::box(0);
}
x_64 = lean::cnstr_get(x_42, 0);
x_66 = lean::cnstr_get_scalar<uint8>(x_42, sizeof(void*)*1);
if (lean::is_exclusive(x_42)) {
 x_67 = x_42;
} else {
 lean::inc(x_64);
 lean::dec(x_42);
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
x_70 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_22, x_69);
x_71 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_72 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_71, x_70);
x_73 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_72, x_17);
x_74 = l_lean_parser_parsec__t_try__mk__res___rarg(x_73);
if (lean::is_scalar(x_63)) {
 x_75 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_75 = x_63;
}
lean::cnstr_set(x_75, 0, x_74);
lean::cnstr_set(x_75, 1, x_61);
return x_75;
}
}
else
{
obj* x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_86; obj* x_87; 
lean::dec(x_5);
lean::dec(x_6);
lean::dec(x_2);
lean::dec(x_29);
x_80 = l_lean_parser_finish__comment__block___closed__2;
if (lean::is_scalar(x_24)) {
 x_81 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_81 = x_24;
}
lean::cnstr_set(x_81, 0, x_18);
lean::cnstr_set(x_81, 1, x_20);
lean::cnstr_set(x_81, 2, x_80);
x_82 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_22, x_81);
x_83 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_84 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_83, x_82);
x_85 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_84, x_17);
x_86 = l_lean_parser_parsec__t_try__mk__res___rarg(x_85);
if (lean::is_scalar(x_15)) {
 x_87 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_87 = x_15;
}
lean::cnstr_set(x_87, 0, x_86);
lean::cnstr_set(x_87, 1, x_13);
return x_87;
}
}
case 3:
{
obj* x_91; 
lean::dec(x_15);
lean::dec(x_24);
lean::dec(x_0);
x_91 = lean::box(0);
x_25 = x_91;
goto lbl_26;
}
default:
{
obj* x_96; 
lean::dec(x_15);
lean::dec(x_24);
lean::dec(x_0);
lean::dec(x_18);
x_96 = lean::box(0);
x_25 = x_96;
goto lbl_26;
}
}
lbl_26:
{
obj* x_98; obj* x_99; obj* x_100; obj* x_101; obj* x_105; obj* x_107; obj* x_109; obj* x_110; obj* x_111; obj* x_112; obj* x_113; obj* x_114; obj* x_115; 
lean::dec(x_25);
x_98 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_98, 0, x_6);
x_99 = lean::box(0);
x_100 = l_string_join___closed__1;
x_101 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_100, x_2, x_98, x_99, x_5, x_20, x_13);
lean::dec(x_20);
lean::dec(x_5);
lean::dec(x_98);
x_105 = lean::cnstr_get(x_101, 0);
x_107 = lean::cnstr_get(x_101, 1);
if (lean::is_exclusive(x_101)) {
 x_109 = x_101;
} else {
 lean::inc(x_105);
 lean::inc(x_107);
 lean::dec(x_101);
 x_109 = lean::box(0);
}
x_110 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_22, x_105);
x_111 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_112 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_111, x_110);
x_113 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_112, x_17);
x_114 = l_lean_parser_parsec__t_try__mk__res___rarg(x_113);
if (lean::is_scalar(x_109)) {
 x_115 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_115 = x_109;
}
lean::cnstr_set(x_115, 0, x_114);
lean::cnstr_set(x_115, 1, x_107);
return x_115;
}
}
else
{
obj* x_120; uint8 x_122; obj* x_123; obj* x_124; obj* x_125; obj* x_126; obj* x_127; obj* x_128; obj* x_129; obj* x_130; 
lean::dec(x_5);
lean::dec(x_6);
lean::dec(x_0);
lean::dec(x_2);
x_120 = lean::cnstr_get(x_11, 0);
x_122 = lean::cnstr_get_scalar<uint8>(x_11, sizeof(void*)*1);
if (lean::is_exclusive(x_11)) {
 x_123 = x_11;
} else {
 lean::inc(x_120);
 lean::dec(x_11);
 x_123 = lean::box(0);
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
x_127 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_126, x_125);
x_128 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_127, x_17);
x_129 = l_lean_parser_parsec__t_try__mk__res___rarg(x_128);
if (lean::is_scalar(x_15)) {
 x_130 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_130 = x_15;
}
lean::cnstr_set(x_130, 0, x_129);
lean::cnstr_set(x_130, 1, x_13);
return x_130;
}
}
}
obj* l_lean_parser_number_parser___at_lean_parser_level_add__lit_parser_lean_parser_has__tokens___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2) {
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
obj* x_8; obj* x_10; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_19; 
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
lean::inc(x_11);
x_19 = l_lean_parser_try__view___at_lean_parser_number_parser___spec__1(x_11);
if (lean::obj_tag(x_19) == 0)
{
obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_31; obj* x_33; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; 
lean::dec(x_17);
lean::dec(x_10);
lean::dec(x_11);
x_23 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_23, 0, x_1);
x_24 = lean::box(0);
x_25 = l_string_join___closed__1;
x_26 = l_lean_parser_number_parser___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__2___rarg___closed__1;
x_27 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_25, x_26, x_23, x_24, x_0, x_13, x_8);
lean::dec(x_13);
lean::dec(x_0);
lean::dec(x_23);
x_31 = lean::cnstr_get(x_27, 0);
x_33 = lean::cnstr_get(x_27, 1);
if (lean::is_exclusive(x_27)) {
 x_35 = x_27;
} else {
 lean::inc(x_31);
 lean::inc(x_33);
 lean::dec(x_27);
 x_35 = lean::box(0);
}
x_36 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_37 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_36, x_31);
x_38 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_37);
x_39 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_36, x_38);
x_40 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_39, x_26);
x_41 = l_lean_parser_parsec__t_try__mk__res___rarg(x_40);
if (lean::is_scalar(x_35)) {
 x_42 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_42 = x_35;
}
lean::cnstr_set(x_42, 0, x_41);
lean::cnstr_set(x_42, 1, x_33);
return x_42;
}
else
{
obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_19);
x_46 = l_lean_parser_finish__comment__block___closed__2;
if (lean::is_scalar(x_17)) {
 x_47 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_47 = x_17;
}
lean::cnstr_set(x_47, 0, x_11);
lean::cnstr_set(x_47, 1, x_13);
lean::cnstr_set(x_47, 2, x_46);
x_48 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_47);
x_49 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_50 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_49, x_48);
x_51 = l_lean_parser_number_parser___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__2___rarg___closed__1;
x_52 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_50, x_51);
x_53 = l_lean_parser_parsec__t_try__mk__res___rarg(x_52);
if (lean::is_scalar(x_10)) {
 x_54 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_54 = x_10;
}
lean::cnstr_set(x_54, 0, x_53);
lean::cnstr_set(x_54, 1, x_8);
return x_54;
}
}
else
{
obj* x_57; obj* x_59; obj* x_60; uint8 x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; 
lean::dec(x_1);
lean::dec(x_0);
x_57 = lean::cnstr_get(x_5, 1);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 x_59 = x_5;
} else {
 lean::inc(x_57);
 lean::dec(x_5);
 x_59 = lean::box(0);
}
x_60 = lean::cnstr_get(x_6, 0);
x_62 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*1);
if (lean::is_exclusive(x_6)) {
 x_63 = x_6;
} else {
 lean::inc(x_60);
 lean::dec(x_6);
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
x_68 = l_lean_parser_number_parser___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__2___rarg___closed__1;
x_69 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_67, x_68);
x_70 = l_lean_parser_parsec__t_try__mk__res___rarg(x_69);
if (lean::is_scalar(x_59)) {
 x_71 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_71 = x_59;
}
lean::cnstr_set(x_71, 0, x_70);
lean::cnstr_set(x_71, 1, x_57);
return x_71;
}
}
}
obj* l_lean_parser_number_parser___at_lean_parser_level_add__lit_parser_lean_parser_has__tokens___spec__2(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_number_parser___at_lean_parser_level_add__lit_parser_lean_parser_has__tokens___spec__2___rarg), 3, 0);
return x_2;
}
}
obj* _init_l_lean_parser_level_add__lit_parser_lean_parser_has__tokens() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_8; obj* x_9; obj* x_11; 
x_0 = lean::mk_string("+");
x_1 = lean::mk_nat_obj(0u);
x_2 = l_lean_parser_symbol_tokens___rarg(x_0, x_1);
x_3 = lean::box(0);
x_4 = l_lean_parser_list_cons_tokens___rarg(x_3, x_3);
x_5 = l_lean_parser_list_cons_tokens___rarg(x_2, x_4);
lean::dec(x_4);
lean::dec(x_2);
x_8 = l_lean_parser_level_lean_parser_has__tokens;
x_9 = l_lean_parser_list_cons_tokens___rarg(x_8, x_5);
lean::dec(x_5);
x_11 = l_lean_parser_tokens___rarg(x_9);
lean::dec(x_9);
return x_11;
}
}
obj* l_lean_parser_symbol__core___at_lean_parser_level_add__lit_parser_lean_parser_has__tokens___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = l_lean_parser_symbol__core___at_lean_parser_level_add__lit_parser_lean_parser_has__tokens___spec__1(x_0, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_4);
return x_8;
}
}
obj* l_lean_parser_number_parser___at_lean_parser_level_add__lit_parser_lean_parser_has__tokens___spec__2___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_parser_number_parser___at_lean_parser_level_add__lit_parser_lean_parser_has__tokens___spec__2(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_lean_parser_level_add__lit_parser_lean_parser_has__view() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_0 = lean::mk_string("+");
x_1 = l_string_trim(x_0);
lean::inc(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_3, 0, x_1);
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_level_add__lit_parser_lean_parser_has__tokens___spec__1___boxed), 8, 3);
lean::closure_set(x_5, 0, x_1);
lean::closure_set(x_5, 1, x_4);
lean::closure_set(x_5, 2, x_3);
x_6 = lean::box(0);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_number_parser___at_lean_parser_level_add__lit_parser_lean_parser_has__tokens___spec__2___boxed), 2, 0);
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_6);
x_9 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_9, 0, x_5);
lean::cnstr_set(x_9, 1, x_8);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_level_get__leading___boxed), 5, 0);
x_11 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_9);
x_12 = l_lean_parser_trailing__level__parser__m_monad;
x_13 = l_lean_parser_trailing__level__parser__m_monad__except;
x_14 = l_lean_parser_trailing__level__parser__m_lean_parser_monad__parsec;
x_15 = l_lean_parser_trailing__level__parser__m_alternative;
x_16 = l_lean_parser_level_add__lit;
x_17 = l_lean_parser_level_add__lit_has__view;
x_18 = l_lean_parser_combinators_node_view___rarg(x_12, x_13, x_14, x_15, x_16, x_11, x_17);
lean::dec(x_11);
return x_18;
}
}
obj* _init_l_lean_parser_level_add__lit_parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_0 = lean::mk_string("+");
x_1 = l_string_trim(x_0);
lean::inc(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_3, 0, x_1);
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_level_add__lit_parser_lean_parser_has__tokens___spec__1___boxed), 8, 3);
lean::closure_set(x_5, 0, x_1);
lean::closure_set(x_5, 1, x_4);
lean::closure_set(x_5, 2, x_3);
x_6 = lean::box(0);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_number_parser___at_lean_parser_level_add__lit_parser_lean_parser_has__tokens___spec__2___boxed), 2, 0);
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_6);
x_9 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_9, 0, x_5);
lean::cnstr_set(x_9, 1, x_8);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_level_get__leading___boxed), 5, 0);
x_11 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_9);
return x_11;
}
}
obj* l_lean_parser_level_add__lit_parser(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = l_lean_parser_level_add__lit;
x_6 = l_lean_parser_level_add__lit_parser___closed__1;
x_7 = l_lean_parser_combinators_node___at_lean_parser_level_app_parser___spec__1(x_5, x_6, x_0, x_1, x_2, x_3, x_4);
return x_7;
}
}
obj* _init_l_lean_parser_level_trailing() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("level");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("trailing");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* _init_l_lean_parser_level_trailing_has__view_x_27___lambda__1___closed__1() {
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
obj* x_8; obj* x_9; obj* x_12; obj* x_13; 
x_8 = l_lean_parser_level_add__lit_has__view;
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
lean::dec(x_8);
x_12 = lean::apply_1(x_9, x_0);
x_13 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_13, 0, x_12);
return x_13;
}
else
{
obj* x_14; obj* x_15; obj* x_18; obj* x_19; 
x_14 = l_lean_parser_level_app_has__view;
x_15 = lean::cnstr_get(x_14, 0);
lean::inc(x_15);
lean::dec(x_14);
x_18 = lean::apply_1(x_15, x_0);
x_19 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_19, 0, x_18);
return x_19;
}
}
}
}
obj* _init_l_lean_parser_level_trailing_has__view_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("level");
x_6 = lean_name_mk_string(x_4, x_5);
x_7 = lean::mk_string("trailing");
x_8 = lean_name_mk_string(x_6, x_7);
return x_8;
}
}
obj* l_lean_parser_level_trailing_has__view_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_4 = l_lean_parser_syntax_as__node___main(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; 
x_5 = l_lean_parser_level_trailing_has__view_x_27___lambda__1___closed__1;
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
x_14 = l_lean_parser_level_trailing_has__view_x_27___lambda__1___closed__2;
x_15 = lean_name_dec_eq(x_9, x_14);
lean::dec(x_9);
if (x_15 == 0)
{
obj* x_18; 
lean::dec(x_11);
x_18 = l_lean_parser_level_trailing_has__view_x_27___lambda__1___closed__1;
return x_18;
}
else
{
if (lean::obj_tag(x_11) == 0)
{
obj* x_19; 
x_19 = l_lean_parser_level_trailing_has__view_x_27___lambda__1___closed__1;
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
x_26 = l_lean_parser_level_trailing_has__view_x_27___lambda__1___closed__1;
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
x_33 = l_lean_parser_level_trailing_has__view_x_27___lambda__1___closed__1;
return x_33;
}
case 1:
{
obj* x_36; 
lean::dec(x_27);
lean::dec(x_30);
x_36 = l_lean_parser_level_trailing_has__view_x_27___lambda__1___closed__1;
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
x_50 = l_lean_parser_level_trailing_has__view_x_27___lambda__1___closed__1;
return x_50;
}
else
{
if (lean::obj_tag(x_37) == 0)
{
obj* x_52; 
lean::dec(x_42);
x_52 = l_lean_parser_level_trailing_has__view_x_27___lambda__1___closed__1;
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
x_61 = l_lean_parser_level_trailing_has__view_x_27___lambda__1___closed__1;
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
x_64 = l_lean_parser_level_trailing_has__view_x_27___lambda__1___closed__1;
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
obj* x_68; obj* x_69; obj* x_72; obj* x_73; 
x_68 = l_lean_parser_level_add__lit_has__view;
x_69 = lean::cnstr_get(x_68, 0);
lean::inc(x_69);
lean::dec(x_68);
x_72 = lean::apply_1(x_69, x_1);
x_73 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_73, 0, x_72);
return x_73;
}
else
{
obj* x_74; obj* x_75; obj* x_78; obj* x_79; 
x_74 = l_lean_parser_level_app_has__view;
x_75 = lean::cnstr_get(x_74, 0);
lean::inc(x_75);
lean::dec(x_74);
x_78 = lean::apply_1(x_75, x_1);
x_79 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_79, 0, x_78);
return x_79;
}
}
}
}
obj* l_lean_parser_level_trailing_has__view_x_27___lambda__2(obj* x_0) {
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
x_5 = l_lean_parser_level_app_has__view;
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
x_14 = l_lean_parser_level_trailing;
x_15 = l_lean_parser_syntax_mk__node(x_14, x_13);
return x_15;
}
else
{
obj* x_16; obj* x_19; obj* x_20; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
x_16 = lean::cnstr_get(x_0, 0);
lean::inc(x_16);
lean::dec(x_0);
x_19 = l_lean_parser_level_add__lit_has__view;
x_20 = lean::cnstr_get(x_19, 1);
lean::inc(x_20);
lean::dec(x_19);
x_23 = lean::apply_1(x_20, x_16);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_1);
x_25 = l_lean_parser_detail__ident__part_has__view_x_27___lambda__2___closed__3;
x_26 = l_lean_parser_syntax_mk__node(x_25, x_24);
x_27 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_1);
x_28 = l_lean_parser_level_trailing;
x_29 = l_lean_parser_syntax_mk__node(x_28, x_27);
return x_29;
}
}
}
obj* _init_l_lean_parser_level_trailing_has__view_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_level_trailing_has__view_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_level_trailing_has__view_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_lean_parser_level_trailing_has__view() {
_start:
{
obj* x_0; 
x_0 = l_lean_parser_level_trailing_has__view_x_27;
return x_0;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_level_trailing_parser_lean_parser_has__tokens___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
obj* x_9; obj* x_10; uint8 x_11; obj* x_12; obj* x_13; obj* x_14; 
x_9 = l_option_get__or__else___main___rarg(x_2, x_7);
x_10 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_0);
lean::cnstr_set(x_10, 2, x_1);
lean::cnstr_set(x_10, 3, x_3);
x_11 = 0;
x_12 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_12, 0, x_10);
lean::cnstr_set_scalar(x_12, sizeof(void*)*1, x_11);
x_13 = x_12;
x_14 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_8);
return x_14;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_level_trailing_parser_lean_parser_has__tokens___spec__2(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___at_lean_parser_level_trailing_parser_lean_parser_has__tokens___spec__2___rarg___boxed), 9, 0);
return x_1;
}
}
obj* l_lean_parser_combinators_choice__aux___main___at_lean_parser_level_trailing_parser_lean_parser_has__tokens___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
lean::dec(x_1);
x_8 = lean::box(0);
x_9 = l_lean_parser_combinators_choice__aux___main___rarg___closed__1;
x_10 = l_mjoin___rarg___closed__1;
x_11 = l_lean_parser_monad__parsec_error___at_lean_parser_level_trailing_parser_lean_parser_has__tokens___spec__2___rarg(x_9, x_10, x_8, x_8, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
return x_11;
}
else
{
obj* x_16; obj* x_18; obj* x_20; obj* x_25; obj* x_26; obj* x_28; obj* x_30; obj* x_31; obj* x_32; 
x_16 = lean::cnstr_get(x_0, 0);
x_18 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 x_20 = x_0;
} else {
 lean::inc(x_16);
 lean::inc(x_18);
 lean::dec(x_0);
 x_20 = lean::box(0);
}
lean::inc(x_5);
lean::inc(x_4);
lean::inc(x_3);
lean::inc(x_2);
x_25 = lean::apply_5(x_16, x_2, x_3, x_4, x_5, x_6);
x_26 = lean::cnstr_get(x_25, 0);
x_28 = lean::cnstr_get(x_25, 1);
if (lean::is_exclusive(x_25)) {
 lean::cnstr_set(x_25, 0, lean::box(0));
 lean::cnstr_set(x_25, 1, lean::box(0));
 x_30 = x_25;
} else {
 lean::inc(x_26);
 lean::inc(x_28);
 lean::dec(x_25);
 x_30 = lean::box(0);
}
x_31 = lean::mk_nat_obj(1u);
x_32 = lean::nat_add(x_1, x_31);
if (lean::obj_tag(x_26) == 0)
{
obj* x_33; obj* x_35; obj* x_37; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; 
x_33 = lean::cnstr_get(x_26, 0);
x_35 = lean::cnstr_get(x_26, 1);
x_37 = lean::cnstr_get(x_26, 2);
if (lean::is_exclusive(x_26)) {
 x_39 = x_26;
} else {
 lean::inc(x_33);
 lean::inc(x_35);
 lean::inc(x_37);
 lean::dec(x_26);
 x_39 = lean::box(0);
}
x_40 = lean::box(0);
x_41 = lean_name_mk_numeral(x_40, x_1);
x_42 = lean::box(0);
if (lean::is_scalar(x_20)) {
 x_43 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_43 = x_20;
}
lean::cnstr_set(x_43, 0, x_33);
lean::cnstr_set(x_43, 1, x_42);
x_44 = l_lean_parser_syntax_mk__node(x_41, x_43);
x_45 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_39)) {
 x_46 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_46 = x_39;
}
lean::cnstr_set(x_46, 0, x_44);
lean::cnstr_set(x_46, 1, x_35);
lean::cnstr_set(x_46, 2, x_45);
x_47 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_37, x_46);
if (lean::obj_tag(x_47) == 0)
{
obj* x_54; 
lean::dec(x_5);
lean::dec(x_18);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_32);
if (lean::is_scalar(x_30)) {
 x_54 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_54 = x_30;
}
lean::cnstr_set(x_54, 0, x_47);
lean::cnstr_set(x_54, 1, x_28);
return x_54;
}
else
{
uint8 x_55; 
x_55 = lean::cnstr_get_scalar<uint8>(x_47, sizeof(void*)*1);
if (x_55 == 0)
{
obj* x_57; obj* x_60; obj* x_61; obj* x_63; obj* x_65; obj* x_66; obj* x_67; 
lean::dec(x_30);
x_57 = lean::cnstr_get(x_47, 0);
lean::inc(x_57);
lean::dec(x_47);
x_60 = l_lean_parser_combinators_choice__aux___main___at_lean_parser_level_trailing_parser_lean_parser_has__tokens___spec__1(x_18, x_32, x_2, x_3, x_4, x_5, x_28);
x_61 = lean::cnstr_get(x_60, 0);
x_63 = lean::cnstr_get(x_60, 1);
if (lean::is_exclusive(x_60)) {
 x_65 = x_60;
} else {
 lean::inc(x_61);
 lean::inc(x_63);
 lean::dec(x_60);
 x_65 = lean::box(0);
}
x_66 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_57, x_61);
if (lean::is_scalar(x_65)) {
 x_67 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_67 = x_65;
}
lean::cnstr_set(x_67, 0, x_66);
lean::cnstr_set(x_67, 1, x_63);
return x_67;
}
else
{
obj* x_74; 
lean::dec(x_5);
lean::dec(x_18);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_32);
if (lean::is_scalar(x_30)) {
 x_74 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_74 = x_30;
}
lean::cnstr_set(x_74, 0, x_47);
lean::cnstr_set(x_74, 1, x_28);
return x_74;
}
}
}
else
{
uint8 x_77; 
lean::dec(x_20);
lean::dec(x_1);
x_77 = lean::cnstr_get_scalar<uint8>(x_26, sizeof(void*)*1);
if (x_77 == 0)
{
obj* x_79; obj* x_82; obj* x_83; obj* x_85; obj* x_87; obj* x_88; obj* x_89; 
lean::dec(x_30);
x_79 = lean::cnstr_get(x_26, 0);
lean::inc(x_79);
lean::dec(x_26);
x_82 = l_lean_parser_combinators_choice__aux___main___at_lean_parser_level_trailing_parser_lean_parser_has__tokens___spec__1(x_18, x_32, x_2, x_3, x_4, x_5, x_28);
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
x_88 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_79, x_83);
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
obj* x_96; obj* x_98; obj* x_99; obj* x_100; obj* x_101; 
lean::dec(x_5);
lean::dec(x_18);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_32);
x_96 = lean::cnstr_get(x_26, 0);
if (lean::is_exclusive(x_26)) {
 x_98 = x_26;
} else {
 lean::inc(x_96);
 lean::dec(x_26);
 x_98 = lean::box(0);
}
if (lean::is_scalar(x_98)) {
 x_99 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_99 = x_98;
}
lean::cnstr_set(x_99, 0, x_96);
lean::cnstr_set_scalar(x_99, sizeof(void*)*1, x_77);
x_100 = x_99;
if (lean::is_scalar(x_30)) {
 x_101 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_101 = x_30;
}
lean::cnstr_set(x_101, 0, x_100);
lean::cnstr_set(x_101, 1, x_28);
return x_101;
}
}
}
}
}
obj* _init_l_lean_parser_level_trailing_parser_lean_parser_has__tokens() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_6; obj* x_8; obj* x_10; 
x_0 = lean::box(0);
x_1 = l_lean_parser_level_add__lit_parser_lean_parser_has__tokens;
x_2 = l_lean_parser_list_cons_tokens___rarg(x_1, x_0);
x_3 = l_lean_parser_level_app_parser_lean_parser_has__tokens;
x_4 = l_lean_parser_list_cons_tokens___rarg(x_3, x_2);
lean::dec(x_2);
x_6 = l_lean_parser_tokens___rarg(x_4);
lean::dec(x_4);
x_8 = l_lean_parser_list_cons_tokens___rarg(x_6, x_0);
lean::dec(x_6);
x_10 = l_lean_parser_tokens___rarg(x_8);
lean::dec(x_8);
return x_10;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_level_trailing_parser_lean_parser_has__tokens___spec__2___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
obj* x_9; 
x_9 = l_lean_parser_monad__parsec_error___at_lean_parser_level_trailing_parser_lean_parser_has__tokens___spec__2___rarg(x_0, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean::dec(x_2);
lean::dec(x_4);
lean::dec(x_5);
lean::dec(x_6);
lean::dec(x_7);
return x_9;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_level_trailing_parser_lean_parser_has__tokens___spec__2___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_monad__parsec_error___at_lean_parser_level_trailing_parser_lean_parser_has__tokens___spec__2(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_lean_parser_level_trailing_parser_lean_parser_has__view() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_0 = lean::box(0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_level_add__lit_parser), 5, 0);
x_2 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_2, 0, x_1);
lean::cnstr_set(x_2, 1, x_0);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_level_app_parser), 5, 0);
x_4 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_2);
x_5 = lean::mk_nat_obj(0u);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_choice__aux___main___at_lean_parser_level_trailing_parser_lean_parser_has__tokens___spec__1), 7, 2);
lean::closure_set(x_6, 0, x_4);
lean::closure_set(x_6, 1, x_5);
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_0);
x_8 = l_lean_parser_trailing__level__parser__m_monad;
x_9 = l_lean_parser_trailing__level__parser__m_monad__except;
x_10 = l_lean_parser_trailing__level__parser__m_lean_parser_monad__parsec;
x_11 = l_lean_parser_trailing__level__parser__m_alternative;
x_12 = l_lean_parser_level_trailing;
x_13 = l_lean_parser_level_trailing_has__view;
x_14 = l_lean_parser_combinators_node_view___rarg(x_8, x_9, x_10, x_11, x_12, x_7, x_13);
lean::dec(x_7);
return x_14;
}
}
obj* _init_l_lean_parser_level_trailing_parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_0 = lean::box(0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_level_add__lit_parser), 5, 0);
x_2 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_2, 0, x_1);
lean::cnstr_set(x_2, 1, x_0);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_level_app_parser), 5, 0);
x_4 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_2);
x_5 = lean::mk_nat_obj(0u);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_choice__aux___main___at_lean_parser_level_trailing_parser_lean_parser_has__tokens___spec__1), 7, 2);
lean::closure_set(x_6, 0, x_4);
lean::closure_set(x_6, 1, x_5);
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_0);
return x_7;
}
}
obj* l_lean_parser_level_trailing_parser(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = l_lean_parser_level_trailing;
x_6 = l_lean_parser_level_trailing_parser___closed__1;
x_7 = l_lean_parser_combinators_node___at_lean_parser_level_app_parser___spec__1(x_5, x_6, x_0, x_1, x_2, x_3, x_4);
return x_7;
}
}
obj* l_lean_parser_level__parser_run_lean_parser_has__tokens(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_lean_parser_level_leading_parser_lean_parser_has__tokens;
x_2 = l_lean_parser_level_trailing_parser_lean_parser_has__tokens;
x_3 = l_list_append___rarg(x_1, x_2);
return x_3;
}
}
obj* l_lean_parser_level__parser_run_lean_parser_has__tokens___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_level__parser_run_lean_parser_has__tokens(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_lean_parser_level__parser_run_lean_parser_has__view___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_has__monad__lift__t__refl___boxed), 2, 1);
lean::closure_set(x_0, 0, lean::box(0));
return x_0;
}
}
obj* _init_l_lean_parser_level__parser_run_lean_parser_has__view___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_level_leading_parser), 4, 0);
return x_0;
}
}
obj* _init_l_lean_parser_level__parser_run_lean_parser_has__view___closed__3() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_level_trailing_parser), 5, 0);
return x_0;
}
}
obj* l_lean_parser_level__parser_run_lean_parser_has__view(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = l_lean_parser_basic__parser__m_monad;
x_2 = l_lean_parser_level__parser_run_lean_parser_has__view___closed__1;
x_3 = l_lean_parser_basic__parser__m_lean_parser_monad__parsec;
x_4 = l_lean_parser_basic__parser__m_monad__reader;
x_5 = l_lean_parser_basic__parser__m_monad__except;
x_6 = l_lean_parser_basic__parser__m_alternative;
x_7 = l_lean_parser_level__parser_run_lean_parser_has__view___closed__2;
x_8 = l_lean_parser_level__parser_run_lean_parser_has__view___closed__3;
x_9 = l_lean_parser_pratt__parser_view___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_0);
return x_9;
}
}
obj* l_lean_parser_level__parser_run_lean_parser_has__view___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_level__parser_run_lean_parser_has__view(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_level__parser_run___spec__3___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
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
obj* l_lean_parser_monad__parsec_error___at_lean_parser_level__parser_run___spec__3(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___at_lean_parser_level__parser_run___spec__3___rarg___boxed), 8, 0);
return x_1;
}
}
obj* l_lean_parser_curr__lbp___at_lean_parser_level__parser_run___spec__4(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; obj* x_6; 
lean::inc(x_1);
x_5 = l_lean_parser_monad__parsec_observing___at_lean_parser_peek__token___spec__2___rarg(x_1, x_2, x_3);
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
if (lean::obj_tag(x_6) == 0)
{
obj* x_8; 
x_8 = lean::cnstr_get(x_6, 0);
lean::inc(x_8);
if (lean::obj_tag(x_8) == 0)
{
obj* x_12; obj* x_14; obj* x_15; obj* x_17; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
lean::dec(x_8);
lean::dec(x_1);
x_12 = lean::cnstr_get(x_5, 1);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 x_14 = x_5;
} else {
 lean::inc(x_12);
 lean::dec(x_5);
 x_14 = lean::box(0);
}
x_15 = lean::cnstr_get(x_6, 1);
x_17 = lean::cnstr_get(x_6, 2);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 x_19 = x_6;
} else {
 lean::inc(x_15);
 lean::inc(x_17);
 lean::dec(x_6);
 x_19 = lean::box(0);
}
x_20 = lean::mk_nat_obj(0u);
x_21 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_19)) {
 x_22 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_22 = x_19;
}
lean::cnstr_set(x_22, 0, x_20);
lean::cnstr_set(x_22, 1, x_15);
lean::cnstr_set(x_22, 2, x_21);
x_23 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_17, x_22);
if (lean::is_scalar(x_14)) {
 x_24 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_24 = x_14;
}
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_12);
return x_24;
}
else
{
obj* x_25; 
x_25 = lean::cnstr_get(x_8, 0);
lean::inc(x_25);
lean::dec(x_8);
switch (lean::obj_tag(x_25)) {
case 0:
{
obj* x_28; obj* x_31; obj* x_34; obj* x_36; obj* x_38; obj* x_39; obj* x_42; obj* x_44; obj* x_45; 
x_28 = lean::cnstr_get(x_25, 0);
lean::inc(x_28);
lean::dec(x_25);
x_31 = lean::cnstr_get(x_5, 1);
lean::inc(x_31);
lean::dec(x_5);
x_34 = lean::cnstr_get(x_6, 1);
x_36 = lean::cnstr_get(x_6, 2);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 lean::cnstr_set(x_6, 1, lean::box(0));
 lean::cnstr_set(x_6, 2, lean::box(0));
 x_38 = x_6;
} else {
 lean::inc(x_34);
 lean::inc(x_36);
 lean::dec(x_6);
 x_38 = lean::box(0);
}
x_39 = lean::cnstr_get(x_28, 1);
lean::inc(x_39);
lean::dec(x_28);
x_42 = lean::cnstr_get(x_1, 1);
lean::inc(x_42);
x_44 = lean::string_mk_iterator(x_39);
x_45 = l_lean_parser_trie_match__prefix___rarg(x_42, x_44);
if (lean::obj_tag(x_45) == 0)
{
obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_53; obj* x_55; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; 
lean::dec(x_38);
x_47 = lean::box(0);
x_48 = l_lean_parser_curr__lbp___rarg___lambda__1___closed__1;
x_49 = l_mjoin___rarg___closed__1;
x_50 = l_lean_parser_monad__parsec_error___at_lean_parser_level__parser_run___spec__3___rarg(x_48, x_49, x_47, x_47, x_0, x_1, x_34, x_31);
lean::dec(x_34);
lean::dec(x_1);
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
x_58 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
x_59 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_58, x_53);
x_60 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_58, x_59);
x_61 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_36, x_60);
if (lean::is_scalar(x_57)) {
 x_62 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_62 = x_57;
}
lean::cnstr_set(x_62, 0, x_61);
lean::cnstr_set(x_62, 1, x_55);
return x_62;
}
else
{
obj* x_64; obj* x_67; obj* x_69; obj* x_70; obj* x_73; obj* x_74; obj* x_75; obj* x_76; 
lean::dec(x_1);
x_64 = lean::cnstr_get(x_45, 0);
lean::inc(x_64);
lean::dec(x_45);
x_67 = lean::cnstr_get(x_64, 1);
if (lean::is_exclusive(x_64)) {
 lean::cnstr_release(x_64, 0);
 x_69 = x_64;
} else {
 lean::inc(x_67);
 lean::dec(x_64);
 x_69 = lean::box(0);
}
x_70 = lean::cnstr_get(x_67, 1);
lean::inc(x_70);
lean::dec(x_67);
x_73 = l_lean_parser_match__token___closed__1;
if (lean::is_scalar(x_38)) {
 x_74 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_74 = x_38;
}
lean::cnstr_set(x_74, 0, x_70);
lean::cnstr_set(x_74, 1, x_34);
lean::cnstr_set(x_74, 2, x_73);
x_75 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_36, x_74);
if (lean::is_scalar(x_69)) {
 x_76 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_76 = x_69;
}
lean::cnstr_set(x_76, 0, x_75);
lean::cnstr_set(x_76, 1, x_31);
return x_76;
}
}
case 1:
{
obj* x_79; obj* x_81; obj* x_82; obj* x_84; obj* x_86; obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; 
lean::dec(x_1);
lean::dec(x_25);
x_79 = lean::cnstr_get(x_5, 1);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 x_81 = x_5;
} else {
 lean::inc(x_79);
 lean::dec(x_5);
 x_81 = lean::box(0);
}
x_82 = lean::cnstr_get(x_6, 1);
x_84 = lean::cnstr_get(x_6, 2);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 x_86 = x_6;
} else {
 lean::inc(x_82);
 lean::inc(x_84);
 lean::dec(x_6);
 x_86 = lean::box(0);
}
x_87 = l_lean_parser_max__prec;
x_88 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_86)) {
 x_89 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_89 = x_86;
}
lean::cnstr_set(x_89, 0, x_87);
lean::cnstr_set(x_89, 1, x_82);
lean::cnstr_set(x_89, 2, x_88);
x_90 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_84, x_89);
if (lean::is_scalar(x_81)) {
 x_91 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_91 = x_81;
}
lean::cnstr_set(x_91, 0, x_90);
lean::cnstr_set(x_91, 1, x_79);
return x_91;
}
case 2:
{
obj* x_92; obj* x_95; obj* x_97; obj* x_98; obj* x_100; obj* x_102; obj* x_103; obj* x_106; uint8 x_107; 
x_92 = lean::cnstr_get(x_25, 0);
lean::inc(x_92);
lean::dec(x_25);
x_95 = lean::cnstr_get(x_5, 1);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 lean::cnstr_set(x_5, 1, lean::box(0));
 x_97 = x_5;
} else {
 lean::inc(x_95);
 lean::dec(x_5);
 x_97 = lean::box(0);
}
x_98 = lean::cnstr_get(x_6, 1);
x_100 = lean::cnstr_get(x_6, 2);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 lean::cnstr_set(x_6, 1, lean::box(0));
 lean::cnstr_set(x_6, 2, lean::box(0));
 x_102 = x_6;
} else {
 lean::inc(x_98);
 lean::inc(x_100);
 lean::dec(x_6);
 x_102 = lean::box(0);
}
x_103 = lean::cnstr_get(x_92, 0);
lean::inc(x_103);
lean::dec(x_92);
x_106 = l_lean_parser_number_has__view_x_27___lambda__1___closed__6;
x_107 = lean_name_dec_eq(x_103, x_106);
if (x_107 == 0)
{
obj* x_108; uint8 x_109; 
x_108 = l_lean_parser_curr__lbp___rarg___lambda__3___closed__1;
x_109 = lean_name_dec_eq(x_103, x_108);
lean::dec(x_103);
if (x_109 == 0)
{
obj* x_113; obj* x_114; obj* x_115; obj* x_116; obj* x_119; obj* x_121; obj* x_123; obj* x_124; obj* x_125; 
lean::dec(x_102);
lean::dec(x_97);
x_113 = lean::box(0);
x_114 = l_lean_parser_curr__lbp___rarg___lambda__3___closed__2;
x_115 = l_mjoin___rarg___closed__1;
x_116 = l_lean_parser_monad__parsec_error___at_lean_parser_level__parser_run___spec__3___rarg(x_114, x_115, x_113, x_113, x_0, x_1, x_98, x_95);
lean::dec(x_98);
lean::dec(x_1);
x_119 = lean::cnstr_get(x_116, 0);
x_121 = lean::cnstr_get(x_116, 1);
if (lean::is_exclusive(x_116)) {
 x_123 = x_116;
} else {
 lean::inc(x_119);
 lean::inc(x_121);
 lean::dec(x_116);
 x_123 = lean::box(0);
}
x_124 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_100, x_119);
if (lean::is_scalar(x_123)) {
 x_125 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_125 = x_123;
}
lean::cnstr_set(x_125, 0, x_124);
lean::cnstr_set(x_125, 1, x_121);
return x_125;
}
else
{
obj* x_127; obj* x_128; obj* x_129; obj* x_130; obj* x_131; 
lean::dec(x_1);
x_127 = l_lean_parser_max__prec;
x_128 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_102)) {
 x_129 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_129 = x_102;
}
lean::cnstr_set(x_129, 0, x_127);
lean::cnstr_set(x_129, 1, x_98);
lean::cnstr_set(x_129, 2, x_128);
x_130 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_100, x_129);
if (lean::is_scalar(x_97)) {
 x_131 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_131 = x_97;
}
lean::cnstr_set(x_131, 0, x_130);
lean::cnstr_set(x_131, 1, x_95);
return x_131;
}
}
else
{
obj* x_134; obj* x_135; obj* x_136; obj* x_137; obj* x_138; 
lean::dec(x_1);
lean::dec(x_103);
x_134 = l_lean_parser_max__prec;
x_135 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_102)) {
 x_136 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_136 = x_102;
}
lean::cnstr_set(x_136, 0, x_134);
lean::cnstr_set(x_136, 1, x_98);
lean::cnstr_set(x_136, 2, x_135);
x_137 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_100, x_136);
if (lean::is_scalar(x_97)) {
 x_138 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_138 = x_97;
}
lean::cnstr_set(x_138, 0, x_137);
lean::cnstr_set(x_138, 1, x_95);
return x_138;
}
}
default:
{
obj* x_139; obj* x_142; obj* x_144; obj* x_147; obj* x_148; obj* x_149; obj* x_150; obj* x_153; obj* x_155; obj* x_157; obj* x_158; obj* x_159; 
x_139 = lean::cnstr_get(x_5, 1);
lean::inc(x_139);
lean::dec(x_5);
x_142 = lean::cnstr_get(x_6, 1);
lean::inc(x_142);
x_144 = lean::cnstr_get(x_6, 2);
lean::inc(x_144);
lean::dec(x_6);
x_147 = lean::box(0);
x_148 = l_lean_parser_curr__lbp___rarg___lambda__3___closed__2;
x_149 = l_mjoin___rarg___closed__1;
x_150 = l_lean_parser_monad__parsec_error___at_lean_parser_level__parser_run___spec__3___rarg(x_148, x_149, x_147, x_147, x_0, x_1, x_142, x_139);
lean::dec(x_142);
lean::dec(x_1);
x_153 = lean::cnstr_get(x_150, 0);
x_155 = lean::cnstr_get(x_150, 1);
if (lean::is_exclusive(x_150)) {
 x_157 = x_150;
} else {
 lean::inc(x_153);
 lean::inc(x_155);
 lean::dec(x_150);
 x_157 = lean::box(0);
}
x_158 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_144, x_153);
if (lean::is_scalar(x_157)) {
 x_159 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_159 = x_157;
}
lean::cnstr_set(x_159, 0, x_158);
lean::cnstr_set(x_159, 1, x_155);
return x_159;
}
}
}
}
else
{
obj* x_161; obj* x_163; obj* x_164; uint8 x_166; obj* x_167; obj* x_168; obj* x_169; obj* x_170; 
lean::dec(x_1);
x_161 = lean::cnstr_get(x_5, 1);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 x_163 = x_5;
} else {
 lean::inc(x_161);
 lean::dec(x_5);
 x_163 = lean::box(0);
}
x_164 = lean::cnstr_get(x_6, 0);
x_166 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*1);
if (lean::is_exclusive(x_6)) {
 x_167 = x_6;
} else {
 lean::inc(x_164);
 lean::dec(x_6);
 x_167 = lean::box(0);
}
if (lean::is_scalar(x_167)) {
 x_168 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_168 = x_167;
}
lean::cnstr_set(x_168, 0, x_164);
lean::cnstr_set_scalar(x_168, sizeof(void*)*1, x_166);
x_169 = x_168;
if (lean::is_scalar(x_163)) {
 x_170 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_170 = x_163;
}
lean::cnstr_set(x_170, 0, x_169);
lean::cnstr_set(x_170, 1, x_161);
return x_170;
}
}
}
obj* l___private_init_lean_parser_pratt_1__trailing__loop___main___at_lean_parser_level__parser_run___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; uint8 x_9; 
x_8 = lean::mk_nat_obj(0u);
x_9 = lean::nat_dec_eq(x_2, x_8);
if (x_9 == 0)
{
obj* x_11; obj* x_12; 
lean::inc(x_5);
x_11 = l_lean_parser_curr__lbp___at_lean_parser_level__parser_run___spec__4(x_4, x_5, x_6, x_7);
x_12 = lean::cnstr_get(x_11, 0);
lean::inc(x_12);
if (lean::obj_tag(x_12) == 0)
{
obj* x_14; obj* x_16; obj* x_17; obj* x_19; obj* x_21; obj* x_23; uint8 x_24; 
x_14 = lean::cnstr_get(x_11, 1);
if (lean::is_exclusive(x_11)) {
 lean::cnstr_release(x_11, 0);
 lean::cnstr_set(x_11, 1, lean::box(0));
 x_16 = x_11;
} else {
 lean::inc(x_14);
 lean::dec(x_11);
 x_16 = lean::box(0);
}
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
x_24 = lean::nat_dec_lt(x_1, x_17);
lean::dec(x_17);
if (x_24 == 0)
{
obj* x_29; obj* x_30; obj* x_31; obj* x_32; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_0);
x_29 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
if (lean::is_scalar(x_23)) {
 x_30 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_30 = x_23;
}
lean::cnstr_set(x_30, 0, x_3);
lean::cnstr_set(x_30, 1, x_19);
lean::cnstr_set(x_30, 2, x_29);
x_31 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_21, x_30);
if (lean::is_scalar(x_16)) {
 x_32 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_32 = x_16;
}
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_14);
return x_32;
}
else
{
obj* x_35; obj* x_36; obj* x_40; obj* x_41; 
lean::dec(x_16);
lean::dec(x_23);
x_35 = lean::mk_nat_obj(1u);
x_36 = lean::nat_sub(x_2, x_35);
lean::inc(x_5);
lean::inc(x_4);
lean::inc(x_0);
x_40 = lean::apply_5(x_0, x_3, x_4, x_5, x_19, x_14);
x_41 = lean::cnstr_get(x_40, 0);
lean::inc(x_41);
if (lean::obj_tag(x_41) == 0)
{
obj* x_43; obj* x_46; obj* x_48; obj* x_50; obj* x_53; obj* x_55; obj* x_57; obj* x_59; obj* x_60; obj* x_61; obj* x_62; 
x_43 = lean::cnstr_get(x_40, 1);
lean::inc(x_43);
lean::dec(x_40);
x_46 = lean::cnstr_get(x_41, 0);
lean::inc(x_46);
x_48 = lean::cnstr_get(x_41, 1);
lean::inc(x_48);
x_50 = lean::cnstr_get(x_41, 2);
lean::inc(x_50);
lean::dec(x_41);
x_53 = l___private_init_lean_parser_pratt_1__trailing__loop___main___at_lean_parser_level__parser_run___spec__2(x_0, x_1, x_36, x_46, x_4, x_5, x_48, x_43);
lean::dec(x_36);
x_55 = lean::cnstr_get(x_53, 0);
x_57 = lean::cnstr_get(x_53, 1);
if (lean::is_exclusive(x_53)) {
 x_59 = x_53;
} else {
 lean::inc(x_55);
 lean::inc(x_57);
 lean::dec(x_53);
 x_59 = lean::box(0);
}
x_60 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_50, x_55);
x_61 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_21, x_60);
if (lean::is_scalar(x_59)) {
 x_62 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_62 = x_59;
}
lean::cnstr_set(x_62, 0, x_61);
lean::cnstr_set(x_62, 1, x_57);
return x_62;
}
else
{
obj* x_67; obj* x_69; obj* x_70; uint8 x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_0);
lean::dec(x_36);
x_67 = lean::cnstr_get(x_40, 1);
if (lean::is_exclusive(x_40)) {
 lean::cnstr_release(x_40, 0);
 x_69 = x_40;
} else {
 lean::inc(x_67);
 lean::dec(x_40);
 x_69 = lean::box(0);
}
x_70 = lean::cnstr_get(x_41, 0);
x_72 = lean::cnstr_get_scalar<uint8>(x_41, sizeof(void*)*1);
if (lean::is_exclusive(x_41)) {
 x_73 = x_41;
} else {
 lean::inc(x_70);
 lean::dec(x_41);
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
x_76 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_21, x_75);
if (lean::is_scalar(x_69)) {
 x_77 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_77 = x_69;
}
lean::cnstr_set(x_77, 0, x_76);
lean::cnstr_set(x_77, 1, x_67);
return x_77;
}
}
}
else
{
obj* x_82; obj* x_84; obj* x_85; uint8 x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_0);
x_82 = lean::cnstr_get(x_11, 1);
if (lean::is_exclusive(x_11)) {
 lean::cnstr_release(x_11, 0);
 x_84 = x_11;
} else {
 lean::inc(x_82);
 lean::dec(x_11);
 x_84 = lean::box(0);
}
x_85 = lean::cnstr_get(x_12, 0);
x_87 = lean::cnstr_get_scalar<uint8>(x_12, sizeof(void*)*1);
if (lean::is_exclusive(x_12)) {
 x_88 = x_12;
} else {
 lean::inc(x_85);
 lean::dec(x_12);
 x_88 = lean::box(0);
}
if (lean::is_scalar(x_88)) {
 x_89 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_89 = x_88;
}
lean::cnstr_set(x_89, 0, x_85);
lean::cnstr_set_scalar(x_89, sizeof(void*)*1, x_87);
x_90 = x_89;
if (lean::is_scalar(x_84)) {
 x_91 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_91 = x_84;
}
lean::cnstr_set(x_91, 0, x_90);
lean::cnstr_set(x_91, 1, x_82);
return x_91;
}
}
else
{
obj* x_94; obj* x_95; obj* x_96; obj* x_97; 
lean::dec(x_3);
lean::dec(x_0);
x_94 = lean::box(0);
x_95 = l___private_init_lean_parser_combinators_1__many1__aux___main___rarg___closed__1;
x_96 = l_mjoin___rarg___closed__1;
x_97 = l_lean_parser_monad__parsec_error___at_lean_parser_level__parser_run___spec__3___rarg(x_95, x_96, x_94, x_94, x_4, x_5, x_6, x_7);
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_4);
return x_97;
}
}
}
obj* l___private_init_lean_parser_rec_1__run__aux___at_lean_parser_level__parser_run___spec__7(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_8; 
x_7 = l___private_init_lean_parser_rec_1__run__aux___main___rarg(x_0, x_1, x_2, x_3);
x_8 = lean::apply_3(x_7, x_4, x_5, x_6);
return x_8;
}
}
obj* l_lean_parser_rec__t_run___at_lean_parser_level__parser_run___spec__6(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_8; 
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_rec_1__run__aux___at_lean_parser_level__parser_run___spec__7___boxed), 7, 3);
lean::closure_set(x_7, 0, x_1);
lean::closure_set(x_7, 1, x_2);
lean::closure_set(x_7, 2, x_3);
x_8 = lean::apply_4(x_0, x_7, x_4, x_5, x_6);
return x_8;
}
}
obj* l_lean_parser_rec__t_run__parsec___at_lean_parser_level__parser_run___spec__5(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; obj* x_9; obj* x_10; obj* x_11; obj* x_13; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_5 = lean::string_iterator_remaining(x_3);
x_6 = lean::mk_nat_obj(1u);
x_7 = lean::nat_add(x_5, x_6);
lean::dec(x_5);
x_9 = l_lean_parser_rec__t_run__parsec___at_lean_parser_detail__ident_parser___spec__1___closed__1;
x_10 = l_lean_parser_rec__t_run___at_lean_parser_level__parser_run___spec__6(x_0, x_9, x_1, x_7, x_2, x_3, x_4);
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
obj* l_lean_parser_pratt__parser___at_lean_parser_level__parser_run___spec__1___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_9; obj* x_10; 
lean::inc(x_4);
lean::inc(x_3);
x_9 = lean::apply_4(x_0, x_3, x_4, x_5, x_6);
x_10 = lean::cnstr_get(x_9, 0);
lean::inc(x_10);
if (lean::obj_tag(x_10) == 0)
{
obj* x_12; obj* x_15; obj* x_17; obj* x_19; obj* x_22; obj* x_23; obj* x_24; obj* x_26; obj* x_28; obj* x_30; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; 
x_12 = lean::cnstr_get(x_9, 1);
lean::inc(x_12);
lean::dec(x_9);
x_15 = lean::cnstr_get(x_10, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_10, 1);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_10, 2);
lean::inc(x_19);
lean::dec(x_10);
x_22 = lean::string_iterator_remaining(x_17);
x_23 = lean::mk_nat_obj(1u);
x_24 = lean::nat_add(x_22, x_23);
lean::dec(x_22);
x_26 = l___private_init_lean_parser_pratt_1__trailing__loop___main___at_lean_parser_level__parser_run___spec__2(x_1, x_2, x_24, x_15, x_3, x_4, x_17, x_12);
lean::dec(x_24);
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
x_33 = l_lean_parser_finish__comment__block___closed__2;
x_34 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_33, x_28);
x_35 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_19, x_34);
if (lean::is_scalar(x_32)) {
 x_36 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_36 = x_32;
}
lean::cnstr_set(x_36, 0, x_35);
lean::cnstr_set(x_36, 1, x_30);
return x_36;
}
else
{
obj* x_40; obj* x_42; obj* x_43; uint8 x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; 
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_3);
x_40 = lean::cnstr_get(x_9, 1);
if (lean::is_exclusive(x_9)) {
 lean::cnstr_release(x_9, 0);
 x_42 = x_9;
} else {
 lean::inc(x_40);
 lean::dec(x_9);
 x_42 = lean::box(0);
}
x_43 = lean::cnstr_get(x_10, 0);
x_45 = lean::cnstr_get_scalar<uint8>(x_10, sizeof(void*)*1);
if (lean::is_exclusive(x_10)) {
 x_46 = x_10;
} else {
 lean::inc(x_43);
 lean::dec(x_10);
 x_46 = lean::box(0);
}
if (lean::is_scalar(x_46)) {
 x_47 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_47 = x_46;
}
lean::cnstr_set(x_47, 0, x_43);
lean::cnstr_set_scalar(x_47, sizeof(void*)*1, x_45);
x_48 = x_47;
if (lean::is_scalar(x_42)) {
 x_49 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_49 = x_42;
}
lean::cnstr_set(x_49, 0, x_48);
lean::cnstr_set(x_49, 1, x_40);
return x_49;
}
}
}
obj* l_lean_parser_pratt__parser___at_lean_parser_level__parser_run___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; 
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_pratt__parser___at_lean_parser_level__parser_run___spec__1___lambda__1___boxed), 7, 2);
lean::closure_set(x_6, 0, x_0);
lean::closure_set(x_6, 1, x_1);
x_7 = l_lean_parser_rec__t_run__parsec___at_lean_parser_level__parser_run___spec__5(x_2, x_6, x_3, x_4, x_5);
return x_7;
}
}
obj* l_lean_parser_level__parser_run(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = l_lean_parser_level__parser_run_lean_parser_has__view___closed__2;
x_5 = l_lean_parser_level__parser_run_lean_parser_has__view___closed__3;
x_6 = l_lean_parser_pratt__parser___at_lean_parser_level__parser_run___spec__1(x_4, x_5, x_0, x_1, x_2, x_3);
return x_6;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_level__parser_run___spec__3___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = l_lean_parser_monad__parsec_error___at_lean_parser_level__parser_run___spec__3___rarg(x_0, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean::dec(x_2);
lean::dec(x_4);
lean::dec(x_5);
lean::dec(x_6);
return x_8;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_level__parser_run___spec__3___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_monad__parsec_error___at_lean_parser_level__parser_run___spec__3(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_parser_curr__lbp___at_lean_parser_level__parser_run___spec__4___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_parser_curr__lbp___at_lean_parser_level__parser_run___spec__4(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l___private_init_lean_parser_pratt_1__trailing__loop___main___at_lean_parser_level__parser_run___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = l___private_init_lean_parser_pratt_1__trailing__loop___main___at_lean_parser_level__parser_run___spec__2(x_0, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean::dec(x_1);
lean::dec(x_2);
return x_8;
}
}
obj* l___private_init_lean_parser_rec_1__run__aux___at_lean_parser_level__parser_run___spec__7___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l___private_init_lean_parser_rec_1__run__aux___at_lean_parser_level__parser_run___spec__7(x_0, x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_2);
return x_7;
}
}
obj* l_lean_parser_pratt__parser___at_lean_parser_level__parser_run___spec__1___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_lean_parser_pratt__parser___at_lean_parser_level__parser_run___spec__1___lambda__1(x_0, x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_2);
return x_7;
}
}
obj* _init_l_lean_parser_level__parser__coe() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_level__parser_run), 4, 0);
return x_0;
}
}
void initialize_init_lean_parser_pratt();
static bool _G_initialized = false;
void initialize_init_lean_parser_level() {
 if (_G_initialized) return;
 _G_initialized = true;
 initialize_init_lean_parser_pratt();
 l_lean_parser_level__parser__m_monad = _init_l_lean_parser_level__parser__m_monad();
lean::mark_persistent(l_lean_parser_level__parser__m_monad);
 l_lean_parser_level__parser__m_alternative = _init_l_lean_parser_level__parser__m_alternative();
lean::mark_persistent(l_lean_parser_level__parser__m_alternative);
 l_lean_parser_level__parser__m_monad__reader = _init_l_lean_parser_level__parser__m_monad__reader();
lean::mark_persistent(l_lean_parser_level__parser__m_monad__reader);
 l_lean_parser_level__parser__m_lean_parser_monad__parsec = _init_l_lean_parser_level__parser__m_lean_parser_monad__parsec();
lean::mark_persistent(l_lean_parser_level__parser__m_lean_parser_monad__parsec);
 l_lean_parser_level__parser__m_monad__except = _init_l_lean_parser_level__parser__m_monad__except();
lean::mark_persistent(l_lean_parser_level__parser__m_monad__except);
 l_lean_parser_level__parser__m_lean_parser_monad__rec = _init_l_lean_parser_level__parser__m_lean_parser_monad__rec();
lean::mark_persistent(l_lean_parser_level__parser__m_lean_parser_monad__rec);
 l_lean_parser_level__parser__m_lean_parser_monad__basic__parser = _init_l_lean_parser_level__parser__m_lean_parser_monad__basic__parser();
lean::mark_persistent(l_lean_parser_level__parser__m_lean_parser_monad__basic__parser);
 l_lean_parser_trailing__level__parser__m_monad = _init_l_lean_parser_trailing__level__parser__m_monad();
lean::mark_persistent(l_lean_parser_trailing__level__parser__m_monad);
 l_lean_parser_trailing__level__parser__m_alternative = _init_l_lean_parser_trailing__level__parser__m_alternative();
lean::mark_persistent(l_lean_parser_trailing__level__parser__m_alternative);
 l_lean_parser_trailing__level__parser__m_monad__reader = _init_l_lean_parser_trailing__level__parser__m_monad__reader();
lean::mark_persistent(l_lean_parser_trailing__level__parser__m_monad__reader);
 l_lean_parser_trailing__level__parser__m_lean_parser_monad__parsec = _init_l_lean_parser_trailing__level__parser__m_lean_parser_monad__parsec();
lean::mark_persistent(l_lean_parser_trailing__level__parser__m_lean_parser_monad__parsec);
 l_lean_parser_trailing__level__parser__m_monad__except = _init_l_lean_parser_trailing__level__parser__m_monad__except();
lean::mark_persistent(l_lean_parser_trailing__level__parser__m_monad__except);
 l_lean_parser_trailing__level__parser__m_lean_parser_monad__rec = _init_l_lean_parser_trailing__level__parser__m_lean_parser_monad__rec();
lean::mark_persistent(l_lean_parser_trailing__level__parser__m_lean_parser_monad__rec);
 l_lean_parser_trailing__level__parser__m_lean_parser_monad__basic__parser = _init_l_lean_parser_trailing__level__parser__m_lean_parser_monad__basic__parser();
lean::mark_persistent(l_lean_parser_trailing__level__parser__m_lean_parser_monad__basic__parser);
 l_lean_parser_level_parser_lean_parser_has__tokens___closed__1 = _init_l_lean_parser_level_parser_lean_parser_has__tokens___closed__1();
lean::mark_persistent(l_lean_parser_level_parser_lean_parser_has__tokens___closed__1);
 l_lean_parser_level_parser_lean_parser_has__view___closed__1 = _init_l_lean_parser_level_parser_lean_parser_has__view___closed__1();
lean::mark_persistent(l_lean_parser_level_parser_lean_parser_has__view___closed__1);
 l_lean_parser_level_parser___closed__1 = _init_l_lean_parser_level_parser___closed__1();
lean::mark_persistent(l_lean_parser_level_parser___closed__1);
 l_lean_parser_level_lean_parser_has__tokens = _init_l_lean_parser_level_lean_parser_has__tokens();
lean::mark_persistent(l_lean_parser_level_lean_parser_has__tokens);
 l_lean_parser_level_lean_parser_has__view = _init_l_lean_parser_level_lean_parser_has__view();
lean::mark_persistent(l_lean_parser_level_lean_parser_has__view);
 l_lean_parser_level_paren = _init_l_lean_parser_level_paren();
lean::mark_persistent(l_lean_parser_level_paren);
 l_lean_parser_level_paren_has__view_x_27___lambda__1___closed__1 = _init_l_lean_parser_level_paren_has__view_x_27___lambda__1___closed__1();
lean::mark_persistent(l_lean_parser_level_paren_has__view_x_27___lambda__1___closed__1);
 l_lean_parser_level_paren_has__view_x_27 = _init_l_lean_parser_level_paren_has__view_x_27();
lean::mark_persistent(l_lean_parser_level_paren_has__view_x_27);
 l_lean_parser_level_paren_has__view = _init_l_lean_parser_level_paren_has__view();
lean::mark_persistent(l_lean_parser_level_paren_has__view);
 l_lean_parser_level_paren_parser_lean_parser_has__tokens = _init_l_lean_parser_level_paren_parser_lean_parser_has__tokens();
lean::mark_persistent(l_lean_parser_level_paren_parser_lean_parser_has__tokens);
 l_lean_parser_level_paren_parser_lean_parser_has__view = _init_l_lean_parser_level_paren_parser_lean_parser_has__view();
lean::mark_persistent(l_lean_parser_level_paren_parser_lean_parser_has__view);
 l_lean_parser_level_paren_parser___closed__1 = _init_l_lean_parser_level_paren_parser___closed__1();
lean::mark_persistent(l_lean_parser_level_paren_parser___closed__1);
 l_lean_parser_level_leading = _init_l_lean_parser_level_leading();
lean::mark_persistent(l_lean_parser_level_leading);
 l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__1 = _init_l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__1();
lean::mark_persistent(l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__1);
 l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__2 = _init_l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__2();
lean::mark_persistent(l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__2);
 l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__3 = _init_l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__3();
lean::mark_persistent(l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__3);
 l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__4 = _init_l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__4();
lean::mark_persistent(l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__4);
 l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__5 = _init_l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__5();
lean::mark_persistent(l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__5);
 l_lean_parser_level_leading_has__view_x_27___lambda__2___closed__1 = _init_l_lean_parser_level_leading_has__view_x_27___lambda__2___closed__1();
lean::mark_persistent(l_lean_parser_level_leading_has__view_x_27___lambda__2___closed__1);
 l_lean_parser_level_leading_has__view_x_27___lambda__2___closed__2 = _init_l_lean_parser_level_leading_has__view_x_27___lambda__2___closed__2();
lean::mark_persistent(l_lean_parser_level_leading_has__view_x_27___lambda__2___closed__2);
 l_lean_parser_level_leading_has__view_x_27___lambda__2___closed__3 = _init_l_lean_parser_level_leading_has__view_x_27___lambda__2___closed__3();
lean::mark_persistent(l_lean_parser_level_leading_has__view_x_27___lambda__2___closed__3);
 l_lean_parser_level_leading_has__view_x_27 = _init_l_lean_parser_level_leading_has__view_x_27();
lean::mark_persistent(l_lean_parser_level_leading_has__view_x_27);
 l_lean_parser_level_leading_has__view = _init_l_lean_parser_level_leading_has__view();
lean::mark_persistent(l_lean_parser_level_leading_has__view);
 l_lean_parser_number_parser___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__2___rarg___closed__1 = _init_l_lean_parser_number_parser___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__2___rarg___closed__1();
lean::mark_persistent(l_lean_parser_number_parser___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__2___rarg___closed__1);
 l_lean_parser_ident_parser___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__3___rarg___closed__1 = _init_l_lean_parser_ident_parser___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__3___rarg___closed__1();
lean::mark_persistent(l_lean_parser_ident_parser___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__3___rarg___closed__1);
 l_lean_parser_level_leading_parser_lean_parser_has__tokens = _init_l_lean_parser_level_leading_parser_lean_parser_has__tokens();
lean::mark_persistent(l_lean_parser_level_leading_parser_lean_parser_has__tokens);
 l_lean_parser_level_leading_parser_lean_parser_has__view = _init_l_lean_parser_level_leading_parser_lean_parser_has__view();
lean::mark_persistent(l_lean_parser_level_leading_parser_lean_parser_has__view);
 l_lean_parser_level_leading_parser___closed__1 = _init_l_lean_parser_level_leading_parser___closed__1();
lean::mark_persistent(l_lean_parser_level_leading_parser___closed__1);
 l_lean_parser_level_app = _init_l_lean_parser_level_app();
lean::mark_persistent(l_lean_parser_level_app);
 l_lean_parser_level_app_has__view_x_27___lambda__1___closed__1 = _init_l_lean_parser_level_app_has__view_x_27___lambda__1___closed__1();
lean::mark_persistent(l_lean_parser_level_app_has__view_x_27___lambda__1___closed__1);
 l_lean_parser_level_app_has__view_x_27 = _init_l_lean_parser_level_app_has__view_x_27();
lean::mark_persistent(l_lean_parser_level_app_has__view_x_27);
 l_lean_parser_level_app_has__view = _init_l_lean_parser_level_app_has__view();
lean::mark_persistent(l_lean_parser_level_app_has__view);
 l_lean_parser_level_app_parser_lean_parser_has__tokens = _init_l_lean_parser_level_app_parser_lean_parser_has__tokens();
lean::mark_persistent(l_lean_parser_level_app_parser_lean_parser_has__tokens);
 l_lean_parser_level_app_parser_lean_parser_has__view = _init_l_lean_parser_level_app_parser_lean_parser_has__view();
lean::mark_persistent(l_lean_parser_level_app_parser_lean_parser_has__view);
 l_lean_parser_level_app_parser___closed__1 = _init_l_lean_parser_level_app_parser___closed__1();
lean::mark_persistent(l_lean_parser_level_app_parser___closed__1);
 l_lean_parser_level_add__lit = _init_l_lean_parser_level_add__lit();
lean::mark_persistent(l_lean_parser_level_add__lit);
 l_lean_parser_level_add__lit_has__view_x_27___lambda__1___closed__1 = _init_l_lean_parser_level_add__lit_has__view_x_27___lambda__1___closed__1();
lean::mark_persistent(l_lean_parser_level_add__lit_has__view_x_27___lambda__1___closed__1);
 l_lean_parser_level_add__lit_has__view_x_27___lambda__1___closed__2 = _init_l_lean_parser_level_add__lit_has__view_x_27___lambda__1___closed__2();
lean::mark_persistent(l_lean_parser_level_add__lit_has__view_x_27___lambda__1___closed__2);
 l_lean_parser_level_add__lit_has__view_x_27 = _init_l_lean_parser_level_add__lit_has__view_x_27();
lean::mark_persistent(l_lean_parser_level_add__lit_has__view_x_27);
 l_lean_parser_level_add__lit_has__view = _init_l_lean_parser_level_add__lit_has__view();
lean::mark_persistent(l_lean_parser_level_add__lit_has__view);
 l_lean_parser_level_add__lit_parser_lean_parser_has__tokens = _init_l_lean_parser_level_add__lit_parser_lean_parser_has__tokens();
lean::mark_persistent(l_lean_parser_level_add__lit_parser_lean_parser_has__tokens);
 l_lean_parser_level_add__lit_parser_lean_parser_has__view = _init_l_lean_parser_level_add__lit_parser_lean_parser_has__view();
lean::mark_persistent(l_lean_parser_level_add__lit_parser_lean_parser_has__view);
 l_lean_parser_level_add__lit_parser___closed__1 = _init_l_lean_parser_level_add__lit_parser___closed__1();
lean::mark_persistent(l_lean_parser_level_add__lit_parser___closed__1);
 l_lean_parser_level_trailing = _init_l_lean_parser_level_trailing();
lean::mark_persistent(l_lean_parser_level_trailing);
 l_lean_parser_level_trailing_has__view_x_27___lambda__1___closed__1 = _init_l_lean_parser_level_trailing_has__view_x_27___lambda__1___closed__1();
lean::mark_persistent(l_lean_parser_level_trailing_has__view_x_27___lambda__1___closed__1);
 l_lean_parser_level_trailing_has__view_x_27___lambda__1___closed__2 = _init_l_lean_parser_level_trailing_has__view_x_27___lambda__1___closed__2();
lean::mark_persistent(l_lean_parser_level_trailing_has__view_x_27___lambda__1___closed__2);
 l_lean_parser_level_trailing_has__view_x_27 = _init_l_lean_parser_level_trailing_has__view_x_27();
lean::mark_persistent(l_lean_parser_level_trailing_has__view_x_27);
 l_lean_parser_level_trailing_has__view = _init_l_lean_parser_level_trailing_has__view();
lean::mark_persistent(l_lean_parser_level_trailing_has__view);
 l_lean_parser_level_trailing_parser_lean_parser_has__tokens = _init_l_lean_parser_level_trailing_parser_lean_parser_has__tokens();
lean::mark_persistent(l_lean_parser_level_trailing_parser_lean_parser_has__tokens);
 l_lean_parser_level_trailing_parser_lean_parser_has__view = _init_l_lean_parser_level_trailing_parser_lean_parser_has__view();
lean::mark_persistent(l_lean_parser_level_trailing_parser_lean_parser_has__view);
 l_lean_parser_level_trailing_parser___closed__1 = _init_l_lean_parser_level_trailing_parser___closed__1();
lean::mark_persistent(l_lean_parser_level_trailing_parser___closed__1);
 l_lean_parser_level__parser_run_lean_parser_has__view___closed__1 = _init_l_lean_parser_level__parser_run_lean_parser_has__view___closed__1();
lean::mark_persistent(l_lean_parser_level__parser_run_lean_parser_has__view___closed__1);
 l_lean_parser_level__parser_run_lean_parser_has__view___closed__2 = _init_l_lean_parser_level__parser_run_lean_parser_has__view___closed__2();
lean::mark_persistent(l_lean_parser_level__parser_run_lean_parser_has__view___closed__2);
 l_lean_parser_level__parser_run_lean_parser_has__view___closed__3 = _init_l_lean_parser_level__parser_run_lean_parser_has__view___closed__3();
lean::mark_persistent(l_lean_parser_level__parser_run_lean_parser_has__view___closed__3);
 l_lean_parser_level__parser__coe = _init_l_lean_parser_level__parser__coe();
lean::mark_persistent(l_lean_parser_level__parser__coe);
}
