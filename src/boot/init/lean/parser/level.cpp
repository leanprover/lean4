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
obj* l_lean_parser_trailing__level__parser__m_monad__except;
extern obj* l_lean_parser_match__token___closed__2;
obj* l_lean_parser_parsec__t_bind__mk__res___rarg(obj*, obj*);
obj* l_lean_parser_level__parser__m;
obj* l_lean_parser_trie_match__prefix___rarg(obj*, obj*);
obj* l_lean_parser_level_parser_lean_parser_has__view(obj*);
obj* l_lean_parser_level__parser_run_lean_parser_has__view(obj*);
obj* l_lean_parser_level_app_has__view_x_27___lambda__2(obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_level_trailing_parser_lean_parser_has__tokens___spec__2(obj*);
extern obj* l_lean_parser_number_has__view_x_27___lambda__2___closed__1;
obj* l_lean_parser_number_parser___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__2___rarg(obj*, obj*, obj*);
obj* l_lean_parser_trailing__level__parser__m_lean_parser_monad__parsec;
obj* l_lean_parser_level_add__lit_parser_lean_parser_has__tokens;
obj* l_reader__t_lift___rarg(obj*, obj*);
obj* l_lean_parser_level_trailing_has__view_x_27___lambda__1___closed__1;
obj* l_lean_parser_level_paren_has__view_x_27___lambda__2(obj*);
obj* l_lean_parser_level_leading_has__view;
obj* l_lean_parser_level__parser;
namespace lean {
obj* nat_add(obj*, obj*);
}
obj* l_lean_parser_level__parser__m_lean_parser_monad__parsec;
extern obj* l_mjoin___rarg___closed__1;
extern obj* l_lean_parser_basic__parser__m_monad;
obj* l_lean_parser_level_app;
obj* l_lean_parser_number_parser___at_lean_parser_level_add__lit_parser_lean_parser_has__tokens___spec__2(obj*, obj*);
obj* l_has__monad__lift__t__refl(obj*, obj*);
obj* l_list_mfoldl___main___at_lean_parser_level_paren_parser___spec__2(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_level_parser(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_level_leading_has__view_x_27___lambda__1(obj*);
obj* l_lean_parser_list_cons_tokens___rarg(obj*, obj*);
obj* l_lean_parser_number_parser___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__2(obj*);
obj* l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_trailing__level__parser__m;
obj* l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__2;
obj* l_lean_parser_parsec__t_try__mk__res___rarg(obj*);
obj* l_lean_parser_level_add__lit_parser(obj*, obj*, obj*, obj*, obj*);
obj* l_list_reverse___rarg(obj*);
extern "C" obj* lean_name_mk_string(obj*, obj*);
obj* l_reader__t_alternative___rarg(obj*, obj*);
obj* l_lean_parser_rec__t_recurse___at_lean_parser_level_parser_lean_parser_has__tokens___spec__1(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_combinators_node___at_lean_parser_level_paren_parser___spec__1(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_level_parser___closed__1;
obj* l_lean_parser_level__parser__m_monad__reader;
obj* l_lean_parser_parsec__t_labels__mk__res___rarg(obj*, obj*);
obj* l_lean_parser_level_add__lit_has__view_x_27___lambda__1___closed__1;
extern obj* l___private_init_lean_parser_combinators_1__many1__aux___main___rarg___closed__1;
obj* l_lean_parser_combinators_choice__aux___main___at_lean_parser_level_trailing_parser_lean_parser_has__tokens___spec__1(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_level_trailing_parser_lean_parser_has__tokens;
obj* l_lean_parser_level_paren_has__view_x_27___lambda__1___closed__1;
obj* l_lean_parser_curr__lbp___at_lean_parser_level__parser_run___spec__4(obj*, obj*, obj*, obj*);
obj* l_lean_parser_combinators_choice__aux___main___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__4(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_string_quote(obj*);
obj* l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__1;
obj* l_lean_parser_level__parser__coe;
obj* l_lean_parser_level_leading;
obj* l_lean_parser_level_get__leading(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_level_app_has__view;
obj* l_lean_parser_level_parser_lean_parser_has__view___closed__1;
obj* l_lean_parser_level__parser_run_lean_parser_has__tokens(obj*);
obj* l_reader__t_monad__functor(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_observing___at_lean_parser_peek__token___spec__2(obj*, obj*, obj*);
obj* l_lean_parser_level_app_parser_lean_parser_has__view;
obj* l_lean_parser_level__parser__m_alternative;
obj* l_lean_parser_trailing__level__parser__m_lean_parser_monad__rec;
obj* l_lean_parser_level_app_has__view_x_27___lambda__1(obj*);
obj* l_lean_parser_trailing__level__parser__m_monad;
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
obj* l_lean_parser_level_trailing_has__view_x_27___lambda__2(obj*);
obj* l_lean_parser_level_leading_has__view_x_27___lambda__2___closed__1;
extern obj* l_lean_parser_number_has__view;
obj* l_lean_parser_level__parser_run(obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_number_has__view_x_27___lambda__2___closed__2;
obj* l_lean_parser_level__parser__m_monad;
obj* l_lean_parser_level_leading_has__view_x_27___lambda__2___closed__2;
obj* l_lean_parser_tokens___rarg(obj*);
obj* l_option_get__or__else___main___rarg(obj*, obj*);
obj* l_lean_parser_level__parser_run_lean_parser_has__view___closed__1;
obj* l_lean_parser_level_trailing_parser___closed__1;
obj* l_lean_parser_syntax_as__node___main(obj*);
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
obj* l_lean_parser_trailing__level__parser;
obj* l_lean_parser_level__parser__m_lean_parser_monad__basic__parser;
obj* l_lean_parser_level_app_parser_lean_parser_has__view___lambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_combinators_node_view___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_level_app_parser_lean_parser_has__tokens;
obj* l_lean_parser_level_paren_parser___closed__1;
obj* l_lean_parser_trailing__level__parser__m_alternative;
obj* l_lean_parser_symbol__core___at_lean_parser_level_add__lit_parser_lean_parser_has__tokens___spec__1(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_ident_parser___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__3(obj*);
extern obj* l_lean_parser_finish__comment__block___closed__2;
extern obj* l_string_join___closed__1;
obj* l_lean_parser_level_leading_parser(obj*, obj*, obj*, obj*);
obj* l_id___rarg(obj*);
obj* l_reader__t_read___rarg(obj*, obj*);
extern obj* l_lean_parser_max__prec;
obj* l_lean_parser_rec__t_lean_parser_monad__parsec___rarg(obj*, obj*, obj*);
obj* l_lean_parser_level_app_has__view_x_27___lambda__1___closed__1;
obj* l_lean_parser_syntax_mk__node(obj*, obj*);
obj* l_lean_parser_level_add__lit_parser_lean_parser_has__view;
obj* l_lean_parser_level_parser_lean_parser_has__tokens(obj*);
extern obj* l_lean_parser_rec__t_run__parsec___at_lean_parser_detail__ident_parser___spec__1___closed__1;
obj* l_lean_parser_symbol__core___at_lean_parser_level_paren_parser_lean_parser_has__tokens___spec__1(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_combinators_recurse_view___rarg(obj*, obj*);
obj* l_lean_parser_level_paren_parser_lean_parser_has__view;
obj* l_lean_parser_token(obj*, obj*, obj*);
obj* l_reader__t_monad__except___rarg(obj*);
obj* l_lean_parser_monad__parsec__trans___rarg(obj*, obj*, obj*);
obj* l_lean_parser_level_add__lit_has__view_x_27;
obj* l_lean_parser_level_leading_parser_lean_parser_has__tokens;
obj* l_lean_parser_level_trailing_has__view_x_27___lambda__1___closed__2;
extern obj* l_lean_parser_curr__lbp___rarg___lambda__3___closed__2;
obj* l_lean_parser_level__parser__m_lean_parser_monad__rec;
obj* l_lean_parser_substring_to__string(obj*);
obj* l_lean_parser_level__parser_run_lean_parser_has__view___closed__3;
obj* l_lean_parser_level_paren_parser(obj*, obj*, obj*, obj*);
extern "C" uint8 lean_name_dec_eq(obj*, obj*);
obj* l_lean_parser_rec__t_recurse___rarg(obj*, obj*, obj*);
namespace lean {
uint8 string_dec_eq(obj*, obj*);
}
obj* l_reader__t_lift(obj*, obj*, obj*, obj*);
obj* l_lean_parser_level_paren_has__view;
extern obj* l_lean_parser_combinators_choice__aux___main___rarg___closed__1;
obj* l_lean_parser_level_leading_has__view_x_27___lambda__2(obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_level__parser_run___spec__3(obj*);
obj* l_lean_parser_level__parser_run_lean_parser_has__view___closed__2;
obj* l_lean_parser_number_parser___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__2___rarg___closed__1;
namespace lean {
obj* string_iterator_remaining(obj*);
}
namespace lean {
obj* string_mk_iterator(obj*);
}
extern obj* l_lean_parser_basic__parser__m_alternative;
obj* l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__4;
obj* l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__3;
obj* l_lean_parser_trailing__level__parser__m_monad__reader;
obj* l_lean_parser_level_add__lit_parser___closed__1;
obj* l_string_trim(obj*);
obj* l_list_mfoldl___main___at_lean_parser_level_app_parser___spec__2(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_option_get___main___at_lean_parser_run___spec__2(obj*);
extern obj* l_lean_parser_curr__lbp___rarg___lambda__3___closed__1;
obj* l_lean_parser_ident_parser___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__3___rarg(obj*, obj*, obj*);
obj* l_reader__t_monad___rarg(obj*);
obj* l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__5;
extern "C" obj* lean_name_mk_numeral(obj*, obj*);
obj* l_has__monad__lift__t__trans___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_parser_level_add__lit_has__view;
obj* l_lean_parser_monad__parsec_error___at_lean_parser_level_trailing_parser_lean_parser_has__tokens___spec__2___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_level_app_parser(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_rec__t_run___at_lean_parser_level__parser_run___spec__6(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_pratt_1__trailing__loop___main___at_lean_parser_level__parser_run___spec__2(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_trailing__level__parser__m_lean_parser_monad__basic__parser;
obj* l_lean_parser_level_paren_has__view_x_27;
obj* l_lean_parser_pratt__parser_view___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_level_add__lit_has__view_x_27___lambda__1(obj*);
obj* l_lean_parser_level_trailing_parser_lean_parser_has__view;
namespace lean {
obj* nat_sub(obj*, obj*);
}
obj* l_lean_parser_level_app_has__view_x_27;
obj* l_lean_parser_monad__parsec_error___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__5___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_number_parser___at_lean_parser_level_add__lit_parser_lean_parser_has__tokens___spec__2___rarg(obj*, obj*, obj*);
extern obj* l_lean_parser_detail__ident__part_has__view_x_27___lambda__2___closed__2;
extern obj* l_lean_parser_basic__parser__m_lean_parser_monad__parsec;
obj* l_lean_parser_level_add__lit_has__view_x_27___lambda__2(obj*);
obj* l_lean_parser_level_lean_parser_has__view;
obj* l_dlist_singleton___rarg(obj*, obj*);
extern obj* l_lean_parser_basic__parser__m_monad__except;
obj* l_lean_parser_level_trailing_has__view;
obj* l_lean_parser_parsec__t_orelse__mk__res___rarg(obj*, obj*);
obj* l_list_append___rarg(obj*, obj*);
obj* l_lean_parser_level_paren_has__view_x_27___lambda__1(obj*);
extern obj* l_lean_parser_number_has__view_x_27___lambda__1___closed__6;
obj* l_option_map___rarg(obj*, obj*);
obj* l_lean_parser_rec__t_run__parsec___at_lean_parser_level__parser_run___spec__5(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_ident_parser___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__3___rarg___closed__1;
obj* l_lean_parser_monad__rec_trans___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_parser_level_leading_parser___closed__1;
obj* l_lean_parser_substring_of__string(obj*);
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
obj* l_lean_parser_level_paren_parser_lean_parser_has__tokens;
obj* l_lean_parser_level_trailing_has__view_x_27;
obj* l___private_init_lean_parser_rec_1__run__aux___main___rarg(obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_raw_view___rarg___lambda__3___closed__1;
obj* _init_l_lean_parser_level__parser__m_monad() {
_start:
{
obj* x_0; obj* x_2; 
x_0 = l_lean_parser_basic__parser__m_monad;
lean::inc(x_0);
x_2 = l_reader__t_monad___rarg(x_0);
return x_2;
}
}
obj* _init_l_lean_parser_level__parser__m_alternative() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; 
x_0 = l_lean_parser_basic__parser__m_monad;
x_1 = l_lean_parser_basic__parser__m_alternative;
lean::inc(x_1);
lean::inc(x_0);
x_4 = l_reader__t_alternative___rarg(x_0, x_1);
return x_4;
}
}
obj* _init_l_lean_parser_level__parser__m_monad__reader() {
_start:
{
obj* x_0; obj* x_2; 
x_0 = l_lean_parser_basic__parser__m_monad__reader;
lean::inc(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_lift___rarg), 2, 1);
lean::closure_set(x_2, 0, x_0);
return x_2;
}
}
obj* _init_l_lean_parser_level__parser__m_lean_parser_monad__parsec() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; 
x_0 = l_lean_parser_basic__parser__m_monad;
x_1 = l_lean_parser_basic__parser__m_lean_parser_monad__parsec;
lean::inc(x_1);
lean::inc(x_0);
x_4 = l_lean_parser_rec__t_lean_parser_monad__parsec___rarg(x_0, lean::box(0), x_1);
return x_4;
}
}
obj* _init_l_lean_parser_level__parser__m_monad__except() {
_start:
{
obj* x_0; obj* x_2; 
x_0 = l_lean_parser_basic__parser__m_monad__except;
lean::inc(x_0);
x_2 = l_reader__t_monad__except___rarg(x_0);
return x_2;
}
}
obj* _init_l_lean_parser_level__parser__m_lean_parser_monad__rec() {
_start:
{
obj* x_0; obj* x_2; 
x_0 = l_lean_parser_basic__parser__m_monad;
lean::inc(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_rec__t_recurse___rarg), 3, 1);
lean::closure_set(x_2, 0, x_0);
return x_2;
}
}
obj* _init_l_lean_parser_level__parser__m_lean_parser_monad__basic__parser() {
_start:
{
obj* x_0; obj* x_2; obj* x_3; obj* x_4; 
x_0 = l_lean_parser_basic__parser__m_monad;
lean::inc(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_lift), 4, 3);
lean::closure_set(x_2, 0, lean::box(0));
lean::closure_set(x_2, 1, lean::box(0));
lean::closure_set(x_2, 2, x_0);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_has__monad__lift__t__refl), 2, 1);
lean::closure_set(x_3, 0, lean::box(0));
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_has__monad__lift__t__trans___rarg), 4, 2);
lean::closure_set(x_4, 0, x_2);
lean::closure_set(x_4, 1, x_3);
return x_4;
}
}
obj* _init_l_lean_parser_level__parser__m() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* _init_l_lean_parser_level__parser() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* _init_l_lean_parser_trailing__level__parser__m_monad() {
_start:
{
obj* x_0; obj* x_2; 
x_0 = l_lean_parser_level__parser__m_monad;
lean::inc(x_0);
x_2 = l_reader__t_monad___rarg(x_0);
return x_2;
}
}
obj* _init_l_lean_parser_trailing__level__parser__m_alternative() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; 
x_0 = l_lean_parser_level__parser__m_monad;
x_1 = l_lean_parser_level__parser__m_alternative;
lean::inc(x_1);
lean::inc(x_0);
x_4 = l_reader__t_alternative___rarg(x_0, x_1);
return x_4;
}
}
obj* _init_l_lean_parser_trailing__level__parser__m_monad__reader() {
_start:
{
obj* x_0; obj* x_2; 
x_0 = l_lean_parser_level__parser__m_monad;
lean::inc(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_read___rarg), 2, 1);
lean::closure_set(x_2, 0, x_0);
return x_2;
}
}
obj* _init_l_lean_parser_trailing__level__parser__m_lean_parser_monad__parsec() {
_start:
{
obj* x_0; obj* x_2; obj* x_5; obj* x_6; obj* x_8; 
x_0 = l_lean_parser_level__parser__m_monad;
lean::inc(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_lift), 4, 3);
lean::closure_set(x_2, 0, lean::box(0));
lean::closure_set(x_2, 1, lean::box(0));
lean::closure_set(x_2, 2, x_0);
lean::inc(x_0);
lean::inc(x_0);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_monad__functor), 6, 5);
lean::closure_set(x_5, 0, lean::box(0));
lean::closure_set(x_5, 1, lean::box(0));
lean::closure_set(x_5, 2, lean::box(0));
lean::closure_set(x_5, 3, x_0);
lean::closure_set(x_5, 4, x_0);
x_6 = l_lean_parser_level__parser__m_lean_parser_monad__parsec;
lean::inc(x_6);
x_8 = l_lean_parser_monad__parsec__trans___rarg(x_2, x_5, x_6);
return x_8;
}
}
obj* _init_l_lean_parser_trailing__level__parser__m_monad__except() {
_start:
{
obj* x_0; obj* x_2; 
x_0 = l_lean_parser_level__parser__m_monad__except;
lean::inc(x_0);
x_2 = l_reader__t_monad__except___rarg(x_0);
return x_2;
}
}
obj* _init_l_lean_parser_trailing__level__parser__m_lean_parser_monad__rec() {
_start:
{
obj* x_0; obj* x_2; obj* x_3; obj* x_6; 
x_0 = l_lean_parser_level__parser__m_monad;
lean::inc(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_lift), 4, 3);
lean::closure_set(x_2, 0, lean::box(0));
lean::closure_set(x_2, 1, lean::box(0));
lean::closure_set(x_2, 2, x_0);
x_3 = l_lean_parser_level__parser__m_lean_parser_monad__rec;
lean::inc(x_0);
lean::inc(x_3);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__rec_trans___rarg), 4, 3);
lean::closure_set(x_6, 0, x_2);
lean::closure_set(x_6, 1, x_3);
lean::closure_set(x_6, 2, x_0);
return x_6;
}
}
obj* _init_l_lean_parser_trailing__level__parser__m_lean_parser_monad__basic__parser() {
_start:
{
obj* x_0; obj* x_2; obj* x_3; obj* x_5; 
x_0 = l_lean_parser_level__parser__m_monad;
lean::inc(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_lift), 4, 3);
lean::closure_set(x_2, 0, lean::box(0));
lean::closure_set(x_2, 1, lean::box(0));
lean::closure_set(x_2, 2, x_0);
x_3 = l_lean_parser_level__parser__m_lean_parser_monad__basic__parser;
lean::inc(x_3);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_has__monad__lift__t__trans___rarg), 4, 2);
lean::closure_set(x_5, 0, x_2);
lean::closure_set(x_5, 1, x_3);
return x_5;
}
}
obj* _init_l_lean_parser_trailing__level__parser__m() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* _init_l_lean_parser_trailing__level__parser() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* l_lean_parser_trailing__level__parser__coe(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_7; 
lean::dec(x_1);
x_7 = lean::apply_4(x_0, x_2, x_3, x_4, x_5);
return x_7;
}
}
obj* l_lean_parser_rec__t_recurse___at_lean_parser_level_parser_lean_parser_has__tokens___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
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
obj* x_2; 
lean::dec(x_0);
x_2 = l_lean_parser_level_parser_lean_parser_has__tokens___closed__1;
lean::inc(x_2);
return x_2;
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
obj* x_2; obj* x_3; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_12; 
lean::inc(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_rec__t_recurse___at_lean_parser_level_parser_lean_parser_has__tokens___spec__1), 5, 1);
lean::closure_set(x_2, 0, x_0);
x_3 = l_lean_parser_level__parser__m_lean_parser_monad__rec;
lean::inc(x_3);
x_5 = l_lean_parser_combinators_recurse_view___rarg(x_0, x_3);
x_6 = l_lean_parser_level__parser__m_lean_parser_monad__parsec;
x_7 = l_lean_parser_level__parser__m_alternative;
x_8 = l_lean_parser_level_parser_lean_parser_has__view___closed__1;
lean::inc(x_8);
lean::inc(x_7);
lean::inc(x_6);
x_12 = l_lean_parser_combinators_label_view___rarg(x_6, x_7, x_2, x_8, x_5);
return x_12;
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
obj* x_5; obj* x_6; obj* x_8; obj* x_10; obj* x_11; obj* x_13; obj* x_14; 
x_5 = l_lean_parser_rec__t_recurse___at_lean_parser_level_parser_lean_parser_has__tokens___spec__1(x_0, x_1, x_2, x_3, x_4);
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
x_11 = l_lean_parser_level_parser___closed__1;
lean::inc(x_11);
x_13 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_6, x_11);
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
obj* l_lean_parser_level_get__leading(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_7; obj* x_9; obj* x_10; 
lean::dec(x_2);
lean::dec(x_1);
x_7 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_7);
x_9 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_9, 0, x_0);
lean::cnstr_set(x_9, 1, x_3);
lean::cnstr_set(x_9, 2, x_7);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_4);
return x_10;
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
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_id___rarg), 1, 0);
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
lean::inc(x_9);
return x_9;
}
else
{
obj* x_11; obj* x_14; 
x_11 = lean::cnstr_get(x_8, 0);
lean::inc(x_11);
lean::dec(x_8);
x_14 = lean::cnstr_get(x_11, 1);
lean::inc(x_14);
lean::dec(x_11);
if (lean::obj_tag(x_14) == 0)
{
obj* x_17; 
x_17 = lean::box(3);
x_5 = x_14;
x_6 = x_17;
goto lbl_7;
}
else
{
obj* x_18; obj* x_20; 
x_18 = lean::cnstr_get(x_14, 0);
lean::inc(x_18);
x_20 = lean::cnstr_get(x_14, 1);
lean::inc(x_20);
lean::dec(x_14);
x_5 = x_20;
x_6 = x_18;
goto lbl_7;
}
}
lbl_4:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_23; obj* x_24; 
x_23 = lean::box(0);
x_24 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_24, 0, x_1);
lean::cnstr_set(x_24, 1, x_2);
lean::cnstr_set(x_24, 2, x_23);
return x_24;
}
else
{
obj* x_25; 
x_25 = lean::cnstr_get(x_3, 0);
lean::inc(x_25);
lean::dec(x_3);
switch (lean::obj_tag(x_25)) {
case 0:
{
obj* x_28; obj* x_31; obj* x_32; 
x_28 = lean::cnstr_get(x_25, 0);
lean::inc(x_28);
lean::dec(x_25);
x_31 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_31, 0, x_28);
x_32 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_32, 0, x_1);
lean::cnstr_set(x_32, 1, x_2);
lean::cnstr_set(x_32, 2, x_31);
return x_32;
}
case 3:
{
obj* x_33; obj* x_34; 
x_33 = lean::box(0);
x_34 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_34, 0, x_1);
lean::cnstr_set(x_34, 1, x_2);
lean::cnstr_set(x_34, 2, x_33);
return x_34;
}
default:
{
obj* x_36; obj* x_37; 
lean::dec(x_25);
x_36 = lean::box(0);
x_37 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_37, 0, x_1);
lean::cnstr_set(x_37, 1, x_2);
lean::cnstr_set(x_37, 2, x_36);
return x_37;
}
}
}
}
lbl_7:
{
obj* x_38; 
switch (lean::obj_tag(x_6)) {
case 0:
{
obj* x_40; obj* x_43; 
x_40 = lean::cnstr_get(x_6, 0);
lean::inc(x_40);
lean::dec(x_6);
x_43 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_43, 0, x_40);
if (lean::obj_tag(x_5) == 0)
{
x_38 = x_43;
goto lbl_39;
}
else
{
obj* x_44; obj* x_46; 
x_44 = lean::cnstr_get(x_5, 0);
lean::inc(x_44);
x_46 = lean::cnstr_get(x_5, 1);
lean::inc(x_46);
lean::dec(x_5);
x_1 = x_43;
x_2 = x_44;
x_3 = x_46;
goto lbl_4;
}
}
case 3:
{
obj* x_49; 
x_49 = lean::box(0);
if (lean::obj_tag(x_5) == 0)
{
x_38 = x_49;
goto lbl_39;
}
else
{
obj* x_50; obj* x_52; 
x_50 = lean::cnstr_get(x_5, 0);
lean::inc(x_50);
x_52 = lean::cnstr_get(x_5, 1);
lean::inc(x_52);
lean::dec(x_5);
x_1 = x_49;
x_2 = x_50;
x_3 = x_52;
goto lbl_4;
}
}
default:
{
obj* x_56; 
lean::dec(x_6);
x_56 = lean::box(0);
if (lean::obj_tag(x_5) == 0)
{
x_38 = x_56;
goto lbl_39;
}
else
{
obj* x_57; obj* x_59; 
x_57 = lean::cnstr_get(x_5, 0);
lean::inc(x_57);
x_59 = lean::cnstr_get(x_5, 1);
lean::inc(x_59);
lean::dec(x_5);
x_1 = x_56;
x_2 = x_57;
x_3 = x_59;
goto lbl_4;
}
}
}
lbl_39:
{
if (lean::obj_tag(x_5) == 0)
{
obj* x_62; obj* x_63; obj* x_64; 
x_62 = lean::box(0);
x_63 = lean::box(3);
x_64 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_64, 0, x_38);
lean::cnstr_set(x_64, 1, x_63);
lean::cnstr_set(x_64, 2, x_62);
return x_64;
}
else
{
obj* x_65; 
x_65 = lean::cnstr_get(x_5, 0);
lean::inc(x_65);
lean::dec(x_5);
switch (lean::obj_tag(x_65)) {
case 0:
{
obj* x_68; obj* x_71; obj* x_72; obj* x_73; 
x_68 = lean::cnstr_get(x_65, 0);
lean::inc(x_68);
lean::dec(x_65);
x_71 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_71, 0, x_68);
x_72 = lean::box(3);
x_73 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_73, 0, x_38);
lean::cnstr_set(x_73, 1, x_72);
lean::cnstr_set(x_73, 2, x_71);
return x_73;
}
case 3:
{
obj* x_74; obj* x_75; obj* x_76; 
x_74 = lean::box(0);
x_75 = lean::box(3);
x_76 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_76, 0, x_38);
lean::cnstr_set(x_76, 1, x_75);
lean::cnstr_set(x_76, 2, x_74);
return x_76;
}
default:
{
obj* x_78; obj* x_79; obj* x_80; 
lean::dec(x_65);
x_78 = lean::box(0);
x_79 = lean::box(3);
x_80 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_80, 0, x_38);
lean::cnstr_set(x_80, 1, x_79);
lean::cnstr_set(x_80, 2, x_78);
return x_80;
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
obj* x_1; obj* x_3; obj* x_5; obj* x_8; obj* x_10; obj* x_11; obj* x_12; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_22; 
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
x_12 = l_option_get__or__else___main___rarg(x_10, x_11);
lean::inc(x_8);
x_14 = l_option_map___rarg(x_8, x_5);
x_15 = l_option_get__or__else___main___rarg(x_14, x_11);
x_16 = lean::box(0);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_16);
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_3);
lean::cnstr_set(x_18, 1, x_17);
x_19 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_19, 0, x_12);
lean::cnstr_set(x_19, 1, x_18);
x_20 = l_lean_parser_level_paren;
lean::inc(x_20);
x_22 = l_lean_parser_syntax_mk__node(x_20, x_19);
return x_22;
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
lean::inc(x_0);
return x_0;
}
}
obj* l_lean_parser_symbol__core___at_lean_parser_level_paren_parser_lean_parser_has__tokens___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_11; obj* x_12; obj* x_14; obj* x_16; obj* x_18; 
lean::dec(x_3);
lean::dec(x_1);
lean::inc(x_5);
lean::inc(x_4);
x_11 = l_lean_parser_token(x_4, x_5, x_6);
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
lean::inc(x_0);
x_18 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_18, 0, x_0);
if (lean::obj_tag(x_12) == 0)
{
obj* x_19; obj* x_21; obj* x_23; obj* x_25; obj* x_26; 
x_19 = lean::cnstr_get(x_12, 0);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_12, 1);
lean::inc(x_21);
x_23 = lean::cnstr_get(x_12, 2);
lean::inc(x_23);
if (lean::is_shared(x_12)) {
 lean::dec(x_12);
 x_25 = lean::box(0);
} else {
 lean::cnstr_release(x_12, 0);
 lean::cnstr_release(x_12, 1);
 lean::cnstr_release(x_12, 2);
 x_25 = x_12;
}
switch (lean::obj_tag(x_19)) {
case 0:
{
obj* x_29; obj* x_31; uint8 x_34; 
lean::dec(x_16);
x_29 = lean::cnstr_get(x_19, 0);
lean::inc(x_29);
x_31 = lean::cnstr_get(x_29, 1);
lean::inc(x_31);
lean::dec(x_29);
x_34 = lean::string_dec_eq(x_0, x_31);
lean::dec(x_0);
if (x_34 == 0)
{
obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_41; obj* x_43; 
x_36 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_36, 0, x_5);
x_37 = lean::box(0);
x_38 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_31, x_2, x_36, x_37, x_4, x_21, x_14);
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
if (lean::obj_tag(x_39) == 0)
{
obj* x_44; obj* x_46; obj* x_49; obj* x_51; obj* x_52; obj* x_53; obj* x_55; obj* x_56; obj* x_57; obj* x_58; 
x_44 = lean::cnstr_get(x_39, 1);
lean::inc(x_44);
x_46 = lean::cnstr_get(x_39, 2);
lean::inc(x_46);
lean::dec(x_39);
x_49 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_49);
if (lean::is_scalar(x_25)) {
 x_51 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_51 = x_25;
}
lean::cnstr_set(x_51, 0, x_19);
lean::cnstr_set(x_51, 1, x_44);
lean::cnstr_set(x_51, 2, x_49);
x_52 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_46, x_51);
x_53 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_23, x_52);
lean::inc(x_49);
x_55 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_49, x_53);
x_56 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_55, x_18);
x_57 = l_lean_parser_parsec__t_try__mk__res___rarg(x_56);
if (lean::is_scalar(x_43)) {
 x_58 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_58 = x_43;
}
lean::cnstr_set(x_58, 0, x_57);
lean::cnstr_set(x_58, 1, x_41);
return x_58;
}
else
{
obj* x_61; uint8 x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_70; obj* x_71; obj* x_72; obj* x_73; 
lean::dec(x_25);
lean::dec(x_19);
x_61 = lean::cnstr_get(x_39, 0);
lean::inc(x_61);
x_63 = lean::cnstr_get_scalar<uint8>(x_39, sizeof(void*)*1);
if (lean::is_shared(x_39)) {
 lean::dec(x_39);
 x_64 = lean::box(0);
} else {
 lean::cnstr_release(x_39, 0);
 x_64 = x_39;
}
if (lean::is_scalar(x_64)) {
 x_65 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_65 = x_64;
}
lean::cnstr_set(x_65, 0, x_61);
lean::cnstr_set_scalar(x_65, sizeof(void*)*1, x_63);
x_66 = x_65;
x_67 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_23, x_66);
x_68 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_68);
x_70 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_68, x_67);
x_71 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_70, x_18);
x_72 = l_lean_parser_parsec__t_try__mk__res___rarg(x_71);
if (lean::is_scalar(x_43)) {
 x_73 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_73 = x_43;
}
lean::cnstr_set(x_73, 0, x_72);
lean::cnstr_set(x_73, 1, x_41);
return x_73;
}
}
else
{
obj* x_78; obj* x_80; obj* x_81; obj* x_82; obj* x_84; obj* x_85; obj* x_86; obj* x_87; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_2);
lean::dec(x_31);
x_78 = l_lean_parser_finish__comment__block___closed__2;
lean::inc(x_78);
if (lean::is_scalar(x_25)) {
 x_80 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_80 = x_25;
}
lean::cnstr_set(x_80, 0, x_19);
lean::cnstr_set(x_80, 1, x_21);
lean::cnstr_set(x_80, 2, x_78);
x_81 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_23, x_80);
x_82 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_82);
x_84 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_82, x_81);
x_85 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_84, x_18);
x_86 = l_lean_parser_parsec__t_try__mk__res___rarg(x_85);
x_87 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_87, 0, x_86);
lean::cnstr_set(x_87, 1, x_14);
return x_87;
}
}
case 3:
{
obj* x_90; 
lean::dec(x_25);
lean::dec(x_0);
x_90 = lean::box(0);
x_26 = x_90;
goto lbl_27;
}
default:
{
obj* x_94; 
lean::dec(x_25);
lean::dec(x_0);
lean::dec(x_19);
x_94 = lean::box(0);
x_26 = x_94;
goto lbl_27;
}
}
lbl_27:
{
obj* x_96; obj* x_97; obj* x_98; obj* x_100; obj* x_101; obj* x_103; obj* x_106; obj* x_107; obj* x_109; obj* x_110; obj* x_111; obj* x_112; 
lean::dec(x_26);
x_96 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_96, 0, x_5);
x_97 = lean::box(0);
x_98 = l_string_join___closed__1;
lean::inc(x_98);
x_100 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_98, x_2, x_96, x_97, x_4, x_21, x_14);
x_101 = lean::cnstr_get(x_100, 0);
lean::inc(x_101);
x_103 = lean::cnstr_get(x_100, 1);
lean::inc(x_103);
lean::dec(x_100);
x_106 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_23, x_101);
x_107 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_107);
x_109 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_107, x_106);
x_110 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_109, x_18);
x_111 = l_lean_parser_parsec__t_try__mk__res___rarg(x_110);
if (lean::is_scalar(x_16)) {
 x_112 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_112 = x_16;
}
lean::cnstr_set(x_112, 0, x_111);
lean::cnstr_set(x_112, 1, x_103);
return x_112;
}
}
else
{
obj* x_117; uint8 x_119; obj* x_120; obj* x_121; obj* x_122; obj* x_123; obj* x_125; obj* x_126; obj* x_127; obj* x_128; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_0);
lean::dec(x_2);
x_117 = lean::cnstr_get(x_12, 0);
lean::inc(x_117);
x_119 = lean::cnstr_get_scalar<uint8>(x_12, sizeof(void*)*1);
if (lean::is_shared(x_12)) {
 lean::dec(x_12);
 x_120 = lean::box(0);
} else {
 lean::cnstr_release(x_12, 0);
 x_120 = x_12;
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
x_126 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_125, x_18);
x_127 = l_lean_parser_parsec__t_try__mk__res___rarg(x_126);
if (lean::is_scalar(x_16)) {
 x_128 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_128 = x_16;
}
lean::cnstr_set(x_128, 0, x_127);
lean::cnstr_set(x_128, 1, x_14);
return x_128;
}
}
}
obj* _init_l_lean_parser_level_paren_parser_lean_parser_has__tokens() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_11; obj* x_12; obj* x_13; 
x_0 = lean::mk_string("(");
x_1 = l_lean_parser_max__prec;
lean::inc(x_1);
x_3 = l_lean_parser_symbol_tokens___rarg(x_0, x_1);
x_4 = lean::mk_string(")");
x_5 = lean::mk_nat_obj(0u);
x_6 = l_lean_parser_symbol_tokens___rarg(x_4, x_5);
x_7 = lean::box(0);
x_8 = l_lean_parser_list_cons_tokens___rarg(x_6, x_7);
x_9 = l_lean_parser_level_parser_lean_parser_has__tokens___closed__1;
lean::inc(x_9);
x_11 = l_lean_parser_list_cons_tokens___rarg(x_9, x_8);
x_12 = l_lean_parser_list_cons_tokens___rarg(x_3, x_11);
x_13 = l_lean_parser_tokens___rarg(x_12);
return x_13;
}
}
obj* _init_l_lean_parser_level_paren_parser_lean_parser_has__view() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_30; 
x_0 = lean::mk_string("(");
x_1 = l_string_trim(x_0);
lean::inc(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_3, 0, x_1);
x_4 = l_lean_parser_max__prec;
lean::inc(x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_level_paren_parser_lean_parser_has__tokens___spec__1), 7, 3);
lean::closure_set(x_6, 0, x_1);
lean::closure_set(x_6, 1, x_4);
lean::closure_set(x_6, 2, x_3);
x_7 = lean::mk_nat_obj(0u);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_level_parser), 5, 1);
lean::closure_set(x_8, 0, x_7);
x_9 = lean::mk_string(")");
x_10 = l_string_trim(x_9);
lean::inc(x_10);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_12, 0, x_10);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_level_paren_parser_lean_parser_has__tokens___spec__1), 7, 3);
lean::closure_set(x_13, 0, x_10);
lean::closure_set(x_13, 1, x_7);
lean::closure_set(x_13, 2, x_12);
x_14 = lean::box(0);
x_15 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_15, 0, x_13);
lean::cnstr_set(x_15, 1, x_14);
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_8);
lean::cnstr_set(x_16, 1, x_15);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_6);
lean::cnstr_set(x_17, 1, x_16);
x_18 = l_lean_parser_level__parser__m_monad;
x_19 = l_lean_parser_level__parser__m_monad__except;
x_20 = l_lean_parser_level__parser__m_lean_parser_monad__parsec;
x_21 = l_lean_parser_level__parser__m_alternative;
x_22 = l_lean_parser_level_paren;
x_23 = l_lean_parser_level_paren_has__view;
lean::inc(x_23);
lean::inc(x_22);
lean::inc(x_21);
lean::inc(x_20);
lean::inc(x_19);
lean::inc(x_18);
x_30 = l_lean_parser_combinators_node_view___rarg(x_18, x_19, x_20, x_21, x_22, x_17, x_23);
return x_30;
}
}
obj* l_list_mfoldl___main___at_lean_parser_level_paren_parser___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_10; obj* x_12; obj* x_13; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_0);
x_10 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_10);
x_12 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_12, 0, x_1);
lean::cnstr_set(x_12, 1, x_5);
lean::cnstr_set(x_12, 2, x_10);
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_6);
return x_13;
}
else
{
obj* x_14; obj* x_16; obj* x_18; obj* x_19; obj* x_20; obj* x_24; obj* x_25; obj* x_27; 
x_14 = lean::cnstr_get(x_2, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_2, 1);
lean::inc(x_16);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_18 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 lean::cnstr_release(x_2, 1);
 x_18 = x_2;
}
lean::inc(x_4);
lean::inc(x_3);
x_24 = lean::apply_4(x_14, x_3, x_4, x_5, x_6);
x_25 = lean::cnstr_get(x_24, 0);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_24, 1);
lean::inc(x_27);
lean::dec(x_24);
if (lean::obj_tag(x_25) == 0)
{
x_19 = x_25;
x_20 = x_27;
goto lbl_21;
}
else
{
obj* x_30; uint8 x_32; obj* x_33; 
x_30 = lean::cnstr_get(x_25, 0);
lean::inc(x_30);
x_32 = lean::cnstr_get_scalar<uint8>(x_25, sizeof(void*)*1);
if (lean::is_shared(x_25)) {
 lean::dec(x_25);
 x_33 = lean::box(0);
} else {
 lean::cnstr_release(x_25, 0);
 x_33 = x_25;
}
if (lean::obj_tag(x_1) == 0)
{
if (x_32 == 0)
{
uint8 x_34; obj* x_35; obj* x_36; 
x_34 = 0;
if (lean::is_scalar(x_33)) {
 x_35 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_35 = x_33;
}
lean::cnstr_set(x_35, 0, x_30);
lean::cnstr_set_scalar(x_35, sizeof(void*)*1, x_34);
x_36 = x_35;
x_19 = x_36;
x_20 = x_27;
goto lbl_21;
}
else
{
obj* x_37; obj* x_38; 
if (lean::is_scalar(x_33)) {
 x_37 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_37 = x_33;
}
lean::cnstr_set(x_37, 0, x_30);
lean::cnstr_set_scalar(x_37, sizeof(void*)*1, x_32);
x_38 = x_37;
x_19 = x_38;
x_20 = x_27;
goto lbl_21;
}
}
else
{
obj* x_39; obj* x_41; obj* x_43; obj* x_44; obj* x_46; obj* x_48; obj* x_51; obj* x_53; obj* x_54; obj* x_55; 
x_39 = lean::cnstr_get(x_30, 3);
lean::inc(x_39);
x_41 = l_option_get___main___at_lean_parser_run___spec__2(x_39);
lean::inc(x_1);
x_43 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_43, 0, x_41);
lean::cnstr_set(x_43, 1, x_1);
x_44 = lean::cnstr_get(x_30, 0);
lean::inc(x_44);
x_46 = lean::cnstr_get(x_30, 1);
lean::inc(x_46);
x_48 = lean::cnstr_get(x_30, 2);
lean::inc(x_48);
lean::dec(x_30);
x_51 = l_list_reverse___rarg(x_43);
lean::inc(x_0);
x_53 = l_lean_parser_syntax_mk__node(x_0, x_51);
x_54 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_54, 0, x_53);
x_55 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_55, 0, x_44);
lean::cnstr_set(x_55, 1, x_46);
lean::cnstr_set(x_55, 2, x_48);
lean::cnstr_set(x_55, 3, x_54);
if (x_32 == 0)
{
uint8 x_56; obj* x_57; obj* x_58; 
x_56 = 0;
if (lean::is_scalar(x_33)) {
 x_57 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_57 = x_33;
}
lean::cnstr_set(x_57, 0, x_55);
lean::cnstr_set_scalar(x_57, sizeof(void*)*1, x_56);
x_58 = x_57;
x_19 = x_58;
x_20 = x_27;
goto lbl_21;
}
else
{
obj* x_59; obj* x_60; 
if (lean::is_scalar(x_33)) {
 x_59 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_59 = x_33;
}
lean::cnstr_set(x_59, 0, x_55);
lean::cnstr_set_scalar(x_59, sizeof(void*)*1, x_32);
x_60 = x_59;
x_19 = x_60;
x_20 = x_27;
goto lbl_21;
}
}
}
lbl_21:
{
if (lean::obj_tag(x_19) == 0)
{
obj* x_61; obj* x_63; obj* x_65; obj* x_67; obj* x_68; obj* x_69; obj* x_71; obj* x_72; 
x_61 = lean::cnstr_get(x_19, 0);
lean::inc(x_61);
x_63 = lean::cnstr_get(x_19, 1);
lean::inc(x_63);
x_65 = lean::cnstr_get(x_19, 2);
lean::inc(x_65);
if (lean::is_shared(x_19)) {
 lean::dec(x_19);
 x_67 = lean::box(0);
} else {
 lean::cnstr_release(x_19, 0);
 lean::cnstr_release(x_19, 1);
 lean::cnstr_release(x_19, 2);
 x_67 = x_19;
}
if (lean::is_scalar(x_18)) {
 x_68 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_68 = x_18;
}
lean::cnstr_set(x_68, 0, x_61);
lean::cnstr_set(x_68, 1, x_1);
x_69 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_69);
if (lean::is_scalar(x_67)) {
 x_71 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_71 = x_67;
}
lean::cnstr_set(x_71, 0, x_68);
lean::cnstr_set(x_71, 1, x_63);
lean::cnstr_set(x_71, 2, x_69);
x_72 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_65, x_71);
if (lean::obj_tag(x_72) == 0)
{
obj* x_73; obj* x_75; obj* x_77; obj* x_80; obj* x_81; obj* x_83; obj* x_85; obj* x_86; obj* x_87; 
x_73 = lean::cnstr_get(x_72, 0);
lean::inc(x_73);
x_75 = lean::cnstr_get(x_72, 1);
lean::inc(x_75);
x_77 = lean::cnstr_get(x_72, 2);
lean::inc(x_77);
lean::dec(x_72);
x_80 = l_list_mfoldl___main___at_lean_parser_level_paren_parser___spec__2(x_0, x_73, x_16, x_3, x_4, x_75, x_20);
x_81 = lean::cnstr_get(x_80, 0);
lean::inc(x_81);
x_83 = lean::cnstr_get(x_80, 1);
lean::inc(x_83);
if (lean::is_shared(x_80)) {
 lean::dec(x_80);
 x_85 = lean::box(0);
} else {
 lean::cnstr_release(x_80, 0);
 lean::cnstr_release(x_80, 1);
 x_85 = x_80;
}
x_86 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_77, x_81);
if (lean::is_scalar(x_85)) {
 x_87 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_87 = x_85;
}
lean::cnstr_set(x_87, 0, x_86);
lean::cnstr_set(x_87, 1, x_83);
return x_87;
}
else
{
obj* x_92; uint8 x_94; obj* x_95; obj* x_96; obj* x_97; obj* x_98; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_16);
x_92 = lean::cnstr_get(x_72, 0);
lean::inc(x_92);
x_94 = lean::cnstr_get_scalar<uint8>(x_72, sizeof(void*)*1);
if (lean::is_shared(x_72)) {
 lean::dec(x_72);
 x_95 = lean::box(0);
} else {
 lean::cnstr_release(x_72, 0);
 x_95 = x_72;
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
lean::cnstr_set(x_98, 1, x_20);
return x_98;
}
}
else
{
obj* x_105; uint8 x_107; obj* x_108; obj* x_109; obj* x_110; obj* x_111; 
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_16);
lean::dec(x_18);
x_105 = lean::cnstr_get(x_19, 0);
lean::inc(x_105);
x_107 = lean::cnstr_get_scalar<uint8>(x_19, sizeof(void*)*1);
if (lean::is_shared(x_19)) {
 lean::dec(x_19);
 x_108 = lean::box(0);
} else {
 lean::cnstr_release(x_19, 0);
 x_108 = x_19;
}
if (lean::is_scalar(x_108)) {
 x_109 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_109 = x_108;
}
lean::cnstr_set(x_109, 0, x_105);
lean::cnstr_set_scalar(x_109, sizeof(void*)*1, x_107);
x_110 = x_109;
x_111 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_111, 0, x_110);
lean::cnstr_set(x_111, 1, x_20);
return x_111;
}
}
}
}
}
obj* l_lean_parser_combinators_node___at_lean_parser_level_paren_parser___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_8; obj* x_9; obj* x_11; obj* x_13; 
x_6 = lean::box(0);
lean::inc(x_0);
x_8 = l_list_mfoldl___main___at_lean_parser_level_paren_parser___spec__2(x_0, x_6, x_1, x_2, x_3, x_4, x_5);
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
obj* _init_l_lean_parser_level_paren_parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_0 = lean::mk_string("(");
x_1 = l_string_trim(x_0);
lean::inc(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_3, 0, x_1);
x_4 = l_lean_parser_max__prec;
lean::inc(x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_level_paren_parser_lean_parser_has__tokens___spec__1), 7, 3);
lean::closure_set(x_6, 0, x_1);
lean::closure_set(x_6, 1, x_4);
lean::closure_set(x_6, 2, x_3);
x_7 = lean::mk_nat_obj(0u);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_level_parser), 5, 1);
lean::closure_set(x_8, 0, x_7);
x_9 = lean::mk_string(")");
x_10 = l_string_trim(x_9);
lean::inc(x_10);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_12, 0, x_10);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_level_paren_parser_lean_parser_has__tokens___spec__1), 7, 3);
lean::closure_set(x_13, 0, x_10);
lean::closure_set(x_13, 1, x_7);
lean::closure_set(x_13, 2, x_12);
x_14 = lean::box(0);
x_15 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_15, 0, x_13);
lean::cnstr_set(x_15, 1, x_14);
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_8);
lean::cnstr_set(x_16, 1, x_15);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_6);
lean::cnstr_set(x_17, 1, x_16);
return x_17;
}
}
obj* l_lean_parser_level_paren_parser(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_8; 
x_4 = l_lean_parser_level_paren;
x_5 = l_lean_parser_level_paren_parser___closed__1;
lean::inc(x_5);
lean::inc(x_4);
x_8 = l_lean_parser_combinators_node___at_lean_parser_level_paren_parser___spec__1(x_4, x_5, x_0, x_1, x_2, x_3);
return x_8;
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
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_0 = lean::box(0);
x_1 = lean::mk_string("NOT_AN_IDENT");
lean::inc(x_1);
x_3 = l_lean_parser_substring_of__string(x_1);
x_4 = lean_name_mk_string(x_0, x_1);
x_5 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_5, 0, x_0);
lean::cnstr_set(x_5, 1, x_3);
lean::cnstr_set(x_5, 2, x_4);
lean::cnstr_set(x_5, 3, x_0);
lean::cnstr_set(x_5, 4, x_0);
x_6 = lean::alloc_cnstr(5, 1, 0);
lean::cnstr_set(x_6, 0, x_5);
return x_6;
}
}
obj* _init_l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; 
x_0 = l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__1;
lean::inc(x_0);
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
lean::inc(x_20);
return x_20;
}
default:
{
obj* x_23; 
lean::dec(x_0);
x_23 = l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__2;
lean::inc(x_23);
return x_23;
}
}
}
else
{
obj* x_25; obj* x_26; obj* x_28; obj* x_29; 
x_25 = l_lean_parser_number_has__view;
x_26 = lean::cnstr_get(x_25, 0);
lean::inc(x_26);
x_28 = lean::apply_1(x_26, x_0);
x_29 = lean::alloc_cnstr(4, 1, 0);
lean::cnstr_set(x_29, 0, x_28);
return x_29;
}
}
else
{
obj* x_31; obj* x_32; obj* x_34; obj* x_35; 
lean::dec(x_1);
x_31 = l_lean_parser_level_paren_has__view;
x_32 = lean::cnstr_get(x_31, 0);
lean::inc(x_32);
x_34 = lean::apply_1(x_32, x_0);
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
lean::inc(x_42);
return x_42;
}
default:
{
obj* x_45; 
lean::dec(x_0);
x_45 = l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__3;
lean::inc(x_45);
return x_45;
}
}
}
}
else
{
obj* x_48; 
lean::dec(x_1);
x_48 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_48, 0, x_0);
return x_48;
}
}
else
{
obj* x_50; 
lean::dec(x_1);
x_50 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_50, 0, x_0);
return x_50;
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
lean::inc(x_5);
return x_5;
}
else
{
obj* x_7; obj* x_10; obj* x_12; obj* x_15; uint8 x_16; 
x_7 = lean::cnstr_get(x_4, 0);
lean::inc(x_7);
lean::dec(x_4);
x_10 = lean::cnstr_get(x_7, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_7, 1);
lean::inc(x_12);
lean::dec(x_7);
x_15 = l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__5;
x_16 = lean_name_dec_eq(x_10, x_15);
lean::dec(x_10);
if (x_16 == 0)
{
obj* x_19; 
lean::dec(x_12);
x_19 = l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__4;
lean::inc(x_19);
return x_19;
}
else
{
if (lean::obj_tag(x_12) == 0)
{
obj* x_21; 
x_21 = l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__4;
lean::inc(x_21);
return x_21;
}
else
{
obj* x_23; obj* x_25; 
x_23 = lean::cnstr_get(x_12, 0);
lean::inc(x_23);
x_25 = lean::cnstr_get(x_12, 1);
lean::inc(x_25);
lean::dec(x_12);
if (lean::obj_tag(x_25) == 0)
{
obj* x_28; 
x_28 = l_lean_parser_syntax_as__node___main(x_23);
if (lean::obj_tag(x_28) == 0)
{
obj* x_29; 
x_29 = l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__4;
lean::inc(x_29);
return x_29;
}
else
{
obj* x_31; obj* x_34; obj* x_36; 
x_31 = lean::cnstr_get(x_28, 0);
lean::inc(x_31);
lean::dec(x_28);
x_34 = lean::cnstr_get(x_31, 0);
lean::inc(x_34);
x_36 = lean::cnstr_get(x_31, 1);
lean::inc(x_36);
lean::dec(x_31);
switch (lean::obj_tag(x_34)) {
case 0:
{
obj* x_40; 
lean::dec(x_36);
x_40 = l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__4;
lean::inc(x_40);
return x_40;
}
case 1:
{
obj* x_44; 
lean::dec(x_36);
lean::dec(x_34);
x_44 = l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__4;
lean::inc(x_44);
return x_44;
}
default:
{
obj* x_46; obj* x_48; obj* x_51; uint8 x_52; 
x_46 = lean::cnstr_get(x_34, 0);
lean::inc(x_46);
x_48 = lean::cnstr_get(x_34, 1);
lean::inc(x_48);
lean::dec(x_34);
x_51 = lean::box(0);
x_52 = lean_name_dec_eq(x_46, x_51);
lean::dec(x_46);
if (x_52 == 0)
{
obj* x_56; 
lean::dec(x_36);
lean::dec(x_48);
x_56 = l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__4;
lean::inc(x_56);
return x_56;
}
else
{
if (lean::obj_tag(x_36) == 0)
{
obj* x_59; 
lean::dec(x_48);
x_59 = l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__4;
lean::inc(x_59);
return x_59;
}
else
{
obj* x_61; obj* x_63; 
x_61 = lean::cnstr_get(x_36, 0);
lean::inc(x_61);
x_63 = lean::cnstr_get(x_36, 1);
lean::inc(x_63);
lean::dec(x_36);
if (lean::obj_tag(x_63) == 0)
{
x_1 = x_61;
x_2 = x_48;
goto lbl_3;
}
else
{
obj* x_69; 
lean::dec(x_61);
lean::dec(x_63);
lean::dec(x_48);
x_69 = l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__4;
lean::inc(x_69);
return x_69;
}
}
}
}
}
}
}
else
{
obj* x_73; 
lean::dec(x_23);
lean::dec(x_25);
x_73 = l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__4;
lean::inc(x_73);
return x_73;
}
}
}
}
lbl_3:
{
obj* x_75; uint8 x_76; 
x_75 = lean::mk_nat_obj(0u);
x_76 = lean::nat_dec_eq(x_2, x_75);
if (x_76 == 0)
{
obj* x_77; uint8 x_78; 
x_77 = lean::mk_nat_obj(1u);
x_78 = lean::nat_dec_eq(x_2, x_77);
if (x_78 == 0)
{
obj* x_79; uint8 x_80; 
x_79 = lean::mk_nat_obj(2u);
x_80 = lean::nat_dec_eq(x_2, x_79);
if (x_80 == 0)
{
obj* x_81; uint8 x_82; 
x_81 = lean::mk_nat_obj(3u);
x_82 = lean::nat_dec_eq(x_2, x_81);
if (x_82 == 0)
{
obj* x_83; uint8 x_84; 
x_83 = lean::mk_nat_obj(4u);
x_84 = lean::nat_dec_eq(x_2, x_83);
lean::dec(x_2);
if (x_84 == 0)
{
switch (lean::obj_tag(x_1)) {
case 1:
{
obj* x_86; obj* x_89; 
x_86 = lean::cnstr_get(x_1, 0);
lean::inc(x_86);
lean::dec(x_1);
x_89 = lean::alloc_cnstr(5, 1, 0);
lean::cnstr_set(x_89, 0, x_86);
return x_89;
}
case 3:
{
obj* x_90; 
x_90 = l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__2;
lean::inc(x_90);
return x_90;
}
default:
{
obj* x_93; 
lean::dec(x_1);
x_93 = l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__2;
lean::inc(x_93);
return x_93;
}
}
}
else
{
obj* x_95; obj* x_96; obj* x_98; obj* x_99; 
x_95 = l_lean_parser_number_has__view;
x_96 = lean::cnstr_get(x_95, 0);
lean::inc(x_96);
x_98 = lean::apply_1(x_96, x_1);
x_99 = lean::alloc_cnstr(4, 1, 0);
lean::cnstr_set(x_99, 0, x_98);
return x_99;
}
}
else
{
obj* x_101; obj* x_102; obj* x_104; obj* x_105; 
lean::dec(x_2);
x_101 = l_lean_parser_level_paren_has__view;
x_102 = lean::cnstr_get(x_101, 0);
lean::inc(x_102);
x_104 = lean::apply_1(x_102, x_1);
x_105 = lean::alloc_cnstr(3, 1, 0);
lean::cnstr_set(x_105, 0, x_104);
return x_105;
}
}
else
{
lean::dec(x_2);
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
case 3:
{
obj* x_112; 
x_112 = l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__3;
lean::inc(x_112);
return x_112;
}
default:
{
obj* x_115; 
lean::dec(x_1);
x_115 = l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__3;
lean::inc(x_115);
return x_115;
}
}
}
}
else
{
obj* x_118; 
lean::dec(x_2);
x_118 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_118, 0, x_1);
return x_118;
}
}
else
{
obj* x_120; 
lean::dec(x_2);
x_120 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_120, 0, x_1);
return x_120;
}
}
}
}
obj* _init_l_lean_parser_level_leading_has__view_x_27___lambda__2___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_nat_obj(4u);
x_2 = lean_name_mk_numeral(x_0, x_1);
return x_2;
}
}
obj* _init_l_lean_parser_level_leading_has__view_x_27___lambda__2___closed__2() {
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
obj* x_2; obj* x_5; obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_12; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
x_5 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_5, 0, x_2);
lean::cnstr_set(x_5, 1, x_1);
x_6 = l_lean_parser_detail__ident__part_has__view_x_27___lambda__2___closed__1;
lean::inc(x_6);
x_8 = l_lean_parser_syntax_mk__node(x_6, x_5);
x_9 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_1);
x_10 = l_lean_parser_level_leading;
lean::inc(x_10);
x_12 = l_lean_parser_syntax_mk__node(x_10, x_9);
return x_12;
}
case 1:
{
obj* x_13; obj* x_16; obj* x_17; obj* x_19; obj* x_20; obj* x_21; obj* x_23; 
x_13 = lean::cnstr_get(x_0, 0);
lean::inc(x_13);
lean::dec(x_0);
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_13);
lean::cnstr_set(x_16, 1, x_1);
x_17 = l_lean_parser_detail__ident__part_has__view_x_27___lambda__2___closed__2;
lean::inc(x_17);
x_19 = l_lean_parser_syntax_mk__node(x_17, x_16);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_1);
x_21 = l_lean_parser_level_leading;
lean::inc(x_21);
x_23 = l_lean_parser_syntax_mk__node(x_21, x_20);
return x_23;
}
case 2:
{
obj* x_24; obj* x_27; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_35; obj* x_36; obj* x_37; obj* x_39; 
x_24 = lean::cnstr_get(x_0, 0);
lean::inc(x_24);
lean::dec(x_0);
x_27 = l_lean_parser_raw_view___rarg___lambda__3___closed__1;
lean::inc(x_27);
x_29 = l_option_map___rarg(x_27, x_24);
x_30 = lean::box(3);
x_31 = l_option_get__or__else___main___rarg(x_29, x_30);
x_32 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_1);
x_33 = l_lean_parser_number_has__view_x_27___lambda__2___closed__1;
lean::inc(x_33);
x_35 = l_lean_parser_syntax_mk__node(x_33, x_32);
x_36 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_36, 0, x_35);
lean::cnstr_set(x_36, 1, x_1);
x_37 = l_lean_parser_level_leading;
lean::inc(x_37);
x_39 = l_lean_parser_syntax_mk__node(x_37, x_36);
return x_39;
}
case 3:
{
obj* x_40; obj* x_43; obj* x_44; obj* x_46; obj* x_47; obj* x_48; obj* x_50; obj* x_51; obj* x_52; obj* x_54; 
x_40 = lean::cnstr_get(x_0, 0);
lean::inc(x_40);
lean::dec(x_0);
x_43 = l_lean_parser_level_paren_has__view;
x_44 = lean::cnstr_get(x_43, 1);
lean::inc(x_44);
x_46 = lean::apply_1(x_44, x_40);
x_47 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_47, 0, x_46);
lean::cnstr_set(x_47, 1, x_1);
x_48 = l_lean_parser_number_has__view_x_27___lambda__2___closed__2;
lean::inc(x_48);
x_50 = l_lean_parser_syntax_mk__node(x_48, x_47);
x_51 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_51, 0, x_50);
lean::cnstr_set(x_51, 1, x_1);
x_52 = l_lean_parser_level_leading;
lean::inc(x_52);
x_54 = l_lean_parser_syntax_mk__node(x_52, x_51);
return x_54;
}
case 4:
{
obj* x_55; obj* x_58; obj* x_59; obj* x_61; obj* x_62; obj* x_63; obj* x_65; obj* x_66; obj* x_67; obj* x_69; 
x_55 = lean::cnstr_get(x_0, 0);
lean::inc(x_55);
lean::dec(x_0);
x_58 = l_lean_parser_number_has__view;
x_59 = lean::cnstr_get(x_58, 1);
lean::inc(x_59);
x_61 = lean::apply_1(x_59, x_55);
x_62 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_62, 0, x_61);
lean::cnstr_set(x_62, 1, x_1);
x_63 = l_lean_parser_level_leading_has__view_x_27___lambda__2___closed__1;
lean::inc(x_63);
x_65 = l_lean_parser_syntax_mk__node(x_63, x_62);
x_66 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_66, 0, x_65);
lean::cnstr_set(x_66, 1, x_1);
x_67 = l_lean_parser_level_leading;
lean::inc(x_67);
x_69 = l_lean_parser_syntax_mk__node(x_67, x_66);
return x_69;
}
default:
{
obj* x_70; obj* x_73; obj* x_74; obj* x_75; obj* x_77; obj* x_78; obj* x_79; obj* x_81; 
x_70 = lean::cnstr_get(x_0, 0);
lean::inc(x_70);
lean::dec(x_0);
x_73 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_73, 0, x_70);
x_74 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_74, 0, x_73);
lean::cnstr_set(x_74, 1, x_1);
x_75 = l_lean_parser_level_leading_has__view_x_27___lambda__2___closed__2;
lean::inc(x_75);
x_77 = l_lean_parser_syntax_mk__node(x_75, x_74);
x_78 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_78, 0, x_77);
lean::cnstr_set(x_78, 1, x_1);
x_79 = l_lean_parser_level_leading;
lean::inc(x_79);
x_81 = l_lean_parser_syntax_mk__node(x_79, x_78);
return x_81;
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
lean::inc(x_0);
return x_0;
}
}
obj* l_lean_parser_symbol__or__ident___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_8; obj* x_9; obj* x_11; obj* x_13; 
lean::dec(x_1);
lean::inc(x_3);
lean::inc(x_2);
x_8 = l_lean_parser_token(x_2, x_3, x_4);
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
obj* x_23; obj* x_25; obj* x_28; 
x_23 = lean::cnstr_get(x_14, 0);
lean::inc(x_23);
x_25 = lean::cnstr_get(x_23, 1);
lean::inc(x_25);
lean::dec(x_23);
x_28 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_28, 0, x_25);
x_21 = x_28;
goto lbl_22;
}
case 1:
{
obj* x_29; obj* x_31; obj* x_34; obj* x_35; 
x_29 = lean::cnstr_get(x_14, 0);
lean::inc(x_29);
x_31 = lean::cnstr_get(x_29, 1);
lean::inc(x_31);
lean::dec(x_29);
x_34 = l_lean_parser_substring_to__string(x_31);
x_35 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_35, 0, x_34);
x_21 = x_35;
goto lbl_22;
}
default:
{
obj* x_36; 
x_36 = lean::box(0);
x_21 = x_36;
goto lbl_22;
}
}
lbl_22:
{
uint8 x_37; 
if (lean::obj_tag(x_21) == 0)
{
uint8 x_39; 
x_39 = 1;
x_37 = x_39;
goto lbl_38;
}
else
{
obj* x_40; uint8 x_43; 
x_40 = lean::cnstr_get(x_21, 0);
lean::inc(x_40);
lean::dec(x_21);
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
obj* x_50; obj* x_52; obj* x_53; obj* x_54; obj* x_56; obj* x_57; obj* x_58; 
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
x_50 = l_lean_parser_finish__comment__block___closed__2;
lean::inc(x_50);
if (lean::is_scalar(x_20)) {
 x_52 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_52 = x_20;
}
lean::cnstr_set(x_52, 0, x_14);
lean::cnstr_set(x_52, 1, x_16);
lean::cnstr_set(x_52, 2, x_50);
x_53 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_18, x_52);
x_54 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_54);
x_56 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_54, x_53);
x_57 = l_lean_parser_parsec__t_try__mk__res___rarg(x_56);
if (lean::is_scalar(x_13)) {
 x_58 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_58 = x_13;
}
lean::cnstr_set(x_58, 0, x_57);
lean::cnstr_set(x_58, 1, x_11);
return x_58;
}
else
{
obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_65; obj* x_66; obj* x_68; 
x_59 = l_string_quote(x_0);
x_60 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_60, 0, x_59);
x_61 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_61, 0, x_3);
x_62 = lean::box(0);
x_63 = l_string_join___closed__1;
lean::inc(x_63);
x_65 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_63, x_60, x_61, x_62, x_2, x_16, x_11);
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
if (lean::is_scalar(x_20)) {
 x_78 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_78 = x_20;
}
lean::cnstr_set(x_78, 0, x_14);
lean::cnstr_set(x_78, 1, x_71);
lean::cnstr_set(x_78, 2, x_76);
x_79 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_73, x_78);
x_80 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_18, x_79);
lean::inc(x_76);
x_82 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_76, x_80);
x_83 = l_lean_parser_parsec__t_try__mk__res___rarg(x_82);
if (lean::is_scalar(x_13)) {
 x_84 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_84 = x_13;
}
lean::cnstr_set(x_84, 0, x_83);
lean::cnstr_set(x_84, 1, x_68);
return x_84;
}
else
{
obj* x_87; uint8 x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_96; obj* x_97; obj* x_98; 
lean::dec(x_14);
lean::dec(x_20);
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
x_93 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_18, x_92);
x_94 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_94);
x_96 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_94, x_93);
x_97 = l_lean_parser_parsec__t_try__mk__res___rarg(x_96);
if (lean::is_scalar(x_13)) {
 x_98 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_98 = x_13;
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
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
x_102 = lean::cnstr_get(x_9, 0);
lean::inc(x_102);
x_104 = lean::cnstr_get_scalar<uint8>(x_9, sizeof(void*)*1);
if (lean::is_shared(x_9)) {
 lean::dec(x_9);
 x_105 = lean::box(0);
} else {
 lean::cnstr_release(x_9, 0);
 x_105 = x_9;
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
if (lean::is_scalar(x_13)) {
 x_112 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_112 = x_13;
}
lean::cnstr_set(x_112, 0, x_111);
lean::cnstr_set(x_112, 1, x_11);
return x_112;
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
obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_19; 
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
lean::inc(x_11);
x_19 = l_lean_parser_try__view___at_lean_parser_number_parser___spec__1(x_11);
if (lean::obj_tag(x_19) == 0)
{
obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_28; obj* x_29; obj* x_31; obj* x_34; obj* x_36; obj* x_37; obj* x_39; obj* x_41; obj* x_42; obj* x_43; 
lean::dec(x_17);
lean::dec(x_11);
x_22 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_22, 0, x_1);
x_23 = lean::box(0);
x_24 = l_string_join___closed__1;
x_25 = l_lean_parser_number_parser___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__2___rarg___closed__1;
lean::inc(x_25);
lean::inc(x_24);
x_28 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_24, x_25, x_22, x_23, x_0, x_13, x_8);
x_29 = lean::cnstr_get(x_28, 0);
lean::inc(x_29);
x_31 = lean::cnstr_get(x_28, 1);
lean::inc(x_31);
lean::dec(x_28);
x_34 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_34);
x_36 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_34, x_29);
x_37 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_36);
lean::inc(x_34);
x_39 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_34, x_37);
lean::inc(x_25);
x_41 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_39, x_25);
x_42 = l_lean_parser_parsec__t_try__mk__res___rarg(x_41);
if (lean::is_scalar(x_10)) {
 x_43 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_43 = x_10;
}
lean::cnstr_set(x_43, 0, x_42);
lean::cnstr_set(x_43, 1, x_31);
return x_43;
}
else
{
obj* x_47; obj* x_49; obj* x_50; obj* x_51; obj* x_53; obj* x_54; obj* x_56; obj* x_57; obj* x_58; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_19);
x_47 = l_lean_parser_finish__comment__block___closed__2;
lean::inc(x_47);
if (lean::is_scalar(x_17)) {
 x_49 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_49 = x_17;
}
lean::cnstr_set(x_49, 0, x_11);
lean::cnstr_set(x_49, 1, x_13);
lean::cnstr_set(x_49, 2, x_47);
x_50 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_49);
x_51 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_51);
x_53 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_51, x_50);
x_54 = l_lean_parser_number_parser___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__2___rarg___closed__1;
lean::inc(x_54);
x_56 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_53, x_54);
x_57 = l_lean_parser_parsec__t_try__mk__res___rarg(x_56);
if (lean::is_scalar(x_10)) {
 x_58 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_58 = x_10;
}
lean::cnstr_set(x_58, 0, x_57);
lean::cnstr_set(x_58, 1, x_8);
return x_58;
}
}
else
{
obj* x_61; uint8 x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_69; obj* x_70; obj* x_72; obj* x_73; obj* x_74; 
lean::dec(x_1);
lean::dec(x_0);
x_61 = lean::cnstr_get(x_6, 0);
lean::inc(x_61);
x_63 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*1);
if (lean::is_shared(x_6)) {
 lean::dec(x_6);
 x_64 = lean::box(0);
} else {
 lean::cnstr_release(x_6, 0);
 x_64 = x_6;
}
if (lean::is_scalar(x_64)) {
 x_65 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_65 = x_64;
}
lean::cnstr_set(x_65, 0, x_61);
lean::cnstr_set_scalar(x_65, sizeof(void*)*1, x_63);
x_66 = x_65;
x_67 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_67);
x_69 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_67, x_66);
x_70 = l_lean_parser_number_parser___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__2___rarg___closed__1;
lean::inc(x_70);
x_72 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_69, x_70);
x_73 = l_lean_parser_parsec__t_try__mk__res___rarg(x_72);
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
obj* l_lean_parser_number_parser___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__2(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_number_parser___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__2___rarg), 3, 0);
return x_2;
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
case 1:
{
obj* x_23; obj* x_25; obj* x_26; obj* x_28; obj* x_29; obj* x_31; obj* x_32; obj* x_33; 
lean::dec(x_1);
lean::dec(x_10);
lean::dec(x_0);
x_23 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_23);
if (lean::is_scalar(x_17)) {
 x_25 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_25 = x_17;
}
lean::cnstr_set(x_25, 0, x_11);
lean::cnstr_set(x_25, 1, x_13);
lean::cnstr_set(x_25, 2, x_23);
x_26 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_25);
lean::inc(x_23);
x_28 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_23, x_26);
x_29 = l_lean_parser_ident_parser___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__3___rarg___closed__1;
lean::inc(x_29);
x_31 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_28, x_29);
x_32 = l_lean_parser_parsec__t_try__mk__res___rarg(x_31);
x_33 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_8);
return x_33;
}
case 3:
{
obj* x_35; 
lean::dec(x_17);
x_35 = lean::box(0);
x_18 = x_35;
goto lbl_19;
}
default:
{
obj* x_38; 
lean::dec(x_17);
lean::dec(x_11);
x_38 = lean::box(0);
x_18 = x_38;
goto lbl_19;
}
}
lbl_19:
{
obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_46; obj* x_47; obj* x_49; obj* x_52; obj* x_53; obj* x_55; obj* x_57; obj* x_58; obj* x_59; 
lean::dec(x_18);
x_40 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_40, 0, x_1);
x_41 = lean::box(0);
x_42 = l_string_join___closed__1;
x_43 = l_lean_parser_ident_parser___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__3___rarg___closed__1;
lean::inc(x_43);
lean::inc(x_42);
x_46 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_42, x_43, x_40, x_41, x_0, x_13, x_8);
x_47 = lean::cnstr_get(x_46, 0);
lean::inc(x_47);
x_49 = lean::cnstr_get(x_46, 1);
lean::inc(x_49);
lean::dec(x_46);
x_52 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_47);
x_53 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_53);
x_55 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_53, x_52);
lean::inc(x_43);
x_57 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_55, x_43);
x_58 = l_lean_parser_parsec__t_try__mk__res___rarg(x_57);
if (lean::is_scalar(x_10)) {
 x_59 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_59 = x_10;
}
lean::cnstr_set(x_59, 0, x_58);
lean::cnstr_set(x_59, 1, x_49);
return x_59;
}
}
else
{
obj* x_62; uint8 x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_70; obj* x_71; obj* x_73; obj* x_74; obj* x_75; 
lean::dec(x_1);
lean::dec(x_0);
x_62 = lean::cnstr_get(x_6, 0);
lean::inc(x_62);
x_64 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*1);
if (lean::is_shared(x_6)) {
 lean::dec(x_6);
 x_65 = lean::box(0);
} else {
 lean::cnstr_release(x_6, 0);
 x_65 = x_6;
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
lean::inc(x_68);
x_70 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_68, x_67);
x_71 = l_lean_parser_ident_parser___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__3___rarg___closed__1;
lean::inc(x_71);
x_73 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_70, x_71);
x_74 = l_lean_parser_parsec__t_try__mk__res___rarg(x_73);
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
obj* l_lean_parser_ident_parser___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__3(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_ident_parser___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__3___rarg), 3, 0);
return x_2;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__5___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
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
obj* l_lean_parser_monad__parsec_error___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__5(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__5___rarg), 8, 0);
return x_2;
}
}
obj* l_lean_parser_combinators_choice__aux___main___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__4(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_12; 
lean::dec(x_1);
x_7 = lean::box(0);
x_8 = l_lean_parser_combinators_choice__aux___main___rarg___closed__1;
x_9 = l_mjoin___rarg___closed__1;
lean::inc(x_9);
lean::inc(x_8);
x_12 = l_lean_parser_monad__parsec_error___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__5___rarg(x_8, x_9, x_7, x_7, x_2, x_3, x_4, x_5);
return x_12;
}
else
{
obj* x_13; obj* x_15; obj* x_17; obj* x_21; obj* x_22; obj* x_24; obj* x_26; obj* x_27; obj* x_28; 
x_13 = lean::cnstr_get(x_0, 0);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_0, 1);
lean::inc(x_15);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_17 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_17 = x_0;
}
lean::inc(x_4);
lean::inc(x_3);
lean::inc(x_2);
x_21 = lean::apply_4(x_13, x_2, x_3, x_4, x_5);
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
if (lean::obj_tag(x_22) == 0)
{
obj* x_29; obj* x_31; obj* x_33; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_42; obj* x_43; 
x_29 = lean::cnstr_get(x_22, 0);
lean::inc(x_29);
x_31 = lean::cnstr_get(x_22, 1);
lean::inc(x_31);
x_33 = lean::cnstr_get(x_22, 2);
lean::inc(x_33);
if (lean::is_shared(x_22)) {
 lean::dec(x_22);
 x_35 = lean::box(0);
} else {
 lean::cnstr_release(x_22, 0);
 lean::cnstr_release(x_22, 1);
 lean::cnstr_release(x_22, 2);
 x_35 = x_22;
}
x_36 = lean::box(0);
x_37 = lean_name_mk_numeral(x_36, x_1);
if (lean::is_scalar(x_17)) {
 x_38 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_38 = x_17;
}
lean::cnstr_set(x_38, 0, x_29);
lean::cnstr_set(x_38, 1, x_36);
x_39 = l_lean_parser_syntax_mk__node(x_37, x_38);
x_40 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_40);
if (lean::is_scalar(x_35)) {
 x_42 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_42 = x_35;
}
lean::cnstr_set(x_42, 0, x_39);
lean::cnstr_set(x_42, 1, x_31);
lean::cnstr_set(x_42, 2, x_40);
x_43 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_33, x_42);
if (lean::obj_tag(x_43) == 0)
{
obj* x_49; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_28);
lean::dec(x_15);
if (lean::is_scalar(x_26)) {
 x_49 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_49 = x_26;
}
lean::cnstr_set(x_49, 0, x_43);
lean::cnstr_set(x_49, 1, x_24);
return x_49;
}
else
{
obj* x_50; uint8 x_52; 
x_50 = lean::cnstr_get(x_43, 0);
lean::inc(x_50);
x_52 = lean::cnstr_get_scalar<uint8>(x_43, sizeof(void*)*1);
if (x_52 == 0)
{
obj* x_54; obj* x_55; obj* x_57; obj* x_60; obj* x_61; 
lean::dec(x_43);
x_54 = l_lean_parser_combinators_choice__aux___main___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__4(x_15, x_28, x_2, x_3, x_4, x_24);
x_55 = lean::cnstr_get(x_54, 0);
lean::inc(x_55);
x_57 = lean::cnstr_get(x_54, 1);
lean::inc(x_57);
lean::dec(x_54);
x_60 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_50, x_55);
if (lean::is_scalar(x_26)) {
 x_61 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_61 = x_26;
}
lean::cnstr_set(x_61, 0, x_60);
lean::cnstr_set(x_61, 1, x_57);
return x_61;
}
else
{
obj* x_68; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_50);
lean::dec(x_28);
lean::dec(x_15);
if (lean::is_scalar(x_26)) {
 x_68 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_68 = x_26;
}
lean::cnstr_set(x_68, 0, x_43);
lean::cnstr_set(x_68, 1, x_24);
return x_68;
}
}
}
else
{
obj* x_71; uint8 x_73; obj* x_74; 
lean::dec(x_1);
lean::dec(x_17);
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
x_76 = l_lean_parser_combinators_choice__aux___main___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__4(x_15, x_28, x_2, x_3, x_4, x_24);
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
obj* x_89; obj* x_90; obj* x_91; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_28);
lean::dec(x_15);
if (lean::is_scalar(x_74)) {
 x_89 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_89 = x_74;
}
lean::cnstr_set(x_89, 0, x_71);
lean::cnstr_set_scalar(x_89, sizeof(void*)*1, x_73);
x_90 = x_89;
if (lean::is_scalar(x_26)) {
 x_91 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_91 = x_26;
}
lean::cnstr_set(x_91, 0, x_90);
lean::cnstr_set(x_91, 1, x_24);
return x_91;
}
}
}
}
}
obj* _init_l_lean_parser_level_leading_parser_lean_parser_has__tokens() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_0 = lean::box(0);
x_1 = lean::mk_string("_");
x_2 = l_lean_parser_max__prec;
lean::inc(x_2);
x_4 = l_lean_parser_symbol_tokens___rarg(x_1, x_2);
x_5 = l_lean_parser_list_cons_tokens___rarg(x_0, x_0);
x_6 = l_lean_parser_list_cons_tokens___rarg(x_0, x_5);
x_7 = l_lean_parser_level_paren_parser_lean_parser_has__tokens;
lean::inc(x_7);
x_9 = l_lean_parser_list_cons_tokens___rarg(x_7, x_6);
x_10 = l_lean_parser_list_cons_tokens___rarg(x_4, x_9);
x_11 = l_lean_parser_list_cons_tokens___rarg(x_0, x_10);
x_12 = l_lean_parser_list_cons_tokens___rarg(x_0, x_11);
x_13 = l_lean_parser_tokens___rarg(x_12);
x_14 = l_lean_parser_list_cons_tokens___rarg(x_13, x_0);
x_15 = l_lean_parser_tokens___rarg(x_14);
return x_15;
}
}
obj* _init_l_lean_parser_level_leading_parser_lean_parser_has__view() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_7; obj* x_8; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_36; 
x_0 = lean::mk_string("max");
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__or__ident___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__1), 5, 1);
lean::closure_set(x_1, 0, x_0);
x_2 = lean::mk_string("imax");
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__or__ident___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__1), 5, 1);
lean::closure_set(x_3, 0, x_2);
x_4 = lean::mk_string("_");
x_5 = l_string_trim(x_4);
lean::inc(x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_7, 0, x_5);
x_8 = l_lean_parser_max__prec;
lean::inc(x_8);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_level_paren_parser_lean_parser_has__tokens___spec__1), 7, 3);
lean::closure_set(x_10, 0, x_5);
lean::closure_set(x_10, 1, x_8);
lean::closure_set(x_10, 2, x_7);
x_11 = lean::box(0);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_ident_parser___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__3), 1, 0);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_11);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_number_parser___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__2), 1, 0);
x_15 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_15, 0, x_14);
lean::cnstr_set(x_15, 1, x_13);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_level_paren_parser), 4, 0);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_15);
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_10);
lean::cnstr_set(x_18, 1, x_17);
x_19 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_19, 0, x_3);
lean::cnstr_set(x_19, 1, x_18);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_1);
lean::cnstr_set(x_20, 1, x_19);
x_21 = lean::mk_nat_obj(0u);
x_22 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_choice__aux___main___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__4), 6, 2);
lean::closure_set(x_22, 0, x_20);
lean::closure_set(x_22, 1, x_21);
x_23 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_23, 0, x_22);
lean::cnstr_set(x_23, 1, x_11);
x_24 = l_lean_parser_level__parser__m_monad;
x_25 = l_lean_parser_level__parser__m_monad__except;
x_26 = l_lean_parser_level__parser__m_lean_parser_monad__parsec;
x_27 = l_lean_parser_level__parser__m_alternative;
x_28 = l_lean_parser_level_leading;
x_29 = l_lean_parser_level_leading_has__view;
lean::inc(x_29);
lean::inc(x_28);
lean::inc(x_27);
lean::inc(x_26);
lean::inc(x_25);
lean::inc(x_24);
x_36 = l_lean_parser_combinators_node_view___rarg(x_24, x_25, x_26, x_27, x_28, x_23, x_29);
return x_36;
}
}
obj* _init_l_lean_parser_level_leading_parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_7; obj* x_8; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
x_0 = lean::mk_string("max");
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__or__ident___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__1), 5, 1);
lean::closure_set(x_1, 0, x_0);
x_2 = lean::mk_string("imax");
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__or__ident___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__1), 5, 1);
lean::closure_set(x_3, 0, x_2);
x_4 = lean::mk_string("_");
x_5 = l_string_trim(x_4);
lean::inc(x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_7, 0, x_5);
x_8 = l_lean_parser_max__prec;
lean::inc(x_8);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_level_paren_parser_lean_parser_has__tokens___spec__1), 7, 3);
lean::closure_set(x_10, 0, x_5);
lean::closure_set(x_10, 1, x_8);
lean::closure_set(x_10, 2, x_7);
x_11 = lean::box(0);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_ident_parser___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__3), 1, 0);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_11);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_number_parser___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__2), 1, 0);
x_15 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_15, 0, x_14);
lean::cnstr_set(x_15, 1, x_13);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_level_paren_parser), 4, 0);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_15);
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_10);
lean::cnstr_set(x_18, 1, x_17);
x_19 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_19, 0, x_3);
lean::cnstr_set(x_19, 1, x_18);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_1);
lean::cnstr_set(x_20, 1, x_19);
x_21 = lean::mk_nat_obj(0u);
x_22 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_choice__aux___main___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__4), 6, 2);
lean::closure_set(x_22, 0, x_20);
lean::closure_set(x_22, 1, x_21);
x_23 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_23, 0, x_22);
lean::cnstr_set(x_23, 1, x_11);
return x_23;
}
}
obj* l_lean_parser_level_leading_parser(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_8; 
x_4 = l_lean_parser_level_leading;
x_5 = l_lean_parser_level_leading_parser___closed__1;
lean::inc(x_5);
lean::inc(x_4);
x_8 = l_lean_parser_combinators_node___at_lean_parser_level_paren_parser___spec__1(x_4, x_5, x_0, x_1, x_2, x_3);
return x_8;
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
lean::inc(x_2);
return x_2;
}
else
{
obj* x_4; obj* x_7; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
lean::dec(x_1);
x_7 = lean::cnstr_get(x_4, 1);
lean::inc(x_7);
lean::dec(x_4);
if (lean::obj_tag(x_7) == 0)
{
if (lean::obj_tag(x_7) == 0)
{
obj* x_10; 
x_10 = l_lean_parser_level_app_has__view_x_27___lambda__1___closed__1;
lean::inc(x_10);
return x_10;
}
else
{
obj* x_12; obj* x_15; obj* x_16; 
x_12 = lean::cnstr_get(x_7, 0);
lean::inc(x_12);
lean::dec(x_7);
x_15 = lean::box(3);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_15);
lean::cnstr_set(x_16, 1, x_12);
return x_16;
}
}
else
{
obj* x_17; obj* x_19; 
x_17 = lean::cnstr_get(x_7, 0);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_7, 1);
lean::inc(x_19);
lean::dec(x_7);
if (lean::obj_tag(x_19) == 0)
{
obj* x_22; obj* x_23; 
x_22 = lean::box(3);
x_23 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_23, 0, x_17);
lean::cnstr_set(x_23, 1, x_22);
return x_23;
}
else
{
obj* x_24; obj* x_27; 
x_24 = lean::cnstr_get(x_19, 0);
lean::inc(x_24);
lean::dec(x_19);
x_27 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_27, 0, x_17);
lean::cnstr_set(x_27, 1, x_24);
return x_27;
}
}
}
}
}
obj* l_lean_parser_level_app_has__view_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_11; 
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
lean::inc(x_9);
x_11 = l_lean_parser_syntax_mk__node(x_9, x_8);
return x_11;
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
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_lean_parser_level_app_parser_lean_parser_has__tokens() {
_start:
{
obj* x_0; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_7; obj* x_8; 
x_0 = l_lean_parser_level_parser_lean_parser_has__tokens___closed__1;
lean::inc(x_0);
x_2 = l_lean_parser_tokens___rarg(x_0);
x_3 = lean::box(0);
x_4 = l_lean_parser_list_cons_tokens___rarg(x_2, x_3);
x_5 = l_lean_parser_level_lean_parser_has__tokens;
lean::inc(x_5);
x_7 = l_lean_parser_list_cons_tokens___rarg(x_5, x_4);
x_8 = l_lean_parser_tokens___rarg(x_7);
return x_8;
}
}
obj* l_lean_parser_level_app_parser_lean_parser_has__view___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_6; obj* x_8; 
lean::dec(x_0);
x_6 = l_lean_parser_max__prec;
lean::inc(x_6);
x_8 = l_lean_parser_level_parser(x_6, x_1, x_2, x_3, x_4);
return x_8;
}
}
obj* _init_l_lean_parser_level_app_parser_lean_parser_has__view() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_17; 
x_0 = lean::box(0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_level_app_parser_lean_parser_has__view___lambda__1), 5, 0);
x_2 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_2, 0, x_1);
lean::cnstr_set(x_2, 1, x_0);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_level_get__leading), 5, 0);
x_4 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_2);
x_5 = l_lean_parser_trailing__level__parser__m_monad;
x_6 = l_lean_parser_trailing__level__parser__m_monad__except;
x_7 = l_lean_parser_trailing__level__parser__m_lean_parser_monad__parsec;
x_8 = l_lean_parser_trailing__level__parser__m_alternative;
x_9 = l_lean_parser_level_app;
x_10 = l_lean_parser_level_app_has__view;
lean::inc(x_10);
lean::inc(x_9);
lean::inc(x_8);
lean::inc(x_7);
lean::inc(x_6);
lean::inc(x_5);
x_17 = l_lean_parser_combinators_node_view___rarg(x_5, x_6, x_7, x_8, x_9, x_4, x_10);
return x_17;
}
}
obj* l_list_mfoldl___main___at_lean_parser_level_app_parser___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_12; obj* x_14; obj* x_15; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_0);
x_12 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_12);
x_14 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_14, 0, x_1);
lean::cnstr_set(x_14, 1, x_6);
lean::cnstr_set(x_14, 2, x_12);
x_15 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_15, 0, x_14);
lean::cnstr_set(x_15, 1, x_7);
return x_15;
}
else
{
obj* x_16; obj* x_18; obj* x_20; obj* x_21; obj* x_22; obj* x_27; obj* x_28; obj* x_30; 
x_16 = lean::cnstr_get(x_2, 0);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_2, 1);
lean::inc(x_18);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_20 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 lean::cnstr_release(x_2, 1);
 x_20 = x_2;
}
lean::inc(x_5);
lean::inc(x_4);
lean::inc(x_3);
x_27 = lean::apply_5(x_16, x_3, x_4, x_5, x_6, x_7);
x_28 = lean::cnstr_get(x_27, 0);
lean::inc(x_28);
x_30 = lean::cnstr_get(x_27, 1);
lean::inc(x_30);
lean::dec(x_27);
if (lean::obj_tag(x_28) == 0)
{
x_21 = x_28;
x_22 = x_30;
goto lbl_23;
}
else
{
obj* x_33; uint8 x_35; obj* x_36; 
x_33 = lean::cnstr_get(x_28, 0);
lean::inc(x_33);
x_35 = lean::cnstr_get_scalar<uint8>(x_28, sizeof(void*)*1);
if (lean::is_shared(x_28)) {
 lean::dec(x_28);
 x_36 = lean::box(0);
} else {
 lean::cnstr_release(x_28, 0);
 x_36 = x_28;
}
if (lean::obj_tag(x_1) == 0)
{
if (x_35 == 0)
{
uint8 x_37; obj* x_38; obj* x_39; 
x_37 = 0;
if (lean::is_scalar(x_36)) {
 x_38 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_38 = x_36;
}
lean::cnstr_set(x_38, 0, x_33);
lean::cnstr_set_scalar(x_38, sizeof(void*)*1, x_37);
x_39 = x_38;
x_21 = x_39;
x_22 = x_30;
goto lbl_23;
}
else
{
obj* x_40; obj* x_41; 
if (lean::is_scalar(x_36)) {
 x_40 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_40 = x_36;
}
lean::cnstr_set(x_40, 0, x_33);
lean::cnstr_set_scalar(x_40, sizeof(void*)*1, x_35);
x_41 = x_40;
x_21 = x_41;
x_22 = x_30;
goto lbl_23;
}
}
else
{
obj* x_42; obj* x_44; obj* x_46; obj* x_47; obj* x_49; obj* x_51; obj* x_54; obj* x_56; obj* x_57; obj* x_58; 
x_42 = lean::cnstr_get(x_33, 3);
lean::inc(x_42);
x_44 = l_option_get___main___at_lean_parser_run___spec__2(x_42);
lean::inc(x_1);
x_46 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_46, 0, x_44);
lean::cnstr_set(x_46, 1, x_1);
x_47 = lean::cnstr_get(x_33, 0);
lean::inc(x_47);
x_49 = lean::cnstr_get(x_33, 1);
lean::inc(x_49);
x_51 = lean::cnstr_get(x_33, 2);
lean::inc(x_51);
lean::dec(x_33);
x_54 = l_list_reverse___rarg(x_46);
lean::inc(x_0);
x_56 = l_lean_parser_syntax_mk__node(x_0, x_54);
x_57 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_57, 0, x_56);
x_58 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_58, 0, x_47);
lean::cnstr_set(x_58, 1, x_49);
lean::cnstr_set(x_58, 2, x_51);
lean::cnstr_set(x_58, 3, x_57);
if (x_35 == 0)
{
uint8 x_59; obj* x_60; obj* x_61; 
x_59 = 0;
if (lean::is_scalar(x_36)) {
 x_60 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_60 = x_36;
}
lean::cnstr_set(x_60, 0, x_58);
lean::cnstr_set_scalar(x_60, sizeof(void*)*1, x_59);
x_61 = x_60;
x_21 = x_61;
x_22 = x_30;
goto lbl_23;
}
else
{
obj* x_62; obj* x_63; 
if (lean::is_scalar(x_36)) {
 x_62 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_62 = x_36;
}
lean::cnstr_set(x_62, 0, x_58);
lean::cnstr_set_scalar(x_62, sizeof(void*)*1, x_35);
x_63 = x_62;
x_21 = x_63;
x_22 = x_30;
goto lbl_23;
}
}
}
lbl_23:
{
if (lean::obj_tag(x_21) == 0)
{
obj* x_64; obj* x_66; obj* x_68; obj* x_70; obj* x_71; obj* x_72; obj* x_74; obj* x_75; 
x_64 = lean::cnstr_get(x_21, 0);
lean::inc(x_64);
x_66 = lean::cnstr_get(x_21, 1);
lean::inc(x_66);
x_68 = lean::cnstr_get(x_21, 2);
lean::inc(x_68);
if (lean::is_shared(x_21)) {
 lean::dec(x_21);
 x_70 = lean::box(0);
} else {
 lean::cnstr_release(x_21, 0);
 lean::cnstr_release(x_21, 1);
 lean::cnstr_release(x_21, 2);
 x_70 = x_21;
}
if (lean::is_scalar(x_20)) {
 x_71 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_71 = x_20;
}
lean::cnstr_set(x_71, 0, x_64);
lean::cnstr_set(x_71, 1, x_1);
x_72 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_72);
if (lean::is_scalar(x_70)) {
 x_74 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_74 = x_70;
}
lean::cnstr_set(x_74, 0, x_71);
lean::cnstr_set(x_74, 1, x_66);
lean::cnstr_set(x_74, 2, x_72);
x_75 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_68, x_74);
if (lean::obj_tag(x_75) == 0)
{
obj* x_76; obj* x_78; obj* x_80; obj* x_83; obj* x_84; obj* x_86; obj* x_88; obj* x_89; obj* x_90; 
x_76 = lean::cnstr_get(x_75, 0);
lean::inc(x_76);
x_78 = lean::cnstr_get(x_75, 1);
lean::inc(x_78);
x_80 = lean::cnstr_get(x_75, 2);
lean::inc(x_80);
lean::dec(x_75);
x_83 = l_list_mfoldl___main___at_lean_parser_level_app_parser___spec__2(x_0, x_76, x_18, x_3, x_4, x_5, x_78, x_22);
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
x_89 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_80, x_84);
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
obj* x_96; uint8 x_98; obj* x_99; obj* x_100; obj* x_101; obj* x_102; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_18);
x_96 = lean::cnstr_get(x_75, 0);
lean::inc(x_96);
x_98 = lean::cnstr_get_scalar<uint8>(x_75, sizeof(void*)*1);
if (lean::is_shared(x_75)) {
 lean::dec(x_75);
 x_99 = lean::box(0);
} else {
 lean::cnstr_release(x_75, 0);
 x_99 = x_75;
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
lean::cnstr_set(x_102, 1, x_22);
return x_102;
}
}
else
{
obj* x_110; uint8 x_112; obj* x_113; obj* x_114; obj* x_115; obj* x_116; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_18);
lean::dec(x_20);
x_110 = lean::cnstr_get(x_21, 0);
lean::inc(x_110);
x_112 = lean::cnstr_get_scalar<uint8>(x_21, sizeof(void*)*1);
if (lean::is_shared(x_21)) {
 lean::dec(x_21);
 x_113 = lean::box(0);
} else {
 lean::cnstr_release(x_21, 0);
 x_113 = x_21;
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
lean::cnstr_set(x_116, 1, x_22);
return x_116;
}
}
}
}
}
obj* l_lean_parser_combinators_node___at_lean_parser_level_app_parser___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_14; 
x_7 = lean::box(0);
lean::inc(x_0);
x_9 = l_list_mfoldl___main___at_lean_parser_level_app_parser___spec__2(x_0, x_7, x_1, x_2, x_3, x_4, x_5, x_6);
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
obj* x_15; obj* x_17; obj* x_19; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_26; obj* x_27; obj* x_28; 
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
x_22 = l_list_reverse___rarg(x_15);
x_23 = l_lean_parser_syntax_mk__node(x_0, x_22);
x_24 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_24);
if (lean::is_scalar(x_21)) {
 x_26 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_26 = x_21;
}
lean::cnstr_set(x_26, 0, x_23);
lean::cnstr_set(x_26, 1, x_17);
lean::cnstr_set(x_26, 2, x_24);
x_27 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_19, x_26);
if (lean::is_scalar(x_14)) {
 x_28 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_28 = x_14;
}
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_12);
return x_28;
}
else
{
obj* x_30; uint8 x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; 
lean::dec(x_0);
x_30 = lean::cnstr_get(x_10, 0);
lean::inc(x_30);
x_32 = lean::cnstr_get_scalar<uint8>(x_10, sizeof(void*)*1);
if (lean::is_shared(x_10)) {
 lean::dec(x_10);
 x_33 = lean::box(0);
} else {
 lean::cnstr_release(x_10, 0);
 x_33 = x_10;
}
if (lean::is_scalar(x_33)) {
 x_34 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_34 = x_33;
}
lean::cnstr_set(x_34, 0, x_30);
lean::cnstr_set_scalar(x_34, sizeof(void*)*1, x_32);
x_35 = x_34;
if (lean::is_scalar(x_14)) {
 x_36 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_36 = x_14;
}
lean::cnstr_set(x_36, 0, x_35);
lean::cnstr_set(x_36, 1, x_12);
return x_36;
}
}
}
obj* _init_l_lean_parser_level_app_parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = lean::box(0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_level_app_parser_lean_parser_has__view___lambda__1), 5, 0);
x_2 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_2, 0, x_1);
lean::cnstr_set(x_2, 1, x_0);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_level_get__leading), 5, 0);
x_4 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_2);
return x_4;
}
}
obj* l_lean_parser_level_app_parser(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_9; 
x_5 = l_lean_parser_level_app;
x_6 = l_lean_parser_level_app_parser___closed__1;
lean::inc(x_6);
lean::inc(x_5);
x_9 = l_lean_parser_combinators_node___at_lean_parser_level_app_parser___spec__1(x_5, x_6, x_0, x_1, x_2, x_3, x_4);
return x_9;
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
obj* x_0; obj* x_1; obj* x_3; obj* x_4; 
x_0 = l_lean_parser_number_has__view;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::box(3);
x_4 = lean::apply_1(x_1, x_3);
return x_4;
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
obj* x_18; obj* x_20; 
x_18 = l_lean_parser_level_add__lit_has__view_x_27___lambda__1___closed__1;
lean::inc(x_18);
x_20 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_20, 0, x_1);
lean::cnstr_set(x_20, 1, x_17);
lean::cnstr_set(x_20, 2, x_18);
return x_20;
}
else
{
obj* x_21; obj* x_24; obj* x_25; obj* x_27; obj* x_28; 
x_21 = lean::cnstr_get(x_5, 0);
lean::inc(x_21);
lean::dec(x_5);
x_24 = l_lean_parser_number_has__view;
x_25 = lean::cnstr_get(x_24, 0);
lean::inc(x_25);
x_27 = lean::apply_1(x_25, x_21);
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
obj* x_30; obj* x_32; 
x_30 = l_lean_parser_level_add__lit_has__view_x_27___lambda__1___closed__1;
lean::inc(x_30);
x_32 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_32, 0, x_1);
lean::cnstr_set(x_32, 1, x_29);
lean::cnstr_set(x_32, 2, x_30);
return x_32;
}
else
{
obj* x_33; obj* x_36; obj* x_37; obj* x_39; obj* x_40; 
x_33 = lean::cnstr_get(x_5, 0);
lean::inc(x_33);
lean::dec(x_5);
x_36 = l_lean_parser_number_has__view;
x_37 = lean::cnstr_get(x_36, 0);
lean::inc(x_37);
x_39 = lean::apply_1(x_37, x_33);
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
obj* x_43; obj* x_45; 
x_43 = l_lean_parser_level_add__lit_has__view_x_27___lambda__1___closed__1;
lean::inc(x_43);
x_45 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_45, 0, x_1);
lean::cnstr_set(x_45, 1, x_42);
lean::cnstr_set(x_45, 2, x_43);
return x_45;
}
else
{
obj* x_46; obj* x_49; obj* x_50; obj* x_52; obj* x_53; 
x_46 = lean::cnstr_get(x_5, 0);
lean::inc(x_46);
lean::dec(x_5);
x_49 = l_lean_parser_number_has__view;
x_50 = lean::cnstr_get(x_49, 0);
lean::inc(x_50);
x_52 = lean::apply_1(x_50, x_46);
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
lean::inc(x_5);
return x_5;
}
else
{
obj* x_7; obj* x_10; 
x_7 = lean::cnstr_get(x_4, 0);
lean::inc(x_7);
lean::dec(x_4);
x_10 = lean::cnstr_get(x_7, 1);
lean::inc(x_10);
lean::dec(x_7);
if (lean::obj_tag(x_10) == 0)
{
obj* x_13; 
x_13 = lean::box(3);
x_1 = x_10;
x_2 = x_13;
goto lbl_3;
}
else
{
obj* x_14; obj* x_16; 
x_14 = lean::cnstr_get(x_10, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_10, 1);
lean::inc(x_16);
lean::dec(x_10);
x_1 = x_16;
x_2 = x_14;
goto lbl_3;
}
}
lbl_3:
{
obj* x_19; obj* x_20; 
if (lean::obj_tag(x_1) == 0)
{
obj* x_22; 
x_22 = lean::box(3);
x_19 = x_1;
x_20 = x_22;
goto lbl_21;
}
else
{
obj* x_23; obj* x_25; 
x_23 = lean::cnstr_get(x_1, 0);
lean::inc(x_23);
x_25 = lean::cnstr_get(x_1, 1);
lean::inc(x_25);
lean::dec(x_1);
x_19 = x_25;
x_20 = x_23;
goto lbl_21;
}
lbl_21:
{
switch (lean::obj_tag(x_20)) {
case 0:
{
obj* x_28; obj* x_31; 
x_28 = lean::cnstr_get(x_20, 0);
lean::inc(x_28);
lean::dec(x_20);
x_31 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_31, 0, x_28);
if (lean::obj_tag(x_19) == 0)
{
obj* x_32; obj* x_34; 
x_32 = l_lean_parser_level_add__lit_has__view_x_27___lambda__1___closed__1;
lean::inc(x_32);
x_34 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_34, 0, x_2);
lean::cnstr_set(x_34, 1, x_31);
lean::cnstr_set(x_34, 2, x_32);
return x_34;
}
else
{
obj* x_35; obj* x_38; obj* x_39; obj* x_41; obj* x_42; 
x_35 = lean::cnstr_get(x_19, 0);
lean::inc(x_35);
lean::dec(x_19);
x_38 = l_lean_parser_number_has__view;
x_39 = lean::cnstr_get(x_38, 0);
lean::inc(x_39);
x_41 = lean::apply_1(x_39, x_35);
x_42 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_42, 0, x_2);
lean::cnstr_set(x_42, 1, x_31);
lean::cnstr_set(x_42, 2, x_41);
return x_42;
}
}
case 3:
{
obj* x_43; 
x_43 = lean::box(0);
if (lean::obj_tag(x_19) == 0)
{
obj* x_44; obj* x_46; 
x_44 = l_lean_parser_level_add__lit_has__view_x_27___lambda__1___closed__1;
lean::inc(x_44);
x_46 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_46, 0, x_2);
lean::cnstr_set(x_46, 1, x_43);
lean::cnstr_set(x_46, 2, x_44);
return x_46;
}
else
{
obj* x_47; obj* x_50; obj* x_51; obj* x_53; obj* x_54; 
x_47 = lean::cnstr_get(x_19, 0);
lean::inc(x_47);
lean::dec(x_19);
x_50 = l_lean_parser_number_has__view;
x_51 = lean::cnstr_get(x_50, 0);
lean::inc(x_51);
x_53 = lean::apply_1(x_51, x_47);
x_54 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_54, 0, x_2);
lean::cnstr_set(x_54, 1, x_43);
lean::cnstr_set(x_54, 2, x_53);
return x_54;
}
}
default:
{
obj* x_56; 
lean::dec(x_20);
x_56 = lean::box(0);
if (lean::obj_tag(x_19) == 0)
{
obj* x_57; obj* x_59; 
x_57 = l_lean_parser_level_add__lit_has__view_x_27___lambda__1___closed__1;
lean::inc(x_57);
x_59 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_59, 0, x_2);
lean::cnstr_set(x_59, 1, x_56);
lean::cnstr_set(x_59, 2, x_57);
return x_59;
}
else
{
obj* x_60; obj* x_63; obj* x_64; obj* x_66; obj* x_67; 
x_60 = lean::cnstr_get(x_19, 0);
lean::inc(x_60);
lean::dec(x_19);
x_63 = l_lean_parser_number_has__view;
x_64 = lean::cnstr_get(x_63, 0);
lean::inc(x_64);
x_66 = lean::apply_1(x_64, x_60);
x_67 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_67, 0, x_2);
lean::cnstr_set(x_67, 1, x_56);
lean::cnstr_set(x_67, 2, x_66);
return x_67;
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
obj* x_1; obj* x_3; obj* x_5; obj* x_8; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_23; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 2);
lean::inc(x_5);
lean::dec(x_0);
x_8 = l_lean_parser_raw_view___rarg___lambda__3___closed__1;
lean::inc(x_8);
x_10 = l_option_map___rarg(x_8, x_3);
x_11 = lean::box(3);
x_12 = l_option_get__or__else___main___rarg(x_10, x_11);
x_13 = l_lean_parser_number_has__view;
x_14 = lean::cnstr_get(x_13, 1);
lean::inc(x_14);
x_16 = lean::apply_1(x_14, x_5);
x_17 = lean::box(0);
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_16);
lean::cnstr_set(x_18, 1, x_17);
x_19 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_19, 0, x_12);
lean::cnstr_set(x_19, 1, x_18);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_1);
lean::cnstr_set(x_20, 1, x_19);
x_21 = l_lean_parser_level_add__lit;
lean::inc(x_21);
x_23 = l_lean_parser_syntax_mk__node(x_21, x_20);
return x_23;
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
lean::inc(x_0);
return x_0;
}
}
obj* l_lean_parser_symbol__core___at_lean_parser_level_add__lit_parser_lean_parser_has__tokens___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_13; obj* x_14; obj* x_16; obj* x_18; obj* x_20; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_1);
lean::inc(x_6);
lean::inc(x_5);
x_13 = l_lean_parser_token(x_5, x_6, x_7);
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
lean::inc(x_0);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_20, 0, x_0);
if (lean::obj_tag(x_14) == 0)
{
obj* x_21; obj* x_23; obj* x_25; obj* x_27; obj* x_28; 
x_21 = lean::cnstr_get(x_14, 0);
lean::inc(x_21);
x_23 = lean::cnstr_get(x_14, 1);
lean::inc(x_23);
x_25 = lean::cnstr_get(x_14, 2);
lean::inc(x_25);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_27 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 lean::cnstr_release(x_14, 1);
 lean::cnstr_release(x_14, 2);
 x_27 = x_14;
}
switch (lean::obj_tag(x_21)) {
case 0:
{
obj* x_31; obj* x_33; uint8 x_36; 
lean::dec(x_18);
x_31 = lean::cnstr_get(x_21, 0);
lean::inc(x_31);
x_33 = lean::cnstr_get(x_31, 1);
lean::inc(x_33);
lean::dec(x_31);
x_36 = lean::string_dec_eq(x_0, x_33);
lean::dec(x_0);
if (x_36 == 0)
{
obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_43; obj* x_45; 
x_38 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_38, 0, x_6);
x_39 = lean::box(0);
x_40 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_33, x_2, x_38, x_39, x_5, x_23, x_16);
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
if (lean::obj_tag(x_41) == 0)
{
obj* x_46; obj* x_48; obj* x_51; obj* x_53; obj* x_54; obj* x_55; obj* x_57; obj* x_58; obj* x_59; obj* x_60; 
x_46 = lean::cnstr_get(x_41, 1);
lean::inc(x_46);
x_48 = lean::cnstr_get(x_41, 2);
lean::inc(x_48);
lean::dec(x_41);
x_51 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_51);
if (lean::is_scalar(x_27)) {
 x_53 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_53 = x_27;
}
lean::cnstr_set(x_53, 0, x_21);
lean::cnstr_set(x_53, 1, x_46);
lean::cnstr_set(x_53, 2, x_51);
x_54 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_48, x_53);
x_55 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_25, x_54);
lean::inc(x_51);
x_57 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_51, x_55);
x_58 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_57, x_20);
x_59 = l_lean_parser_parsec__t_try__mk__res___rarg(x_58);
if (lean::is_scalar(x_45)) {
 x_60 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_60 = x_45;
}
lean::cnstr_set(x_60, 0, x_59);
lean::cnstr_set(x_60, 1, x_43);
return x_60;
}
else
{
obj* x_63; uint8 x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_72; obj* x_73; obj* x_74; obj* x_75; 
lean::dec(x_27);
lean::dec(x_21);
x_63 = lean::cnstr_get(x_41, 0);
lean::inc(x_63);
x_65 = lean::cnstr_get_scalar<uint8>(x_41, sizeof(void*)*1);
if (lean::is_shared(x_41)) {
 lean::dec(x_41);
 x_66 = lean::box(0);
} else {
 lean::cnstr_release(x_41, 0);
 x_66 = x_41;
}
if (lean::is_scalar(x_66)) {
 x_67 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_67 = x_66;
}
lean::cnstr_set(x_67, 0, x_63);
lean::cnstr_set_scalar(x_67, sizeof(void*)*1, x_65);
x_68 = x_67;
x_69 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_25, x_68);
x_70 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_70);
x_72 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_70, x_69);
x_73 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_72, x_20);
x_74 = l_lean_parser_parsec__t_try__mk__res___rarg(x_73);
if (lean::is_scalar(x_45)) {
 x_75 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_75 = x_45;
}
lean::cnstr_set(x_75, 0, x_74);
lean::cnstr_set(x_75, 1, x_43);
return x_75;
}
}
else
{
obj* x_80; obj* x_82; obj* x_83; obj* x_84; obj* x_86; obj* x_87; obj* x_88; obj* x_89; 
lean::dec(x_5);
lean::dec(x_6);
lean::dec(x_2);
lean::dec(x_33);
x_80 = l_lean_parser_finish__comment__block___closed__2;
lean::inc(x_80);
if (lean::is_scalar(x_27)) {
 x_82 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_82 = x_27;
}
lean::cnstr_set(x_82, 0, x_21);
lean::cnstr_set(x_82, 1, x_23);
lean::cnstr_set(x_82, 2, x_80);
x_83 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_25, x_82);
x_84 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_84);
x_86 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_84, x_83);
x_87 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_86, x_20);
x_88 = l_lean_parser_parsec__t_try__mk__res___rarg(x_87);
x_89 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_89, 0, x_88);
lean::cnstr_set(x_89, 1, x_16);
return x_89;
}
}
case 3:
{
obj* x_92; 
lean::dec(x_27);
lean::dec(x_0);
x_92 = lean::box(0);
x_28 = x_92;
goto lbl_29;
}
default:
{
obj* x_96; 
lean::dec(x_27);
lean::dec(x_0);
lean::dec(x_21);
x_96 = lean::box(0);
x_28 = x_96;
goto lbl_29;
}
}
lbl_29:
{
obj* x_98; obj* x_99; obj* x_100; obj* x_102; obj* x_103; obj* x_105; obj* x_108; obj* x_109; obj* x_111; obj* x_112; obj* x_113; obj* x_114; 
lean::dec(x_28);
x_98 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_98, 0, x_6);
x_99 = lean::box(0);
x_100 = l_string_join___closed__1;
lean::inc(x_100);
x_102 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_100, x_2, x_98, x_99, x_5, x_23, x_16);
x_103 = lean::cnstr_get(x_102, 0);
lean::inc(x_103);
x_105 = lean::cnstr_get(x_102, 1);
lean::inc(x_105);
lean::dec(x_102);
x_108 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_25, x_103);
x_109 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_109);
x_111 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_109, x_108);
x_112 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_111, x_20);
x_113 = l_lean_parser_parsec__t_try__mk__res___rarg(x_112);
if (lean::is_scalar(x_18)) {
 x_114 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_114 = x_18;
}
lean::cnstr_set(x_114, 0, x_113);
lean::cnstr_set(x_114, 1, x_105);
return x_114;
}
}
else
{
obj* x_119; uint8 x_121; obj* x_122; obj* x_123; obj* x_124; obj* x_125; obj* x_127; obj* x_128; obj* x_129; obj* x_130; 
lean::dec(x_5);
lean::dec(x_6);
lean::dec(x_0);
lean::dec(x_2);
x_119 = lean::cnstr_get(x_14, 0);
lean::inc(x_119);
x_121 = lean::cnstr_get_scalar<uint8>(x_14, sizeof(void*)*1);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_122 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 x_122 = x_14;
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
lean::inc(x_125);
x_127 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_125, x_124);
x_128 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_127, x_20);
x_129 = l_lean_parser_parsec__t_try__mk__res___rarg(x_128);
if (lean::is_scalar(x_18)) {
 x_130 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_130 = x_18;
}
lean::cnstr_set(x_130, 0, x_129);
lean::cnstr_set(x_130, 1, x_16);
return x_130;
}
}
}
obj* l_lean_parser_number_parser___at_lean_parser_level_add__lit_parser_lean_parser_has__tokens___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2) {
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
obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_19; 
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
lean::inc(x_11);
x_19 = l_lean_parser_try__view___at_lean_parser_number_parser___spec__1(x_11);
if (lean::obj_tag(x_19) == 0)
{
obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_28; obj* x_29; obj* x_31; obj* x_34; obj* x_36; obj* x_37; obj* x_39; obj* x_41; obj* x_42; obj* x_43; 
lean::dec(x_17);
lean::dec(x_11);
x_22 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_22, 0, x_1);
x_23 = lean::box(0);
x_24 = l_string_join___closed__1;
x_25 = l_lean_parser_number_parser___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__2___rarg___closed__1;
lean::inc(x_25);
lean::inc(x_24);
x_28 = l_lean_parser_monad__parsec_error___at___private_init_lean_parser_token_1__finish__comment__block__aux___main___spec__1___rarg(x_24, x_25, x_22, x_23, x_0, x_13, x_8);
x_29 = lean::cnstr_get(x_28, 0);
lean::inc(x_29);
x_31 = lean::cnstr_get(x_28, 1);
lean::inc(x_31);
lean::dec(x_28);
x_34 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_34);
x_36 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_34, x_29);
x_37 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_36);
lean::inc(x_34);
x_39 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_34, x_37);
lean::inc(x_25);
x_41 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_39, x_25);
x_42 = l_lean_parser_parsec__t_try__mk__res___rarg(x_41);
if (lean::is_scalar(x_10)) {
 x_43 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_43 = x_10;
}
lean::cnstr_set(x_43, 0, x_42);
lean::cnstr_set(x_43, 1, x_31);
return x_43;
}
else
{
obj* x_47; obj* x_49; obj* x_50; obj* x_51; obj* x_53; obj* x_54; obj* x_56; obj* x_57; obj* x_58; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_19);
x_47 = l_lean_parser_finish__comment__block___closed__2;
lean::inc(x_47);
if (lean::is_scalar(x_17)) {
 x_49 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_49 = x_17;
}
lean::cnstr_set(x_49, 0, x_11);
lean::cnstr_set(x_49, 1, x_13);
lean::cnstr_set(x_49, 2, x_47);
x_50 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_49);
x_51 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_51);
x_53 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_51, x_50);
x_54 = l_lean_parser_number_parser___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__2___rarg___closed__1;
lean::inc(x_54);
x_56 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_53, x_54);
x_57 = l_lean_parser_parsec__t_try__mk__res___rarg(x_56);
if (lean::is_scalar(x_10)) {
 x_58 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_58 = x_10;
}
lean::cnstr_set(x_58, 0, x_57);
lean::cnstr_set(x_58, 1, x_8);
return x_58;
}
}
else
{
obj* x_61; uint8 x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_69; obj* x_70; obj* x_72; obj* x_73; obj* x_74; 
lean::dec(x_1);
lean::dec(x_0);
x_61 = lean::cnstr_get(x_6, 0);
lean::inc(x_61);
x_63 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*1);
if (lean::is_shared(x_6)) {
 lean::dec(x_6);
 x_64 = lean::box(0);
} else {
 lean::cnstr_release(x_6, 0);
 x_64 = x_6;
}
if (lean::is_scalar(x_64)) {
 x_65 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_65 = x_64;
}
lean::cnstr_set(x_65, 0, x_61);
lean::cnstr_set_scalar(x_65, sizeof(void*)*1, x_63);
x_66 = x_65;
x_67 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_67);
x_69 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_67, x_66);
x_70 = l_lean_parser_number_parser___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__2___rarg___closed__1;
lean::inc(x_70);
x_72 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_69, x_70);
x_73 = l_lean_parser_parsec__t_try__mk__res___rarg(x_72);
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
obj* l_lean_parser_number_parser___at_lean_parser_level_add__lit_parser_lean_parser_has__tokens___spec__2(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_number_parser___at_lean_parser_level_add__lit_parser_lean_parser_has__tokens___spec__2___rarg), 3, 0);
return x_4;
}
}
obj* _init_l_lean_parser_level_add__lit_parser_lean_parser_has__tokens() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_8; obj* x_9; 
x_0 = lean::mk_string("+");
x_1 = lean::mk_nat_obj(0u);
x_2 = l_lean_parser_symbol_tokens___rarg(x_0, x_1);
x_3 = lean::box(0);
x_4 = l_lean_parser_list_cons_tokens___rarg(x_3, x_3);
x_5 = l_lean_parser_list_cons_tokens___rarg(x_2, x_4);
x_6 = l_lean_parser_level_lean_parser_has__tokens;
lean::inc(x_6);
x_8 = l_lean_parser_list_cons_tokens___rarg(x_6, x_5);
x_9 = l_lean_parser_tokens___rarg(x_8);
return x_9;
}
}
obj* _init_l_lean_parser_level_add__lit_parser_lean_parser_has__view() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_24; 
x_0 = lean::mk_string("+");
x_1 = l_string_trim(x_0);
lean::inc(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_3, 0, x_1);
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_level_add__lit_parser_lean_parser_has__tokens___spec__1), 8, 3);
lean::closure_set(x_5, 0, x_1);
lean::closure_set(x_5, 1, x_4);
lean::closure_set(x_5, 2, x_3);
x_6 = lean::box(0);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_number_parser___at_lean_parser_level_add__lit_parser_lean_parser_has__tokens___spec__2), 2, 0);
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_6);
x_9 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_9, 0, x_5);
lean::cnstr_set(x_9, 1, x_8);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_level_get__leading), 5, 0);
x_11 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_9);
x_12 = l_lean_parser_trailing__level__parser__m_monad;
x_13 = l_lean_parser_trailing__level__parser__m_monad__except;
x_14 = l_lean_parser_trailing__level__parser__m_lean_parser_monad__parsec;
x_15 = l_lean_parser_trailing__level__parser__m_alternative;
x_16 = l_lean_parser_level_add__lit;
x_17 = l_lean_parser_level_add__lit_has__view;
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
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_level_add__lit_parser_lean_parser_has__tokens___spec__1), 8, 3);
lean::closure_set(x_5, 0, x_1);
lean::closure_set(x_5, 1, x_4);
lean::closure_set(x_5, 2, x_3);
x_6 = lean::box(0);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_number_parser___at_lean_parser_level_add__lit_parser_lean_parser_has__tokens___spec__2), 2, 0);
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_6);
x_9 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_9, 0, x_5);
lean::cnstr_set(x_9, 1, x_8);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_level_get__leading), 5, 0);
x_11 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_9);
return x_11;
}
}
obj* l_lean_parser_level_add__lit_parser(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_9; 
x_5 = l_lean_parser_level_add__lit;
x_6 = l_lean_parser_level_add__lit_parser___closed__1;
lean::inc(x_6);
lean::inc(x_5);
x_9 = l_lean_parser_combinators_node___at_lean_parser_level_app_parser___spec__1(x_5, x_6, x_0, x_1, x_2, x_3, x_4);
return x_9;
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
obj* x_8; obj* x_9; obj* x_11; obj* x_12; 
x_8 = l_lean_parser_level_add__lit_has__view;
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
x_11 = lean::apply_1(x_9, x_0);
x_12 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_12, 0, x_11);
return x_12;
}
else
{
obj* x_13; obj* x_14; obj* x_16; obj* x_17; 
x_13 = l_lean_parser_level_app_has__view;
x_14 = lean::cnstr_get(x_13, 0);
lean::inc(x_14);
x_16 = lean::apply_1(x_14, x_0);
x_17 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_17, 0, x_16);
return x_17;
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
lean::inc(x_5);
return x_5;
}
else
{
obj* x_7; obj* x_10; obj* x_12; obj* x_15; uint8 x_16; 
x_7 = lean::cnstr_get(x_4, 0);
lean::inc(x_7);
lean::dec(x_4);
x_10 = lean::cnstr_get(x_7, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_7, 1);
lean::inc(x_12);
lean::dec(x_7);
x_15 = l_lean_parser_level_trailing_has__view_x_27___lambda__1___closed__2;
x_16 = lean_name_dec_eq(x_10, x_15);
lean::dec(x_10);
if (x_16 == 0)
{
obj* x_19; 
lean::dec(x_12);
x_19 = l_lean_parser_level_trailing_has__view_x_27___lambda__1___closed__1;
lean::inc(x_19);
return x_19;
}
else
{
if (lean::obj_tag(x_12) == 0)
{
obj* x_21; 
x_21 = l_lean_parser_level_trailing_has__view_x_27___lambda__1___closed__1;
lean::inc(x_21);
return x_21;
}
else
{
obj* x_23; obj* x_25; 
x_23 = lean::cnstr_get(x_12, 0);
lean::inc(x_23);
x_25 = lean::cnstr_get(x_12, 1);
lean::inc(x_25);
lean::dec(x_12);
if (lean::obj_tag(x_25) == 0)
{
obj* x_28; 
x_28 = l_lean_parser_syntax_as__node___main(x_23);
if (lean::obj_tag(x_28) == 0)
{
obj* x_29; 
x_29 = l_lean_parser_level_trailing_has__view_x_27___lambda__1___closed__1;
lean::inc(x_29);
return x_29;
}
else
{
obj* x_31; obj* x_34; obj* x_36; 
x_31 = lean::cnstr_get(x_28, 0);
lean::inc(x_31);
lean::dec(x_28);
x_34 = lean::cnstr_get(x_31, 0);
lean::inc(x_34);
x_36 = lean::cnstr_get(x_31, 1);
lean::inc(x_36);
lean::dec(x_31);
switch (lean::obj_tag(x_34)) {
case 0:
{
obj* x_40; 
lean::dec(x_36);
x_40 = l_lean_parser_level_trailing_has__view_x_27___lambda__1___closed__1;
lean::inc(x_40);
return x_40;
}
case 1:
{
obj* x_44; 
lean::dec(x_36);
lean::dec(x_34);
x_44 = l_lean_parser_level_trailing_has__view_x_27___lambda__1___closed__1;
lean::inc(x_44);
return x_44;
}
default:
{
obj* x_46; obj* x_48; obj* x_51; uint8 x_52; 
x_46 = lean::cnstr_get(x_34, 0);
lean::inc(x_46);
x_48 = lean::cnstr_get(x_34, 1);
lean::inc(x_48);
lean::dec(x_34);
x_51 = lean::box(0);
x_52 = lean_name_dec_eq(x_46, x_51);
lean::dec(x_46);
if (x_52 == 0)
{
obj* x_56; 
lean::dec(x_36);
lean::dec(x_48);
x_56 = l_lean_parser_level_trailing_has__view_x_27___lambda__1___closed__1;
lean::inc(x_56);
return x_56;
}
else
{
if (lean::obj_tag(x_36) == 0)
{
obj* x_59; 
lean::dec(x_48);
x_59 = l_lean_parser_level_trailing_has__view_x_27___lambda__1___closed__1;
lean::inc(x_59);
return x_59;
}
else
{
obj* x_61; obj* x_63; 
x_61 = lean::cnstr_get(x_36, 0);
lean::inc(x_61);
x_63 = lean::cnstr_get(x_36, 1);
lean::inc(x_63);
lean::dec(x_36);
if (lean::obj_tag(x_63) == 0)
{
x_1 = x_61;
x_2 = x_48;
goto lbl_3;
}
else
{
obj* x_69; 
lean::dec(x_61);
lean::dec(x_63);
lean::dec(x_48);
x_69 = l_lean_parser_level_trailing_has__view_x_27___lambda__1___closed__1;
lean::inc(x_69);
return x_69;
}
}
}
}
}
}
}
else
{
obj* x_73; 
lean::dec(x_23);
lean::dec(x_25);
x_73 = l_lean_parser_level_trailing_has__view_x_27___lambda__1___closed__1;
lean::inc(x_73);
return x_73;
}
}
}
}
lbl_3:
{
obj* x_75; uint8 x_76; 
x_75 = lean::mk_nat_obj(0u);
x_76 = lean::nat_dec_eq(x_2, x_75);
lean::dec(x_2);
if (x_76 == 0)
{
obj* x_78; obj* x_79; obj* x_81; obj* x_82; 
x_78 = l_lean_parser_level_add__lit_has__view;
x_79 = lean::cnstr_get(x_78, 0);
lean::inc(x_79);
x_81 = lean::apply_1(x_79, x_1);
x_82 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_82, 0, x_81);
return x_82;
}
else
{
obj* x_83; obj* x_84; obj* x_86; obj* x_87; 
x_83 = l_lean_parser_level_app_has__view;
x_84 = lean::cnstr_get(x_83, 0);
lean::inc(x_84);
x_86 = lean::apply_1(x_84, x_1);
x_87 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_87, 0, x_86);
return x_87;
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
obj* x_2; obj* x_5; obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_12; obj* x_13; obj* x_14; obj* x_16; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
x_5 = l_lean_parser_level_app_has__view;
x_6 = lean::cnstr_get(x_5, 1);
lean::inc(x_6);
x_8 = lean::apply_1(x_6, x_2);
x_9 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_1);
x_10 = l_lean_parser_detail__ident__part_has__view_x_27___lambda__2___closed__1;
lean::inc(x_10);
x_12 = l_lean_parser_syntax_mk__node(x_10, x_9);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_1);
x_14 = l_lean_parser_level_trailing;
lean::inc(x_14);
x_16 = l_lean_parser_syntax_mk__node(x_14, x_13);
return x_16;
}
else
{
obj* x_17; obj* x_20; obj* x_21; obj* x_23; obj* x_24; obj* x_25; obj* x_27; obj* x_28; obj* x_29; obj* x_31; 
x_17 = lean::cnstr_get(x_0, 0);
lean::inc(x_17);
lean::dec(x_0);
x_20 = l_lean_parser_level_add__lit_has__view;
x_21 = lean::cnstr_get(x_20, 1);
lean::inc(x_21);
x_23 = lean::apply_1(x_21, x_17);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_1);
x_25 = l_lean_parser_detail__ident__part_has__view_x_27___lambda__2___closed__2;
lean::inc(x_25);
x_27 = l_lean_parser_syntax_mk__node(x_25, x_24);
x_28 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_1);
x_29 = l_lean_parser_level_trailing;
lean::inc(x_29);
x_31 = l_lean_parser_syntax_mk__node(x_29, x_28);
return x_31;
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
lean::inc(x_0);
return x_0;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_level_trailing_parser_lean_parser_has__tokens___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
obj* x_12; obj* x_13; uint8 x_14; obj* x_15; obj* x_16; obj* x_17; 
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_4);
x_12 = l_option_get__or__else___main___rarg(x_2, x_7);
x_13 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_0);
lean::cnstr_set(x_13, 2, x_1);
lean::cnstr_set(x_13, 3, x_3);
x_14 = 0;
x_15 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_15, 0, x_13);
lean::cnstr_set_scalar(x_15, sizeof(void*)*1, x_14);
x_16 = x_15;
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_8);
return x_17;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_level_trailing_parser_lean_parser_has__tokens___spec__2(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___at_lean_parser_level_trailing_parser_lean_parser_has__tokens___spec__2___rarg), 9, 0);
return x_2;
}
}
obj* l_lean_parser_combinators_choice__aux___main___at_lean_parser_level_trailing_parser_lean_parser_has__tokens___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_13; 
lean::dec(x_1);
x_8 = lean::box(0);
x_9 = l_lean_parser_combinators_choice__aux___main___rarg___closed__1;
x_10 = l_mjoin___rarg___closed__1;
lean::inc(x_10);
lean::inc(x_9);
x_13 = l_lean_parser_monad__parsec_error___at_lean_parser_level_trailing_parser_lean_parser_has__tokens___spec__2___rarg(x_9, x_10, x_8, x_8, x_2, x_3, x_4, x_5, x_6);
return x_13;
}
else
{
obj* x_14; obj* x_16; obj* x_18; obj* x_23; obj* x_24; obj* x_26; obj* x_28; obj* x_29; obj* x_30; 
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
lean::inc(x_5);
lean::inc(x_4);
lean::inc(x_3);
lean::inc(x_2);
x_23 = lean::apply_5(x_14, x_2, x_3, x_4, x_5, x_6);
x_24 = lean::cnstr_get(x_23, 0);
lean::inc(x_24);
x_26 = lean::cnstr_get(x_23, 1);
lean::inc(x_26);
if (lean::is_shared(x_23)) {
 lean::dec(x_23);
 x_28 = lean::box(0);
} else {
 lean::cnstr_release(x_23, 0);
 lean::cnstr_release(x_23, 1);
 x_28 = x_23;
}
x_29 = lean::mk_nat_obj(1u);
x_30 = lean::nat_add(x_1, x_29);
if (lean::obj_tag(x_24) == 0)
{
obj* x_31; obj* x_33; obj* x_35; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_44; obj* x_45; 
x_31 = lean::cnstr_get(x_24, 0);
lean::inc(x_31);
x_33 = lean::cnstr_get(x_24, 1);
lean::inc(x_33);
x_35 = lean::cnstr_get(x_24, 2);
lean::inc(x_35);
if (lean::is_shared(x_24)) {
 lean::dec(x_24);
 x_37 = lean::box(0);
} else {
 lean::cnstr_release(x_24, 0);
 lean::cnstr_release(x_24, 1);
 lean::cnstr_release(x_24, 2);
 x_37 = x_24;
}
x_38 = lean::box(0);
x_39 = lean_name_mk_numeral(x_38, x_1);
if (lean::is_scalar(x_18)) {
 x_40 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_40 = x_18;
}
lean::cnstr_set(x_40, 0, x_31);
lean::cnstr_set(x_40, 1, x_38);
x_41 = l_lean_parser_syntax_mk__node(x_39, x_40);
x_42 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_42);
if (lean::is_scalar(x_37)) {
 x_44 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_44 = x_37;
}
lean::cnstr_set(x_44, 0, x_41);
lean::cnstr_set(x_44, 1, x_33);
lean::cnstr_set(x_44, 2, x_42);
x_45 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_35, x_44);
if (lean::obj_tag(x_45) == 0)
{
obj* x_52; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_30);
lean::dec(x_16);
if (lean::is_scalar(x_28)) {
 x_52 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_52 = x_28;
}
lean::cnstr_set(x_52, 0, x_45);
lean::cnstr_set(x_52, 1, x_26);
return x_52;
}
else
{
obj* x_53; uint8 x_55; 
x_53 = lean::cnstr_get(x_45, 0);
lean::inc(x_53);
x_55 = lean::cnstr_get_scalar<uint8>(x_45, sizeof(void*)*1);
if (x_55 == 0)
{
obj* x_57; obj* x_58; obj* x_60; obj* x_63; obj* x_64; 
lean::dec(x_45);
x_57 = l_lean_parser_combinators_choice__aux___main___at_lean_parser_level_trailing_parser_lean_parser_has__tokens___spec__1(x_16, x_30, x_2, x_3, x_4, x_5, x_26);
x_58 = lean::cnstr_get(x_57, 0);
lean::inc(x_58);
x_60 = lean::cnstr_get(x_57, 1);
lean::inc(x_60);
lean::dec(x_57);
x_63 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_53, x_58);
if (lean::is_scalar(x_28)) {
 x_64 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_64 = x_28;
}
lean::cnstr_set(x_64, 0, x_63);
lean::cnstr_set(x_64, 1, x_60);
return x_64;
}
else
{
obj* x_72; 
lean::dec(x_5);
lean::dec(x_53);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_30);
lean::dec(x_16);
if (lean::is_scalar(x_28)) {
 x_72 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_72 = x_28;
}
lean::cnstr_set(x_72, 0, x_45);
lean::cnstr_set(x_72, 1, x_26);
return x_72;
}
}
}
else
{
obj* x_75; uint8 x_77; obj* x_78; 
lean::dec(x_1);
lean::dec(x_18);
x_75 = lean::cnstr_get(x_24, 0);
lean::inc(x_75);
x_77 = lean::cnstr_get_scalar<uint8>(x_24, sizeof(void*)*1);
if (lean::is_shared(x_24)) {
 lean::dec(x_24);
 x_78 = lean::box(0);
} else {
 lean::cnstr_release(x_24, 0);
 x_78 = x_24;
}
if (x_77 == 0)
{
obj* x_80; obj* x_81; obj* x_83; obj* x_86; obj* x_87; 
lean::dec(x_78);
x_80 = l_lean_parser_combinators_choice__aux___main___at_lean_parser_level_trailing_parser_lean_parser_has__tokens___spec__1(x_16, x_30, x_2, x_3, x_4, x_5, x_26);
x_81 = lean::cnstr_get(x_80, 0);
lean::inc(x_81);
x_83 = lean::cnstr_get(x_80, 1);
lean::inc(x_83);
lean::dec(x_80);
x_86 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_75, x_81);
if (lean::is_scalar(x_28)) {
 x_87 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_87 = x_28;
}
lean::cnstr_set(x_87, 0, x_86);
lean::cnstr_set(x_87, 1, x_83);
return x_87;
}
else
{
obj* x_94; obj* x_95; obj* x_96; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_30);
lean::dec(x_16);
if (lean::is_scalar(x_78)) {
 x_94 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_94 = x_78;
}
lean::cnstr_set(x_94, 0, x_75);
lean::cnstr_set_scalar(x_94, sizeof(void*)*1, x_77);
x_95 = x_94;
if (lean::is_scalar(x_28)) {
 x_96 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_96 = x_28;
}
lean::cnstr_set(x_96, 0, x_95);
lean::cnstr_set(x_96, 1, x_26);
return x_96;
}
}
}
}
}
obj* _init_l_lean_parser_level_trailing_parser_lean_parser_has__tokens() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_0 = lean::box(0);
x_1 = l_lean_parser_level_add__lit_parser_lean_parser_has__tokens;
lean::inc(x_1);
x_3 = l_lean_parser_list_cons_tokens___rarg(x_1, x_0);
x_4 = l_lean_parser_level_app_parser_lean_parser_has__tokens;
lean::inc(x_4);
x_6 = l_lean_parser_list_cons_tokens___rarg(x_4, x_3);
x_7 = l_lean_parser_tokens___rarg(x_6);
x_8 = l_lean_parser_list_cons_tokens___rarg(x_7, x_0);
x_9 = l_lean_parser_tokens___rarg(x_8);
return x_9;
}
}
obj* _init_l_lean_parser_level_trailing_parser_lean_parser_has__view() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_20; 
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
obj* x_5; obj* x_6; obj* x_9; 
x_5 = l_lean_parser_level_trailing;
x_6 = l_lean_parser_level_trailing_parser___closed__1;
lean::inc(x_6);
lean::inc(x_5);
x_9 = l_lean_parser_combinators_node___at_lean_parser_level_app_parser___spec__1(x_5, x_6, x_0, x_1, x_2, x_3, x_4);
return x_9;
}
}
obj* l_lean_parser_level__parser_run_lean_parser_has__tokens(obj* x_0) {
_start:
{
obj* x_2; obj* x_3; obj* x_6; 
lean::dec(x_0);
x_2 = l_lean_parser_level_leading_parser_lean_parser_has__tokens;
x_3 = l_lean_parser_level_trailing_parser_lean_parser_has__tokens;
lean::inc(x_3);
lean::inc(x_2);
x_6 = l_list_append___rarg(x_2, x_3);
return x_6;
}
}
obj* _init_l_lean_parser_level__parser_run_lean_parser_has__view___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_has__monad__lift__t__refl), 2, 1);
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
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_17; 
x_1 = l_lean_parser_basic__parser__m_monad;
x_2 = l_lean_parser_level__parser_run_lean_parser_has__view___closed__1;
x_3 = l_lean_parser_basic__parser__m_lean_parser_monad__parsec;
x_4 = l_lean_parser_basic__parser__m_monad__reader;
x_5 = l_lean_parser_basic__parser__m_monad__except;
x_6 = l_lean_parser_basic__parser__m_alternative;
x_7 = l_lean_parser_level__parser_run_lean_parser_has__view___closed__2;
x_8 = l_lean_parser_level__parser_run_lean_parser_has__view___closed__3;
lean::inc(x_8);
lean::inc(x_7);
lean::inc(x_6);
lean::inc(x_5);
lean::inc(x_4);
lean::inc(x_3);
lean::inc(x_2);
lean::inc(x_1);
x_17 = l_lean_parser_pratt__parser_view___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_0);
return x_17;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_level__parser_run___spec__3___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
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
obj* l_lean_parser_monad__parsec_error___at_lean_parser_level__parser_run___spec__3(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___at_lean_parser_level__parser_run___spec__3___rarg), 8, 0);
return x_2;
}
}
obj* l_lean_parser_curr__lbp___at_lean_parser_level__parser_run___spec__4(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; obj* x_6; obj* x_8; obj* x_10; 
lean::inc(x_1);
x_5 = l_lean_parser_monad__parsec_observing___at_lean_parser_peek__token___spec__2(x_1, x_2, x_3);
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
obj* x_21; obj* x_22; obj* x_24; obj* x_25; obj* x_26; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_11);
x_21 = lean::mk_nat_obj(0u);
x_22 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_22);
if (lean::is_scalar(x_17)) {
 x_24 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_24 = x_17;
}
lean::cnstr_set(x_24, 0, x_21);
lean::cnstr_set(x_24, 1, x_13);
lean::cnstr_set(x_24, 2, x_22);
x_25 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_24);
if (lean::is_scalar(x_10)) {
 x_26 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_26 = x_10;
}
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_8);
return x_26;
}
else
{
obj* x_27; 
x_27 = lean::cnstr_get(x_11, 0);
lean::inc(x_27);
lean::dec(x_11);
switch (lean::obj_tag(x_27)) {
case 0:
{
obj* x_30; obj* x_33; obj* x_36; obj* x_38; obj* x_39; 
x_30 = lean::cnstr_get(x_27, 0);
lean::inc(x_30);
lean::dec(x_27);
x_33 = lean::cnstr_get(x_30, 1);
lean::inc(x_33);
lean::dec(x_30);
x_36 = lean::cnstr_get(x_1, 1);
lean::inc(x_36);
x_38 = lean::string_mk_iterator(x_33);
x_39 = l_lean_parser_trie_match__prefix___rarg(x_36, x_38);
if (lean::obj_tag(x_39) == 0)
{
obj* x_41; obj* x_42; obj* x_43; obj* x_46; obj* x_47; obj* x_49; obj* x_52; obj* x_54; obj* x_56; obj* x_57; obj* x_58; 
lean::dec(x_17);
x_41 = lean::box(0);
x_42 = l_lean_parser_curr__lbp___rarg___lambda__1___closed__1;
x_43 = l_mjoin___rarg___closed__1;
lean::inc(x_43);
lean::inc(x_42);
x_46 = l_lean_parser_monad__parsec_error___at_lean_parser_level__parser_run___spec__3___rarg(x_42, x_43, x_41, x_41, x_0, x_1, x_13, x_8);
x_47 = lean::cnstr_get(x_46, 0);
lean::inc(x_47);
x_49 = lean::cnstr_get(x_46, 1);
lean::inc(x_49);
lean::dec(x_46);
x_52 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_52);
x_54 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_52, x_47);
lean::inc(x_52);
x_56 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_52, x_54);
x_57 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_56);
if (lean::is_scalar(x_10)) {
 x_58 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_58 = x_10;
}
lean::cnstr_set(x_58, 0, x_57);
lean::cnstr_set(x_58, 1, x_49);
return x_58;
}
else
{
obj* x_61; obj* x_64; obj* x_67; obj* x_70; obj* x_72; obj* x_73; obj* x_74; 
lean::dec(x_1);
lean::dec(x_0);
x_61 = lean::cnstr_get(x_39, 0);
lean::inc(x_61);
lean::dec(x_39);
x_64 = lean::cnstr_get(x_61, 1);
lean::inc(x_64);
lean::dec(x_61);
x_67 = lean::cnstr_get(x_64, 1);
lean::inc(x_67);
lean::dec(x_64);
x_70 = l_lean_parser_match__token___closed__2;
lean::inc(x_70);
if (lean::is_scalar(x_17)) {
 x_72 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_72 = x_17;
}
lean::cnstr_set(x_72, 0, x_67);
lean::cnstr_set(x_72, 1, x_13);
lean::cnstr_set(x_72, 2, x_70);
x_73 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_72);
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
case 1:
{
obj* x_78; obj* x_79; obj* x_82; obj* x_83; obj* x_84; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_27);
x_78 = l_lean_parser_max__prec;
x_79 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_79);
lean::inc(x_78);
if (lean::is_scalar(x_17)) {
 x_82 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_82 = x_17;
}
lean::cnstr_set(x_82, 0, x_78);
lean::cnstr_set(x_82, 1, x_13);
lean::cnstr_set(x_82, 2, x_79);
x_83 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_82);
if (lean::is_scalar(x_10)) {
 x_84 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_84 = x_10;
}
lean::cnstr_set(x_84, 0, x_83);
lean::cnstr_set(x_84, 1, x_8);
return x_84;
}
case 2:
{
obj* x_85; obj* x_88; obj* x_91; uint8 x_92; 
x_85 = lean::cnstr_get(x_27, 0);
lean::inc(x_85);
lean::dec(x_27);
x_88 = lean::cnstr_get(x_85, 0);
lean::inc(x_88);
lean::dec(x_85);
x_91 = l_lean_parser_number_has__view_x_27___lambda__1___closed__6;
x_92 = lean_name_dec_eq(x_88, x_91);
if (x_92 == 0)
{
obj* x_93; uint8 x_94; 
x_93 = l_lean_parser_curr__lbp___rarg___lambda__3___closed__1;
x_94 = lean_name_dec_eq(x_88, x_93);
lean::dec(x_88);
if (x_94 == 0)
{
obj* x_97; obj* x_98; obj* x_99; obj* x_102; obj* x_103; obj* x_105; obj* x_108; obj* x_109; 
lean::dec(x_17);
x_97 = lean::box(0);
x_98 = l_lean_parser_curr__lbp___rarg___lambda__3___closed__2;
x_99 = l_mjoin___rarg___closed__1;
lean::inc(x_99);
lean::inc(x_98);
x_102 = l_lean_parser_monad__parsec_error___at_lean_parser_level__parser_run___spec__3___rarg(x_98, x_99, x_97, x_97, x_0, x_1, x_13, x_8);
x_103 = lean::cnstr_get(x_102, 0);
lean::inc(x_103);
x_105 = lean::cnstr_get(x_102, 1);
lean::inc(x_105);
lean::dec(x_102);
x_108 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_103);
if (lean::is_scalar(x_10)) {
 x_109 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_109 = x_10;
}
lean::cnstr_set(x_109, 0, x_108);
lean::cnstr_set(x_109, 1, x_105);
return x_109;
}
else
{
obj* x_112; obj* x_113; obj* x_116; obj* x_117; obj* x_118; 
lean::dec(x_1);
lean::dec(x_0);
x_112 = l_lean_parser_max__prec;
x_113 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_113);
lean::inc(x_112);
if (lean::is_scalar(x_17)) {
 x_116 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_116 = x_17;
}
lean::cnstr_set(x_116, 0, x_112);
lean::cnstr_set(x_116, 1, x_13);
lean::cnstr_set(x_116, 2, x_113);
x_117 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_116);
if (lean::is_scalar(x_10)) {
 x_118 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_118 = x_10;
}
lean::cnstr_set(x_118, 0, x_117);
lean::cnstr_set(x_118, 1, x_8);
return x_118;
}
}
else
{
obj* x_122; obj* x_123; obj* x_126; obj* x_127; obj* x_128; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_88);
x_122 = l_lean_parser_max__prec;
x_123 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_123);
lean::inc(x_122);
if (lean::is_scalar(x_17)) {
 x_126 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_126 = x_17;
}
lean::cnstr_set(x_126, 0, x_122);
lean::cnstr_set(x_126, 1, x_13);
lean::cnstr_set(x_126, 2, x_123);
x_127 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_126);
if (lean::is_scalar(x_10)) {
 x_128 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_128 = x_10;
}
lean::cnstr_set(x_128, 0, x_127);
lean::cnstr_set(x_128, 1, x_8);
return x_128;
}
}
default:
{
obj* x_130; obj* x_131; obj* x_132; obj* x_135; obj* x_136; obj* x_138; obj* x_141; obj* x_142; 
lean::dec(x_17);
x_130 = lean::box(0);
x_131 = l_lean_parser_curr__lbp___rarg___lambda__3___closed__2;
x_132 = l_mjoin___rarg___closed__1;
lean::inc(x_132);
lean::inc(x_131);
x_135 = l_lean_parser_monad__parsec_error___at_lean_parser_level__parser_run___spec__3___rarg(x_131, x_132, x_130, x_130, x_0, x_1, x_13, x_8);
x_136 = lean::cnstr_get(x_135, 0);
lean::inc(x_136);
x_138 = lean::cnstr_get(x_135, 1);
lean::inc(x_138);
lean::dec(x_135);
x_141 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_136);
if (lean::is_scalar(x_10)) {
 x_142 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_142 = x_10;
}
lean::cnstr_set(x_142, 0, x_141);
lean::cnstr_set(x_142, 1, x_138);
return x_142;
}
}
}
}
else
{
obj* x_145; uint8 x_147; obj* x_148; obj* x_149; obj* x_150; obj* x_151; 
lean::dec(x_1);
lean::dec(x_0);
x_145 = lean::cnstr_get(x_6, 0);
lean::inc(x_145);
x_147 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*1);
if (lean::is_shared(x_6)) {
 lean::dec(x_6);
 x_148 = lean::box(0);
} else {
 lean::cnstr_release(x_6, 0);
 x_148 = x_6;
}
if (lean::is_scalar(x_148)) {
 x_149 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_149 = x_148;
}
lean::cnstr_set(x_149, 0, x_145);
lean::cnstr_set_scalar(x_149, sizeof(void*)*1, x_147);
x_150 = x_149;
if (lean::is_scalar(x_10)) {
 x_151 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_151 = x_10;
}
lean::cnstr_set(x_151, 0, x_150);
lean::cnstr_set(x_151, 1, x_8);
return x_151;
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
obj* x_12; obj* x_13; obj* x_15; obj* x_17; 
lean::inc(x_5);
lean::inc(x_4);
x_12 = l_lean_parser_curr__lbp___at_lean_parser_level__parser_run___spec__4(x_4, x_5, x_6, x_7);
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
obj* x_18; obj* x_20; obj* x_22; obj* x_24; uint8 x_25; 
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
x_25 = lean::nat_dec_lt(x_1, x_18);
lean::dec(x_18);
if (x_25 == 0)
{
obj* x_32; obj* x_34; obj* x_35; obj* x_36; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_32 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_32);
if (lean::is_scalar(x_24)) {
 x_34 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_34 = x_24;
}
lean::cnstr_set(x_34, 0, x_3);
lean::cnstr_set(x_34, 1, x_20);
lean::cnstr_set(x_34, 2, x_32);
x_35 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_22, x_34);
if (lean::is_scalar(x_17)) {
 x_36 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_36 = x_17;
}
lean::cnstr_set(x_36, 0, x_35);
lean::cnstr_set(x_36, 1, x_15);
return x_36;
}
else
{
obj* x_38; obj* x_39; obj* x_44; obj* x_45; obj* x_47; 
lean::dec(x_24);
x_38 = lean::mk_nat_obj(1u);
x_39 = lean::nat_sub(x_2, x_38);
lean::dec(x_2);
lean::inc(x_5);
lean::inc(x_4);
lean::inc(x_0);
x_44 = lean::apply_5(x_0, x_3, x_4, x_5, x_20, x_15);
x_45 = lean::cnstr_get(x_44, 0);
lean::inc(x_45);
x_47 = lean::cnstr_get(x_44, 1);
lean::inc(x_47);
lean::dec(x_44);
if (lean::obj_tag(x_45) == 0)
{
obj* x_50; obj* x_52; obj* x_54; obj* x_57; obj* x_58; obj* x_60; obj* x_63; obj* x_64; obj* x_65; 
x_50 = lean::cnstr_get(x_45, 0);
lean::inc(x_50);
x_52 = lean::cnstr_get(x_45, 1);
lean::inc(x_52);
x_54 = lean::cnstr_get(x_45, 2);
lean::inc(x_54);
lean::dec(x_45);
x_57 = l___private_init_lean_parser_pratt_1__trailing__loop___main___at_lean_parser_level__parser_run___spec__2(x_0, x_1, x_39, x_50, x_4, x_5, x_52, x_47);
x_58 = lean::cnstr_get(x_57, 0);
lean::inc(x_58);
x_60 = lean::cnstr_get(x_57, 1);
lean::inc(x_60);
lean::dec(x_57);
x_63 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_54, x_58);
x_64 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_22, x_63);
if (lean::is_scalar(x_17)) {
 x_65 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_65 = x_17;
}
lean::cnstr_set(x_65, 0, x_64);
lean::cnstr_set(x_65, 1, x_60);
return x_65;
}
else
{
obj* x_71; uint8 x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_39);
x_71 = lean::cnstr_get(x_45, 0);
lean::inc(x_71);
x_73 = lean::cnstr_get_scalar<uint8>(x_45, sizeof(void*)*1);
if (lean::is_shared(x_45)) {
 lean::dec(x_45);
 x_74 = lean::box(0);
} else {
 lean::cnstr_release(x_45, 0);
 x_74 = x_45;
}
if (lean::is_scalar(x_74)) {
 x_75 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_75 = x_74;
}
lean::cnstr_set(x_75, 0, x_71);
lean::cnstr_set_scalar(x_75, sizeof(void*)*1, x_73);
x_76 = x_75;
x_77 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_22, x_76);
if (lean::is_scalar(x_17)) {
 x_78 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_78 = x_17;
}
lean::cnstr_set(x_78, 0, x_77);
lean::cnstr_set(x_78, 1, x_47);
return x_78;
}
}
}
else
{
obj* x_85; uint8 x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
x_85 = lean::cnstr_get(x_13, 0);
lean::inc(x_85);
x_87 = lean::cnstr_get_scalar<uint8>(x_13, sizeof(void*)*1);
if (lean::is_shared(x_13)) {
 lean::dec(x_13);
 x_88 = lean::box(0);
} else {
 lean::cnstr_release(x_13, 0);
 x_88 = x_13;
}
if (lean::is_scalar(x_88)) {
 x_89 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_89 = x_88;
}
lean::cnstr_set(x_89, 0, x_85);
lean::cnstr_set_scalar(x_89, sizeof(void*)*1, x_87);
x_90 = x_89;
if (lean::is_scalar(x_17)) {
 x_91 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_91 = x_17;
}
lean::cnstr_set(x_91, 0, x_90);
lean::cnstr_set(x_91, 1, x_15);
return x_91;
}
}
else
{
obj* x_96; obj* x_97; obj* x_98; obj* x_101; 
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
x_96 = lean::box(0);
x_97 = l___private_init_lean_parser_combinators_1__many1__aux___main___rarg___closed__1;
x_98 = l_mjoin___rarg___closed__1;
lean::inc(x_98);
lean::inc(x_97);
x_101 = l_lean_parser_monad__parsec_error___at_lean_parser_level__parser_run___spec__3___rarg(x_97, x_98, x_96, x_96, x_4, x_5, x_6, x_7);
return x_101;
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
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_rec_1__run__aux___at_lean_parser_level__parser_run___spec__7), 7, 3);
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
obj* x_5; obj* x_6; obj* x_7; obj* x_9; obj* x_11; obj* x_12; obj* x_14; obj* x_16; obj* x_17; obj* x_19; obj* x_20; 
x_5 = lean::string_iterator_remaining(x_3);
x_6 = lean::mk_nat_obj(1u);
x_7 = lean::nat_add(x_5, x_6);
lean::dec(x_5);
x_9 = l_lean_parser_rec__t_run__parsec___at_lean_parser_detail__ident_parser___spec__1___closed__1;
lean::inc(x_9);
x_11 = l_lean_parser_rec__t_run___at_lean_parser_level__parser_run___spec__6(x_0, x_9, x_1, x_7, x_2, x_3, x_4);
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
}
obj* l_lean_parser_pratt__parser___at_lean_parser_level__parser_run___spec__1___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_9; obj* x_10; obj* x_12; obj* x_14; 
lean::inc(x_4);
lean::inc(x_3);
x_9 = lean::apply_4(x_0, x_3, x_4, x_5, x_6);
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
obj* x_15; obj* x_17; obj* x_19; obj* x_22; obj* x_23; obj* x_24; obj* x_26; obj* x_27; obj* x_29; obj* x_32; obj* x_34; obj* x_35; obj* x_36; 
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
x_27 = lean::cnstr_get(x_26, 0);
lean::inc(x_27);
x_29 = lean::cnstr_get(x_26, 1);
lean::inc(x_29);
lean::dec(x_26);
x_32 = l_lean_parser_finish__comment__block___closed__2;
lean::inc(x_32);
x_34 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_32, x_27);
x_35 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_19, x_34);
if (lean::is_scalar(x_14)) {
 x_36 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_36 = x_14;
}
lean::cnstr_set(x_36, 0, x_35);
lean::cnstr_set(x_36, 1, x_29);
return x_36;
}
else
{
obj* x_41; uint8 x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; 
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_2);
x_41 = lean::cnstr_get(x_10, 0);
lean::inc(x_41);
x_43 = lean::cnstr_get_scalar<uint8>(x_10, sizeof(void*)*1);
if (lean::is_shared(x_10)) {
 lean::dec(x_10);
 x_44 = lean::box(0);
} else {
 lean::cnstr_release(x_10, 0);
 x_44 = x_10;
}
if (lean::is_scalar(x_44)) {
 x_45 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_45 = x_44;
}
lean::cnstr_set(x_45, 0, x_41);
lean::cnstr_set_scalar(x_45, sizeof(void*)*1, x_43);
x_46 = x_45;
if (lean::is_scalar(x_14)) {
 x_47 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_47 = x_14;
}
lean::cnstr_set(x_47, 0, x_46);
lean::cnstr_set(x_47, 1, x_12);
return x_47;
}
}
}
obj* l_lean_parser_pratt__parser___at_lean_parser_level__parser_run___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; 
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_pratt__parser___at_lean_parser_level__parser_run___spec__1___lambda__1), 7, 2);
lean::closure_set(x_6, 0, x_0);
lean::closure_set(x_6, 1, x_1);
x_7 = l_lean_parser_rec__t_run__parsec___at_lean_parser_level__parser_run___spec__5(x_2, x_6, x_3, x_4, x_5);
return x_7;
}
}
obj* l_lean_parser_level__parser_run(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_8; 
x_4 = l_lean_parser_level__parser_run_lean_parser_has__view___closed__2;
x_5 = l_lean_parser_level__parser_run_lean_parser_has__view___closed__3;
lean::inc(x_5);
lean::inc(x_4);
x_8 = l_lean_parser_pratt__parser___at_lean_parser_level__parser_run___spec__1(x_4, x_5, x_0, x_1, x_2, x_3);
return x_8;
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
 l_lean_parser_level__parser__m_alternative = _init_l_lean_parser_level__parser__m_alternative();
 l_lean_parser_level__parser__m_monad__reader = _init_l_lean_parser_level__parser__m_monad__reader();
 l_lean_parser_level__parser__m_lean_parser_monad__parsec = _init_l_lean_parser_level__parser__m_lean_parser_monad__parsec();
 l_lean_parser_level__parser__m_monad__except = _init_l_lean_parser_level__parser__m_monad__except();
 l_lean_parser_level__parser__m_lean_parser_monad__rec = _init_l_lean_parser_level__parser__m_lean_parser_monad__rec();
 l_lean_parser_level__parser__m_lean_parser_monad__basic__parser = _init_l_lean_parser_level__parser__m_lean_parser_monad__basic__parser();
 l_lean_parser_level__parser__m = _init_l_lean_parser_level__parser__m();
 l_lean_parser_level__parser = _init_l_lean_parser_level__parser();
 l_lean_parser_trailing__level__parser__m_monad = _init_l_lean_parser_trailing__level__parser__m_monad();
 l_lean_parser_trailing__level__parser__m_alternative = _init_l_lean_parser_trailing__level__parser__m_alternative();
 l_lean_parser_trailing__level__parser__m_monad__reader = _init_l_lean_parser_trailing__level__parser__m_monad__reader();
 l_lean_parser_trailing__level__parser__m_lean_parser_monad__parsec = _init_l_lean_parser_trailing__level__parser__m_lean_parser_monad__parsec();
 l_lean_parser_trailing__level__parser__m_monad__except = _init_l_lean_parser_trailing__level__parser__m_monad__except();
 l_lean_parser_trailing__level__parser__m_lean_parser_monad__rec = _init_l_lean_parser_trailing__level__parser__m_lean_parser_monad__rec();
 l_lean_parser_trailing__level__parser__m_lean_parser_monad__basic__parser = _init_l_lean_parser_trailing__level__parser__m_lean_parser_monad__basic__parser();
 l_lean_parser_trailing__level__parser__m = _init_l_lean_parser_trailing__level__parser__m();
 l_lean_parser_trailing__level__parser = _init_l_lean_parser_trailing__level__parser();
 l_lean_parser_level_parser_lean_parser_has__tokens___closed__1 = _init_l_lean_parser_level_parser_lean_parser_has__tokens___closed__1();
 l_lean_parser_level_parser_lean_parser_has__view___closed__1 = _init_l_lean_parser_level_parser_lean_parser_has__view___closed__1();
 l_lean_parser_level_parser___closed__1 = _init_l_lean_parser_level_parser___closed__1();
 l_lean_parser_level_lean_parser_has__tokens = _init_l_lean_parser_level_lean_parser_has__tokens();
 l_lean_parser_level_lean_parser_has__view = _init_l_lean_parser_level_lean_parser_has__view();
 l_lean_parser_level_paren = _init_l_lean_parser_level_paren();
 l_lean_parser_level_paren_has__view_x_27___lambda__1___closed__1 = _init_l_lean_parser_level_paren_has__view_x_27___lambda__1___closed__1();
 l_lean_parser_level_paren_has__view_x_27 = _init_l_lean_parser_level_paren_has__view_x_27();
 l_lean_parser_level_paren_has__view = _init_l_lean_parser_level_paren_has__view();
 l_lean_parser_level_paren_parser_lean_parser_has__tokens = _init_l_lean_parser_level_paren_parser_lean_parser_has__tokens();
 l_lean_parser_level_paren_parser_lean_parser_has__view = _init_l_lean_parser_level_paren_parser_lean_parser_has__view();
 l_lean_parser_level_paren_parser___closed__1 = _init_l_lean_parser_level_paren_parser___closed__1();
 l_lean_parser_level_leading = _init_l_lean_parser_level_leading();
 l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__1 = _init_l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__1();
 l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__2 = _init_l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__2();
 l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__3 = _init_l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__3();
 l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__4 = _init_l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__4();
 l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__5 = _init_l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__5();
 l_lean_parser_level_leading_has__view_x_27___lambda__2___closed__1 = _init_l_lean_parser_level_leading_has__view_x_27___lambda__2___closed__1();
 l_lean_parser_level_leading_has__view_x_27___lambda__2___closed__2 = _init_l_lean_parser_level_leading_has__view_x_27___lambda__2___closed__2();
 l_lean_parser_level_leading_has__view_x_27 = _init_l_lean_parser_level_leading_has__view_x_27();
 l_lean_parser_level_leading_has__view = _init_l_lean_parser_level_leading_has__view();
 l_lean_parser_number_parser___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__2___rarg___closed__1 = _init_l_lean_parser_number_parser___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__2___rarg___closed__1();
 l_lean_parser_ident_parser___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__3___rarg___closed__1 = _init_l_lean_parser_ident_parser___at_lean_parser_level_leading_parser_lean_parser_has__tokens___spec__3___rarg___closed__1();
 l_lean_parser_level_leading_parser_lean_parser_has__tokens = _init_l_lean_parser_level_leading_parser_lean_parser_has__tokens();
 l_lean_parser_level_leading_parser_lean_parser_has__view = _init_l_lean_parser_level_leading_parser_lean_parser_has__view();
 l_lean_parser_level_leading_parser___closed__1 = _init_l_lean_parser_level_leading_parser___closed__1();
 l_lean_parser_level_app = _init_l_lean_parser_level_app();
 l_lean_parser_level_app_has__view_x_27___lambda__1___closed__1 = _init_l_lean_parser_level_app_has__view_x_27___lambda__1___closed__1();
 l_lean_parser_level_app_has__view_x_27 = _init_l_lean_parser_level_app_has__view_x_27();
 l_lean_parser_level_app_has__view = _init_l_lean_parser_level_app_has__view();
 l_lean_parser_level_app_parser_lean_parser_has__tokens = _init_l_lean_parser_level_app_parser_lean_parser_has__tokens();
 l_lean_parser_level_app_parser_lean_parser_has__view = _init_l_lean_parser_level_app_parser_lean_parser_has__view();
 l_lean_parser_level_app_parser___closed__1 = _init_l_lean_parser_level_app_parser___closed__1();
 l_lean_parser_level_add__lit = _init_l_lean_parser_level_add__lit();
 l_lean_parser_level_add__lit_has__view_x_27___lambda__1___closed__1 = _init_l_lean_parser_level_add__lit_has__view_x_27___lambda__1___closed__1();
 l_lean_parser_level_add__lit_has__view_x_27___lambda__1___closed__2 = _init_l_lean_parser_level_add__lit_has__view_x_27___lambda__1___closed__2();
 l_lean_parser_level_add__lit_has__view_x_27 = _init_l_lean_parser_level_add__lit_has__view_x_27();
 l_lean_parser_level_add__lit_has__view = _init_l_lean_parser_level_add__lit_has__view();
 l_lean_parser_level_add__lit_parser_lean_parser_has__tokens = _init_l_lean_parser_level_add__lit_parser_lean_parser_has__tokens();
 l_lean_parser_level_add__lit_parser_lean_parser_has__view = _init_l_lean_parser_level_add__lit_parser_lean_parser_has__view();
 l_lean_parser_level_add__lit_parser___closed__1 = _init_l_lean_parser_level_add__lit_parser___closed__1();
 l_lean_parser_level_trailing = _init_l_lean_parser_level_trailing();
 l_lean_parser_level_trailing_has__view_x_27___lambda__1___closed__1 = _init_l_lean_parser_level_trailing_has__view_x_27___lambda__1___closed__1();
 l_lean_parser_level_trailing_has__view_x_27___lambda__1___closed__2 = _init_l_lean_parser_level_trailing_has__view_x_27___lambda__1___closed__2();
 l_lean_parser_level_trailing_has__view_x_27 = _init_l_lean_parser_level_trailing_has__view_x_27();
 l_lean_parser_level_trailing_has__view = _init_l_lean_parser_level_trailing_has__view();
 l_lean_parser_level_trailing_parser_lean_parser_has__tokens = _init_l_lean_parser_level_trailing_parser_lean_parser_has__tokens();
 l_lean_parser_level_trailing_parser_lean_parser_has__view = _init_l_lean_parser_level_trailing_parser_lean_parser_has__view();
 l_lean_parser_level_trailing_parser___closed__1 = _init_l_lean_parser_level_trailing_parser___closed__1();
 l_lean_parser_level__parser_run_lean_parser_has__view___closed__1 = _init_l_lean_parser_level__parser_run_lean_parser_has__view___closed__1();
 l_lean_parser_level__parser_run_lean_parser_has__view___closed__2 = _init_l_lean_parser_level__parser_run_lean_parser_has__view___closed__2();
 l_lean_parser_level__parser_run_lean_parser_has__view___closed__3 = _init_l_lean_parser_level__parser_run_lean_parser_has__view___closed__3();
 l_lean_parser_level__parser__coe = _init_l_lean_parser_level__parser__coe();
}
