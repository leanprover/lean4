// Lean compiler output
// Module: init.lean.parser.level
// Imports: init.lean.parser.pratt
#include "runtime/object.h"
#include "runtime/apply.h"
#include "runtime/io.h"
#include "kernel/builtin.h"
typedef lean::object obj;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#endif
obj* l_lean_parser_level_trailing_parser___closed__1;
obj* l_lean_parser_level_trailing;
obj* l_lean_parser_symbol_tokens___rarg(obj*, obj*);
extern obj* l_lean_parser_raw_view___rarg___lambda__3___closed__1;
obj* l_lean_parser_level_paren_has__view_x_27;
extern obj* l_lean_parser_curr__lbp___rarg___lambda__3___closed__1;
obj* l_lean_parser_level_add__lit_has__view_x_27___lambda__1(obj*);
obj* l_lean_parser_rec__t_run__parsec___at_lean_parser_level__parser_run___spec__5___closed__1;
obj* l_lean_parser_rec__t_run__parsec___at_lean_parser_level__parser_run___spec__5(obj*, obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_number_has__view;
extern obj* l_lean_parser_basic__parser__m_monad;
obj* l_lean_parser_symbol__core___at_lean_parser_level_paren_parser___spec__1(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_level_leading_parser___spec__5___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_combinators_node_view___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_pratt__parser_view___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_parsec__t_bind__mk__res___rarg(obj*, obj*);
obj* l_lean_parser_level__parser__m_lean_parser_monad__parsec;
extern obj* l_lean_parser_basic__parser__m_lean_parser_monad__parsec;
obj* l_string_trim(obj*);
extern obj* l_lean_parser_curr__lbp___rarg___lambda__1___closed__1;
obj* l_lean_parser_combinators_node___at_lean_parser_level_app_parser___spec__1(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_level_leading_has__view_x_27___lambda__1(obj*);
obj* l_lean_parser_level_trailing_has__view_x_27___lambda__2(obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_level__parser_run___spec__3(obj*);
extern obj* l_lean_parser_rec__t_run__parsec___rarg___lambda__1___closed__1;
obj* l_lean_parser_level__parser_run_lean_parser_has__view(obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_level_leading_parser___spec__5(obj*);
obj* l_lean_parser_level_add__lit;
obj* l_lean_parser_trailing__level__parser__m_lean_parser_monad__parsec;
obj* l_lean_parser_level_paren_has__view_x_27___lambda__1___closed__1;
obj* l_lean_parser_level_trailing_has__view_x_27___lambda__1(obj*);
obj* l_reader__t_alternative___rarg(obj*, obj*);
obj* l_lean_parser_level__parser__m_lean_parser_monad__basic__parser;
obj* l_lean_parser_list_cons_tokens___rarg(obj*, obj*);
obj* l_lean_parser_syntax_as__node___main(obj*);
extern obj* l_lean_parser_basic__parser__m_alternative;
obj* l_lean_parser_level_parser_lean_parser_has__view___closed__1;
obj* l_lean_parser_trie_match__prefix___rarg(obj*, obj*);
obj* l_lean_parser_level_add__lit_has__view_x_27___lambda__1___closed__1;
extern obj* l_lean_parser_basic__parser__m_monad__except;
obj* l_lean_parser_level_paren_has__view;
obj* l_lean_parser_level__parser__m_monad__reader;
obj* l_lean_parser_level_leading_has__view;
obj* l_lean_parser_level_get__leading(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_rec__t_lean_parser_monad__parsec___rarg(obj*, obj*, obj*);
obj* l_lean_parser_level__parser_run___closed__1;
obj* l_lean_parser_substring_of__string(obj*);
obj* l_lean_parser_number_parser___at_lean_parser_level_leading_parser___spec__2___rarg(obj*, obj*, obj*);
obj* l_lean_parser_level_app_has__view_x_27;
obj* l_lean_parser_level_leading_has__view_x_27___lambda__2___closed__2;
obj* l_lean_parser_monad__rec_trans___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_parser_level_paren_has__view_x_27___lambda__1(obj*);
obj* l_lean_parser_combinators_recurse_view___rarg(obj*, obj*);
extern obj* l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
obj* l_lean_parser_combinators_label_view___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_level_lean_parser_has__tokens;
obj* l_lean_parser_level_app_parser_lean_parser_has__tokens;
obj* l_lean_parser_level_app_parser_lean_parser_has__view;
obj* l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__4;
obj* l_lean_parser_monad__parsec_error___at_lean_parser_level_trailing_parser___spec__2(obj*);
obj* l_lean_parser_level_trailing_parser(obj*, obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_number_has__view_x_27___lambda__1___closed__6;
obj* l_lean_parser_trailing__level__parser__m_monad__except;
obj* l_option_map___rarg(obj*, obj*);
obj* l_lean_parser_level_paren_parser___closed__1;
obj* l_option_get___main___at_lean_parser_run___spec__2(obj*);
obj* l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__2;
obj* l_lean_parser_level__parser__m_monad__except;
obj* l_lean_parser_level_app_has__view_x_27___lambda__1(obj*);
obj* l_lean_parser_level__parser__coe;
obj* l_lean_parser_level_leading_has__view_x_27___lambda__2(obj*);
extern obj* l_mjoin___rarg___closed__1;
obj* l_lean_parser_level_trailing_has__view_x_27;
obj* l_has__monad__lift__t__refl(obj*, obj*);
obj* l_lean_parser_level_add__lit_has__view_x_27___lambda__2(obj*);
obj* l_lean_parser_level_app_has__view_x_27___lambda__2(obj*);
obj* l_lean_parser_parsec__t_orelse__mk__res___rarg(obj*, obj*);
obj* l_lean_parser_curr__lbp___at_lean_parser_level__parser_run___spec__4(obj*, obj*, obj*, obj*);
obj* l_id___rarg(obj*);
obj* l_lean_parser_level_leading_has__view_x_27;
obj* l_lean_parser_level_app_parser___closed__1;
obj* l_lean_parser_combinators_choice__aux___main___at_lean_parser_level_leading_parser___spec__4(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_reader__t_monad__functor(obj*, obj*, obj*, obj*, obj*, obj*);
extern obj* l___private_1297690757__many1__aux___main___rarg___closed__1;
obj* l_reader__t_monad___rarg(obj*);
obj* l_lean_parser_level__parser__m_monad;
obj* l_lean_parser_level__parser__m_lean_parser_monad__rec;
obj* l___private_1055111885__trailing__loop___main___at_lean_parser_level__parser_run___spec__2(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_reader__t_lift(obj*, obj*, obj*, obj*);
obj* l_lean_parser_trailing__level__parser__coe(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_ident_parser___at_lean_parser_level_leading_parser___spec__3___rarg(obj*, obj*, obj*);
obj* l_lean_parser_level_parser_lean_parser_has__view(obj*);
obj* l_lean_parser_level__parser_run___closed__2;
obj* l_lean_parser_monad__parsec_error___at___private_4089500695__finish__comment__block__aux___main___spec__1___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_trailing__level__parser__m_monad__reader;
obj* l_option_get__or__else___main___rarg(obj*, obj*);
obj* l_lean_parser_level_app_has__view_x_27___lambda__1___closed__1;
obj* l_lean_parser_monad__parsec__trans___rarg(obj*, obj*, obj*);
obj* l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__1;
obj* l_lean_parser_number_parser___at_lean_parser_level_leading_parser___spec__2(obj*);
obj* l_lean_parser_parsec__t_try__mk__res___rarg(obj*);
obj* l_lean_parser_trailing__level__parser__m_alternative;
obj* l_lean_parser_level_add__lit_has__view_x_27;
obj* l_lean_parser_level_parser_lean_parser_has__tokens(obj*);
obj* l_lean_parser_level_paren;
obj* l_lean_parser_rec__t_run___at_lean_parser_level__parser_run___spec__6(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_level_trailing_parser_lean_parser_has__tokens;
obj* l_lean_parser_level__parser;
obj* l_has__monad__lift__t__trans___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_parser_trailing__level__parser__m;
obj* l_lean_parser_try__view___at_lean_parser_number_parser___spec__1(obj*);
obj* l_lean_parser_level_add__lit_has__view;
obj* l_lean_parser_monad__parsec_observing___at_lean_parser_peek__token___spec__2(obj*, obj*, obj*);
obj* l_lean_parser_ident_parser___at_lean_parser_level_leading_parser___spec__3___rarg___closed__1;
obj* l___private_3693562977__run__aux___main___rarg(obj*, obj*, obj*, obj*);
obj* l_lean_parser_rec__t_recurse___at_lean_parser_level_parser___spec__1(obj*, obj*, obj*, obj*, obj*);
obj* l_reader__t_read___rarg(obj*, obj*);
obj* l_lean_parser_number_parser___at_lean_parser_level_leading_parser___spec__2___rarg___closed__1;
extern obj* l_lean_parser_finish__comment__block___closed__2;
obj* l_lean_parser_trailing__level__parser__m_monad;
obj* l_lean_parser_level_parser(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_level_lean_parser_has__view;
obj* l_lean_parser_level_add__lit_parser_lean_parser_has__view;
obj* l_lean_parser_level_leading_parser(obj*, obj*, obj*, obj*);
obj* l_lean_parser_combinators_node___at_lean_parser_level_paren_parser___spec__2(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_level_leading_parser_lean_parser_has__tokens;
obj* l_lean_parser_level_leading_has__view_x_27___lambda__2___closed__1;
obj* l_lean_parser_tokens___rarg(obj*);
extern obj* l_lean_parser_basic__parser__m_monad__reader;
obj* l_lean_parser_number_parser___at_lean_parser_level_add__lit_parser___spec__2___rarg(obj*, obj*, obj*);
obj* l_lean_parser_level__parser_run_lean_parser_has__tokens(obj*);
obj* l_list_reverse___rarg(obj*);
obj* l_lean_parser_level_paren_parser_lean_parser_has__view;
obj* l_lean_parser_token(obj*, obj*, obj*);
obj* l___private_3693562977__run__aux___at_lean_parser_level__parser_run___spec__7(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_level__parser_run_lean_parser_has__view___closed__1;
obj* l_lean_parser_syntax_mk__node(obj*, obj*);
extern obj* l_string_join___closed__1;
extern obj* l_lean_parser_number_has__view_x_27___lambda__2___closed__1;
obj* l_lean_parser_level_add__lit_parser_lean_parser_has__tokens;
obj* l_lean_parser_trailing__level__parser__m_lean_parser_monad__basic__parser;
obj* l_lean_parser_number_parser___at_lean_parser_level_add__lit_parser___spec__2(obj*, obj*);
obj* l_reader__t_monad__except___rarg(obj*);
obj* l_reader__t_lift___rarg(obj*, obj*);
obj* l_lean_parser_level_app;
obj* l_lean_parser_level_paren_parser(obj*, obj*, obj*, obj*);
obj* l_lean_parser_level_app_parser(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_level_leading_parser___closed__1;
obj* l_list_mfoldl___main___at_lean_parser_level_app_parser___spec__2(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_combinators_choice__aux___main___at_lean_parser_level_trailing_parser___spec__1(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_level_app_has__view;
obj* l_lean_parser_level_leading_parser_lean_parser_has__view;
obj* l_list_append___main___rarg(obj*, obj*);
obj* l_lean_parser_level_trailing_has__view_x_27___lambda__1___closed__1;
obj* l_lean_parser_pratt__parser___at_lean_parser_level__parser_run___spec__1(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_rec__t_recurse___rarg(obj*, obj*, obj*);
obj* l_lean_parser_level_add__lit_has__view_x_27___lambda__1___closed__2;
obj* l_lean_parser_level_app_parser___lambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_level_trailing_has__view_x_27___lambda__1___closed__2;
obj* l_lean_parser_level_add__lit_parser___closed__1;
obj* l_lean_parser_level_trailing_has__view;
obj* l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__3;
obj* l_lean_parser_level_parser_lean_parser_has__tokens___closed__1;
obj* l_lean_parser_level_add__lit_parser(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_trailing__level__parser__m_lean_parser_monad__rec;
extern obj* l_lean_parser_number_has__view_x_27___lambda__2___closed__2;
obj* l_lean_parser_trailing__level__parser;
obj* l_lean_parser_level_trailing_parser_lean_parser_has__view;
obj* l_lean_parser_monad__parsec_error___at_lean_parser_level_trailing_parser___spec__2___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_ident_parser___at_lean_parser_level_leading_parser___spec__3(obj*);
obj* l_lean_parser_level__parser_run(obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_match__token___closed__2;
obj* l_lean_parser_level_paren_parser_lean_parser_has__tokens;
obj* l_lean_parser_level__parser__m;
extern obj* l_lean_parser_max__prec;
obj* l_lean_parser_level_parser___closed__1;
obj* l_lean_parser_substring_to__string(obj*);
obj* l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__5;
obj* l_lean_name_has__dec__eq___main(obj*, obj*);
obj* l_lean_parser_symbol__core___at_lean_parser_level_add__lit_parser___spec__1(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_symbol__or__ident___at_lean_parser_level_leading_parser___spec__1(obj*, obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_combinators_choice__aux___main___rarg___closed__1;
extern obj* l_lean_parser_detail__ident__part_has__view_x_27___lambda__2___closed__1;
obj* l_lean_parser_rec__t_run__parsec___at_lean_parser_level__parser_run___spec__5___lambda__1(obj*, obj*, obj*, obj*);
obj* l_lean_parser_parsec__t_labels__mk__res___rarg(obj*, obj*);
obj* l_lean_parser_level_paren_has__view_x_27___lambda__2(obj*);
extern obj* l_lean_parser_curr__lbp___rarg___lambda__3___closed__2;
obj* l_lean_parser_level_leading;
obj* l_list_mfoldl___main___at_lean_parser_level_paren_parser___spec__3(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_monad__parsec_error___at_lean_parser_level__parser_run___spec__3___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_string_quote(obj*);
obj* l_dlist_singleton___rarg(obj*, obj*);
obj* l_lean_parser_pratt__parser___at_lean_parser_level__parser_run___spec__1___lambda__1(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_level__parser__m_alternative;
extern obj* l_lean_parser_detail__ident__part_has__view_x_27___lambda__2___closed__2;
obj* _init_l_lean_parser_level__parser__m() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
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
obj* _init_l_lean_parser_level__parser() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init_l_lean_parser_trailing__level__parser__m() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
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
obj* _init_l_lean_parser_trailing__level__parser() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
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
obj* l_lean_parser_level_parser(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_8; obj* x_10; obj* x_11; obj* x_13; obj* x_14; 
x_5 = l_lean_parser_rec__t_recurse___at_lean_parser_level_parser___spec__1(x_0, x_1, x_2, x_3, x_4);
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
obj* l_lean_parser_rec__t_recurse___at_lean_parser_level_parser___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
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
obj* l_lean_parser_level_parser_lean_parser_has__view(obj* x_0) {
_start:
{
obj* x_2; obj* x_3; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_12; 
lean::inc(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_rec__t_recurse___at_lean_parser_level_parser___spec__1), 5, 1);
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
obj* _init_l_lean_parser_level_parser_lean_parser_has__view___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("universe level");
return x_0;
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
obj* _init_l_lean_parser_level_parser_lean_parser_has__tokens___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(0);
x_1 = l_lean_parser_tokens___rarg(x_0);
return x_1;
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
x_2 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_4, 0, x_2);
lean::cnstr_set(x_4, 1, x_3);
x_5 = lean::mk_string("level");
x_6 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_6, 0, x_4);
lean::cnstr_set(x_6, 1, x_5);
x_7 = lean::mk_string("paren");
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set(x_8, 1, x_7);
return x_8;
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
obj* l_lean_parser_level_paren_has__view_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_5; obj* x_6; obj* x_8; 
x_8 = l_lean_parser_syntax_as__node___main(x_0);
if (lean::obj_tag(x_8) == 0)
{
obj* x_10; 
lean::dec(x_8);
x_10 = l_lean_parser_level_paren_has__view_x_27___lambda__1___closed__1;
lean::inc(x_10);
return x_10;
}
else
{
obj* x_12; obj* x_15; 
x_12 = lean::cnstr_get(x_8, 0);
lean::inc(x_12);
lean::dec(x_8);
x_15 = lean::cnstr_get(x_12, 1);
lean::inc(x_15);
lean::dec(x_12);
if (lean::obj_tag(x_15) == 0)
{
obj* x_18; 
x_18 = lean::box(3);
x_5 = x_15;
x_6 = x_18;
goto lbl_7;
}
else
{
obj* x_19; obj* x_21; 
x_19 = lean::cnstr_get(x_15, 0);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_15, 1);
lean::inc(x_21);
lean::dec(x_15);
x_5 = x_21;
x_6 = x_19;
goto lbl_7;
}
}
lbl_4:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_25; obj* x_26; 
lean::dec(x_3);
x_25 = lean::box(0);
x_26 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_26, 0, x_1);
lean::cnstr_set(x_26, 1, x_2);
lean::cnstr_set(x_26, 2, x_25);
return x_26;
}
else
{
obj* x_27; 
x_27 = lean::cnstr_get(x_3, 0);
lean::inc(x_27);
lean::dec(x_3);
switch (lean::obj_tag(x_27)) {
case 0:
{
obj* x_30; obj* x_33; obj* x_34; 
x_30 = lean::cnstr_get(x_27, 0);
lean::inc(x_30);
lean::dec(x_27);
x_33 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_33, 0, x_30);
x_34 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_34, 0, x_1);
lean::cnstr_set(x_34, 1, x_2);
lean::cnstr_set(x_34, 2, x_33);
return x_34;
}
case 1:
{
obj* x_36; obj* x_37; 
lean::dec(x_27);
x_36 = lean::box(0);
x_37 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_37, 0, x_1);
lean::cnstr_set(x_37, 1, x_2);
lean::cnstr_set(x_37, 2, x_36);
return x_37;
}
case 2:
{
obj* x_39; obj* x_40; 
lean::dec(x_27);
x_39 = lean::box(0);
x_40 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_40, 0, x_1);
lean::cnstr_set(x_40, 1, x_2);
lean::cnstr_set(x_40, 2, x_39);
return x_40;
}
default:
{
obj* x_42; obj* x_43; 
lean::dec(x_27);
x_42 = lean::box(0);
x_43 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_43, 0, x_1);
lean::cnstr_set(x_43, 1, x_2);
lean::cnstr_set(x_43, 2, x_42);
return x_43;
}
}
}
}
lbl_7:
{
obj* x_44; 
switch (lean::obj_tag(x_6)) {
case 0:
{
obj* x_46; obj* x_49; 
x_46 = lean::cnstr_get(x_6, 0);
lean::inc(x_46);
lean::dec(x_6);
x_49 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_49, 0, x_46);
if (lean::obj_tag(x_5) == 0)
{
x_44 = x_49;
goto lbl_45;
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
case 1:
{
obj* x_56; 
lean::dec(x_6);
x_56 = lean::box(0);
if (lean::obj_tag(x_5) == 0)
{
x_44 = x_56;
goto lbl_45;
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
case 2:
{
obj* x_63; 
lean::dec(x_6);
x_63 = lean::box(0);
if (lean::obj_tag(x_5) == 0)
{
x_44 = x_63;
goto lbl_45;
}
else
{
obj* x_64; obj* x_66; 
x_64 = lean::cnstr_get(x_5, 0);
lean::inc(x_64);
x_66 = lean::cnstr_get(x_5, 1);
lean::inc(x_66);
lean::dec(x_5);
x_1 = x_63;
x_2 = x_64;
x_3 = x_66;
goto lbl_4;
}
}
default:
{
obj* x_70; 
lean::dec(x_6);
x_70 = lean::box(0);
if (lean::obj_tag(x_5) == 0)
{
x_44 = x_70;
goto lbl_45;
}
else
{
obj* x_71; obj* x_73; 
x_71 = lean::cnstr_get(x_5, 0);
lean::inc(x_71);
x_73 = lean::cnstr_get(x_5, 1);
lean::inc(x_73);
lean::dec(x_5);
x_1 = x_70;
x_2 = x_71;
x_3 = x_73;
goto lbl_4;
}
}
}
lbl_45:
{
if (lean::obj_tag(x_5) == 0)
{
obj* x_77; obj* x_78; obj* x_79; 
lean::dec(x_5);
x_77 = lean::box(0);
x_78 = lean::box(3);
x_79 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_79, 0, x_44);
lean::cnstr_set(x_79, 1, x_78);
lean::cnstr_set(x_79, 2, x_77);
return x_79;
}
else
{
obj* x_80; 
x_80 = lean::cnstr_get(x_5, 0);
lean::inc(x_80);
lean::dec(x_5);
switch (lean::obj_tag(x_80)) {
case 0:
{
obj* x_83; obj* x_86; obj* x_87; obj* x_88; 
x_83 = lean::cnstr_get(x_80, 0);
lean::inc(x_83);
lean::dec(x_80);
x_86 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_86, 0, x_83);
x_87 = lean::box(3);
x_88 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_88, 0, x_44);
lean::cnstr_set(x_88, 1, x_87);
lean::cnstr_set(x_88, 2, x_86);
return x_88;
}
case 1:
{
obj* x_90; obj* x_91; obj* x_92; 
lean::dec(x_80);
x_90 = lean::box(0);
x_91 = lean::box(3);
x_92 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_92, 0, x_44);
lean::cnstr_set(x_92, 1, x_91);
lean::cnstr_set(x_92, 2, x_90);
return x_92;
}
case 2:
{
obj* x_94; obj* x_95; obj* x_96; 
lean::dec(x_80);
x_94 = lean::box(0);
x_95 = lean::box(3);
x_96 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_96, 0, x_44);
lean::cnstr_set(x_96, 1, x_95);
lean::cnstr_set(x_96, 2, x_94);
return x_96;
}
default:
{
obj* x_98; obj* x_99; obj* x_100; 
lean::dec(x_80);
x_98 = lean::box(0);
x_99 = lean::box(3);
x_100 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_100, 0, x_44);
lean::cnstr_set(x_100, 1, x_99);
lean::cnstr_set(x_100, 2, x_98);
return x_100;
}
}
}
}
}
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
obj* x_10; obj* x_11; 
lean::dec(x_2);
x_10 = lean::box(0);
x_11 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_11, 0, x_0);
lean::cnstr_set(x_11, 1, x_1);
lean::cnstr_set(x_11, 2, x_10);
return x_11;
}
else
{
obj* x_12; 
x_12 = lean::cnstr_get(x_2, 0);
lean::inc(x_12);
lean::dec(x_2);
switch (lean::obj_tag(x_12)) {
case 0:
{
obj* x_15; obj* x_18; obj* x_19; 
x_15 = lean::cnstr_get(x_12, 0);
lean::inc(x_15);
lean::dec(x_12);
x_18 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_18, 0, x_15);
x_19 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_19, 0, x_0);
lean::cnstr_set(x_19, 1, x_1);
lean::cnstr_set(x_19, 2, x_18);
return x_19;
}
case 1:
{
obj* x_21; obj* x_22; 
lean::dec(x_12);
x_21 = lean::box(0);
x_22 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_22, 0, x_0);
lean::cnstr_set(x_22, 1, x_1);
lean::cnstr_set(x_22, 2, x_21);
return x_22;
}
case 2:
{
obj* x_24; obj* x_25; 
lean::dec(x_12);
x_24 = lean::box(0);
x_25 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_25, 0, x_0);
lean::cnstr_set(x_25, 1, x_1);
lean::cnstr_set(x_25, 2, x_24);
return x_25;
}
default:
{
obj* x_27; obj* x_28; 
lean::dec(x_12);
x_27 = lean::box(0);
x_28 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_28, 0, x_0);
lean::cnstr_set(x_28, 1, x_1);
lean::cnstr_set(x_28, 2, x_27);
return x_28;
}
}
}
}
lbl_6:
{
obj* x_29; 
switch (lean::obj_tag(x_5)) {
case 0:
{
obj* x_31; obj* x_34; 
x_31 = lean::cnstr_get(x_5, 0);
lean::inc(x_31);
lean::dec(x_5);
x_34 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_34, 0, x_31);
if (lean::obj_tag(x_4) == 0)
{
x_29 = x_34;
goto lbl_30;
}
else
{
obj* x_35; obj* x_37; 
x_35 = lean::cnstr_get(x_4, 0);
lean::inc(x_35);
x_37 = lean::cnstr_get(x_4, 1);
lean::inc(x_37);
lean::dec(x_4);
x_0 = x_34;
x_1 = x_35;
x_2 = x_37;
goto lbl_3;
}
}
case 1:
{
obj* x_41; 
lean::dec(x_5);
x_41 = lean::box(0);
if (lean::obj_tag(x_4) == 0)
{
x_29 = x_41;
goto lbl_30;
}
else
{
obj* x_42; obj* x_44; 
x_42 = lean::cnstr_get(x_4, 0);
lean::inc(x_42);
x_44 = lean::cnstr_get(x_4, 1);
lean::inc(x_44);
lean::dec(x_4);
x_0 = x_41;
x_1 = x_42;
x_2 = x_44;
goto lbl_3;
}
}
case 2:
{
obj* x_48; 
lean::dec(x_5);
x_48 = lean::box(0);
if (lean::obj_tag(x_4) == 0)
{
x_29 = x_48;
goto lbl_30;
}
else
{
obj* x_49; obj* x_51; 
x_49 = lean::cnstr_get(x_4, 0);
lean::inc(x_49);
x_51 = lean::cnstr_get(x_4, 1);
lean::inc(x_51);
lean::dec(x_4);
x_0 = x_48;
x_1 = x_49;
x_2 = x_51;
goto lbl_3;
}
}
default:
{
obj* x_55; 
lean::dec(x_5);
x_55 = lean::box(0);
if (lean::obj_tag(x_4) == 0)
{
x_29 = x_55;
goto lbl_30;
}
else
{
obj* x_56; obj* x_58; 
x_56 = lean::cnstr_get(x_4, 0);
lean::inc(x_56);
x_58 = lean::cnstr_get(x_4, 1);
lean::inc(x_58);
lean::dec(x_4);
x_0 = x_55;
x_1 = x_56;
x_2 = x_58;
goto lbl_3;
}
}
}
lbl_30:
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_62; obj* x_63; obj* x_64; 
lean::dec(x_4);
x_62 = lean::box(0);
x_63 = lean::box(3);
x_64 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_64, 0, x_29);
lean::cnstr_set(x_64, 1, x_63);
lean::cnstr_set(x_64, 2, x_62);
return x_64;
}
else
{
obj* x_65; 
x_65 = lean::cnstr_get(x_4, 0);
lean::inc(x_65);
lean::dec(x_4);
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
lean::cnstr_set(x_73, 0, x_29);
lean::cnstr_set(x_73, 1, x_72);
lean::cnstr_set(x_73, 2, x_71);
return x_73;
}
case 1:
{
obj* x_75; obj* x_76; obj* x_77; 
lean::dec(x_65);
x_75 = lean::box(0);
x_76 = lean::box(3);
x_77 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_77, 0, x_29);
lean::cnstr_set(x_77, 1, x_76);
lean::cnstr_set(x_77, 2, x_75);
return x_77;
}
case 2:
{
obj* x_79; obj* x_80; obj* x_81; 
lean::dec(x_65);
x_79 = lean::box(0);
x_80 = lean::box(3);
x_81 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_81, 0, x_29);
lean::cnstr_set(x_81, 1, x_80);
lean::cnstr_set(x_81, 2, x_79);
return x_81;
}
default:
{
obj* x_83; obj* x_84; obj* x_85; 
lean::dec(x_65);
x_83 = lean::box(0);
x_84 = lean::box(3);
x_85 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_85, 0, x_29);
lean::cnstr_set(x_85, 1, x_84);
lean::cnstr_set(x_85, 2, x_83);
return x_85;
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
obj* x_1; obj* x_3; obj* x_5; obj* x_8; obj* x_10; obj* x_11; obj* x_13; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_23; 
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
x_15 = l_option_map___rarg(x_8, x_5);
x_16 = l_option_get__or__else___main___rarg(x_15, x_11);
x_17 = lean::box(0);
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_16);
lean::cnstr_set(x_18, 1, x_17);
x_19 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_19, 0, x_3);
lean::cnstr_set(x_19, 1, x_18);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_13);
lean::cnstr_set(x_20, 1, x_19);
x_21 = l_lean_parser_level_paren;
lean::inc(x_21);
x_23 = l_lean_parser_syntax_mk__node(x_21, x_20);
return x_23;
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
obj* l_lean_parser_level_paren_parser(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_8; 
x_4 = l_lean_parser_level_paren;
x_5 = l_lean_parser_level_paren_parser___closed__1;
lean::inc(x_5);
lean::inc(x_4);
x_8 = l_lean_parser_combinators_node___at_lean_parser_level_paren_parser___spec__2(x_4, x_5, x_0, x_1, x_2, x_3);
return x_8;
}
}
obj* _init_l_lean_parser_level_paren_parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_9; obj* x_10; obj* x_11; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_0 = lean::mk_string("(");
x_1 = l_string_trim(x_0);
lean::inc(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_3, 0, x_1);
x_4 = l_lean_parser_max__prec;
lean::inc(x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_level_paren_parser___spec__1), 7, 3);
lean::closure_set(x_6, 0, x_1);
lean::closure_set(x_6, 1, x_4);
lean::closure_set(x_6, 2, x_3);
x_7 = lean::mk_nat_obj(0u);
lean::inc(x_7);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_level_parser), 5, 1);
lean::closure_set(x_9, 0, x_7);
x_10 = lean::mk_string(")");
x_11 = l_string_trim(x_10);
lean::inc(x_11);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_13, 0, x_11);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_level_paren_parser___spec__1), 7, 3);
lean::closure_set(x_14, 0, x_11);
lean::closure_set(x_14, 1, x_7);
lean::closure_set(x_14, 2, x_13);
x_15 = lean::box(0);
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_15);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_9);
lean::cnstr_set(x_17, 1, x_16);
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_6);
lean::cnstr_set(x_18, 1, x_17);
return x_18;
}
}
obj* l_lean_parser_symbol__core___at_lean_parser_level_paren_parser___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
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
obj* x_19; obj* x_21; obj* x_23; obj* x_25; unsigned char x_26; 
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
obj* x_29; obj* x_31; obj* x_34; 
lean::dec(x_16);
x_29 = lean::cnstr_get(x_19, 0);
lean::inc(x_29);
x_31 = lean::cnstr_get(x_29, 1);
lean::inc(x_31);
lean::dec(x_29);
x_34 = lean::string_dec_eq(x_0, x_31);
lean::dec(x_0);
if (lean::obj_tag(x_34) == 0)
{
obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_42; obj* x_44; 
lean::dec(x_34);
x_37 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_37, 0, x_5);
x_38 = lean::box(0);
x_39 = l_lean_parser_monad__parsec_error___at___private_4089500695__finish__comment__block__aux___main___spec__1___rarg(x_31, x_2, x_37, x_38, x_4, x_21, x_14);
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
if (lean::obj_tag(x_40) == 0)
{
obj* x_45; obj* x_47; obj* x_50; obj* x_52; obj* x_53; obj* x_54; obj* x_56; obj* x_57; obj* x_58; obj* x_59; 
x_45 = lean::cnstr_get(x_40, 1);
lean::inc(x_45);
x_47 = lean::cnstr_get(x_40, 2);
lean::inc(x_47);
lean::dec(x_40);
x_50 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_50);
if (lean::is_scalar(x_25)) {
 x_52 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_52 = x_25;
}
lean::cnstr_set(x_52, 0, x_19);
lean::cnstr_set(x_52, 1, x_45);
lean::cnstr_set(x_52, 2, x_50);
x_53 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_47, x_52);
x_54 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_23, x_53);
lean::inc(x_50);
x_56 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_50, x_54);
x_57 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_56, x_18);
x_58 = l_lean_parser_parsec__t_try__mk__res___rarg(x_57);
if (lean::is_scalar(x_44)) {
 x_59 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_59 = x_44;
}
lean::cnstr_set(x_59, 0, x_58);
lean::cnstr_set(x_59, 1, x_42);
return x_59;
}
else
{
obj* x_62; unsigned char x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_71; obj* x_72; obj* x_73; obj* x_74; 
lean::dec(x_25);
lean::dec(x_19);
x_62 = lean::cnstr_get(x_40, 0);
lean::inc(x_62);
x_64 = lean::cnstr_get_scalar<unsigned char>(x_40, sizeof(void*)*1);
if (lean::is_shared(x_40)) {
 lean::dec(x_40);
 x_65 = lean::box(0);
} else {
 lean::cnstr_release(x_40, 0);
 x_65 = x_40;
}
if (lean::is_scalar(x_65)) {
 x_66 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_66 = x_65;
}
lean::cnstr_set(x_66, 0, x_62);
lean::cnstr_set_scalar(x_66, sizeof(void*)*1, x_64);
x_67 = x_66;
x_68 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_23, x_67);
x_69 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_69);
x_71 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_69, x_68);
x_72 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_71, x_18);
x_73 = l_lean_parser_parsec__t_try__mk__res___rarg(x_72);
if (lean::is_scalar(x_44)) {
 x_74 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_74 = x_44;
}
lean::cnstr_set(x_74, 0, x_73);
lean::cnstr_set(x_74, 1, x_42);
return x_74;
}
}
else
{
obj* x_80; obj* x_82; obj* x_83; obj* x_84; obj* x_86; obj* x_87; obj* x_88; obj* x_89; 
lean::dec(x_4);
lean::dec(x_5);
lean::dec(x_2);
lean::dec(x_31);
lean::dec(x_34);
x_80 = l_lean_parser_finish__comment__block___closed__2;
lean::inc(x_80);
if (lean::is_scalar(x_25)) {
 x_82 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_82 = x_25;
}
lean::cnstr_set(x_82, 0, x_19);
lean::cnstr_set(x_82, 1, x_21);
lean::cnstr_set(x_82, 2, x_80);
x_83 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_23, x_82);
x_84 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_84);
x_86 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_84, x_83);
x_87 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_86, x_18);
x_88 = l_lean_parser_parsec__t_try__mk__res___rarg(x_87);
x_89 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_89, 0, x_88);
lean::cnstr_set(x_89, 1, x_14);
return x_89;
}
}
case 1:
{
unsigned char x_93; 
lean::dec(x_25);
lean::dec(x_0);
lean::dec(x_19);
x_93 = 0;
x_26 = x_93;
goto lbl_27;
}
case 2:
{
unsigned char x_97; 
lean::dec(x_25);
lean::dec(x_0);
lean::dec(x_19);
x_97 = 0;
x_26 = x_97;
goto lbl_27;
}
default:
{
unsigned char x_101; 
lean::dec(x_25);
lean::dec(x_0);
lean::dec(x_19);
x_101 = 0;
x_26 = x_101;
goto lbl_27;
}
}
lbl_27:
{
obj* x_102; obj* x_103; obj* x_104; obj* x_106; obj* x_107; obj* x_109; obj* x_112; obj* x_113; obj* x_115; obj* x_116; obj* x_117; obj* x_118; 
x_102 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_102, 0, x_5);
x_103 = lean::box(0);
x_104 = l_string_join___closed__1;
lean::inc(x_104);
x_106 = l_lean_parser_monad__parsec_error___at___private_4089500695__finish__comment__block__aux___main___spec__1___rarg(x_104, x_2, x_102, x_103, x_4, x_21, x_14);
x_107 = lean::cnstr_get(x_106, 0);
lean::inc(x_107);
x_109 = lean::cnstr_get(x_106, 1);
lean::inc(x_109);
lean::dec(x_106);
x_112 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_23, x_107);
x_113 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_113);
x_115 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_113, x_112);
x_116 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_115, x_18);
x_117 = l_lean_parser_parsec__t_try__mk__res___rarg(x_116);
if (lean::is_scalar(x_16)) {
 x_118 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_118 = x_16;
}
lean::cnstr_set(x_118, 0, x_117);
lean::cnstr_set(x_118, 1, x_109);
return x_118;
}
}
else
{
obj* x_123; unsigned char x_125; obj* x_126; obj* x_127; obj* x_128; obj* x_129; obj* x_131; obj* x_132; obj* x_133; obj* x_134; 
lean::dec(x_4);
lean::dec(x_5);
lean::dec(x_0);
lean::dec(x_2);
x_123 = lean::cnstr_get(x_12, 0);
lean::inc(x_123);
x_125 = lean::cnstr_get_scalar<unsigned char>(x_12, sizeof(void*)*1);
if (lean::is_shared(x_12)) {
 lean::dec(x_12);
 x_126 = lean::box(0);
} else {
 lean::cnstr_release(x_12, 0);
 x_126 = x_12;
}
if (lean::is_scalar(x_126)) {
 x_127 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_127 = x_126;
}
lean::cnstr_set(x_127, 0, x_123);
lean::cnstr_set_scalar(x_127, sizeof(void*)*1, x_125);
x_128 = x_127;
x_129 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_129);
x_131 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_129, x_128);
x_132 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_131, x_18);
x_133 = l_lean_parser_parsec__t_try__mk__res___rarg(x_132);
if (lean::is_scalar(x_16)) {
 x_134 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_134 = x_16;
}
lean::cnstr_set(x_134, 0, x_133);
lean::cnstr_set(x_134, 1, x_14);
return x_134;
}
}
}
obj* l_list_mfoldl___main___at_lean_parser_level_paren_parser___spec__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_11; obj* x_13; obj* x_14; 
lean::dec(x_4);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_3);
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
x_81 = l_list_mfoldl___main___at_lean_parser_level_paren_parser___spec__3(x_0, x_74, x_17, x_3, x_4, x_76, x_21);
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
lean::dec(x_0);
lean::dec(x_3);
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
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_3);
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
obj* l_lean_parser_combinators_node___at_lean_parser_level_paren_parser___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_8; obj* x_9; obj* x_11; obj* x_13; 
x_6 = lean::box(0);
lean::inc(x_0);
x_8 = l_list_mfoldl___main___at_lean_parser_level_paren_parser___spec__3(x_0, x_6, x_1, x_2, x_3, x_4, x_5);
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
obj* _init_l_lean_parser_level_paren_parser_lean_parser_has__view() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_9; obj* x_10; obj* x_11; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_31; 
x_0 = lean::mk_string("(");
x_1 = l_string_trim(x_0);
lean::inc(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_3, 0, x_1);
x_4 = l_lean_parser_max__prec;
lean::inc(x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_level_paren_parser___spec__1), 7, 3);
lean::closure_set(x_6, 0, x_1);
lean::closure_set(x_6, 1, x_4);
lean::closure_set(x_6, 2, x_3);
x_7 = lean::mk_nat_obj(0u);
lean::inc(x_7);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_level_parser), 5, 1);
lean::closure_set(x_9, 0, x_7);
x_10 = lean::mk_string(")");
x_11 = l_string_trim(x_10);
lean::inc(x_11);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_13, 0, x_11);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_level_paren_parser___spec__1), 7, 3);
lean::closure_set(x_14, 0, x_11);
lean::closure_set(x_14, 1, x_7);
lean::closure_set(x_14, 2, x_13);
x_15 = lean::box(0);
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_15);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_9);
lean::cnstr_set(x_17, 1, x_16);
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_6);
lean::cnstr_set(x_18, 1, x_17);
x_19 = l_lean_parser_level__parser__m_monad;
x_20 = l_lean_parser_level__parser__m_monad__except;
x_21 = l_lean_parser_level__parser__m_lean_parser_monad__parsec;
x_22 = l_lean_parser_level__parser__m_alternative;
x_23 = l_lean_parser_level_paren;
x_24 = l_lean_parser_level_paren_has__view;
lean::inc(x_24);
lean::inc(x_23);
lean::inc(x_22);
lean::inc(x_21);
lean::inc(x_20);
lean::inc(x_19);
x_31 = l_lean_parser_combinators_node_view___rarg(x_19, x_20, x_21, x_22, x_23, x_18, x_24);
return x_31;
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
obj* _init_l_lean_parser_level_leading() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_4, 0, x_2);
lean::cnstr_set(x_4, 1, x_3);
x_5 = lean::mk_string("level");
x_6 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_6, 0, x_4);
lean::cnstr_set(x_6, 1, x_5);
x_7 = lean::mk_string("leading");
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set(x_8, 1, x_7);
return x_8;
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
obj* l_lean_parser_level_leading_has__view_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_4 = l_lean_parser_syntax_as__node___main(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; 
lean::dec(x_4);
x_6 = l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__4;
lean::inc(x_6);
return x_6;
}
else
{
obj* x_8; obj* x_11; obj* x_13; obj* x_16; obj* x_18; 
x_8 = lean::cnstr_get(x_4, 0);
lean::inc(x_8);
lean::dec(x_4);
x_11 = lean::cnstr_get(x_8, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_8, 1);
lean::inc(x_13);
lean::dec(x_8);
x_16 = l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__5;
lean::inc(x_16);
x_18 = l_lean_name_has__dec__eq___main(x_11, x_16);
if (lean::obj_tag(x_18) == 0)
{
obj* x_21; 
lean::dec(x_18);
lean::dec(x_13);
x_21 = l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__4;
lean::inc(x_21);
return x_21;
}
else
{
lean::dec(x_18);
if (lean::obj_tag(x_13) == 0)
{
obj* x_25; 
lean::dec(x_13);
x_25 = l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__4;
lean::inc(x_25);
return x_25;
}
else
{
obj* x_27; obj* x_29; 
x_27 = lean::cnstr_get(x_13, 0);
lean::inc(x_27);
x_29 = lean::cnstr_get(x_13, 1);
lean::inc(x_29);
lean::dec(x_13);
if (lean::obj_tag(x_29) == 0)
{
obj* x_33; 
lean::dec(x_29);
x_33 = l_lean_parser_syntax_as__node___main(x_27);
if (lean::obj_tag(x_33) == 0)
{
obj* x_35; 
lean::dec(x_33);
x_35 = l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__4;
lean::inc(x_35);
return x_35;
}
else
{
obj* x_37; obj* x_40; obj* x_42; 
x_37 = lean::cnstr_get(x_33, 0);
lean::inc(x_37);
lean::dec(x_33);
x_40 = lean::cnstr_get(x_37, 0);
lean::inc(x_40);
x_42 = lean::cnstr_get(x_37, 1);
lean::inc(x_42);
lean::dec(x_37);
switch (lean::obj_tag(x_40)) {
case 0:
{
obj* x_47; 
lean::dec(x_40);
lean::dec(x_42);
x_47 = l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__4;
lean::inc(x_47);
return x_47;
}
case 1:
{
obj* x_51; 
lean::dec(x_40);
lean::dec(x_42);
x_51 = l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__4;
lean::inc(x_51);
return x_51;
}
default:
{
obj* x_53; obj* x_55; obj* x_58; obj* x_59; 
x_53 = lean::cnstr_get(x_40, 0);
lean::inc(x_53);
x_55 = lean::cnstr_get(x_40, 1);
lean::inc(x_55);
lean::dec(x_40);
x_58 = lean::box(0);
x_59 = l_lean_name_has__dec__eq___main(x_53, x_58);
if (lean::obj_tag(x_59) == 0)
{
obj* x_63; 
lean::dec(x_55);
lean::dec(x_42);
lean::dec(x_59);
x_63 = l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__4;
lean::inc(x_63);
return x_63;
}
else
{
lean::dec(x_59);
if (lean::obj_tag(x_42) == 0)
{
obj* x_68; 
lean::dec(x_55);
lean::dec(x_42);
x_68 = l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__4;
lean::inc(x_68);
return x_68;
}
else
{
obj* x_70; obj* x_72; 
x_70 = lean::cnstr_get(x_42, 0);
lean::inc(x_70);
x_72 = lean::cnstr_get(x_42, 1);
lean::inc(x_72);
lean::dec(x_42);
if (lean::obj_tag(x_72) == 0)
{
lean::dec(x_72);
x_1 = x_70;
x_2 = x_55;
goto lbl_3;
}
else
{
obj* x_79; 
lean::dec(x_70);
lean::dec(x_72);
lean::dec(x_55);
x_79 = l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__4;
lean::inc(x_79);
return x_79;
}
}
}
}
}
}
}
else
{
obj* x_83; 
lean::dec(x_29);
lean::dec(x_27);
x_83 = l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__4;
lean::inc(x_83);
return x_83;
}
}
}
}
lbl_3:
{
obj* x_85; obj* x_86; 
x_85 = lean::mk_nat_obj(0u);
x_86 = lean::nat_dec_eq(x_2, x_85);
lean::dec(x_85);
if (lean::obj_tag(x_86) == 0)
{
obj* x_89; obj* x_90; 
lean::dec(x_86);
x_89 = lean::mk_nat_obj(1u);
x_90 = lean::nat_dec_eq(x_2, x_89);
lean::dec(x_89);
if (lean::obj_tag(x_90) == 0)
{
obj* x_93; obj* x_94; 
lean::dec(x_90);
x_93 = lean::mk_nat_obj(2u);
x_94 = lean::nat_dec_eq(x_2, x_93);
lean::dec(x_93);
if (lean::obj_tag(x_94) == 0)
{
obj* x_97; obj* x_98; 
lean::dec(x_94);
x_97 = lean::mk_nat_obj(3u);
x_98 = lean::nat_dec_eq(x_2, x_97);
lean::dec(x_97);
if (lean::obj_tag(x_98) == 0)
{
obj* x_101; obj* x_102; 
lean::dec(x_98);
x_101 = lean::mk_nat_obj(4u);
x_102 = lean::nat_dec_eq(x_2, x_101);
lean::dec(x_101);
lean::dec(x_2);
if (lean::obj_tag(x_102) == 0)
{
lean::dec(x_102);
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_107; 
lean::dec(x_1);
x_107 = l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__2;
lean::inc(x_107);
return x_107;
}
case 1:
{
obj* x_109; obj* x_112; 
x_109 = lean::cnstr_get(x_1, 0);
lean::inc(x_109);
lean::dec(x_1);
x_112 = lean::alloc_cnstr(5, 1, 0);
lean::cnstr_set(x_112, 0, x_109);
return x_112;
}
case 2:
{
obj* x_114; 
lean::dec(x_1);
x_114 = l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__2;
lean::inc(x_114);
return x_114;
}
default:
{
obj* x_117; 
lean::dec(x_1);
x_117 = l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__2;
lean::inc(x_117);
return x_117;
}
}
}
else
{
obj* x_120; obj* x_121; obj* x_123; obj* x_124; 
lean::dec(x_102);
x_120 = l_lean_parser_number_has__view;
x_121 = lean::cnstr_get(x_120, 0);
lean::inc(x_121);
x_123 = lean::apply_1(x_121, x_1);
x_124 = lean::alloc_cnstr(4, 1, 0);
lean::cnstr_set(x_124, 0, x_123);
return x_124;
}
}
else
{
obj* x_127; obj* x_128; obj* x_130; obj* x_131; 
lean::dec(x_98);
lean::dec(x_2);
x_127 = l_lean_parser_level_paren_has__view;
x_128 = lean::cnstr_get(x_127, 0);
lean::inc(x_128);
x_130 = lean::apply_1(x_128, x_1);
x_131 = lean::alloc_cnstr(3, 1, 0);
lean::cnstr_set(x_131, 0, x_130);
return x_131;
}
}
else
{
lean::dec(x_94);
lean::dec(x_2);
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_134; obj* x_137; obj* x_138; 
x_134 = lean::cnstr_get(x_1, 0);
lean::inc(x_134);
lean::dec(x_1);
x_137 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_137, 0, x_134);
x_138 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_138, 0, x_137);
return x_138;
}
case 1:
{
obj* x_140; 
lean::dec(x_1);
x_140 = l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__3;
lean::inc(x_140);
return x_140;
}
case 2:
{
obj* x_143; 
lean::dec(x_1);
x_143 = l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__3;
lean::inc(x_143);
return x_143;
}
default:
{
obj* x_146; 
lean::dec(x_1);
x_146 = l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__3;
lean::inc(x_146);
return x_146;
}
}
}
}
else
{
obj* x_150; 
lean::dec(x_90);
lean::dec(x_2);
x_150 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_150, 0, x_1);
return x_150;
}
}
else
{
obj* x_153; 
lean::dec(x_86);
lean::dec(x_2);
x_153 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_153, 0, x_1);
return x_153;
}
}
}
}
obj* _init_l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_5; obj* x_8; obj* x_9; 
x_0 = lean::box(0);
x_1 = lean::mk_string("NOT_AN_IDENT");
lean::inc(x_1);
x_3 = l_lean_parser_substring_of__string(x_1);
lean::inc(x_0);
x_5 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_5, 0, x_0);
lean::cnstr_set(x_5, 1, x_1);
lean::inc(x_0);
lean::inc(x_0);
x_8 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_8, 0, x_0);
lean::cnstr_set(x_8, 1, x_3);
lean::cnstr_set(x_8, 2, x_5);
lean::cnstr_set(x_8, 3, x_0);
lean::cnstr_set(x_8, 4, x_0);
x_9 = lean::alloc_cnstr(5, 1, 0);
lean::cnstr_set(x_9, 0, x_8);
return x_9;
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
obj* x_5; obj* x_6; 
x_5 = lean::mk_nat_obj(0u);
x_6 = lean::nat_dec_eq(x_1, x_5);
lean::dec(x_5);
if (lean::obj_tag(x_6) == 0)
{
obj* x_9; obj* x_10; 
lean::dec(x_6);
x_9 = lean::mk_nat_obj(1u);
x_10 = lean::nat_dec_eq(x_1, x_9);
lean::dec(x_9);
if (lean::obj_tag(x_10) == 0)
{
obj* x_13; obj* x_14; 
lean::dec(x_10);
x_13 = lean::mk_nat_obj(2u);
x_14 = lean::nat_dec_eq(x_1, x_13);
lean::dec(x_13);
if (lean::obj_tag(x_14) == 0)
{
obj* x_17; obj* x_18; 
lean::dec(x_14);
x_17 = lean::mk_nat_obj(3u);
x_18 = lean::nat_dec_eq(x_1, x_17);
lean::dec(x_17);
if (lean::obj_tag(x_18) == 0)
{
obj* x_21; obj* x_22; 
lean::dec(x_18);
x_21 = lean::mk_nat_obj(4u);
x_22 = lean::nat_dec_eq(x_1, x_21);
lean::dec(x_21);
lean::dec(x_1);
if (lean::obj_tag(x_22) == 0)
{
lean::dec(x_22);
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_27; 
lean::dec(x_0);
x_27 = l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__2;
lean::inc(x_27);
return x_27;
}
case 1:
{
obj* x_29; obj* x_32; 
x_29 = lean::cnstr_get(x_0, 0);
lean::inc(x_29);
lean::dec(x_0);
x_32 = lean::alloc_cnstr(5, 1, 0);
lean::cnstr_set(x_32, 0, x_29);
return x_32;
}
case 2:
{
obj* x_34; 
lean::dec(x_0);
x_34 = l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__2;
lean::inc(x_34);
return x_34;
}
default:
{
obj* x_37; 
lean::dec(x_0);
x_37 = l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__2;
lean::inc(x_37);
return x_37;
}
}
}
else
{
obj* x_40; obj* x_41; obj* x_43; obj* x_44; 
lean::dec(x_22);
x_40 = l_lean_parser_number_has__view;
x_41 = lean::cnstr_get(x_40, 0);
lean::inc(x_41);
x_43 = lean::apply_1(x_41, x_0);
x_44 = lean::alloc_cnstr(4, 1, 0);
lean::cnstr_set(x_44, 0, x_43);
return x_44;
}
}
else
{
obj* x_47; obj* x_48; obj* x_50; obj* x_51; 
lean::dec(x_1);
lean::dec(x_18);
x_47 = l_lean_parser_level_paren_has__view;
x_48 = lean::cnstr_get(x_47, 0);
lean::inc(x_48);
x_50 = lean::apply_1(x_48, x_0);
x_51 = lean::alloc_cnstr(3, 1, 0);
lean::cnstr_set(x_51, 0, x_50);
return x_51;
}
}
else
{
lean::dec(x_14);
lean::dec(x_1);
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_54; obj* x_57; obj* x_58; 
x_54 = lean::cnstr_get(x_0, 0);
lean::inc(x_54);
lean::dec(x_0);
x_57 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_57, 0, x_54);
x_58 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_58, 0, x_57);
return x_58;
}
case 1:
{
obj* x_60; 
lean::dec(x_0);
x_60 = l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__3;
lean::inc(x_60);
return x_60;
}
case 2:
{
obj* x_63; 
lean::dec(x_0);
x_63 = l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__3;
lean::inc(x_63);
return x_63;
}
default:
{
obj* x_66; 
lean::dec(x_0);
x_66 = l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__3;
lean::inc(x_66);
return x_66;
}
}
}
}
else
{
obj* x_70; 
lean::dec(x_10);
lean::dec(x_1);
x_70 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_70, 0, x_0);
return x_70;
}
}
else
{
obj* x_73; 
lean::dec(x_1);
lean::dec(x_6);
x_73 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_73, 0, x_0);
return x_73;
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
x_2 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_4, 0, x_2);
lean::cnstr_set(x_4, 1, x_3);
x_5 = lean::mk_string("level");
x_6 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_6, 0, x_4);
lean::cnstr_set(x_6, 1, x_5);
x_7 = lean::mk_string("leading");
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set(x_8, 1, x_7);
return x_8;
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
obj* x_2; obj* x_6; obj* x_7; obj* x_9; obj* x_10; obj* x_11; obj* x_13; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
lean::inc(x_1);
x_6 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_6, 0, x_2);
lean::cnstr_set(x_6, 1, x_1);
x_7 = l_lean_parser_detail__ident__part_has__view_x_27___lambda__2___closed__1;
lean::inc(x_7);
x_9 = l_lean_parser_syntax_mk__node(x_7, x_6);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_1);
x_11 = l_lean_parser_level_leading;
lean::inc(x_11);
x_13 = l_lean_parser_syntax_mk__node(x_11, x_10);
return x_13;
}
case 1:
{
obj* x_14; obj* x_18; obj* x_19; obj* x_21; obj* x_22; obj* x_23; obj* x_25; 
x_14 = lean::cnstr_get(x_0, 0);
lean::inc(x_14);
lean::dec(x_0);
lean::inc(x_1);
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_14);
lean::cnstr_set(x_18, 1, x_1);
x_19 = l_lean_parser_detail__ident__part_has__view_x_27___lambda__2___closed__2;
lean::inc(x_19);
x_21 = l_lean_parser_syntax_mk__node(x_19, x_18);
x_22 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_1);
x_23 = l_lean_parser_level_leading;
lean::inc(x_23);
x_25 = l_lean_parser_syntax_mk__node(x_23, x_22);
return x_25;
}
case 2:
{
obj* x_26; obj* x_29; obj* x_31; obj* x_32; obj* x_33; obj* x_35; obj* x_36; obj* x_38; obj* x_39; obj* x_40; obj* x_42; 
x_26 = lean::cnstr_get(x_0, 0);
lean::inc(x_26);
lean::dec(x_0);
x_29 = l_lean_parser_raw_view___rarg___lambda__3___closed__1;
lean::inc(x_29);
x_31 = l_option_map___rarg(x_29, x_26);
x_32 = lean::box(3);
x_33 = l_option_get__or__else___main___rarg(x_31, x_32);
lean::inc(x_1);
x_35 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_35, 0, x_33);
lean::cnstr_set(x_35, 1, x_1);
x_36 = l_lean_parser_number_has__view_x_27___lambda__2___closed__1;
lean::inc(x_36);
x_38 = l_lean_parser_syntax_mk__node(x_36, x_35);
x_39 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_39, 0, x_38);
lean::cnstr_set(x_39, 1, x_1);
x_40 = l_lean_parser_level_leading;
lean::inc(x_40);
x_42 = l_lean_parser_syntax_mk__node(x_40, x_39);
return x_42;
}
case 3:
{
obj* x_43; obj* x_46; obj* x_47; obj* x_49; obj* x_51; obj* x_52; obj* x_54; obj* x_55; obj* x_56; obj* x_58; 
x_43 = lean::cnstr_get(x_0, 0);
lean::inc(x_43);
lean::dec(x_0);
x_46 = l_lean_parser_level_paren_has__view;
x_47 = lean::cnstr_get(x_46, 1);
lean::inc(x_47);
x_49 = lean::apply_1(x_47, x_43);
lean::inc(x_1);
x_51 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_51, 0, x_49);
lean::cnstr_set(x_51, 1, x_1);
x_52 = l_lean_parser_number_has__view_x_27___lambda__2___closed__2;
lean::inc(x_52);
x_54 = l_lean_parser_syntax_mk__node(x_52, x_51);
x_55 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_55, 0, x_54);
lean::cnstr_set(x_55, 1, x_1);
x_56 = l_lean_parser_level_leading;
lean::inc(x_56);
x_58 = l_lean_parser_syntax_mk__node(x_56, x_55);
return x_58;
}
case 4:
{
obj* x_59; obj* x_62; obj* x_63; obj* x_65; obj* x_67; obj* x_68; obj* x_70; obj* x_71; obj* x_72; obj* x_74; 
x_59 = lean::cnstr_get(x_0, 0);
lean::inc(x_59);
lean::dec(x_0);
x_62 = l_lean_parser_number_has__view;
x_63 = lean::cnstr_get(x_62, 1);
lean::inc(x_63);
x_65 = lean::apply_1(x_63, x_59);
lean::inc(x_1);
x_67 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_67, 0, x_65);
lean::cnstr_set(x_67, 1, x_1);
x_68 = l_lean_parser_level_leading_has__view_x_27___lambda__2___closed__1;
lean::inc(x_68);
x_70 = l_lean_parser_syntax_mk__node(x_68, x_67);
x_71 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_71, 0, x_70);
lean::cnstr_set(x_71, 1, x_1);
x_72 = l_lean_parser_level_leading;
lean::inc(x_72);
x_74 = l_lean_parser_syntax_mk__node(x_72, x_71);
return x_74;
}
default:
{
obj* x_75; obj* x_78; obj* x_80; obj* x_81; obj* x_83; obj* x_84; obj* x_85; obj* x_87; 
x_75 = lean::cnstr_get(x_0, 0);
lean::inc(x_75);
lean::dec(x_0);
x_78 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_78, 0, x_75);
lean::inc(x_1);
x_80 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_80, 0, x_78);
lean::cnstr_set(x_80, 1, x_1);
x_81 = l_lean_parser_level_leading_has__view_x_27___lambda__2___closed__2;
lean::inc(x_81);
x_83 = l_lean_parser_syntax_mk__node(x_81, x_80);
x_84 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_84, 0, x_83);
lean::cnstr_set(x_84, 1, x_1);
x_85 = l_lean_parser_level_leading;
lean::inc(x_85);
x_87 = l_lean_parser_syntax_mk__node(x_85, x_84);
return x_87;
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
x_2 = lean::alloc_cnstr(2, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_lean_parser_level_leading_has__view_x_27___lambda__2___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_nat_obj(5u);
x_2 = lean::alloc_cnstr(2, 2, 0);
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
obj* l_lean_parser_level_leading_parser(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_8; 
x_4 = l_lean_parser_level_leading;
x_5 = l_lean_parser_level_leading_parser___closed__1;
lean::inc(x_5);
lean::inc(x_4);
x_8 = l_lean_parser_combinators_node___at_lean_parser_level_paren_parser___spec__2(x_4, x_5, x_0, x_1, x_2, x_3);
return x_8;
}
}
obj* _init_l_lean_parser_level_leading_parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_7; obj* x_8; obj* x_10; obj* x_11; obj* x_12; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_0 = lean::mk_string("max");
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__or__ident___at_lean_parser_level_leading_parser___spec__1), 5, 1);
lean::closure_set(x_1, 0, x_0);
x_2 = lean::mk_string("imax");
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__or__ident___at_lean_parser_level_leading_parser___spec__1), 5, 1);
lean::closure_set(x_3, 0, x_2);
x_4 = lean::mk_string("_");
x_5 = l_string_trim(x_4);
lean::inc(x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_7, 0, x_5);
x_8 = l_lean_parser_max__prec;
lean::inc(x_8);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_level_paren_parser___spec__1), 7, 3);
lean::closure_set(x_10, 0, x_5);
lean::closure_set(x_10, 1, x_8);
lean::closure_set(x_10, 2, x_7);
x_11 = lean::box(0);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_ident_parser___at_lean_parser_level_leading_parser___spec__3), 1, 0);
lean::inc(x_11);
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_12);
lean::cnstr_set(x_14, 1, x_11);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_number_parser___at_lean_parser_level_leading_parser___spec__2), 1, 0);
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_15);
lean::cnstr_set(x_16, 1, x_14);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_level_paren_parser), 4, 0);
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_16);
x_19 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_19, 0, x_10);
lean::cnstr_set(x_19, 1, x_18);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_3);
lean::cnstr_set(x_20, 1, x_19);
x_21 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_21, 0, x_1);
lean::cnstr_set(x_21, 1, x_20);
x_22 = lean::mk_nat_obj(0u);
x_23 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_choice__aux___main___at_lean_parser_level_leading_parser___spec__4), 6, 2);
lean::closure_set(x_23, 0, x_21);
lean::closure_set(x_23, 1, x_22);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_11);
return x_24;
}
}
obj* l_lean_parser_symbol__or__ident___at_lean_parser_level_leading_parser___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
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
case 2:
{
obj* x_36; 
x_36 = lean::box(0);
x_21 = x_36;
goto lbl_22;
}
default:
{
obj* x_37; 
x_37 = lean::box(0);
x_21 = x_37;
goto lbl_22;
}
}
lbl_22:
{
obj* x_38; 
if (lean::obj_tag(x_21) == 0)
{
obj* x_41; 
lean::dec(x_21);
x_41 = lean::box(1);
x_38 = x_41;
goto lbl_39;
}
else
{
obj* x_42; obj* x_45; 
x_42 = lean::cnstr_get(x_21, 0);
lean::inc(x_42);
lean::dec(x_21);
x_45 = lean::string_dec_eq(x_42, x_0);
lean::dec(x_42);
if (lean::obj_tag(x_45) == 0)
{
obj* x_48; 
lean::dec(x_45);
x_48 = lean::box(1);
x_38 = x_48;
goto lbl_39;
}
else
{
obj* x_50; 
lean::dec(x_45);
x_50 = lean::box(0);
x_38 = x_50;
goto lbl_39;
}
}
lbl_39:
{
if (lean::obj_tag(x_38) == 0)
{
obj* x_55; obj* x_57; obj* x_58; obj* x_59; obj* x_61; obj* x_62; obj* x_63; 
lean::dec(x_38);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_3);
x_55 = l_lean_parser_finish__comment__block___closed__2;
lean::inc(x_55);
if (lean::is_scalar(x_20)) {
 x_57 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_57 = x_20;
}
lean::cnstr_set(x_57, 0, x_14);
lean::cnstr_set(x_57, 1, x_16);
lean::cnstr_set(x_57, 2, x_55);
x_58 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_18, x_57);
x_59 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_59);
x_61 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_59, x_58);
x_62 = l_lean_parser_parsec__t_try__mk__res___rarg(x_61);
if (lean::is_scalar(x_13)) {
 x_63 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_63 = x_13;
}
lean::cnstr_set(x_63, 0, x_62);
lean::cnstr_set(x_63, 1, x_11);
return x_63;
}
else
{
obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_71; obj* x_72; obj* x_74; 
lean::dec(x_38);
x_65 = l_string_quote(x_0);
x_66 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_66, 0, x_65);
x_67 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_67, 0, x_3);
x_68 = lean::box(0);
x_69 = l_string_join___closed__1;
lean::inc(x_69);
x_71 = l_lean_parser_monad__parsec_error___at___private_4089500695__finish__comment__block__aux___main___spec__1___rarg(x_69, x_66, x_67, x_68, x_2, x_16, x_11);
x_72 = lean::cnstr_get(x_71, 0);
lean::inc(x_72);
x_74 = lean::cnstr_get(x_71, 1);
lean::inc(x_74);
lean::dec(x_71);
if (lean::obj_tag(x_72) == 0)
{
obj* x_77; obj* x_79; obj* x_82; obj* x_84; obj* x_85; obj* x_86; obj* x_88; obj* x_89; obj* x_90; 
x_77 = lean::cnstr_get(x_72, 1);
lean::inc(x_77);
x_79 = lean::cnstr_get(x_72, 2);
lean::inc(x_79);
lean::dec(x_72);
x_82 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_82);
if (lean::is_scalar(x_20)) {
 x_84 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_84 = x_20;
}
lean::cnstr_set(x_84, 0, x_14);
lean::cnstr_set(x_84, 1, x_77);
lean::cnstr_set(x_84, 2, x_82);
x_85 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_79, x_84);
x_86 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_18, x_85);
lean::inc(x_82);
x_88 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_82, x_86);
x_89 = l_lean_parser_parsec__t_try__mk__res___rarg(x_88);
if (lean::is_scalar(x_13)) {
 x_90 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_90 = x_13;
}
lean::cnstr_set(x_90, 0, x_89);
lean::cnstr_set(x_90, 1, x_74);
return x_90;
}
else
{
obj* x_93; unsigned char x_95; obj* x_96; obj* x_97; obj* x_98; obj* x_99; obj* x_100; obj* x_102; obj* x_103; obj* x_104; 
lean::dec(x_14);
lean::dec(x_20);
x_93 = lean::cnstr_get(x_72, 0);
lean::inc(x_93);
x_95 = lean::cnstr_get_scalar<unsigned char>(x_72, sizeof(void*)*1);
if (lean::is_shared(x_72)) {
 lean::dec(x_72);
 x_96 = lean::box(0);
} else {
 lean::cnstr_release(x_72, 0);
 x_96 = x_72;
}
if (lean::is_scalar(x_96)) {
 x_97 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_97 = x_96;
}
lean::cnstr_set(x_97, 0, x_93);
lean::cnstr_set_scalar(x_97, sizeof(void*)*1, x_95);
x_98 = x_97;
x_99 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_18, x_98);
x_100 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_100);
x_102 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_100, x_99);
x_103 = l_lean_parser_parsec__t_try__mk__res___rarg(x_102);
if (lean::is_scalar(x_13)) {
 x_104 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_104 = x_13;
}
lean::cnstr_set(x_104, 0, x_103);
lean::cnstr_set(x_104, 1, x_74);
return x_104;
}
}
}
}
}
else
{
obj* x_108; unsigned char x_110; obj* x_111; obj* x_112; obj* x_113; obj* x_114; obj* x_116; obj* x_117; obj* x_118; 
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_3);
x_108 = lean::cnstr_get(x_9, 0);
lean::inc(x_108);
x_110 = lean::cnstr_get_scalar<unsigned char>(x_9, sizeof(void*)*1);
if (lean::is_shared(x_9)) {
 lean::dec(x_9);
 x_111 = lean::box(0);
} else {
 lean::cnstr_release(x_9, 0);
 x_111 = x_9;
}
if (lean::is_scalar(x_111)) {
 x_112 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_112 = x_111;
}
lean::cnstr_set(x_112, 0, x_108);
lean::cnstr_set_scalar(x_112, sizeof(void*)*1, x_110);
x_113 = x_112;
x_114 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_114);
x_116 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_114, x_113);
x_117 = l_lean_parser_parsec__t_try__mk__res___rarg(x_116);
if (lean::is_scalar(x_13)) {
 x_118 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_118 = x_13;
}
lean::cnstr_set(x_118, 0, x_117);
lean::cnstr_set(x_118, 1, x_11);
return x_118;
}
}
}
obj* l_lean_parser_number_parser___at_lean_parser_level_leading_parser___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2) {
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
obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_29; obj* x_30; obj* x_32; obj* x_35; obj* x_37; obj* x_38; obj* x_40; obj* x_42; obj* x_43; obj* x_44; 
lean::dec(x_17);
lean::dec(x_19);
lean::dec(x_11);
x_23 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_23, 0, x_1);
x_24 = lean::box(0);
x_25 = l_string_join___closed__1;
x_26 = l_lean_parser_number_parser___at_lean_parser_level_leading_parser___spec__2___rarg___closed__1;
lean::inc(x_26);
lean::inc(x_25);
x_29 = l_lean_parser_monad__parsec_error___at___private_4089500695__finish__comment__block__aux___main___spec__1___rarg(x_25, x_26, x_23, x_24, x_0, x_13, x_8);
x_30 = lean::cnstr_get(x_29, 0);
lean::inc(x_30);
x_32 = lean::cnstr_get(x_29, 1);
lean::inc(x_32);
lean::dec(x_29);
x_35 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_35);
x_37 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_35, x_30);
x_38 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_37);
lean::inc(x_35);
x_40 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_35, x_38);
lean::inc(x_26);
x_42 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_40, x_26);
x_43 = l_lean_parser_parsec__t_try__mk__res___rarg(x_42);
if (lean::is_scalar(x_10)) {
 x_44 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_44 = x_10;
}
lean::cnstr_set(x_44, 0, x_43);
lean::cnstr_set(x_44, 1, x_32);
return x_44;
}
else
{
obj* x_48; obj* x_50; obj* x_51; obj* x_52; obj* x_54; obj* x_55; obj* x_57; obj* x_58; obj* x_59; 
lean::dec(x_19);
lean::dec(x_0);
lean::dec(x_1);
x_48 = l_lean_parser_finish__comment__block___closed__2;
lean::inc(x_48);
if (lean::is_scalar(x_17)) {
 x_50 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_50 = x_17;
}
lean::cnstr_set(x_50, 0, x_11);
lean::cnstr_set(x_50, 1, x_13);
lean::cnstr_set(x_50, 2, x_48);
x_51 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_50);
x_52 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_52);
x_54 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_52, x_51);
x_55 = l_lean_parser_number_parser___at_lean_parser_level_leading_parser___spec__2___rarg___closed__1;
lean::inc(x_55);
x_57 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_54, x_55);
x_58 = l_lean_parser_parsec__t_try__mk__res___rarg(x_57);
if (lean::is_scalar(x_10)) {
 x_59 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_59 = x_10;
}
lean::cnstr_set(x_59, 0, x_58);
lean::cnstr_set(x_59, 1, x_8);
return x_59;
}
}
else
{
obj* x_62; unsigned char x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_70; obj* x_71; obj* x_73; obj* x_74; obj* x_75; 
lean::dec(x_0);
lean::dec(x_1);
x_62 = lean::cnstr_get(x_6, 0);
lean::inc(x_62);
x_64 = lean::cnstr_get_scalar<unsigned char>(x_6, sizeof(void*)*1);
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
x_71 = l_lean_parser_number_parser___at_lean_parser_level_leading_parser___spec__2___rarg___closed__1;
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
obj* _init_l_lean_parser_number_parser___at_lean_parser_level_leading_parser___spec__2___rarg___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("number");
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_lean_parser_number_parser___at_lean_parser_level_leading_parser___spec__2(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_number_parser___at_lean_parser_level_leading_parser___spec__2___rarg), 3, 0);
return x_2;
}
}
obj* l_lean_parser_ident_parser___at_lean_parser_level_leading_parser___spec__3___rarg(obj* x_0, obj* x_1, obj* x_2) {
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
obj* x_11; obj* x_13; obj* x_15; obj* x_17; unsigned char x_18; 
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
unsigned char x_22; 
lean::dec(x_17);
lean::dec(x_11);
x_22 = 0;
x_18 = x_22;
goto lbl_19;
}
case 1:
{
obj* x_26; obj* x_28; obj* x_29; obj* x_31; obj* x_32; obj* x_34; obj* x_35; obj* x_36; 
lean::dec(x_10);
lean::dec(x_0);
lean::dec(x_1);
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
x_32 = l_lean_parser_ident_parser___at_lean_parser_level_leading_parser___spec__3___rarg___closed__1;
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
unsigned char x_39; 
lean::dec(x_17);
lean::dec(x_11);
x_39 = 0;
x_18 = x_39;
goto lbl_19;
}
default:
{
unsigned char x_42; 
lean::dec(x_17);
lean::dec(x_11);
x_42 = 0;
x_18 = x_42;
goto lbl_19;
}
}
lbl_19:
{
obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_49; obj* x_50; obj* x_52; obj* x_55; obj* x_56; obj* x_58; obj* x_60; obj* x_61; obj* x_62; 
x_43 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_43, 0, x_1);
x_44 = lean::box(0);
x_45 = l_string_join___closed__1;
x_46 = l_lean_parser_ident_parser___at_lean_parser_level_leading_parser___spec__3___rarg___closed__1;
lean::inc(x_46);
lean::inc(x_45);
x_49 = l_lean_parser_monad__parsec_error___at___private_4089500695__finish__comment__block__aux___main___spec__1___rarg(x_45, x_46, x_43, x_44, x_0, x_13, x_8);
x_50 = lean::cnstr_get(x_49, 0);
lean::inc(x_50);
x_52 = lean::cnstr_get(x_49, 1);
lean::inc(x_52);
lean::dec(x_49);
x_55 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_50);
x_56 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_56);
x_58 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_56, x_55);
lean::inc(x_46);
x_60 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_58, x_46);
x_61 = l_lean_parser_parsec__t_try__mk__res___rarg(x_60);
if (lean::is_scalar(x_10)) {
 x_62 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_62 = x_10;
}
lean::cnstr_set(x_62, 0, x_61);
lean::cnstr_set(x_62, 1, x_52);
return x_62;
}
}
else
{
obj* x_65; unsigned char x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_73; obj* x_74; obj* x_76; obj* x_77; obj* x_78; 
lean::dec(x_0);
lean::dec(x_1);
x_65 = lean::cnstr_get(x_6, 0);
lean::inc(x_65);
x_67 = lean::cnstr_get_scalar<unsigned char>(x_6, sizeof(void*)*1);
if (lean::is_shared(x_6)) {
 lean::dec(x_6);
 x_68 = lean::box(0);
} else {
 lean::cnstr_release(x_6, 0);
 x_68 = x_6;
}
if (lean::is_scalar(x_68)) {
 x_69 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_69 = x_68;
}
lean::cnstr_set(x_69, 0, x_65);
lean::cnstr_set_scalar(x_69, sizeof(void*)*1, x_67);
x_70 = x_69;
x_71 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_71);
x_73 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_71, x_70);
x_74 = l_lean_parser_ident_parser___at_lean_parser_level_leading_parser___spec__3___rarg___closed__1;
lean::inc(x_74);
x_76 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_73, x_74);
x_77 = l_lean_parser_parsec__t_try__mk__res___rarg(x_76);
if (lean::is_scalar(x_10)) {
 x_78 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_78 = x_10;
}
lean::cnstr_set(x_78, 0, x_77);
lean::cnstr_set(x_78, 1, x_8);
return x_78;
}
}
}
obj* _init_l_lean_parser_ident_parser___at_lean_parser_level_leading_parser___spec__3___rarg___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("identifier");
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_lean_parser_ident_parser___at_lean_parser_level_leading_parser___spec__3(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_ident_parser___at_lean_parser_level_leading_parser___spec__3___rarg), 3, 0);
return x_2;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_level_leading_parser___spec__5___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
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
obj* l_lean_parser_monad__parsec_error___at_lean_parser_level_leading_parser___spec__5(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___at_lean_parser_level_leading_parser___spec__5___rarg), 8, 0);
return x_2;
}
}
obj* l_lean_parser_combinators_choice__aux___main___at_lean_parser_level_leading_parser___spec__4(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_14; 
lean::dec(x_0);
lean::dec(x_1);
x_8 = lean::box(0);
x_9 = l_lean_parser_combinators_choice__aux___main___rarg___closed__1;
x_10 = l_mjoin___rarg___closed__1;
lean::inc(x_8);
lean::inc(x_10);
lean::inc(x_9);
x_14 = l_lean_parser_monad__parsec_error___at_lean_parser_level_leading_parser___spec__5___rarg(x_9, x_10, x_8, x_8, x_2, x_3, x_4, x_5);
return x_14;
}
else
{
obj* x_15; obj* x_17; obj* x_19; obj* x_23; obj* x_24; obj* x_26; obj* x_28; obj* x_29; obj* x_30; 
x_15 = lean::cnstr_get(x_0, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_0, 1);
lean::inc(x_17);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_19 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_19 = x_0;
}
lean::inc(x_4);
lean::inc(x_3);
lean::inc(x_2);
x_23 = lean::apply_4(x_15, x_2, x_3, x_4, x_5);
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
lean::dec(x_29);
if (lean::obj_tag(x_24) == 0)
{
obj* x_32; obj* x_34; obj* x_36; obj* x_38; obj* x_39; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_46; obj* x_47; 
x_32 = lean::cnstr_get(x_24, 0);
lean::inc(x_32);
x_34 = lean::cnstr_get(x_24, 1);
lean::inc(x_34);
x_36 = lean::cnstr_get(x_24, 2);
lean::inc(x_36);
if (lean::is_shared(x_24)) {
 lean::dec(x_24);
 x_38 = lean::box(0);
} else {
 lean::cnstr_release(x_24, 0);
 lean::cnstr_release(x_24, 1);
 lean::cnstr_release(x_24, 2);
 x_38 = x_24;
}
x_39 = lean::box(0);
lean::inc(x_39);
x_41 = lean::alloc_cnstr(2, 2, 0);
lean::cnstr_set(x_41, 0, x_39);
lean::cnstr_set(x_41, 1, x_1);
if (lean::is_scalar(x_19)) {
 x_42 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_42 = x_19;
}
lean::cnstr_set(x_42, 0, x_32);
lean::cnstr_set(x_42, 1, x_39);
x_43 = l_lean_parser_syntax_mk__node(x_41, x_42);
x_44 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_44);
if (lean::is_scalar(x_38)) {
 x_46 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_46 = x_38;
}
lean::cnstr_set(x_46, 0, x_43);
lean::cnstr_set(x_46, 1, x_34);
lean::cnstr_set(x_46, 2, x_44);
x_47 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_36, x_46);
if (lean::obj_tag(x_47) == 0)
{
obj* x_53; 
lean::dec(x_4);
lean::dec(x_2);
lean::dec(x_3);
lean::dec(x_17);
lean::dec(x_30);
if (lean::is_scalar(x_28)) {
 x_53 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_53 = x_28;
}
lean::cnstr_set(x_53, 0, x_47);
lean::cnstr_set(x_53, 1, x_26);
return x_53;
}
else
{
obj* x_54; unsigned char x_56; 
x_54 = lean::cnstr_get(x_47, 0);
lean::inc(x_54);
x_56 = lean::cnstr_get_scalar<unsigned char>(x_47, sizeof(void*)*1);
if (x_56 == 0)
{
obj* x_58; obj* x_59; obj* x_61; obj* x_64; obj* x_65; 
lean::dec(x_47);
x_58 = l_lean_parser_combinators_choice__aux___main___at_lean_parser_level_leading_parser___spec__4(x_17, x_30, x_2, x_3, x_4, x_26);
x_59 = lean::cnstr_get(x_58, 0);
lean::inc(x_59);
x_61 = lean::cnstr_get(x_58, 1);
lean::inc(x_61);
lean::dec(x_58);
x_64 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_54, x_59);
if (lean::is_scalar(x_28)) {
 x_65 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_65 = x_28;
}
lean::cnstr_set(x_65, 0, x_64);
lean::cnstr_set(x_65, 1, x_61);
return x_65;
}
else
{
obj* x_72; 
lean::dec(x_54);
lean::dec(x_4);
lean::dec(x_2);
lean::dec(x_3);
lean::dec(x_17);
lean::dec(x_30);
if (lean::is_scalar(x_28)) {
 x_72 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_72 = x_28;
}
lean::cnstr_set(x_72, 0, x_47);
lean::cnstr_set(x_72, 1, x_26);
return x_72;
}
}
}
else
{
obj* x_75; unsigned char x_77; obj* x_78; 
lean::dec(x_19);
lean::dec(x_1);
x_75 = lean::cnstr_get(x_24, 0);
lean::inc(x_75);
x_77 = lean::cnstr_get_scalar<unsigned char>(x_24, sizeof(void*)*1);
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
x_80 = l_lean_parser_combinators_choice__aux___main___at_lean_parser_level_leading_parser___spec__4(x_17, x_30, x_2, x_3, x_4, x_26);
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
obj* x_93; obj* x_94; obj* x_95; 
lean::dec(x_4);
lean::dec(x_2);
lean::dec(x_3);
lean::dec(x_17);
lean::dec(x_30);
if (lean::is_scalar(x_78)) {
 x_93 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_93 = x_78;
}
lean::cnstr_set(x_93, 0, x_75);
lean::cnstr_set_scalar(x_93, sizeof(void*)*1, x_77);
x_94 = x_93;
if (lean::is_scalar(x_28)) {
 x_95 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_95 = x_28;
}
lean::cnstr_set(x_95, 0, x_94);
lean::cnstr_set(x_95, 1, x_26);
return x_95;
}
}
}
}
}
obj* _init_l_lean_parser_level_leading_parser_lean_parser_has__view() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_7; obj* x_8; obj* x_10; obj* x_11; obj* x_12; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_37; 
x_0 = lean::mk_string("max");
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__or__ident___at_lean_parser_level_leading_parser___spec__1), 5, 1);
lean::closure_set(x_1, 0, x_0);
x_2 = lean::mk_string("imax");
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__or__ident___at_lean_parser_level_leading_parser___spec__1), 5, 1);
lean::closure_set(x_3, 0, x_2);
x_4 = lean::mk_string("_");
x_5 = l_string_trim(x_4);
lean::inc(x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_dlist_singleton___rarg), 2, 1);
lean::closure_set(x_7, 0, x_5);
x_8 = l_lean_parser_max__prec;
lean::inc(x_8);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_level_paren_parser___spec__1), 7, 3);
lean::closure_set(x_10, 0, x_5);
lean::closure_set(x_10, 1, x_8);
lean::closure_set(x_10, 2, x_7);
x_11 = lean::box(0);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_ident_parser___at_lean_parser_level_leading_parser___spec__3), 1, 0);
lean::inc(x_11);
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_12);
lean::cnstr_set(x_14, 1, x_11);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_number_parser___at_lean_parser_level_leading_parser___spec__2), 1, 0);
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_15);
lean::cnstr_set(x_16, 1, x_14);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_level_paren_parser), 4, 0);
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_16);
x_19 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_19, 0, x_10);
lean::cnstr_set(x_19, 1, x_18);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_3);
lean::cnstr_set(x_20, 1, x_19);
x_21 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_21, 0, x_1);
lean::cnstr_set(x_21, 1, x_20);
x_22 = lean::mk_nat_obj(0u);
x_23 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_choice__aux___main___at_lean_parser_level_leading_parser___spec__4), 6, 2);
lean::closure_set(x_23, 0, x_21);
lean::closure_set(x_23, 1, x_22);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_11);
x_25 = l_lean_parser_level__parser__m_monad;
x_26 = l_lean_parser_level__parser__m_monad__except;
x_27 = l_lean_parser_level__parser__m_lean_parser_monad__parsec;
x_28 = l_lean_parser_level__parser__m_alternative;
x_29 = l_lean_parser_level_leading;
x_30 = l_lean_parser_level_leading_has__view;
lean::inc(x_30);
lean::inc(x_29);
lean::inc(x_28);
lean::inc(x_27);
lean::inc(x_26);
lean::inc(x_25);
x_37 = l_lean_parser_combinators_node_view___rarg(x_25, x_26, x_27, x_28, x_29, x_24, x_30);
return x_37;
}
}
obj* _init_l_lean_parser_level_leading_parser_lean_parser_has__tokens() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_4; obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_13; obj* x_15; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_0 = lean::box(0);
x_1 = lean::mk_string("_");
x_2 = l_lean_parser_max__prec;
lean::inc(x_2);
x_4 = l_lean_parser_symbol_tokens___rarg(x_1, x_2);
lean::inc(x_0);
lean::inc(x_0);
x_7 = l_lean_parser_list_cons_tokens___rarg(x_0, x_0);
lean::inc(x_0);
x_9 = l_lean_parser_list_cons_tokens___rarg(x_0, x_7);
x_10 = l_lean_parser_level_paren_parser_lean_parser_has__tokens;
lean::inc(x_10);
x_12 = l_lean_parser_list_cons_tokens___rarg(x_10, x_9);
x_13 = l_lean_parser_list_cons_tokens___rarg(x_4, x_12);
lean::inc(x_0);
x_15 = l_lean_parser_list_cons_tokens___rarg(x_0, x_13);
lean::inc(x_0);
x_17 = l_lean_parser_list_cons_tokens___rarg(x_0, x_15);
x_18 = l_lean_parser_tokens___rarg(x_17);
x_19 = l_lean_parser_list_cons_tokens___rarg(x_18, x_0);
x_20 = l_lean_parser_tokens___rarg(x_19);
return x_20;
}
}
obj* _init_l_lean_parser_level_app() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_4, 0, x_2);
lean::cnstr_set(x_4, 1, x_3);
x_5 = lean::mk_string("level");
x_6 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_6, 0, x_4);
lean::cnstr_set(x_6, 1, x_5);
x_7 = lean::mk_string("app");
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set(x_8, 1, x_7);
return x_8;
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
obj* l_lean_parser_level_app_has__view_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_syntax_as__node___main(x_0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; 
lean::dec(x_1);
x_3 = l_lean_parser_level_app_has__view_x_27___lambda__1___closed__1;
lean::inc(x_3);
return x_3;
}
else
{
obj* x_5; obj* x_8; 
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
lean::dec(x_1);
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
lean::dec(x_5);
if (lean::obj_tag(x_8) == 0)
{
if (lean::obj_tag(x_8) == 0)
{
obj* x_12; 
lean::dec(x_8);
x_12 = l_lean_parser_level_app_has__view_x_27___lambda__1___closed__1;
lean::inc(x_12);
return x_12;
}
else
{
obj* x_14; obj* x_17; obj* x_18; 
x_14 = lean::cnstr_get(x_8, 0);
lean::inc(x_14);
lean::dec(x_8);
x_17 = lean::box(3);
x_18 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_14);
return x_18;
}
}
else
{
obj* x_19; obj* x_21; 
x_19 = lean::cnstr_get(x_8, 0);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_8, 1);
lean::inc(x_21);
lean::dec(x_8);
if (lean::obj_tag(x_21) == 0)
{
obj* x_25; obj* x_26; 
lean::dec(x_21);
x_25 = lean::box(3);
x_26 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_26, 0, x_19);
lean::cnstr_set(x_26, 1, x_25);
return x_26;
}
else
{
obj* x_27; obj* x_30; 
x_27 = lean::cnstr_get(x_21, 0);
lean::inc(x_27);
lean::dec(x_21);
x_30 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_30, 0, x_19);
lean::cnstr_set(x_30, 1, x_27);
return x_30;
}
}
}
}
}
obj* _init_l_lean_parser_level_app_has__view_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_2; 
x_0 = lean::box(3);
lean::inc(x_0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_0);
return x_2;
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
obj* _init_l_lean_parser_level_app_has__view() {
_start:
{
obj* x_0; 
x_0 = l_lean_parser_level_app_has__view_x_27;
lean::inc(x_0);
return x_0;
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
obj* _init_l_lean_parser_level_app_parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = lean::box(0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_level_app_parser___lambda__1), 5, 0);
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
obj* l_lean_parser_level_app_parser___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
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
obj* l_list_mfoldl___main___at_lean_parser_level_app_parser___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_13; obj* x_15; obj* x_16; 
lean::dec(x_4);
lean::dec(x_5);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_3);
x_13 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_13);
x_15 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_15, 0, x_1);
lean::cnstr_set(x_15, 1, x_6);
lean::cnstr_set(x_15, 2, x_13);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_15);
lean::cnstr_set(x_16, 1, x_7);
return x_16;
}
else
{
obj* x_17; obj* x_19; obj* x_21; obj* x_22; obj* x_23; obj* x_28; obj* x_29; obj* x_31; 
x_17 = lean::cnstr_get(x_2, 0);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_2, 1);
lean::inc(x_19);
if (lean::is_shared(x_2)) {
 lean::dec(x_2);
 x_21 = lean::box(0);
} else {
 lean::cnstr_release(x_2, 0);
 lean::cnstr_release(x_2, 1);
 x_21 = x_2;
}
lean::inc(x_5);
lean::inc(x_4);
lean::inc(x_3);
x_28 = lean::apply_5(x_17, x_3, x_4, x_5, x_6, x_7);
x_29 = lean::cnstr_get(x_28, 0);
lean::inc(x_29);
x_31 = lean::cnstr_get(x_28, 1);
lean::inc(x_31);
lean::dec(x_28);
if (lean::obj_tag(x_29) == 0)
{
x_22 = x_29;
x_23 = x_31;
goto lbl_24;
}
else
{
obj* x_34; unsigned char x_36; obj* x_37; 
x_34 = lean::cnstr_get(x_29, 0);
lean::inc(x_34);
x_36 = lean::cnstr_get_scalar<unsigned char>(x_29, sizeof(void*)*1);
if (lean::is_shared(x_29)) {
 lean::dec(x_29);
 x_37 = lean::box(0);
} else {
 lean::cnstr_release(x_29, 0);
 x_37 = x_29;
}
if (lean::obj_tag(x_1) == 0)
{
if (x_36 == 0)
{
unsigned char x_38; obj* x_39; obj* x_40; 
x_38 = 0;
if (lean::is_scalar(x_37)) {
 x_39 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_39 = x_37;
}
lean::cnstr_set(x_39, 0, x_34);
lean::cnstr_set_scalar(x_39, sizeof(void*)*1, x_38);
x_40 = x_39;
x_22 = x_40;
x_23 = x_31;
goto lbl_24;
}
else
{
obj* x_41; obj* x_42; 
if (lean::is_scalar(x_37)) {
 x_41 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_41 = x_37;
}
lean::cnstr_set(x_41, 0, x_34);
lean::cnstr_set_scalar(x_41, sizeof(void*)*1, x_36);
x_42 = x_41;
x_22 = x_42;
x_23 = x_31;
goto lbl_24;
}
}
else
{
obj* x_43; obj* x_45; obj* x_47; obj* x_48; obj* x_50; obj* x_52; obj* x_55; obj* x_57; obj* x_58; obj* x_59; 
x_43 = lean::cnstr_get(x_34, 3);
lean::inc(x_43);
x_45 = l_option_get___main___at_lean_parser_run___spec__2(x_43);
lean::inc(x_1);
x_47 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_47, 0, x_45);
lean::cnstr_set(x_47, 1, x_1);
x_48 = lean::cnstr_get(x_34, 0);
lean::inc(x_48);
x_50 = lean::cnstr_get(x_34, 1);
lean::inc(x_50);
x_52 = lean::cnstr_get(x_34, 2);
lean::inc(x_52);
lean::dec(x_34);
x_55 = l_list_reverse___rarg(x_47);
lean::inc(x_0);
x_57 = l_lean_parser_syntax_mk__node(x_0, x_55);
x_58 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_58, 0, x_57);
x_59 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_59, 0, x_48);
lean::cnstr_set(x_59, 1, x_50);
lean::cnstr_set(x_59, 2, x_52);
lean::cnstr_set(x_59, 3, x_58);
if (x_36 == 0)
{
unsigned char x_60; obj* x_61; obj* x_62; 
x_60 = 0;
if (lean::is_scalar(x_37)) {
 x_61 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_61 = x_37;
}
lean::cnstr_set(x_61, 0, x_59);
lean::cnstr_set_scalar(x_61, sizeof(void*)*1, x_60);
x_62 = x_61;
x_22 = x_62;
x_23 = x_31;
goto lbl_24;
}
else
{
obj* x_63; obj* x_64; 
if (lean::is_scalar(x_37)) {
 x_63 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_63 = x_37;
}
lean::cnstr_set(x_63, 0, x_59);
lean::cnstr_set_scalar(x_63, sizeof(void*)*1, x_36);
x_64 = x_63;
x_22 = x_64;
x_23 = x_31;
goto lbl_24;
}
}
}
lbl_24:
{
if (lean::obj_tag(x_22) == 0)
{
obj* x_65; obj* x_67; obj* x_69; obj* x_71; obj* x_72; obj* x_73; obj* x_75; obj* x_76; 
x_65 = lean::cnstr_get(x_22, 0);
lean::inc(x_65);
x_67 = lean::cnstr_get(x_22, 1);
lean::inc(x_67);
x_69 = lean::cnstr_get(x_22, 2);
lean::inc(x_69);
if (lean::is_shared(x_22)) {
 lean::dec(x_22);
 x_71 = lean::box(0);
} else {
 lean::cnstr_release(x_22, 0);
 lean::cnstr_release(x_22, 1);
 lean::cnstr_release(x_22, 2);
 x_71 = x_22;
}
if (lean::is_scalar(x_21)) {
 x_72 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_72 = x_21;
}
lean::cnstr_set(x_72, 0, x_65);
lean::cnstr_set(x_72, 1, x_1);
x_73 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_73);
if (lean::is_scalar(x_71)) {
 x_75 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_75 = x_71;
}
lean::cnstr_set(x_75, 0, x_72);
lean::cnstr_set(x_75, 1, x_67);
lean::cnstr_set(x_75, 2, x_73);
x_76 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_69, x_75);
if (lean::obj_tag(x_76) == 0)
{
obj* x_77; obj* x_79; obj* x_81; obj* x_84; obj* x_85; obj* x_87; obj* x_89; obj* x_90; obj* x_91; 
x_77 = lean::cnstr_get(x_76, 0);
lean::inc(x_77);
x_79 = lean::cnstr_get(x_76, 1);
lean::inc(x_79);
x_81 = lean::cnstr_get(x_76, 2);
lean::inc(x_81);
lean::dec(x_76);
x_84 = l_list_mfoldl___main___at_lean_parser_level_app_parser___spec__2(x_0, x_77, x_19, x_3, x_4, x_5, x_79, x_23);
x_85 = lean::cnstr_get(x_84, 0);
lean::inc(x_85);
x_87 = lean::cnstr_get(x_84, 1);
lean::inc(x_87);
if (lean::is_shared(x_84)) {
 lean::dec(x_84);
 x_89 = lean::box(0);
} else {
 lean::cnstr_release(x_84, 0);
 lean::cnstr_release(x_84, 1);
 x_89 = x_84;
}
x_90 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_81, x_85);
if (lean::is_scalar(x_89)) {
 x_91 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_91 = x_89;
}
lean::cnstr_set(x_91, 0, x_90);
lean::cnstr_set(x_91, 1, x_87);
return x_91;
}
else
{
obj* x_97; unsigned char x_99; obj* x_100; obj* x_101; obj* x_102; obj* x_103; 
lean::dec(x_4);
lean::dec(x_5);
lean::dec(x_0);
lean::dec(x_3);
lean::dec(x_19);
x_97 = lean::cnstr_get(x_76, 0);
lean::inc(x_97);
x_99 = lean::cnstr_get_scalar<unsigned char>(x_76, sizeof(void*)*1);
if (lean::is_shared(x_76)) {
 lean::dec(x_76);
 x_100 = lean::box(0);
} else {
 lean::cnstr_release(x_76, 0);
 x_100 = x_76;
}
if (lean::is_scalar(x_100)) {
 x_101 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_101 = x_100;
}
lean::cnstr_set(x_101, 0, x_97);
lean::cnstr_set_scalar(x_101, sizeof(void*)*1, x_99);
x_102 = x_101;
x_103 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_103, 0, x_102);
lean::cnstr_set(x_103, 1, x_23);
return x_103;
}
}
else
{
obj* x_111; unsigned char x_113; obj* x_114; obj* x_115; obj* x_116; obj* x_117; 
lean::dec(x_4);
lean::dec(x_5);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_19);
lean::dec(x_21);
x_111 = lean::cnstr_get(x_22, 0);
lean::inc(x_111);
x_113 = lean::cnstr_get_scalar<unsigned char>(x_22, sizeof(void*)*1);
if (lean::is_shared(x_22)) {
 lean::dec(x_22);
 x_114 = lean::box(0);
} else {
 lean::cnstr_release(x_22, 0);
 x_114 = x_22;
}
if (lean::is_scalar(x_114)) {
 x_115 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_115 = x_114;
}
lean::cnstr_set(x_115, 0, x_111);
lean::cnstr_set_scalar(x_115, sizeof(void*)*1, x_113);
x_116 = x_115;
x_117 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_117, 0, x_116);
lean::cnstr_set(x_117, 1, x_23);
return x_117;
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
obj* x_30; unsigned char x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; 
lean::dec(x_0);
x_30 = lean::cnstr_get(x_10, 0);
lean::inc(x_30);
x_32 = lean::cnstr_get_scalar<unsigned char>(x_10, sizeof(void*)*1);
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
obj* _init_l_lean_parser_level_app_parser_lean_parser_has__view() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_17; 
x_0 = lean::box(0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_level_app_parser___lambda__1), 5, 0);
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
obj* _init_l_lean_parser_level_add__lit() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_4, 0, x_2);
lean::cnstr_set(x_4, 1, x_3);
x_5 = lean::mk_string("level");
x_6 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_6, 0, x_4);
lean::cnstr_set(x_6, 1, x_5);
x_7 = lean::mk_string("add_lit");
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set(x_8, 1, x_7);
return x_8;
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
obj* l_lean_parser_level_add__lit_has__view_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_4 = l_lean_parser_syntax_as__node___main(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; 
lean::dec(x_4);
x_6 = l_lean_parser_level_add__lit_has__view_x_27___lambda__1___closed__2;
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
obj* x_20; obj* x_21; 
if (lean::obj_tag(x_1) == 0)
{
obj* x_23; 
x_23 = lean::box(3);
x_20 = x_1;
x_21 = x_23;
goto lbl_22;
}
else
{
obj* x_24; obj* x_26; 
x_24 = lean::cnstr_get(x_1, 0);
lean::inc(x_24);
x_26 = lean::cnstr_get(x_1, 1);
lean::inc(x_26);
lean::dec(x_1);
x_20 = x_26;
x_21 = x_24;
goto lbl_22;
}
lbl_22:
{
switch (lean::obj_tag(x_21)) {
case 0:
{
obj* x_29; obj* x_32; 
x_29 = lean::cnstr_get(x_21, 0);
lean::inc(x_29);
lean::dec(x_21);
x_32 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_32, 0, x_29);
if (lean::obj_tag(x_20) == 0)
{
obj* x_34; obj* x_36; 
lean::dec(x_20);
x_34 = l_lean_parser_level_add__lit_has__view_x_27___lambda__1___closed__1;
lean::inc(x_34);
x_36 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_36, 0, x_2);
lean::cnstr_set(x_36, 1, x_32);
lean::cnstr_set(x_36, 2, x_34);
return x_36;
}
else
{
obj* x_37; obj* x_40; obj* x_41; obj* x_43; obj* x_44; 
x_37 = lean::cnstr_get(x_20, 0);
lean::inc(x_37);
lean::dec(x_20);
x_40 = l_lean_parser_number_has__view;
x_41 = lean::cnstr_get(x_40, 0);
lean::inc(x_41);
x_43 = lean::apply_1(x_41, x_37);
x_44 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_44, 0, x_2);
lean::cnstr_set(x_44, 1, x_32);
lean::cnstr_set(x_44, 2, x_43);
return x_44;
}
}
case 1:
{
obj* x_46; 
lean::dec(x_21);
x_46 = lean::box(0);
if (lean::obj_tag(x_20) == 0)
{
obj* x_48; obj* x_50; 
lean::dec(x_20);
x_48 = l_lean_parser_level_add__lit_has__view_x_27___lambda__1___closed__1;
lean::inc(x_48);
x_50 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_50, 0, x_2);
lean::cnstr_set(x_50, 1, x_46);
lean::cnstr_set(x_50, 2, x_48);
return x_50;
}
else
{
obj* x_51; obj* x_54; obj* x_55; obj* x_57; obj* x_58; 
x_51 = lean::cnstr_get(x_20, 0);
lean::inc(x_51);
lean::dec(x_20);
x_54 = l_lean_parser_number_has__view;
x_55 = lean::cnstr_get(x_54, 0);
lean::inc(x_55);
x_57 = lean::apply_1(x_55, x_51);
x_58 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_58, 0, x_2);
lean::cnstr_set(x_58, 1, x_46);
lean::cnstr_set(x_58, 2, x_57);
return x_58;
}
}
case 2:
{
obj* x_60; 
lean::dec(x_21);
x_60 = lean::box(0);
if (lean::obj_tag(x_20) == 0)
{
obj* x_62; obj* x_64; 
lean::dec(x_20);
x_62 = l_lean_parser_level_add__lit_has__view_x_27___lambda__1___closed__1;
lean::inc(x_62);
x_64 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_64, 0, x_2);
lean::cnstr_set(x_64, 1, x_60);
lean::cnstr_set(x_64, 2, x_62);
return x_64;
}
else
{
obj* x_65; obj* x_68; obj* x_69; obj* x_71; obj* x_72; 
x_65 = lean::cnstr_get(x_20, 0);
lean::inc(x_65);
lean::dec(x_20);
x_68 = l_lean_parser_number_has__view;
x_69 = lean::cnstr_get(x_68, 0);
lean::inc(x_69);
x_71 = lean::apply_1(x_69, x_65);
x_72 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_72, 0, x_2);
lean::cnstr_set(x_72, 1, x_60);
lean::cnstr_set(x_72, 2, x_71);
return x_72;
}
}
default:
{
obj* x_74; 
lean::dec(x_21);
x_74 = lean::box(0);
if (lean::obj_tag(x_20) == 0)
{
obj* x_76; obj* x_78; 
lean::dec(x_20);
x_76 = l_lean_parser_level_add__lit_has__view_x_27___lambda__1___closed__1;
lean::inc(x_76);
x_78 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_78, 0, x_2);
lean::cnstr_set(x_78, 1, x_74);
lean::cnstr_set(x_78, 2, x_76);
return x_78;
}
else
{
obj* x_79; obj* x_82; obj* x_83; obj* x_85; obj* x_86; 
x_79 = lean::cnstr_get(x_20, 0);
lean::inc(x_79);
lean::dec(x_20);
x_82 = l_lean_parser_number_has__view;
x_83 = lean::cnstr_get(x_82, 0);
lean::inc(x_83);
x_85 = lean::apply_1(x_83, x_79);
x_86 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_86, 0, x_2);
lean::cnstr_set(x_86, 1, x_74);
lean::cnstr_set(x_86, 2, x_85);
return x_86;
}
}
}
}
}
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
obj* x_19; obj* x_21; 
lean::dec(x_5);
x_19 = l_lean_parser_level_add__lit_has__view_x_27___lambda__1___closed__1;
lean::inc(x_19);
x_21 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_21, 0, x_1);
lean::cnstr_set(x_21, 1, x_17);
lean::cnstr_set(x_21, 2, x_19);
return x_21;
}
else
{
obj* x_22; obj* x_25; obj* x_26; obj* x_28; obj* x_29; 
x_22 = lean::cnstr_get(x_5, 0);
lean::inc(x_22);
lean::dec(x_5);
x_25 = l_lean_parser_number_has__view;
x_26 = lean::cnstr_get(x_25, 0);
lean::inc(x_26);
x_28 = lean::apply_1(x_26, x_22);
x_29 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_29, 0, x_1);
lean::cnstr_set(x_29, 1, x_17);
lean::cnstr_set(x_29, 2, x_28);
return x_29;
}
}
case 1:
{
obj* x_31; 
lean::dec(x_6);
x_31 = lean::box(0);
if (lean::obj_tag(x_5) == 0)
{
obj* x_33; obj* x_35; 
lean::dec(x_5);
x_33 = l_lean_parser_level_add__lit_has__view_x_27___lambda__1___closed__1;
lean::inc(x_33);
x_35 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_35, 0, x_1);
lean::cnstr_set(x_35, 1, x_31);
lean::cnstr_set(x_35, 2, x_33);
return x_35;
}
else
{
obj* x_36; obj* x_39; obj* x_40; obj* x_42; obj* x_43; 
x_36 = lean::cnstr_get(x_5, 0);
lean::inc(x_36);
lean::dec(x_5);
x_39 = l_lean_parser_number_has__view;
x_40 = lean::cnstr_get(x_39, 0);
lean::inc(x_40);
x_42 = lean::apply_1(x_40, x_36);
x_43 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_43, 0, x_1);
lean::cnstr_set(x_43, 1, x_31);
lean::cnstr_set(x_43, 2, x_42);
return x_43;
}
}
case 2:
{
obj* x_45; 
lean::dec(x_6);
x_45 = lean::box(0);
if (lean::obj_tag(x_5) == 0)
{
obj* x_47; obj* x_49; 
lean::dec(x_5);
x_47 = l_lean_parser_level_add__lit_has__view_x_27___lambda__1___closed__1;
lean::inc(x_47);
x_49 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_49, 0, x_1);
lean::cnstr_set(x_49, 1, x_45);
lean::cnstr_set(x_49, 2, x_47);
return x_49;
}
else
{
obj* x_50; obj* x_53; obj* x_54; obj* x_56; obj* x_57; 
x_50 = lean::cnstr_get(x_5, 0);
lean::inc(x_50);
lean::dec(x_5);
x_53 = l_lean_parser_number_has__view;
x_54 = lean::cnstr_get(x_53, 0);
lean::inc(x_54);
x_56 = lean::apply_1(x_54, x_50);
x_57 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_57, 0, x_1);
lean::cnstr_set(x_57, 1, x_45);
lean::cnstr_set(x_57, 2, x_56);
return x_57;
}
}
default:
{
obj* x_59; 
lean::dec(x_6);
x_59 = lean::box(0);
if (lean::obj_tag(x_5) == 0)
{
obj* x_61; obj* x_63; 
lean::dec(x_5);
x_61 = l_lean_parser_level_add__lit_has__view_x_27___lambda__1___closed__1;
lean::inc(x_61);
x_63 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_63, 0, x_1);
lean::cnstr_set(x_63, 1, x_59);
lean::cnstr_set(x_63, 2, x_61);
return x_63;
}
else
{
obj* x_64; obj* x_67; obj* x_68; obj* x_70; obj* x_71; 
x_64 = lean::cnstr_get(x_5, 0);
lean::inc(x_64);
lean::dec(x_5);
x_67 = l_lean_parser_number_has__view;
x_68 = lean::cnstr_get(x_67, 0);
lean::inc(x_68);
x_70 = lean::apply_1(x_68, x_64);
x_71 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_71, 0, x_1);
lean::cnstr_set(x_71, 1, x_59);
lean::cnstr_set(x_71, 2, x_70);
return x_71;
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
obj* _init_l_lean_parser_level_add__lit_has__view() {
_start:
{
obj* x_0; 
x_0 = l_lean_parser_level_add__lit_has__view_x_27;
lean::inc(x_0);
return x_0;
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
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_level_add__lit_parser___spec__1), 8, 3);
lean::closure_set(x_5, 0, x_1);
lean::closure_set(x_5, 1, x_4);
lean::closure_set(x_5, 2, x_3);
x_6 = lean::box(0);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_number_parser___at_lean_parser_level_add__lit_parser___spec__2), 2, 0);
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
obj* l_lean_parser_symbol__core___at_lean_parser_level_add__lit_parser___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
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
obj* x_21; obj* x_23; obj* x_25; obj* x_27; unsigned char x_28; 
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
obj* x_31; obj* x_33; obj* x_36; 
lean::dec(x_18);
x_31 = lean::cnstr_get(x_21, 0);
lean::inc(x_31);
x_33 = lean::cnstr_get(x_31, 1);
lean::inc(x_33);
lean::dec(x_31);
x_36 = lean::string_dec_eq(x_0, x_33);
lean::dec(x_0);
if (lean::obj_tag(x_36) == 0)
{
obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_44; obj* x_46; 
lean::dec(x_36);
x_39 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_39, 0, x_6);
x_40 = lean::box(0);
x_41 = l_lean_parser_monad__parsec_error___at___private_4089500695__finish__comment__block__aux___main___spec__1___rarg(x_33, x_2, x_39, x_40, x_5, x_23, x_16);
x_42 = lean::cnstr_get(x_41, 0);
lean::inc(x_42);
x_44 = lean::cnstr_get(x_41, 1);
lean::inc(x_44);
if (lean::is_shared(x_41)) {
 lean::dec(x_41);
 x_46 = lean::box(0);
} else {
 lean::cnstr_release(x_41, 0);
 lean::cnstr_release(x_41, 1);
 x_46 = x_41;
}
if (lean::obj_tag(x_42) == 0)
{
obj* x_47; obj* x_49; obj* x_52; obj* x_54; obj* x_55; obj* x_56; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
x_47 = lean::cnstr_get(x_42, 1);
lean::inc(x_47);
x_49 = lean::cnstr_get(x_42, 2);
lean::inc(x_49);
lean::dec(x_42);
x_52 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_52);
if (lean::is_scalar(x_27)) {
 x_54 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_54 = x_27;
}
lean::cnstr_set(x_54, 0, x_21);
lean::cnstr_set(x_54, 1, x_47);
lean::cnstr_set(x_54, 2, x_52);
x_55 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_49, x_54);
x_56 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_25, x_55);
lean::inc(x_52);
x_58 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_52, x_56);
x_59 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_58, x_20);
x_60 = l_lean_parser_parsec__t_try__mk__res___rarg(x_59);
if (lean::is_scalar(x_46)) {
 x_61 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_61 = x_46;
}
lean::cnstr_set(x_61, 0, x_60);
lean::cnstr_set(x_61, 1, x_44);
return x_61;
}
else
{
obj* x_64; unsigned char x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_73; obj* x_74; obj* x_75; obj* x_76; 
lean::dec(x_21);
lean::dec(x_27);
x_64 = lean::cnstr_get(x_42, 0);
lean::inc(x_64);
x_66 = lean::cnstr_get_scalar<unsigned char>(x_42, sizeof(void*)*1);
if (lean::is_shared(x_42)) {
 lean::dec(x_42);
 x_67 = lean::box(0);
} else {
 lean::cnstr_release(x_42, 0);
 x_67 = x_42;
}
if (lean::is_scalar(x_67)) {
 x_68 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_68 = x_67;
}
lean::cnstr_set(x_68, 0, x_64);
lean::cnstr_set_scalar(x_68, sizeof(void*)*1, x_66);
x_69 = x_68;
x_70 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_25, x_69);
x_71 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_71);
x_73 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_71, x_70);
x_74 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_73, x_20);
x_75 = l_lean_parser_parsec__t_try__mk__res___rarg(x_74);
if (lean::is_scalar(x_46)) {
 x_76 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_76 = x_46;
}
lean::cnstr_set(x_76, 0, x_75);
lean::cnstr_set(x_76, 1, x_44);
return x_76;
}
}
else
{
obj* x_82; obj* x_84; obj* x_85; obj* x_86; obj* x_88; obj* x_89; obj* x_90; obj* x_91; 
lean::dec(x_5);
lean::dec(x_6);
lean::dec(x_2);
lean::dec(x_36);
lean::dec(x_33);
x_82 = l_lean_parser_finish__comment__block___closed__2;
lean::inc(x_82);
if (lean::is_scalar(x_27)) {
 x_84 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_84 = x_27;
}
lean::cnstr_set(x_84, 0, x_21);
lean::cnstr_set(x_84, 1, x_23);
lean::cnstr_set(x_84, 2, x_82);
x_85 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_25, x_84);
x_86 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_86);
x_88 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_86, x_85);
x_89 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_88, x_20);
x_90 = l_lean_parser_parsec__t_try__mk__res___rarg(x_89);
x_91 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_91, 0, x_90);
lean::cnstr_set(x_91, 1, x_16);
return x_91;
}
}
case 1:
{
unsigned char x_95; 
lean::dec(x_0);
lean::dec(x_21);
lean::dec(x_27);
x_95 = 0;
x_28 = x_95;
goto lbl_29;
}
case 2:
{
unsigned char x_99; 
lean::dec(x_0);
lean::dec(x_21);
lean::dec(x_27);
x_99 = 0;
x_28 = x_99;
goto lbl_29;
}
default:
{
unsigned char x_103; 
lean::dec(x_0);
lean::dec(x_21);
lean::dec(x_27);
x_103 = 0;
x_28 = x_103;
goto lbl_29;
}
}
lbl_29:
{
obj* x_104; obj* x_105; obj* x_106; obj* x_108; obj* x_109; obj* x_111; obj* x_114; obj* x_115; obj* x_117; obj* x_118; obj* x_119; obj* x_120; 
x_104 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_104, 0, x_6);
x_105 = lean::box(0);
x_106 = l_string_join___closed__1;
lean::inc(x_106);
x_108 = l_lean_parser_monad__parsec_error___at___private_4089500695__finish__comment__block__aux___main___spec__1___rarg(x_106, x_2, x_104, x_105, x_5, x_23, x_16);
x_109 = lean::cnstr_get(x_108, 0);
lean::inc(x_109);
x_111 = lean::cnstr_get(x_108, 1);
lean::inc(x_111);
lean::dec(x_108);
x_114 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_25, x_109);
x_115 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_115);
x_117 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_115, x_114);
x_118 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_117, x_20);
x_119 = l_lean_parser_parsec__t_try__mk__res___rarg(x_118);
if (lean::is_scalar(x_18)) {
 x_120 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_120 = x_18;
}
lean::cnstr_set(x_120, 0, x_119);
lean::cnstr_set(x_120, 1, x_111);
return x_120;
}
}
else
{
obj* x_125; unsigned char x_127; obj* x_128; obj* x_129; obj* x_130; obj* x_131; obj* x_133; obj* x_134; obj* x_135; obj* x_136; 
lean::dec(x_5);
lean::dec(x_6);
lean::dec(x_0);
lean::dec(x_2);
x_125 = lean::cnstr_get(x_14, 0);
lean::inc(x_125);
x_127 = lean::cnstr_get_scalar<unsigned char>(x_14, sizeof(void*)*1);
if (lean::is_shared(x_14)) {
 lean::dec(x_14);
 x_128 = lean::box(0);
} else {
 lean::cnstr_release(x_14, 0);
 x_128 = x_14;
}
if (lean::is_scalar(x_128)) {
 x_129 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_129 = x_128;
}
lean::cnstr_set(x_129, 0, x_125);
lean::cnstr_set_scalar(x_129, sizeof(void*)*1, x_127);
x_130 = x_129;
x_131 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_131);
x_133 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_131, x_130);
x_134 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_133, x_20);
x_135 = l_lean_parser_parsec__t_try__mk__res___rarg(x_134);
if (lean::is_scalar(x_18)) {
 x_136 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_136 = x_18;
}
lean::cnstr_set(x_136, 0, x_135);
lean::cnstr_set(x_136, 1, x_16);
return x_136;
}
}
}
obj* l_lean_parser_number_parser___at_lean_parser_level_add__lit_parser___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2) {
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
obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_29; obj* x_30; obj* x_32; obj* x_35; obj* x_37; obj* x_38; obj* x_40; obj* x_42; obj* x_43; obj* x_44; 
lean::dec(x_17);
lean::dec(x_19);
lean::dec(x_11);
x_23 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_23, 0, x_1);
x_24 = lean::box(0);
x_25 = l_string_join___closed__1;
x_26 = l_lean_parser_number_parser___at_lean_parser_level_leading_parser___spec__2___rarg___closed__1;
lean::inc(x_26);
lean::inc(x_25);
x_29 = l_lean_parser_monad__parsec_error___at___private_4089500695__finish__comment__block__aux___main___spec__1___rarg(x_25, x_26, x_23, x_24, x_0, x_13, x_8);
x_30 = lean::cnstr_get(x_29, 0);
lean::inc(x_30);
x_32 = lean::cnstr_get(x_29, 1);
lean::inc(x_32);
lean::dec(x_29);
x_35 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_35);
x_37 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_35, x_30);
x_38 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_37);
lean::inc(x_35);
x_40 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_35, x_38);
lean::inc(x_26);
x_42 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_40, x_26);
x_43 = l_lean_parser_parsec__t_try__mk__res___rarg(x_42);
if (lean::is_scalar(x_10)) {
 x_44 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_44 = x_10;
}
lean::cnstr_set(x_44, 0, x_43);
lean::cnstr_set(x_44, 1, x_32);
return x_44;
}
else
{
obj* x_48; obj* x_50; obj* x_51; obj* x_52; obj* x_54; obj* x_55; obj* x_57; obj* x_58; obj* x_59; 
lean::dec(x_19);
lean::dec(x_0);
lean::dec(x_1);
x_48 = l_lean_parser_finish__comment__block___closed__2;
lean::inc(x_48);
if (lean::is_scalar(x_17)) {
 x_50 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_50 = x_17;
}
lean::cnstr_set(x_50, 0, x_11);
lean::cnstr_set(x_50, 1, x_13);
lean::cnstr_set(x_50, 2, x_48);
x_51 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_50);
x_52 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_52);
x_54 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_52, x_51);
x_55 = l_lean_parser_number_parser___at_lean_parser_level_leading_parser___spec__2___rarg___closed__1;
lean::inc(x_55);
x_57 = l_lean_parser_parsec__t_labels__mk__res___rarg(x_54, x_55);
x_58 = l_lean_parser_parsec__t_try__mk__res___rarg(x_57);
if (lean::is_scalar(x_10)) {
 x_59 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_59 = x_10;
}
lean::cnstr_set(x_59, 0, x_58);
lean::cnstr_set(x_59, 1, x_8);
return x_59;
}
}
else
{
obj* x_62; unsigned char x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_70; obj* x_71; obj* x_73; obj* x_74; obj* x_75; 
lean::dec(x_0);
lean::dec(x_1);
x_62 = lean::cnstr_get(x_6, 0);
lean::inc(x_62);
x_64 = lean::cnstr_get_scalar<unsigned char>(x_6, sizeof(void*)*1);
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
x_71 = l_lean_parser_number_parser___at_lean_parser_level_leading_parser___spec__2___rarg___closed__1;
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
obj* l_lean_parser_number_parser___at_lean_parser_level_add__lit_parser___spec__2(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_number_parser___at_lean_parser_level_add__lit_parser___spec__2___rarg), 3, 0);
return x_4;
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
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_symbol__core___at_lean_parser_level_add__lit_parser___spec__1), 8, 3);
lean::closure_set(x_5, 0, x_1);
lean::closure_set(x_5, 1, x_4);
lean::closure_set(x_5, 2, x_3);
x_6 = lean::box(0);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_number_parser___at_lean_parser_level_add__lit_parser___spec__2), 2, 0);
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
obj* _init_l_lean_parser_level_add__lit_parser_lean_parser_has__tokens() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_5; obj* x_6; obj* x_7; obj* x_9; obj* x_10; 
x_0 = lean::mk_string("+");
x_1 = lean::mk_nat_obj(0u);
x_2 = l_lean_parser_symbol_tokens___rarg(x_0, x_1);
x_3 = lean::box(0);
lean::inc(x_3);
x_5 = l_lean_parser_list_cons_tokens___rarg(x_3, x_3);
x_6 = l_lean_parser_list_cons_tokens___rarg(x_2, x_5);
x_7 = l_lean_parser_level_lean_parser_has__tokens;
lean::inc(x_7);
x_9 = l_lean_parser_list_cons_tokens___rarg(x_7, x_6);
x_10 = l_lean_parser_tokens___rarg(x_9);
return x_10;
}
}
obj* _init_l_lean_parser_level_trailing() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("lean");
x_2 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_4, 0, x_2);
lean::cnstr_set(x_4, 1, x_3);
x_5 = lean::mk_string("level");
x_6 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_6, 0, x_4);
lean::cnstr_set(x_6, 1, x_5);
x_7 = lean::mk_string("trailing");
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set(x_8, 1, x_7);
return x_8;
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
obj* l_lean_parser_level_trailing_has__view_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_4 = l_lean_parser_syntax_as__node___main(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; 
lean::dec(x_4);
x_6 = l_lean_parser_level_trailing_has__view_x_27___lambda__1___closed__1;
lean::inc(x_6);
return x_6;
}
else
{
obj* x_8; obj* x_11; obj* x_13; obj* x_16; obj* x_18; 
x_8 = lean::cnstr_get(x_4, 0);
lean::inc(x_8);
lean::dec(x_4);
x_11 = lean::cnstr_get(x_8, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_8, 1);
lean::inc(x_13);
lean::dec(x_8);
x_16 = l_lean_parser_level_trailing_has__view_x_27___lambda__1___closed__2;
lean::inc(x_16);
x_18 = l_lean_name_has__dec__eq___main(x_11, x_16);
if (lean::obj_tag(x_18) == 0)
{
obj* x_21; 
lean::dec(x_18);
lean::dec(x_13);
x_21 = l_lean_parser_level_trailing_has__view_x_27___lambda__1___closed__1;
lean::inc(x_21);
return x_21;
}
else
{
lean::dec(x_18);
if (lean::obj_tag(x_13) == 0)
{
obj* x_25; 
lean::dec(x_13);
x_25 = l_lean_parser_level_trailing_has__view_x_27___lambda__1___closed__1;
lean::inc(x_25);
return x_25;
}
else
{
obj* x_27; obj* x_29; 
x_27 = lean::cnstr_get(x_13, 0);
lean::inc(x_27);
x_29 = lean::cnstr_get(x_13, 1);
lean::inc(x_29);
lean::dec(x_13);
if (lean::obj_tag(x_29) == 0)
{
obj* x_33; 
lean::dec(x_29);
x_33 = l_lean_parser_syntax_as__node___main(x_27);
if (lean::obj_tag(x_33) == 0)
{
obj* x_35; 
lean::dec(x_33);
x_35 = l_lean_parser_level_trailing_has__view_x_27___lambda__1___closed__1;
lean::inc(x_35);
return x_35;
}
else
{
obj* x_37; obj* x_40; obj* x_42; 
x_37 = lean::cnstr_get(x_33, 0);
lean::inc(x_37);
lean::dec(x_33);
x_40 = lean::cnstr_get(x_37, 0);
lean::inc(x_40);
x_42 = lean::cnstr_get(x_37, 1);
lean::inc(x_42);
lean::dec(x_37);
switch (lean::obj_tag(x_40)) {
case 0:
{
obj* x_47; 
lean::dec(x_40);
lean::dec(x_42);
x_47 = l_lean_parser_level_trailing_has__view_x_27___lambda__1___closed__1;
lean::inc(x_47);
return x_47;
}
case 1:
{
obj* x_51; 
lean::dec(x_40);
lean::dec(x_42);
x_51 = l_lean_parser_level_trailing_has__view_x_27___lambda__1___closed__1;
lean::inc(x_51);
return x_51;
}
default:
{
obj* x_53; obj* x_55; obj* x_58; obj* x_59; 
x_53 = lean::cnstr_get(x_40, 0);
lean::inc(x_53);
x_55 = lean::cnstr_get(x_40, 1);
lean::inc(x_55);
lean::dec(x_40);
x_58 = lean::box(0);
x_59 = l_lean_name_has__dec__eq___main(x_53, x_58);
if (lean::obj_tag(x_59) == 0)
{
obj* x_63; 
lean::dec(x_55);
lean::dec(x_42);
lean::dec(x_59);
x_63 = l_lean_parser_level_trailing_has__view_x_27___lambda__1___closed__1;
lean::inc(x_63);
return x_63;
}
else
{
lean::dec(x_59);
if (lean::obj_tag(x_42) == 0)
{
obj* x_68; 
lean::dec(x_55);
lean::dec(x_42);
x_68 = l_lean_parser_level_trailing_has__view_x_27___lambda__1___closed__1;
lean::inc(x_68);
return x_68;
}
else
{
obj* x_70; obj* x_72; 
x_70 = lean::cnstr_get(x_42, 0);
lean::inc(x_70);
x_72 = lean::cnstr_get(x_42, 1);
lean::inc(x_72);
lean::dec(x_42);
if (lean::obj_tag(x_72) == 0)
{
lean::dec(x_72);
x_1 = x_70;
x_2 = x_55;
goto lbl_3;
}
else
{
obj* x_79; 
lean::dec(x_70);
lean::dec(x_72);
lean::dec(x_55);
x_79 = l_lean_parser_level_trailing_has__view_x_27___lambda__1___closed__1;
lean::inc(x_79);
return x_79;
}
}
}
}
}
}
}
else
{
obj* x_83; 
lean::dec(x_29);
lean::dec(x_27);
x_83 = l_lean_parser_level_trailing_has__view_x_27___lambda__1___closed__1;
lean::inc(x_83);
return x_83;
}
}
}
}
lbl_3:
{
obj* x_85; obj* x_86; 
x_85 = lean::mk_nat_obj(0u);
x_86 = lean::nat_dec_eq(x_2, x_85);
lean::dec(x_85);
lean::dec(x_2);
if (lean::obj_tag(x_86) == 0)
{
obj* x_90; obj* x_91; obj* x_93; obj* x_94; 
lean::dec(x_86);
x_90 = l_lean_parser_level_add__lit_has__view;
x_91 = lean::cnstr_get(x_90, 0);
lean::inc(x_91);
x_93 = lean::apply_1(x_91, x_1);
x_94 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_94, 0, x_93);
return x_94;
}
else
{
obj* x_96; obj* x_97; obj* x_99; obj* x_100; 
lean::dec(x_86);
x_96 = l_lean_parser_level_app_has__view;
x_97 = lean::cnstr_get(x_96, 0);
lean::inc(x_97);
x_99 = lean::apply_1(x_97, x_1);
x_100 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_100, 0, x_99);
return x_100;
}
}
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
obj* x_5; obj* x_6; 
x_5 = lean::mk_nat_obj(0u);
x_6 = lean::nat_dec_eq(x_1, x_5);
lean::dec(x_5);
lean::dec(x_1);
if (lean::obj_tag(x_6) == 0)
{
obj* x_10; obj* x_11; obj* x_13; obj* x_14; 
lean::dec(x_6);
x_10 = l_lean_parser_level_add__lit_has__view;
x_11 = lean::cnstr_get(x_10, 0);
lean::inc(x_11);
x_13 = lean::apply_1(x_11, x_0);
x_14 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_14, 0, x_13);
return x_14;
}
else
{
obj* x_16; obj* x_17; obj* x_19; obj* x_20; 
lean::dec(x_6);
x_16 = l_lean_parser_level_app_has__view;
x_17 = lean::cnstr_get(x_16, 0);
lean::inc(x_17);
x_19 = lean::apply_1(x_17, x_0);
x_20 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_20, 0, x_19);
return x_20;
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
x_2 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
x_3 = lean::mk_string("parser");
x_4 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_4, 0, x_2);
lean::cnstr_set(x_4, 1, x_3);
x_5 = lean::mk_string("level");
x_6 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_6, 0, x_4);
lean::cnstr_set(x_6, 1, x_5);
x_7 = lean::mk_string("trailing");
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set(x_8, 1, x_7);
return x_8;
}
}
obj* l_lean_parser_level_trailing_has__view_x_27___lambda__2(obj* x_0) {
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
x_5 = l_lean_parser_level_app_has__view;
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
x_15 = l_lean_parser_level_trailing;
lean::inc(x_15);
x_17 = l_lean_parser_syntax_mk__node(x_15, x_14);
return x_17;
}
else
{
obj* x_18; obj* x_21; obj* x_22; obj* x_24; obj* x_26; obj* x_27; obj* x_29; obj* x_30; obj* x_31; obj* x_33; 
x_18 = lean::cnstr_get(x_0, 0);
lean::inc(x_18);
lean::dec(x_0);
x_21 = l_lean_parser_level_add__lit_has__view;
x_22 = lean::cnstr_get(x_21, 1);
lean::inc(x_22);
x_24 = lean::apply_1(x_22, x_18);
lean::inc(x_1);
x_26 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_26, 0, x_24);
lean::cnstr_set(x_26, 1, x_1);
x_27 = l_lean_parser_detail__ident__part_has__view_x_27___lambda__2___closed__2;
lean::inc(x_27);
x_29 = l_lean_parser_syntax_mk__node(x_27, x_26);
x_30 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_1);
x_31 = l_lean_parser_level_trailing;
lean::inc(x_31);
x_33 = l_lean_parser_syntax_mk__node(x_31, x_30);
return x_33;
}
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
obj* _init_l_lean_parser_level_trailing_parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_level_add__lit_parser), 5, 0);
lean::inc(x_0);
x_3 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_level_app_parser), 5, 0);
x_5 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_3);
x_6 = lean::mk_nat_obj(0u);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_choice__aux___main___at_lean_parser_level_trailing_parser___spec__1), 7, 2);
lean::closure_set(x_7, 0, x_5);
lean::closure_set(x_7, 1, x_6);
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_0);
return x_8;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_level_trailing_parser___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
obj* x_12; obj* x_13; unsigned char x_14; obj* x_15; obj* x_16; obj* x_17; 
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
obj* l_lean_parser_monad__parsec_error___at_lean_parser_level_trailing_parser___spec__2(obj* x_0) {
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__parsec_error___at_lean_parser_level_trailing_parser___spec__2___rarg), 9, 0);
return x_2;
}
}
obj* l_lean_parser_combinators_choice__aux___main___at_lean_parser_level_trailing_parser___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_9; obj* x_10; obj* x_11; obj* x_15; 
lean::dec(x_0);
lean::dec(x_1);
x_9 = lean::box(0);
x_10 = l_lean_parser_combinators_choice__aux___main___rarg___closed__1;
x_11 = l_mjoin___rarg___closed__1;
lean::inc(x_9);
lean::inc(x_11);
lean::inc(x_10);
x_15 = l_lean_parser_monad__parsec_error___at_lean_parser_level_trailing_parser___spec__2___rarg(x_10, x_11, x_9, x_9, x_2, x_3, x_4, x_5, x_6);
return x_15;
}
else
{
obj* x_16; obj* x_18; obj* x_20; obj* x_25; obj* x_26; obj* x_28; obj* x_30; obj* x_31; obj* x_32; 
x_16 = lean::cnstr_get(x_0, 0);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_0, 1);
lean::inc(x_18);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_20 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 x_20 = x_0;
}
lean::inc(x_5);
lean::inc(x_4);
lean::inc(x_3);
lean::inc(x_2);
x_25 = lean::apply_5(x_16, x_2, x_3, x_4, x_5, x_6);
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
x_31 = lean::mk_nat_obj(1u);
x_32 = lean::nat_add(x_1, x_31);
lean::dec(x_31);
if (lean::obj_tag(x_26) == 0)
{
obj* x_34; obj* x_36; obj* x_38; obj* x_40; obj* x_41; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_48; obj* x_49; 
x_34 = lean::cnstr_get(x_26, 0);
lean::inc(x_34);
x_36 = lean::cnstr_get(x_26, 1);
lean::inc(x_36);
x_38 = lean::cnstr_get(x_26, 2);
lean::inc(x_38);
if (lean::is_shared(x_26)) {
 lean::dec(x_26);
 x_40 = lean::box(0);
} else {
 lean::cnstr_release(x_26, 0);
 lean::cnstr_release(x_26, 1);
 lean::cnstr_release(x_26, 2);
 x_40 = x_26;
}
x_41 = lean::box(0);
lean::inc(x_41);
x_43 = lean::alloc_cnstr(2, 2, 0);
lean::cnstr_set(x_43, 0, x_41);
lean::cnstr_set(x_43, 1, x_1);
if (lean::is_scalar(x_20)) {
 x_44 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_44 = x_20;
}
lean::cnstr_set(x_44, 0, x_34);
lean::cnstr_set(x_44, 1, x_41);
x_45 = l_lean_parser_syntax_mk__node(x_43, x_44);
x_46 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_46);
if (lean::is_scalar(x_40)) {
 x_48 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_48 = x_40;
}
lean::cnstr_set(x_48, 0, x_45);
lean::cnstr_set(x_48, 1, x_36);
lean::cnstr_set(x_48, 2, x_46);
x_49 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_38, x_48);
if (lean::obj_tag(x_49) == 0)
{
obj* x_56; 
lean::dec(x_18);
lean::dec(x_4);
lean::dec(x_5);
lean::dec(x_2);
lean::dec(x_3);
lean::dec(x_32);
if (lean::is_scalar(x_30)) {
 x_56 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_56 = x_30;
}
lean::cnstr_set(x_56, 0, x_49);
lean::cnstr_set(x_56, 1, x_28);
return x_56;
}
else
{
obj* x_57; unsigned char x_59; 
x_57 = lean::cnstr_get(x_49, 0);
lean::inc(x_57);
x_59 = lean::cnstr_get_scalar<unsigned char>(x_49, sizeof(void*)*1);
if (x_59 == 0)
{
obj* x_61; obj* x_62; obj* x_64; obj* x_67; obj* x_68; 
lean::dec(x_49);
x_61 = l_lean_parser_combinators_choice__aux___main___at_lean_parser_level_trailing_parser___spec__1(x_18, x_32, x_2, x_3, x_4, x_5, x_28);
x_62 = lean::cnstr_get(x_61, 0);
lean::inc(x_62);
x_64 = lean::cnstr_get(x_61, 1);
lean::inc(x_64);
lean::dec(x_61);
x_67 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_57, x_62);
if (lean::is_scalar(x_30)) {
 x_68 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_68 = x_30;
}
lean::cnstr_set(x_68, 0, x_67);
lean::cnstr_set(x_68, 1, x_64);
return x_68;
}
else
{
obj* x_76; 
lean::dec(x_18);
lean::dec(x_57);
lean::dec(x_4);
lean::dec(x_5);
lean::dec(x_2);
lean::dec(x_3);
lean::dec(x_32);
if (lean::is_scalar(x_30)) {
 x_76 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_76 = x_30;
}
lean::cnstr_set(x_76, 0, x_49);
lean::cnstr_set(x_76, 1, x_28);
return x_76;
}
}
}
else
{
obj* x_79; unsigned char x_81; obj* x_82; 
lean::dec(x_1);
lean::dec(x_20);
x_79 = lean::cnstr_get(x_26, 0);
lean::inc(x_79);
x_81 = lean::cnstr_get_scalar<unsigned char>(x_26, sizeof(void*)*1);
if (lean::is_shared(x_26)) {
 lean::dec(x_26);
 x_82 = lean::box(0);
} else {
 lean::cnstr_release(x_26, 0);
 x_82 = x_26;
}
if (x_81 == 0)
{
obj* x_84; obj* x_85; obj* x_87; obj* x_90; obj* x_91; 
lean::dec(x_82);
x_84 = l_lean_parser_combinators_choice__aux___main___at_lean_parser_level_trailing_parser___spec__1(x_18, x_32, x_2, x_3, x_4, x_5, x_28);
x_85 = lean::cnstr_get(x_84, 0);
lean::inc(x_85);
x_87 = lean::cnstr_get(x_84, 1);
lean::inc(x_87);
lean::dec(x_84);
x_90 = l_lean_parser_parsec__t_orelse__mk__res___rarg(x_79, x_85);
if (lean::is_scalar(x_30)) {
 x_91 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_91 = x_30;
}
lean::cnstr_set(x_91, 0, x_90);
lean::cnstr_set(x_91, 1, x_87);
return x_91;
}
else
{
obj* x_98; obj* x_99; obj* x_100; 
lean::dec(x_18);
lean::dec(x_4);
lean::dec(x_5);
lean::dec(x_2);
lean::dec(x_3);
lean::dec(x_32);
if (lean::is_scalar(x_82)) {
 x_98 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_98 = x_82;
}
lean::cnstr_set(x_98, 0, x_79);
lean::cnstr_set_scalar(x_98, sizeof(void*)*1, x_81);
x_99 = x_98;
if (lean::is_scalar(x_30)) {
 x_100 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_100 = x_30;
}
lean::cnstr_set(x_100, 0, x_99);
lean::cnstr_set(x_100, 1, x_28);
return x_100;
}
}
}
}
}
obj* _init_l_lean_parser_level_trailing_parser_lean_parser_has__view() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_21; 
x_0 = lean::box(0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_level_add__lit_parser), 5, 0);
lean::inc(x_0);
x_3 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_level_app_parser), 5, 0);
x_5 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_3);
x_6 = lean::mk_nat_obj(0u);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_combinators_choice__aux___main___at_lean_parser_level_trailing_parser___spec__1), 7, 2);
lean::closure_set(x_7, 0, x_5);
lean::closure_set(x_7, 1, x_6);
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_0);
x_9 = l_lean_parser_trailing__level__parser__m_monad;
x_10 = l_lean_parser_trailing__level__parser__m_monad__except;
x_11 = l_lean_parser_trailing__level__parser__m_lean_parser_monad__parsec;
x_12 = l_lean_parser_trailing__level__parser__m_alternative;
x_13 = l_lean_parser_level_trailing;
x_14 = l_lean_parser_level_trailing_has__view;
lean::inc(x_14);
lean::inc(x_13);
lean::inc(x_12);
lean::inc(x_11);
lean::inc(x_10);
lean::inc(x_9);
x_21 = l_lean_parser_combinators_node_view___rarg(x_9, x_10, x_11, x_12, x_13, x_8, x_14);
return x_21;
}
}
obj* _init_l_lean_parser_level_trailing_parser_lean_parser_has__tokens() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_0 = lean::box(0);
x_1 = l_lean_parser_level_add__lit_parser_lean_parser_has__tokens;
lean::inc(x_0);
lean::inc(x_1);
x_4 = l_lean_parser_list_cons_tokens___rarg(x_1, x_0);
x_5 = l_lean_parser_level_app_parser_lean_parser_has__tokens;
lean::inc(x_5);
x_7 = l_lean_parser_list_cons_tokens___rarg(x_5, x_4);
x_8 = l_lean_parser_tokens___rarg(x_7);
x_9 = l_lean_parser_list_cons_tokens___rarg(x_8, x_0);
x_10 = l_lean_parser_tokens___rarg(x_9);
return x_10;
}
}
obj* l_lean_parser_level__parser_run(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_8; 
x_4 = l_lean_parser_level__parser_run___closed__1;
x_5 = l_lean_parser_level__parser_run___closed__2;
lean::inc(x_5);
lean::inc(x_4);
x_8 = l_lean_parser_pratt__parser___at_lean_parser_level__parser_run___spec__1(x_4, x_5, x_0, x_1, x_2, x_3);
return x_8;
}
}
obj* _init_l_lean_parser_level__parser_run___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_level_leading_parser), 4, 0);
return x_0;
}
}
obj* _init_l_lean_parser_level__parser_run___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_level_trailing_parser), 5, 0);
return x_0;
}
}
obj* l_lean_parser_monad__parsec_error___at_lean_parser_level__parser_run___spec__3___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
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
lean::dec(x_11);
lean::dec(x_0);
lean::dec(x_1);
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
obj* x_42; obj* x_43; obj* x_44; obj* x_48; obj* x_49; obj* x_51; obj* x_54; obj* x_56; obj* x_58; obj* x_59; obj* x_60; 
lean::dec(x_17);
lean::dec(x_39);
x_42 = lean::box(0);
x_43 = l_lean_parser_curr__lbp___rarg___lambda__1___closed__1;
x_44 = l_mjoin___rarg___closed__1;
lean::inc(x_42);
lean::inc(x_44);
lean::inc(x_43);
x_48 = l_lean_parser_monad__parsec_error___at_lean_parser_level__parser_run___spec__3___rarg(x_43, x_44, x_42, x_42, x_0, x_1, x_13, x_8);
x_49 = lean::cnstr_get(x_48, 0);
lean::inc(x_49);
x_51 = lean::cnstr_get(x_48, 1);
lean::inc(x_51);
lean::dec(x_48);
x_54 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_54);
x_56 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_54, x_49);
lean::inc(x_54);
x_58 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_54, x_56);
x_59 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_58);
if (lean::is_scalar(x_10)) {
 x_60 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_60 = x_10;
}
lean::cnstr_set(x_60, 0, x_59);
lean::cnstr_set(x_60, 1, x_51);
return x_60;
}
else
{
obj* x_63; obj* x_66; obj* x_69; obj* x_72; obj* x_74; obj* x_75; obj* x_76; 
lean::dec(x_0);
lean::dec(x_1);
x_63 = lean::cnstr_get(x_39, 0);
lean::inc(x_63);
lean::dec(x_39);
x_66 = lean::cnstr_get(x_63, 1);
lean::inc(x_66);
lean::dec(x_63);
x_69 = lean::cnstr_get(x_66, 1);
lean::inc(x_69);
lean::dec(x_66);
x_72 = l_lean_parser_match__token___closed__2;
lean::inc(x_72);
if (lean::is_scalar(x_17)) {
 x_74 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_74 = x_17;
}
lean::cnstr_set(x_74, 0, x_69);
lean::cnstr_set(x_74, 1, x_13);
lean::cnstr_set(x_74, 2, x_72);
x_75 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_74);
if (lean::is_scalar(x_10)) {
 x_76 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_76 = x_10;
}
lean::cnstr_set(x_76, 0, x_75);
lean::cnstr_set(x_76, 1, x_8);
return x_76;
}
}
case 1:
{
obj* x_80; obj* x_81; obj* x_84; obj* x_85; obj* x_86; 
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_27);
x_80 = l_lean_parser_max__prec;
x_81 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_81);
lean::inc(x_80);
if (lean::is_scalar(x_17)) {
 x_84 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_84 = x_17;
}
lean::cnstr_set(x_84, 0, x_80);
lean::cnstr_set(x_84, 1, x_13);
lean::cnstr_set(x_84, 2, x_81);
x_85 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_84);
if (lean::is_scalar(x_10)) {
 x_86 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_86 = x_10;
}
lean::cnstr_set(x_86, 0, x_85);
lean::cnstr_set(x_86, 1, x_8);
return x_86;
}
case 2:
{
obj* x_87; obj* x_90; obj* x_93; obj* x_96; 
x_87 = lean::cnstr_get(x_27, 0);
lean::inc(x_87);
lean::dec(x_27);
x_90 = lean::cnstr_get(x_87, 0);
lean::inc(x_90);
lean::dec(x_87);
x_93 = l_lean_parser_number_has__view_x_27___lambda__1___closed__6;
lean::inc(x_93);
lean::inc(x_90);
x_96 = l_lean_name_has__dec__eq___main(x_90, x_93);
if (lean::obj_tag(x_96) == 0)
{
obj* x_98; obj* x_100; 
lean::dec(x_96);
x_98 = l_lean_parser_curr__lbp___rarg___lambda__3___closed__1;
lean::inc(x_98);
x_100 = l_lean_name_has__dec__eq___main(x_90, x_98);
if (lean::obj_tag(x_100) == 0)
{
obj* x_103; obj* x_104; obj* x_105; obj* x_109; obj* x_110; obj* x_112; obj* x_115; obj* x_116; 
lean::dec(x_100);
lean::dec(x_17);
x_103 = lean::box(0);
x_104 = l_lean_parser_curr__lbp___rarg___lambda__3___closed__2;
x_105 = l_mjoin___rarg___closed__1;
lean::inc(x_103);
lean::inc(x_105);
lean::inc(x_104);
x_109 = l_lean_parser_monad__parsec_error___at_lean_parser_level__parser_run___spec__3___rarg(x_104, x_105, x_103, x_103, x_0, x_1, x_13, x_8);
x_110 = lean::cnstr_get(x_109, 0);
lean::inc(x_110);
x_112 = lean::cnstr_get(x_109, 1);
lean::inc(x_112);
lean::dec(x_109);
x_115 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_110);
if (lean::is_scalar(x_10)) {
 x_116 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_116 = x_10;
}
lean::cnstr_set(x_116, 0, x_115);
lean::cnstr_set(x_116, 1, x_112);
return x_116;
}
else
{
obj* x_120; obj* x_121; obj* x_124; obj* x_125; obj* x_126; 
lean::dec(x_100);
lean::dec(x_0);
lean::dec(x_1);
x_120 = l_lean_parser_max__prec;
x_121 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_121);
lean::inc(x_120);
if (lean::is_scalar(x_17)) {
 x_124 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_124 = x_17;
}
lean::cnstr_set(x_124, 0, x_120);
lean::cnstr_set(x_124, 1, x_13);
lean::cnstr_set(x_124, 2, x_121);
x_125 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_124);
if (lean::is_scalar(x_10)) {
 x_126 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_126 = x_10;
}
lean::cnstr_set(x_126, 0, x_125);
lean::cnstr_set(x_126, 1, x_8);
return x_126;
}
}
else
{
obj* x_131; obj* x_132; obj* x_135; obj* x_136; obj* x_137; 
lean::dec(x_96);
lean::dec(x_90);
lean::dec(x_0);
lean::dec(x_1);
x_131 = l_lean_parser_max__prec;
x_132 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_132);
lean::inc(x_131);
if (lean::is_scalar(x_17)) {
 x_135 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_135 = x_17;
}
lean::cnstr_set(x_135, 0, x_131);
lean::cnstr_set(x_135, 1, x_13);
lean::cnstr_set(x_135, 2, x_132);
x_136 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_135);
if (lean::is_scalar(x_10)) {
 x_137 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_137 = x_10;
}
lean::cnstr_set(x_137, 0, x_136);
lean::cnstr_set(x_137, 1, x_8);
return x_137;
}
}
default:
{
obj* x_140; obj* x_141; obj* x_142; obj* x_146; obj* x_147; obj* x_149; obj* x_152; obj* x_153; 
lean::dec(x_17);
lean::dec(x_27);
x_140 = lean::box(0);
x_141 = l_lean_parser_curr__lbp___rarg___lambda__3___closed__2;
x_142 = l_mjoin___rarg___closed__1;
lean::inc(x_140);
lean::inc(x_142);
lean::inc(x_141);
x_146 = l_lean_parser_monad__parsec_error___at_lean_parser_level__parser_run___spec__3___rarg(x_141, x_142, x_140, x_140, x_0, x_1, x_13, x_8);
x_147 = lean::cnstr_get(x_146, 0);
lean::inc(x_147);
x_149 = lean::cnstr_get(x_146, 1);
lean::inc(x_149);
lean::dec(x_146);
x_152 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_15, x_147);
if (lean::is_scalar(x_10)) {
 x_153 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_153 = x_10;
}
lean::cnstr_set(x_153, 0, x_152);
lean::cnstr_set(x_153, 1, x_149);
return x_153;
}
}
}
}
else
{
obj* x_156; unsigned char x_158; obj* x_159; obj* x_160; obj* x_161; obj* x_162; 
lean::dec(x_0);
lean::dec(x_1);
x_156 = lean::cnstr_get(x_6, 0);
lean::inc(x_156);
x_158 = lean::cnstr_get_scalar<unsigned char>(x_6, sizeof(void*)*1);
if (lean::is_shared(x_6)) {
 lean::dec(x_6);
 x_159 = lean::box(0);
} else {
 lean::cnstr_release(x_6, 0);
 x_159 = x_6;
}
if (lean::is_scalar(x_159)) {
 x_160 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_160 = x_159;
}
lean::cnstr_set(x_160, 0, x_156);
lean::cnstr_set_scalar(x_160, sizeof(void*)*1, x_158);
x_161 = x_160;
if (lean::is_scalar(x_10)) {
 x_162 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_162 = x_10;
}
lean::cnstr_set(x_162, 0, x_161);
lean::cnstr_set(x_162, 1, x_8);
return x_162;
}
}
}
obj* l___private_1055111885__trailing__loop___main___at_lean_parser_level__parser_run___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; obj* x_9; 
x_8 = lean::mk_nat_obj(0u);
x_9 = lean::nat_dec_eq(x_2, x_8);
lean::dec(x_8);
if (lean::obj_tag(x_9) == 0)
{
obj* x_14; obj* x_15; obj* x_17; obj* x_19; 
lean::dec(x_9);
lean::inc(x_5);
lean::inc(x_4);
x_14 = l_lean_parser_curr__lbp___at_lean_parser_level__parser_run___spec__4(x_4, x_5, x_6, x_7);
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
obj* x_20; obj* x_22; obj* x_24; obj* x_26; obj* x_27; 
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
x_27 = lean::nat_dec_lt(x_1, x_20);
lean::dec(x_20);
if (lean::obj_tag(x_27) == 0)
{
obj* x_35; obj* x_37; obj* x_38; obj* x_39; 
lean::dec(x_4);
lean::dec(x_5);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_27);
x_35 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_35);
if (lean::is_scalar(x_26)) {
 x_37 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_37 = x_26;
}
lean::cnstr_set(x_37, 0, x_3);
lean::cnstr_set(x_37, 1, x_22);
lean::cnstr_set(x_37, 2, x_35);
x_38 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_24, x_37);
if (lean::is_scalar(x_19)) {
 x_39 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_39 = x_19;
}
lean::cnstr_set(x_39, 0, x_38);
lean::cnstr_set(x_39, 1, x_17);
return x_39;
}
else
{
obj* x_42; obj* x_43; obj* x_49; obj* x_50; obj* x_52; 
lean::dec(x_26);
lean::dec(x_27);
x_42 = lean::mk_nat_obj(1u);
x_43 = lean::nat_sub(x_2, x_42);
lean::dec(x_42);
lean::dec(x_2);
lean::inc(x_5);
lean::inc(x_4);
lean::inc(x_0);
x_49 = lean::apply_5(x_0, x_3, x_4, x_5, x_22, x_17);
x_50 = lean::cnstr_get(x_49, 0);
lean::inc(x_50);
x_52 = lean::cnstr_get(x_49, 1);
lean::inc(x_52);
lean::dec(x_49);
if (lean::obj_tag(x_50) == 0)
{
obj* x_55; obj* x_57; obj* x_59; obj* x_62; obj* x_63; obj* x_65; obj* x_68; obj* x_69; obj* x_70; 
x_55 = lean::cnstr_get(x_50, 0);
lean::inc(x_55);
x_57 = lean::cnstr_get(x_50, 1);
lean::inc(x_57);
x_59 = lean::cnstr_get(x_50, 2);
lean::inc(x_59);
lean::dec(x_50);
x_62 = l___private_1055111885__trailing__loop___main___at_lean_parser_level__parser_run___spec__2(x_0, x_1, x_43, x_55, x_4, x_5, x_57, x_52);
x_63 = lean::cnstr_get(x_62, 0);
lean::inc(x_63);
x_65 = lean::cnstr_get(x_62, 1);
lean::inc(x_65);
lean::dec(x_62);
x_68 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_59, x_63);
x_69 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_24, x_68);
if (lean::is_scalar(x_19)) {
 x_70 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_70 = x_19;
}
lean::cnstr_set(x_70, 0, x_69);
lean::cnstr_set(x_70, 1, x_65);
return x_70;
}
else
{
obj* x_76; unsigned char x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; 
lean::dec(x_43);
lean::dec(x_4);
lean::dec(x_5);
lean::dec(x_0);
lean::dec(x_1);
x_76 = lean::cnstr_get(x_50, 0);
lean::inc(x_76);
x_78 = lean::cnstr_get_scalar<unsigned char>(x_50, sizeof(void*)*1);
if (lean::is_shared(x_50)) {
 lean::dec(x_50);
 x_79 = lean::box(0);
} else {
 lean::cnstr_release(x_50, 0);
 x_79 = x_50;
}
if (lean::is_scalar(x_79)) {
 x_80 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_80 = x_79;
}
lean::cnstr_set(x_80, 0, x_76);
lean::cnstr_set_scalar(x_80, sizeof(void*)*1, x_78);
x_81 = x_80;
x_82 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_24, x_81);
if (lean::is_scalar(x_19)) {
 x_83 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_83 = x_19;
}
lean::cnstr_set(x_83, 0, x_82);
lean::cnstr_set(x_83, 1, x_52);
return x_83;
}
}
}
else
{
obj* x_90; unsigned char x_92; obj* x_93; obj* x_94; obj* x_95; obj* x_96; 
lean::dec(x_4);
lean::dec(x_5);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
x_90 = lean::cnstr_get(x_15, 0);
lean::inc(x_90);
x_92 = lean::cnstr_get_scalar<unsigned char>(x_15, sizeof(void*)*1);
if (lean::is_shared(x_15)) {
 lean::dec(x_15);
 x_93 = lean::box(0);
} else {
 lean::cnstr_release(x_15, 0);
 x_93 = x_15;
}
if (lean::is_scalar(x_93)) {
 x_94 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_94 = x_93;
}
lean::cnstr_set(x_94, 0, x_90);
lean::cnstr_set_scalar(x_94, sizeof(void*)*1, x_92);
x_95 = x_94;
if (lean::is_scalar(x_19)) {
 x_96 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_96 = x_19;
}
lean::cnstr_set(x_96, 0, x_95);
lean::cnstr_set(x_96, 1, x_17);
return x_96;
}
}
else
{
obj* x_102; obj* x_103; obj* x_104; obj* x_108; 
lean::dec(x_9);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
x_102 = lean::box(0);
x_103 = l___private_1297690757__many1__aux___main___rarg___closed__1;
x_104 = l_mjoin___rarg___closed__1;
lean::inc(x_102);
lean::inc(x_104);
lean::inc(x_103);
x_108 = l_lean_parser_monad__parsec_error___at_lean_parser_level__parser_run___spec__3___rarg(x_103, x_104, x_102, x_102, x_4, x_5, x_6, x_7);
return x_108;
}
}
}
obj* l___private_3693562977__run__aux___at_lean_parser_level__parser_run___spec__7(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_8; 
x_7 = l___private_3693562977__run__aux___main___rarg(x_0, x_1, x_2, x_3);
x_8 = lean::apply_3(x_7, x_4, x_5, x_6);
return x_8;
}
}
obj* l_lean_parser_rec__t_run___at_lean_parser_level__parser_run___spec__6(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_8; 
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l___private_3693562977__run__aux___at_lean_parser_level__parser_run___spec__7), 7, 3);
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
obj* x_5; obj* x_6; obj* x_7; obj* x_10; obj* x_12; obj* x_13; obj* x_15; obj* x_17; obj* x_18; obj* x_20; obj* x_21; 
x_5 = lean::string_iterator_remaining(x_3);
x_6 = lean::mk_nat_obj(1u);
x_7 = lean::nat_add(x_5, x_6);
lean::dec(x_6);
lean::dec(x_5);
x_10 = l_lean_parser_rec__t_run__parsec___at_lean_parser_level__parser_run___spec__5___closed__1;
lean::inc(x_10);
x_12 = l_lean_parser_rec__t_run___at_lean_parser_level__parser_run___spec__6(x_0, x_10, x_1, x_7, x_2, x_3, x_4);
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
obj* _init_l_lean_parser_rec__t_run__parsec___at_lean_parser_level__parser_run___spec__5___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_rec__t_run__parsec___at_lean_parser_level__parser_run___spec__5___lambda__1), 4, 0);
return x_0;
}
}
obj* l_lean_parser_rec__t_run__parsec___at_lean_parser_level__parser_run___spec__5___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
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
obj* x_15; obj* x_17; obj* x_19; obj* x_22; obj* x_23; obj* x_24; obj* x_27; obj* x_28; obj* x_30; obj* x_33; obj* x_35; obj* x_36; obj* x_37; 
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
lean::dec(x_23);
lean::dec(x_22);
x_27 = l___private_1055111885__trailing__loop___main___at_lean_parser_level__parser_run___spec__2(x_1, x_2, x_24, x_15, x_3, x_4, x_17, x_12);
x_28 = lean::cnstr_get(x_27, 0);
lean::inc(x_28);
x_30 = lean::cnstr_get(x_27, 1);
lean::inc(x_30);
lean::dec(x_27);
x_33 = l_lean_parser_finish__comment__block___closed__2;
lean::inc(x_33);
x_35 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_33, x_28);
x_36 = l_lean_parser_parsec__t_bind__mk__res___rarg(x_19, x_35);
if (lean::is_scalar(x_14)) {
 x_37 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_37 = x_14;
}
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_30);
return x_37;
}
else
{
obj* x_42; unsigned char x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; 
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
x_42 = lean::cnstr_get(x_10, 0);
lean::inc(x_42);
x_44 = lean::cnstr_get_scalar<unsigned char>(x_10, sizeof(void*)*1);
if (lean::is_shared(x_10)) {
 lean::dec(x_10);
 x_45 = lean::box(0);
} else {
 lean::cnstr_release(x_10, 0);
 x_45 = x_10;
}
if (lean::is_scalar(x_45)) {
 x_46 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_46 = x_45;
}
lean::cnstr_set(x_46, 0, x_42);
lean::cnstr_set_scalar(x_46, sizeof(void*)*1, x_44);
x_47 = x_46;
if (lean::is_scalar(x_14)) {
 x_48 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_48 = x_14;
}
lean::cnstr_set(x_48, 0, x_47);
lean::cnstr_set(x_48, 1, x_12);
return x_48;
}
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
x_7 = l_lean_parser_level__parser_run___closed__1;
x_8 = l_lean_parser_level__parser_run___closed__2;
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
obj* _init_l_lean_parser_level__parser_run_lean_parser_has__view___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_has__monad__lift__t__refl), 2, 1);
lean::closure_set(x_0, 0, lean::box(0));
return x_0;
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
x_6 = l_list_append___main___rarg(x_2, x_3);
return x_6;
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
 l_lean_parser_level__parser__m = _init_l_lean_parser_level__parser__m();
 l_lean_parser_level__parser__m_lean_parser_monad__basic__parser = _init_l_lean_parser_level__parser__m_lean_parser_monad__basic__parser();
 l_lean_parser_level__parser__m_lean_parser_monad__rec = _init_l_lean_parser_level__parser__m_lean_parser_monad__rec();
 l_lean_parser_level__parser__m_monad__except = _init_l_lean_parser_level__parser__m_monad__except();
 l_lean_parser_level__parser__m_lean_parser_monad__parsec = _init_l_lean_parser_level__parser__m_lean_parser_monad__parsec();
 l_lean_parser_level__parser__m_monad__reader = _init_l_lean_parser_level__parser__m_monad__reader();
 l_lean_parser_level__parser__m_alternative = _init_l_lean_parser_level__parser__m_alternative();
 l_lean_parser_level__parser__m_monad = _init_l_lean_parser_level__parser__m_monad();
 l_lean_parser_level__parser = _init_l_lean_parser_level__parser();
 l_lean_parser_trailing__level__parser__m = _init_l_lean_parser_trailing__level__parser__m();
 l_lean_parser_trailing__level__parser__m_lean_parser_monad__basic__parser = _init_l_lean_parser_trailing__level__parser__m_lean_parser_monad__basic__parser();
 l_lean_parser_trailing__level__parser__m_lean_parser_monad__rec = _init_l_lean_parser_trailing__level__parser__m_lean_parser_monad__rec();
 l_lean_parser_trailing__level__parser__m_monad__except = _init_l_lean_parser_trailing__level__parser__m_monad__except();
 l_lean_parser_trailing__level__parser__m_lean_parser_monad__parsec = _init_l_lean_parser_trailing__level__parser__m_lean_parser_monad__parsec();
 l_lean_parser_trailing__level__parser__m_monad__reader = _init_l_lean_parser_trailing__level__parser__m_monad__reader();
 l_lean_parser_trailing__level__parser__m_alternative = _init_l_lean_parser_trailing__level__parser__m_alternative();
 l_lean_parser_trailing__level__parser__m_monad = _init_l_lean_parser_trailing__level__parser__m_monad();
 l_lean_parser_trailing__level__parser = _init_l_lean_parser_trailing__level__parser();
 l_lean_parser_level_parser___closed__1 = _init_l_lean_parser_level_parser___closed__1();
 l_lean_parser_level_parser_lean_parser_has__view___closed__1 = _init_l_lean_parser_level_parser_lean_parser_has__view___closed__1();
 l_lean_parser_level_parser_lean_parser_has__tokens___closed__1 = _init_l_lean_parser_level_parser_lean_parser_has__tokens___closed__1();
 l_lean_parser_level_lean_parser_has__tokens = _init_l_lean_parser_level_lean_parser_has__tokens();
 l_lean_parser_level_lean_parser_has__view = _init_l_lean_parser_level_lean_parser_has__view();
 l_lean_parser_level_paren = _init_l_lean_parser_level_paren();
 l_lean_parser_level_paren_has__view_x_27 = _init_l_lean_parser_level_paren_has__view_x_27();
 l_lean_parser_level_paren_has__view_x_27___lambda__1___closed__1 = _init_l_lean_parser_level_paren_has__view_x_27___lambda__1___closed__1();
 l_lean_parser_level_paren_has__view = _init_l_lean_parser_level_paren_has__view();
 l_lean_parser_level_paren_parser___closed__1 = _init_l_lean_parser_level_paren_parser___closed__1();
 l_lean_parser_level_paren_parser_lean_parser_has__view = _init_l_lean_parser_level_paren_parser_lean_parser_has__view();
 l_lean_parser_level_paren_parser_lean_parser_has__tokens = _init_l_lean_parser_level_paren_parser_lean_parser_has__tokens();
 l_lean_parser_level_leading = _init_l_lean_parser_level_leading();
 l_lean_parser_level_leading_has__view_x_27 = _init_l_lean_parser_level_leading_has__view_x_27();
 l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__1 = _init_l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__1();
 l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__2 = _init_l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__2();
 l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__3 = _init_l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__3();
 l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__4 = _init_l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__4();
 l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__5 = _init_l_lean_parser_level_leading_has__view_x_27___lambda__1___closed__5();
 l_lean_parser_level_leading_has__view_x_27___lambda__2___closed__1 = _init_l_lean_parser_level_leading_has__view_x_27___lambda__2___closed__1();
 l_lean_parser_level_leading_has__view_x_27___lambda__2___closed__2 = _init_l_lean_parser_level_leading_has__view_x_27___lambda__2___closed__2();
 l_lean_parser_level_leading_has__view = _init_l_lean_parser_level_leading_has__view();
 l_lean_parser_level_leading_parser___closed__1 = _init_l_lean_parser_level_leading_parser___closed__1();
 l_lean_parser_number_parser___at_lean_parser_level_leading_parser___spec__2___rarg___closed__1 = _init_l_lean_parser_number_parser___at_lean_parser_level_leading_parser___spec__2___rarg___closed__1();
 l_lean_parser_ident_parser___at_lean_parser_level_leading_parser___spec__3___rarg___closed__1 = _init_l_lean_parser_ident_parser___at_lean_parser_level_leading_parser___spec__3___rarg___closed__1();
 l_lean_parser_level_leading_parser_lean_parser_has__view = _init_l_lean_parser_level_leading_parser_lean_parser_has__view();
 l_lean_parser_level_leading_parser_lean_parser_has__tokens = _init_l_lean_parser_level_leading_parser_lean_parser_has__tokens();
 l_lean_parser_level_app = _init_l_lean_parser_level_app();
 l_lean_parser_level_app_has__view_x_27 = _init_l_lean_parser_level_app_has__view_x_27();
 l_lean_parser_level_app_has__view_x_27___lambda__1___closed__1 = _init_l_lean_parser_level_app_has__view_x_27___lambda__1___closed__1();
 l_lean_parser_level_app_has__view = _init_l_lean_parser_level_app_has__view();
 l_lean_parser_level_app_parser___closed__1 = _init_l_lean_parser_level_app_parser___closed__1();
 l_lean_parser_level_app_parser_lean_parser_has__view = _init_l_lean_parser_level_app_parser_lean_parser_has__view();
 l_lean_parser_level_app_parser_lean_parser_has__tokens = _init_l_lean_parser_level_app_parser_lean_parser_has__tokens();
 l_lean_parser_level_add__lit = _init_l_lean_parser_level_add__lit();
 l_lean_parser_level_add__lit_has__view_x_27 = _init_l_lean_parser_level_add__lit_has__view_x_27();
 l_lean_parser_level_add__lit_has__view_x_27___lambda__1___closed__1 = _init_l_lean_parser_level_add__lit_has__view_x_27___lambda__1___closed__1();
 l_lean_parser_level_add__lit_has__view_x_27___lambda__1___closed__2 = _init_l_lean_parser_level_add__lit_has__view_x_27___lambda__1___closed__2();
 l_lean_parser_level_add__lit_has__view = _init_l_lean_parser_level_add__lit_has__view();
 l_lean_parser_level_add__lit_parser___closed__1 = _init_l_lean_parser_level_add__lit_parser___closed__1();
 l_lean_parser_level_add__lit_parser_lean_parser_has__view = _init_l_lean_parser_level_add__lit_parser_lean_parser_has__view();
 l_lean_parser_level_add__lit_parser_lean_parser_has__tokens = _init_l_lean_parser_level_add__lit_parser_lean_parser_has__tokens();
 l_lean_parser_level_trailing = _init_l_lean_parser_level_trailing();
 l_lean_parser_level_trailing_has__view_x_27 = _init_l_lean_parser_level_trailing_has__view_x_27();
 l_lean_parser_level_trailing_has__view_x_27___lambda__1___closed__1 = _init_l_lean_parser_level_trailing_has__view_x_27___lambda__1___closed__1();
 l_lean_parser_level_trailing_has__view_x_27___lambda__1___closed__2 = _init_l_lean_parser_level_trailing_has__view_x_27___lambda__1___closed__2();
 l_lean_parser_level_trailing_has__view = _init_l_lean_parser_level_trailing_has__view();
 l_lean_parser_level_trailing_parser___closed__1 = _init_l_lean_parser_level_trailing_parser___closed__1();
 l_lean_parser_level_trailing_parser_lean_parser_has__view = _init_l_lean_parser_level_trailing_parser_lean_parser_has__view();
 l_lean_parser_level_trailing_parser_lean_parser_has__tokens = _init_l_lean_parser_level_trailing_parser_lean_parser_has__tokens();
 l_lean_parser_level__parser_run___closed__1 = _init_l_lean_parser_level__parser_run___closed__1();
 l_lean_parser_level__parser_run___closed__2 = _init_l_lean_parser_level__parser_run___closed__2();
 l_lean_parser_rec__t_run__parsec___at_lean_parser_level__parser_run___spec__5___closed__1 = _init_l_lean_parser_rec__t_run__parsec___at_lean_parser_level__parser_run___spec__5___closed__1();
 l_lean_parser_level__parser_run_lean_parser_has__view___closed__1 = _init_l_lean_parser_level__parser_run_lean_parser_has__view___closed__1();
 l_lean_parser_level__parser__coe = _init_l_lean_parser_level__parser__coe();
}
