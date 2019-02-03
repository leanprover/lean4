// Lean compiler output
// Module: init.lean.parser.basic
// Imports: init.lean.parser.parsec init.lean.parser.syntax init.lean.parser.rec init.lean.parser.trie init.lean.parser.identifier init.data.rbmap.default init.lean.message init.control.coroutine
#include "runtime/object.h"
#include "runtime/apply.h"
#include "runtime/io.h"
#include "kernel/builtin.h"
typedef lean::object obj;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#endif
obj* _l_s4_lean_s6_parser_s9_parsec__t_s3_run_s4___at_s4_lean_s6_parser_s3_run_s9___spec__1_s6___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s18_command__parser__m_s5_monad(obj*);
unsigned char _l_s4_lean_s6_parser_s6_syntax_s12_is__of__kind_s6___main(obj*, obj*);
obj* _l_s4_lean_s6_parser_s4_lean_s6_parser_s13_monad__parsec_s6___rarg(obj*);
obj* _l_s4_lean_s6_parser_s13_basic__parser;
obj* _l_s4_lean_s6_parser_s18_command__parser__m_s13_basic__parser(obj*);
obj* _l_s4_lean_s6_parser_s18_command__parser__m_s22_monad__reader__adapter(obj*, obj*);
obj* _l_s4_lean_s6_parser_s16_basic__parser__m_s5_monad;
obj* _l_s4_lean_s6_parser_s18_command__parser__m_s13_basic__parser_s6___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s18_command__parser__m_s11_alternative(obj*);
unsigned char _l_s6_rbnode_s10_get__color_s6___main_s6___rarg(obj*);
obj* _l_s4_lean_s6_parser_s15_parser__core__t_s4_lean_s6_parser_s13_monad__parsec(obj*);
obj* _l_s4_lean_s6_parser_s28_message__of__parsec__message(obj*);
obj* _l_s6_rbnode_s3_ins_s6___main_s4___at_s4_lean_s6_parser_s10_token__map_s6_insert_s9___spec__5(obj*);
obj* _l_s4_lean_s6_parser_s16_basic__parser__m_s4_lean_s6_parser_s13_monad__parsec;
obj* _l_s4_lean_s6_parser_s18_command__parser__m_s4_lean_s6_parser_s13_monad__parsec_s11___closed__1;
obj* _l_s4_lean_s6_parser_s25_trailing__term__parser__m;
obj* _l_s4_lean_s6_parser_s15_mk__token__trie_s11___closed__1;
obj* _l_s4_lean_s6_parser_s15_parser__core__t_s13_monad__except_s6___rarg(obj*);
obj* _l_s2_id_s5_monad_s11___lambda__2(obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s15_command__parser;
obj* _l_s9_reader__t_s11_alternative_s6___rarg(obj*, obj*);
obj* _l_s4_lean_s6_parser_s4_list_s4_cons_s6_tokens_s6___rarg(obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s16_basic__parser__m_s11_alternative;
obj* _l_s4_lean_s6_parser_s10_get__cache_s6___rarg(obj*, obj*);
obj* _l_s5_rbmap_s6_insert_s6___main_s4___at_s4_lean_s6_parser_s10_token__map_s6_insert_s9___spec__3_s6___rarg(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s16_basic__parser__m_s13_monad__except;
obj* _l_s4_lean_s6_parser_s9_parser__t;
obj* _l_s5_rbmap_s4_find_s6___main_s4___at_s4_lean_s6_parser_s10_token__map_s6_insert_s9___spec__1_s6___rarg(obj*, obj*);
obj* _l_s4_lean_s6_parser_s19_parser__config__coe(obj*);
obj* _l_s4_lean_s6_parser_s6_rec__t_s4_lean_s6_parser_s13_monad__parsec_s6___rarg(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s44_command__parser__config__coe__parser__config(obj*);
obj* _l_s4_lean_s6_parser_s10_monad__rec_s5_trans_s6___rarg(obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s10_token__map;
obj* _l_s4_lean_s6_parser_s6_parsec_s7_message_s4_text_s6___rarg(obj*);
obj* _l_s4_lean_s6_parser_s22_trailing__term__parser;
obj* _l_s4_lean_s6_parser_s10_get__cache(obj*);
obj* _l_s4_lean_s6_parser_s4_list_s4_cons_s6_tokens(obj*);
obj* _l_s4_lean_s6_parser_s27_trailing__term__parser__coe(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
extern obj* _l_s4_lean_s6_parser_s6_parsec_s6_result_s7_mk__eps_s6___rarg_s11___closed__1;
obj* _l_s6_rbnode_s14_balance2__node_s6___main_s6___rarg(obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s10_token__map_s8_of__list_s6___main(obj*);
obj* _l_s4_lean_s6_parser_s15_mk__token__trie(obj*);
obj* _l_s4_lean_s6_parser_s9_parser__t_s4_lean_s6_parser_s13_monad__parsec(obj*, obj*);
obj* _l_s4_lean_s6_parser_s9_parsec__t_s5_monad_s6___rarg(obj*, obj*);
obj* _l_s2_id_s5_monad_s11___lambda__3(obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s18_command__parser__m_s11_alternative_s11___closed__1;
obj* _l_s4_lean_s6_parser_s9_try__view_s6___rarg(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s10_token__map_s8_of__list(obj*);
obj* _l_s4_lean_s6_parser_s25_trailing__term__parser__m_s4_lean_s6_parser_s20_monad__basic__parser;
obj* _l_s6_rbnode_s14_balance1__node_s6___main_s6___rarg(obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s25_trailing__term__parser__m_s13_monad__except;
obj* _l_s6_option_s3_get_s6___main_s4___at_s4_lean_s6_parser_s3_run_s9___spec__2(obj*);
obj* _l_s4_lean_s6_parser_s15_parser__core__t_s11_alternative_s6___rarg(obj*);
obj* _l_s4_lean_s6_parser_s18_command__parser__m;
obj* _l_s6_rbnode_s6_insert_s4___at_s4_lean_s6_parser_s10_token__map_s6_insert_s9___spec__7(obj*);
extern obj* _l_s5_mjoin_s6___rarg_s11___closed__1;
obj* _l_s6_rbnode_s3_ins_s6___main_s4___at_s4_lean_s6_parser_s10_token__map_s6_insert_s9___spec__5_s6___rarg(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s9_has__view_s7_default_s6___rarg(obj*);
obj* _l_s4_lean_s6_parser_s18_command__parser__m_s4_lean_s6_parser_s13_monad__parsec(obj*);
obj* _l_s4_lean_s6_parser_s9_parser__t_s4_lean_s6_parser_s13_monad__parsec_s6___rarg(obj*);
obj* _l_s2_id_s6___rarg(obj*);
obj* _l_s4_lean_s6_parser_s25_trailing__term__parser__m_s13_monad__reader;
obj* _l_s4_lean_s6_parser_s18_command__parser__m_s13_monad__reader_s11___closed__1;
obj* _l_s4_lean_s6_parser_s16_token__map__cons_s6_tokens(obj*, obj*);
obj* _l_s4_lean_s6_parser_s10_token__map_s8_of__list_s6___main_s6___rarg(obj*);
obj* _l_s4_lean_s6_parser_s18_command__parser__m_s4_lean_s6_parser_s10_monad__rec_s11___closed__1;
obj* _l_s4_lean_s6_parser_s25_trailing__term__parser__m_s5_monad;
obj* _l_s6_rbnode_s3_ins_s6___main_s4___at_s4_lean_s6_parser_s10_token__map_s6_insert_s9___spec__8_s6___rarg(obj*, obj*, obj*);
obj* _l_s9_reader__t_s14_monad__functor(obj*, obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s9_parser__t_s13_monad__reader_s6___rarg(obj*);
obj* _l_s4_lean_s6_parser_s28_message__of__parsec__message_s6___rarg(obj*, obj*);
obj* _l_s9_reader__t_s5_monad_s6___rarg(obj*);
obj* _l_s5_rbmap_s6_insert_s6___main_s4___at_s4_lean_s6_parser_s10_token__map_s6_insert_s9___spec__6(obj*);
obj* _l_s4_lean_s6_parser_s15_term__parser__m_s4_lean_s6_parser_s10_monad__rec;
obj* _l_s9_reader__t_s4_lift(obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s18_command__parser__m_s5_monad_s11___closed__1;
obj* _l_s4_lean_s6_parser_s10_token__map_s6_insert_s6___rarg(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s9_parser__t_s5_monad_s6___rarg(obj*);
obj* _l_s4_lean_s6_parser_s25_trailing__term__parser__m_s4_lean_s6_parser_s10_monad__rec;
obj* _l_s4_lean_s6_parser_s9_parser__t_s13_monad__except(obj*, obj*);
obj* _l_s6_rbnode_s4_find_s6___main_s4___at_s4_lean_s6_parser_s10_token__map_s6_insert_s9___spec__2(obj*);
obj* _l_s4_lean_s6_parser_s15_parser__core__t_s4_lean_s6_parser_s13_monad__parsec_s6___rarg(obj*);
obj* _l_s4_lean_s6_parser_s10_put__cache(obj*, obj*, obj*, obj*);
obj* _l_s8_state__t_s5_monad_s6___rarg(obj*);
obj* _l_s4_lean_s6_parser_s20_monad__parsec__trans_s6___rarg(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s9_parsec__t_s3_run_s4___at_s4_lean_s6_parser_s3_run_s9___spec__1_s6___rarg_s11___lambda__1(obj*, obj*);
obj* _l_s4_lean_s6_parser_s15_term__parser__m_s13_monad__except;
obj* _l_s4_lean_s6_parser_s9_parser__t_s5_monad(obj*, obj*);
obj* _l_s4_lean_s4_name_s9_quick__lt_s6___main(obj*, obj*);
obj* _l_s4_lean_s6_parser_s18_command__parser__m_s13_monad__except(obj*);
obj* _l_s26_has__monad__lift__t__trans_s6___rarg(obj*, obj*, obj*, obj*);
obj* _l_s2_id_s5_monad_s11___lambda__1(obj*, obj*, obj*, obj*);
obj* _l_s5_rbmap_s6_insert_s6___main_s4___at_s4_lean_s6_parser_s10_token__map_s6_insert_s9___spec__6_s6___rarg(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s9_parsec__t_s3_run_s4___at_s4_lean_s6_parser_s3_run_s9___spec__1(obj*);
obj* _l_s4_lean_s6_parser_s18_command__parser__m_s13_monad__reader(obj*);
obj* _l_s4_lean_s6_parser_s15_term__parser__m_s13_monad__reader;
obj* _l_s4_lean_s6_parser_s4_list_s3_nil_s6_tokens(obj*);
obj* _l_s4_lean_s6_parser_s15_term__parser__m_s4_lean_s6_parser_s20_monad__basic__parser;
obj* _l_s4_lean_s6_parser_s16_token__map__cons_s6_tokens_s6___rarg(obj*, obj*, obj*, obj*);
obj* _l_s9_reader__t_s4_read_s6___rarg(obj*, obj*);
obj* _l_s4_lean_s6_parser_s15_token__map__nil_s6_tokens(obj*);
obj* _l_s4_lean_s6_parser_s18_command__parser__m_s22_monad__reader__adapter_s11___closed__1;
obj* _l_s4_lean_s6_parser_s15_parser__core__t_s11_alternative(obj*);
obj* _l_s4_list_s6_mfoldl_s6___main_s4___at_s4_lean_s6_parser_s15_mk__token__trie_s9___spec__1_s11___closed__3;
obj* _l_s4_lean_s6_parser_s12_log__message(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s16_basic__parser__m;
obj* _l_s4_lean_s6_parser_s15_term__parser__m_s4_lean_s6_parser_s13_monad__parsec;
obj* _l_s4_lean_s6_parser_s6_tokens_s6___rarg(obj*);
obj* _l_s4_lean_s6_parser_s16_basic__parser__m_s13_monad__reader;
obj* _l_s4_lean_s6_parser_s18_command__parser__m_s4_lean_s6_parser_s10_monad__rec(obj*);
obj* _l_s5_rbmap_s6_insert_s6___main_s4___at_s4_lean_s6_parser_s10_token__map_s6_insert_s9___spec__3(obj*);
obj* _l_s9_reader__t_s22_monad__reader__adapter(obj*, obj*, obj*, obj*, obj*);
obj* _l_s6_rbnode_s4_find_s6___main_s4___at_s4_lean_s6_parser_s10_token__map_s6_insert_s9___spec__2_s6___rarg(obj*, obj*);
extern obj* _l_s6_string_s4_join_s11___closed__1;
obj* _l_s4_lean_s6_parser_s12_log__message_s6___rarg_s11___lambda__2(obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s18_command__parser__m_s13_monad__except_s11___closed__1;
obj* _l_s9_reader__t_s13_monad__except_s6___rarg(obj*);
obj* _l_s9_reader__t_s4_lift_s6___rarg(obj*, obj*);
obj* _l_s4_lean_s6_parser_s15_term__parser__m_s11_alternative;
obj* _l_s4_list_s6_mfoldl_s6___main_s4___at_s4_lean_s6_parser_s15_mk__token__trie_s9___spec__1(obj*, obj*);
obj* _l_s4_lean_s6_parser_s3_run_s6___rarg_s11___lambda__1(obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s4_trie_s6_insert_s6___rarg(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s9_parser__t_s13_monad__except_s6___rarg(obj*);
obj* _l_s3_nat_s4_repr(obj*);
obj* _l_s4_lean_s6_parser_s10_token__map_s6_insert(obj*);
obj* _l_s4_lean_s6_parser_s25_trailing__term__parser__m_s4_lean_s6_parser_s13_monad__parsec;
obj* _l_s4_list_s6_append_s6___main_s6___rarg(obj*, obj*);
obj* _l_s6_rbnode_s6_insert_s4___at_s4_lean_s6_parser_s10_token__map_s6_insert_s9___spec__4(obj*);
obj* _l_s4_lean_s6_parser_s6_rec__t_s7_recurse_s6___rarg(obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s12_term__parser;
obj* _l_s4_list_s6_mfoldl_s6___main_s4___at_s4_lean_s6_parser_s15_mk__token__trie_s9___spec__1_s11___closed__2;
obj* _l_s4_lean_s6_parser_s12_log__message_s6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s15_term__parser__m;
obj* _l_s4_lean_s6_parser_s9_parser__t_s11_alternative(obj*, obj*);
obj* _l_s4_lean_s6_parser_s9_parsec__t_s13_monad__except_s6___rarg(obj*, obj*);
obj* _l_s6_rbnode_s3_ins_s6___main_s4___at_s4_lean_s6_parser_s10_token__map_s6_insert_s9___spec__8(obj*);
obj* _l_s4_lean_s6_parser_s10_token__map_s8_of__list_s6___rarg(obj*);
obj* _l_s4_lean_s6_parser_s15_parser__core__t_s5_monad(obj*);
obj* _l_s4_lean_s6_parser_s15_parser__core__t;
obj* _l_s2_id(obj*);
obj* _l_s4_lean_s6_parser_s11_has__tokens_s9_inhabited(obj*, obj*);
obj* _l_s4_lean_s6_parser_s12_log__message_s6___rarg_s11___lambda__1(obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s15_parser__core__t_s5_monad_s6___rarg(obj*);
obj* _l_s4_lean_s6_parser_s3_run_s6___rarg_s11___closed__1;
obj* _l_s5_rbmap_s4_find_s6___main_s4___at_s4_lean_s6_parser_s10_token__map_s6_insert_s9___spec__1(obj*);
obj* _l_s4_lean_s6_parser_s3_run_s6___rarg(obj*, obj*, obj*, obj*, obj*);
obj* _l_s4_lean_s6_parser_s4_trie_s4_find_s6___rarg(obj*, obj*);
obj* _l_s4_lean_s6_parser_s9_parser__t_s11_alternative_s6___rarg(obj*);
obj* _l_s4_list_s6_mfoldl_s6___main_s4___at_s4_lean_s6_parser_s15_mk__token__trie_s9___spec__1_s11___closed__1;
obj* _l_s4_lean_s6_parser_s9_parsec__t_s11_alternative_s6___rarg(obj*, obj*);
obj* _l_s4_lean_s6_parser_s9_max__prec;
obj* _l_s4_lean_s6_parser_s6_tokens(obj*, obj*);
obj* _l_s4_lean_s6_parser_s15_parser__core__t_s13_monad__except(obj*);
obj* _l_s4_lean_s6_parser_s15_term__parser__m_s5_monad;
obj* _l_s4_lean_s6_parser_s9_has__view_s7_default(obj*);
obj* _l_s4_lean_s6_parser_s20_monad__basic__parser;
obj* _l_s4_lean_s9_file__map_s12_to__position(obj*, obj*);
obj* _l_s2_id_s4_bind(obj*, obj*);
obj* _l_s6_rbnode_s18_mk__insert__result_s6___main_s6___rarg(unsigned char, obj*);
obj* _l_s4_lean_s6_parser_s9_try__view(obj*);
obj* _l_s6_rbnode_s6_insert_s4___at_s4_lean_s6_parser_s10_token__map_s6_insert_s9___spec__4_s6___rarg(obj*, obj*, obj*);
extern obj* _l_s4_lean_s12_message__log_s5_empty;
obj* _l_s4_lean_s6_parser_s3_run(obj*, obj*, obj*);
obj* _l_s6_rbnode_s6_insert_s4___at_s4_lean_s6_parser_s10_token__map_s6_insert_s9___spec__7_s6___rarg(obj*, obj*, obj*);
extern obj* _l_s4_lean_s6_parser_s4_trie_s2_mk_s11___closed__1;
obj* _l_s4_lean_s6_parser_s25_trailing__term__parser__m_s11_alternative;
obj* _l_s4_lean_s6_parser_s9_parser__t_s13_monad__reader(obj*, obj*);
obj* _init__l_s4_lean_s6_parser_s9_max__prec(){
_start:
{
obj* x_0; 
x_0 = lean::mk_nat_obj(1024u);
return x_0;
}
}
obj* _l_s4_lean_s6_parser_s19_parser__config__coe(obj* x_0){
_start:
{
obj* x_1; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
return x_1;
}
}
obj* _init__l_s4_lean_s6_parser_s15_parser__core__t(){
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _l_s4_lean_s6_parser_s15_parser__core__t_s13_monad__except_s6___rarg(obj* x_0){
_start:
{
obj* x_1; obj* x_2; 
x_1 = _l_s8_state__t_s5_monad_s6___rarg(x_0);
x_2 = _l_s4_lean_s6_parser_s9_parsec__t_s13_monad__except_s6___rarg(x_1, lean::box(0));
return x_2;
}
}
obj* _l_s4_lean_s6_parser_s15_parser__core__t_s13_monad__except(obj* x_0){
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s15_parser__core__t_s13_monad__except_s6___rarg), 1, 0);
return x_2;
}
}
obj* _l_s4_lean_s6_parser_s15_parser__core__t_s4_lean_s6_parser_s13_monad__parsec_s6___rarg(obj* x_0){
_start:
{
obj* x_1; obj* x_2; 
x_1 = _l_s8_state__t_s5_monad_s6___rarg(x_0);
x_2 = _l_s4_lean_s6_parser_s4_lean_s6_parser_s13_monad__parsec_s6___rarg(x_1);
return x_2;
}
}
obj* _l_s4_lean_s6_parser_s15_parser__core__t_s4_lean_s6_parser_s13_monad__parsec(obj* x_0){
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s15_parser__core__t_s4_lean_s6_parser_s13_monad__parsec_s6___rarg), 1, 0);
return x_2;
}
}
obj* _l_s4_lean_s6_parser_s15_parser__core__t_s11_alternative_s6___rarg(obj* x_0){
_start:
{
obj* x_1; obj* x_2; 
x_1 = _l_s8_state__t_s5_monad_s6___rarg(x_0);
x_2 = _l_s4_lean_s6_parser_s9_parsec__t_s11_alternative_s6___rarg(x_1, lean::box(0));
return x_2;
}
}
obj* _l_s4_lean_s6_parser_s15_parser__core__t_s11_alternative(obj* x_0){
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s15_parser__core__t_s11_alternative_s6___rarg), 1, 0);
return x_2;
}
}
obj* _l_s4_lean_s6_parser_s15_parser__core__t_s5_monad_s6___rarg(obj* x_0){
_start:
{
obj* x_1; obj* x_2; 
x_1 = _l_s8_state__t_s5_monad_s6___rarg(x_0);
x_2 = _l_s4_lean_s6_parser_s9_parsec__t_s5_monad_s6___rarg(x_1, lean::box(0));
return x_2;
}
}
obj* _l_s4_lean_s6_parser_s15_parser__core__t_s5_monad(obj* x_0){
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s15_parser__core__t_s5_monad_s6___rarg), 1, 0);
return x_2;
}
}
obj* _init__l_s4_lean_s6_parser_s9_parser__t(){
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _l_s4_lean_s6_parser_s9_parser__t_s13_monad__except_s6___rarg(obj* x_0){
_start:
{
obj* x_1; obj* x_2; 
x_1 = _l_s4_lean_s6_parser_s15_parser__core__t_s13_monad__except_s6___rarg(x_0);
x_2 = _l_s9_reader__t_s13_monad__except_s6___rarg(x_1);
return x_2;
}
}
obj* _l_s4_lean_s6_parser_s9_parser__t_s13_monad__except(obj* x_0, obj* x_1){
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s9_parser__t_s13_monad__except_s6___rarg), 1, 0);
return x_4;
}
}
obj* _l_s4_lean_s6_parser_s9_parser__t_s4_lean_s6_parser_s13_monad__parsec_s6___rarg(obj* x_0){
_start:
{
obj* x_2; obj* x_4; obj* x_6; obj* x_7; obj* x_8; 
lean::inc(x_0);
x_2 = _l_s4_lean_s6_parser_s15_parser__core__t_s5_monad_s6___rarg(x_0);
lean::inc(x_2);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_reader__t_s4_lift), 4, 3);
lean::closure_set(x_4, 0, lean::box(0));
lean::closure_set(x_4, 1, lean::box(0));
lean::closure_set(x_4, 2, x_2);
lean::inc(x_2);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_reader__t_s14_monad__functor), 6, 5);
lean::closure_set(x_6, 0, lean::box(0));
lean::closure_set(x_6, 1, lean::box(0));
lean::closure_set(x_6, 2, lean::box(0));
lean::closure_set(x_6, 3, x_2);
lean::closure_set(x_6, 4, x_2);
x_7 = _l_s4_lean_s6_parser_s15_parser__core__t_s4_lean_s6_parser_s13_monad__parsec_s6___rarg(x_0);
x_8 = _l_s4_lean_s6_parser_s20_monad__parsec__trans_s6___rarg(x_4, x_6, x_7);
return x_8;
}
}
obj* _l_s4_lean_s6_parser_s9_parser__t_s4_lean_s6_parser_s13_monad__parsec(obj* x_0, obj* x_1){
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s9_parser__t_s4_lean_s6_parser_s13_monad__parsec_s6___rarg), 1, 0);
return x_4;
}
}
obj* _l_s4_lean_s6_parser_s9_parser__t_s13_monad__reader_s6___rarg(obj* x_0){
_start:
{
obj* x_1; obj* x_2; 
x_1 = _l_s4_lean_s6_parser_s15_parser__core__t_s5_monad_s6___rarg(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_reader__t_s4_read_s6___rarg), 2, 1);
lean::closure_set(x_2, 0, x_1);
return x_2;
}
}
obj* _l_s4_lean_s6_parser_s9_parser__t_s13_monad__reader(obj* x_0, obj* x_1){
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s9_parser__t_s13_monad__reader_s6___rarg), 1, 0);
return x_4;
}
}
obj* _l_s4_lean_s6_parser_s9_parser__t_s11_alternative_s6___rarg(obj* x_0){
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
lean::inc(x_0);
x_2 = _l_s4_lean_s6_parser_s15_parser__core__t_s5_monad_s6___rarg(x_0);
x_3 = _l_s4_lean_s6_parser_s15_parser__core__t_s11_alternative_s6___rarg(x_0);
x_4 = _l_s9_reader__t_s11_alternative_s6___rarg(x_2, x_3);
return x_4;
}
}
obj* _l_s4_lean_s6_parser_s9_parser__t_s11_alternative(obj* x_0, obj* x_1){
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s9_parser__t_s11_alternative_s6___rarg), 1, 0);
return x_4;
}
}
obj* _l_s4_lean_s6_parser_s9_parser__t_s5_monad_s6___rarg(obj* x_0){
_start:
{
obj* x_1; obj* x_2; 
x_1 = _l_s4_lean_s6_parser_s15_parser__core__t_s5_monad_s6___rarg(x_0);
x_2 = _l_s9_reader__t_s5_monad_s6___rarg(x_1);
return x_2;
}
}
obj* _l_s4_lean_s6_parser_s9_parser__t_s5_monad(obj* x_0, obj* x_1){
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s9_parser__t_s5_monad_s6___rarg), 1, 0);
return x_4;
}
}
obj* _init__l_s4_lean_s6_parser_s16_basic__parser__m(){
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init__l_s4_lean_s6_parser_s16_basic__parser__m_s13_monad__except(){
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id_s5_monad_s11___lambda__1), 4, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id_s5_monad_s11___lambda__2), 4, 0);
lean::inc(x_1);
lean::inc(x_0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id), 1, 0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id_s5_monad_s11___lambda__3), 4, 0);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_4);
lean::cnstr_set(x_7, 1, x_5);
lean::cnstr_set(x_7, 2, x_0);
lean::cnstr_set(x_7, 3, x_1);
lean::cnstr_set(x_7, 4, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id_s4_bind), 2, 0);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
x_10 = _l_s4_lean_s6_parser_s9_parser__t_s13_monad__except_s6___rarg(x_9);
return x_10;
}
}
obj* _init__l_s4_lean_s6_parser_s16_basic__parser__m_s4_lean_s6_parser_s13_monad__parsec(){
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id_s5_monad_s11___lambda__1), 4, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id_s5_monad_s11___lambda__2), 4, 0);
lean::inc(x_1);
lean::inc(x_0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id), 1, 0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id_s5_monad_s11___lambda__3), 4, 0);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_4);
lean::cnstr_set(x_7, 1, x_5);
lean::cnstr_set(x_7, 2, x_0);
lean::cnstr_set(x_7, 3, x_1);
lean::cnstr_set(x_7, 4, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id_s4_bind), 2, 0);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
x_10 = _l_s4_lean_s6_parser_s9_parser__t_s4_lean_s6_parser_s13_monad__parsec_s6___rarg(x_9);
return x_10;
}
}
obj* _init__l_s4_lean_s6_parser_s16_basic__parser__m_s13_monad__reader(){
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id_s5_monad_s11___lambda__1), 4, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id_s5_monad_s11___lambda__2), 4, 0);
lean::inc(x_1);
lean::inc(x_0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id), 1, 0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id_s5_monad_s11___lambda__3), 4, 0);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_4);
lean::cnstr_set(x_7, 1, x_5);
lean::cnstr_set(x_7, 2, x_0);
lean::cnstr_set(x_7, 3, x_1);
lean::cnstr_set(x_7, 4, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id_s4_bind), 2, 0);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
x_10 = _l_s4_lean_s6_parser_s9_parser__t_s13_monad__reader_s6___rarg(x_9);
return x_10;
}
}
obj* _init__l_s4_lean_s6_parser_s16_basic__parser__m_s11_alternative(){
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id_s5_monad_s11___lambda__1), 4, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id_s5_monad_s11___lambda__2), 4, 0);
lean::inc(x_1);
lean::inc(x_0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id), 1, 0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id_s5_monad_s11___lambda__3), 4, 0);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_4);
lean::cnstr_set(x_7, 1, x_5);
lean::cnstr_set(x_7, 2, x_0);
lean::cnstr_set(x_7, 3, x_1);
lean::cnstr_set(x_7, 4, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id_s4_bind), 2, 0);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
x_10 = _l_s4_lean_s6_parser_s9_parser__t_s11_alternative_s6___rarg(x_9);
return x_10;
}
}
obj* _init__l_s4_lean_s6_parser_s16_basic__parser__m_s5_monad(){
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id_s5_monad_s11___lambda__1), 4, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id_s5_monad_s11___lambda__2), 4, 0);
lean::inc(x_1);
lean::inc(x_0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id), 1, 0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id_s5_monad_s11___lambda__3), 4, 0);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_4);
lean::cnstr_set(x_7, 1, x_5);
lean::cnstr_set(x_7, 2, x_0);
lean::cnstr_set(x_7, 3, x_1);
lean::cnstr_set(x_7, 4, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id_s4_bind), 2, 0);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
x_10 = _l_s4_lean_s6_parser_s9_parser__t_s5_monad_s6___rarg(x_9);
return x_10;
}
}
obj* _init__l_s4_lean_s6_parser_s13_basic__parser(){
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init__l_s4_lean_s6_parser_s20_monad__basic__parser(){
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _l_s4_lean_s6_parser_s10_get__cache_s6___rarg(obj* x_0, obj* x_1){
_start:
{
obj* x_2; obj* x_5; obj* x_6; 
x_2 = _l_s4_lean_s6_parser_s6_parsec_s6_result_s7_mk__eps_s6___rarg_s11___closed__1;
lean::inc(x_2);
lean::inc(x_1);
x_5 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_5, 0, x_1);
lean::cnstr_set(x_5, 1, x_0);
lean::cnstr_set(x_5, 2, x_2);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_1);
return x_6;
}
}
obj* _l_s4_lean_s6_parser_s10_get__cache(obj* x_0){
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s10_get__cache_s6___rarg), 2, 0);
return x_2;
}
}
obj* _l_s4_lean_s6_parser_s10_put__cache(obj* x_0, obj* x_1, obj* x_2, obj* x_3){
_start:
{
unsigned char x_6; obj* x_7; obj* x_8; obj* x_10; obj* x_11; 
lean::dec(x_3);
lean::dec(x_1);
x_6 = 0;
x_7 = _l_s4_lean_s6_parser_s6_parsec_s6_result_s7_mk__eps_s6___rarg_s11___closed__1;
x_8 = lean::box(x_6);
lean::inc(x_7);
x_10 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_2);
lean::cnstr_set(x_10, 2, x_7);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_0);
return x_11;
}
}
obj* _l_s4_lean_s6_parser_s6_tokens_s6___rarg(obj* x_0){
_start:
{

return x_0;
}
}
obj* _l_s4_lean_s6_parser_s6_tokens(obj* x_0, obj* x_1){
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s6_tokens_s6___rarg), 1, 0);
return x_4;
}
}
obj* _l_s4_lean_s6_parser_s11_has__tokens_s9_inhabited(obj* x_0, obj* x_1){
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_cnstr(0, 0, 0);
;
return x_4;
}
}
obj* _l_s4_lean_s6_parser_s4_list_s3_nil_s6_tokens(obj* x_0){
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_cnstr(0, 0, 0);
;
return x_2;
}
}
obj* _l_s4_lean_s6_parser_s4_list_s4_cons_s6_tokens_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3){
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_4 = _l_s4_lean_s6_parser_s6_tokens(lean::box(0), x_0);
x_5 = lean::apply_1(x_4, x_2);
x_6 = _l_s4_lean_s6_parser_s6_tokens(lean::box(0), x_1);
x_7 = lean::apply_1(x_6, x_3);
x_8 = _l_s4_list_s6_append_s6___main_s6___rarg(x_5, x_7);
return x_8;
}
}
obj* _l_s4_lean_s6_parser_s4_list_s4_cons_s6_tokens(obj* x_0){
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s4_list_s4_cons_s6_tokens_s6___rarg), 4, 0);
return x_2;
}
}
obj* _l_s4_lean_s6_parser_s9_try__view_s6___rarg(obj* x_0, obj* x_1, obj* x_2){
_start:
{
unsigned char x_4; 
lean::inc(x_2);
x_4 = _l_s4_lean_s6_parser_s6_syntax_s12_is__of__kind_s6___main(x_0, x_2);
if (x_4 == 0)
{
obj* x_7; 
lean::dec(x_1);
lean::dec(x_2);
x_7 = lean::alloc_cnstr(0, 0, 0);
;
return x_7;
}
else
{
obj* x_8; obj* x_11; obj* x_12; 
x_8 = lean::cnstr_get(x_1, 0);
lean::inc(x_8);
lean::dec(x_1);
x_11 = lean::apply_1(x_8, x_2);
x_12 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_12, 0, x_11);
return x_12;
}
}
}
obj* _l_s4_lean_s6_parser_s9_try__view(obj* x_0){
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s9_try__view_s6___rarg), 3, 0);
return x_2;
}
}
obj* _l_s4_lean_s6_parser_s9_has__view_s7_default_s6___rarg(obj* x_0){
_start:
{
obj* x_2; obj* x_5; 
lean::dec(x_0);
x_2 = _l_s5_mjoin_s6___rarg_s11___closed__1;
lean::inc(x_2);
lean::inc(x_2);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_2);
lean::cnstr_set(x_5, 1, x_2);
return x_5;
}
}
obj* _l_s4_lean_s6_parser_s9_has__view_s7_default(obj* x_0){
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s9_has__view_s7_default_s6___rarg), 1, 0);
return x_2;
}
}
obj* _l_s4_lean_s6_parser_s28_message__of__parsec__message_s6___rarg(obj* x_0, obj* x_1){
_start:
{
obj* x_2; obj* x_4; obj* x_7; obj* x_9; obj* x_11; obj* x_12; obj* x_13; unsigned char x_14; obj* x_15; obj* x_17; obj* x_18; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_0, 2);
lean::inc(x_4);
lean::dec(x_0);
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
x_9 = lean::string_iterator_offset(x_7);
lean::dec(x_7);
x_11 = _l_s4_lean_s9_file__map_s12_to__position(x_4, x_9);
x_12 = lean::alloc_cnstr(0, 0, 0);
;
x_13 = _l_s4_lean_s6_parser_s6_parsec_s7_message_s4_text_s6___rarg(x_1);
x_14 = 2;
x_15 = _l_s6_string_s4_join_s11___closed__1;
lean::inc(x_15);
x_17 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_17, 0, x_2);
lean::cnstr_set(x_17, 1, x_11);
lean::cnstr_set(x_17, 2, x_12);
lean::cnstr_set(x_17, 3, x_15);
lean::cnstr_set(x_17, 4, x_13);
lean::cnstr_set_scalar(x_17, sizeof(void*)*5, x_14);
x_18 = x_17;
return x_18;
}
}
obj* _l_s4_lean_s6_parser_s28_message__of__parsec__message(obj* x_0){
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s28_message__of__parsec__message_s6___rarg), 2, 0);
return x_2;
}
}
obj* _l_s4_lean_s6_parser_s3_run_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4){
_start:
{
obj* x_5; obj* x_7; obj* x_10; obj* x_11; obj* x_12; obj* x_16; obj* x_17; obj* x_18; 
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
x_7 = _l_s4_lean_s12_message__log_s5_empty;
lean::inc(x_2);
lean::inc(x_7);
x_10 = lean::apply_2(x_4, x_7, x_2);
x_11 = _l_s6_string_s4_join_s11___closed__1;
x_12 = _l_s4_lean_s6_parser_s3_run_s6___rarg_s11___closed__1;
lean::inc(x_12);
lean::inc(x_11);
lean::inc(x_0);
x_16 = _l_s4_lean_s6_parser_s9_parsec__t_s3_run_s4___at_s4_lean_s6_parser_s3_run_s9___spec__1_s6___rarg(x_0, lean::box(0), lean::box(0), x_10, x_3, x_11, x_12);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s3_run_s6___rarg_s11___lambda__1), 4, 3);
lean::closure_set(x_17, 0, x_0);
lean::closure_set(x_17, 1, x_1);
lean::closure_set(x_17, 2, x_2);
x_18 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_16, x_17);
return x_18;
}
}
obj* _init__l_s4_lean_s6_parser_s3_run_s6___rarg_s11___closed__1(){
_start:
{
obj* x_0; obj* x_1; obj* x_3; 
x_0 = lean::alloc_cnstr(0, 0, 0);
;
x_1 = lean::mk_nat_obj(0u);
lean::inc(x_1);
x_3 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_3, 0, x_0);
lean::cnstr_set(x_3, 1, x_1);
lean::cnstr_set(x_3, 2, x_1);
return x_3;
}
}
obj* _l_s4_lean_s6_parser_s3_run_s6___rarg_s11___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3){
_start:
{
obj* x_4; obj* x_6; obj* x_7; obj* x_10; 
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
if (lean::is_shared(x_3)) {
 lean::dec(x_3);
 x_6 = lean::box(0);
} else {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 1);
 x_6 = x_3;
}
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::cnstr_get(x_7, 1);
lean::inc(x_10);
lean::dec(x_7);
if (lean::obj_tag(x_4) == 0)
{
obj* x_13; obj* x_16; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_24; obj* x_25; obj* x_26; 
x_13 = lean::cnstr_get(x_4, 0);
lean::inc(x_13);
lean::dec(x_4);
x_16 = lean::cnstr_get(x_13, 3);
lean::inc(x_16);
x_18 = _l_s6_option_s3_get_s6___main_s4___at_s4_lean_s6_parser_s3_run_s9___spec__2(x_16);
x_19 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_19, 0, x_18);
x_20 = lean::apply_1(x_1, x_2);
x_21 = _l_s4_lean_s6_parser_s28_message__of__parsec__message_s6___rarg(x_20, x_13);
x_22 = _l_s4_lean_s12_message__log_s5_empty;
lean::inc(x_22);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_21);
lean::cnstr_set(x_24, 1, x_22);
if (lean::is_scalar(x_6)) {
 x_25 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_25 = x_6;
}
lean::cnstr_set(x_25, 0, x_19);
lean::cnstr_set(x_25, 1, x_24);
x_26 = lean::apply_2(x_10, lean::box(0), x_25);
return x_26;
}
else
{
obj* x_29; obj* x_32; obj* x_34; obj* x_37; obj* x_38; obj* x_39; 
lean::dec(x_1);
lean::dec(x_2);
x_29 = lean::cnstr_get(x_4, 0);
lean::inc(x_29);
lean::dec(x_4);
x_32 = lean::cnstr_get(x_29, 0);
lean::inc(x_32);
x_34 = lean::cnstr_get(x_29, 1);
lean::inc(x_34);
lean::dec(x_29);
x_37 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_37, 0, x_32);
if (lean::is_scalar(x_6)) {
 x_38 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_38 = x_6;
}
lean::cnstr_set(x_38, 0, x_37);
lean::cnstr_set(x_38, 1, x_34);
x_39 = lean::apply_2(x_10, lean::box(0), x_38);
return x_39;
}
}
}
obj* _l_s4_lean_s6_parser_s3_run(obj* x_0, obj* x_1, obj* x_2){
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s3_run_s6___rarg), 5, 0);
return x_6;
}
}
obj* _l_s4_lean_s6_parser_s9_parsec__t_s3_run_s4___at_s4_lean_s6_parser_s3_run_s9___spec__1_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6){
_start:
{
obj* x_10; obj* x_11; obj* x_13; obj* x_14; obj* x_15; 
lean::dec(x_5);
lean::dec(x_2);
lean::dec(x_1);
x_10 = lean::string_mk_iterator(x_4);
x_11 = lean::cnstr_get(x_0, 1);
lean::inc(x_11);
x_13 = lean::apply_2(x_3, x_10, x_6);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s9_parsec__t_s3_run_s4___at_s4_lean_s6_parser_s3_run_s9___spec__1_s6___rarg_s11___lambda__1), 2, 1);
lean::closure_set(x_14, 0, x_0);
x_15 = lean::apply_4(x_11, lean::box(0), lean::box(0), x_13, x_14);
return x_15;
}
}
obj* _l_s4_lean_s6_parser_s9_parsec__t_s3_run_s4___at_s4_lean_s6_parser_s3_run_s9___spec__1_s6___rarg_s11___lambda__1(obj* x_0, obj* x_1){
_start:
{
obj* x_2; obj* x_4; obj* x_6; 
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
 x_6 = x_1;
}
if (lean::obj_tag(x_2) == 0)
{
obj* x_7; obj* x_10; obj* x_11; obj* x_14; obj* x_17; obj* x_18; 
x_7 = lean::cnstr_get(x_2, 0);
lean::inc(x_7);
lean::dec(x_2);
x_10 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_10, 0, x_7);
x_11 = lean::cnstr_get(x_0, 0);
lean::inc(x_11);
lean::dec(x_0);
x_14 = lean::cnstr_get(x_11, 1);
lean::inc(x_14);
lean::dec(x_11);
if (lean::is_scalar(x_6)) {
 x_17 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_17 = x_6;
}
lean::cnstr_set(x_17, 0, x_10);
lean::cnstr_set(x_17, 1, x_4);
x_18 = lean::apply_2(x_14, lean::box(0), x_17);
return x_18;
}
else
{
obj* x_19; obj* x_22; obj* x_23; obj* x_26; obj* x_29; obj* x_30; 
x_19 = lean::cnstr_get(x_2, 0);
lean::inc(x_19);
lean::dec(x_2);
x_22 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_22, 0, x_19);
x_23 = lean::cnstr_get(x_0, 0);
lean::inc(x_23);
lean::dec(x_0);
x_26 = lean::cnstr_get(x_23, 1);
lean::inc(x_26);
lean::dec(x_23);
if (lean::is_scalar(x_6)) {
 x_29 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_29 = x_6;
}
lean::cnstr_set(x_29, 0, x_22);
lean::cnstr_set(x_29, 1, x_4);
x_30 = lean::apply_2(x_26, lean::box(0), x_29);
return x_30;
}
}
}
obj* _l_s4_lean_s6_parser_s9_parsec__t_s3_run_s4___at_s4_lean_s6_parser_s3_run_s9___spec__1(obj* x_0){
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s9_parsec__t_s3_run_s4___at_s4_lean_s6_parser_s3_run_s9___spec__1_s6___rarg), 7, 0);
return x_2;
}
}
obj* _l_s6_option_s3_get_s6___main_s4___at_s4_lean_s6_parser_s3_run_s9___spec__2(obj* x_0){
_start:
{

if (lean::obj_tag(x_0) == 0)
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_cnstr(3, 0, 0);
;
return x_2;
}
else
{
obj* x_3; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
lean::dec(x_0);
return x_3;
}
}
}
obj* _l_s4_lean_s6_parser_s12_log__message_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4){
_start:
{
obj* x_5; obj* x_8; obj* x_9; 
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
lean::dec(x_0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s12_log__message_s6___rarg_s11___lambda__2), 4, 3);
lean::closure_set(x_8, 0, x_3);
lean::closure_set(x_8, 1, x_2);
lean::closure_set(x_8, 2, x_4);
x_9 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_1, x_8);
return x_9;
}
}
obj* _l_s4_lean_s6_parser_s12_log__message_s6___rarg_s11___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3){
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = lean::apply_1(x_0, x_1);
x_5 = _l_s4_lean_s6_parser_s28_message__of__parsec__message_s6___rarg(x_4, x_2);
x_6 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_3);
return x_6;
}
}
obj* _l_s4_lean_s6_parser_s12_log__message_s6___rarg_s11___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3){
_start:
{
obj* x_4; obj* x_7; obj* x_8; 
x_4 = lean::cnstr_get(x_0, 2);
lean::inc(x_4);
lean::dec(x_0);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s12_log__message_s6___rarg_s11___lambda__1), 4, 3);
lean::closure_set(x_7, 0, x_1);
lean::closure_set(x_7, 1, x_3);
lean::closure_set(x_7, 2, x_2);
x_8 = lean::apply_1(x_4, x_7);
return x_8;
}
}
obj* _l_s4_lean_s6_parser_s12_log__message(obj* x_0, obj* x_1, obj* x_2){
_start:
{
obj* x_6; 
lean::dec(x_2);
lean::dec(x_1);
lean::dec(x_0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s12_log__message_s6___rarg), 5, 0);
return x_6;
}
}
obj* _l_s4_lean_s6_parser_s15_mk__token__trie(obj* x_0){
_start:
{
obj* x_1; obj* x_3; obj* x_4; obj* x_6; 
x_1 = _l_s4_lean_s6_parser_s15_mk__token__trie_s11___closed__1;
lean::inc(x_1);
x_3 = _l_s4_list_s6_append_s6___main_s6___rarg(x_1, x_0);
x_4 = _l_s4_lean_s6_parser_s4_trie_s2_mk_s11___closed__1;
lean::inc(x_4);
x_6 = _l_s4_list_s6_mfoldl_s6___main_s4___at_s4_lean_s6_parser_s15_mk__token__trie_s9___spec__1(x_4, x_3);
if (lean::obj_tag(x_6) == 0)
{
obj* x_7; obj* x_9; obj* x_10; 
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
if (lean::is_shared(x_6)) {
 lean::dec(x_6);
 x_9 = lean::box(0);
} else {
 lean::cnstr_release(x_6, 0);
 x_9 = x_6;
}
if (lean::is_scalar(x_9)) {
 x_10 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_10 = x_9;
}
lean::cnstr_set(x_10, 0, x_7);
return x_10;
}
else
{
obj* x_11; obj* x_13; obj* x_14; 
x_11 = lean::cnstr_get(x_6, 0);
lean::inc(x_11);
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
lean::cnstr_set(x_14, 0, x_11);
return x_14;
}
}
}
obj* _init__l_s4_lean_s6_parser_s15_mk__token__trie_s11___closed__1(){
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_5; obj* x_6; obj* x_8; obj* x_9; obj* x_10; 
x_0 = lean::alloc_cnstr(0, 0, 0);
;
x_1 = lean::mk_string("/-");
x_2 = lean::mk_nat_obj(0u);
lean::inc(x_0);
lean::inc(x_2);
x_5 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_5, 0, x_1);
lean::cnstr_set(x_5, 1, x_2);
lean::cnstr_set(x_5, 2, x_0);
x_6 = lean::mk_string("--");
lean::inc(x_0);
x_8 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set(x_8, 1, x_2);
lean::cnstr_set(x_8, 2, x_0);
x_9 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_0);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_5);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
}
}
obj* _l_s4_list_s6_mfoldl_s6___main_s4___at_s4_lean_s6_parser_s15_mk__token__trie_s9___spec__1(obj* x_0, obj* x_1){
_start:
{

if (lean::obj_tag(x_1) == 0)
{
obj* x_3; 
lean::dec(x_1);
x_3 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_3, 0, x_0);
return x_3;
}
else
{
obj* x_4; obj* x_6; obj* x_9; obj* x_13; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_1, 1);
lean::inc(x_6);
lean::dec(x_1);
x_9 = lean::cnstr_get(x_4, 0);
lean::inc(x_9);
lean::inc(x_9);
lean::inc(x_0);
x_13 = _l_s4_lean_s6_parser_s4_trie_s4_find_s6___rarg(x_0, x_9);
if (lean::obj_tag(x_13) == 0)
{
obj* x_15; obj* x_16; 
lean::dec(x_13);
x_15 = _l_s4_lean_s6_parser_s4_trie_s6_insert_s6___rarg(x_0, x_9, x_4);
x_16 = _l_s4_list_s6_mfoldl_s6___main_s4___at_s4_lean_s6_parser_s15_mk__token__trie_s9___spec__1(x_15, x_6);
x_0 = x_15;
x_1 = x_6;
goto _start;
}
else
{
obj* x_17; obj* x_20; obj* x_22; obj* x_23; 
x_17 = lean::cnstr_get(x_13, 0);
lean::inc(x_17);
lean::dec(x_13);
x_20 = lean::cnstr_get(x_4, 1);
lean::inc(x_20);
x_22 = lean::mk_nat_obj(0u);
x_23 = lean::nat_dec_eq(x_20, x_22);
if (lean::obj_tag(x_23) == 0)
{
obj* x_25; obj* x_28; 
lean::dec(x_23);
x_25 = lean::cnstr_get(x_17, 1);
lean::inc(x_25);
lean::dec(x_17);
x_28 = lean::nat_dec_eq(x_25, x_22);
lean::dec(x_22);
if (lean::obj_tag(x_28) == 0)
{
obj* x_32; 
lean::dec(x_4);
lean::dec(x_28);
x_32 = lean::nat_dec_eq(x_20, x_25);
if (lean::obj_tag(x_32) == 0)
{
obj* x_36; obj* x_38; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_50; 
lean::dec(x_32);
lean::dec(x_6);
lean::dec(x_0);
x_36 = _l_s4_list_s6_mfoldl_s6___main_s4___at_s4_lean_s6_parser_s15_mk__token__trie_s9___spec__1_s11___closed__1;
lean::inc(x_36);
x_38 = lean::string_append(x_36, x_9);
lean::dec(x_9);
x_40 = _l_s4_list_s6_mfoldl_s6___main_s4___at_s4_lean_s6_parser_s15_mk__token__trie_s9___spec__1_s11___closed__2;
x_41 = lean::string_append(x_38, x_40);
x_42 = _l_s3_nat_s4_repr(x_20);
x_43 = lean::string_append(x_41, x_42);
lean::dec(x_42);
x_45 = _l_s4_list_s6_mfoldl_s6___main_s4___at_s4_lean_s6_parser_s15_mk__token__trie_s9___spec__1_s11___closed__3;
x_46 = lean::string_append(x_43, x_45);
x_47 = _l_s3_nat_s4_repr(x_25);
x_48 = lean::string_append(x_46, x_47);
lean::dec(x_47);
x_50 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_50, 0, x_48);
return x_50;
}
else
{
obj* x_55; 
lean::dec(x_32);
lean::dec(x_20);
lean::dec(x_9);
lean::dec(x_25);
x_55 = _l_s4_list_s6_mfoldl_s6___main_s4___at_s4_lean_s6_parser_s15_mk__token__trie_s9___spec__1(x_0, x_6);
x_1 = x_6;
goto _start;
}
}
else
{
obj* x_59; obj* x_60; 
lean::dec(x_20);
lean::dec(x_25);
lean::dec(x_28);
x_59 = _l_s4_lean_s6_parser_s4_trie_s6_insert_s6___rarg(x_0, x_9, x_4);
x_60 = _l_s4_list_s6_mfoldl_s6___main_s4___at_s4_lean_s6_parser_s15_mk__token__trie_s9___spec__1(x_59, x_6);
x_0 = x_59;
x_1 = x_6;
goto _start;
}
}
else
{
obj* x_63; obj* x_66; 
lean::dec(x_20);
lean::dec(x_23);
x_63 = lean::cnstr_get(x_17, 1);
lean::inc(x_63);
lean::dec(x_17);
x_66 = lean::nat_dec_eq(x_63, x_22);
lean::dec(x_22);
lean::dec(x_63);
if (lean::obj_tag(x_66) == 0)
{
obj* x_72; 
lean::dec(x_66);
lean::dec(x_9);
lean::dec(x_4);
x_72 = _l_s4_list_s6_mfoldl_s6___main_s4___at_s4_lean_s6_parser_s15_mk__token__trie_s9___spec__1(x_0, x_6);
x_1 = x_6;
goto _start;
}
else
{
obj* x_74; obj* x_75; 
lean::dec(x_66);
x_74 = _l_s4_lean_s6_parser_s4_trie_s6_insert_s6___rarg(x_0, x_9, x_4);
x_75 = _l_s4_list_s6_mfoldl_s6___main_s4___at_s4_lean_s6_parser_s15_mk__token__trie_s9___spec__1(x_74, x_6);
x_0 = x_74;
x_1 = x_6;
goto _start;
}
}
}
}
}
}
obj* _init__l_s4_list_s6_mfoldl_s6___main_s4___at_s4_lean_s6_parser_s15_mk__token__trie_s9___spec__1_s11___closed__1(){
_start:
{
obj* x_0; 
x_0 = lean::mk_string("invalid token '");
return x_0;
}
}
obj* _init__l_s4_list_s6_mfoldl_s6___main_s4___at_s4_lean_s6_parser_s15_mk__token__trie_s9___spec__1_s11___closed__2(){
_start:
{
obj* x_0; 
x_0 = lean::mk_string("', has been defined with precedences ");
return x_0;
}
}
obj* _init__l_s4_list_s6_mfoldl_s6___main_s4___at_s4_lean_s6_parser_s15_mk__token__trie_s9___spec__1_s11___closed__3(){
_start:
{
obj* x_0; 
x_0 = lean::mk_string(" and ");
return x_0;
}
}
obj* _init__l_s4_lean_s6_parser_s18_command__parser__m(){
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _l_s4_lean_s6_parser_s18_command__parser__m_s4_lean_s6_parser_s10_monad__rec(obj* x_0){
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = _l_s4_lean_s6_parser_s18_command__parser__m_s4_lean_s6_parser_s10_monad__rec_s11___closed__1;
lean::inc(x_2);
return x_2;
}
}
obj* _init__l_s4_lean_s6_parser_s18_command__parser__m_s4_lean_s6_parser_s10_monad__rec_s11___closed__1(){
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_12; obj* x_14; obj* x_15; obj* x_16; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id_s5_monad_s11___lambda__1), 4, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id_s5_monad_s11___lambda__2), 4, 0);
lean::inc(x_1);
lean::inc(x_0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id), 1, 0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id_s5_monad_s11___lambda__3), 4, 0);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_4);
lean::cnstr_set(x_7, 1, x_5);
lean::cnstr_set(x_7, 2, x_0);
lean::cnstr_set(x_7, 3, x_1);
lean::cnstr_set(x_7, 4, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id_s4_bind), 2, 0);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
x_10 = _l_s4_lean_s6_parser_s15_parser__core__t_s5_monad_s6___rarg(x_9);
lean::inc(x_10);
x_12 = _l_s9_reader__t_s5_monad_s6___rarg(x_10);
lean::inc(x_12);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_reader__t_s4_lift), 4, 3);
lean::closure_set(x_14, 0, lean::box(0));
lean::closure_set(x_14, 1, lean::box(0));
lean::closure_set(x_14, 2, x_12);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s6_rec__t_s7_recurse_s6___rarg), 3, 1);
lean::closure_set(x_15, 0, x_10);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s10_monad__rec_s5_trans_s6___rarg), 4, 3);
lean::closure_set(x_16, 0, x_14);
lean::closure_set(x_16, 1, x_15);
lean::closure_set(x_16, 2, x_12);
return x_16;
}
}
obj* _l_s4_lean_s6_parser_s18_command__parser__m_s13_monad__except(obj* x_0){
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = _l_s4_lean_s6_parser_s18_command__parser__m_s13_monad__except_s11___closed__1;
lean::inc(x_2);
return x_2;
}
}
obj* _init__l_s4_lean_s6_parser_s18_command__parser__m_s13_monad__except_s11___closed__1(){
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id_s5_monad_s11___lambda__1), 4, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id_s5_monad_s11___lambda__2), 4, 0);
lean::inc(x_1);
lean::inc(x_0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id), 1, 0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id_s5_monad_s11___lambda__3), 4, 0);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_4);
lean::cnstr_set(x_7, 1, x_5);
lean::cnstr_set(x_7, 2, x_0);
lean::cnstr_set(x_7, 3, x_1);
lean::cnstr_set(x_7, 4, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id_s4_bind), 2, 0);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
x_10 = _l_s4_lean_s6_parser_s15_parser__core__t_s13_monad__except_s6___rarg(x_9);
x_11 = _l_s9_reader__t_s13_monad__except_s6___rarg(x_10);
x_12 = _l_s9_reader__t_s13_monad__except_s6___rarg(x_11);
return x_12;
}
}
obj* _l_s4_lean_s6_parser_s18_command__parser__m_s4_lean_s6_parser_s13_monad__parsec(obj* x_0){
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = _l_s4_lean_s6_parser_s18_command__parser__m_s4_lean_s6_parser_s13_monad__parsec_s11___closed__1;
lean::inc(x_2);
return x_2;
}
}
obj* _init__l_s4_lean_s6_parser_s18_command__parser__m_s4_lean_s6_parser_s13_monad__parsec_s11___closed__1(){
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id_s5_monad_s11___lambda__1), 4, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id_s5_monad_s11___lambda__2), 4, 0);
lean::inc(x_1);
lean::inc(x_0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id), 1, 0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id_s5_monad_s11___lambda__3), 4, 0);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_4);
lean::cnstr_set(x_7, 1, x_5);
lean::cnstr_set(x_7, 2, x_0);
lean::cnstr_set(x_7, 3, x_1);
lean::cnstr_set(x_7, 4, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id_s4_bind), 2, 0);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
lean::inc(x_9);
x_11 = _l_s4_lean_s6_parser_s15_parser__core__t_s5_monad_s6___rarg(x_9);
lean::inc(x_11);
x_13 = _l_s9_reader__t_s5_monad_s6___rarg(x_11);
lean::inc(x_13);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_reader__t_s4_lift), 4, 3);
lean::closure_set(x_15, 0, lean::box(0));
lean::closure_set(x_15, 1, lean::box(0));
lean::closure_set(x_15, 2, x_13);
lean::inc(x_13);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_reader__t_s14_monad__functor), 6, 5);
lean::closure_set(x_17, 0, lean::box(0));
lean::closure_set(x_17, 1, lean::box(0));
lean::closure_set(x_17, 2, lean::box(0));
lean::closure_set(x_17, 3, x_13);
lean::closure_set(x_17, 4, x_13);
x_18 = _l_s4_lean_s6_parser_s15_parser__core__t_s4_lean_s6_parser_s13_monad__parsec_s6___rarg(x_9);
x_19 = _l_s4_lean_s6_parser_s6_rec__t_s4_lean_s6_parser_s13_monad__parsec_s6___rarg(x_11, lean::box(0), x_18);
x_20 = _l_s4_lean_s6_parser_s20_monad__parsec__trans_s6___rarg(x_15, x_17, x_19);
return x_20;
}
}
obj* _l_s4_lean_s6_parser_s18_command__parser__m_s13_monad__reader(obj* x_0){
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = _l_s4_lean_s6_parser_s18_command__parser__m_s13_monad__reader_s11___closed__1;
lean::inc(x_2);
return x_2;
}
}
obj* _init__l_s4_lean_s6_parser_s18_command__parser__m_s13_monad__reader_s11___closed__1(){
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id_s5_monad_s11___lambda__1), 4, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id_s5_monad_s11___lambda__2), 4, 0);
lean::inc(x_1);
lean::inc(x_0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id), 1, 0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id_s5_monad_s11___lambda__3), 4, 0);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_4);
lean::cnstr_set(x_7, 1, x_5);
lean::cnstr_set(x_7, 2, x_0);
lean::cnstr_set(x_7, 3, x_1);
lean::cnstr_set(x_7, 4, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id_s4_bind), 2, 0);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
x_10 = _l_s4_lean_s6_parser_s15_parser__core__t_s5_monad_s6___rarg(x_9);
x_11 = _l_s9_reader__t_s5_monad_s6___rarg(x_10);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_reader__t_s4_read_s6___rarg), 2, 1);
lean::closure_set(x_12, 0, x_11);
return x_12;
}
}
obj* _l_s4_lean_s6_parser_s18_command__parser__m_s11_alternative(obj* x_0){
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = _l_s4_lean_s6_parser_s18_command__parser__m_s11_alternative_s11___closed__1;
lean::inc(x_2);
return x_2;
}
}
obj* _init__l_s4_lean_s6_parser_s18_command__parser__m_s11_alternative_s11___closed__1(){
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_11; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id_s5_monad_s11___lambda__1), 4, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id_s5_monad_s11___lambda__2), 4, 0);
lean::inc(x_1);
lean::inc(x_0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id), 1, 0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id_s5_monad_s11___lambda__3), 4, 0);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_4);
lean::cnstr_set(x_7, 1, x_5);
lean::cnstr_set(x_7, 2, x_0);
lean::cnstr_set(x_7, 3, x_1);
lean::cnstr_set(x_7, 4, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id_s4_bind), 2, 0);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
lean::inc(x_9);
x_11 = _l_s4_lean_s6_parser_s15_parser__core__t_s5_monad_s6___rarg(x_9);
lean::inc(x_11);
x_13 = _l_s9_reader__t_s5_monad_s6___rarg(x_11);
x_14 = _l_s4_lean_s6_parser_s15_parser__core__t_s11_alternative_s6___rarg(x_9);
x_15 = _l_s9_reader__t_s11_alternative_s6___rarg(x_11, x_14);
x_16 = _l_s9_reader__t_s11_alternative_s6___rarg(x_13, x_15);
return x_16;
}
}
obj* _l_s4_lean_s6_parser_s18_command__parser__m_s5_monad(obj* x_0){
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = _l_s4_lean_s6_parser_s18_command__parser__m_s5_monad_s11___closed__1;
lean::inc(x_2);
return x_2;
}
}
obj* _init__l_s4_lean_s6_parser_s18_command__parser__m_s5_monad_s11___closed__1(){
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id_s5_monad_s11___lambda__1), 4, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id_s5_monad_s11___lambda__2), 4, 0);
lean::inc(x_1);
lean::inc(x_0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id), 1, 0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id_s5_monad_s11___lambda__3), 4, 0);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_4);
lean::cnstr_set(x_7, 1, x_5);
lean::cnstr_set(x_7, 2, x_0);
lean::cnstr_set(x_7, 3, x_1);
lean::cnstr_set(x_7, 4, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id_s4_bind), 2, 0);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
x_10 = _l_s4_lean_s6_parser_s15_parser__core__t_s5_monad_s6___rarg(x_9);
x_11 = _l_s9_reader__t_s5_monad_s6___rarg(x_10);
x_12 = _l_s9_reader__t_s5_monad_s6___rarg(x_11);
return x_12;
}
}
obj* _l_s4_lean_s6_parser_s18_command__parser__m_s22_monad__reader__adapter(obj* x_0, obj* x_1){
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = _l_s4_lean_s6_parser_s18_command__parser__m_s22_monad__reader__adapter_s11___closed__1;
lean::inc(x_4);
return x_4;
}
}
obj* _init__l_s4_lean_s6_parser_s18_command__parser__m_s22_monad__reader__adapter_s11___closed__1(){
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id_s5_monad_s11___lambda__1), 4, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id_s5_monad_s11___lambda__2), 4, 0);
lean::inc(x_1);
lean::inc(x_0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id), 1, 0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id_s5_monad_s11___lambda__3), 4, 0);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_4);
lean::cnstr_set(x_7, 1, x_5);
lean::cnstr_set(x_7, 2, x_0);
lean::cnstr_set(x_7, 3, x_1);
lean::cnstr_set(x_7, 4, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id_s4_bind), 2, 0);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
x_10 = _l_s4_lean_s6_parser_s15_parser__core__t_s5_monad_s6___rarg(x_9);
x_11 = _l_s9_reader__t_s5_monad_s6___rarg(x_10);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_reader__t_s22_monad__reader__adapter), 5, 4);
lean::closure_set(x_12, 0, lean::box(0));
lean::closure_set(x_12, 1, lean::box(0));
lean::closure_set(x_12, 2, lean::box(0));
lean::closure_set(x_12, 3, x_11);
return x_12;
}
}
obj* _l_s4_lean_s6_parser_s18_command__parser__m_s13_basic__parser_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6){
_start:
{
obj* x_9; obj* x_10; 
lean::dec(x_4);
lean::dec(x_1);
x_9 = lean::apply_1(x_0, x_3);
x_10 = lean::apply_3(x_2, x_9, x_5, x_6);
return x_10;
}
}
obj* _l_s4_lean_s6_parser_s18_command__parser__m_s13_basic__parser(obj* x_0){
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s18_command__parser__m_s13_basic__parser_s6___rarg), 7, 0);
return x_2;
}
}
obj* _init__l_s4_lean_s6_parser_s15_term__parser__m(){
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init__l_s4_lean_s6_parser_s15_term__parser__m_s4_lean_s6_parser_s20_monad__basic__parser(){
_start:
{
obj* x_0; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_0 = _l_s4_lean_s6_parser_s18_command__parser__m_s5_monad_s11___closed__1;
lean::inc(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_reader__t_s4_lift), 4, 3);
lean::closure_set(x_2, 0, lean::box(0));
lean::closure_set(x_2, 1, lean::box(0));
lean::closure_set(x_2, 2, x_0);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(_l_s2_id_s6___rarg), 1, 0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s18_command__parser__m_s13_basic__parser_s6___rarg), 7, 1);
lean::closure_set(x_4, 0, x_3);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(_l_s26_has__monad__lift__t__trans_s6___rarg), 4, 2);
lean::closure_set(x_5, 0, x_2);
lean::closure_set(x_5, 1, x_4);
return x_5;
}
}
obj* _init__l_s4_lean_s6_parser_s15_term__parser__m_s4_lean_s6_parser_s10_monad__rec(){
_start:
{
obj* x_0; obj* x_2; 
x_0 = _l_s4_lean_s6_parser_s18_command__parser__m_s5_monad_s11___closed__1;
lean::inc(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s6_rec__t_s7_recurse_s6___rarg), 3, 1);
lean::closure_set(x_2, 0, x_0);
return x_2;
}
}
obj* _init__l_s4_lean_s6_parser_s15_term__parser__m_s13_monad__except(){
_start:
{
obj* x_0; obj* x_2; 
x_0 = _l_s4_lean_s6_parser_s18_command__parser__m_s13_monad__except_s11___closed__1;
lean::inc(x_0);
x_2 = _l_s9_reader__t_s13_monad__except_s6___rarg(x_0);
return x_2;
}
}
obj* _init__l_s4_lean_s6_parser_s15_term__parser__m_s4_lean_s6_parser_s13_monad__parsec(){
_start:
{
obj* x_0; obj* x_1; obj* x_4; 
x_0 = _l_s4_lean_s6_parser_s18_command__parser__m_s5_monad_s11___closed__1;
x_1 = _l_s4_lean_s6_parser_s18_command__parser__m_s4_lean_s6_parser_s13_monad__parsec_s11___closed__1;
lean::inc(x_1);
lean::inc(x_0);
x_4 = _l_s4_lean_s6_parser_s6_rec__t_s4_lean_s6_parser_s13_monad__parsec_s6___rarg(x_0, lean::box(0), x_1);
return x_4;
}
}
obj* _init__l_s4_lean_s6_parser_s15_term__parser__m_s13_monad__reader(){
_start:
{
obj* x_0; obj* x_2; 
x_0 = _l_s4_lean_s6_parser_s18_command__parser__m_s13_monad__reader_s11___closed__1;
lean::inc(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_reader__t_s4_lift_s6___rarg), 2, 1);
lean::closure_set(x_2, 0, x_0);
return x_2;
}
}
obj* _init__l_s4_lean_s6_parser_s15_term__parser__m_s11_alternative(){
_start:
{
obj* x_0; obj* x_1; obj* x_4; 
x_0 = _l_s4_lean_s6_parser_s18_command__parser__m_s5_monad_s11___closed__1;
x_1 = _l_s4_lean_s6_parser_s18_command__parser__m_s11_alternative_s11___closed__1;
lean::inc(x_1);
lean::inc(x_0);
x_4 = _l_s9_reader__t_s11_alternative_s6___rarg(x_0, x_1);
return x_4;
}
}
obj* _init__l_s4_lean_s6_parser_s15_term__parser__m_s5_monad(){
_start:
{
obj* x_0; obj* x_2; 
x_0 = _l_s4_lean_s6_parser_s18_command__parser__m_s5_monad_s11___closed__1;
lean::inc(x_0);
x_2 = _l_s9_reader__t_s5_monad_s6___rarg(x_0);
return x_2;
}
}
obj* _init__l_s4_lean_s6_parser_s12_term__parser(){
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init__l_s4_lean_s6_parser_s25_trailing__term__parser__m(){
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _init__l_s4_lean_s6_parser_s25_trailing__term__parser__m_s4_lean_s6_parser_s20_monad__basic__parser(){
_start:
{
obj* x_0; obj* x_2; obj* x_3; obj* x_5; 
x_0 = _l_s4_lean_s6_parser_s15_term__parser__m_s5_monad;
lean::inc(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_reader__t_s4_lift), 4, 3);
lean::closure_set(x_2, 0, lean::box(0));
lean::closure_set(x_2, 1, lean::box(0));
lean::closure_set(x_2, 2, x_0);
x_3 = _l_s4_lean_s6_parser_s15_term__parser__m_s4_lean_s6_parser_s20_monad__basic__parser;
lean::inc(x_3);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(_l_s26_has__monad__lift__t__trans_s6___rarg), 4, 2);
lean::closure_set(x_5, 0, x_2);
lean::closure_set(x_5, 1, x_3);
return x_5;
}
}
obj* _init__l_s4_lean_s6_parser_s25_trailing__term__parser__m_s4_lean_s6_parser_s10_monad__rec(){
_start:
{
obj* x_0; obj* x_2; obj* x_3; obj* x_6; 
x_0 = _l_s4_lean_s6_parser_s15_term__parser__m_s5_monad;
lean::inc(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_reader__t_s4_lift), 4, 3);
lean::closure_set(x_2, 0, lean::box(0));
lean::closure_set(x_2, 1, lean::box(0));
lean::closure_set(x_2, 2, x_0);
x_3 = _l_s4_lean_s6_parser_s15_term__parser__m_s4_lean_s6_parser_s10_monad__rec;
lean::inc(x_0);
lean::inc(x_3);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s10_monad__rec_s5_trans_s6___rarg), 4, 3);
lean::closure_set(x_6, 0, x_2);
lean::closure_set(x_6, 1, x_3);
lean::closure_set(x_6, 2, x_0);
return x_6;
}
}
obj* _init__l_s4_lean_s6_parser_s25_trailing__term__parser__m_s13_monad__except(){
_start:
{
obj* x_0; obj* x_2; 
x_0 = _l_s4_lean_s6_parser_s15_term__parser__m_s13_monad__except;
lean::inc(x_0);
x_2 = _l_s9_reader__t_s13_monad__except_s6___rarg(x_0);
return x_2;
}
}
obj* _init__l_s4_lean_s6_parser_s25_trailing__term__parser__m_s4_lean_s6_parser_s13_monad__parsec(){
_start:
{
obj* x_0; obj* x_2; obj* x_5; obj* x_6; obj* x_8; 
x_0 = _l_s4_lean_s6_parser_s15_term__parser__m_s5_monad;
lean::inc(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_reader__t_s4_lift), 4, 3);
lean::closure_set(x_2, 0, lean::box(0));
lean::closure_set(x_2, 1, lean::box(0));
lean::closure_set(x_2, 2, x_0);
lean::inc(x_0);
lean::inc(x_0);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_reader__t_s14_monad__functor), 6, 5);
lean::closure_set(x_5, 0, lean::box(0));
lean::closure_set(x_5, 1, lean::box(0));
lean::closure_set(x_5, 2, lean::box(0));
lean::closure_set(x_5, 3, x_0);
lean::closure_set(x_5, 4, x_0);
x_6 = _l_s4_lean_s6_parser_s15_term__parser__m_s4_lean_s6_parser_s13_monad__parsec;
lean::inc(x_6);
x_8 = _l_s4_lean_s6_parser_s20_monad__parsec__trans_s6___rarg(x_2, x_5, x_6);
return x_8;
}
}
obj* _init__l_s4_lean_s6_parser_s25_trailing__term__parser__m_s13_monad__reader(){
_start:
{
obj* x_0; obj* x_2; 
x_0 = _l_s4_lean_s6_parser_s15_term__parser__m_s5_monad;
lean::inc(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s9_reader__t_s4_read_s6___rarg), 2, 1);
lean::closure_set(x_2, 0, x_0);
return x_2;
}
}
obj* _init__l_s4_lean_s6_parser_s25_trailing__term__parser__m_s11_alternative(){
_start:
{
obj* x_0; obj* x_1; obj* x_4; 
x_0 = _l_s4_lean_s6_parser_s15_term__parser__m_s5_monad;
x_1 = _l_s4_lean_s6_parser_s15_term__parser__m_s11_alternative;
lean::inc(x_1);
lean::inc(x_0);
x_4 = _l_s9_reader__t_s11_alternative_s6___rarg(x_0, x_1);
return x_4;
}
}
obj* _init__l_s4_lean_s6_parser_s25_trailing__term__parser__m_s5_monad(){
_start:
{
obj* x_0; obj* x_2; 
x_0 = _l_s4_lean_s6_parser_s15_term__parser__m_s5_monad;
lean::inc(x_0);
x_2 = _l_s9_reader__t_s5_monad_s6___rarg(x_0);
return x_2;
}
}
obj* _init__l_s4_lean_s6_parser_s22_trailing__term__parser(){
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _l_s4_lean_s6_parser_s27_trailing__term__parser__coe(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6){
_start:
{
obj* x_8; 
lean::dec(x_1);
x_8 = lean::apply_5(x_0, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
obj* _init__l_s4_lean_s6_parser_s10_token__map(){
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
obj* _l_s4_lean_s6_parser_s10_token__map_s6_insert_s6___rarg(obj* x_0, obj* x_1, obj* x_2){
_start:
{
obj* x_5; 
lean::inc(x_1);
lean::inc(x_0);
x_5 = _l_s6_rbnode_s4_find_s6___main_s4___at_s4_lean_s6_parser_s10_token__map_s6_insert_s9___spec__2_s6___rarg(x_0, x_1);
if (lean::obj_tag(x_5) == 0)
{
obj* x_7; obj* x_8; obj* x_9; 
lean::dec(x_5);
x_7 = lean::alloc_cnstr(0, 0, 0);
;
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_2);
lean::cnstr_set(x_8, 1, x_7);
x_9 = _l_s6_rbnode_s6_insert_s4___at_s4_lean_s6_parser_s10_token__map_s6_insert_s9___spec__4_s6___rarg(x_0, x_1, x_8);
return x_9;
}
else
{
obj* x_10; obj* x_13; obj* x_14; 
x_10 = lean::cnstr_get(x_5, 0);
lean::inc(x_10);
lean::dec(x_5);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_2);
lean::cnstr_set(x_13, 1, x_10);
x_14 = _l_s6_rbnode_s6_insert_s4___at_s4_lean_s6_parser_s10_token__map_s6_insert_s9___spec__7_s6___rarg(x_0, x_1, x_13);
return x_14;
}
}
}
obj* _l_s4_lean_s6_parser_s10_token__map_s6_insert(obj* x_0){
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s10_token__map_s6_insert_s6___rarg), 3, 0);
return x_2;
}
}
obj* _l_s6_rbnode_s4_find_s6___main_s4___at_s4_lean_s6_parser_s10_token__map_s6_insert_s9___spec__2_s6___rarg(obj* x_0, obj* x_1){
_start:
{

switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_4; 
lean::dec(x_0);
lean::dec(x_1);
x_4 = lean::alloc_cnstr(0, 0, 0);
;
return x_4;
}
case 1:
{
obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_16; unsigned char x_17; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 2);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_0, 3);
lean::inc(x_11);
lean::dec(x_0);
lean::inc(x_7);
lean::inc(x_1);
x_16 = _l_s4_lean_s4_name_s9_quick__lt_s6___main(x_1, x_7);
x_17 = lean::unbox(x_16);
lean::dec(x_16);
if (x_17 == 0)
{
obj* x_21; unsigned char x_22; 
lean::dec(x_5);
lean::inc(x_1);
x_21 = _l_s4_lean_s4_name_s9_quick__lt_s6___main(x_7, x_1);
x_22 = lean::unbox(x_21);
lean::dec(x_21);
if (x_22 == 0)
{
obj* x_26; 
lean::dec(x_11);
lean::dec(x_1);
x_26 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_26, 0, x_9);
return x_26;
}
else
{
obj* x_28; 
lean::dec(x_9);
x_28 = _l_s6_rbnode_s4_find_s6___main_s4___at_s4_lean_s6_parser_s10_token__map_s6_insert_s9___spec__2_s6___rarg(x_11, x_1);
x_0 = x_11;
goto _start;
}
}
else
{
obj* x_32; 
lean::dec(x_7);
lean::dec(x_9);
lean::dec(x_11);
x_32 = _l_s6_rbnode_s4_find_s6___main_s4___at_s4_lean_s6_parser_s10_token__map_s6_insert_s9___spec__2_s6___rarg(x_5, x_1);
x_0 = x_5;
goto _start;
}
}
default:
{
obj* x_33; obj* x_35; obj* x_37; obj* x_39; obj* x_44; unsigned char x_45; 
x_33 = lean::cnstr_get(x_0, 0);
lean::inc(x_33);
x_35 = lean::cnstr_get(x_0, 1);
lean::inc(x_35);
x_37 = lean::cnstr_get(x_0, 2);
lean::inc(x_37);
x_39 = lean::cnstr_get(x_0, 3);
lean::inc(x_39);
lean::dec(x_0);
lean::inc(x_35);
lean::inc(x_1);
x_44 = _l_s4_lean_s4_name_s9_quick__lt_s6___main(x_1, x_35);
x_45 = lean::unbox(x_44);
lean::dec(x_44);
if (x_45 == 0)
{
obj* x_49; unsigned char x_50; 
lean::dec(x_33);
lean::inc(x_1);
x_49 = _l_s4_lean_s4_name_s9_quick__lt_s6___main(x_35, x_1);
x_50 = lean::unbox(x_49);
lean::dec(x_49);
if (x_50 == 0)
{
obj* x_54; 
lean::dec(x_39);
lean::dec(x_1);
x_54 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_54, 0, x_37);
return x_54;
}
else
{
obj* x_56; 
lean::dec(x_37);
x_56 = _l_s6_rbnode_s4_find_s6___main_s4___at_s4_lean_s6_parser_s10_token__map_s6_insert_s9___spec__2_s6___rarg(x_39, x_1);
x_0 = x_39;
goto _start;
}
}
else
{
obj* x_60; 
lean::dec(x_35);
lean::dec(x_37);
lean::dec(x_39);
x_60 = _l_s6_rbnode_s4_find_s6___main_s4___at_s4_lean_s6_parser_s10_token__map_s6_insert_s9___spec__2_s6___rarg(x_33, x_1);
x_0 = x_33;
goto _start;
}
}
}
}
}
obj* _l_s6_rbnode_s4_find_s6___main_s4___at_s4_lean_s6_parser_s10_token__map_s6_insert_s9___spec__2(obj* x_0){
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s6_rbnode_s4_find_s6___main_s4___at_s4_lean_s6_parser_s10_token__map_s6_insert_s9___spec__2_s6___rarg), 2, 0);
return x_2;
}
}
obj* _l_s5_rbmap_s4_find_s6___main_s4___at_s4_lean_s6_parser_s10_token__map_s6_insert_s9___spec__1_s6___rarg(obj* x_0, obj* x_1){
_start:
{
obj* x_2; 
x_2 = _l_s6_rbnode_s4_find_s6___main_s4___at_s4_lean_s6_parser_s10_token__map_s6_insert_s9___spec__2_s6___rarg(x_0, x_1);
return x_2;
}
}
obj* _l_s5_rbmap_s4_find_s6___main_s4___at_s4_lean_s6_parser_s10_token__map_s6_insert_s9___spec__1(obj* x_0){
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s5_rbmap_s4_find_s6___main_s4___at_s4_lean_s6_parser_s10_token__map_s6_insert_s9___spec__1_s6___rarg), 2, 0);
return x_2;
}
}
obj* _l_s6_rbnode_s3_ins_s6___main_s4___at_s4_lean_s6_parser_s10_token__map_s6_insert_s9___spec__5_s6___rarg(obj* x_0, obj* x_1, obj* x_2){
_start:
{

switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_4; 
lean::inc(x_0);
x_4 = lean::alloc_cnstr(1, 4, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
lean::cnstr_set(x_4, 2, x_2);
lean::cnstr_set(x_4, 3, x_0);
return x_4;
}
case 1:
{
obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_16; unsigned char x_17; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 2);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_0, 3);
lean::inc(x_11);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_13 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 lean::cnstr_release(x_0, 2);
 lean::cnstr_release(x_0, 3);
 x_13 = x_0;
}
lean::inc(x_7);
lean::inc(x_1);
x_16 = _l_s4_lean_s4_name_s9_quick__lt_s6___main(x_1, x_7);
x_17 = lean::unbox(x_16);
lean::dec(x_16);
if (x_17 == 0)
{
obj* x_21; unsigned char x_22; 
lean::inc(x_1);
lean::inc(x_7);
x_21 = _l_s4_lean_s4_name_s9_quick__lt_s6___main(x_7, x_1);
x_22 = lean::unbox(x_21);
lean::dec(x_21);
if (x_22 == 0)
{
obj* x_26; 
lean::dec(x_7);
lean::dec(x_9);
if (lean::is_scalar(x_13)) {
 x_26 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_26 = x_13;
}
lean::cnstr_set(x_26, 0, x_5);
lean::cnstr_set(x_26, 1, x_1);
lean::cnstr_set(x_26, 2, x_2);
lean::cnstr_set(x_26, 3, x_11);
return x_26;
}
else
{
obj* x_27; obj* x_28; 
x_27 = _l_s6_rbnode_s3_ins_s6___main_s4___at_s4_lean_s6_parser_s10_token__map_s6_insert_s9___spec__5_s6___rarg(x_11, x_1, x_2);
if (lean::is_scalar(x_13)) {
 x_28 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_28 = x_13;
}
lean::cnstr_set(x_28, 0, x_5);
lean::cnstr_set(x_28, 1, x_7);
lean::cnstr_set(x_28, 2, x_9);
lean::cnstr_set(x_28, 3, x_27);
return x_28;
}
}
else
{
obj* x_29; obj* x_30; 
x_29 = _l_s6_rbnode_s3_ins_s6___main_s4___at_s4_lean_s6_parser_s10_token__map_s6_insert_s9___spec__5_s6___rarg(x_5, x_1, x_2);
if (lean::is_scalar(x_13)) {
 x_30 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_30 = x_13;
}
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_7);
lean::cnstr_set(x_30, 2, x_9);
lean::cnstr_set(x_30, 3, x_11);
return x_30;
}
}
default:
{
obj* x_31; obj* x_33; obj* x_35; obj* x_37; obj* x_39; obj* x_42; unsigned char x_43; 
x_31 = lean::cnstr_get(x_0, 0);
lean::inc(x_31);
x_33 = lean::cnstr_get(x_0, 1);
lean::inc(x_33);
x_35 = lean::cnstr_get(x_0, 2);
lean::inc(x_35);
x_37 = lean::cnstr_get(x_0, 3);
lean::inc(x_37);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_39 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 lean::cnstr_release(x_0, 2);
 lean::cnstr_release(x_0, 3);
 x_39 = x_0;
}
lean::inc(x_33);
lean::inc(x_1);
x_42 = _l_s4_lean_s4_name_s9_quick__lt_s6___main(x_1, x_33);
x_43 = lean::unbox(x_42);
lean::dec(x_42);
if (x_43 == 0)
{
obj* x_47; unsigned char x_48; 
lean::inc(x_1);
lean::inc(x_33);
x_47 = _l_s4_lean_s4_name_s9_quick__lt_s6___main(x_33, x_1);
x_48 = lean::unbox(x_47);
lean::dec(x_47);
if (x_48 == 0)
{
obj* x_52; 
lean::dec(x_35);
lean::dec(x_33);
if (lean::is_scalar(x_39)) {
 x_52 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_52 = x_39;
}
lean::cnstr_set(x_52, 0, x_31);
lean::cnstr_set(x_52, 1, x_1);
lean::cnstr_set(x_52, 2, x_2);
lean::cnstr_set(x_52, 3, x_37);
return x_52;
}
else
{
unsigned char x_54; 
lean::inc(x_37);
x_54 = _l_s6_rbnode_s10_get__color_s6___main_s6___rarg(x_37);
if (x_54 == 0)
{
obj* x_56; obj* x_57; 
lean::dec(x_39);
x_56 = _l_s6_rbnode_s3_ins_s6___main_s4___at_s4_lean_s6_parser_s10_token__map_s6_insert_s9___spec__5_s6___rarg(x_37, x_1, x_2);
x_57 = _l_s6_rbnode_s14_balance2__node_s6___main_s6___rarg(x_56, x_33, x_35, x_31);
return x_57;
}
else
{
obj* x_58; obj* x_59; 
x_58 = _l_s6_rbnode_s3_ins_s6___main_s4___at_s4_lean_s6_parser_s10_token__map_s6_insert_s9___spec__5_s6___rarg(x_37, x_1, x_2);
if (lean::is_scalar(x_39)) {
 x_59 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_59 = x_39;
}
lean::cnstr_set(x_59, 0, x_31);
lean::cnstr_set(x_59, 1, x_33);
lean::cnstr_set(x_59, 2, x_35);
lean::cnstr_set(x_59, 3, x_58);
return x_59;
}
}
}
else
{
unsigned char x_61; 
lean::inc(x_31);
x_61 = _l_s6_rbnode_s10_get__color_s6___main_s6___rarg(x_31);
if (x_61 == 0)
{
obj* x_63; obj* x_64; 
lean::dec(x_39);
x_63 = _l_s6_rbnode_s3_ins_s6___main_s4___at_s4_lean_s6_parser_s10_token__map_s6_insert_s9___spec__5_s6___rarg(x_31, x_1, x_2);
x_64 = _l_s6_rbnode_s14_balance1__node_s6___main_s6___rarg(x_63, x_33, x_35, x_37);
return x_64;
}
else
{
obj* x_65; obj* x_66; 
x_65 = _l_s6_rbnode_s3_ins_s6___main_s4___at_s4_lean_s6_parser_s10_token__map_s6_insert_s9___spec__5_s6___rarg(x_31, x_1, x_2);
if (lean::is_scalar(x_39)) {
 x_66 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_66 = x_39;
}
lean::cnstr_set(x_66, 0, x_65);
lean::cnstr_set(x_66, 1, x_33);
lean::cnstr_set(x_66, 2, x_35);
lean::cnstr_set(x_66, 3, x_37);
return x_66;
}
}
}
}
}
}
obj* _l_s6_rbnode_s3_ins_s6___main_s4___at_s4_lean_s6_parser_s10_token__map_s6_insert_s9___spec__5(obj* x_0){
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s6_rbnode_s3_ins_s6___main_s4___at_s4_lean_s6_parser_s10_token__map_s6_insert_s9___spec__5_s6___rarg), 3, 0);
return x_2;
}
}
obj* _l_s6_rbnode_s6_insert_s4___at_s4_lean_s6_parser_s10_token__map_s6_insert_s9___spec__4_s6___rarg(obj* x_0, obj* x_1, obj* x_2){
_start:
{
unsigned char x_4; obj* x_5; obj* x_6; 
lean::inc(x_0);
x_4 = _l_s6_rbnode_s10_get__color_s6___main_s6___rarg(x_0);
x_5 = _l_s6_rbnode_s3_ins_s6___main_s4___at_s4_lean_s6_parser_s10_token__map_s6_insert_s9___spec__5_s6___rarg(x_0, x_1, x_2);
x_6 = _l_s6_rbnode_s18_mk__insert__result_s6___main_s6___rarg(x_4, x_5);
return x_6;
}
}
obj* _l_s6_rbnode_s6_insert_s4___at_s4_lean_s6_parser_s10_token__map_s6_insert_s9___spec__4(obj* x_0){
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s6_rbnode_s6_insert_s4___at_s4_lean_s6_parser_s10_token__map_s6_insert_s9___spec__4_s6___rarg), 3, 0);
return x_2;
}
}
obj* _l_s5_rbmap_s6_insert_s6___main_s4___at_s4_lean_s6_parser_s10_token__map_s6_insert_s9___spec__3_s6___rarg(obj* x_0, obj* x_1, obj* x_2){
_start:
{
obj* x_3; 
x_3 = _l_s6_rbnode_s6_insert_s4___at_s4_lean_s6_parser_s10_token__map_s6_insert_s9___spec__4_s6___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* _l_s5_rbmap_s6_insert_s6___main_s4___at_s4_lean_s6_parser_s10_token__map_s6_insert_s9___spec__3(obj* x_0){
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s5_rbmap_s6_insert_s6___main_s4___at_s4_lean_s6_parser_s10_token__map_s6_insert_s9___spec__3_s6___rarg), 3, 0);
return x_2;
}
}
obj* _l_s6_rbnode_s3_ins_s6___main_s4___at_s4_lean_s6_parser_s10_token__map_s6_insert_s9___spec__8_s6___rarg(obj* x_0, obj* x_1, obj* x_2){
_start:
{

switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_4; 
lean::inc(x_0);
x_4 = lean::alloc_cnstr(1, 4, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
lean::cnstr_set(x_4, 2, x_2);
lean::cnstr_set(x_4, 3, x_0);
return x_4;
}
case 1:
{
obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_16; unsigned char x_17; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 2);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_0, 3);
lean::inc(x_11);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_13 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 lean::cnstr_release(x_0, 2);
 lean::cnstr_release(x_0, 3);
 x_13 = x_0;
}
lean::inc(x_7);
lean::inc(x_1);
x_16 = _l_s4_lean_s4_name_s9_quick__lt_s6___main(x_1, x_7);
x_17 = lean::unbox(x_16);
lean::dec(x_16);
if (x_17 == 0)
{
obj* x_21; unsigned char x_22; 
lean::inc(x_1);
lean::inc(x_7);
x_21 = _l_s4_lean_s4_name_s9_quick__lt_s6___main(x_7, x_1);
x_22 = lean::unbox(x_21);
lean::dec(x_21);
if (x_22 == 0)
{
obj* x_26; 
lean::dec(x_7);
lean::dec(x_9);
if (lean::is_scalar(x_13)) {
 x_26 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_26 = x_13;
}
lean::cnstr_set(x_26, 0, x_5);
lean::cnstr_set(x_26, 1, x_1);
lean::cnstr_set(x_26, 2, x_2);
lean::cnstr_set(x_26, 3, x_11);
return x_26;
}
else
{
obj* x_27; obj* x_28; 
x_27 = _l_s6_rbnode_s3_ins_s6___main_s4___at_s4_lean_s6_parser_s10_token__map_s6_insert_s9___spec__8_s6___rarg(x_11, x_1, x_2);
if (lean::is_scalar(x_13)) {
 x_28 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_28 = x_13;
}
lean::cnstr_set(x_28, 0, x_5);
lean::cnstr_set(x_28, 1, x_7);
lean::cnstr_set(x_28, 2, x_9);
lean::cnstr_set(x_28, 3, x_27);
return x_28;
}
}
else
{
obj* x_29; obj* x_30; 
x_29 = _l_s6_rbnode_s3_ins_s6___main_s4___at_s4_lean_s6_parser_s10_token__map_s6_insert_s9___spec__8_s6___rarg(x_5, x_1, x_2);
if (lean::is_scalar(x_13)) {
 x_30 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_30 = x_13;
}
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_7);
lean::cnstr_set(x_30, 2, x_9);
lean::cnstr_set(x_30, 3, x_11);
return x_30;
}
}
default:
{
obj* x_31; obj* x_33; obj* x_35; obj* x_37; obj* x_39; obj* x_42; unsigned char x_43; 
x_31 = lean::cnstr_get(x_0, 0);
lean::inc(x_31);
x_33 = lean::cnstr_get(x_0, 1);
lean::inc(x_33);
x_35 = lean::cnstr_get(x_0, 2);
lean::inc(x_35);
x_37 = lean::cnstr_get(x_0, 3);
lean::inc(x_37);
if (lean::is_shared(x_0)) {
 lean::dec(x_0);
 x_39 = lean::box(0);
} else {
 lean::cnstr_release(x_0, 0);
 lean::cnstr_release(x_0, 1);
 lean::cnstr_release(x_0, 2);
 lean::cnstr_release(x_0, 3);
 x_39 = x_0;
}
lean::inc(x_33);
lean::inc(x_1);
x_42 = _l_s4_lean_s4_name_s9_quick__lt_s6___main(x_1, x_33);
x_43 = lean::unbox(x_42);
lean::dec(x_42);
if (x_43 == 0)
{
obj* x_47; unsigned char x_48; 
lean::inc(x_1);
lean::inc(x_33);
x_47 = _l_s4_lean_s4_name_s9_quick__lt_s6___main(x_33, x_1);
x_48 = lean::unbox(x_47);
lean::dec(x_47);
if (x_48 == 0)
{
obj* x_52; 
lean::dec(x_35);
lean::dec(x_33);
if (lean::is_scalar(x_39)) {
 x_52 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_52 = x_39;
}
lean::cnstr_set(x_52, 0, x_31);
lean::cnstr_set(x_52, 1, x_1);
lean::cnstr_set(x_52, 2, x_2);
lean::cnstr_set(x_52, 3, x_37);
return x_52;
}
else
{
unsigned char x_54; 
lean::inc(x_37);
x_54 = _l_s6_rbnode_s10_get__color_s6___main_s6___rarg(x_37);
if (x_54 == 0)
{
obj* x_56; obj* x_57; 
lean::dec(x_39);
x_56 = _l_s6_rbnode_s3_ins_s6___main_s4___at_s4_lean_s6_parser_s10_token__map_s6_insert_s9___spec__8_s6___rarg(x_37, x_1, x_2);
x_57 = _l_s6_rbnode_s14_balance2__node_s6___main_s6___rarg(x_56, x_33, x_35, x_31);
return x_57;
}
else
{
obj* x_58; obj* x_59; 
x_58 = _l_s6_rbnode_s3_ins_s6___main_s4___at_s4_lean_s6_parser_s10_token__map_s6_insert_s9___spec__8_s6___rarg(x_37, x_1, x_2);
if (lean::is_scalar(x_39)) {
 x_59 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_59 = x_39;
}
lean::cnstr_set(x_59, 0, x_31);
lean::cnstr_set(x_59, 1, x_33);
lean::cnstr_set(x_59, 2, x_35);
lean::cnstr_set(x_59, 3, x_58);
return x_59;
}
}
}
else
{
unsigned char x_61; 
lean::inc(x_31);
x_61 = _l_s6_rbnode_s10_get__color_s6___main_s6___rarg(x_31);
if (x_61 == 0)
{
obj* x_63; obj* x_64; 
lean::dec(x_39);
x_63 = _l_s6_rbnode_s3_ins_s6___main_s4___at_s4_lean_s6_parser_s10_token__map_s6_insert_s9___spec__8_s6___rarg(x_31, x_1, x_2);
x_64 = _l_s6_rbnode_s14_balance1__node_s6___main_s6___rarg(x_63, x_33, x_35, x_37);
return x_64;
}
else
{
obj* x_65; obj* x_66; 
x_65 = _l_s6_rbnode_s3_ins_s6___main_s4___at_s4_lean_s6_parser_s10_token__map_s6_insert_s9___spec__8_s6___rarg(x_31, x_1, x_2);
if (lean::is_scalar(x_39)) {
 x_66 = lean::alloc_cnstr(2, 4, 0);
} else {
 x_66 = x_39;
}
lean::cnstr_set(x_66, 0, x_65);
lean::cnstr_set(x_66, 1, x_33);
lean::cnstr_set(x_66, 2, x_35);
lean::cnstr_set(x_66, 3, x_37);
return x_66;
}
}
}
}
}
}
obj* _l_s6_rbnode_s3_ins_s6___main_s4___at_s4_lean_s6_parser_s10_token__map_s6_insert_s9___spec__8(obj* x_0){
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s6_rbnode_s3_ins_s6___main_s4___at_s4_lean_s6_parser_s10_token__map_s6_insert_s9___spec__8_s6___rarg), 3, 0);
return x_2;
}
}
obj* _l_s6_rbnode_s6_insert_s4___at_s4_lean_s6_parser_s10_token__map_s6_insert_s9___spec__7_s6___rarg(obj* x_0, obj* x_1, obj* x_2){
_start:
{
unsigned char x_4; obj* x_5; obj* x_6; 
lean::inc(x_0);
x_4 = _l_s6_rbnode_s10_get__color_s6___main_s6___rarg(x_0);
x_5 = _l_s6_rbnode_s3_ins_s6___main_s4___at_s4_lean_s6_parser_s10_token__map_s6_insert_s9___spec__8_s6___rarg(x_0, x_1, x_2);
x_6 = _l_s6_rbnode_s18_mk__insert__result_s6___main_s6___rarg(x_4, x_5);
return x_6;
}
}
obj* _l_s6_rbnode_s6_insert_s4___at_s4_lean_s6_parser_s10_token__map_s6_insert_s9___spec__7(obj* x_0){
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s6_rbnode_s6_insert_s4___at_s4_lean_s6_parser_s10_token__map_s6_insert_s9___spec__7_s6___rarg), 3, 0);
return x_2;
}
}
obj* _l_s5_rbmap_s6_insert_s6___main_s4___at_s4_lean_s6_parser_s10_token__map_s6_insert_s9___spec__6_s6___rarg(obj* x_0, obj* x_1, obj* x_2){
_start:
{
obj* x_3; 
x_3 = _l_s6_rbnode_s6_insert_s4___at_s4_lean_s6_parser_s10_token__map_s6_insert_s9___spec__7_s6___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* _l_s5_rbmap_s6_insert_s6___main_s4___at_s4_lean_s6_parser_s10_token__map_s6_insert_s9___spec__6(obj* x_0){
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s5_rbmap_s6_insert_s6___main_s4___at_s4_lean_s6_parser_s10_token__map_s6_insert_s9___spec__6_s6___rarg), 3, 0);
return x_2;
}
}
obj* _l_s4_lean_s6_parser_s10_token__map_s8_of__list_s6___main_s6___rarg(obj* x_0){
_start:
{

if (lean::obj_tag(x_0) == 0)
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_cnstr(0, 0, 0);
;
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_8; obj* x_10; obj* x_13; obj* x_14; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
lean::dec(x_0);
x_8 = lean::cnstr_get(x_3, 0);
lean::inc(x_8);
x_10 = lean::cnstr_get(x_3, 1);
lean::inc(x_10);
lean::dec(x_3);
x_13 = _l_s4_lean_s6_parser_s10_token__map_s8_of__list_s6___main_s6___rarg(x_5);
x_14 = _l_s4_lean_s6_parser_s10_token__map_s6_insert_s6___rarg(x_13, x_8, x_10);
return x_14;
}
}
}
obj* _l_s4_lean_s6_parser_s10_token__map_s8_of__list_s6___main(obj* x_0){
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s10_token__map_s8_of__list_s6___main_s6___rarg), 1, 0);
return x_2;
}
}
obj* _l_s4_lean_s6_parser_s10_token__map_s8_of__list_s6___rarg(obj* x_0){
_start:
{
obj* x_1; 
x_1 = _l_s4_lean_s6_parser_s10_token__map_s8_of__list_s6___main_s6___rarg(x_0);
return x_1;
}
}
obj* _l_s4_lean_s6_parser_s10_token__map_s8_of__list(obj* x_0){
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s10_token__map_s8_of__list_s6___rarg), 1, 0);
return x_2;
}
}
obj* _l_s4_lean_s6_parser_s15_token__map__nil_s6_tokens(obj* x_0){
_start:
{
obj* x_2; 
lean::dec(x_0);
x_2 = lean::alloc_cnstr(0, 0, 0);
;
return x_2;
}
}
obj* _l_s4_lean_s6_parser_s16_token__map__cons_s6_tokens_s6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3){
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_4 = _l_s4_lean_s6_parser_s6_tokens(lean::box(0), x_0);
x_5 = lean::apply_1(x_4, x_2);
x_6 = _l_s4_lean_s6_parser_s10_token__map_s8_of__list_s6___main_s6___rarg(x_1);
x_7 = _l_s4_lean_s6_parser_s6_tokens(lean::box(0), x_6);
x_8 = lean::apply_1(x_7, x_3);
x_9 = _l_s4_list_s6_append_s6___main_s6___rarg(x_5, x_8);
return x_9;
}
}
obj* _l_s4_lean_s6_parser_s16_token__map__cons_s6_tokens(obj* x_0, obj* x_1){
_start:
{
obj* x_4; 
lean::dec(x_1);
lean::dec(x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(_l_s4_lean_s6_parser_s16_token__map__cons_s6_tokens_s6___rarg), 4, 0);
return x_4;
}
}
obj* _l_s4_lean_s6_parser_s44_command__parser__config__coe__parser__config(obj* x_0){
_start:
{
obj* x_1; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
return x_1;
}
}
obj* _init__l_s4_lean_s6_parser_s15_command__parser(){
_start:
{
obj* x_0; 
x_0 = lean::box(0);
lean::inc(x_0);
return x_0;
}
}
void _l_initialize__l_s4_init_s4_lean_s6_parser_s6_parsec();
void _l_initialize__l_s4_init_s4_lean_s6_parser_s6_syntax();
void _l_initialize__l_s4_init_s4_lean_s6_parser_s3_rec();
void _l_initialize__l_s4_init_s4_lean_s6_parser_s4_trie();
void _l_initialize__l_s4_init_s4_lean_s6_parser_s10_identifier();
void _l_initialize__l_s4_init_s4_data_s5_rbmap_s7_default();
void _l_initialize__l_s4_init_s4_lean_s7_message();
void _l_initialize__l_s4_init_s7_control_s9_coroutine();
static bool _G_initialized = false;
void _l_initialize__l_s4_init_s4_lean_s6_parser_s5_basic() {
 if (_G_initialized) return;
 _G_initialized = true;
 _l_initialize__l_s4_init_s4_lean_s6_parser_s6_parsec();
 _l_initialize__l_s4_init_s4_lean_s6_parser_s6_syntax();
 _l_initialize__l_s4_init_s4_lean_s6_parser_s3_rec();
 _l_initialize__l_s4_init_s4_lean_s6_parser_s4_trie();
 _l_initialize__l_s4_init_s4_lean_s6_parser_s10_identifier();
 _l_initialize__l_s4_init_s4_data_s5_rbmap_s7_default();
 _l_initialize__l_s4_init_s4_lean_s7_message();
 _l_initialize__l_s4_init_s7_control_s9_coroutine();
 _l_s4_lean_s6_parser_s9_max__prec = _init__l_s4_lean_s6_parser_s9_max__prec();
 _l_s4_lean_s6_parser_s15_parser__core__t = _init__l_s4_lean_s6_parser_s15_parser__core__t();
 _l_s4_lean_s6_parser_s9_parser__t = _init__l_s4_lean_s6_parser_s9_parser__t();
 _l_s4_lean_s6_parser_s16_basic__parser__m = _init__l_s4_lean_s6_parser_s16_basic__parser__m();
 _l_s4_lean_s6_parser_s16_basic__parser__m_s13_monad__except = _init__l_s4_lean_s6_parser_s16_basic__parser__m_s13_monad__except();
 _l_s4_lean_s6_parser_s16_basic__parser__m_s4_lean_s6_parser_s13_monad__parsec = _init__l_s4_lean_s6_parser_s16_basic__parser__m_s4_lean_s6_parser_s13_monad__parsec();
 _l_s4_lean_s6_parser_s16_basic__parser__m_s13_monad__reader = _init__l_s4_lean_s6_parser_s16_basic__parser__m_s13_monad__reader();
 _l_s4_lean_s6_parser_s16_basic__parser__m_s11_alternative = _init__l_s4_lean_s6_parser_s16_basic__parser__m_s11_alternative();
 _l_s4_lean_s6_parser_s16_basic__parser__m_s5_monad = _init__l_s4_lean_s6_parser_s16_basic__parser__m_s5_monad();
 _l_s4_lean_s6_parser_s13_basic__parser = _init__l_s4_lean_s6_parser_s13_basic__parser();
 _l_s4_lean_s6_parser_s20_monad__basic__parser = _init__l_s4_lean_s6_parser_s20_monad__basic__parser();
 _l_s4_lean_s6_parser_s3_run_s6___rarg_s11___closed__1 = _init__l_s4_lean_s6_parser_s3_run_s6___rarg_s11___closed__1();
 _l_s4_lean_s6_parser_s15_mk__token__trie_s11___closed__1 = _init__l_s4_lean_s6_parser_s15_mk__token__trie_s11___closed__1();
 _l_s4_list_s6_mfoldl_s6___main_s4___at_s4_lean_s6_parser_s15_mk__token__trie_s9___spec__1_s11___closed__1 = _init__l_s4_list_s6_mfoldl_s6___main_s4___at_s4_lean_s6_parser_s15_mk__token__trie_s9___spec__1_s11___closed__1();
 _l_s4_list_s6_mfoldl_s6___main_s4___at_s4_lean_s6_parser_s15_mk__token__trie_s9___spec__1_s11___closed__2 = _init__l_s4_list_s6_mfoldl_s6___main_s4___at_s4_lean_s6_parser_s15_mk__token__trie_s9___spec__1_s11___closed__2();
 _l_s4_list_s6_mfoldl_s6___main_s4___at_s4_lean_s6_parser_s15_mk__token__trie_s9___spec__1_s11___closed__3 = _init__l_s4_list_s6_mfoldl_s6___main_s4___at_s4_lean_s6_parser_s15_mk__token__trie_s9___spec__1_s11___closed__3();
 _l_s4_lean_s6_parser_s18_command__parser__m = _init__l_s4_lean_s6_parser_s18_command__parser__m();
 _l_s4_lean_s6_parser_s18_command__parser__m_s4_lean_s6_parser_s10_monad__rec_s11___closed__1 = _init__l_s4_lean_s6_parser_s18_command__parser__m_s4_lean_s6_parser_s10_monad__rec_s11___closed__1();
 _l_s4_lean_s6_parser_s18_command__parser__m_s13_monad__except_s11___closed__1 = _init__l_s4_lean_s6_parser_s18_command__parser__m_s13_monad__except_s11___closed__1();
 _l_s4_lean_s6_parser_s18_command__parser__m_s4_lean_s6_parser_s13_monad__parsec_s11___closed__1 = _init__l_s4_lean_s6_parser_s18_command__parser__m_s4_lean_s6_parser_s13_monad__parsec_s11___closed__1();
 _l_s4_lean_s6_parser_s18_command__parser__m_s13_monad__reader_s11___closed__1 = _init__l_s4_lean_s6_parser_s18_command__parser__m_s13_monad__reader_s11___closed__1();
 _l_s4_lean_s6_parser_s18_command__parser__m_s11_alternative_s11___closed__1 = _init__l_s4_lean_s6_parser_s18_command__parser__m_s11_alternative_s11___closed__1();
 _l_s4_lean_s6_parser_s18_command__parser__m_s5_monad_s11___closed__1 = _init__l_s4_lean_s6_parser_s18_command__parser__m_s5_monad_s11___closed__1();
 _l_s4_lean_s6_parser_s18_command__parser__m_s22_monad__reader__adapter_s11___closed__1 = _init__l_s4_lean_s6_parser_s18_command__parser__m_s22_monad__reader__adapter_s11___closed__1();
 _l_s4_lean_s6_parser_s15_term__parser__m = _init__l_s4_lean_s6_parser_s15_term__parser__m();
 _l_s4_lean_s6_parser_s15_term__parser__m_s4_lean_s6_parser_s20_monad__basic__parser = _init__l_s4_lean_s6_parser_s15_term__parser__m_s4_lean_s6_parser_s20_monad__basic__parser();
 _l_s4_lean_s6_parser_s15_term__parser__m_s4_lean_s6_parser_s10_monad__rec = _init__l_s4_lean_s6_parser_s15_term__parser__m_s4_lean_s6_parser_s10_monad__rec();
 _l_s4_lean_s6_parser_s15_term__parser__m_s13_monad__except = _init__l_s4_lean_s6_parser_s15_term__parser__m_s13_monad__except();
 _l_s4_lean_s6_parser_s15_term__parser__m_s4_lean_s6_parser_s13_monad__parsec = _init__l_s4_lean_s6_parser_s15_term__parser__m_s4_lean_s6_parser_s13_monad__parsec();
 _l_s4_lean_s6_parser_s15_term__parser__m_s13_monad__reader = _init__l_s4_lean_s6_parser_s15_term__parser__m_s13_monad__reader();
 _l_s4_lean_s6_parser_s15_term__parser__m_s11_alternative = _init__l_s4_lean_s6_parser_s15_term__parser__m_s11_alternative();
 _l_s4_lean_s6_parser_s15_term__parser__m_s5_monad = _init__l_s4_lean_s6_parser_s15_term__parser__m_s5_monad();
 _l_s4_lean_s6_parser_s12_term__parser = _init__l_s4_lean_s6_parser_s12_term__parser();
 _l_s4_lean_s6_parser_s25_trailing__term__parser__m = _init__l_s4_lean_s6_parser_s25_trailing__term__parser__m();
 _l_s4_lean_s6_parser_s25_trailing__term__parser__m_s4_lean_s6_parser_s20_monad__basic__parser = _init__l_s4_lean_s6_parser_s25_trailing__term__parser__m_s4_lean_s6_parser_s20_monad__basic__parser();
 _l_s4_lean_s6_parser_s25_trailing__term__parser__m_s4_lean_s6_parser_s10_monad__rec = _init__l_s4_lean_s6_parser_s25_trailing__term__parser__m_s4_lean_s6_parser_s10_monad__rec();
 _l_s4_lean_s6_parser_s25_trailing__term__parser__m_s13_monad__except = _init__l_s4_lean_s6_parser_s25_trailing__term__parser__m_s13_monad__except();
 _l_s4_lean_s6_parser_s25_trailing__term__parser__m_s4_lean_s6_parser_s13_monad__parsec = _init__l_s4_lean_s6_parser_s25_trailing__term__parser__m_s4_lean_s6_parser_s13_monad__parsec();
 _l_s4_lean_s6_parser_s25_trailing__term__parser__m_s13_monad__reader = _init__l_s4_lean_s6_parser_s25_trailing__term__parser__m_s13_monad__reader();
 _l_s4_lean_s6_parser_s25_trailing__term__parser__m_s11_alternative = _init__l_s4_lean_s6_parser_s25_trailing__term__parser__m_s11_alternative();
 _l_s4_lean_s6_parser_s25_trailing__term__parser__m_s5_monad = _init__l_s4_lean_s6_parser_s25_trailing__term__parser__m_s5_monad();
 _l_s4_lean_s6_parser_s22_trailing__term__parser = _init__l_s4_lean_s6_parser_s22_trailing__term__parser();
 _l_s4_lean_s6_parser_s10_token__map = _init__l_s4_lean_s6_parser_s10_token__map();
 _l_s4_lean_s6_parser_s15_command__parser = _init__l_s4_lean_s6_parser_s15_command__parser();
}
