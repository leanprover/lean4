// Lean compiler output
// Module: init.lean.parser.basic
// Imports: init.lean.parser.parsec init.lean.parser.syntax init.lean.parser.rec init.lean.parser.trie init.lean.parser.identifier init.data.rbmap.default init.lean.message init.control.coroutine
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
obj* l_lean_parser_put__cache(obj*, obj*, obj*, obj*);
obj* l_rbnode_insert___at_lean_parser_token__map_insert___spec__4(obj*);
obj* l_lean_parser_token__map_insert___rarg(obj*, obj*, obj*);
obj* l_rbnode_ins___main___at_lean_parser_token__map_insert___spec__5___rarg___boxed(obj*, obj*, obj*);
obj* l_lean_parser_parser__t_monad___rarg(obj*);
obj* l_lean_parser_run___boxed(obj*, obj*, obj*);
obj* l_lean_parser_has__view_default(obj*);
obj* l_lean_parser_command__parser__config__coe__parser__config___boxed(obj*);
obj* l_lean_parser_parser__core__t_lean_parser_monad__parsec(obj*);
obj* l_rbnode_ins___main___at_lean_parser_token__map_insert___spec__5___rarg(obj*, obj*, obj*);
obj* l_lean_parser_trailing__term__parser;
obj* l_id___boxed(obj*);
obj* l_lean_parser_parser__t_monad__except___boxed(obj*, obj*);
obj* l_lean_parser_monad__basic__parser;
obj* l_lean_parser_parser__core__t;
obj* l_rbnode_insert___at_lean_parser_token__map_insert___spec__4___boxed(obj*);
obj* l_lean_parser_get__cache___rarg(obj*, obj*);
obj* l_lean_parser_parsec__t_monad__except___rarg(obj*, obj*);
obj* l_rbnode_ins___main___at_lean_parser_token__map_insert___spec__6___rarg(obj*, obj*, obj*);
obj* l_lean_parser_parsec__t_alternative___rarg(obj*, obj*);
obj* l_rbmap_insert___main___at_lean_parser_token__map_insert___spec__7(obj*);
obj* l_lean_parser_trailing__term__parser__m_monad__except;
obj* l_lean_parser_command__parser__m_basic__parser___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_command__parser__m_lean_parser_monad__rec___boxed(obj*);
obj* l_lean_parser_mk__token__trie(obj*);
obj* l_lean_parser_term__parser__m_lean_parser_monad__basic__parser;
obj* l_rbnode_find___main___at_lean_parser_token__map_insert___spec__2___boxed(obj*);
extern obj* l_mjoin___rarg___closed__1;
obj* l_lean_parser_token__map__cons_tokens___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_basic__parser__m_monad;
obj* l_list_mfoldl___main___at_lean_parser_mk__token__trie___spec__1(obj*, obj*);
obj* l_list_mfoldl___main___at_lean_parser_mk__token__trie___spec__1___closed__2;
obj* l_rbmap_find___main___at_lean_parser_token__map_insert___spec__1___rarg(obj*, obj*);
obj* l_lean_parser_command__parser__m;
obj* l_lean_parser_list_cons_tokens___rarg(obj*, obj*);
obj* l_lean_parser_has__view_default___rarg___boxed(obj*);
obj* l_lean_parser_token__map_insert___rarg___boxed(obj*, obj*, obj*);
obj* l_reader__t_lift___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_trie_find___rarg(obj*, obj*);
obj* l_lean_parser_parsec__t_monad___rarg(obj*, obj*);
obj* l_lean_parser_command__parser__m_lean_parser_monad__rec(obj*);
obj* l_lean_parser_command__parser__m_monad__except___closed__1;
obj* l_reader__t_alternative___rarg(obj*, obj*);
obj* l_rbnode_insert___at_lean_parser_token__map_insert___spec__8___rarg(obj*, obj*, obj*);
obj* l_lean_parser_token__map_of__list___main___boxed(obj*);
obj* l_lean_parser_run(obj*, obj*, obj*);
obj* l_lean_parser_parser__t_monad(obj*, obj*);
obj* l_lean_parser_command__parser__m_monad__reader__adapter(obj*, obj*);
obj* l_rbnode_insert___at_lean_parser_token__map_insert___spec__8___boxed(obj*);
uint8 l_lean_parser_syntax_is__of__kind___main(obj*, obj*);
obj* l_rbnode_ins___main___at_lean_parser_token__map_insert___spec__5(obj*);
obj* l_id___rarg___boxed(obj*);
obj* l_lean_parser_token__map_of__list___main___rarg___boxed(obj*);
obj* l_rbnode_ins___main___at_lean_parser_token__map_insert___spec__9___rarg(obj*, obj*, obj*);
obj* l_lean_parser_has__tokens_inhabited___boxed(obj*, obj*);
obj* l_lean_parser_command__parser__m_basic__parser___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_command__parser__m_lean_parser_monad__parsec(obj*);
obj* l_lean_parser_parser__t_alternative___boxed(obj*, obj*);
obj* l_lean_parser_command__parser__m_monad___closed__1;
obj* l_rbmap_insert___main___at_lean_parser_token__map_insert___spec__7___rarg(obj*, obj*, obj*);
obj* l_lean_parser_token__map_of__list___rarg(obj*);
obj* l_lean_parser_message__of__parsec__message___rarg(obj*, obj*);
obj* l_lean_parser_token__map;
obj* l_lean_parser_parser__t_monad__reader___rarg(obj*);
obj* l_lean_parser_parsec__t_run___at_lean_parser_run___spec__1___boxed(obj*);
obj* l_lean_parser_log__message___rarg___lambda__2(obj*, obj*, obj*, obj*);
obj* l_rbnode_ins___main___at_lean_parser_token__map_insert___spec__9___rarg___boxed(obj*, obj*, obj*);
obj* l_lean_parser_token__map_of__list___rarg___boxed(obj*);
obj* l_lean_parser_tokens___boxed(obj*, obj*);
obj* l_lean_parser_list_nil_tokens(obj*);
obj* l_lean_parser_try__view___rarg___boxed(obj*, obj*, obj*);
obj* l_lean_parser_command__parser__m_monad(obj*);
obj* l_lean_parser_message__of__parsec__message___rarg___boxed(obj*, obj*);
obj* l_lean_parser_has__view_default___rarg(obj*);
obj* l_lean_parser_basic__parser__m;
obj* l_lean_parser_token__map__nil_tokens___boxed(obj*);
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_lean_parser_command__parser__m_alternative___closed__1;
obj* l_lean_parser_parser__config__coe___boxed(obj*);
obj* l_lean_parser_parser__core__t_monad__except(obj*);
obj* l_lean_parser_token__map__cons_tokens___rarg___boxed(obj*, obj*);
obj* l_lean_parser_command__parser;
obj* l_lean_parser_trie_insert___rarg(obj*, obj*, obj*);
obj* l_lean_parser_parser__t_lean_parser_monad__parsec(obj*, obj*);
obj* l_lean_parser_trailing__term__parser__coe(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_parser__t_alternative___rarg(obj*);
obj* l_lean_parser_list_cons_tokens___boxed(obj*, obj*, obj*);
obj* l_rbnode_ins___main___at_lean_parser_token__map_insert___spec__9___boxed(obj*);
extern obj* l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
obj* l_rbmap_insert___main___at_lean_parser_token__map_insert___spec__7___boxed(obj*);
obj* l_lean_parser_parser__core__t_alternative(obj*);
obj* l_lean_parser_log__message___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*);
obj* l_rbnode_find___main___at_lean_parser_token__map_insert___spec__2___rarg(obj*, obj*);
obj* l_rbnode_insert___at_lean_parser_token__map_insert___spec__8(obj*);
obj* l_lean_parser_token__map_of__list(obj*);
obj* l_lean_parser_command__parser__m_lean_parser_monad__parsec___closed__1;
obj* l_rbnode_ins___main___at_lean_parser_token__map_insert___spec__6___rarg___boxed(obj*, obj*, obj*);
obj* l_lean_parser_parser__core__t_monad___boxed(obj*);
obj* l_lean_parser_get__cache___boxed(obj*);
obj* l_lean_parser_list_cons_tokens(obj*, obj*, obj*);
obj* l_lean_parser_parsec__t_run___at_lean_parser_run___spec__1___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_parsec__t_run___at_lean_parser_run___spec__1___rarg___lambda__1(obj*, obj*);
obj* l_lean_parser_command__parser__m_monad__reader(obj*);
obj* l_rbmap_insert___main___at_lean_parser_token__map_insert___spec__3___rarg(obj*, obj*, obj*);
obj* l_lean_parser_tokens___rarg(obj*);
obj* l_lean_parser_parser__t;
obj* l_lean_parser_token__map__cons_tokens(obj*, obj*, obj*, obj*);
obj* l_lean_parser_parser__t_monad__reader___boxed(obj*, obj*);
obj* l_lean_parser_parser__core__t_monad(obj*);
obj* l_lean_parser_log__message___rarg(obj*, obj*, obj*, obj*, obj*);
extern obj* l_lean_parser_trie_mk___closed__1;
obj* l_lean_parser_lean_parser_monad__parsec___rarg(obj*);
obj* l_rbnode_ins___main___at_lean_parser_token__map_insert___spec__6(obj*);
extern obj* l_lean_message__log_empty;
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l_lean_parser_token__map__cons_tokens___rarg(obj*, obj*);
obj* l_lean_parser_command__parser__m_basic__parser(obj*);
obj* l_lean_parser_term__parser__m_lean_parser_monad__parsec;
obj* l_rbnode_ins___main___at_lean_parser_token__map_insert___spec__5___boxed(obj*);
obj* l_lean_parser_parser__core__t_monad___rarg(obj*);
obj* l_lean_parser_basic__parser__m_monad__reader;
obj* l_lean_parser_term__parser__m_monad;
obj* l_rbnode_find___main___at_lean_parser_token__map_insert___spec__2(obj*);
obj* l_lean_parser_trailing__term__parser__m;
obj* l_lean_parser_tokens___rarg___boxed(obj*);
obj* l_rbmap_find___main___at_lean_parser_token__map_insert___spec__1___rarg___boxed(obj*, obj*);
extern obj* l_string_join___closed__1;
obj* l_lean_parser_list_nil_tokens___boxed(obj*);
obj* l_lean_parser_monad__rec_trans___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_command__parser__m_alternative___boxed(obj*);
obj* l_lean_parser_trailing__term__parser__coe___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_reader__t_read___rarg(obj*, obj*);
obj* l_rbnode_insert___at_lean_parser_token__map_insert___spec__8___rarg___boxed(obj*, obj*, obj*);
obj* l_lean_parser_max__prec;
obj* l_lean_parser_rec__t_lean_parser_monad__parsec___rarg(obj*, obj*, obj*);
obj* l_lean_parser_command__parser__m_monad__reader__adapter___boxed(obj*, obj*);
obj* l_lean_parser_command__parser__m_monad__reader___closed__1;
obj* l_lean_parser_token__map_insert___boxed(obj*);
obj* l_lean_parser_token__map_of__list___main___rarg(obj*);
obj* l_lean_parser_message__of__parsec__message___boxed(obj*);
obj* l_rbnode_balance2___main___rarg(obj*, obj*);
obj* l_lean_parser_get__cache(obj*);
obj* l_rbmap_insert___main___at_lean_parser_token__map_insert___spec__3(obj*);
obj* l_lean_parser_run___rarg___closed__1;
obj* l_lean_parser_command__parser__config__coe__parser__config(obj*);
obj* l_lean_parser_try__view___rarg(obj*, obj*, obj*);
obj* l_reader__t_monad__reader__adapter___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_mk__token__trie___closed__1;
obj* l_rbnode_insert___at_lean_parser_token__map_insert___spec__4___rarg___boxed(obj*, obj*, obj*);
obj* l_lean_parser_has__view_default___boxed(obj*);
obj* l_reader__t_monad__except___rarg(obj*);
obj* l_lean_parser_monad__parsec__trans___rarg(obj*, obj*, obj*);
obj* l_lean_parser_parser__core__t_alternative___boxed(obj*);
obj* l_rbmap_find___main___at_lean_parser_token__map_insert___spec__1(obj*);
obj* l_lean_parser_parsec_message_text___rarg(obj*);
namespace lean {
obj* string_iterator_offset(obj*);
}
obj* l_id_monad___lambda__1___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_list_cons_tokens___rarg___boxed(obj*, obj*);
obj* l_lean_parser_token__map_of__list___main(obj*);
obj* l_rbnode_ins___main___at_lean_parser_token__map_insert___spec__10___rarg(obj*, obj*, obj*);
obj* l_list_mfoldl___main___at_lean_parser_mk__token__trie___spec__1___closed__3;
obj* l_lean_parser_parser__t_lean_parser_monad__parsec___boxed(obj*, obj*);
obj* l_state__t_monad___rarg(obj*);
obj* l_list_mfoldl___main___at_lean_parser_mk__token__trie___spec__1___closed__1;
obj* l_lean_parser_has__tokens_inhabited(obj*, obj*);
obj* l_lean_parser_trailing__term__parser__m_monad__reader;
obj* l_rbnode_ins___main___at_lean_parser_token__map_insert___spec__10___boxed(obj*);
obj* l_lean_parser_parser__core__t_monad__except___boxed(obj*);
obj* l_lean_parser_token__map__nil_tokens(obj*);
obj* l_rbmap_insert___main___at_lean_parser_token__map_insert___spec__3___rarg___boxed(obj*, obj*, obj*);
obj* l_lean_parser_command__parser__m_lean_parser_monad__parsec___boxed(obj*);
obj* l_lean_parser_log__message___rarg___lambda__1(obj*, obj*, obj*, obj*);
obj* l_rbnode_insert___at_lean_parser_token__map_insert___spec__4___rarg(obj*, obj*, obj*);
obj* l_lean_parser_rec__t_recurse___rarg(obj*, obj*, obj*);
obj* l_rbmap_find___main___at_lean_parser_token__map_insert___spec__1___boxed(obj*);
obj* l_option_get___main___at_lean_parser_run___spec__2___boxed(obj*);
obj* l_lean_parser_try__view(obj*);
obj* l_reader__t_monad__functor___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_trailing__term__parser__m_monad;
namespace lean {
obj* string_mk_iterator(obj*);
}
obj* l_lean_parser_basic__parser__m_alternative;
obj* l_reader__t_lift___rarg___boxed(obj*, obj*);
obj* l_lean_parser_parser__core__t_lean_parser_monad__parsec___boxed(obj*);
obj* l_rbnode_balance1___main___rarg(obj*, obj*);
obj* l_lean_parser_parser__t_alternative(obj*, obj*);
obj* l_rbnode_ins___main___at_lean_parser_token__map_insert___spec__10___rarg___boxed(obj*, obj*, obj*);
obj* l_lean_parser_command__parser__m_monad__except(obj*);
obj* l_rbnode_ins___main___at_lean_parser_token__map_insert___spec__9(obj*);
obj* l_lean_parser_trailing__term__parser__m_lean_parser_monad__parsec;
obj* l_lean_parser_message__of__parsec__message(obj*);
obj* l_rbmap_insert___main___at_lean_parser_token__map_insert___spec__7___rarg___boxed(obj*, obj*, obj*);
obj* l_option_get___main___at_lean_parser_run___spec__2(obj*);
obj* l_lean_parser_command__parser__m_basic__parser___boxed(obj*);
obj* l_lean_parser_parser__config__coe(obj*);
obj* l_lean_parser_try__view___boxed(obj*);
obj* l_lean_parser_parser__core__t_lean_parser_monad__parsec___rarg(obj*);
obj* l_lean_parser_log__message___boxed(obj*, obj*, obj*);
obj* l_has__monad__lift__t__trans___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_parsec__t_run___at_lean_parser_run___spec__1___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_parser__t_monad__except___rarg(obj*);
obj* l_rbnode_find___main___at_lean_parser_token__map_insert___spec__2___rarg___boxed(obj*, obj*);
obj* l_reader__t_monad___rarg(obj*);
obj* l_lean_parser_trailing__term__parser__m_alternative;
obj* l_lean_parser_basic__parser;
obj* l_nat_repr(obj*);
obj* l_rbnode_ins___main___at_lean_parser_token__map_insert___spec__6___boxed(obj*);
obj* l_lean_parser_command__parser__m_monad___boxed(obj*);
obj* l_id_bind___boxed(obj*, obj*);
obj* l_lean_parser_parser__t_monad___boxed(obj*, obj*);
obj* l_lean_parser_command__parser__m_lean_parser_monad__rec___closed__1;
obj* l_lean_parser_term__parser__m_lean_parser_monad__rec;
obj* l_lean_parser_parser__core__t_alternative___rarg(obj*);
obj* l_rbnode_ins___main___at_lean_parser_token__map_insert___spec__10(obj*);
obj* l_lean_parser_token__map_insert(obj*);
obj* l_lean_parser_parsec__t_run___at_lean_parser_run___spec__1(obj*);
obj* l_rbmap_insert___main___at_lean_parser_token__map_insert___spec__3___boxed(obj*);
obj* l_lean_parser_trailing__term__parser__m_lean_parser_monad__rec;
obj* l_lean_parser_parser__t_monad__reader(obj*, obj*);
obj* l_lean_file__map_to__position(obj*, obj*);
obj* l_lean_parser_basic__parser__m_lean_parser_monad__parsec;
obj* l_lean_parser_parser__t_lean_parser_monad__parsec___rarg(obj*);
uint8 l_rbnode_is__red___main___rarg(obj*);
obj* l_lean_name_quick__lt___main(obj*, obj*);
obj* l_lean_parser_put__cache___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_basic__parser__m_monad__except;
obj* l_list_append___rarg(obj*, obj*);
obj* l_lean_parser_run___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_lean_parser_term__parser__m;
obj* l_lean_parser_parser__t_monad__except(obj*, obj*);
obj* l_lean_parser_token__map_of__list___boxed(obj*);
obj* l_lean_parser_term__parser__m_monad__except;
obj* l_lean_parser_parser__core__t_monad__except___rarg(obj*);
obj* l_lean_parser_command__parser__m_monad__except___boxed(obj*);
obj* l_lean_parser_tokens(obj*, obj*);
obj* l_lean_parser_term__parser;
obj* l_lean_parser_term__parser__m_monad__reader;
obj* l_lean_parser_log__message(obj*, obj*, obj*);
obj* l_id_monad___lambda__2___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_command__parser__m_alternative(obj*);
obj* l_lean_parser_get__cache___rarg___boxed(obj*, obj*);
obj* l_id_monad___lambda__3___boxed(obj*, obj*, obj*, obj*);
obj* l_lean_parser_run___rarg___lambda__1(obj*, obj*, obj*, obj*);
obj* l_lean_parser_command__parser__m_monad__reader___boxed(obj*);
obj* l_rbnode_set__black___main___rarg(obj*);
obj* l_lean_parser_command__parser__m_monad__reader__adapter___closed__1;
obj* l_lean_parser_trailing__term__parser__m_lean_parser_monad__basic__parser;
obj* l_lean_parser_term__parser__m_alternative;
obj* _init_l_lean_parser_max__prec() {
_start:
{
obj* x_0; 
x_0 = lean::mk_nat_obj(1024u);
return x_0;
}
}
obj* l_lean_parser_parser__config__coe(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
return x_1;
}
}
obj* l_lean_parser_parser__config__coe___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_parser__config__coe(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_parser_parser__core__t_monad___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_state__t_monad___rarg(x_0);
x_2 = l_lean_parser_parsec__t_monad___rarg(x_1, lean::box(0));
return x_2;
}
}
obj* l_lean_parser_parser__core__t_monad(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parser__core__t_monad___rarg), 1, 0);
return x_1;
}
}
obj* l_lean_parser_parser__core__t_monad___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_parser__core__t_monad(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_parser_parser__core__t_alternative___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_state__t_monad___rarg(x_0);
x_2 = l_lean_parser_parsec__t_alternative___rarg(x_1, lean::box(0));
return x_2;
}
}
obj* l_lean_parser_parser__core__t_alternative(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parser__core__t_alternative___rarg), 1, 0);
return x_1;
}
}
obj* l_lean_parser_parser__core__t_alternative___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_parser__core__t_alternative(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_parser_parser__core__t_lean_parser_monad__parsec___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_state__t_monad___rarg(x_0);
x_2 = l_lean_parser_lean_parser_monad__parsec___rarg(x_1);
return x_2;
}
}
obj* l_lean_parser_parser__core__t_lean_parser_monad__parsec(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parser__core__t_lean_parser_monad__parsec___rarg), 1, 0);
return x_1;
}
}
obj* l_lean_parser_parser__core__t_lean_parser_monad__parsec___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_parser__core__t_lean_parser_monad__parsec(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_parser_parser__core__t_monad__except___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_state__t_monad___rarg(x_0);
x_2 = l_lean_parser_parsec__t_monad__except___rarg(x_1, lean::box(0));
return x_2;
}
}
obj* l_lean_parser_parser__core__t_monad__except(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parser__core__t_monad__except___rarg), 1, 0);
return x_1;
}
}
obj* l_lean_parser_parser__core__t_monad__except___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_parser__core__t_monad__except(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_lean_parser_parser__core__t() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* l_lean_parser_parser__t_monad___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_lean_parser_parser__core__t_monad___rarg(x_0);
x_2 = l_reader__t_monad___rarg(x_1);
return x_2;
}
}
obj* l_lean_parser_parser__t_monad(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parser__t_monad___rarg), 1, 0);
return x_2;
}
}
obj* l_lean_parser_parser__t_monad___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_parser_parser__t_monad(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_lean_parser_parser__t_alternative___rarg(obj* x_0) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
lean::inc(x_0);
x_2 = l_lean_parser_parser__core__t_monad___rarg(x_0);
x_3 = l_lean_parser_parser__core__t_alternative___rarg(x_0);
x_4 = l_reader__t_alternative___rarg(x_2, x_3);
return x_4;
}
}
obj* l_lean_parser_parser__t_alternative(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parser__t_alternative___rarg), 1, 0);
return x_2;
}
}
obj* l_lean_parser_parser__t_alternative___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_parser_parser__t_alternative(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_lean_parser_parser__t_monad__reader___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_lean_parser_parser__core__t_monad___rarg(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_read___rarg), 2, 1);
lean::closure_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_lean_parser_parser__t_monad__reader(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parser__t_monad__reader___rarg), 1, 0);
return x_2;
}
}
obj* l_lean_parser_parser__t_monad__reader___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_parser_parser__t_monad__reader(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_lean_parser_parser__t_lean_parser_monad__parsec___rarg(obj* x_0) {
_start:
{
obj* x_2; obj* x_4; obj* x_6; obj* x_7; obj* x_8; 
lean::inc(x_0);
x_2 = l_lean_parser_parser__core__t_monad___rarg(x_0);
lean::inc(x_2);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_lift___boxed), 4, 3);
lean::closure_set(x_4, 0, lean::box(0));
lean::closure_set(x_4, 1, lean::box(0));
lean::closure_set(x_4, 2, x_2);
lean::inc(x_2);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_monad__functor___boxed), 6, 5);
lean::closure_set(x_6, 0, lean::box(0));
lean::closure_set(x_6, 1, lean::box(0));
lean::closure_set(x_6, 2, lean::box(0));
lean::closure_set(x_6, 3, x_2);
lean::closure_set(x_6, 4, x_2);
x_7 = l_lean_parser_parser__core__t_lean_parser_monad__parsec___rarg(x_0);
x_8 = l_lean_parser_monad__parsec__trans___rarg(x_4, x_6, x_7);
return x_8;
}
}
obj* l_lean_parser_parser__t_lean_parser_monad__parsec(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parser__t_lean_parser_monad__parsec___rarg), 1, 0);
return x_2;
}
}
obj* l_lean_parser_parser__t_lean_parser_monad__parsec___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_parser_parser__t_lean_parser_monad__parsec(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_lean_parser_parser__t_monad__except___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_lean_parser_parser__core__t_monad__except___rarg(x_0);
x_2 = l_reader__t_monad__except___rarg(x_1);
return x_2;
}
}
obj* l_lean_parser_parser__t_monad__except(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parser__t_monad__except___rarg), 1, 0);
return x_2;
}
}
obj* l_lean_parser_parser__t_monad__except___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_parser_parser__t_monad__except(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_lean_parser_parser__t() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* _init_l_lean_parser_basic__parser__m_monad() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__1___boxed), 4, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__2___boxed), 4, 0);
lean::inc(x_1);
lean::inc(x_0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_id___boxed), 1, 0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__3___boxed), 4, 0);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_4);
lean::cnstr_set(x_7, 1, x_5);
lean::cnstr_set(x_7, 2, x_0);
lean::cnstr_set(x_7, 3, x_1);
lean::cnstr_set(x_7, 4, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_id_bind___boxed), 2, 0);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
x_10 = l_lean_parser_parser__t_monad___rarg(x_9);
return x_10;
}
}
obj* _init_l_lean_parser_basic__parser__m_alternative() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__1___boxed), 4, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__2___boxed), 4, 0);
lean::inc(x_1);
lean::inc(x_0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_id___boxed), 1, 0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__3___boxed), 4, 0);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_4);
lean::cnstr_set(x_7, 1, x_5);
lean::cnstr_set(x_7, 2, x_0);
lean::cnstr_set(x_7, 3, x_1);
lean::cnstr_set(x_7, 4, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_id_bind___boxed), 2, 0);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
x_10 = l_lean_parser_parser__t_alternative___rarg(x_9);
return x_10;
}
}
obj* _init_l_lean_parser_basic__parser__m_monad__reader() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__1___boxed), 4, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__2___boxed), 4, 0);
lean::inc(x_1);
lean::inc(x_0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_id___boxed), 1, 0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__3___boxed), 4, 0);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_4);
lean::cnstr_set(x_7, 1, x_5);
lean::cnstr_set(x_7, 2, x_0);
lean::cnstr_set(x_7, 3, x_1);
lean::cnstr_set(x_7, 4, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_id_bind___boxed), 2, 0);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
x_10 = l_lean_parser_parser__t_monad__reader___rarg(x_9);
return x_10;
}
}
obj* _init_l_lean_parser_basic__parser__m_lean_parser_monad__parsec() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__1___boxed), 4, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__2___boxed), 4, 0);
lean::inc(x_1);
lean::inc(x_0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_id___boxed), 1, 0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__3___boxed), 4, 0);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_4);
lean::cnstr_set(x_7, 1, x_5);
lean::cnstr_set(x_7, 2, x_0);
lean::cnstr_set(x_7, 3, x_1);
lean::cnstr_set(x_7, 4, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_id_bind___boxed), 2, 0);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
x_10 = l_lean_parser_parser__t_lean_parser_monad__parsec___rarg(x_9);
return x_10;
}
}
obj* _init_l_lean_parser_basic__parser__m_monad__except() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__1___boxed), 4, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__2___boxed), 4, 0);
lean::inc(x_1);
lean::inc(x_0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_id___boxed), 1, 0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__3___boxed), 4, 0);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_4);
lean::cnstr_set(x_7, 1, x_5);
lean::cnstr_set(x_7, 2, x_0);
lean::cnstr_set(x_7, 3, x_1);
lean::cnstr_set(x_7, 4, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_id_bind___boxed), 2, 0);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
x_10 = l_lean_parser_parser__t_monad__except___rarg(x_9);
return x_10;
}
}
obj* _init_l_lean_parser_basic__parser__m() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* _init_l_lean_parser_basic__parser() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* _init_l_lean_parser_monad__basic__parser() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* l_lean_parser_get__cache___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_5; obj* x_7; 
x_2 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_0);
lean::inc(x_1);
x_5 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_5, 0, x_1);
lean::cnstr_set(x_5, 1, x_0);
lean::cnstr_set(x_5, 2, x_2);
lean::inc(x_1);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_1);
return x_7;
}
}
obj* l_lean_parser_get__cache(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_get__cache___rarg___boxed), 2, 0);
return x_1;
}
}
obj* l_lean_parser_get__cache___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_parser_get__cache___rarg(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_lean_parser_get__cache___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_get__cache(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_parser_put__cache(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_7; obj* x_9; 
x_4 = lean::box(0);
x_5 = l_lean_parser_parsec_result_mk__eps___rarg___closed__1;
lean::inc(x_2);
x_7 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_7, 0, x_4);
lean::cnstr_set(x_7, 1, x_2);
lean::cnstr_set(x_7, 2, x_5);
lean::inc(x_0);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_0);
return x_9;
}
}
obj* l_lean_parser_put__cache___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_parser_put__cache(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_lean_parser_tokens___rarg(obj* x_0) {
_start:
{
lean::inc(x_0);
return x_0;
}
}
obj* l_lean_parser_tokens(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_tokens___rarg___boxed), 1, 0);
return x_2;
}
}
obj* l_lean_parser_tokens___rarg___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_tokens___rarg(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_parser_tokens___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_parser_tokens(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_lean_parser_has__tokens_inhabited(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::box(0);
return x_2;
}
}
obj* l_lean_parser_has__tokens_inhabited___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_parser_has__tokens_inhabited(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_lean_parser_list_nil_tokens(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::box(0);
return x_1;
}
}
obj* l_lean_parser_list_nil_tokens___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_list_nil_tokens(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_parser_list_cons_tokens___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = l_lean_parser_tokens___rarg(x_0);
x_3 = l_lean_parser_tokens___rarg(x_1);
x_4 = l_list_append___rarg(x_2, x_3);
return x_4;
}
}
obj* l_lean_parser_list_cons_tokens(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_list_cons_tokens___rarg___boxed), 2, 0);
return x_3;
}
}
obj* l_lean_parser_list_cons_tokens___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_parser_list_cons_tokens___rarg(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_lean_parser_list_cons_tokens___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_parser_list_cons_tokens(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_lean_parser_try__view___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_lean_parser_syntax_is__of__kind___main(x_0, x_2);
if (x_3 == 0)
{
obj* x_6; 
lean::dec(x_1);
lean::dec(x_2);
x_6 = lean::box(0);
return x_6;
}
else
{
obj* x_7; obj* x_10; obj* x_11; 
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
lean::dec(x_1);
x_10 = lean::apply_1(x_7, x_2);
x_11 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_11, 0, x_10);
return x_11;
}
}
}
obj* l_lean_parser_try__view(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_try__view___rarg___boxed), 3, 0);
return x_1;
}
}
obj* l_lean_parser_try__view___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_parser_try__view___rarg(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_lean_parser_try__view___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_try__view(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_parser_has__view_default___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_mjoin___rarg___closed__1;
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_1);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* l_lean_parser_has__view_default(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_has__view_default___rarg___boxed), 1, 0);
return x_1;
}
}
obj* l_lean_parser_has__view_default___rarg___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_has__view_default___rarg(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_parser_has__view_default___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_has__view_default(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_parser_message__of__parsec__message___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_6; obj* x_8; obj* x_10; obj* x_11; uint8 x_12; obj* x_13; obj* x_15; obj* x_16; 
x_2 = lean::cnstr_get(x_0, 0);
x_3 = lean::cnstr_get(x_0, 2);
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
x_6 = lean::string_iterator_offset(x_4);
lean::dec(x_4);
x_8 = l_lean_file__map_to__position(x_3, x_6);
lean::dec(x_6);
x_10 = lean::box(0);
x_11 = l_lean_parser_parsec_message_text___rarg(x_1);
x_12 = 2;
x_13 = l_string_join___closed__1;
lean::inc(x_2);
x_15 = lean::alloc_cnstr(0, 5, 1);
lean::cnstr_set(x_15, 0, x_2);
lean::cnstr_set(x_15, 1, x_8);
lean::cnstr_set(x_15, 2, x_10);
lean::cnstr_set(x_15, 3, x_13);
lean::cnstr_set(x_15, 4, x_11);
lean::cnstr_set_scalar(x_15, sizeof(void*)*5, x_12);
x_16 = x_15;
return x_16;
}
}
obj* l_lean_parser_message__of__parsec__message(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_message__of__parsec__message___rarg___boxed), 2, 0);
return x_1;
}
}
obj* l_lean_parser_message__of__parsec__message___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_parser_message__of__parsec__message___rarg(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_lean_parser_message__of__parsec__message___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_message__of__parsec__message(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_parser_parsec__t_run___at_lean_parser_run___spec__1___rarg___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
if (lean::obj_tag(x_2) == 0)
{
obj* x_4; obj* x_6; obj* x_7; obj* x_10; obj* x_11; obj* x_14; obj* x_17; obj* x_18; 
x_4 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 x_6 = x_1;
} else {
 lean::inc(x_4);
 lean::dec(x_1);
 x_6 = lean::box(0);
}
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
obj* x_19; obj* x_21; obj* x_22; obj* x_25; obj* x_26; obj* x_29; obj* x_32; obj* x_33; 
x_19 = lean::cnstr_get(x_1, 1);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 x_21 = x_1;
} else {
 lean::inc(x_19);
 lean::dec(x_1);
 x_21 = lean::box(0);
}
x_22 = lean::cnstr_get(x_2, 0);
lean::inc(x_22);
lean::dec(x_2);
x_25 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_25, 0, x_22);
x_26 = lean::cnstr_get(x_0, 0);
lean::inc(x_26);
lean::dec(x_0);
x_29 = lean::cnstr_get(x_26, 1);
lean::inc(x_29);
lean::dec(x_26);
if (lean::is_scalar(x_21)) {
 x_32 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_32 = x_21;
}
lean::cnstr_set(x_32, 0, x_25);
lean::cnstr_set(x_32, 1, x_19);
x_33 = lean::apply_2(x_29, lean::box(0), x_32);
return x_33;
}
}
}
obj* l_lean_parser_parsec__t_run___at_lean_parser_run___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_8; obj* x_10; obj* x_11; obj* x_12; 
x_7 = lean::string_mk_iterator(x_4);
x_8 = lean::cnstr_get(x_0, 1);
lean::inc(x_8);
x_10 = lean::apply_2(x_3, x_7, x_6);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parsec__t_run___at_lean_parser_run___spec__1___rarg___lambda__1), 2, 1);
lean::closure_set(x_11, 0, x_0);
x_12 = lean::apply_4(x_8, lean::box(0), lean::box(0), x_10, x_11);
return x_12;
}
}
obj* l_lean_parser_parsec__t_run___at_lean_parser_run___spec__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_parsec__t_run___at_lean_parser_run___spec__1___rarg___boxed), 7, 0);
return x_1;
}
}
obj* l_option_get___main___at_lean_parser_run___spec__2(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_1; 
x_1 = lean::box(3);
return x_1;
}
else
{
obj* x_2; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
return x_2;
}
}
}
obj* l_lean_parser_run___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_6; 
x_4 = lean::cnstr_get(x_3, 0);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_set(x_3, 0, lean::box(0));
 lean::cnstr_release(x_3, 1);
 x_6 = x_3;
} else {
 lean::inc(x_4);
 lean::dec(x_3);
 x_6 = lean::box(0);
}
if (lean::obj_tag(x_4) == 0)
{
obj* x_7; obj* x_10; obj* x_13; obj* x_16; obj* x_18; obj* x_20; obj* x_21; obj* x_22; obj* x_24; obj* x_25; obj* x_26; obj* x_27; 
x_7 = lean::cnstr_get(x_0, 0);
lean::inc(x_7);
lean::dec(x_0);
x_10 = lean::cnstr_get(x_7, 1);
lean::inc(x_10);
lean::dec(x_7);
x_13 = lean::cnstr_get(x_4, 0);
lean::inc(x_13);
lean::dec(x_4);
x_16 = lean::cnstr_get(x_13, 3);
lean::inc(x_16);
x_18 = l_option_get___main___at_lean_parser_run___spec__2(x_16);
lean::dec(x_16);
x_20 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_20, 0, x_18);
x_21 = lean::apply_1(x_1, x_2);
x_22 = l_lean_parser_message__of__parsec__message___rarg(x_21, x_13);
lean::dec(x_21);
x_24 = l_lean_message__log_empty;
x_25 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_25, 0, x_22);
lean::cnstr_set(x_25, 1, x_24);
if (lean::is_scalar(x_6)) {
 x_26 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_26 = x_6;
}
lean::cnstr_set(x_26, 0, x_20);
lean::cnstr_set(x_26, 1, x_25);
x_27 = lean::apply_2(x_10, lean::box(0), x_26);
return x_27;
}
else
{
obj* x_31; obj* x_34; obj* x_37; obj* x_40; obj* x_42; obj* x_44; obj* x_45; obj* x_46; obj* x_47; 
lean::dec(x_6);
lean::dec(x_1);
lean::dec(x_2);
x_31 = lean::cnstr_get(x_4, 0);
lean::inc(x_31);
lean::dec(x_4);
x_34 = lean::cnstr_get(x_0, 0);
lean::inc(x_34);
lean::dec(x_0);
x_37 = lean::cnstr_get(x_34, 1);
lean::inc(x_37);
lean::dec(x_34);
x_40 = lean::cnstr_get(x_31, 0);
x_42 = lean::cnstr_get(x_31, 1);
if (lean::is_exclusive(x_31)) {
 x_44 = x_31;
} else {
 lean::inc(x_40);
 lean::inc(x_42);
 lean::dec(x_31);
 x_44 = lean::box(0);
}
x_45 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_45, 0, x_40);
if (lean::is_scalar(x_44)) {
 x_46 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_46 = x_44;
}
lean::cnstr_set(x_46, 0, x_45);
lean::cnstr_set(x_46, 1, x_42);
x_47 = lean::apply_2(x_37, lean::box(0), x_46);
return x_47;
}
}
}
obj* _init_l_lean_parser_run___rarg___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_nat_obj(0u);
x_2 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
lean::cnstr_set(x_2, 2, x_1);
return x_2;
}
}
obj* l_lean_parser_run___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_7; obj* x_9; obj* x_10; obj* x_11; obj* x_13; obj* x_14; obj* x_15; 
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
x_7 = l_lean_message__log_empty;
lean::inc(x_2);
x_9 = lean::apply_2(x_4, x_7, x_2);
x_10 = l_string_join___closed__1;
x_11 = l_lean_parser_run___rarg___closed__1;
lean::inc(x_0);
x_13 = l_lean_parser_parsec__t_run___at_lean_parser_run___spec__1___rarg(x_0, lean::box(0), lean::box(0), x_9, x_3, x_10, x_11);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_run___rarg___lambda__1), 4, 3);
lean::closure_set(x_14, 0, x_0);
lean::closure_set(x_14, 1, x_1);
lean::closure_set(x_14, 2, x_2);
x_15 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_13, x_14);
return x_15;
}
}
obj* l_lean_parser_run(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_run___rarg), 5, 0);
return x_3;
}
}
obj* l_lean_parser_parsec__t_run___at_lean_parser_run___spec__1___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_lean_parser_parsec__t_run___at_lean_parser_run___spec__1___rarg(x_0, x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_5);
return x_7;
}
}
obj* l_lean_parser_parsec__t_run___at_lean_parser_run___spec__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_parsec__t_run___at_lean_parser_run___spec__1(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_option_get___main___at_lean_parser_run___spec__2___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_option_get___main___at_lean_parser_run___spec__2(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_parser_run___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_parser_run(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_lean_parser_log__message___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_8; 
x_4 = lean::apply_1(x_0, x_1);
x_5 = l_lean_parser_message__of__parsec__message___rarg(x_4, x_2);
lean::dec(x_4);
lean::inc(x_3);
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_5);
lean::cnstr_set(x_8, 1, x_3);
return x_8;
}
}
obj* l_lean_parser_log__message___rarg___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_7; obj* x_8; 
x_4 = lean::cnstr_get(x_0, 2);
lean::inc(x_4);
lean::dec(x_0);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_log__message___rarg___lambda__1___boxed), 4, 3);
lean::closure_set(x_7, 0, x_1);
lean::closure_set(x_7, 1, x_3);
lean::closure_set(x_7, 2, x_2);
x_8 = lean::apply_1(x_4, x_7);
return x_8;
}
}
obj* l_lean_parser_log__message___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_8; obj* x_9; 
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
lean::dec(x_0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_log__message___rarg___lambda__2), 4, 3);
lean::closure_set(x_8, 0, x_3);
lean::closure_set(x_8, 1, x_2);
lean::closure_set(x_8, 2, x_4);
x_9 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_1, x_8);
return x_9;
}
}
obj* l_lean_parser_log__message(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_log__message___rarg), 5, 0);
return x_3;
}
}
obj* l_lean_parser_log__message___rarg___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_parser_log__message___rarg___lambda__1(x_0, x_1, x_2, x_3);
lean::dec(x_3);
return x_4;
}
}
obj* l_lean_parser_log__message___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_parser_log__message(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* _init_l_list_mfoldl___main___at_lean_parser_mk__token__trie___spec__1___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("invalid token '");
return x_0;
}
}
obj* _init_l_list_mfoldl___main___at_lean_parser_mk__token__trie___spec__1___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("', has been defined with precedences ");
return x_0;
}
}
obj* _init_l_list_mfoldl___main___at_lean_parser_mk__token__trie___spec__1___closed__3() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string(" and ");
return x_0;
}
}
obj* l_list_mfoldl___main___at_lean_parser_mk__token__trie___spec__1(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; 
x_2 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2, 0, x_0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_8; obj* x_12; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
lean::dec(x_1);
x_8 = lean::cnstr_get(x_3, 0);
lean::inc(x_8);
lean::inc(x_8);
lean::inc(x_0);
x_12 = l_lean_parser_trie_find___rarg(x_0, x_8);
if (lean::obj_tag(x_12) == 0)
{
obj* x_13; 
x_13 = l_lean_parser_trie_insert___rarg(x_0, x_8, x_3);
lean::dec(x_3);
x_0 = x_13;
x_1 = x_5;
goto _start;
}
else
{
obj* x_16; obj* x_19; obj* x_21; uint8 x_22; 
x_16 = lean::cnstr_get(x_12, 0);
lean::inc(x_16);
lean::dec(x_12);
x_19 = lean::cnstr_get(x_3, 1);
lean::inc(x_19);
x_21 = lean::mk_nat_obj(0u);
x_22 = lean::nat_dec_eq(x_19, x_21);
if (x_22 == 0)
{
obj* x_23; uint8 x_26; 
x_23 = lean::cnstr_get(x_16, 1);
lean::inc(x_23);
lean::dec(x_16);
x_26 = lean::nat_dec_eq(x_23, x_21);
if (x_26 == 0)
{
uint8 x_28; 
lean::dec(x_3);
x_28 = lean::nat_dec_eq(x_19, x_23);
if (x_28 == 0)
{
obj* x_31; obj* x_32; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_44; 
lean::dec(x_5);
lean::dec(x_0);
x_31 = l_list_mfoldl___main___at_lean_parser_mk__token__trie___spec__1___closed__1;
x_32 = lean::string_append(x_31, x_8);
lean::dec(x_8);
x_34 = l_list_mfoldl___main___at_lean_parser_mk__token__trie___spec__1___closed__2;
x_35 = lean::string_append(x_32, x_34);
x_36 = l_nat_repr(x_19);
x_37 = lean::string_append(x_35, x_36);
lean::dec(x_36);
x_39 = l_list_mfoldl___main___at_lean_parser_mk__token__trie___spec__1___closed__3;
x_40 = lean::string_append(x_37, x_39);
x_41 = l_nat_repr(x_23);
x_42 = lean::string_append(x_40, x_41);
lean::dec(x_41);
x_44 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_44, 0, x_42);
return x_44;
}
else
{
lean::dec(x_8);
lean::dec(x_23);
lean::dec(x_19);
x_1 = x_5;
goto _start;
}
}
else
{
obj* x_51; 
lean::dec(x_23);
lean::dec(x_19);
x_51 = l_lean_parser_trie_insert___rarg(x_0, x_8, x_3);
lean::dec(x_3);
x_0 = x_51;
x_1 = x_5;
goto _start;
}
}
else
{
obj* x_55; uint8 x_58; 
lean::dec(x_19);
x_55 = lean::cnstr_get(x_16, 1);
lean::inc(x_55);
lean::dec(x_16);
x_58 = lean::nat_dec_eq(x_55, x_21);
lean::dec(x_55);
if (x_58 == 0)
{
lean::dec(x_8);
lean::dec(x_3);
x_1 = x_5;
goto _start;
}
else
{
obj* x_63; 
x_63 = l_lean_parser_trie_insert___rarg(x_0, x_8, x_3);
lean::dec(x_3);
x_0 = x_63;
x_1 = x_5;
goto _start;
}
}
}
}
}
}
obj* _init_l_lean_parser_mk__token__trie___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::box(0);
x_1 = lean::mk_string("/-");
x_2 = lean::mk_nat_obj(0u);
x_3 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
lean::cnstr_set(x_3, 2, x_0);
x_4 = lean::mk_string("--");
x_5 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_2);
lean::cnstr_set(x_5, 2, x_0);
x_6 = lean::box(0);
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_6);
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_3);
lean::cnstr_set(x_8, 1, x_7);
return x_8;
}
}
obj* l_lean_parser_mk__token__trie(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_1 = l_lean_parser_mk__token__trie___closed__1;
x_2 = l_list_append___rarg(x_1, x_0);
x_3 = l_lean_parser_trie_mk___closed__1;
x_4 = l_list_mfoldl___main___at_lean_parser_mk__token__trie___spec__1(x_3, x_2);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; obj* x_7; obj* x_8; 
x_5 = lean::cnstr_get(x_4, 0);
if (lean::is_exclusive(x_4)) {
 x_7 = x_4;
} else {
 lean::inc(x_5);
 lean::dec(x_4);
 x_7 = lean::box(0);
}
if (lean::is_scalar(x_7)) {
 x_8 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_8 = x_7;
}
lean::cnstr_set(x_8, 0, x_5);
return x_8;
}
else
{
obj* x_9; obj* x_11; obj* x_12; 
x_9 = lean::cnstr_get(x_4, 0);
if (lean::is_exclusive(x_4)) {
 x_11 = x_4;
} else {
 lean::inc(x_9);
 lean::dec(x_4);
 x_11 = lean::box(0);
}
if (lean::is_scalar(x_11)) {
 x_12 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_12 = x_11;
}
lean::cnstr_set(x_12, 0, x_9);
return x_12;
}
}
}
obj* _init_l_lean_parser_command__parser__m_monad___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__1___boxed), 4, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__2___boxed), 4, 0);
lean::inc(x_1);
lean::inc(x_0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_id___boxed), 1, 0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__3___boxed), 4, 0);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_4);
lean::cnstr_set(x_7, 1, x_5);
lean::cnstr_set(x_7, 2, x_0);
lean::cnstr_set(x_7, 3, x_1);
lean::cnstr_set(x_7, 4, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_id_bind___boxed), 2, 0);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
x_10 = l_lean_parser_parser__core__t_monad___rarg(x_9);
x_11 = l_reader__t_monad___rarg(x_10);
x_12 = l_reader__t_monad___rarg(x_11);
return x_12;
}
}
obj* l_lean_parser_command__parser__m_monad(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_command__parser__m_monad___closed__1;
return x_1;
}
}
obj* l_lean_parser_command__parser__m_monad___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_command__parser__m_monad(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_lean_parser_command__parser__m_alternative___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_11; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__1___boxed), 4, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__2___boxed), 4, 0);
lean::inc(x_1);
lean::inc(x_0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_id___boxed), 1, 0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__3___boxed), 4, 0);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_4);
lean::cnstr_set(x_7, 1, x_5);
lean::cnstr_set(x_7, 2, x_0);
lean::cnstr_set(x_7, 3, x_1);
lean::cnstr_set(x_7, 4, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_id_bind___boxed), 2, 0);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
lean::inc(x_9);
x_11 = l_lean_parser_parser__core__t_monad___rarg(x_9);
lean::inc(x_11);
x_13 = l_reader__t_monad___rarg(x_11);
x_14 = l_lean_parser_parser__core__t_alternative___rarg(x_9);
x_15 = l_reader__t_alternative___rarg(x_11, x_14);
x_16 = l_reader__t_alternative___rarg(x_13, x_15);
return x_16;
}
}
obj* l_lean_parser_command__parser__m_alternative(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_command__parser__m_alternative___closed__1;
return x_1;
}
}
obj* l_lean_parser_command__parser__m_alternative___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_command__parser__m_alternative(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_lean_parser_command__parser__m_monad__reader___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__1___boxed), 4, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__2___boxed), 4, 0);
lean::inc(x_1);
lean::inc(x_0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_id___boxed), 1, 0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__3___boxed), 4, 0);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_4);
lean::cnstr_set(x_7, 1, x_5);
lean::cnstr_set(x_7, 2, x_0);
lean::cnstr_set(x_7, 3, x_1);
lean::cnstr_set(x_7, 4, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_id_bind___boxed), 2, 0);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
x_10 = l_lean_parser_parser__core__t_monad___rarg(x_9);
x_11 = l_reader__t_monad___rarg(x_10);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_read___rarg), 2, 1);
lean::closure_set(x_12, 0, x_11);
return x_12;
}
}
obj* l_lean_parser_command__parser__m_monad__reader(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_command__parser__m_monad__reader___closed__1;
return x_1;
}
}
obj* l_lean_parser_command__parser__m_monad__reader___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_command__parser__m_monad__reader(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_lean_parser_command__parser__m_lean_parser_monad__parsec___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__1___boxed), 4, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__2___boxed), 4, 0);
lean::inc(x_1);
lean::inc(x_0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_id___boxed), 1, 0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__3___boxed), 4, 0);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_4);
lean::cnstr_set(x_7, 1, x_5);
lean::cnstr_set(x_7, 2, x_0);
lean::cnstr_set(x_7, 3, x_1);
lean::cnstr_set(x_7, 4, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_id_bind___boxed), 2, 0);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
lean::inc(x_9);
x_11 = l_lean_parser_parser__core__t_monad___rarg(x_9);
lean::inc(x_11);
x_13 = l_reader__t_monad___rarg(x_11);
lean::inc(x_13);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_lift___boxed), 4, 3);
lean::closure_set(x_15, 0, lean::box(0));
lean::closure_set(x_15, 1, lean::box(0));
lean::closure_set(x_15, 2, x_13);
lean::inc(x_13);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_monad__functor___boxed), 6, 5);
lean::closure_set(x_17, 0, lean::box(0));
lean::closure_set(x_17, 1, lean::box(0));
lean::closure_set(x_17, 2, lean::box(0));
lean::closure_set(x_17, 3, x_13);
lean::closure_set(x_17, 4, x_13);
x_18 = l_lean_parser_parser__core__t_lean_parser_monad__parsec___rarg(x_9);
x_19 = l_lean_parser_rec__t_lean_parser_monad__parsec___rarg(x_11, lean::box(0), x_18);
x_20 = l_lean_parser_monad__parsec__trans___rarg(x_15, x_17, x_19);
return x_20;
}
}
obj* l_lean_parser_command__parser__m_lean_parser_monad__parsec(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_command__parser__m_lean_parser_monad__parsec___closed__1;
return x_1;
}
}
obj* l_lean_parser_command__parser__m_lean_parser_monad__parsec___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_command__parser__m_lean_parser_monad__parsec(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_lean_parser_command__parser__m_monad__except___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__1___boxed), 4, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__2___boxed), 4, 0);
lean::inc(x_1);
lean::inc(x_0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_id___boxed), 1, 0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__3___boxed), 4, 0);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_4);
lean::cnstr_set(x_7, 1, x_5);
lean::cnstr_set(x_7, 2, x_0);
lean::cnstr_set(x_7, 3, x_1);
lean::cnstr_set(x_7, 4, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_id_bind___boxed), 2, 0);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
x_10 = l_lean_parser_parser__core__t_monad__except___rarg(x_9);
x_11 = l_reader__t_monad__except___rarg(x_10);
x_12 = l_reader__t_monad__except___rarg(x_11);
return x_12;
}
}
obj* l_lean_parser_command__parser__m_monad__except(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_command__parser__m_monad__except___closed__1;
return x_1;
}
}
obj* l_lean_parser_command__parser__m_monad__except___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_command__parser__m_monad__except(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_lean_parser_command__parser__m_lean_parser_monad__rec___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_12; obj* x_14; obj* x_15; obj* x_16; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__1___boxed), 4, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__2___boxed), 4, 0);
lean::inc(x_1);
lean::inc(x_0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_id___boxed), 1, 0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__3___boxed), 4, 0);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_4);
lean::cnstr_set(x_7, 1, x_5);
lean::cnstr_set(x_7, 2, x_0);
lean::cnstr_set(x_7, 3, x_1);
lean::cnstr_set(x_7, 4, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_id_bind___boxed), 2, 0);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
x_10 = l_lean_parser_parser__core__t_monad___rarg(x_9);
lean::inc(x_10);
x_12 = l_reader__t_monad___rarg(x_10);
lean::inc(x_12);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_lift___boxed), 4, 3);
lean::closure_set(x_14, 0, lean::box(0));
lean::closure_set(x_14, 1, lean::box(0));
lean::closure_set(x_14, 2, x_12);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_rec__t_recurse___rarg), 3, 1);
lean::closure_set(x_15, 0, x_10);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__rec_trans___rarg___boxed), 4, 3);
lean::closure_set(x_16, 0, x_14);
lean::closure_set(x_16, 1, x_15);
lean::closure_set(x_16, 2, x_12);
return x_16;
}
}
obj* l_lean_parser_command__parser__m_lean_parser_monad__rec(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_command__parser__m_lean_parser_monad__rec___closed__1;
return x_1;
}
}
obj* l_lean_parser_command__parser__m_lean_parser_monad__rec___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_command__parser__m_lean_parser_monad__rec(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_lean_parser_command__parser__m() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* _init_l_lean_parser_command__parser__m_monad__reader__adapter___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__1___boxed), 4, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__2___boxed), 4, 0);
lean::inc(x_1);
lean::inc(x_0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_id___boxed), 1, 0);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_id_monad___lambda__3___boxed), 4, 0);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_4);
lean::cnstr_set(x_7, 1, x_5);
lean::cnstr_set(x_7, 2, x_0);
lean::cnstr_set(x_7, 3, x_1);
lean::cnstr_set(x_7, 4, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_id_bind___boxed), 2, 0);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
x_10 = l_lean_parser_parser__core__t_monad___rarg(x_9);
x_11 = l_reader__t_monad___rarg(x_10);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_monad__reader__adapter___boxed), 5, 4);
lean::closure_set(x_12, 0, lean::box(0));
lean::closure_set(x_12, 1, lean::box(0));
lean::closure_set(x_12, 2, lean::box(0));
lean::closure_set(x_12, 3, x_11);
return x_12;
}
}
obj* l_lean_parser_command__parser__m_monad__reader__adapter(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_parser_command__parser__m_monad__reader__adapter___closed__1;
return x_2;
}
}
obj* l_lean_parser_command__parser__m_monad__reader__adapter___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_parser_command__parser__m_monad__reader__adapter(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_lean_parser_command__parser__m_basic__parser___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_8; 
x_7 = lean::apply_1(x_0, x_3);
x_8 = lean::apply_3(x_2, x_7, x_5, x_6);
return x_8;
}
}
obj* l_lean_parser_command__parser__m_basic__parser(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command__parser__m_basic__parser___rarg___boxed), 7, 0);
return x_1;
}
}
obj* l_lean_parser_command__parser__m_basic__parser___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_lean_parser_command__parser__m_basic__parser___rarg(x_0, x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_1);
lean::dec(x_4);
return x_7;
}
}
obj* l_lean_parser_command__parser__m_basic__parser___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_command__parser__m_basic__parser(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_lean_parser_term__parser__m_monad() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = l_lean_parser_command__parser__m_monad___closed__1;
x_1 = l_reader__t_monad___rarg(x_0);
return x_1;
}
}
obj* _init_l_lean_parser_term__parser__m_alternative() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = l_lean_parser_command__parser__m_monad___closed__1;
x_1 = l_lean_parser_command__parser__m_alternative___closed__1;
x_2 = l_reader__t_alternative___rarg(x_0, x_1);
return x_2;
}
}
obj* _init_l_lean_parser_term__parser__m_monad__reader() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = l_lean_parser_command__parser__m_monad__reader___closed__1;
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_lift___rarg___boxed), 2, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_lean_parser_term__parser__m_lean_parser_monad__parsec() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = l_lean_parser_command__parser__m_monad___closed__1;
x_1 = l_lean_parser_command__parser__m_lean_parser_monad__parsec___closed__1;
x_2 = l_lean_parser_rec__t_lean_parser_monad__parsec___rarg(x_0, lean::box(0), x_1);
return x_2;
}
}
obj* _init_l_lean_parser_term__parser__m_monad__except() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = l_lean_parser_command__parser__m_monad__except___closed__1;
x_1 = l_reader__t_monad__except___rarg(x_0);
return x_1;
}
}
obj* _init_l_lean_parser_term__parser__m_lean_parser_monad__rec() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = l_lean_parser_command__parser__m_monad___closed__1;
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_rec__t_recurse___rarg), 3, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_lean_parser_term__parser__m_lean_parser_monad__basic__parser() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = l_lean_parser_command__parser__m_monad___closed__1;
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_lift___boxed), 4, 3);
lean::closure_set(x_1, 0, lean::box(0));
lean::closure_set(x_1, 1, lean::box(0));
lean::closure_set(x_1, 2, x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_id___rarg___boxed), 1, 0);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_command__parser__m_basic__parser___rarg___boxed), 7, 1);
lean::closure_set(x_3, 0, x_2);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_has__monad__lift__t__trans___rarg___boxed), 4, 2);
lean::closure_set(x_4, 0, x_1);
lean::closure_set(x_4, 1, x_3);
return x_4;
}
}
obj* _init_l_lean_parser_term__parser__m() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* _init_l_lean_parser_term__parser() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* _init_l_lean_parser_trailing__term__parser__m_monad() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = l_lean_parser_term__parser__m_monad;
x_1 = l_reader__t_monad___rarg(x_0);
return x_1;
}
}
obj* _init_l_lean_parser_trailing__term__parser__m_alternative() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = l_lean_parser_term__parser__m_monad;
x_1 = l_lean_parser_term__parser__m_alternative;
x_2 = l_reader__t_alternative___rarg(x_0, x_1);
return x_2;
}
}
obj* _init_l_lean_parser_trailing__term__parser__m_monad__reader() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = l_lean_parser_term__parser__m_monad;
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_read___rarg), 2, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_lean_parser_trailing__term__parser__m_lean_parser_monad__parsec() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = l_lean_parser_term__parser__m_monad;
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
x_3 = l_lean_parser_term__parser__m_lean_parser_monad__parsec;
x_4 = l_lean_parser_monad__parsec__trans___rarg(x_1, x_2, x_3);
return x_4;
}
}
obj* _init_l_lean_parser_trailing__term__parser__m_monad__except() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = l_lean_parser_term__parser__m_monad__except;
x_1 = l_reader__t_monad__except___rarg(x_0);
return x_1;
}
}
obj* _init_l_lean_parser_trailing__term__parser__m_lean_parser_monad__rec() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; 
x_0 = l_lean_parser_term__parser__m_monad;
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_lift___boxed), 4, 3);
lean::closure_set(x_1, 0, lean::box(0));
lean::closure_set(x_1, 1, lean::box(0));
lean::closure_set(x_1, 2, x_0);
x_2 = l_lean_parser_term__parser__m_lean_parser_monad__rec;
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_monad__rec_trans___rarg___boxed), 4, 3);
lean::closure_set(x_3, 0, x_1);
lean::closure_set(x_3, 1, x_2);
lean::closure_set(x_3, 2, x_0);
return x_3;
}
}
obj* _init_l_lean_parser_trailing__term__parser__m_lean_parser_monad__basic__parser() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; 
x_0 = l_lean_parser_term__parser__m_monad;
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_reader__t_lift___boxed), 4, 3);
lean::closure_set(x_1, 0, lean::box(0));
lean::closure_set(x_1, 1, lean::box(0));
lean::closure_set(x_1, 2, x_0);
x_2 = l_lean_parser_term__parser__m_lean_parser_monad__basic__parser;
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_has__monad__lift__t__trans___rarg___boxed), 4, 2);
lean::closure_set(x_3, 0, x_1);
lean::closure_set(x_3, 1, x_2);
return x_3;
}
}
obj* _init_l_lean_parser_trailing__term__parser__m() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* _init_l_lean_parser_trailing__term__parser() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* l_lean_parser_trailing__term__parser__coe(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = lean::apply_5(x_0, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
obj* l_lean_parser_trailing__term__parser__coe___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_lean_parser_trailing__term__parser__coe(x_0, x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_1);
return x_7;
}
}
obj* _init_l_lean_parser_token__map() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
obj* l_rbnode_find___main___at_lean_parser_token__map_insert___spec__2___rarg(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; 
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; uint8 x_8; 
x_3 = lean::cnstr_get(x_0, 0);
x_4 = lean::cnstr_get(x_0, 1);
x_5 = lean::cnstr_get(x_0, 2);
x_6 = lean::cnstr_get(x_0, 3);
x_7 = l_lean_name_quick__lt___main(x_1, x_4);
x_8 = lean::unbox(x_7);
if (x_8 == 0)
{
obj* x_9; uint8 x_10; 
x_9 = l_lean_name_quick__lt___main(x_4, x_1);
x_10 = lean::unbox(x_9);
if (x_10 == 0)
{
obj* x_12; 
lean::inc(x_5);
x_12 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_12, 0, x_5);
return x_12;
}
else
{
x_0 = x_6;
goto _start;
}
}
else
{
x_0 = x_3;
goto _start;
}
}
}
}
obj* l_rbnode_find___main___at_lean_parser_token__map_insert___spec__2(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_find___main___at_lean_parser_token__map_insert___spec__2___rarg___boxed), 2, 0);
return x_1;
}
}
obj* l_rbmap_find___main___at_lean_parser_token__map_insert___spec__1___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_find___main___at_lean_parser_token__map_insert___spec__2___rarg(x_0, x_1);
return x_2;
}
}
obj* l_rbmap_find___main___at_lean_parser_token__map_insert___spec__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_find___main___at_lean_parser_token__map_insert___spec__1___rarg___boxed), 2, 0);
return x_1;
}
}
obj* l_rbnode_ins___main___at_lean_parser_token__map_insert___spec__5___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
uint8 x_3; obj* x_6; obj* x_7; 
x_3 = 0;
lean::inc(x_2);
lean::inc(x_1);
x_6 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_6, 0, x_0);
lean::cnstr_set(x_6, 1, x_1);
lean::cnstr_set(x_6, 2, x_2);
lean::cnstr_set(x_6, 3, x_0);
lean::cnstr_set_scalar(x_6, sizeof(void*)*4, x_3);
x_7 = x_6;
return x_7;
}
else
{
uint8 x_8; 
x_8 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*4);
if (x_8 == 0)
{
obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_18; uint8 x_19; 
x_9 = lean::cnstr_get(x_0, 0);
x_11 = lean::cnstr_get(x_0, 1);
x_13 = lean::cnstr_get(x_0, 2);
x_15 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 lean::cnstr_set(x_0, 3, lean::box(0));
 x_17 = x_0;
} else {
 lean::inc(x_9);
 lean::inc(x_11);
 lean::inc(x_13);
 lean::inc(x_15);
 lean::dec(x_0);
 x_17 = lean::box(0);
}
x_18 = l_lean_name_quick__lt___main(x_1, x_11);
x_19 = lean::unbox(x_18);
if (x_19 == 0)
{
obj* x_20; uint8 x_21; 
x_20 = l_lean_name_quick__lt___main(x_11, x_1);
x_21 = lean::unbox(x_20);
if (x_21 == 0)
{
obj* x_26; obj* x_27; 
lean::dec(x_13);
lean::dec(x_11);
lean::inc(x_2);
lean::inc(x_1);
if (lean::is_scalar(x_17)) {
 x_26 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_26 = x_17;
}
lean::cnstr_set(x_26, 0, x_9);
lean::cnstr_set(x_26, 1, x_1);
lean::cnstr_set(x_26, 2, x_2);
lean::cnstr_set(x_26, 3, x_15);
lean::cnstr_set_scalar(x_26, sizeof(void*)*4, x_8);
x_27 = x_26;
return x_27;
}
else
{
obj* x_28; obj* x_29; obj* x_30; 
x_28 = l_rbnode_ins___main___at_lean_parser_token__map_insert___spec__5___rarg(x_15, x_1, x_2);
if (lean::is_scalar(x_17)) {
 x_29 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_29 = x_17;
}
lean::cnstr_set(x_29, 0, x_9);
lean::cnstr_set(x_29, 1, x_11);
lean::cnstr_set(x_29, 2, x_13);
lean::cnstr_set(x_29, 3, x_28);
lean::cnstr_set_scalar(x_29, sizeof(void*)*4, x_8);
x_30 = x_29;
return x_30;
}
}
else
{
obj* x_31; obj* x_32; obj* x_33; 
x_31 = l_rbnode_ins___main___at_lean_parser_token__map_insert___spec__5___rarg(x_9, x_1, x_2);
if (lean::is_scalar(x_17)) {
 x_32 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_32 = x_17;
}
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_11);
lean::cnstr_set(x_32, 2, x_13);
lean::cnstr_set(x_32, 3, x_15);
lean::cnstr_set_scalar(x_32, sizeof(void*)*4, x_8);
x_33 = x_32;
return x_33;
}
}
else
{
obj* x_34; obj* x_36; obj* x_38; obj* x_40; obj* x_42; obj* x_43; uint8 x_44; 
x_34 = lean::cnstr_get(x_0, 0);
x_36 = lean::cnstr_get(x_0, 1);
x_38 = lean::cnstr_get(x_0, 2);
x_40 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 lean::cnstr_set(x_0, 3, lean::box(0));
 x_42 = x_0;
} else {
 lean::inc(x_34);
 lean::inc(x_36);
 lean::inc(x_38);
 lean::inc(x_40);
 lean::dec(x_0);
 x_42 = lean::box(0);
}
x_43 = l_lean_name_quick__lt___main(x_1, x_36);
x_44 = lean::unbox(x_43);
if (x_44 == 0)
{
obj* x_45; uint8 x_46; 
x_45 = l_lean_name_quick__lt___main(x_36, x_1);
x_46 = lean::unbox(x_45);
if (x_46 == 0)
{
obj* x_51; obj* x_52; 
lean::dec(x_38);
lean::dec(x_36);
lean::inc(x_2);
lean::inc(x_1);
if (lean::is_scalar(x_42)) {
 x_51 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_51 = x_42;
}
lean::cnstr_set(x_51, 0, x_34);
lean::cnstr_set(x_51, 1, x_1);
lean::cnstr_set(x_51, 2, x_2);
lean::cnstr_set(x_51, 3, x_40);
lean::cnstr_set_scalar(x_51, sizeof(void*)*4, x_8);
x_52 = x_51;
return x_52;
}
else
{
uint8 x_53; 
x_53 = l_rbnode_is__red___main___rarg(x_40);
if (x_53 == 0)
{
obj* x_54; obj* x_55; obj* x_56; 
x_54 = l_rbnode_ins___main___at_lean_parser_token__map_insert___spec__5___rarg(x_40, x_1, x_2);
if (lean::is_scalar(x_42)) {
 x_55 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_55 = x_42;
}
lean::cnstr_set(x_55, 0, x_34);
lean::cnstr_set(x_55, 1, x_36);
lean::cnstr_set(x_55, 2, x_38);
lean::cnstr_set(x_55, 3, x_54);
lean::cnstr_set_scalar(x_55, sizeof(void*)*4, x_8);
x_56 = x_55;
return x_56;
}
else
{
obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
x_57 = lean::box(0);
if (lean::is_scalar(x_42)) {
 x_58 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_58 = x_42;
}
lean::cnstr_set(x_58, 0, x_34);
lean::cnstr_set(x_58, 1, x_36);
lean::cnstr_set(x_58, 2, x_38);
lean::cnstr_set(x_58, 3, x_57);
lean::cnstr_set_scalar(x_58, sizeof(void*)*4, x_8);
x_59 = x_58;
x_60 = l_rbnode_ins___main___at_lean_parser_token__map_insert___spec__5___rarg(x_40, x_1, x_2);
x_61 = l_rbnode_balance2___main___rarg(x_59, x_60);
return x_61;
}
}
}
else
{
uint8 x_62; 
x_62 = l_rbnode_is__red___main___rarg(x_34);
if (x_62 == 0)
{
obj* x_63; obj* x_64; obj* x_65; 
x_63 = l_rbnode_ins___main___at_lean_parser_token__map_insert___spec__5___rarg(x_34, x_1, x_2);
if (lean::is_scalar(x_42)) {
 x_64 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_64 = x_42;
}
lean::cnstr_set(x_64, 0, x_63);
lean::cnstr_set(x_64, 1, x_36);
lean::cnstr_set(x_64, 2, x_38);
lean::cnstr_set(x_64, 3, x_40);
lean::cnstr_set_scalar(x_64, sizeof(void*)*4, x_8);
x_65 = x_64;
return x_65;
}
else
{
obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; 
x_66 = lean::box(0);
if (lean::is_scalar(x_42)) {
 x_67 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_67 = x_42;
}
lean::cnstr_set(x_67, 0, x_66);
lean::cnstr_set(x_67, 1, x_36);
lean::cnstr_set(x_67, 2, x_38);
lean::cnstr_set(x_67, 3, x_40);
lean::cnstr_set_scalar(x_67, sizeof(void*)*4, x_8);
x_68 = x_67;
x_69 = l_rbnode_ins___main___at_lean_parser_token__map_insert___spec__5___rarg(x_34, x_1, x_2);
x_70 = l_rbnode_balance1___main___rarg(x_68, x_69);
return x_70;
}
}
}
}
}
}
obj* l_rbnode_ins___main___at_lean_parser_token__map_insert___spec__5(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_ins___main___at_lean_parser_token__map_insert___spec__5___rarg___boxed), 3, 0);
return x_1;
}
}
obj* l_rbnode_ins___main___at_lean_parser_token__map_insert___spec__6___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
uint8 x_3; obj* x_6; obj* x_7; 
x_3 = 0;
lean::inc(x_2);
lean::inc(x_1);
x_6 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_6, 0, x_0);
lean::cnstr_set(x_6, 1, x_1);
lean::cnstr_set(x_6, 2, x_2);
lean::cnstr_set(x_6, 3, x_0);
lean::cnstr_set_scalar(x_6, sizeof(void*)*4, x_3);
x_7 = x_6;
return x_7;
}
else
{
uint8 x_8; 
x_8 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*4);
if (x_8 == 0)
{
obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_18; uint8 x_19; 
x_9 = lean::cnstr_get(x_0, 0);
x_11 = lean::cnstr_get(x_0, 1);
x_13 = lean::cnstr_get(x_0, 2);
x_15 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 lean::cnstr_set(x_0, 3, lean::box(0));
 x_17 = x_0;
} else {
 lean::inc(x_9);
 lean::inc(x_11);
 lean::inc(x_13);
 lean::inc(x_15);
 lean::dec(x_0);
 x_17 = lean::box(0);
}
x_18 = l_lean_name_quick__lt___main(x_1, x_11);
x_19 = lean::unbox(x_18);
if (x_19 == 0)
{
obj* x_20; uint8 x_21; 
x_20 = l_lean_name_quick__lt___main(x_11, x_1);
x_21 = lean::unbox(x_20);
if (x_21 == 0)
{
obj* x_26; obj* x_27; 
lean::dec(x_13);
lean::dec(x_11);
lean::inc(x_2);
lean::inc(x_1);
if (lean::is_scalar(x_17)) {
 x_26 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_26 = x_17;
}
lean::cnstr_set(x_26, 0, x_9);
lean::cnstr_set(x_26, 1, x_1);
lean::cnstr_set(x_26, 2, x_2);
lean::cnstr_set(x_26, 3, x_15);
lean::cnstr_set_scalar(x_26, sizeof(void*)*4, x_8);
x_27 = x_26;
return x_27;
}
else
{
obj* x_28; obj* x_29; obj* x_30; 
x_28 = l_rbnode_ins___main___at_lean_parser_token__map_insert___spec__6___rarg(x_15, x_1, x_2);
if (lean::is_scalar(x_17)) {
 x_29 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_29 = x_17;
}
lean::cnstr_set(x_29, 0, x_9);
lean::cnstr_set(x_29, 1, x_11);
lean::cnstr_set(x_29, 2, x_13);
lean::cnstr_set(x_29, 3, x_28);
lean::cnstr_set_scalar(x_29, sizeof(void*)*4, x_8);
x_30 = x_29;
return x_30;
}
}
else
{
obj* x_31; obj* x_32; obj* x_33; 
x_31 = l_rbnode_ins___main___at_lean_parser_token__map_insert___spec__6___rarg(x_9, x_1, x_2);
if (lean::is_scalar(x_17)) {
 x_32 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_32 = x_17;
}
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_11);
lean::cnstr_set(x_32, 2, x_13);
lean::cnstr_set(x_32, 3, x_15);
lean::cnstr_set_scalar(x_32, sizeof(void*)*4, x_8);
x_33 = x_32;
return x_33;
}
}
else
{
obj* x_34; obj* x_36; obj* x_38; obj* x_40; obj* x_42; obj* x_43; uint8 x_44; 
x_34 = lean::cnstr_get(x_0, 0);
x_36 = lean::cnstr_get(x_0, 1);
x_38 = lean::cnstr_get(x_0, 2);
x_40 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 lean::cnstr_set(x_0, 3, lean::box(0));
 x_42 = x_0;
} else {
 lean::inc(x_34);
 lean::inc(x_36);
 lean::inc(x_38);
 lean::inc(x_40);
 lean::dec(x_0);
 x_42 = lean::box(0);
}
x_43 = l_lean_name_quick__lt___main(x_1, x_36);
x_44 = lean::unbox(x_43);
if (x_44 == 0)
{
obj* x_45; uint8 x_46; 
x_45 = l_lean_name_quick__lt___main(x_36, x_1);
x_46 = lean::unbox(x_45);
if (x_46 == 0)
{
obj* x_51; obj* x_52; 
lean::dec(x_38);
lean::dec(x_36);
lean::inc(x_2);
lean::inc(x_1);
if (lean::is_scalar(x_42)) {
 x_51 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_51 = x_42;
}
lean::cnstr_set(x_51, 0, x_34);
lean::cnstr_set(x_51, 1, x_1);
lean::cnstr_set(x_51, 2, x_2);
lean::cnstr_set(x_51, 3, x_40);
lean::cnstr_set_scalar(x_51, sizeof(void*)*4, x_8);
x_52 = x_51;
return x_52;
}
else
{
uint8 x_53; 
x_53 = l_rbnode_is__red___main___rarg(x_40);
if (x_53 == 0)
{
obj* x_54; obj* x_55; obj* x_56; 
x_54 = l_rbnode_ins___main___at_lean_parser_token__map_insert___spec__6___rarg(x_40, x_1, x_2);
if (lean::is_scalar(x_42)) {
 x_55 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_55 = x_42;
}
lean::cnstr_set(x_55, 0, x_34);
lean::cnstr_set(x_55, 1, x_36);
lean::cnstr_set(x_55, 2, x_38);
lean::cnstr_set(x_55, 3, x_54);
lean::cnstr_set_scalar(x_55, sizeof(void*)*4, x_8);
x_56 = x_55;
return x_56;
}
else
{
obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
x_57 = lean::box(0);
if (lean::is_scalar(x_42)) {
 x_58 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_58 = x_42;
}
lean::cnstr_set(x_58, 0, x_34);
lean::cnstr_set(x_58, 1, x_36);
lean::cnstr_set(x_58, 2, x_38);
lean::cnstr_set(x_58, 3, x_57);
lean::cnstr_set_scalar(x_58, sizeof(void*)*4, x_8);
x_59 = x_58;
x_60 = l_rbnode_ins___main___at_lean_parser_token__map_insert___spec__6___rarg(x_40, x_1, x_2);
x_61 = l_rbnode_balance2___main___rarg(x_59, x_60);
return x_61;
}
}
}
else
{
uint8 x_62; 
x_62 = l_rbnode_is__red___main___rarg(x_34);
if (x_62 == 0)
{
obj* x_63; obj* x_64; obj* x_65; 
x_63 = l_rbnode_ins___main___at_lean_parser_token__map_insert___spec__6___rarg(x_34, x_1, x_2);
if (lean::is_scalar(x_42)) {
 x_64 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_64 = x_42;
}
lean::cnstr_set(x_64, 0, x_63);
lean::cnstr_set(x_64, 1, x_36);
lean::cnstr_set(x_64, 2, x_38);
lean::cnstr_set(x_64, 3, x_40);
lean::cnstr_set_scalar(x_64, sizeof(void*)*4, x_8);
x_65 = x_64;
return x_65;
}
else
{
obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; 
x_66 = lean::box(0);
if (lean::is_scalar(x_42)) {
 x_67 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_67 = x_42;
}
lean::cnstr_set(x_67, 0, x_66);
lean::cnstr_set(x_67, 1, x_36);
lean::cnstr_set(x_67, 2, x_38);
lean::cnstr_set(x_67, 3, x_40);
lean::cnstr_set_scalar(x_67, sizeof(void*)*4, x_8);
x_68 = x_67;
x_69 = l_rbnode_ins___main___at_lean_parser_token__map_insert___spec__6___rarg(x_34, x_1, x_2);
x_70 = l_rbnode_balance1___main___rarg(x_68, x_69);
return x_70;
}
}
}
}
}
}
obj* l_rbnode_ins___main___at_lean_parser_token__map_insert___spec__6(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_ins___main___at_lean_parser_token__map_insert___spec__6___rarg___boxed), 3, 0);
return x_1;
}
}
obj* l_rbnode_insert___at_lean_parser_token__map_insert___spec__4___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_rbnode_is__red___main___rarg(x_0);
if (x_3 == 0)
{
obj* x_4; 
x_4 = l_rbnode_ins___main___at_lean_parser_token__map_insert___spec__5___rarg(x_0, x_1, x_2);
return x_4;
}
else
{
obj* x_5; obj* x_6; 
x_5 = l_rbnode_ins___main___at_lean_parser_token__map_insert___spec__6___rarg(x_0, x_1, x_2);
x_6 = l_rbnode_set__black___main___rarg(x_5);
return x_6;
}
}
}
obj* l_rbnode_insert___at_lean_parser_token__map_insert___spec__4(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_insert___at_lean_parser_token__map_insert___spec__4___rarg___boxed), 3, 0);
return x_1;
}
}
obj* l_rbmap_insert___main___at_lean_parser_token__map_insert___spec__3___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_insert___at_lean_parser_token__map_insert___spec__4___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_rbmap_insert___main___at_lean_parser_token__map_insert___spec__3(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_insert___main___at_lean_parser_token__map_insert___spec__3___rarg___boxed), 3, 0);
return x_1;
}
}
obj* l_rbnode_ins___main___at_lean_parser_token__map_insert___spec__9___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
uint8 x_3; obj* x_6; obj* x_7; 
x_3 = 0;
lean::inc(x_2);
lean::inc(x_1);
x_6 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_6, 0, x_0);
lean::cnstr_set(x_6, 1, x_1);
lean::cnstr_set(x_6, 2, x_2);
lean::cnstr_set(x_6, 3, x_0);
lean::cnstr_set_scalar(x_6, sizeof(void*)*4, x_3);
x_7 = x_6;
return x_7;
}
else
{
uint8 x_8; 
x_8 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*4);
if (x_8 == 0)
{
obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_18; uint8 x_19; 
x_9 = lean::cnstr_get(x_0, 0);
x_11 = lean::cnstr_get(x_0, 1);
x_13 = lean::cnstr_get(x_0, 2);
x_15 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 lean::cnstr_set(x_0, 3, lean::box(0));
 x_17 = x_0;
} else {
 lean::inc(x_9);
 lean::inc(x_11);
 lean::inc(x_13);
 lean::inc(x_15);
 lean::dec(x_0);
 x_17 = lean::box(0);
}
x_18 = l_lean_name_quick__lt___main(x_1, x_11);
x_19 = lean::unbox(x_18);
if (x_19 == 0)
{
obj* x_20; uint8 x_21; 
x_20 = l_lean_name_quick__lt___main(x_11, x_1);
x_21 = lean::unbox(x_20);
if (x_21 == 0)
{
obj* x_26; obj* x_27; 
lean::dec(x_13);
lean::dec(x_11);
lean::inc(x_2);
lean::inc(x_1);
if (lean::is_scalar(x_17)) {
 x_26 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_26 = x_17;
}
lean::cnstr_set(x_26, 0, x_9);
lean::cnstr_set(x_26, 1, x_1);
lean::cnstr_set(x_26, 2, x_2);
lean::cnstr_set(x_26, 3, x_15);
lean::cnstr_set_scalar(x_26, sizeof(void*)*4, x_8);
x_27 = x_26;
return x_27;
}
else
{
obj* x_28; obj* x_29; obj* x_30; 
x_28 = l_rbnode_ins___main___at_lean_parser_token__map_insert___spec__9___rarg(x_15, x_1, x_2);
if (lean::is_scalar(x_17)) {
 x_29 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_29 = x_17;
}
lean::cnstr_set(x_29, 0, x_9);
lean::cnstr_set(x_29, 1, x_11);
lean::cnstr_set(x_29, 2, x_13);
lean::cnstr_set(x_29, 3, x_28);
lean::cnstr_set_scalar(x_29, sizeof(void*)*4, x_8);
x_30 = x_29;
return x_30;
}
}
else
{
obj* x_31; obj* x_32; obj* x_33; 
x_31 = l_rbnode_ins___main___at_lean_parser_token__map_insert___spec__9___rarg(x_9, x_1, x_2);
if (lean::is_scalar(x_17)) {
 x_32 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_32 = x_17;
}
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_11);
lean::cnstr_set(x_32, 2, x_13);
lean::cnstr_set(x_32, 3, x_15);
lean::cnstr_set_scalar(x_32, sizeof(void*)*4, x_8);
x_33 = x_32;
return x_33;
}
}
else
{
obj* x_34; obj* x_36; obj* x_38; obj* x_40; obj* x_42; obj* x_43; uint8 x_44; 
x_34 = lean::cnstr_get(x_0, 0);
x_36 = lean::cnstr_get(x_0, 1);
x_38 = lean::cnstr_get(x_0, 2);
x_40 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 lean::cnstr_set(x_0, 3, lean::box(0));
 x_42 = x_0;
} else {
 lean::inc(x_34);
 lean::inc(x_36);
 lean::inc(x_38);
 lean::inc(x_40);
 lean::dec(x_0);
 x_42 = lean::box(0);
}
x_43 = l_lean_name_quick__lt___main(x_1, x_36);
x_44 = lean::unbox(x_43);
if (x_44 == 0)
{
obj* x_45; uint8 x_46; 
x_45 = l_lean_name_quick__lt___main(x_36, x_1);
x_46 = lean::unbox(x_45);
if (x_46 == 0)
{
obj* x_51; obj* x_52; 
lean::dec(x_38);
lean::dec(x_36);
lean::inc(x_2);
lean::inc(x_1);
if (lean::is_scalar(x_42)) {
 x_51 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_51 = x_42;
}
lean::cnstr_set(x_51, 0, x_34);
lean::cnstr_set(x_51, 1, x_1);
lean::cnstr_set(x_51, 2, x_2);
lean::cnstr_set(x_51, 3, x_40);
lean::cnstr_set_scalar(x_51, sizeof(void*)*4, x_8);
x_52 = x_51;
return x_52;
}
else
{
uint8 x_53; 
x_53 = l_rbnode_is__red___main___rarg(x_40);
if (x_53 == 0)
{
obj* x_54; obj* x_55; obj* x_56; 
x_54 = l_rbnode_ins___main___at_lean_parser_token__map_insert___spec__9___rarg(x_40, x_1, x_2);
if (lean::is_scalar(x_42)) {
 x_55 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_55 = x_42;
}
lean::cnstr_set(x_55, 0, x_34);
lean::cnstr_set(x_55, 1, x_36);
lean::cnstr_set(x_55, 2, x_38);
lean::cnstr_set(x_55, 3, x_54);
lean::cnstr_set_scalar(x_55, sizeof(void*)*4, x_8);
x_56 = x_55;
return x_56;
}
else
{
obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
x_57 = lean::box(0);
if (lean::is_scalar(x_42)) {
 x_58 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_58 = x_42;
}
lean::cnstr_set(x_58, 0, x_34);
lean::cnstr_set(x_58, 1, x_36);
lean::cnstr_set(x_58, 2, x_38);
lean::cnstr_set(x_58, 3, x_57);
lean::cnstr_set_scalar(x_58, sizeof(void*)*4, x_8);
x_59 = x_58;
x_60 = l_rbnode_ins___main___at_lean_parser_token__map_insert___spec__9___rarg(x_40, x_1, x_2);
x_61 = l_rbnode_balance2___main___rarg(x_59, x_60);
return x_61;
}
}
}
else
{
uint8 x_62; 
x_62 = l_rbnode_is__red___main___rarg(x_34);
if (x_62 == 0)
{
obj* x_63; obj* x_64; obj* x_65; 
x_63 = l_rbnode_ins___main___at_lean_parser_token__map_insert___spec__9___rarg(x_34, x_1, x_2);
if (lean::is_scalar(x_42)) {
 x_64 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_64 = x_42;
}
lean::cnstr_set(x_64, 0, x_63);
lean::cnstr_set(x_64, 1, x_36);
lean::cnstr_set(x_64, 2, x_38);
lean::cnstr_set(x_64, 3, x_40);
lean::cnstr_set_scalar(x_64, sizeof(void*)*4, x_8);
x_65 = x_64;
return x_65;
}
else
{
obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; 
x_66 = lean::box(0);
if (lean::is_scalar(x_42)) {
 x_67 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_67 = x_42;
}
lean::cnstr_set(x_67, 0, x_66);
lean::cnstr_set(x_67, 1, x_36);
lean::cnstr_set(x_67, 2, x_38);
lean::cnstr_set(x_67, 3, x_40);
lean::cnstr_set_scalar(x_67, sizeof(void*)*4, x_8);
x_68 = x_67;
x_69 = l_rbnode_ins___main___at_lean_parser_token__map_insert___spec__9___rarg(x_34, x_1, x_2);
x_70 = l_rbnode_balance1___main___rarg(x_68, x_69);
return x_70;
}
}
}
}
}
}
obj* l_rbnode_ins___main___at_lean_parser_token__map_insert___spec__9(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_ins___main___at_lean_parser_token__map_insert___spec__9___rarg___boxed), 3, 0);
return x_1;
}
}
obj* l_rbnode_ins___main___at_lean_parser_token__map_insert___spec__10___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
uint8 x_3; obj* x_6; obj* x_7; 
x_3 = 0;
lean::inc(x_2);
lean::inc(x_1);
x_6 = lean::alloc_cnstr(1, 4, 1);
lean::cnstr_set(x_6, 0, x_0);
lean::cnstr_set(x_6, 1, x_1);
lean::cnstr_set(x_6, 2, x_2);
lean::cnstr_set(x_6, 3, x_0);
lean::cnstr_set_scalar(x_6, sizeof(void*)*4, x_3);
x_7 = x_6;
return x_7;
}
else
{
uint8 x_8; 
x_8 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*4);
if (x_8 == 0)
{
obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_18; uint8 x_19; 
x_9 = lean::cnstr_get(x_0, 0);
x_11 = lean::cnstr_get(x_0, 1);
x_13 = lean::cnstr_get(x_0, 2);
x_15 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 lean::cnstr_set(x_0, 3, lean::box(0));
 x_17 = x_0;
} else {
 lean::inc(x_9);
 lean::inc(x_11);
 lean::inc(x_13);
 lean::inc(x_15);
 lean::dec(x_0);
 x_17 = lean::box(0);
}
x_18 = l_lean_name_quick__lt___main(x_1, x_11);
x_19 = lean::unbox(x_18);
if (x_19 == 0)
{
obj* x_20; uint8 x_21; 
x_20 = l_lean_name_quick__lt___main(x_11, x_1);
x_21 = lean::unbox(x_20);
if (x_21 == 0)
{
obj* x_26; obj* x_27; 
lean::dec(x_13);
lean::dec(x_11);
lean::inc(x_2);
lean::inc(x_1);
if (lean::is_scalar(x_17)) {
 x_26 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_26 = x_17;
}
lean::cnstr_set(x_26, 0, x_9);
lean::cnstr_set(x_26, 1, x_1);
lean::cnstr_set(x_26, 2, x_2);
lean::cnstr_set(x_26, 3, x_15);
lean::cnstr_set_scalar(x_26, sizeof(void*)*4, x_8);
x_27 = x_26;
return x_27;
}
else
{
obj* x_28; obj* x_29; obj* x_30; 
x_28 = l_rbnode_ins___main___at_lean_parser_token__map_insert___spec__10___rarg(x_15, x_1, x_2);
if (lean::is_scalar(x_17)) {
 x_29 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_29 = x_17;
}
lean::cnstr_set(x_29, 0, x_9);
lean::cnstr_set(x_29, 1, x_11);
lean::cnstr_set(x_29, 2, x_13);
lean::cnstr_set(x_29, 3, x_28);
lean::cnstr_set_scalar(x_29, sizeof(void*)*4, x_8);
x_30 = x_29;
return x_30;
}
}
else
{
obj* x_31; obj* x_32; obj* x_33; 
x_31 = l_rbnode_ins___main___at_lean_parser_token__map_insert___spec__10___rarg(x_9, x_1, x_2);
if (lean::is_scalar(x_17)) {
 x_32 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_32 = x_17;
}
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_11);
lean::cnstr_set(x_32, 2, x_13);
lean::cnstr_set(x_32, 3, x_15);
lean::cnstr_set_scalar(x_32, sizeof(void*)*4, x_8);
x_33 = x_32;
return x_33;
}
}
else
{
obj* x_34; obj* x_36; obj* x_38; obj* x_40; obj* x_42; obj* x_43; uint8 x_44; 
x_34 = lean::cnstr_get(x_0, 0);
x_36 = lean::cnstr_get(x_0, 1);
x_38 = lean::cnstr_get(x_0, 2);
x_40 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 lean::cnstr_set(x_0, 3, lean::box(0));
 x_42 = x_0;
} else {
 lean::inc(x_34);
 lean::inc(x_36);
 lean::inc(x_38);
 lean::inc(x_40);
 lean::dec(x_0);
 x_42 = lean::box(0);
}
x_43 = l_lean_name_quick__lt___main(x_1, x_36);
x_44 = lean::unbox(x_43);
if (x_44 == 0)
{
obj* x_45; uint8 x_46; 
x_45 = l_lean_name_quick__lt___main(x_36, x_1);
x_46 = lean::unbox(x_45);
if (x_46 == 0)
{
obj* x_51; obj* x_52; 
lean::dec(x_38);
lean::dec(x_36);
lean::inc(x_2);
lean::inc(x_1);
if (lean::is_scalar(x_42)) {
 x_51 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_51 = x_42;
}
lean::cnstr_set(x_51, 0, x_34);
lean::cnstr_set(x_51, 1, x_1);
lean::cnstr_set(x_51, 2, x_2);
lean::cnstr_set(x_51, 3, x_40);
lean::cnstr_set_scalar(x_51, sizeof(void*)*4, x_8);
x_52 = x_51;
return x_52;
}
else
{
uint8 x_53; 
x_53 = l_rbnode_is__red___main___rarg(x_40);
if (x_53 == 0)
{
obj* x_54; obj* x_55; obj* x_56; 
x_54 = l_rbnode_ins___main___at_lean_parser_token__map_insert___spec__10___rarg(x_40, x_1, x_2);
if (lean::is_scalar(x_42)) {
 x_55 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_55 = x_42;
}
lean::cnstr_set(x_55, 0, x_34);
lean::cnstr_set(x_55, 1, x_36);
lean::cnstr_set(x_55, 2, x_38);
lean::cnstr_set(x_55, 3, x_54);
lean::cnstr_set_scalar(x_55, sizeof(void*)*4, x_8);
x_56 = x_55;
return x_56;
}
else
{
obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
x_57 = lean::box(0);
if (lean::is_scalar(x_42)) {
 x_58 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_58 = x_42;
}
lean::cnstr_set(x_58, 0, x_34);
lean::cnstr_set(x_58, 1, x_36);
lean::cnstr_set(x_58, 2, x_38);
lean::cnstr_set(x_58, 3, x_57);
lean::cnstr_set_scalar(x_58, sizeof(void*)*4, x_8);
x_59 = x_58;
x_60 = l_rbnode_ins___main___at_lean_parser_token__map_insert___spec__10___rarg(x_40, x_1, x_2);
x_61 = l_rbnode_balance2___main___rarg(x_59, x_60);
return x_61;
}
}
}
else
{
uint8 x_62; 
x_62 = l_rbnode_is__red___main___rarg(x_34);
if (x_62 == 0)
{
obj* x_63; obj* x_64; obj* x_65; 
x_63 = l_rbnode_ins___main___at_lean_parser_token__map_insert___spec__10___rarg(x_34, x_1, x_2);
if (lean::is_scalar(x_42)) {
 x_64 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_64 = x_42;
}
lean::cnstr_set(x_64, 0, x_63);
lean::cnstr_set(x_64, 1, x_36);
lean::cnstr_set(x_64, 2, x_38);
lean::cnstr_set(x_64, 3, x_40);
lean::cnstr_set_scalar(x_64, sizeof(void*)*4, x_8);
x_65 = x_64;
return x_65;
}
else
{
obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; 
x_66 = lean::box(0);
if (lean::is_scalar(x_42)) {
 x_67 = lean::alloc_cnstr(1, 4, 1);
} else {
 x_67 = x_42;
}
lean::cnstr_set(x_67, 0, x_66);
lean::cnstr_set(x_67, 1, x_36);
lean::cnstr_set(x_67, 2, x_38);
lean::cnstr_set(x_67, 3, x_40);
lean::cnstr_set_scalar(x_67, sizeof(void*)*4, x_8);
x_68 = x_67;
x_69 = l_rbnode_ins___main___at_lean_parser_token__map_insert___spec__10___rarg(x_34, x_1, x_2);
x_70 = l_rbnode_balance1___main___rarg(x_68, x_69);
return x_70;
}
}
}
}
}
}
obj* l_rbnode_ins___main___at_lean_parser_token__map_insert___spec__10(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_ins___main___at_lean_parser_token__map_insert___spec__10___rarg___boxed), 3, 0);
return x_1;
}
}
obj* l_rbnode_insert___at_lean_parser_token__map_insert___spec__8___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_rbnode_is__red___main___rarg(x_0);
if (x_3 == 0)
{
obj* x_4; 
x_4 = l_rbnode_ins___main___at_lean_parser_token__map_insert___spec__9___rarg(x_0, x_1, x_2);
return x_4;
}
else
{
obj* x_5; obj* x_6; 
x_5 = l_rbnode_ins___main___at_lean_parser_token__map_insert___spec__10___rarg(x_0, x_1, x_2);
x_6 = l_rbnode_set__black___main___rarg(x_5);
return x_6;
}
}
}
obj* l_rbnode_insert___at_lean_parser_token__map_insert___spec__8(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_rbnode_insert___at_lean_parser_token__map_insert___spec__8___rarg___boxed), 3, 0);
return x_1;
}
}
obj* l_rbmap_insert___main___at_lean_parser_token__map_insert___spec__7___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_insert___at_lean_parser_token__map_insert___spec__8___rarg(x_0, x_1, x_2);
return x_3;
}
}
obj* l_rbmap_insert___main___at_lean_parser_token__map_insert___spec__7(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_rbmap_insert___main___at_lean_parser_token__map_insert___spec__7___rarg___boxed), 3, 0);
return x_1;
}
}
obj* l_lean_parser_token__map_insert___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_find___main___at_lean_parser_token__map_insert___spec__2___rarg(x_0, x_1);
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; obj* x_6; obj* x_7; 
x_4 = lean::box(0);
lean::inc(x_2);
x_6 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_6, 0, x_2);
lean::cnstr_set(x_6, 1, x_4);
x_7 = l_rbnode_insert___at_lean_parser_token__map_insert___spec__4___rarg(x_0, x_1, x_6);
lean::dec(x_6);
return x_7;
}
else
{
obj* x_9; obj* x_13; obj* x_14; 
x_9 = lean::cnstr_get(x_3, 0);
lean::inc(x_9);
lean::dec(x_3);
lean::inc(x_2);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_2);
lean::cnstr_set(x_13, 1, x_9);
x_14 = l_rbnode_insert___at_lean_parser_token__map_insert___spec__8___rarg(x_0, x_1, x_13);
lean::dec(x_13);
return x_14;
}
}
}
obj* l_lean_parser_token__map_insert(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_token__map_insert___rarg___boxed), 3, 0);
return x_1;
}
}
obj* l_rbnode_find___main___at_lean_parser_token__map_insert___spec__2___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbnode_find___main___at_lean_parser_token__map_insert___spec__2___rarg(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_rbnode_find___main___at_lean_parser_token__map_insert___spec__2___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_rbnode_find___main___at_lean_parser_token__map_insert___spec__2(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_rbmap_find___main___at_lean_parser_token__map_insert___spec__1___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_rbmap_find___main___at_lean_parser_token__map_insert___spec__1___rarg(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_rbmap_find___main___at_lean_parser_token__map_insert___spec__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_rbmap_find___main___at_lean_parser_token__map_insert___spec__1(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_rbnode_ins___main___at_lean_parser_token__map_insert___spec__5___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_ins___main___at_lean_parser_token__map_insert___spec__5___rarg(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_rbnode_ins___main___at_lean_parser_token__map_insert___spec__5___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_rbnode_ins___main___at_lean_parser_token__map_insert___spec__5(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_rbnode_ins___main___at_lean_parser_token__map_insert___spec__6___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_ins___main___at_lean_parser_token__map_insert___spec__6___rarg(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_rbnode_ins___main___at_lean_parser_token__map_insert___spec__6___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_rbnode_ins___main___at_lean_parser_token__map_insert___spec__6(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_rbnode_insert___at_lean_parser_token__map_insert___spec__4___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_insert___at_lean_parser_token__map_insert___spec__4___rarg(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_rbnode_insert___at_lean_parser_token__map_insert___spec__4___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_rbnode_insert___at_lean_parser_token__map_insert___spec__4(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_rbmap_insert___main___at_lean_parser_token__map_insert___spec__3___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbmap_insert___main___at_lean_parser_token__map_insert___spec__3___rarg(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_rbmap_insert___main___at_lean_parser_token__map_insert___spec__3___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_rbmap_insert___main___at_lean_parser_token__map_insert___spec__3(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_rbnode_ins___main___at_lean_parser_token__map_insert___spec__9___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_ins___main___at_lean_parser_token__map_insert___spec__9___rarg(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_rbnode_ins___main___at_lean_parser_token__map_insert___spec__9___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_rbnode_ins___main___at_lean_parser_token__map_insert___spec__9(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_rbnode_ins___main___at_lean_parser_token__map_insert___spec__10___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_ins___main___at_lean_parser_token__map_insert___spec__10___rarg(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_rbnode_ins___main___at_lean_parser_token__map_insert___spec__10___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_rbnode_ins___main___at_lean_parser_token__map_insert___spec__10(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_rbnode_insert___at_lean_parser_token__map_insert___spec__8___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbnode_insert___at_lean_parser_token__map_insert___spec__8___rarg(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_rbnode_insert___at_lean_parser_token__map_insert___spec__8___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_rbnode_insert___at_lean_parser_token__map_insert___spec__8(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_rbmap_insert___main___at_lean_parser_token__map_insert___spec__7___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_rbmap_insert___main___at_lean_parser_token__map_insert___spec__7___rarg(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_rbmap_insert___main___at_lean_parser_token__map_insert___spec__7___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_rbmap_insert___main___at_lean_parser_token__map_insert___spec__7(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_parser_token__map_insert___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_lean_parser_token__map_insert___rarg(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_lean_parser_token__map_insert___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_token__map_insert(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_parser_token__map_of__list___main___rarg(obj* x_0) {
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
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_2 = lean::cnstr_get(x_0, 0);
x_3 = lean::cnstr_get(x_0, 1);
x_4 = lean::cnstr_get(x_2, 0);
x_5 = lean::cnstr_get(x_2, 1);
x_6 = l_lean_parser_token__map_of__list___main___rarg(x_3);
x_7 = l_lean_parser_token__map_insert___rarg(x_6, x_4, x_5);
return x_7;
}
}
}
obj* l_lean_parser_token__map_of__list___main(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_token__map_of__list___main___rarg___boxed), 1, 0);
return x_1;
}
}
obj* l_lean_parser_token__map_of__list___main___rarg___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_token__map_of__list___main___rarg(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_parser_token__map_of__list___main___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_token__map_of__list___main(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_parser_token__map_of__list___rarg(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_token__map_of__list___main___rarg(x_0);
return x_1;
}
}
obj* l_lean_parser_token__map_of__list(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_token__map_of__list___rarg___boxed), 1, 0);
return x_1;
}
}
obj* l_lean_parser_token__map_of__list___rarg___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_token__map_of__list___rarg(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_parser_token__map_of__list___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_token__map_of__list(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_parser_token__map__nil_tokens(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::box(0);
return x_1;
}
}
obj* l_lean_parser_token__map__nil_tokens___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_token__map__nil_tokens(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_lean_parser_token__map__cons_tokens___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = l_lean_parser_tokens___rarg(x_0);
x_3 = l_lean_parser_tokens___rarg(x_1);
x_4 = l_list_append___rarg(x_2, x_3);
return x_4;
}
}
obj* l_lean_parser_token__map__cons_tokens(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_lean_parser_token__map__cons_tokens___rarg___boxed), 2, 0);
return x_4;
}
}
obj* l_lean_parser_token__map__cons_tokens___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_lean_parser_token__map__cons_tokens___rarg(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_lean_parser_token__map__cons_tokens___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_lean_parser_token__map__cons_tokens(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_lean_parser_command__parser__config__coe__parser__config(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
return x_1;
}
}
obj* l_lean_parser_command__parser__config__coe__parser__config___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_lean_parser_command__parser__config__coe__parser__config(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_lean_parser_command__parser() {
_start:
{
obj* x_0; 
x_0 = lean::box(0);
return x_0;
}
}
void initialize_init_lean_parser_parsec();
void initialize_init_lean_parser_syntax();
void initialize_init_lean_parser_rec();
void initialize_init_lean_parser_trie();
void initialize_init_lean_parser_identifier();
void initialize_init_data_rbmap_default();
void initialize_init_lean_message();
void initialize_init_control_coroutine();
static bool _G_initialized = false;
void initialize_init_lean_parser_basic() {
 if (_G_initialized) return;
 _G_initialized = true;
 initialize_init_lean_parser_parsec();
 initialize_init_lean_parser_syntax();
 initialize_init_lean_parser_rec();
 initialize_init_lean_parser_trie();
 initialize_init_lean_parser_identifier();
 initialize_init_data_rbmap_default();
 initialize_init_lean_message();
 initialize_init_control_coroutine();
 l_lean_parser_max__prec = _init_l_lean_parser_max__prec();
lean::mark_persistent(l_lean_parser_max__prec);
 l_lean_parser_parser__core__t = _init_l_lean_parser_parser__core__t();
lean::mark_persistent(l_lean_parser_parser__core__t);
 l_lean_parser_parser__t = _init_l_lean_parser_parser__t();
lean::mark_persistent(l_lean_parser_parser__t);
 l_lean_parser_basic__parser__m_monad = _init_l_lean_parser_basic__parser__m_monad();
lean::mark_persistent(l_lean_parser_basic__parser__m_monad);
 l_lean_parser_basic__parser__m_alternative = _init_l_lean_parser_basic__parser__m_alternative();
lean::mark_persistent(l_lean_parser_basic__parser__m_alternative);
 l_lean_parser_basic__parser__m_monad__reader = _init_l_lean_parser_basic__parser__m_monad__reader();
lean::mark_persistent(l_lean_parser_basic__parser__m_monad__reader);
 l_lean_parser_basic__parser__m_lean_parser_monad__parsec = _init_l_lean_parser_basic__parser__m_lean_parser_monad__parsec();
lean::mark_persistent(l_lean_parser_basic__parser__m_lean_parser_monad__parsec);
 l_lean_parser_basic__parser__m_monad__except = _init_l_lean_parser_basic__parser__m_monad__except();
lean::mark_persistent(l_lean_parser_basic__parser__m_monad__except);
 l_lean_parser_basic__parser__m = _init_l_lean_parser_basic__parser__m();
lean::mark_persistent(l_lean_parser_basic__parser__m);
 l_lean_parser_basic__parser = _init_l_lean_parser_basic__parser();
lean::mark_persistent(l_lean_parser_basic__parser);
 l_lean_parser_monad__basic__parser = _init_l_lean_parser_monad__basic__parser();
lean::mark_persistent(l_lean_parser_monad__basic__parser);
 l_lean_parser_run___rarg___closed__1 = _init_l_lean_parser_run___rarg___closed__1();
lean::mark_persistent(l_lean_parser_run___rarg___closed__1);
 l_list_mfoldl___main___at_lean_parser_mk__token__trie___spec__1___closed__1 = _init_l_list_mfoldl___main___at_lean_parser_mk__token__trie___spec__1___closed__1();
lean::mark_persistent(l_list_mfoldl___main___at_lean_parser_mk__token__trie___spec__1___closed__1);
 l_list_mfoldl___main___at_lean_parser_mk__token__trie___spec__1___closed__2 = _init_l_list_mfoldl___main___at_lean_parser_mk__token__trie___spec__1___closed__2();
lean::mark_persistent(l_list_mfoldl___main___at_lean_parser_mk__token__trie___spec__1___closed__2);
 l_list_mfoldl___main___at_lean_parser_mk__token__trie___spec__1___closed__3 = _init_l_list_mfoldl___main___at_lean_parser_mk__token__trie___spec__1___closed__3();
lean::mark_persistent(l_list_mfoldl___main___at_lean_parser_mk__token__trie___spec__1___closed__3);
 l_lean_parser_mk__token__trie___closed__1 = _init_l_lean_parser_mk__token__trie___closed__1();
lean::mark_persistent(l_lean_parser_mk__token__trie___closed__1);
 l_lean_parser_command__parser__m_monad___closed__1 = _init_l_lean_parser_command__parser__m_monad___closed__1();
lean::mark_persistent(l_lean_parser_command__parser__m_monad___closed__1);
 l_lean_parser_command__parser__m_alternative___closed__1 = _init_l_lean_parser_command__parser__m_alternative___closed__1();
lean::mark_persistent(l_lean_parser_command__parser__m_alternative___closed__1);
 l_lean_parser_command__parser__m_monad__reader___closed__1 = _init_l_lean_parser_command__parser__m_monad__reader___closed__1();
lean::mark_persistent(l_lean_parser_command__parser__m_monad__reader___closed__1);
 l_lean_parser_command__parser__m_lean_parser_monad__parsec___closed__1 = _init_l_lean_parser_command__parser__m_lean_parser_monad__parsec___closed__1();
lean::mark_persistent(l_lean_parser_command__parser__m_lean_parser_monad__parsec___closed__1);
 l_lean_parser_command__parser__m_monad__except___closed__1 = _init_l_lean_parser_command__parser__m_monad__except___closed__1();
lean::mark_persistent(l_lean_parser_command__parser__m_monad__except___closed__1);
 l_lean_parser_command__parser__m_lean_parser_monad__rec___closed__1 = _init_l_lean_parser_command__parser__m_lean_parser_monad__rec___closed__1();
lean::mark_persistent(l_lean_parser_command__parser__m_lean_parser_monad__rec___closed__1);
 l_lean_parser_command__parser__m = _init_l_lean_parser_command__parser__m();
lean::mark_persistent(l_lean_parser_command__parser__m);
 l_lean_parser_command__parser__m_monad__reader__adapter___closed__1 = _init_l_lean_parser_command__parser__m_monad__reader__adapter___closed__1();
lean::mark_persistent(l_lean_parser_command__parser__m_monad__reader__adapter___closed__1);
 l_lean_parser_term__parser__m_monad = _init_l_lean_parser_term__parser__m_monad();
lean::mark_persistent(l_lean_parser_term__parser__m_monad);
 l_lean_parser_term__parser__m_alternative = _init_l_lean_parser_term__parser__m_alternative();
lean::mark_persistent(l_lean_parser_term__parser__m_alternative);
 l_lean_parser_term__parser__m_monad__reader = _init_l_lean_parser_term__parser__m_monad__reader();
lean::mark_persistent(l_lean_parser_term__parser__m_monad__reader);
 l_lean_parser_term__parser__m_lean_parser_monad__parsec = _init_l_lean_parser_term__parser__m_lean_parser_monad__parsec();
lean::mark_persistent(l_lean_parser_term__parser__m_lean_parser_monad__parsec);
 l_lean_parser_term__parser__m_monad__except = _init_l_lean_parser_term__parser__m_monad__except();
lean::mark_persistent(l_lean_parser_term__parser__m_monad__except);
 l_lean_parser_term__parser__m_lean_parser_monad__rec = _init_l_lean_parser_term__parser__m_lean_parser_monad__rec();
lean::mark_persistent(l_lean_parser_term__parser__m_lean_parser_monad__rec);
 l_lean_parser_term__parser__m_lean_parser_monad__basic__parser = _init_l_lean_parser_term__parser__m_lean_parser_monad__basic__parser();
lean::mark_persistent(l_lean_parser_term__parser__m_lean_parser_monad__basic__parser);
 l_lean_parser_term__parser__m = _init_l_lean_parser_term__parser__m();
lean::mark_persistent(l_lean_parser_term__parser__m);
 l_lean_parser_term__parser = _init_l_lean_parser_term__parser();
lean::mark_persistent(l_lean_parser_term__parser);
 l_lean_parser_trailing__term__parser__m_monad = _init_l_lean_parser_trailing__term__parser__m_monad();
lean::mark_persistent(l_lean_parser_trailing__term__parser__m_monad);
 l_lean_parser_trailing__term__parser__m_alternative = _init_l_lean_parser_trailing__term__parser__m_alternative();
lean::mark_persistent(l_lean_parser_trailing__term__parser__m_alternative);
 l_lean_parser_trailing__term__parser__m_monad__reader = _init_l_lean_parser_trailing__term__parser__m_monad__reader();
lean::mark_persistent(l_lean_parser_trailing__term__parser__m_monad__reader);
 l_lean_parser_trailing__term__parser__m_lean_parser_monad__parsec = _init_l_lean_parser_trailing__term__parser__m_lean_parser_monad__parsec();
lean::mark_persistent(l_lean_parser_trailing__term__parser__m_lean_parser_monad__parsec);
 l_lean_parser_trailing__term__parser__m_monad__except = _init_l_lean_parser_trailing__term__parser__m_monad__except();
lean::mark_persistent(l_lean_parser_trailing__term__parser__m_monad__except);
 l_lean_parser_trailing__term__parser__m_lean_parser_monad__rec = _init_l_lean_parser_trailing__term__parser__m_lean_parser_monad__rec();
lean::mark_persistent(l_lean_parser_trailing__term__parser__m_lean_parser_monad__rec);
 l_lean_parser_trailing__term__parser__m_lean_parser_monad__basic__parser = _init_l_lean_parser_trailing__term__parser__m_lean_parser_monad__basic__parser();
lean::mark_persistent(l_lean_parser_trailing__term__parser__m_lean_parser_monad__basic__parser);
 l_lean_parser_trailing__term__parser__m = _init_l_lean_parser_trailing__term__parser__m();
lean::mark_persistent(l_lean_parser_trailing__term__parser__m);
 l_lean_parser_trailing__term__parser = _init_l_lean_parser_trailing__term__parser();
lean::mark_persistent(l_lean_parser_trailing__term__parser);
 l_lean_parser_token__map = _init_l_lean_parser_token__map();
lean::mark_persistent(l_lean_parser_token__map);
 l_lean_parser_command__parser = _init_l_lean_parser_command__parser();
lean::mark_persistent(l_lean_parser_command__parser);
}
