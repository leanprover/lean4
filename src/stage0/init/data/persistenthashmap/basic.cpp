// Lean compiler output
// Module: init.data.persistenthashmap.basic
// Imports: init.data.array.default init.data.hashable
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
obj* l_PersistentHashMap_findAtAux___main___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_PersistentHashMap_isUnaryEntries___main___rarg___boxed(obj*, obj*, obj*);
obj* l_PersistentHashMap_find(obj*, obj*);
obj* l_PersistentHashMap_mfoldlAux___main___at_PersistentHashMap_foldl___spec__2___rarg(obj*, obj*, obj*);
obj* l_PersistentHashMap_mul2Shift___boxed(obj*, obj*);
usize l_USize_mul(usize, usize);
obj* l_PersistentHashMap_find___main___rarg___boxed(obj*, obj*, obj*, obj*);
uint8 l_PersistentHashMap_containsAtAux___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_PersistentHashMap_foldl___spec__4(obj*, obj*, obj*);
obj* l_PersistentHashMap_mfoldl___at_PersistentHashMap_toList___spec__1___rarg___boxed(obj*, obj*);
extern obj* l_Array_empty___closed__1;
namespace lean {
obj* nat_sub(obj*, obj*);
}
usize l_PersistentHashMap_insertAux___main___rarg___closed__1;
obj* l_PersistentHashMap_Stats_toString___closed__3;
obj* l_Array_miterateAux___main___at_PersistentHashMap_mfoldlAux___main___spec__1___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_PersistentHashMap_Stats_toString___closed__4;
obj* l_PersistentHashMap_findAux___main___rarg(obj*, obj*, usize, obj*);
obj* l_Array_mkArray(obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_PersistentHashMap_collectStats___main___spec__1(obj*, obj*);
obj* l_PersistentHashMap_isUnaryEntries___rarg___boxed(obj*, obj*, obj*);
obj* l_PersistentHashMap_insert___main(obj*, obj*);
obj* l_PersistentHashMap_isUnaryEntries(obj*, obj*);
usize l_USize_shift__right(usize, usize);
obj* l_PersistentHashMap_contains(obj*, obj*);
obj* l_PersistentHashMap_findAux___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_PersistentHashMap_insert___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_PersistentHashMap_foldl___spec__3(obj*, obj*, obj*);
obj* l_PersistentHashMap_mfoldlAux___main___at_PersistentHashMap_foldl___spec__2(obj*, obj*, obj*);
obj* l_PersistentHashMap_mfoldl___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_PersistentHashMap_eraseAux___rarg(obj*, obj*, usize, obj*);
obj* l_PersistentHashMap_isEmpty(obj*, obj*);
obj* l_Array_miterateAux___main___at_PersistentHashMap_toList___spec__4___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_PersistentHashMap_toList___spec__3___rarg(obj*, obj*, obj*, obj*);
obj* l_PersistentHashMap_findAtAux___main(obj*, obj*);
obj* l_PersistentHashMap_insertAtCollisionNode(obj*, obj*);
usize l_USize_sub(usize, usize);
obj* l_PersistentHashMap_Stats_toString(obj*);
obj* l_PersistentHashMap_mfoldl___at_PersistentHashMap_foldl___spec__1___rarg___boxed(obj*, obj*, obj*);
obj* l_PersistentHashMap_insertAtCollisionNodeAux(obj*, obj*);
obj* l_PersistentHashMap_isUnaryNode___main___rarg(obj*);
obj* l_PersistentHashMap_toList___rarg___boxed(obj*);
obj* l_PersistentHashMap_findAtAux___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_PersistentHashMap_mkCollisionNode___rarg___closed__1;
obj* l_PersistentHashMap_insert___main___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_PersistentHashMap_mfoldlAux___main___at_PersistentHashMap_toList___spec__2___rarg(obj*, obj*);
obj* l_PersistentHashMap_isUnaryEntries___rarg(obj*, obj*, obj*);
obj* l_PersistentHashMap_getCollisionNodeSize___main(obj*, obj*);
obj* l_PersistentHashMap_mfoldlAux___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_PersistentHashMap_mfoldlAux___main___spec__1___boxed(obj*, obj*, obj*);
obj* l_PersistentHashMap_containsAtAux___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_PersistentHashMap_mfoldl___at_PersistentHashMap_foldl___spec__1(obj*, obj*, obj*);
obj* l_PersistentHashMap_toList(obj*, obj*);
obj* l_PersistentHashMap_getCollisionNodeSize(obj*, obj*);
obj* l_PersistentHashMap_findAtAux(obj*, obj*);
obj* l_PersistentHashMap_getCollisionNodeSize___rarg(obj*);
obj* l_Array_miterateAux___main___at_PersistentHashMap_insertAux___main___spec__1___rarg(obj*, obj*, usize, obj*, obj*, obj*, obj*, obj*);
obj* l_PersistentHashMap_contains___main___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_PersistentHashMap_containsAux(obj*, obj*);
usize l_PersistentHashMap_mod2Shift(usize, usize);
obj* l_Array_mkEmpty(obj*, obj*);
obj* l_Array_miterateAux___main___at_PersistentHashMap_collectStats___main___spec__1___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_PersistentHashMap_stats___rarg(obj*);
obj* l_Array_miterateAux___main___at_PersistentHashMap_mfoldlAux___main___spec__1___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_PersistentHashMap_mkEmptyEntries(obj*, obj*);
obj* l_PersistentHashMap_maxCollisions;
obj* l_Array_miterateAux___main___at_PersistentHashMap_foldl___spec__3___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_PersistentHashMap_containsAux___main___rarg(obj*, obj*, usize, obj*);
obj* l_Array_miterateAux___main___at_PersistentHashMap_toList___spec__4___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_PersistentHashMap_collectStats___main___rarg___boxed(obj*, obj*, obj*);
obj* l_PersistentHashMap_find___main(obj*, obj*);
obj* l_PersistentHashMap_toList___rarg(obj*);
obj* l_Nat_repr(obj*);
obj* l_PersistentHashMap_mkCollisionNode___rarg(obj*, obj*, obj*, obj*);
obj* l_PersistentHashMap_insertAtCollisionNodeAux___main(obj*, obj*);
obj* l_PersistentHashMap_findAux___rarg(obj*, obj*, usize, obj*);
obj* l_PersistentHashMap_mfoldlAux___main___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_PersistentHashMap_insertAux___main___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_PersistentHashMap_mod2Shift___boxed(obj*, obj*);
obj* l_Array_miterateAux___main___at_PersistentHashMap_insertAux___main___spec__1___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_PersistentHashMap_containsAux___rarg(obj*, obj*, usize, obj*);
obj* l_PersistentHashMap_contains___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_PersistentHashMap_foldl___rarg___boxed(obj*, obj*, obj*);
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_PersistentHashMap_isUnaryEntries___main(obj*, obj*);
obj* l_PersistentHashMap_insertAtCollisionNodeAux___main___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_PersistentHashMap_insertAux___main___spec__1(obj*, obj*);
usize l_USize_add(usize, usize);
obj* l_PersistentHashMap_Stats_toString___closed__5;
obj* l_PersistentHashMap_containsAtAux___main___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_PersistentHashMap_findAtAux___main___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_PersistentHashMap_foldl(obj*, obj*, obj*);
obj* l_PersistentHashMap_mfoldlAux___boxed(obj*, obj*, obj*);
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
obj* l_PersistentHashMap_mfoldl___at_PersistentHashMap_toList___spec__1(obj*, obj*);
obj* l_PersistentHashMap_isUnaryNode___rarg___boxed(obj*);
obj* l_Array_miterateAux___main___at_PersistentHashMap_mfoldlAux___main___spec__2___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_PersistentHashMap_mfoldlAux___main___spec__2(obj*, obj*, obj*);
obj* l_PersistentHashMap_div2Shift___boxed(obj*, obj*);
obj* l_PersistentHashMap_empty___closed__3;
obj* l_PersistentHashMap_stats___rarg___closed__1;
obj* l_Array_fget(obj*, obj*, obj*);
obj* l_PersistentHashMap_containsAux___main(obj*, obj*);
obj* l_PersistentHashMap_isUnaryEntries___main___rarg(obj*, obj*, obj*);
obj* l_PersistentHashMap_mkEmptyEntriesArray___closed__1;
namespace lean {
obj* nat_add(obj*, obj*);
}
obj* l_PersistentHashMap_foldl___rarg(obj*, obj*, obj*);
obj* l_PersistentHashMap_collectStats___rarg(obj*, obj*, obj*);
obj* l_PersistentHashMap_Stats_toString___closed__1;
obj* l_Array_miterateAux___main___at_PersistentHashMap_mfoldlAux___main___spec__1(obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_PersistentHashMap_mfoldlAux___main___spec__2___boxed(obj*, obj*, obj*);
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l_Array_miterateAux___main___at_PersistentHashMap_toList___spec__3___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_PersistentHashMap_isEmpty___rarg___boxed(obj*);
obj* l_PersistentHashMap_insertAux___main___rarg(obj*, obj*, obj*, usize, usize, obj*, obj*);
obj* l_Array_push(obj*, obj*, obj*);
obj* l_Array_indexOfAux___main___rarg(obj*, obj*, obj*, obj*);
obj* l_PersistentHashMap_insertAux___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_PersistentHashMap_empty___closed__2;
obj* l_Array_miterateAux___main___at_PersistentHashMap_toList___spec__3(obj*, obj*);
obj* l_PersistentHashMap_HasToString;
usize l_PersistentHashMap_shift;
usize l_PersistentHashMap_insertAux___main___rarg___closed__2;
obj* l_PersistentHashMap_mfoldlAux___main___at_PersistentHashMap_foldl___spec__2___rarg___boxed(obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_PersistentHashMap_mfoldlAux___main___spec__2___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_PersistentHashMap_stats(obj*, obj*);
obj* l_PersistentHashMap_isUnaryNode___main(obj*, obj*);
obj* l_PersistentHashMap_eraseAux___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_PersistentHashMap_contains___main___rarg(obj*, obj*, obj*, obj*);
obj* l_PersistentHashMap_Node_inhabited(obj*, obj*);
obj* l_PersistentHashMap_eraseAux___main___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_PersistentHashMap_Node_inhabited___closed__1;
usize l_PersistentHashMap_maxDepth;
obj* l_PersistentHashMap_mfoldl(obj*, obj*, obj*);
obj* l_PersistentHashMap_stats___rarg___boxed(obj*);
obj* l_PersistentHashMap_insertAux___rarg(obj*, obj*, obj*, usize, usize, obj*, obj*);
obj* l_Array_miterateAux___main___at_PersistentHashMap_toList___spec__4(obj*, obj*);
obj* l_PersistentHashMap_erase___main(obj*, obj*);
obj* l_PersistentHashMap_contains___main(obj*, obj*);
obj* l_PersistentHashMap_mfoldl___at_PersistentHashMap_toList___spec__1___rarg(obj*, obj*);
obj* l_PersistentHashMap_find___rarg(obj*, obj*, obj*, obj*);
obj* l_PersistentHashMap_getCollisionNodeSize___main___rarg___boxed(obj*);
obj* l_PersistentHashMap_HasToString___closed__1;
obj* l_PersistentHashMap_collectStats(obj*, obj*);
obj* l_PersistentHashMap_mfoldlAux(obj*, obj*, obj*);
obj* l_PersistentHashMap_containsAtAux___main(obj*);
obj* l_Array_miterateAux___main___at_PersistentHashMap_foldl___spec__4___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_PersistentHashMap_Entry_inhabited(obj*, obj*, obj*);
obj* l_PersistentHashMap_insertAux___main___rarg___closed__3;
obj* l_Array_size(obj*, obj*);
obj* l_Array_eraseIdx_x27___rarg(obj*, obj*);
obj* l_PersistentHashMap_mfoldlAux___main___at_PersistentHashMap_toList___spec__2(obj*, obj*);
obj* l_PersistentHashMap_Stats_toString___closed__2;
obj* l_PersistentHashMap_isUnaryNode___rarg(obj*);
obj* l_PersistentHashMap_find___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_Array_fset(obj*, obj*, obj*, obj*);
obj* l_Array_get(obj*, obj*, obj*, obj*);
obj* l_PersistentHashMap_mkEmptyEntriesArray(obj*, obj*);
obj* l_PersistentHashMap_mfoldl___at_PersistentHashMap_foldl___spec__1___rarg(obj*, obj*, obj*);
obj* l_PersistentHashMap_getCollisionNodeSize___rarg___boxed(obj*);
obj* l_PersistentHashMap_empty___closed__1;
obj* l_PersistentHashMap_collectStats___main___rarg(obj*, obj*, obj*);
obj* l_PersistentHashMap_findAtAux___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_PersistentHashMap_getCollisionNodeSize___main___rarg(obj*);
obj* l_PersistentHashMap_mfoldlAux___main(obj*, obj*, obj*);
obj* l_PersistentHashMap_empty(obj*, obj*);
obj* l_PersistentHashMap_isUnaryNode(obj*, obj*);
obj* l_PersistentHashMap_insertAtCollisionNode___rarg(obj*, obj*, obj*, obj*);
obj* l_PersistentHashMap_containsAux___main___rarg___boxed(obj*, obj*, obj*, obj*);
uint8 l_USize_decLe(usize, usize);
obj* l_PersistentHashMap_insertAux___main(obj*, obj*);
obj* l_PersistentHashMap_eraseAux___main(obj*, obj*);
obj* l_PersistentHashMap_contains___rarg(obj*, obj*, obj*, obj*);
obj* l_PersistentHashMap_mfoldlAux___main___at_PersistentHashMap_toList___spec__2___rarg___boxed(obj*, obj*);
obj* l_PersistentHashMap_insert(obj*, obj*);
obj* l_PersistentHashMap_find___main___rarg(obj*, obj*, obj*, obj*);
usize l_USize_shift__left(usize, usize);
obj* l_PersistentHashMap_collectStats___main(obj*, obj*);
obj* l_PersistentHashMap_erase___rarg(obj*, obj*, obj*, obj*);
obj* l_Array_set(obj*, obj*, obj*, obj*);
obj* l_PersistentHashMap_Inhabited(obj*, obj*);
obj* l_Array_miterateAux___main___at_PersistentHashMap_foldl___spec__4___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_PersistentHashMap_containsAtAux(obj*, obj*);
usize l_USize_land(usize, usize);
usize l_PersistentHashMap_mul2Shift(usize, usize);
usize l_PersistentHashMap_div2Shift(usize, usize);
obj* l_PersistentHashMap_insertAtCollisionNodeAux___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Nat_max(obj*, obj*);
obj* l_PersistentHashMap_erase___main___rarg(obj*, obj*, obj*, obj*);
namespace lean {
obj* usize_to_nat(usize);
}
obj* l_PersistentHashMap_mfoldlAux___main___boxed(obj*, obj*, obj*);
obj* l_PersistentHashMap_findAux___main___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_PersistentHashMap_mkCollisionNode(obj*, obj*);
obj* l_PersistentHashMap_insertAux(obj*, obj*);
obj* l_PersistentHashMap_isUnaryNode___main___rarg___boxed(obj*);
uint8 l_PersistentHashMap_isEmpty___rarg(obj*);
uint8 l_PersistentHashMap_containsAtAux___main___rarg(obj*, obj*, obj*, obj*);
obj* l_PersistentHashMap_findAux(obj*, obj*);
obj* l_PersistentHashMap_mfoldl___boxed(obj*, obj*, obj*);
obj* l_PersistentHashMap_collectStats___rarg___boxed(obj*, obj*, obj*);
obj* l_PersistentHashMap_containsAux___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_PersistentHashMap_erase(obj*, obj*);
usize l_PersistentHashMap_branching;
obj* l_PersistentHashMap_eraseAux(obj*, obj*);
obj* l_Array_miterateAux___main___at_PersistentHashMap_collectStats___main___spec__1___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_PersistentHashMap_findAux___main(obj*, obj*);
obj* l_Array_miterateAux___main___at_PersistentHashMap_foldl___spec__3___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_PersistentHashMap_eraseAux___main___rarg(obj*, obj*, usize, obj*);
obj* l_PersistentHashMap_Entry_inhabited(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::box(2);
return x_4;
}
}
obj* _init_l_PersistentHashMap_Node_inhabited___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Array_empty___closed__1;
x_2 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_PersistentHashMap_Node_inhabited(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_PersistentHashMap_Node_inhabited___closed__1;
return x_3;
}
}
usize _init_l_PersistentHashMap_shift() {
_start:
{
usize x_1; 
x_1 = 5;
return x_1;
}
}
usize _init_l_PersistentHashMap_branching() {
_start:
{
usize x_1; 
x_1 = 32;
return x_1;
}
}
usize _init_l_PersistentHashMap_maxDepth() {
_start:
{
usize x_1; 
x_1 = 7;
return x_1;
}
}
obj* _init_l_PersistentHashMap_maxCollisions() {
_start:
{
obj* x_1; 
x_1 = lean::mk_nat_obj(4u);
return x_1;
}
}
obj* _init_l_PersistentHashMap_mkEmptyEntriesArray___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(2);
x_2 = lean::mk_nat_obj(32u);
x_3 = lean::mk_array(x_2, x_1);
return x_3;
}
}
obj* l_PersistentHashMap_mkEmptyEntriesArray(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_PersistentHashMap_mkEmptyEntriesArray___closed__1;
return x_3;
}
}
obj* _init_l_PersistentHashMap_empty___closed__1() {
_start:
{
obj* x_1; 
x_1 = l_PersistentHashMap_mkEmptyEntriesArray(lean::box(0), lean::box(0));
return x_1;
}
}
obj* _init_l_PersistentHashMap_empty___closed__2() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_PersistentHashMap_empty___closed__1;
x_2 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_PersistentHashMap_empty___closed__3() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_PersistentHashMap_empty___closed__2;
x_2 = lean::mk_nat_obj(0u);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* l_PersistentHashMap_empty(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_PersistentHashMap_empty___closed__3;
return x_3;
}
}
uint8 l_PersistentHashMap_isEmpty___rarg(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; uint8 x_4; 
x_2 = lean::cnstr_get(x_1, 1);
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_2, x_3);
return x_4;
}
}
obj* l_PersistentHashMap_isEmpty(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentHashMap_isEmpty___rarg___boxed), 1, 0);
return x_3;
}
}
obj* l_PersistentHashMap_isEmpty___rarg___boxed(obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_PersistentHashMap_isEmpty___rarg(x_1);
lean::dec(x_1);
x_3 = lean::box(x_2);
return x_3;
}
}
obj* l_PersistentHashMap_Inhabited(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_PersistentHashMap_empty___closed__3;
return x_3;
}
}
obj* l_PersistentHashMap_mkEmptyEntries(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_PersistentHashMap_empty___closed__2;
return x_3;
}
}
usize l_PersistentHashMap_mul2Shift(usize x_1, usize x_2) {
_start:
{
usize x_3; 
x_3 = x_1 << x_2;
return x_3;
}
}
obj* l_PersistentHashMap_mul2Shift___boxed(obj* x_1, obj* x_2) {
_start:
{
usize x_3; usize x_4; usize x_5; obj* x_6; 
x_3 = lean::unbox_size_t(x_1);
lean::dec(x_1);
x_4 = lean::unbox_size_t(x_2);
lean::dec(x_2);
x_5 = l_PersistentHashMap_mul2Shift(x_3, x_4);
x_6 = lean::box_size_t(x_5);
return x_6;
}
}
usize l_PersistentHashMap_div2Shift(usize x_1, usize x_2) {
_start:
{
usize x_3; 
x_3 = x_1 >> x_2;
return x_3;
}
}
obj* l_PersistentHashMap_div2Shift___boxed(obj* x_1, obj* x_2) {
_start:
{
usize x_3; usize x_4; usize x_5; obj* x_6; 
x_3 = lean::unbox_size_t(x_1);
lean::dec(x_1);
x_4 = lean::unbox_size_t(x_2);
lean::dec(x_2);
x_5 = l_PersistentHashMap_div2Shift(x_3, x_4);
x_6 = lean::box_size_t(x_5);
return x_6;
}
}
usize l_PersistentHashMap_mod2Shift(usize x_1, usize x_2) {
_start:
{
usize x_3; usize x_4; usize x_5; usize x_6; 
x_3 = 1;
x_4 = x_3 << x_2;
x_5 = x_4 - x_3;
x_6 = x_1 & x_5;
return x_6;
}
}
obj* l_PersistentHashMap_mod2Shift___boxed(obj* x_1, obj* x_2) {
_start:
{
usize x_3; usize x_4; usize x_5; obj* x_6; 
x_3 = lean::unbox_size_t(x_1);
lean::dec(x_1);
x_4 = lean::unbox_size_t(x_2);
lean::dec(x_2);
x_5 = l_PersistentHashMap_mod2Shift(x_3, x_4);
x_6 = lean::box_size_t(x_5);
return x_6;
}
}
obj* l_PersistentHashMap_insertAtCollisionNodeAux___main___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; uint8 x_9; 
x_6 = lean::cnstr_get(x_2, 0);
lean::inc(x_6);
x_7 = lean::cnstr_get(x_2, 1);
lean::inc(x_7);
x_8 = lean::array_get_size(x_6);
x_9 = lean::nat_dec_lt(x_3, x_8);
lean::dec(x_8);
if (x_9 == 0)
{
uint8 x_10; 
lean::dec(x_3);
lean::dec(x_1);
x_10 = !lean::is_exclusive(x_2);
if (x_10 == 0)
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_11 = lean::cnstr_get(x_2, 1);
lean::dec(x_11);
x_12 = lean::cnstr_get(x_2, 0);
lean::dec(x_12);
x_13 = lean::array_push(x_6, x_4);
x_14 = lean::array_push(x_7, x_5);
lean::cnstr_set(x_2, 1, x_14);
lean::cnstr_set(x_2, 0, x_13);
return x_2;
}
else
{
obj* x_15; obj* x_16; obj* x_17; 
lean::dec(x_2);
x_15 = lean::array_push(x_6, x_4);
x_16 = lean::array_push(x_7, x_5);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_16);
return x_17;
}
}
else
{
obj* x_18; obj* x_19; uint8 x_20; 
x_18 = lean::array_fget(x_6, x_3);
lean::inc(x_1);
lean::inc(x_4);
x_19 = lean::apply_2(x_1, x_4, x_18);
x_20 = lean::unbox(x_19);
lean::dec(x_19);
if (x_20 == 0)
{
obj* x_21; obj* x_22; 
lean::dec(x_7);
lean::dec(x_6);
x_21 = lean::mk_nat_obj(1u);
x_22 = lean::nat_add(x_3, x_21);
lean::dec(x_3);
x_3 = x_22;
goto _start;
}
else
{
uint8 x_24; 
lean::dec(x_1);
x_24 = !lean::is_exclusive(x_2);
if (x_24 == 0)
{
obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
x_25 = lean::cnstr_get(x_2, 1);
lean::dec(x_25);
x_26 = lean::cnstr_get(x_2, 0);
lean::dec(x_26);
x_27 = lean::array_fset(x_6, x_3, x_4);
x_28 = lean::array_fset(x_7, x_3, x_5);
lean::dec(x_3);
lean::cnstr_set(x_2, 1, x_28);
lean::cnstr_set(x_2, 0, x_27);
return x_2;
}
else
{
obj* x_29; obj* x_30; obj* x_31; 
lean::dec(x_2);
x_29 = lean::array_fset(x_6, x_3, x_4);
x_30 = lean::array_fset(x_7, x_3, x_5);
lean::dec(x_3);
x_31 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_31, 0, x_29);
lean::cnstr_set(x_31, 1, x_30);
return x_31;
}
}
}
}
}
obj* l_PersistentHashMap_insertAtCollisionNodeAux___main(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentHashMap_insertAtCollisionNodeAux___main___rarg), 5, 0);
return x_3;
}
}
obj* l_PersistentHashMap_insertAtCollisionNodeAux___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_PersistentHashMap_insertAtCollisionNodeAux___main___rarg(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
obj* l_PersistentHashMap_insertAtCollisionNodeAux(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentHashMap_insertAtCollisionNodeAux___rarg), 5, 0);
return x_3;
}
}
obj* l_PersistentHashMap_insertAtCollisionNode___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; 
x_5 = lean::mk_nat_obj(0u);
x_6 = l_PersistentHashMap_insertAtCollisionNodeAux___main___rarg(x_1, x_2, x_5, x_3, x_4);
return x_6;
}
}
obj* l_PersistentHashMap_insertAtCollisionNode(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentHashMap_insertAtCollisionNode___rarg), 4, 0);
return x_3;
}
}
obj* l_PersistentHashMap_getCollisionNodeSize___main___rarg(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::cnstr_get(x_1, 0);
x_3 = lean::array_get_size(x_2);
return x_3;
}
}
obj* l_PersistentHashMap_getCollisionNodeSize___main(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentHashMap_getCollisionNodeSize___main___rarg___boxed), 1, 0);
return x_3;
}
}
obj* l_PersistentHashMap_getCollisionNodeSize___main___rarg___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_PersistentHashMap_getCollisionNodeSize___main___rarg(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_PersistentHashMap_getCollisionNodeSize___rarg(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_PersistentHashMap_getCollisionNodeSize___main___rarg(x_1);
return x_2;
}
}
obj* l_PersistentHashMap_getCollisionNodeSize(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentHashMap_getCollisionNodeSize___rarg___boxed), 1, 0);
return x_3;
}
}
obj* l_PersistentHashMap_getCollisionNodeSize___rarg___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_PersistentHashMap_getCollisionNodeSize___rarg(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_PersistentHashMap_mkCollisionNode___rarg___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_nat_obj(4u);
x_2 = lean::mk_empty_array(x_1);
return x_2;
}
}
obj* l_PersistentHashMap_mkCollisionNode___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_5 = l_PersistentHashMap_mkCollisionNode___rarg___closed__1;
x_6 = lean::array_push(x_5, x_1);
x_7 = lean::array_push(x_6, x_3);
x_8 = lean::array_push(x_5, x_2);
x_9 = lean::array_push(x_8, x_4);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_7);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
}
}
obj* l_PersistentHashMap_mkCollisionNode(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentHashMap_mkCollisionNode___rarg), 4, 0);
return x_3;
}
}
obj* l_Array_miterateAux___main___at_PersistentHashMap_insertAux___main___spec__1___rarg(obj* x_1, obj* x_2, usize x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
obj* x_9; uint8 x_10; 
x_9 = lean::array_get_size(x_6);
x_10 = lean::nat_dec_lt(x_7, x_9);
lean::dec(x_9);
if (x_10 == 0)
{
lean::dec(x_7);
lean::dec(x_2);
lean::dec(x_1);
return x_8;
}
else
{
obj* x_11; usize x_12; usize x_13; usize x_14; usize x_15; obj* x_16; usize x_17; usize x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_11 = lean::array_fget(x_6, x_7);
x_12 = 1;
x_13 = x_3 - x_12;
x_14 = 5;
x_15 = x_14 * x_13;
lean::inc(x_2);
lean::inc(x_11);
x_16 = lean::apply_1(x_2, x_11);
x_17 = lean::unbox_size_t(x_16);
lean::dec(x_16);
x_18 = x_17 >> x_15;
x_19 = lean::array_fget(x_5, x_7);
lean::inc(x_2);
lean::inc(x_1);
x_20 = l_PersistentHashMap_insertAux___main___rarg(x_1, x_2, x_8, x_18, x_3, x_11, x_19);
x_21 = lean::mk_nat_obj(1u);
x_22 = lean::nat_add(x_7, x_21);
lean::dec(x_7);
x_7 = x_22;
x_8 = x_20;
goto _start;
}
}
}
obj* l_Array_miterateAux___main___at_PersistentHashMap_insertAux___main___spec__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at_PersistentHashMap_insertAux___main___spec__1___rarg___boxed), 8, 0);
return x_3;
}
}
usize _init_l_PersistentHashMap_insertAux___main___rarg___closed__1() {
_start:
{
usize x_1; usize x_2; usize x_3; 
x_1 = 1;
x_2 = 5;
x_3 = x_1 << x_2;
return x_3;
}
}
usize _init_l_PersistentHashMap_insertAux___main___rarg___closed__2() {
_start:
{
usize x_1; usize x_2; usize x_3; 
x_1 = 1;
x_2 = l_PersistentHashMap_insertAux___main___rarg___closed__1;
x_3 = x_2 - x_1;
return x_3;
}
}
obj* _init_l_PersistentHashMap_insertAux___main___rarg___closed__3() {
_start:
{
obj* x_1; 
x_1 = l_PersistentHashMap_mkEmptyEntries(lean::box(0), lean::box(0));
return x_1;
}
}
obj* l_PersistentHashMap_insertAux___main___rarg(obj* x_1, obj* x_2, obj* x_3, usize x_4, usize x_5, obj* x_6, obj* x_7) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
uint8 x_8; 
x_8 = !lean::is_exclusive(x_3);
if (x_8 == 0)
{
obj* x_9; usize x_10; usize x_11; usize x_12; usize x_13; obj* x_14; obj* x_15; uint8 x_16; 
x_9 = lean::cnstr_get(x_3, 0);
x_10 = 1;
x_11 = 5;
x_12 = l_PersistentHashMap_insertAux___main___rarg___closed__2;
x_13 = x_4 & x_12;
x_14 = lean::usize_to_nat(x_13);
x_15 = lean::array_get_size(x_9);
x_16 = lean::nat_dec_lt(x_14, x_15);
lean::dec(x_15);
if (x_16 == 0)
{
lean::dec(x_14);
lean::dec(x_7);
lean::dec(x_6);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
else
{
obj* x_17; obj* x_18; obj* x_19; 
x_17 = lean::array_fget(x_9, x_14);
x_18 = lean::box(2);
x_19 = lean::array_fset(x_9, x_14, x_18);
switch (lean::obj_tag(x_17)) {
case 0:
{
uint8 x_20; 
lean::dec(x_2);
x_20 = !lean::is_exclusive(x_17);
if (x_20 == 0)
{
obj* x_21; obj* x_22; obj* x_23; uint8 x_24; 
x_21 = lean::cnstr_get(x_17, 0);
x_22 = lean::cnstr_get(x_17, 1);
lean::inc(x_21);
lean::inc(x_6);
x_23 = lean::apply_2(x_1, x_6, x_21);
x_24 = lean::unbox(x_23);
lean::dec(x_23);
if (x_24 == 0)
{
obj* x_25; obj* x_26; obj* x_27; 
lean::free_heap_obj(x_17);
x_25 = l_PersistentHashMap_mkCollisionNode___rarg(x_21, x_22, x_6, x_7);
x_26 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_26, 0, x_25);
x_27 = lean::array_fset(x_19, x_14, x_26);
lean::dec(x_14);
lean::cnstr_set(x_3, 0, x_27);
return x_3;
}
else
{
obj* x_28; 
lean::dec(x_22);
lean::dec(x_21);
lean::cnstr_set(x_17, 1, x_7);
lean::cnstr_set(x_17, 0, x_6);
x_28 = lean::array_fset(x_19, x_14, x_17);
lean::dec(x_14);
lean::cnstr_set(x_3, 0, x_28);
return x_3;
}
}
else
{
obj* x_29; obj* x_30; obj* x_31; uint8 x_32; 
x_29 = lean::cnstr_get(x_17, 0);
x_30 = lean::cnstr_get(x_17, 1);
lean::inc(x_30);
lean::inc(x_29);
lean::dec(x_17);
lean::inc(x_29);
lean::inc(x_6);
x_31 = lean::apply_2(x_1, x_6, x_29);
x_32 = lean::unbox(x_31);
lean::dec(x_31);
if (x_32 == 0)
{
obj* x_33; obj* x_34; obj* x_35; 
x_33 = l_PersistentHashMap_mkCollisionNode___rarg(x_29, x_30, x_6, x_7);
x_34 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_34, 0, x_33);
x_35 = lean::array_fset(x_19, x_14, x_34);
lean::dec(x_14);
lean::cnstr_set(x_3, 0, x_35);
return x_3;
}
else
{
obj* x_36; obj* x_37; 
lean::dec(x_30);
lean::dec(x_29);
x_36 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_36, 0, x_6);
lean::cnstr_set(x_36, 1, x_7);
x_37 = lean::array_fset(x_19, x_14, x_36);
lean::dec(x_14);
lean::cnstr_set(x_3, 0, x_37);
return x_3;
}
}
}
case 1:
{
uint8 x_38; 
x_38 = !lean::is_exclusive(x_17);
if (x_38 == 0)
{
obj* x_39; usize x_40; usize x_41; obj* x_42; obj* x_43; 
x_39 = lean::cnstr_get(x_17, 0);
x_40 = x_4 >> x_11;
x_41 = x_5 + x_10;
x_42 = l_PersistentHashMap_insertAux___main___rarg(x_1, x_2, x_39, x_40, x_41, x_6, x_7);
lean::cnstr_set(x_17, 0, x_42);
x_43 = lean::array_fset(x_19, x_14, x_17);
lean::dec(x_14);
lean::cnstr_set(x_3, 0, x_43);
return x_3;
}
else
{
obj* x_44; usize x_45; usize x_46; obj* x_47; obj* x_48; obj* x_49; 
x_44 = lean::cnstr_get(x_17, 0);
lean::inc(x_44);
lean::dec(x_17);
x_45 = x_4 >> x_11;
x_46 = x_5 + x_10;
x_47 = l_PersistentHashMap_insertAux___main___rarg(x_1, x_2, x_44, x_45, x_46, x_6, x_7);
x_48 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_48, 0, x_47);
x_49 = lean::array_fset(x_19, x_14, x_48);
lean::dec(x_14);
lean::cnstr_set(x_3, 0, x_49);
return x_3;
}
}
default: 
{
obj* x_50; obj* x_51; 
lean::dec(x_2);
lean::dec(x_1);
x_50 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_50, 0, x_6);
lean::cnstr_set(x_50, 1, x_7);
x_51 = lean::array_fset(x_19, x_14, x_50);
lean::dec(x_14);
lean::cnstr_set(x_3, 0, x_51);
return x_3;
}
}
}
}
else
{
obj* x_52; usize x_53; usize x_54; usize x_55; usize x_56; obj* x_57; obj* x_58; uint8 x_59; 
x_52 = lean::cnstr_get(x_3, 0);
lean::inc(x_52);
lean::dec(x_3);
x_53 = 1;
x_54 = 5;
x_55 = l_PersistentHashMap_insertAux___main___rarg___closed__2;
x_56 = x_4 & x_55;
x_57 = lean::usize_to_nat(x_56);
x_58 = lean::array_get_size(x_52);
x_59 = lean::nat_dec_lt(x_57, x_58);
lean::dec(x_58);
if (x_59 == 0)
{
obj* x_60; 
lean::dec(x_57);
lean::dec(x_7);
lean::dec(x_6);
lean::dec(x_2);
lean::dec(x_1);
x_60 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_60, 0, x_52);
return x_60;
}
else
{
obj* x_61; obj* x_62; obj* x_63; 
x_61 = lean::array_fget(x_52, x_57);
x_62 = lean::box(2);
x_63 = lean::array_fset(x_52, x_57, x_62);
switch (lean::obj_tag(x_61)) {
case 0:
{
obj* x_64; obj* x_65; obj* x_66; obj* x_67; uint8 x_68; 
lean::dec(x_2);
x_64 = lean::cnstr_get(x_61, 0);
lean::inc(x_64);
x_65 = lean::cnstr_get(x_61, 1);
lean::inc(x_65);
if (lean::is_exclusive(x_61)) {
 lean::cnstr_release(x_61, 0);
 lean::cnstr_release(x_61, 1);
 x_66 = x_61;
} else {
 lean::dec_ref(x_61);
 x_66 = lean::box(0);
}
lean::inc(x_64);
lean::inc(x_6);
x_67 = lean::apply_2(x_1, x_6, x_64);
x_68 = lean::unbox(x_67);
lean::dec(x_67);
if (x_68 == 0)
{
obj* x_69; obj* x_70; obj* x_71; obj* x_72; 
lean::dec(x_66);
x_69 = l_PersistentHashMap_mkCollisionNode___rarg(x_64, x_65, x_6, x_7);
x_70 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_70, 0, x_69);
x_71 = lean::array_fset(x_63, x_57, x_70);
lean::dec(x_57);
x_72 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_72, 0, x_71);
return x_72;
}
else
{
obj* x_73; obj* x_74; obj* x_75; 
lean::dec(x_65);
lean::dec(x_64);
if (lean::is_scalar(x_66)) {
 x_73 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_73 = x_66;
}
lean::cnstr_set(x_73, 0, x_6);
lean::cnstr_set(x_73, 1, x_7);
x_74 = lean::array_fset(x_63, x_57, x_73);
lean::dec(x_57);
x_75 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_75, 0, x_74);
return x_75;
}
}
case 1:
{
obj* x_76; obj* x_77; usize x_78; usize x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; 
x_76 = lean::cnstr_get(x_61, 0);
lean::inc(x_76);
if (lean::is_exclusive(x_61)) {
 lean::cnstr_release(x_61, 0);
 x_77 = x_61;
} else {
 lean::dec_ref(x_61);
 x_77 = lean::box(0);
}
x_78 = x_4 >> x_54;
x_79 = x_5 + x_53;
x_80 = l_PersistentHashMap_insertAux___main___rarg(x_1, x_2, x_76, x_78, x_79, x_6, x_7);
if (lean::is_scalar(x_77)) {
 x_81 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_81 = x_77;
}
lean::cnstr_set(x_81, 0, x_80);
x_82 = lean::array_fset(x_63, x_57, x_81);
lean::dec(x_57);
x_83 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_83, 0, x_82);
return x_83;
}
default: 
{
obj* x_84; obj* x_85; obj* x_86; 
lean::dec(x_2);
lean::dec(x_1);
x_84 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_84, 0, x_6);
lean::cnstr_set(x_84, 1, x_7);
x_85 = lean::array_fset(x_63, x_57, x_84);
lean::dec(x_57);
x_86 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_86, 0, x_85);
return x_86;
}
}
}
}
}
else
{
obj* x_87; obj* x_88; usize x_89; uint8 x_90; 
x_87 = lean::mk_nat_obj(0u);
lean::inc(x_1);
x_88 = l_PersistentHashMap_insertAtCollisionNodeAux___main___rarg(x_1, x_3, x_87, x_6, x_7);
x_89 = 7;
x_90 = x_89 <= x_5;
if (x_90 == 0)
{
obj* x_91; obj* x_92; uint8 x_93; 
x_91 = l_PersistentHashMap_getCollisionNodeSize___main___rarg(x_88);
x_92 = lean::mk_nat_obj(4u);
x_93 = lean::nat_dec_lt(x_91, x_92);
lean::dec(x_91);
if (x_93 == 0)
{
obj* x_94; obj* x_95; obj* x_96; obj* x_97; 
x_94 = lean::cnstr_get(x_88, 0);
lean::inc(x_94);
x_95 = lean::cnstr_get(x_88, 1);
lean::inc(x_95);
lean::dec(x_88);
x_96 = l_PersistentHashMap_insertAux___main___rarg___closed__3;
x_97 = l_Array_miterateAux___main___at_PersistentHashMap_insertAux___main___spec__1___rarg(x_1, x_2, x_5, x_94, x_95, x_94, x_87, x_96);
lean::dec(x_95);
lean::dec(x_94);
return x_97;
}
else
{
lean::dec(x_2);
lean::dec(x_1);
return x_88;
}
}
else
{
lean::dec(x_2);
lean::dec(x_1);
return x_88;
}
}
}
}
obj* l_PersistentHashMap_insertAux___main(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentHashMap_insertAux___main___rarg___boxed), 7, 0);
return x_3;
}
}
obj* l_Array_miterateAux___main___at_PersistentHashMap_insertAux___main___spec__1___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
usize x_9; obj* x_10; 
x_9 = lean::unbox_size_t(x_3);
lean::dec(x_3);
x_10 = l_Array_miterateAux___main___at_PersistentHashMap_insertAux___main___spec__1___rarg(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_4);
return x_10;
}
}
obj* l_PersistentHashMap_insertAux___main___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
usize x_8; usize x_9; obj* x_10; 
x_8 = lean::unbox_size_t(x_4);
lean::dec(x_4);
x_9 = lean::unbox_size_t(x_5);
lean::dec(x_5);
x_10 = l_PersistentHashMap_insertAux___main___rarg(x_1, x_2, x_3, x_8, x_9, x_6, x_7);
return x_10;
}
}
obj* l_PersistentHashMap_insertAux___rarg(obj* x_1, obj* x_2, obj* x_3, usize x_4, usize x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = l_PersistentHashMap_insertAux___main___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
obj* l_PersistentHashMap_insertAux(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentHashMap_insertAux___rarg___boxed), 7, 0);
return x_3;
}
}
obj* l_PersistentHashMap_insertAux___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
usize x_8; usize x_9; obj* x_10; 
x_8 = lean::unbox_size_t(x_4);
lean::dec(x_4);
x_9 = lean::unbox_size_t(x_5);
lean::dec(x_5);
x_10 = l_PersistentHashMap_insertAux___rarg(x_1, x_2, x_3, x_8, x_9, x_6, x_7);
return x_10;
}
}
obj* l_PersistentHashMap_insert___main___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; 
x_6 = !lean::is_exclusive(x_3);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_9; usize x_10; usize x_11; obj* x_12; obj* x_13; obj* x_14; 
x_7 = lean::cnstr_get(x_3, 0);
x_8 = lean::cnstr_get(x_3, 1);
lean::inc(x_2);
lean::inc(x_4);
x_9 = lean::apply_1(x_2, x_4);
x_10 = lean::unbox_size_t(x_9);
lean::dec(x_9);
x_11 = 1;
x_12 = l_PersistentHashMap_insertAux___main___rarg(x_1, x_2, x_7, x_10, x_11, x_4, x_5);
x_13 = lean::mk_nat_obj(1u);
x_14 = lean::nat_add(x_8, x_13);
lean::dec(x_8);
lean::cnstr_set(x_3, 1, x_14);
lean::cnstr_set(x_3, 0, x_12);
return x_3;
}
else
{
obj* x_15; obj* x_16; obj* x_17; usize x_18; usize x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
x_15 = lean::cnstr_get(x_3, 0);
x_16 = lean::cnstr_get(x_3, 1);
lean::inc(x_16);
lean::inc(x_15);
lean::dec(x_3);
lean::inc(x_2);
lean::inc(x_4);
x_17 = lean::apply_1(x_2, x_4);
x_18 = lean::unbox_size_t(x_17);
lean::dec(x_17);
x_19 = 1;
x_20 = l_PersistentHashMap_insertAux___main___rarg(x_1, x_2, x_15, x_18, x_19, x_4, x_5);
x_21 = lean::mk_nat_obj(1u);
x_22 = lean::nat_add(x_16, x_21);
lean::dec(x_16);
x_23 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_23, 0, x_20);
lean::cnstr_set(x_23, 1, x_22);
return x_23;
}
}
}
obj* l_PersistentHashMap_insert___main(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentHashMap_insert___main___rarg), 5, 0);
return x_3;
}
}
obj* l_PersistentHashMap_insert___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_PersistentHashMap_insert___main___rarg(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
obj* l_PersistentHashMap_insert(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentHashMap_insert___rarg), 5, 0);
return x_3;
}
}
obj* l_PersistentHashMap_findAtAux___main___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; uint8 x_8; 
x_7 = lean::array_get_size(x_2);
x_8 = lean::nat_dec_lt(x_5, x_7);
lean::dec(x_7);
if (x_8 == 0)
{
obj* x_9; 
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_1);
x_9 = lean::box(0);
return x_9;
}
else
{
obj* x_10; obj* x_11; uint8 x_12; 
x_10 = lean::array_fget(x_2, x_5);
lean::inc(x_1);
lean::inc(x_6);
x_11 = lean::apply_2(x_1, x_6, x_10);
x_12 = lean::unbox(x_11);
lean::dec(x_11);
if (x_12 == 0)
{
obj* x_13; obj* x_14; 
x_13 = lean::mk_nat_obj(1u);
x_14 = lean::nat_add(x_5, x_13);
lean::dec(x_5);
x_4 = lean::box(0);
x_5 = x_14;
goto _start;
}
else
{
obj* x_16; obj* x_17; 
lean::dec(x_6);
lean::dec(x_1);
x_16 = lean::array_fget(x_3, x_5);
lean::dec(x_5);
x_17 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_17, 0, x_16);
return x_17;
}
}
}
}
obj* l_PersistentHashMap_findAtAux___main(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentHashMap_findAtAux___main___rarg___boxed), 6, 0);
return x_3;
}
}
obj* l_PersistentHashMap_findAtAux___main___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_PersistentHashMap_findAtAux___main___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_3);
lean::dec(x_2);
return x_7;
}
}
obj* l_PersistentHashMap_findAtAux___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_PersistentHashMap_findAtAux___main___rarg(x_1, x_2, x_3, lean::box(0), x_5, x_6);
return x_7;
}
}
obj* l_PersistentHashMap_findAtAux(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentHashMap_findAtAux___rarg___boxed), 6, 0);
return x_3;
}
}
obj* l_PersistentHashMap_findAtAux___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_PersistentHashMap_findAtAux___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_3);
lean::dec(x_2);
return x_7;
}
}
obj* l_PersistentHashMap_findAux___main___rarg(obj* x_1, obj* x_2, usize x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_5; usize x_6; usize x_7; usize x_8; obj* x_9; obj* x_10; obj* x_11; 
x_5 = lean::cnstr_get(x_2, 0);
x_6 = 5;
x_7 = l_PersistentHashMap_insertAux___main___rarg___closed__2;
x_8 = x_3 & x_7;
x_9 = lean::usize_to_nat(x_8);
x_10 = lean::box(2);
x_11 = lean::array_get(x_10, x_5, x_9);
lean::dec(x_9);
switch (lean::obj_tag(x_11)) {
case 0:
{
obj* x_12; obj* x_13; obj* x_14; uint8 x_15; 
x_12 = lean::cnstr_get(x_11, 0);
lean::inc(x_12);
x_13 = lean::cnstr_get(x_11, 1);
lean::inc(x_13);
lean::dec(x_11);
x_14 = lean::apply_2(x_1, x_4, x_12);
x_15 = lean::unbox(x_14);
lean::dec(x_14);
if (x_15 == 0)
{
obj* x_16; 
lean::dec(x_13);
x_16 = lean::box(0);
return x_16;
}
else
{
obj* x_17; 
x_17 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_17, 0, x_13);
return x_17;
}
}
case 1:
{
obj* x_18; usize x_19; obj* x_20; 
x_18 = lean::cnstr_get(x_11, 0);
lean::inc(x_18);
lean::dec(x_11);
x_19 = x_3 >> x_6;
x_20 = l_PersistentHashMap_findAux___main___rarg(x_1, x_18, x_19, x_4);
lean::dec(x_18);
return x_20;
}
default: 
{
obj* x_21; 
lean::dec(x_4);
lean::dec(x_1);
x_21 = lean::box(0);
return x_21;
}
}
}
else
{
obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_22 = lean::cnstr_get(x_2, 0);
x_23 = lean::cnstr_get(x_2, 1);
x_24 = lean::mk_nat_obj(0u);
x_25 = l_PersistentHashMap_findAtAux___main___rarg(x_1, x_22, x_23, lean::box(0), x_24, x_4);
return x_25;
}
}
}
obj* l_PersistentHashMap_findAux___main(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentHashMap_findAux___main___rarg___boxed), 4, 0);
return x_3;
}
}
obj* l_PersistentHashMap_findAux___main___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
usize x_5; obj* x_6; 
x_5 = lean::unbox_size_t(x_3);
lean::dec(x_3);
x_6 = l_PersistentHashMap_findAux___main___rarg(x_1, x_2, x_5, x_4);
lean::dec(x_2);
return x_6;
}
}
obj* l_PersistentHashMap_findAux___rarg(obj* x_1, obj* x_2, usize x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_PersistentHashMap_findAux___main___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* l_PersistentHashMap_findAux(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentHashMap_findAux___rarg___boxed), 4, 0);
return x_3;
}
}
obj* l_PersistentHashMap_findAux___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
usize x_5; obj* x_6; 
x_5 = lean::unbox_size_t(x_3);
lean::dec(x_3);
x_6 = l_PersistentHashMap_findAux___rarg(x_1, x_2, x_5, x_4);
lean::dec(x_2);
return x_6;
}
}
obj* l_PersistentHashMap_find___main___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; usize x_7; obj* x_8; 
x_5 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_6 = lean::apply_1(x_2, x_4);
x_7 = lean::unbox_size_t(x_6);
lean::dec(x_6);
x_8 = l_PersistentHashMap_findAux___main___rarg(x_1, x_5, x_7, x_4);
return x_8;
}
}
obj* l_PersistentHashMap_find___main(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentHashMap_find___main___rarg___boxed), 4, 0);
return x_3;
}
}
obj* l_PersistentHashMap_find___main___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_PersistentHashMap_find___main___rarg(x_1, x_2, x_3, x_4);
lean::dec(x_3);
return x_5;
}
}
obj* l_PersistentHashMap_find___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_PersistentHashMap_find___main___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* l_PersistentHashMap_find(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentHashMap_find___rarg___boxed), 4, 0);
return x_3;
}
}
obj* l_PersistentHashMap_find___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_PersistentHashMap_find___rarg(x_1, x_2, x_3, x_4);
lean::dec(x_3);
return x_5;
}
}
uint8 l_PersistentHashMap_containsAtAux___main___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::array_get_size(x_2);
x_6 = lean::nat_dec_lt(x_3, x_5);
lean::dec(x_5);
if (x_6 == 0)
{
uint8 x_7; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_1);
x_7 = 0;
return x_7;
}
else
{
obj* x_8; obj* x_9; uint8 x_10; 
x_8 = lean::array_fget(x_2, x_3);
lean::inc(x_1);
lean::inc(x_4);
x_9 = lean::apply_2(x_1, x_4, x_8);
x_10 = lean::unbox(x_9);
lean::dec(x_9);
if (x_10 == 0)
{
obj* x_11; obj* x_12; 
x_11 = lean::mk_nat_obj(1u);
x_12 = lean::nat_add(x_3, x_11);
lean::dec(x_3);
x_3 = x_12;
goto _start;
}
else
{
uint8 x_14; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_1);
x_14 = 1;
return x_14;
}
}
}
}
obj* l_PersistentHashMap_containsAtAux___main(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentHashMap_containsAtAux___main___rarg___boxed), 4, 0);
return x_2;
}
}
obj* l_PersistentHashMap_containsAtAux___main___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; obj* x_6; 
x_5 = l_PersistentHashMap_containsAtAux___main___rarg(x_1, x_2, x_3, x_4);
lean::dec(x_2);
x_6 = lean::box(x_5);
return x_6;
}
}
uint8 l_PersistentHashMap_containsAtAux___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
uint8 x_7; 
x_7 = l_PersistentHashMap_containsAtAux___main___rarg(x_1, x_2, x_5, x_6);
return x_7;
}
}
obj* l_PersistentHashMap_containsAtAux(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentHashMap_containsAtAux___rarg___boxed), 6, 0);
return x_3;
}
}
obj* l_PersistentHashMap_containsAtAux___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
uint8 x_7; obj* x_8; 
x_7 = l_PersistentHashMap_containsAtAux___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_3);
lean::dec(x_2);
x_8 = lean::box(x_7);
return x_8;
}
}
obj* l_PersistentHashMap_containsAux___main___rarg(obj* x_1, obj* x_2, usize x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_5; usize x_6; usize x_7; usize x_8; obj* x_9; obj* x_10; obj* x_11; 
x_5 = lean::cnstr_get(x_2, 0);
x_6 = 5;
x_7 = l_PersistentHashMap_insertAux___main___rarg___closed__2;
x_8 = x_3 & x_7;
x_9 = lean::usize_to_nat(x_8);
x_10 = lean::box(2);
x_11 = lean::array_get(x_10, x_5, x_9);
lean::dec(x_9);
switch (lean::obj_tag(x_11)) {
case 0:
{
obj* x_12; obj* x_13; 
x_12 = lean::cnstr_get(x_11, 0);
lean::inc(x_12);
lean::dec(x_11);
x_13 = lean::apply_2(x_1, x_4, x_12);
return x_13;
}
case 1:
{
obj* x_14; usize x_15; obj* x_16; 
x_14 = lean::cnstr_get(x_11, 0);
lean::inc(x_14);
lean::dec(x_11);
x_15 = x_3 >> x_6;
x_16 = l_PersistentHashMap_containsAux___main___rarg(x_1, x_14, x_15, x_4);
lean::dec(x_14);
return x_16;
}
default: 
{
uint8 x_17; obj* x_18; 
lean::dec(x_4);
lean::dec(x_1);
x_17 = 0;
x_18 = lean::box(x_17);
return x_18;
}
}
}
else
{
obj* x_19; obj* x_20; uint8 x_21; obj* x_22; 
x_19 = lean::cnstr_get(x_2, 0);
x_20 = lean::mk_nat_obj(0u);
x_21 = l_PersistentHashMap_containsAtAux___main___rarg(x_1, x_19, x_20, x_4);
x_22 = lean::box(x_21);
return x_22;
}
}
}
obj* l_PersistentHashMap_containsAux___main(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentHashMap_containsAux___main___rarg___boxed), 4, 0);
return x_3;
}
}
obj* l_PersistentHashMap_containsAux___main___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
usize x_5; obj* x_6; 
x_5 = lean::unbox_size_t(x_3);
lean::dec(x_3);
x_6 = l_PersistentHashMap_containsAux___main___rarg(x_1, x_2, x_5, x_4);
lean::dec(x_2);
return x_6;
}
}
obj* l_PersistentHashMap_containsAux___rarg(obj* x_1, obj* x_2, usize x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_PersistentHashMap_containsAux___main___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* l_PersistentHashMap_containsAux(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentHashMap_containsAux___rarg___boxed), 4, 0);
return x_3;
}
}
obj* l_PersistentHashMap_containsAux___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
usize x_5; obj* x_6; 
x_5 = lean::unbox_size_t(x_3);
lean::dec(x_3);
x_6 = l_PersistentHashMap_containsAux___rarg(x_1, x_2, x_5, x_4);
lean::dec(x_2);
return x_6;
}
}
obj* l_PersistentHashMap_contains___main___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; usize x_7; obj* x_8; 
x_5 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
x_6 = lean::apply_1(x_2, x_4);
x_7 = lean::unbox_size_t(x_6);
lean::dec(x_6);
x_8 = l_PersistentHashMap_containsAux___main___rarg(x_1, x_5, x_7, x_4);
return x_8;
}
}
obj* l_PersistentHashMap_contains___main(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentHashMap_contains___main___rarg___boxed), 4, 0);
return x_3;
}
}
obj* l_PersistentHashMap_contains___main___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_PersistentHashMap_contains___main___rarg(x_1, x_2, x_3, x_4);
lean::dec(x_3);
return x_5;
}
}
obj* l_PersistentHashMap_contains___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_PersistentHashMap_contains___main___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* l_PersistentHashMap_contains(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentHashMap_contains___rarg___boxed), 4, 0);
return x_3;
}
}
obj* l_PersistentHashMap_contains___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_PersistentHashMap_contains___rarg(x_1, x_2, x_3, x_4);
lean::dec(x_3);
return x_5;
}
}
obj* l_PersistentHashMap_isUnaryEntries___main___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::array_get_size(x_1);
x_5 = lean::nat_dec_lt(x_2, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
lean::dec(x_2);
return x_3;
}
else
{
obj* x_6; 
x_6 = lean::array_fget(x_1, x_2);
switch (lean::obj_tag(x_6)) {
case 0:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
x_8 = lean::cnstr_get(x_6, 1);
lean::inc(x_8);
lean::dec(x_6);
x_9 = lean::mk_nat_obj(1u);
x_10 = lean::nat_add(x_2, x_9);
lean::dec(x_2);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_7);
lean::cnstr_set(x_11, 1, x_8);
x_12 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_12, 0, x_11);
x_2 = x_10;
x_3 = x_12;
goto _start;
}
else
{
obj* x_14; 
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_2);
x_14 = lean::box(0);
return x_14;
}
}
case 1:
{
obj* x_15; 
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_2);
x_15 = lean::box(0);
return x_15;
}
default: 
{
obj* x_16; obj* x_17; 
x_16 = lean::mk_nat_obj(1u);
x_17 = lean::nat_add(x_2, x_16);
lean::dec(x_2);
x_2 = x_17;
goto _start;
}
}
}
}
}
obj* l_PersistentHashMap_isUnaryEntries___main(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentHashMap_isUnaryEntries___main___rarg___boxed), 3, 0);
return x_3;
}
}
obj* l_PersistentHashMap_isUnaryEntries___main___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_PersistentHashMap_isUnaryEntries___main___rarg(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_PersistentHashMap_isUnaryEntries___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_PersistentHashMap_isUnaryEntries___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
obj* l_PersistentHashMap_isUnaryEntries(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentHashMap_isUnaryEntries___rarg___boxed), 3, 0);
return x_3;
}
}
obj* l_PersistentHashMap_isUnaryEntries___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_PersistentHashMap_isUnaryEntries___rarg(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_PersistentHashMap_isUnaryNode___main___rarg(obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = lean::cnstr_get(x_1, 0);
x_3 = lean::box(0);
x_4 = lean::mk_nat_obj(0u);
x_5 = l_PersistentHashMap_isUnaryEntries___main___rarg(x_2, x_4, x_3);
return x_5;
}
else
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; uint8 x_10; 
x_6 = lean::cnstr_get(x_1, 0);
x_7 = lean::cnstr_get(x_1, 1);
x_8 = lean::array_get_size(x_6);
x_9 = lean::mk_nat_obj(1u);
x_10 = lean::nat_dec_eq(x_9, x_8);
lean::dec(x_8);
if (x_10 == 0)
{
obj* x_11; 
x_11 = lean::box(0);
return x_11;
}
else
{
obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_12 = lean::mk_nat_obj(0u);
x_13 = lean::array_fget(x_6, x_12);
x_14 = lean::array_fget(x_7, x_12);
x_15 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_15, 0, x_13);
lean::cnstr_set(x_15, 1, x_14);
x_16 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_16, 0, x_15);
return x_16;
}
}
}
}
obj* l_PersistentHashMap_isUnaryNode___main(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentHashMap_isUnaryNode___main___rarg___boxed), 1, 0);
return x_3;
}
}
obj* l_PersistentHashMap_isUnaryNode___main___rarg___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_PersistentHashMap_isUnaryNode___main___rarg(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_PersistentHashMap_isUnaryNode___rarg(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_PersistentHashMap_isUnaryNode___main___rarg(x_1);
return x_2;
}
}
obj* l_PersistentHashMap_isUnaryNode(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentHashMap_isUnaryNode___rarg___boxed), 1, 0);
return x_3;
}
}
obj* l_PersistentHashMap_isUnaryNode___rarg___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_PersistentHashMap_isUnaryNode___rarg(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_PersistentHashMap_eraseAux___main___rarg(obj* x_1, obj* x_2, usize x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_5; usize x_6; usize x_7; usize x_8; obj* x_9; obj* x_10; obj* x_11; 
x_5 = lean::cnstr_get(x_2, 0);
lean::inc(x_5);
x_6 = 5;
x_7 = l_PersistentHashMap_insertAux___main___rarg___closed__2;
x_8 = x_3 & x_7;
x_9 = lean::usize_to_nat(x_8);
x_10 = lean::box(2);
x_11 = lean::array_get(x_10, x_5, x_9);
switch (lean::obj_tag(x_11)) {
case 0:
{
obj* x_12; obj* x_13; uint8 x_14; 
x_12 = lean::cnstr_get(x_11, 0);
lean::inc(x_12);
lean::dec(x_11);
x_13 = lean::apply_2(x_1, x_4, x_12);
x_14 = lean::unbox(x_13);
lean::dec(x_13);
if (x_14 == 0)
{
uint8 x_15; obj* x_16; obj* x_17; 
lean::dec(x_9);
lean::dec(x_5);
x_15 = 0;
x_16 = lean::box(x_15);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_2);
lean::cnstr_set(x_17, 1, x_16);
return x_17;
}
else
{
uint8 x_18; 
x_18 = !lean::is_exclusive(x_2);
if (x_18 == 0)
{
obj* x_19; obj* x_20; uint8 x_21; obj* x_22; obj* x_23; 
x_19 = lean::cnstr_get(x_2, 0);
lean::dec(x_19);
x_20 = lean::array_set(x_5, x_9, x_10);
lean::dec(x_9);
lean::cnstr_set(x_2, 0, x_20);
x_21 = 1;
x_22 = lean::box(x_21);
x_23 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_23, 0, x_2);
lean::cnstr_set(x_23, 1, x_22);
return x_23;
}
else
{
obj* x_24; obj* x_25; uint8 x_26; obj* x_27; obj* x_28; 
lean::dec(x_2);
x_24 = lean::array_set(x_5, x_9, x_10);
lean::dec(x_9);
x_25 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_25, 0, x_24);
x_26 = 1;
x_27 = lean::box(x_26);
x_28 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_28, 0, x_25);
lean::cnstr_set(x_28, 1, x_27);
return x_28;
}
}
}
case 1:
{
uint8 x_29; 
x_29 = !lean::is_exclusive(x_11);
if (x_29 == 0)
{
obj* x_30; obj* x_31; usize x_32; obj* x_33; obj* x_34; uint8 x_35; 
x_30 = lean::cnstr_get(x_11, 0);
x_31 = lean::array_set(x_5, x_9, x_10);
x_32 = x_3 >> x_6;
x_33 = l_PersistentHashMap_eraseAux___main___rarg(x_1, x_30, x_32, x_4);
x_34 = lean::cnstr_get(x_33, 1);
lean::inc(x_34);
x_35 = lean::unbox(x_34);
lean::dec(x_34);
if (x_35 == 0)
{
uint8 x_36; 
lean::dec(x_31);
lean::free_heap_obj(x_11);
lean::dec(x_9);
x_36 = !lean::is_exclusive(x_33);
if (x_36 == 0)
{
obj* x_37; obj* x_38; uint8 x_39; obj* x_40; 
x_37 = lean::cnstr_get(x_33, 1);
lean::dec(x_37);
x_38 = lean::cnstr_get(x_33, 0);
lean::dec(x_38);
x_39 = 0;
x_40 = lean::box(x_39);
lean::cnstr_set(x_33, 1, x_40);
lean::cnstr_set(x_33, 0, x_2);
return x_33;
}
else
{
uint8 x_41; obj* x_42; obj* x_43; 
lean::dec(x_33);
x_41 = 0;
x_42 = lean::box(x_41);
x_43 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_43, 0, x_2);
lean::cnstr_set(x_43, 1, x_42);
return x_43;
}
}
else
{
uint8 x_44; 
x_44 = !lean::is_exclusive(x_2);
if (x_44 == 0)
{
obj* x_45; uint8 x_46; 
x_45 = lean::cnstr_get(x_2, 0);
lean::dec(x_45);
x_46 = !lean::is_exclusive(x_33);
if (x_46 == 0)
{
obj* x_47; obj* x_48; obj* x_49; 
x_47 = lean::cnstr_get(x_33, 0);
x_48 = lean::cnstr_get(x_33, 1);
lean::dec(x_48);
x_49 = l_PersistentHashMap_isUnaryNode___main___rarg(x_47);
if (lean::obj_tag(x_49) == 0)
{
obj* x_50; uint8 x_51; obj* x_52; 
lean::cnstr_set(x_11, 0, x_47);
x_50 = lean::array_set(x_31, x_9, x_11);
lean::dec(x_9);
lean::cnstr_set(x_2, 0, x_50);
x_51 = 1;
x_52 = lean::box(x_51);
lean::cnstr_set(x_33, 1, x_52);
lean::cnstr_set(x_33, 0, x_2);
return x_33;
}
else
{
obj* x_53; uint8 x_54; 
lean::free_heap_obj(x_33);
lean::dec(x_47);
lean::free_heap_obj(x_11);
x_53 = lean::cnstr_get(x_49, 0);
lean::inc(x_53);
lean::dec(x_49);
x_54 = !lean::is_exclusive(x_53);
if (x_54 == 0)
{
obj* x_55; obj* x_56; obj* x_57; obj* x_58; uint8 x_59; obj* x_60; 
x_55 = lean::cnstr_get(x_53, 0);
x_56 = lean::cnstr_get(x_53, 1);
x_57 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_57, 0, x_55);
lean::cnstr_set(x_57, 1, x_56);
x_58 = lean::array_set(x_31, x_9, x_57);
lean::dec(x_9);
lean::cnstr_set(x_2, 0, x_58);
x_59 = 1;
x_60 = lean::box(x_59);
lean::cnstr_set(x_53, 1, x_60);
lean::cnstr_set(x_53, 0, x_2);
return x_53;
}
else
{
obj* x_61; obj* x_62; obj* x_63; obj* x_64; uint8 x_65; obj* x_66; obj* x_67; 
x_61 = lean::cnstr_get(x_53, 0);
x_62 = lean::cnstr_get(x_53, 1);
lean::inc(x_62);
lean::inc(x_61);
lean::dec(x_53);
x_63 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_63, 0, x_61);
lean::cnstr_set(x_63, 1, x_62);
x_64 = lean::array_set(x_31, x_9, x_63);
lean::dec(x_9);
lean::cnstr_set(x_2, 0, x_64);
x_65 = 1;
x_66 = lean::box(x_65);
x_67 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_67, 0, x_2);
lean::cnstr_set(x_67, 1, x_66);
return x_67;
}
}
}
else
{
obj* x_68; obj* x_69; 
x_68 = lean::cnstr_get(x_33, 0);
lean::inc(x_68);
lean::dec(x_33);
x_69 = l_PersistentHashMap_isUnaryNode___main___rarg(x_68);
if (lean::obj_tag(x_69) == 0)
{
obj* x_70; uint8 x_71; obj* x_72; obj* x_73; 
lean::cnstr_set(x_11, 0, x_68);
x_70 = lean::array_set(x_31, x_9, x_11);
lean::dec(x_9);
lean::cnstr_set(x_2, 0, x_70);
x_71 = 1;
x_72 = lean::box(x_71);
x_73 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_73, 0, x_2);
lean::cnstr_set(x_73, 1, x_72);
return x_73;
}
else
{
obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; uint8 x_80; obj* x_81; obj* x_82; 
lean::dec(x_68);
lean::free_heap_obj(x_11);
x_74 = lean::cnstr_get(x_69, 0);
lean::inc(x_74);
lean::dec(x_69);
x_75 = lean::cnstr_get(x_74, 0);
lean::inc(x_75);
x_76 = lean::cnstr_get(x_74, 1);
lean::inc(x_76);
if (lean::is_exclusive(x_74)) {
 lean::cnstr_release(x_74, 0);
 lean::cnstr_release(x_74, 1);
 x_77 = x_74;
} else {
 lean::dec_ref(x_74);
 x_77 = lean::box(0);
}
x_78 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_78, 0, x_75);
lean::cnstr_set(x_78, 1, x_76);
x_79 = lean::array_set(x_31, x_9, x_78);
lean::dec(x_9);
lean::cnstr_set(x_2, 0, x_79);
x_80 = 1;
x_81 = lean::box(x_80);
if (lean::is_scalar(x_77)) {
 x_82 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_82 = x_77;
}
lean::cnstr_set(x_82, 0, x_2);
lean::cnstr_set(x_82, 1, x_81);
return x_82;
}
}
}
else
{
obj* x_83; obj* x_84; obj* x_85; 
lean::dec(x_2);
x_83 = lean::cnstr_get(x_33, 0);
lean::inc(x_83);
if (lean::is_exclusive(x_33)) {
 lean::cnstr_release(x_33, 0);
 lean::cnstr_release(x_33, 1);
 x_84 = x_33;
} else {
 lean::dec_ref(x_33);
 x_84 = lean::box(0);
}
x_85 = l_PersistentHashMap_isUnaryNode___main___rarg(x_83);
if (lean::obj_tag(x_85) == 0)
{
obj* x_86; obj* x_87; uint8 x_88; obj* x_89; obj* x_90; 
lean::cnstr_set(x_11, 0, x_83);
x_86 = lean::array_set(x_31, x_9, x_11);
lean::dec(x_9);
x_87 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_87, 0, x_86);
x_88 = 1;
x_89 = lean::box(x_88);
if (lean::is_scalar(x_84)) {
 x_90 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_90 = x_84;
}
lean::cnstr_set(x_90, 0, x_87);
lean::cnstr_set(x_90, 1, x_89);
return x_90;
}
else
{
obj* x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_95; obj* x_96; obj* x_97; uint8 x_98; obj* x_99; obj* x_100; 
lean::dec(x_84);
lean::dec(x_83);
lean::free_heap_obj(x_11);
x_91 = lean::cnstr_get(x_85, 0);
lean::inc(x_91);
lean::dec(x_85);
x_92 = lean::cnstr_get(x_91, 0);
lean::inc(x_92);
x_93 = lean::cnstr_get(x_91, 1);
lean::inc(x_93);
if (lean::is_exclusive(x_91)) {
 lean::cnstr_release(x_91, 0);
 lean::cnstr_release(x_91, 1);
 x_94 = x_91;
} else {
 lean::dec_ref(x_91);
 x_94 = lean::box(0);
}
x_95 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_95, 0, x_92);
lean::cnstr_set(x_95, 1, x_93);
x_96 = lean::array_set(x_31, x_9, x_95);
lean::dec(x_9);
x_97 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_97, 0, x_96);
x_98 = 1;
x_99 = lean::box(x_98);
if (lean::is_scalar(x_94)) {
 x_100 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_100 = x_94;
}
lean::cnstr_set(x_100, 0, x_97);
lean::cnstr_set(x_100, 1, x_99);
return x_100;
}
}
}
}
else
{
obj* x_101; obj* x_102; usize x_103; obj* x_104; obj* x_105; uint8 x_106; 
x_101 = lean::cnstr_get(x_11, 0);
lean::inc(x_101);
lean::dec(x_11);
x_102 = lean::array_set(x_5, x_9, x_10);
x_103 = x_3 >> x_6;
x_104 = l_PersistentHashMap_eraseAux___main___rarg(x_1, x_101, x_103, x_4);
x_105 = lean::cnstr_get(x_104, 1);
lean::inc(x_105);
x_106 = lean::unbox(x_105);
lean::dec(x_105);
if (x_106 == 0)
{
obj* x_107; uint8 x_108; obj* x_109; obj* x_110; 
lean::dec(x_102);
lean::dec(x_9);
if (lean::is_exclusive(x_104)) {
 lean::cnstr_release(x_104, 0);
 lean::cnstr_release(x_104, 1);
 x_107 = x_104;
} else {
 lean::dec_ref(x_104);
 x_107 = lean::box(0);
}
x_108 = 0;
x_109 = lean::box(x_108);
if (lean::is_scalar(x_107)) {
 x_110 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_110 = x_107;
}
lean::cnstr_set(x_110, 0, x_2);
lean::cnstr_set(x_110, 1, x_109);
return x_110;
}
else
{
obj* x_111; obj* x_112; obj* x_113; obj* x_114; 
if (lean::is_exclusive(x_2)) {
 lean::cnstr_release(x_2, 0);
 x_111 = x_2;
} else {
 lean::dec_ref(x_2);
 x_111 = lean::box(0);
}
x_112 = lean::cnstr_get(x_104, 0);
lean::inc(x_112);
if (lean::is_exclusive(x_104)) {
 lean::cnstr_release(x_104, 0);
 lean::cnstr_release(x_104, 1);
 x_113 = x_104;
} else {
 lean::dec_ref(x_104);
 x_113 = lean::box(0);
}
x_114 = l_PersistentHashMap_isUnaryNode___main___rarg(x_112);
if (lean::obj_tag(x_114) == 0)
{
obj* x_115; obj* x_116; obj* x_117; uint8 x_118; obj* x_119; obj* x_120; 
x_115 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_115, 0, x_112);
x_116 = lean::array_set(x_102, x_9, x_115);
lean::dec(x_9);
if (lean::is_scalar(x_111)) {
 x_117 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_117 = x_111;
}
lean::cnstr_set(x_117, 0, x_116);
x_118 = 1;
x_119 = lean::box(x_118);
if (lean::is_scalar(x_113)) {
 x_120 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_120 = x_113;
}
lean::cnstr_set(x_120, 0, x_117);
lean::cnstr_set(x_120, 1, x_119);
return x_120;
}
else
{
obj* x_121; obj* x_122; obj* x_123; obj* x_124; obj* x_125; obj* x_126; obj* x_127; uint8 x_128; obj* x_129; obj* x_130; 
lean::dec(x_113);
lean::dec(x_112);
x_121 = lean::cnstr_get(x_114, 0);
lean::inc(x_121);
lean::dec(x_114);
x_122 = lean::cnstr_get(x_121, 0);
lean::inc(x_122);
x_123 = lean::cnstr_get(x_121, 1);
lean::inc(x_123);
if (lean::is_exclusive(x_121)) {
 lean::cnstr_release(x_121, 0);
 lean::cnstr_release(x_121, 1);
 x_124 = x_121;
} else {
 lean::dec_ref(x_121);
 x_124 = lean::box(0);
}
x_125 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_125, 0, x_122);
lean::cnstr_set(x_125, 1, x_123);
x_126 = lean::array_set(x_102, x_9, x_125);
lean::dec(x_9);
if (lean::is_scalar(x_111)) {
 x_127 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_127 = x_111;
}
lean::cnstr_set(x_127, 0, x_126);
x_128 = 1;
x_129 = lean::box(x_128);
if (lean::is_scalar(x_124)) {
 x_130 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_130 = x_124;
}
lean::cnstr_set(x_130, 0, x_127);
lean::cnstr_set(x_130, 1, x_129);
return x_130;
}
}
}
}
default: 
{
uint8 x_131; obj* x_132; obj* x_133; 
lean::dec(x_9);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_1);
x_131 = 0;
x_132 = lean::box(x_131);
x_133 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_133, 0, x_2);
lean::cnstr_set(x_133, 1, x_132);
return x_133;
}
}
}
else
{
obj* x_134; obj* x_135; obj* x_136; obj* x_137; 
x_134 = lean::cnstr_get(x_2, 0);
lean::inc(x_134);
x_135 = lean::cnstr_get(x_2, 1);
lean::inc(x_135);
x_136 = lean::mk_nat_obj(0u);
x_137 = l_Array_indexOfAux___main___rarg(x_1, x_134, x_4, x_136);
if (lean::obj_tag(x_137) == 0)
{
uint8 x_138; obj* x_139; obj* x_140; 
lean::dec(x_135);
lean::dec(x_134);
x_138 = 0;
x_139 = lean::box(x_138);
x_140 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_140, 0, x_2);
lean::cnstr_set(x_140, 1, x_139);
return x_140;
}
else
{
uint8 x_141; 
x_141 = !lean::is_exclusive(x_2);
if (x_141 == 0)
{
obj* x_142; obj* x_143; obj* x_144; obj* x_145; obj* x_146; uint8 x_147; obj* x_148; obj* x_149; 
x_142 = lean::cnstr_get(x_2, 1);
lean::dec(x_142);
x_143 = lean::cnstr_get(x_2, 0);
lean::dec(x_143);
x_144 = lean::cnstr_get(x_137, 0);
lean::inc(x_144);
lean::dec(x_137);
x_145 = l_Array_eraseIdx_x27___rarg(x_134, x_144);
x_146 = l_Array_eraseIdx_x27___rarg(x_135, x_144);
lean::dec(x_144);
lean::cnstr_set(x_2, 1, x_146);
lean::cnstr_set(x_2, 0, x_145);
x_147 = 1;
x_148 = lean::box(x_147);
x_149 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_149, 0, x_2);
lean::cnstr_set(x_149, 1, x_148);
return x_149;
}
else
{
obj* x_150; obj* x_151; obj* x_152; obj* x_153; uint8 x_154; obj* x_155; obj* x_156; 
lean::dec(x_2);
x_150 = lean::cnstr_get(x_137, 0);
lean::inc(x_150);
lean::dec(x_137);
x_151 = l_Array_eraseIdx_x27___rarg(x_134, x_150);
x_152 = l_Array_eraseIdx_x27___rarg(x_135, x_150);
lean::dec(x_150);
x_153 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_153, 0, x_151);
lean::cnstr_set(x_153, 1, x_152);
x_154 = 1;
x_155 = lean::box(x_154);
x_156 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_156, 0, x_153);
lean::cnstr_set(x_156, 1, x_155);
return x_156;
}
}
}
}
}
obj* l_PersistentHashMap_eraseAux___main(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentHashMap_eraseAux___main___rarg___boxed), 4, 0);
return x_3;
}
}
obj* l_PersistentHashMap_eraseAux___main___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
usize x_5; obj* x_6; 
x_5 = lean::unbox_size_t(x_3);
lean::dec(x_3);
x_6 = l_PersistentHashMap_eraseAux___main___rarg(x_1, x_2, x_5, x_4);
return x_6;
}
}
obj* l_PersistentHashMap_eraseAux___rarg(obj* x_1, obj* x_2, usize x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_PersistentHashMap_eraseAux___main___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* l_PersistentHashMap_eraseAux(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentHashMap_eraseAux___rarg___boxed), 4, 0);
return x_3;
}
}
obj* l_PersistentHashMap_eraseAux___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
usize x_5; obj* x_6; 
x_5 = lean::unbox_size_t(x_3);
lean::dec(x_3);
x_6 = l_PersistentHashMap_eraseAux___rarg(x_1, x_2, x_5, x_4);
return x_6;
}
}
obj* l_PersistentHashMap_erase___main___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; 
x_5 = !lean::is_exclusive(x_3);
if (x_5 == 0)
{
obj* x_6; obj* x_7; obj* x_8; usize x_9; obj* x_10; obj* x_11; uint8 x_12; 
x_6 = lean::cnstr_get(x_3, 0);
x_7 = lean::cnstr_get(x_3, 1);
lean::inc(x_4);
x_8 = lean::apply_1(x_2, x_4);
x_9 = lean::unbox_size_t(x_8);
lean::dec(x_8);
x_10 = l_PersistentHashMap_eraseAux___main___rarg(x_1, x_6, x_9, x_4);
x_11 = lean::cnstr_get(x_10, 1);
lean::inc(x_11);
x_12 = lean::unbox(x_11);
lean::dec(x_11);
if (x_12 == 0)
{
obj* x_13; 
x_13 = lean::cnstr_get(x_10, 0);
lean::inc(x_13);
lean::dec(x_10);
lean::cnstr_set(x_3, 0, x_13);
return x_3;
}
else
{
obj* x_14; obj* x_15; obj* x_16; 
x_14 = lean::cnstr_get(x_10, 0);
lean::inc(x_14);
lean::dec(x_10);
x_15 = lean::mk_nat_obj(1u);
x_16 = lean::nat_sub(x_7, x_15);
lean::dec(x_7);
lean::cnstr_set(x_3, 1, x_16);
lean::cnstr_set(x_3, 0, x_14);
return x_3;
}
}
else
{
obj* x_17; obj* x_18; obj* x_19; usize x_20; obj* x_21; obj* x_22; uint8 x_23; 
x_17 = lean::cnstr_get(x_3, 0);
x_18 = lean::cnstr_get(x_3, 1);
lean::inc(x_18);
lean::inc(x_17);
lean::dec(x_3);
lean::inc(x_4);
x_19 = lean::apply_1(x_2, x_4);
x_20 = lean::unbox_size_t(x_19);
lean::dec(x_19);
x_21 = l_PersistentHashMap_eraseAux___main___rarg(x_1, x_17, x_20, x_4);
x_22 = lean::cnstr_get(x_21, 1);
lean::inc(x_22);
x_23 = lean::unbox(x_22);
lean::dec(x_22);
if (x_23 == 0)
{
obj* x_24; obj* x_25; 
x_24 = lean::cnstr_get(x_21, 0);
lean::inc(x_24);
lean::dec(x_21);
x_25 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_18);
return x_25;
}
else
{
obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
x_26 = lean::cnstr_get(x_21, 0);
lean::inc(x_26);
lean::dec(x_21);
x_27 = lean::mk_nat_obj(1u);
x_28 = lean::nat_sub(x_18, x_27);
lean::dec(x_18);
x_29 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_29, 0, x_26);
lean::cnstr_set(x_29, 1, x_28);
return x_29;
}
}
}
}
obj* l_PersistentHashMap_erase___main(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentHashMap_erase___main___rarg), 4, 0);
return x_3;
}
}
obj* l_PersistentHashMap_erase___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_PersistentHashMap_erase___main___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* l_PersistentHashMap_erase(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentHashMap_erase___rarg), 4, 0);
return x_3;
}
}
obj* l_Array_miterateAux___main___at_PersistentHashMap_mfoldlAux___main___spec__1___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; uint8 x_9; 
x_8 = lean::array_get_size(x_5);
x_9 = lean::nat_dec_lt(x_6, x_8);
lean::dec(x_8);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_12; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
x_10 = lean::cnstr_get(x_1, 0);
lean::inc(x_10);
lean::dec(x_1);
x_11 = lean::cnstr_get(x_10, 1);
lean::inc(x_11);
lean::dec(x_10);
x_12 = lean::apply_2(x_11, lean::box(0), x_7);
return x_12;
}
else
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_13 = lean::cnstr_get(x_1, 1);
lean::inc(x_13);
x_14 = lean::array_fget(x_5, x_6);
x_15 = lean::mk_nat_obj(1u);
x_16 = lean::nat_add(x_6, x_15);
lean::inc(x_3);
lean::inc(x_1);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at_PersistentHashMap_mfoldlAux___main___spec__1___rarg___boxed), 7, 6);
lean::closure_set(x_17, 0, x_1);
lean::closure_set(x_17, 1, lean::box(0));
lean::closure_set(x_17, 2, x_3);
lean::closure_set(x_17, 3, x_4);
lean::closure_set(x_17, 4, x_5);
lean::closure_set(x_17, 5, x_16);
switch (lean::obj_tag(x_14)) {
case 0:
{
obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
lean::dec(x_1);
x_18 = lean::cnstr_get(x_14, 0);
lean::inc(x_18);
x_19 = lean::cnstr_get(x_14, 1);
lean::inc(x_19);
lean::dec(x_14);
x_20 = lean::apply_3(x_3, x_7, x_18, x_19);
x_21 = lean::apply_4(x_13, lean::box(0), lean::box(0), x_20, x_17);
return x_21;
}
case 1:
{
obj* x_22; obj* x_23; obj* x_24; 
x_22 = lean::cnstr_get(x_14, 0);
lean::inc(x_22);
lean::dec(x_14);
x_23 = l_PersistentHashMap_mfoldlAux___main___rarg(x_1, lean::box(0), x_3, x_22, x_7);
x_24 = lean::apply_4(x_13, lean::box(0), lean::box(0), x_23, x_17);
return x_24;
}
default: 
{
obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
lean::dec(x_3);
x_25 = lean::cnstr_get(x_1, 0);
lean::inc(x_25);
lean::dec(x_1);
x_26 = lean::cnstr_get(x_25, 1);
lean::inc(x_26);
lean::dec(x_25);
x_27 = lean::apply_2(x_26, lean::box(0), x_7);
x_28 = lean::apply_4(x_13, lean::box(0), lean::box(0), x_27, x_17);
return x_28;
}
}
}
}
}
obj* l_Array_miterateAux___main___at_PersistentHashMap_mfoldlAux___main___spec__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at_PersistentHashMap_mfoldlAux___main___spec__1___rarg___boxed), 7, 0);
return x_4;
}
}
obj* l_Array_miterateAux___main___at_PersistentHashMap_mfoldlAux___main___spec__2___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
obj* x_9; uint8 x_10; 
x_9 = lean::array_get_size(x_6);
x_10 = lean::nat_dec_lt(x_7, x_9);
lean::dec(x_9);
if (x_10 == 0)
{
obj* x_11; obj* x_12; obj* x_13; 
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
x_11 = lean::cnstr_get(x_1, 0);
lean::inc(x_11);
lean::dec(x_1);
x_12 = lean::cnstr_get(x_11, 1);
lean::inc(x_12);
lean::dec(x_11);
x_13 = lean::apply_2(x_12, lean::box(0), x_8);
return x_13;
}
else
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_14 = lean::cnstr_get(x_1, 1);
lean::inc(x_14);
x_15 = lean::array_fget(x_6, x_7);
x_16 = lean::array_fget(x_5, x_7);
lean::inc(x_3);
x_17 = lean::apply_3(x_3, x_8, x_15, x_16);
x_18 = lean::mk_nat_obj(1u);
x_19 = lean::nat_add(x_7, x_18);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at_PersistentHashMap_mfoldlAux___main___spec__2___rarg___boxed), 8, 7);
lean::closure_set(x_20, 0, x_1);
lean::closure_set(x_20, 1, lean::box(0));
lean::closure_set(x_20, 2, x_3);
lean::closure_set(x_20, 3, x_4);
lean::closure_set(x_20, 4, x_5);
lean::closure_set(x_20, 5, x_6);
lean::closure_set(x_20, 6, x_19);
x_21 = lean::apply_4(x_14, lean::box(0), lean::box(0), x_17, x_20);
return x_21;
}
}
}
obj* l_Array_miterateAux___main___at_PersistentHashMap_mfoldlAux___main___spec__2(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at_PersistentHashMap_mfoldlAux___main___spec__2___rarg___boxed), 8, 0);
return x_4;
}
}
obj* l_PersistentHashMap_mfoldlAux___main___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; obj* x_7; obj* x_8; 
x_6 = lean::cnstr_get(x_4, 0);
lean::inc(x_6);
lean::dec(x_4);
x_7 = lean::mk_nat_obj(0u);
lean::inc(x_6);
x_8 = l_Array_miterateAux___main___at_PersistentHashMap_mfoldlAux___main___spec__1___rarg(x_1, lean::box(0), x_3, x_6, x_6, x_7, x_5);
return x_8;
}
else
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_9 = lean::cnstr_get(x_4, 0);
lean::inc(x_9);
x_10 = lean::cnstr_get(x_4, 1);
lean::inc(x_10);
lean::dec(x_4);
x_11 = lean::mk_nat_obj(0u);
lean::inc(x_9);
x_12 = l_Array_miterateAux___main___at_PersistentHashMap_mfoldlAux___main___spec__2___rarg(x_1, lean::box(0), x_3, x_9, x_10, x_9, x_11, x_5);
return x_12;
}
}
}
obj* l_PersistentHashMap_mfoldlAux___main(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentHashMap_mfoldlAux___main___rarg), 5, 0);
return x_4;
}
}
obj* l_Array_miterateAux___main___at_PersistentHashMap_mfoldlAux___main___spec__1___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = l_Array_miterateAux___main___at_PersistentHashMap_mfoldlAux___main___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean::dec(x_6);
return x_8;
}
}
obj* l_Array_miterateAux___main___at_PersistentHashMap_mfoldlAux___main___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Array_miterateAux___main___at_PersistentHashMap_mfoldlAux___main___spec__1(x_1, x_2, x_3);
lean::dec(x_3);
return x_4;
}
}
obj* l_Array_miterateAux___main___at_PersistentHashMap_mfoldlAux___main___spec__2___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
obj* x_9; 
x_9 = l_Array_miterateAux___main___at_PersistentHashMap_mfoldlAux___main___spec__2___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean::dec(x_7);
return x_9;
}
}
obj* l_Array_miterateAux___main___at_PersistentHashMap_mfoldlAux___main___spec__2___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Array_miterateAux___main___at_PersistentHashMap_mfoldlAux___main___spec__2(x_1, x_2, x_3);
lean::dec(x_3);
return x_4;
}
}
obj* l_PersistentHashMap_mfoldlAux___main___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_PersistentHashMap_mfoldlAux___main(x_1, x_2, x_3);
lean::dec(x_3);
return x_4;
}
}
obj* l_PersistentHashMap_mfoldlAux___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_PersistentHashMap_mfoldlAux___main___rarg(x_1, lean::box(0), x_3, x_4, x_5);
return x_6;
}
}
obj* l_PersistentHashMap_mfoldlAux(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentHashMap_mfoldlAux___rarg), 5, 0);
return x_4;
}
}
obj* l_PersistentHashMap_mfoldlAux___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_PersistentHashMap_mfoldlAux(x_1, x_2, x_3);
lean::dec(x_3);
return x_4;
}
}
obj* l_PersistentHashMap_mfoldl___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; 
x_6 = lean::cnstr_get(x_3, 0);
lean::inc(x_6);
lean::dec(x_3);
x_7 = l_PersistentHashMap_mfoldlAux___main___rarg(x_1, lean::box(0), x_4, x_6, x_5);
return x_7;
}
}
obj* l_PersistentHashMap_mfoldl(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentHashMap_mfoldl___rarg), 5, 0);
return x_4;
}
}
obj* l_PersistentHashMap_mfoldl___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_PersistentHashMap_mfoldl(x_1, x_2, x_3);
lean::dec(x_3);
return x_4;
}
}
obj* l_Array_miterateAux___main___at_PersistentHashMap_foldl___spec__3___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_7; 
x_6 = lean::array_get_size(x_3);
x_7 = lean::nat_dec_lt(x_4, x_6);
lean::dec(x_6);
if (x_7 == 0)
{
lean::dec(x_4);
lean::dec(x_1);
return x_5;
}
else
{
obj* x_8; obj* x_9; obj* x_10; 
x_8 = lean::array_fget(x_3, x_4);
x_9 = lean::mk_nat_obj(1u);
x_10 = lean::nat_add(x_4, x_9);
lean::dec(x_4);
switch (lean::obj_tag(x_8)) {
case 0:
{
obj* x_11; obj* x_12; obj* x_13; 
x_11 = lean::cnstr_get(x_8, 0);
lean::inc(x_11);
x_12 = lean::cnstr_get(x_8, 1);
lean::inc(x_12);
lean::dec(x_8);
lean::inc(x_1);
x_13 = lean::apply_3(x_1, x_5, x_11, x_12);
x_4 = x_10;
x_5 = x_13;
goto _start;
}
case 1:
{
obj* x_15; obj* x_16; 
x_15 = lean::cnstr_get(x_8, 0);
lean::inc(x_15);
lean::dec(x_8);
lean::inc(x_1);
x_16 = l_PersistentHashMap_mfoldlAux___main___at_PersistentHashMap_foldl___spec__2___rarg(x_1, x_15, x_5);
lean::dec(x_15);
x_4 = x_10;
x_5 = x_16;
goto _start;
}
default: 
{
x_4 = x_10;
goto _start;
}
}
}
}
}
obj* l_Array_miterateAux___main___at_PersistentHashMap_foldl___spec__3(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at_PersistentHashMap_foldl___spec__3___rarg___boxed), 5, 0);
return x_4;
}
}
obj* l_Array_miterateAux___main___at_PersistentHashMap_foldl___spec__4___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; uint8 x_8; 
x_7 = lean::array_get_size(x_4);
x_8 = lean::nat_dec_lt(x_5, x_7);
lean::dec(x_7);
if (x_8 == 0)
{
lean::dec(x_5);
lean::dec(x_1);
return x_6;
}
else
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_9 = lean::array_fget(x_4, x_5);
x_10 = lean::array_fget(x_3, x_5);
lean::inc(x_1);
x_11 = lean::apply_3(x_1, x_6, x_9, x_10);
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_add(x_5, x_12);
lean::dec(x_5);
x_5 = x_13;
x_6 = x_11;
goto _start;
}
}
}
obj* l_Array_miterateAux___main___at_PersistentHashMap_foldl___spec__4(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at_PersistentHashMap_foldl___spec__4___rarg___boxed), 6, 0);
return x_4;
}
}
obj* l_PersistentHashMap_mfoldlAux___main___at_PersistentHashMap_foldl___spec__2___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = lean::cnstr_get(x_2, 0);
x_5 = lean::mk_nat_obj(0u);
x_6 = l_Array_miterateAux___main___at_PersistentHashMap_foldl___spec__3___rarg(x_1, x_4, x_4, x_5, x_3);
return x_6;
}
else
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_7 = lean::cnstr_get(x_2, 0);
x_8 = lean::cnstr_get(x_2, 1);
x_9 = lean::mk_nat_obj(0u);
x_10 = l_Array_miterateAux___main___at_PersistentHashMap_foldl___spec__4___rarg(x_1, x_7, x_8, x_7, x_9, x_3);
return x_10;
}
}
}
obj* l_PersistentHashMap_mfoldlAux___main___at_PersistentHashMap_foldl___spec__2(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentHashMap_mfoldlAux___main___at_PersistentHashMap_foldl___spec__2___rarg___boxed), 3, 0);
return x_4;
}
}
obj* l_PersistentHashMap_mfoldl___at_PersistentHashMap_foldl___spec__1___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::cnstr_get(x_2, 0);
x_5 = l_PersistentHashMap_mfoldlAux___main___at_PersistentHashMap_foldl___spec__2___rarg(x_1, x_4, x_3);
return x_5;
}
}
obj* l_PersistentHashMap_mfoldl___at_PersistentHashMap_foldl___spec__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentHashMap_mfoldl___at_PersistentHashMap_foldl___spec__1___rarg___boxed), 3, 0);
return x_4;
}
}
obj* l_PersistentHashMap_foldl___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_PersistentHashMap_mfoldl___at_PersistentHashMap_foldl___spec__1___rarg(x_2, x_1, x_3);
return x_4;
}
}
obj* l_PersistentHashMap_foldl(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentHashMap_foldl___rarg___boxed), 3, 0);
return x_4;
}
}
obj* l_Array_miterateAux___main___at_PersistentHashMap_foldl___spec__3___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Array_miterateAux___main___at_PersistentHashMap_foldl___spec__3___rarg(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_3);
lean::dec(x_2);
return x_6;
}
}
obj* l_Array_miterateAux___main___at_PersistentHashMap_foldl___spec__4___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Array_miterateAux___main___at_PersistentHashMap_foldl___spec__4___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
return x_7;
}
}
obj* l_PersistentHashMap_mfoldlAux___main___at_PersistentHashMap_foldl___spec__2___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_PersistentHashMap_mfoldlAux___main___at_PersistentHashMap_foldl___spec__2___rarg(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_PersistentHashMap_mfoldl___at_PersistentHashMap_foldl___spec__1___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_PersistentHashMap_mfoldl___at_PersistentHashMap_foldl___spec__1___rarg(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_PersistentHashMap_foldl___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_PersistentHashMap_foldl___rarg(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Array_miterateAux___main___at_PersistentHashMap_toList___spec__3___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::array_get_size(x_2);
x_6 = lean::nat_dec_lt(x_3, x_5);
lean::dec(x_5);
if (x_6 == 0)
{
lean::dec(x_3);
return x_4;
}
else
{
obj* x_7; obj* x_8; obj* x_9; 
x_7 = lean::array_fget(x_2, x_3);
x_8 = lean::mk_nat_obj(1u);
x_9 = lean::nat_add(x_3, x_8);
lean::dec(x_3);
switch (lean::obj_tag(x_7)) {
case 0:
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_10 = lean::cnstr_get(x_7, 0);
lean::inc(x_10);
x_11 = lean::cnstr_get(x_7, 1);
lean::inc(x_11);
lean::dec(x_7);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_10);
lean::cnstr_set(x_12, 1, x_11);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_4);
x_3 = x_9;
x_4 = x_13;
goto _start;
}
case 1:
{
obj* x_15; obj* x_16; 
x_15 = lean::cnstr_get(x_7, 0);
lean::inc(x_15);
lean::dec(x_7);
x_16 = l_PersistentHashMap_mfoldlAux___main___at_PersistentHashMap_toList___spec__2___rarg(x_15, x_4);
lean::dec(x_15);
x_3 = x_9;
x_4 = x_16;
goto _start;
}
default: 
{
x_3 = x_9;
goto _start;
}
}
}
}
}
obj* l_Array_miterateAux___main___at_PersistentHashMap_toList___spec__3(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at_PersistentHashMap_toList___spec__3___rarg___boxed), 4, 0);
return x_3;
}
}
obj* l_Array_miterateAux___main___at_PersistentHashMap_toList___spec__4___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_7; 
x_6 = lean::array_get_size(x_3);
x_7 = lean::nat_dec_lt(x_4, x_6);
lean::dec(x_6);
if (x_7 == 0)
{
lean::dec(x_4);
return x_5;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_8 = lean::array_fget(x_3, x_4);
x_9 = lean::array_fget(x_2, x_4);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_9);
x_11 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_5);
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_add(x_4, x_12);
lean::dec(x_4);
x_4 = x_13;
x_5 = x_11;
goto _start;
}
}
}
obj* l_Array_miterateAux___main___at_PersistentHashMap_toList___spec__4(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at_PersistentHashMap_toList___spec__4___rarg___boxed), 5, 0);
return x_3;
}
}
obj* l_PersistentHashMap_mfoldlAux___main___at_PersistentHashMap_toList___spec__2___rarg(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = lean::cnstr_get(x_1, 0);
x_4 = lean::mk_nat_obj(0u);
x_5 = l_Array_miterateAux___main___at_PersistentHashMap_toList___spec__3___rarg(x_3, x_3, x_4, x_2);
return x_5;
}
else
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_6 = lean::cnstr_get(x_1, 0);
x_7 = lean::cnstr_get(x_1, 1);
x_8 = lean::mk_nat_obj(0u);
x_9 = l_Array_miterateAux___main___at_PersistentHashMap_toList___spec__4___rarg(x_6, x_7, x_6, x_8, x_2);
return x_9;
}
}
}
obj* l_PersistentHashMap_mfoldlAux___main___at_PersistentHashMap_toList___spec__2(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentHashMap_mfoldlAux___main___at_PersistentHashMap_toList___spec__2___rarg___boxed), 2, 0);
return x_3;
}
}
obj* l_PersistentHashMap_mfoldl___at_PersistentHashMap_toList___spec__1___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::cnstr_get(x_1, 0);
x_4 = l_PersistentHashMap_mfoldlAux___main___at_PersistentHashMap_toList___spec__2___rarg(x_3, x_2);
return x_4;
}
}
obj* l_PersistentHashMap_mfoldl___at_PersistentHashMap_toList___spec__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentHashMap_mfoldl___at_PersistentHashMap_toList___spec__1___rarg___boxed), 2, 0);
return x_3;
}
}
obj* l_PersistentHashMap_toList___rarg(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::box(0);
x_3 = l_PersistentHashMap_mfoldl___at_PersistentHashMap_toList___spec__1___rarg(x_1, x_2);
return x_3;
}
}
obj* l_PersistentHashMap_toList(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentHashMap_toList___rarg___boxed), 1, 0);
return x_3;
}
}
obj* l_Array_miterateAux___main___at_PersistentHashMap_toList___spec__3___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_miterateAux___main___at_PersistentHashMap_toList___spec__3___rarg(x_1, x_2, x_3, x_4);
lean::dec(x_2);
lean::dec(x_1);
return x_5;
}
}
obj* l_Array_miterateAux___main___at_PersistentHashMap_toList___spec__4___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Array_miterateAux___main___at_PersistentHashMap_toList___spec__4___rarg(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_6;
}
}
obj* l_PersistentHashMap_mfoldlAux___main___at_PersistentHashMap_toList___spec__2___rarg___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_PersistentHashMap_mfoldlAux___main___at_PersistentHashMap_toList___spec__2___rarg(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_PersistentHashMap_mfoldl___at_PersistentHashMap_toList___spec__1___rarg___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_PersistentHashMap_mfoldl___at_PersistentHashMap_toList___spec__1___rarg(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_PersistentHashMap_toList___rarg___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_PersistentHashMap_toList___rarg(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Array_miterateAux___main___at_PersistentHashMap_collectStats___main___spec__1___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_7; 
x_6 = lean::array_get_size(x_3);
x_7 = lean::nat_dec_lt(x_4, x_6);
lean::dec(x_6);
if (x_7 == 0)
{
lean::dec(x_4);
return x_5;
}
else
{
obj* x_8; obj* x_9; obj* x_10; 
x_8 = lean::array_fget(x_3, x_4);
x_9 = lean::mk_nat_obj(1u);
x_10 = lean::nat_add(x_4, x_9);
lean::dec(x_4);
switch (lean::obj_tag(x_8)) {
case 0:
{
lean::dec(x_8);
x_4 = x_10;
goto _start;
}
case 1:
{
obj* x_12; obj* x_13; obj* x_14; 
x_12 = lean::cnstr_get(x_8, 0);
lean::inc(x_12);
lean::dec(x_8);
x_13 = lean::nat_add(x_1, x_9);
x_14 = l_PersistentHashMap_collectStats___main___rarg(x_12, x_5, x_13);
lean::dec(x_13);
lean::dec(x_12);
x_4 = x_10;
x_5 = x_14;
goto _start;
}
default: 
{
uint8 x_16; 
x_16 = !lean::is_exclusive(x_5);
if (x_16 == 0)
{
obj* x_17; obj* x_18; 
x_17 = lean::cnstr_get(x_5, 1);
x_18 = lean::nat_add(x_17, x_9);
lean::dec(x_17);
lean::cnstr_set(x_5, 1, x_18);
x_4 = x_10;
goto _start;
}
else
{
obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_20 = lean::cnstr_get(x_5, 0);
x_21 = lean::cnstr_get(x_5, 1);
x_22 = lean::cnstr_get(x_5, 2);
x_23 = lean::cnstr_get(x_5, 3);
lean::inc(x_23);
lean::inc(x_22);
lean::inc(x_21);
lean::inc(x_20);
lean::dec(x_5);
x_24 = lean::nat_add(x_21, x_9);
lean::dec(x_21);
x_25 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_25, 0, x_20);
lean::cnstr_set(x_25, 1, x_24);
lean::cnstr_set(x_25, 2, x_22);
lean::cnstr_set(x_25, 3, x_23);
x_4 = x_10;
x_5 = x_25;
goto _start;
}
}
}
}
}
}
obj* l_Array_miterateAux___main___at_PersistentHashMap_collectStats___main___spec__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Array_miterateAux___main___at_PersistentHashMap_collectStats___main___spec__1___rarg___boxed), 5, 0);
return x_3;
}
}
obj* l_PersistentHashMap_collectStats___main___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_2);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_5 = lean::cnstr_get(x_1, 0);
x_6 = lean::cnstr_get(x_2, 0);
x_7 = lean::cnstr_get(x_2, 3);
x_8 = lean::mk_nat_obj(1u);
x_9 = lean::nat_add(x_6, x_8);
lean::dec(x_6);
x_10 = l_Nat_max(x_7, x_3);
lean::dec(x_7);
lean::cnstr_set(x_2, 3, x_10);
lean::cnstr_set(x_2, 0, x_9);
x_11 = lean::mk_nat_obj(0u);
x_12 = l_Array_miterateAux___main___at_PersistentHashMap_collectStats___main___spec__1___rarg(x_3, x_5, x_5, x_11, x_2);
return x_12;
}
else
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
x_13 = lean::cnstr_get(x_1, 0);
x_14 = lean::cnstr_get(x_2, 0);
x_15 = lean::cnstr_get(x_2, 1);
x_16 = lean::cnstr_get(x_2, 2);
x_17 = lean::cnstr_get(x_2, 3);
lean::inc(x_17);
lean::inc(x_16);
lean::inc(x_15);
lean::inc(x_14);
lean::dec(x_2);
x_18 = lean::mk_nat_obj(1u);
x_19 = lean::nat_add(x_14, x_18);
lean::dec(x_14);
x_20 = l_Nat_max(x_17, x_3);
lean::dec(x_17);
x_21 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_21, 0, x_19);
lean::cnstr_set(x_21, 1, x_15);
lean::cnstr_set(x_21, 2, x_16);
lean::cnstr_set(x_21, 3, x_20);
x_22 = lean::mk_nat_obj(0u);
x_23 = l_Array_miterateAux___main___at_PersistentHashMap_collectStats___main___spec__1___rarg(x_3, x_13, x_13, x_22, x_21);
return x_23;
}
}
else
{
uint8 x_24; 
x_24 = !lean::is_exclusive(x_2);
if (x_24 == 0)
{
obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; 
x_25 = lean::cnstr_get(x_1, 0);
x_26 = lean::cnstr_get(x_2, 0);
x_27 = lean::cnstr_get(x_2, 2);
x_28 = lean::cnstr_get(x_2, 3);
x_29 = lean::mk_nat_obj(1u);
x_30 = lean::nat_add(x_26, x_29);
lean::dec(x_26);
x_31 = lean::array_get_size(x_25);
x_32 = lean::nat_add(x_27, x_31);
lean::dec(x_31);
lean::dec(x_27);
x_33 = lean::nat_sub(x_32, x_29);
lean::dec(x_32);
x_34 = l_Nat_max(x_28, x_3);
lean::dec(x_28);
lean::cnstr_set(x_2, 3, x_34);
lean::cnstr_set(x_2, 2, x_33);
lean::cnstr_set(x_2, 0, x_30);
return x_2;
}
else
{
obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; 
x_35 = lean::cnstr_get(x_1, 0);
x_36 = lean::cnstr_get(x_2, 0);
x_37 = lean::cnstr_get(x_2, 1);
x_38 = lean::cnstr_get(x_2, 2);
x_39 = lean::cnstr_get(x_2, 3);
lean::inc(x_39);
lean::inc(x_38);
lean::inc(x_37);
lean::inc(x_36);
lean::dec(x_2);
x_40 = lean::mk_nat_obj(1u);
x_41 = lean::nat_add(x_36, x_40);
lean::dec(x_36);
x_42 = lean::array_get_size(x_35);
x_43 = lean::nat_add(x_38, x_42);
lean::dec(x_42);
lean::dec(x_38);
x_44 = lean::nat_sub(x_43, x_40);
lean::dec(x_43);
x_45 = l_Nat_max(x_39, x_3);
lean::dec(x_39);
x_46 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_46, 0, x_41);
lean::cnstr_set(x_46, 1, x_37);
lean::cnstr_set(x_46, 2, x_44);
lean::cnstr_set(x_46, 3, x_45);
return x_46;
}
}
}
}
obj* l_PersistentHashMap_collectStats___main(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentHashMap_collectStats___main___rarg___boxed), 3, 0);
return x_3;
}
}
obj* l_Array_miterateAux___main___at_PersistentHashMap_collectStats___main___spec__1___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Array_miterateAux___main___at_PersistentHashMap_collectStats___main___spec__1___rarg(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_6;
}
}
obj* l_PersistentHashMap_collectStats___main___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_PersistentHashMap_collectStats___main___rarg(x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_PersistentHashMap_collectStats___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_PersistentHashMap_collectStats___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
obj* l_PersistentHashMap_collectStats(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentHashMap_collectStats___rarg___boxed), 3, 0);
return x_3;
}
}
obj* l_PersistentHashMap_collectStats___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_PersistentHashMap_collectStats___rarg(x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_1);
return x_4;
}
}
obj* _init_l_PersistentHashMap_stats___rarg___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_nat_obj(0u);
x_2 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_2, 0, x_1);
lean::cnstr_set(x_2, 1, x_1);
lean::cnstr_set(x_2, 2, x_1);
lean::cnstr_set(x_2, 3, x_1);
return x_2;
}
}
obj* l_PersistentHashMap_stats___rarg(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = lean::cnstr_get(x_1, 0);
x_3 = l_PersistentHashMap_stats___rarg___closed__1;
x_4 = lean::mk_nat_obj(1u);
x_5 = l_PersistentHashMap_collectStats___main___rarg(x_2, x_3, x_4);
return x_5;
}
}
obj* l_PersistentHashMap_stats(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentHashMap_stats___rarg___boxed), 1, 0);
return x_3;
}
}
obj* l_PersistentHashMap_stats___rarg___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_PersistentHashMap_stats___rarg(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_PersistentHashMap_Stats_toString___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("{ nodes := ");
return x_1;
}
}
obj* _init_l_PersistentHashMap_Stats_toString___closed__2() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string(", null := ");
return x_1;
}
}
obj* _init_l_PersistentHashMap_Stats_toString___closed__3() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string(", collisions := ");
return x_1;
}
}
obj* _init_l_PersistentHashMap_Stats_toString___closed__4() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string(", depth := ");
return x_1;
}
}
obj* _init_l_PersistentHashMap_Stats_toString___closed__5() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("}");
return x_1;
}
}
obj* l_PersistentHashMap_Stats_toString(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = l_Nat_repr(x_2);
x_4 = l_PersistentHashMap_Stats_toString___closed__1;
x_5 = lean::string_append(x_4, x_3);
lean::dec(x_3);
x_6 = l_PersistentHashMap_Stats_toString___closed__2;
x_7 = lean::string_append(x_5, x_6);
x_8 = lean::cnstr_get(x_1, 1);
lean::inc(x_8);
x_9 = l_Nat_repr(x_8);
x_10 = lean::string_append(x_7, x_9);
lean::dec(x_9);
x_11 = l_PersistentHashMap_Stats_toString___closed__3;
x_12 = lean::string_append(x_10, x_11);
x_13 = lean::cnstr_get(x_1, 2);
lean::inc(x_13);
x_14 = l_Nat_repr(x_13);
x_15 = lean::string_append(x_12, x_14);
lean::dec(x_14);
x_16 = l_PersistentHashMap_Stats_toString___closed__4;
x_17 = lean::string_append(x_15, x_16);
x_18 = lean::cnstr_get(x_1, 3);
lean::inc(x_18);
lean::dec(x_1);
x_19 = l_Nat_repr(x_18);
x_20 = lean::string_append(x_17, x_19);
lean::dec(x_19);
x_21 = l_PersistentHashMap_Stats_toString___closed__5;
x_22 = lean::string_append(x_20, x_21);
return x_22;
}
}
obj* _init_l_PersistentHashMap_HasToString___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_PersistentHashMap_Stats_toString), 1, 0);
return x_1;
}
}
obj* _init_l_PersistentHashMap_HasToString() {
_start:
{
obj* x_1; 
x_1 = l_PersistentHashMap_HasToString___closed__1;
return x_1;
}
}
obj* initialize_init_data_array_default(obj*);
obj* initialize_init_data_hashable(obj*);
static bool _G_initialized = false;
obj* initialize_init_data_persistenthashmap_basic(obj* w) {
if (_G_initialized) return w;
_G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_data_array_default(w);
if (io_result_is_error(w)) return w;
w = initialize_init_data_hashable(w);
if (io_result_is_error(w)) return w;
l_PersistentHashMap_Node_inhabited___closed__1 = _init_l_PersistentHashMap_Node_inhabited___closed__1();
lean::mark_persistent(l_PersistentHashMap_Node_inhabited___closed__1);
l_PersistentHashMap_shift = _init_l_PersistentHashMap_shift();
l_PersistentHashMap_branching = _init_l_PersistentHashMap_branching();
l_PersistentHashMap_maxDepth = _init_l_PersistentHashMap_maxDepth();
l_PersistentHashMap_maxCollisions = _init_l_PersistentHashMap_maxCollisions();
lean::mark_persistent(l_PersistentHashMap_maxCollisions);
l_PersistentHashMap_mkEmptyEntriesArray___closed__1 = _init_l_PersistentHashMap_mkEmptyEntriesArray___closed__1();
lean::mark_persistent(l_PersistentHashMap_mkEmptyEntriesArray___closed__1);
l_PersistentHashMap_empty___closed__1 = _init_l_PersistentHashMap_empty___closed__1();
lean::mark_persistent(l_PersistentHashMap_empty___closed__1);
l_PersistentHashMap_empty___closed__2 = _init_l_PersistentHashMap_empty___closed__2();
lean::mark_persistent(l_PersistentHashMap_empty___closed__2);
l_PersistentHashMap_empty___closed__3 = _init_l_PersistentHashMap_empty___closed__3();
lean::mark_persistent(l_PersistentHashMap_empty___closed__3);
l_PersistentHashMap_mkCollisionNode___rarg___closed__1 = _init_l_PersistentHashMap_mkCollisionNode___rarg___closed__1();
lean::mark_persistent(l_PersistentHashMap_mkCollisionNode___rarg___closed__1);
l_PersistentHashMap_insertAux___main___rarg___closed__1 = _init_l_PersistentHashMap_insertAux___main___rarg___closed__1();
l_PersistentHashMap_insertAux___main___rarg___closed__2 = _init_l_PersistentHashMap_insertAux___main___rarg___closed__2();
l_PersistentHashMap_insertAux___main___rarg___closed__3 = _init_l_PersistentHashMap_insertAux___main___rarg___closed__3();
lean::mark_persistent(l_PersistentHashMap_insertAux___main___rarg___closed__3);
l_PersistentHashMap_stats___rarg___closed__1 = _init_l_PersistentHashMap_stats___rarg___closed__1();
lean::mark_persistent(l_PersistentHashMap_stats___rarg___closed__1);
l_PersistentHashMap_Stats_toString___closed__1 = _init_l_PersistentHashMap_Stats_toString___closed__1();
lean::mark_persistent(l_PersistentHashMap_Stats_toString___closed__1);
l_PersistentHashMap_Stats_toString___closed__2 = _init_l_PersistentHashMap_Stats_toString___closed__2();
lean::mark_persistent(l_PersistentHashMap_Stats_toString___closed__2);
l_PersistentHashMap_Stats_toString___closed__3 = _init_l_PersistentHashMap_Stats_toString___closed__3();
lean::mark_persistent(l_PersistentHashMap_Stats_toString___closed__3);
l_PersistentHashMap_Stats_toString___closed__4 = _init_l_PersistentHashMap_Stats_toString___closed__4();
lean::mark_persistent(l_PersistentHashMap_Stats_toString___closed__4);
l_PersistentHashMap_Stats_toString___closed__5 = _init_l_PersistentHashMap_Stats_toString___closed__5();
lean::mark_persistent(l_PersistentHashMap_Stats_toString___closed__5);
l_PersistentHashMap_HasToString___closed__1 = _init_l_PersistentHashMap_HasToString___closed__1();
lean::mark_persistent(l_PersistentHashMap_HasToString___closed__1);
l_PersistentHashMap_HasToString = _init_l_PersistentHashMap_HasToString();
lean::mark_persistent(l_PersistentHashMap_HasToString);
return w;
}
