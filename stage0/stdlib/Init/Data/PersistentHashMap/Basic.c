// Lean compiler output
// Module: Init.Data.PersistentHashMap.Basic
// Imports: Init.Data.Array Init.Data.Hashable
#include "runtime/lean.h"
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* l_PersistentHashMap_Inhabited___rarg(lean_object*, lean_object*);
size_t l_PersistentHashMap_div2Shift(size_t, size_t);
lean_object* l_PersistentHashMap_toList___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_eraseAux(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_foldl___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
extern uint8_t l_String_anyAux___main___at_String_all___spec__1___closed__1;
size_t l_USize_add(size_t, size_t);
lean_object* l_PersistentHashMap_insertAtCollisionNodeAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_Node_inhabited___closed__1;
lean_object* l_PersistentHashMap_find___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_PersistentHashMap_foldlMAux___main___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_findAtAux___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern uint8_t l_String_Iterator_extract___closed__1;
lean_object* l_PersistentHashMap_find(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_eraseAux___main___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_PersistentHashMap_insertAux___main___rarg___closed__2;
size_t l_PersistentHashMap_insertAux___main___rarg___closed__1;
lean_object* l_PersistentHashMap_collectStats___main(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_PersistentHashMap_insertAux___main___spec__1(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_insertAux___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_HasEmptyc___rarg(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_containsAux(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_PersistentHashMap_collectStats___main___spec__1(lean_object*, lean_object*);
uint8_t l_PersistentHashMap_containsAtAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_collectStats___main___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_stats___rarg(lean_object*);
lean_object* l_PersistentHashMap_collectStats___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_mkCollisionNode___rarg___closed__1;
lean_object* l_PersistentHashMap_find___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_sub(size_t, size_t);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
lean_object* l___private_Init_Util_1__mkPanicMessage(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_contains(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_foldlMAux(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_foldlM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_isUnaryNode___rarg___boxed(lean_object*);
lean_object* l_PersistentHashMap_mkEmptyEntriesArray___closed__1;
lean_object* l_PersistentHashMap_HasEmptyc(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_isUnaryNode___rarg(lean_object*);
lean_object* l_PersistentHashMap_HasToString___closed__1;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_foldlMAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_PersistentHashMap_toList___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_max(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_foldlM___at_PersistentHashMap_toList___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_getCollisionNodeSize___rarg___boxed(lean_object*);
lean_object* l_PersistentHashMap_isEmpty___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_containsAux___main___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_containsAux___main___rarg(lean_object*, lean_object*, size_t, lean_object*);
size_t l_USize_shiftRight(size_t, size_t);
lean_object* l_PersistentHashMap_foldlMAux___main___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_HasToString;
lean_object* l_PersistentHashMap_isUnaryEntries___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_Stats_toString___closed__5;
lean_object* l_PersistentHashMap_foldlMAux___main___at_PersistentHashMap_toList___spec__2___rarg___boxed(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_foldlMAux___main___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_Stats_toString___closed__3;
lean_object* l_PersistentHashMap_isUnaryEntries___main___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_insertAtCollisionNodeAux___main(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_foldlM___at_PersistentHashMap_toList___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_findAtAux___main___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_PersistentHashMap_shift;
size_t l_PersistentHashMap_mul2Shift(size_t, size_t);
lean_object* l_PersistentHashMap_foldl(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_mul2Shift___boxed(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_foldlM___at_PersistentHashMap_toList___spec__1___rarg___boxed(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_maxCollisions;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_Stats_toString___closed__2;
lean_object* l_PersistentHashMap_mod2Shift___boxed(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_Stats_toString___closed__4;
lean_object* l_PersistentHashMap_find_x21___rarg___closed__1;
lean_object* l_PersistentHashMap_insertAux___main___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_containsAtAux(lean_object*, lean_object*);
size_t l_PersistentHashMap_branching;
lean_object* l_PersistentHashMap_insert(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_find_x21___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_foldlMAux___main___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_foldlMAux___main___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_findAux___main___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_Stats_toString___closed__1;
lean_object* l_PersistentHashMap_foldlM(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_containsAtAux___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
lean_object* l_PersistentHashMap_insertAtCollisionNodeAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_foldlMAux___main(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_findD(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_insertAux___main___rarg___closed__3;
lean_object* l_PersistentHashMap_contains___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_shiftLeft(size_t, size_t);
lean_object* l_PersistentHashMap_insertAux___rarg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_empty___rarg___closed__1;
lean_object* l_PersistentHashMap_erase(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_empty___rarg___boxed(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_insert___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_insertAux___main(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_Inhabited(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_stats___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_empty___rarg___closed__2;
lean_object* l_PersistentHashMap_containsAux___rarg(lean_object*, lean_object*, size_t, lean_object*);
lean_object* l_PersistentHashMap_findAux___main(lean_object*, lean_object*);
size_t l_USize_mul(size_t, size_t);
lean_object* l_PersistentHashMap_foldlMAux___boxed(lean_object*, lean_object*, lean_object*);
size_t l_PersistentHashMap_mod2Shift(size_t, size_t);
lean_object* l_PersistentHashMap_empty___rarg(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
extern lean_object* l_Id_Monad;
size_t l_USize_land(size_t, size_t);
lean_object* l_PersistentHashMap_div2Shift___boxed(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_containsAtAux___main(lean_object*);
lean_object* l_PersistentHashMap_eraseAux___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_eraseAux___rarg(lean_object*, lean_object*, size_t, lean_object*);
lean_object* l_PersistentHashMap_mkCollisionNode(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_findAux___main___rarg(lean_object*, lean_object*, size_t, lean_object*);
lean_object* l_PersistentHashMap_Inhabited___rarg___boxed(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_findAtAux(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_PersistentHashMap_collectStats___main___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_findAux___rarg(lean_object*, lean_object*, size_t, lean_object*);
lean_object* l_PersistentHashMap_collectStats(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_PersistentHashMap_collectStats___main___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_findAux___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_PersistentHashMap_toList___spec__3(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_PersistentHashMap_toList___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_isEmpty___rarg___boxed(lean_object*);
lean_object* l_PersistentHashMap_Stats_toString(lean_object*);
lean_object* l_PersistentHashMap_isUnaryEntries___main___rarg(lean_object*, lean_object*, lean_object*);
uint8_t l_USize_decLe(size_t, size_t);
lean_object* l_panic(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_isUnaryEntries___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_empty(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_collectStats___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_isUnaryEntries___main(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_foldlMAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_indexOfAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_getCollisionNodeSize(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_findAtAux___main(lean_object*, lean_object*);
lean_object* l_Array_eraseIdx_x27___rarg(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_Node_inhabited(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_toList(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_containsAtAux___main___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_eraseAux___main(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_containsAux___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_isUnaryEntries(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_foldl___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_insertAux___main___rarg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_PersistentHashMap_toList___spec__4(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_findAux(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_getCollisionNodeSize___rarg(lean_object*);
lean_object* l_PersistentHashMap_collectStats___main___rarg___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_PersistentHashMap_isEmpty___rarg(lean_object*);
lean_object* l_PersistentHashMap_containsAux___main(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_find_x21___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_findD___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_PersistentHashMap_insertAux___main___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_find_x21___rarg___closed__2;
lean_object* l_PersistentHashMap_foldlM___at_PersistentHashMap_toList___spec__1___rarg(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_findAtAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_findD___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_foldlMAux___main___at_PersistentHashMap_toList___spec__2(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_foldlMAux___main___at_PersistentHashMap_toList___spec__2___rarg(lean_object*, lean_object*);
size_t l_PersistentHashMap_maxDepth;
lean_object* l_PersistentHashMap_find_x21(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_toList___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_insertAtCollisionNode___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_PersistentHashMap_toList___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_Entry_inhabited(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_insertAtCollisionNodeAux(lean_object*, lean_object*);
uint8_t l_PersistentHashMap_containsAtAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_findAtAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_find_x21___rarg___closed__3;
lean_object* l_Array_iterateMAux___main___at_PersistentHashMap_insertAux___main___spec__1___rarg(lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_foldlM___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_PersistentHashMap_toList___spec__4___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Bool_DecidableEq(uint8_t, uint8_t);
lean_object* l_PersistentHashMap_eraseAux___main___rarg(lean_object*, lean_object*, size_t, lean_object*);
lean_object* l_PersistentHashMap_isUnaryNode(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_insertAtCollisionNode(lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_PersistentHashMap_stats___rarg___closed__1;
lean_object* l_PersistentHashMap_stats___rarg___boxed(lean_object*);
lean_object* l_PersistentHashMap_stats(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_isEmpty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_insertAux(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_contains___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_mkCollisionNode___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_HasEmptyc___rarg___boxed(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_erase___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_foldlM___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_Entry_inhabited(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_box(2);
return x_4;
}
}
lean_object* _init_l_PersistentHashMap_Node_inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_empty___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_PersistentHashMap_Node_inhabited(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_PersistentHashMap_Node_inhabited___closed__1;
return x_3;
}
}
size_t _init_l_PersistentHashMap_shift() {
_start:
{
size_t x_1; 
x_1 = 5;
return x_1;
}
}
size_t _init_l_PersistentHashMap_branching() {
_start:
{
size_t x_1; 
x_1 = 32;
return x_1;
}
}
size_t _init_l_PersistentHashMap_maxDepth() {
_start:
{
size_t x_1; 
x_1 = 7;
return x_1;
}
}
lean_object* _init_l_PersistentHashMap_maxCollisions() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(4u);
return x_1;
}
}
lean_object* _init_l_PersistentHashMap_mkEmptyEntriesArray___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(2);
x_2 = lean_unsigned_to_nat(32u);
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
lean_object* l_PersistentHashMap_mkEmptyEntriesArray(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_PersistentHashMap_mkEmptyEntriesArray___closed__1;
return x_3;
}
}
lean_object* _init_l_PersistentHashMap_empty___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
lean_object* _init_l_PersistentHashMap_empty___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_PersistentHashMap_empty___rarg___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_PersistentHashMap_empty___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_PersistentHashMap_empty___rarg___closed__2;
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
lean_object* l_PersistentHashMap_empty(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_PersistentHashMap_empty___rarg___boxed), 2, 0);
return x_3;
}
}
lean_object* l_PersistentHashMap_empty___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_PersistentHashMap_empty___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_PersistentHashMap_HasEmptyc___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_PersistentHashMap_empty___rarg(x_1, x_2);
return x_3;
}
}
lean_object* l_PersistentHashMap_HasEmptyc(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_PersistentHashMap_HasEmptyc___rarg___boxed), 2, 0);
return x_3;
}
}
lean_object* l_PersistentHashMap_HasEmptyc___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_PersistentHashMap_HasEmptyc___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
uint8_t l_PersistentHashMap_isEmpty___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
return x_4;
}
}
lean_object* l_PersistentHashMap_isEmpty(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_PersistentHashMap_isEmpty___rarg___boxed), 1, 0);
return x_5;
}
}
lean_object* l_PersistentHashMap_isEmpty___rarg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_PersistentHashMap_isEmpty___rarg(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_PersistentHashMap_isEmpty___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_PersistentHashMap_isEmpty(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_PersistentHashMap_Inhabited___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_PersistentHashMap_empty___rarg___closed__2;
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
lean_object* l_PersistentHashMap_Inhabited(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_PersistentHashMap_Inhabited___rarg___boxed), 2, 0);
return x_3;
}
}
lean_object* l_PersistentHashMap_Inhabited___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_PersistentHashMap_Inhabited___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_PersistentHashMap_mkEmptyEntries(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_PersistentHashMap_empty___rarg___closed__2;
return x_3;
}
}
size_t l_PersistentHashMap_mul2Shift(size_t x_1, size_t x_2) {
_start:
{
size_t x_3; 
x_3 = x_1 << x_2;
return x_3;
}
}
lean_object* l_PersistentHashMap_mul2Shift___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_PersistentHashMap_mul2Shift(x_3, x_4);
x_6 = lean_box_usize(x_5);
return x_6;
}
}
size_t l_PersistentHashMap_div2Shift(size_t x_1, size_t x_2) {
_start:
{
size_t x_3; 
x_3 = x_1 >> x_2;
return x_3;
}
}
lean_object* l_PersistentHashMap_div2Shift___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_PersistentHashMap_div2Shift(x_3, x_4);
x_6 = lean_box_usize(x_5);
return x_6;
}
}
size_t l_PersistentHashMap_mod2Shift(size_t x_1, size_t x_2) {
_start:
{
size_t x_3; size_t x_4; size_t x_5; size_t x_6; 
x_3 = 1;
x_4 = x_3 << x_2;
x_5 = x_4 - x_3;
x_6 = x_1 & x_5;
return x_6;
}
}
lean_object* l_PersistentHashMap_mod2Shift___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_PersistentHashMap_mod2Shift(x_3, x_4);
x_6 = lean_box_usize(x_5);
return x_6;
}
}
lean_object* l_PersistentHashMap_insertAtCollisionNodeAux___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
x_8 = lean_array_get_size(x_6);
x_9 = lean_nat_dec_lt(x_3, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_3);
lean_dec(x_1);
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_2, 1);
lean_dec(x_11);
x_12 = lean_ctor_get(x_2, 0);
lean_dec(x_12);
x_13 = lean_array_push(x_6, x_4);
x_14 = lean_array_push(x_7, x_5);
lean_ctor_set(x_2, 1, x_14);
lean_ctor_set(x_2, 0, x_13);
return x_2;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_2);
x_15 = lean_array_push(x_6, x_4);
x_16 = lean_array_push(x_7, x_5);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; 
x_18 = lean_array_fget(x_6, x_3);
lean_inc(x_1);
lean_inc(x_4);
x_19 = lean_apply_2(x_1, x_4, x_18);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
x_21 = 1;
x_22 = l_Bool_DecidableEq(x_20, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_7);
lean_dec(x_6);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_3, x_23);
lean_dec(x_3);
x_3 = x_24;
goto _start;
}
else
{
uint8_t x_26; 
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_2);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_2, 1);
lean_dec(x_27);
x_28 = lean_ctor_get(x_2, 0);
lean_dec(x_28);
x_29 = lean_array_fset(x_6, x_3, x_4);
x_30 = lean_array_fset(x_7, x_3, x_5);
lean_dec(x_3);
lean_ctor_set(x_2, 1, x_30);
lean_ctor_set(x_2, 0, x_29);
return x_2;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_2);
x_31 = lean_array_fset(x_6, x_3, x_4);
x_32 = lean_array_fset(x_7, x_3, x_5);
lean_dec(x_3);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
}
lean_object* l_PersistentHashMap_insertAtCollisionNodeAux___main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_PersistentHashMap_insertAtCollisionNodeAux___main___rarg), 5, 0);
return x_3;
}
}
lean_object* l_PersistentHashMap_insertAtCollisionNodeAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_PersistentHashMap_insertAtCollisionNodeAux___main___rarg(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_PersistentHashMap_insertAtCollisionNodeAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_PersistentHashMap_insertAtCollisionNodeAux___rarg), 5, 0);
return x_3;
}
}
lean_object* l_PersistentHashMap_insertAtCollisionNode___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_PersistentHashMap_insertAtCollisionNodeAux___main___rarg(x_1, x_2, x_5, x_3, x_4);
return x_6;
}
}
lean_object* l_PersistentHashMap_insertAtCollisionNode(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_PersistentHashMap_insertAtCollisionNode___rarg), 4, 0);
return x_3;
}
}
lean_object* l_PersistentHashMap_getCollisionNodeSize___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_array_get_size(x_2);
return x_3;
}
}
lean_object* l_PersistentHashMap_getCollisionNodeSize(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_PersistentHashMap_getCollisionNodeSize___rarg___boxed), 1, 0);
return x_3;
}
}
lean_object* l_PersistentHashMap_getCollisionNodeSize___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_PersistentHashMap_getCollisionNodeSize___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* _init_l_PersistentHashMap_mkCollisionNode___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
lean_object* l_PersistentHashMap_mkCollisionNode___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = l_PersistentHashMap_mkCollisionNode___rarg___closed__1;
x_6 = lean_array_push(x_5, x_1);
x_7 = lean_array_push(x_6, x_3);
x_8 = lean_array_push(x_5, x_2);
x_9 = lean_array_push(x_8, x_4);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
lean_object* l_PersistentHashMap_mkCollisionNode(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_PersistentHashMap_mkCollisionNode___rarg), 4, 0);
return x_3;
}
}
lean_object* l_Array_iterateMAux___main___at_PersistentHashMap_insertAux___main___spec__1___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_get_size(x_6);
x_10 = lean_nat_dec_lt(x_7, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_11 = lean_array_fget(x_6, x_7);
x_12 = lean_array_fget(x_5, x_7);
lean_inc(x_2);
lean_inc(x_11);
x_13 = lean_apply_1(x_2, x_11);
x_14 = lean_unbox_usize(x_13);
lean_dec(x_13);
x_15 = 1;
x_16 = x_3 - x_15;
x_17 = 5;
x_18 = x_17 * x_16;
x_19 = x_14 >> x_18;
lean_inc(x_2);
lean_inc(x_1);
x_20 = l_PersistentHashMap_insertAux___main___rarg(x_1, x_2, x_8, x_19, x_3, x_11, x_12);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_7, x_21);
lean_dec(x_7);
x_7 = x_22;
x_8 = x_20;
goto _start;
}
}
}
lean_object* l_Array_iterateMAux___main___at_PersistentHashMap_insertAux___main___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_iterateMAux___main___at_PersistentHashMap_insertAux___main___spec__1___rarg___boxed), 8, 0);
return x_3;
}
}
size_t _init_l_PersistentHashMap_insertAux___main___rarg___closed__1() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = 5;
x_3 = x_1 << x_2;
return x_3;
}
}
size_t _init_l_PersistentHashMap_insertAux___main___rarg___closed__2() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = l_PersistentHashMap_insertAux___main___rarg___closed__1;
x_3 = x_2 - x_1;
return x_3;
}
}
lean_object* _init_l_PersistentHashMap_insertAux___main___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return x_1;
}
}
lean_object* l_PersistentHashMap_insertAux___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_3);
if (x_8 == 0)
{
lean_object* x_9; size_t x_10; size_t x_11; size_t x_12; size_t x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = 1;
x_11 = 5;
x_12 = l_PersistentHashMap_insertAux___main___rarg___closed__2;
x_13 = x_4 & x_12;
x_14 = lean_usize_to_nat(x_13);
x_15 = lean_array_get_size(x_9);
x_16 = lean_nat_dec_lt(x_14, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_array_fget(x_9, x_14);
x_18 = lean_box(2);
x_19 = lean_array_fset(x_9, x_14, x_18);
switch (lean_obj_tag(x_17)) {
case 0:
{
uint8_t x_20; 
lean_dec(x_2);
x_20 = !lean_is_exclusive(x_17);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; 
x_21 = lean_ctor_get(x_17, 0);
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_inc(x_6);
x_23 = lean_apply_2(x_1, x_6, x_21);
x_24 = lean_unbox(x_23);
lean_dec(x_23);
x_25 = 1;
x_26 = l_Bool_DecidableEq(x_24, x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_free_object(x_17);
x_27 = l_PersistentHashMap_mkCollisionNode___rarg(x_21, x_22, x_6, x_7);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_array_fset(x_19, x_14, x_28);
lean_dec(x_14);
lean_ctor_set(x_3, 0, x_29);
return x_3;
}
else
{
lean_object* x_30; 
lean_dec(x_22);
lean_dec(x_21);
lean_ctor_set(x_17, 1, x_7);
lean_ctor_set(x_17, 0, x_6);
x_30 = lean_array_fset(x_19, x_14, x_17);
lean_dec(x_14);
lean_ctor_set(x_3, 0, x_30);
return x_3;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; 
x_31 = lean_ctor_get(x_17, 0);
x_32 = lean_ctor_get(x_17, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_17);
lean_inc(x_31);
lean_inc(x_6);
x_33 = lean_apply_2(x_1, x_6, x_31);
x_34 = lean_unbox(x_33);
lean_dec(x_33);
x_35 = 1;
x_36 = l_Bool_DecidableEq(x_34, x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = l_PersistentHashMap_mkCollisionNode___rarg(x_31, x_32, x_6, x_7);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_39 = lean_array_fset(x_19, x_14, x_38);
lean_dec(x_14);
lean_ctor_set(x_3, 0, x_39);
return x_3;
}
else
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_32);
lean_dec(x_31);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_6);
lean_ctor_set(x_40, 1, x_7);
x_41 = lean_array_fset(x_19, x_14, x_40);
lean_dec(x_14);
lean_ctor_set(x_3, 0, x_41);
return x_3;
}
}
}
case 1:
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_17);
if (x_42 == 0)
{
lean_object* x_43; size_t x_44; size_t x_45; lean_object* x_46; lean_object* x_47; 
x_43 = lean_ctor_get(x_17, 0);
x_44 = x_4 >> x_11;
x_45 = x_5 + x_10;
x_46 = l_PersistentHashMap_insertAux___main___rarg(x_1, x_2, x_43, x_44, x_45, x_6, x_7);
lean_ctor_set(x_17, 0, x_46);
x_47 = lean_array_fset(x_19, x_14, x_17);
lean_dec(x_14);
lean_ctor_set(x_3, 0, x_47);
return x_3;
}
else
{
lean_object* x_48; size_t x_49; size_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_48 = lean_ctor_get(x_17, 0);
lean_inc(x_48);
lean_dec(x_17);
x_49 = x_4 >> x_11;
x_50 = x_5 + x_10;
x_51 = l_PersistentHashMap_insertAux___main___rarg(x_1, x_2, x_48, x_49, x_50, x_6, x_7);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_53 = lean_array_fset(x_19, x_14, x_52);
lean_dec(x_14);
lean_ctor_set(x_3, 0, x_53);
return x_3;
}
}
default: 
{
lean_object* x_54; lean_object* x_55; 
lean_dec(x_2);
lean_dec(x_1);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_6);
lean_ctor_set(x_54, 1, x_7);
x_55 = lean_array_fset(x_19, x_14, x_54);
lean_dec(x_14);
lean_ctor_set(x_3, 0, x_55);
return x_3;
}
}
}
}
else
{
lean_object* x_56; size_t x_57; size_t x_58; size_t x_59; size_t x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_56 = lean_ctor_get(x_3, 0);
lean_inc(x_56);
lean_dec(x_3);
x_57 = 1;
x_58 = 5;
x_59 = l_PersistentHashMap_insertAux___main___rarg___closed__2;
x_60 = x_4 & x_59;
x_61 = lean_usize_to_nat(x_60);
x_62 = lean_array_get_size(x_56);
x_63 = lean_nat_dec_lt(x_61, x_62);
lean_dec(x_62);
if (x_63 == 0)
{
lean_object* x_64; 
lean_dec(x_61);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_64 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_64, 0, x_56);
return x_64;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_array_fget(x_56, x_61);
x_66 = lean_box(2);
x_67 = lean_array_fset(x_56, x_61, x_66);
switch (lean_obj_tag(x_65)) {
case 0:
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; uint8_t x_73; uint8_t x_74; 
lean_dec(x_2);
x_68 = lean_ctor_get(x_65, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_65, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_70 = x_65;
} else {
 lean_dec_ref(x_65);
 x_70 = lean_box(0);
}
lean_inc(x_68);
lean_inc(x_6);
x_71 = lean_apply_2(x_1, x_6, x_68);
x_72 = lean_unbox(x_71);
lean_dec(x_71);
x_73 = 1;
x_74 = l_Bool_DecidableEq(x_72, x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_70);
x_75 = l_PersistentHashMap_mkCollisionNode___rarg(x_68, x_69, x_6, x_7);
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_75);
x_77 = lean_array_fset(x_67, x_61, x_76);
lean_dec(x_61);
x_78 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_78, 0, x_77);
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_69);
lean_dec(x_68);
if (lean_is_scalar(x_70)) {
 x_79 = lean_alloc_ctor(0, 2, 0);
} else {
 x_79 = x_70;
}
lean_ctor_set(x_79, 0, x_6);
lean_ctor_set(x_79, 1, x_7);
x_80 = lean_array_fset(x_67, x_61, x_79);
lean_dec(x_61);
x_81 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_81, 0, x_80);
return x_81;
}
}
case 1:
{
lean_object* x_82; lean_object* x_83; size_t x_84; size_t x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_82 = lean_ctor_get(x_65, 0);
lean_inc(x_82);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 x_83 = x_65;
} else {
 lean_dec_ref(x_65);
 x_83 = lean_box(0);
}
x_84 = x_4 >> x_58;
x_85 = x_5 + x_57;
x_86 = l_PersistentHashMap_insertAux___main___rarg(x_1, x_2, x_82, x_84, x_85, x_6, x_7);
if (lean_is_scalar(x_83)) {
 x_87 = lean_alloc_ctor(1, 1, 0);
} else {
 x_87 = x_83;
}
lean_ctor_set(x_87, 0, x_86);
x_88 = lean_array_fset(x_67, x_61, x_87);
lean_dec(x_61);
x_89 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_89, 0, x_88);
return x_89;
}
default: 
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_2);
lean_dec(x_1);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_6);
lean_ctor_set(x_90, 1, x_7);
x_91 = lean_array_fset(x_67, x_61, x_90);
lean_dec(x_61);
x_92 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_92, 0, x_91);
return x_92;
}
}
}
}
}
else
{
lean_object* x_93; lean_object* x_94; uint8_t x_95; size_t x_103; uint8_t x_104; 
x_93 = lean_unsigned_to_nat(0u);
lean_inc(x_1);
x_94 = l_PersistentHashMap_insertAtCollisionNodeAux___main___rarg(x_1, x_3, x_93, x_6, x_7);
x_103 = 7;
x_104 = x_103 <= x_5;
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; uint8_t x_107; 
x_105 = l_PersistentHashMap_getCollisionNodeSize___rarg(x_94);
x_106 = lean_unsigned_to_nat(4u);
x_107 = lean_nat_dec_lt(x_105, x_106);
lean_dec(x_105);
x_95 = x_107;
goto block_102;
}
else
{
uint8_t x_108; 
x_108 = 1;
x_95 = x_108;
goto block_102;
}
block_102:
{
uint8_t x_96; uint8_t x_97; 
x_96 = 1;
x_97 = l_Bool_DecidableEq(x_95, x_96);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_98 = lean_ctor_get(x_94, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_94, 1);
lean_inc(x_99);
lean_dec(x_94);
x_100 = l_PersistentHashMap_insertAux___main___rarg___closed__3;
x_101 = l_Array_iterateMAux___main___at_PersistentHashMap_insertAux___main___spec__1___rarg(x_1, x_2, x_5, x_98, x_99, x_98, x_93, x_100);
lean_dec(x_99);
lean_dec(x_98);
return x_101;
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_94;
}
}
}
}
}
lean_object* l_PersistentHashMap_insertAux___main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_PersistentHashMap_insertAux___main___rarg___boxed), 7, 0);
return x_3;
}
}
lean_object* l_Array_iterateMAux___main___at_PersistentHashMap_insertAux___main___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; lean_object* x_10; 
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l_Array_iterateMAux___main___at_PersistentHashMap_insertAux___main___spec__1___rarg(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_10;
}
}
lean_object* l_PersistentHashMap_insertAux___main___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_10 = l_PersistentHashMap_insertAux___main___rarg(x_1, x_2, x_3, x_8, x_9, x_6, x_7);
return x_10;
}
}
lean_object* l_PersistentHashMap_insertAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_PersistentHashMap_insertAux___main___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
lean_object* l_PersistentHashMap_insertAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_PersistentHashMap_insertAux___rarg___boxed), 7, 0);
return x_3;
}
}
lean_object* l_PersistentHashMap_insertAux___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_10 = l_PersistentHashMap_insertAux___rarg(x_1, x_2, x_3, x_8, x_9, x_6, x_7);
return x_10;
}
}
lean_object* l_PersistentHashMap_insert___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_2);
lean_inc(x_4);
x_9 = lean_apply_1(x_2, x_4);
x_10 = lean_unbox_usize(x_9);
lean_dec(x_9);
x_11 = 1;
x_12 = l_PersistentHashMap_insertAux___main___rarg(x_1, x_2, x_7, x_10, x_11, x_4, x_5);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_8, x_13);
lean_dec(x_8);
lean_ctor_set(x_3, 1, x_14);
lean_ctor_set(x_3, 0, x_12);
return x_3;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_15 = lean_ctor_get(x_3, 0);
x_16 = lean_ctor_get(x_3, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_3);
lean_inc(x_2);
lean_inc(x_4);
x_17 = lean_apply_1(x_2, x_4);
x_18 = lean_unbox_usize(x_17);
lean_dec(x_17);
x_19 = 1;
x_20 = l_PersistentHashMap_insertAux___main___rarg(x_1, x_2, x_15, x_18, x_19, x_4, x_5);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_16, x_21);
lean_dec(x_16);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
lean_object* l_PersistentHashMap_insert(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_PersistentHashMap_insert___rarg), 5, 0);
return x_3;
}
}
lean_object* l_PersistentHashMap_findAtAux___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_9 = lean_box(0);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; 
x_10 = lean_array_fget(x_2, x_5);
lean_inc(x_1);
lean_inc(x_6);
x_11 = lean_apply_2(x_1, x_6, x_10);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
x_13 = 1;
x_14 = l_Bool_DecidableEq(x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_5, x_15);
lean_dec(x_5);
x_4 = lean_box(0);
x_5 = x_16;
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_6);
lean_dec(x_1);
x_18 = lean_array_fget(x_3, x_5);
lean_dec(x_5);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
}
}
lean_object* l_PersistentHashMap_findAtAux___main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_PersistentHashMap_findAtAux___main___rarg___boxed), 6, 0);
return x_3;
}
}
lean_object* l_PersistentHashMap_findAtAux___main___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_PersistentHashMap_findAtAux___main___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_PersistentHashMap_findAtAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_PersistentHashMap_findAtAux___main___rarg(x_1, x_2, x_3, lean_box(0), x_5, x_6);
return x_7;
}
}
lean_object* l_PersistentHashMap_findAtAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_PersistentHashMap_findAtAux___rarg___boxed), 6, 0);
return x_3;
}
}
lean_object* l_PersistentHashMap_findAtAux___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_PersistentHashMap_findAtAux___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_PersistentHashMap_findAux___main___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; size_t x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = 5;
x_7 = l_PersistentHashMap_insertAux___main___rarg___closed__2;
x_8 = x_3 & x_7;
x_9 = lean_usize_to_nat(x_8);
x_10 = lean_box(2);
x_11 = lean_array_get(x_10, x_5, x_9);
lean_dec(x_9);
switch (lean_obj_tag(x_11)) {
case 0:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_apply_2(x_1, x_4, x_12);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
x_16 = 1;
x_17 = l_Bool_DecidableEq(x_15, x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_13);
x_18 = lean_box(0);
return x_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_13);
return x_19;
}
}
case 1:
{
lean_object* x_20; size_t x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_11, 0);
lean_inc(x_20);
lean_dec(x_11);
x_21 = x_3 >> x_6;
x_22 = l_PersistentHashMap_findAux___main___rarg(x_1, x_20, x_21, x_4);
lean_dec(x_20);
return x_22;
}
default: 
{
lean_object* x_23; 
lean_dec(x_4);
lean_dec(x_1);
x_23 = lean_box(0);
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_2, 0);
x_25 = lean_ctor_get(x_2, 1);
x_26 = lean_unsigned_to_nat(0u);
x_27 = l_PersistentHashMap_findAtAux___main___rarg(x_1, x_24, x_25, lean_box(0), x_26, x_4);
return x_27;
}
}
}
lean_object* l_PersistentHashMap_findAux___main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_PersistentHashMap_findAux___main___rarg___boxed), 4, 0);
return x_3;
}
}
lean_object* l_PersistentHashMap_findAux___main___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_PersistentHashMap_findAux___main___rarg(x_1, x_2, x_5, x_4);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_PersistentHashMap_findAux___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_PersistentHashMap_findAux___main___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_PersistentHashMap_findAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_PersistentHashMap_findAux___rarg___boxed), 4, 0);
return x_3;
}
}
lean_object* l_PersistentHashMap_findAux___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_PersistentHashMap_findAux___rarg(x_1, x_2, x_5, x_4);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_PersistentHashMap_find___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; size_t x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_6 = lean_apply_1(x_2, x_4);
x_7 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_8 = l_PersistentHashMap_findAux___main___rarg(x_1, x_5, x_7, x_4);
return x_8;
}
}
lean_object* l_PersistentHashMap_find(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_PersistentHashMap_find___rarg___boxed), 4, 0);
return x_3;
}
}
lean_object* l_PersistentHashMap_find___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_PersistentHashMap_find___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_PersistentHashMap_findD___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_PersistentHashMap_find___rarg(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_inc(x_5);
return x_5;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
return x_7;
}
}
}
lean_object* l_PersistentHashMap_findD(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_PersistentHashMap_findD___rarg___boxed), 5, 0);
return x_3;
}
}
lean_object* l_PersistentHashMap_findD___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_PersistentHashMap_findD___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_3);
return x_6;
}
}
lean_object* _init_l_PersistentHashMap_find_x21___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Init.Data.PersistentHashMap.Basic");
return x_1;
}
}
lean_object* _init_l_PersistentHashMap_find_x21___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("key is not in the map");
return x_1;
}
}
lean_object* _init_l_PersistentHashMap_find_x21___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_PersistentHashMap_find_x21___rarg___closed__1;
x_2 = lean_unsigned_to_nat(164u);
x_3 = lean_unsigned_to_nat(12u);
x_4 = l_PersistentHashMap_find_x21___rarg___closed__2;
x_5 = l___private_Init_Util_1__mkPanicMessage(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_PersistentHashMap_find_x21___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_PersistentHashMap_find___rarg(x_1, x_2, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_PersistentHashMap_find_x21___rarg___closed__3;
x_8 = lean_panic_fn(x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_3);
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
return x_9;
}
}
}
lean_object* l_PersistentHashMap_find_x21(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_PersistentHashMap_find_x21___rarg___boxed), 5, 0);
return x_3;
}
}
lean_object* l_PersistentHashMap_find_x21___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_PersistentHashMap_find_x21___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
uint8_t l_PersistentHashMap_containsAtAux___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; 
x_8 = lean_array_fget(x_2, x_3);
lean_inc(x_1);
lean_inc(x_4);
x_9 = lean_apply_2(x_1, x_4, x_8);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
x_11 = 1;
x_12 = l_Bool_DecidableEq(x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_3, x_13);
lean_dec(x_3);
x_3 = x_14;
goto _start;
}
else
{
uint8_t x_16; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_16 = 1;
return x_16;
}
}
}
}
lean_object* l_PersistentHashMap_containsAtAux___main(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_PersistentHashMap_containsAtAux___main___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_PersistentHashMap_containsAtAux___main___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_PersistentHashMap_containsAtAux___main___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
x_6 = lean_box(x_5);
return x_6;
}
}
uint8_t l_PersistentHashMap_containsAtAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = l_PersistentHashMap_containsAtAux___main___rarg(x_1, x_2, x_5, x_6);
return x_7;
}
}
lean_object* l_PersistentHashMap_containsAtAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_PersistentHashMap_containsAtAux___rarg___boxed), 6, 0);
return x_3;
}
}
lean_object* l_PersistentHashMap_containsAtAux___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_PersistentHashMap_containsAtAux___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
x_8 = lean_box(x_7);
return x_8;
}
}
lean_object* l_PersistentHashMap_containsAux___main___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; size_t x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = 5;
x_7 = l_PersistentHashMap_insertAux___main___rarg___closed__2;
x_8 = x_3 & x_7;
x_9 = lean_usize_to_nat(x_8);
x_10 = lean_box(2);
x_11 = lean_array_get(x_10, x_5, x_9);
lean_dec(x_9);
switch (lean_obj_tag(x_11)) {
case 0:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_apply_2(x_1, x_4, x_12);
return x_13;
}
case 1:
{
lean_object* x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
lean_dec(x_11);
x_15 = x_3 >> x_6;
x_16 = l_PersistentHashMap_containsAux___main___rarg(x_1, x_14, x_15, x_4);
lean_dec(x_14);
return x_16;
}
default: 
{
uint8_t x_17; lean_object* x_18; 
lean_dec(x_4);
lean_dec(x_1);
x_17 = 0;
x_18 = lean_box(x_17);
return x_18;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_2, 0);
x_20 = lean_unsigned_to_nat(0u);
x_21 = l_PersistentHashMap_containsAtAux___main___rarg(x_1, x_19, x_20, x_4);
x_22 = lean_box(x_21);
return x_22;
}
}
}
lean_object* l_PersistentHashMap_containsAux___main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_PersistentHashMap_containsAux___main___rarg___boxed), 4, 0);
return x_3;
}
}
lean_object* l_PersistentHashMap_containsAux___main___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_PersistentHashMap_containsAux___main___rarg(x_1, x_2, x_5, x_4);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_PersistentHashMap_containsAux___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_PersistentHashMap_containsAux___main___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_PersistentHashMap_containsAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_PersistentHashMap_containsAux___rarg___boxed), 4, 0);
return x_3;
}
}
lean_object* l_PersistentHashMap_containsAux___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_PersistentHashMap_containsAux___rarg(x_1, x_2, x_5, x_4);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_PersistentHashMap_contains___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; size_t x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_6 = lean_apply_1(x_2, x_4);
x_7 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_8 = l_PersistentHashMap_containsAux___main___rarg(x_1, x_5, x_7, x_4);
return x_8;
}
}
lean_object* l_PersistentHashMap_contains(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_PersistentHashMap_contains___rarg___boxed), 4, 0);
return x_3;
}
}
lean_object* l_PersistentHashMap_contains___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_PersistentHashMap_contains___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_PersistentHashMap_isUnaryEntries___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec(x_2);
return x_3;
}
else
{
lean_object* x_6; 
x_6 = lean_array_fget(x_1, x_2);
switch (lean_obj_tag(x_6)) {
case 0:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_2, x_9);
lean_dec(x_2);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_8);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_2 = x_10;
x_3 = x_12;
goto _start;
}
else
{
lean_object* x_14; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_box(0);
return x_14;
}
}
case 1:
{
lean_object* x_15; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_15 = lean_box(0);
return x_15;
}
default: 
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_2, x_16);
lean_dec(x_2);
x_2 = x_17;
goto _start;
}
}
}
}
}
lean_object* l_PersistentHashMap_isUnaryEntries___main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_PersistentHashMap_isUnaryEntries___main___rarg___boxed), 3, 0);
return x_3;
}
}
lean_object* l_PersistentHashMap_isUnaryEntries___main___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_PersistentHashMap_isUnaryEntries___main___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_PersistentHashMap_isUnaryEntries___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_PersistentHashMap_isUnaryEntries___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_PersistentHashMap_isUnaryEntries(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_PersistentHashMap_isUnaryEntries___rarg___boxed), 3, 0);
return x_3;
}
}
lean_object* l_PersistentHashMap_isUnaryEntries___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_PersistentHashMap_isUnaryEntries___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_PersistentHashMap_isUnaryNode___rarg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_box(0);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_PersistentHashMap_isUnaryEntries___main___rarg(x_2, x_4, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_array_get_size(x_6);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_dec_eq(x_9, x_8);
lean_dec(x_8);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_box(0);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_fget(x_6, x_12);
x_14 = lean_array_fget(x_7, x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
}
lean_object* l_PersistentHashMap_isUnaryNode(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_PersistentHashMap_isUnaryNode___rarg___boxed), 1, 0);
return x_3;
}
}
lean_object* l_PersistentHashMap_isUnaryNode___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_PersistentHashMap_isUnaryNode___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_PersistentHashMap_eraseAux___main___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; size_t x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = 5;
x_7 = l_PersistentHashMap_insertAux___main___rarg___closed__2;
x_8 = x_3 & x_7;
x_9 = lean_usize_to_nat(x_8);
x_10 = lean_box(2);
x_11 = lean_array_get(x_10, x_5, x_9);
switch (lean_obj_tag(x_11)) {
case 0:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_apply_2(x_1, x_4, x_12);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
x_15 = 1;
x_16 = l_Bool_DecidableEq(x_14, x_15);
if (x_16 == 0)
{
uint8_t x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_9);
lean_dec(x_5);
x_17 = 0;
x_18 = lean_box(x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_2);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_2);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_2, 0);
lean_dec(x_21);
x_22 = lean_array_set(x_5, x_9, x_10);
lean_dec(x_9);
lean_ctor_set(x_2, 0, x_22);
x_23 = lean_box(x_15);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_2);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_2);
x_25 = lean_array_set(x_5, x_9, x_10);
lean_dec(x_9);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_box(x_15);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
case 1:
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_11);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; size_t x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_30 = lean_ctor_get(x_11, 0);
x_31 = lean_array_set(x_5, x_9, x_10);
x_32 = x_3 >> x_6;
x_33 = l_PersistentHashMap_eraseAux___main___rarg(x_1, x_30, x_32, x_4);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
x_35 = lean_unbox(x_34);
lean_dec(x_34);
if (x_35 == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_33);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_ctor_get(x_33, 0);
x_38 = lean_ctor_get(x_33, 1);
lean_dec(x_38);
x_39 = l_String_Iterator_extract___closed__1;
if (x_39 == 0)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_2);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_2, 0);
lean_dec(x_41);
x_42 = l_PersistentHashMap_isUnaryNode___rarg(x_37);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; uint8_t x_44; lean_object* x_45; 
lean_ctor_set(x_11, 0, x_37);
x_43 = lean_array_set(x_31, x_9, x_11);
lean_dec(x_9);
lean_ctor_set(x_2, 0, x_43);
x_44 = 1;
x_45 = lean_box(x_44);
lean_ctor_set(x_33, 1, x_45);
lean_ctor_set(x_33, 0, x_2);
return x_33;
}
else
{
lean_object* x_46; uint8_t x_47; 
lean_free_object(x_33);
lean_dec(x_37);
lean_free_object(x_11);
x_46 = lean_ctor_get(x_42, 0);
lean_inc(x_46);
lean_dec(x_42);
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; 
x_48 = lean_ctor_get(x_46, 0);
x_49 = lean_ctor_get(x_46, 1);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_array_set(x_31, x_9, x_50);
lean_dec(x_9);
lean_ctor_set(x_2, 0, x_51);
x_52 = 1;
x_53 = lean_box(x_52);
lean_ctor_set(x_46, 1, x_53);
lean_ctor_set(x_46, 0, x_2);
return x_46;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; 
x_54 = lean_ctor_get(x_46, 0);
x_55 = lean_ctor_get(x_46, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_46);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_array_set(x_31, x_9, x_56);
lean_dec(x_9);
lean_ctor_set(x_2, 0, x_57);
x_58 = 1;
x_59 = lean_box(x_58);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_2);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
lean_object* x_61; 
lean_dec(x_2);
x_61 = l_PersistentHashMap_isUnaryNode___rarg(x_37);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; 
lean_ctor_set(x_11, 0, x_37);
x_62 = lean_array_set(x_31, x_9, x_11);
lean_dec(x_9);
x_63 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_63, 0, x_62);
x_64 = 1;
x_65 = lean_box(x_64);
lean_ctor_set(x_33, 1, x_65);
lean_ctor_set(x_33, 0, x_63);
return x_33;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; lean_object* x_75; 
lean_free_object(x_33);
lean_dec(x_37);
lean_free_object(x_11);
x_66 = lean_ctor_get(x_61, 0);
lean_inc(x_66);
lean_dec(x_61);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_69 = x_66;
} else {
 lean_dec_ref(x_66);
 x_69 = lean_box(0);
}
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_67);
lean_ctor_set(x_70, 1, x_68);
x_71 = lean_array_set(x_31, x_9, x_70);
lean_dec(x_9);
x_72 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_72, 0, x_71);
x_73 = 1;
x_74 = lean_box(x_73);
if (lean_is_scalar(x_69)) {
 x_75 = lean_alloc_ctor(0, 2, 0);
} else {
 x_75 = x_69;
}
lean_ctor_set(x_75, 0, x_72);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
else
{
uint8_t x_76; lean_object* x_77; 
lean_dec(x_37);
lean_dec(x_31);
lean_free_object(x_11);
lean_dec(x_9);
x_76 = 0;
x_77 = lean_box(x_76);
lean_ctor_set(x_33, 1, x_77);
lean_ctor_set(x_33, 0, x_2);
return x_33;
}
}
else
{
lean_object* x_78; uint8_t x_79; 
x_78 = lean_ctor_get(x_33, 0);
lean_inc(x_78);
lean_dec(x_33);
x_79 = l_String_Iterator_extract___closed__1;
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; 
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 x_80 = x_2;
} else {
 lean_dec_ref(x_2);
 x_80 = lean_box(0);
}
x_81 = l_PersistentHashMap_isUnaryNode___rarg(x_78);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; lean_object* x_85; lean_object* x_86; 
lean_ctor_set(x_11, 0, x_78);
x_82 = lean_array_set(x_31, x_9, x_11);
lean_dec(x_9);
if (lean_is_scalar(x_80)) {
 x_83 = lean_alloc_ctor(0, 1, 0);
} else {
 x_83 = x_80;
}
lean_ctor_set(x_83, 0, x_82);
x_84 = 1;
x_85 = lean_box(x_84);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_83);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_78);
lean_free_object(x_11);
x_87 = lean_ctor_get(x_81, 0);
lean_inc(x_87);
lean_dec(x_81);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_90 = x_87;
} else {
 lean_dec_ref(x_87);
 x_90 = lean_box(0);
}
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_88);
lean_ctor_set(x_91, 1, x_89);
x_92 = lean_array_set(x_31, x_9, x_91);
lean_dec(x_9);
if (lean_is_scalar(x_80)) {
 x_93 = lean_alloc_ctor(0, 1, 0);
} else {
 x_93 = x_80;
}
lean_ctor_set(x_93, 0, x_92);
x_94 = 1;
x_95 = lean_box(x_94);
if (lean_is_scalar(x_90)) {
 x_96 = lean_alloc_ctor(0, 2, 0);
} else {
 x_96 = x_90;
}
lean_ctor_set(x_96, 0, x_93);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
else
{
uint8_t x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_78);
lean_dec(x_31);
lean_free_object(x_11);
lean_dec(x_9);
x_97 = 0;
x_98 = lean_box(x_97);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_2);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
else
{
uint8_t x_100; 
x_100 = !lean_is_exclusive(x_33);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_101 = lean_ctor_get(x_33, 0);
x_102 = lean_ctor_get(x_33, 1);
lean_dec(x_102);
x_103 = l_String_anyAux___main___at_String_all___spec__1___closed__1;
if (x_103 == 0)
{
uint8_t x_104; 
x_104 = !lean_is_exclusive(x_2);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; 
x_105 = lean_ctor_get(x_2, 0);
lean_dec(x_105);
x_106 = l_PersistentHashMap_isUnaryNode___rarg(x_101);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; uint8_t x_108; lean_object* x_109; 
lean_ctor_set(x_11, 0, x_101);
x_107 = lean_array_set(x_31, x_9, x_11);
lean_dec(x_9);
lean_ctor_set(x_2, 0, x_107);
x_108 = 1;
x_109 = lean_box(x_108);
lean_ctor_set(x_33, 1, x_109);
lean_ctor_set(x_33, 0, x_2);
return x_33;
}
else
{
lean_object* x_110; uint8_t x_111; 
lean_free_object(x_33);
lean_dec(x_101);
lean_free_object(x_11);
x_110 = lean_ctor_get(x_106, 0);
lean_inc(x_110);
lean_dec(x_106);
x_111 = !lean_is_exclusive(x_110);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; lean_object* x_117; 
x_112 = lean_ctor_get(x_110, 0);
x_113 = lean_ctor_get(x_110, 1);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
x_115 = lean_array_set(x_31, x_9, x_114);
lean_dec(x_9);
lean_ctor_set(x_2, 0, x_115);
x_116 = 1;
x_117 = lean_box(x_116);
lean_ctor_set(x_110, 1, x_117);
lean_ctor_set(x_110, 0, x_2);
return x_110;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; lean_object* x_123; lean_object* x_124; 
x_118 = lean_ctor_get(x_110, 0);
x_119 = lean_ctor_get(x_110, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_110);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
x_121 = lean_array_set(x_31, x_9, x_120);
lean_dec(x_9);
lean_ctor_set(x_2, 0, x_121);
x_122 = 1;
x_123 = lean_box(x_122);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_2);
lean_ctor_set(x_124, 1, x_123);
return x_124;
}
}
}
else
{
lean_object* x_125; 
lean_dec(x_2);
x_125 = l_PersistentHashMap_isUnaryNode___rarg(x_101);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; uint8_t x_128; lean_object* x_129; 
lean_ctor_set(x_11, 0, x_101);
x_126 = lean_array_set(x_31, x_9, x_11);
lean_dec(x_9);
x_127 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_127, 0, x_126);
x_128 = 1;
x_129 = lean_box(x_128);
lean_ctor_set(x_33, 1, x_129);
lean_ctor_set(x_33, 0, x_127);
return x_33;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; lean_object* x_138; lean_object* x_139; 
lean_free_object(x_33);
lean_dec(x_101);
lean_free_object(x_11);
x_130 = lean_ctor_get(x_125, 0);
lean_inc(x_130);
lean_dec(x_125);
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_133 = x_130;
} else {
 lean_dec_ref(x_130);
 x_133 = lean_box(0);
}
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_131);
lean_ctor_set(x_134, 1, x_132);
x_135 = lean_array_set(x_31, x_9, x_134);
lean_dec(x_9);
x_136 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_136, 0, x_135);
x_137 = 1;
x_138 = lean_box(x_137);
if (lean_is_scalar(x_133)) {
 x_139 = lean_alloc_ctor(0, 2, 0);
} else {
 x_139 = x_133;
}
lean_ctor_set(x_139, 0, x_136);
lean_ctor_set(x_139, 1, x_138);
return x_139;
}
}
}
else
{
uint8_t x_140; lean_object* x_141; 
lean_dec(x_101);
lean_dec(x_31);
lean_free_object(x_11);
lean_dec(x_9);
x_140 = 0;
x_141 = lean_box(x_140);
lean_ctor_set(x_33, 1, x_141);
lean_ctor_set(x_33, 0, x_2);
return x_33;
}
}
else
{
lean_object* x_142; uint8_t x_143; 
x_142 = lean_ctor_get(x_33, 0);
lean_inc(x_142);
lean_dec(x_33);
x_143 = l_String_anyAux___main___at_String_all___spec__1___closed__1;
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; 
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 x_144 = x_2;
} else {
 lean_dec_ref(x_2);
 x_144 = lean_box(0);
}
x_145 = l_PersistentHashMap_isUnaryNode___rarg(x_142);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; lean_object* x_147; uint8_t x_148; lean_object* x_149; lean_object* x_150; 
lean_ctor_set(x_11, 0, x_142);
x_146 = lean_array_set(x_31, x_9, x_11);
lean_dec(x_9);
if (lean_is_scalar(x_144)) {
 x_147 = lean_alloc_ctor(0, 1, 0);
} else {
 x_147 = x_144;
}
lean_ctor_set(x_147, 0, x_146);
x_148 = 1;
x_149 = lean_box(x_148);
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_147);
lean_ctor_set(x_150, 1, x_149);
return x_150;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; uint8_t x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_142);
lean_free_object(x_11);
x_151 = lean_ctor_get(x_145, 0);
lean_inc(x_151);
lean_dec(x_145);
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_151, 1);
lean_inc(x_153);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_154 = x_151;
} else {
 lean_dec_ref(x_151);
 x_154 = lean_box(0);
}
x_155 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_155, 0, x_152);
lean_ctor_set(x_155, 1, x_153);
x_156 = lean_array_set(x_31, x_9, x_155);
lean_dec(x_9);
if (lean_is_scalar(x_144)) {
 x_157 = lean_alloc_ctor(0, 1, 0);
} else {
 x_157 = x_144;
}
lean_ctor_set(x_157, 0, x_156);
x_158 = 1;
x_159 = lean_box(x_158);
if (lean_is_scalar(x_154)) {
 x_160 = lean_alloc_ctor(0, 2, 0);
} else {
 x_160 = x_154;
}
lean_ctor_set(x_160, 0, x_157);
lean_ctor_set(x_160, 1, x_159);
return x_160;
}
}
else
{
uint8_t x_161; lean_object* x_162; lean_object* x_163; 
lean_dec(x_142);
lean_dec(x_31);
lean_free_object(x_11);
lean_dec(x_9);
x_161 = 0;
x_162 = lean_box(x_161);
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_2);
lean_ctor_set(x_163, 1, x_162);
return x_163;
}
}
}
}
else
{
lean_object* x_164; lean_object* x_165; size_t x_166; lean_object* x_167; lean_object* x_168; uint8_t x_169; 
x_164 = lean_ctor_get(x_11, 0);
lean_inc(x_164);
lean_dec(x_11);
x_165 = lean_array_set(x_5, x_9, x_10);
x_166 = x_3 >> x_6;
x_167 = l_PersistentHashMap_eraseAux___main___rarg(x_1, x_164, x_166, x_4);
x_168 = lean_ctor_get(x_167, 1);
lean_inc(x_168);
x_169 = lean_unbox(x_168);
lean_dec(x_168);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; uint8_t x_172; 
x_170 = lean_ctor_get(x_167, 0);
lean_inc(x_170);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 lean_ctor_release(x_167, 1);
 x_171 = x_167;
} else {
 lean_dec_ref(x_167);
 x_171 = lean_box(0);
}
x_172 = l_String_Iterator_extract___closed__1;
if (x_172 == 0)
{
lean_object* x_173; lean_object* x_174; 
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 x_173 = x_2;
} else {
 lean_dec_ref(x_2);
 x_173 = lean_box(0);
}
x_174 = l_PersistentHashMap_isUnaryNode___rarg(x_170);
if (lean_obj_tag(x_174) == 0)
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; uint8_t x_178; lean_object* x_179; lean_object* x_180; 
x_175 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_175, 0, x_170);
x_176 = lean_array_set(x_165, x_9, x_175);
lean_dec(x_9);
if (lean_is_scalar(x_173)) {
 x_177 = lean_alloc_ctor(0, 1, 0);
} else {
 x_177 = x_173;
}
lean_ctor_set(x_177, 0, x_176);
x_178 = 1;
x_179 = lean_box(x_178);
if (lean_is_scalar(x_171)) {
 x_180 = lean_alloc_ctor(0, 2, 0);
} else {
 x_180 = x_171;
}
lean_ctor_set(x_180, 0, x_177);
lean_ctor_set(x_180, 1, x_179);
return x_180;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; uint8_t x_188; lean_object* x_189; lean_object* x_190; 
lean_dec(x_171);
lean_dec(x_170);
x_181 = lean_ctor_get(x_174, 0);
lean_inc(x_181);
lean_dec(x_174);
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_181, 1);
lean_inc(x_183);
if (lean_is_exclusive(x_181)) {
 lean_ctor_release(x_181, 0);
 lean_ctor_release(x_181, 1);
 x_184 = x_181;
} else {
 lean_dec_ref(x_181);
 x_184 = lean_box(0);
}
x_185 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_185, 0, x_182);
lean_ctor_set(x_185, 1, x_183);
x_186 = lean_array_set(x_165, x_9, x_185);
lean_dec(x_9);
if (lean_is_scalar(x_173)) {
 x_187 = lean_alloc_ctor(0, 1, 0);
} else {
 x_187 = x_173;
}
lean_ctor_set(x_187, 0, x_186);
x_188 = 1;
x_189 = lean_box(x_188);
if (lean_is_scalar(x_184)) {
 x_190 = lean_alloc_ctor(0, 2, 0);
} else {
 x_190 = x_184;
}
lean_ctor_set(x_190, 0, x_187);
lean_ctor_set(x_190, 1, x_189);
return x_190;
}
}
else
{
uint8_t x_191; lean_object* x_192; lean_object* x_193; 
lean_dec(x_170);
lean_dec(x_165);
lean_dec(x_9);
x_191 = 0;
x_192 = lean_box(x_191);
if (lean_is_scalar(x_171)) {
 x_193 = lean_alloc_ctor(0, 2, 0);
} else {
 x_193 = x_171;
}
lean_ctor_set(x_193, 0, x_2);
lean_ctor_set(x_193, 1, x_192);
return x_193;
}
}
else
{
lean_object* x_194; lean_object* x_195; uint8_t x_196; 
x_194 = lean_ctor_get(x_167, 0);
lean_inc(x_194);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 lean_ctor_release(x_167, 1);
 x_195 = x_167;
} else {
 lean_dec_ref(x_167);
 x_195 = lean_box(0);
}
x_196 = l_String_anyAux___main___at_String_all___spec__1___closed__1;
if (x_196 == 0)
{
lean_object* x_197; lean_object* x_198; 
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 x_197 = x_2;
} else {
 lean_dec_ref(x_2);
 x_197 = lean_box(0);
}
x_198 = l_PersistentHashMap_isUnaryNode___rarg(x_194);
if (lean_obj_tag(x_198) == 0)
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; uint8_t x_202; lean_object* x_203; lean_object* x_204; 
x_199 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_199, 0, x_194);
x_200 = lean_array_set(x_165, x_9, x_199);
lean_dec(x_9);
if (lean_is_scalar(x_197)) {
 x_201 = lean_alloc_ctor(0, 1, 0);
} else {
 x_201 = x_197;
}
lean_ctor_set(x_201, 0, x_200);
x_202 = 1;
x_203 = lean_box(x_202);
if (lean_is_scalar(x_195)) {
 x_204 = lean_alloc_ctor(0, 2, 0);
} else {
 x_204 = x_195;
}
lean_ctor_set(x_204, 0, x_201);
lean_ctor_set(x_204, 1, x_203);
return x_204;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; uint8_t x_212; lean_object* x_213; lean_object* x_214; 
lean_dec(x_195);
lean_dec(x_194);
x_205 = lean_ctor_get(x_198, 0);
lean_inc(x_205);
lean_dec(x_198);
x_206 = lean_ctor_get(x_205, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_205, 1);
lean_inc(x_207);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 lean_ctor_release(x_205, 1);
 x_208 = x_205;
} else {
 lean_dec_ref(x_205);
 x_208 = lean_box(0);
}
x_209 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_209, 0, x_206);
lean_ctor_set(x_209, 1, x_207);
x_210 = lean_array_set(x_165, x_9, x_209);
lean_dec(x_9);
if (lean_is_scalar(x_197)) {
 x_211 = lean_alloc_ctor(0, 1, 0);
} else {
 x_211 = x_197;
}
lean_ctor_set(x_211, 0, x_210);
x_212 = 1;
x_213 = lean_box(x_212);
if (lean_is_scalar(x_208)) {
 x_214 = lean_alloc_ctor(0, 2, 0);
} else {
 x_214 = x_208;
}
lean_ctor_set(x_214, 0, x_211);
lean_ctor_set(x_214, 1, x_213);
return x_214;
}
}
else
{
uint8_t x_215; lean_object* x_216; lean_object* x_217; 
lean_dec(x_194);
lean_dec(x_165);
lean_dec(x_9);
x_215 = 0;
x_216 = lean_box(x_215);
if (lean_is_scalar(x_195)) {
 x_217 = lean_alloc_ctor(0, 2, 0);
} else {
 x_217 = x_195;
}
lean_ctor_set(x_217, 0, x_2);
lean_ctor_set(x_217, 1, x_216);
return x_217;
}
}
}
}
default: 
{
uint8_t x_218; lean_object* x_219; lean_object* x_220; 
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_218 = 0;
x_219 = lean_box(x_218);
x_220 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_220, 0, x_2);
lean_ctor_set(x_220, 1, x_219);
return x_220;
}
}
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_221 = lean_ctor_get(x_2, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_2, 1);
lean_inc(x_222);
x_223 = lean_unsigned_to_nat(0u);
x_224 = l_Array_indexOfAux___main___rarg(x_1, x_221, x_4, x_223);
if (lean_obj_tag(x_224) == 0)
{
uint8_t x_225; lean_object* x_226; lean_object* x_227; 
lean_dec(x_222);
lean_dec(x_221);
x_225 = 0;
x_226 = lean_box(x_225);
x_227 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_227, 0, x_2);
lean_ctor_set(x_227, 1, x_226);
return x_227;
}
else
{
uint8_t x_228; 
x_228 = !lean_is_exclusive(x_2);
if (x_228 == 0)
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; uint8_t x_234; lean_object* x_235; lean_object* x_236; 
x_229 = lean_ctor_get(x_2, 1);
lean_dec(x_229);
x_230 = lean_ctor_get(x_2, 0);
lean_dec(x_230);
x_231 = lean_ctor_get(x_224, 0);
lean_inc(x_231);
lean_dec(x_224);
x_232 = l_Array_eraseIdx_x27___rarg(x_221, x_231);
x_233 = l_Array_eraseIdx_x27___rarg(x_222, x_231);
lean_dec(x_231);
lean_ctor_set(x_2, 1, x_233);
lean_ctor_set(x_2, 0, x_232);
x_234 = 1;
x_235 = lean_box(x_234);
x_236 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_236, 0, x_2);
lean_ctor_set(x_236, 1, x_235);
return x_236;
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; uint8_t x_241; lean_object* x_242; lean_object* x_243; 
lean_dec(x_2);
x_237 = lean_ctor_get(x_224, 0);
lean_inc(x_237);
lean_dec(x_224);
x_238 = l_Array_eraseIdx_x27___rarg(x_221, x_237);
x_239 = l_Array_eraseIdx_x27___rarg(x_222, x_237);
lean_dec(x_237);
x_240 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_240, 0, x_238);
lean_ctor_set(x_240, 1, x_239);
x_241 = 1;
x_242 = lean_box(x_241);
x_243 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_243, 0, x_240);
lean_ctor_set(x_243, 1, x_242);
return x_243;
}
}
}
}
}
lean_object* l_PersistentHashMap_eraseAux___main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_PersistentHashMap_eraseAux___main___rarg___boxed), 4, 0);
return x_3;
}
}
lean_object* l_PersistentHashMap_eraseAux___main___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_PersistentHashMap_eraseAux___main___rarg(x_1, x_2, x_5, x_4);
return x_6;
}
}
lean_object* l_PersistentHashMap_eraseAux___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_PersistentHashMap_eraseAux___main___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_PersistentHashMap_eraseAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_PersistentHashMap_eraseAux___rarg___boxed), 4, 0);
return x_3;
}
}
lean_object* l_PersistentHashMap_eraseAux___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_PersistentHashMap_eraseAux___rarg(x_1, x_2, x_5, x_4);
return x_6;
}
}
lean_object* l_PersistentHashMap_erase___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_8 = lean_apply_1(x_2, x_4);
x_9 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_10 = l_PersistentHashMap_eraseAux___main___rarg(x_1, x_6, x_9, x_4);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = 1;
x_14 = lean_unbox(x_12);
lean_dec(x_12);
x_15 = l_Bool_DecidableEq(x_14, x_13);
if (x_15 == 0)
{
lean_ctor_set(x_3, 0, x_11);
return x_3;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_7, x_16);
lean_dec(x_7);
lean_ctor_set(x_3, 1, x_17);
lean_ctor_set(x_3, 0, x_11);
return x_3;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; 
x_18 = lean_ctor_get(x_3, 0);
x_19 = lean_ctor_get(x_3, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_3);
lean_inc(x_4);
x_20 = lean_apply_1(x_2, x_4);
x_21 = lean_unbox_usize(x_20);
lean_dec(x_20);
x_22 = l_PersistentHashMap_eraseAux___main___rarg(x_1, x_18, x_21, x_4);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = 1;
x_26 = lean_unbox(x_24);
lean_dec(x_24);
x_27 = l_Bool_DecidableEq(x_26, x_25);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_23);
lean_ctor_set(x_28, 1, x_19);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_sub(x_19, x_29);
lean_dec(x_19);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_23);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
lean_object* l_PersistentHashMap_erase(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_PersistentHashMap_erase___rarg), 4, 0);
return x_3;
}
}
lean_object* l_PersistentHashMap_foldlMAux___main___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_4)) {
case 0:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
x_8 = lean_apply_3(x_1, x_5, x_6, x_7);
return x_8;
}
case 1:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
lean_dec(x_4);
x_10 = l_PersistentHashMap_foldlMAux___main___rarg(x_2, lean_box(0), x_1, x_9, x_5);
return x_10;
}
default: 
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_1);
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_apply_2(x_12, lean_box(0), x_5);
return x_13;
}
}
}
}
lean_object* l_PersistentHashMap_foldlMAux___main___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_array_fget(x_1, x_3);
x_7 = lean_apply_3(x_2, x_5, x_4, x_6);
return x_7;
}
}
lean_object* l_PersistentHashMap_foldlMAux___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l_PersistentHashMap_foldlMAux___main___rarg___lambda__1___boxed), 5, 2);
lean_closure_set(x_7, 0, x_3);
lean_closure_set(x_7, 1, x_1);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_iterateMAux___main___rarg(x_1, lean_box(0), x_6, x_7, x_8, x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_4, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_dec(x_4);
x_12 = lean_alloc_closure((void*)(l_PersistentHashMap_foldlMAux___main___rarg___lambda__2___boxed), 5, 2);
lean_closure_set(x_12, 0, x_11);
lean_closure_set(x_12, 1, x_3);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Array_iterateMAux___main___rarg(x_1, lean_box(0), x_10, x_12, x_13, x_5);
return x_14;
}
}
}
lean_object* l_PersistentHashMap_foldlMAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_PersistentHashMap_foldlMAux___main___rarg), 5, 0);
return x_4;
}
}
lean_object* l_PersistentHashMap_foldlMAux___main___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_PersistentHashMap_foldlMAux___main___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
lean_object* l_PersistentHashMap_foldlMAux___main___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_PersistentHashMap_foldlMAux___main___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_PersistentHashMap_foldlMAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_PersistentHashMap_foldlMAux___main(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_PersistentHashMap_foldlMAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_PersistentHashMap_foldlMAux___main___rarg(x_1, lean_box(0), x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_PersistentHashMap_foldlMAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_PersistentHashMap_foldlMAux___rarg), 5, 0);
return x_4;
}
}
lean_object* l_PersistentHashMap_foldlMAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_PersistentHashMap_foldlMAux(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_PersistentHashMap_foldlM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec(x_5);
x_9 = l_PersistentHashMap_foldlMAux___main___rarg(x_1, lean_box(0), x_6, x_8, x_7);
return x_9;
}
}
lean_object* l_PersistentHashMap_foldlM(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_PersistentHashMap_foldlM___rarg___boxed), 7, 0);
return x_4;
}
}
lean_object* l_PersistentHashMap_foldlM___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_PersistentHashMap_foldlM___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
lean_object* l_PersistentHashMap_foldlM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_PersistentHashMap_foldlM(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_PersistentHashMap_foldl___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Id_Monad;
x_7 = l_PersistentHashMap_foldlM___rarg(x_6, lean_box(0), x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
lean_object* l_PersistentHashMap_foldl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_PersistentHashMap_foldl___rarg___boxed), 5, 0);
return x_4;
}
}
lean_object* l_PersistentHashMap_foldl___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_PersistentHashMap_foldl___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Array_iterateMAux___main___at_PersistentHashMap_toList___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_dec(x_3);
return x_4;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_3, x_8);
lean_dec(x_3);
switch (lean_obj_tag(x_7)) {
case 0:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_7, 1);
lean_inc(x_11);
lean_dec(x_7);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_4);
x_3 = x_9;
x_4 = x_13;
goto _start;
}
case 1:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_7, 0);
lean_inc(x_15);
lean_dec(x_7);
x_16 = l_PersistentHashMap_foldlMAux___main___at_PersistentHashMap_toList___spec__2___rarg(x_15, x_4);
lean_dec(x_15);
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
lean_object* l_Array_iterateMAux___main___at_PersistentHashMap_toList___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_iterateMAux___main___at_PersistentHashMap_toList___spec__3___rarg___boxed), 4, 0);
return x_3;
}
}
lean_object* l_Array_iterateMAux___main___at_PersistentHashMap_toList___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_array_fget(x_3, x_4);
x_9 = lean_array_fget(x_2, x_4);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_5);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_4, x_12);
lean_dec(x_4);
x_4 = x_13;
x_5 = x_11;
goto _start;
}
}
}
lean_object* l_Array_iterateMAux___main___at_PersistentHashMap_toList___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_iterateMAux___main___at_PersistentHashMap_toList___spec__4___rarg___boxed), 5, 0);
return x_3;
}
}
lean_object* l_PersistentHashMap_foldlMAux___main___at_PersistentHashMap_toList___spec__2___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Array_iterateMAux___main___at_PersistentHashMap_toList___spec__3___rarg(x_3, x_3, x_4, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_iterateMAux___main___at_PersistentHashMap_toList___spec__4___rarg(x_6, x_7, x_6, x_8, x_2);
return x_9;
}
}
}
lean_object* l_PersistentHashMap_foldlMAux___main___at_PersistentHashMap_toList___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_PersistentHashMap_foldlMAux___main___at_PersistentHashMap_toList___spec__2___rarg___boxed), 2, 0);
return x_3;
}
}
lean_object* l_PersistentHashMap_foldlM___at_PersistentHashMap_toList___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = l_PersistentHashMap_foldlMAux___main___at_PersistentHashMap_toList___spec__2___rarg(x_3, x_2);
return x_4;
}
}
lean_object* l_PersistentHashMap_foldlM___at_PersistentHashMap_toList___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_PersistentHashMap_foldlM___at_PersistentHashMap_toList___spec__1___rarg___boxed), 2, 0);
return x_5;
}
}
lean_object* l_PersistentHashMap_toList___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = l_PersistentHashMap_foldlM___at_PersistentHashMap_toList___spec__1___rarg(x_3, x_4);
return x_5;
}
}
lean_object* l_PersistentHashMap_toList(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_PersistentHashMap_toList___rarg___boxed), 3, 0);
return x_3;
}
}
lean_object* l_Array_iterateMAux___main___at_PersistentHashMap_toList___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_iterateMAux___main___at_PersistentHashMap_toList___spec__3___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_iterateMAux___main___at_PersistentHashMap_toList___spec__4___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_iterateMAux___main___at_PersistentHashMap_toList___spec__4___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_PersistentHashMap_foldlMAux___main___at_PersistentHashMap_toList___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_PersistentHashMap_foldlMAux___main___at_PersistentHashMap_toList___spec__2___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_PersistentHashMap_foldlM___at_PersistentHashMap_toList___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_PersistentHashMap_foldlM___at_PersistentHashMap_toList___spec__1___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_PersistentHashMap_foldlM___at_PersistentHashMap_toList___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_PersistentHashMap_foldlM___at_PersistentHashMap_toList___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_PersistentHashMap_toList___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_PersistentHashMap_toList___rarg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_iterateMAux___main___at_PersistentHashMap_collectStats___main___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_array_fget(x_3, x_4);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_4, x_9);
lean_dec(x_4);
switch (lean_obj_tag(x_8)) {
case 0:
{
lean_dec(x_8);
x_4 = x_10;
goto _start;
}
case 1:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
x_13 = lean_nat_add(x_1, x_9);
x_14 = l_PersistentHashMap_collectStats___main___rarg(x_12, x_5, x_13);
lean_dec(x_13);
lean_dec(x_12);
x_4 = x_10;
x_5 = x_14;
goto _start;
}
default: 
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_5);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_5, 1);
x_18 = lean_nat_add(x_17, x_9);
lean_dec(x_17);
lean_ctor_set(x_5, 1, x_18);
x_4 = x_10;
goto _start;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_5, 0);
x_21 = lean_ctor_get(x_5, 1);
x_22 = lean_ctor_get(x_5, 2);
x_23 = lean_ctor_get(x_5, 3);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_5);
x_24 = lean_nat_add(x_21, x_9);
lean_dec(x_21);
x_25 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_25, 2, x_22);
lean_ctor_set(x_25, 3, x_23);
x_4 = x_10;
x_5 = x_25;
goto _start;
}
}
}
}
}
}
lean_object* l_Array_iterateMAux___main___at_PersistentHashMap_collectStats___main___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_iterateMAux___main___at_PersistentHashMap_collectStats___main___spec__1___rarg___boxed), 5, 0);
return x_3;
}
}
lean_object* l_PersistentHashMap_collectStats___main___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 3);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_6, x_8);
lean_dec(x_6);
x_10 = l_Nat_max(x_7, x_3);
lean_dec(x_7);
lean_ctor_set(x_2, 3, x_10);
lean_ctor_set(x_2, 0, x_9);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Array_iterateMAux___main___at_PersistentHashMap_collectStats___main___spec__1___rarg(x_3, x_5, x_5, x_11, x_2);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_2, 0);
x_15 = lean_ctor_get(x_2, 1);
x_16 = lean_ctor_get(x_2, 2);
x_17 = lean_ctor_get(x_2, 3);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_2);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_14, x_18);
lean_dec(x_14);
x_20 = l_Nat_max(x_17, x_3);
lean_dec(x_17);
x_21 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_15);
lean_ctor_set(x_21, 2, x_16);
lean_ctor_set(x_21, 3, x_20);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Array_iterateMAux___main___at_PersistentHashMap_collectStats___main___spec__1___rarg(x_3, x_13, x_13, x_22, x_21);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_2);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_25 = lean_ctor_get(x_1, 0);
x_26 = lean_ctor_get(x_2, 0);
x_27 = lean_ctor_get(x_2, 2);
x_28 = lean_ctor_get(x_2, 3);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_add(x_26, x_29);
lean_dec(x_26);
x_31 = lean_array_get_size(x_25);
x_32 = lean_nat_add(x_27, x_31);
lean_dec(x_31);
lean_dec(x_27);
x_33 = lean_nat_sub(x_32, x_29);
lean_dec(x_32);
x_34 = l_Nat_max(x_28, x_3);
lean_dec(x_28);
lean_ctor_set(x_2, 3, x_34);
lean_ctor_set(x_2, 2, x_33);
lean_ctor_set(x_2, 0, x_30);
return x_2;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_35 = lean_ctor_get(x_1, 0);
x_36 = lean_ctor_get(x_2, 0);
x_37 = lean_ctor_get(x_2, 1);
x_38 = lean_ctor_get(x_2, 2);
x_39 = lean_ctor_get(x_2, 3);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_2);
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_nat_add(x_36, x_40);
lean_dec(x_36);
x_42 = lean_array_get_size(x_35);
x_43 = lean_nat_add(x_38, x_42);
lean_dec(x_42);
lean_dec(x_38);
x_44 = lean_nat_sub(x_43, x_40);
lean_dec(x_43);
x_45 = l_Nat_max(x_39, x_3);
lean_dec(x_39);
x_46 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_46, 0, x_41);
lean_ctor_set(x_46, 1, x_37);
lean_ctor_set(x_46, 2, x_44);
lean_ctor_set(x_46, 3, x_45);
return x_46;
}
}
}
}
lean_object* l_PersistentHashMap_collectStats___main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_PersistentHashMap_collectStats___main___rarg___boxed), 3, 0);
return x_3;
}
}
lean_object* l_Array_iterateMAux___main___at_PersistentHashMap_collectStats___main___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_iterateMAux___main___at_PersistentHashMap_collectStats___main___spec__1___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_PersistentHashMap_collectStats___main___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_PersistentHashMap_collectStats___main___rarg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_PersistentHashMap_collectStats___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_PersistentHashMap_collectStats___main___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_PersistentHashMap_collectStats(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_PersistentHashMap_collectStats___rarg___boxed), 3, 0);
return x_3;
}
}
lean_object* l_PersistentHashMap_collectStats___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_PersistentHashMap_collectStats___rarg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l_PersistentHashMap_stats___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 2, x_1);
lean_ctor_set(x_2, 3, x_1);
return x_2;
}
}
lean_object* l_PersistentHashMap_stats___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = l_PersistentHashMap_stats___rarg___closed__1;
x_4 = lean_unsigned_to_nat(1u);
x_5 = l_PersistentHashMap_collectStats___main___rarg(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_PersistentHashMap_stats(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_PersistentHashMap_stats___rarg___boxed), 1, 0);
return x_5;
}
}
lean_object* l_PersistentHashMap_stats___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_PersistentHashMap_stats___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_PersistentHashMap_stats___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_PersistentHashMap_stats(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* _init_l_PersistentHashMap_Stats_toString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("{ nodes := ");
return x_1;
}
}
lean_object* _init_l_PersistentHashMap_Stats_toString___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(", null := ");
return x_1;
}
}
lean_object* _init_l_PersistentHashMap_Stats_toString___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(", collisions := ");
return x_1;
}
}
lean_object* _init_l_PersistentHashMap_Stats_toString___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(", depth := ");
return x_1;
}
}
lean_object* _init_l_PersistentHashMap_Stats_toString___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("}");
return x_1;
}
}
lean_object* l_PersistentHashMap_Stats_toString(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Nat_repr(x_2);
x_4 = l_PersistentHashMap_Stats_toString___closed__1;
x_5 = lean_string_append(x_4, x_3);
lean_dec(x_3);
x_6 = l_PersistentHashMap_Stats_toString___closed__2;
x_7 = lean_string_append(x_5, x_6);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = l_Nat_repr(x_8);
x_10 = lean_string_append(x_7, x_9);
lean_dec(x_9);
x_11 = l_PersistentHashMap_Stats_toString___closed__3;
x_12 = lean_string_append(x_10, x_11);
x_13 = lean_ctor_get(x_1, 2);
lean_inc(x_13);
x_14 = l_Nat_repr(x_13);
x_15 = lean_string_append(x_12, x_14);
lean_dec(x_14);
x_16 = l_PersistentHashMap_Stats_toString___closed__4;
x_17 = lean_string_append(x_15, x_16);
x_18 = lean_ctor_get(x_1, 3);
lean_inc(x_18);
lean_dec(x_1);
x_19 = l_Nat_repr(x_18);
x_20 = lean_string_append(x_17, x_19);
lean_dec(x_19);
x_21 = l_PersistentHashMap_Stats_toString___closed__5;
x_22 = lean_string_append(x_20, x_21);
return x_22;
}
}
lean_object* _init_l_PersistentHashMap_HasToString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_PersistentHashMap_Stats_toString), 1, 0);
return x_1;
}
}
lean_object* _init_l_PersistentHashMap_HasToString() {
_start:
{
lean_object* x_1; 
x_1 = l_PersistentHashMap_HasToString___closed__1;
return x_1;
}
}
lean_object* initialize_Init_Data_Array(lean_object*);
lean_object* initialize_Init_Data_Hashable(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Data_PersistentHashMap_Basic(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Array(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Hashable(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_PersistentHashMap_Node_inhabited___closed__1 = _init_l_PersistentHashMap_Node_inhabited___closed__1();
lean_mark_persistent(l_PersistentHashMap_Node_inhabited___closed__1);
l_PersistentHashMap_shift = _init_l_PersistentHashMap_shift();
l_PersistentHashMap_branching = _init_l_PersistentHashMap_branching();
l_PersistentHashMap_maxDepth = _init_l_PersistentHashMap_maxDepth();
l_PersistentHashMap_maxCollisions = _init_l_PersistentHashMap_maxCollisions();
lean_mark_persistent(l_PersistentHashMap_maxCollisions);
l_PersistentHashMap_mkEmptyEntriesArray___closed__1 = _init_l_PersistentHashMap_mkEmptyEntriesArray___closed__1();
lean_mark_persistent(l_PersistentHashMap_mkEmptyEntriesArray___closed__1);
l_PersistentHashMap_empty___rarg___closed__1 = _init_l_PersistentHashMap_empty___rarg___closed__1();
lean_mark_persistent(l_PersistentHashMap_empty___rarg___closed__1);
l_PersistentHashMap_empty___rarg___closed__2 = _init_l_PersistentHashMap_empty___rarg___closed__2();
lean_mark_persistent(l_PersistentHashMap_empty___rarg___closed__2);
l_PersistentHashMap_mkCollisionNode___rarg___closed__1 = _init_l_PersistentHashMap_mkCollisionNode___rarg___closed__1();
lean_mark_persistent(l_PersistentHashMap_mkCollisionNode___rarg___closed__1);
l_PersistentHashMap_insertAux___main___rarg___closed__1 = _init_l_PersistentHashMap_insertAux___main___rarg___closed__1();
l_PersistentHashMap_insertAux___main___rarg___closed__2 = _init_l_PersistentHashMap_insertAux___main___rarg___closed__2();
l_PersistentHashMap_insertAux___main___rarg___closed__3 = _init_l_PersistentHashMap_insertAux___main___rarg___closed__3();
lean_mark_persistent(l_PersistentHashMap_insertAux___main___rarg___closed__3);
l_PersistentHashMap_find_x21___rarg___closed__1 = _init_l_PersistentHashMap_find_x21___rarg___closed__1();
lean_mark_persistent(l_PersistentHashMap_find_x21___rarg___closed__1);
l_PersistentHashMap_find_x21___rarg___closed__2 = _init_l_PersistentHashMap_find_x21___rarg___closed__2();
lean_mark_persistent(l_PersistentHashMap_find_x21___rarg___closed__2);
l_PersistentHashMap_find_x21___rarg___closed__3 = _init_l_PersistentHashMap_find_x21___rarg___closed__3();
lean_mark_persistent(l_PersistentHashMap_find_x21___rarg___closed__3);
l_PersistentHashMap_stats___rarg___closed__1 = _init_l_PersistentHashMap_stats___rarg___closed__1();
lean_mark_persistent(l_PersistentHashMap_stats___rarg___closed__1);
l_PersistentHashMap_Stats_toString___closed__1 = _init_l_PersistentHashMap_Stats_toString___closed__1();
lean_mark_persistent(l_PersistentHashMap_Stats_toString___closed__1);
l_PersistentHashMap_Stats_toString___closed__2 = _init_l_PersistentHashMap_Stats_toString___closed__2();
lean_mark_persistent(l_PersistentHashMap_Stats_toString___closed__2);
l_PersistentHashMap_Stats_toString___closed__3 = _init_l_PersistentHashMap_Stats_toString___closed__3();
lean_mark_persistent(l_PersistentHashMap_Stats_toString___closed__3);
l_PersistentHashMap_Stats_toString___closed__4 = _init_l_PersistentHashMap_Stats_toString___closed__4();
lean_mark_persistent(l_PersistentHashMap_Stats_toString___closed__4);
l_PersistentHashMap_Stats_toString___closed__5 = _init_l_PersistentHashMap_Stats_toString___closed__5();
lean_mark_persistent(l_PersistentHashMap_Stats_toString___closed__5);
l_PersistentHashMap_HasToString___closed__1 = _init_l_PersistentHashMap_HasToString___closed__1();
lean_mark_persistent(l_PersistentHashMap_HasToString___closed__1);
l_PersistentHashMap_HasToString = _init_l_PersistentHashMap_HasToString();
lean_mark_persistent(l_PersistentHashMap_HasToString);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
