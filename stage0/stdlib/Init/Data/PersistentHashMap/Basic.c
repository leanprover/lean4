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
size_t l_USize_add(size_t, size_t);
lean_object* l_PersistentHashMap_insertAtCollisionNodeAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_find_x3f(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_Node_inhabited___closed__1;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_PersistentHashMap_foldlMAux___main___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_findAtAux___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_PersistentHashMap_getOp(lean_object*, lean_object*);
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
lean_object* l_PersistentHashMap_forM(lean_object*, lean_object*, lean_object*);
size_t l_PersistentHashMap_shift;
size_t l_PersistentHashMap_mul2Shift(size_t, size_t);
lean_object* l_PersistentHashMap_foldl(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_mul2Shift___boxed(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_foldlM___at_PersistentHashMap_toList___spec__1___rarg___boxed(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_maxCollisions;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_forM___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_Stats_toString___closed__2;
lean_object* l_PersistentHashMap_mod2Shift___boxed(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_Stats_toString___closed__4;
lean_object* l_PersistentHashMap_find_x21___rarg___closed__1;
lean_object* l_PersistentHashMap_insertAux___main___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_containsAtAux(lean_object*, lean_object*);
size_t l_PersistentHashMap_branching;
lean_object* l_PersistentHashMap_insert(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
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
uint8_t l_coeDecidableEq(uint8_t);
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
extern uint8_t l_String_posOfAux___main___closed__2;
lean_object* l_PersistentHashMap_foldlMAux___boxed(lean_object*, lean_object*, lean_object*);
extern uint8_t l_String_posOfAux___main___closed__1;
size_t l_PersistentHashMap_mod2Shift(size_t, size_t);
lean_object* l_PersistentHashMap_empty___rarg(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_find_x3f___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
extern lean_object* l_Id_Monad;
size_t l_USize_land(size_t, size_t);
lean_object* l_PersistentHashMap_div2Shift___boxed(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_containsAtAux___main(lean_object*);
lean_object* l_PersistentHashMap_eraseAux___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_eraseAux___rarg(lean_object*, lean_object*, size_t, lean_object*);
lean_object* l_PersistentHashMap_mkCollisionNode(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_findAux___main___rarg(lean_object*, lean_object*, size_t, lean_object*);
lean_object* l_PersistentHashMap_forM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_Inhabited___rarg___boxed(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_findAtAux(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_getOp___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* lean_panic_fn(lean_object*, lean_object*);
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
lean_object* l_PersistentHashMap_forM___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_PersistentHashMap_insertAux___main___spec__1___rarg(lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_foldlM___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_PersistentHashMap_toList___spec__4___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_eraseAux___main___rarg(lean_object*, lean_object*, size_t, lean_object*);
lean_object* l_PersistentHashMap_isUnaryNode(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_insertAtCollisionNode(lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_PersistentHashMap_forM___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_stats___rarg___closed__1;
lean_object* l_PersistentHashMap_stats___rarg___boxed(lean_object*);
lean_object* l_PersistentHashMap_stats(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_isEmpty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_insertAux(lean_object*, lean_object*);
lean_object* l_PersistentHashMap_mkCollisionNode___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentHashMap_forM___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; 
x_18 = lean_array_fget(x_6, x_3);
lean_inc(x_1);
lean_inc(x_4);
x_19 = lean_apply_2(x_1, x_4, x_18);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
x_21 = l_coeDecidableEq(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_7);
lean_dec(x_6);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_3, x_22);
lean_dec(x_3);
x_3 = x_23;
goto _start;
}
else
{
uint8_t x_25; 
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_2);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_2, 1);
lean_dec(x_26);
x_27 = lean_ctor_get(x_2, 0);
lean_dec(x_27);
x_28 = lean_array_fset(x_6, x_3, x_4);
x_29 = lean_array_fset(x_7, x_3, x_5);
lean_dec(x_3);
lean_ctor_set(x_2, 1, x_29);
lean_ctor_set(x_2, 0, x_28);
return x_2;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_2);
x_30 = lean_array_fset(x_6, x_3, x_4);
x_31 = lean_array_fset(x_7, x_3, x_5);
lean_dec(x_3);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
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
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_25; 
x_21 = lean_ctor_get(x_17, 0);
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_inc(x_6);
x_23 = lean_apply_2(x_1, x_6, x_21);
x_24 = lean_unbox(x_23);
lean_dec(x_23);
x_25 = l_coeDecidableEq(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_free_object(x_17);
x_26 = l_PersistentHashMap_mkCollisionNode___rarg(x_21, x_22, x_6, x_7);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_array_fset(x_19, x_14, x_27);
lean_dec(x_14);
lean_ctor_set(x_3, 0, x_28);
return x_3;
}
else
{
lean_object* x_29; 
lean_dec(x_22);
lean_dec(x_21);
lean_ctor_set(x_17, 1, x_7);
lean_ctor_set(x_17, 0, x_6);
x_29 = lean_array_fset(x_19, x_14, x_17);
lean_dec(x_14);
lean_ctor_set(x_3, 0, x_29);
return x_3;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_34; 
x_30 = lean_ctor_get(x_17, 0);
x_31 = lean_ctor_get(x_17, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_17);
lean_inc(x_30);
lean_inc(x_6);
x_32 = lean_apply_2(x_1, x_6, x_30);
x_33 = lean_unbox(x_32);
lean_dec(x_32);
x_34 = l_coeDecidableEq(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = l_PersistentHashMap_mkCollisionNode___rarg(x_30, x_31, x_6, x_7);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_37 = lean_array_fset(x_19, x_14, x_36);
lean_dec(x_14);
lean_ctor_set(x_3, 0, x_37);
return x_3;
}
else
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_31);
lean_dec(x_30);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_6);
lean_ctor_set(x_38, 1, x_7);
x_39 = lean_array_fset(x_19, x_14, x_38);
lean_dec(x_14);
lean_ctor_set(x_3, 0, x_39);
return x_3;
}
}
}
case 1:
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_17);
if (x_40 == 0)
{
lean_object* x_41; size_t x_42; size_t x_43; lean_object* x_44; lean_object* x_45; 
x_41 = lean_ctor_get(x_17, 0);
x_42 = x_4 >> x_11;
x_43 = x_5 + x_10;
x_44 = l_PersistentHashMap_insertAux___main___rarg(x_1, x_2, x_41, x_42, x_43, x_6, x_7);
lean_ctor_set(x_17, 0, x_44);
x_45 = lean_array_fset(x_19, x_14, x_17);
lean_dec(x_14);
lean_ctor_set(x_3, 0, x_45);
return x_3;
}
else
{
lean_object* x_46; size_t x_47; size_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_46 = lean_ctor_get(x_17, 0);
lean_inc(x_46);
lean_dec(x_17);
x_47 = x_4 >> x_11;
x_48 = x_5 + x_10;
x_49 = l_PersistentHashMap_insertAux___main___rarg(x_1, x_2, x_46, x_47, x_48, x_6, x_7);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
x_51 = lean_array_fset(x_19, x_14, x_50);
lean_dec(x_14);
lean_ctor_set(x_3, 0, x_51);
return x_3;
}
}
default: 
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_2);
lean_dec(x_1);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_6);
lean_ctor_set(x_52, 1, x_7);
x_53 = lean_array_fset(x_19, x_14, x_52);
lean_dec(x_14);
lean_ctor_set(x_3, 0, x_53);
return x_3;
}
}
}
}
else
{
lean_object* x_54; size_t x_55; size_t x_56; size_t x_57; size_t x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_54 = lean_ctor_get(x_3, 0);
lean_inc(x_54);
lean_dec(x_3);
x_55 = 1;
x_56 = 5;
x_57 = l_PersistentHashMap_insertAux___main___rarg___closed__2;
x_58 = x_4 & x_57;
x_59 = lean_usize_to_nat(x_58);
x_60 = lean_array_get_size(x_54);
x_61 = lean_nat_dec_lt(x_59, x_60);
lean_dec(x_60);
if (x_61 == 0)
{
lean_object* x_62; 
lean_dec(x_59);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_62 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_62, 0, x_54);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_array_fget(x_54, x_59);
x_64 = lean_box(2);
x_65 = lean_array_fset(x_54, x_59, x_64);
switch (lean_obj_tag(x_63)) {
case 0:
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; uint8_t x_71; 
lean_dec(x_2);
x_66 = lean_ctor_get(x_63, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_63, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_68 = x_63;
} else {
 lean_dec_ref(x_63);
 x_68 = lean_box(0);
}
lean_inc(x_66);
lean_inc(x_6);
x_69 = lean_apply_2(x_1, x_6, x_66);
x_70 = lean_unbox(x_69);
lean_dec(x_69);
x_71 = l_coeDecidableEq(x_70);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_68);
x_72 = l_PersistentHashMap_mkCollisionNode___rarg(x_66, x_67, x_6, x_7);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_72);
x_74 = lean_array_fset(x_65, x_59, x_73);
lean_dec(x_59);
x_75 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_75, 0, x_74);
return x_75;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_67);
lean_dec(x_66);
if (lean_is_scalar(x_68)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_68;
}
lean_ctor_set(x_76, 0, x_6);
lean_ctor_set(x_76, 1, x_7);
x_77 = lean_array_fset(x_65, x_59, x_76);
lean_dec(x_59);
x_78 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_78, 0, x_77);
return x_78;
}
}
case 1:
{
lean_object* x_79; lean_object* x_80; size_t x_81; size_t x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_79 = lean_ctor_get(x_63, 0);
lean_inc(x_79);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 x_80 = x_63;
} else {
 lean_dec_ref(x_63);
 x_80 = lean_box(0);
}
x_81 = x_4 >> x_56;
x_82 = x_5 + x_55;
x_83 = l_PersistentHashMap_insertAux___main___rarg(x_1, x_2, x_79, x_81, x_82, x_6, x_7);
if (lean_is_scalar(x_80)) {
 x_84 = lean_alloc_ctor(1, 1, 0);
} else {
 x_84 = x_80;
}
lean_ctor_set(x_84, 0, x_83);
x_85 = lean_array_fset(x_65, x_59, x_84);
lean_dec(x_59);
x_86 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_86, 0, x_85);
return x_86;
}
default: 
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_2);
lean_dec(x_1);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_6);
lean_ctor_set(x_87, 1, x_7);
x_88 = lean_array_fset(x_65, x_59, x_87);
lean_dec(x_59);
x_89 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_89, 0, x_88);
return x_89;
}
}
}
}
}
else
{
lean_object* x_90; lean_object* x_91; uint8_t x_92; size_t x_99; uint8_t x_100; 
x_90 = lean_unsigned_to_nat(0u);
lean_inc(x_1);
x_91 = l_PersistentHashMap_insertAtCollisionNodeAux___main___rarg(x_1, x_3, x_90, x_6, x_7);
x_99 = 7;
x_100 = x_99 <= x_5;
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_101 = l_PersistentHashMap_getCollisionNodeSize___rarg(x_91);
x_102 = lean_unsigned_to_nat(4u);
x_103 = lean_nat_dec_lt(x_101, x_102);
lean_dec(x_101);
x_92 = x_103;
goto block_98;
}
else
{
uint8_t x_104; 
x_104 = 1;
x_92 = x_104;
goto block_98;
}
block_98:
{
uint8_t x_93; 
x_93 = l_coeDecidableEq(x_92);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_94 = lean_ctor_get(x_91, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_91, 1);
lean_inc(x_95);
lean_dec(x_91);
x_96 = l_PersistentHashMap_insertAux___main___rarg___closed__3;
x_97 = l_Array_iterateMAux___main___at_PersistentHashMap_insertAux___main___spec__1___rarg(x_1, x_2, x_5, x_94, x_95, x_94, x_90, x_96);
lean_dec(x_95);
lean_dec(x_94);
return x_97;
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_91;
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
lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; 
x_10 = lean_array_fget(x_2, x_5);
lean_inc(x_1);
lean_inc(x_6);
x_11 = lean_apply_2(x_1, x_6, x_10);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
x_13 = l_coeDecidableEq(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_5, x_14);
lean_dec(x_5);
x_4 = lean_box(0);
x_5 = x_15;
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_6);
lean_dec(x_1);
x_17 = lean_array_fget(x_3, x_5);
lean_dec(x_5);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
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
lean_inc(x_5);
lean_dec(x_2);
x_6 = 5;
x_7 = l_PersistentHashMap_insertAux___main___rarg___closed__2;
x_8 = x_3 & x_7;
x_9 = lean_usize_to_nat(x_8);
x_10 = lean_box(2);
x_11 = lean_array_get(x_10, x_5, x_9);
lean_dec(x_9);
lean_dec(x_5);
switch (lean_obj_tag(x_11)) {
case 0:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_apply_2(x_1, x_4, x_12);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
x_16 = l_coeDecidableEq(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_13);
x_17 = lean_box(0);
return x_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_13);
return x_18;
}
}
case 1:
{
lean_object* x_19; size_t x_20; 
x_19 = lean_ctor_get(x_11, 0);
lean_inc(x_19);
lean_dec(x_11);
x_20 = x_3 >> x_6;
x_2 = x_19;
x_3 = x_20;
goto _start;
}
default: 
{
lean_object* x_22; 
lean_dec(x_4);
lean_dec(x_1);
x_22 = lean_box(0);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_2, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_2, 1);
lean_inc(x_24);
lean_dec(x_2);
x_25 = lean_unsigned_to_nat(0u);
x_26 = l_PersistentHashMap_findAtAux___main___rarg(x_1, x_23, x_24, lean_box(0), x_25, x_4);
lean_dec(x_24);
lean_dec(x_23);
return x_26;
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
return x_6;
}
}
lean_object* l_PersistentHashMap_find_x3f___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; size_t x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
lean_inc(x_4);
x_6 = lean_apply_1(x_2, x_4);
x_7 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_8 = l_PersistentHashMap_findAux___main___rarg(x_1, x_5, x_7, x_4);
return x_8;
}
}
lean_object* l_PersistentHashMap_find_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_PersistentHashMap_find_x3f___rarg), 4, 0);
return x_3;
}
}
lean_object* l_PersistentHashMap_getOp___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_PersistentHashMap_find_x3f___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_PersistentHashMap_getOp(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_PersistentHashMap_getOp___rarg), 4, 0);
return x_3;
}
}
lean_object* l_PersistentHashMap_findD___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_PersistentHashMap_find_x3f___rarg(x_1, x_2, x_3, x_4);
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
x_2 = lean_unsigned_to_nat(167u);
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
x_6 = l_PersistentHashMap_find_x3f___rarg(x_1, x_2, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_PersistentHashMap_find_x21___rarg___closed__3;
x_8 = lean_panic_fn(x_3, x_7);
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
x_3 = lean_alloc_closure((void*)(l_PersistentHashMap_find_x21___rarg), 5, 0);
return x_3;
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
lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; 
x_8 = lean_array_fget(x_2, x_3);
lean_inc(x_1);
lean_inc(x_4);
x_9 = lean_apply_2(x_1, x_4, x_8);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
x_11 = l_coeDecidableEq(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_3, x_12);
lean_dec(x_3);
x_3 = x_13;
goto _start;
}
else
{
uint8_t x_15; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_15 = 1;
return x_15;
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
lean_inc(x_5);
lean_dec(x_2);
x_6 = 5;
x_7 = l_PersistentHashMap_insertAux___main___rarg___closed__2;
x_8 = x_3 & x_7;
x_9 = lean_usize_to_nat(x_8);
x_10 = lean_box(2);
x_11 = lean_array_get(x_10, x_5, x_9);
lean_dec(x_9);
lean_dec(x_5);
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
lean_object* x_14; size_t x_15; 
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
lean_dec(x_11);
x_15 = x_3 >> x_6;
x_2 = x_14;
x_3 = x_15;
goto _start;
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
lean_inc(x_19);
lean_dec(x_2);
x_20 = lean_unsigned_to_nat(0u);
x_21 = l_PersistentHashMap_containsAtAux___main___rarg(x_1, x_19, x_20, x_4);
lean_dec(x_19);
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
return x_6;
}
}
lean_object* l_PersistentHashMap_contains___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; size_t x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
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
x_3 = lean_alloc_closure((void*)(l_PersistentHashMap_contains___rarg), 4, 0);
return x_3;
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
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_apply_2(x_1, x_4, x_12);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
x_15 = l_coeDecidableEq(x_14);
if (x_15 == 0)
{
uint8_t x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_9);
lean_dec(x_5);
x_16 = 0;
x_17 = lean_box(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_2);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_2);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_2, 0);
lean_dec(x_20);
x_21 = lean_array_set(x_5, x_9, x_10);
lean_dec(x_9);
lean_ctor_set(x_2, 0, x_21);
x_22 = 1;
x_23 = lean_box(x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_2);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_2);
x_25 = lean_array_set(x_5, x_9, x_10);
lean_dec(x_9);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = 1;
x_28 = lean_box(x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
case 1:
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_11);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; size_t x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_31 = lean_ctor_get(x_11, 0);
x_32 = lean_array_set(x_5, x_9, x_10);
x_33 = x_3 >> x_6;
x_34 = l_PersistentHashMap_eraseAux___main___rarg(x_1, x_31, x_33, x_4);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
x_36 = lean_unbox(x_35);
lean_dec(x_35);
if (x_36 == 0)
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_34);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_ctor_get(x_34, 0);
x_39 = lean_ctor_get(x_34, 1);
lean_dec(x_39);
x_40 = l_String_posOfAux___main___closed__2;
if (x_40 == 0)
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_2);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_2, 0);
lean_dec(x_42);
x_43 = l_PersistentHashMap_isUnaryNode___rarg(x_38);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; uint8_t x_45; lean_object* x_46; 
lean_ctor_set(x_11, 0, x_38);
x_44 = lean_array_set(x_32, x_9, x_11);
lean_dec(x_9);
lean_ctor_set(x_2, 0, x_44);
x_45 = 1;
x_46 = lean_box(x_45);
lean_ctor_set(x_34, 1, x_46);
lean_ctor_set(x_34, 0, x_2);
return x_34;
}
else
{
lean_object* x_47; uint8_t x_48; 
lean_free_object(x_34);
lean_dec(x_38);
lean_free_object(x_11);
x_47 = lean_ctor_get(x_43, 0);
lean_inc(x_47);
lean_dec(x_43);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; 
x_49 = lean_ctor_get(x_47, 0);
x_50 = lean_ctor_get(x_47, 1);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_array_set(x_32, x_9, x_51);
lean_dec(x_9);
lean_ctor_set(x_2, 0, x_52);
x_53 = 1;
x_54 = lean_box(x_53);
lean_ctor_set(x_47, 1, x_54);
lean_ctor_set(x_47, 0, x_2);
return x_47;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; 
x_55 = lean_ctor_get(x_47, 0);
x_56 = lean_ctor_get(x_47, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_47);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_array_set(x_32, x_9, x_57);
lean_dec(x_9);
lean_ctor_set(x_2, 0, x_58);
x_59 = 1;
x_60 = lean_box(x_59);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_2);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
lean_object* x_62; 
lean_dec(x_2);
x_62 = l_PersistentHashMap_isUnaryNode___rarg(x_38);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; 
lean_ctor_set(x_11, 0, x_38);
x_63 = lean_array_set(x_32, x_9, x_11);
lean_dec(x_9);
x_64 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_64, 0, x_63);
x_65 = 1;
x_66 = lean_box(x_65);
lean_ctor_set(x_34, 1, x_66);
lean_ctor_set(x_34, 0, x_64);
return x_34;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; 
lean_free_object(x_34);
lean_dec(x_38);
lean_free_object(x_11);
x_67 = lean_ctor_get(x_62, 0);
lean_inc(x_67);
lean_dec(x_62);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_70 = x_67;
} else {
 lean_dec_ref(x_67);
 x_70 = lean_box(0);
}
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set(x_71, 1, x_69);
x_72 = lean_array_set(x_32, x_9, x_71);
lean_dec(x_9);
x_73 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_73, 0, x_72);
x_74 = 1;
x_75 = lean_box(x_74);
if (lean_is_scalar(x_70)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_70;
}
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
else
{
uint8_t x_77; lean_object* x_78; 
lean_dec(x_38);
lean_dec(x_32);
lean_free_object(x_11);
lean_dec(x_9);
x_77 = 0;
x_78 = lean_box(x_77);
lean_ctor_set(x_34, 1, x_78);
lean_ctor_set(x_34, 0, x_2);
return x_34;
}
}
else
{
lean_object* x_79; uint8_t x_80; 
x_79 = lean_ctor_get(x_34, 0);
lean_inc(x_79);
lean_dec(x_34);
x_80 = l_String_posOfAux___main___closed__2;
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; 
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 x_81 = x_2;
} else {
 lean_dec_ref(x_2);
 x_81 = lean_box(0);
}
x_82 = l_PersistentHashMap_isUnaryNode___rarg(x_79);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; uint8_t x_85; lean_object* x_86; lean_object* x_87; 
lean_ctor_set(x_11, 0, x_79);
x_83 = lean_array_set(x_32, x_9, x_11);
lean_dec(x_9);
if (lean_is_scalar(x_81)) {
 x_84 = lean_alloc_ctor(0, 1, 0);
} else {
 x_84 = x_81;
}
lean_ctor_set(x_84, 0, x_83);
x_85 = 1;
x_86 = lean_box(x_85);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_84);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_79);
lean_free_object(x_11);
x_88 = lean_ctor_get(x_82, 0);
lean_inc(x_88);
lean_dec(x_82);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_91 = x_88;
} else {
 lean_dec_ref(x_88);
 x_91 = lean_box(0);
}
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_89);
lean_ctor_set(x_92, 1, x_90);
x_93 = lean_array_set(x_32, x_9, x_92);
lean_dec(x_9);
if (lean_is_scalar(x_81)) {
 x_94 = lean_alloc_ctor(0, 1, 0);
} else {
 x_94 = x_81;
}
lean_ctor_set(x_94, 0, x_93);
x_95 = 1;
x_96 = lean_box(x_95);
if (lean_is_scalar(x_91)) {
 x_97 = lean_alloc_ctor(0, 2, 0);
} else {
 x_97 = x_91;
}
lean_ctor_set(x_97, 0, x_94);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
else
{
uint8_t x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_79);
lean_dec(x_32);
lean_free_object(x_11);
lean_dec(x_9);
x_98 = 0;
x_99 = lean_box(x_98);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_2);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
else
{
uint8_t x_101; 
x_101 = !lean_is_exclusive(x_34);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; uint8_t x_104; 
x_102 = lean_ctor_get(x_34, 0);
x_103 = lean_ctor_get(x_34, 1);
lean_dec(x_103);
x_104 = l_String_posOfAux___main___closed__1;
if (x_104 == 0)
{
uint8_t x_105; 
x_105 = !lean_is_exclusive(x_2);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_ctor_get(x_2, 0);
lean_dec(x_106);
x_107 = l_PersistentHashMap_isUnaryNode___rarg(x_102);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; uint8_t x_109; lean_object* x_110; 
lean_ctor_set(x_11, 0, x_102);
x_108 = lean_array_set(x_32, x_9, x_11);
lean_dec(x_9);
lean_ctor_set(x_2, 0, x_108);
x_109 = 1;
x_110 = lean_box(x_109);
lean_ctor_set(x_34, 1, x_110);
lean_ctor_set(x_34, 0, x_2);
return x_34;
}
else
{
lean_object* x_111; uint8_t x_112; 
lean_free_object(x_34);
lean_dec(x_102);
lean_free_object(x_11);
x_111 = lean_ctor_get(x_107, 0);
lean_inc(x_111);
lean_dec(x_107);
x_112 = !lean_is_exclusive(x_111);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; lean_object* x_118; 
x_113 = lean_ctor_get(x_111, 0);
x_114 = lean_ctor_get(x_111, 1);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
x_116 = lean_array_set(x_32, x_9, x_115);
lean_dec(x_9);
lean_ctor_set(x_2, 0, x_116);
x_117 = 1;
x_118 = lean_box(x_117);
lean_ctor_set(x_111, 1, x_118);
lean_ctor_set(x_111, 0, x_2);
return x_111;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; lean_object* x_124; lean_object* x_125; 
x_119 = lean_ctor_get(x_111, 0);
x_120 = lean_ctor_get(x_111, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_111);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
x_122 = lean_array_set(x_32, x_9, x_121);
lean_dec(x_9);
lean_ctor_set(x_2, 0, x_122);
x_123 = 1;
x_124 = lean_box(x_123);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_2);
lean_ctor_set(x_125, 1, x_124);
return x_125;
}
}
}
else
{
lean_object* x_126; 
lean_dec(x_2);
x_126 = l_PersistentHashMap_isUnaryNode___rarg(x_102);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; lean_object* x_128; uint8_t x_129; lean_object* x_130; 
lean_ctor_set(x_11, 0, x_102);
x_127 = lean_array_set(x_32, x_9, x_11);
lean_dec(x_9);
x_128 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_128, 0, x_127);
x_129 = 1;
x_130 = lean_box(x_129);
lean_ctor_set(x_34, 1, x_130);
lean_ctor_set(x_34, 0, x_128);
return x_34;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; lean_object* x_139; lean_object* x_140; 
lean_free_object(x_34);
lean_dec(x_102);
lean_free_object(x_11);
x_131 = lean_ctor_get(x_126, 0);
lean_inc(x_131);
lean_dec(x_126);
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_134 = x_131;
} else {
 lean_dec_ref(x_131);
 x_134 = lean_box(0);
}
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_132);
lean_ctor_set(x_135, 1, x_133);
x_136 = lean_array_set(x_32, x_9, x_135);
lean_dec(x_9);
x_137 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_137, 0, x_136);
x_138 = 1;
x_139 = lean_box(x_138);
if (lean_is_scalar(x_134)) {
 x_140 = lean_alloc_ctor(0, 2, 0);
} else {
 x_140 = x_134;
}
lean_ctor_set(x_140, 0, x_137);
lean_ctor_set(x_140, 1, x_139);
return x_140;
}
}
}
else
{
uint8_t x_141; lean_object* x_142; 
lean_dec(x_102);
lean_dec(x_32);
lean_free_object(x_11);
lean_dec(x_9);
x_141 = 0;
x_142 = lean_box(x_141);
lean_ctor_set(x_34, 1, x_142);
lean_ctor_set(x_34, 0, x_2);
return x_34;
}
}
else
{
lean_object* x_143; uint8_t x_144; 
x_143 = lean_ctor_get(x_34, 0);
lean_inc(x_143);
lean_dec(x_34);
x_144 = l_String_posOfAux___main___closed__1;
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; 
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 x_145 = x_2;
} else {
 lean_dec_ref(x_2);
 x_145 = lean_box(0);
}
x_146 = l_PersistentHashMap_isUnaryNode___rarg(x_143);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; lean_object* x_148; uint8_t x_149; lean_object* x_150; lean_object* x_151; 
lean_ctor_set(x_11, 0, x_143);
x_147 = lean_array_set(x_32, x_9, x_11);
lean_dec(x_9);
if (lean_is_scalar(x_145)) {
 x_148 = lean_alloc_ctor(0, 1, 0);
} else {
 x_148 = x_145;
}
lean_ctor_set(x_148, 0, x_147);
x_149 = 1;
x_150 = lean_box(x_149);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_148);
lean_ctor_set(x_151, 1, x_150);
return x_151;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; lean_object* x_160; lean_object* x_161; 
lean_dec(x_143);
lean_free_object(x_11);
x_152 = lean_ctor_get(x_146, 0);
lean_inc(x_152);
lean_dec(x_146);
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_152, 1);
lean_inc(x_154);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 lean_ctor_release(x_152, 1);
 x_155 = x_152;
} else {
 lean_dec_ref(x_152);
 x_155 = lean_box(0);
}
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_153);
lean_ctor_set(x_156, 1, x_154);
x_157 = lean_array_set(x_32, x_9, x_156);
lean_dec(x_9);
if (lean_is_scalar(x_145)) {
 x_158 = lean_alloc_ctor(0, 1, 0);
} else {
 x_158 = x_145;
}
lean_ctor_set(x_158, 0, x_157);
x_159 = 1;
x_160 = lean_box(x_159);
if (lean_is_scalar(x_155)) {
 x_161 = lean_alloc_ctor(0, 2, 0);
} else {
 x_161 = x_155;
}
lean_ctor_set(x_161, 0, x_158);
lean_ctor_set(x_161, 1, x_160);
return x_161;
}
}
else
{
uint8_t x_162; lean_object* x_163; lean_object* x_164; 
lean_dec(x_143);
lean_dec(x_32);
lean_free_object(x_11);
lean_dec(x_9);
x_162 = 0;
x_163 = lean_box(x_162);
x_164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_164, 0, x_2);
lean_ctor_set(x_164, 1, x_163);
return x_164;
}
}
}
}
else
{
lean_object* x_165; lean_object* x_166; size_t x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; 
x_165 = lean_ctor_get(x_11, 0);
lean_inc(x_165);
lean_dec(x_11);
x_166 = lean_array_set(x_5, x_9, x_10);
x_167 = x_3 >> x_6;
x_168 = l_PersistentHashMap_eraseAux___main___rarg(x_1, x_165, x_167, x_4);
x_169 = lean_ctor_get(x_168, 1);
lean_inc(x_169);
x_170 = lean_unbox(x_169);
lean_dec(x_169);
if (x_170 == 0)
{
lean_object* x_171; lean_object* x_172; uint8_t x_173; 
x_171 = lean_ctor_get(x_168, 0);
lean_inc(x_171);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 x_172 = x_168;
} else {
 lean_dec_ref(x_168);
 x_172 = lean_box(0);
}
x_173 = l_String_posOfAux___main___closed__2;
if (x_173 == 0)
{
lean_object* x_174; lean_object* x_175; 
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 x_174 = x_2;
} else {
 lean_dec_ref(x_2);
 x_174 = lean_box(0);
}
x_175 = l_PersistentHashMap_isUnaryNode___rarg(x_171);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; uint8_t x_179; lean_object* x_180; lean_object* x_181; 
x_176 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_176, 0, x_171);
x_177 = lean_array_set(x_166, x_9, x_176);
lean_dec(x_9);
if (lean_is_scalar(x_174)) {
 x_178 = lean_alloc_ctor(0, 1, 0);
} else {
 x_178 = x_174;
}
lean_ctor_set(x_178, 0, x_177);
x_179 = 1;
x_180 = lean_box(x_179);
if (lean_is_scalar(x_172)) {
 x_181 = lean_alloc_ctor(0, 2, 0);
} else {
 x_181 = x_172;
}
lean_ctor_set(x_181, 0, x_178);
lean_ctor_set(x_181, 1, x_180);
return x_181;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; uint8_t x_189; lean_object* x_190; lean_object* x_191; 
lean_dec(x_172);
lean_dec(x_171);
x_182 = lean_ctor_get(x_175, 0);
lean_inc(x_182);
lean_dec(x_175);
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_182, 1);
lean_inc(x_184);
if (lean_is_exclusive(x_182)) {
 lean_ctor_release(x_182, 0);
 lean_ctor_release(x_182, 1);
 x_185 = x_182;
} else {
 lean_dec_ref(x_182);
 x_185 = lean_box(0);
}
x_186 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_186, 0, x_183);
lean_ctor_set(x_186, 1, x_184);
x_187 = lean_array_set(x_166, x_9, x_186);
lean_dec(x_9);
if (lean_is_scalar(x_174)) {
 x_188 = lean_alloc_ctor(0, 1, 0);
} else {
 x_188 = x_174;
}
lean_ctor_set(x_188, 0, x_187);
x_189 = 1;
x_190 = lean_box(x_189);
if (lean_is_scalar(x_185)) {
 x_191 = lean_alloc_ctor(0, 2, 0);
} else {
 x_191 = x_185;
}
lean_ctor_set(x_191, 0, x_188);
lean_ctor_set(x_191, 1, x_190);
return x_191;
}
}
else
{
uint8_t x_192; lean_object* x_193; lean_object* x_194; 
lean_dec(x_171);
lean_dec(x_166);
lean_dec(x_9);
x_192 = 0;
x_193 = lean_box(x_192);
if (lean_is_scalar(x_172)) {
 x_194 = lean_alloc_ctor(0, 2, 0);
} else {
 x_194 = x_172;
}
lean_ctor_set(x_194, 0, x_2);
lean_ctor_set(x_194, 1, x_193);
return x_194;
}
}
else
{
lean_object* x_195; lean_object* x_196; uint8_t x_197; 
x_195 = lean_ctor_get(x_168, 0);
lean_inc(x_195);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 x_196 = x_168;
} else {
 lean_dec_ref(x_168);
 x_196 = lean_box(0);
}
x_197 = l_String_posOfAux___main___closed__1;
if (x_197 == 0)
{
lean_object* x_198; lean_object* x_199; 
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 x_198 = x_2;
} else {
 lean_dec_ref(x_2);
 x_198 = lean_box(0);
}
x_199 = l_PersistentHashMap_isUnaryNode___rarg(x_195);
if (lean_obj_tag(x_199) == 0)
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; uint8_t x_203; lean_object* x_204; lean_object* x_205; 
x_200 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_200, 0, x_195);
x_201 = lean_array_set(x_166, x_9, x_200);
lean_dec(x_9);
if (lean_is_scalar(x_198)) {
 x_202 = lean_alloc_ctor(0, 1, 0);
} else {
 x_202 = x_198;
}
lean_ctor_set(x_202, 0, x_201);
x_203 = 1;
x_204 = lean_box(x_203);
if (lean_is_scalar(x_196)) {
 x_205 = lean_alloc_ctor(0, 2, 0);
} else {
 x_205 = x_196;
}
lean_ctor_set(x_205, 0, x_202);
lean_ctor_set(x_205, 1, x_204);
return x_205;
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; uint8_t x_213; lean_object* x_214; lean_object* x_215; 
lean_dec(x_196);
lean_dec(x_195);
x_206 = lean_ctor_get(x_199, 0);
lean_inc(x_206);
lean_dec(x_199);
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_206, 1);
lean_inc(x_208);
if (lean_is_exclusive(x_206)) {
 lean_ctor_release(x_206, 0);
 lean_ctor_release(x_206, 1);
 x_209 = x_206;
} else {
 lean_dec_ref(x_206);
 x_209 = lean_box(0);
}
x_210 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_210, 0, x_207);
lean_ctor_set(x_210, 1, x_208);
x_211 = lean_array_set(x_166, x_9, x_210);
lean_dec(x_9);
if (lean_is_scalar(x_198)) {
 x_212 = lean_alloc_ctor(0, 1, 0);
} else {
 x_212 = x_198;
}
lean_ctor_set(x_212, 0, x_211);
x_213 = 1;
x_214 = lean_box(x_213);
if (lean_is_scalar(x_209)) {
 x_215 = lean_alloc_ctor(0, 2, 0);
} else {
 x_215 = x_209;
}
lean_ctor_set(x_215, 0, x_212);
lean_ctor_set(x_215, 1, x_214);
return x_215;
}
}
else
{
uint8_t x_216; lean_object* x_217; lean_object* x_218; 
lean_dec(x_195);
lean_dec(x_166);
lean_dec(x_9);
x_216 = 0;
x_217 = lean_box(x_216);
if (lean_is_scalar(x_196)) {
 x_218 = lean_alloc_ctor(0, 2, 0);
} else {
 x_218 = x_196;
}
lean_ctor_set(x_218, 0, x_2);
lean_ctor_set(x_218, 1, x_217);
return x_218;
}
}
}
}
default: 
{
uint8_t x_219; lean_object* x_220; lean_object* x_221; 
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_219 = 0;
x_220 = lean_box(x_219);
x_221 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_221, 0, x_2);
lean_ctor_set(x_221, 1, x_220);
return x_221;
}
}
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_222 = lean_ctor_get(x_2, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_2, 1);
lean_inc(x_223);
x_224 = lean_unsigned_to_nat(0u);
x_225 = l_Array_indexOfAux___main___rarg(x_1, x_222, x_4, x_224);
if (lean_obj_tag(x_225) == 0)
{
uint8_t x_226; lean_object* x_227; lean_object* x_228; 
lean_dec(x_223);
lean_dec(x_222);
x_226 = 0;
x_227 = lean_box(x_226);
x_228 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_228, 0, x_2);
lean_ctor_set(x_228, 1, x_227);
return x_228;
}
else
{
uint8_t x_229; 
x_229 = !lean_is_exclusive(x_2);
if (x_229 == 0)
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; uint8_t x_235; lean_object* x_236; lean_object* x_237; 
x_230 = lean_ctor_get(x_2, 1);
lean_dec(x_230);
x_231 = lean_ctor_get(x_2, 0);
lean_dec(x_231);
x_232 = lean_ctor_get(x_225, 0);
lean_inc(x_232);
lean_dec(x_225);
x_233 = l_Array_eraseIdx_x27___rarg(x_222, x_232);
x_234 = l_Array_eraseIdx_x27___rarg(x_223, x_232);
lean_dec(x_232);
lean_ctor_set(x_2, 1, x_234);
lean_ctor_set(x_2, 0, x_233);
x_235 = 1;
x_236 = lean_box(x_235);
x_237 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_237, 0, x_2);
lean_ctor_set(x_237, 1, x_236);
return x_237;
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; uint8_t x_242; lean_object* x_243; lean_object* x_244; 
lean_dec(x_2);
x_238 = lean_ctor_get(x_225, 0);
lean_inc(x_238);
lean_dec(x_225);
x_239 = l_Array_eraseIdx_x27___rarg(x_222, x_238);
x_240 = l_Array_eraseIdx_x27___rarg(x_223, x_238);
lean_dec(x_238);
x_241 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_241, 0, x_239);
lean_ctor_set(x_241, 1, x_240);
x_242 = 1;
x_243 = lean_box(x_242);
x_244 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_244, 0, x_241);
lean_ctor_set(x_244, 1, x_243);
return x_244;
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; 
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
x_13 = lean_unbox(x_12);
lean_dec(x_12);
x_14 = l_coeDecidableEq(x_13);
if (x_14 == 0)
{
lean_ctor_set(x_3, 0, x_11);
return x_3;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_7, x_15);
lean_dec(x_7);
lean_ctor_set(x_3, 1, x_16);
lean_ctor_set(x_3, 0, x_11);
return x_3;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_25; 
x_17 = lean_ctor_get(x_3, 0);
x_18 = lean_ctor_get(x_3, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_3);
lean_inc(x_4);
x_19 = lean_apply_1(x_2, x_4);
x_20 = lean_unbox_usize(x_19);
lean_dec(x_19);
x_21 = l_PersistentHashMap_eraseAux___main___rarg(x_1, x_17, x_20, x_4);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_unbox(x_23);
lean_dec(x_23);
x_25 = l_coeDecidableEq(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_22);
lean_ctor_set(x_26, 1, x_18);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_sub(x_18, x_27);
lean_dec(x_18);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_22);
lean_ctor_set(x_29, 1, x_28);
return x_29;
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
lean_object* l_PersistentHashMap_forM___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_2(x_1, x_3, x_4);
return x_5;
}
}
lean_object* l_PersistentHashMap_forM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_alloc_closure((void*)(l_PersistentHashMap_forM___rarg___lambda__1___boxed), 4, 1);
lean_closure_set(x_6, 0, x_5);
x_7 = lean_box(0);
x_8 = l_PersistentHashMap_foldlM___rarg(x_1, lean_box(0), x_2, x_3, x_4, x_6, x_7);
return x_8;
}
}
lean_object* l_PersistentHashMap_forM(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_PersistentHashMap_forM___rarg___boxed), 5, 0);
return x_4;
}
}
lean_object* l_PersistentHashMap_forM___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_PersistentHashMap_forM___rarg___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_PersistentHashMap_forM___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_PersistentHashMap_forM___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_PersistentHashMap_forM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_PersistentHashMap_forM(x_1, x_2, x_3);
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
