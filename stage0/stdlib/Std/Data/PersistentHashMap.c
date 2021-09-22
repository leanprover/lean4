// Lean compiler output
// Module: Std.Data.PersistentHashMap
// Imports: Init
#include <lean/lean.h>
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
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
size_t l_USize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_empty___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_isUnaryEntries___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_isEmpty___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAtCollisionNode___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_indexOfAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findEntryAux(lean_object*, lean_object*);
static lean_object* l_Std_PersistentHashMap_root___default___closed__1;
uint8_t l_USize_decEq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux_traverse___rarg(lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_instToStringStats;
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_find_x21(lean_object*, lean_object*);
static lean_object* l_Std_PersistentHashMap_foldlMAux___at_Std_PersistentHashMap_toList___spec__2___rarg___closed__1;
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_Stats_maxDepth___default;
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_stats(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlMAux_traverse___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT size_t l_Std_PersistentHashMap_mod2Shift(size_t, size_t);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findEntryAux___rarg(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_erase(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_collectStats___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_mkCollisionNode(lean_object*, lean_object*);
size_t l_USize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_Stats_numNull___default;
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlMAux_traverse___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlM___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_PersistentHashMap_Stats_toString___closed__2;
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_forM___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux_traverse(lean_object*, lean_object*);
static lean_object* l_Std_PersistentHashMap_root___default___closed__2;
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlMAux___at_Std_PersistentHashMap_toList___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_instInhabitedPersistentHashMap(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_Stats_toString(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_getCollisionNodeSize___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Std_PersistentHashMap_toList___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Nat_max(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insert(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_getCollisionNodeSize(lean_object*, lean_object*);
size_t l_USize_shiftRight(size_t, size_t);
LEAN_EXPORT size_t l_Std_PersistentHashMap_shift;
LEAN_EXPORT size_t l_Std_PersistentHashMap_mul2Shift(size_t, size_t);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlMAux___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlM(lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findEntryAtAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_toList___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_PersistentHashMap_stats___rarg___closed__1;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlM___at_Std_PersistentHashMap_toList___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlMAux_traverse___at_Std_PersistentHashMap_toList___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT size_t l_Std_PersistentHashMap_maxDepth;
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_containsAux___rarg(lean_object*, lean_object*, size_t, lean_object*);
size_t l_UInt64_toUSize(uint64_t);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_empty___rarg(lean_object*, lean_object*);
static lean_object* l_Std_PersistentHashMap_find_x21___rarg___closed__4;
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlMAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldl___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Std_PersistentHashMap_toList___spec__3___rarg(lean_object*, size_t, size_t, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_instInhabitedPersistentHashMap___rarg(lean_object*, lean_object*);
static lean_object* l_Std_PersistentHashMap_insertAux___rarg___closed__3;
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_isUnaryNode___rarg(lean_object*);
static lean_object* l_Std_PersistentHashMap_find_x21___rarg___closed__1;
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlM___at_Std_PersistentHashMap_toList___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_contains___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_toList(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_containsAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findEntryAux___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_PersistentHashMap_instToStringStats___closed__1;
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_forM___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_PersistentHashMap_find_x21___rarg___closed__2;
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_instInhabitedEntry(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_getOp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux(lean_object*, lean_object*);
static lean_object* l_Std_PersistentHashMap_Stats_toString___closed__4;
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_isUnaryEntries(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_isUnaryEntries___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_isEmpty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___rarg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlMAux_traverse___at_Std_PersistentHashMap_toList___spec__4___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l_Std_PersistentHashMap_instInhabitedNode___closed__2;
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_Stats_numNodes___default;
size_t l_USize_shiftLeft(size_t, size_t);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_containsAtAux___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_collectStats(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findEntry_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlMAux___at_Std_PersistentHashMap_toList___spec__2___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_stats___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_forM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_mul(size_t, size_t);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insert___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_getCollisionNodeSize___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_maxCollisions;
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAtCollisionNodeAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlM___at_Std_PersistentHashMap_toList___spec__1___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findD___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findD___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_find_x3f(lean_object*, lean_object*);
LEAN_EXPORT size_t l_Std_PersistentHashMap_div2Shift(size_t, size_t);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_mod2Shift___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldl(lean_object*, lean_object*, lean_object*);
size_t l_USize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findEntry_x3f___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_PersistentHashMap_Stats_toString___closed__3;
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_PersistentHashMap_instInhabitedNode___closed__1;
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_getOp___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static size_t l_Std_PersistentHashMap_insertAux___rarg___closed__1;
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_size___default;
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_containsAux___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_isUnaryNode___rarg___boxed(lean_object*);
extern lean_object* l_Id_instMonadId;
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findEntryAtAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t l_USize_decLe(size_t, size_t);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux___rarg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Std_PersistentHashMap_collectStats___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_PersistentHashMap_find_x21___rarg___closed__3;
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_root___default(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
static lean_object* l_Std_PersistentHashMap_mkCollisionNode___rarg___closed__1;
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_mul2Shift___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Std_PersistentHashMap_toList___spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_erase___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAtCollisionNode(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_stats___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_eraseIdx_x27___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___rarg(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_isUnaryNode(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_eraseAux___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_isEmpty___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_contains(lean_object*, lean_object*);
static lean_object* l_Std_PersistentHashMap_Stats_toString___closed__5;
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findD(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Std_PersistentHashMap_collectStats___spec__1___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT size_t l_Std_PersistentHashMap_branching;
lean_object* lean_mk_array(lean_object*, lean_object*);
static size_t l_Std_PersistentHashMap_insertAux___rarg___closed__2;
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux_traverse___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_forM___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlMAux_traverse(lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_find_x21___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_instInhabitedPersistentHashMap___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldl___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_div2Shift___boxed(lean_object*, lean_object*);
static lean_object* l_Std_PersistentHashMap_Stats_toString___closed__1;
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_eraseAux___rarg(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_find_x3f___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_forM(lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_eraseAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Std_PersistentHashMap_collectStats___spec__1(lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_empty(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
static lean_object* l_Std_PersistentHashMap_mkEmptyEntriesArray___closed__1;
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAtCollisionNodeAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_instInhabitedNode(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlMAux_traverse___at_Std_PersistentHashMap_toList___spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findEntryAtAux___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_PersistentHashMap_isEmpty___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_containsAtAux(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_PersistentHashMap_containsAtAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlMAux(lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlMAux___at_Std_PersistentHashMap_toList___spec__2___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_mkCollisionNode___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_Stats_numCollisions___default;
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_instInhabitedEntry(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_box(2);
return x_4;
}
}
static lean_object* _init_l_Std_PersistentHashMap_instInhabitedNode___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_PersistentHashMap_instInhabitedNode___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_PersistentHashMap_instInhabitedNode___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_instInhabitedNode(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_PersistentHashMap_instInhabitedNode___closed__2;
return x_3;
}
}
static size_t _init_l_Std_PersistentHashMap_shift() {
_start:
{
size_t x_1; 
x_1 = 5;
return x_1;
}
}
static size_t _init_l_Std_PersistentHashMap_branching() {
_start:
{
size_t x_1; 
x_1 = 32;
return x_1;
}
}
static size_t _init_l_Std_PersistentHashMap_maxDepth() {
_start:
{
size_t x_1; 
x_1 = 7;
return x_1;
}
}
static lean_object* _init_l_Std_PersistentHashMap_maxCollisions() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(4u);
return x_1;
}
}
static lean_object* _init_l_Std_PersistentHashMap_mkEmptyEntriesArray___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(2);
x_2 = lean_unsigned_to_nat(32u);
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_PersistentHashMap_mkEmptyEntriesArray___closed__1;
return x_3;
}
}
static lean_object* _init_l_Std_PersistentHashMap_root___default___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Std_PersistentHashMap_root___default___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Std_PersistentHashMap_root___default___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_root___default(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_PersistentHashMap_root___default___closed__2;
return x_3;
}
}
static lean_object* _init_l_Std_PersistentHashMap_size___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(0u);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_empty___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Std_PersistentHashMap_root___default___closed__2;
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_empty(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_empty___rarg___boxed), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_empty___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_PersistentHashMap_empty___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Std_PersistentHashMap_isEmpty___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_isEmpty(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_isEmpty___rarg___boxed), 1, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_isEmpty___rarg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Std_PersistentHashMap_isEmpty___rarg(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_isEmpty___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_PersistentHashMap_isEmpty(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_instInhabitedPersistentHashMap___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Std_PersistentHashMap_root___default___closed__2;
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_instInhabitedPersistentHashMap(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_instInhabitedPersistentHashMap___rarg___boxed), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_instInhabitedPersistentHashMap___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_PersistentHashMap_instInhabitedPersistentHashMap___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_mkEmptyEntries(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_PersistentHashMap_root___default___closed__2;
return x_3;
}
}
LEAN_EXPORT size_t l_Std_PersistentHashMap_mul2Shift(size_t x_1, size_t x_2) {
_start:
{
size_t x_3; 
x_3 = x_1 << x_2 % (sizeof(size_t) * 8);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_mul2Shift___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Std_PersistentHashMap_mul2Shift(x_3, x_4);
x_6 = lean_box_usize(x_5);
return x_6;
}
}
LEAN_EXPORT size_t l_Std_PersistentHashMap_div2Shift(size_t x_1, size_t x_2) {
_start:
{
size_t x_3; 
x_3 = x_1 >> x_2 % (sizeof(size_t) * 8);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_div2Shift___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Std_PersistentHashMap_div2Shift(x_3, x_4);
x_6 = lean_box_usize(x_5);
return x_6;
}
}
LEAN_EXPORT size_t l_Std_PersistentHashMap_mod2Shift(size_t x_1, size_t x_2) {
_start:
{
size_t x_3; size_t x_4; size_t x_5; size_t x_6; 
x_3 = 1;
x_4 = x_3 << x_2 % (sizeof(size_t) * 8);
x_5 = x_4 - x_3;
x_6 = x_1 & x_5;
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_mod2Shift___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Std_PersistentHashMap_mod2Shift(x_3, x_4);
x_6 = lean_box_usize(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAtCollisionNodeAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_array_fget(x_6, x_3);
lean_inc(x_1);
lean_inc(x_4);
x_19 = lean_apply_2(x_1, x_4, x_18);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_7);
lean_dec(x_6);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_3, x_21);
lean_dec(x_3);
x_3 = x_22;
goto _start;
}
else
{
uint8_t x_24; 
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_2);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_2, 1);
lean_dec(x_25);
x_26 = lean_ctor_get(x_2, 0);
lean_dec(x_26);
x_27 = lean_array_fset(x_6, x_3, x_4);
x_28 = lean_array_fset(x_7, x_3, x_5);
lean_dec(x_3);
lean_ctor_set(x_2, 1, x_28);
lean_ctor_set(x_2, 0, x_27);
return x_2;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_2);
x_29 = lean_array_fset(x_6, x_3, x_4);
x_30 = lean_array_fset(x_7, x_3, x_5);
lean_dec(x_3);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAtCollisionNodeAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_insertAtCollisionNodeAux___rarg), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAtCollisionNode___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Std_PersistentHashMap_insertAtCollisionNodeAux___rarg(x_1, x_2, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAtCollisionNode(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_insertAtCollisionNode___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_getCollisionNodeSize___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_array_get_size(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_getCollisionNodeSize(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_getCollisionNodeSize___rarg___boxed), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_getCollisionNodeSize___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_PersistentHashMap_getCollisionNodeSize___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_PersistentHashMap_mkCollisionNode___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_mkCollisionNode___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = l_Std_PersistentHashMap_mkCollisionNode___rarg___closed__1;
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
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_mkCollisionNode(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_mkCollisionNode___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux_traverse___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_get_size(x_4);
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint64_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_11 = lean_array_fget(x_4, x_7);
x_12 = lean_array_fget(x_5, x_7);
lean_inc(x_2);
lean_inc(x_11);
x_13 = lean_apply_1(x_2, x_11);
x_14 = lean_unbox_uint64(x_13);
lean_dec(x_13);
x_15 = (size_t)x_14;
x_16 = 1;
x_17 = x_3 - x_16;
x_18 = 5;
x_19 = x_18 * x_17;
x_20 = x_15 >> x_19 % (sizeof(size_t) * 8);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_7, x_21);
lean_dec(x_7);
lean_inc(x_2);
lean_inc(x_1);
x_23 = l_Std_PersistentHashMap_insertAux___rarg(x_1, x_2, x_8, x_20, x_3, x_11, x_12);
x_6 = lean_box(0);
x_7 = x_22;
x_8 = x_23;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux_traverse(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_insertAux_traverse___rarg___boxed), 8, 0);
return x_3;
}
}
static size_t _init_l_Std_PersistentHashMap_insertAux___rarg___closed__1() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = 5;
x_3 = x_1 << x_2 % (sizeof(size_t) * 8);
return x_3;
}
}
static size_t _init_l_Std_PersistentHashMap_insertAux___rarg___closed__2() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = l_Std_PersistentHashMap_insertAux___rarg___closed__1;
x_3 = x_2 - x_1;
return x_3;
}
}
static lean_object* _init_l_Std_PersistentHashMap_insertAux___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7) {
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
x_12 = l_Std_PersistentHashMap_insertAux___rarg___closed__2;
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
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_17, 0);
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_inc(x_6);
x_23 = lean_apply_2(x_1, x_6, x_21);
x_24 = lean_unbox(x_23);
lean_dec(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_free_object(x_17);
x_25 = l_Std_PersistentHashMap_mkCollisionNode___rarg(x_21, x_22, x_6, x_7);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_array_fset(x_19, x_14, x_26);
lean_dec(x_14);
lean_ctor_set(x_3, 0, x_27);
return x_3;
}
else
{
lean_object* x_28; 
lean_dec(x_22);
lean_dec(x_21);
lean_ctor_set(x_17, 1, x_7);
lean_ctor_set(x_17, 0, x_6);
x_28 = lean_array_fset(x_19, x_14, x_17);
lean_dec(x_14);
lean_ctor_set(x_3, 0, x_28);
return x_3;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_ctor_get(x_17, 0);
x_30 = lean_ctor_get(x_17, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_17);
lean_inc(x_29);
lean_inc(x_6);
x_31 = lean_apply_2(x_1, x_6, x_29);
x_32 = lean_unbox(x_31);
lean_dec(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = l_Std_PersistentHashMap_mkCollisionNode___rarg(x_29, x_30, x_6, x_7);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = lean_array_fset(x_19, x_14, x_34);
lean_dec(x_14);
lean_ctor_set(x_3, 0, x_35);
return x_3;
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_30);
lean_dec(x_29);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_6);
lean_ctor_set(x_36, 1, x_7);
x_37 = lean_array_fset(x_19, x_14, x_36);
lean_dec(x_14);
lean_ctor_set(x_3, 0, x_37);
return x_3;
}
}
}
case 1:
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_17);
if (x_38 == 0)
{
lean_object* x_39; size_t x_40; size_t x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_17, 0);
x_40 = x_4 >> x_11 % (sizeof(size_t) * 8);
x_41 = x_5 + x_10;
x_42 = l_Std_PersistentHashMap_insertAux___rarg(x_1, x_2, x_39, x_40, x_41, x_6, x_7);
lean_ctor_set(x_17, 0, x_42);
x_43 = lean_array_fset(x_19, x_14, x_17);
lean_dec(x_14);
lean_ctor_set(x_3, 0, x_43);
return x_3;
}
else
{
lean_object* x_44; size_t x_45; size_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_44 = lean_ctor_get(x_17, 0);
lean_inc(x_44);
lean_dec(x_17);
x_45 = x_4 >> x_11 % (sizeof(size_t) * 8);
x_46 = x_5 + x_10;
x_47 = l_Std_PersistentHashMap_insertAux___rarg(x_1, x_2, x_44, x_45, x_46, x_6, x_7);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_49 = lean_array_fset(x_19, x_14, x_48);
lean_dec(x_14);
lean_ctor_set(x_3, 0, x_49);
return x_3;
}
}
default: 
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_2);
lean_dec(x_1);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_6);
lean_ctor_set(x_50, 1, x_7);
x_51 = lean_array_fset(x_19, x_14, x_50);
lean_dec(x_14);
lean_ctor_set(x_3, 0, x_51);
return x_3;
}
}
}
}
else
{
lean_object* x_52; size_t x_53; size_t x_54; size_t x_55; size_t x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_52 = lean_ctor_get(x_3, 0);
lean_inc(x_52);
lean_dec(x_3);
x_53 = 1;
x_54 = 5;
x_55 = l_Std_PersistentHashMap_insertAux___rarg___closed__2;
x_56 = x_4 & x_55;
x_57 = lean_usize_to_nat(x_56);
x_58 = lean_array_get_size(x_52);
x_59 = lean_nat_dec_lt(x_57, x_58);
lean_dec(x_58);
if (x_59 == 0)
{
lean_object* x_60; 
lean_dec(x_57);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_60 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_60, 0, x_52);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_array_fget(x_52, x_57);
x_62 = lean_box(2);
x_63 = lean_array_fset(x_52, x_57, x_62);
switch (lean_obj_tag(x_61)) {
case 0:
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
lean_dec(x_2);
x_64 = lean_ctor_get(x_61, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_61, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_66 = x_61;
} else {
 lean_dec_ref(x_61);
 x_66 = lean_box(0);
}
lean_inc(x_64);
lean_inc(x_6);
x_67 = lean_apply_2(x_1, x_6, x_64);
x_68 = lean_unbox(x_67);
lean_dec(x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_66);
x_69 = l_Std_PersistentHashMap_mkCollisionNode___rarg(x_64, x_65, x_6, x_7);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_69);
x_71 = lean_array_fset(x_63, x_57, x_70);
lean_dec(x_57);
x_72 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_72, 0, x_71);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_65);
lean_dec(x_64);
if (lean_is_scalar(x_66)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_66;
}
lean_ctor_set(x_73, 0, x_6);
lean_ctor_set(x_73, 1, x_7);
x_74 = lean_array_fset(x_63, x_57, x_73);
lean_dec(x_57);
x_75 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_75, 0, x_74);
return x_75;
}
}
case 1:
{
lean_object* x_76; lean_object* x_77; size_t x_78; size_t x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_76 = lean_ctor_get(x_61, 0);
lean_inc(x_76);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 x_77 = x_61;
} else {
 lean_dec_ref(x_61);
 x_77 = lean_box(0);
}
x_78 = x_4 >> x_54 % (sizeof(size_t) * 8);
x_79 = x_5 + x_53;
x_80 = l_Std_PersistentHashMap_insertAux___rarg(x_1, x_2, x_76, x_78, x_79, x_6, x_7);
if (lean_is_scalar(x_77)) {
 x_81 = lean_alloc_ctor(1, 1, 0);
} else {
 x_81 = x_77;
}
lean_ctor_set(x_81, 0, x_80);
x_82 = lean_array_fset(x_63, x_57, x_81);
lean_dec(x_57);
x_83 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_83, 0, x_82);
return x_83;
}
default: 
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_2);
lean_dec(x_1);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_6);
lean_ctor_set(x_84, 1, x_7);
x_85 = lean_array_fset(x_63, x_57, x_84);
lean_dec(x_57);
x_86 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_86, 0, x_85);
return x_86;
}
}
}
}
}
else
{
uint8_t x_87; 
x_87 = !lean_is_exclusive(x_3);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; size_t x_90; uint8_t x_91; 
x_88 = lean_unsigned_to_nat(0u);
lean_inc(x_1);
x_89 = l_Std_PersistentHashMap_insertAtCollisionNodeAux___rarg(x_1, x_3, x_88, x_6, x_7);
x_90 = 7;
x_91 = x_90 <= x_5;
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_92 = l_Std_PersistentHashMap_getCollisionNodeSize___rarg(x_89);
x_93 = lean_unsigned_to_nat(4u);
x_94 = lean_nat_dec_lt(x_92, x_93);
lean_dec(x_92);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_95 = lean_ctor_get(x_89, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_89, 1);
lean_inc(x_96);
lean_dec(x_89);
x_97 = l_Std_PersistentHashMap_insertAux___rarg___closed__3;
x_98 = l_Std_PersistentHashMap_insertAux_traverse___rarg(x_1, x_2, x_5, x_95, x_96, lean_box(0), x_88, x_97);
lean_dec(x_96);
lean_dec(x_95);
return x_98;
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_89;
}
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_89;
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; size_t x_104; uint8_t x_105; 
x_99 = lean_ctor_get(x_3, 0);
x_100 = lean_ctor_get(x_3, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_3);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
x_102 = lean_unsigned_to_nat(0u);
lean_inc(x_1);
x_103 = l_Std_PersistentHashMap_insertAtCollisionNodeAux___rarg(x_1, x_101, x_102, x_6, x_7);
x_104 = 7;
x_105 = x_104 <= x_5;
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_106 = l_Std_PersistentHashMap_getCollisionNodeSize___rarg(x_103);
x_107 = lean_unsigned_to_nat(4u);
x_108 = lean_nat_dec_lt(x_106, x_107);
lean_dec(x_106);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_109 = lean_ctor_get(x_103, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_103, 1);
lean_inc(x_110);
lean_dec(x_103);
x_111 = l_Std_PersistentHashMap_insertAux___rarg___closed__3;
x_112 = l_Std_PersistentHashMap_insertAux_traverse___rarg(x_1, x_2, x_5, x_109, x_110, lean_box(0), x_102, x_111);
lean_dec(x_110);
lean_dec(x_109);
return x_112;
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_103;
}
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_103;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_insertAux___rarg___boxed), 7, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux_traverse___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; lean_object* x_10; 
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l_Std_PersistentHashMap_insertAux_traverse___rarg(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insertAux___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_10 = l_Std_PersistentHashMap_insertAux___rarg(x_1, x_2, x_3, x_8, x_9, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insert___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint64_t x_10; size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_2);
lean_inc(x_4);
x_9 = lean_apply_1(x_2, x_4);
x_10 = lean_unbox_uint64(x_9);
lean_dec(x_9);
x_11 = (size_t)x_10;
x_12 = 1;
x_13 = l_Std_PersistentHashMap_insertAux___rarg(x_1, x_2, x_7, x_11, x_12, x_4, x_5);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_8, x_14);
lean_dec(x_8);
lean_ctor_set(x_3, 1, x_15);
lean_ctor_set(x_3, 0, x_13);
return x_3;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint64_t x_19; size_t x_20; size_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_16 = lean_ctor_get(x_3, 0);
x_17 = lean_ctor_get(x_3, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_3);
lean_inc(x_2);
lean_inc(x_4);
x_18 = lean_apply_1(x_2, x_4);
x_19 = lean_unbox_uint64(x_18);
lean_dec(x_18);
x_20 = (size_t)x_19;
x_21 = 1;
x_22 = l_Std_PersistentHashMap_insertAux___rarg(x_1, x_2, x_16, x_20, x_21, x_4, x_5);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_17, x_23);
lean_dec(x_17);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_insert(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_insert___rarg), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_array_fget(x_2, x_5);
lean_inc(x_1);
lean_inc(x_6);
x_11 = lean_apply_2(x_1, x_6, x_10);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_5, x_13);
lean_dec(x_5);
x_4 = lean_box(0);
x_5 = x_14;
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_6);
lean_dec(x_1);
x_16 = lean_array_fget(x_3, x_5);
lean_dec(x_5);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_findAtAux___rarg___boxed), 6, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAtAux___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_PersistentHashMap_findAtAux___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; size_t x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
x_6 = 5;
x_7 = l_Std_PersistentHashMap_insertAux___rarg___closed__2;
x_8 = x_3 & x_7;
x_9 = lean_usize_to_nat(x_8);
x_10 = lean_box(2);
x_11 = lean_array_get(x_10, x_5, x_9);
lean_dec(x_9);
lean_dec(x_5);
switch (lean_obj_tag(x_11)) {
case 0:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_apply_2(x_1, x_4, x_12);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_13);
x_16 = lean_box(0);
return x_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_13);
return x_17;
}
}
case 1:
{
lean_object* x_18; size_t x_19; 
x_18 = lean_ctor_get(x_11, 0);
lean_inc(x_18);
lean_dec(x_11);
x_19 = x_3 >> x_6 % (sizeof(size_t) * 8);
x_2 = x_18;
x_3 = x_19;
goto _start;
}
default: 
{
lean_object* x_21; 
lean_dec(x_4);
lean_dec(x_1);
x_21 = lean_box(0);
return x_21;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_2, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_2, 1);
lean_inc(x_23);
lean_dec(x_2);
x_24 = lean_unsigned_to_nat(0u);
x_25 = l_Std_PersistentHashMap_findAtAux___rarg(x_1, x_22, x_23, lean_box(0), x_24, x_4);
lean_dec(x_23);
lean_dec(x_22);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_findAux___rarg___boxed), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findAux___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Std_PersistentHashMap_findAux___rarg(x_1, x_2, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_find_x3f___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint64_t x_7; size_t x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
lean_inc(x_4);
x_6 = lean_apply_1(x_2, x_4);
x_7 = lean_unbox_uint64(x_6);
lean_dec(x_6);
x_8 = (size_t)x_7;
x_9 = l_Std_PersistentHashMap_findAux___rarg(x_1, x_5, x_8, x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_find_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_find_x3f___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_getOp___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_PersistentHashMap_find_x3f___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_getOp(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_getOp___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findD___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_PersistentHashMap_find_x3f___rarg(x_1, x_2, x_3, x_4);
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
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findD(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_findD___rarg___boxed), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findD___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_PersistentHashMap_findD___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
return x_6;
}
}
static lean_object* _init_l_Std_PersistentHashMap_find_x21___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Std.Data.PersistentHashMap");
return x_1;
}
}
static lean_object* _init_l_Std_PersistentHashMap_find_x21___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Std.PersistentHashMap.find!");
return x_1;
}
}
static lean_object* _init_l_Std_PersistentHashMap_find_x21___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("key is not in the map");
return x_1;
}
}
static lean_object* _init_l_Std_PersistentHashMap_find_x21___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Std_PersistentHashMap_find_x21___rarg___closed__1;
x_2 = l_Std_PersistentHashMap_find_x21___rarg___closed__2;
x_3 = lean_unsigned_to_nat(158u);
x_4 = lean_unsigned_to_nat(14u);
x_5 = l_Std_PersistentHashMap_find_x21___rarg___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_find_x21___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_PersistentHashMap_find_x3f___rarg(x_1, x_2, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Std_PersistentHashMap_find_x21___rarg___closed__4;
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
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_find_x21(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_find_x21___rarg), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findEntryAtAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_array_fget(x_2, x_5);
lean_inc(x_1);
lean_inc(x_10);
lean_inc(x_6);
x_11 = lean_apply_2(x_1, x_6, x_10);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_10);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_5, x_13);
lean_dec(x_5);
x_4 = lean_box(0);
x_5 = x_14;
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_6);
lean_dec(x_1);
x_16 = lean_array_fget(x_3, x_5);
lean_dec(x_5);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findEntryAtAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_findEntryAtAux___rarg___boxed), 6, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findEntryAtAux___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_PersistentHashMap_findEntryAtAux___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findEntryAux___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; size_t x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
x_6 = 5;
x_7 = l_Std_PersistentHashMap_insertAux___rarg___closed__2;
x_8 = x_3 & x_7;
x_9 = lean_usize_to_nat(x_8);
x_10 = lean_box(2);
x_11 = lean_array_get(x_10, x_5, x_9);
lean_dec(x_9);
lean_dec(x_5);
switch (lean_obj_tag(x_11)) {
case 0:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_12);
x_14 = lean_apply_2(x_1, x_4, x_12);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_13);
lean_dec(x_12);
x_16 = lean_box(0);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_13);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
case 1:
{
lean_object* x_19; size_t x_20; 
x_19 = lean_ctor_get(x_11, 0);
lean_inc(x_19);
lean_dec(x_11);
x_20 = x_3 >> x_6 % (sizeof(size_t) * 8);
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
x_26 = l_Std_PersistentHashMap_findEntryAtAux___rarg(x_1, x_23, x_24, lean_box(0), x_25, x_4);
lean_dec(x_24);
lean_dec(x_23);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findEntryAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_findEntryAux___rarg___boxed), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findEntryAux___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Std_PersistentHashMap_findEntryAux___rarg(x_1, x_2, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findEntry_x3f___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint64_t x_7; size_t x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
lean_inc(x_4);
x_6 = lean_apply_1(x_2, x_4);
x_7 = lean_unbox_uint64(x_6);
lean_dec(x_6);
x_8 = (size_t)x_7;
x_9 = l_Std_PersistentHashMap_findEntryAux___rarg(x_1, x_5, x_8, x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_findEntry_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_findEntry_x3f___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Std_PersistentHashMap_containsAtAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_9 = 0;
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_array_fget(x_2, x_5);
lean_inc(x_1);
lean_inc(x_6);
x_11 = lean_apply_2(x_1, x_6, x_10);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_5, x_13);
lean_dec(x_5);
x_4 = lean_box(0);
x_5 = x_14;
goto _start;
}
else
{
uint8_t x_16; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_16 = 1;
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_containsAtAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_containsAtAux___rarg___boxed), 6, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_containsAtAux___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_Std_PersistentHashMap_containsAtAux___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_containsAux___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; size_t x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
x_6 = 5;
x_7 = l_Std_PersistentHashMap_insertAux___rarg___closed__2;
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
x_15 = x_3 >> x_6 % (sizeof(size_t) * 8);
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
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_2, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_2, 1);
lean_inc(x_20);
lean_dec(x_2);
x_21 = lean_unsigned_to_nat(0u);
x_22 = l_Std_PersistentHashMap_containsAtAux___rarg(x_1, x_19, x_20, lean_box(0), x_21, x_4);
lean_dec(x_20);
lean_dec(x_19);
x_23 = lean_box(x_22);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_containsAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_containsAux___rarg___boxed), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_containsAux___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Std_PersistentHashMap_containsAux___rarg(x_1, x_2, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_contains___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint64_t x_7; size_t x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
lean_inc(x_4);
x_6 = lean_apply_1(x_2, x_4);
x_7 = lean_unbox_uint64(x_6);
lean_dec(x_6);
x_8 = (size_t)x_7;
x_9 = l_Std_PersistentHashMap_containsAux___rarg(x_1, x_5, x_8, x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_contains(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_contains___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_isUnaryEntries___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_isUnaryEntries(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_isUnaryEntries___rarg___boxed), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_isUnaryEntries___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_PersistentHashMap_isUnaryEntries___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_isUnaryNode___rarg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_box(0);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Std_PersistentHashMap_isUnaryEntries___rarg(x_2, x_4, x_3);
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
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_isUnaryNode(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_isUnaryNode___rarg___boxed), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_isUnaryNode___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_PersistentHashMap_isUnaryNode___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_eraseAux___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; size_t x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = 5;
x_7 = l_Std_PersistentHashMap_insertAux___rarg___closed__2;
x_8 = x_3 & x_7;
x_9 = lean_usize_to_nat(x_8);
x_10 = lean_box(2);
x_11 = lean_array_get(x_10, x_5, x_9);
switch (lean_obj_tag(x_11)) {
case 0:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_apply_2(x_1, x_4, x_12);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
uint8_t x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_9);
lean_dec(x_5);
x_15 = 0;
x_16 = lean_box(x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_2);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_2);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_2, 0);
lean_dec(x_19);
x_20 = lean_array_set(x_5, x_9, x_10);
lean_dec(x_9);
lean_ctor_set(x_2, 0, x_20);
x_21 = 1;
x_22 = lean_box(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_2);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_2);
x_24 = lean_array_set(x_5, x_9, x_10);
lean_dec(x_9);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = 1;
x_27 = lean_box(x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_25);
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
x_32 = x_3 >> x_6 % (sizeof(size_t) * 8);
x_33 = l_Std_PersistentHashMap_eraseAux___rarg(x_1, x_30, x_32, x_4);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
x_35 = lean_unbox(x_34);
lean_dec(x_34);
if (x_35 == 0)
{
uint8_t x_36; 
lean_dec(x_31);
lean_free_object(x_11);
lean_dec(x_9);
x_36 = !lean_is_exclusive(x_33);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_33, 1);
lean_dec(x_37);
x_38 = lean_ctor_get(x_33, 0);
lean_dec(x_38);
x_39 = 0;
x_40 = lean_box(x_39);
lean_ctor_set(x_33, 1, x_40);
lean_ctor_set(x_33, 0, x_2);
return x_33;
}
else
{
uint8_t x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_33);
x_41 = 0;
x_42 = lean_box(x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_2);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
else
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_2);
if (x_44 == 0)
{
lean_object* x_45; uint8_t x_46; 
x_45 = lean_ctor_get(x_2, 0);
lean_dec(x_45);
x_46 = !lean_is_exclusive(x_33);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_33, 0);
x_48 = lean_ctor_get(x_33, 1);
lean_dec(x_48);
x_49 = l_Std_PersistentHashMap_isUnaryNode___rarg(x_47);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; uint8_t x_51; lean_object* x_52; 
lean_ctor_set(x_11, 0, x_47);
x_50 = lean_array_set(x_31, x_9, x_11);
lean_dec(x_9);
lean_ctor_set(x_2, 0, x_50);
x_51 = 1;
x_52 = lean_box(x_51);
lean_ctor_set(x_33, 1, x_52);
lean_ctor_set(x_33, 0, x_2);
return x_33;
}
else
{
lean_object* x_53; uint8_t x_54; 
lean_free_object(x_33);
lean_dec(x_47);
lean_free_object(x_11);
x_53 = lean_ctor_get(x_49, 0);
lean_inc(x_53);
lean_dec(x_49);
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; 
x_55 = lean_ctor_get(x_53, 0);
x_56 = lean_ctor_get(x_53, 1);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_array_set(x_31, x_9, x_57);
lean_dec(x_9);
lean_ctor_set(x_2, 0, x_58);
x_59 = 1;
x_60 = lean_box(x_59);
lean_ctor_set(x_53, 1, x_60);
lean_ctor_set(x_53, 0, x_2);
return x_53;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; 
x_61 = lean_ctor_get(x_53, 0);
x_62 = lean_ctor_get(x_53, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_53);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
x_64 = lean_array_set(x_31, x_9, x_63);
lean_dec(x_9);
lean_ctor_set(x_2, 0, x_64);
x_65 = 1;
x_66 = lean_box(x_65);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_2);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
else
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_33, 0);
lean_inc(x_68);
lean_dec(x_33);
x_69 = l_Std_PersistentHashMap_isUnaryNode___rarg(x_68);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; uint8_t x_71; lean_object* x_72; lean_object* x_73; 
lean_ctor_set(x_11, 0, x_68);
x_70 = lean_array_set(x_31, x_9, x_11);
lean_dec(x_9);
lean_ctor_set(x_2, 0, x_70);
x_71 = 1;
x_72 = lean_box(x_71);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_2);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_68);
lean_free_object(x_11);
x_74 = lean_ctor_get(x_69, 0);
lean_inc(x_74);
lean_dec(x_69);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_77 = x_74;
} else {
 lean_dec_ref(x_74);
 x_77 = lean_box(0);
}
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_76);
x_79 = lean_array_set(x_31, x_9, x_78);
lean_dec(x_9);
lean_ctor_set(x_2, 0, x_79);
x_80 = 1;
x_81 = lean_box(x_80);
if (lean_is_scalar(x_77)) {
 x_82 = lean_alloc_ctor(0, 2, 0);
} else {
 x_82 = x_77;
}
lean_ctor_set(x_82, 0, x_2);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_2);
x_83 = lean_ctor_get(x_33, 0);
lean_inc(x_83);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_84 = x_33;
} else {
 lean_dec_ref(x_33);
 x_84 = lean_box(0);
}
x_85 = l_Std_PersistentHashMap_isUnaryNode___rarg(x_83);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; lean_object* x_89; lean_object* x_90; 
lean_ctor_set(x_11, 0, x_83);
x_86 = lean_array_set(x_31, x_9, x_11);
lean_dec(x_9);
x_87 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_87, 0, x_86);
x_88 = 1;
x_89 = lean_box(x_88);
if (lean_is_scalar(x_84)) {
 x_90 = lean_alloc_ctor(0, 2, 0);
} else {
 x_90 = x_84;
}
lean_ctor_set(x_90, 0, x_87);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_84);
lean_dec(x_83);
lean_free_object(x_11);
x_91 = lean_ctor_get(x_85, 0);
lean_inc(x_91);
lean_dec(x_85);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_94 = x_91;
} else {
 lean_dec_ref(x_91);
 x_94 = lean_box(0);
}
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_92);
lean_ctor_set(x_95, 1, x_93);
x_96 = lean_array_set(x_31, x_9, x_95);
lean_dec(x_9);
x_97 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_97, 0, x_96);
x_98 = 1;
x_99 = lean_box(x_98);
if (lean_is_scalar(x_94)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_94;
}
lean_ctor_set(x_100, 0, x_97);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
}
else
{
lean_object* x_101; lean_object* x_102; size_t x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; 
x_101 = lean_ctor_get(x_11, 0);
lean_inc(x_101);
lean_dec(x_11);
x_102 = lean_array_set(x_5, x_9, x_10);
x_103 = x_3 >> x_6 % (sizeof(size_t) * 8);
x_104 = l_Std_PersistentHashMap_eraseAux___rarg(x_1, x_101, x_103, x_4);
x_105 = lean_ctor_get(x_104, 1);
lean_inc(x_105);
x_106 = lean_unbox(x_105);
lean_dec(x_105);
if (x_106 == 0)
{
lean_object* x_107; uint8_t x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_102);
lean_dec(x_9);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_107 = x_104;
} else {
 lean_dec_ref(x_104);
 x_107 = lean_box(0);
}
x_108 = 0;
x_109 = lean_box(x_108);
if (lean_is_scalar(x_107)) {
 x_110 = lean_alloc_ctor(0, 2, 0);
} else {
 x_110 = x_107;
}
lean_ctor_set(x_110, 0, x_2);
lean_ctor_set(x_110, 1, x_109);
return x_110;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 x_111 = x_2;
} else {
 lean_dec_ref(x_2);
 x_111 = lean_box(0);
}
x_112 = lean_ctor_get(x_104, 0);
lean_inc(x_112);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_113 = x_104;
} else {
 lean_dec_ref(x_104);
 x_113 = lean_box(0);
}
x_114 = l_Std_PersistentHashMap_isUnaryNode___rarg(x_112);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; lean_object* x_119; lean_object* x_120; 
x_115 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_115, 0, x_112);
x_116 = lean_array_set(x_102, x_9, x_115);
lean_dec(x_9);
if (lean_is_scalar(x_111)) {
 x_117 = lean_alloc_ctor(0, 1, 0);
} else {
 x_117 = x_111;
}
lean_ctor_set(x_117, 0, x_116);
x_118 = 1;
x_119 = lean_box(x_118);
if (lean_is_scalar(x_113)) {
 x_120 = lean_alloc_ctor(0, 2, 0);
} else {
 x_120 = x_113;
}
lean_ctor_set(x_120, 0, x_117);
lean_ctor_set(x_120, 1, x_119);
return x_120;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; lean_object* x_129; lean_object* x_130; 
lean_dec(x_113);
lean_dec(x_112);
x_121 = lean_ctor_get(x_114, 0);
lean_inc(x_121);
lean_dec(x_114);
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 lean_ctor_release(x_121, 1);
 x_124 = x_121;
} else {
 lean_dec_ref(x_121);
 x_124 = lean_box(0);
}
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_122);
lean_ctor_set(x_125, 1, x_123);
x_126 = lean_array_set(x_102, x_9, x_125);
lean_dec(x_9);
if (lean_is_scalar(x_111)) {
 x_127 = lean_alloc_ctor(0, 1, 0);
} else {
 x_127 = x_111;
}
lean_ctor_set(x_127, 0, x_126);
x_128 = 1;
x_129 = lean_box(x_128);
if (lean_is_scalar(x_124)) {
 x_130 = lean_alloc_ctor(0, 2, 0);
} else {
 x_130 = x_124;
}
lean_ctor_set(x_130, 0, x_127);
lean_ctor_set(x_130, 1, x_129);
return x_130;
}
}
}
}
default: 
{
uint8_t x_131; lean_object* x_132; lean_object* x_133; 
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_131 = 0;
x_132 = lean_box(x_131);
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_2);
lean_ctor_set(x_133, 1, x_132);
return x_133;
}
}
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_134 = lean_ctor_get(x_2, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_2, 1);
lean_inc(x_135);
x_136 = lean_unsigned_to_nat(0u);
x_137 = l_Array_indexOfAux___rarg(x_1, x_134, x_4, x_136);
if (lean_obj_tag(x_137) == 0)
{
uint8_t x_138; lean_object* x_139; lean_object* x_140; 
lean_dec(x_135);
lean_dec(x_134);
x_138 = 0;
x_139 = lean_box(x_138);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_2);
lean_ctor_set(x_140, 1, x_139);
return x_140;
}
else
{
uint8_t x_141; 
x_141 = !lean_is_exclusive(x_2);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; lean_object* x_148; lean_object* x_149; 
x_142 = lean_ctor_get(x_2, 1);
lean_dec(x_142);
x_143 = lean_ctor_get(x_2, 0);
lean_dec(x_143);
x_144 = lean_ctor_get(x_137, 0);
lean_inc(x_144);
lean_dec(x_137);
x_145 = l_Array_eraseIdx_x27___rarg(x_134, x_144);
x_146 = l_Array_eraseIdx_x27___rarg(x_135, x_144);
lean_dec(x_144);
lean_ctor_set(x_2, 1, x_146);
lean_ctor_set(x_2, 0, x_145);
x_147 = 1;
x_148 = lean_box(x_147);
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_2);
lean_ctor_set(x_149, 1, x_148);
return x_149;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_2);
x_150 = lean_ctor_get(x_137, 0);
lean_inc(x_150);
lean_dec(x_137);
x_151 = l_Array_eraseIdx_x27___rarg(x_134, x_150);
x_152 = l_Array_eraseIdx_x27___rarg(x_135, x_150);
lean_dec(x_150);
x_153 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set(x_153, 1, x_152);
x_154 = 1;
x_155 = lean_box(x_154);
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_153);
lean_ctor_set(x_156, 1, x_155);
return x_156;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_eraseAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_eraseAux___rarg___boxed), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_eraseAux___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Std_PersistentHashMap_eraseAux___rarg(x_1, x_2, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_erase___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_8 = lean_apply_1(x_2, x_4);
x_9 = lean_unbox_uint64(x_8);
lean_dec(x_8);
x_10 = (size_t)x_9;
x_11 = l_Std_PersistentHashMap_eraseAux___rarg(x_1, x_6, x_10, x_4);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
lean_dec(x_11);
lean_ctor_set(x_3, 0, x_14);
return x_3;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_11, 0);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_7, x_16);
lean_dec(x_7);
lean_ctor_set(x_3, 1, x_17);
lean_ctor_set(x_3, 0, x_15);
return x_3;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint64_t x_21; size_t x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_18 = lean_ctor_get(x_3, 0);
x_19 = lean_ctor_get(x_3, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_3);
lean_inc(x_4);
x_20 = lean_apply_1(x_2, x_4);
x_21 = lean_unbox_uint64(x_20);
lean_dec(x_20);
x_22 = (size_t)x_21;
x_23 = l_Std_PersistentHashMap_eraseAux___rarg(x_1, x_18, x_22, x_4);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
x_25 = lean_unbox(x_24);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_23, 0);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_19);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_23, 0);
lean_inc(x_28);
lean_dec(x_23);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_sub(x_19, x_29);
lean_dec(x_19);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_erase(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_erase___rarg), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlMAux_traverse___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_add(x_1, x_7);
lean_dec(x_1);
x_9 = l_Std_PersistentHashMap_foldlMAux_traverse___rarg(x_2, lean_box(0), lean_box(0), lean_box(0), x_3, x_4, x_5, lean_box(0), x_8, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlMAux_traverse___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_get_size(x_6);
x_12 = lean_nat_dec_lt(x_9, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_apply_2(x_14, lean_box(0), x_10);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_array_fget(x_6, x_9);
x_17 = lean_array_fget(x_7, x_9);
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
lean_inc(x_5);
x_19 = lean_apply_3(x_5, x_10, x_16, x_17);
x_20 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_foldlMAux_traverse___rarg___lambda__1), 6, 5);
lean_closure_set(x_20, 0, x_9);
lean_closure_set(x_20, 1, x_1);
lean_closure_set(x_20, 2, x_5);
lean_closure_set(x_20, 3, x_6);
lean_closure_set(x_20, 4, x_7);
x_21 = lean_apply_4(x_18, lean_box(0), lean_box(0), x_19, x_20);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlMAux_traverse(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_foldlMAux_traverse___rarg), 10, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlMAux___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_4)) {
case 0:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_apply_3(x_1, x_3, x_5, x_6);
return x_7;
}
case 1:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
lean_dec(x_4);
x_9 = l_Std_PersistentHashMap_foldlMAux___rarg(x_2, lean_box(0), lean_box(0), lean_box(0), x_1, x_8, x_3);
return x_9;
}
default: 
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_1);
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_apply_2(x_11, lean_box(0), x_3);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlMAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_foldlMAux___rarg___lambda__1), 4, 2);
lean_closure_set(x_9, 0, x_5);
lean_closure_set(x_9, 1, x_1);
x_10 = lean_array_get_size(x_8);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_lt(x_11, x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_apply_2(x_14, lean_box(0), x_7);
return x_15;
}
else
{
uint8_t x_16; 
x_16 = lean_nat_dec_le(x_10, x_10);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
lean_dec(x_1);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_apply_2(x_18, lean_box(0), x_7);
return x_19;
}
else
{
size_t x_20; size_t x_21; lean_object* x_22; 
x_20 = 0;
x_21 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_22 = l_Array_foldlMUnsafe_fold___rarg(x_1, x_9, x_8, x_20, x_21, x_7);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_6, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_6, 1);
lean_inc(x_24);
lean_dec(x_6);
x_25 = lean_unsigned_to_nat(0u);
x_26 = l_Std_PersistentHashMap_foldlMAux_traverse___rarg(x_1, lean_box(0), lean_box(0), lean_box(0), x_5, x_23, x_24, lean_box(0), x_25, x_7);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlMAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_foldlMAux___rarg), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
lean_dec(x_7);
x_11 = l_Std_PersistentHashMap_foldlMAux___rarg(x_1, lean_box(0), lean_box(0), lean_box(0), x_8, x_10, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_foldlM___rarg___boxed), 9, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlM___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Std_PersistentHashMap_foldlM___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_6);
lean_dec(x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_forM___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_2(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_forM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_forM___rarg___lambda__1___boxed), 4, 1);
lean_closure_set(x_8, 0, x_7);
x_9 = lean_box(0);
x_10 = l_Std_PersistentHashMap_foldlM___rarg(x_1, lean_box(0), lean_box(0), lean_box(0), x_4, x_5, x_6, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_forM(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_forM___rarg___boxed), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_forM___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_PersistentHashMap_forM___rarg___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_forM___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_PersistentHashMap_forM___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldl___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Id_instMonadId;
x_7 = l_Std_PersistentHashMap_foldlM___rarg(x_6, lean_box(0), lean_box(0), lean_box(0), x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_foldl___rarg___boxed), 5, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldl___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_PersistentHashMap_foldl___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Std_PersistentHashMap_toList___spec__3___rarg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_2 == x_3;
if (x_5 == 0)
{
lean_object* x_6; size_t x_7; size_t x_8; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = 1;
x_8 = x_2 + x_7;
switch (lean_obj_tag(x_6)) {
case 0:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_6, 1);
lean_inc(x_10);
lean_dec(x_6);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_4);
x_2 = x_8;
x_4 = x_12;
goto _start;
}
case 1:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_6, 0);
lean_inc(x_14);
lean_dec(x_6);
x_15 = l_Std_PersistentHashMap_foldlMAux___at_Std_PersistentHashMap_toList___spec__2___rarg(x_14, x_4);
x_2 = x_8;
x_4 = x_15;
goto _start;
}
default: 
{
x_2 = x_8;
goto _start;
}
}
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Std_PersistentHashMap_toList___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Std_PersistentHashMap_toList___spec__3___rarg___boxed), 4, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlMAux_traverse___at_Std_PersistentHashMap_toList___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_dec(x_5);
lean_dec(x_1);
return x_6;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_array_fget(x_2, x_5);
x_10 = lean_array_fget(x_3, x_5);
lean_inc(x_1);
x_11 = lean_apply_3(x_1, x_6, x_9, x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_5, x_12);
lean_dec(x_5);
x_4 = lean_box(0);
x_5 = x_13;
x_6 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlMAux_traverse___at_Std_PersistentHashMap_toList___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_foldlMAux_traverse___at_Std_PersistentHashMap_toList___spec__4___rarg___boxed), 6, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlMAux___at_Std_PersistentHashMap_toList___spec__2___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_1);
return x_5;
}
}
static lean_object* _init_l_Std_PersistentHashMap_foldlMAux___at_Std_PersistentHashMap_toList___spec__2___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_foldlMAux___at_Std_PersistentHashMap_toList___spec__2___rarg___lambda__1), 3, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlMAux___at_Std_PersistentHashMap_toList___spec__2___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_array_get_size(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
lean_dec(x_4);
lean_dec(x_3);
return x_2;
}
else
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_4, x_4);
if (x_7 == 0)
{
lean_dec(x_4);
lean_dec(x_3);
return x_2;
}
else
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = 0;
x_9 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_10 = l_Array_foldlMUnsafe_fold___at_Std_PersistentHashMap_toList___spec__3___rarg(x_3, x_8, x_9, x_2);
lean_dec(x_3);
return x_10;
}
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_dec(x_1);
x_13 = l_Std_PersistentHashMap_foldlMAux___at_Std_PersistentHashMap_toList___spec__2___rarg___closed__1;
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Std_PersistentHashMap_foldlMAux_traverse___at_Std_PersistentHashMap_toList___spec__4___rarg(x_13, x_11, x_12, lean_box(0), x_14, x_2);
lean_dec(x_12);
lean_dec(x_11);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlMAux___at_Std_PersistentHashMap_toList___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_foldlMAux___at_Std_PersistentHashMap_toList___spec__2___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlM___at_Std_PersistentHashMap_toList___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Std_PersistentHashMap_foldlMAux___at_Std_PersistentHashMap_toList___spec__2___rarg(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlM___at_Std_PersistentHashMap_toList___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_foldlM___at_Std_PersistentHashMap_toList___spec__1___rarg), 2, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_toList___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(0);
x_5 = l_Std_PersistentHashMap_foldlM___at_Std_PersistentHashMap_toList___spec__1___rarg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_toList(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_toList___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Std_PersistentHashMap_toList___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Std_PersistentHashMap_toList___spec__3___rarg(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlMAux_traverse___at_Std_PersistentHashMap_toList___spec__4___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_PersistentHashMap_foldlMAux_traverse___at_Std_PersistentHashMap_toList___spec__4___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_foldlM___at_Std_PersistentHashMap_toList___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_PersistentHashMap_foldlM___at_Std_PersistentHashMap_toList___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
static lean_object* _init_l_Std_PersistentHashMap_Stats_numNodes___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(0u);
return x_1;
}
}
static lean_object* _init_l_Std_PersistentHashMap_Stats_numNull___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(0u);
return x_1;
}
}
static lean_object* _init_l_Std_PersistentHashMap_Stats_numCollisions___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(0u);
return x_1;
}
}
static lean_object* _init_l_Std_PersistentHashMap_Stats_maxDepth___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(0u);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Std_PersistentHashMap_collectStats___spec__1___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = x_3 == x_4;
if (x_6 == 0)
{
lean_object* x_7; size_t x_8; size_t x_9; 
x_7 = lean_array_uget(x_2, x_3);
x_8 = 1;
x_9 = x_3 + x_8;
switch (lean_obj_tag(x_7)) {
case 0:
{
lean_dec(x_7);
x_3 = x_9;
goto _start;
}
case 1:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_1, x_12);
x_14 = l_Std_PersistentHashMap_collectStats___rarg(x_11, x_5, x_13);
x_3 = x_9;
x_5 = x_14;
goto _start;
}
default: 
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_5);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_5, 1);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_17, x_18);
lean_dec(x_17);
lean_ctor_set(x_5, 1, x_19);
x_3 = x_9;
goto _start;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_21 = lean_ctor_get(x_5, 0);
x_22 = lean_ctor_get(x_5, 1);
x_23 = lean_ctor_get(x_5, 2);
x_24 = lean_ctor_get(x_5, 3);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_5);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_add(x_22, x_25);
lean_dec(x_22);
x_27 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_27, 0, x_21);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set(x_27, 2, x_23);
lean_ctor_set(x_27, 3, x_24);
x_3 = x_9;
x_5 = x_27;
goto _start;
}
}
}
}
else
{
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Std_PersistentHashMap_collectStats___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Std_PersistentHashMap_collectStats___spec__1___rarg___boxed), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_collectStats___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 3);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_6, x_8);
lean_dec(x_6);
x_10 = l_Nat_max(x_7, x_3);
lean_dec(x_7);
lean_ctor_set(x_2, 3, x_10);
lean_ctor_set(x_2, 0, x_9);
x_11 = lean_array_get_size(x_4);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_lt(x_12, x_11);
if (x_13 == 0)
{
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_3);
return x_2;
}
else
{
uint8_t x_14; 
x_14 = lean_nat_dec_le(x_11, x_11);
if (x_14 == 0)
{
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_3);
return x_2;
}
else
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = 0;
x_16 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_17 = l_Array_foldlMUnsafe_fold___at_Std_PersistentHashMap_collectStats___spec__1___rarg(x_3, x_4, x_15, x_16, x_2);
lean_dec(x_4);
lean_dec(x_3);
return x_17;
}
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_18 = lean_ctor_get(x_2, 0);
x_19 = lean_ctor_get(x_2, 1);
x_20 = lean_ctor_get(x_2, 2);
x_21 = lean_ctor_get(x_2, 3);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_2);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_18, x_22);
lean_dec(x_18);
x_24 = l_Nat_max(x_21, x_3);
lean_dec(x_21);
x_25 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_19);
lean_ctor_set(x_25, 2, x_20);
lean_ctor_set(x_25, 3, x_24);
x_26 = lean_array_get_size(x_4);
x_27 = lean_unsigned_to_nat(0u);
x_28 = lean_nat_dec_lt(x_27, x_26);
if (x_28 == 0)
{
lean_dec(x_26);
lean_dec(x_4);
lean_dec(x_3);
return x_25;
}
else
{
uint8_t x_29; 
x_29 = lean_nat_dec_le(x_26, x_26);
if (x_29 == 0)
{
lean_dec(x_26);
lean_dec(x_4);
lean_dec(x_3);
return x_25;
}
else
{
size_t x_30; size_t x_31; lean_object* x_32; 
x_30 = 0;
x_31 = lean_usize_of_nat(x_26);
lean_dec(x_26);
x_32 = l_Array_foldlMUnsafe_fold___at_Std_PersistentHashMap_collectStats___spec__1___rarg(x_3, x_4, x_30, x_31, x_25);
lean_dec(x_4);
lean_dec(x_3);
return x_32;
}
}
}
}
else
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_1, 0);
lean_inc(x_33);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_2);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_35 = lean_ctor_get(x_2, 0);
x_36 = lean_ctor_get(x_2, 2);
x_37 = lean_ctor_get(x_2, 3);
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_nat_add(x_35, x_38);
lean_dec(x_35);
x_40 = lean_array_get_size(x_33);
lean_dec(x_33);
x_41 = lean_nat_add(x_36, x_40);
lean_dec(x_40);
lean_dec(x_36);
x_42 = lean_nat_sub(x_41, x_38);
lean_dec(x_41);
x_43 = l_Nat_max(x_37, x_3);
lean_dec(x_3);
lean_dec(x_37);
lean_ctor_set(x_2, 3, x_43);
lean_ctor_set(x_2, 2, x_42);
lean_ctor_set(x_2, 0, x_39);
return x_2;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_44 = lean_ctor_get(x_2, 0);
x_45 = lean_ctor_get(x_2, 1);
x_46 = lean_ctor_get(x_2, 2);
x_47 = lean_ctor_get(x_2, 3);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_2);
x_48 = lean_unsigned_to_nat(1u);
x_49 = lean_nat_add(x_44, x_48);
lean_dec(x_44);
x_50 = lean_array_get_size(x_33);
lean_dec(x_33);
x_51 = lean_nat_add(x_46, x_50);
lean_dec(x_50);
lean_dec(x_46);
x_52 = lean_nat_sub(x_51, x_48);
lean_dec(x_51);
x_53 = l_Nat_max(x_47, x_3);
lean_dec(x_3);
lean_dec(x_47);
x_54 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_54, 0, x_49);
lean_ctor_set(x_54, 1, x_45);
lean_ctor_set(x_54, 2, x_52);
lean_ctor_set(x_54, 3, x_53);
return x_54;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_collectStats(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_collectStats___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Std_PersistentHashMap_collectStats___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Std_PersistentHashMap_collectStats___spec__1___rarg(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
static lean_object* _init_l_Std_PersistentHashMap_stats___rarg___closed__1() {
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
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_stats___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
x_3 = l_Std_PersistentHashMap_stats___rarg___closed__1;
x_4 = lean_unsigned_to_nat(1u);
x_5 = l_Std_PersistentHashMap_collectStats___rarg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_stats(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_stats___rarg), 1, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_stats___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_PersistentHashMap_stats(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
static lean_object* _init_l_Std_PersistentHashMap_Stats_toString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("{ nodes := ");
return x_1;
}
}
static lean_object* _init_l_Std_PersistentHashMap_Stats_toString___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(", null := ");
return x_1;
}
}
static lean_object* _init_l_Std_PersistentHashMap_Stats_toString___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(", collisions := ");
return x_1;
}
}
static lean_object* _init_l_Std_PersistentHashMap_Stats_toString___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(", depth := ");
return x_1;
}
}
static lean_object* _init_l_Std_PersistentHashMap_Stats_toString___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("}");
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_PersistentHashMap_Stats_toString(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = l_Nat_repr(x_2);
x_4 = l_Std_PersistentHashMap_Stats_toString___closed__1;
x_5 = lean_string_append(x_4, x_3);
lean_dec(x_3);
x_6 = l_Std_PersistentHashMap_Stats_toString___closed__2;
x_7 = lean_string_append(x_5, x_6);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = l_Nat_repr(x_8);
x_10 = lean_string_append(x_7, x_9);
lean_dec(x_9);
x_11 = l_Std_PersistentHashMap_Stats_toString___closed__3;
x_12 = lean_string_append(x_10, x_11);
x_13 = lean_ctor_get(x_1, 2);
lean_inc(x_13);
x_14 = l_Nat_repr(x_13);
x_15 = lean_string_append(x_12, x_14);
lean_dec(x_14);
x_16 = l_Std_PersistentHashMap_Stats_toString___closed__4;
x_17 = lean_string_append(x_15, x_16);
x_18 = lean_ctor_get(x_1, 3);
lean_inc(x_18);
lean_dec(x_1);
x_19 = l_Nat_repr(x_18);
x_20 = lean_string_append(x_17, x_19);
lean_dec(x_19);
x_21 = l_Std_PersistentHashMap_Stats_toString___closed__5;
x_22 = lean_string_append(x_20, x_21);
return x_22;
}
}
static lean_object* _init_l_Std_PersistentHashMap_instToStringStats___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_Stats_toString), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Std_PersistentHashMap_instToStringStats() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_PersistentHashMap_instToStringStats___closed__1;
return x_1;
}
}
lean_object* initialize_Init(lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_PersistentHashMap(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_PersistentHashMap_instInhabitedNode___closed__1 = _init_l_Std_PersistentHashMap_instInhabitedNode___closed__1();
lean_mark_persistent(l_Std_PersistentHashMap_instInhabitedNode___closed__1);
l_Std_PersistentHashMap_instInhabitedNode___closed__2 = _init_l_Std_PersistentHashMap_instInhabitedNode___closed__2();
lean_mark_persistent(l_Std_PersistentHashMap_instInhabitedNode___closed__2);
l_Std_PersistentHashMap_shift = _init_l_Std_PersistentHashMap_shift();
l_Std_PersistentHashMap_branching = _init_l_Std_PersistentHashMap_branching();
l_Std_PersistentHashMap_maxDepth = _init_l_Std_PersistentHashMap_maxDepth();
l_Std_PersistentHashMap_maxCollisions = _init_l_Std_PersistentHashMap_maxCollisions();
lean_mark_persistent(l_Std_PersistentHashMap_maxCollisions);
l_Std_PersistentHashMap_mkEmptyEntriesArray___closed__1 = _init_l_Std_PersistentHashMap_mkEmptyEntriesArray___closed__1();
lean_mark_persistent(l_Std_PersistentHashMap_mkEmptyEntriesArray___closed__1);
l_Std_PersistentHashMap_root___default___closed__1 = _init_l_Std_PersistentHashMap_root___default___closed__1();
lean_mark_persistent(l_Std_PersistentHashMap_root___default___closed__1);
l_Std_PersistentHashMap_root___default___closed__2 = _init_l_Std_PersistentHashMap_root___default___closed__2();
lean_mark_persistent(l_Std_PersistentHashMap_root___default___closed__2);
l_Std_PersistentHashMap_size___default = _init_l_Std_PersistentHashMap_size___default();
lean_mark_persistent(l_Std_PersistentHashMap_size___default);
l_Std_PersistentHashMap_mkCollisionNode___rarg___closed__1 = _init_l_Std_PersistentHashMap_mkCollisionNode___rarg___closed__1();
lean_mark_persistent(l_Std_PersistentHashMap_mkCollisionNode___rarg___closed__1);
l_Std_PersistentHashMap_insertAux___rarg___closed__1 = _init_l_Std_PersistentHashMap_insertAux___rarg___closed__1();
l_Std_PersistentHashMap_insertAux___rarg___closed__2 = _init_l_Std_PersistentHashMap_insertAux___rarg___closed__2();
l_Std_PersistentHashMap_insertAux___rarg___closed__3 = _init_l_Std_PersistentHashMap_insertAux___rarg___closed__3();
lean_mark_persistent(l_Std_PersistentHashMap_insertAux___rarg___closed__3);
l_Std_PersistentHashMap_find_x21___rarg___closed__1 = _init_l_Std_PersistentHashMap_find_x21___rarg___closed__1();
lean_mark_persistent(l_Std_PersistentHashMap_find_x21___rarg___closed__1);
l_Std_PersistentHashMap_find_x21___rarg___closed__2 = _init_l_Std_PersistentHashMap_find_x21___rarg___closed__2();
lean_mark_persistent(l_Std_PersistentHashMap_find_x21___rarg___closed__2);
l_Std_PersistentHashMap_find_x21___rarg___closed__3 = _init_l_Std_PersistentHashMap_find_x21___rarg___closed__3();
lean_mark_persistent(l_Std_PersistentHashMap_find_x21___rarg___closed__3);
l_Std_PersistentHashMap_find_x21___rarg___closed__4 = _init_l_Std_PersistentHashMap_find_x21___rarg___closed__4();
lean_mark_persistent(l_Std_PersistentHashMap_find_x21___rarg___closed__4);
l_Std_PersistentHashMap_foldlMAux___at_Std_PersistentHashMap_toList___spec__2___rarg___closed__1 = _init_l_Std_PersistentHashMap_foldlMAux___at_Std_PersistentHashMap_toList___spec__2___rarg___closed__1();
lean_mark_persistent(l_Std_PersistentHashMap_foldlMAux___at_Std_PersistentHashMap_toList___spec__2___rarg___closed__1);
l_Std_PersistentHashMap_Stats_numNodes___default = _init_l_Std_PersistentHashMap_Stats_numNodes___default();
lean_mark_persistent(l_Std_PersistentHashMap_Stats_numNodes___default);
l_Std_PersistentHashMap_Stats_numNull___default = _init_l_Std_PersistentHashMap_Stats_numNull___default();
lean_mark_persistent(l_Std_PersistentHashMap_Stats_numNull___default);
l_Std_PersistentHashMap_Stats_numCollisions___default = _init_l_Std_PersistentHashMap_Stats_numCollisions___default();
lean_mark_persistent(l_Std_PersistentHashMap_Stats_numCollisions___default);
l_Std_PersistentHashMap_Stats_maxDepth___default = _init_l_Std_PersistentHashMap_Stats_maxDepth___default();
lean_mark_persistent(l_Std_PersistentHashMap_Stats_maxDepth___default);
l_Std_PersistentHashMap_stats___rarg___closed__1 = _init_l_Std_PersistentHashMap_stats___rarg___closed__1();
lean_mark_persistent(l_Std_PersistentHashMap_stats___rarg___closed__1);
l_Std_PersistentHashMap_Stats_toString___closed__1 = _init_l_Std_PersistentHashMap_Stats_toString___closed__1();
lean_mark_persistent(l_Std_PersistentHashMap_Stats_toString___closed__1);
l_Std_PersistentHashMap_Stats_toString___closed__2 = _init_l_Std_PersistentHashMap_Stats_toString___closed__2();
lean_mark_persistent(l_Std_PersistentHashMap_Stats_toString___closed__2);
l_Std_PersistentHashMap_Stats_toString___closed__3 = _init_l_Std_PersistentHashMap_Stats_toString___closed__3();
lean_mark_persistent(l_Std_PersistentHashMap_Stats_toString___closed__3);
l_Std_PersistentHashMap_Stats_toString___closed__4 = _init_l_Std_PersistentHashMap_Stats_toString___closed__4();
lean_mark_persistent(l_Std_PersistentHashMap_Stats_toString___closed__4);
l_Std_PersistentHashMap_Stats_toString___closed__5 = _init_l_Std_PersistentHashMap_Stats_toString___closed__5();
lean_mark_persistent(l_Std_PersistentHashMap_Stats_toString___closed__5);
l_Std_PersistentHashMap_instToStringStats___closed__1 = _init_l_Std_PersistentHashMap_instToStringStats___closed__1();
lean_mark_persistent(l_Std_PersistentHashMap_instToStringStats___closed__1);
l_Std_PersistentHashMap_instToStringStats = _init_l_Std_PersistentHashMap_instToStringStats();
lean_mark_persistent(l_Std_PersistentHashMap_instToStringStats);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
