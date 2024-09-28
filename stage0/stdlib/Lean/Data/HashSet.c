// Lean compiler output
// Module: Lean.Data.HashSet
// Imports: Init.Data.Nat.Power2 Std.Data.HashSet.Basic Std.Data.HashSet.Raw
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
LEAN_EXPORT lean_object* l_Lean_HashSet_fold(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_HashSet_fold___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSet_merge___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_HashSetImp_foldBuckets___spec__1___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSet_insert(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSet_foldM___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSetImp_moveEntries___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSet_foldM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSetImp_insert___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSet_fold___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSet_merge___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSet_instForIn___rarg___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_bindCont___at_Lean_HashSet_instForIn___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkHashSetImp___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSet_toArray___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSet_instInhabited(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkHashSetImp(lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSetImp_forBucketsM___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSetImp_find_x3f___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSet_instForIn___spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSet_toArray___spec__2(lean_object*);
size_t lean_hashset_mk_idx(lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Lean_HashSetImp_insert(lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSet_instForM(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSet_size___rarg(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_HashSetImp_contains___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkHashSetImp___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSet_instForM___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSet_numBuckets(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
static lean_object* l_Lean_HashSetImp_insert___rarg___closed__1;
lean_object* l_List_foldlM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSet_forM___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSetImp_contains(lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSet_instForIn___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_replaceTR_go___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSet_toList(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSetBucket_update(lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSet_fold___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_find_x3f___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSet_erase(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkHashSet(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSetImp_forM(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSet_foldM___spec__1___rarg___lambda__1(size_t, lean_object*, lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSetImp_expand(lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSetImp_fold(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSetImp_foldBucketsM(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSet_instEmptyCollection(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSet_size___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSet_fold___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSetImp_forBucketsM___spec__1___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSetImp_reinsertAux___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_HashSetImp_moveEntries___spec__1___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSet_foldM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSet_instForIn___spec__3___rarg___lambda__1(size_t, lean_object*, lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSetImp_foldM___spec__1___rarg___lambda__1(size_t, lean_object*, lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSet_find_x3f___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSetImp_foldBucketsM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSet_toList___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSetBucket_update___rarg(lean_object*, size_t, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSetImp_fold___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSet_toList___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSetImp_foldBuckets___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSetImp_foldBuckets(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkHashSet___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSet_toArray___spec__2___rarg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSet_fold___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSet_isEmpty(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSetImp_forBucketsM___spec__1___rarg___lambda__1(size_t, lean_object*, lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSet_instForIn___spec__3___rarg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSetImp_fold___spec__2___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSetImp_forM___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSetImp_moveEntries(lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_HashSetImp_fold___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSet_insertMany(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSet_toArray___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSet_find_x3f(lean_object*);
static lean_object* l_Lean_HashSet_instForM___closed__1;
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_HashSet_toArray___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_HashSetImp_fold___spec__1___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSetImp_fold___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSetImp_forM___spec__1___rarg___lambda__1(size_t, lean_object*, lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSet_contains___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_HashSetImp_moveEntries___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_HashSet_toList___spec__1(lean_object*);
lean_object* l_List_forM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSet_toList___spec__2___rarg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_HashSet_merge___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSet_fold___spec__2___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSet_numBuckets___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSetImp_erase(lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSet_foldM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_HashSet_contains___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSet_isEmpty___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSetBucket_update___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSetImp_forBucketsM___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSet_size___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_HashSet_isEmpty___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSetImp_forM___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSetImp_find_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSet_foldM___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSetImp_foldBucketsM___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSetImp_expand___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSet_merge___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_elem___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSet_toArray(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSet_numBuckets___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSet_empty(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_bindCont___at_Lean_HashSet_instForIn___spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSet_insertMany___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_HashSet_toList___spec__1___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSet_empty___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSetImp_reinsertAux(lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSet_insert___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_HashSet_empty___closed__1;
LEAN_EXPORT lean_object* l_Lean_HashSet_instForIn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ExceptT_bindCont___at_Lean_HashSet_instForIn___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_HashSet_0__Lean_HashSetImp_mkIdx___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSet_forM___spec__1___rarg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSet_merge___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at_Lean_HashSet_instForIn___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSetImp_foldM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSetImp_forBucketsM___spec__1___rarg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSetImp_forBucketsM___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_HashSet_merge___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSet_numBuckets___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSet_find_x3f___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSet_erase___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSetImp_foldBucketsM___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at_Lean_HashSet_instForIn___spec__1___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSet_forM___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSetImp_foldBuckets___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSetImp_foldBucketsM___spec__1___rarg___lambda__1(size_t, lean_object*, lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSet_merge___spec__2___rarg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSetImp_foldM(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSet_fold___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSetImp_foldM___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSetImp_fold___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSet_forM___spec__1___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkHashSet___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSetImp_forM___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSet_forM___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Id_instMonad;
LEAN_EXPORT lean_object* l_Lean_HashSetImp_foldBuckets___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSet_toList___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSetImp_fold___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSet_contains(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSetImp_forM___spec__1___rarg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_HashSetImp_foldBuckets___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSetImp_foldBucketsM___spec__1___rarg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSet_forM(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSet_instInhabited___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSetImp_erase___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSet_isEmpty___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSetImp_foldM___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSet_toArray___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_HashSet_size(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSetImp_find_x3f___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_ExceptT_bindCont___at_Lean_HashSet_instForIn___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSet_foldM___spec__1___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSet_merge(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSet_instForIn___spec__3___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSet_forM___spec__1___rarg___lambda__1(size_t, lean_object*, lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkHashSet___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSetImp_foldBuckets___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_HashSet_fold___spec__1___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSet_insertMany___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSet_toList___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSetImp_forM___spec__1___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSet_instForIn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSetImp_foldM___spec__1___rarg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_HashSet_toArray___spec__1___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSet_foldM___spec__1___rarg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at_Lean_HashSet_instForIn___spec__1___rarg___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSet_instForIn___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSetImp_foldBuckets___spec__2___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSetImp_foldBucketsM___spec__1___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_eraseTR_go___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSetImp_forBucketsM(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSet_toList___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at_Lean_HashSet_instForIn___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSet_toArray___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSetImp_foldM___spec__1___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSet_forM___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSet_instEmptyCollection___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSetImp_contains___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashSetBucket_update___rarg(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_array_uset(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_HashSetBucket_update(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_HashSetBucket_update___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_HashSetBucket_update___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Lean_HashSetBucket_update___rarg(x_1, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_mkHashSetImp___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = lean_unsigned_to_nat(4u);
x_3 = lean_nat_mul(x_1, x_2);
x_4 = lean_unsigned_to_nat(3u);
x_5 = lean_nat_div(x_3, x_4);
lean_dec(x_3);
x_6 = lean_unsigned_to_nat(1u);
x_7 = l_Nat_nextPowerOfTwo_go(x_5, x_6, lean_box(0));
lean_dec(x_5);
x_8 = lean_box(0);
x_9 = lean_mk_array(x_7, x_8);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_mkHashSetImp(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_mkHashSetImp___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_mkHashSetImp___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkHashSetImp___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_HashSet_0__Lean_HashSetImp_mkIdx___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = lean_hashset_mk_idx(x_1, x_4);
x_6 = lean_box_usize(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_HashSetImp_reinsertAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint64_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_array_get_size(x_2);
lean_inc(x_3);
x_5 = lean_apply_1(x_1, x_3);
x_6 = lean_unbox_uint64(x_5);
lean_dec(x_5);
x_7 = lean_hashset_mk_idx(x_4, x_6);
x_8 = lean_array_uget(x_2, x_7);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_array_uset(x_2, x_7, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_HashSetImp_reinsertAux(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_HashSetImp_reinsertAux___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSetImp_foldBucketsM___spec__1___rarg___lambda__1(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = 1;
x_8 = lean_usize_add(x_1, x_7);
x_9 = l_Array_foldlMUnsafe_fold___at_Lean_HashSetImp_foldBucketsM___spec__1___rarg(x_2, x_3, x_4, x_8, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSetImp_foldBucketsM___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_4, x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_array_uget(x_3, x_4);
lean_inc(x_2);
lean_inc(x_1);
x_10 = l_List_foldlM___rarg(x_1, lean_box(0), lean_box(0), x_2, x_6, x_9);
x_11 = lean_box_usize(x_4);
x_12 = lean_box_usize(x_5);
x_13 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_HashSetImp_foldBucketsM___spec__1___rarg___lambda__1___boxed), 6, 5);
lean_closure_set(x_13, 0, x_11);
lean_closure_set(x_13, 1, x_1);
lean_closure_set(x_13, 2, x_2);
lean_closure_set(x_13, 3, x_3);
lean_closure_set(x_13, 4, x_12);
x_14 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_10, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_3);
lean_dec(x_2);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_apply_2(x_16, lean_box(0), x_6);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSetImp_foldBucketsM___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_HashSetImp_foldBucketsM___spec__1___rarg___boxed), 6, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_HashSetImp_foldBucketsM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_apply_2(x_9, lean_box(0), x_3);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = lean_nat_dec_le(x_5, x_5);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_apply_2(x_13, lean_box(0), x_3);
return x_14;
}
else
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = 0;
x_16 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_17 = l_Array_foldlMUnsafe_fold___at_Lean_HashSetImp_foldBucketsM___spec__1___rarg(x_1, x_4, x_2, x_15, x_16, x_3);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HashSetImp_foldBucketsM(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_HashSetImp_foldBucketsM___rarg), 4, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSetImp_foldBucketsM___spec__1___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_foldlMUnsafe_fold___at_Lean_HashSetImp_foldBucketsM___spec__1___rarg___lambda__1(x_7, x_2, x_3, x_4, x_8, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSetImp_foldBucketsM___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_foldlMUnsafe_fold___at_Lean_HashSetImp_foldBucketsM___spec__1___rarg(x_1, x_2, x_3, x_7, x_8, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_HashSetImp_foldBuckets___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
lean_inc(x_1);
x_6 = lean_apply_2(x_1, x_2, x_4);
x_2 = x_6;
x_3 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_HashSetImp_foldBuckets___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_List_foldlM___at_Lean_HashSetImp_foldBuckets___spec__1___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSetImp_foldBuckets___spec__2___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_7 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_8 = l_List_foldlM___at_Lean_HashSetImp_foldBuckets___spec__1___rarg(x_1, x_5, x_7);
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
x_3 = x_10;
x_5 = x_8;
goto _start;
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSetImp_foldBuckets___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_HashSetImp_foldBuckets___spec__2___rarg___boxed), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_HashSetImp_foldBuckets___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_array_get_size(x_1);
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
x_10 = l_Array_foldlMUnsafe_fold___at_Lean_HashSetImp_foldBuckets___spec__2___rarg(x_3, x_1, x_8, x_9, x_2);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HashSetImp_foldBuckets(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_HashSetImp_foldBuckets___rarg___boxed), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSetImp_foldBuckets___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lean_HashSetImp_foldBuckets___spec__2___rarg(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_HashSetImp_foldBuckets___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_HashSetImp_foldBuckets___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSetImp_foldM___spec__1___rarg___lambda__1(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = 1;
x_8 = lean_usize_add(x_1, x_7);
x_9 = l_Array_foldlMUnsafe_fold___at_Lean_HashSetImp_foldM___spec__1___rarg(x_2, x_3, x_4, x_8, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSetImp_foldM___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_4, x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_array_uget(x_3, x_4);
lean_inc(x_2);
lean_inc(x_1);
x_10 = l_List_foldlM___rarg(x_1, lean_box(0), lean_box(0), x_2, x_6, x_9);
x_11 = lean_box_usize(x_4);
x_12 = lean_box_usize(x_5);
x_13 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_HashSetImp_foldM___spec__1___rarg___lambda__1___boxed), 6, 5);
lean_closure_set(x_13, 0, x_11);
lean_closure_set(x_13, 1, x_1);
lean_closure_set(x_13, 2, x_2);
lean_closure_set(x_13, 3, x_3);
lean_closure_set(x_13, 4, x_12);
x_14 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_10, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_3);
lean_dec(x_2);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_apply_2(x_16, lean_box(0), x_6);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSetImp_foldM___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_HashSetImp_foldM___spec__1___rarg___boxed), 6, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_HashSetImp_foldM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_array_get_size(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_lt(x_7, x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_apply_2(x_10, lean_box(0), x_3);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = lean_nat_dec_le(x_6, x_6);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_apply_2(x_14, lean_box(0), x_3);
return x_15;
}
else
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_18 = l_Array_foldlMUnsafe_fold___at_Lean_HashSetImp_foldM___spec__1___rarg(x_1, x_2, x_5, x_16, x_17, x_3);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HashSetImp_foldM(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_HashSetImp_foldM___rarg), 4, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSetImp_foldM___spec__1___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_foldlMUnsafe_fold___at_Lean_HashSetImp_foldM___spec__1___rarg___lambda__1(x_7, x_2, x_3, x_4, x_8, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSetImp_foldM___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_foldlMUnsafe_fold___at_Lean_HashSetImp_foldM___spec__1___rarg(x_1, x_2, x_3, x_7, x_8, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_HashSetImp_fold___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
lean_inc(x_1);
x_6 = lean_apply_2(x_1, x_2, x_4);
x_2 = x_6;
x_3 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_HashSetImp_fold___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_List_foldlM___at_Lean_HashSetImp_fold___spec__1___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSetImp_fold___spec__2___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_7 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_8 = l_List_foldlM___at_Lean_HashSetImp_fold___spec__1___rarg(x_1, x_5, x_7);
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
x_3 = x_10;
x_5 = x_8;
goto _start;
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSetImp_fold___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_HashSetImp_fold___spec__2___rarg___boxed), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_HashSetImp_fold___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_3, 1);
x_5 = lean_array_get_size(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_5);
if (x_7 == 0)
{
lean_dec(x_5);
lean_dec(x_1);
return x_2;
}
else
{
uint8_t x_8; 
x_8 = lean_nat_dec_le(x_5, x_5);
if (x_8 == 0)
{
lean_dec(x_5);
lean_dec(x_1);
return x_2;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = 0;
x_10 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_11 = l_Array_foldlMUnsafe_fold___at_Lean_HashSetImp_fold___spec__2___rarg(x_1, x_4, x_9, x_10, x_2);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HashSetImp_fold(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_HashSetImp_fold___rarg___boxed), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSetImp_fold___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lean_HashSetImp_fold___spec__2___rarg(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_HashSetImp_fold___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_HashSetImp_fold___rarg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSetImp_forBucketsM___spec__1___rarg___lambda__1(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = 1;
x_8 = lean_usize_add(x_1, x_7);
x_9 = l_Array_foldlMUnsafe_fold___at_Lean_HashSetImp_forBucketsM___spec__1___rarg(x_2, x_3, x_4, x_8, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSetImp_forBucketsM___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_4, x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_6);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_array_uget(x_3, x_4);
lean_inc(x_2);
lean_inc(x_1);
x_10 = l_List_forM___rarg(x_1, lean_box(0), x_9, x_2);
x_11 = lean_box_usize(x_4);
x_12 = lean_box_usize(x_5);
x_13 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_HashSetImp_forBucketsM___spec__1___rarg___lambda__1___boxed), 6, 5);
lean_closure_set(x_13, 0, x_11);
lean_closure_set(x_13, 1, x_1);
lean_closure_set(x_13, 2, x_2);
lean_closure_set(x_13, 3, x_3);
lean_closure_set(x_13, 4, x_12);
x_14 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_10, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_3);
lean_dec(x_2);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_apply_2(x_16, lean_box(0), x_6);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSetImp_forBucketsM___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_HashSetImp_forBucketsM___spec__1___rarg___boxed), 6, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_HashSetImp_forBucketsM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_box(0);
x_10 = lean_apply_2(x_8, lean_box(0), x_9);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = lean_nat_dec_le(x_4, x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_box(0);
x_15 = lean_apply_2(x_13, lean_box(0), x_14);
return x_15;
}
else
{
size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_18 = lean_box(0);
x_19 = l_Array_foldlMUnsafe_fold___at_Lean_HashSetImp_forBucketsM___spec__1___rarg(x_1, x_3, x_2, x_16, x_17, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HashSetImp_forBucketsM(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_HashSetImp_forBucketsM___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSetImp_forBucketsM___spec__1___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_foldlMUnsafe_fold___at_Lean_HashSetImp_forBucketsM___spec__1___rarg___lambda__1(x_7, x_2, x_3, x_4, x_8, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSetImp_forBucketsM___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_foldlMUnsafe_fold___at_Lean_HashSetImp_forBucketsM___spec__1___rarg(x_1, x_2, x_3, x_7, x_8, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSetImp_forM___spec__1___rarg___lambda__1(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = 1;
x_8 = lean_usize_add(x_1, x_7);
x_9 = l_Array_foldlMUnsafe_fold___at_Lean_HashSetImp_forM___spec__1___rarg(x_2, x_3, x_4, x_8, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSetImp_forM___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_4, x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_6);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_array_uget(x_3, x_4);
lean_inc(x_2);
lean_inc(x_1);
x_10 = l_List_forM___rarg(x_1, lean_box(0), x_9, x_2);
x_11 = lean_box_usize(x_4);
x_12 = lean_box_usize(x_5);
x_13 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_HashSetImp_forM___spec__1___rarg___lambda__1___boxed), 6, 5);
lean_closure_set(x_13, 0, x_11);
lean_closure_set(x_13, 1, x_1);
lean_closure_set(x_13, 2, x_2);
lean_closure_set(x_13, 3, x_3);
lean_closure_set(x_13, 4, x_12);
x_14 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_10, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_3);
lean_dec(x_2);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_apply_2(x_16, lean_box(0), x_6);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSetImp_forM___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_HashSetImp_forM___spec__1___rarg___boxed), 6, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_HashSetImp_forM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_array_get_size(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = lean_apply_2(x_9, lean_box(0), x_10);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = lean_nat_dec_le(x_5, x_5);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = lean_apply_2(x_14, lean_box(0), x_15);
return x_16;
}
else
{
size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; 
x_17 = 0;
x_18 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_19 = lean_box(0);
x_20 = l_Array_foldlMUnsafe_fold___at_Lean_HashSetImp_forM___spec__1___rarg(x_1, x_2, x_4, x_17, x_18, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HashSetImp_forM(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_HashSetImp_forM___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSetImp_forM___spec__1___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_foldlMUnsafe_fold___at_Lean_HashSetImp_forM___spec__1___rarg___lambda__1(x_7, x_2, x_3, x_4, x_8, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSetImp_forM___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_foldlMUnsafe_fold___at_Lean_HashSetImp_forM___spec__1___rarg(x_1, x_2, x_3, x_7, x_8, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_HashSetImp_find_x3f___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_array_get_size(x_5);
lean_inc(x_4);
x_7 = lean_apply_1(x_2, x_4);
x_8 = lean_unbox_uint64(x_7);
lean_dec(x_7);
x_9 = lean_hashset_mk_idx(x_6, x_8);
x_10 = lean_apply_1(x_1, x_4);
x_11 = lean_array_uget(x_5, x_9);
x_12 = l_List_find_x3f___rarg(x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_HashSetImp_find_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_HashSetImp_find_x3f___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_HashSetImp_find_x3f___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_HashSetImp_find_x3f___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_HashSetImp_contains___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; size_t x_9; lean_object* x_10; uint8_t x_11; 
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_array_get_size(x_5);
lean_inc(x_4);
x_7 = lean_apply_1(x_2, x_4);
x_8 = lean_unbox_uint64(x_7);
lean_dec(x_7);
x_9 = lean_hashset_mk_idx(x_6, x_8);
x_10 = lean_array_uget(x_5, x_9);
x_11 = l_List_elem___rarg(x_1, x_4, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_HashSetImp_contains(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_HashSetImp_contains___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_HashSetImp_contains___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Lean_HashSetImp_contains___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_HashSetImp_moveEntries___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_array_get_size(x_2);
lean_inc(x_1);
lean_inc(x_5);
x_8 = lean_apply_1(x_1, x_5);
x_9 = lean_unbox_uint64(x_8);
lean_dec(x_8);
x_10 = lean_hashset_mk_idx(x_7, x_9);
x_11 = lean_array_uget(x_2, x_10);
lean_ctor_set(x_3, 1, x_11);
x_12 = lean_array_uset(x_2, x_10, x_3);
x_2 = x_12;
x_3 = x_6;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint64_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_14 = lean_ctor_get(x_3, 0);
x_15 = lean_ctor_get(x_3, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_3);
x_16 = lean_array_get_size(x_2);
lean_inc(x_1);
lean_inc(x_14);
x_17 = lean_apply_1(x_1, x_14);
x_18 = lean_unbox_uint64(x_17);
lean_dec(x_17);
x_19 = lean_hashset_mk_idx(x_16, x_18);
x_20 = lean_array_uget(x_2, x_19);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_14);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_array_uset(x_2, x_19, x_21);
x_2 = x_22;
x_3 = x_15;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_HashSetImp_moveEntries___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_foldl___at_Lean_HashSetImp_moveEntries___spec__1___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_HashSetImp_moveEntries___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_3);
x_6 = lean_nat_dec_lt(x_2, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_array_fget(x_3, x_2);
x_8 = lean_box(0);
x_9 = lean_array_fset(x_3, x_2, x_8);
lean_inc(x_1);
x_10 = l_List_foldl___at_Lean_HashSetImp_moveEntries___spec__1___rarg(x_1, x_4, x_7);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_2, x_11);
lean_dec(x_2);
x_2 = x_12;
x_3 = x_9;
x_4 = x_10;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_HashSetImp_moveEntries(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_HashSetImp_moveEntries___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_HashSetImp_expand___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_array_get_size(x_3);
x_5 = lean_unsigned_to_nat(2u);
x_6 = lean_nat_mul(x_4, x_5);
lean_dec(x_4);
x_7 = lean_box(0);
x_8 = lean_mk_array(x_6, x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Lean_HashSetImp_moveEntries___rarg(x_1, x_9, x_3, x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_HashSetImp_expand(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_HashSetImp_expand___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_HashSetImp_insert___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_HashSetImp_insert___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint64_t x_10; size_t x_11; lean_object* x_12; uint8_t x_13; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_array_get_size(x_7);
lean_inc(x_2);
lean_inc(x_4);
x_9 = lean_apply_1(x_2, x_4);
x_10 = lean_unbox_uint64(x_9);
lean_dec(x_9);
lean_inc(x_8);
x_11 = lean_hashset_mk_idx(x_8, x_10);
x_12 = lean_array_uget(x_7, x_11);
lean_inc(x_12);
lean_inc(x_4);
lean_inc(x_1);
x_13 = l_List_elem___rarg(x_1, x_4, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_dec(x_1);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_6, x_14);
lean_dec(x_6);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_4);
lean_ctor_set(x_16, 1, x_12);
x_17 = lean_array_uset(x_7, x_11, x_16);
x_18 = lean_nat_dec_le(x_15, x_8);
lean_dec(x_8);
if (x_18 == 0)
{
lean_object* x_19; 
lean_free_object(x_3);
x_19 = l_Lean_HashSetImp_expand___rarg(x_2, x_15, x_17);
return x_19;
}
else
{
lean_dec(x_2);
lean_ctor_set(x_3, 1, x_17);
lean_ctor_set(x_3, 0, x_15);
return x_3;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_8);
lean_dec(x_2);
x_20 = lean_box(0);
x_21 = lean_array_uset(x_7, x_11, x_20);
x_22 = l_Lean_HashSetImp_insert___rarg___closed__1;
lean_inc(x_4);
lean_inc(x_12);
x_23 = l_List_replaceTR_go___rarg(x_1, x_12, x_4, x_4, x_12, x_22);
lean_dec(x_12);
x_24 = lean_array_uset(x_21, x_11, x_23);
lean_ctor_set(x_3, 1, x_24);
return x_3;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint64_t x_29; size_t x_30; lean_object* x_31; uint8_t x_32; 
x_25 = lean_ctor_get(x_3, 0);
x_26 = lean_ctor_get(x_3, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_3);
x_27 = lean_array_get_size(x_26);
lean_inc(x_2);
lean_inc(x_4);
x_28 = lean_apply_1(x_2, x_4);
x_29 = lean_unbox_uint64(x_28);
lean_dec(x_28);
lean_inc(x_27);
x_30 = lean_hashset_mk_idx(x_27, x_29);
x_31 = lean_array_uget(x_26, x_30);
lean_inc(x_31);
lean_inc(x_4);
lean_inc(x_1);
x_32 = l_List_elem___rarg(x_1, x_4, x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
lean_dec(x_1);
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_nat_add(x_25, x_33);
lean_dec(x_25);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_4);
lean_ctor_set(x_35, 1, x_31);
x_36 = lean_array_uset(x_26, x_30, x_35);
x_37 = lean_nat_dec_le(x_34, x_27);
lean_dec(x_27);
if (x_37 == 0)
{
lean_object* x_38; 
x_38 = l_Lean_HashSetImp_expand___rarg(x_2, x_34, x_36);
return x_38;
}
else
{
lean_object* x_39; 
lean_dec(x_2);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_34);
lean_ctor_set(x_39, 1, x_36);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_27);
lean_dec(x_2);
x_40 = lean_box(0);
x_41 = lean_array_uset(x_26, x_30, x_40);
x_42 = l_Lean_HashSetImp_insert___rarg___closed__1;
lean_inc(x_4);
lean_inc(x_31);
x_43 = l_List_replaceTR_go___rarg(x_1, x_31, x_4, x_4, x_31, x_42);
lean_dec(x_31);
x_44 = lean_array_uset(x_41, x_30, x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_25);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HashSetImp_insert(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_HashSetImp_insert___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_HashSetImp_erase___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint64_t x_10; size_t x_11; lean_object* x_12; uint8_t x_13; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_array_get_size(x_7);
lean_inc(x_4);
x_9 = lean_apply_1(x_2, x_4);
x_10 = lean_unbox_uint64(x_9);
lean_dec(x_9);
x_11 = lean_hashset_mk_idx(x_8, x_10);
x_12 = lean_array_uget(x_7, x_11);
lean_inc(x_12);
lean_inc(x_4);
lean_inc(x_1);
x_13 = l_List_elem___rarg(x_1, x_4, x_12);
if (x_13 == 0)
{
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_box(0);
x_15 = lean_array_uset(x_7, x_11, x_14);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_6, x_16);
lean_dec(x_6);
x_18 = l_Lean_HashSetImp_insert___rarg___closed__1;
lean_inc(x_12);
x_19 = l_List_eraseTR_go___rarg(x_1, x_12, x_4, x_12, x_18);
lean_dec(x_12);
x_20 = lean_array_uset(x_15, x_11, x_19);
lean_ctor_set(x_3, 1, x_20);
lean_ctor_set(x_3, 0, x_17);
return x_3;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint64_t x_25; size_t x_26; lean_object* x_27; uint8_t x_28; 
x_21 = lean_ctor_get(x_3, 0);
x_22 = lean_ctor_get(x_3, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_3);
x_23 = lean_array_get_size(x_22);
lean_inc(x_4);
x_24 = lean_apply_1(x_2, x_4);
x_25 = lean_unbox_uint64(x_24);
lean_dec(x_24);
x_26 = lean_hashset_mk_idx(x_23, x_25);
x_27 = lean_array_uget(x_22, x_26);
lean_inc(x_27);
lean_inc(x_4);
lean_inc(x_1);
x_28 = l_List_elem___rarg(x_1, x_4, x_27);
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_27);
lean_dec(x_4);
lean_dec(x_1);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_21);
lean_ctor_set(x_29, 1, x_22);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_30 = lean_box(0);
x_31 = lean_array_uset(x_22, x_26, x_30);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_sub(x_21, x_32);
lean_dec(x_21);
x_34 = l_Lean_HashSetImp_insert___rarg___closed__1;
lean_inc(x_27);
x_35 = l_List_eraseTR_go___rarg(x_1, x_27, x_4, x_27, x_34);
lean_dec(x_27);
x_36 = lean_array_uset(x_31, x_26, x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_33);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HashSetImp_erase(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_HashSetImp_erase___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_mkHashSet___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkHashSetImp___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_mkHashSet(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_mkHashSet___rarg___boxed), 1, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_mkHashSet___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkHashSet___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_mkHashSet___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_mkHashSet(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_HashSet_empty___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Lean_mkHashSetImp___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_HashSet_empty(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_HashSet_empty___closed__1;
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_HashSet_empty___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_HashSet_empty(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_HashSet_instInhabited(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_HashSet_empty___closed__1;
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_HashSet_instInhabited___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_HashSet_instInhabited(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_HashSet_instEmptyCollection(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_HashSet_empty___closed__1;
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_HashSet_instEmptyCollection___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_HashSet_instEmptyCollection(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_HashSet_insert___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_HashSetImp_insert___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_HashSet_insert(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_HashSet_insert___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_HashSet_erase___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_HashSetImp_erase___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_HashSet_erase(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_HashSet_erase___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_HashSet_find_x3f___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_HashSetImp_find_x3f___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_HashSet_find_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_HashSet_find_x3f___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_HashSet_find_x3f___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_HashSet_find_x3f___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_HashSet_contains___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_HashSetImp_contains___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_HashSet_contains(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_HashSet_contains___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_HashSet_contains___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Lean_HashSet_contains___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSet_foldM___spec__1___rarg___lambda__1(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = 1;
x_8 = lean_usize_add(x_1, x_7);
x_9 = l_Array_foldlMUnsafe_fold___at_Lean_HashSet_foldM___spec__1___rarg(x_2, x_3, x_4, x_8, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSet_foldM___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_4, x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_array_uget(x_3, x_4);
lean_inc(x_2);
lean_inc(x_1);
x_10 = l_List_foldlM___rarg(x_1, lean_box(0), lean_box(0), x_2, x_6, x_9);
x_11 = lean_box_usize(x_4);
x_12 = lean_box_usize(x_5);
x_13 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_HashSet_foldM___spec__1___rarg___lambda__1___boxed), 6, 5);
lean_closure_set(x_13, 0, x_11);
lean_closure_set(x_13, 1, x_1);
lean_closure_set(x_13, 2, x_2);
lean_closure_set(x_13, 3, x_3);
lean_closure_set(x_13, 4, x_12);
x_14 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_10, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_3);
lean_dec(x_2);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_apply_2(x_16, lean_box(0), x_6);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSet_foldM___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_HashSet_foldM___spec__1___rarg___boxed), 6, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_HashSet_foldM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_array_get_size(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_lt(x_7, x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_apply_2(x_10, lean_box(0), x_3);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = lean_nat_dec_le(x_6, x_6);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_apply_2(x_14, lean_box(0), x_3);
return x_15;
}
else
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_18 = l_Array_foldlMUnsafe_fold___at_Lean_HashSet_foldM___spec__1___rarg(x_1, x_2, x_5, x_16, x_17, x_3);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HashSet_foldM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l_Lean_HashSet_foldM___rarg), 4, 0);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSet_foldM___spec__1___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_foldlMUnsafe_fold___at_Lean_HashSet_foldM___spec__1___rarg___lambda__1(x_7, x_2, x_3, x_4, x_8, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSet_foldM___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_foldlMUnsafe_fold___at_Lean_HashSet_foldM___spec__1___rarg(x_1, x_2, x_3, x_7, x_8, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_HashSet_foldM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_HashSet_foldM(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_HashSet_fold___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
lean_inc(x_1);
x_6 = lean_apply_2(x_1, x_2, x_4);
x_2 = x_6;
x_3 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_HashSet_fold___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_List_foldlM___at_Lean_HashSet_fold___spec__1___rarg), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSet_fold___spec__2___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_7 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_8 = l_List_foldlM___at_Lean_HashSet_fold___spec__1___rarg(x_1, x_5, x_7);
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
x_3 = x_10;
x_5 = x_8;
goto _start;
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSet_fold___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_HashSet_fold___spec__2___rarg___boxed), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_HashSet_fold___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_3, 1);
x_5 = lean_array_get_size(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_5);
if (x_7 == 0)
{
lean_dec(x_5);
lean_dec(x_1);
return x_2;
}
else
{
uint8_t x_8; 
x_8 = lean_nat_dec_le(x_5, x_5);
if (x_8 == 0)
{
lean_dec(x_5);
lean_dec(x_1);
return x_2;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = 0;
x_10 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_11 = l_Array_foldlMUnsafe_fold___at_Lean_HashSet_fold___spec__2___rarg(x_1, x_4, x_9, x_10, x_2);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HashSet_fold(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_HashSet_fold___rarg___boxed), 3, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSet_fold___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lean_HashSet_fold___spec__2___rarg(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_HashSet_fold___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_HashSet_fold___rarg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_HashSet_fold___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_HashSet_fold(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSet_forM___spec__1___rarg___lambda__1(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = 1;
x_8 = lean_usize_add(x_1, x_7);
x_9 = l_Array_foldlMUnsafe_fold___at_Lean_HashSet_forM___spec__1___rarg(x_2, x_3, x_4, x_8, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSet_forM___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_4, x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_6);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_array_uget(x_3, x_4);
lean_inc(x_2);
lean_inc(x_1);
x_10 = l_List_forM___rarg(x_1, lean_box(0), x_9, x_2);
x_11 = lean_box_usize(x_4);
x_12 = lean_box_usize(x_5);
x_13 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_HashSet_forM___spec__1___rarg___lambda__1___boxed), 6, 5);
lean_closure_set(x_13, 0, x_11);
lean_closure_set(x_13, 1, x_1);
lean_closure_set(x_13, 2, x_2);
lean_closure_set(x_13, 3, x_3);
lean_closure_set(x_13, 4, x_12);
x_14 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_10, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_3);
lean_dec(x_2);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_apply_2(x_16, lean_box(0), x_6);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSet_forM___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_HashSet_forM___spec__1___rarg___boxed), 6, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_HashSet_forM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_array_get_size(x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_lt(x_6, x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = lean_apply_2(x_9, lean_box(0), x_10);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = lean_nat_dec_le(x_5, x_5);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = lean_apply_2(x_14, lean_box(0), x_15);
return x_16;
}
else
{
size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; 
x_17 = 0;
x_18 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_19 = lean_box(0);
x_20 = l_Array_foldlMUnsafe_fold___at_Lean_HashSet_forM___spec__1___rarg(x_1, x_3, x_4, x_17, x_18, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HashSet_forM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_HashSet_forM___rarg), 3, 0);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSet_forM___spec__1___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_foldlMUnsafe_fold___at_Lean_HashSet_forM___spec__1___rarg___lambda__1(x_7, x_2, x_3, x_4, x_8, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSet_forM___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_foldlMUnsafe_fold___at_Lean_HashSet_forM___spec__1___rarg(x_1, x_2, x_3, x_7, x_8, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_HashSet_forM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_HashSet_forM(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
static lean_object* _init_l_Lean_HashSet_instForM___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_HashSet_forM___rarg), 3, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_HashSet_instForM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_HashSet_instForM___closed__1;
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_HashSet_instForM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_HashSet_instForM(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_ExceptT_bindCont___at_Lean_HashSet_instForIn___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
lean_dec(x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_apply_2(x_8, lean_box(0), x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_10);
x_14 = lean_apply_2(x_12, lean_box(0), x_13);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_1);
x_15 = lean_ctor_get(x_5, 0);
lean_inc(x_15);
lean_dec(x_5);
x_16 = lean_apply_1(x_4, x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_ExceptT_bindCont___at_Lean_HashSet_instForIn___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ExceptT_bindCont___at_Lean_HashSet_instForIn___spec__2___rarg), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_forM___at_Lean_HashSet_instForIn___spec__1___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_apply_2(x_5, lean_box(0), x_2);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_7);
x_11 = lean_apply_2(x_9, lean_box(0), x_10);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_2);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_13);
lean_ctor_set(x_2, 0, x_17);
x_18 = lean_apply_2(x_15, lean_box(0), x_2);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_2, 0);
lean_inc(x_19);
lean_dec(x_2);
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
lean_dec(x_1);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_19);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_apply_2(x_21, lean_box(0), x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at_Lean_HashSet_instForIn___spec__1___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = l_List_forM___at_Lean_HashSet_instForIn___spec__1___rarg(x_1, x_2, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_forM___at_Lean_HashSet_instForIn___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_6);
x_10 = lean_apply_2(x_8, lean_box(0), x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_inc(x_2);
x_14 = lean_apply_2(x_2, x_11, x_4);
lean_inc(x_1);
x_15 = lean_alloc_closure((void*)(l_List_forM___at_Lean_HashSet_instForIn___spec__1___rarg___lambda__1), 2, 1);
lean_closure_set(x_15, 0, x_1);
lean_inc(x_13);
x_16 = lean_apply_4(x_13, lean_box(0), lean_box(0), x_14, x_15);
lean_inc(x_1);
x_17 = lean_alloc_closure((void*)(l_List_forM___at_Lean_HashSet_instForIn___spec__1___rarg___lambda__2), 4, 3);
lean_closure_set(x_17, 0, x_1);
lean_closure_set(x_17, 1, x_2);
lean_closure_set(x_17, 2, x_12);
x_18 = lean_alloc_closure((void*)(l_ExceptT_bindCont___at_Lean_HashSet_instForIn___spec__2___rarg), 5, 4);
lean_closure_set(x_18, 0, x_1);
lean_closure_set(x_18, 1, lean_box(0));
lean_closure_set(x_18, 2, lean_box(0));
lean_closure_set(x_18, 3, x_17);
x_19 = lean_apply_4(x_13, lean_box(0), lean_box(0), x_16, x_18);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at_Lean_HashSet_instForIn___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_List_forM___at_Lean_HashSet_instForIn___spec__1___rarg), 4, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_ExceptT_bindCont___at_Lean_HashSet_instForIn___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
lean_dec(x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_apply_2(x_8, lean_box(0), x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_10);
x_14 = lean_apply_2(x_12, lean_box(0), x_13);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_1);
x_15 = lean_ctor_get(x_5, 0);
lean_inc(x_15);
lean_dec(x_5);
x_16 = lean_apply_1(x_4, x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_ExceptT_bindCont___at_Lean_HashSet_instForIn___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ExceptT_bindCont___at_Lean_HashSet_instForIn___spec__4___rarg), 5, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSet_instForIn___spec__3___rarg___lambda__1(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = 1;
x_10 = lean_usize_add(x_1, x_9);
x_11 = l_Array_foldlMUnsafe_fold___at_Lean_HashSet_instForIn___spec__3___rarg(x_2, x_3, x_4, x_10, x_5, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSet_instForIn___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_eq(x_4, x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_6);
x_9 = lean_array_uget(x_3, x_4);
lean_inc(x_2);
lean_inc(x_1);
x_10 = l_List_forM___at_Lean_HashSet_instForIn___spec__1___rarg(x_1, x_2, x_9, x_7);
x_11 = lean_box_usize(x_4);
x_12 = lean_box_usize(x_5);
lean_inc(x_1);
x_13 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_HashSet_instForIn___spec__3___rarg___lambda__1___boxed), 6, 5);
lean_closure_set(x_13, 0, x_11);
lean_closure_set(x_13, 1, x_1);
lean_closure_set(x_13, 2, x_2);
lean_closure_set(x_13, 3, x_3);
lean_closure_set(x_13, 4, x_12);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
x_15 = lean_alloc_closure((void*)(l_ExceptT_bindCont___at_Lean_HashSet_instForIn___spec__4___rarg), 5, 4);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, lean_box(0));
lean_closure_set(x_15, 2, lean_box(0));
lean_closure_set(x_15, 3, x_13);
x_16 = lean_apply_4(x_14, lean_box(0), lean_box(0), x_10, x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_3);
lean_dec(x_2);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_6);
lean_ctor_set(x_17, 1, x_7);
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
lean_dec(x_1);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_17);
x_21 = lean_apply_2(x_19, lean_box(0), x_20);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSet_instForIn___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_HashSet_instForIn___spec__3___rarg___boxed), 7, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_HashSet_instForIn___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_apply_2(x_5, lean_box(0), x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_apply_2(x_9, lean_box(0), x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_HashSet_instForIn___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l_Lean_HashSet_instForIn___rarg___lambda__1), 2, 1);
lean_closure_set(x_6, 0, x_1);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_array_get_size(x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_lt(x_9, x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_3);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_12);
x_16 = lean_apply_2(x_14, lean_box(0), x_15);
x_17 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_16, x_6);
return x_17;
}
else
{
uint8_t x_18; 
x_18 = lean_nat_dec_le(x_8, x_8);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_3);
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_20);
x_24 = lean_apply_2(x_22, lean_box(0), x_23);
x_25 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_24, x_6);
return x_25;
}
else
{
size_t x_26; size_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = 0;
x_27 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_28 = lean_box(0);
x_29 = l_Array_foldlMUnsafe_fold___at_Lean_HashSet_instForIn___spec__3___rarg(x_1, x_4, x_7, x_26, x_27, x_28, x_3);
x_30 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_29, x_6);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HashSet_instForIn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l_Lean_HashSet_instForIn___rarg), 4, 0);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSet_instForIn___spec__3___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_foldlMUnsafe_fold___at_Lean_HashSet_instForIn___spec__3___rarg___lambda__1(x_7, x_2, x_3, x_4, x_8, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSet_instForIn___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_10 = l_Array_foldlMUnsafe_fold___at_Lean_HashSet_instForIn___spec__3___rarg(x_1, x_2, x_3, x_8, x_9, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_HashSet_instForIn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_HashSet_instForIn(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_HashSet_size___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_HashSet_size(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_HashSet_size___rarg___boxed), 1, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_HashSet_size___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_HashSet_size___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_HashSet_size___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_HashSet_size(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_HashSet_isEmpty___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_HashSet_isEmpty(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_HashSet_isEmpty___rarg___boxed), 1, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_HashSet_isEmpty___rarg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_HashSet_isEmpty___rarg(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_HashSet_isEmpty___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_HashSet_isEmpty(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_HashSet_toList___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 1);
lean_ctor_set(x_2, 1, x_1);
x_1 = x_2;
x_2 = x_4;
goto _start;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_2);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_1);
x_1 = x_8;
x_2 = x_7;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_HashSet_toList___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_foldlM___at_Lean_HashSet_toList___spec__1___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSet_toList___spec__2___rarg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_List_foldlM___at_Lean_HashSet_toList___spec__1___rarg(x_4, x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_2 = x_9;
x_4 = x_7;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSet_toList___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_HashSet_toList___spec__2___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_HashSet_toList___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_2 = lean_box(0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
lean_dec(x_4);
return x_2;
}
else
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_4, x_4);
if (x_7 == 0)
{
lean_dec(x_4);
return x_2;
}
else
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = 0;
x_9 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_10 = l_Array_foldlMUnsafe_fold___at_Lean_HashSet_toList___spec__2___rarg(x_3, x_8, x_9, x_2);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HashSet_toList(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_HashSet_toList___rarg___boxed), 1, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSet_toList___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_HashSet_toList___spec__2___rarg(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_HashSet_toList___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_HashSet_toList___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_HashSet_toList___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_HashSet_toList(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_HashSet_toArray___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_array_push(x_1, x_3);
x_1 = x_5;
x_2 = x_4;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_HashSet_toArray___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_foldlM___at_Lean_HashSet_toArray___spec__1___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSet_toArray___spec__2___rarg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_List_foldlM___at_Lean_HashSet_toArray___spec__1___rarg(x_4, x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_2 = x_9;
x_4 = x_7;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSet_toArray___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_HashSet_toArray___spec__2___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_HashSet_toArray___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_3);
x_6 = l_Lean_HashSetImp_insert___rarg___closed__1;
return x_6;
}
else
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_3, x_3);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_3);
x_8 = l_Lean_HashSetImp_insert___rarg___closed__1;
return x_8;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; 
x_9 = 0;
x_10 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_11 = l_Lean_HashSetImp_insert___rarg___closed__1;
x_12 = l_Array_foldlMUnsafe_fold___at_Lean_HashSet_toArray___spec__2___rarg(x_2, x_9, x_10, x_11);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HashSet_toArray(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_HashSet_toArray___rarg___boxed), 1, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSet_toArray___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_HashSet_toArray___spec__2___rarg(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_HashSet_toArray___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_HashSet_toArray___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_HashSet_toArray___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_HashSet_toArray(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_HashSet_numBuckets___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_array_get_size(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_HashSet_numBuckets(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_HashSet_numBuckets___rarg___boxed), 1, 0);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_HashSet_numBuckets___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_HashSet_numBuckets___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_HashSet_numBuckets___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_HashSet_numBuckets(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_HashSet_insertMany___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_HashSetImp_insert___rarg(x_1, x_2, x_4, x_3);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_HashSet_insertMany___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_alloc_closure((void*)(l_Lean_HashSet_insertMany___rarg___lambda__1), 4, 2);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_2);
x_8 = l_Id_instMonad;
x_9 = lean_apply_5(x_4, lean_box(0), x_8, x_6, x_5, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_HashSet_insertMany(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_HashSet_insertMany___rarg), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_HashSet_merge___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_7 = l_Lean_HashSetImp_insert___rarg(x_1, x_2, x_3, x_5);
x_3 = x_7;
x_4 = x_6;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at_Lean_HashSet_merge___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_foldlM___at_Lean_HashSet_merge___spec__1___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSet_merge___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_4, x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; 
x_8 = lean_array_uget(x_3, x_4);
lean_inc(x_2);
lean_inc(x_1);
x_9 = l_List_foldlM___at_Lean_HashSet_merge___spec__1___rarg(x_1, x_2, x_6, x_8);
x_10 = 1;
x_11 = lean_usize_add(x_4, x_10);
x_4 = x_11;
x_6 = x_9;
goto _start;
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSet_merge___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_HashSet_merge___spec__2___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_HashSet_merge___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_4, 1);
x_6 = lean_array_get_size(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_lt(x_7, x_6);
if (x_8 == 0)
{
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
uint8_t x_9; 
x_9 = lean_nat_dec_le(x_6, x_6);
if (x_9 == 0)
{
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = 0;
x_11 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_12 = l_Array_foldlMUnsafe_fold___at_Lean_HashSet_merge___spec__2___rarg(x_1, x_2, x_5, x_10, x_11, x_3);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HashSet_merge(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_HashSet_merge___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_HashSet_merge___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_foldlMUnsafe_fold___at_Lean_HashSet_merge___spec__2___rarg(x_1, x_2, x_3, x_7, x_8, x_6);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_HashSet_merge___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_HashSet_merge___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
lean_object* initialize_Init_Data_Nat_Power2(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Data_HashSet_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Data_HashSet_Raw(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_HashSet(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Nat_Power2(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_HashSet_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_HashSet_Raw(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_HashSetImp_insert___rarg___closed__1 = _init_l_Lean_HashSetImp_insert___rarg___closed__1();
lean_mark_persistent(l_Lean_HashSetImp_insert___rarg___closed__1);
l_Lean_HashSet_empty___closed__1 = _init_l_Lean_HashSet_empty___closed__1();
lean_mark_persistent(l_Lean_HashSet_empty___closed__1);
l_Lean_HashSet_instForM___closed__1 = _init_l_Lean_HashSet_instForM___closed__1();
lean_mark_persistent(l_Lean_HashSet_instForM___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
