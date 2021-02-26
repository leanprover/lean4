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
lean_object* l_Array_modify___at_Std_PersistentHashMap_insertAux___spec__1(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
size_t l_USize_add(size_t, size_t);
lean_object* l_Std_PersistentHashMap_empty___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_isUnaryEntries___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_isEmpty___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_insertAtCollisionNode___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Std_PersistentHashMap_toList___spec__4___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Array_indexOfAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Std_PersistentHashMap_findEntryAux(lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe___at_Std_PersistentHashMap_toList___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_foldlMAux___at_Std_PersistentHashMap_toList___spec__2___rarg___lambda__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_root___default___closed__1;
lean_object* l_Std_PersistentHashMap_foldlMAux_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_USize_decEq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Std_PersistentHashMap_insertAux_traverse___rarg(lean_object*, lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_instToStringStats;
lean_object* l_Std_PersistentHashMap_insertAux_match__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_find_x21(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_foldlMAux___at_Std_PersistentHashMap_toList___spec__2___rarg___closed__1;
lean_object* l_Std_PersistentHashMap_Stats_maxDepth___default;
lean_object* l_Std_PersistentHashMap_insertAux(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_stats(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_foldlMAux_traverse___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_find_x3f_match__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_Std_PersistentHashMap_mod2Shift(size_t, size_t);
lean_object* l_Std_PersistentHashMap_findEntryAux___rarg(lean_object*, lean_object*, size_t, lean_object*);
lean_object* l_Std_PersistentHashMap_find_x3f_match__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_erase(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_collectStats___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_mkCollisionNode(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_isUnaryEntries_match__1(lean_object*, lean_object*, lean_object*);
size_t l_USize_sub(size_t, size_t);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Std_PersistentHashMap_Stats_numNull___default;
lean_object* l_Std_PersistentHashMap_foldlMAux_traverse___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_foldlM___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_Stats_toString___closed__2;
lean_object* l_Std_PersistentHashMap_forM___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_insertAux_traverse(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_toList___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_eraseAux___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_root___default___closed__2;
lean_object* l_Std_PersistentHashMap_collectStats___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_foldlMAux___at_Std_PersistentHashMap_toList___spec__2(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_instInhabitedPersistentHashMap(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_Stats_toString(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Std_PersistentHashMap_getCollisionNodeSize___rarg(lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Std_PersistentHashMap_toList___spec__4(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_getCollisionNodeSize_match__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_max(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_insert(lean_object*, lean_object*);
lean_object* l_Array_modifyM___at_Std_PersistentHashMap_insertAux___spec__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_eraseAux___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*);
lean_object* l_Std_PersistentHashMap_getCollisionNodeSize(lean_object*, lean_object*);
size_t l_USize_shiftRight(size_t, size_t);
size_t l_Std_PersistentHashMap_shift;
size_t l_Std_PersistentHashMap_mul2Shift(size_t, size_t);
lean_object* l_Std_PersistentHashMap_collectStats___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_foldlMAux___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_foldlM(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_findEntryAtAux(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_find_x3f_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_toList___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_stats___rarg___closed__1;
extern lean_object* l_Std_Range_myMacro____x40_Init_Data_Range___hyg_276____closed__22;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_stats___rarg___boxed(lean_object*);
lean_object* l_Std_PersistentHashMap_foldlM___at_Std_PersistentHashMap_toList___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_Std_PersistentHashMap_maxDepth;
lean_object* l_Std_PersistentHashMap_containsAux___rarg(lean_object*, lean_object*, size_t, lean_object*);
lean_object* l_Std_PersistentHashMap_collectStats_match__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_eraseAux_match__4___rarg(lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe___at_Array_foldl___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_eraseAux_match__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_empty___rarg(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_erase_match__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_find_x21___rarg___closed__4;
lean_object* l_Std_PersistentHashMap_foldlMAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_foldl___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_instInhabitedPersistentHashMap___rarg(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_insertAux___rarg___closed__3;
lean_object* l_Std_PersistentHashMap_isUnaryNode___rarg(lean_object*);
lean_object* l_Std_PersistentHashMap_find_x21___rarg___closed__1;
lean_object* l_Std_PersistentHashMap_foldlM___at_Std_PersistentHashMap_toList___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_contains___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_toList(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_containsAux(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_erase_match__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_insertAtCollisionNodeAux_match__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_findEntryAux___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_instToStringStats___closed__1;
lean_object* l_Std_PersistentHashMap_eraseAux_match__5___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_forM___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_find_x21___rarg___closed__2;
lean_object* l_Std_PersistentHashMap_eraseAux___rarg___lambda__2(lean_object*, lean_object*, lean_object*, size_t, lean_object*);
lean_object* l_Std_PersistentHashMap_instInhabitedEntry(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_foldlM___at_Std_PersistentHashMap_toList___spec__1___rarg___boxed(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_getOp(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_eraseAux_match__6___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_findAux(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_Stats_toString___closed__4;
lean_object* l_Array_foldlMUnsafe___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_isUnaryEntries(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_isUnaryEntries___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_insertAtCollisionNodeAux_match__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
lean_object* l_Std_PersistentHashMap_isEmpty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_collectStats___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe___at_Std_PersistentHashMap_toList___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_insertAux___rarg___boxed__const__2;
lean_object* l_Std_PersistentHashMap_erase_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_Stats_numNodes___default;
lean_object* l_Std_PersistentHashMap_foldlMAux_traverse___at_Std_PersistentHashMap_toList___spec__5___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_shiftLeft(size_t, size_t);
lean_object* l_Std_PersistentHashMap_containsAtAux___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_collectStats(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_getCollisionNodeSize_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_findEntry_x3f(lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Std_PersistentHashMap_toList___spec__4___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_collectStats_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_foldlMAux___at_Std_PersistentHashMap_toList___spec__2___rarg(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_stats___rarg(lean_object*);
lean_object* l_Std_PersistentHashMap_forM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_mul(size_t, size_t);
lean_object* l_Std_PersistentHashMap_findAtAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_insert___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_getCollisionNodeSize___rarg___boxed(lean_object*);
lean_object* l_Std_PersistentHashMap_foldlMAux___at_Std_PersistentHashMap_toList___spec__2___rarg___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_foldlMAux_traverse___at_Std_PersistentHashMap_toList___spec__5___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_maxCollisions;
lean_object* l_Std_PersistentHashMap_insertAtCollisionNodeAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Std_PersistentHashMap_foldlM___at_Std_PersistentHashMap_toList___spec__1___rarg(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_findD___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_findD___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_findAtAux___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_find_x3f(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_insertAux___rarg___lambda__1(lean_object*, lean_object*, lean_object*, size_t, size_t, size_t, size_t, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_insertAux_match__2(lean_object*, lean_object*, lean_object*);
size_t l_Std_PersistentHashMap_div2Shift(size_t, size_t);
lean_object* l_Std_PersistentHashMap_mod2Shift___boxed(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_foldl(lean_object*, lean_object*, lean_object*);
size_t l_USize_land(size_t, size_t);
lean_object* l_Std_PersistentHashMap_findEntry_x3f___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe___at_Std_PersistentHashMap_toList___spec__3(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_Stats_toString___closed__3;
lean_object* l_Std_PersistentHashMap_insertAux___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_instInhabitedNode___closed__1;
lean_object* l_Std_PersistentHashMap_getOp___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_Std_PersistentHashMap_insertAux___rarg___closed__1;
lean_object* l_Std_PersistentHashMap_size___default;
lean_object* l_Std_PersistentHashMap_insert_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_containsAux___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_isUnaryNode___rarg___boxed(lean_object*);
lean_object* l_Std_PersistentHashMap_find_x21_match__1(lean_object*, lean_object*);
extern lean_object* l_Id_instMonadId;
lean_object* l_Std_PersistentHashMap_findEntryAtAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_modifyM___at_Std_PersistentHashMap_insertAux___spec__2(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t l_USize_decLe(size_t, size_t);
lean_object* l_Std_PersistentHashMap_insertAux___rarg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_isUnaryEntries_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_find_x21___rarg___closed__3;
lean_object* l_Std_PersistentHashMap_root___default(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_eraseAux_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_insertAux_match__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_mkCollisionNode___rarg___closed__1;
lean_object* l_Std_PersistentHashMap_mul2Shift___boxed(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_eraseAux_match__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_modify___at_Std_PersistentHashMap_insertAux___spec__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_findAtAux(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_erase___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_foldlMAux_traverse___at_Std_PersistentHashMap_toList___spec__5(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_insertAtCollisionNode(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_findAux_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_stats___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_eraseAux_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_findAux_match__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_find_x21_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_eraseIdx_x27___rarg(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_findAux___rarg(lean_object*, lean_object*, size_t, lean_object*);
lean_object* l_Std_PersistentHashMap_isUnaryNode(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_eraseAux_match__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_eraseAux_match__3___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_eraseAux___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_isUnaryNode_match__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_isEmpty___rarg___boxed(lean_object*);
lean_object* l_Std_PersistentHashMap_contains(lean_object*, lean_object*);
lean_object* l_Array_modify___at_Std_PersistentHashMap_insertAux___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_insert_match__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_findD(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_insertAux_match__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_Std_PersistentHashMap_branching;
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_findAux_match__1___rarg(lean_object*, size_t, lean_object*, lean_object*, lean_object*);
size_t l_Std_PersistentHashMap_insertAux___rarg___closed__2;
lean_object* l_Std_PersistentHashMap_insertAux_traverse___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_forM___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_findAux___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_foldlMAux_traverse(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_find_x21___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_insertAux_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_instInhabitedPersistentHashMap___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Array_modifyM___at_Std_PersistentHashMap_insertAux___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_eraseAux___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_foldl___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_insert_match__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_eraseAux_match__5(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_eraseAux_match__4(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_div2Shift___boxed(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_eraseAux_match__6___rarg(lean_object*, size_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_Stats_toString___closed__1;
lean_object* l_Std_PersistentHashMap_foldlM___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_eraseAux___rarg(lean_object*, lean_object*, size_t, lean_object*);
lean_object* l_Std_PersistentHashMap_eraseAux_match__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_insertAux___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_find_x3f___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_isUnaryNode_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_eraseAux_match__6(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_forM(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_eraseAux(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_insertAux_match__3___rarg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_foldlMAux_traverse___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Std_PersistentHashMap_empty(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_foldlMAux___at_Std_PersistentHashMap_toList___spec__2___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_eraseAux_match__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_foldlMAux___at_Std_PersistentHashMap_toList___spec__2___rarg___closed__2;
lean_object* l_Std_PersistentHashMap_foldlMAux_match__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_mkEmptyEntriesArray___closed__1;
lean_object* l_Std_PersistentHashMap_insertAtCollisionNodeAux(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_insertAux___rarg___boxed__const__1;
lean_object* l_Std_PersistentHashMap_instInhabitedNode(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_findEntryAtAux___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_PersistentHashMap_isEmpty___rarg(lean_object*);
lean_object* l_Std_PersistentHashMap_containsAtAux(lean_object*, lean_object*);
uint8_t l_Std_PersistentHashMap_containsAtAux___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_foldlMAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_foldlMAux___at_Std_PersistentHashMap_toList___spec__2___rarg___lambda__1(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_mkCollisionNode___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_insertAux_match__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_Stats_numCollisions___default;
lean_object* l_Std_PersistentHashMap_instInhabitedEntry(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_1 = l_Array_empty___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Std_PersistentHashMap_instInhabitedNode(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_PersistentHashMap_instInhabitedNode___closed__1;
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
lean_object* l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Std_PersistentHashMap_root___default(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Std_PersistentHashMap_empty___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Std_PersistentHashMap_empty(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_empty___rarg___boxed), 2, 0);
return x_3;
}
}
lean_object* l_Std_PersistentHashMap_empty___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_PersistentHashMap_empty___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
uint8_t l_Std_PersistentHashMap_isEmpty___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
return x_4;
}
}
lean_object* l_Std_PersistentHashMap_isEmpty(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_isEmpty___rarg___boxed), 1, 0);
return x_5;
}
}
lean_object* l_Std_PersistentHashMap_isEmpty___rarg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Std_PersistentHashMap_isEmpty___rarg(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Std_PersistentHashMap_isEmpty___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_PersistentHashMap_isEmpty(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Std_PersistentHashMap_instInhabitedPersistentHashMap___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Std_PersistentHashMap_instInhabitedPersistentHashMap(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_instInhabitedPersistentHashMap___rarg___boxed), 2, 0);
return x_3;
}
}
lean_object* l_Std_PersistentHashMap_instInhabitedPersistentHashMap___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_PersistentHashMap_instInhabitedPersistentHashMap___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Std_PersistentHashMap_mkEmptyEntries(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_PersistentHashMap_root___default___closed__2;
return x_3;
}
}
size_t l_Std_PersistentHashMap_mul2Shift(size_t x_1, size_t x_2) {
_start:
{
size_t x_3; 
x_3 = x_1 << x_2;
return x_3;
}
}
lean_object* l_Std_PersistentHashMap_mul2Shift___boxed(lean_object* x_1, lean_object* x_2) {
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
size_t l_Std_PersistentHashMap_div2Shift(size_t x_1, size_t x_2) {
_start:
{
size_t x_3; 
x_3 = x_1 >> x_2;
return x_3;
}
}
lean_object* l_Std_PersistentHashMap_div2Shift___boxed(lean_object* x_1, lean_object* x_2) {
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
size_t l_Std_PersistentHashMap_mod2Shift(size_t x_1, size_t x_2) {
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
lean_object* l_Std_PersistentHashMap_mod2Shift___boxed(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Std_PersistentHashMap_insertAtCollisionNodeAux_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_5);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_5(x_6, x_7, lean_box(0), x_2, x_3, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = lean_apply_8(x_5, x_1, x_9, x_10, lean_box(0), lean_box(0), x_2, x_3, x_4);
return x_11;
}
}
}
lean_object* l_Std_PersistentHashMap_insertAtCollisionNodeAux_match__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_insertAtCollisionNodeAux_match__2___rarg), 6, 0);
return x_4;
}
}
lean_object* l_Std_PersistentHashMap_insertAtCollisionNodeAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* l_Std_PersistentHashMap_insertAtCollisionNodeAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_insertAtCollisionNodeAux___rarg), 5, 0);
return x_3;
}
}
lean_object* l_Std_PersistentHashMap_insertAtCollisionNode___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Std_PersistentHashMap_insertAtCollisionNodeAux___rarg(x_1, x_2, x_5, x_3, x_4);
return x_6;
}
}
lean_object* l_Std_PersistentHashMap_insertAtCollisionNode(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_insertAtCollisionNode___rarg), 4, 0);
return x_3;
}
}
lean_object* l_Std_PersistentHashMap_getCollisionNodeSize_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_3, x_4, lean_box(0));
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_4(x_2, x_6, x_7, lean_box(0), lean_box(0));
return x_8;
}
}
}
lean_object* l_Std_PersistentHashMap_getCollisionNodeSize_match__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_getCollisionNodeSize_match__1___rarg), 3, 0);
return x_4;
}
}
lean_object* l_Std_PersistentHashMap_getCollisionNodeSize___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_array_get_size(x_2);
return x_3;
}
}
lean_object* l_Std_PersistentHashMap_getCollisionNodeSize(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_getCollisionNodeSize___rarg___boxed), 1, 0);
return x_3;
}
}
lean_object* l_Std_PersistentHashMap_getCollisionNodeSize___rarg___boxed(lean_object* x_1) {
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
lean_object* l_Std_PersistentHashMap_mkCollisionNode___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l_Std_PersistentHashMap_mkCollisionNode(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_mkCollisionNode___rarg), 4, 0);
return x_3;
}
}
lean_object* l_Std_PersistentHashMap_insertAux_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_4, lean_box(0));
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_4(x_3, x_6, x_7, lean_box(0), lean_box(0));
return x_8;
}
}
}
lean_object* l_Std_PersistentHashMap_insertAux_match__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_insertAux_match__1___rarg), 3, 0);
return x_4;
}
}
lean_object* l_Std_PersistentHashMap_insertAux_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_2(x_4, x_5, x_6);
return x_7;
}
case 1:
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_2);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_apply_1(x_3, x_8);
return x_9;
}
default: 
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
lean_dec(x_3);
x_10 = lean_box(0);
x_11 = lean_apply_1(x_2, x_10);
return x_11;
}
}
}
}
lean_object* l_Std_PersistentHashMap_insertAux_match__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_insertAux_match__2___rarg), 4, 0);
return x_4;
}
}
lean_object* l_Std_PersistentHashMap_insertAux_match__3___rarg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_box_usize(x_2);
x_10 = lean_box_usize(x_3);
x_11 = lean_apply_5(x_7, x_8, x_9, x_10, x_4, x_5);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_7);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_box_usize(x_2);
x_15 = lean_box_usize(x_3);
x_16 = lean_apply_7(x_6, x_12, x_13, lean_box(0), x_14, x_15, x_4, x_5);
return x_16;
}
}
}
lean_object* l_Std_PersistentHashMap_insertAux_match__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_insertAux_match__3___rarg___boxed), 7, 0);
return x_4;
}
}
lean_object* l_Std_PersistentHashMap_insertAux_match__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l_Std_PersistentHashMap_insertAux_match__3___rarg(x_1, x_8, x_9, x_4, x_5, x_6, x_7);
return x_10;
}
}
lean_object* l_Std_PersistentHashMap_insertAux_traverse___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_11 = lean_array_fget(x_4, x_7);
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
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_7, x_20);
lean_dec(x_7);
lean_inc(x_2);
lean_inc(x_1);
x_22 = l_Std_PersistentHashMap_insertAux___rarg(x_1, x_2, x_8, x_19, x_3, x_11, x_12);
x_6 = lean_box(0);
x_7 = x_21;
x_8 = x_22;
goto _start;
}
}
}
lean_object* l_Std_PersistentHashMap_insertAux_traverse(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_insertAux_traverse___rarg___boxed), 8, 0);
return x_3;
}
}
lean_object* l_Array_modifyM___at_Std_PersistentHashMap_insertAux___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec(x_3);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_array_fget(x_1, x_2);
x_7 = lean_box(2);
x_8 = lean_array_fset(x_1, x_2, x_7);
x_9 = lean_apply_1(x_3, x_6);
x_10 = lean_array_fset(x_8, x_2, x_9);
return x_10;
}
}
}
lean_object* l_Array_modifyM___at_Std_PersistentHashMap_insertAux___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_modifyM___at_Std_PersistentHashMap_insertAux___spec__2___rarg___boxed), 3, 0);
return x_3;
}
}
lean_object* l_Array_modify___at_Std_PersistentHashMap_insertAux___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_modifyM___at_Std_PersistentHashMap_insertAux___spec__2___rarg(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Array_modify___at_Std_PersistentHashMap_insertAux___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_modify___at_Std_PersistentHashMap_insertAux___spec__1___rarg___boxed), 3, 0);
return x_3;
}
}
lean_object* l_Std_PersistentHashMap_insertAux___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
switch (lean_obj_tag(x_9)) {
case 0:
{
uint8_t x_10; 
lean_dec(x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_inc(x_2);
x_13 = lean_apply_2(x_1, x_2, x_11);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_free_object(x_9);
x_15 = l_Std_PersistentHashMap_mkCollisionNode___rarg(x_11, x_12, x_2, x_3);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
else
{
lean_dec(x_12);
lean_dec(x_11);
lean_ctor_set(x_9, 1, x_3);
lean_ctor_set(x_9, 0, x_2);
return x_9;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_9, 0);
x_18 = lean_ctor_get(x_9, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_9);
lean_inc(x_17);
lean_inc(x_2);
x_19 = lean_apply_2(x_1, x_2, x_17);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = l_Std_PersistentHashMap_mkCollisionNode___rarg(x_17, x_18, x_2, x_3);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
else
{
lean_object* x_23; 
lean_dec(x_18);
lean_dec(x_17);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_2);
lean_ctor_set(x_23, 1, x_3);
return x_23;
}
}
}
case 1:
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_9);
if (x_24 == 0)
{
lean_object* x_25; size_t x_26; size_t x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_9, 0);
x_26 = x_4 >> x_5;
x_27 = x_6 + x_7;
x_28 = l_Std_PersistentHashMap_insertAux___rarg(x_1, x_8, x_25, x_26, x_27, x_2, x_3);
lean_ctor_set(x_9, 0, x_28);
return x_9;
}
else
{
lean_object* x_29; size_t x_30; size_t x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_9, 0);
lean_inc(x_29);
lean_dec(x_9);
x_30 = x_4 >> x_5;
x_31 = x_6 + x_7;
x_32 = l_Std_PersistentHashMap_insertAux___rarg(x_1, x_8, x_29, x_30, x_31, x_2, x_3);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
}
default: 
{
lean_object* x_34; 
lean_dec(x_8);
lean_dec(x_1);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_2);
lean_ctor_set(x_34, 1, x_3);
return x_34;
}
}
}
}
static size_t _init_l_Std_PersistentHashMap_insertAux___rarg___closed__1() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = 5;
x_3 = x_1 << x_2;
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
static lean_object* _init_l_Std_PersistentHashMap_insertAux___rarg___boxed__const__1() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 5;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_PersistentHashMap_insertAux___rarg___boxed__const__2() {
_start:
{
size_t x_1; lean_object* x_2; 
x_1 = 1;
x_2 = lean_box_usize(x_1);
return x_2;
}
}
lean_object* l_Std_PersistentHashMap_insertAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_3);
if (x_8 == 0)
{
lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = l_Std_PersistentHashMap_insertAux___rarg___closed__2;
x_11 = x_4 & x_10;
x_12 = lean_usize_to_nat(x_11);
x_13 = lean_box_usize(x_4);
x_14 = l_Std_PersistentHashMap_insertAux___rarg___boxed__const__1;
x_15 = lean_box_usize(x_5);
x_16 = l_Std_PersistentHashMap_insertAux___rarg___boxed__const__2;
x_17 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_insertAux___rarg___lambda__1___boxed), 9, 8);
lean_closure_set(x_17, 0, x_1);
lean_closure_set(x_17, 1, x_6);
lean_closure_set(x_17, 2, x_7);
lean_closure_set(x_17, 3, x_13);
lean_closure_set(x_17, 4, x_14);
lean_closure_set(x_17, 5, x_15);
lean_closure_set(x_17, 6, x_16);
lean_closure_set(x_17, 7, x_2);
x_18 = l_Array_modifyM___at_Std_PersistentHashMap_insertAux___spec__2___rarg(x_9, x_12, x_17);
lean_dec(x_12);
lean_ctor_set(x_3, 0, x_18);
return x_3;
}
else
{
lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_19 = lean_ctor_get(x_3, 0);
lean_inc(x_19);
lean_dec(x_3);
x_20 = l_Std_PersistentHashMap_insertAux___rarg___closed__2;
x_21 = x_4 & x_20;
x_22 = lean_usize_to_nat(x_21);
x_23 = lean_box_usize(x_4);
x_24 = l_Std_PersistentHashMap_insertAux___rarg___boxed__const__1;
x_25 = lean_box_usize(x_5);
x_26 = l_Std_PersistentHashMap_insertAux___rarg___boxed__const__2;
x_27 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_insertAux___rarg___lambda__1___boxed), 9, 8);
lean_closure_set(x_27, 0, x_1);
lean_closure_set(x_27, 1, x_6);
lean_closure_set(x_27, 2, x_7);
lean_closure_set(x_27, 3, x_23);
lean_closure_set(x_27, 4, x_24);
lean_closure_set(x_27, 5, x_25);
lean_closure_set(x_27, 6, x_26);
lean_closure_set(x_27, 7, x_2);
x_28 = l_Array_modifyM___at_Std_PersistentHashMap_insertAux___spec__2___rarg(x_19, x_22, x_27);
lean_dec(x_22);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_3);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; size_t x_33; uint8_t x_34; 
x_31 = lean_unsigned_to_nat(0u);
lean_inc(x_1);
x_32 = l_Std_PersistentHashMap_insertAtCollisionNodeAux___rarg(x_1, x_3, x_31, x_6, x_7);
x_33 = 7;
x_34 = x_33 <= x_5;
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = l_Std_PersistentHashMap_getCollisionNodeSize___rarg(x_32);
x_36 = lean_unsigned_to_nat(4u);
x_37 = lean_nat_dec_lt(x_35, x_36);
lean_dec(x_35);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_32, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_32, 1);
lean_inc(x_39);
lean_dec(x_32);
x_40 = l_Std_PersistentHashMap_insertAux___rarg___closed__3;
x_41 = l_Std_PersistentHashMap_insertAux_traverse___rarg(x_1, x_2, x_5, x_38, x_39, lean_box(0), x_31, x_40);
lean_dec(x_39);
lean_dec(x_38);
return x_41;
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_32;
}
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_32;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; size_t x_47; uint8_t x_48; 
x_42 = lean_ctor_get(x_3, 0);
x_43 = lean_ctor_get(x_3, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_3);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_unsigned_to_nat(0u);
lean_inc(x_1);
x_46 = l_Std_PersistentHashMap_insertAtCollisionNodeAux___rarg(x_1, x_44, x_45, x_6, x_7);
x_47 = 7;
x_48 = x_47 <= x_5;
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_49 = l_Std_PersistentHashMap_getCollisionNodeSize___rarg(x_46);
x_50 = lean_unsigned_to_nat(4u);
x_51 = lean_nat_dec_lt(x_49, x_50);
lean_dec(x_49);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_46, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_46, 1);
lean_inc(x_53);
lean_dec(x_46);
x_54 = l_Std_PersistentHashMap_insertAux___rarg___closed__3;
x_55 = l_Std_PersistentHashMap_insertAux_traverse___rarg(x_1, x_2, x_5, x_52, x_53, lean_box(0), x_45, x_54);
lean_dec(x_53);
lean_dec(x_52);
return x_55;
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_46;
}
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_46;
}
}
}
}
}
lean_object* l_Std_PersistentHashMap_insertAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_insertAux___rarg___boxed), 7, 0);
return x_3;
}
}
lean_object* l_Std_PersistentHashMap_insertAux_traverse___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_object* l_Array_modifyM___at_Std_PersistentHashMap_insertAux___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_modifyM___at_Std_PersistentHashMap_insertAux___spec__2___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Array_modify___at_Std_PersistentHashMap_insertAux___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_modify___at_Std_PersistentHashMap_insertAux___spec__1___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Std_PersistentHashMap_insertAux___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_12 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_13 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_14 = l_Std_PersistentHashMap_insertAux___rarg___lambda__1(x_1, x_2, x_3, x_10, x_11, x_12, x_13, x_8, x_9);
return x_14;
}
}
lean_object* l_Std_PersistentHashMap_insertAux___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
lean_object* l_Std_PersistentHashMap_insert_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_4(x_4, x_5, x_6, x_2, x_3);
return x_7;
}
}
lean_object* l_Std_PersistentHashMap_insert_match__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_insert_match__1___rarg), 4, 0);
return x_6;
}
}
lean_object* l_Std_PersistentHashMap_insert_match__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_PersistentHashMap_insert_match__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
lean_object* l_Std_PersistentHashMap_insert___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_12 = l_Std_PersistentHashMap_insertAux___rarg(x_1, x_2, x_7, x_10, x_11, x_4, x_5);
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
x_20 = l_Std_PersistentHashMap_insertAux___rarg(x_1, x_2, x_15, x_18, x_19, x_4, x_5);
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
lean_object* l_Std_PersistentHashMap_insert(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_insert___rarg), 5, 0);
return x_3;
}
}
lean_object* l_Std_PersistentHashMap_findAtAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* l_Std_PersistentHashMap_findAtAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_findAtAux___rarg___boxed), 6, 0);
return x_3;
}
}
lean_object* l_Std_PersistentHashMap_findAtAux___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_PersistentHashMap_findAtAux___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Std_PersistentHashMap_findAux_match__1___rarg(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_5);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_box_usize(x_2);
x_8 = lean_apply_3(x_4, x_6, x_7, x_3);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_4);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_box_usize(x_2);
x_12 = lean_apply_5(x_5, x_9, x_10, lean_box(0), x_11, x_3);
return x_12;
}
}
}
lean_object* l_Std_PersistentHashMap_findAux_match__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_findAux_match__1___rarg___boxed), 5, 0);
return x_4;
}
}
lean_object* l_Std_PersistentHashMap_findAux_match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; lean_object* x_7; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = l_Std_PersistentHashMap_findAux_match__1___rarg(x_1, x_6, x_3, x_4, x_5);
return x_7;
}
}
lean_object* l_Std_PersistentHashMap_findAux___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
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
x_19 = x_3 >> x_6;
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
lean_object* l_Std_PersistentHashMap_findAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_findAux___rarg___boxed), 4, 0);
return x_3;
}
}
lean_object* l_Std_PersistentHashMap_findAux___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Std_PersistentHashMap_findAux___rarg(x_1, x_2, x_5, x_4);
return x_6;
}
}
lean_object* l_Std_PersistentHashMap_find_x3f_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_3(x_3, x_4, x_2, x_5);
return x_6;
}
}
lean_object* l_Std_PersistentHashMap_find_x3f_match__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_find_x3f_match__1___rarg), 3, 0);
return x_6;
}
}
lean_object* l_Std_PersistentHashMap_find_x3f_match__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_PersistentHashMap_find_x3f_match__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
lean_object* l_Std_PersistentHashMap_find_x3f___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_8 = l_Std_PersistentHashMap_findAux___rarg(x_1, x_5, x_7, x_4);
return x_8;
}
}
lean_object* l_Std_PersistentHashMap_find_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_find_x3f___rarg), 4, 0);
return x_3;
}
}
lean_object* l_Std_PersistentHashMap_getOp___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_PersistentHashMap_find_x3f___rarg(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Std_PersistentHashMap_getOp(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_getOp___rarg), 4, 0);
return x_3;
}
}
lean_object* l_Std_PersistentHashMap_findD___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* l_Std_PersistentHashMap_findD(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_findD___rarg___boxed), 5, 0);
return x_3;
}
}
lean_object* l_Std_PersistentHashMap_findD___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_PersistentHashMap_findD___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
return x_6;
}
}
lean_object* l_Std_PersistentHashMap_find_x21_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l_Std_PersistentHashMap_find_x21_match__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_find_x21_match__1___rarg), 3, 0);
return x_3;
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
x_3 = lean_unsigned_to_nat(159u);
x_4 = lean_unsigned_to_nat(14u);
x_5 = l_Std_PersistentHashMap_find_x21___rarg___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Std_PersistentHashMap_find_x21___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* l_Std_PersistentHashMap_find_x21(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_find_x21___rarg), 5, 0);
return x_3;
}
}
lean_object* l_Std_PersistentHashMap_findEntryAtAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* l_Std_PersistentHashMap_findEntryAtAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_findEntryAtAux___rarg___boxed), 6, 0);
return x_3;
}
}
lean_object* l_Std_PersistentHashMap_findEntryAtAux___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_PersistentHashMap_findEntryAtAux___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Std_PersistentHashMap_findEntryAux___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
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
x_26 = l_Std_PersistentHashMap_findEntryAtAux___rarg(x_1, x_23, x_24, lean_box(0), x_25, x_4);
lean_dec(x_24);
lean_dec(x_23);
return x_26;
}
}
}
lean_object* l_Std_PersistentHashMap_findEntryAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_findEntryAux___rarg___boxed), 4, 0);
return x_3;
}
}
lean_object* l_Std_PersistentHashMap_findEntryAux___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Std_PersistentHashMap_findEntryAux___rarg(x_1, x_2, x_5, x_4);
return x_6;
}
}
lean_object* l_Std_PersistentHashMap_findEntry_x3f___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_8 = l_Std_PersistentHashMap_findEntryAux___rarg(x_1, x_5, x_7, x_4);
return x_8;
}
}
lean_object* l_Std_PersistentHashMap_findEntry_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_findEntry_x3f___rarg), 4, 0);
return x_3;
}
}
uint8_t l_Std_PersistentHashMap_containsAtAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* l_Std_PersistentHashMap_containsAtAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_containsAtAux___rarg___boxed), 6, 0);
return x_3;
}
}
lean_object* l_Std_PersistentHashMap_containsAtAux___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* l_Std_PersistentHashMap_containsAux___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
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
lean_object* l_Std_PersistentHashMap_containsAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_containsAux___rarg___boxed), 4, 0);
return x_3;
}
}
lean_object* l_Std_PersistentHashMap_containsAux___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Std_PersistentHashMap_containsAux___rarg(x_1, x_2, x_5, x_4);
return x_6;
}
}
lean_object* l_Std_PersistentHashMap_contains___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_8 = l_Std_PersistentHashMap_containsAux___rarg(x_1, x_5, x_7, x_4);
return x_8;
}
}
lean_object* l_Std_PersistentHashMap_contains(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_contains___rarg), 4, 0);
return x_3;
}
}
lean_object* l_Std_PersistentHashMap_isUnaryEntries_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l_Std_PersistentHashMap_isUnaryEntries_match__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_isUnaryEntries_match__1___rarg), 3, 0);
return x_4;
}
}
lean_object* l_Std_PersistentHashMap_isUnaryEntries___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Std_PersistentHashMap_isUnaryEntries(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_isUnaryEntries___rarg___boxed), 3, 0);
return x_3;
}
}
lean_object* l_Std_PersistentHashMap_isUnaryEntries___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_PersistentHashMap_isUnaryEntries___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Std_PersistentHashMap_isUnaryNode_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_3(x_3, x_6, x_7, lean_box(0));
return x_8;
}
}
}
lean_object* l_Std_PersistentHashMap_isUnaryNode_match__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_isUnaryNode_match__1___rarg), 3, 0);
return x_4;
}
}
lean_object* l_Std_PersistentHashMap_isUnaryNode___rarg(lean_object* x_1) {
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
lean_object* l_Std_PersistentHashMap_isUnaryNode(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_isUnaryNode___rarg___boxed), 1, 0);
return x_3;
}
}
lean_object* l_Std_PersistentHashMap_isUnaryNode___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_PersistentHashMap_isUnaryNode___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Std_PersistentHashMap_eraseAux_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_2(x_2, x_1, lean_box(0));
return x_3;
}
}
lean_object* l_Std_PersistentHashMap_eraseAux_match__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_eraseAux_match__1___rarg), 2, 0);
return x_4;
}
}
lean_object* l_Std_PersistentHashMap_eraseAux_match__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_PersistentHashMap_eraseAux_match__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Std_PersistentHashMap_eraseAux_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
lean_object* l_Std_PersistentHashMap_eraseAux_match__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_eraseAux_match__2___rarg), 3, 0);
return x_4;
}
}
lean_object* l_Std_PersistentHashMap_eraseAux_match__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_PersistentHashMap_eraseAux_match__2(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Std_PersistentHashMap_eraseAux_match__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_apply_2(x_3, x_7, x_8);
return x_9;
}
}
}
lean_object* l_Std_PersistentHashMap_eraseAux_match__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_eraseAux_match__3___rarg), 3, 0);
return x_4;
}
}
lean_object* l_Std_PersistentHashMap_eraseAux_match__4___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Std_PersistentHashMap_eraseAux_match__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_eraseAux_match__4___rarg), 2, 0);
return x_4;
}
}
lean_object* l_Std_PersistentHashMap_eraseAux_match__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_2(x_3, x_5, x_6);
return x_7;
}
case 1:
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
lean_dec(x_2);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_apply_1(x_4, x_8);
return x_9;
}
default: 
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
lean_dec(x_3);
x_10 = lean_box(0);
x_11 = lean_apply_1(x_2, x_10);
return x_11;
}
}
}
}
lean_object* l_Std_PersistentHashMap_eraseAux_match__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_eraseAux_match__5___rarg), 4, 0);
return x_4;
}
}
lean_object* l_Std_PersistentHashMap_eraseAux_match__6___rarg(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_box_usize(x_2);
x_8 = lean_apply_4(x_5, x_1, x_6, x_7, x_3);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = lean_box_usize(x_2);
x_12 = lean_apply_6(x_4, x_1, x_9, x_10, lean_box(0), x_11, x_3);
return x_12;
}
}
}
lean_object* l_Std_PersistentHashMap_eraseAux_match__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_eraseAux_match__6___rarg___boxed), 5, 0);
return x_4;
}
}
lean_object* l_Std_PersistentHashMap_eraseAux_match__6___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; lean_object* x_7; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = l_Std_PersistentHashMap_eraseAux_match__6___rarg(x_1, x_6, x_3, x_4, x_5);
return x_7;
}
}
lean_object* l_Std_PersistentHashMap_eraseAux___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_indexOfAux___rarg(x_1, x_3, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_4);
lean_dec(x_3);
x_10 = 0;
x_11 = lean_box(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_2);
x_13 = lean_ctor_get(x_9, 0);
lean_inc(x_13);
lean_dec(x_9);
x_14 = l_Array_eraseIdx_x27___rarg(x_3, x_13);
x_15 = l_Array_eraseIdx_x27___rarg(x_4, x_13);
lean_dec(x_13);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = 1;
x_18 = lean_box(x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
lean_object* l_Std_PersistentHashMap_eraseAux___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = 5;
x_7 = l_Std_PersistentHashMap_insertAux___rarg___closed__2;
x_8 = x_4 & x_7;
x_9 = lean_usize_to_nat(x_8);
x_10 = lean_box(2);
x_11 = lean_array_get(x_10, x_3, x_9);
switch (lean_obj_tag(x_11)) {
case 0:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_apply_2(x_1, x_5, x_12);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
uint8_t x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_9);
lean_dec(x_3);
x_15 = 0;
x_16 = lean_box(x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_2);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_2);
x_18 = lean_array_set(x_3, x_9, x_10);
lean_dec(x_9);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = 1;
x_21 = lean_box(x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
case 1:
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_11);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; size_t x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_24 = lean_ctor_get(x_11, 0);
x_25 = lean_array_set(x_3, x_9, x_10);
x_26 = x_4 >> x_6;
x_27 = l_Std_PersistentHashMap_eraseAux___rarg(x_1, x_24, x_26, x_5);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
x_29 = lean_unbox(x_28);
lean_dec(x_28);
if (x_29 == 0)
{
uint8_t x_30; 
lean_dec(x_25);
lean_free_object(x_11);
lean_dec(x_9);
x_30 = !lean_is_exclusive(x_27);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_27, 1);
lean_dec(x_31);
x_32 = lean_ctor_get(x_27, 0);
lean_dec(x_32);
x_33 = 0;
x_34 = lean_box(x_33);
lean_ctor_set(x_27, 1, x_34);
lean_ctor_set(x_27, 0, x_2);
return x_27;
}
else
{
uint8_t x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_27);
x_35 = 0;
x_36 = lean_box(x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_2);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
else
{
uint8_t x_38; 
lean_dec(x_2);
x_38 = !lean_is_exclusive(x_27);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_27, 0);
x_40 = lean_ctor_get(x_27, 1);
lean_dec(x_40);
x_41 = l_Std_PersistentHashMap_isUnaryNode___rarg(x_39);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; 
lean_ctor_set(x_11, 0, x_39);
x_42 = lean_array_set(x_25, x_9, x_11);
lean_dec(x_9);
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_44 = 1;
x_45 = lean_box(x_44);
lean_ctor_set(x_27, 1, x_45);
lean_ctor_set(x_27, 0, x_43);
return x_27;
}
else
{
lean_object* x_46; uint8_t x_47; 
lean_free_object(x_27);
lean_dec(x_39);
lean_free_object(x_11);
x_46 = lean_ctor_get(x_41, 0);
lean_inc(x_46);
lean_dec(x_41);
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; 
x_48 = lean_ctor_get(x_46, 0);
x_49 = lean_ctor_get(x_46, 1);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_array_set(x_25, x_9, x_50);
lean_dec(x_9);
x_52 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_53 = 1;
x_54 = lean_box(x_53);
lean_ctor_set(x_46, 1, x_54);
lean_ctor_set(x_46, 0, x_52);
return x_46;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; 
x_55 = lean_ctor_get(x_46, 0);
x_56 = lean_ctor_get(x_46, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_46);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_array_set(x_25, x_9, x_57);
lean_dec(x_9);
x_59 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_59, 0, x_58);
x_60 = 1;
x_61 = lean_box(x_60);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_27, 0);
lean_inc(x_63);
lean_dec(x_27);
x_64 = l_Std_PersistentHashMap_isUnaryNode___rarg(x_63);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; 
lean_ctor_set(x_11, 0, x_63);
x_65 = lean_array_set(x_25, x_9, x_11);
lean_dec(x_9);
x_66 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_66, 0, x_65);
x_67 = 1;
x_68 = lean_box(x_67);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_66);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_63);
lean_free_object(x_11);
x_70 = lean_ctor_get(x_64, 0);
lean_inc(x_70);
lean_dec(x_64);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_73 = x_70;
} else {
 lean_dec_ref(x_70);
 x_73 = lean_box(0);
}
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_71);
lean_ctor_set(x_74, 1, x_72);
x_75 = lean_array_set(x_25, x_9, x_74);
lean_dec(x_9);
x_76 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_76, 0, x_75);
x_77 = 1;
x_78 = lean_box(x_77);
if (lean_is_scalar(x_73)) {
 x_79 = lean_alloc_ctor(0, 2, 0);
} else {
 x_79 = x_73;
}
lean_ctor_set(x_79, 0, x_76);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
}
else
{
lean_object* x_80; lean_object* x_81; size_t x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_80 = lean_ctor_get(x_11, 0);
lean_inc(x_80);
lean_dec(x_11);
x_81 = lean_array_set(x_3, x_9, x_10);
x_82 = x_4 >> x_6;
x_83 = l_Std_PersistentHashMap_eraseAux___rarg(x_1, x_80, x_82, x_5);
x_84 = lean_ctor_get(x_83, 1);
lean_inc(x_84);
x_85 = lean_unbox(x_84);
lean_dec(x_84);
if (x_85 == 0)
{
lean_object* x_86; uint8_t x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_81);
lean_dec(x_9);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_86 = x_83;
} else {
 lean_dec_ref(x_83);
 x_86 = lean_box(0);
}
x_87 = 0;
x_88 = lean_box(x_87);
if (lean_is_scalar(x_86)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_86;
}
lean_ctor_set(x_89, 0, x_2);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_2);
x_90 = lean_ctor_get(x_83, 0);
lean_inc(x_90);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_91 = x_83;
} else {
 lean_dec_ref(x_83);
 x_91 = lean_box(0);
}
x_92 = l_Std_PersistentHashMap_isUnaryNode___rarg(x_90);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; lean_object* x_97; lean_object* x_98; 
x_93 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_93, 0, x_90);
x_94 = lean_array_set(x_81, x_9, x_93);
lean_dec(x_9);
x_95 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_95, 0, x_94);
x_96 = 1;
x_97 = lean_box(x_96);
if (lean_is_scalar(x_91)) {
 x_98 = lean_alloc_ctor(0, 2, 0);
} else {
 x_98 = x_91;
}
lean_ctor_set(x_98, 0, x_95);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_91);
lean_dec(x_90);
x_99 = lean_ctor_get(x_92, 0);
lean_inc(x_99);
lean_dec(x_92);
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_102 = x_99;
} else {
 lean_dec_ref(x_99);
 x_102 = lean_box(0);
}
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_100);
lean_ctor_set(x_103, 1, x_101);
x_104 = lean_array_set(x_81, x_9, x_103);
lean_dec(x_9);
x_105 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_105, 0, x_104);
x_106 = 1;
x_107 = lean_box(x_106);
if (lean_is_scalar(x_102)) {
 x_108 = lean_alloc_ctor(0, 2, 0);
} else {
 x_108 = x_102;
}
lean_ctor_set(x_108, 0, x_105);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
}
}
default: 
{
uint8_t x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_109 = 0;
x_110 = lean_box(x_109);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_2);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
}
}
lean_object* l_Std_PersistentHashMap_eraseAux___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_inc(x_1);
x_5 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_eraseAux___rarg___lambda__1___boxed), 7, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_eraseAux___rarg___lambda__2___boxed), 5, 1);
lean_closure_set(x_6, 0, x_1);
x_7 = l_Std_PersistentHashMap_eraseAux_match__6___rarg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Std_PersistentHashMap_eraseAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_eraseAux___rarg___boxed), 4, 0);
return x_3;
}
}
lean_object* l_Std_PersistentHashMap_eraseAux___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; lean_object* x_9; 
x_8 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_9 = l_Std_PersistentHashMap_eraseAux___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_8, x_7);
return x_9;
}
}
lean_object* l_Std_PersistentHashMap_eraseAux___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; lean_object* x_7; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Std_PersistentHashMap_eraseAux___rarg___lambda__2(x_1, x_2, x_3, x_6, x_5);
return x_7;
}
}
lean_object* l_Std_PersistentHashMap_eraseAux___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Std_PersistentHashMap_eraseAux___rarg(x_1, x_2, x_5, x_4);
return x_6;
}
}
lean_object* l_Std_PersistentHashMap_erase_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_3(x_3, x_4, x_5, x_2);
return x_6;
}
}
lean_object* l_Std_PersistentHashMap_erase_match__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_erase_match__1___rarg), 3, 0);
return x_6;
}
}
lean_object* l_Std_PersistentHashMap_erase_match__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_PersistentHashMap_erase_match__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
lean_object* l_Std_PersistentHashMap_erase___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_8 = lean_apply_1(x_2, x_4);
x_9 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_10 = l_Std_PersistentHashMap_eraseAux___rarg(x_1, x_6, x_9, x_4);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
lean_ctor_set(x_3, 0, x_13);
return x_3;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_7, x_15);
lean_dec(x_7);
lean_ctor_set(x_3, 1, x_16);
lean_ctor_set(x_3, 0, x_14);
return x_3;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_17 = lean_ctor_get(x_3, 0);
x_18 = lean_ctor_get(x_3, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_3);
lean_inc(x_4);
x_19 = lean_apply_1(x_2, x_4);
x_20 = lean_unbox_usize(x_19);
lean_dec(x_19);
x_21 = l_Std_PersistentHashMap_eraseAux___rarg(x_1, x_17, x_20, x_4);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
x_23 = lean_unbox(x_22);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_18);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_21, 0);
lean_inc(x_26);
lean_dec(x_21);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_sub(x_18, x_27);
lean_dec(x_18);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
lean_object* l_Std_PersistentHashMap_erase(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_erase___rarg), 4, 0);
return x_3;
}
}
lean_object* l_Std_PersistentHashMap_foldlMAux_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_4, x_5, x_2);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_apply_4(x_3, x_7, x_8, lean_box(0), x_2);
return x_9;
}
}
}
lean_object* l_Std_PersistentHashMap_foldlMAux_match__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_foldlMAux_match__1___rarg), 4, 0);
return x_5;
}
}
lean_object* l_Std_PersistentHashMap_foldlMAux_traverse___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_add(x_1, x_7);
x_9 = l_Std_PersistentHashMap_foldlMAux_traverse___rarg(x_2, lean_box(0), x_3, x_4, x_5, lean_box(0), x_8, x_6);
return x_9;
}
}
lean_object* l_Std_PersistentHashMap_foldlMAux_traverse___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_get_size(x_4);
x_10 = lean_nat_dec_lt(x_7, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_apply_2(x_12, lean_box(0), x_8);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_array_fget(x_4, x_7);
x_15 = lean_array_fget(x_5, x_7);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
lean_inc(x_3);
x_17 = lean_apply_3(x_3, x_8, x_14, x_15);
x_18 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_foldlMAux_traverse___rarg___lambda__1___boxed), 6, 5);
lean_closure_set(x_18, 0, x_7);
lean_closure_set(x_18, 1, x_1);
lean_closure_set(x_18, 2, x_3);
lean_closure_set(x_18, 3, x_4);
lean_closure_set(x_18, 4, x_5);
x_19 = lean_apply_4(x_16, lean_box(0), lean_box(0), x_17, x_18);
return x_19;
}
}
}
lean_object* l_Std_PersistentHashMap_foldlMAux_traverse(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_foldlMAux_traverse___rarg), 8, 0);
return x_4;
}
}
lean_object* l_Std_PersistentHashMap_foldlMAux_traverse___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_PersistentHashMap_foldlMAux_traverse___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Std_PersistentHashMap_foldlMAux___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_9 = l_Std_PersistentHashMap_foldlMAux___rarg(x_2, lean_box(0), x_1, x_8, x_3);
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
lean_object* l_Std_PersistentHashMap_foldlMAux___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_foldlMAux___rarg___lambda__1), 4, 2);
lean_closure_set(x_7, 0, x_3);
lean_closure_set(x_7, 1, x_1);
x_8 = lean_array_get_size(x_6);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_foldlMUnsafe___rarg(x_1, x_7, x_5, x_6, x_9, x_8);
lean_dec(x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_4, 1);
lean_inc(x_12);
lean_dec(x_4);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Std_PersistentHashMap_foldlMAux_traverse___rarg(x_1, lean_box(0), x_3, x_11, x_12, lean_box(0), x_13, x_5);
return x_14;
}
}
}
lean_object* l_Std_PersistentHashMap_foldlMAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_foldlMAux___rarg), 5, 0);
return x_4;
}
}
lean_object* l_Std_PersistentHashMap_foldlM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec(x_5);
x_9 = l_Std_PersistentHashMap_foldlMAux___rarg(x_1, lean_box(0), x_6, x_8, x_7);
return x_9;
}
}
lean_object* l_Std_PersistentHashMap_foldlM(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_foldlM___rarg___boxed), 7, 0);
return x_4;
}
}
lean_object* l_Std_PersistentHashMap_foldlM___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_PersistentHashMap_foldlM___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
lean_object* l_Std_PersistentHashMap_forM___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_2(x_1, x_3, x_4);
return x_5;
}
}
lean_object* l_Std_PersistentHashMap_forM___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_forM___rarg___lambda__1___boxed), 4, 1);
lean_closure_set(x_6, 0, x_5);
x_7 = lean_box(0);
x_8 = l_Std_PersistentHashMap_foldlM___rarg(x_1, lean_box(0), x_2, x_3, x_4, x_6, x_7);
return x_8;
}
}
lean_object* l_Std_PersistentHashMap_forM(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_forM___rarg___boxed), 5, 0);
return x_4;
}
}
lean_object* l_Std_PersistentHashMap_forM___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_PersistentHashMap_forM___rarg___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Std_PersistentHashMap_forM___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_PersistentHashMap_forM___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Std_PersistentHashMap_foldl___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Id_instMonadId;
x_7 = l_Std_PersistentHashMap_foldlM___rarg(x_6, lean_box(0), x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
lean_object* l_Std_PersistentHashMap_foldl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_foldl___rarg___boxed), 5, 0);
return x_4;
}
}
lean_object* l_Std_PersistentHashMap_foldl___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_PersistentHashMap_foldl___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Std_PersistentHashMap_toList___spec__4___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = x_3 == x_4;
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_7 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_8 = lean_apply_2(x_1, x_5, x_7);
x_9 = 1;
x_10 = x_3 + x_9;
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
lean_object* l_Array_foldlMUnsafe_fold___at_Std_PersistentHashMap_toList___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Std_PersistentHashMap_toList___spec__4___rarg___boxed), 5, 0);
return x_3;
}
}
lean_object* l_Array_foldlMUnsafe___at_Std_PersistentHashMap_toList___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_4, x_5);
if (x_6 == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_3);
x_8 = lean_nat_dec_le(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_usize_of_nat(x_4);
x_10 = lean_usize_of_nat(x_5);
x_11 = l_Array_foldlMUnsafe_fold___at_Std_PersistentHashMap_toList___spec__4___rarg(x_1, x_3, x_9, x_10, x_2);
return x_11;
}
}
}
}
lean_object* l_Array_foldlMUnsafe___at_Std_PersistentHashMap_toList___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe___at_Std_PersistentHashMap_toList___spec__3___rarg___boxed), 5, 0);
return x_3;
}
}
lean_object* l_Std_PersistentHashMap_foldlMAux_traverse___at_Std_PersistentHashMap_toList___spec__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* l_Std_PersistentHashMap_foldlMAux_traverse___at_Std_PersistentHashMap_toList___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_foldlMAux_traverse___at_Std_PersistentHashMap_toList___spec__5___rarg___boxed), 6, 0);
return x_4;
}
}
lean_object* l_Std_PersistentHashMap_foldlMAux___at_Std_PersistentHashMap_toList___spec__2___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_inc(x_3);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_1);
return x_6;
}
case 1:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = l_Std_PersistentHashMap_foldlMAux___at_Std_PersistentHashMap_toList___spec__2___rarg(x_7, x_1);
return x_8;
}
default: 
{
return x_1;
}
}
}
}
lean_object* l_Std_PersistentHashMap_foldlMAux___at_Std_PersistentHashMap_toList___spec__2___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_1 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_foldlMAux___at_Std_PersistentHashMap_toList___spec__2___rarg___lambda__1___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Std_PersistentHashMap_foldlMAux___at_Std_PersistentHashMap_toList___spec__2___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_foldlMAux___at_Std_PersistentHashMap_toList___spec__2___rarg___lambda__2), 3, 0);
return x_1;
}
}
lean_object* l_Std_PersistentHashMap_foldlMAux___at_Std_PersistentHashMap_toList___spec__2___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_array_get_size(x_3);
x_5 = l_Std_PersistentHashMap_foldlMAux___at_Std_PersistentHashMap_toList___spec__2___rarg___closed__1;
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Array_foldlMUnsafe___at_Std_PersistentHashMap_toList___spec__3___rarg(x_5, x_2, x_3, x_6, x_4);
lean_dec(x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = l_Std_PersistentHashMap_foldlMAux___at_Std_PersistentHashMap_toList___spec__2___rarg___closed__2;
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Std_PersistentHashMap_foldlMAux_traverse___at_Std_PersistentHashMap_toList___spec__5___rarg(x_10, x_8, x_9, lean_box(0), x_11, x_2);
return x_12;
}
}
}
lean_object* l_Std_PersistentHashMap_foldlMAux___at_Std_PersistentHashMap_toList___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_foldlMAux___at_Std_PersistentHashMap_toList___spec__2___rarg___boxed), 2, 0);
return x_3;
}
}
lean_object* l_Std_PersistentHashMap_foldlM___at_Std_PersistentHashMap_toList___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = l_Std_PersistentHashMap_foldlMAux___at_Std_PersistentHashMap_toList___spec__2___rarg(x_3, x_2);
return x_4;
}
}
lean_object* l_Std_PersistentHashMap_foldlM___at_Std_PersistentHashMap_toList___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_foldlM___at_Std_PersistentHashMap_toList___spec__1___rarg___boxed), 2, 0);
return x_5;
}
}
lean_object* l_Std_PersistentHashMap_toList___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = l_Std_PersistentHashMap_foldlM___at_Std_PersistentHashMap_toList___spec__1___rarg(x_3, x_4);
return x_5;
}
}
lean_object* l_Std_PersistentHashMap_toList(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_toList___rarg___boxed), 3, 0);
return x_3;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Std_PersistentHashMap_toList___spec__4___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Std_PersistentHashMap_toList___spec__4___rarg(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Array_foldlMUnsafe___at_Std_PersistentHashMap_toList___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_foldlMUnsafe___at_Std_PersistentHashMap_toList___spec__3___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
lean_object* l_Std_PersistentHashMap_foldlMAux_traverse___at_Std_PersistentHashMap_toList___spec__5___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_PersistentHashMap_foldlMAux_traverse___at_Std_PersistentHashMap_toList___spec__5___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Std_PersistentHashMap_foldlMAux___at_Std_PersistentHashMap_toList___spec__2___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_PersistentHashMap_foldlMAux___at_Std_PersistentHashMap_toList___spec__2___rarg___lambda__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Std_PersistentHashMap_foldlMAux___at_Std_PersistentHashMap_toList___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_PersistentHashMap_foldlMAux___at_Std_PersistentHashMap_toList___spec__2___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Std_PersistentHashMap_foldlM___at_Std_PersistentHashMap_toList___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_PersistentHashMap_foldlM___at_Std_PersistentHashMap_toList___spec__1___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Std_PersistentHashMap_foldlM___at_Std_PersistentHashMap_toList___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_PersistentHashMap_foldlM___at_Std_PersistentHashMap_toList___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Std_PersistentHashMap_toList___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_PersistentHashMap_toList___rarg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
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
lean_object* l_Std_PersistentHashMap_collectStats_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_4);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_3(x_5, x_6, x_2, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_5);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_apply_5(x_4, x_8, x_9, lean_box(0), x_2, x_3);
return x_10;
}
}
}
lean_object* l_Std_PersistentHashMap_collectStats_match__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_collectStats_match__1___rarg), 5, 0);
return x_4;
}
}
lean_object* l_Std_PersistentHashMap_collectStats___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 0:
{
return x_2;
}
case 1:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_add(x_1, x_5);
x_7 = l_Std_PersistentHashMap_collectStats___rarg(x_4, x_2, x_6);
return x_7;
}
default: 
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_2);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_2, 1);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_9, x_10);
lean_dec(x_9);
lean_ctor_set(x_2, 1, x_11);
return x_2;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
x_14 = lean_ctor_get(x_2, 2);
x_15 = lean_ctor_get(x_2, 3);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_2);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_13, x_16);
lean_dec(x_13);
x_18 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set(x_18, 2, x_14);
lean_ctor_set(x_18, 3, x_15);
return x_18;
}
}
}
}
}
lean_object* l_Std_PersistentHashMap_collectStats___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
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
x_11 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_collectStats___rarg___lambda__1___boxed), 3, 1);
lean_closure_set(x_11, 0, x_3);
x_12 = lean_array_get_size(x_5);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Array_foldlMUnsafe___at_Array_foldl___spec__1___rarg(x_11, x_2, x_5, x_13, x_12);
lean_dec(x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_15 = lean_ctor_get(x_1, 0);
x_16 = lean_ctor_get(x_2, 0);
x_17 = lean_ctor_get(x_2, 1);
x_18 = lean_ctor_get(x_2, 2);
x_19 = lean_ctor_get(x_2, 3);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_2);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_16, x_20);
lean_dec(x_16);
x_22 = l_Nat_max(x_19, x_3);
lean_dec(x_19);
x_23 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_17);
lean_ctor_set(x_23, 2, x_18);
lean_ctor_set(x_23, 3, x_22);
x_24 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_collectStats___rarg___lambda__1___boxed), 3, 1);
lean_closure_set(x_24, 0, x_3);
x_25 = lean_array_get_size(x_15);
x_26 = lean_unsigned_to_nat(0u);
x_27 = l_Array_foldlMUnsafe___at_Array_foldl___spec__1___rarg(x_24, x_23, x_15, x_26, x_25);
lean_dec(x_25);
return x_27;
}
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_2);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_29 = lean_ctor_get(x_1, 0);
x_30 = lean_ctor_get(x_2, 0);
x_31 = lean_ctor_get(x_2, 2);
x_32 = lean_ctor_get(x_2, 3);
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_nat_add(x_30, x_33);
lean_dec(x_30);
x_35 = lean_array_get_size(x_29);
x_36 = lean_nat_add(x_31, x_35);
lean_dec(x_35);
lean_dec(x_31);
x_37 = lean_nat_sub(x_36, x_33);
lean_dec(x_36);
x_38 = l_Nat_max(x_32, x_3);
lean_dec(x_3);
lean_dec(x_32);
lean_ctor_set(x_2, 3, x_38);
lean_ctor_set(x_2, 2, x_37);
lean_ctor_set(x_2, 0, x_34);
return x_2;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_39 = lean_ctor_get(x_1, 0);
x_40 = lean_ctor_get(x_2, 0);
x_41 = lean_ctor_get(x_2, 1);
x_42 = lean_ctor_get(x_2, 2);
x_43 = lean_ctor_get(x_2, 3);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_2);
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_nat_add(x_40, x_44);
lean_dec(x_40);
x_46 = lean_array_get_size(x_39);
x_47 = lean_nat_add(x_42, x_46);
lean_dec(x_46);
lean_dec(x_42);
x_48 = lean_nat_sub(x_47, x_44);
lean_dec(x_47);
x_49 = l_Nat_max(x_43, x_3);
lean_dec(x_3);
lean_dec(x_43);
x_50 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_50, 0, x_45);
lean_ctor_set(x_50, 1, x_41);
lean_ctor_set(x_50, 2, x_48);
lean_ctor_set(x_50, 3, x_49);
return x_50;
}
}
}
}
lean_object* l_Std_PersistentHashMap_collectStats(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_collectStats___rarg___boxed), 3, 0);
return x_3;
}
}
lean_object* l_Std_PersistentHashMap_collectStats___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_PersistentHashMap_collectStats___rarg___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Std_PersistentHashMap_collectStats___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_PersistentHashMap_collectStats___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
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
lean_object* l_Std_PersistentHashMap_stats___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = l_Std_PersistentHashMap_stats___rarg___closed__1;
x_4 = lean_unsigned_to_nat(1u);
x_5 = l_Std_PersistentHashMap_collectStats___rarg(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Std_PersistentHashMap_stats(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_stats___rarg___boxed), 1, 0);
return x_5;
}
}
lean_object* l_Std_PersistentHashMap_stats___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_PersistentHashMap_stats___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Std_PersistentHashMap_stats___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l_Std_PersistentHashMap_Stats_toString(lean_object* x_1) {
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
x_21 = l_Std_Range_myMacro____x40_Init_Data_Range___hyg_276____closed__22;
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
lean_object* initialize_Std_Data_PersistentHashMap(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_PersistentHashMap_instInhabitedNode___closed__1 = _init_l_Std_PersistentHashMap_instInhabitedNode___closed__1();
lean_mark_persistent(l_Std_PersistentHashMap_instInhabitedNode___closed__1);
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
l_Std_PersistentHashMap_insertAux___rarg___boxed__const__1 = _init_l_Std_PersistentHashMap_insertAux___rarg___boxed__const__1();
lean_mark_persistent(l_Std_PersistentHashMap_insertAux___rarg___boxed__const__1);
l_Std_PersistentHashMap_insertAux___rarg___boxed__const__2 = _init_l_Std_PersistentHashMap_insertAux___rarg___boxed__const__2();
lean_mark_persistent(l_Std_PersistentHashMap_insertAux___rarg___boxed__const__2);
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
l_Std_PersistentHashMap_foldlMAux___at_Std_PersistentHashMap_toList___spec__2___rarg___closed__2 = _init_l_Std_PersistentHashMap_foldlMAux___at_Std_PersistentHashMap_toList___spec__2___rarg___closed__2();
lean_mark_persistent(l_Std_PersistentHashMap_foldlMAux___at_Std_PersistentHashMap_toList___spec__2___rarg___closed__2);
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
l_Std_PersistentHashMap_instToStringStats___closed__1 = _init_l_Std_PersistentHashMap_instToStringStats___closed__1();
lean_mark_persistent(l_Std_PersistentHashMap_instToStringStats___closed__1);
l_Std_PersistentHashMap_instToStringStats = _init_l_Std_PersistentHashMap_instToStringStats();
lean_mark_persistent(l_Std_PersistentHashMap_instToStringStats);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
