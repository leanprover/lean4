// Lean compiler output
// Module: Lean.Meta.Tactic.Ext
// Imports: Init.Data.Array.InsertionSort Lean.Meta.DiscrTree
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
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_reprPrec(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Ext_ExtTheorems_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_instReprExtTheorem;
uint8_t l_Lean_PersistentHashMap_contains___at_Lean_NameSSet_contains___spec__2(lean_object*, lean_object*);
static lean_object* l_Lean_PersistentHashMap_empty___at_Lean_Meta_Ext_instInhabitedExtTheorems___spec__1___closed__2;
static lean_object* l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__13;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__15(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_Ext_ExtTheorems_contains___spec__6___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Ext_getExtTheorems___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_isExtTheorem___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_reprKey____x40_Lean_Meta_DiscrTreeTypes___hyg_379_(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Ext_beqExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_129_(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertVal_loop___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_ExtTheorems_contains___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_Array_repr___at_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____spec__1___closed__1;
static lean_object* l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__11;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__14(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__14___boxed(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_extExtension;
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_isExtTheorem(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_repr___at_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_ExtTheorems_erase(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_insert___at_Lean_NameSSet_insert___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_instInhabited(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____closed__5;
static lean_object* l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_hashExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_219____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____spec__3(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_foldlMUnsafe_fold___at_Lean_Meta_Ext_ExtTheorems_contains___spec__5(lean_object*, lean_object*, size_t, size_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_ExtTheorems_erase___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_DiscrTree_Trie_foldValuesM___at_Lean_Meta_Ext_ExtTheorems_contains___spec__1(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_instInhabitedExtTheorem;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__3;
lean_object* l_Lean_PersistentHashMap_foldlMAux___at_Lean_MetavarContext_getExprAssignmentDomain___spec__3___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__9;
static lean_object* l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__14;
static lean_object* l_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____closed__8;
static lean_object* l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__7;
lean_object* l_Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_Ext_getExtTheorems___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_PersistentHashMap_isUnaryNode___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__15___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_reverse___rarg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_ExtTheorems_contains___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____closed__6;
lean_object* l_Lean_registerSimpleScopedEnvExtension___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
static lean_object* l_Array_Array_repr___at_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____spec__1___closed__10;
static lean_object* l_Array_Array_repr___at_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____spec__1___closed__3;
static lean_object* l_Lean_Meta_Ext_ExtTheorems_erase___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at_Lean_Meta_Ext_instInhabitedExtTheorems___spec__1;
static lean_object* l_Lean_Meta_Ext_getExtTheorems___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____lambda__1(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____closed__3;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__8;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_Ext_getExtTheorems___spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_instInhabitedExtTheorems;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_Ext_ExtTheorems_contains___spec__6(lean_object*, lean_object*, uint8_t);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Ext_instHashableExtTheorem___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_getExtTheorems(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__5(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__17;
lean_object* lean_array_to_list(lean_object*);
static lean_object* l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__12;
static lean_object* l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Ext_ExtTheorems_erase___rarg___closed__3;
uint8_t l_Lean_Meta_DiscrTree_Key_lt(lean_object*, lean_object*);
static lean_object* l_Lean_PersistentHashMap_empty___at_Lean_Meta_Ext_instInhabitedExtTheorems___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__6(lean_object*, size_t, size_t, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__6;
LEAN_EXPORT lean_object* l_Array_Array_repr___at_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____spec__1(lean_object*);
static lean_object* l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__4;
LEAN_EXPORT lean_object* l_panic___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__13(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_Ext_ExtTheorems_contains___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Ext_instInhabitedExtTheorem___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__2___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_ExtTheorems_erase___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Ext_ExtTheorems_erase___rarg___closed__2;
lean_object* l_Array_eraseIdx___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_beqExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_129____boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__9___closed__1;
LEAN_EXPORT lean_object* l_Array_isEqvAux___at_Lean_Meta_Ext_beqExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_129____spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
static lean_object* l_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____closed__2;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_Ext_hashExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_219____spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_Array_repr___at_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____spec__1___closed__2;
static lean_object* l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__15;
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_insertionSort_traverse___at_Lean_Meta_Ext_getExtTheorems___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__16;
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321_(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at_Lean_Meta_Ext_beqExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_129____spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____closed__9;
lean_object* l_Lean_throwError___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__2(lean_object*, lean_object*);
static lean_object* l_Array_Array_repr___at_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____spec__1___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_ExtTheorems_eraseCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_DiscrTree_instInhabitedKey;
static lean_object* l_Lean_Meta_Ext_instInhabitedExtTheorem___closed__2;
static lean_object* l_Lean_Meta_Ext_instBEqExtTheorem___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValuesM___at_Lean_Meta_Ext_ExtTheorems_contains___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Ext_ExtTheorems_contains___lambda__2(lean_object*, uint8_t, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Array_Array_repr___at_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____spec__1___closed__7;
static lean_object* l_Array_Array_repr___at_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____spec__1___closed__11;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__6___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_id___rarg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Ext_ExtTheorems_contains___lambda__1(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_Ext_ExtTheorems_contains___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_idxOfAux___at_Lean_MetavarContext_setMVarUserName___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Name_hash___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_ExtTheorems_erase___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__9___closed__2;
static lean_object* l_Array_Array_repr___at_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____spec__1___closed__4;
lean_object* lean_panic_fn(lean_object*, lean_object*);
static size_t l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__3___closed__2;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_getState___rarg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_Ext_ExtTheorems_contains___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lean_Meta_Ext_hashExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_219_(lean_object*);
static lean_object* l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__10;
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_instBEqExtTheorem;
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_Array_repr___at_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____spec__1___closed__9;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__7(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_ExtTheorems_contains___boxed(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_mk(lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__1___closed__3;
static lean_object* l_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____closed__7;
size_t lean_usize_add(size_t, size_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__1;
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____closed__4;
static lean_object* l_Lean_Meta_Ext_instReprExtTheorem___closed__1;
LEAN_EXPORT lean_object* l_Array_insertionSort_swapLoop___at_Lean_Meta_Ext_getExtTheorems___spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_foldlMUnsafe_fold___at_Lean_Meta_Ext_ExtTheorems_contains___spec__3(lean_object*, lean_object*, size_t, size_t, uint8_t);
size_t lean_usize_shift_left(size_t, size_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_125_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_Ext_ExtTheorems_contains___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_panic___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__13___closed__1;
static size_t l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__3___closed__1;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Array_foldlMUnsafe_fold___at_Lean_Meta_Ext_hashExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_219____spec__1(lean_object*, size_t, size_t, uint64_t);
static lean_object* l_Array_Array_repr___at_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____spec__1___closed__8;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__3(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_instHashableExtTheorem;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_getMatch___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_foldlMUnsafe_fold___at_Lean_Meta_Ext_ExtTheorems_contains___spec__4(lean_object*, lean_object*, size_t, size_t, uint8_t);
static lean_object* l_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____closed__1;
lean_object* l_Lean_MessageData_ofName(lean_object*);
static lean_object* l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__1___closed__4;
uint64_t l_Lean_Meta_DiscrTree_Key_hash(lean_object*);
static lean_object* l_Array_Array_repr___at_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____spec__1___closed__5;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Array_insertIdx_loop___rarg(lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_binInsertM___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_foldlMUnsafe_fold___at_Lean_Meta_Ext_ExtTheorems_contains___spec__2(lean_object*, lean_object*, size_t, size_t, uint8_t);
static lean_object* l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__18;
static lean_object* l_Lean_Meta_Ext_ExtTheorems_erase___rarg___closed__4;
uint8_t l_Array_isEmpty___rarg(lean_object*);
static lean_object* _init_l_Lean_Meta_Ext_instInhabitedExtTheorem___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Ext_instInhabitedExtTheorem___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Meta_Ext_instInhabitedExtTheorem___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Ext_instInhabitedExtTheorem() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Ext_instInhabitedExtTheorem___closed__2;
return x_1;
}
}
LEAN_EXPORT lean_object* l_repr___at_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Meta_DiscrTree_reprKey____x40_Lean_Meta_DiscrTreeTypes___hyg_379_(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_1);
lean_ctor_set_tag(x_3, 5);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 0, x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Lean_Meta_DiscrTree_reprKey____x40_Lean_Meta_DiscrTreeTypes___hyg_379_(x_5, x_7);
x_9 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_8);
x_2 = x_9;
x_3 = x_6;
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
lean_inc(x_1);
x_13 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_13, 0, x_2);
lean_ctor_set(x_13, 1, x_1);
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Lean_Meta_DiscrTree_reprKey____x40_Lean_Meta_DiscrTreeTypes___hyg_379_(x_11, x_14);
x_16 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
x_2 = x_16;
x_3 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
lean_dec(x_2);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Lean_Meta_DiscrTree_reprKey____x40_Lean_Meta_DiscrTreeTypes___hyg_379_(x_5, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Lean_Meta_DiscrTree_reprKey____x40_Lean_Meta_DiscrTreeTypes___hyg_379_(x_8, x_9);
x_11 = l_List_foldl___at_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____spec__4(x_2, x_10, x_4);
return x_11;
}
}
}
}
static lean_object* _init_l_Array_Array_repr___at_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(",", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Array_Array_repr___at_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_Array_repr___at_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____spec__1___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_Array_repr___at_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_Array_repr___at_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____spec__1___closed__2;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_Array_repr___at_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____spec__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("#[", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Array_Array_repr___at_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____spec__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_Array_repr___at_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____spec__1___closed__4;
x_2 = lean_string_length(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_Array_repr___at_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____spec__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_Array_repr___at_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____spec__1___closed__5;
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_Array_repr___at_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____spec__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_Array_repr___at_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____spec__1___closed__4;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_Array_repr___at_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____spec__1___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("]", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Array_Array_repr___at_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____spec__1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_Array_repr___at_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____spec__1___closed__8;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Array_Array_repr___at_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____spec__1___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("#[]", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Array_Array_repr___at_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____spec__1___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_Array_repr___at_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____spec__1___closed__10;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_Array_repr___at_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
lean_dec(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_5 = lean_array_to_list(x_1);
x_6 = l_Array_Array_repr___at_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____spec__1___closed__3;
x_7 = l_Std_Format_joinSep___at_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____spec__3(x_5, x_6);
x_8 = l_Array_Array_repr___at_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____spec__1___closed__7;
x_9 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
x_10 = l_Array_Array_repr___at_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____spec__1___closed__9;
x_11 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Array_Array_repr___at_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____spec__1___closed__6;
x_13 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = 1;
x_15 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set_uint8(x_15, sizeof(void*)*1, x_14);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_1);
x_16 = l_Array_Array_repr___at_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____spec__1___closed__11;
return x_16;
}
}
}
static lean_object* _init_l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("declName", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__2;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" := ", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__4;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__3;
x_2 = l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__5;
x_3 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(12u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("priority", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__8;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("keys", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__10;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("{ ", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__13;
x_2 = lean_string_length(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__14;
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__13;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" }", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__17;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_Name_reprPrec(x_3, x_4);
x_6 = l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__7;
x_7 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
x_8 = 0;
x_9 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_8);
x_10 = l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__6;
x_11 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
x_12 = l_Array_Array_repr___at_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____spec__1___closed__2;
x_13 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_box(1);
x_15 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__9;
x_17 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__5;
x_19 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
x_21 = l_Nat_reprFast(x_20);
x_22 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_23, 0, x_6);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set_uint8(x_24, sizeof(void*)*1, x_8);
x_25 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_25, 0, x_19);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_12);
x_27 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_14);
x_28 = l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__11;
x_29 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_18);
x_31 = lean_ctor_get(x_1, 2);
lean_inc(x_31);
lean_dec(x_1);
x_32 = l_Array_Array_repr___at_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____spec__1(x_31);
x_33 = l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__12;
x_34 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
x_35 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_8);
x_36 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_36, 0, x_30);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__16;
x_38 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
x_39 = l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__18;
x_40 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__15;
x_42 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
x_43 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set_uint8(x_43, sizeof(void*)*1, x_8);
return x_43;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51_(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Ext_instReprExtTheorem___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Ext_instReprExtTheorem() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Ext_instReprExtTheorem___closed__1;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at_Lean_Meta_Ext_beqExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_129____spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_6, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_6, x_10);
lean_dec(x_6);
x_12 = lean_array_fget(x_4, x_11);
x_13 = lean_array_fget(x_5, x_11);
x_14 = l_Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_125_(x_12, x_13);
lean_dec(x_13);
lean_dec(x_12);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_11);
x_15 = 0;
return x_15;
}
else
{
x_3 = lean_box(0);
x_6 = x_11;
x_7 = lean_box(0);
goto _start;
}
}
else
{
uint8_t x_17; 
lean_dec(x_6);
x_17 = 1;
return x_17;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Ext_beqExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_129_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get(x_2, 2);
x_9 = lean_name_eq(x_3, x_6);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = 0;
return x_10;
}
else
{
uint8_t x_11; 
x_11 = lean_nat_dec_eq(x_4, x_7);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = 0;
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_array_get_size(x_5);
x_14 = lean_array_get_size(x_8);
x_15 = lean_nat_dec_eq(x_13, x_14);
lean_dec(x_14);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_13);
x_16 = 0;
return x_16;
}
else
{
uint8_t x_17; 
x_17 = l_Array_isEqvAux___at_Lean_Meta_Ext_beqExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_129____spec__1(x_5, x_8, lean_box(0), x_5, x_8, x_13, lean_box(0));
return x_17;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at_Lean_Meta_Ext_beqExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_129____spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = l_Array_isEqvAux___at_Lean_Meta_Ext_beqExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_129____spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_beqExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_129____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_Ext_beqExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_129_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Ext_instBEqExtTheorem___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Ext_beqExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_129____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Ext_instBEqExtTheorem() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Ext_instBEqExtTheorem___closed__1;
return x_1;
}
}
LEAN_EXPORT uint64_t l_Array_foldlMUnsafe_fold___at_Lean_Meta_Ext_hashExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_219____spec__1(lean_object* x_1, size_t x_2, size_t x_3, uint64_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; uint64_t x_7; uint64_t x_8; size_t x_9; size_t x_10; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Lean_Meta_DiscrTree_Key_hash(x_6);
lean_dec(x_6);
x_8 = lean_uint64_mix_hash(x_4, x_7);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_2 = x_10;
x_4 = x_8;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT uint64_t l_Lean_Meta_Ext_hashExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_219_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint64_t x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
x_5 = 0;
x_6 = l_Lean_Name_hash___override(x_2);
x_7 = lean_uint64_mix_hash(x_5, x_6);
x_8 = lean_uint64_of_nat(x_3);
x_9 = lean_uint64_mix_hash(x_7, x_8);
x_10 = 7;
x_11 = lean_array_get_size(x_4);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_lt(x_12, x_11);
if (x_13 == 0)
{
uint64_t x_14; 
lean_dec(x_11);
x_14 = lean_uint64_mix_hash(x_9, x_10);
return x_14;
}
else
{
uint8_t x_15; 
x_15 = lean_nat_dec_le(x_11, x_11);
if (x_15 == 0)
{
uint64_t x_16; 
lean_dec(x_11);
x_16 = lean_uint64_mix_hash(x_9, x_10);
return x_16;
}
else
{
size_t x_17; size_t x_18; uint64_t x_19; uint64_t x_20; 
x_17 = 0;
x_18 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_19 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_Ext_hashExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_219____spec__1(x_4, x_17, x_18, x_10);
x_20 = lean_uint64_mix_hash(x_9, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_Ext_hashExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_219____spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint64_t x_7; uint64_t x_8; lean_object* x_9; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_uint64(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_Ext_hashExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_219____spec__1(x_1, x_5, x_6, x_7);
lean_dec(x_1);
x_9 = lean_box_uint64(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_hashExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_219____boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Ext_hashExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_219_(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Ext_instHashableExtTheorem___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Ext_hashExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_219____boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Ext_instHashableExtTheorem() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Ext_instHashableExtTheorem___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at_Lean_Meta_Ext_instInhabitedExtTheorems___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at_Lean_Meta_Ext_instInhabitedExtTheorems___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PersistentHashMap_empty___at_Lean_Meta_Ext_instInhabitedExtTheorems___spec__1___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at_Lean_Meta_Ext_instInhabitedExtTheorems___spec__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_empty___at_Lean_Meta_Ext_instInhabitedExtTheorems___spec__1___closed__2;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Ext_instInhabitedExtTheorems() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PersistentHashMap_empty___at_Lean_Meta_Ext_instInhabitedExtTheorems___spec__1___closed__2;
x_2 = l_Lean_PersistentHashMap_empty___at_Lean_Meta_Ext_instInhabitedExtTheorems___spec__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_4);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_fget(x_1, x_4);
x_10 = l_Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_125_(x_5, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
x_3 = lean_box(0);
x_4 = x_12;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_fget(x_2, x_4);
lean_dec(x_4);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__3___closed__1() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = 5;
x_3 = lean_usize_shift_left(x_1, x_2);
return x_3;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__3___closed__2() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__3___closed__1;
x_3 = lean_usize_sub(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__3(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; size_t x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = 5;
x_7 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__3___closed__2;
x_8 = lean_usize_land(x_2, x_7);
x_9 = lean_usize_to_nat(x_8);
x_10 = lean_box(2);
x_11 = lean_array_get(x_10, x_5, x_9);
lean_dec(x_9);
lean_dec(x_5);
switch (lean_obj_tag(x_11)) {
case 0:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_125_(x_3, x_12);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_13);
lean_free_object(x_1);
x_15 = lean_box(0);
return x_15;
}
else
{
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 0, x_13);
return x_1;
}
}
case 1:
{
lean_object* x_16; size_t x_17; 
lean_free_object(x_1);
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_usize_shift_right(x_2, x_6);
x_1 = x_16;
x_2 = x_17;
goto _start;
}
default: 
{
lean_object* x_19; 
lean_free_object(x_1);
x_19 = lean_box(0);
return x_19;
}
}
}
else
{
lean_object* x_20; size_t x_21; size_t x_22; size_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
lean_dec(x_1);
x_21 = 5;
x_22 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__3___closed__2;
x_23 = lean_usize_land(x_2, x_22);
x_24 = lean_usize_to_nat(x_23);
x_25 = lean_box(2);
x_26 = lean_array_get(x_25, x_20, x_24);
lean_dec(x_24);
lean_dec(x_20);
switch (lean_obj_tag(x_26)) {
case 0:
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_125_(x_3, x_27);
lean_dec(x_27);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_28);
x_30 = lean_box(0);
return x_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_28);
return x_31;
}
}
case 1:
{
lean_object* x_32; size_t x_33; 
x_32 = lean_ctor_get(x_26, 0);
lean_inc(x_32);
lean_dec(x_26);
x_33 = lean_usize_shift_right(x_2, x_21);
x_1 = x_32;
x_2 = x_33;
goto _start;
}
default: 
{
lean_object* x_35; 
x_35 = lean_box(0);
return x_35;
}
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_1, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_1, 1);
lean_inc(x_37);
lean_dec(x_1);
x_38 = lean_unsigned_to_nat(0u);
x_39 = l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__4(x_36, x_37, lean_box(0), x_38, x_3);
lean_dec(x_37);
lean_dec(x_36);
return x_39;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; size_t x_4; lean_object* x_5; 
x_3 = l_Lean_Meta_DiscrTree_Key_hash(x_2);
x_4 = lean_uint64_to_usize(x_3);
x_5 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__3(x_1, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__7(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_dec(x_5);
return x_6;
}
else
{
lean_object* x_9; lean_object* x_10; uint64_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_9 = lean_array_fget(x_2, x_5);
x_10 = lean_array_fget(x_3, x_5);
x_11 = l_Lean_Meta_DiscrTree_Key_hash(x_9);
x_12 = lean_uint64_to_usize(x_11);
x_13 = 1;
x_14 = lean_usize_sub(x_1, x_13);
x_15 = 5;
x_16 = lean_usize_mul(x_15, x_14);
x_17 = lean_usize_shift_right(x_12, x_16);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_5, x_18);
lean_dec(x_5);
x_20 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__6(x_6, x_17, x_1, x_9, x_10);
x_4 = lean_box(0);
x_5 = x_19;
x_6 = x_20;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_array_get_size(x_5);
x_8 = lean_nat_dec_lt(x_2, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_2);
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_1, 1);
lean_dec(x_10);
x_11 = lean_ctor_get(x_1, 0);
lean_dec(x_11);
x_12 = lean_array_push(x_5, x_3);
x_13 = lean_array_push(x_6, x_4);
lean_ctor_set(x_1, 1, x_13);
lean_ctor_set(x_1, 0, x_12);
return x_1;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_1);
x_14 = lean_array_push(x_5, x_3);
x_15 = lean_array_push(x_6, x_4);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_array_fget(x_5, x_2);
x_18 = l_Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_125_(x_3, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_6);
lean_dec(x_5);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_2, x_19);
lean_dec(x_2);
x_2 = x_20;
goto _start;
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_1);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_1, 1);
lean_dec(x_23);
x_24 = lean_ctor_get(x_1, 0);
lean_dec(x_24);
x_25 = lean_array_fset(x_5, x_2, x_3);
x_26 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
lean_ctor_set(x_1, 1, x_26);
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_1);
x_27 = lean_array_fset(x_5, x_2, x_3);
x_28 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__6___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__6(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; size_t x_8; size_t x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = 1;
x_9 = 5;
x_10 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__3___closed__2;
x_11 = lean_usize_land(x_2, x_10);
x_12 = lean_usize_to_nat(x_11);
x_13 = lean_array_get_size(x_7);
x_14 = lean_nat_dec_lt(x_12, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
return x_1;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_array_fget(x_7, x_12);
x_16 = lean_box(0);
x_17 = lean_array_fset(x_7, x_12, x_16);
switch (lean_obj_tag(x_15)) {
case 0:
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
x_21 = l_Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_125_(x_4, x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_free_object(x_15);
x_22 = l_Lean_PersistentHashMap_mkCollisionNode___rarg(x_19, x_20, x_4, x_5);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_array_fset(x_17, x_12, x_23);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_24);
return x_1;
}
else
{
lean_object* x_25; 
lean_dec(x_20);
lean_dec(x_19);
lean_ctor_set(x_15, 1, x_5);
lean_ctor_set(x_15, 0, x_4);
x_25 = lean_array_fset(x_17, x_12, x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_15, 0);
x_27 = lean_ctor_get(x_15, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_15);
x_28 = l_Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_125_(x_4, x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = l_Lean_PersistentHashMap_mkCollisionNode___rarg(x_26, x_27, x_4, x_5);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_array_fset(x_17, x_12, x_30);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_31);
return x_1;
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_27);
lean_dec(x_26);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_4);
lean_ctor_set(x_32, 1, x_5);
x_33 = lean_array_fset(x_17, x_12, x_32);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_33);
return x_1;
}
}
}
case 1:
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_15);
if (x_34 == 0)
{
lean_object* x_35; size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_15, 0);
x_36 = lean_usize_shift_right(x_2, x_9);
x_37 = lean_usize_add(x_3, x_8);
x_38 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__6(x_35, x_36, x_37, x_4, x_5);
lean_ctor_set(x_15, 0, x_38);
x_39 = lean_array_fset(x_17, x_12, x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_39);
return x_1;
}
else
{
lean_object* x_40; size_t x_41; size_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_15, 0);
lean_inc(x_40);
lean_dec(x_15);
x_41 = lean_usize_shift_right(x_2, x_9);
x_42 = lean_usize_add(x_3, x_8);
x_43 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__6(x_40, x_41, x_42, x_4, x_5);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_45 = lean_array_fset(x_17, x_12, x_44);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_45);
return x_1;
}
}
default: 
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_4);
lean_ctor_set(x_46, 1, x_5);
x_47 = lean_array_fset(x_17, x_12, x_46);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_47);
return x_1;
}
}
}
}
else
{
lean_object* x_48; size_t x_49; size_t x_50; size_t x_51; size_t x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_48 = lean_ctor_get(x_1, 0);
lean_inc(x_48);
lean_dec(x_1);
x_49 = 1;
x_50 = 5;
x_51 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__3___closed__2;
x_52 = lean_usize_land(x_2, x_51);
x_53 = lean_usize_to_nat(x_52);
x_54 = lean_array_get_size(x_48);
x_55 = lean_nat_dec_lt(x_53, x_54);
lean_dec(x_54);
if (x_55 == 0)
{
lean_object* x_56; 
lean_dec(x_53);
lean_dec(x_5);
lean_dec(x_4);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_48);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_array_fget(x_48, x_53);
x_58 = lean_box(0);
x_59 = lean_array_fset(x_48, x_53, x_58);
switch (lean_obj_tag(x_57)) {
case 0:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_60 = lean_ctor_get(x_57, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_57, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_62 = x_57;
} else {
 lean_dec_ref(x_57);
 x_62 = lean_box(0);
}
x_63 = l_Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_125_(x_4, x_60);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_62);
x_64 = l_Lean_PersistentHashMap_mkCollisionNode___rarg(x_60, x_61, x_4, x_5);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_64);
x_66 = lean_array_fset(x_59, x_53, x_65);
lean_dec(x_53);
x_67 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_67, 0, x_66);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_61);
lean_dec(x_60);
if (lean_is_scalar(x_62)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_62;
}
lean_ctor_set(x_68, 0, x_4);
lean_ctor_set(x_68, 1, x_5);
x_69 = lean_array_fset(x_59, x_53, x_68);
lean_dec(x_53);
x_70 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_70, 0, x_69);
return x_70;
}
}
case 1:
{
lean_object* x_71; lean_object* x_72; size_t x_73; size_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_71 = lean_ctor_get(x_57, 0);
lean_inc(x_71);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 x_72 = x_57;
} else {
 lean_dec_ref(x_57);
 x_72 = lean_box(0);
}
x_73 = lean_usize_shift_right(x_2, x_50);
x_74 = lean_usize_add(x_3, x_49);
x_75 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__6(x_71, x_73, x_74, x_4, x_5);
if (lean_is_scalar(x_72)) {
 x_76 = lean_alloc_ctor(1, 1, 0);
} else {
 x_76 = x_72;
}
lean_ctor_set(x_76, 0, x_75);
x_77 = lean_array_fset(x_59, x_53, x_76);
lean_dec(x_53);
x_78 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_78, 0, x_77);
return x_78;
}
default: 
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_4);
lean_ctor_set(x_79, 1, x_5);
x_80 = lean_array_fset(x_59, x_53, x_79);
lean_dec(x_53);
x_81 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_81, 0, x_80);
return x_81;
}
}
}
}
}
else
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_1);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; size_t x_85; uint8_t x_86; 
x_83 = lean_unsigned_to_nat(0u);
x_84 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__8(x_1, x_83, x_4, x_5);
x_85 = 7;
x_86 = lean_usize_dec_le(x_85, x_3);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_87 = l_Lean_PersistentHashMap_getCollisionNodeSize___rarg(x_84);
x_88 = lean_unsigned_to_nat(4u);
x_89 = lean_nat_dec_lt(x_87, x_88);
lean_dec(x_87);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_90 = lean_ctor_get(x_84, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_84, 1);
lean_inc(x_91);
lean_dec(x_84);
x_92 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__6___closed__1;
x_93 = l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__7(x_3, x_90, x_91, lean_box(0), x_83, x_92);
lean_dec(x_91);
lean_dec(x_90);
return x_93;
}
else
{
return x_84;
}
}
else
{
return x_84;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; size_t x_99; uint8_t x_100; 
x_94 = lean_ctor_get(x_1, 0);
x_95 = lean_ctor_get(x_1, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_1);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
x_97 = lean_unsigned_to_nat(0u);
x_98 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__8(x_96, x_97, x_4, x_5);
x_99 = 7;
x_100 = lean_usize_dec_le(x_99, x_3);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_101 = l_Lean_PersistentHashMap_getCollisionNodeSize___rarg(x_98);
x_102 = lean_unsigned_to_nat(4u);
x_103 = lean_nat_dec_lt(x_101, x_102);
lean_dec(x_101);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_104 = lean_ctor_get(x_98, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_98, 1);
lean_inc(x_105);
lean_dec(x_98);
x_106 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__6___closed__1;
x_107 = l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__7(x_3, x_104, x_105, lean_box(0), x_97, x_106);
lean_dec(x_105);
lean_dec(x_104);
return x_107;
}
else
{
return x_98;
}
}
else
{
return x_98;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; size_t x_5; size_t x_6; lean_object* x_7; 
x_4 = l_Lean_Meta_DiscrTree_Key_hash(x_2);
x_5 = lean_uint64_to_usize(x_4);
x_6 = 1;
x_7 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__6(x_1, x_5, x_6, x_2, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertVal_loop___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_3);
x_6 = lean_array_push(x_1, x_2);
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_fget(x_1, x_3);
x_8 = l_Lean_Meta_Ext_beqExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_129_(x_2, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_3, x_9);
lean_dec(x_3);
x_3 = x_10;
goto _start;
}
else
{
lean_object* x_12; 
x_12 = lean_array_fset(x_1, x_3, x_2);
lean_dec(x_3);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_11 = lean_nat_add(x_7, x_8);
x_12 = lean_unsigned_to_nat(2u);
x_13 = lean_nat_div(x_11, x_12);
lean_dec(x_11);
x_14 = lean_array_fget(x_5, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_6, 0);
x_17 = l_Lean_Meta_DiscrTree_Key_lt(x_15, x_16);
if (x_17 == 0)
{
uint8_t x_18; 
lean_dec(x_8);
x_18 = l_Lean_Meta_DiscrTree_Key_lt(x_16, x_15);
lean_dec(x_15);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
lean_dec(x_7);
x_19 = lean_array_get_size(x_5);
x_20 = lean_nat_dec_lt(x_13, x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_2);
return x_5;
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_box(0);
x_22 = lean_array_fset(x_5, x_13, x_21);
x_23 = !lean_is_exclusive(x_14);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_14, 1);
x_25 = lean_ctor_get(x_14, 0);
lean_dec(x_25);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_3, x_26);
x_28 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__9(x_1, x_2, x_27, x_24);
lean_dec(x_27);
lean_ctor_set(x_14, 1, x_28);
lean_ctor_set(x_14, 0, x_4);
x_29 = lean_array_fset(x_22, x_13, x_14);
lean_dec(x_13);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_30 = lean_ctor_get(x_14, 1);
lean_inc(x_30);
lean_dec(x_14);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_add(x_3, x_31);
x_33 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__9(x_1, x_2, x_32, x_30);
lean_dec(x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_4);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_array_fset(x_22, x_13, x_34);
lean_dec(x_13);
return x_35;
}
}
}
else
{
lean_dec(x_14);
x_8 = x_13;
x_9 = lean_box(0);
x_10 = lean_box(0);
goto _start;
}
}
else
{
uint8_t x_37; 
lean_dec(x_15);
lean_dec(x_14);
x_37 = lean_nat_dec_eq(x_13, x_7);
if (x_37 == 0)
{
lean_dec(x_7);
x_7 = x_13;
x_9 = lean_box(0);
x_10 = lean_box(0);
goto _start;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_13);
lean_dec(x_8);
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_nat_add(x_3, x_39);
x_41 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___rarg(x_1, x_2, x_40);
lean_dec(x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_4);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_nat_add(x_7, x_39);
lean_dec(x_7);
x_44 = lean_array_get_size(x_5);
x_45 = lean_array_push(x_5, x_42);
x_46 = l_Array_insertIdx_loop___rarg(x_43, x_45, x_44);
lean_dec(x_43);
return x_46;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_array_get_size(x_5);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_array_fget(x_5, x_8);
x_11 = lean_ctor_get(x_6, 0);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
x_13 = l_Lean_Meta_DiscrTree_Key_lt(x_11, x_12);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = l_Lean_Meta_DiscrTree_Key_lt(x_12, x_11);
lean_dec(x_12);
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = lean_nat_dec_lt(x_8, x_7);
lean_dec(x_7);
if (x_15 == 0)
{
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_2);
return x_5;
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_box(0);
x_17 = lean_array_fset(x_5, x_8, x_16);
x_18 = !lean_is_exclusive(x_10);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_10, 1);
x_20 = lean_ctor_get(x_10, 0);
lean_dec(x_20);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_3, x_21);
x_23 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__9(x_1, x_2, x_22, x_19);
lean_dec(x_22);
lean_ctor_set(x_10, 1, x_23);
lean_ctor_set(x_10, 0, x_4);
x_24 = lean_array_fset(x_17, x_8, x_10);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_10, 1);
lean_inc(x_25);
lean_dec(x_10);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_3, x_26);
x_28 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__9(x_1, x_2, x_27, x_25);
lean_dec(x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_4);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_array_fset(x_17, x_8, x_29);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
lean_dec(x_10);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_sub(x_7, x_31);
x_33 = lean_array_fget(x_5, x_32);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = l_Lean_Meta_DiscrTree_Key_lt(x_34, x_11);
if (x_35 == 0)
{
uint8_t x_36; 
x_36 = l_Lean_Meta_DiscrTree_Key_lt(x_11, x_34);
lean_dec(x_34);
if (x_36 == 0)
{
uint8_t x_37; 
x_37 = lean_nat_dec_lt(x_32, x_7);
lean_dec(x_7);
if (x_37 == 0)
{
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_4);
lean_dec(x_2);
return x_5;
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_box(0);
x_39 = lean_array_fset(x_5, x_32, x_38);
x_40 = !lean_is_exclusive(x_33);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_41 = lean_ctor_get(x_33, 1);
x_42 = lean_ctor_get(x_33, 0);
lean_dec(x_42);
x_43 = lean_nat_add(x_3, x_31);
x_44 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__9(x_1, x_2, x_43, x_41);
lean_dec(x_43);
lean_ctor_set(x_33, 1, x_44);
lean_ctor_set(x_33, 0, x_4);
x_45 = lean_array_fset(x_39, x_32, x_33);
lean_dec(x_32);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_46 = lean_ctor_get(x_33, 1);
lean_inc(x_46);
lean_dec(x_33);
x_47 = lean_nat_add(x_3, x_31);
x_48 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__9(x_1, x_2, x_47, x_46);
lean_dec(x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_4);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_array_fset(x_39, x_32, x_49);
lean_dec(x_32);
return x_50;
}
}
}
else
{
lean_object* x_51; 
lean_dec(x_33);
lean_dec(x_7);
x_51 = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__12(x_1, x_2, x_3, x_4, x_5, x_6, x_8, x_32, lean_box(0), lean_box(0));
return x_51;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_7);
x_52 = lean_nat_add(x_3, x_31);
x_53 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___rarg(x_1, x_2, x_52);
lean_dec(x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_4);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_array_push(x_5, x_54);
return x_55;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_12);
lean_dec(x_10);
x_56 = lean_unsigned_to_nat(1u);
x_57 = lean_nat_add(x_3, x_56);
x_58 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___rarg(x_1, x_2, x_57);
lean_dec(x_57);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_4);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_array_push(x_5, x_59);
x_61 = l_Array_insertIdx_loop___rarg(x_8, x_60, x_7);
return x_61;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_7);
x_62 = lean_unsigned_to_nat(1u);
x_63 = lean_nat_add(x_3, x_62);
x_64 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___rarg(x_1, x_2, x_63);
lean_dec(x_63);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_4);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_array_push(x_5, x_65);
return x_66;
}
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__9___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__9___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__9___closed__1;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_array_get_size(x_1);
x_9 = lean_nat_dec_lt(x_3, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertVal_loop___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__10(x_6, x_2, x_10);
lean_ctor_set(x_4, 0, x_11);
return x_4;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_array_fget(x_1, x_3);
x_13 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__9___closed__2;
lean_inc(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Array_binInsertM___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__11(x_1, x_2, x_3, x_12, x_7, x_14);
lean_dec(x_14);
lean_ctor_set(x_4, 1, x_15);
return x_4;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_4, 0);
x_17 = lean_ctor_get(x_4, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_4);
x_18 = lean_array_get_size(x_1);
x_19 = lean_nat_dec_lt(x_3, x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_unsigned_to_nat(0u);
x_21 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertVal_loop___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__10(x_16, x_2, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_17);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_array_fget(x_1, x_3);
x_24 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__9___closed__2;
lean_inc(x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Array_binInsertM___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__11(x_1, x_2, x_3, x_23, x_17, x_25);
lean_dec(x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_16);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
static lean_object* _init_l_panic___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__13___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_DiscrTree_instInhabited(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__13(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_panic___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__13___closed__1;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.DiscrTree", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.DiscrTree.insertCore", 30, 30);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid key sequence", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__1___closed__1;
x_2 = l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__1___closed__2;
x_3 = lean_unsigned_to_nat(482u);
x_4 = lean_unsigned_to_nat(23u);
x_5 = l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__1___closed__3;
x_6 = l_mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Array_isEmpty___rarg(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = l_Lean_Meta_DiscrTree_instInhabitedKey;
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_get(x_5, x_2, x_6);
lean_inc(x_1);
x_8 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__2(x_1, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___rarg(x_2, x_3, x_9);
x_11 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__5(x_1, x_7, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
x_13 = lean_unsigned_to_nat(1u);
x_14 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__9(x_2, x_3, x_13, x_12);
x_15 = l_Lean_PersistentHashMap_insert___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__5(x_1, x_7, x_14);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_3);
lean_dec(x_1);
x_16 = l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__1___closed__4;
x_17 = l_panic___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__13(x_16);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__15(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = 5;
x_6 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__3___closed__2;
x_7 = lean_usize_land(x_2, x_6);
x_8 = lean_usize_to_nat(x_7);
x_9 = lean_box(2);
x_10 = lean_array_get(x_9, x_4, x_8);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_name_eq(x_3, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_dec(x_8);
lean_dec(x_4);
return x_1;
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_1, 0);
lean_dec(x_14);
x_15 = lean_array_set(x_4, x_8, x_9);
lean_dec(x_8);
lean_ctor_set(x_1, 0, x_15);
return x_1;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_1);
x_16 = lean_array_set(x_4, x_8, x_9);
lean_dec(x_8);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
}
case 1:
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_1);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_1, 0);
lean_dec(x_19);
x_20 = !lean_is_exclusive(x_10);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; size_t x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_10, 0);
x_22 = lean_array_set(x_4, x_8, x_9);
x_23 = lean_usize_shift_right(x_2, x_5);
x_24 = l_Lean_PersistentHashMap_eraseAux___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__15(x_21, x_23, x_3);
lean_inc(x_24);
x_25 = l_Lean_PersistentHashMap_isUnaryNode___rarg(x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
lean_ctor_set(x_10, 0, x_24);
x_26 = lean_array_set(x_22, x_8, x_10);
lean_dec(x_8);
lean_ctor_set(x_1, 0, x_26);
return x_1;
}
else
{
lean_object* x_27; uint8_t x_28; 
lean_dec(x_24);
lean_free_object(x_10);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
lean_dec(x_25);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_array_set(x_22, x_8, x_27);
lean_dec(x_8);
lean_ctor_set(x_1, 0, x_29);
return x_1;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_27, 0);
x_31 = lean_ctor_get(x_27, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_27);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_array_set(x_22, x_8, x_32);
lean_dec(x_8);
lean_ctor_set(x_1, 0, x_33);
return x_1;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; size_t x_36; lean_object* x_37; lean_object* x_38; 
x_34 = lean_ctor_get(x_10, 0);
lean_inc(x_34);
lean_dec(x_10);
x_35 = lean_array_set(x_4, x_8, x_9);
x_36 = lean_usize_shift_right(x_2, x_5);
x_37 = l_Lean_PersistentHashMap_eraseAux___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__15(x_34, x_36, x_3);
lean_inc(x_37);
x_38 = l_Lean_PersistentHashMap_isUnaryNode___rarg(x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_37);
x_40 = lean_array_set(x_35, x_8, x_39);
lean_dec(x_8);
lean_ctor_set(x_1, 0, x_40);
return x_1;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_37);
x_41 = lean_ctor_get(x_38, 0);
lean_inc(x_41);
lean_dec(x_38);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_44 = x_41;
} else {
 lean_dec_ref(x_41);
 x_44 = lean_box(0);
}
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_44;
}
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_43);
x_46 = lean_array_set(x_35, x_8, x_45);
lean_dec(x_8);
lean_ctor_set(x_1, 0, x_46);
return x_1;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; size_t x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_1);
x_47 = lean_ctor_get(x_10, 0);
lean_inc(x_47);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 x_48 = x_10;
} else {
 lean_dec_ref(x_10);
 x_48 = lean_box(0);
}
x_49 = lean_array_set(x_4, x_8, x_9);
x_50 = lean_usize_shift_right(x_2, x_5);
x_51 = l_Lean_PersistentHashMap_eraseAux___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__15(x_47, x_50, x_3);
lean_inc(x_51);
x_52 = l_Lean_PersistentHashMap_isUnaryNode___rarg(x_51);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
if (lean_is_scalar(x_48)) {
 x_53 = lean_alloc_ctor(1, 1, 0);
} else {
 x_53 = x_48;
}
lean_ctor_set(x_53, 0, x_51);
x_54 = lean_array_set(x_49, x_8, x_53);
lean_dec(x_8);
x_55 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_55, 0, x_54);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_51);
lean_dec(x_48);
x_56 = lean_ctor_get(x_52, 0);
lean_inc(x_56);
lean_dec(x_52);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_59 = x_56;
} else {
 lean_dec_ref(x_56);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_58);
x_61 = lean_array_set(x_49, x_8, x_60);
lean_dec(x_8);
x_62 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_62, 0, x_61);
return x_62;
}
}
}
default: 
{
lean_dec(x_8);
lean_dec(x_4);
return x_1;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_ctor_get(x_1, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_1, 1);
lean_inc(x_64);
x_65 = lean_unsigned_to_nat(0u);
x_66 = l_Array_idxOfAux___at_Lean_MetavarContext_setMVarUserName___spec__3(x_63, x_3, x_65);
if (lean_obj_tag(x_66) == 0)
{
lean_dec(x_64);
lean_dec(x_63);
return x_1;
}
else
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_1);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_68 = lean_ctor_get(x_1, 1);
lean_dec(x_68);
x_69 = lean_ctor_get(x_1, 0);
lean_dec(x_69);
x_70 = lean_ctor_get(x_66, 0);
lean_inc(x_70);
lean_dec(x_66);
lean_inc(x_70);
x_71 = l_Array_eraseIdx___rarg(x_63, x_70, lean_box(0));
x_72 = l_Array_eraseIdx___rarg(x_64, x_70, lean_box(0));
lean_ctor_set(x_1, 1, x_72);
lean_ctor_set(x_1, 0, x_71);
return x_1;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_1);
x_73 = lean_ctor_get(x_66, 0);
lean_inc(x_73);
lean_dec(x_66);
lean_inc(x_73);
x_74 = l_Array_eraseIdx___rarg(x_63, x_73, lean_box(0));
x_75 = l_Array_eraseIdx___rarg(x_64, x_73, lean_box(0));
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__14(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; size_t x_4; lean_object* x_5; 
x_3 = l_Lean_Name_hash___override(x_2);
x_4 = lean_uint64_to_usize(x_3);
x_5 = l_Lean_PersistentHashMap_eraseAux___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__15(x_1, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
lean_inc(x_2);
x_7 = l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__1(x_4, x_6, x_2);
lean_dec(x_6);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = l_Lean_PersistentHashMap_erase___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__14(x_5, x_8);
lean_dec(x_8);
lean_ctor_set(x_1, 1, x_9);
lean_ctor_set(x_1, 0, x_7);
return x_1;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_1);
x_12 = lean_ctor_get(x_2, 2);
lean_inc(x_12);
lean_inc(x_2);
x_13 = l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__1(x_10, x_12, x_2);
lean_dec(x_12);
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
lean_dec(x_2);
x_15 = l_Lean_PersistentHashMap_erase___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__14(x_11, x_14);
lean_dec(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
static lean_object* _init_l_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Meta", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Ext", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("extExtension", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____closed__1;
x_2 = l_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____closed__2;
x_3 = l_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____closed__3;
x_4 = l_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____closed__4;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PersistentHashMap_empty___at_Lean_Meta_Ext_instInhabitedExtTheorems___spec__1___closed__2;
x_2 = l_Lean_PersistentHashMap_empty___at_Lean_Meta_Ext_instInhabitedExtTheorems___spec__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____lambda__1), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_id___rarg___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____closed__5;
x_2 = l_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____closed__7;
x_3 = l_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____closed__6;
x_4 = l_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____closed__8;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____closed__9;
x_3 = l_Lean_registerSimpleScopedEnvExtension___rarg(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentHashMap_findAtAux___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__4(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__3(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__2(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; lean_object* x_8; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__7(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__6(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__12(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_binInsertM___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__11(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__9(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__15___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_eraseAux___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__15(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__14___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PersistentHashMap_erase___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__14(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_insertionSort_swapLoop___at_Lean_Meta_Ext_getExtTheorems___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_2, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_2, x_6);
x_8 = lean_array_fget(x_1, x_2);
x_9 = lean_array_fget(x_1, x_7);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_nat_dec_lt(x_10, x_11);
lean_dec(x_11);
lean_dec(x_10);
if (x_12 == 0)
{
lean_dec(x_7);
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_13; 
x_13 = lean_array_fswap(x_1, x_2, x_7);
lean_dec(x_2);
x_1 = x_13;
x_2 = x_7;
x_3 = lean_box(0);
goto _start;
}
}
else
{
lean_dec(x_2);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Array_insertionSort_traverse___at_Lean_Meta_Ext_getExtTheorems___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_3, x_6);
lean_dec(x_3);
x_8 = lean_array_get_size(x_1);
x_9 = lean_nat_dec_lt(x_2, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_dec(x_7);
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_inc(x_2);
x_10 = l_Array_insertionSort_swapLoop___at_Lean_Meta_Ext_getExtTheorems___spec__2(x_1, x_2, lean_box(0));
x_11 = lean_nat_add(x_2, x_6);
lean_dec(x_2);
x_1 = x_10;
x_2 = x_11;
x_3 = x_7;
goto _start;
}
}
else
{
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_Ext_getExtTheorems___spec__3(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; size_t x_11; size_t x_12; 
x_7 = lean_array_uget(x_2, x_3);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = l_Lean_PersistentHashMap_contains___at_Lean_NameSSet_contains___spec__2(x_8, x_9);
lean_dec(x_9);
x_11 = 1;
x_12 = lean_usize_add(x_3, x_11);
if (x_10 == 0)
{
lean_object* x_13; 
x_13 = lean_array_push(x_5, x_7);
x_3 = x_12;
x_5 = x_13;
goto _start;
}
else
{
lean_dec(x_7);
x_3 = x_12;
goto _start;
}
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
static lean_object* _init_l_Lean_Meta_Ext_getExtTheorems___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Ext_extExtension;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Ext_getExtTheorems___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__9___closed__1;
x_2 = lean_array_get_size(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_getExtTheorems(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Meta_Ext_extExtension;
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_ctor_get_uint8(x_13, sizeof(void*)*3);
lean_dec(x_13);
x_15 = l_Lean_Meta_Ext_instInhabitedExtTheorems;
x_16 = l_Lean_Meta_Ext_getExtTheorems___closed__1;
x_17 = l_Lean_ScopedEnvExtension_getState___rarg(x_15, x_16, x_10, x_14);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = l_Lean_Meta_DiscrTree_getMatch___rarg(x_18, x_1, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_array_get_size(x_21);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_nat_dec_lt(x_23, x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_17);
x_25 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__9___closed__1;
x_26 = l_Lean_Meta_Ext_getExtTheorems___closed__2;
x_27 = l_Array_insertionSort_traverse___at_Lean_Meta_Ext_getExtTheorems___spec__1(x_25, x_23, x_26);
x_28 = l_Array_reverse___rarg(x_27);
lean_ctor_set(x_19, 0, x_28);
return x_19;
}
else
{
uint8_t x_29; 
x_29 = lean_nat_dec_le(x_22, x_22);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_17);
x_30 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__9___closed__1;
x_31 = l_Lean_Meta_Ext_getExtTheorems___closed__2;
x_32 = l_Array_insertionSort_traverse___at_Lean_Meta_Ext_getExtTheorems___spec__1(x_30, x_23, x_31);
x_33 = l_Array_reverse___rarg(x_32);
lean_ctor_set(x_19, 0, x_33);
return x_19;
}
else
{
size_t x_34; size_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_34 = 0;
x_35 = lean_usize_of_nat(x_22);
lean_dec(x_22);
x_36 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__9___closed__1;
x_37 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_Ext_getExtTheorems___spec__3(x_17, x_21, x_34, x_35, x_36);
lean_dec(x_21);
x_38 = lean_array_get_size(x_37);
x_39 = l_Array_insertionSort_traverse___at_Lean_Meta_Ext_getExtTheorems___spec__1(x_37, x_23, x_38);
x_40 = l_Array_reverse___rarg(x_39);
lean_ctor_set(x_19, 0, x_40);
return x_19;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_41 = lean_ctor_get(x_19, 0);
x_42 = lean_ctor_get(x_19, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_19);
x_43 = lean_array_get_size(x_41);
x_44 = lean_unsigned_to_nat(0u);
x_45 = lean_nat_dec_lt(x_44, x_43);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_43);
lean_dec(x_41);
lean_dec(x_17);
x_46 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__9___closed__1;
x_47 = l_Lean_Meta_Ext_getExtTheorems___closed__2;
x_48 = l_Array_insertionSort_traverse___at_Lean_Meta_Ext_getExtTheorems___spec__1(x_46, x_44, x_47);
x_49 = l_Array_reverse___rarg(x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_42);
return x_50;
}
else
{
uint8_t x_51; 
x_51 = lean_nat_dec_le(x_43, x_43);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_43);
lean_dec(x_41);
lean_dec(x_17);
x_52 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__9___closed__1;
x_53 = l_Lean_Meta_Ext_getExtTheorems___closed__2;
x_54 = l_Array_insertionSort_traverse___at_Lean_Meta_Ext_getExtTheorems___spec__1(x_52, x_44, x_53);
x_55 = l_Array_reverse___rarg(x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_42);
return x_56;
}
else
{
size_t x_57; size_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_57 = 0;
x_58 = lean_usize_of_nat(x_43);
lean_dec(x_43);
x_59 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__9___closed__1;
x_60 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_Ext_getExtTheorems___spec__3(x_17, x_41, x_57, x_58, x_59);
lean_dec(x_41);
x_61 = lean_array_get_size(x_60);
x_62 = l_Array_insertionSort_traverse___at_Lean_Meta_Ext_getExtTheorems___spec__1(x_60, x_44, x_61);
x_63 = l_Array_reverse___rarg(x_62);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_42);
return x_64;
}
}
}
}
else
{
uint8_t x_65; 
lean_dec(x_17);
x_65 = !lean_is_exclusive(x_19);
if (x_65 == 0)
{
return x_19;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_19, 0);
x_67 = lean_ctor_get(x_19, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_19);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_Ext_getExtTheorems___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_Ext_getExtTheorems___spec__3(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_ExtTheorems_eraseCore(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_box(0);
x_6 = l_Lean_PersistentHashMap_insert___at_Lean_NameSSet_insert___spec__2(x_4, x_2, x_5);
lean_ctor_set(x_1, 1, x_6);
return x_1;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_1);
x_9 = lean_box(0);
x_10 = l_Lean_PersistentHashMap_insert___at_Lean_NameSSet_insert___spec__2(x_8, x_2, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
}
LEAN_EXPORT uint8_t l_Array_foldlMUnsafe_fold___at_Lean_Meta_Ext_ExtTheorems_contains___spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, uint8_t x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_array_uget(x_2, x_3);
x_8 = 1;
x_9 = lean_usize_add(x_3, x_8);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
lean_inc(x_1);
x_11 = l_Lean_Meta_DiscrTree_Trie_foldValuesM___at_Lean_Meta_Ext_ExtTheorems_contains___spec__1(x_1, x_5, x_10);
lean_dec(x_10);
x_3 = x_9;
x_5 = x_11;
goto _start;
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT uint8_t l_Array_foldlMUnsafe_fold___at_Lean_Meta_Ext_ExtTheorems_contains___spec__3(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, uint8_t x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_array_uget(x_2, x_3);
x_8 = 1;
x_9 = lean_usize_add(x_3, x_8);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
lean_inc(x_1);
x_11 = l_Lean_Meta_DiscrTree_Trie_foldValuesM___at_Lean_Meta_Ext_ExtTheorems_contains___spec__1(x_1, x_5, x_10);
lean_dec(x_10);
x_3 = x_9;
x_5 = x_11;
goto _start;
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT uint8_t l_Array_foldlMUnsafe_fold___at_Lean_Meta_Ext_ExtTheorems_contains___spec__4(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, uint8_t x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; size_t x_11; size_t x_12; 
x_7 = lean_array_uget(x_2, x_3);
x_8 = lean_box(x_5);
lean_inc(x_1);
x_9 = lean_apply_2(x_1, x_8, x_7);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
x_11 = 1;
x_12 = lean_usize_add(x_3, x_11);
x_3 = x_12;
x_5 = x_10;
goto _start;
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT uint8_t l_Array_foldlMUnsafe_fold___at_Lean_Meta_Ext_ExtTheorems_contains___spec__5(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, uint8_t x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_array_uget(x_2, x_3);
x_8 = 1;
x_9 = lean_usize_add(x_3, x_8);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
lean_inc(x_1);
x_11 = l_Lean_Meta_DiscrTree_Trie_foldValuesM___at_Lean_Meta_Ext_ExtTheorems_contains___spec__1(x_1, x_5, x_10);
lean_dec(x_10);
x_3 = x_9;
x_5 = x_11;
goto _start;
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_DiscrTree_Trie_foldValuesM___at_Lean_Meta_Ext_ExtTheorems_contains___spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_array_get_size(x_4);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_lt(x_7, x_6);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
lean_dec(x_6);
x_9 = lean_array_get_size(x_5);
x_10 = lean_nat_dec_lt(x_7, x_9);
if (x_10 == 0)
{
lean_dec(x_9);
lean_dec(x_1);
return x_2;
}
else
{
uint8_t x_11; 
x_11 = lean_nat_dec_le(x_9, x_9);
if (x_11 == 0)
{
lean_dec(x_9);
lean_dec(x_1);
return x_2;
}
else
{
size_t x_12; size_t x_13; uint8_t x_14; 
x_12 = 0;
x_13 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_14 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_Ext_ExtTheorems_contains___spec__2(x_1, x_5, x_12, x_13, x_2);
return x_14;
}
}
}
else
{
uint8_t x_15; 
x_15 = lean_nat_dec_le(x_6, x_6);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
lean_dec(x_6);
x_16 = lean_array_get_size(x_5);
x_17 = lean_nat_dec_lt(x_7, x_16);
if (x_17 == 0)
{
lean_dec(x_16);
lean_dec(x_1);
return x_2;
}
else
{
uint8_t x_18; 
x_18 = lean_nat_dec_le(x_16, x_16);
if (x_18 == 0)
{
lean_dec(x_16);
lean_dec(x_1);
return x_2;
}
else
{
size_t x_19; size_t x_20; uint8_t x_21; 
x_19 = 0;
x_20 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_21 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_Ext_ExtTheorems_contains___spec__3(x_1, x_5, x_19, x_20, x_2);
return x_21;
}
}
}
else
{
size_t x_22; size_t x_23; uint8_t x_24; lean_object* x_25; uint8_t x_26; 
x_22 = 0;
x_23 = lean_usize_of_nat(x_6);
lean_dec(x_6);
lean_inc(x_1);
x_24 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_Ext_ExtTheorems_contains___spec__4(x_1, x_4, x_22, x_23, x_2);
x_25 = lean_array_get_size(x_5);
x_26 = lean_nat_dec_lt(x_7, x_25);
if (x_26 == 0)
{
lean_dec(x_25);
lean_dec(x_1);
return x_24;
}
else
{
uint8_t x_27; 
x_27 = lean_nat_dec_le(x_25, x_25);
if (x_27 == 0)
{
lean_dec(x_25);
lean_dec(x_1);
return x_24;
}
else
{
size_t x_28; uint8_t x_29; 
x_28 = lean_usize_of_nat(x_25);
lean_dec(x_25);
x_29 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_Ext_ExtTheorems_contains___spec__5(x_1, x_5, x_22, x_28, x_24);
return x_29;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_Ext_ExtTheorems_contains___spec__6(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(x_3);
x_5 = l_Lean_PersistentHashMap_foldlMAux___at_Lean_MetavarContext_getExprAssignmentDomain___spec__3___rarg(x_2, x_1, x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Ext_ExtTheorems_contains___lambda__1(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
if (x_2 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_name_eq(x_4, x_1);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 1;
return x_6;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Ext_ExtTheorems_contains___lambda__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_Meta_DiscrTree_Trie_foldValuesM___at_Lean_Meta_Ext_ExtTheorems_contains___spec__1(x_1, x_2, x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Ext_ExtTheorems_contains(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_inc(x_2);
x_4 = lean_alloc_closure((void*)(l_Lean_Meta_Ext_ExtTheorems_contains___lambda__1___boxed), 3, 1);
lean_closure_set(x_4, 0, x_2);
x_5 = lean_alloc_closure((void*)(l_Lean_Meta_Ext_ExtTheorems_contains___lambda__2___boxed), 4, 1);
lean_closure_set(x_5, 0, x_4);
x_6 = 0;
x_7 = lean_box(x_6);
x_8 = l_Lean_PersistentHashMap_foldlMAux___at_Lean_MetavarContext_getExprAssignmentDomain___spec__3___rarg(x_5, x_3, x_7);
lean_dec(x_3);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_2);
lean_dec(x_1);
x_10 = 0;
return x_10;
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_12 = l_Lean_PersistentHashMap_contains___at_Lean_NameSSet_contains___spec__2(x_11, x_2);
lean_dec(x_2);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = 1;
return x_13;
}
else
{
uint8_t x_14; 
x_14 = 0;
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_Ext_ExtTheorems_contains___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox(x_5);
lean_dec(x_5);
x_9 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_Ext_ExtTheorems_contains___spec__2(x_1, x_2, x_6, x_7, x_8);
lean_dec(x_2);
x_10 = lean_box(x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_Ext_ExtTheorems_contains___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox(x_5);
lean_dec(x_5);
x_9 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_Ext_ExtTheorems_contains___spec__3(x_1, x_2, x_6, x_7, x_8);
lean_dec(x_2);
x_10 = lean_box(x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_Ext_ExtTheorems_contains___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox(x_5);
lean_dec(x_5);
x_9 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_Ext_ExtTheorems_contains___spec__4(x_1, x_2, x_6, x_7, x_8);
lean_dec(x_2);
x_10 = lean_box(x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_Ext_ExtTheorems_contains___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox(x_5);
lean_dec(x_5);
x_9 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_Ext_ExtTheorems_contains___spec__5(x_1, x_2, x_6, x_7, x_8);
lean_dec(x_2);
x_10 = lean_box(x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Trie_foldValuesM___at_Lean_Meta_Ext_ExtTheorems_contains___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lean_Meta_DiscrTree_Trie_foldValuesM___at_Lean_Meta_Ext_ExtTheorems_contains___spec__1(x_1, x_4, x_3);
lean_dec(x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_Ext_ExtTheorems_contains___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
lean_dec(x_3);
x_5 = l_Lean_PersistentHashMap_foldlM___at_Lean_Meta_Ext_ExtTheorems_contains___spec__6(x_1, x_2, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_ExtTheorems_contains___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lean_Meta_Ext_ExtTheorems_contains___lambda__1(x_1, x_4, x_3);
lean_dec(x_3);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_ExtTheorems_contains___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_Meta_Ext_ExtTheorems_contains___lambda__2(x_1, x_5, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_ExtTheorems_contains___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_Ext_ExtTheorems_contains(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_isExtTheorem(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_Meta_Ext_extExtension;
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_ctor_get_uint8(x_11, sizeof(void*)*3);
lean_dec(x_11);
x_13 = l_Lean_Meta_Ext_instInhabitedExtTheorems;
x_14 = l_Lean_Meta_Ext_getExtTheorems___closed__1;
x_15 = l_Lean_ScopedEnvExtension_getState___rarg(x_13, x_14, x_8, x_12);
x_16 = l_Lean_Meta_Ext_ExtTheorems_contains(x_15, x_1);
x_17 = lean_box(x_16);
lean_ctor_set(x_5, 0, x_17);
return x_5;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; 
x_18 = lean_ctor_get(x_5, 0);
x_19 = lean_ctor_get(x_5, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_5);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Meta_Ext_extExtension;
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_ctor_get_uint8(x_23, sizeof(void*)*3);
lean_dec(x_23);
x_25 = l_Lean_Meta_Ext_instInhabitedExtTheorems;
x_26 = l_Lean_Meta_Ext_getExtTheorems___closed__1;
x_27 = l_Lean_ScopedEnvExtension_getState___rarg(x_25, x_26, x_20, x_24);
x_28 = l_Lean_Meta_Ext_ExtTheorems_contains(x_27, x_1);
x_29 = lean_box(x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_19);
return x_30;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_isExtTheorem___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Ext_isExtTheorem(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_ExtTheorems_erase___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_Meta_Ext_ExtTheorems_eraseCore(x_2, x_3);
x_8 = lean_apply_2(x_6, lean_box(0), x_7);
return x_8;
}
}
static lean_object* _init_l_Lean_Meta_Ext_ExtTheorems_erase___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Ext_ExtTheorems_erase___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Ext_ExtTheorems_erase___rarg___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Ext_ExtTheorems_erase___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' does not have [ext] attribute", 31, 31);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Ext_ExtTheorems_erase___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Ext_ExtTheorems_erase___rarg___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_ExtTheorems_erase___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_5 = lean_alloc_closure((void*)(l_Lean_Meta_Ext_ExtTheorems_erase___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_3);
lean_closure_set(x_5, 2, x_4);
lean_inc(x_4);
x_6 = l_Lean_Meta_Ext_ExtTheorems_contains(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = l_Lean_MessageData_ofName(x_4);
x_9 = l_Lean_Meta_Ext_ExtTheorems_erase___rarg___closed__2;
x_10 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = l_Lean_Meta_Ext_ExtTheorems_erase___rarg___closed__4;
x_12 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Lean_throwError___rarg(x_1, x_2, x_12);
x_14 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_13, x_5);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_4);
lean_dec(x_2);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
lean_dec(x_1);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_box(0);
x_19 = lean_apply_2(x_17, lean_box(0), x_18);
x_20 = lean_apply_4(x_15, lean_box(0), lean_box(0), x_19, x_5);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_ExtTheorems_erase(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Ext_ExtTheorems_erase___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Ext_ExtTheorems_erase___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Ext_ExtTheorems_erase___rarg___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
lean_object* initialize_Init_Data_Array_InsertionSort(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_DiscrTree(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Ext(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Array_InsertionSort(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_DiscrTree(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Ext_instInhabitedExtTheorem___closed__1 = _init_l_Lean_Meta_Ext_instInhabitedExtTheorem___closed__1();
lean_mark_persistent(l_Lean_Meta_Ext_instInhabitedExtTheorem___closed__1);
l_Lean_Meta_Ext_instInhabitedExtTheorem___closed__2 = _init_l_Lean_Meta_Ext_instInhabitedExtTheorem___closed__2();
lean_mark_persistent(l_Lean_Meta_Ext_instInhabitedExtTheorem___closed__2);
l_Lean_Meta_Ext_instInhabitedExtTheorem = _init_l_Lean_Meta_Ext_instInhabitedExtTheorem();
lean_mark_persistent(l_Lean_Meta_Ext_instInhabitedExtTheorem);
l_Array_Array_repr___at_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____spec__1___closed__1 = _init_l_Array_Array_repr___at_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____spec__1___closed__1();
lean_mark_persistent(l_Array_Array_repr___at_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____spec__1___closed__1);
l_Array_Array_repr___at_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____spec__1___closed__2 = _init_l_Array_Array_repr___at_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____spec__1___closed__2();
lean_mark_persistent(l_Array_Array_repr___at_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____spec__1___closed__2);
l_Array_Array_repr___at_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____spec__1___closed__3 = _init_l_Array_Array_repr___at_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____spec__1___closed__3();
lean_mark_persistent(l_Array_Array_repr___at_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____spec__1___closed__3);
l_Array_Array_repr___at_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____spec__1___closed__4 = _init_l_Array_Array_repr___at_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____spec__1___closed__4();
lean_mark_persistent(l_Array_Array_repr___at_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____spec__1___closed__4);
l_Array_Array_repr___at_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____spec__1___closed__5 = _init_l_Array_Array_repr___at_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____spec__1___closed__5();
lean_mark_persistent(l_Array_Array_repr___at_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____spec__1___closed__5);
l_Array_Array_repr___at_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____spec__1___closed__6 = _init_l_Array_Array_repr___at_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____spec__1___closed__6();
lean_mark_persistent(l_Array_Array_repr___at_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____spec__1___closed__6);
l_Array_Array_repr___at_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____spec__1___closed__7 = _init_l_Array_Array_repr___at_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____spec__1___closed__7();
lean_mark_persistent(l_Array_Array_repr___at_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____spec__1___closed__7);
l_Array_Array_repr___at_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____spec__1___closed__8 = _init_l_Array_Array_repr___at_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____spec__1___closed__8();
lean_mark_persistent(l_Array_Array_repr___at_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____spec__1___closed__8);
l_Array_Array_repr___at_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____spec__1___closed__9 = _init_l_Array_Array_repr___at_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____spec__1___closed__9();
lean_mark_persistent(l_Array_Array_repr___at_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____spec__1___closed__9);
l_Array_Array_repr___at_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____spec__1___closed__10 = _init_l_Array_Array_repr___at_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____spec__1___closed__10();
lean_mark_persistent(l_Array_Array_repr___at_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____spec__1___closed__10);
l_Array_Array_repr___at_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____spec__1___closed__11 = _init_l_Array_Array_repr___at_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____spec__1___closed__11();
lean_mark_persistent(l_Array_Array_repr___at_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____spec__1___closed__11);
l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__1 = _init_l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__1();
lean_mark_persistent(l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__1);
l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__2 = _init_l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__2();
lean_mark_persistent(l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__2);
l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__3 = _init_l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__3();
lean_mark_persistent(l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__3);
l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__4 = _init_l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__4();
lean_mark_persistent(l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__4);
l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__5 = _init_l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__5();
lean_mark_persistent(l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__5);
l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__6 = _init_l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__6();
lean_mark_persistent(l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__6);
l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__7 = _init_l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__7();
lean_mark_persistent(l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__7);
l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__8 = _init_l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__8();
lean_mark_persistent(l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__8);
l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__9 = _init_l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__9();
lean_mark_persistent(l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__9);
l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__10 = _init_l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__10();
lean_mark_persistent(l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__10);
l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__11 = _init_l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__11();
lean_mark_persistent(l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__11);
l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__12 = _init_l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__12();
lean_mark_persistent(l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__12);
l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__13 = _init_l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__13();
lean_mark_persistent(l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__13);
l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__14 = _init_l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__14();
lean_mark_persistent(l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__14);
l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__15 = _init_l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__15();
lean_mark_persistent(l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__15);
l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__16 = _init_l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__16();
lean_mark_persistent(l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__16);
l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__17 = _init_l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__17();
lean_mark_persistent(l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__17);
l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__18 = _init_l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__18();
lean_mark_persistent(l_Lean_Meta_Ext_reprExtTheorem____x40_Lean_Meta_Tactic_Ext___hyg_51____closed__18);
l_Lean_Meta_Ext_instReprExtTheorem___closed__1 = _init_l_Lean_Meta_Ext_instReprExtTheorem___closed__1();
lean_mark_persistent(l_Lean_Meta_Ext_instReprExtTheorem___closed__1);
l_Lean_Meta_Ext_instReprExtTheorem = _init_l_Lean_Meta_Ext_instReprExtTheorem();
lean_mark_persistent(l_Lean_Meta_Ext_instReprExtTheorem);
l_Lean_Meta_Ext_instBEqExtTheorem___closed__1 = _init_l_Lean_Meta_Ext_instBEqExtTheorem___closed__1();
lean_mark_persistent(l_Lean_Meta_Ext_instBEqExtTheorem___closed__1);
l_Lean_Meta_Ext_instBEqExtTheorem = _init_l_Lean_Meta_Ext_instBEqExtTheorem();
lean_mark_persistent(l_Lean_Meta_Ext_instBEqExtTheorem);
l_Lean_Meta_Ext_instHashableExtTheorem___closed__1 = _init_l_Lean_Meta_Ext_instHashableExtTheorem___closed__1();
lean_mark_persistent(l_Lean_Meta_Ext_instHashableExtTheorem___closed__1);
l_Lean_Meta_Ext_instHashableExtTheorem = _init_l_Lean_Meta_Ext_instHashableExtTheorem();
lean_mark_persistent(l_Lean_Meta_Ext_instHashableExtTheorem);
l_Lean_PersistentHashMap_empty___at_Lean_Meta_Ext_instInhabitedExtTheorems___spec__1___closed__1 = _init_l_Lean_PersistentHashMap_empty___at_Lean_Meta_Ext_instInhabitedExtTheorems___spec__1___closed__1();
lean_mark_persistent(l_Lean_PersistentHashMap_empty___at_Lean_Meta_Ext_instInhabitedExtTheorems___spec__1___closed__1);
l_Lean_PersistentHashMap_empty___at_Lean_Meta_Ext_instInhabitedExtTheorems___spec__1___closed__2 = _init_l_Lean_PersistentHashMap_empty___at_Lean_Meta_Ext_instInhabitedExtTheorems___spec__1___closed__2();
lean_mark_persistent(l_Lean_PersistentHashMap_empty___at_Lean_Meta_Ext_instInhabitedExtTheorems___spec__1___closed__2);
l_Lean_PersistentHashMap_empty___at_Lean_Meta_Ext_instInhabitedExtTheorems___spec__1 = _init_l_Lean_PersistentHashMap_empty___at_Lean_Meta_Ext_instInhabitedExtTheorems___spec__1();
lean_mark_persistent(l_Lean_PersistentHashMap_empty___at_Lean_Meta_Ext_instInhabitedExtTheorems___spec__1);
l_Lean_Meta_Ext_instInhabitedExtTheorems = _init_l_Lean_Meta_Ext_instInhabitedExtTheorems();
lean_mark_persistent(l_Lean_Meta_Ext_instInhabitedExtTheorems);
l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__3___closed__1 = _init_l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__3___closed__1();
l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__3___closed__2 = _init_l_Lean_PersistentHashMap_findAux___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__3___closed__2();
l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__6___closed__1 = _init_l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__6___closed__1();
lean_mark_persistent(l_Lean_PersistentHashMap_insertAux___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__6___closed__1);
l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__9___closed__1 = _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__9___closed__1();
lean_mark_persistent(l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__9___closed__1);
l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__9___closed__2 = _init_l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__9___closed__2();
lean_mark_persistent(l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__9___closed__2);
l_panic___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__13___closed__1 = _init_l_panic___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__13___closed__1();
lean_mark_persistent(l_panic___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__13___closed__1);
l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__1___closed__1 = _init_l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__1___closed__1();
lean_mark_persistent(l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__1___closed__1);
l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__1___closed__2 = _init_l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__1___closed__2();
lean_mark_persistent(l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__1___closed__2);
l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__1___closed__3 = _init_l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__1___closed__3();
lean_mark_persistent(l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__1___closed__3);
l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__1___closed__4 = _init_l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__1___closed__4();
lean_mark_persistent(l_Lean_Meta_DiscrTree_insertCore___at_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____spec__1___closed__4);
l_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____closed__1 = _init_l_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____closed__1();
lean_mark_persistent(l_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____closed__1);
l_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____closed__2 = _init_l_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____closed__2();
lean_mark_persistent(l_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____closed__2);
l_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____closed__3 = _init_l_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____closed__3();
lean_mark_persistent(l_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____closed__3);
l_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____closed__4 = _init_l_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____closed__4();
lean_mark_persistent(l_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____closed__4);
l_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____closed__5 = _init_l_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____closed__5();
lean_mark_persistent(l_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____closed__5);
l_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____closed__6 = _init_l_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____closed__6();
lean_mark_persistent(l_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____closed__6);
l_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____closed__7 = _init_l_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____closed__7();
lean_mark_persistent(l_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____closed__7);
l_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____closed__8 = _init_l_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____closed__8();
lean_mark_persistent(l_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____closed__8);
l_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____closed__9 = _init_l_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____closed__9();
lean_mark_persistent(l_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321____closed__9);
if (builtin) {res = l_Lean_Meta_Ext_initFn____x40_Lean_Meta_Tactic_Ext___hyg_321_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Ext_extExtension = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Ext_extExtension);
lean_dec_ref(res);
}l_Lean_Meta_Ext_getExtTheorems___closed__1 = _init_l_Lean_Meta_Ext_getExtTheorems___closed__1();
lean_mark_persistent(l_Lean_Meta_Ext_getExtTheorems___closed__1);
l_Lean_Meta_Ext_getExtTheorems___closed__2 = _init_l_Lean_Meta_Ext_getExtTheorems___closed__2();
lean_mark_persistent(l_Lean_Meta_Ext_getExtTheorems___closed__2);
l_Lean_Meta_Ext_ExtTheorems_erase___rarg___closed__1 = _init_l_Lean_Meta_Ext_ExtTheorems_erase___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_Ext_ExtTheorems_erase___rarg___closed__1);
l_Lean_Meta_Ext_ExtTheorems_erase___rarg___closed__2 = _init_l_Lean_Meta_Ext_ExtTheorems_erase___rarg___closed__2();
lean_mark_persistent(l_Lean_Meta_Ext_ExtTheorems_erase___rarg___closed__2);
l_Lean_Meta_Ext_ExtTheorems_erase___rarg___closed__3 = _init_l_Lean_Meta_Ext_ExtTheorems_erase___rarg___closed__3();
lean_mark_persistent(l_Lean_Meta_Ext_ExtTheorems_erase___rarg___closed__3);
l_Lean_Meta_Ext_ExtTheorems_erase___rarg___closed__4 = _init_l_Lean_Meta_Ext_ExtTheorems_erase___rarg___closed__4();
lean_mark_persistent(l_Lean_Meta_Ext_ExtTheorems_erase___rarg___closed__4);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
