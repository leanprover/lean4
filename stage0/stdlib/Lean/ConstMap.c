// Lean compiler output
// Module: Lean.ConstMap
// Imports: public import Lean.ConstTrie public import Lean.Declaration public import Lean.Data.PersistentHashMap
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
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_foldlMAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ImportedConsts_foldlM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* l_Lean_PersistentHashMap_forM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ImportedConsts_forM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_instMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_instMonad___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ExceptT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ImportedConsts_findEntry_x3f___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_ImportedConsts_empty___redArg();
lean_object* l_Lean_PersistentHashMap_foldl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_imported_consts_find_entry_core(lean_object*, lean_object*);
lean_object* lean_imported_consts_find_entry_cached(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstMap_0__Lean_ImportedConsts_findConstEntryCachedImpl___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_findConstEntryCached_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_findConstEntryCached_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_findConstCached_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_findConstCached_x3f___boxed(lean_object*, lean_object*);
lean_object* lean_imported_consts_find_mod_idx_cached(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ConstMap_0__Lean_ImportedConsts_findConstModIdxCachedImpl___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_findConstModIdxCached_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_findConstModIdxCached_x3f___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_instInhabitedConstMap___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedConstMap___closed__0;
static lean_once_cell_t l_Lean_instInhabitedConstMap___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedConstMap___closed__1;
static lean_once_cell_t l_Lean_instInhabitedConstMap___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedConstMap___closed__2;
static lean_once_cell_t l_Lean_instInhabitedConstMap___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedConstMap___closed__3;
LEAN_EXPORT lean_object* l_Lean_instInhabitedConstMap;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ConstMap_find_x3f_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ConstMap_find_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ConstMap_find_x3f_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ConstMap_find_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_ConstMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_ConstMap_find_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstMap_find_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstMap_find_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_ConstMap_find_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_ConstMap_find_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ConstMap_find_x3f_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ConstMap_find_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ConstMap_find_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ConstMap_find_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstMap_find_x3f_x27(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstMap_find_x3f_x27___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_ConstMap_contains_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_ConstMap_contains_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_ConstMap_contains_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_ConstMap_contains_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_ConstMap_contains_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_ConstMap_contains_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_ConstMap_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstMap_contains___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_ConstMap_contains_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_ConstMap_contains_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_ConstMap_contains_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_ConstMap_contains_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_ConstMap_contains_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_ConstMap_contains_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ConstMap_insert_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ConstMap_insert_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ConstMap_insert_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ConstMap_insert_spec__0_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ConstMap_insert_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ConstMap_insert_spec__0_spec__0_spec__2___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ConstMap_insert_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ConstMap_insert_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_ConstMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstMap_insert(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_ConstMap_insert_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ConstMap_insert_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ConstMap_insert_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ConstMap_insert_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ConstMap_insert_spec__0_spec__0_spec__2(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ConstMap_insert_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ConstMap_insert_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstMap_foldStage2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstMap_foldStage2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstMap_foldM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstMap_foldM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstMap_foldM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_ConstMap_fold_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_ConstMap_fold_spec__0_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_ConstMap_fold_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_ConstMap_fold_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_ConstMap_fold_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_ConstMap_fold_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_ConstMap_fold_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_ConstMap_fold_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_ConstMap_fold_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstMap_fold___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstMap_fold(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_ConstMap_fold_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_ConstMap_fold_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_ConstMap_fold_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_ConstMap_fold_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_ConstMap_fold_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_ConstMap_fold_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_ConstMap_fold_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_ConstMap_fold_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_ConstMap_fold_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_ConstMap_fold_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_ConstMap_fold_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_ConstMap_fold_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstMap_forM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstMap_forM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstMap_forM(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstMap_instForMProdNameConstantInfoOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstMap_instForMProdNameConstantInfoOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstMap_instForMProdNameConstantInfoOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstMap_instForMProdNameConstantInfoOfMonad(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstMap_instForInProdNameConstantInfoOfMonad___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstMap_instForInProdNameConstantInfoOfMonad___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstMap_instForInProdNameConstantInfoOfMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstMap_instForInProdNameConstantInfoOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstMap_instForInProdNameConstantInfoOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstMap_instForInProdNameConstantInfoOfMonad(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ConstMap_toList___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_ConstMap_toList___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_ConstMap_toList___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ConstMap_toList___closed__0 = (const lean_object*)&l_Lean_ConstMap_toList___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_ConstMap_toList(lean_object*);
LEAN_EXPORT lean_object* lean_imported_consts_find_entry_core(lean_object* v_t_1_, lean_object* v_n_2_){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = l_Lean_ImportedConsts_findEntry_x3f___redArg(v_t_1_, v_n_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstMap_0__Lean_ImportedConsts_findConstEntryCachedImpl___boxed(lean_object* v_cache_x3f_7_, lean_object* v_t_8_, lean_object* v_n_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = lean_imported_consts_find_entry_cached(v_cache_x3f_7_, v_t_8_, v_n_9_);
lean_dec(v_n_9_);
lean_dec_ref(v_t_8_);
lean_dec(v_cache_x3f_7_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_findConstEntryCached_x3f(lean_object* v_t_11_, lean_object* v_n_12_){
_start:
{
lean_object* v_cache_x3f_13_; lean_object* v___x_14_; 
v_cache_x3f_13_ = lean_ctor_get(v_t_11_, 0);
v___x_14_ = lean_imported_consts_find_entry_cached(v_cache_x3f_13_, v_t_11_, v_n_12_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_findConstEntryCached_x3f___boxed(lean_object* v_t_15_, lean_object* v_n_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = l_Lean_ImportedConsts_findConstEntryCached_x3f(v_t_15_, v_n_16_);
lean_dec(v_n_16_);
lean_dec_ref(v_t_15_);
return v_res_17_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_findConstCached_x3f(lean_object* v_t_18_, lean_object* v_n_19_){
_start:
{
lean_object* v_cache_x3f_20_; lean_object* v___x_21_; 
v_cache_x3f_20_ = lean_ctor_get(v_t_18_, 0);
v___x_21_ = lean_imported_consts_find_entry_cached(v_cache_x3f_20_, v_t_18_, v_n_19_);
if (lean_obj_tag(v___x_21_) == 0)
{
lean_object* v___x_22_; 
v___x_22_ = lean_box(0);
return v___x_22_;
}
else
{
lean_object* v_val_23_; lean_object* v___x_25_; uint8_t v_isShared_26_; uint8_t v_isSharedCheck_31_; 
v_val_23_ = lean_ctor_get(v___x_21_, 0);
v_isSharedCheck_31_ = !lean_is_exclusive(v___x_21_);
if (v_isSharedCheck_31_ == 0)
{
v___x_25_ = v___x_21_;
v_isShared_26_ = v_isSharedCheck_31_;
goto v_resetjp_24_;
}
else
{
lean_inc(v_val_23_);
lean_dec(v___x_21_);
v___x_25_ = lean_box(0);
v_isShared_26_ = v_isSharedCheck_31_;
goto v_resetjp_24_;
}
v_resetjp_24_:
{
lean_object* v_fst_27_; lean_object* v___x_29_; 
v_fst_27_ = lean_ctor_get(v_val_23_, 0);
lean_inc(v_fst_27_);
lean_dec(v_val_23_);
if (v_isShared_26_ == 0)
{
lean_ctor_set(v___x_25_, 0, v_fst_27_);
v___x_29_ = v___x_25_;
goto v_reusejp_28_;
}
else
{
lean_object* v_reuseFailAlloc_30_; 
v_reuseFailAlloc_30_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_30_, 0, v_fst_27_);
v___x_29_ = v_reuseFailAlloc_30_;
goto v_reusejp_28_;
}
v_reusejp_28_:
{
return v___x_29_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_findConstCached_x3f___boxed(lean_object* v_t_32_, lean_object* v_n_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_Lean_ImportedConsts_findConstCached_x3f(v_t_32_, v_n_33_);
lean_dec(v_n_33_);
lean_dec_ref(v_t_32_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ConstMap_0__Lean_ImportedConsts_findConstModIdxCachedImpl___boxed(lean_object* v_cache_x3f_38_, lean_object* v_t_39_, lean_object* v_n_40_){
_start:
{
lean_object* v_res_41_; 
v_res_41_ = lean_imported_consts_find_mod_idx_cached(v_cache_x3f_38_, v_t_39_, v_n_40_);
lean_dec(v_n_40_);
lean_dec_ref(v_t_39_);
lean_dec(v_cache_x3f_38_);
return v_res_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_findConstModIdxCached_x3f(lean_object* v_t_42_, lean_object* v_n_43_){
_start:
{
lean_object* v_cache_x3f_44_; lean_object* v___x_45_; lean_object* v_zero_46_; uint8_t v_isZero_47_; 
v_cache_x3f_44_ = lean_ctor_get(v_t_42_, 0);
v___x_45_ = lean_imported_consts_find_mod_idx_cached(v_cache_x3f_44_, v_t_42_, v_n_43_);
v_zero_46_ = lean_unsigned_to_nat(0u);
v_isZero_47_ = lean_nat_dec_eq(v___x_45_, v_zero_46_);
if (v_isZero_47_ == 1)
{
lean_object* v___x_48_; 
lean_dec(v___x_45_);
v___x_48_ = lean_box(0);
return v___x_48_;
}
else
{
lean_object* v_one_49_; lean_object* v_n_50_; lean_object* v___x_51_; 
v_one_49_ = lean_unsigned_to_nat(1u);
v_n_50_ = lean_nat_sub(v___x_45_, v_one_49_);
lean_dec(v___x_45_);
v___x_51_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_51_, 0, v_n_50_);
return v___x_51_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ImportedConsts_findConstModIdxCached_x3f___boxed(lean_object* v_t_52_, lean_object* v_n_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l_Lean_ImportedConsts_findConstModIdxCached_x3f(v_t_52_, v_n_53_);
lean_dec(v_n_53_);
lean_dec_ref(v_t_52_);
return v_res_54_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstMap___closed__0(void){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = l_Lean_ImportedConsts_empty___redArg();
return v___x_55_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstMap___closed__1(void){
_start:
{
lean_object* v___x_56_; 
v___x_56_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_56_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstMap___closed__2(void){
_start:
{
lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_57_ = lean_obj_once(&l_Lean_instInhabitedConstMap___closed__1, &l_Lean_instInhabitedConstMap___closed__1_once, _init_l_Lean_instInhabitedConstMap___closed__1);
v___x_58_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_58_, 0, v___x_57_);
return v___x_58_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstMap___closed__3(void){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_59_ = lean_obj_once(&l_Lean_instInhabitedConstMap___closed__2, &l_Lean_instInhabitedConstMap___closed__2_once, _init_l_Lean_instInhabitedConstMap___closed__2);
v___x_60_ = lean_obj_once(&l_Lean_instInhabitedConstMap___closed__0, &l_Lean_instInhabitedConstMap___closed__0_once, _init_l_Lean_instInhabitedConstMap___closed__0);
v___x_61_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_61_, 0, v___x_60_);
lean_ctor_set(v___x_61_, 1, v___x_59_);
return v___x_61_;
}
}
static lean_object* _init_l_Lean_instInhabitedConstMap(void){
_start:
{
lean_object* v___x_62_; 
v___x_62_ = lean_obj_once(&l_Lean_instInhabitedConstMap___closed__3, &l_Lean_instInhabitedConstMap___closed__3_once, _init_l_Lean_instInhabitedConstMap___closed__3);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ConstMap_find_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_63_, lean_object* v_vals_64_, lean_object* v_i_65_, lean_object* v_k_66_){
_start:
{
lean_object* v___x_67_; uint8_t v___x_68_; 
v___x_67_ = lean_array_get_size(v_keys_63_);
v___x_68_ = lean_nat_dec_lt(v_i_65_, v___x_67_);
if (v___x_68_ == 0)
{
lean_object* v___x_69_; 
lean_dec(v_i_65_);
v___x_69_ = lean_box(0);
return v___x_69_;
}
else
{
lean_object* v_k_x27_70_; uint8_t v___x_71_; 
v_k_x27_70_ = lean_array_fget_borrowed(v_keys_63_, v_i_65_);
v___x_71_ = lean_name_eq(v_k_66_, v_k_x27_70_);
if (v___x_71_ == 0)
{
lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_72_ = lean_unsigned_to_nat(1u);
v___x_73_ = lean_nat_add(v_i_65_, v___x_72_);
lean_dec(v_i_65_);
v_i_65_ = v___x_73_;
goto _start;
}
else
{
lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_75_ = lean_array_fget_borrowed(v_vals_64_, v_i_65_);
lean_dec(v_i_65_);
lean_inc(v___x_75_);
v___x_76_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_76_, 0, v___x_75_);
return v___x_76_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ConstMap_find_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_77_, lean_object* v_vals_78_, lean_object* v_i_79_, lean_object* v_k_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ConstMap_find_x3f_spec__0_spec__0_spec__1___redArg(v_keys_77_, v_vals_78_, v_i_79_, v_k_80_);
lean_dec(v_k_80_);
lean_dec_ref(v_vals_78_);
lean_dec_ref(v_keys_77_);
return v_res_81_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ConstMap_find_x3f_spec__0_spec__0___redArg(lean_object* v_x_82_, size_t v_x_83_, lean_object* v_x_84_){
_start:
{
if (lean_obj_tag(v_x_82_) == 0)
{
lean_object* v_es_85_; lean_object* v___x_86_; size_t v___x_87_; size_t v___x_88_; lean_object* v_j_89_; lean_object* v___x_90_; 
v_es_85_ = lean_ctor_get(v_x_82_, 0);
v___x_86_ = lean_box(2);
v___x_87_ = ((size_t)31ULL);
v___x_88_ = lean_usize_land(v_x_83_, v___x_87_);
v_j_89_ = lean_usize_to_nat(v___x_88_);
v___x_90_ = lean_array_get_borrowed(v___x_86_, v_es_85_, v_j_89_);
lean_dec(v_j_89_);
switch(lean_obj_tag(v___x_90_))
{
case 0:
{
lean_object* v_key_91_; lean_object* v_val_92_; uint8_t v___x_93_; 
v_key_91_ = lean_ctor_get(v___x_90_, 0);
v_val_92_ = lean_ctor_get(v___x_90_, 1);
v___x_93_ = lean_name_eq(v_x_84_, v_key_91_);
if (v___x_93_ == 0)
{
lean_object* v___x_94_; 
v___x_94_ = lean_box(0);
return v___x_94_;
}
else
{
lean_object* v___x_95_; 
lean_inc(v_val_92_);
v___x_95_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_95_, 0, v_val_92_);
return v___x_95_;
}
}
case 1:
{
lean_object* v_node_96_; size_t v___x_97_; size_t v___x_98_; 
v_node_96_ = lean_ctor_get(v___x_90_, 0);
v___x_97_ = ((size_t)5ULL);
v___x_98_ = lean_usize_shift_right(v_x_83_, v___x_97_);
v_x_82_ = v_node_96_;
v_x_83_ = v___x_98_;
goto _start;
}
default: 
{
lean_object* v___x_100_; 
v___x_100_ = lean_box(0);
return v___x_100_;
}
}
}
else
{
lean_object* v_ks_101_; lean_object* v_vs_102_; lean_object* v___x_103_; lean_object* v___x_104_; 
v_ks_101_ = lean_ctor_get(v_x_82_, 0);
v_vs_102_ = lean_ctor_get(v_x_82_, 1);
v___x_103_ = lean_unsigned_to_nat(0u);
v___x_104_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ConstMap_find_x3f_spec__0_spec__0_spec__1___redArg(v_ks_101_, v_vs_102_, v___x_103_, v_x_84_);
return v___x_104_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ConstMap_find_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_105_, lean_object* v_x_106_, lean_object* v_x_107_){
_start:
{
size_t v_x_175__boxed_108_; lean_object* v_res_109_; 
v_x_175__boxed_108_ = lean_unbox_usize(v_x_106_);
lean_dec(v_x_106_);
v_res_109_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ConstMap_find_x3f_spec__0_spec__0___redArg(v_x_105_, v_x_175__boxed_108_, v_x_107_);
lean_dec(v_x_107_);
lean_dec_ref(v_x_105_);
return v_res_109_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_ConstMap_find_x3f_spec__0___redArg(lean_object* v_x_110_, lean_object* v_x_111_){
_start:
{
uint64_t v___y_113_; 
if (lean_obj_tag(v_x_111_) == 0)
{
uint64_t v___x_116_; 
v___x_116_ = 1723ULL;
v___y_113_ = v___x_116_;
goto v___jp_112_;
}
else
{
uint64_t v_hash_117_; 
v_hash_117_ = lean_ctor_get_uint64(v_x_111_, sizeof(void*)*2);
v___y_113_ = v_hash_117_;
goto v___jp_112_;
}
v___jp_112_:
{
size_t v___x_114_; lean_object* v___x_115_; 
v___x_114_ = lean_uint64_to_usize(v___y_113_);
v___x_115_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ConstMap_find_x3f_spec__0_spec__0___redArg(v_x_110_, v___x_114_, v_x_111_);
return v___x_115_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_ConstMap_find_x3f_spec__0___redArg___boxed(lean_object* v_x_118_, lean_object* v_x_119_){
_start:
{
lean_object* v_res_120_; 
v_res_120_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_ConstMap_find_x3f_spec__0___redArg(v_x_118_, v_x_119_);
lean_dec(v_x_119_);
lean_dec_ref(v_x_118_);
return v_res_120_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstMap_find_x3f(lean_object* v_m_121_, lean_object* v_n_122_){
_start:
{
lean_object* v_map_u2081_123_; lean_object* v_map_u2082_124_; lean_object* v___x_125_; 
v_map_u2081_123_ = lean_ctor_get(v_m_121_, 0);
v_map_u2082_124_ = lean_ctor_get(v_m_121_, 1);
v___x_125_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_ConstMap_find_x3f_spec__0___redArg(v_map_u2082_124_, v_n_122_);
if (lean_obj_tag(v___x_125_) == 0)
{
lean_object* v_cache_x3f_126_; lean_object* v___x_127_; 
v_cache_x3f_126_ = lean_ctor_get(v_map_u2081_123_, 0);
v___x_127_ = lean_imported_consts_find_entry_cached(v_cache_x3f_126_, v_map_u2081_123_, v_n_122_);
if (lean_obj_tag(v___x_127_) == 0)
{
return v___x_125_;
}
else
{
lean_object* v_val_128_; lean_object* v___x_130_; uint8_t v_isShared_131_; uint8_t v_isSharedCheck_136_; 
v_val_128_ = lean_ctor_get(v___x_127_, 0);
v_isSharedCheck_136_ = !lean_is_exclusive(v___x_127_);
if (v_isSharedCheck_136_ == 0)
{
v___x_130_ = v___x_127_;
v_isShared_131_ = v_isSharedCheck_136_;
goto v_resetjp_129_;
}
else
{
lean_inc(v_val_128_);
lean_dec(v___x_127_);
v___x_130_ = lean_box(0);
v_isShared_131_ = v_isSharedCheck_136_;
goto v_resetjp_129_;
}
v_resetjp_129_:
{
lean_object* v_fst_132_; lean_object* v___x_134_; 
v_fst_132_ = lean_ctor_get(v_val_128_, 0);
lean_inc(v_fst_132_);
lean_dec(v_val_128_);
if (v_isShared_131_ == 0)
{
lean_ctor_set(v___x_130_, 0, v_fst_132_);
v___x_134_ = v___x_130_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_135_; 
v_reuseFailAlloc_135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_135_, 0, v_fst_132_);
v___x_134_ = v_reuseFailAlloc_135_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
return v___x_134_;
}
}
}
}
else
{
return v___x_125_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstMap_find_x3f___boxed(lean_object* v_m_137_, lean_object* v_n_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l_Lean_ConstMap_find_x3f(v_m_137_, v_n_138_);
lean_dec(v_n_138_);
lean_dec_ref(v_m_137_);
return v_res_139_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_ConstMap_find_x3f_spec__0(lean_object* v_00_u03b2_140_, lean_object* v_x_141_, lean_object* v_x_142_){
_start:
{
lean_object* v___x_143_; 
v___x_143_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_ConstMap_find_x3f_spec__0___redArg(v_x_141_, v_x_142_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_ConstMap_find_x3f_spec__0___boxed(lean_object* v_00_u03b2_144_, lean_object* v_x_145_, lean_object* v_x_146_){
_start:
{
lean_object* v_res_147_; 
v_res_147_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_ConstMap_find_x3f_spec__0(v_00_u03b2_144_, v_x_145_, v_x_146_);
lean_dec(v_x_146_);
lean_dec_ref(v_x_145_);
return v_res_147_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ConstMap_find_x3f_spec__0_spec__0(lean_object* v_00_u03b2_148_, lean_object* v_x_149_, size_t v_x_150_, lean_object* v_x_151_){
_start:
{
lean_object* v___x_152_; 
v___x_152_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ConstMap_find_x3f_spec__0_spec__0___redArg(v_x_149_, v_x_150_, v_x_151_);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ConstMap_find_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_153_, lean_object* v_x_154_, lean_object* v_x_155_, lean_object* v_x_156_){
_start:
{
size_t v_x_267__boxed_157_; lean_object* v_res_158_; 
v_x_267__boxed_157_ = lean_unbox_usize(v_x_155_);
lean_dec(v_x_155_);
v_res_158_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ConstMap_find_x3f_spec__0_spec__0(v_00_u03b2_153_, v_x_154_, v_x_267__boxed_157_, v_x_156_);
lean_dec(v_x_156_);
lean_dec_ref(v_x_154_);
return v_res_158_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ConstMap_find_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_159_, lean_object* v_keys_160_, lean_object* v_vals_161_, lean_object* v_heq_162_, lean_object* v_i_163_, lean_object* v_k_164_){
_start:
{
lean_object* v___x_165_; 
v___x_165_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ConstMap_find_x3f_spec__0_spec__0_spec__1___redArg(v_keys_160_, v_vals_161_, v_i_163_, v_k_164_);
return v___x_165_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ConstMap_find_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_166_, lean_object* v_keys_167_, lean_object* v_vals_168_, lean_object* v_heq_169_, lean_object* v_i_170_, lean_object* v_k_171_){
_start:
{
lean_object* v_res_172_; 
v_res_172_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_ConstMap_find_x3f_spec__0_spec__0_spec__1(v_00_u03b2_166_, v_keys_167_, v_vals_168_, v_heq_169_, v_i_170_, v_k_171_);
lean_dec(v_k_171_);
lean_dec_ref(v_vals_168_);
lean_dec_ref(v_keys_167_);
return v_res_172_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstMap_find_x3f_x27(lean_object* v_m_173_, lean_object* v_n_174_){
_start:
{
lean_object* v_map_u2081_175_; lean_object* v_map_u2082_176_; lean_object* v_cache_x3f_177_; lean_object* v___x_178_; 
v_map_u2081_175_ = lean_ctor_get(v_m_173_, 0);
v_map_u2082_176_ = lean_ctor_get(v_m_173_, 1);
v_cache_x3f_177_ = lean_ctor_get(v_map_u2081_175_, 0);
v___x_178_ = lean_imported_consts_find_entry_cached(v_cache_x3f_177_, v_map_u2081_175_, v_n_174_);
if (lean_obj_tag(v___x_178_) == 0)
{
lean_object* v___x_179_; 
v___x_179_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_ConstMap_find_x3f_spec__0___redArg(v_map_u2082_176_, v_n_174_);
return v___x_179_;
}
else
{
lean_object* v_val_180_; lean_object* v___x_182_; uint8_t v_isShared_183_; uint8_t v_isSharedCheck_188_; 
v_val_180_ = lean_ctor_get(v___x_178_, 0);
v_isSharedCheck_188_ = !lean_is_exclusive(v___x_178_);
if (v_isSharedCheck_188_ == 0)
{
v___x_182_ = v___x_178_;
v_isShared_183_ = v_isSharedCheck_188_;
goto v_resetjp_181_;
}
else
{
lean_inc(v_val_180_);
lean_dec(v___x_178_);
v___x_182_ = lean_box(0);
v_isShared_183_ = v_isSharedCheck_188_;
goto v_resetjp_181_;
}
v_resetjp_181_:
{
lean_object* v_fst_184_; lean_object* v___x_186_; 
v_fst_184_ = lean_ctor_get(v_val_180_, 0);
lean_inc(v_fst_184_);
lean_dec(v_val_180_);
if (v_isShared_183_ == 0)
{
lean_ctor_set(v___x_182_, 0, v_fst_184_);
v___x_186_ = v___x_182_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_187_; 
v_reuseFailAlloc_187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_187_, 0, v_fst_184_);
v___x_186_ = v_reuseFailAlloc_187_;
goto v_reusejp_185_;
}
v_reusejp_185_:
{
return v___x_186_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstMap_find_x3f_x27___boxed(lean_object* v_m_189_, lean_object* v_n_190_){
_start:
{
lean_object* v_res_191_; 
v_res_191_ = l_Lean_ConstMap_find_x3f_x27(v_m_189_, v_n_190_);
lean_dec(v_n_190_);
lean_dec_ref(v_m_189_);
return v_res_191_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_ConstMap_contains_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_192_, lean_object* v_i_193_, lean_object* v_k_194_){
_start:
{
lean_object* v___x_195_; uint8_t v___x_196_; 
v___x_195_ = lean_array_get_size(v_keys_192_);
v___x_196_ = lean_nat_dec_lt(v_i_193_, v___x_195_);
if (v___x_196_ == 0)
{
lean_dec(v_i_193_);
return v___x_196_;
}
else
{
lean_object* v_k_x27_197_; uint8_t v___x_198_; 
v_k_x27_197_ = lean_array_fget_borrowed(v_keys_192_, v_i_193_);
v___x_198_ = lean_name_eq(v_k_194_, v_k_x27_197_);
if (v___x_198_ == 0)
{
lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_199_ = lean_unsigned_to_nat(1u);
v___x_200_ = lean_nat_add(v_i_193_, v___x_199_);
lean_dec(v_i_193_);
v_i_193_ = v___x_200_;
goto _start;
}
else
{
lean_dec(v_i_193_);
return v___x_196_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_ConstMap_contains_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_202_, lean_object* v_i_203_, lean_object* v_k_204_){
_start:
{
uint8_t v_res_205_; lean_object* v_r_206_; 
v_res_205_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_ConstMap_contains_spec__0_spec__0_spec__1___redArg(v_keys_202_, v_i_203_, v_k_204_);
lean_dec(v_k_204_);
lean_dec_ref(v_keys_202_);
v_r_206_ = lean_box(v_res_205_);
return v_r_206_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_ConstMap_contains_spec__0_spec__0___redArg(lean_object* v_x_207_, size_t v_x_208_, lean_object* v_x_209_){
_start:
{
if (lean_obj_tag(v_x_207_) == 0)
{
lean_object* v_es_210_; lean_object* v___x_211_; size_t v___x_212_; size_t v___x_213_; lean_object* v_j_214_; lean_object* v___x_215_; 
v_es_210_ = lean_ctor_get(v_x_207_, 0);
v___x_211_ = lean_box(2);
v___x_212_ = ((size_t)31ULL);
v___x_213_ = lean_usize_land(v_x_208_, v___x_212_);
v_j_214_ = lean_usize_to_nat(v___x_213_);
v___x_215_ = lean_array_get_borrowed(v___x_211_, v_es_210_, v_j_214_);
lean_dec(v_j_214_);
switch(lean_obj_tag(v___x_215_))
{
case 0:
{
lean_object* v_key_216_; uint8_t v___x_217_; 
v_key_216_ = lean_ctor_get(v___x_215_, 0);
v___x_217_ = lean_name_eq(v_x_209_, v_key_216_);
return v___x_217_;
}
case 1:
{
lean_object* v_node_218_; size_t v___x_219_; size_t v___x_220_; 
v_node_218_ = lean_ctor_get(v___x_215_, 0);
v___x_219_ = ((size_t)5ULL);
v___x_220_ = lean_usize_shift_right(v_x_208_, v___x_219_);
v_x_207_ = v_node_218_;
v_x_208_ = v___x_220_;
goto _start;
}
default: 
{
uint8_t v___x_222_; 
v___x_222_ = 0;
return v___x_222_;
}
}
}
else
{
lean_object* v_ks_223_; lean_object* v___x_224_; uint8_t v___x_225_; 
v_ks_223_ = lean_ctor_get(v_x_207_, 0);
v___x_224_ = lean_unsigned_to_nat(0u);
v___x_225_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_ConstMap_contains_spec__0_spec__0_spec__1___redArg(v_ks_223_, v___x_224_, v_x_209_);
return v___x_225_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_ConstMap_contains_spec__0_spec__0___redArg___boxed(lean_object* v_x_226_, lean_object* v_x_227_, lean_object* v_x_228_){
_start:
{
size_t v_x_170__boxed_229_; uint8_t v_res_230_; lean_object* v_r_231_; 
v_x_170__boxed_229_ = lean_unbox_usize(v_x_227_);
lean_dec(v_x_227_);
v_res_230_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_ConstMap_contains_spec__0_spec__0___redArg(v_x_226_, v_x_170__boxed_229_, v_x_228_);
lean_dec(v_x_228_);
lean_dec_ref(v_x_226_);
v_r_231_ = lean_box(v_res_230_);
return v_r_231_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_ConstMap_contains_spec__0___redArg(lean_object* v_x_232_, lean_object* v_x_233_){
_start:
{
uint64_t v___y_235_; 
if (lean_obj_tag(v_x_233_) == 0)
{
uint64_t v___x_238_; 
v___x_238_ = 1723ULL;
v___y_235_ = v___x_238_;
goto v___jp_234_;
}
else
{
uint64_t v_hash_239_; 
v_hash_239_ = lean_ctor_get_uint64(v_x_233_, sizeof(void*)*2);
v___y_235_ = v_hash_239_;
goto v___jp_234_;
}
v___jp_234_:
{
size_t v___x_236_; uint8_t v___x_237_; 
v___x_236_ = lean_uint64_to_usize(v___y_235_);
v___x_237_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_ConstMap_contains_spec__0_spec__0___redArg(v_x_232_, v___x_236_, v_x_233_);
return v___x_237_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_ConstMap_contains_spec__0___redArg___boxed(lean_object* v_x_240_, lean_object* v_x_241_){
_start:
{
uint8_t v_res_242_; lean_object* v_r_243_; 
v_res_242_ = l_Lean_PersistentHashMap_contains___at___00Lean_ConstMap_contains_spec__0___redArg(v_x_240_, v_x_241_);
lean_dec(v_x_241_);
lean_dec_ref(v_x_240_);
v_r_243_ = lean_box(v_res_242_);
return v_r_243_;
}
}
LEAN_EXPORT uint8_t l_Lean_ConstMap_contains(lean_object* v_m_244_, lean_object* v_n_245_){
_start:
{
lean_object* v_map_u2081_246_; lean_object* v_map_u2082_247_; uint8_t v___x_248_; 
v_map_u2081_246_ = lean_ctor_get(v_m_244_, 0);
v_map_u2082_247_ = lean_ctor_get(v_m_244_, 1);
v___x_248_ = l_Lean_PersistentHashMap_contains___at___00Lean_ConstMap_contains_spec__0___redArg(v_map_u2082_247_, v_n_245_);
if (v___x_248_ == 0)
{
lean_object* v_cache_x3f_249_; lean_object* v___x_250_; 
v_cache_x3f_249_ = lean_ctor_get(v_map_u2081_246_, 0);
v___x_250_ = lean_imported_consts_find_entry_cached(v_cache_x3f_249_, v_map_u2081_246_, v_n_245_);
if (lean_obj_tag(v___x_250_) == 0)
{
return v___x_248_;
}
else
{
uint8_t v___x_251_; 
lean_dec_ref_known(v___x_250_, 1);
v___x_251_ = 1;
return v___x_251_;
}
}
else
{
return v___x_248_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstMap_contains___boxed(lean_object* v_m_252_, lean_object* v_n_253_){
_start:
{
uint8_t v_res_254_; lean_object* v_r_255_; 
v_res_254_ = l_Lean_ConstMap_contains(v_m_252_, v_n_253_);
lean_dec(v_n_253_);
lean_dec_ref(v_m_252_);
v_r_255_ = lean_box(v_res_254_);
return v_r_255_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_ConstMap_contains_spec__0(lean_object* v_00_u03b2_256_, lean_object* v_x_257_, lean_object* v_x_258_){
_start:
{
uint8_t v___x_259_; 
v___x_259_ = l_Lean_PersistentHashMap_contains___at___00Lean_ConstMap_contains_spec__0___redArg(v_x_257_, v_x_258_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_ConstMap_contains_spec__0___boxed(lean_object* v_00_u03b2_260_, lean_object* v_x_261_, lean_object* v_x_262_){
_start:
{
uint8_t v_res_263_; lean_object* v_r_264_; 
v_res_263_ = l_Lean_PersistentHashMap_contains___at___00Lean_ConstMap_contains_spec__0(v_00_u03b2_260_, v_x_261_, v_x_262_);
lean_dec(v_x_262_);
lean_dec_ref(v_x_261_);
v_r_264_ = lean_box(v_res_263_);
return v_r_264_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_ConstMap_contains_spec__0_spec__0(lean_object* v_00_u03b2_265_, lean_object* v_x_266_, size_t v_x_267_, lean_object* v_x_268_){
_start:
{
uint8_t v___x_269_; 
v___x_269_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_ConstMap_contains_spec__0_spec__0___redArg(v_x_266_, v_x_267_, v_x_268_);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_ConstMap_contains_spec__0_spec__0___boxed(lean_object* v_00_u03b2_270_, lean_object* v_x_271_, lean_object* v_x_272_, lean_object* v_x_273_){
_start:
{
size_t v_x_242__boxed_274_; uint8_t v_res_275_; lean_object* v_r_276_; 
v_x_242__boxed_274_ = lean_unbox_usize(v_x_272_);
lean_dec(v_x_272_);
v_res_275_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_ConstMap_contains_spec__0_spec__0(v_00_u03b2_270_, v_x_271_, v_x_242__boxed_274_, v_x_273_);
lean_dec(v_x_273_);
lean_dec_ref(v_x_271_);
v_r_276_ = lean_box(v_res_275_);
return v_r_276_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_ConstMap_contains_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_277_, lean_object* v_keys_278_, lean_object* v_vals_279_, lean_object* v_heq_280_, lean_object* v_i_281_, lean_object* v_k_282_){
_start:
{
uint8_t v___x_283_; 
v___x_283_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_ConstMap_contains_spec__0_spec__0_spec__1___redArg(v_keys_278_, v_i_281_, v_k_282_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_ConstMap_contains_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_284_, lean_object* v_keys_285_, lean_object* v_vals_286_, lean_object* v_heq_287_, lean_object* v_i_288_, lean_object* v_k_289_){
_start:
{
uint8_t v_res_290_; lean_object* v_r_291_; 
v_res_290_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_ConstMap_contains_spec__0_spec__0_spec__1(v_00_u03b2_284_, v_keys_285_, v_vals_286_, v_heq_287_, v_i_288_, v_k_289_);
lean_dec(v_k_289_);
lean_dec_ref(v_vals_286_);
lean_dec_ref(v_keys_285_);
v_r_291_ = lean_box(v_res_290_);
return v_r_291_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ConstMap_insert_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_292_, lean_object* v_x_293_, lean_object* v_x_294_, lean_object* v_x_295_){
_start:
{
lean_object* v_ks_296_; lean_object* v_vs_297_; lean_object* v___x_299_; uint8_t v_isShared_300_; uint8_t v_isSharedCheck_321_; 
v_ks_296_ = lean_ctor_get(v_x_292_, 0);
v_vs_297_ = lean_ctor_get(v_x_292_, 1);
v_isSharedCheck_321_ = !lean_is_exclusive(v_x_292_);
if (v_isSharedCheck_321_ == 0)
{
v___x_299_ = v_x_292_;
v_isShared_300_ = v_isSharedCheck_321_;
goto v_resetjp_298_;
}
else
{
lean_inc(v_vs_297_);
lean_inc(v_ks_296_);
lean_dec(v_x_292_);
v___x_299_ = lean_box(0);
v_isShared_300_ = v_isSharedCheck_321_;
goto v_resetjp_298_;
}
v_resetjp_298_:
{
lean_object* v___x_301_; uint8_t v___x_302_; 
v___x_301_ = lean_array_get_size(v_ks_296_);
v___x_302_ = lean_nat_dec_lt(v_x_293_, v___x_301_);
if (v___x_302_ == 0)
{
lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_306_; 
lean_dec(v_x_293_);
v___x_303_ = lean_array_push(v_ks_296_, v_x_294_);
v___x_304_ = lean_array_push(v_vs_297_, v_x_295_);
if (v_isShared_300_ == 0)
{
lean_ctor_set(v___x_299_, 1, v___x_304_);
lean_ctor_set(v___x_299_, 0, v___x_303_);
v___x_306_ = v___x_299_;
goto v_reusejp_305_;
}
else
{
lean_object* v_reuseFailAlloc_307_; 
v_reuseFailAlloc_307_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_307_, 0, v___x_303_);
lean_ctor_set(v_reuseFailAlloc_307_, 1, v___x_304_);
v___x_306_ = v_reuseFailAlloc_307_;
goto v_reusejp_305_;
}
v_reusejp_305_:
{
return v___x_306_;
}
}
else
{
lean_object* v_k_x27_308_; uint8_t v___x_309_; 
v_k_x27_308_ = lean_array_fget_borrowed(v_ks_296_, v_x_293_);
v___x_309_ = lean_name_eq(v_x_294_, v_k_x27_308_);
if (v___x_309_ == 0)
{
lean_object* v___x_311_; 
if (v_isShared_300_ == 0)
{
v___x_311_ = v___x_299_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v_ks_296_);
lean_ctor_set(v_reuseFailAlloc_315_, 1, v_vs_297_);
v___x_311_ = v_reuseFailAlloc_315_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_312_ = lean_unsigned_to_nat(1u);
v___x_313_ = lean_nat_add(v_x_293_, v___x_312_);
lean_dec(v_x_293_);
v_x_292_ = v___x_311_;
v_x_293_ = v___x_313_;
goto _start;
}
}
else
{
lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_319_; 
v___x_316_ = lean_array_fset(v_ks_296_, v_x_293_, v_x_294_);
v___x_317_ = lean_array_fset(v_vs_297_, v_x_293_, v_x_295_);
lean_dec(v_x_293_);
if (v_isShared_300_ == 0)
{
lean_ctor_set(v___x_299_, 1, v___x_317_);
lean_ctor_set(v___x_299_, 0, v___x_316_);
v___x_319_ = v___x_299_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v___x_316_);
lean_ctor_set(v_reuseFailAlloc_320_, 1, v___x_317_);
v___x_319_ = v_reuseFailAlloc_320_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
return v___x_319_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ConstMap_insert_spec__0_spec__0_spec__1___redArg(lean_object* v_n_322_, lean_object* v_k_323_, lean_object* v_v_324_){
_start:
{
lean_object* v___x_325_; lean_object* v___x_326_; 
v___x_325_ = lean_unsigned_to_nat(0u);
v___x_326_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ConstMap_insert_spec__0_spec__0_spec__1_spec__2___redArg(v_n_322_, v___x_325_, v_k_323_, v_v_324_);
return v___x_326_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ConstMap_insert_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_327_; 
v___x_327_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_327_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ConstMap_insert_spec__0_spec__0___redArg(lean_object* v_x_328_, size_t v_x_329_, size_t v_x_330_, lean_object* v_x_331_, lean_object* v_x_332_){
_start:
{
if (lean_obj_tag(v_x_328_) == 0)
{
lean_object* v_es_333_; size_t v___x_334_; size_t v___x_335_; lean_object* v_j_336_; lean_object* v___x_337_; uint8_t v___x_338_; 
v_es_333_ = lean_ctor_get(v_x_328_, 0);
v___x_334_ = ((size_t)31ULL);
v___x_335_ = lean_usize_land(v_x_329_, v___x_334_);
v_j_336_ = lean_usize_to_nat(v___x_335_);
v___x_337_ = lean_array_get_size(v_es_333_);
v___x_338_ = lean_nat_dec_lt(v_j_336_, v___x_337_);
if (v___x_338_ == 0)
{
lean_dec(v_j_336_);
lean_dec(v_x_332_);
lean_dec(v_x_331_);
return v_x_328_;
}
else
{
lean_object* v___x_340_; uint8_t v_isShared_341_; uint8_t v_isSharedCheck_377_; 
lean_inc_ref(v_es_333_);
v_isSharedCheck_377_ = !lean_is_exclusive(v_x_328_);
if (v_isSharedCheck_377_ == 0)
{
lean_object* v_unused_378_; 
v_unused_378_ = lean_ctor_get(v_x_328_, 0);
lean_dec(v_unused_378_);
v___x_340_ = v_x_328_;
v_isShared_341_ = v_isSharedCheck_377_;
goto v_resetjp_339_;
}
else
{
lean_dec(v_x_328_);
v___x_340_ = lean_box(0);
v_isShared_341_ = v_isSharedCheck_377_;
goto v_resetjp_339_;
}
v_resetjp_339_:
{
lean_object* v_v_342_; lean_object* v___x_343_; lean_object* v_xs_x27_344_; lean_object* v___y_346_; 
v_v_342_ = lean_array_fget(v_es_333_, v_j_336_);
v___x_343_ = lean_box(0);
v_xs_x27_344_ = lean_array_fset(v_es_333_, v_j_336_, v___x_343_);
switch(lean_obj_tag(v_v_342_))
{
case 0:
{
lean_object* v_key_351_; lean_object* v_val_352_; lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_362_; 
v_key_351_ = lean_ctor_get(v_v_342_, 0);
v_val_352_ = lean_ctor_get(v_v_342_, 1);
v_isSharedCheck_362_ = !lean_is_exclusive(v_v_342_);
if (v_isSharedCheck_362_ == 0)
{
v___x_354_ = v_v_342_;
v_isShared_355_ = v_isSharedCheck_362_;
goto v_resetjp_353_;
}
else
{
lean_inc(v_val_352_);
lean_inc(v_key_351_);
lean_dec(v_v_342_);
v___x_354_ = lean_box(0);
v_isShared_355_ = v_isSharedCheck_362_;
goto v_resetjp_353_;
}
v_resetjp_353_:
{
uint8_t v___x_356_; 
v___x_356_ = lean_name_eq(v_x_331_, v_key_351_);
if (v___x_356_ == 0)
{
lean_object* v___x_357_; lean_object* v___x_358_; 
lean_del_object(v___x_354_);
v___x_357_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_351_, v_val_352_, v_x_331_, v_x_332_);
v___x_358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_358_, 0, v___x_357_);
v___y_346_ = v___x_358_;
goto v___jp_345_;
}
else
{
lean_object* v___x_360_; 
lean_dec(v_val_352_);
lean_dec(v_key_351_);
if (v_isShared_355_ == 0)
{
lean_ctor_set(v___x_354_, 1, v_x_332_);
lean_ctor_set(v___x_354_, 0, v_x_331_);
v___x_360_ = v___x_354_;
goto v_reusejp_359_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v_x_331_);
lean_ctor_set(v_reuseFailAlloc_361_, 1, v_x_332_);
v___x_360_ = v_reuseFailAlloc_361_;
goto v_reusejp_359_;
}
v_reusejp_359_:
{
v___y_346_ = v___x_360_;
goto v___jp_345_;
}
}
}
}
case 1:
{
lean_object* v_node_363_; lean_object* v___x_365_; uint8_t v_isShared_366_; uint8_t v_isSharedCheck_375_; 
v_node_363_ = lean_ctor_get(v_v_342_, 0);
v_isSharedCheck_375_ = !lean_is_exclusive(v_v_342_);
if (v_isSharedCheck_375_ == 0)
{
v___x_365_ = v_v_342_;
v_isShared_366_ = v_isSharedCheck_375_;
goto v_resetjp_364_;
}
else
{
lean_inc(v_node_363_);
lean_dec(v_v_342_);
v___x_365_ = lean_box(0);
v_isShared_366_ = v_isSharedCheck_375_;
goto v_resetjp_364_;
}
v_resetjp_364_:
{
size_t v___x_367_; size_t v___x_368_; size_t v___x_369_; size_t v___x_370_; lean_object* v___x_371_; lean_object* v___x_373_; 
v___x_367_ = ((size_t)5ULL);
v___x_368_ = lean_usize_shift_right(v_x_329_, v___x_367_);
v___x_369_ = ((size_t)1ULL);
v___x_370_ = lean_usize_add(v_x_330_, v___x_369_);
v___x_371_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ConstMap_insert_spec__0_spec__0___redArg(v_node_363_, v___x_368_, v___x_370_, v_x_331_, v_x_332_);
if (v_isShared_366_ == 0)
{
lean_ctor_set(v___x_365_, 0, v___x_371_);
v___x_373_ = v___x_365_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v___x_371_);
v___x_373_ = v_reuseFailAlloc_374_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
v___y_346_ = v___x_373_;
goto v___jp_345_;
}
}
}
default: 
{
lean_object* v___x_376_; 
v___x_376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_376_, 0, v_x_331_);
lean_ctor_set(v___x_376_, 1, v_x_332_);
v___y_346_ = v___x_376_;
goto v___jp_345_;
}
}
v___jp_345_:
{
lean_object* v___x_347_; lean_object* v___x_349_; 
v___x_347_ = lean_array_fset(v_xs_x27_344_, v_j_336_, v___y_346_);
lean_dec(v_j_336_);
if (v_isShared_341_ == 0)
{
lean_ctor_set(v___x_340_, 0, v___x_347_);
v___x_349_ = v___x_340_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v___x_347_);
v___x_349_ = v_reuseFailAlloc_350_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
return v___x_349_;
}
}
}
}
}
else
{
lean_object* v_ks_379_; lean_object* v_vs_380_; lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_398_; 
v_ks_379_ = lean_ctor_get(v_x_328_, 0);
v_vs_380_ = lean_ctor_get(v_x_328_, 1);
v_isSharedCheck_398_ = !lean_is_exclusive(v_x_328_);
if (v_isSharedCheck_398_ == 0)
{
v___x_382_ = v_x_328_;
v_isShared_383_ = v_isSharedCheck_398_;
goto v_resetjp_381_;
}
else
{
lean_inc(v_vs_380_);
lean_inc(v_ks_379_);
lean_dec(v_x_328_);
v___x_382_ = lean_box(0);
v_isShared_383_ = v_isSharedCheck_398_;
goto v_resetjp_381_;
}
v_resetjp_381_:
{
lean_object* v___x_385_; 
if (v_isShared_383_ == 0)
{
v___x_385_ = v___x_382_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v_ks_379_);
lean_ctor_set(v_reuseFailAlloc_397_, 1, v_vs_380_);
v___x_385_ = v_reuseFailAlloc_397_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
lean_object* v_newNode_386_; size_t v___x_387_; uint8_t v___x_388_; 
v_newNode_386_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ConstMap_insert_spec__0_spec__0_spec__1___redArg(v___x_385_, v_x_331_, v_x_332_);
v___x_387_ = ((size_t)7ULL);
v___x_388_ = lean_usize_dec_le(v___x_387_, v_x_330_);
if (v___x_388_ == 0)
{
lean_object* v___x_389_; lean_object* v___x_390_; uint8_t v___x_391_; 
v___x_389_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_386_);
v___x_390_ = lean_unsigned_to_nat(4u);
v___x_391_ = lean_nat_dec_lt(v___x_389_, v___x_390_);
lean_dec(v___x_389_);
if (v___x_391_ == 0)
{
lean_object* v_ks_392_; lean_object* v_vs_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; 
v_ks_392_ = lean_ctor_get(v_newNode_386_, 0);
lean_inc_ref(v_ks_392_);
v_vs_393_ = lean_ctor_get(v_newNode_386_, 1);
lean_inc_ref(v_vs_393_);
lean_dec_ref(v_newNode_386_);
v___x_394_ = lean_unsigned_to_nat(0u);
v___x_395_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ConstMap_insert_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ConstMap_insert_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ConstMap_insert_spec__0_spec__0___redArg___closed__0);
v___x_396_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ConstMap_insert_spec__0_spec__0_spec__2___redArg(v_x_330_, v_ks_392_, v_vs_393_, v___x_394_, v___x_395_);
lean_dec_ref(v_vs_393_);
lean_dec_ref(v_ks_392_);
return v___x_396_;
}
else
{
return v_newNode_386_;
}
}
else
{
return v_newNode_386_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ConstMap_insert_spec__0_spec__0_spec__2___redArg(size_t v_depth_399_, lean_object* v_keys_400_, lean_object* v_vals_401_, lean_object* v_i_402_, lean_object* v_entries_403_){
_start:
{
lean_object* v___x_404_; uint8_t v___x_405_; 
v___x_404_ = lean_array_get_size(v_keys_400_);
v___x_405_ = lean_nat_dec_lt(v_i_402_, v___x_404_);
if (v___x_405_ == 0)
{
lean_dec(v_i_402_);
return v_entries_403_;
}
else
{
lean_object* v_k_406_; lean_object* v_v_407_; uint64_t v___y_409_; 
v_k_406_ = lean_array_fget_borrowed(v_keys_400_, v_i_402_);
v_v_407_ = lean_array_fget_borrowed(v_vals_401_, v_i_402_);
if (lean_obj_tag(v_k_406_) == 0)
{
uint64_t v___x_420_; 
v___x_420_ = 1723ULL;
v___y_409_ = v___x_420_;
goto v___jp_408_;
}
else
{
uint64_t v_hash_421_; 
v_hash_421_ = lean_ctor_get_uint64(v_k_406_, sizeof(void*)*2);
v___y_409_ = v_hash_421_;
goto v___jp_408_;
}
v___jp_408_:
{
size_t v_h_410_; size_t v___x_411_; lean_object* v___x_412_; size_t v___x_413_; size_t v___x_414_; size_t v___x_415_; size_t v_h_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
v_h_410_ = lean_uint64_to_usize(v___y_409_);
v___x_411_ = ((size_t)5ULL);
v___x_412_ = lean_unsigned_to_nat(1u);
v___x_413_ = ((size_t)1ULL);
v___x_414_ = lean_usize_sub(v_depth_399_, v___x_413_);
v___x_415_ = lean_usize_mul(v___x_411_, v___x_414_);
v_h_416_ = lean_usize_shift_right(v_h_410_, v___x_415_);
v___x_417_ = lean_nat_add(v_i_402_, v___x_412_);
lean_dec(v_i_402_);
lean_inc(v_v_407_);
lean_inc(v_k_406_);
v___x_418_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ConstMap_insert_spec__0_spec__0___redArg(v_entries_403_, v_h_416_, v_depth_399_, v_k_406_, v_v_407_);
v_i_402_ = v___x_417_;
v_entries_403_ = v___x_418_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ConstMap_insert_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_422_, lean_object* v_keys_423_, lean_object* v_vals_424_, lean_object* v_i_425_, lean_object* v_entries_426_){
_start:
{
size_t v_depth_boxed_427_; lean_object* v_res_428_; 
v_depth_boxed_427_ = lean_unbox_usize(v_depth_422_);
lean_dec(v_depth_422_);
v_res_428_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ConstMap_insert_spec__0_spec__0_spec__2___redArg(v_depth_boxed_427_, v_keys_423_, v_vals_424_, v_i_425_, v_entries_426_);
lean_dec_ref(v_vals_424_);
lean_dec_ref(v_keys_423_);
return v_res_428_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ConstMap_insert_spec__0_spec__0___redArg___boxed(lean_object* v_x_429_, lean_object* v_x_430_, lean_object* v_x_431_, lean_object* v_x_432_, lean_object* v_x_433_){
_start:
{
size_t v_x_359__boxed_434_; size_t v_x_360__boxed_435_; lean_object* v_res_436_; 
v_x_359__boxed_434_ = lean_unbox_usize(v_x_430_);
lean_dec(v_x_430_);
v_x_360__boxed_435_ = lean_unbox_usize(v_x_431_);
lean_dec(v_x_431_);
v_res_436_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ConstMap_insert_spec__0_spec__0___redArg(v_x_429_, v_x_359__boxed_434_, v_x_360__boxed_435_, v_x_432_, v_x_433_);
return v_res_436_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_ConstMap_insert_spec__0___redArg(lean_object* v_x_437_, lean_object* v_x_438_, lean_object* v_x_439_){
_start:
{
uint64_t v___y_441_; 
if (lean_obj_tag(v_x_438_) == 0)
{
uint64_t v___x_445_; 
v___x_445_ = 1723ULL;
v___y_441_ = v___x_445_;
goto v___jp_440_;
}
else
{
uint64_t v_hash_446_; 
v_hash_446_ = lean_ctor_get_uint64(v_x_438_, sizeof(void*)*2);
v___y_441_ = v_hash_446_;
goto v___jp_440_;
}
v___jp_440_:
{
size_t v___x_442_; size_t v___x_443_; lean_object* v___x_444_; 
v___x_442_ = lean_uint64_to_usize(v___y_441_);
v___x_443_ = ((size_t)1ULL);
v___x_444_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ConstMap_insert_spec__0_spec__0___redArg(v_x_437_, v___x_442_, v___x_443_, v_x_438_, v_x_439_);
return v___x_444_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstMap_insert(lean_object* v_m_447_, lean_object* v_n_448_, lean_object* v_v_449_){
_start:
{
lean_object* v_map_u2081_450_; lean_object* v_map_u2082_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_459_; 
v_map_u2081_450_ = lean_ctor_get(v_m_447_, 0);
v_map_u2082_451_ = lean_ctor_get(v_m_447_, 1);
v_isSharedCheck_459_ = !lean_is_exclusive(v_m_447_);
if (v_isSharedCheck_459_ == 0)
{
v___x_453_ = v_m_447_;
v_isShared_454_ = v_isSharedCheck_459_;
goto v_resetjp_452_;
}
else
{
lean_inc(v_map_u2082_451_);
lean_inc(v_map_u2081_450_);
lean_dec(v_m_447_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_459_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
lean_object* v___x_455_; lean_object* v___x_457_; 
v___x_455_ = l_Lean_PersistentHashMap_insert___at___00Lean_ConstMap_insert_spec__0___redArg(v_map_u2082_451_, v_n_448_, v_v_449_);
if (v_isShared_454_ == 0)
{
lean_ctor_set(v___x_453_, 1, v___x_455_);
v___x_457_ = v___x_453_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v_map_u2081_450_);
lean_ctor_set(v_reuseFailAlloc_458_, 1, v___x_455_);
v___x_457_ = v_reuseFailAlloc_458_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
return v___x_457_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_ConstMap_insert_spec__0(lean_object* v_00_u03b2_460_, lean_object* v_x_461_, lean_object* v_x_462_, lean_object* v_x_463_){
_start:
{
lean_object* v___x_464_; 
v___x_464_ = l_Lean_PersistentHashMap_insert___at___00Lean_ConstMap_insert_spec__0___redArg(v_x_461_, v_x_462_, v_x_463_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ConstMap_insert_spec__0_spec__0(lean_object* v_00_u03b2_465_, lean_object* v_x_466_, size_t v_x_467_, size_t v_x_468_, lean_object* v_x_469_, lean_object* v_x_470_){
_start:
{
lean_object* v___x_471_; 
v___x_471_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ConstMap_insert_spec__0_spec__0___redArg(v_x_466_, v_x_467_, v_x_468_, v_x_469_, v_x_470_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ConstMap_insert_spec__0_spec__0___boxed(lean_object* v_00_u03b2_472_, lean_object* v_x_473_, lean_object* v_x_474_, lean_object* v_x_475_, lean_object* v_x_476_, lean_object* v_x_477_){
_start:
{
size_t v_x_555__boxed_478_; size_t v_x_556__boxed_479_; lean_object* v_res_480_; 
v_x_555__boxed_478_ = lean_unbox_usize(v_x_474_);
lean_dec(v_x_474_);
v_x_556__boxed_479_ = lean_unbox_usize(v_x_475_);
lean_dec(v_x_475_);
v_res_480_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ConstMap_insert_spec__0_spec__0(v_00_u03b2_472_, v_x_473_, v_x_555__boxed_478_, v_x_556__boxed_479_, v_x_476_, v_x_477_);
return v_res_480_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ConstMap_insert_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_481_, lean_object* v_n_482_, lean_object* v_k_483_, lean_object* v_v_484_){
_start:
{
lean_object* v___x_485_; 
v___x_485_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ConstMap_insert_spec__0_spec__0_spec__1___redArg(v_n_482_, v_k_483_, v_v_484_);
return v___x_485_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ConstMap_insert_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_486_, size_t v_depth_487_, lean_object* v_keys_488_, lean_object* v_vals_489_, lean_object* v_heq_490_, lean_object* v_i_491_, lean_object* v_entries_492_){
_start:
{
lean_object* v___x_493_; 
v___x_493_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ConstMap_insert_spec__0_spec__0_spec__2___redArg(v_depth_487_, v_keys_488_, v_vals_489_, v_i_491_, v_entries_492_);
return v___x_493_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ConstMap_insert_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_494_, lean_object* v_depth_495_, lean_object* v_keys_496_, lean_object* v_vals_497_, lean_object* v_heq_498_, lean_object* v_i_499_, lean_object* v_entries_500_){
_start:
{
size_t v_depth_boxed_501_; lean_object* v_res_502_; 
v_depth_boxed_501_ = lean_unbox_usize(v_depth_495_);
lean_dec(v_depth_495_);
v_res_502_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ConstMap_insert_spec__0_spec__0_spec__2(v_00_u03b2_494_, v_depth_boxed_501_, v_keys_496_, v_vals_497_, v_heq_498_, v_i_499_, v_entries_500_);
lean_dec_ref(v_vals_497_);
lean_dec_ref(v_keys_496_);
return v_res_502_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ConstMap_insert_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_503_, lean_object* v_x_504_, lean_object* v_x_505_, lean_object* v_x_506_, lean_object* v_x_507_){
_start:
{
lean_object* v___x_508_; 
v___x_508_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_ConstMap_insert_spec__0_spec__0_spec__1_spec__2___redArg(v_x_504_, v_x_505_, v_x_506_, v_x_507_);
return v___x_508_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstMap_foldStage2___redArg(lean_object* v_f_509_, lean_object* v_s_510_, lean_object* v_m_511_){
_start:
{
lean_object* v_map_u2082_512_; lean_object* v___x_513_; 
v_map_u2082_512_ = lean_ctor_get(v_m_511_, 1);
lean_inc_ref(v_map_u2082_512_);
lean_dec_ref(v_m_511_);
v___x_513_ = l_Lean_PersistentHashMap_foldl___redArg(v_map_u2082_512_, v_f_509_, v_s_510_);
return v___x_513_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstMap_foldStage2(lean_object* v_00_u03c3_514_, lean_object* v_f_515_, lean_object* v_s_516_, lean_object* v_m_517_){
_start:
{
lean_object* v_map_u2082_518_; lean_object* v___x_519_; 
v_map_u2082_518_ = lean_ctor_get(v_m_517_, 1);
lean_inc_ref(v_map_u2082_518_);
lean_dec_ref(v_m_517_);
v___x_519_ = l_Lean_PersistentHashMap_foldl___redArg(v_map_u2082_518_, v_f_515_, v_s_516_);
return v___x_519_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstMap_foldM___redArg___lam__0(lean_object* v_inst_520_, lean_object* v_f_521_, lean_object* v_map_u2082_522_, lean_object* v_____do__lift_523_){
_start:
{
lean_object* v___x_524_; 
v___x_524_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_520_, v_f_521_, v_map_u2082_522_, v_____do__lift_523_);
return v___x_524_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstMap_foldM___redArg(lean_object* v_inst_525_, lean_object* v_f_526_, lean_object* v_init_527_, lean_object* v_map_528_){
_start:
{
lean_object* v_toBind_529_; lean_object* v_map_u2081_530_; lean_object* v_map_u2082_531_; lean_object* v___f_532_; lean_object* v___x_533_; lean_object* v___x_534_; 
v_toBind_529_ = lean_ctor_get(v_inst_525_, 1);
lean_inc(v_toBind_529_);
v_map_u2081_530_ = lean_ctor_get(v_map_528_, 0);
lean_inc_ref(v_map_u2081_530_);
v_map_u2082_531_ = lean_ctor_get(v_map_528_, 1);
lean_inc_ref(v_map_u2082_531_);
lean_dec_ref(v_map_528_);
lean_inc(v_f_526_);
lean_inc_ref(v_inst_525_);
v___f_532_ = lean_alloc_closure((void*)(l_Lean_ConstMap_foldM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_532_, 0, v_inst_525_);
lean_closure_set(v___f_532_, 1, v_f_526_);
lean_closure_set(v___f_532_, 2, v_map_u2082_531_);
v___x_533_ = l_Lean_ImportedConsts_foldlM___redArg(v_inst_525_, v_map_u2081_530_, v_f_526_, v_init_527_);
v___x_534_ = lean_apply_4(v_toBind_529_, lean_box(0), lean_box(0), v___x_533_, v___f_532_);
return v___x_534_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstMap_foldM(lean_object* v_00_u03c3_535_, lean_object* v_m_536_, lean_object* v_inst_537_, lean_object* v_f_538_, lean_object* v_init_539_, lean_object* v_map_540_){
_start:
{
lean_object* v___x_541_; 
v___x_541_ = l_Lean_ConstMap_foldM___redArg(v_inst_537_, v_f_538_, v_init_539_, v_map_540_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_ConstMap_fold_spec__0___redArg___lam__0(lean_object* v_f_542_, lean_object* v_x1_543_, lean_object* v_x2_544_, lean_object* v_x3_545_){
_start:
{
lean_object* v___x_546_; 
v___x_546_ = lean_apply_3(v_f_542_, v_x1_543_, v_x2_544_, v_x3_545_);
return v___x_546_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_ConstMap_fold_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_f_547_, lean_object* v_keys_548_, lean_object* v_vals_549_, lean_object* v_i_550_, lean_object* v_acc_551_){
_start:
{
lean_object* v___x_552_; uint8_t v___x_553_; 
v___x_552_ = lean_array_get_size(v_keys_548_);
v___x_553_ = lean_nat_dec_lt(v_i_550_, v___x_552_);
if (v___x_553_ == 0)
{
lean_dec(v_i_550_);
lean_dec(v_f_547_);
return v_acc_551_;
}
else
{
lean_object* v_k_554_; lean_object* v_v_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; 
v_k_554_ = lean_array_fget_borrowed(v_keys_548_, v_i_550_);
v_v_555_ = lean_array_fget_borrowed(v_vals_549_, v_i_550_);
lean_inc(v_f_547_);
lean_inc(v_v_555_);
lean_inc(v_k_554_);
v___x_556_ = lean_apply_3(v_f_547_, v_acc_551_, v_k_554_, v_v_555_);
v___x_557_ = lean_unsigned_to_nat(1u);
v___x_558_ = lean_nat_add(v_i_550_, v___x_557_);
lean_dec(v_i_550_);
v_i_550_ = v___x_558_;
v_acc_551_ = v___x_556_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_ConstMap_fold_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_f_560_, lean_object* v_keys_561_, lean_object* v_vals_562_, lean_object* v_i_563_, lean_object* v_acc_564_){
_start:
{
lean_object* v_res_565_; 
v_res_565_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_ConstMap_fold_spec__0_spec__0_spec__1_spec__3___redArg(v_f_560_, v_keys_561_, v_vals_562_, v_i_563_, v_acc_564_);
lean_dec_ref(v_vals_562_);
lean_dec_ref(v_keys_561_);
return v_res_565_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_ConstMap_fold_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_f_566_, lean_object* v_as_567_, size_t v_i_568_, size_t v_stop_569_, lean_object* v_b_570_){
_start:
{
lean_object* v___y_572_; uint8_t v___x_576_; 
v___x_576_ = lean_usize_dec_eq(v_i_568_, v_stop_569_);
if (v___x_576_ == 0)
{
lean_object* v___x_577_; 
v___x_577_ = lean_array_uget_borrowed(v_as_567_, v_i_568_);
switch(lean_obj_tag(v___x_577_))
{
case 0:
{
lean_object* v_key_578_; lean_object* v_val_579_; lean_object* v___x_580_; 
v_key_578_ = lean_ctor_get(v___x_577_, 0);
v_val_579_ = lean_ctor_get(v___x_577_, 1);
lean_inc(v_f_566_);
lean_inc(v_val_579_);
lean_inc(v_key_578_);
v___x_580_ = lean_apply_3(v_f_566_, v_b_570_, v_key_578_, v_val_579_);
v___y_572_ = v___x_580_;
goto v___jp_571_;
}
case 1:
{
lean_object* v_node_581_; lean_object* v___x_582_; 
v_node_581_ = lean_ctor_get(v___x_577_, 0);
lean_inc(v_f_566_);
v___x_582_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_ConstMap_fold_spec__0_spec__0_spec__1___redArg(v_f_566_, v_node_581_, v_b_570_);
v___y_572_ = v___x_582_;
goto v___jp_571_;
}
default: 
{
v___y_572_ = v_b_570_;
goto v___jp_571_;
}
}
}
else
{
lean_dec(v_f_566_);
return v_b_570_;
}
v___jp_571_:
{
size_t v___x_573_; size_t v___x_574_; 
v___x_573_ = ((size_t)1ULL);
v___x_574_ = lean_usize_add(v_i_568_, v___x_573_);
v_i_568_ = v___x_574_;
v_b_570_ = v___y_572_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_ConstMap_fold_spec__0_spec__0_spec__1___redArg(lean_object* v_f_583_, lean_object* v_x_584_, lean_object* v_x_585_){
_start:
{
if (lean_obj_tag(v_x_584_) == 0)
{
lean_object* v_es_586_; lean_object* v___x_587_; lean_object* v___x_588_; uint8_t v___x_589_; 
v_es_586_ = lean_ctor_get(v_x_584_, 0);
v___x_587_ = lean_unsigned_to_nat(0u);
v___x_588_ = lean_array_get_size(v_es_586_);
v___x_589_ = lean_nat_dec_lt(v___x_587_, v___x_588_);
if (v___x_589_ == 0)
{
lean_dec(v_f_583_);
return v_x_585_;
}
else
{
size_t v___x_590_; size_t v___x_591_; lean_object* v___x_592_; 
v___x_590_ = ((size_t)0ULL);
v___x_591_ = lean_usize_of_nat(v___x_588_);
v___x_592_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_ConstMap_fold_spec__0_spec__0_spec__1_spec__2___redArg(v_f_583_, v_es_586_, v___x_590_, v___x_591_, v_x_585_);
return v___x_592_;
}
}
else
{
lean_object* v_ks_593_; lean_object* v_vs_594_; lean_object* v___x_595_; lean_object* v___x_596_; 
v_ks_593_ = lean_ctor_get(v_x_584_, 0);
v_vs_594_ = lean_ctor_get(v_x_584_, 1);
v___x_595_ = lean_unsigned_to_nat(0u);
v___x_596_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_ConstMap_fold_spec__0_spec__0_spec__1_spec__3___redArg(v_f_583_, v_ks_593_, v_vs_594_, v___x_595_, v_x_585_);
return v___x_596_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_ConstMap_fold_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_f_597_, lean_object* v_x_598_, lean_object* v_x_599_){
_start:
{
lean_object* v_res_600_; 
v_res_600_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_ConstMap_fold_spec__0_spec__0_spec__1___redArg(v_f_597_, v_x_598_, v_x_599_);
lean_dec_ref(v_x_598_);
return v_res_600_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_ConstMap_fold_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_f_601_, lean_object* v_as_602_, lean_object* v_i_603_, lean_object* v_stop_604_, lean_object* v_b_605_){
_start:
{
size_t v_i_boxed_606_; size_t v_stop_boxed_607_; lean_object* v_res_608_; 
v_i_boxed_606_ = lean_unbox_usize(v_i_603_);
lean_dec(v_i_603_);
v_stop_boxed_607_ = lean_unbox_usize(v_stop_604_);
lean_dec(v_stop_604_);
v_res_608_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_ConstMap_fold_spec__0_spec__0_spec__1_spec__2___redArg(v_f_601_, v_as_602_, v_i_boxed_606_, v_stop_boxed_607_, v_b_605_);
lean_dec_ref(v_as_602_);
return v_res_608_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_ConstMap_fold_spec__0___redArg(lean_object* v_map_609_, lean_object* v_f_610_, lean_object* v_init_611_){
_start:
{
lean_object* v___f_612_; lean_object* v___x_613_; 
v___f_612_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_ConstMap_fold_spec__0___redArg___lam__0), 4, 1);
lean_closure_set(v___f_612_, 0, v_f_610_);
v___x_613_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_ConstMap_fold_spec__0_spec__0_spec__1___redArg(v___f_612_, v_map_609_, v_init_611_);
return v___x_613_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_ConstMap_fold_spec__0___redArg___boxed(lean_object* v_map_614_, lean_object* v_f_615_, lean_object* v_init_616_){
_start:
{
lean_object* v_res_617_; 
v_res_617_ = l_Lean_PersistentHashMap_foldl___at___00Lean_ConstMap_fold_spec__0___redArg(v_map_614_, v_f_615_, v_init_616_);
lean_dec_ref(v_map_614_);
return v_res_617_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstMap_fold___redArg(lean_object* v_f_618_, lean_object* v_init_619_, lean_object* v_m_620_){
_start:
{
lean_object* v_map_u2081_621_; lean_object* v_map_u2082_622_; lean_object* v___x_623_; lean_object* v___x_624_; 
v_map_u2081_621_ = lean_ctor_get(v_m_620_, 0);
lean_inc_ref(v_map_u2081_621_);
v_map_u2082_622_ = lean_ctor_get(v_m_620_, 1);
lean_inc_ref(v_map_u2082_622_);
lean_dec_ref(v_m_620_);
lean_inc(v_f_618_);
v___x_623_ = l_Lean_ImportedConsts_foldlM___at___00Lean_ImportedConsts_foldl_spec__0___redArg(v_map_u2081_621_, v_f_618_, v_init_619_);
v___x_624_ = l_Lean_PersistentHashMap_foldl___at___00Lean_ConstMap_fold_spec__0___redArg(v_map_u2082_622_, v_f_618_, v___x_623_);
lean_dec_ref(v_map_u2082_622_);
return v___x_624_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstMap_fold(lean_object* v_00_u03c3_625_, lean_object* v_f_626_, lean_object* v_init_627_, lean_object* v_m_628_){
_start:
{
lean_object* v___x_629_; 
v___x_629_ = l_Lean_ConstMap_fold___redArg(v_f_626_, v_init_627_, v_m_628_);
return v___x_629_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_ConstMap_fold_spec__0(lean_object* v_00_u03c3_630_, lean_object* v_00_u03b2_631_, lean_object* v_map_632_, lean_object* v_f_633_, lean_object* v_init_634_){
_start:
{
lean_object* v___x_635_; 
v___x_635_ = l_Lean_PersistentHashMap_foldl___at___00Lean_ConstMap_fold_spec__0___redArg(v_map_632_, v_f_633_, v_init_634_);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_ConstMap_fold_spec__0___boxed(lean_object* v_00_u03c3_636_, lean_object* v_00_u03b2_637_, lean_object* v_map_638_, lean_object* v_f_639_, lean_object* v_init_640_){
_start:
{
lean_object* v_res_641_; 
v_res_641_ = l_Lean_PersistentHashMap_foldl___at___00Lean_ConstMap_fold_spec__0(v_00_u03c3_636_, v_00_u03b2_637_, v_map_638_, v_f_639_, v_init_640_);
lean_dec_ref(v_map_638_);
return v_res_641_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_ConstMap_fold_spec__0_spec__0___redArg(lean_object* v_map_642_, lean_object* v_f_643_, lean_object* v_init_644_){
_start:
{
lean_object* v___x_645_; 
v___x_645_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_ConstMap_fold_spec__0_spec__0_spec__1___redArg(v_f_643_, v_map_642_, v_init_644_);
return v___x_645_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_ConstMap_fold_spec__0_spec__0___redArg___boxed(lean_object* v_map_646_, lean_object* v_f_647_, lean_object* v_init_648_){
_start:
{
lean_object* v_res_649_; 
v_res_649_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_ConstMap_fold_spec__0_spec__0___redArg(v_map_646_, v_f_647_, v_init_648_);
lean_dec_ref(v_map_646_);
return v_res_649_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_ConstMap_fold_spec__0_spec__0(lean_object* v_00_u03c3_650_, lean_object* v_00_u03b2_651_, lean_object* v_map_652_, lean_object* v_f_653_, lean_object* v_init_654_){
_start:
{
lean_object* v___x_655_; 
v___x_655_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_ConstMap_fold_spec__0_spec__0_spec__1___redArg(v_f_653_, v_map_652_, v_init_654_);
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_ConstMap_fold_spec__0_spec__0___boxed(lean_object* v_00_u03c3_656_, lean_object* v_00_u03b2_657_, lean_object* v_map_658_, lean_object* v_f_659_, lean_object* v_init_660_){
_start:
{
lean_object* v_res_661_; 
v_res_661_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_ConstMap_fold_spec__0_spec__0(v_00_u03c3_656_, v_00_u03b2_657_, v_map_658_, v_f_659_, v_init_660_);
lean_dec_ref(v_map_658_);
return v_res_661_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_ConstMap_fold_spec__0_spec__0_spec__1(lean_object* v_00_u03c3_662_, lean_object* v_00_u03b1_663_, lean_object* v_00_u03b2_664_, lean_object* v_f_665_, lean_object* v_x_666_, lean_object* v_x_667_){
_start:
{
lean_object* v___x_668_; 
v___x_668_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_ConstMap_fold_spec__0_spec__0_spec__1___redArg(v_f_665_, v_x_666_, v_x_667_);
return v___x_668_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_ConstMap_fold_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03c3_669_, lean_object* v_00_u03b1_670_, lean_object* v_00_u03b2_671_, lean_object* v_f_672_, lean_object* v_x_673_, lean_object* v_x_674_){
_start:
{
lean_object* v_res_675_; 
v_res_675_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_ConstMap_fold_spec__0_spec__0_spec__1(v_00_u03c3_669_, v_00_u03b1_670_, v_00_u03b2_671_, v_f_672_, v_x_673_, v_x_674_);
lean_dec_ref(v_x_673_);
return v_res_675_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_ConstMap_fold_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_676_, lean_object* v_00_u03b2_677_, lean_object* v_00_u03c3_678_, lean_object* v_f_679_, lean_object* v_as_680_, size_t v_i_681_, size_t v_stop_682_, lean_object* v_b_683_){
_start:
{
lean_object* v___x_684_; 
v___x_684_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_ConstMap_fold_spec__0_spec__0_spec__1_spec__2___redArg(v_f_679_, v_as_680_, v_i_681_, v_stop_682_, v_b_683_);
return v___x_684_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_ConstMap_fold_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_685_, lean_object* v_00_u03b2_686_, lean_object* v_00_u03c3_687_, lean_object* v_f_688_, lean_object* v_as_689_, lean_object* v_i_690_, lean_object* v_stop_691_, lean_object* v_b_692_){
_start:
{
size_t v_i_boxed_693_; size_t v_stop_boxed_694_; lean_object* v_res_695_; 
v_i_boxed_693_ = lean_unbox_usize(v_i_690_);
lean_dec(v_i_690_);
v_stop_boxed_694_ = lean_unbox_usize(v_stop_691_);
lean_dec(v_stop_691_);
v_res_695_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_ConstMap_fold_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_685_, v_00_u03b2_686_, v_00_u03c3_687_, v_f_688_, v_as_689_, v_i_boxed_693_, v_stop_boxed_694_, v_b_692_);
lean_dec_ref(v_as_689_);
return v_res_695_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_ConstMap_fold_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03c3_696_, lean_object* v_00_u03b1_697_, lean_object* v_00_u03b2_698_, lean_object* v_f_699_, lean_object* v_keys_700_, lean_object* v_vals_701_, lean_object* v_heq_702_, lean_object* v_i_703_, lean_object* v_acc_704_){
_start:
{
lean_object* v___x_705_; 
v___x_705_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_ConstMap_fold_spec__0_spec__0_spec__1_spec__3___redArg(v_f_699_, v_keys_700_, v_vals_701_, v_i_703_, v_acc_704_);
return v___x_705_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_ConstMap_fold_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03c3_706_, lean_object* v_00_u03b1_707_, lean_object* v_00_u03b2_708_, lean_object* v_f_709_, lean_object* v_keys_710_, lean_object* v_vals_711_, lean_object* v_heq_712_, lean_object* v_i_713_, lean_object* v_acc_714_){
_start:
{
lean_object* v_res_715_; 
v_res_715_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_ConstMap_fold_spec__0_spec__0_spec__1_spec__3(v_00_u03c3_706_, v_00_u03b1_707_, v_00_u03b2_708_, v_f_709_, v_keys_710_, v_vals_711_, v_heq_712_, v_i_713_, v_acc_714_);
lean_dec_ref(v_vals_711_);
lean_dec_ref(v_keys_710_);
return v_res_715_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstMap_forM___redArg___lam__0(lean_object* v_inst_716_, lean_object* v_map_u2082_717_, lean_object* v_f_718_, lean_object* v_____r_719_){
_start:
{
lean_object* v___x_720_; 
v___x_720_ = l_Lean_PersistentHashMap_forM___redArg(v_inst_716_, v_map_u2082_717_, v_f_718_);
return v___x_720_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstMap_forM___redArg(lean_object* v_inst_721_, lean_object* v_map_722_, lean_object* v_f_723_){
_start:
{
lean_object* v_toBind_724_; lean_object* v_map_u2081_725_; lean_object* v_map_u2082_726_; lean_object* v___f_727_; lean_object* v___x_728_; lean_object* v___x_729_; 
v_toBind_724_ = lean_ctor_get(v_inst_721_, 1);
lean_inc(v_toBind_724_);
v_map_u2081_725_ = lean_ctor_get(v_map_722_, 0);
lean_inc_ref(v_map_u2081_725_);
v_map_u2082_726_ = lean_ctor_get(v_map_722_, 1);
lean_inc_ref(v_map_u2082_726_);
lean_dec_ref(v_map_722_);
lean_inc(v_f_723_);
lean_inc_ref(v_inst_721_);
v___f_727_ = lean_alloc_closure((void*)(l_Lean_ConstMap_forM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_727_, 0, v_inst_721_);
lean_closure_set(v___f_727_, 1, v_map_u2082_726_);
lean_closure_set(v___f_727_, 2, v_f_723_);
v___x_728_ = l_Lean_ImportedConsts_forM___redArg(v_inst_721_, v_map_u2081_725_, v_f_723_);
v___x_729_ = lean_apply_4(v_toBind_724_, lean_box(0), lean_box(0), v___x_728_, v___f_727_);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstMap_forM(lean_object* v_m_730_, lean_object* v_inst_731_, lean_object* v_map_732_, lean_object* v_f_733_){
_start:
{
lean_object* v___x_734_; 
v___x_734_ = l_Lean_ConstMap_forM___redArg(v_inst_731_, v_map_732_, v_f_733_);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstMap_instForMProdNameConstantInfoOfMonad___redArg___lam__0(lean_object* v_f_735_, lean_object* v_n_736_, lean_object* v_v_737_){
_start:
{
lean_object* v___x_738_; lean_object* v___x_739_; 
v___x_738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_738_, 0, v_n_736_);
lean_ctor_set(v___x_738_, 1, v_v_737_);
v___x_739_ = lean_apply_1(v_f_735_, v___x_738_);
return v___x_739_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstMap_instForMProdNameConstantInfoOfMonad___redArg___lam__1(lean_object* v_inst_740_, lean_object* v_map_741_, lean_object* v_f_742_){
_start:
{
lean_object* v___f_743_; lean_object* v___x_744_; 
v___f_743_ = lean_alloc_closure((void*)(l_Lean_ConstMap_instForMProdNameConstantInfoOfMonad___redArg___lam__0), 3, 1);
lean_closure_set(v___f_743_, 0, v_f_742_);
v___x_744_ = l_Lean_ConstMap_forM___redArg(v_inst_740_, v_map_741_, v___f_743_);
return v___x_744_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstMap_instForMProdNameConstantInfoOfMonad___redArg(lean_object* v_inst_745_){
_start:
{
lean_object* v___f_746_; 
v___f_746_ = lean_alloc_closure((void*)(l_Lean_ConstMap_instForMProdNameConstantInfoOfMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_746_, 0, v_inst_745_);
return v___f_746_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstMap_instForMProdNameConstantInfoOfMonad(lean_object* v_m_747_, lean_object* v_inst_748_){
_start:
{
lean_object* v___f_749_; 
v___f_749_ = lean_alloc_closure((void*)(l_Lean_ConstMap_instForMProdNameConstantInfoOfMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_749_, 0, v_inst_748_);
return v___f_749_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstMap_instForInProdNameConstantInfoOfMonad___redArg___lam__0(lean_object* v_toPure_750_, lean_object* v_____do__lift_751_){
_start:
{
if (lean_obj_tag(v_____do__lift_751_) == 0)
{
lean_object* v_a_752_; lean_object* v___x_753_; 
v_a_752_ = lean_ctor_get(v_____do__lift_751_, 0);
lean_inc(v_a_752_);
lean_dec_ref_known(v_____do__lift_751_, 1);
v___x_753_ = lean_apply_2(v_toPure_750_, lean_box(0), v_a_752_);
return v___x_753_;
}
else
{
lean_object* v_a_754_; lean_object* v_snd_755_; lean_object* v___x_756_; 
v_a_754_ = lean_ctor_get(v_____do__lift_751_, 0);
lean_inc(v_a_754_);
lean_dec_ref_known(v_____do__lift_751_, 1);
v_snd_755_ = lean_ctor_get(v_a_754_, 1);
lean_inc(v_snd_755_);
lean_dec(v_a_754_);
v___x_756_ = lean_apply_2(v_toPure_750_, lean_box(0), v_snd_755_);
return v___x_756_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstMap_instForInProdNameConstantInfoOfMonad___redArg___lam__1(lean_object* v_toPure_757_, lean_object* v_____do__lift_758_){
_start:
{
if (lean_obj_tag(v_____do__lift_758_) == 0)
{
lean_object* v_a_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_767_; 
v_a_759_ = lean_ctor_get(v_____do__lift_758_, 0);
v_isSharedCheck_767_ = !lean_is_exclusive(v_____do__lift_758_);
if (v_isSharedCheck_767_ == 0)
{
v___x_761_ = v_____do__lift_758_;
v_isShared_762_ = v_isSharedCheck_767_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_a_759_);
lean_dec(v_____do__lift_758_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_767_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v___x_764_; 
if (v_isShared_762_ == 0)
{
v___x_764_ = v___x_761_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_766_; 
v_reuseFailAlloc_766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_766_, 0, v_a_759_);
v___x_764_ = v_reuseFailAlloc_766_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
lean_object* v___x_765_; 
v___x_765_ = lean_apply_2(v_toPure_757_, lean_box(0), v___x_764_);
return v___x_765_;
}
}
}
else
{
lean_object* v_a_768_; lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_778_; 
v_a_768_ = lean_ctor_get(v_____do__lift_758_, 0);
v_isSharedCheck_778_ = !lean_is_exclusive(v_____do__lift_758_);
if (v_isSharedCheck_778_ == 0)
{
v___x_770_ = v_____do__lift_758_;
v_isShared_771_ = v_isSharedCheck_778_;
goto v_resetjp_769_;
}
else
{
lean_inc(v_a_768_);
lean_dec(v_____do__lift_758_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_778_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_775_; 
v___x_772_ = lean_box(0);
v___x_773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_773_, 0, v___x_772_);
lean_ctor_set(v___x_773_, 1, v_a_768_);
if (v_isShared_771_ == 0)
{
lean_ctor_set(v___x_770_, 0, v___x_773_);
v___x_775_ = v___x_770_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v___x_773_);
v___x_775_ = v_reuseFailAlloc_777_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
lean_object* v___x_776_; 
v___x_776_ = lean_apply_2(v_toPure_757_, lean_box(0), v___x_775_);
return v___x_776_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ConstMap_instForInProdNameConstantInfoOfMonad___redArg___lam__2(lean_object* v___y_779_, lean_object* v_toBind_780_, lean_object* v___f_781_, lean_object* v_n_782_, lean_object* v_v_783_, lean_object* v___y_784_){
_start:
{
lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_785_, 0, v_n_782_);
lean_ctor_set(v___x_785_, 1, v_v_783_);
v___x_786_ = lean_apply_2(v___y_779_, v___x_785_, v___y_784_);
v___x_787_ = lean_apply_4(v_toBind_780_, lean_box(0), lean_box(0), v___x_786_, v___f_781_);
return v___x_787_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstMap_instForInProdNameConstantInfoOfMonad___redArg___lam__3(lean_object* v_inst_788_, lean_object* v_00_u03b2_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_){
_start:
{
lean_object* v___f_793_; lean_object* v___f_794_; lean_object* v___f_795_; lean_object* v___f_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___f_803_; lean_object* v___f_804_; lean_object* v___f_805_; lean_object* v___f_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v_toApplicative_813_; lean_object* v_toBind_814_; lean_object* v_toPure_815_; lean_object* v___f_816_; lean_object* v___f_817_; lean_object* v___f_818_; lean_object* v___x_138__overap_819_; lean_object* v___x_820_; lean_object* v___x_821_; 
lean_inc_ref_n(v_inst_788_, 7);
v___f_793_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_793_, 0, v_inst_788_);
v___f_794_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__4), 5, 1);
lean_closure_set(v___f_794_, 0, v_inst_788_);
v___f_795_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__7), 5, 1);
lean_closure_set(v___f_795_, 0, v_inst_788_);
v___f_796_ = lean_alloc_closure((void*)(l_ExceptT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_796_, 0, v_inst_788_);
v___x_797_ = lean_alloc_closure((void*)(l_ExceptT_map), 7, 3);
lean_closure_set(v___x_797_, 0, lean_box(0));
lean_closure_set(v___x_797_, 1, lean_box(0));
lean_closure_set(v___x_797_, 2, v_inst_788_);
v___x_798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_798_, 0, v___x_797_);
lean_ctor_set(v___x_798_, 1, v___f_793_);
v___x_799_ = lean_alloc_closure((void*)(l_ExceptT_pure), 5, 3);
lean_closure_set(v___x_799_, 0, lean_box(0));
lean_closure_set(v___x_799_, 1, lean_box(0));
lean_closure_set(v___x_799_, 2, v_inst_788_);
v___x_800_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_800_, 0, v___x_798_);
lean_ctor_set(v___x_800_, 1, v___x_799_);
lean_ctor_set(v___x_800_, 2, v___f_794_);
lean_ctor_set(v___x_800_, 3, v___f_795_);
lean_ctor_set(v___x_800_, 4, v___f_796_);
v___x_801_ = lean_alloc_closure((void*)(l_ExceptT_bind), 7, 3);
lean_closure_set(v___x_801_, 0, lean_box(0));
lean_closure_set(v___x_801_, 1, lean_box(0));
lean_closure_set(v___x_801_, 2, v_inst_788_);
v___x_802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_802_, 0, v___x_800_);
lean_ctor_set(v___x_802_, 1, v___x_801_);
lean_inc_ref_n(v___x_802_, 6);
v___f_803_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_803_, 0, v___x_802_);
v___f_804_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_804_, 0, v___x_802_);
v___f_805_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_805_, 0, v___x_802_);
v___f_806_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_806_, 0, v___x_802_);
v___x_807_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_807_, 0, lean_box(0));
lean_closure_set(v___x_807_, 1, lean_box(0));
lean_closure_set(v___x_807_, 2, v___x_802_);
v___x_808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_808_, 0, v___x_807_);
lean_ctor_set(v___x_808_, 1, v___f_803_);
v___x_809_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_809_, 0, lean_box(0));
lean_closure_set(v___x_809_, 1, lean_box(0));
lean_closure_set(v___x_809_, 2, v___x_802_);
v___x_810_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_810_, 0, v___x_808_);
lean_ctor_set(v___x_810_, 1, v___x_809_);
lean_ctor_set(v___x_810_, 2, v___f_804_);
lean_ctor_set(v___x_810_, 3, v___f_805_);
lean_ctor_set(v___x_810_, 4, v___f_806_);
v___x_811_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_811_, 0, lean_box(0));
lean_closure_set(v___x_811_, 1, lean_box(0));
lean_closure_set(v___x_811_, 2, v___x_802_);
v___x_812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_812_, 0, v___x_810_);
lean_ctor_set(v___x_812_, 1, v___x_811_);
v_toApplicative_813_ = lean_ctor_get(v_inst_788_, 0);
lean_inc_ref(v_toApplicative_813_);
v_toBind_814_ = lean_ctor_get(v_inst_788_, 1);
lean_inc_n(v_toBind_814_, 2);
lean_dec_ref(v_inst_788_);
v_toPure_815_ = lean_ctor_get(v_toApplicative_813_, 1);
lean_inc_n(v_toPure_815_, 2);
lean_dec_ref(v_toApplicative_813_);
v___f_816_ = lean_alloc_closure((void*)(l_Lean_ConstMap_instForInProdNameConstantInfoOfMonad___redArg___lam__0), 2, 1);
lean_closure_set(v___f_816_, 0, v_toPure_815_);
v___f_817_ = lean_alloc_closure((void*)(l_Lean_ConstMap_instForInProdNameConstantInfoOfMonad___redArg___lam__1), 2, 1);
lean_closure_set(v___f_817_, 0, v_toPure_815_);
v___f_818_ = lean_alloc_closure((void*)(l_Lean_ConstMap_instForInProdNameConstantInfoOfMonad___redArg___lam__2), 6, 3);
lean_closure_set(v___f_818_, 0, v___y_792_);
lean_closure_set(v___f_818_, 1, v_toBind_814_);
lean_closure_set(v___f_818_, 2, v___f_817_);
v___x_138__overap_819_ = l_Lean_ConstMap_forM___redArg(v___x_812_, v___y_790_, v___f_818_);
v___x_820_ = lean_apply_1(v___x_138__overap_819_, v___y_791_);
v___x_821_ = lean_apply_4(v_toBind_814_, lean_box(0), lean_box(0), v___x_820_, v___f_816_);
return v___x_821_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstMap_instForInProdNameConstantInfoOfMonad___redArg(lean_object* v_inst_822_){
_start:
{
lean_object* v___f_823_; 
v___f_823_ = lean_alloc_closure((void*)(l_Lean_ConstMap_instForInProdNameConstantInfoOfMonad___redArg___lam__3), 5, 1);
lean_closure_set(v___f_823_, 0, v_inst_822_);
return v___f_823_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstMap_instForInProdNameConstantInfoOfMonad(lean_object* v_m_824_, lean_object* v_inst_825_){
_start:
{
lean_object* v___f_826_; 
v___f_826_ = lean_alloc_closure((void*)(l_Lean_ConstMap_instForInProdNameConstantInfoOfMonad___redArg___lam__3), 5, 1);
lean_closure_set(v___f_826_, 0, v_inst_825_);
return v___f_826_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstMap_toList___lam__0(lean_object* v_es_827_, lean_object* v_n_828_, lean_object* v_v_829_){
_start:
{
lean_object* v___x_830_; lean_object* v___x_831_; 
v___x_830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_830_, 0, v_n_828_);
lean_ctor_set(v___x_830_, 1, v_v_829_);
v___x_831_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_831_, 0, v___x_830_);
lean_ctor_set(v___x_831_, 1, v_es_827_);
return v___x_831_;
}
}
LEAN_EXPORT lean_object* l_Lean_ConstMap_toList(lean_object* v_m_833_){
_start:
{
lean_object* v___f_834_; lean_object* v___x_835_; lean_object* v___x_836_; 
v___f_834_ = ((lean_object*)(l_Lean_ConstMap_toList___closed__0));
v___x_835_ = lean_box(0);
v___x_836_ = l_Lean_ConstMap_fold___redArg(v___f_834_, v___x_835_, v_m_833_);
return v___x_836_;
}
}
lean_object* runtime_initialize_Lean_ConstTrie(uint8_t builtin);
lean_object* runtime_initialize_Lean_Declaration(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_PersistentHashMap(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_ConstMap(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_ConstTrie(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Declaration(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_PersistentHashMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_instInhabitedConstMap = _init_l_Lean_instInhabitedConstMap();
lean_mark_persistent(l_Lean_instInhabitedConstMap);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_ConstMap(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_ConstTrie(uint8_t builtin);
lean_object* initialize_Lean_Declaration(uint8_t builtin);
lean_object* initialize_Lean_Data_PersistentHashMap(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_ConstMap(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_ConstTrie(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Declaration(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_PersistentHashMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_ConstMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_ConstMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_ConstMap(builtin);
}
#ifdef __cplusplus
}
#endif
