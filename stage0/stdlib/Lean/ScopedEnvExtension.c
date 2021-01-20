// Lean compiler output
// Module: Lean.ScopedEnvExtension
// Imports: Init Lean.Environment Lean.Data.NameTrie Lean.Attributes
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
lean_object* l_Array_forInUnsafe_loop___at_Lean_activateScoped___spec__1___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_addImportedFn___rarg___closed__1;
lean_object* l_Lean_ScopedEnvExtension_StateStack_scopedEntries___default___closed__1;
extern lean_object* l_Lean_Name_toString___closed__1;
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_ScopedEnvExtension_activateScoped___spec__7___rarg___boxed(lean_object*, lean_object*);
size_t l_USize_add(size_t, size_t);
extern lean_object* l_Lean_Name_getString_x21___closed__3;
lean_object* l_Lean_popScope_match__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_addImportedFn___rarg___closed__2;
lean_object* l_List_map___at_Lean_ScopedEnvExtension_addEntryFn___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_mkHashMap___at_Lean_ScopedEnvExtension_StateStack_scopedEntries___default___spec__1___rarg(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_pushScope_match__1___boxed(lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_ScopedEnvExtension_activateScoped___spec__12___rarg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_pushScope___spec__1___rarg___lambda__2(lean_object*, size_t, lean_object*, lean_object*, lean_object*, size_t, lean_object*);
lean_object* l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___at_Lean_ScopedEnvExtension_addEntryFn___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_getState(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_AssocList_find_x3f___at_Lean_ScopedEnvExtension_activateScoped___spec__8(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_addImportedFn___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_AssocList_replace___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__30___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_expand___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__27___rarg(lean_object*, lean_object*);
uint8_t l_USize_decEq(size_t, size_t);
lean_object* l_Lean_activateScoped(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Std_AssocList_find_x3f___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__8___rarg(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_insert___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__10___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_add___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__5(lean_object*);
lean_object* l_Std_PersistentArray_forInAux___at_Lean_ScopedEnvExtension_activateScoped___spec__10___rarg___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_ScopedEnvExtension_activateScoped___spec__13(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_LocalContext_fvarIdToDecl___default___closed__1;
lean_object* l_Lean_ScopedEnvExtension_add___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_IO_mkRef___at_Lean_initFn____x40_Lean_ScopedEnvExtension___hyg_657____spec__1(lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_addLocalEntry_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_findAux___at_Lean_ScopedEnvExtension_activateScoped___spec__3(lean_object*);
lean_object* l_Lean_pushScope___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_find_x3f___at_Lean_ScopedEnvExtension_activateScoped___spec__1(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_registerSimpleScopedEnvExtension___rarg(lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_mkInitial___rarg(lean_object*, lean_object*);
lean_object* l_Lean_registerScopedEnvExtensionUnsafe___rarg___closed__2;
lean_object* l_Std_PersistentArray_forIn___at_Lean_ScopedEnvExtension_activateScoped___spec__9(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_registerInternalExceptionId___closed__2;
lean_object* l_Lean_pushScope___rarg___lambda__1(lean_object*, lean_object*);
lean_object* l_Std_mkHashMap___at_Lean_ScopedEnvExtension_instInhabitedScopedEntries___spec__1___rarg(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_add___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_pushScope___spec__1___rarg___lambda__1(lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_pushScope___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Std_HashMapImp_insert___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__14___rarg(lean_object*, lean_object*, lean_object*);
size_t l_USize_sub(size_t, size_t);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_ScopedEnvExtension_activateScoped___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_addImportedFn_match__5(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_forInAux___at_Lean_ScopedEnvExtension_activateScoped___spec__10___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_getState_match__1(lean_object*, lean_object*);
lean_object* l_Lean_registerSimpleScopedEnvExtension___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_addScopedEntry(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___rarg(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Monad_seqRight___default___rarg___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_registerScopedEnvExtension___rarg(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_addEntry(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_addImportedFn_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_AssocList_contains___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__26___rarg___boxed(lean_object*, lean_object*);
extern lean_object* l_Std_PersistentArray_empty___closed__1;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_addImportedFn(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_find_x3f___at_Lean_ScopedEnvExtension_activateScoped___spec__1___rarg(lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_ScopedEnvExtension_addImportedFn___spec__3___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_AssocList_find_x3f___at_Lean_ScopedEnvExtension_activateScoped___spec__6___rarg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_setState___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_exportEntriesFn(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_popScope___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Std_AssocList_foldlM___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__18(lean_object*);
lean_object* l_Lean_registerScopedEnvExtensionUnsafe___rarg___lambda__1(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_mkInitial(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_addImportedFn_match__4(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_ScopedEnvExtension_activateScoped___spec__5(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Std_PersistentHashMap_getCollisionNodeSize___rarg(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_pushScope___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_ScopedEnvExtension_activateScoped___spec__13___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_mkHashMap___at_Lean_ScopedEnvExtension_instInhabitedStateStack___spec__1(lean_object*);
lean_object* l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__24___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_StateStack_scopedEntries___default___closed__2;
extern lean_object* l_Applicative_seqRight___default___rarg___closed__1;
lean_object* l_Array_forInUnsafe_loop___at_Lean_ScopedEnvExtension_activateScoped___spec__12___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_insert___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__21___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_addLocalEntry(lean_object*, lean_object*, lean_object*);
size_t l_USize_shiftRight(size_t, size_t);
lean_object* l_Lean_ScopedEnvExtension_addScopedEntry___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_insert___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__25(lean_object*);
lean_object* l_Std_HashMapImp_moveEntries___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__28(lean_object*);
lean_object* l_Std_PersistentHashMap_findAux___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_USize_decLt(size_t, size_t);
lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__11___rarg(lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_add_match__1___rarg(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_pushScope___rarg___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_findAux___at_Lean_ScopedEnvExtension_activateScoped___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_ScopedEnvExtension_activateScoped___spec__4(lean_object*);
lean_object* l_Std_PersistentHashMap_insertAux_traverse___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__12(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___rarg___closed__1;
lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__11___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithSep(lean_object*, lean_object*);
lean_object* l_Std_AssocList_contains___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__15(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_addImportedFn___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_mkHashMap___at_Lean_ScopedEnvExtension_mkInitial___spec__1___rarg(lean_object*);
lean_object* l_Std_AssocList_foldlM___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__29(lean_object*);
lean_object* l_Lean_pushScope(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_popScope___rarg(lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_ScopedEntries_insert_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_expand___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__27(lean_object*);
lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__22___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_activateScoped___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__2(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_addEntryFn_match__2___rarg(lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_popScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_mkInitial___rarg___closed__2;
lean_object* l_Std_mkHashMap___at_Lean_ScopedEnvExtension_addImportedFn___spec__1(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_popScope___spec__1___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_mkHashMap___at_Lean_ScopedEnvExtension_ScopedEntries_map___default___spec__1(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_addImportedFn_match__3___rarg(lean_object*, lean_object*);
lean_object* l_Std_AssocList_find_x3f___at_Lean_ScopedEnvExtension_activateScoped___spec__6___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__7(lean_object*);
lean_object* l_Std_HashMapImp_insert___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__14(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_ScopedEnvExtension_addImportedFn___spec__2___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__22(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_activateScoped_match__2(lean_object*, lean_object*);
lean_object* l_Lean_popScope_match__1(lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
extern lean_object* l_Std_PersistentHashMap_insertAux___rarg___closed__3;
lean_object* l_Lean_ScopedEnvExtension_addLocalEntry___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_insertAux_traverse___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__23___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_mkInitial___rarg___closed__1;
lean_object* l_Lean_pushScope_match__1(lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_ScopedEnvExtension_addImportedFn___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_activateScoped___spec__1___rarg___lambda__2(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_add_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_AssocList_replace___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__19(lean_object*);
lean_object* l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__13(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_addImportedFn_match__2___rarg(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_ScopedEnvExtension_activateScoped___spec__2___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_moveEntries___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__28___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_pushScope___spec__1(lean_object*);
lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__2___rarg(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedPersistentEnvExtension___closed__2;
lean_object* l_Array_forInUnsafe_loop___at_Lean_ScopedEnvExtension_addImportedFn___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_addImportedFn_match__5___rarg(lean_object*, lean_object*);
lean_object* l_Lean_SMap_find_x3f___at_Lean_ScopedEnvExtension_activateScoped___spec__1___rarg___boxed(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_popScope_match__1___rarg(lean_object*);
lean_object* l_Std_HashMapImp_expand___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__16___rarg(lean_object*, lean_object*);
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_mkHashMapImp___rarg(lean_object*);
lean_object* l_Lean_registerSimpleScopedEnvExtension___rarg___closed__1;
lean_object* l_Lean_registerSimpleScopedEnvExtension___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_find_x3f___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__1(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_pushScope___rarg(lean_object*, lean_object*);
uint8_t l_Std_AssocList_contains___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__26___rarg(lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_add(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_addEntryFn___rarg(lean_object*, lean_object*, lean_object*);
size_t l_Lean_Name_hash(lean_object*);
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__7___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__7___rarg(lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__4(lean_object*);
uint8_t l_Array_anyMUnsafe_any___at_Lean_registerScopedEnvExtensionUnsafe___spec__2___rarg(lean_object*, lean_object*, size_t, size_t);
lean_object* l_Std_mkHashMap___at_Lean_ScopedEnvExtension_addImportedFn___spec__1___rarg(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_pushScope___spec__1___rarg___lambda__1___closed__1;
lean_object* l_Array_forInUnsafe_loop___at_Lean_pushScope___spec__1___rarg___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_ScopedEntries_insert___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedScopedEnvExtension(lean_object*);
extern lean_object* l_IO_instInhabitedError___closed__1;
lean_object* l_Lean_ScopedEnvExtension_activateScoped(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__4___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_popScope_match__1(lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_popScope___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_registerScopedEnvExtension___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_StateStack_scopedEntries___default(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_addLocalEntry_match__1(lean_object*, lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___lambda__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_pushScope_match__1(lean_object*, lean_object*);
lean_object* l_Std_AssocList_find_x3f___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__8___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_ScopedEnvExtension_activateScoped___spec__5___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_popScope(lean_object*);
lean_object* l_Std_AssocList_find_x3f___at_Lean_ScopedEnvExtension_activateScoped___spec__8___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_insertAux_traverse___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__23___rarg(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_AssocList_replace___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__19___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_addImportedFn_match__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_insert___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__20___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_persistentEnvExtensionsRef;
lean_object* l_Lean_SMap_find_x3f___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__1___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__24(lean_object*);
size_t lean_usize_modn(size_t, lean_object*);
lean_object* l_Lean_initFn____x40_Lean_ScopedEnvExtension___hyg_657_(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_add___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_registerScopedEnvExtensionUnsafe___spec__1___rarg(lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_reverse___rarg(lean_object*);
lean_object* l_Std_AssocList_contains___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__26(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_activateScoped_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_State_activeScopes___default;
size_t l_USize_mul(size_t, size_t);
lean_object* l_Std_PersistentArray_forInAux___at_Lean_ScopedEnvExtension_activateScoped___spec__10(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Std_mkHashMap___at_Lean_ScopedEnvExtension_mkInitial___spec__1(lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__5___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__13___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerScopedEnvExtensionUnsafe___rarg___lambda__1___boxed(lean_object*);
lean_object* l_Std_AssocList_find_x3f___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__8(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_getState___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedScopedEnvExtension___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___rarg(lean_object*, lean_object*, lean_object*);
size_t l_USize_land(size_t, size_t);
lean_object* l_Array_forInUnsafe_loop___at_Lean_ScopedEnvExtension_activateScoped___spec__11___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_ScopedEnvExtension_activateScoped___spec__11(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_getState___rarg___closed__1;
lean_object* l_Lean_ScopedEnvExtension_getState___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__5___rarg(lean_object*, lean_object*);
lean_object* l_Std_AssocList_find_x3f___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__6___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_popScope_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_addEntryFn_match__1(lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_instInhabitedScopedEntries(lean_object*);
lean_object* l_Std_PersistentHashMap_insertAux_traverse___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__12___rarg(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyMUnsafe_any___at_Lean_registerScopedEnvExtensionUnsafe___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_instInhabitedStateStack___closed__1;
lean_object* l_Lean_activateScoped___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
lean_object* l_List_redLength___rarg(lean_object*);
lean_object* l_Std_PersistentArray_push___rarg(lean_object*, lean_object*);
lean_object* l_Lean_registerScopedEnvExtension(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_popScope___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_find_x3f___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_instInhabitedStateStack___closed__2;
lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_insert___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__21(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_instInhabitedScopedEntries___closed__1;
lean_object* l_Lean_ScopedEnvExtension_pushScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_AssocList_find_x3f___at_Lean_ScopedEnvExtension_activateScoped___spec__8___rarg(lean_object*, lean_object*);
extern lean_object* l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__4___closed__2;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t l_USize_decLe(size_t, size_t);
lean_object* l_Lean_ScopedEnvExtension_add___rarg___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_activateScoped_match__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_popScope___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_ScopedEnvExtension_activateScoped___spec__2(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_ScopedEntries_map___default(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_activateScoped_match__1(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__11(lean_object*);
lean_object* l_Lean_registerScopedEnvExtensionUnsafe___rarg(lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_activateScoped_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_registerScopedEnvExtensionUnsafe___rarg___closed__1;
lean_object* l_Array_forInUnsafe_loop___at_Lean_ScopedEnvExtension_addImportedFn___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_forIn___at_Lean_ScopedEnvExtension_activateScoped___spec__9___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_insertAux_traverse___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__23(lean_object*);
lean_object* l_Lean_registerSimpleScopedEnvExtension(lean_object*, lean_object*);
uint8_t l_Std_AssocList_contains___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__15___rarg(lean_object*, lean_object*);
lean_object* l_Lean_registerScopedEnvExtensionUnsafe(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_ScopedEnvExtension_activateScoped___spec__7(lean_object*);
extern lean_object* l_Lean_instInhabitedPersistentEnvExtension___closed__5;
lean_object* l_Lean_ScopedEnvExtension_ScopedEntries_insert_match__1(lean_object*, lean_object*);
lean_object* l_Lean_SMap_insert___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__20(lean_object*);
lean_object* l_Std_AssocList_find_x3f___at_Lean_ScopedEnvExtension_activateScoped___spec__6(lean_object*);
lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__2___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_StateStack_stateStack___default(lean_object*);
lean_object* l_Std_PersistentHashMap_findAux___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__3___rarg(lean_object*, size_t, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_popScope___spec__1___rarg___lambda__1(lean_object*, size_t, lean_object*, lean_object*, lean_object*, size_t, lean_object*);
lean_object* l_Std_AssocList_foldlM___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__29___rarg(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_ScopedEntries_insert(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_addEntryFn_match__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_registerScopedEnvExtensionUnsafe___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_ScopedEnvExtension_addImportedFn___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_mkHashMap___at_Lean_ScopedEnvExtension_instInhabitedStateStack___spec__1___rarg(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_addEntryFn(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_pushScope___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_AssocList_contains___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__15___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_popScope___spec__1(lean_object*);
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_ScopedEnvExtension_activateScoped___spec__5___rarg(lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_instInhabitedScopedEntries___closed__2;
lean_object* l_List_toArrayAux___rarg(lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_insert___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__25___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_findAux___at_Lean_ScopedEnvExtension_activateScoped___spec__3___rarg(lean_object*, size_t, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_getState___rarg___closed__3;
lean_object* l_Lean_activateScoped_match__1(lean_object*, lean_object*);
lean_object* l_Lean_activateScoped_match__1___rarg(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_addImportedFn_match__4___rarg(lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_forInAux___at_Lean_ScopedEnvExtension_activateScoped___spec__10___rarg___lambda__1(lean_object*, lean_object*);
lean_object* l_List_map___at_Lean_ScopedEnvExtension_addEntryFn___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_pushScope___rarg___closed__1;
extern lean_object* l_Lean_EnvExtensionInterfaceUnsafe_instInhabitedExt___closed__1;
lean_object* lean_mk_array(lean_object*, lean_object*);
extern size_t l_Std_PersistentHashMap_insertAux___rarg___closed__2;
lean_object* l_Lean_PersistentEnvExtension_getState___rarg(lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_ScopedEnvExtension_activateScoped___spec__13___rarg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_SMap_insert___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__9___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_instInhabitedStateStack(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_ScopedEnvExtension_activateScoped___spec__4___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_addEntry___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_insert___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__10(lean_object*);
lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_ScopedEnvExtension_activateScoped___spec__2___rarg(lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_getState_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_exportEntriesFn___rarg(lean_object*);
lean_object* l_Lean_activateScoped___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_add___rarg___lambda__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_forInAux___at_Lean_ScopedEnvExtension_activateScoped___spec__10___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_AssocList_find_x3f___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__6(lean_object*);
lean_object* l_Std_PersistentHashMap_insertAux_traverse___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__12___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_addImportedFn_match__1(lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_activateScoped___spec__1___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_ScopedEnvExtension_activateScoped___spec__11___rarg(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_addEntryFn_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_getState___rarg___closed__2;
lean_object* l_Std_PersistentArray_forIn___at_Lean_ScopedEnvExtension_activateScoped___spec__9___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___at_Lean_ScopedEnvExtension_addEntryFn___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_scopedEnvExtensionsRef;
lean_object* l_List_lengthAux___rarg(lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_ScopedEnvExtension_activateScoped___spec__12(lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Lean_SMap_insert___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__9(lean_object*);
lean_object* l_Std_AssocList_foldlM___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__18___rarg(lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_add_match__1(lean_object*);
lean_object* l_EStateM_pure___rarg(lean_object*, lean_object*);
lean_object* l_Lean_popScope___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_activateScoped___spec__1(lean_object*);
lean_object* l_Std_AssocList_find_x3f___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__6___rarg(lean_object*, lean_object*);
lean_object* l_Std_mkHashMap___at_Lean_ScopedEnvExtension_StateStack_scopedEntries___default___spec__1(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_pushScope_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyMUnsafe_any___at_Lean_registerScopedEnvExtensionUnsafe___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_activateScoped___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_mkHashMap___at_Lean_ScopedEnvExtension_instInhabitedScopedEntries___spec__1(lean_object*);
lean_object* l_Std_AssocList_replace___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__30(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_activateScoped___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_ScopedEntries_map___default___closed__2;
lean_object* l_List_map___at_Lean_ScopedEnvExtension_addEntryFn___spec__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_mkHashMap___at_Lean_ScopedEnvExtension_ScopedEntries_map___default___spec__1___rarg(lean_object*);
lean_object* l_Std_PersistentHashMap_findAux___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__3(lean_object*);
lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__22___rarg(lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_ScopedEntries_map___default___closed__1;
lean_object* l_Lean_pushScope_match__1___rarg(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_pushScope___rarg___boxed(lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_ScopedEnvExtension_activateScoped___spec__7___rarg(lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_pushScope___spec__1___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_addImportedFn_match__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_instInhabitedStateStack___closed__3;
lean_object* l_Std_PersistentHashMap_mkCollisionNode___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_expand___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__16(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_moveEntries___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__17___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_StateStack_newEntries___default(lean_object*);
lean_object* l_Std_HashMapImp_moveEntries___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__17(lean_object*);
static lean_object* _init_l_Lean_ScopedEnvExtension_State_activeScopes___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_NameSet_empty;
return x_1;
}
}
lean_object* l_Std_mkHashMap___at_Lean_ScopedEnvExtension_ScopedEntries_map___default___spec__1___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* l_Std_mkHashMap___at_Lean_ScopedEnvExtension_ScopedEntries_map___default___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_mkHashMap___at_Lean_ScopedEnvExtension_ScopedEntries_map___default___spec__1___rarg), 1, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_ScopedEntries_map___default___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_ScopedEntries_map___default___closed__2() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = l_Lean_ScopedEnvExtension_ScopedEntries_map___default___closed__1;
x_3 = l_Lean_LocalContext_fvarIdToDecl___default___closed__1;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
lean_object* l_Lean_ScopedEnvExtension_ScopedEntries_map___default(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_ScopedEnvExtension_ScopedEntries_map___default___closed__2;
return x_2;
}
}
lean_object* l_Std_mkHashMap___at_Lean_ScopedEnvExtension_instInhabitedScopedEntries___spec__1___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* l_Std_mkHashMap___at_Lean_ScopedEnvExtension_instInhabitedScopedEntries___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_mkHashMap___at_Lean_ScopedEnvExtension_instInhabitedScopedEntries___spec__1___rarg), 1, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries___closed__2() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = l_Lean_ScopedEnvExtension_instInhabitedScopedEntries___closed__1;
x_3 = l_Lean_LocalContext_fvarIdToDecl___default___closed__1;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
lean_object* l_Lean_ScopedEnvExtension_instInhabitedScopedEntries(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_ScopedEnvExtension_instInhabitedScopedEntries___closed__2;
return x_2;
}
}
lean_object* l_Lean_ScopedEnvExtension_StateStack_stateStack___default(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
lean_object* l_Std_mkHashMap___at_Lean_ScopedEnvExtension_StateStack_scopedEntries___default___spec__1___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* l_Std_mkHashMap___at_Lean_ScopedEnvExtension_StateStack_scopedEntries___default___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_mkHashMap___at_Lean_ScopedEnvExtension_StateStack_scopedEntries___default___spec__1___rarg), 1, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_StateStack_scopedEntries___default___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_StateStack_scopedEntries___default___closed__2() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = l_Lean_ScopedEnvExtension_StateStack_scopedEntries___default___closed__1;
x_3 = l_Lean_LocalContext_fvarIdToDecl___default___closed__1;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
lean_object* l_Lean_ScopedEnvExtension_StateStack_scopedEntries___default(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_ScopedEnvExtension_StateStack_scopedEntries___default___closed__2;
return x_2;
}
}
lean_object* l_Lean_ScopedEnvExtension_StateStack_newEntries___default(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
lean_object* l_Std_mkHashMap___at_Lean_ScopedEnvExtension_instInhabitedStateStack___spec__1___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* l_Std_mkHashMap___at_Lean_ScopedEnvExtension_instInhabitedStateStack___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_mkHashMap___at_Lean_ScopedEnvExtension_instInhabitedStateStack___spec__1___rarg), 1, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_instInhabitedStateStack___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_instInhabitedStateStack___closed__2() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = l_Lean_ScopedEnvExtension_instInhabitedStateStack___closed__1;
x_3 = l_Lean_LocalContext_fvarIdToDecl___default___closed__1;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_instInhabitedStateStack___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_ScopedEnvExtension_instInhabitedStateStack___closed__2;
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_1);
return x_3;
}
}
lean_object* l_Lean_ScopedEnvExtension_instInhabitedStateStack(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_ScopedEnvExtension_instInhabitedStateStack___closed__3;
return x_4;
}
}
lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_IO_instInhabitedError___closed__1;
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_instInhabitedDescr___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___rarg___lambda__1___boxed), 4, 0);
return x_1;
}
}
lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_alloc_closure((void*)(l_Monad_seqRight___default___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = lean_box(0);
x_4 = l_Lean_EnvExtensionInterfaceUnsafe_instInhabitedExt___closed__1;
x_5 = l_Lean_ScopedEnvExtension_instInhabitedDescr___rarg___closed__1;
x_6 = l_Lean_instInhabitedPersistentEnvExtension___closed__2;
x_7 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_4);
lean_ctor_set(x_7, 2, x_5);
lean_ctor_set(x_7, 3, x_2);
lean_ctor_set(x_7, 4, x_6);
return x_7;
}
}
lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_instInhabitedDescr___rarg), 1, 0);
return x_4;
}
}
lean_object* l_Lean_ScopedEnvExtension_instInhabitedDescr___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_ScopedEnvExtension_instInhabitedDescr___rarg___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Std_mkHashMap___at_Lean_ScopedEnvExtension_mkInitial___spec__1___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* l_Std_mkHashMap___at_Lean_ScopedEnvExtension_mkInitial___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_mkHashMap___at_Lean_ScopedEnvExtension_mkInitial___spec__1___rarg), 1, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_mkInitial___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_mkInitial___rarg___closed__2() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = l_Lean_ScopedEnvExtension_mkInitial___rarg___closed__1;
x_3 = l_Lean_LocalContext_fvarIdToDecl___default___closed__1;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
lean_object* l_Lean_ScopedEnvExtension_mkInitial___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_apply_1(x_3, x_2);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = l_Lean_NameSet_empty;
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = l_Lean_ScopedEnvExtension_mkInitial___rarg___closed__2;
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set(x_12, 2, x_9);
lean_ctor_set(x_4, 0, x_12);
return x_4;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_4);
x_15 = l_Lean_NameSet_empty;
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_ScopedEnvExtension_mkInitial___rarg___closed__2;
x_20 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_20, 2, x_17);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_14);
return x_21;
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_4);
if (x_22 == 0)
{
return x_4;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_4, 0);
x_24 = lean_ctor_get(x_4, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_4);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
lean_object* l_Lean_ScopedEnvExtension_mkInitial(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_mkInitial___rarg), 2, 0);
return x_4;
}
}
lean_object* l_Lean_ScopedEnvExtension_ScopedEntries_insert_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_ScopedEnvExtension_ScopedEntries_insert_match__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_ScopedEntries_insert_match__1___rarg), 3, 0);
return x_3;
}
}
lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_10 = lean_name_eq(x_5, x_9);
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
lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_findAtAux___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__4___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Std_PersistentHashMap_findAux___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__3___rarg(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = 5;
x_6 = l_Std_PersistentHashMap_insertAux___rarg___closed__2;
x_7 = x_2 & x_6;
x_8 = lean_usize_to_nat(x_7);
x_9 = lean_box(2);
x_10 = lean_array_get(x_9, x_4, x_8);
lean_dec(x_8);
lean_dec(x_4);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_name_eq(x_3, x_11);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_12);
x_14 = lean_box(0);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_12);
return x_15;
}
}
case 1:
{
lean_object* x_16; size_t x_17; 
x_16 = lean_ctor_get(x_10, 0);
lean_inc(x_16);
lean_dec(x_10);
x_17 = x_2 >> x_5;
x_1 = x_16;
x_2 = x_17;
goto _start;
}
default: 
{
lean_object* x_19; 
x_19 = lean_box(0);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Std_PersistentHashMap_findAtAux___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__4___rarg(x_20, x_21, lean_box(0), x_22, x_3);
lean_dec(x_21);
lean_dec(x_20);
return x_23;
}
}
}
lean_object* l_Std_PersistentHashMap_findAux___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_findAux___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__3___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__2___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_Name_hash(x_2);
x_5 = l_Std_PersistentHashMap_findAux___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__3___rarg(x_3, x_4, x_2);
return x_5;
}
}
lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_find_x3f___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__2___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_Std_AssocList_find_x3f___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__6___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_name_eq(x_4, x_1);
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_9; 
lean_inc(x_5);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_5);
return x_9;
}
}
}
}
lean_object* l_Std_AssocList_find_x3f___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_AssocList_find_x3f___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__6___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__5___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Name_hash(x_2);
x_6 = lean_usize_modn(x_5, x_4);
lean_dec(x_4);
x_7 = lean_array_uget(x_3, x_6);
x_8 = l_Std_AssocList_find_x3f___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__6___rarg(x_2, x_7);
lean_dec(x_7);
return x_8;
}
}
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_HashMapImp_find_x3f___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__5___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_Std_AssocList_find_x3f___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__8___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_name_eq(x_4, x_1);
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_9; 
lean_inc(x_5);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_5);
return x_9;
}
}
}
}
lean_object* l_Std_AssocList_find_x3f___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__8(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_AssocList_find_x3f___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__8___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__7___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Name_hash(x_2);
x_6 = lean_usize_modn(x_5, x_4);
lean_dec(x_4);
x_7 = lean_array_uget(x_3, x_6);
x_8 = l_Std_AssocList_find_x3f___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__8___rarg(x_2, x_7);
lean_dec(x_7);
return x_8;
}
}
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__7(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_HashMapImp_find_x3f___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__7___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_Lean_SMap_find_x3f___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l_Std_PersistentHashMap_find_x3f___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__2___rarg(x_5, x_2);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = l_Std_HashMapImp_find_x3f___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__5___rarg(x_4, x_2);
lean_dec(x_4);
return x_7;
}
else
{
uint8_t x_8; 
lean_dec(x_4);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
return x_6;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = l_Std_HashMapImp_find_x3f___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__7___rarg(x_11, x_2);
lean_dec(x_11);
return x_12;
}
}
}
lean_object* l_Lean_SMap_find_x3f___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_SMap_find_x3f___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__1___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_Std_PersistentHashMap_insertAux_traverse___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__12___rarg(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_9 = lean_array_fget(x_2, x_5);
x_10 = lean_array_fget(x_3, x_5);
x_11 = l_Lean_Name_hash(x_9);
x_12 = 1;
x_13 = x_1 - x_12;
x_14 = 5;
x_15 = x_14 * x_13;
x_16 = x_11 >> x_15;
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_5, x_17);
lean_dec(x_5);
x_19 = l_Std_PersistentHashMap_insertAux___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__11___rarg(x_6, x_16, x_1, x_9, x_10);
x_4 = lean_box(0);
x_5 = x_18;
x_6 = x_19;
goto _start;
}
}
}
lean_object* l_Std_PersistentHashMap_insertAux_traverse___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__12(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_insertAux_traverse___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__12___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__13___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_18 = lean_name_eq(x_3, x_17);
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
lean_object* l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__13(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__13___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__11___rarg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
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
x_10 = l_Std_PersistentHashMap_insertAux___rarg___closed__2;
x_11 = x_2 & x_10;
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
x_16 = lean_box(2);
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
x_21 = lean_name_eq(x_4, x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_free_object(x_15);
x_22 = l_Std_PersistentHashMap_mkCollisionNode___rarg(x_19, x_20, x_4, x_5);
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
x_28 = lean_name_eq(x_4, x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = l_Std_PersistentHashMap_mkCollisionNode___rarg(x_26, x_27, x_4, x_5);
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
x_36 = x_2 >> x_9;
x_37 = x_3 + x_8;
x_38 = l_Std_PersistentHashMap_insertAux___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__11___rarg(x_35, x_36, x_37, x_4, x_5);
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
x_41 = x_2 >> x_9;
x_42 = x_3 + x_8;
x_43 = l_Std_PersistentHashMap_insertAux___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__11___rarg(x_40, x_41, x_42, x_4, x_5);
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
x_51 = l_Std_PersistentHashMap_insertAux___rarg___closed__2;
x_52 = x_2 & x_51;
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
x_58 = lean_box(2);
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
x_63 = lean_name_eq(x_4, x_60);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_62);
x_64 = l_Std_PersistentHashMap_mkCollisionNode___rarg(x_60, x_61, x_4, x_5);
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
x_73 = x_2 >> x_50;
x_74 = x_3 + x_49;
x_75 = l_Std_PersistentHashMap_insertAux___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__11___rarg(x_71, x_73, x_74, x_4, x_5);
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
x_84 = l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__13___rarg(x_1, x_83, x_4, x_5);
x_85 = 7;
x_86 = x_85 <= x_3;
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_87 = l_Std_PersistentHashMap_getCollisionNodeSize___rarg(x_84);
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
x_92 = l_Std_PersistentHashMap_insertAux___rarg___closed__3;
x_93 = l_Std_PersistentHashMap_insertAux_traverse___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__12___rarg(x_3, x_90, x_91, lean_box(0), x_83, x_92);
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
x_98 = l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__13___rarg(x_96, x_97, x_4, x_5);
x_99 = 7;
x_100 = x_99 <= x_3;
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_101 = l_Std_PersistentHashMap_getCollisionNodeSize___rarg(x_98);
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
x_106 = l_Std_PersistentHashMap_insertAux___rarg___closed__3;
x_107 = l_Std_PersistentHashMap_insertAux_traverse___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__12___rarg(x_3, x_104, x_105, lean_box(0), x_97, x_106);
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
lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__11(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_insertAux___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__11___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Std_PersistentHashMap_insert___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__10___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_Name_hash(x_2);
x_8 = 1;
x_9 = l_Std_PersistentHashMap_insertAux___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__11___rarg(x_5, x_7, x_8, x_2, x_3);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_6, x_10);
lean_dec(x_6);
lean_ctor_set(x_1, 1, x_11);
lean_ctor_set(x_1, 0, x_9);
return x_1;
}
else
{
lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_1);
x_14 = l_Lean_Name_hash(x_2);
x_15 = 1;
x_16 = l_Std_PersistentHashMap_insertAux___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__11___rarg(x_12, x_14, x_15, x_2, x_3);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_13, x_17);
lean_dec(x_13);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
lean_object* l_Std_PersistentHashMap_insert___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__10(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_insert___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__10___rarg), 3, 0);
return x_2;
}
}
uint8_t l_Std_AssocList_contains___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__15___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_name_eq(x_4, x_1);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
}
}
}
lean_object* l_Std_AssocList_contains___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__15(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_AssocList_contains___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__15___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_Std_AssocList_foldlM___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__18___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = l_Lean_Name_hash(x_4);
x_8 = lean_usize_modn(x_7, x_6);
lean_dec(x_6);
x_9 = lean_array_uget(x_1, x_8);
lean_ctor_set(x_2, 2, x_9);
x_10 = lean_array_uset(x_1, x_8, x_2);
x_1 = x_10;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
x_14 = lean_ctor_get(x_2, 2);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_2);
x_15 = lean_array_get_size(x_1);
x_16 = l_Lean_Name_hash(x_12);
x_17 = lean_usize_modn(x_16, x_15);
lean_dec(x_15);
x_18 = lean_array_uget(x_1, x_17);
x_19 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_13);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_array_uset(x_1, x_17, x_19);
x_1 = x_20;
x_2 = x_14;
goto _start;
}
}
}
}
lean_object* l_Std_AssocList_foldlM___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__18(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_AssocList_foldlM___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__18___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Std_HashMapImp_moveEntries___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__17___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Std_AssocList_foldlM___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__18___rarg(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
lean_object* l_Std_HashMapImp_moveEntries___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__17(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_HashMapImp_moveEntries___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__17___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Std_HashMapImp_expand___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__16___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(2u);
x_5 = lean_nat_mul(x_3, x_4);
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_5, x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Std_HashMapImp_moveEntries___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__17___rarg(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
lean_object* l_Std_HashMapImp_expand___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__16(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_HashMapImp_expand___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__16___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Std_AssocList_replace___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__19___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_ctor_get(x_3, 2);
x_9 = lean_name_eq(x_6, x_1);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = l_Std_AssocList_replace___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__19___rarg(x_1, x_2, x_8);
lean_ctor_set(x_3, 2, x_10);
return x_3;
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
x_13 = lean_ctor_get(x_3, 2);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
x_14 = lean_name_eq(x_11, x_1);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_Std_AssocList_replace___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__19___rarg(x_1, x_2, x_13);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_12);
lean_ctor_set(x_16, 2, x_15);
return x_16;
}
else
{
lean_object* x_17; 
lean_dec(x_12);
lean_dec(x_11);
x_17 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_2);
lean_ctor_set(x_17, 2, x_13);
return x_17;
}
}
}
}
}
lean_object* l_Std_AssocList_replace___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__19(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_AssocList_replace___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__19___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Std_HashMapImp_insert___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__14___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; uint8_t x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = l_Lean_Name_hash(x_2);
x_9 = lean_usize_modn(x_8, x_7);
x_10 = lean_array_uget(x_6, x_9);
x_11 = l_Std_AssocList_contains___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__15___rarg(x_2, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_5, x_12);
lean_dec(x_5);
x_14 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_3);
lean_ctor_set(x_14, 2, x_10);
x_15 = lean_array_uset(x_6, x_9, x_14);
x_16 = lean_nat_dec_le(x_13, x_7);
lean_dec(x_7);
if (x_16 == 0)
{
lean_object* x_17; 
lean_free_object(x_1);
x_17 = l_Std_HashMapImp_expand___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__16___rarg(x_13, x_15);
return x_17;
}
else
{
lean_ctor_set(x_1, 1, x_15);
lean_ctor_set(x_1, 0, x_13);
return x_1;
}
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_7);
x_18 = l_Std_AssocList_replace___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__19___rarg(x_2, x_3, x_10);
x_19 = lean_array_uset(x_6, x_9, x_18);
lean_ctor_set(x_1, 1, x_19);
return x_1;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; uint8_t x_26; 
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_1);
x_22 = lean_array_get_size(x_21);
x_23 = l_Lean_Name_hash(x_2);
x_24 = lean_usize_modn(x_23, x_22);
x_25 = lean_array_uget(x_21, x_24);
x_26 = l_Std_AssocList_contains___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__15___rarg(x_2, x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_20, x_27);
lean_dec(x_20);
x_29 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_29, 0, x_2);
lean_ctor_set(x_29, 1, x_3);
lean_ctor_set(x_29, 2, x_25);
x_30 = lean_array_uset(x_21, x_24, x_29);
x_31 = lean_nat_dec_le(x_28, x_22);
lean_dec(x_22);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = l_Std_HashMapImp_expand___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__16___rarg(x_28, x_30);
return x_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_28);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_22);
x_34 = l_Std_AssocList_replace___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__19___rarg(x_2, x_3, x_25);
x_35 = lean_array_uset(x_21, x_24, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_20);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
lean_object* l_Std_HashMapImp_insert___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__14(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_HashMapImp_insert___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__14___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_SMap_insert___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__9___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Std_PersistentHashMap_insert___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__10___rarg(x_6, x_2, x_3);
x_8 = 0;
lean_ctor_set(x_1, 1, x_7);
lean_ctor_set_uint8(x_1, sizeof(void*)*2, x_8);
return x_1;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = l_Std_PersistentHashMap_insert___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__10___rarg(x_10, x_2, x_3);
x_12 = 0;
x_13 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_11);
lean_ctor_set_uint8(x_13, sizeof(void*)*2, x_12);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_1);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_1, 0);
x_16 = l_Std_HashMapImp_insert___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__14___rarg(x_15, x_2, x_3);
x_17 = 1;
lean_ctor_set(x_1, 0, x_16);
lean_ctor_set_uint8(x_1, sizeof(void*)*2, x_17);
return x_1;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_1, 0);
x_19 = lean_ctor_get(x_1, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_1);
x_20 = l_Std_HashMapImp_insert___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__14___rarg(x_18, x_2, x_3);
x_21 = 1;
x_22 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_19);
lean_ctor_set_uint8(x_22, sizeof(void*)*2, x_21);
return x_22;
}
}
}
}
lean_object* l_Lean_SMap_insert___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__9(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_SMap_insert___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__9___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Std_PersistentHashMap_insertAux_traverse___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__23___rarg(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_9 = lean_array_fget(x_2, x_5);
x_10 = lean_array_fget(x_3, x_5);
x_11 = l_Lean_Name_hash(x_9);
x_12 = 1;
x_13 = x_1 - x_12;
x_14 = 5;
x_15 = x_14 * x_13;
x_16 = x_11 >> x_15;
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_5, x_17);
lean_dec(x_5);
x_19 = l_Std_PersistentHashMap_insertAux___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__22___rarg(x_6, x_16, x_1, x_9, x_10);
x_4 = lean_box(0);
x_5 = x_18;
x_6 = x_19;
goto _start;
}
}
}
lean_object* l_Std_PersistentHashMap_insertAux_traverse___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__23(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_insertAux_traverse___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__23___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__24___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_18 = lean_name_eq(x_3, x_17);
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
lean_object* l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__24(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__24___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__22___rarg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
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
x_10 = l_Std_PersistentHashMap_insertAux___rarg___closed__2;
x_11 = x_2 & x_10;
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
x_16 = lean_box(2);
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
x_21 = lean_name_eq(x_4, x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_free_object(x_15);
x_22 = l_Std_PersistentHashMap_mkCollisionNode___rarg(x_19, x_20, x_4, x_5);
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
x_28 = lean_name_eq(x_4, x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = l_Std_PersistentHashMap_mkCollisionNode___rarg(x_26, x_27, x_4, x_5);
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
x_36 = x_2 >> x_9;
x_37 = x_3 + x_8;
x_38 = l_Std_PersistentHashMap_insertAux___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__22___rarg(x_35, x_36, x_37, x_4, x_5);
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
x_41 = x_2 >> x_9;
x_42 = x_3 + x_8;
x_43 = l_Std_PersistentHashMap_insertAux___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__22___rarg(x_40, x_41, x_42, x_4, x_5);
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
x_51 = l_Std_PersistentHashMap_insertAux___rarg___closed__2;
x_52 = x_2 & x_51;
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
x_58 = lean_box(2);
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
x_63 = lean_name_eq(x_4, x_60);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_62);
x_64 = l_Std_PersistentHashMap_mkCollisionNode___rarg(x_60, x_61, x_4, x_5);
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
x_73 = x_2 >> x_50;
x_74 = x_3 + x_49;
x_75 = l_Std_PersistentHashMap_insertAux___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__22___rarg(x_71, x_73, x_74, x_4, x_5);
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
x_84 = l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__24___rarg(x_1, x_83, x_4, x_5);
x_85 = 7;
x_86 = x_85 <= x_3;
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_87 = l_Std_PersistentHashMap_getCollisionNodeSize___rarg(x_84);
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
x_92 = l_Std_PersistentHashMap_insertAux___rarg___closed__3;
x_93 = l_Std_PersistentHashMap_insertAux_traverse___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__23___rarg(x_3, x_90, x_91, lean_box(0), x_83, x_92);
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
x_98 = l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__24___rarg(x_96, x_97, x_4, x_5);
x_99 = 7;
x_100 = x_99 <= x_3;
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_101 = l_Std_PersistentHashMap_getCollisionNodeSize___rarg(x_98);
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
x_106 = l_Std_PersistentHashMap_insertAux___rarg___closed__3;
x_107 = l_Std_PersistentHashMap_insertAux_traverse___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__23___rarg(x_3, x_104, x_105, lean_box(0), x_97, x_106);
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
lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__22(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_insertAux___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__22___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Std_PersistentHashMap_insert___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__21___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_Name_hash(x_2);
x_8 = 1;
x_9 = l_Std_PersistentHashMap_insertAux___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__22___rarg(x_5, x_7, x_8, x_2, x_3);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_6, x_10);
lean_dec(x_6);
lean_ctor_set(x_1, 1, x_11);
lean_ctor_set(x_1, 0, x_9);
return x_1;
}
else
{
lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_1);
x_14 = l_Lean_Name_hash(x_2);
x_15 = 1;
x_16 = l_Std_PersistentHashMap_insertAux___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__22___rarg(x_12, x_14, x_15, x_2, x_3);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_13, x_17);
lean_dec(x_13);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
lean_object* l_Std_PersistentHashMap_insert___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__21(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_insert___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__21___rarg), 3, 0);
return x_2;
}
}
uint8_t l_Std_AssocList_contains___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__26___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_name_eq(x_4, x_1);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
}
}
}
lean_object* l_Std_AssocList_contains___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__26(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_AssocList_contains___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__26___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_Std_AssocList_foldlM___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__29___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = l_Lean_Name_hash(x_4);
x_8 = lean_usize_modn(x_7, x_6);
lean_dec(x_6);
x_9 = lean_array_uget(x_1, x_8);
lean_ctor_set(x_2, 2, x_9);
x_10 = lean_array_uset(x_1, x_8, x_2);
x_1 = x_10;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
x_14 = lean_ctor_get(x_2, 2);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_2);
x_15 = lean_array_get_size(x_1);
x_16 = l_Lean_Name_hash(x_12);
x_17 = lean_usize_modn(x_16, x_15);
lean_dec(x_15);
x_18 = lean_array_uget(x_1, x_17);
x_19 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_13);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_array_uset(x_1, x_17, x_19);
x_1 = x_20;
x_2 = x_14;
goto _start;
}
}
}
}
lean_object* l_Std_AssocList_foldlM___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__29(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_AssocList_foldlM___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__29___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Std_HashMapImp_moveEntries___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__28___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Std_AssocList_foldlM___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__29___rarg(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
lean_object* l_Std_HashMapImp_moveEntries___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__28(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_HashMapImp_moveEntries___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__28___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Std_HashMapImp_expand___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__27___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(2u);
x_5 = lean_nat_mul(x_3, x_4);
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_5, x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Std_HashMapImp_moveEntries___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__28___rarg(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
lean_object* l_Std_HashMapImp_expand___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__27(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_HashMapImp_expand___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__27___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Std_AssocList_replace___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__30___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_ctor_get(x_3, 2);
x_9 = lean_name_eq(x_6, x_1);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = l_Std_AssocList_replace___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__30___rarg(x_1, x_2, x_8);
lean_ctor_set(x_3, 2, x_10);
return x_3;
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
x_13 = lean_ctor_get(x_3, 2);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
x_14 = lean_name_eq(x_11, x_1);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_Std_AssocList_replace___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__30___rarg(x_1, x_2, x_13);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_12);
lean_ctor_set(x_16, 2, x_15);
return x_16;
}
else
{
lean_object* x_17; 
lean_dec(x_12);
lean_dec(x_11);
x_17 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_2);
lean_ctor_set(x_17, 2, x_13);
return x_17;
}
}
}
}
}
lean_object* l_Std_AssocList_replace___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__30(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_AssocList_replace___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__30___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Std_HashMapImp_insert___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__25___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; uint8_t x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = l_Lean_Name_hash(x_2);
x_9 = lean_usize_modn(x_8, x_7);
x_10 = lean_array_uget(x_6, x_9);
x_11 = l_Std_AssocList_contains___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__26___rarg(x_2, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_5, x_12);
lean_dec(x_5);
x_14 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_3);
lean_ctor_set(x_14, 2, x_10);
x_15 = lean_array_uset(x_6, x_9, x_14);
x_16 = lean_nat_dec_le(x_13, x_7);
lean_dec(x_7);
if (x_16 == 0)
{
lean_object* x_17; 
lean_free_object(x_1);
x_17 = l_Std_HashMapImp_expand___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__27___rarg(x_13, x_15);
return x_17;
}
else
{
lean_ctor_set(x_1, 1, x_15);
lean_ctor_set(x_1, 0, x_13);
return x_1;
}
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_7);
x_18 = l_Std_AssocList_replace___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__30___rarg(x_2, x_3, x_10);
x_19 = lean_array_uset(x_6, x_9, x_18);
lean_ctor_set(x_1, 1, x_19);
return x_1;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; uint8_t x_26; 
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_1);
x_22 = lean_array_get_size(x_21);
x_23 = l_Lean_Name_hash(x_2);
x_24 = lean_usize_modn(x_23, x_22);
x_25 = lean_array_uget(x_21, x_24);
x_26 = l_Std_AssocList_contains___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__26___rarg(x_2, x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_20, x_27);
lean_dec(x_20);
x_29 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_29, 0, x_2);
lean_ctor_set(x_29, 1, x_3);
lean_ctor_set(x_29, 2, x_25);
x_30 = lean_array_uset(x_21, x_24, x_29);
x_31 = lean_nat_dec_le(x_28, x_22);
lean_dec(x_22);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = l_Std_HashMapImp_expand___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__27___rarg(x_28, x_30);
return x_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_28);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_22);
x_34 = l_Std_AssocList_replace___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__30___rarg(x_2, x_3, x_25);
x_35 = lean_array_uset(x_21, x_24, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_20);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
lean_object* l_Std_HashMapImp_insert___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__25(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_HashMapImp_insert___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__25___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_SMap_insert___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__20___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Std_PersistentHashMap_insert___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__21___rarg(x_6, x_2, x_3);
x_8 = 0;
lean_ctor_set(x_1, 1, x_7);
lean_ctor_set_uint8(x_1, sizeof(void*)*2, x_8);
return x_1;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = l_Std_PersistentHashMap_insert___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__21___rarg(x_10, x_2, x_3);
x_12 = 0;
x_13 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_11);
lean_ctor_set_uint8(x_13, sizeof(void*)*2, x_12);
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_1);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_1, 0);
x_16 = l_Std_HashMapImp_insert___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__25___rarg(x_15, x_2, x_3);
x_17 = 1;
lean_ctor_set(x_1, 0, x_16);
lean_ctor_set_uint8(x_1, sizeof(void*)*2, x_17);
return x_1;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_1, 0);
x_19 = lean_ctor_get(x_1, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_1);
x_20 = l_Std_HashMapImp_insert___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__25___rarg(x_18, x_2, x_3);
x_21 = 1;
x_22 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_19);
lean_ctor_set_uint8(x_22, sizeof(void*)*2, x_21);
return x_22;
}
}
}
}
lean_object* l_Lean_SMap_insert___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__20(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_SMap_insert___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__20___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_ScopedEnvExtension_ScopedEntries_insert___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_1);
x_4 = l_Lean_SMap_find_x3f___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__1___rarg(x_1, x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Std_PersistentArray_empty___closed__1;
x_6 = l_Std_PersistentArray_push___rarg(x_5, x_3);
x_7 = l_Lean_SMap_insert___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__9___rarg(x_1, x_2, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
lean_dec(x_4);
x_9 = l_Std_PersistentArray_push___rarg(x_8, x_3);
x_10 = l_Lean_SMap_insert___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__20___rarg(x_1, x_2, x_9);
return x_10;
}
}
}
lean_object* l_Lean_ScopedEnvExtension_ScopedEntries_insert(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_ScopedEntries_insert___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__4___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_PersistentHashMap_findAtAux___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__4___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Std_PersistentHashMap_findAux___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Std_PersistentHashMap_findAux___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__3___rarg(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_PersistentHashMap_find_x3f___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__2___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Std_AssocList_find_x3f___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__6___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_AssocList_find_x3f___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__6___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__5___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_HashMapImp_find_x3f___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__5___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Std_AssocList_find_x3f___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__8___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_AssocList_find_x3f___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__8___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__7___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_HashMapImp_find_x3f___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__7___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_SMap_find_x3f___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_SMap_find_x3f___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__1___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Std_PersistentHashMap_insertAux_traverse___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__12___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; lean_object* x_8; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = l_Std_PersistentHashMap_insertAux_traverse___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__12___rarg(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__11___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Std_PersistentHashMap_insertAux___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__11___rarg(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
lean_object* l_Std_AssocList_contains___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__15___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_AssocList_contains___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__15___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Std_PersistentHashMap_insertAux_traverse___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__23___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; lean_object* x_8; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = l_Std_PersistentHashMap_insertAux_traverse___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__23___rarg(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__22___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Std_PersistentHashMap_insertAux___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__22___rarg(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
lean_object* l_Std_AssocList_contains___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__26___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_AssocList_contains___at_Lean_ScopedEnvExtension_ScopedEntries_insert___spec__26___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_ScopedEnvExtension_addImportedFn_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_8 = lean_apply_2(x_3, x_6, x_7);
return x_8;
}
}
}
lean_object* l_Lean_ScopedEnvExtension_addImportedFn_match__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_addImportedFn_match__1___rarg), 3, 0);
return x_3;
}
}
lean_object* l_Lean_ScopedEnvExtension_addImportedFn_match__2___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_ScopedEnvExtension_addImportedFn_match__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_addImportedFn_match__2___rarg), 2, 0);
return x_4;
}
}
lean_object* l_Lean_ScopedEnvExtension_addImportedFn_match__3___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_ScopedEnvExtension_addImportedFn_match__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_addImportedFn_match__3___rarg), 2, 0);
return x_4;
}
}
lean_object* l_Lean_ScopedEnvExtension_addImportedFn_match__4___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_ScopedEnvExtension_addImportedFn_match__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_addImportedFn_match__4___rarg), 2, 0);
return x_4;
}
}
lean_object* l_Lean_ScopedEnvExtension_addImportedFn_match__5___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_ScopedEnvExtension_addImportedFn_match__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_addImportedFn_match__5___rarg), 2, 0);
return x_4;
}
}
lean_object* l_Std_mkHashMap___at_Lean_ScopedEnvExtension_addImportedFn___spec__1___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* l_Std_mkHashMap___at_Lean_ScopedEnvExtension_addImportedFn___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_mkHashMap___at_Lean_ScopedEnvExtension_addImportedFn___spec__1___rarg), 1, 0);
return x_2;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_ScopedEnvExtension_addImportedFn___spec__2___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = x_4 < x_3;
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; 
x_10 = lean_array_uget(x_2, x_4);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_5);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_5, 0);
x_13 = lean_ctor_get(x_5, 1);
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_ctor_get(x_1, 2);
lean_inc(x_15);
lean_inc(x_6);
lean_inc(x_12);
x_16 = lean_apply_4(x_15, x_12, x_14, x_6, x_7);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_1, 4);
lean_inc(x_19);
x_20 = lean_apply_2(x_19, x_12, x_17);
lean_ctor_set(x_5, 0, x_20);
x_21 = 1;
x_22 = x_4 + x_21;
x_4 = x_22;
x_7 = x_18;
goto _start;
}
else
{
uint8_t x_24; 
lean_free_object(x_5);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_16);
if (x_24 == 0)
{
return x_16;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_16, 0);
x_26 = lean_ctor_get(x_16, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_16);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_5, 0);
x_29 = lean_ctor_get(x_5, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_5);
x_30 = lean_ctor_get(x_10, 0);
lean_inc(x_30);
lean_dec(x_10);
x_31 = lean_ctor_get(x_1, 2);
lean_inc(x_31);
lean_inc(x_6);
lean_inc(x_28);
x_32 = lean_apply_4(x_31, x_28, x_30, x_6, x_7);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; size_t x_38; size_t x_39; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_ctor_get(x_1, 4);
lean_inc(x_35);
x_36 = lean_apply_2(x_35, x_28, x_33);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_29);
x_38 = 1;
x_39 = x_4 + x_38;
x_4 = x_39;
x_5 = x_37;
x_7 = x_34;
goto _start;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_6);
lean_dec(x_1);
x_41 = lean_ctor_get(x_32, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_32, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_43 = x_32;
} else {
 lean_dec_ref(x_32);
 x_43 = lean_box(0);
}
if (lean_is_scalar(x_43)) {
 x_44 = lean_alloc_ctor(1, 2, 0);
} else {
 x_44 = x_43;
}
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
}
else
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_5);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_46 = lean_ctor_get(x_5, 0);
x_47 = lean_ctor_get(x_5, 1);
x_48 = lean_ctor_get(x_10, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_10, 1);
lean_inc(x_49);
lean_dec(x_10);
x_50 = lean_ctor_get(x_1, 2);
lean_inc(x_50);
lean_inc(x_6);
lean_inc(x_46);
x_51 = lean_apply_4(x_50, x_46, x_49, x_6, x_7);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; size_t x_55; size_t x_56; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = l_Lean_ScopedEnvExtension_ScopedEntries_insert___rarg(x_47, x_48, x_52);
lean_ctor_set(x_5, 1, x_54);
x_55 = 1;
x_56 = x_4 + x_55;
x_4 = x_56;
x_7 = x_53;
goto _start;
}
else
{
uint8_t x_58; 
lean_dec(x_48);
lean_free_object(x_5);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_6);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_51);
if (x_58 == 0)
{
return x_51;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_51, 0);
x_60 = lean_ctor_get(x_51, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_51);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_62 = lean_ctor_get(x_5, 0);
x_63 = lean_ctor_get(x_5, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_5);
x_64 = lean_ctor_get(x_10, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_10, 1);
lean_inc(x_65);
lean_dec(x_10);
x_66 = lean_ctor_get(x_1, 2);
lean_inc(x_66);
lean_inc(x_6);
lean_inc(x_62);
x_67 = lean_apply_4(x_66, x_62, x_65, x_6, x_7);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; size_t x_72; size_t x_73; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = l_Lean_ScopedEnvExtension_ScopedEntries_insert___rarg(x_63, x_64, x_68);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_62);
lean_ctor_set(x_71, 1, x_70);
x_72 = 1;
x_73 = x_4 + x_72;
x_4 = x_73;
x_5 = x_71;
x_7 = x_69;
goto _start;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_6);
lean_dec(x_1);
x_75 = lean_ctor_get(x_67, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_67, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_77 = x_67;
} else {
 lean_dec_ref(x_67);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(1, 2, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
}
}
}
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_ScopedEnvExtension_addImportedFn___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_ScopedEnvExtension_addImportedFn___spec__2___rarg___boxed), 7, 0);
return x_4;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_ScopedEnvExtension_addImportedFn___spec__3___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = x_4 < x_3;
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_uget(x_2, x_4);
x_11 = !lean_is_exclusive(x_5);
if (x_11 == 0)
{
lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_12 = lean_array_get_size(x_10);
x_13 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_14 = 0;
lean_inc(x_6);
lean_inc(x_1);
x_15 = l_Array_forInUnsafe_loop___at_Lean_ScopedEnvExtension_addImportedFn___spec__2___rarg(x_1, x_10, x_13, x_14, x_5, x_6, x_7);
lean_dec(x_10);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
size_t x_19; size_t x_20; 
x_19 = 1;
x_20 = x_4 + x_19;
x_4 = x_20;
x_5 = x_16;
x_7 = x_17;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; 
x_22 = lean_ctor_get(x_16, 0);
x_23 = lean_ctor_get(x_16, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_16);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = 1;
x_26 = x_4 + x_25;
x_4 = x_26;
x_5 = x_24;
x_7 = x_17;
goto _start;
}
}
else
{
uint8_t x_28; 
lean_dec(x_6);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_15);
if (x_28 == 0)
{
return x_15;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_15, 0);
x_30 = lean_ctor_get(x_15, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_15);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; size_t x_36; size_t x_37; lean_object* x_38; 
x_32 = lean_ctor_get(x_5, 0);
x_33 = lean_ctor_get(x_5, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_5);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_array_get_size(x_10);
x_36 = lean_usize_of_nat(x_35);
lean_dec(x_35);
x_37 = 0;
lean_inc(x_6);
lean_inc(x_1);
x_38 = l_Array_forInUnsafe_loop___at_Lean_ScopedEnvExtension_addImportedFn___spec__2___rarg(x_1, x_10, x_36, x_37, x_34, x_6, x_7);
lean_dec(x_10);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; size_t x_45; size_t x_46; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_ctor_get(x_39, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_43 = x_39;
} else {
 lean_dec_ref(x_39);
 x_43 = lean_box(0);
}
if (lean_is_scalar(x_43)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_43;
}
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_42);
x_45 = 1;
x_46 = x_4 + x_45;
x_4 = x_46;
x_5 = x_44;
x_7 = x_40;
goto _start;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_6);
lean_dec(x_1);
x_48 = lean_ctor_get(x_38, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_38, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_50 = x_38;
} else {
 lean_dec_ref(x_38);
 x_50 = lean_box(0);
}
if (lean_is_scalar(x_50)) {
 x_51 = lean_alloc_ctor(1, 2, 0);
} else {
 x_51 = x_50;
}
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
}
}
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_ScopedEnvExtension_addImportedFn___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_ScopedEnvExtension_addImportedFn___spec__3___rarg___boxed), 7, 0);
return x_4;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_addImportedFn___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_addImportedFn___rarg___closed__2() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = l_Lean_ScopedEnvExtension_addImportedFn___rarg___closed__1;
x_3 = l_Lean_LocalContext_fvarIdToDecl___default___closed__1;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
lean_object* l_Lean_ScopedEnvExtension_addImportedFn___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_apply_1(x_5, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_ScopedEnvExtension_addImportedFn___rarg___closed__2;
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_array_get_size(x_2);
x_12 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_13 = 0;
x_14 = l_Array_forInUnsafe_loop___at_Lean_ScopedEnvExtension_addImportedFn___spec__3___rarg(x_1, x_2, x_12, x_13, x_10, x_3, x_8);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_NameSet_empty;
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_18);
lean_ctor_set(x_23, 2, x_21);
lean_ctor_set(x_14, 0, x_23);
return x_14;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_24 = lean_ctor_get(x_14, 0);
x_25 = lean_ctor_get(x_14, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_14);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = l_Lean_NameSet_empty;
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_27);
lean_ctor_set(x_32, 2, x_30);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_25);
return x_33;
}
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_14);
if (x_34 == 0)
{
return x_14;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_14, 0);
x_36 = lean_ctor_get(x_14, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_14);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_3);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_6);
if (x_38 == 0)
{
return x_6;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_6, 0);
x_40 = lean_ctor_get(x_6, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_6);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
lean_object* l_Lean_ScopedEnvExtension_addImportedFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_addImportedFn___rarg___boxed), 4, 0);
return x_4;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_ScopedEnvExtension_addImportedFn___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l_Array_forInUnsafe_loop___at_Lean_ScopedEnvExtension_addImportedFn___spec__2___rarg(x_1, x_2, x_8, x_9, x_5, x_6, x_7);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_ScopedEnvExtension_addImportedFn___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l_Array_forInUnsafe_loop___at_Lean_ScopedEnvExtension_addImportedFn___spec__3___rarg(x_1, x_2, x_8, x_9, x_5, x_6, x_7);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_Lean_ScopedEnvExtension_addImportedFn___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_ScopedEnvExtension_addImportedFn___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_ScopedEnvExtension_addEntryFn_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_8 = lean_apply_2(x_3, x_6, x_7);
return x_8;
}
}
}
lean_object* l_Lean_ScopedEnvExtension_addEntryFn_match__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_addEntryFn_match__1___rarg), 3, 0);
return x_3;
}
}
lean_object* l_Lean_ScopedEnvExtension_addEntryFn_match__2___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_3(x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_ScopedEnvExtension_addEntryFn_match__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_addEntryFn_match__2___rarg), 2, 0);
return x_5;
}
}
lean_object* l_List_map___at_Lean_ScopedEnvExtension_addEntryFn___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_ctor_get(x_1, 4);
lean_inc(x_8);
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_2);
x_11 = lean_apply_2(x_8, x_10, x_2);
lean_ctor_set(x_6, 0, x_11);
x_12 = l_List_map___at_Lean_ScopedEnvExtension_addEntryFn___spec__1___rarg(x_1, x_2, x_7);
lean_ctor_set(x_3, 1, x_12);
return x_3;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_6, 0);
x_14 = lean_ctor_get(x_6, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_6);
lean_inc(x_2);
x_15 = lean_apply_2(x_8, x_13, x_2);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = l_List_map___at_Lean_ScopedEnvExtension_addEntryFn___spec__1___rarg(x_1, x_2, x_7);
lean_ctor_set(x_3, 1, x_17);
lean_ctor_set(x_3, 0, x_16);
return x_3;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_18 = lean_ctor_get(x_3, 0);
x_19 = lean_ctor_get(x_3, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_3);
x_20 = lean_ctor_get(x_1, 4);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_23 = x_18;
} else {
 lean_dec_ref(x_18);
 x_23 = lean_box(0);
}
lean_inc(x_2);
x_24 = lean_apply_2(x_20, x_21, x_2);
if (lean_is_scalar(x_23)) {
 x_25 = lean_alloc_ctor(0, 2, 0);
} else {
 x_25 = x_23;
}
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
x_26 = l_List_map___at_Lean_ScopedEnvExtension_addEntryFn___spec__1___rarg(x_1, x_2, x_19);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
lean_object* l_List_map___at_Lean_ScopedEnvExtension_addEntryFn___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_List_map___at_Lean_ScopedEnvExtension_addEntryFn___spec__1___rarg), 3, 0);
return x_4;
}
}
lean_object* l_List_map___at_Lean_ScopedEnvExtension_addEntryFn___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
lean_dec(x_3);
lean_dec(x_1);
x_5 = lean_box(0);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_ctor_get(x_4, 1);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
x_11 = l_Lean_NameSet_contains(x_10, x_2);
lean_inc(x_3);
lean_inc(x_1);
x_12 = l_List_map___at_Lean_ScopedEnvExtension_addEntryFn___spec__2___rarg(x_1, x_2, x_3, x_8);
if (x_11 == 0)
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_1);
lean_ctor_set(x_4, 1, x_12);
return x_4;
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_7);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_7, 1);
lean_dec(x_14);
x_15 = lean_ctor_get(x_7, 0);
lean_dec(x_15);
x_16 = lean_ctor_get(x_1, 4);
lean_inc(x_16);
lean_dec(x_1);
x_17 = lean_apply_2(x_16, x_9, x_3);
lean_ctor_set(x_7, 0, x_17);
lean_ctor_set(x_4, 1, x_12);
return x_4;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_7);
x_18 = lean_ctor_get(x_1, 4);
lean_inc(x_18);
lean_dec(x_1);
x_19 = lean_apply_2(x_18, x_9, x_3);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_10);
lean_ctor_set(x_4, 1, x_12);
lean_ctor_set(x_4, 0, x_20);
return x_4;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_4, 0);
x_22 = lean_ctor_get(x_4, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_4);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
x_25 = l_Lean_NameSet_contains(x_24, x_2);
lean_inc(x_3);
lean_inc(x_1);
x_26 = l_List_map___at_Lean_ScopedEnvExtension_addEntryFn___spec__2___rarg(x_1, x_2, x_3, x_22);
if (x_25 == 0)
{
lean_object* x_27; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_3);
lean_dec(x_1);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_21);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_28 = x_21;
} else {
 lean_dec_ref(x_21);
 x_28 = lean_box(0);
}
x_29 = lean_ctor_get(x_1, 4);
lean_inc(x_29);
lean_dec(x_1);
x_30 = lean_apply_2(x_29, x_23, x_3);
if (lean_is_scalar(x_28)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_28;
}
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_24);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_26);
return x_32;
}
}
}
}
}
lean_object* l_List_map___at_Lean_ScopedEnvExtension_addEntryFn___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_List_map___at_Lean_ScopedEnvExtension_addEntryFn___spec__2___rarg___boxed), 4, 0);
return x_4;
}
}
lean_object* l_Lean_ScopedEnvExtension_addEntryFn___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 2);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_inc(x_1);
x_9 = l_List_map___at_Lean_ScopedEnvExtension_addEntryFn___spec__1___rarg(x_1, x_8, x_6);
x_10 = lean_ctor_get(x_1, 3);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_apply_1(x_10, x_8);
lean_ctor_set(x_3, 0, x_11);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_7);
lean_ctor_set(x_2, 2, x_12);
lean_ctor_set(x_2, 0, x_9);
return x_2;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_ctor_get(x_2, 2);
x_15 = lean_ctor_get(x_3, 0);
lean_inc(x_15);
lean_dec(x_3);
lean_inc(x_15);
lean_inc(x_1);
x_16 = l_List_map___at_Lean_ScopedEnvExtension_addEntryFn___spec__1___rarg(x_1, x_15, x_13);
x_17 = lean_ctor_get(x_1, 3);
lean_inc(x_17);
lean_dec(x_1);
x_18 = lean_apply_1(x_17, x_15);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_14);
lean_ctor_set(x_2, 2, x_20);
lean_ctor_set(x_2, 0, x_16);
return x_2;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_21 = lean_ctor_get(x_2, 0);
x_22 = lean_ctor_get(x_2, 1);
x_23 = lean_ctor_get(x_2, 2);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_2);
x_24 = lean_ctor_get(x_3, 0);
lean_inc(x_24);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 x_25 = x_3;
} else {
 lean_dec_ref(x_3);
 x_25 = lean_box(0);
}
lean_inc(x_24);
lean_inc(x_1);
x_26 = l_List_map___at_Lean_ScopedEnvExtension_addEntryFn___spec__1___rarg(x_1, x_24, x_21);
x_27 = lean_ctor_get(x_1, 3);
lean_inc(x_27);
lean_dec(x_1);
x_28 = lean_apply_1(x_27, x_24);
if (lean_is_scalar(x_25)) {
 x_29 = lean_alloc_ctor(0, 1, 0);
} else {
 x_29 = x_25;
}
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_23);
x_31 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_31, 0, x_26);
lean_ctor_set(x_31, 1, x_22);
lean_ctor_set(x_31, 2, x_30);
return x_31;
}
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_2);
if (x_32 == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_3);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_34 = lean_ctor_get(x_2, 0);
x_35 = lean_ctor_get(x_2, 1);
x_36 = lean_ctor_get(x_2, 2);
x_37 = lean_ctor_get(x_3, 0);
x_38 = lean_ctor_get(x_3, 1);
lean_inc(x_38);
lean_inc(x_1);
x_39 = l_List_map___at_Lean_ScopedEnvExtension_addEntryFn___spec__2___rarg(x_1, x_37, x_38, x_34);
lean_inc(x_38);
lean_inc(x_37);
x_40 = l_Lean_ScopedEnvExtension_ScopedEntries_insert___rarg(x_35, x_37, x_38);
x_41 = lean_ctor_get(x_1, 3);
lean_inc(x_41);
lean_dec(x_1);
x_42 = lean_apply_1(x_41, x_38);
lean_ctor_set(x_3, 1, x_42);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_3);
lean_ctor_set(x_43, 1, x_36);
lean_ctor_set(x_2, 2, x_43);
lean_ctor_set(x_2, 1, x_40);
lean_ctor_set(x_2, 0, x_39);
return x_2;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_44 = lean_ctor_get(x_2, 0);
x_45 = lean_ctor_get(x_2, 1);
x_46 = lean_ctor_get(x_2, 2);
x_47 = lean_ctor_get(x_3, 0);
x_48 = lean_ctor_get(x_3, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_3);
lean_inc(x_48);
lean_inc(x_1);
x_49 = l_List_map___at_Lean_ScopedEnvExtension_addEntryFn___spec__2___rarg(x_1, x_47, x_48, x_44);
lean_inc(x_48);
lean_inc(x_47);
x_50 = l_Lean_ScopedEnvExtension_ScopedEntries_insert___rarg(x_45, x_47, x_48);
x_51 = lean_ctor_get(x_1, 3);
lean_inc(x_51);
lean_dec(x_1);
x_52 = lean_apply_1(x_51, x_48);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_47);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_46);
lean_ctor_set(x_2, 2, x_54);
lean_ctor_set(x_2, 1, x_50);
lean_ctor_set(x_2, 0, x_49);
return x_2;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_55 = lean_ctor_get(x_2, 0);
x_56 = lean_ctor_get(x_2, 1);
x_57 = lean_ctor_get(x_2, 2);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_2);
x_58 = lean_ctor_get(x_3, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_3, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_60 = x_3;
} else {
 lean_dec_ref(x_3);
 x_60 = lean_box(0);
}
lean_inc(x_59);
lean_inc(x_1);
x_61 = l_List_map___at_Lean_ScopedEnvExtension_addEntryFn___spec__2___rarg(x_1, x_58, x_59, x_55);
lean_inc(x_59);
lean_inc(x_58);
x_62 = l_Lean_ScopedEnvExtension_ScopedEntries_insert___rarg(x_56, x_58, x_59);
x_63 = lean_ctor_get(x_1, 3);
lean_inc(x_63);
lean_dec(x_1);
x_64 = lean_apply_1(x_63, x_59);
if (lean_is_scalar(x_60)) {
 x_65 = lean_alloc_ctor(1, 2, 0);
} else {
 x_65 = x_60;
}
lean_ctor_set(x_65, 0, x_58);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_57);
x_67 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_67, 0, x_61);
lean_ctor_set(x_67, 1, x_62);
lean_ctor_set(x_67, 2, x_66);
return x_67;
}
}
}
}
lean_object* l_Lean_ScopedEnvExtension_addEntryFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_addEntryFn___rarg), 3, 0);
return x_4;
}
}
lean_object* l_List_map___at_Lean_ScopedEnvExtension_addEntryFn___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_map___at_Lean_ScopedEnvExtension_addEntryFn___spec__2___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_ScopedEnvExtension_exportEntriesFn___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_ctor_get(x_1, 2);
lean_inc(x_2);
lean_dec(x_1);
x_3 = l_List_redLength___rarg(x_2);
x_4 = lean_mk_empty_array_with_capacity(x_3);
lean_dec(x_3);
x_5 = l_List_toArrayAux___rarg(x_2, x_4);
x_6 = l_Array_reverse___rarg(x_5);
return x_6;
}
}
lean_object* l_Lean_ScopedEnvExtension_exportEntriesFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_exportEntriesFn___rarg), 1, 0);
return x_4;
}
}
lean_object* l_Lean_instInhabitedScopedEnvExtension___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_alloc_closure((void*)(l_Monad_seqRight___default___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = lean_box(0);
x_6 = l_Lean_EnvExtensionInterfaceUnsafe_instInhabitedExt___closed__1;
x_7 = l_Lean_ScopedEnvExtension_instInhabitedDescr___rarg___closed__1;
x_8 = l_Lean_instInhabitedPersistentEnvExtension___closed__2;
x_9 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_6);
lean_ctor_set(x_9, 2, x_7);
lean_ctor_set(x_9, 3, x_4);
lean_ctor_set(x_9, 4, x_8);
x_10 = l_Lean_instInhabitedPersistentEnvExtension___closed__5;
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
lean_object* l_Lean_instInhabitedScopedEnvExtension(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_instInhabitedScopedEnvExtension___rarg), 3, 0);
return x_2;
}
}
lean_object* l_IO_mkRef___at_Lean_initFn____x40_Lean_ScopedEnvExtension___hyg_657____spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_st_mk_ref(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
}
lean_object* l_Lean_initFn____x40_Lean_ScopedEnvExtension___hyg_657_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Array_empty___closed__1;
x_3 = l_IO_mkRef___at_Lean_initFn____x40_Lean_ScopedEnvExtension___hyg_657____spec__1(x_2, x_1);
return x_3;
}
}
uint8_t l_Array_anyMUnsafe_any___at_Lean_registerScopedEnvExtensionUnsafe___spec__2___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_3 == x_4;
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_name_eq(x_7, x_8);
lean_dec(x_7);
if (x_9 == 0)
{
size_t x_10; size_t x_11; 
x_10 = 1;
x_11 = x_3 + x_10;
x_3 = x_11;
goto _start;
}
else
{
uint8_t x_13; 
x_13 = 1;
return x_13;
}
}
else
{
uint8_t x_14; 
x_14 = 0;
return x_14;
}
}
}
lean_object* l_Array_anyMUnsafe_any___at_Lean_registerScopedEnvExtensionUnsafe___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Array_anyMUnsafe_any___at_Lean_registerScopedEnvExtensionUnsafe___spec__2___rarg___boxed), 4, 0);
return x_4;
}
}
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_registerScopedEnvExtensionUnsafe___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_persistentEnvExtensionsRef;
x_4 = lean_st_ref_get(x_3, x_2);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_array_get_size(x_6);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_lt(x_9, x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_8);
lean_free_object(x_4);
lean_dec(x_6);
x_11 = lean_box(0);
x_12 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___lambda__2(x_1, x_11, x_7);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = lean_nat_dec_le(x_8, x_8);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_8);
lean_free_object(x_4);
lean_dec(x_6);
x_14 = lean_box(0);
x_15 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___lambda__2(x_1, x_14, x_7);
return x_15;
}
else
{
size_t x_16; size_t x_17; uint8_t x_18; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_18 = l_Array_anyMUnsafe_any___at_Lean_registerScopedEnvExtensionUnsafe___spec__2___rarg(x_1, x_6, x_16, x_17);
lean_dec(x_6);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_free_object(x_4);
x_19 = lean_box(0);
x_20 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___lambda__2(x_1, x_19, x_7);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
lean_dec(x_1);
x_22 = l_Lean_Name_toString___closed__1;
x_23 = l_Lean_Name_toStringWithSep(x_22, x_21);
x_24 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
x_25 = lean_string_append(x_24, x_23);
lean_dec(x_23);
x_26 = l_Lean_registerInternalExceptionId___closed__2;
x_27 = lean_string_append(x_25, x_26);
x_28 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 0, x_28);
return x_4;
}
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_29 = lean_ctor_get(x_4, 0);
x_30 = lean_ctor_get(x_4, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_4);
x_31 = lean_array_get_size(x_29);
x_32 = lean_unsigned_to_nat(0u);
x_33 = lean_nat_dec_lt(x_32, x_31);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_31);
lean_dec(x_29);
x_34 = lean_box(0);
x_35 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___lambda__2(x_1, x_34, x_30);
return x_35;
}
else
{
uint8_t x_36; 
x_36 = lean_nat_dec_le(x_31, x_31);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_31);
lean_dec(x_29);
x_37 = lean_box(0);
x_38 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___lambda__2(x_1, x_37, x_30);
return x_38;
}
else
{
size_t x_39; size_t x_40; uint8_t x_41; 
x_39 = 0;
x_40 = lean_usize_of_nat(x_31);
lean_dec(x_31);
x_41 = l_Array_anyMUnsafe_any___at_Lean_registerScopedEnvExtensionUnsafe___spec__2___rarg(x_1, x_29, x_39, x_40);
lean_dec(x_29);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_box(0);
x_43 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___lambda__2(x_1, x_42, x_30);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_44 = lean_ctor_get(x_1, 0);
lean_inc(x_44);
lean_dec(x_1);
x_45 = l_Lean_Name_toString___closed__1;
x_46 = l_Lean_Name_toStringWithSep(x_45, x_44);
x_47 = l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
x_48 = lean_string_append(x_47, x_46);
lean_dec(x_46);
x_49 = l_Lean_registerInternalExceptionId___closed__2;
x_50 = lean_string_append(x_48, x_49);
x_51 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_51, 0, x_50);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_30);
return x_52;
}
}
}
}
}
}
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_registerScopedEnvExtensionUnsafe___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_registerScopedEnvExtensionUnsafe___spec__1___rarg), 2, 0);
return x_4;
}
}
lean_object* l_Lean_registerScopedEnvExtensionUnsafe___rarg___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_List_lengthAux___rarg(x_2, x_3);
x_5 = l_Nat_repr(x_4);
x_6 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__4___closed__2;
x_8 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
static lean_object* _init_l_Lean_registerScopedEnvExtensionUnsafe___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_exportEntriesFn___rarg), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_registerScopedEnvExtensionUnsafe___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_registerScopedEnvExtensionUnsafe___rarg___lambda__1___boxed), 1, 0);
return x_1;
}
}
lean_object* l_Lean_registerScopedEnvExtensionUnsafe___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_inc(x_1);
x_4 = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_mkInitial___rarg), 2, 1);
lean_closure_set(x_4, 0, x_1);
lean_inc(x_1);
x_5 = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_addImportedFn___rarg___boxed), 4, 1);
lean_closure_set(x_5, 0, x_1);
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_addEntryFn___rarg), 3, 1);
lean_closure_set(x_6, 0, x_1);
x_7 = l_Lean_registerScopedEnvExtensionUnsafe___rarg___closed__1;
x_8 = l_Lean_registerScopedEnvExtensionUnsafe___rarg___closed__2;
x_9 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_4);
lean_ctor_set(x_9, 2, x_5);
lean_ctor_set(x_9, 3, x_6);
lean_ctor_set(x_9, 4, x_7);
lean_ctor_set(x_9, 5, x_8);
x_10 = l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_registerScopedEnvExtensionUnsafe___spec__1___rarg(x_9, x_2);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_11);
x_14 = l_Lean_scopedEnvExtensionsRef;
x_15 = lean_st_ref_take(x_14, x_12);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_13);
x_18 = x_13;
x_19 = lean_array_push(x_16, x_18);
x_20 = lean_st_ref_set(x_14, x_19, x_17);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
lean_ctor_set(x_20, 0, x_13);
return x_20;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_13);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_10);
if (x_25 == 0)
{
return x_10;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_10, 0);
x_27 = lean_ctor_get(x_10, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_10);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
lean_object* l_Lean_registerScopedEnvExtensionUnsafe(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_registerScopedEnvExtensionUnsafe___rarg), 2, 0);
return x_4;
}
}
lean_object* l_Array_anyMUnsafe_any___at_Lean_registerScopedEnvExtensionUnsafe___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_registerScopedEnvExtensionUnsafe___spec__2___rarg(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
lean_object* l_Lean_registerScopedEnvExtensionUnsafe___rarg___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_registerScopedEnvExtensionUnsafe___rarg___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_registerScopedEnvExtension___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_IO_instInhabitedError___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_registerScopedEnvExtension(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_registerScopedEnvExtension___rarg), 1, 0);
return x_5;
}
}
lean_object* l_Lean_registerScopedEnvExtension___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_registerScopedEnvExtension(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
lean_object* l_Lean_ScopedEnvExtension_pushScope_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_2(x_3, x_6, x_7);
return x_8;
}
}
}
lean_object* l_Lean_ScopedEnvExtension_pushScope_match__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_pushScope_match__1___rarg), 3, 0);
return x_3;
}
}
lean_object* l_Lean_ScopedEnvExtension_pushScope___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = l_Lean_PersistentEnvExtension_getState___rarg(x_3, x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_dec(x_4);
return x_2;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_4, 0);
lean_dec(x_7);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_5);
lean_ctor_set(x_4, 0, x_10);
x_11 = l_Lean_PersistentEnvExtension_setState___rarg(x_3, x_2, x_4);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_5, 0);
x_13 = lean_ctor_get(x_5, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_5);
lean_inc(x_12);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set(x_4, 0, x_15);
x_16 = l_Lean_PersistentEnvExtension_setState___rarg(x_3, x_2, x_4);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_17 = lean_ctor_get(x_4, 1);
x_18 = lean_ctor_get(x_4, 2);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_4);
x_19 = lean_ctor_get(x_5, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_5, 1);
lean_inc(x_20);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_21 = x_5;
} else {
 lean_dec_ref(x_5);
 x_21 = lean_box(0);
}
lean_inc(x_19);
if (lean_is_scalar(x_21)) {
 x_22 = lean_alloc_ctor(1, 2, 0);
} else {
 x_22 = x_21;
}
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_20);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_19);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_17);
lean_ctor_set(x_24, 2, x_18);
x_25 = l_Lean_PersistentEnvExtension_setState___rarg(x_3, x_2, x_24);
return x_25;
}
}
}
}
lean_object* l_Lean_ScopedEnvExtension_pushScope(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_pushScope___rarg___boxed), 2, 0);
return x_4;
}
}
lean_object* l_Lean_ScopedEnvExtension_pushScope___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_ScopedEnvExtension_pushScope___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_ScopedEnvExtension_popScope_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_apply_1(x_3, x_1);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
lean_dec(x_2);
x_6 = lean_apply_1(x_3, x_1);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
lean_dec(x_5);
x_10 = lean_apply_3(x_2, x_7, x_8, x_9);
return x_10;
}
}
}
}
lean_object* l_Lean_ScopedEnvExtension_popScope_match__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_popScope_match__1___rarg), 3, 0);
return x_3;
}
}
lean_object* l_Lean_ScopedEnvExtension_popScope___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = l_Lean_PersistentEnvExtension_getState___rarg(x_3, x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_dec(x_4);
return x_2;
}
else
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_dec(x_4);
return x_2;
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_4, 0);
lean_dec(x_8);
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; 
lean_ctor_set(x_4, 0, x_6);
x_10 = l_Lean_PersistentEnvExtension_setState___rarg(x_3, x_2, x_4);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_6, 0);
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_6);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
lean_ctor_set(x_4, 0, x_13);
x_14 = l_Lean_PersistentEnvExtension_setState___rarg(x_3, x_2, x_4);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_15 = lean_ctor_get(x_4, 1);
x_16 = lean_ctor_get(x_4, 2);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_4);
x_17 = lean_ctor_get(x_6, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_6, 1);
lean_inc(x_18);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_19 = x_6;
} else {
 lean_dec_ref(x_6);
 x_19 = lean_box(0);
}
if (lean_is_scalar(x_19)) {
 x_20 = lean_alloc_ctor(1, 2, 0);
} else {
 x_20 = x_19;
}
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_18);
x_21 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_15);
lean_ctor_set(x_21, 2, x_16);
x_22 = l_Lean_PersistentEnvExtension_setState___rarg(x_3, x_2, x_21);
return x_22;
}
}
}
}
}
lean_object* l_Lean_ScopedEnvExtension_popScope(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_popScope___rarg___boxed), 2, 0);
return x_4;
}
}
lean_object* l_Lean_ScopedEnvExtension_popScope___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_ScopedEnvExtension_popScope___rarg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_ScopedEnvExtension_addEntry___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_3);
x_6 = l_Lean_PersistentEnvExtension_addEntry___rarg(x_4, x_2, x_5);
return x_6;
}
}
lean_object* l_Lean_ScopedEnvExtension_addEntry(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_addEntry___rarg), 3, 0);
return x_4;
}
}
lean_object* l_Lean_ScopedEnvExtension_addScopedEntry___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_4);
x_7 = l_Lean_PersistentEnvExtension_addEntry___rarg(x_5, x_2, x_6);
return x_7;
}
}
lean_object* l_Lean_ScopedEnvExtension_addScopedEntry(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_addScopedEntry___rarg), 4, 0);
return x_4;
}
}
lean_object* l_Lean_ScopedEnvExtension_addLocalEntry_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_2(x_3, x_6, x_7);
return x_8;
}
}
}
lean_object* l_Lean_ScopedEnvExtension_addLocalEntry_match__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_addLocalEntry_match__1___rarg), 3, 0);
return x_3;
}
}
lean_object* l_Lean_ScopedEnvExtension_addLocalEntry___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = l_Lean_PersistentEnvExtension_getState___rarg(x_4, x_2);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_5, 0);
lean_dec(x_9);
x_10 = !lean_is_exclusive(x_6);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_6, 0);
lean_dec(x_11);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_ctor_get(x_12, 4);
lean_inc(x_13);
lean_dec(x_12);
x_14 = !lean_is_exclusive(x_7);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_7, 0);
x_16 = lean_apply_2(x_13, x_15, x_3);
lean_ctor_set(x_7, 0, x_16);
x_17 = l_Lean_PersistentEnvExtension_setState___rarg(x_4, x_2, x_5);
lean_dec(x_4);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_7, 0);
x_19 = lean_ctor_get(x_7, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_7);
x_20 = lean_apply_2(x_13, x_18, x_3);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
lean_ctor_set(x_6, 0, x_21);
x_22 = l_Lean_PersistentEnvExtension_setState___rarg(x_4, x_2, x_5);
lean_dec(x_4);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_23 = lean_ctor_get(x_6, 1);
lean_inc(x_23);
lean_dec(x_6);
x_24 = lean_ctor_get(x_1, 0);
lean_inc(x_24);
lean_dec(x_1);
x_25 = lean_ctor_get(x_24, 4);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_ctor_get(x_7, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_7, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_28 = x_7;
} else {
 lean_dec_ref(x_7);
 x_28 = lean_box(0);
}
x_29 = lean_apply_2(x_25, x_26, x_3);
if (lean_is_scalar(x_28)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_28;
}
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_23);
lean_ctor_set(x_5, 0, x_31);
x_32 = l_Lean_PersistentEnvExtension_setState___rarg(x_4, x_2, x_5);
lean_dec(x_4);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_33 = lean_ctor_get(x_5, 1);
x_34 = lean_ctor_get(x_5, 2);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_5);
x_35 = lean_ctor_get(x_6, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_36 = x_6;
} else {
 lean_dec_ref(x_6);
 x_36 = lean_box(0);
}
x_37 = lean_ctor_get(x_1, 0);
lean_inc(x_37);
lean_dec(x_1);
x_38 = lean_ctor_get(x_37, 4);
lean_inc(x_38);
lean_dec(x_37);
x_39 = lean_ctor_get(x_7, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_7, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_41 = x_7;
} else {
 lean_dec_ref(x_7);
 x_41 = lean_box(0);
}
x_42 = lean_apply_2(x_38, x_39, x_3);
if (lean_is_scalar(x_41)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_41;
}
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_40);
if (lean_is_scalar(x_36)) {
 x_44 = lean_alloc_ctor(1, 2, 0);
} else {
 x_44 = x_36;
}
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_35);
x_45 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_33);
lean_ctor_set(x_45, 2, x_34);
x_46 = l_Lean_PersistentEnvExtension_setState___rarg(x_4, x_2, x_45);
lean_dec(x_4);
return x_46;
}
}
}
}
lean_object* l_Lean_ScopedEnvExtension_addLocalEntry(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_addLocalEntry___rarg), 3, 0);
return x_4;
}
}
lean_object* l_Lean_ScopedEnvExtension_add_match__1___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
case 1:
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_2);
x_7 = lean_box(0);
x_8 = lean_apply_1(x_3, x_7);
return x_8;
}
default: 
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_box(0);
x_10 = lean_apply_1(x_4, x_9);
return x_10;
}
}
}
}
lean_object* l_Lean_ScopedEnvExtension_add_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_add_match__1___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_ScopedEnvExtension_add_match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l_Lean_ScopedEnvExtension_add_match__1___rarg(x_5, x_2, x_3, x_4);
return x_6;
}
}
lean_object* l_Lean_ScopedEnvExtension_add___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_ScopedEnvExtension_addEntry___rarg(x_1, x_3, x_2);
return x_4;
}
}
lean_object* l_Lean_ScopedEnvExtension_add___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_ScopedEnvExtension_addLocalEntry___rarg(x_1, x_3, x_2);
return x_4;
}
}
lean_object* l_Lean_ScopedEnvExtension_add___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_ScopedEnvExtension_addScopedEntry___rarg(x_1, x_4, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_ScopedEnvExtension_add___rarg___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_add___rarg___lambda__3), 4, 3);
lean_closure_set(x_6, 0, x_2);
lean_closure_set(x_6, 1, x_4);
lean_closure_set(x_6, 2, x_3);
x_7 = lean_apply_1(x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_ScopedEnvExtension_add___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6) {
_start:
{
switch (x_6) {
case 0:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_add___rarg___lambda__1), 3, 2);
lean_closure_set(x_8, 0, x_4);
lean_closure_set(x_8, 1, x_5);
x_9 = lean_apply_1(x_7, x_8);
return x_9;
}
case 1:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_2);
lean_dec(x_1);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_dec(x_3);
x_11 = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_add___rarg___lambda__2), 3, 2);
lean_closure_set(x_11, 0, x_4);
lean_closure_set(x_11, 1, x_5);
x_12 = lean_apply_1(x_10, x_11);
return x_12;
}
default: 
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
lean_dec(x_2);
x_15 = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_add___rarg___lambda__4), 4, 3);
lean_closure_set(x_15, 0, x_3);
lean_closure_set(x_15, 1, x_4);
lean_closure_set(x_15, 2, x_5);
x_16 = lean_apply_4(x_13, lean_box(0), lean_box(0), x_14, x_15);
return x_16;
}
}
}
}
lean_object* l_Lean_ScopedEnvExtension_add(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_add___rarg___boxed), 6, 0);
return x_5;
}
}
lean_object* l_Lean_ScopedEnvExtension_add___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_6);
lean_dec(x_6);
x_8 = l_Lean_ScopedEnvExtension_add___rarg(x_1, x_2, x_3, x_4, x_5, x_7);
return x_8;
}
}
lean_object* l_Lean_ScopedEnvExtension_getState_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_apply_1(x_3, x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_2(x_2, x_5, x_6);
return x_7;
}
}
}
lean_object* l_Lean_ScopedEnvExtension_getState_match__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_getState_match__1___rarg), 3, 0);
return x_3;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_getState___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.ScopedEnvExtension");
return x_1;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_getState___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.ScopedEnvExtension.getState");
return x_1;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_getState___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_ScopedEnvExtension_getState___rarg___closed__1;
x_2 = l_Lean_ScopedEnvExtension_getState___rarg___closed__2;
x_3 = lean_unsigned_to_nat(155u);
x_4 = lean_unsigned_to_nat(16u);
x_5 = l_Lean_Name_getString_x21___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_ScopedEnvExtension_getState___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_Lean_PersistentEnvExtension_getState___rarg(x_4, x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_ScopedEnvExtension_getState___rarg___closed__3;
x_8 = lean_panic_fn(x_1, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_1);
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
return x_10;
}
}
}
lean_object* l_Lean_ScopedEnvExtension_getState(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_getState___rarg___boxed), 3, 0);
return x_4;
}
}
lean_object* l_Lean_ScopedEnvExtension_getState___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_ScopedEnvExtension_getState___rarg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_ScopedEnvExtension_activateScoped_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_ScopedEnvExtension_activateScoped_match__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_activateScoped_match__1___rarg), 3, 0);
return x_3;
}
}
lean_object* l_Lean_ScopedEnvExtension_activateScoped_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_apply_1(x_3, x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_2(x_2, x_5, x_6);
return x_7;
}
}
}
lean_object* l_Lean_ScopedEnvExtension_activateScoped_match__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_activateScoped_match__2___rarg), 3, 0);
return x_3;
}
}
lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_ScopedEnvExtension_activateScoped___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_10 = lean_name_eq(x_5, x_9);
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
lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_ScopedEnvExtension_activateScoped___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_findAtAux___at_Lean_ScopedEnvExtension_activateScoped___spec__4___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Std_PersistentHashMap_findAux___at_Lean_ScopedEnvExtension_activateScoped___spec__3___rarg(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = 5;
x_6 = l_Std_PersistentHashMap_insertAux___rarg___closed__2;
x_7 = x_2 & x_6;
x_8 = lean_usize_to_nat(x_7);
x_9 = lean_box(2);
x_10 = lean_array_get(x_9, x_4, x_8);
lean_dec(x_8);
lean_dec(x_4);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_name_eq(x_3, x_11);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_12);
x_14 = lean_box(0);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_12);
return x_15;
}
}
case 1:
{
lean_object* x_16; size_t x_17; 
x_16 = lean_ctor_get(x_10, 0);
lean_inc(x_16);
lean_dec(x_10);
x_17 = x_2 >> x_5;
x_1 = x_16;
x_2 = x_17;
goto _start;
}
default: 
{
lean_object* x_19; 
x_19 = lean_box(0);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Std_PersistentHashMap_findAtAux___at_Lean_ScopedEnvExtension_activateScoped___spec__4___rarg(x_20, x_21, lean_box(0), x_22, x_3);
lean_dec(x_21);
lean_dec(x_20);
return x_23;
}
}
}
lean_object* l_Std_PersistentHashMap_findAux___at_Lean_ScopedEnvExtension_activateScoped___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_findAux___at_Lean_ScopedEnvExtension_activateScoped___spec__3___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_ScopedEnvExtension_activateScoped___spec__2___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; size_t x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_Name_hash(x_2);
x_5 = l_Std_PersistentHashMap_findAux___at_Lean_ScopedEnvExtension_activateScoped___spec__3___rarg(x_3, x_4, x_2);
return x_5;
}
}
lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_ScopedEnvExtension_activateScoped___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_PersistentHashMap_find_x3f___at_Lean_ScopedEnvExtension_activateScoped___spec__2___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_Std_AssocList_find_x3f___at_Lean_ScopedEnvExtension_activateScoped___spec__6___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_name_eq(x_4, x_1);
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_9; 
lean_inc(x_5);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_5);
return x_9;
}
}
}
}
lean_object* l_Std_AssocList_find_x3f___at_Lean_ScopedEnvExtension_activateScoped___spec__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_AssocList_find_x3f___at_Lean_ScopedEnvExtension_activateScoped___spec__6___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_ScopedEnvExtension_activateScoped___spec__5___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Name_hash(x_2);
x_6 = lean_usize_modn(x_5, x_4);
lean_dec(x_4);
x_7 = lean_array_uget(x_3, x_6);
x_8 = l_Std_AssocList_find_x3f___at_Lean_ScopedEnvExtension_activateScoped___spec__6___rarg(x_2, x_7);
lean_dec(x_7);
return x_8;
}
}
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_ScopedEnvExtension_activateScoped___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_HashMapImp_find_x3f___at_Lean_ScopedEnvExtension_activateScoped___spec__5___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_Std_AssocList_find_x3f___at_Lean_ScopedEnvExtension_activateScoped___spec__8___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_name_eq(x_4, x_1);
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_9; 
lean_inc(x_5);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_5);
return x_9;
}
}
}
}
lean_object* l_Std_AssocList_find_x3f___at_Lean_ScopedEnvExtension_activateScoped___spec__8(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_AssocList_find_x3f___at_Lean_ScopedEnvExtension_activateScoped___spec__8___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_ScopedEnvExtension_activateScoped___spec__7___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Name_hash(x_2);
x_6 = lean_usize_modn(x_5, x_4);
lean_dec(x_4);
x_7 = lean_array_uget(x_3, x_6);
x_8 = l_Std_AssocList_find_x3f___at_Lean_ScopedEnvExtension_activateScoped___spec__8___rarg(x_2, x_7);
lean_dec(x_7);
return x_8;
}
}
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_ScopedEnvExtension_activateScoped___spec__7(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_HashMapImp_find_x3f___at_Lean_ScopedEnvExtension_activateScoped___spec__7___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_Lean_SMap_find_x3f___at_Lean_ScopedEnvExtension_activateScoped___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l_Std_PersistentHashMap_find_x3f___at_Lean_ScopedEnvExtension_activateScoped___spec__2___rarg(x_5, x_2);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = l_Std_HashMapImp_find_x3f___at_Lean_ScopedEnvExtension_activateScoped___spec__5___rarg(x_4, x_2);
lean_dec(x_4);
return x_7;
}
else
{
uint8_t x_8; 
lean_dec(x_4);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
return x_6;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = l_Std_HashMapImp_find_x3f___at_Lean_ScopedEnvExtension_activateScoped___spec__7___rarg(x_11, x_2);
lean_dec(x_11);
return x_12;
}
}
}
lean_object* l_Lean_SMap_find_x3f___at_Lean_ScopedEnvExtension_activateScoped___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_SMap_find_x3f___at_Lean_ScopedEnvExtension_activateScoped___spec__1___rarg___boxed), 2, 0);
return x_2;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_ScopedEnvExtension_activateScoped___spec__11___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = x_6 < x_5;
if (x_8 == 0)
{
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_uget(x_4, x_6);
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 1);
x_12 = lean_ctor_get(x_7, 0);
lean_dec(x_12);
lean_inc(x_1);
x_13 = l_Std_PersistentArray_forInAux___at_Lean_ScopedEnvExtension_activateScoped___spec__10___rarg(x_1, x_2, x_9, x_11);
lean_dec(x_9);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_3);
lean_dec(x_1);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_7, 1, x_14);
lean_ctor_set(x_7, 0, x_15);
return x_7;
}
else
{
lean_object* x_16; size_t x_17; size_t x_18; 
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec(x_13);
lean_inc(x_3);
lean_ctor_set(x_7, 1, x_16);
lean_ctor_set(x_7, 0, x_3);
x_17 = 1;
x_18 = x_6 + x_17;
x_6 = x_18;
goto _start;
}
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_7, 1);
lean_inc(x_20);
lean_dec(x_7);
lean_inc(x_1);
x_21 = l_Std_PersistentArray_forInAux___at_Lean_ScopedEnvExtension_activateScoped___spec__10___rarg(x_1, x_2, x_9, x_20);
lean_dec(x_9);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_3);
lean_dec(x_1);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_21);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; 
x_25 = lean_ctor_get(x_21, 0);
lean_inc(x_25);
lean_dec(x_21);
lean_inc(x_3);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_3);
lean_ctor_set(x_26, 1, x_25);
x_27 = 1;
x_28 = x_6 + x_27;
x_6 = x_28;
x_7 = x_26;
goto _start;
}
}
}
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_ScopedEnvExtension_activateScoped___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_ScopedEnvExtension_activateScoped___spec__11___rarg___boxed), 7, 0);
return x_4;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_ScopedEnvExtension_activateScoped___spec__12___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = x_5 < x_4;
if (x_7 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_uget(x_3, x_5);
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; 
x_10 = lean_ctor_get(x_6, 1);
x_11 = lean_ctor_get(x_6, 0);
lean_dec(x_11);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_12, 4);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_apply_2(x_13, x_10, x_8);
lean_inc(x_2);
lean_ctor_set(x_6, 1, x_14);
lean_ctor_set(x_6, 0, x_2);
x_15 = 1;
x_16 = x_5 + x_15;
x_5 = x_16;
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; 
x_18 = lean_ctor_get(x_6, 1);
lean_inc(x_18);
lean_dec(x_6);
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 4);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_apply_2(x_20, x_18, x_8);
lean_inc(x_2);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_2);
lean_ctor_set(x_22, 1, x_21);
x_23 = 1;
x_24 = x_5 + x_23;
x_5 = x_24;
x_6 = x_22;
goto _start;
}
}
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_ScopedEnvExtension_activateScoped___spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_ScopedEnvExtension_activateScoped___spec__12___rarg___boxed), 6, 0);
return x_4;
}
}
lean_object* l_Std_PersistentArray_forInAux___at_Lean_ScopedEnvExtension_activateScoped___spec__10___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
lean_object* l_Std_PersistentArray_forInAux___at_Lean_ScopedEnvExtension_activateScoped___spec__10___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
x_8 = lean_array_get_size(x_5);
x_9 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_10 = 0;
x_11 = l_Array_forInUnsafe_loop___at_Lean_ScopedEnvExtension_activateScoped___spec__11___rarg(x_1, x_2, x_6, x_5, x_9, x_10, x_7);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
else
{
lean_object* x_15; 
lean_dec(x_11);
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec(x_12);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; lean_object* x_23; 
x_16 = lean_ctor_get(x_3, 0);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_4);
x_19 = lean_array_get_size(x_16);
x_20 = lean_usize_of_nat(x_19);
lean_dec(x_19);
x_21 = 0;
x_22 = l_Array_forInUnsafe_loop___at_Lean_ScopedEnvExtension_activateScoped___spec__12___rarg(x_1, x_17, x_16, x_20, x_21, x_18);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
else
{
lean_object* x_26; 
lean_dec(x_22);
x_26 = lean_ctor_get(x_23, 0);
lean_inc(x_26);
lean_dec(x_23);
return x_26;
}
}
}
}
lean_object* l_Std_PersistentArray_forInAux___at_Lean_ScopedEnvExtension_activateScoped___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Std_PersistentArray_forInAux___at_Lean_ScopedEnvExtension_activateScoped___spec__10___rarg___boxed), 4, 0);
return x_4;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_ScopedEnvExtension_activateScoped___spec__13___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = x_5 < x_4;
if (x_7 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_uget(x_3, x_5);
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; 
x_10 = lean_ctor_get(x_6, 1);
x_11 = lean_ctor_get(x_6, 0);
lean_dec(x_11);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_12, 4);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_apply_2(x_13, x_10, x_8);
lean_inc(x_2);
lean_ctor_set(x_6, 1, x_14);
lean_ctor_set(x_6, 0, x_2);
x_15 = 1;
x_16 = x_5 + x_15;
x_5 = x_16;
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; 
x_18 = lean_ctor_get(x_6, 1);
lean_inc(x_18);
lean_dec(x_6);
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 4);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_apply_2(x_20, x_18, x_8);
lean_inc(x_2);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_2);
lean_ctor_set(x_22, 1, x_21);
x_23 = 1;
x_24 = x_5 + x_23;
x_5 = x_24;
x_6 = x_22;
goto _start;
}
}
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_ScopedEnvExtension_activateScoped___spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_ScopedEnvExtension_activateScoped___spec__13___rarg___boxed), 6, 0);
return x_4;
}
}
lean_object* l_Std_PersistentArray_forIn___at_Lean_ScopedEnvExtension_activateScoped___spec__9___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_inc(x_1);
x_5 = l_Std_PersistentArray_forInAux___at_Lean_ScopedEnvExtension_activateScoped___spec__10___rarg(x_1, x_3, x_4, x_3);
lean_dec(x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_2, 1);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
x_11 = lean_array_get_size(x_8);
x_12 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_13 = 0;
x_14 = l_Array_forInUnsafe_loop___at_Lean_ScopedEnvExtension_activateScoped___spec__13___rarg(x_1, x_9, x_8, x_12, x_13, x_10);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
return x_16;
}
else
{
lean_object* x_17; 
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
return x_17;
}
}
}
}
lean_object* l_Std_PersistentArray_forIn___at_Lean_ScopedEnvExtension_activateScoped___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Std_PersistentArray_forIn___at_Lean_ScopedEnvExtension_activateScoped___spec__9___rarg___boxed), 3, 0);
return x_4;
}
}
lean_object* l_Lean_ScopedEnvExtension_activateScoped___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = l_Lean_PersistentEnvExtension_getState___rarg(x_4, x_2);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_5, 1);
x_10 = lean_ctor_get(x_5, 2);
x_11 = lean_ctor_get(x_5, 0);
lean_dec(x_11);
x_12 = !lean_is_exclusive(x_6);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_6, 1);
x_14 = lean_ctor_get(x_6, 0);
lean_dec(x_14);
x_15 = !lean_is_exclusive(x_7);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_7, 0);
x_17 = lean_ctor_get(x_7, 1);
x_18 = l_Lean_NameSet_contains(x_17, x_3);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_box(0);
lean_inc(x_3);
x_20 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_17, x_3, x_19);
lean_inc(x_9);
x_21 = l_Lean_SMap_find_x3f___at_Lean_ScopedEnvExtension_activateScoped___spec__1___rarg(x_9, x_3);
lean_dec(x_3);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
lean_dec(x_1);
lean_ctor_set(x_7, 1, x_20);
x_22 = l_Lean_PersistentEnvExtension_setState___rarg(x_4, x_2, x_5);
lean_dec(x_4);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Std_PersistentArray_forIn___at_Lean_ScopedEnvExtension_activateScoped___spec__9___rarg(x_1, x_23, x_16);
lean_dec(x_23);
lean_ctor_set(x_7, 1, x_20);
lean_ctor_set(x_7, 0, x_24);
x_25 = l_Lean_PersistentEnvExtension_setState___rarg(x_4, x_2, x_5);
lean_dec(x_4);
return x_25;
}
}
else
{
lean_free_object(x_7);
lean_dec(x_17);
lean_dec(x_16);
lean_free_object(x_6);
lean_dec(x_13);
lean_free_object(x_5);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_2;
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_7, 0);
x_27 = lean_ctor_get(x_7, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_7);
x_28 = l_Lean_NameSet_contains(x_27, x_3);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_box(0);
lean_inc(x_3);
x_30 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_27, x_3, x_29);
lean_inc(x_9);
x_31 = l_Lean_SMap_find_x3f___at_Lean_ScopedEnvExtension_activateScoped___spec__1___rarg(x_9, x_3);
lean_dec(x_3);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_1);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_26);
lean_ctor_set(x_32, 1, x_30);
lean_ctor_set(x_6, 0, x_32);
x_33 = l_Lean_PersistentEnvExtension_setState___rarg(x_4, x_2, x_5);
lean_dec(x_4);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_31, 0);
lean_inc(x_34);
lean_dec(x_31);
x_35 = l_Std_PersistentArray_forIn___at_Lean_ScopedEnvExtension_activateScoped___spec__9___rarg(x_1, x_34, x_26);
lean_dec(x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_30);
lean_ctor_set(x_6, 0, x_36);
x_37 = l_Lean_PersistentEnvExtension_setState___rarg(x_4, x_2, x_5);
lean_dec(x_4);
return x_37;
}
}
else
{
lean_dec(x_27);
lean_dec(x_26);
lean_free_object(x_6);
lean_dec(x_13);
lean_free_object(x_5);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_2;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_38 = lean_ctor_get(x_6, 1);
lean_inc(x_38);
lean_dec(x_6);
x_39 = lean_ctor_get(x_7, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_7, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_41 = x_7;
} else {
 lean_dec_ref(x_7);
 x_41 = lean_box(0);
}
x_42 = l_Lean_NameSet_contains(x_40, x_3);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_box(0);
lean_inc(x_3);
x_44 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_40, x_3, x_43);
lean_inc(x_9);
x_45 = l_Lean_SMap_find_x3f___at_Lean_ScopedEnvExtension_activateScoped___spec__1___rarg(x_9, x_3);
lean_dec(x_3);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_1);
if (lean_is_scalar(x_41)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_41;
}
lean_ctor_set(x_46, 0, x_39);
lean_ctor_set(x_46, 1, x_44);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_38);
lean_ctor_set(x_5, 0, x_47);
x_48 = l_Lean_PersistentEnvExtension_setState___rarg(x_4, x_2, x_5);
lean_dec(x_4);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_49 = lean_ctor_get(x_45, 0);
lean_inc(x_49);
lean_dec(x_45);
x_50 = l_Std_PersistentArray_forIn___at_Lean_ScopedEnvExtension_activateScoped___spec__9___rarg(x_1, x_49, x_39);
lean_dec(x_49);
if (lean_is_scalar(x_41)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_41;
}
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_44);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_38);
lean_ctor_set(x_5, 0, x_52);
x_53 = l_Lean_PersistentEnvExtension_setState___rarg(x_4, x_2, x_5);
lean_dec(x_4);
return x_53;
}
}
else
{
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_free_object(x_5);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_2;
}
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_54 = lean_ctor_get(x_5, 1);
x_55 = lean_ctor_get(x_5, 2);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_5);
x_56 = lean_ctor_get(x_6, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_57 = x_6;
} else {
 lean_dec_ref(x_6);
 x_57 = lean_box(0);
}
x_58 = lean_ctor_get(x_7, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_7, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_60 = x_7;
} else {
 lean_dec_ref(x_7);
 x_60 = lean_box(0);
}
x_61 = l_Lean_NameSet_contains(x_59, x_3);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_box(0);
lean_inc(x_3);
x_63 = l_Std_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_59, x_3, x_62);
lean_inc(x_54);
x_64 = l_Lean_SMap_find_x3f___at_Lean_ScopedEnvExtension_activateScoped___spec__1___rarg(x_54, x_3);
lean_dec(x_3);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_1);
if (lean_is_scalar(x_60)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_60;
}
lean_ctor_set(x_65, 0, x_58);
lean_ctor_set(x_65, 1, x_63);
if (lean_is_scalar(x_57)) {
 x_66 = lean_alloc_ctor(1, 2, 0);
} else {
 x_66 = x_57;
}
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_56);
x_67 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_54);
lean_ctor_set(x_67, 2, x_55);
x_68 = l_Lean_PersistentEnvExtension_setState___rarg(x_4, x_2, x_67);
lean_dec(x_4);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_69 = lean_ctor_get(x_64, 0);
lean_inc(x_69);
lean_dec(x_64);
x_70 = l_Std_PersistentArray_forIn___at_Lean_ScopedEnvExtension_activateScoped___spec__9___rarg(x_1, x_69, x_58);
lean_dec(x_69);
if (lean_is_scalar(x_60)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_60;
}
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_63);
if (lean_is_scalar(x_57)) {
 x_72 = lean_alloc_ctor(1, 2, 0);
} else {
 x_72 = x_57;
}
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_56);
x_73 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_54);
lean_ctor_set(x_73, 2, x_55);
x_74 = l_Lean_PersistentEnvExtension_setState___rarg(x_4, x_2, x_73);
lean_dec(x_4);
return x_74;
}
}
else
{
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_2;
}
}
}
}
}
lean_object* l_Lean_ScopedEnvExtension_activateScoped(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_activateScoped___rarg), 3, 0);
return x_4;
}
}
lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_ScopedEnvExtension_activateScoped___spec__4___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_PersistentHashMap_findAtAux___at_Lean_ScopedEnvExtension_activateScoped___spec__4___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Std_PersistentHashMap_findAux___at_Lean_ScopedEnvExtension_activateScoped___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Std_PersistentHashMap_findAux___at_Lean_ScopedEnvExtension_activateScoped___spec__3___rarg(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_ScopedEnvExtension_activateScoped___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_PersistentHashMap_find_x3f___at_Lean_ScopedEnvExtension_activateScoped___spec__2___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Std_AssocList_find_x3f___at_Lean_ScopedEnvExtension_activateScoped___spec__6___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_AssocList_find_x3f___at_Lean_ScopedEnvExtension_activateScoped___spec__6___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_ScopedEnvExtension_activateScoped___spec__5___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_HashMapImp_find_x3f___at_Lean_ScopedEnvExtension_activateScoped___spec__5___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Std_AssocList_find_x3f___at_Lean_ScopedEnvExtension_activateScoped___spec__8___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_AssocList_find_x3f___at_Lean_ScopedEnvExtension_activateScoped___spec__8___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_ScopedEnvExtension_activateScoped___spec__7___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_HashMapImp_find_x3f___at_Lean_ScopedEnvExtension_activateScoped___spec__7___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_SMap_find_x3f___at_Lean_ScopedEnvExtension_activateScoped___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_SMap_find_x3f___at_Lean_ScopedEnvExtension_activateScoped___spec__1___rarg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_ScopedEnvExtension_activateScoped___spec__11___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l_Array_forInUnsafe_loop___at_Lean_ScopedEnvExtension_activateScoped___spec__11___rarg(x_1, x_2, x_3, x_4, x_8, x_9, x_7);
lean_dec(x_4);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_ScopedEnvExtension_activateScoped___spec__12___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_forInUnsafe_loop___at_Lean_ScopedEnvExtension_activateScoped___spec__12___rarg(x_1, x_2, x_3, x_7, x_8, x_6);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Std_PersistentArray_forInAux___at_Lean_ScopedEnvExtension_activateScoped___spec__10___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_PersistentArray_forInAux___at_Lean_ScopedEnvExtension_activateScoped___spec__10___rarg___lambda__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Std_PersistentArray_forInAux___at_Lean_ScopedEnvExtension_activateScoped___spec__10___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_PersistentArray_forInAux___at_Lean_ScopedEnvExtension_activateScoped___spec__10___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_ScopedEnvExtension_activateScoped___spec__13___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_forInUnsafe_loop___at_Lean_ScopedEnvExtension_activateScoped___spec__13___rarg(x_1, x_2, x_3, x_7, x_8, x_6);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Std_PersistentArray_forIn___at_Lean_ScopedEnvExtension_activateScoped___spec__9___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_PersistentArray_forIn___at_Lean_ScopedEnvExtension_activateScoped___spec__9___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_pushScope_match__1___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_pushScope_match__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_pushScope_match__1___rarg), 1, 0);
return x_3;
}
}
lean_object* l_Lean_pushScope_match__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_pushScope_match__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_pushScope___spec__1___rarg___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_pushScope___spec__1___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l_Array_forInUnsafe_loop___at_Lean_pushScope___spec__1___rarg___lambda__1___closed__1;
x_6 = lean_apply_2(x_4, lean_box(0), x_5);
return x_6;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_pushScope___spec__1___rarg___lambda__2(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_apply_2(x_10, lean_box(0), x_8);
return x_11;
}
else
{
lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_7, 0);
lean_inc(x_12);
lean_dec(x_7);
x_13 = 1;
x_14 = x_2 + x_13;
x_15 = l_Array_forInUnsafe_loop___at_Lean_pushScope___spec__1___rarg(x_1, x_3, x_4, x_5, x_6, x_14, x_12);
return x_15;
}
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_pushScope___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = x_6 < x_5;
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_apply_2(x_10, lean_box(0), x_7);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_7);
x_12 = lean_array_uget(x_4, x_6);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_14);
x_15 = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_pushScope___rarg___boxed), 2, 1);
lean_closure_set(x_15, 0, x_12);
x_16 = lean_apply_1(x_14, x_15);
lean_inc(x_1);
x_17 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_pushScope___spec__1___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_17, 0, x_1);
lean_inc(x_3);
x_18 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_16, x_17);
x_19 = lean_box_usize(x_6);
x_20 = lean_box_usize(x_5);
x_21 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_pushScope___spec__1___rarg___lambda__2___boxed), 7, 6);
lean_closure_set(x_21, 0, x_1);
lean_closure_set(x_21, 1, x_19);
lean_closure_set(x_21, 2, x_2);
lean_closure_set(x_21, 3, x_3);
lean_closure_set(x_21, 4, x_4);
lean_closure_set(x_21, 5, x_20);
x_22 = lean_apply_4(x_13, lean_box(0), lean_box(0), x_18, x_21);
return x_22;
}
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_pushScope___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_pushScope___spec__1___rarg___boxed), 7, 0);
return x_2;
}
}
lean_object* l_Lean_pushScope___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = lean_apply_2(x_4, lean_box(0), x_5);
return x_6;
}
}
lean_object* l_Lean_pushScope___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_array_get_size(x_4);
x_6 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_7 = 0;
x_8 = lean_box(0);
lean_inc(x_3);
lean_inc(x_1);
x_9 = l_Array_forInUnsafe_loop___at_Lean_pushScope___spec__1___rarg(x_1, x_2, x_3, x_4, x_6, x_7, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_pushScope___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_10, 0, x_1);
x_11 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_9, x_10);
return x_11;
}
}
static lean_object* _init_l_Lean_pushScope___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_scopedEnvExtensionsRef;
x_2 = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, lean_box(0));
lean_closure_set(x_2, 2, x_1);
return x_2;
}
}
lean_object* l_Lean_pushScope___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = l_Lean_pushScope___rarg___closed__1;
x_6 = lean_apply_2(x_3, lean_box(0), x_5);
lean_inc(x_4);
x_7 = lean_alloc_closure((void*)(l_Lean_pushScope___rarg___lambda__2), 4, 3);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_2);
lean_closure_set(x_7, 2, x_4);
x_8 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_6, x_7);
return x_8;
}
}
lean_object* l_Lean_pushScope(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_pushScope___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_pushScope___spec__1___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Array_forInUnsafe_loop___at_Lean_pushScope___spec__1___rarg___lambda__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_pushScope___spec__1___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l_Array_forInUnsafe_loop___at_Lean_pushScope___spec__1___rarg___lambda__2(x_1, x_8, x_3, x_4, x_5, x_9, x_7);
return x_10;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_pushScope___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l_Array_forInUnsafe_loop___at_Lean_pushScope___spec__1___rarg(x_1, x_2, x_3, x_4, x_8, x_9, x_7);
return x_10;
}
}
lean_object* l_Lean_pushScope___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_pushScope___rarg___lambda__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_popScope_match__1___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_popScope_match__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_popScope_match__1___rarg), 1, 0);
return x_3;
}
}
lean_object* l_Lean_popScope_match__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_popScope_match__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_popScope___spec__1___rarg___lambda__1(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_apply_2(x_10, lean_box(0), x_8);
return x_11;
}
else
{
lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_7, 0);
lean_inc(x_12);
lean_dec(x_7);
x_13 = 1;
x_14 = x_2 + x_13;
x_15 = l_Array_forInUnsafe_loop___at_Lean_popScope___spec__1___rarg(x_1, x_3, x_4, x_5, x_6, x_14, x_12);
return x_15;
}
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_popScope___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = x_6 < x_5;
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_apply_2(x_10, lean_box(0), x_7);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_7);
x_12 = lean_array_uget(x_4, x_6);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_14);
x_15 = lean_alloc_closure((void*)(l_Lean_ScopedEnvExtension_popScope___rarg___boxed), 2, 1);
lean_closure_set(x_15, 0, x_12);
x_16 = lean_apply_1(x_14, x_15);
lean_inc(x_1);
x_17 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_pushScope___spec__1___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_17, 0, x_1);
lean_inc(x_3);
x_18 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_16, x_17);
x_19 = lean_box_usize(x_6);
x_20 = lean_box_usize(x_5);
x_21 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_popScope___spec__1___rarg___lambda__1___boxed), 7, 6);
lean_closure_set(x_21, 0, x_1);
lean_closure_set(x_21, 1, x_19);
lean_closure_set(x_21, 2, x_2);
lean_closure_set(x_21, 3, x_3);
lean_closure_set(x_21, 4, x_4);
lean_closure_set(x_21, 5, x_20);
x_22 = lean_apply_4(x_13, lean_box(0), lean_box(0), x_18, x_21);
return x_22;
}
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_popScope___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_popScope___spec__1___rarg___boxed), 7, 0);
return x_2;
}
}
lean_object* l_Lean_popScope___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_array_get_size(x_4);
x_6 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_7 = 0;
x_8 = lean_box(0);
lean_inc(x_3);
lean_inc(x_1);
x_9 = l_Array_forInUnsafe_loop___at_Lean_popScope___spec__1___rarg(x_1, x_2, x_3, x_4, x_6, x_7, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_pushScope___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_10, 0, x_1);
x_11 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_9, x_10);
return x_11;
}
}
lean_object* l_Lean_popScope___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = l_Lean_pushScope___rarg___closed__1;
x_6 = lean_apply_2(x_3, lean_box(0), x_5);
lean_inc(x_4);
x_7 = lean_alloc_closure((void*)(l_Lean_popScope___rarg___lambda__1), 4, 3);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_2);
lean_closure_set(x_7, 2, x_4);
x_8 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_6, x_7);
return x_8;
}
}
lean_object* l_Lean_popScope(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_popScope___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_popScope___spec__1___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l_Array_forInUnsafe_loop___at_Lean_popScope___spec__1___rarg___lambda__1(x_1, x_8, x_3, x_4, x_5, x_9, x_7);
return x_10;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_popScope___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l_Array_forInUnsafe_loop___at_Lean_popScope___spec__1___rarg(x_1, x_2, x_3, x_4, x_8, x_9, x_7);
return x_10;
}
}
lean_object* l_Lean_activateScoped_match__1___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_activateScoped_match__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_activateScoped_match__1___rarg), 1, 0);
return x_3;
}
}
lean_object* l_Lean_activateScoped_match__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_activateScoped_match__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_activateScoped___spec__1___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_ScopedEnvExtension_activateScoped___rarg(x_1, x_3, x_2);
return x_4;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_activateScoped___spec__1___rarg___lambda__2(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, size_t x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_apply_2(x_11, lean_box(0), x_9);
return x_12;
}
else
{
lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_8, 0);
lean_inc(x_13);
lean_dec(x_8);
x_14 = 1;
x_15 = x_2 + x_14;
x_16 = l_Array_forInUnsafe_loop___at_Lean_activateScoped___spec__1___rarg(x_1, x_3, x_4, x_5, x_6, x_7, x_15, x_13);
return x_16;
}
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_activateScoped___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = x_7 < x_6;
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_apply_2(x_11, lean_box(0), x_8);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_8);
x_13 = lean_array_uget(x_5, x_7);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
lean_inc(x_3);
x_16 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_activateScoped___spec__1___rarg___lambda__1), 3, 2);
lean_closure_set(x_16, 0, x_13);
lean_closure_set(x_16, 1, x_3);
x_17 = lean_apply_1(x_15, x_16);
lean_inc(x_1);
x_18 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_pushScope___spec__1___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_18, 0, x_1);
lean_inc(x_4);
x_19 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_17, x_18);
x_20 = lean_box_usize(x_7);
x_21 = lean_box_usize(x_6);
x_22 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_activateScoped___spec__1___rarg___lambda__2___boxed), 8, 7);
lean_closure_set(x_22, 0, x_1);
lean_closure_set(x_22, 1, x_20);
lean_closure_set(x_22, 2, x_2);
lean_closure_set(x_22, 3, x_3);
lean_closure_set(x_22, 4, x_4);
lean_closure_set(x_22, 5, x_5);
lean_closure_set(x_22, 6, x_21);
x_23 = lean_apply_4(x_14, lean_box(0), lean_box(0), x_19, x_22);
return x_23;
}
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_activateScoped___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_forInUnsafe_loop___at_Lean_activateScoped___spec__1___rarg___boxed), 8, 0);
return x_2;
}
}
lean_object* l_Lean_activateScoped___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_array_get_size(x_5);
x_7 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_8 = 0;
x_9 = lean_box(0);
lean_inc(x_4);
lean_inc(x_1);
x_10 = l_Array_forInUnsafe_loop___at_Lean_activateScoped___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_7, x_8, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_pushScope___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_11, 0, x_1);
x_12 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_10, x_11);
return x_12;
}
}
lean_object* l_Lean_activateScoped___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = l_Lean_pushScope___rarg___closed__1;
x_7 = lean_apply_2(x_3, lean_box(0), x_6);
lean_inc(x_5);
x_8 = lean_alloc_closure((void*)(l_Lean_activateScoped___rarg___lambda__1), 5, 4);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_2);
lean_closure_set(x_8, 2, x_4);
lean_closure_set(x_8, 3, x_5);
x_9 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_7, x_8);
return x_9;
}
}
lean_object* l_Lean_activateScoped(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_activateScoped___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_activateScoped___spec__1___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_10 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_11 = l_Array_forInUnsafe_loop___at_Lean_activateScoped___spec__1___rarg___lambda__2(x_1, x_9, x_3, x_4, x_5, x_6, x_10, x_8);
return x_11;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_activateScoped___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_11 = l_Array_forInUnsafe_loop___at_Lean_activateScoped___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_9, x_10, x_8);
return x_11;
}
}
lean_object* l_Lean_registerSimpleScopedEnvExtension___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_registerSimpleScopedEnvExtension___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_registerSimpleScopedEnvExtension___rarg___lambda__1___boxed), 4, 0);
return x_1;
}
}
lean_object* l_Lean_registerSimpleScopedEnvExtension___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_alloc_closure((void*)(l_EStateM_pure___rarg), 2, 1);
lean_closure_set(x_6, 0, x_5);
x_7 = l_Lean_registerSimpleScopedEnvExtension___rarg___closed__1;
x_8 = l_Applicative_seqRight___default___rarg___closed__1;
x_9 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_6);
lean_ctor_set(x_9, 2, x_7);
lean_ctor_set(x_9, 3, x_8);
lean_ctor_set(x_9, 4, x_4);
x_10 = l_Lean_registerScopedEnvExtensionUnsafe___rarg(x_9, x_2);
return x_10;
}
}
lean_object* l_Lean_registerSimpleScopedEnvExtension(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_registerSimpleScopedEnvExtension___rarg), 2, 0);
return x_3;
}
}
lean_object* l_Lean_registerSimpleScopedEnvExtension___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_registerSimpleScopedEnvExtension___rarg___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Environment(lean_object*);
lean_object* initialize_Lean_Data_NameTrie(lean_object*);
lean_object* initialize_Lean_Attributes(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_ScopedEnvExtension(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Environment(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_NameTrie(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Attributes(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_ScopedEnvExtension_State_activeScopes___default = _init_l_Lean_ScopedEnvExtension_State_activeScopes___default();
lean_mark_persistent(l_Lean_ScopedEnvExtension_State_activeScopes___default);
l_Lean_ScopedEnvExtension_ScopedEntries_map___default___closed__1 = _init_l_Lean_ScopedEnvExtension_ScopedEntries_map___default___closed__1();
lean_mark_persistent(l_Lean_ScopedEnvExtension_ScopedEntries_map___default___closed__1);
l_Lean_ScopedEnvExtension_ScopedEntries_map___default___closed__2 = _init_l_Lean_ScopedEnvExtension_ScopedEntries_map___default___closed__2();
lean_mark_persistent(l_Lean_ScopedEnvExtension_ScopedEntries_map___default___closed__2);
l_Lean_ScopedEnvExtension_instInhabitedScopedEntries___closed__1 = _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries___closed__1();
lean_mark_persistent(l_Lean_ScopedEnvExtension_instInhabitedScopedEntries___closed__1);
l_Lean_ScopedEnvExtension_instInhabitedScopedEntries___closed__2 = _init_l_Lean_ScopedEnvExtension_instInhabitedScopedEntries___closed__2();
lean_mark_persistent(l_Lean_ScopedEnvExtension_instInhabitedScopedEntries___closed__2);
l_Lean_ScopedEnvExtension_StateStack_scopedEntries___default___closed__1 = _init_l_Lean_ScopedEnvExtension_StateStack_scopedEntries___default___closed__1();
lean_mark_persistent(l_Lean_ScopedEnvExtension_StateStack_scopedEntries___default___closed__1);
l_Lean_ScopedEnvExtension_StateStack_scopedEntries___default___closed__2 = _init_l_Lean_ScopedEnvExtension_StateStack_scopedEntries___default___closed__2();
lean_mark_persistent(l_Lean_ScopedEnvExtension_StateStack_scopedEntries___default___closed__2);
l_Lean_ScopedEnvExtension_instInhabitedStateStack___closed__1 = _init_l_Lean_ScopedEnvExtension_instInhabitedStateStack___closed__1();
lean_mark_persistent(l_Lean_ScopedEnvExtension_instInhabitedStateStack___closed__1);
l_Lean_ScopedEnvExtension_instInhabitedStateStack___closed__2 = _init_l_Lean_ScopedEnvExtension_instInhabitedStateStack___closed__2();
lean_mark_persistent(l_Lean_ScopedEnvExtension_instInhabitedStateStack___closed__2);
l_Lean_ScopedEnvExtension_instInhabitedStateStack___closed__3 = _init_l_Lean_ScopedEnvExtension_instInhabitedStateStack___closed__3();
lean_mark_persistent(l_Lean_ScopedEnvExtension_instInhabitedStateStack___closed__3);
l_Lean_ScopedEnvExtension_instInhabitedDescr___rarg___closed__1 = _init_l_Lean_ScopedEnvExtension_instInhabitedDescr___rarg___closed__1();
lean_mark_persistent(l_Lean_ScopedEnvExtension_instInhabitedDescr___rarg___closed__1);
l_Lean_ScopedEnvExtension_mkInitial___rarg___closed__1 = _init_l_Lean_ScopedEnvExtension_mkInitial___rarg___closed__1();
lean_mark_persistent(l_Lean_ScopedEnvExtension_mkInitial___rarg___closed__1);
l_Lean_ScopedEnvExtension_mkInitial___rarg___closed__2 = _init_l_Lean_ScopedEnvExtension_mkInitial___rarg___closed__2();
lean_mark_persistent(l_Lean_ScopedEnvExtension_mkInitial___rarg___closed__2);
l_Lean_ScopedEnvExtension_addImportedFn___rarg___closed__1 = _init_l_Lean_ScopedEnvExtension_addImportedFn___rarg___closed__1();
lean_mark_persistent(l_Lean_ScopedEnvExtension_addImportedFn___rarg___closed__1);
l_Lean_ScopedEnvExtension_addImportedFn___rarg___closed__2 = _init_l_Lean_ScopedEnvExtension_addImportedFn___rarg___closed__2();
lean_mark_persistent(l_Lean_ScopedEnvExtension_addImportedFn___rarg___closed__2);
res = l_Lean_initFn____x40_Lean_ScopedEnvExtension___hyg_657_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_scopedEnvExtensionsRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_scopedEnvExtensionsRef);
lean_dec_ref(res);
l_Lean_registerScopedEnvExtensionUnsafe___rarg___closed__1 = _init_l_Lean_registerScopedEnvExtensionUnsafe___rarg___closed__1();
lean_mark_persistent(l_Lean_registerScopedEnvExtensionUnsafe___rarg___closed__1);
l_Lean_registerScopedEnvExtensionUnsafe___rarg___closed__2 = _init_l_Lean_registerScopedEnvExtensionUnsafe___rarg___closed__2();
lean_mark_persistent(l_Lean_registerScopedEnvExtensionUnsafe___rarg___closed__2);
l_Lean_ScopedEnvExtension_getState___rarg___closed__1 = _init_l_Lean_ScopedEnvExtension_getState___rarg___closed__1();
lean_mark_persistent(l_Lean_ScopedEnvExtension_getState___rarg___closed__1);
l_Lean_ScopedEnvExtension_getState___rarg___closed__2 = _init_l_Lean_ScopedEnvExtension_getState___rarg___closed__2();
lean_mark_persistent(l_Lean_ScopedEnvExtension_getState___rarg___closed__2);
l_Lean_ScopedEnvExtension_getState___rarg___closed__3 = _init_l_Lean_ScopedEnvExtension_getState___rarg___closed__3();
lean_mark_persistent(l_Lean_ScopedEnvExtension_getState___rarg___closed__3);
l_Array_forInUnsafe_loop___at_Lean_pushScope___spec__1___rarg___lambda__1___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_pushScope___spec__1___rarg___lambda__1___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_pushScope___spec__1___rarg___lambda__1___closed__1);
l_Lean_pushScope___rarg___closed__1 = _init_l_Lean_pushScope___rarg___closed__1();
lean_mark_persistent(l_Lean_pushScope___rarg___closed__1);
l_Lean_registerSimpleScopedEnvExtension___rarg___closed__1 = _init_l_Lean_registerSimpleScopedEnvExtension___rarg___closed__1();
lean_mark_persistent(l_Lean_registerSimpleScopedEnvExtension___rarg___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
