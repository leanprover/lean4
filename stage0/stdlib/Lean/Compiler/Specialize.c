// Lean compiler output
// Module: Lean.Compiler.Specialize
// Imports: Init Lean.Attributes Lean.Compiler.Util
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
lean_object* l_Lean_EnumAttributes_getValue___at___private_Lean_Compiler_Specialize_0__Lean_Compiler_hasSpecializeAttrAux___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__12;
lean_object* lean_get_specialization_info(lean_object*, lean_object*);
size_t l_USize_add(size_t, size_t);
lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_hasSpecializeAttrAux___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_hasNospecializeAttribute___boxed(lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___at___private_Lean_Compiler_Specialize_0__Lean_Compiler_hasSpecializeAttrAux___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerEnumAttributes___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerEnumAttributes___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__1___lambda__2___boxed(lean_object*);
lean_object* l_Lean_Compiler_instBEqSpecializeAttributeKind;
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_specExtension___elambda__4(lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
uint8_t l_USize_decEq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Compiler_getCachedSpecialization___spec__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_beqSpecializeAttributeKind____x40_Lean_Compiler_Specialize___hyg_11__match__1___rarg(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_insert___at_Lean_Compiler_SpecState_addEntry___spec__6(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_SpecState_cache___default___closed__3;
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
extern lean_object* l_Lean_LocalContext_fvarIdToDecl___default___closed__1;
lean_object* l_Lean_Compiler_SpecState_switch_match__1(lean_object*);
lean_object* l_List_forM___at_Lean_registerEnumAttributes___spec__10(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Compiler_getSpecializationInfo___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_SpecState_specInfo___default;
extern lean_object* l_Lean_registerInternalExceptionId___closed__2;
lean_object* l_Std_AssocList_find_x3f___at_Lean_Compiler_getSpecializationInfo___spec__6___boxed(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Compiler_getSpecializationInfo___spec__2(lean_object*, lean_object*);
size_t l_USize_sub(size_t, size_t);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_SpecState_addEntry___spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Compiler_SpecState_addEntry___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_moveEntries___at_Lean_Compiler_SpecState_addEntry___spec__9(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_registerEnumAttributes___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__1___lambda__2(lean_object*);
uint8_t l___private_Lean_Compiler_Specialize_0__Lean_Compiler_hasSpecializeAttrAux(lean_object*, uint8_t, lean_object*);
lean_object* l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Compiler_SpecState_addEntry___spec__4(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_PersistentHashMap_root___default___closed__2;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_SMap_find_x3f___at_Lean_Compiler_getSpecializationInfo___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_specializeAttrs;
lean_object* l_Lean_EnumAttributes_getValue___at___private_Lean_Compiler_Specialize_0__Lean_Compiler_hasSpecializeAttrAux___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__5(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Std_AssocList_contains___at_Lean_Compiler_SpecState_addEntry___spec__7___boxed(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Std_PersistentHashMap_getCollisionNodeSize___rarg(lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_323____spec__3(lean_object*, size_t, size_t, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Std_AssocList_foldlM___at_Lean_Compiler_SpecState_addEntry___spec__10(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__1;
lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_beqSpecializeAttributeKind____x40_Lean_Compiler_Specialize___hyg_11__match__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_registerTagAttribute___spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_specExtension___closed__1;
lean_object* l_Std_AssocList_replace___at_Lean_Compiler_SpecState_addEntry___spec__11(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_find_x3f___at_Lean_Compiler_getCachedSpecialization___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_323____spec__5(lean_object*, lean_object*);
lean_object* l_Lean_setEnv___at_Lean_registerTagAttribute___spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_shiftRight(size_t, size_t);
lean_object* l_Lean_SMap_switch___at_Lean_Compiler_SpecState_switch___spec__1(lean_object*);
lean_object* l_Std_HashMapImp_expand___at_Lean_Compiler_SpecState_addEntry___spec__8(lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_323____spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_insert___at_Lean_Compiler_SpecState_addEntry___spec__13(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__2;
lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_specExtension___closed__4;
lean_object* l_Lean_SMap_switch___at_Lean_Compiler_SpecState_switch___spec__2(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_specExtension___elambda__3___boxed(lean_object*, lean_object*);
lean_object* l_Lean_SMap_find_x3f___at_Lean_Compiler_getCachedSpecialization___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__4;
lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_beqSpecializeAttributeKind____x40_Lean_Compiler_Specialize___hyg_11____boxed(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_specExtension___elambda__2___boxed(lean_object*);
lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__9;
lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__8;
size_t l_UInt64_toUSize(uint64_t);
lean_object* l_Std_AssocList_find_x3f___at_Lean_Compiler_getCachedSpecialization___spec__6(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_SpecState_switch_match__1___rarg(lean_object*, lean_object*);
extern lean_object* l_Lean_registerTagAttribute___closed__5;
lean_object* l_Lean_Compiler_specExtension___closed__2;
lean_object* l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_insert___at_Lean_Compiler_SpecState_addEntry___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Std_HashMapImp_moveEntries___at_Lean_Compiler_SpecState_addEntry___spec__20(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_specExtension;
lean_object* l_Std_HashMapImp_expand___at_Lean_Compiler_SpecState_addEntry___spec__19(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l___private_Lean_Attributes_0__Lean_beqAttributeKind____x40_Lean_Attributes___hyg_139_(uint8_t, uint8_t);
lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Compiler_getCachedSpecialization___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_323____closed__3;
lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_hasSpecializeAttrAux_match__1___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_PersistentHashMap_insertAux___rarg___closed__3;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_323____spec__2(lean_object*, size_t, size_t, lean_object*);
lean_object* lean_array_swap(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Compiler_instInhabitedSpecializeAttributeKind;
extern lean_object* l_Lean_instInhabitedEnumAttributes___closed__1;
lean_object* l_Std_AssocList_foldlM___at_Lean_Compiler_SpecState_addEntry___spec__21(lean_object*, lean_object*);
lean_object* l_Std_RBNode_find___at___private_Lean_Compiler_Specialize_0__Lean_Compiler_hasSpecializeAttrAux___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__3(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__11;
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_instInhabitedSpecEntry;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isInternal(lean_object*);
lean_object* l_Std_mkHashMapImp___rarg(lean_object*);
lean_object* l_Std_RBNode_fold___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Std_AssocList_replace___at_Lean_Compiler_SpecState_addEntry___spec__22(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_quickCmp(lean_object*, lean_object*);
lean_object* l_Std_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Name_hash(lean_object*);
lean_object* l_Array_qpartition_loop___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__4___closed__1;
extern lean_object* l_IO_instInhabitedError___closed__1;
uint64_t l_Lean_Expr_hash(lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___lambda__2(lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__7___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerEnumAttributes___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__1___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_hasSpecializeAttribute___boxed(lean_object*, lean_object*);
lean_object* l_Array_qpartition_loop___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_has_specialize_attribute(lean_object*, lean_object*);
extern lean_object* l_Lean_persistentEnvExtensionsRef;
lean_object* l_Lean_mkStateFromImportedEntries___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_323____spec__1(lean_object*, lean_object*);
extern lean_object* l_Lean_registerParametricAttribute___rarg___closed__1;
uint8_t l_Std_AssocList_contains___at_Lean_Compiler_SpecState_addEntry___spec__7(lean_object*, lean_object*);
extern lean_object* l_Lean_registerTagAttribute___lambda__5___closed__4;
lean_object* l_List_map___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__7___lambda__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_modn(size_t, lean_object*);
lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_323____closed__2;
lean_object* l_Lean_SMap_insert___at_Lean_Compiler_SpecState_addEntry___spec__12(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkEmptyEnvironment___lambda__1___closed__1;
lean_object* l_Lean_Compiler_SpecState_cache___default___closed__1;
lean_object* lean_add_specialization_info(lean_object*, lean_object*, lean_object*);
size_t l_USize_mul(size_t, size_t);
extern lean_object* l_Lean_initFn____x40_Lean_Environment___hyg_3629____closed__4;
lean_object* l_Std_PersistentHashMap_insert___at_Lean_Compiler_SpecState_addEntry___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_qpartition_loop___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_SpecState_cache___default___closed__2;
lean_object* l_Lean_Compiler_instInhabitedSpecEntry___closed__1;
lean_object* l_Lean_Compiler_instInhabitedSpecState___closed__1;
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_registerEnumAttributes___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
extern lean_object* l_Lean_registerTagAttribute___lambda__6___closed__2;
lean_object* l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Compiler_SpecState_addEntry___spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Compiler_getCachedSpecialization___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_List_map___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_instInhabitedSpecState___closed__2;
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Compiler_getCachedSpecialization___spec__5(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___rarg(lean_object*, lean_object*, lean_object*);
size_t l_USize_land(size_t, size_t);
lean_object* l_Lean_Compiler_instInhabitedSpecInfo___closed__1;
lean_object* l_Lean_SimplePersistentEnvExtension_getState___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__6;
lean_object* l_Array_anyMUnsafe_any___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_323____spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_binSearchAux___at___private_Lean_Compiler_Specialize_0__Lean_Compiler_hasSpecializeAttrAux___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_323____closed__1;
lean_object* lean_cache_specialization(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Compiler_instInhabitedSpecArgKind;
lean_object* l_Lean_Compiler_SpecState_addEntry_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____lambda__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___rarg___closed__1;
lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_SpecState_addEntry___spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_AssocList_find_x3f___at_Lean_Compiler_getSpecializationInfo___spec__6(lean_object*, lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_323____spec__4(lean_object*, lean_object*);
uint8_t l___private_Lean_Compiler_Specialize_0__Lean_Compiler_beqSpecializeAttributeKind____x40_Lean_Compiler_Specialize___hyg_11_(uint8_t, uint8_t);
extern lean_object* l_Lean_registerTagAttribute___lambda__5___closed__2;
lean_object* l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__13;
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_323____lambda__1(lean_object*);
lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_323_(lean_object*);
lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49_(lean_object*);
lean_object* l_List_map___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__7(lean_object*, uint8_t, lean_object*, lean_object*);
uint8_t lean_has_nospecialize_attribute(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t l_USize_decLe(size_t, size_t);
lean_object* l_Lean_SMap_find_x3f___at_Lean_Compiler_getSpecializationInfo___spec__1(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Compiler_getCachedSpecialization___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Compiler_getSpecializationInfo___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_AssocList_contains___at_Lean_Compiler_SpecState_addEntry___spec__18(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_instInhabitedSpecInfo;
extern lean_object* l_Lean_registerEnumAttributes___rarg___closed__2;
extern lean_object* l_Lean_registerSimplePersistentEnvExtension___rarg___closed__1;
lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Compiler_getSpecializationInfo___spec__2___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_registerEnumAttributes___rarg___closed__1;
lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_323____lambda__1___boxed(lean_object*);
lean_object* l_Lean_Compiler_specExtension___elambda__2(lean_object*);
extern lean_object* l_Lean_EnvExtensionInterfaceUnsafe_instInhabitedExt___closed__2;
lean_object* l_Lean_Compiler_specExtension___elambda__1___boxed(lean_object*);
lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__10;
lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_beqSpecializeAttributeKind____x40_Lean_Compiler_Specialize___hyg_11__match__1(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lean_Name_getPrefix(lean_object*);
lean_object* l_Std_RBNode_find___at___private_Lean_Compiler_Specialize_0__Lean_Compiler_hasSpecializeAttrAux___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Compiler_getCachedSpecialization___spec__3(lean_object*, size_t, lean_object*);
extern lean_object* l_Lean_instInhabitedName;
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Compiler_getSpecializationInfo___spec__5___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Array_qsort_sort___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Compiler_getSpecializationInfo___spec__3___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyMUnsafe_any___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__6(lean_object*, lean_object*, size_t, size_t);
lean_object* lean_get_cached_specialization(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_specExtension___elambda__1(lean_object*);
lean_object* l_Array_qsort_sort___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_SpecState_addEntry___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_mkHashMap___at_Lean_Compiler_SpecState_specInfo___default___spec__1(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
extern size_t l_Std_PersistentHashMap_insertAux___rarg___closed__2;
lean_object* l_Lean_PersistentEnvExtension_getState___rarg(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Compiler_SpecState_addEntry___spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_HashMap_instInhabitedHashMap___closed__1;
lean_object* l_List_map___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__7___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_AssocList_find_x3f___at_Lean_Compiler_getCachedSpecialization___spec__6___boxed(lean_object*, lean_object*);
lean_object* l_Std_RBNode_fold___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_SpecState_specInfo___default___closed__2;
lean_object* l_List_map___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__7___lambda__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_hasSpecializeAttrAux_match__1(lean_object*);
lean_object* l_Lean_Compiler_SpecState_specInfo___default___closed__1;
lean_object* l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Compiler_SpecState_addEntry___spec__15(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Compiler_SpecState_addEntry___spec__16(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__7;
lean_object* l_Lean_Compiler_SpecState_switch(lean_object*);
uint8_t l_Array_anyMUnsafe_any___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_323____spec__6(lean_object*, lean_object*, size_t, size_t);
lean_object* l_Lean_Attribute_Builtin_ensureNoArgs(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_SpecState_addEntry(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_specExtension___elambda__4___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__15;
lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_SpecState_addEntry___spec__14(lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_specExtension___closed__3;
lean_object* l_Lean_Compiler_specExtension___closed__5;
lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__14;
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_323____spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_mkHashMap___at_Lean_Compiler_SpecState_cache___default___spec__1(lean_object*);
lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__5;
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Compiler_getSpecializationInfo___spec__5(lean_object*, lean_object*);
lean_object* l_Array_anyMUnsafe_any___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_EStateM_pure___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_SpecState_addEntry_match__1(lean_object*);
lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__3;
lean_object* l_Std_HashMapImp_insert___at_Lean_Compiler_SpecState_addEntry___spec__17(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkStateFromImportedEntries___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_323____spec__1___boxed(lean_object*, lean_object*);
lean_object* l_List_map___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__7___lambda__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Compiler_getSpecializationInfo___spec__3(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Compiler_specExtension___elambda__3(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_instBEqSpecializeAttributeKind___closed__1;
lean_object* l_Lean_registerEnumAttributes___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__1___closed__1;
lean_object* l_Lean_Compiler_specExtension___elambda__4___rarg(lean_object*);
lean_object* l_Std_AssocList_contains___at_Lean_Compiler_SpecState_addEntry___spec__18___boxed(lean_object*, lean_object*);
lean_object* l_List_map___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__7___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_mkCollisionNode___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_qsort_sort___at_Lean_mkMapDeclarationExtension___spec__1___rarg___closed__1;
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Compiler_getCachedSpecialization___spec__5___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_instInhabitedSpecState;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Compiler_getCachedSpecialization___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerEnumAttributes___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__1___closed__2;
lean_object* l_Lean_Compiler_SpecState_cache___default;
#define _init_l_Lean_Compiler_instInhabitedSpecializeAttributeKind(__INIT_VAR__) { \
{\
uint8_t x_1; \
x_1 = 0;\
__INIT_VAR__ = x_1; goto l_Lean_Compiler_instInhabitedSpecializeAttributeKind_end;\
}\
l_Lean_Compiler_instInhabitedSpecializeAttributeKind_end: ((void) 0);}
lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_beqSpecializeAttributeKind____x40_Lean_Compiler_Specialize___hyg_11__match__1___rarg(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (x_1 == 0)
{
lean_dec(x_4);
if (x_2 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_5);
x_6 = lean_box(0);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
x_8 = lean_box(x_1);
x_9 = lean_box(x_2);
x_10 = lean_apply_2(x_5, x_8, x_9);
return x_10;
}
}
else
{
lean_dec(x_3);
if (x_2 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_4);
x_11 = lean_box(x_1);
x_12 = lean_box(x_2);
x_13 = lean_apply_2(x_5, x_11, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_5);
x_14 = lean_box(0);
x_15 = lean_apply_1(x_4, x_14);
return x_15;
}
}
}
}
lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_beqSpecializeAttributeKind____x40_Lean_Compiler_Specialize___hyg_11__match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_beqSpecializeAttributeKind____x40_Lean_Compiler_Specialize___hyg_11__match__1___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_beqSpecializeAttributeKind____x40_Lean_Compiler_Specialize___hyg_11__match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = lean_unbox(x_2);
lean_dec(x_2);
x_8 = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_beqSpecializeAttributeKind____x40_Lean_Compiler_Specialize___hyg_11__match__1___rarg(x_6, x_7, x_3, x_4, x_5);
return x_8;
}
}
uint8_t l___private_Lean_Compiler_Specialize_0__Lean_Compiler_beqSpecializeAttributeKind____x40_Lean_Compiler_Specialize___hyg_11_(uint8_t x_1, uint8_t x_2) {
_start:
{
if (x_1 == 0)
{
if (x_2 == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
else
{
if (x_2 == 0)
{
uint8_t x_5; 
x_5 = 0;
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
}
lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_beqSpecializeAttributeKind____x40_Lean_Compiler_Specialize___hyg_11____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_beqSpecializeAttributeKind____x40_Lean_Compiler_Specialize___hyg_11_(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
#define _init_l_Lean_Compiler_instBEqSpecializeAttributeKind___closed__1(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_alloc_closure((void*)(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_beqSpecializeAttributeKind____x40_Lean_Compiler_Specialize___hyg_11____boxed), 2, 0);\
__INIT_VAR__ = x_1; goto l_Lean_Compiler_instBEqSpecializeAttributeKind___closed__1_end;\
}\
l_Lean_Compiler_instBEqSpecializeAttributeKind___closed__1_end: ((void) 0);}
#define _init_l_Lean_Compiler_instBEqSpecializeAttributeKind(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = l_Lean_Compiler_instBEqSpecializeAttributeKind___closed__1;\
__INIT_VAR__ = x_1; goto l_Lean_Compiler_instBEqSpecializeAttributeKind_end;\
}\
l_Lean_Compiler_instBEqSpecializeAttributeKind_end: ((void) 0);}
lean_object* l_Std_RBNode_fold___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_ctor_get(x_2, 3);
x_7 = l_Std_RBNode_fold___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__2(x_1, x_3);
lean_inc(x_5);
lean_inc(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_5);
x_9 = lean_array_push(x_7, x_8);
x_1 = x_9;
x_2 = x_6;
goto _start;
}
}
}
#define _init_l_Array_qpartition_loop___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__4___closed__1(__INIT_VAR__) { \
{\
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; \
x_1 = l_Lean_instInhabitedName;\
x_2 = l_Lean_Compiler_instInhabitedSpecializeAttributeKind;\
x_3 = lean_box(x_2);\
x_4 = lean_alloc_ctor(0, 2, 0);\
lean_ctor_set(x_4, 0, x_1);\
lean_ctor_set(x_4, 1, x_3);\
__INIT_VAR__ = x_4; goto l_Array_qpartition_loop___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__4___closed__1_end;\
}\
l_Array_qpartition_loop___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__4___closed__1_end: ((void) 0);}
lean_object* l_Array_qpartition_loop___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_nat_dec_lt(x_6, x_2);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_8 = lean_array_swap(x_4, x_5, x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = l_Array_qpartition_loop___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__4___closed__1;
x_11 = lean_array_get(x_10, x_4, x_6);
lean_inc(x_1);
lean_inc(x_3);
x_12 = lean_apply_2(x_1, x_11, x_3);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_6, x_14);
lean_dec(x_6);
x_6 = x_15;
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_array_swap(x_4, x_5, x_6);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_5, x_18);
lean_dec(x_5);
x_20 = lean_nat_add(x_6, x_18);
lean_dec(x_6);
x_4 = x_17;
x_5 = x_19;
x_6 = x_20;
goto _start;
}
}
}
}
lean_object* l_Array_qsort_sort___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_13; 
x_13 = lean_nat_dec_lt(x_2, x_3);
if (x_13 == 0)
{
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_14 = lean_nat_add(x_2, x_3);
x_15 = lean_unsigned_to_nat(2u);
x_16 = lean_nat_div(x_14, x_15);
lean_dec(x_14);
x_46 = l_Array_qpartition_loop___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__4___closed__1;
x_47 = lean_array_get(x_46, x_1, x_16);
x_48 = lean_array_get(x_46, x_1, x_2);
x_49 = lean_ctor_get(x_47, 0);
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_ctor_get(x_48, 0);
lean_inc(x_50);
lean_dec(x_48);
x_51 = l_Lean_Name_quickLt(x_49, x_50);
lean_dec(x_50);
lean_dec(x_49);
if (x_51 == 0)
{
x_17 = x_1;
goto block_45;
}
else
{
lean_object* x_52; 
x_52 = lean_array_swap(x_1, x_2, x_16);
x_17 = x_52;
goto block_45;
}
block_45:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_18 = l_Array_qpartition_loop___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__4___closed__1;
x_19 = lean_array_get(x_18, x_17, x_3);
x_20 = lean_array_get(x_18, x_17, x_2);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Name_quickLt(x_21, x_22);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_array_get(x_18, x_17, x_16);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec(x_24);
x_26 = l_Lean_Name_quickLt(x_25, x_21);
lean_dec(x_21);
lean_dec(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_16);
x_27 = l_Array_qsort_sort___at_Lean_mkMapDeclarationExtension___spec__1___rarg___closed__1;
lean_inc_n(x_2, 2);
x_28 = l_Array_qpartition_loop___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__4(x_27, x_3, x_19, x_17, x_2, x_2);
x_4 = x_28;
goto block_12;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_19);
x_29 = lean_array_swap(x_17, x_16, x_3);
lean_dec(x_16);
x_30 = lean_array_get(x_18, x_29, x_3);
x_31 = l_Array_qsort_sort___at_Lean_mkMapDeclarationExtension___spec__1___rarg___closed__1;
lean_inc_n(x_2, 2);
x_32 = l_Array_qpartition_loop___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__4(x_31, x_3, x_30, x_29, x_2, x_2);
x_4 = x_32;
goto block_12;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
lean_dec(x_21);
lean_dec(x_19);
x_33 = lean_array_swap(x_17, x_2, x_3);
x_34 = lean_array_get(x_18, x_33, x_16);
x_35 = lean_array_get(x_18, x_33, x_3);
x_36 = lean_ctor_get(x_34, 0);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
x_38 = l_Lean_Name_quickLt(x_36, x_37);
lean_dec(x_37);
lean_dec(x_36);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_16);
x_39 = l_Array_qsort_sort___at_Lean_mkMapDeclarationExtension___spec__1___rarg___closed__1;
lean_inc_n(x_2, 2);
x_40 = l_Array_qpartition_loop___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__4(x_39, x_3, x_35, x_33, x_2, x_2);
x_4 = x_40;
goto block_12;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_35);
x_41 = lean_array_swap(x_33, x_16, x_3);
lean_dec(x_16);
x_42 = lean_array_get(x_18, x_41, x_3);
x_43 = l_Array_qsort_sort___at_Lean_mkMapDeclarationExtension___spec__1___rarg___closed__1;
lean_inc_n(x_2, 2);
x_44 = l_Array_qpartition_loop___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__4(x_43, x_3, x_42, x_41, x_2, x_2);
x_4 = x_44;
goto block_12;
}
}
}
}
block_12:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_nat_dec_le(x_3, x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Array_qsort_sort___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__3(x_6, x_2, x_5);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_5, x_9);
lean_dec(x_5);
x_1 = x_8;
x_2 = x_10;
goto _start;
}
else
{
lean_dec(x_5);
lean_dec(x_2);
return x_6;
}
}
}
}
uint8_t l_Array_anyMUnsafe_any___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__6(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
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
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__5(lean_object* x_1, lean_object* x_2) {
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
x_18 = l_Array_anyMUnsafe_any___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__6(x_1, x_6, x_16, x_17);
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
lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
lean_dec(x_1);
x_22 = 1;
x_23 = l_Lean_Name_toString(x_21, x_22);
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
x_41 = l_Array_anyMUnsafe_any___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__6(x_1, x_29, x_39, x_40);
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
lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_44 = lean_ctor_get(x_1, 0);
lean_inc(x_44);
lean_dec(x_1);
x_45 = 1;
x_46 = l_Lean_Name_toString(x_44, x_45);
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
lean_object* l_List_map___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__7___lambda__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(x_3);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
x_11 = lean_apply_5(x_1, x_2, x_10, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_box(x_3);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_PersistentEnvExtension_addEntry___rarg(x_4, x_5, x_14);
x_16 = l_Lean_setEnv___at_Lean_registerTagAttribute___spec__4(x_15, x_7, x_8, x_12);
lean_dec(x_8);
lean_dec(x_7);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_17 = !lean_is_exclusive(x_11);
if (x_17 == 0)
{
return x_11;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_11, 0);
x_19 = lean_ctor_get(x_11, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_11);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
lean_object* l_List_map___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__7___lambda__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_st_ref_get(x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Environment_getModuleIdxFor_x3f(x_13, x_2);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_5);
x_15 = lean_box(0);
x_16 = l_List_map___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__7___lambda__1(x_1, x_2, x_3, x_4, x_13, x_15, x_7, x_8, x_12);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_17 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_17, 0, x_5);
x_18 = l_Lean_registerTagAttribute___lambda__5___closed__2;
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = l_Lean_registerTagAttribute___lambda__5___closed__4;
x_21 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_throwError___at_Lean_registerTagAttribute___spec__5(x_21, x_7, x_8, x_12);
lean_dec(x_8);
lean_dec(x_7);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
return x_22;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_22);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
lean_object* l_List_map___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__7___lambda__3(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_8);
x_11 = l_Lean_Attribute_Builtin_ensureNoArgs(x_6, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; uint8_t x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = 0;
x_14 = l___private_Lean_Attributes_0__Lean_beqAttributeKind____x40_Lean_Attributes___hyg_139_(x_7, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_15 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_15, 0, x_4);
x_16 = l_Lean_registerTagAttribute___lambda__5___closed__2;
x_17 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = l_Lean_registerTagAttribute___lambda__6___closed__2;
x_19 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_throwError___at_Lean_registerTagAttribute___spec__5(x_19, x_8, x_9, x_12);
lean_dec(x_9);
lean_dec(x_8);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
return x_20;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_20);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_box(0);
x_26 = l_List_map___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__7___lambda__2(x_1, x_5, x_2, x_3, x_4, x_25, x_8, x_9, x_12);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_11);
if (x_27 == 0)
{
return x_11;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_11, 0);
x_29 = lean_ctor_get(x_11, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_11);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
lean_object* l_List_map___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__7(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_3);
lean_inc(x_1);
x_9 = l_List_map___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__7(x_1, x_2, x_3, x_8);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
lean_inc(x_11);
x_14 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_12);
lean_ctor_set_uint8(x_14, sizeof(void*)*2, x_2);
x_15 = lean_alloc_closure((void*)(l_List_map___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__7___lambda__3___boxed), 10, 4);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_13);
lean_closure_set(x_15, 2, x_3);
lean_closure_set(x_15, 3, x_11);
x_16 = l_Lean_registerTagAttribute___closed__5;
x_17 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_15);
lean_ctor_set(x_17, 2, x_16);
lean_ctor_set(x_4, 1, x_9);
lean_ctor_set(x_4, 0, x_17);
return x_4;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_18 = lean_ctor_get(x_4, 0);
x_19 = lean_ctor_get(x_4, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_20 = l_List_map___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__7(x_1, x_2, x_3, x_19);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_18, 0);
lean_inc(x_22);
lean_dec(x_18);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
lean_inc(x_22);
x_25 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_23);
lean_ctor_set_uint8(x_25, sizeof(void*)*2, x_2);
x_26 = lean_alloc_closure((void*)(l_List_map___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__7___lambda__3___boxed), 10, 4);
lean_closure_set(x_26, 0, x_1);
lean_closure_set(x_26, 1, x_24);
lean_closure_set(x_26, 2, x_3);
lean_closure_set(x_26, 3, x_22);
x_27 = l_Lean_registerTagAttribute___closed__5;
x_28 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_26);
lean_ctor_set(x_28, 2, x_27);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_20);
return x_29;
}
}
}
}
lean_object* l_Lean_registerEnumAttributes___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__1___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Std_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_1, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_registerEnumAttributes___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__1___lambda__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = l_Array_empty___closed__1;
x_3 = l_Std_RBNode_fold___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__2(x_2, x_1);
x_4 = lean_array_get_size(x_3);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_sub(x_4, x_5);
lean_dec(x_4);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Array_qsort_sort___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__3(x_3, x_7, x_6);
lean_dec(x_6);
return x_8;
}
}
#define _init_l_Lean_registerEnumAttributes___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__1___closed__1(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_alloc_closure((void*)(l_Lean_registerEnumAttributes___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__1___lambda__1), 2, 0);\
__INIT_VAR__ = x_1; goto l_Lean_registerEnumAttributes___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__1___closed__1_end;\
}\
l_Lean_registerEnumAttributes___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__1___closed__1_end: ((void) 0);}
#define _init_l_Lean_registerEnumAttributes___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__1___closed__2(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_alloc_closure((void*)(l_Lean_registerEnumAttributes___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__1___lambda__2___boxed), 1, 0);\
__INIT_VAR__ = x_1; goto l_Lean_registerEnumAttributes___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__1___closed__2_end;\
}\
l_Lean_registerEnumAttributes___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__1___closed__2_end: ((void) 0);}
lean_object* l_Lean_registerEnumAttributes___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = l_Lean_registerParametricAttribute___rarg___closed__1;
x_7 = l_Lean_registerEnumAttributes___rarg___closed__1;
x_8 = l_Lean_registerEnumAttributes___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__1___closed__1;
x_9 = l_Lean_registerEnumAttributes___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__1___closed__2;
x_10 = l_Lean_registerEnumAttributes___rarg___closed__2;
x_11 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_6);
lean_ctor_set(x_11, 2, x_7);
lean_ctor_set(x_11, 3, x_8);
lean_ctor_set(x_11, 4, x_9);
lean_ctor_set(x_11, 5, x_10);
x_12 = l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__5(x_11, x_5);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_13);
x_15 = l_List_map___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__7(x_3, x_4, x_13, x_2);
lean_inc(x_15);
x_16 = l_List_forM___at_Lean_registerEnumAttributes___spec__10(x_15, x_14);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set(x_19, 1, x_13);
lean_ctor_set(x_16, 0, x_19);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_15);
lean_ctor_set(x_21, 1, x_13);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_15);
lean_dec(x_13);
x_23 = !lean_is_exclusive(x_16);
if (x_23 == 0)
{
return x_16;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_16, 0);
x_25 = lean_ctor_get(x_16, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_16);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
uint8_t x_27; 
lean_dec(x_3);
lean_dec(x_2);
x_27 = !lean_is_exclusive(x_12);
if (x_27 == 0)
{
return x_12;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_12, 0);
x_29 = lean_ctor_get(x_12, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_12);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____lambda__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
}
#define _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__1(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_mk_string("specializeAttrs");\
__INIT_VAR__ = x_1; goto l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__1_end;\
}\
l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__1_end: ((void) 0);}
#define _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__2(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; lean_object* x_3; \
x_1 = lean_box(0);\
x_2 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__1;\
x_3 = lean_name_mk_string(x_1, x_2);\
__INIT_VAR__ = x_3; goto l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__2_end;\
}\
l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__2_end: ((void) 0);}
#define _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__3(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_mk_string("specialize");\
__INIT_VAR__ = x_1; goto l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__3_end;\
}\
l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__3_end: ((void) 0);}
#define _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__4(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; lean_object* x_3; \
x_1 = lean_box(0);\
x_2 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__3;\
x_3 = lean_name_mk_string(x_1, x_2);\
__INIT_VAR__ = x_3; goto l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__4_end;\
}\
l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__4_end: ((void) 0);}
#define _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__5(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_mk_string("mark definition to always be specialized");\
__INIT_VAR__ = x_1; goto l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__5_end;\
}\
l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__5_end: ((void) 0);}
#define _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__6(__INIT_VAR__) { \
{\
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; \
x_1 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__5;\
x_2 = 0;\
x_3 = lean_box(x_2);\
x_4 = lean_alloc_ctor(0, 2, 0);\
lean_ctor_set(x_4, 0, x_1);\
lean_ctor_set(x_4, 1, x_3);\
__INIT_VAR__ = x_4; goto l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__6_end;\
}\
l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__6_end: ((void) 0);}
#define _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__7(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; lean_object* x_3; \
x_1 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__4;\
x_2 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__6;\
x_3 = lean_alloc_ctor(0, 2, 0);\
lean_ctor_set(x_3, 0, x_1);\
lean_ctor_set(x_3, 1, x_2);\
__INIT_VAR__ = x_3; goto l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__7_end;\
}\
l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__7_end: ((void) 0);}
#define _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__8(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_mk_string("nospecialize");\
__INIT_VAR__ = x_1; goto l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__8_end;\
}\
l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__8_end: ((void) 0);}
#define _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__9(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; lean_object* x_3; \
x_1 = lean_box(0);\
x_2 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__8;\
x_3 = lean_name_mk_string(x_1, x_2);\
__INIT_VAR__ = x_3; goto l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__9_end;\
}\
l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__9_end: ((void) 0);}
#define _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__10(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_mk_string("mark definition to never be specialized");\
__INIT_VAR__ = x_1; goto l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__10_end;\
}\
l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__10_end: ((void) 0);}
#define _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__11(__INIT_VAR__) { \
{\
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; \
x_1 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__10;\
x_2 = 1;\
x_3 = lean_box(x_2);\
x_4 = lean_alloc_ctor(0, 2, 0);\
lean_ctor_set(x_4, 0, x_1);\
lean_ctor_set(x_4, 1, x_3);\
__INIT_VAR__ = x_4; goto l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__11_end;\
}\
l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__11_end: ((void) 0);}
#define _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__12(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; lean_object* x_3; \
x_1 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__9;\
x_2 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__11;\
x_3 = lean_alloc_ctor(0, 2, 0);\
lean_ctor_set(x_3, 0, x_1);\
lean_ctor_set(x_3, 1, x_2);\
__INIT_VAR__ = x_3; goto l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__12_end;\
}\
l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__12_end: ((void) 0);}
#define _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__13(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; lean_object* x_3; \
x_1 = lean_box(0);\
x_2 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__12;\
x_3 = lean_alloc_ctor(1, 2, 0);\
lean_ctor_set(x_3, 0, x_2);\
lean_ctor_set(x_3, 1, x_1);\
__INIT_VAR__ = x_3; goto l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__13_end;\
}\
l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__13_end: ((void) 0);}
#define _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__14(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; lean_object* x_3; \
x_1 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__7;\
x_2 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__13;\
x_3 = lean_alloc_ctor(1, 2, 0);\
lean_ctor_set(x_3, 0, x_1);\
lean_ctor_set(x_3, 1, x_2);\
__INIT_VAR__ = x_3; goto l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__14_end;\
}\
l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__14_end: ((void) 0);}
#define _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__15(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____lambda__1___boxed), 5, 0);\
__INIT_VAR__ = x_1; goto l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__15_end;\
}\
l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__15_end: ((void) 0);}
lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__2;
x_3 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__14;
x_4 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__15;
x_5 = 2;
x_6 = l_Lean_registerEnumAttributes___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__1(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
lean_object* l_Std_RBNode_fold___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_RBNode_fold___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__2(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_qpartition_loop___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_qpartition_loop___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__4(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Array_qsort_sort___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_qsort_sort___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__3(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_Array_anyMUnsafe_any___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__6(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
lean_object* l_List_map___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__7___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l_List_map___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__7___lambda__1(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_6);
return x_11;
}
}
lean_object* l_List_map___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__7___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l_List_map___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__7___lambda__2(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_6);
return x_11;
}
}
lean_object* l_List_map___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__7___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_2);
lean_dec(x_2);
x_12 = lean_unbox(x_7);
lean_dec(x_7);
x_13 = l_List_map___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__7___lambda__3(x_1, x_11, x_3, x_4, x_5, x_6, x_12, x_8, x_9, x_10);
return x_13;
}
}
lean_object* l_List_map___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_List_map___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__7(x_1, x_5, x_3, x_4);
return x_6;
}
}
lean_object* l_Lean_registerEnumAttributes___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__1___lambda__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_registerEnumAttributes___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__1___lambda__2(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_registerEnumAttributes___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_4);
lean_dec(x_4);
x_7 = l_Lean_registerEnumAttributes___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__1(x_1, x_2, x_3, x_6, x_5);
return x_7;
}
}
lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____lambda__1(x_1, x_6, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_hasSpecializeAttrAux_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_hasSpecializeAttrAux_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Compiler_Specialize_0__Lean_Compiler_hasSpecializeAttrAux_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Std_RBNode_find___at___private_Lean_Compiler_Specialize_0__Lean_Compiler_hasSpecializeAttrAux___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
x_8 = l_Lean_Name_quickCmp(x_2, x_5);
switch (x_8) {
case 0:
{
x_1 = x_4;
goto _start;
}
case 1:
{
lean_object* x_10; 
lean_inc(x_6);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_6);
return x_10;
}
default: 
{
x_1 = x_7;
goto _start;
}
}
}
}
}
lean_object* l_Array_binSearchAux___at___private_Lean_Compiler_Specialize_0__Lean_Compiler_hasSpecializeAttrAux___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_le(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = lean_nat_add(x_3, x_4);
x_8 = lean_unsigned_to_nat(2u);
x_9 = lean_nat_div(x_7, x_8);
lean_dec(x_7);
x_10 = l_Array_qpartition_loop___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__4___closed__1;
x_11 = lean_array_get(x_10, x_1, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 0);
x_14 = l_Lean_Name_quickLt(x_12, x_13);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_4);
x_15 = l_Lean_Name_quickLt(x_13, x_12);
lean_dec(x_12);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_9);
lean_dec(x_3);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_11);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; 
lean_dec(x_11);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_eq(x_9, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_sub(x_9, x_19);
lean_dec(x_9);
x_4 = x_20;
goto _start;
}
else
{
lean_object* x_22; 
lean_dec(x_9);
lean_dec(x_3);
x_22 = lean_box(0);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_3);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_9, x_23);
lean_dec(x_9);
x_3 = x_24;
goto _start;
}
}
}
}
lean_object* l_Lean_EnumAttributes_getValue___at___private_Lean_Compiler_Specialize_0__Lean_Compiler_hasSpecializeAttrAux___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Environment_getModuleIdxFor_x3f(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 1);
x_6 = l_Lean_PersistentEnvExtension_getState___rarg(x_5, x_2);
x_7 = l_Std_RBNode_find___at___private_Lean_Compiler_Specialize_0__Lean_Compiler_hasSpecializeAttrAux___spec__2(x_6, x_3);
lean_dec(x_3);
lean_dec(x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
lean_dec(x_4);
x_9 = lean_ctor_get(x_1, 1);
x_10 = l_Lean_PersistentEnvExtension_getModuleEntries___rarg(x_9, x_2, x_8);
lean_dec(x_8);
x_11 = 0;
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_3);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_array_get_size(x_10);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_14, x_15);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_lt(x_17, x_14);
lean_dec(x_14);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_10);
x_19 = lean_box(0);
return x_19;
}
else
{
lean_object* x_20; 
x_20 = l_Array_binSearchAux___at___private_Lean_Compiler_Specialize_0__Lean_Compiler_hasSpecializeAttrAux___spec__3(x_10, x_13, x_17, x_16);
lean_dec(x_13);
lean_dec(x_10);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_box(0);
return x_21;
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 0);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
lean_ctor_set(x_20, 0, x_24);
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_20, 0);
lean_inc(x_25);
lean_dec(x_20);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
}
}
}
}
uint8_t l___private_Lean_Compiler_Specialize_0__Lean_Compiler_hasSpecializeAttrAux(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Compiler_specializeAttrs;
lean_inc(x_3);
x_5 = l_Lean_EnumAttributes_getValue___at___private_Lean_Compiler_Specialize_0__Lean_Compiler_hasSpecializeAttrAux___spec__1(x_4, x_1, x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = l_Lean_Name_isInternal(x_3);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_3);
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; 
x_8 = l_Lean_Name_getPrefix(x_3);
lean_dec(x_3);
x_3 = x_8;
goto _start;
}
}
else
{
lean_object* x_10; uint8_t x_11; uint8_t x_12; 
lean_dec(x_3);
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
x_12 = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_beqSpecializeAttributeKind____x40_Lean_Compiler_Specialize___hyg_11_(x_2, x_11);
return x_12;
}
}
}
lean_object* l_Std_RBNode_find___at___private_Lean_Compiler_Specialize_0__Lean_Compiler_hasSpecializeAttrAux___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_RBNode_find___at___private_Lean_Compiler_Specialize_0__Lean_Compiler_hasSpecializeAttrAux___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Array_binSearchAux___at___private_Lean_Compiler_Specialize_0__Lean_Compiler_hasSpecializeAttrAux___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_binSearchAux___at___private_Lean_Compiler_Specialize_0__Lean_Compiler_hasSpecializeAttrAux___spec__3(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_EnumAttributes_getValue___at___private_Lean_Compiler_Specialize_0__Lean_Compiler_hasSpecializeAttrAux___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_EnumAttributes_getValue___at___private_Lean_Compiler_Specialize_0__Lean_Compiler_hasSpecializeAttrAux___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l___private_Lean_Compiler_Specialize_0__Lean_Compiler_hasSpecializeAttrAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_hasSpecializeAttrAux(x_1, x_4, x_3);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
uint8_t lean_has_specialize_attribute(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; 
x_3 = 0;
x_4 = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_hasSpecializeAttrAux(x_1, x_3, x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Compiler_hasSpecializeAttribute___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_has_specialize_attribute(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t lean_has_nospecialize_attribute(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; 
x_3 = 1;
x_4 = l___private_Lean_Compiler_Specialize_0__Lean_Compiler_hasSpecializeAttrAux(x_1, x_3, x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_Compiler_hasNospecializeAttribute___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_has_nospecialize_attribute(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
#define _init_l_Lean_Compiler_instInhabitedSpecArgKind(__INIT_VAR__) { \
{\
uint8_t x_1; \
x_1 = 0;\
__INIT_VAR__ = x_1; goto l_Lean_Compiler_instInhabitedSpecArgKind_end;\
}\
l_Lean_Compiler_instInhabitedSpecArgKind_end: ((void) 0);}
#define _init_l_Lean_Compiler_instInhabitedSpecInfo___closed__1(__INIT_VAR__) { \
{\
lean_object* x_1; uint8_t x_2; lean_object* x_3; \
x_1 = lean_box(0);\
x_2 = 0;\
x_3 = lean_alloc_ctor(0, 1, 1);\
lean_ctor_set(x_3, 0, x_1);\
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);\
__INIT_VAR__ = x_3; goto l_Lean_Compiler_instInhabitedSpecInfo___closed__1_end;\
}\
l_Lean_Compiler_instInhabitedSpecInfo___closed__1_end: ((void) 0);}
#define _init_l_Lean_Compiler_instInhabitedSpecInfo(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = l_Lean_Compiler_instInhabitedSpecInfo___closed__1;\
__INIT_VAR__ = x_1; goto l_Lean_Compiler_instInhabitedSpecInfo_end;\
}\
l_Lean_Compiler_instInhabitedSpecInfo_end: ((void) 0);}
lean_object* l_Std_mkHashMap___at_Lean_Compiler_SpecState_specInfo___default___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
#define _init_l_Lean_Compiler_SpecState_specInfo___default___closed__1(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; \
x_1 = lean_unsigned_to_nat(8u);\
x_2 = l_Std_mkHashMapImp___rarg(x_1);\
__INIT_VAR__ = x_2; goto l_Lean_Compiler_SpecState_specInfo___default___closed__1_end;\
}\
l_Lean_Compiler_SpecState_specInfo___default___closed__1_end: ((void) 0);}
#define _init_l_Lean_Compiler_SpecState_specInfo___default___closed__2(__INIT_VAR__) { \
{\
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; \
x_1 = 1;\
x_2 = l_Lean_Compiler_SpecState_specInfo___default___closed__1;\
x_3 = l_Lean_LocalContext_fvarIdToDecl___default___closed__1;\
x_4 = lean_alloc_ctor(0, 2, 1);\
lean_ctor_set(x_4, 0, x_2);\
lean_ctor_set(x_4, 1, x_3);\
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);\
__INIT_VAR__ = x_4; goto l_Lean_Compiler_SpecState_specInfo___default___closed__2_end;\
}\
l_Lean_Compiler_SpecState_specInfo___default___closed__2_end: ((void) 0);}
#define _init_l_Lean_Compiler_SpecState_specInfo___default(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = l_Lean_Compiler_SpecState_specInfo___default___closed__2;\
__INIT_VAR__ = x_1; goto l_Lean_Compiler_SpecState_specInfo___default_end;\
}\
l_Lean_Compiler_SpecState_specInfo___default_end: ((void) 0);}
lean_object* l_Std_mkHashMap___at_Lean_Compiler_SpecState_cache___default___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
#define _init_l_Lean_Compiler_SpecState_cache___default___closed__1(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; \
x_1 = lean_unsigned_to_nat(8u);\
x_2 = l_Std_mkHashMapImp___rarg(x_1);\
__INIT_VAR__ = x_2; goto l_Lean_Compiler_SpecState_cache___default___closed__1_end;\
}\
l_Lean_Compiler_SpecState_cache___default___closed__1_end: ((void) 0);}
#define _init_l_Lean_Compiler_SpecState_cache___default___closed__2(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; lean_object* x_3; \
x_1 = l_Std_PersistentHashMap_root___default___closed__2;\
x_2 = lean_unsigned_to_nat(0u);\
x_3 = lean_alloc_ctor(0, 2, 0);\
lean_ctor_set(x_3, 0, x_1);\
lean_ctor_set(x_3, 1, x_2);\
__INIT_VAR__ = x_3; goto l_Lean_Compiler_SpecState_cache___default___closed__2_end;\
}\
l_Lean_Compiler_SpecState_cache___default___closed__2_end: ((void) 0);}
#define _init_l_Lean_Compiler_SpecState_cache___default___closed__3(__INIT_VAR__) { \
{\
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; \
x_1 = 1;\
x_2 = l_Lean_Compiler_SpecState_cache___default___closed__1;\
x_3 = l_Lean_Compiler_SpecState_cache___default___closed__2;\
x_4 = lean_alloc_ctor(0, 2, 1);\
lean_ctor_set(x_4, 0, x_2);\
lean_ctor_set(x_4, 1, x_3);\
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);\
__INIT_VAR__ = x_4; goto l_Lean_Compiler_SpecState_cache___default___closed__3_end;\
}\
l_Lean_Compiler_SpecState_cache___default___closed__3_end: ((void) 0);}
#define _init_l_Lean_Compiler_SpecState_cache___default(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = l_Lean_Compiler_SpecState_cache___default___closed__3;\
__INIT_VAR__ = x_1; goto l_Lean_Compiler_SpecState_cache___default_end;\
}\
l_Lean_Compiler_SpecState_cache___default_end: ((void) 0);}
#define _init_l_Lean_Compiler_instInhabitedSpecState___closed__1(__INIT_VAR__) { \
{\
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; \
x_1 = 1;\
x_2 = l_Std_HashMap_instInhabitedHashMap___closed__1;\
x_3 = l_Lean_Compiler_SpecState_cache___default___closed__2;\
x_4 = lean_alloc_ctor(0, 2, 1);\
lean_ctor_set(x_4, 0, x_2);\
lean_ctor_set(x_4, 1, x_3);\
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);\
__INIT_VAR__ = x_4; goto l_Lean_Compiler_instInhabitedSpecState___closed__1_end;\
}\
l_Lean_Compiler_instInhabitedSpecState___closed__1_end: ((void) 0);}
#define _init_l_Lean_Compiler_instInhabitedSpecState___closed__2(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; lean_object* x_3; \
x_1 = l_Lean_mkEmptyEnvironment___lambda__1___closed__1;\
x_2 = l_Lean_Compiler_instInhabitedSpecState___closed__1;\
x_3 = lean_alloc_ctor(0, 2, 0);\
lean_ctor_set(x_3, 0, x_1);\
lean_ctor_set(x_3, 1, x_2);\
__INIT_VAR__ = x_3; goto l_Lean_Compiler_instInhabitedSpecState___closed__2_end;\
}\
l_Lean_Compiler_instInhabitedSpecState___closed__2_end: ((void) 0);}
#define _init_l_Lean_Compiler_instInhabitedSpecState(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = l_Lean_Compiler_instInhabitedSpecState___closed__2;\
__INIT_VAR__ = x_1; goto l_Lean_Compiler_instInhabitedSpecState_end;\
}\
l_Lean_Compiler_instInhabitedSpecState_end: ((void) 0);}
#define _init_l_Lean_Compiler_instInhabitedSpecEntry___closed__1(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; lean_object* x_3; \
x_1 = lean_box(0);\
x_2 = l_Lean_Compiler_instInhabitedSpecInfo___closed__1;\
x_3 = lean_alloc_ctor(0, 2, 0);\
lean_ctor_set(x_3, 0, x_1);\
lean_ctor_set(x_3, 1, x_2);\
__INIT_VAR__ = x_3; goto l_Lean_Compiler_instInhabitedSpecEntry___closed__1_end;\
}\
l_Lean_Compiler_instInhabitedSpecEntry___closed__1_end: ((void) 0);}
#define _init_l_Lean_Compiler_instInhabitedSpecEntry(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = l_Lean_Compiler_instInhabitedSpecEntry___closed__1;\
__INIT_VAR__ = x_1; goto l_Lean_Compiler_instInhabitedSpecEntry_end;\
}\
l_Lean_Compiler_instInhabitedSpecEntry_end: ((void) 0);}
lean_object* l_Lean_Compiler_SpecState_addEntry_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_2, x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_apply_2(x_3, x_7, x_8);
return x_9;
}
}
}
lean_object* l_Lean_Compiler_SpecState_addEntry_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_SpecState_addEntry_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Compiler_SpecState_addEntry___spec__4(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_11 = l_Lean_Name_hash(x_9);
x_12 = (size_t)x_11;
x_13 = 1;
x_14 = x_1 - x_13;
x_15 = 5;
x_16 = x_15 * x_14;
x_17 = x_12 >> x_16 % (sizeof(size_t) * 8);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_5, x_18);
lean_dec(x_5);
x_20 = l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_SpecState_addEntry___spec__3(x_6, x_17, x_1, x_9, x_10);
x_4 = lean_box(0);
x_5 = x_19;
x_6 = x_20;
goto _start;
}
}
}
lean_object* l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Compiler_SpecState_addEntry___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_SpecState_addEntry___spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
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
x_36 = x_2 >> x_9 % (sizeof(size_t) * 8);
x_37 = x_3 + x_8;
x_38 = l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_SpecState_addEntry___spec__3(x_35, x_36, x_37, x_4, x_5);
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
x_41 = x_2 >> x_9 % (sizeof(size_t) * 8);
x_42 = x_3 + x_8;
x_43 = l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_SpecState_addEntry___spec__3(x_40, x_41, x_42, x_4, x_5);
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
x_73 = x_2 >> x_50 % (sizeof(size_t) * 8);
x_74 = x_3 + x_49;
x_75 = l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_SpecState_addEntry___spec__3(x_71, x_73, x_74, x_4, x_5);
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
x_84 = l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Compiler_SpecState_addEntry___spec__5(x_1, x_83, x_4, x_5);
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
x_93 = l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Compiler_SpecState_addEntry___spec__4(x_3, x_90, x_91, lean_box(0), x_83, x_92);
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
x_98 = l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Compiler_SpecState_addEntry___spec__5(x_96, x_97, x_4, x_5);
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
x_107 = l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Compiler_SpecState_addEntry___spec__4(x_3, x_104, x_105, lean_box(0), x_97, x_106);
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
lean_object* l_Std_PersistentHashMap_insert___at_Lean_Compiler_SpecState_addEntry___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint64_t x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_Name_hash(x_2);
x_8 = (size_t)x_7;
x_9 = 1;
x_10 = l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_SpecState_addEntry___spec__3(x_5, x_8, x_9, x_2, x_3);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_6, x_11);
lean_dec(x_6);
lean_ctor_set(x_1, 1, x_12);
lean_ctor_set(x_1, 0, x_10);
return x_1;
}
else
{
lean_object* x_13; lean_object* x_14; uint64_t x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_1);
x_15 = l_Lean_Name_hash(x_2);
x_16 = (size_t)x_15;
x_17 = 1;
x_18 = l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_SpecState_addEntry___spec__3(x_13, x_16, x_17, x_2, x_3);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_14, x_19);
lean_dec(x_14);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
uint8_t l_Std_AssocList_contains___at_Lean_Compiler_SpecState_addEntry___spec__7(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Std_AssocList_foldlM___at_Lean_Compiler_SpecState_addEntry___spec__10(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = l_Lean_Name_hash(x_4);
x_8 = (size_t)x_7;
x_9 = lean_usize_modn(x_8, x_6);
lean_dec(x_6);
x_10 = lean_array_uget(x_1, x_9);
lean_ctor_set(x_2, 2, x_10);
x_11 = lean_array_uset(x_1, x_9, x_2);
x_1 = x_11;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint64_t x_17; size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_ctor_get(x_2, 1);
x_15 = lean_ctor_get(x_2, 2);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_2);
x_16 = lean_array_get_size(x_1);
x_17 = l_Lean_Name_hash(x_13);
x_18 = (size_t)x_17;
x_19 = lean_usize_modn(x_18, x_16);
lean_dec(x_16);
x_20 = lean_array_uget(x_1, x_19);
x_21 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_21, 0, x_13);
lean_ctor_set(x_21, 1, x_14);
lean_ctor_set(x_21, 2, x_20);
x_22 = lean_array_uset(x_1, x_19, x_21);
x_1 = x_22;
x_2 = x_15;
goto _start;
}
}
}
}
lean_object* l_Std_HashMapImp_moveEntries___at_Lean_Compiler_SpecState_addEntry___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_AssocList_foldlM___at_Lean_Compiler_SpecState_addEntry___spec__10(x_3, x_6);
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
lean_object* l_Std_HashMapImp_expand___at_Lean_Compiler_SpecState_addEntry___spec__8(lean_object* x_1, lean_object* x_2) {
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
x_9 = l_Std_HashMapImp_moveEntries___at_Lean_Compiler_SpecState_addEntry___spec__9(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
lean_object* l_Std_AssocList_replace___at_Lean_Compiler_SpecState_addEntry___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_10 = l_Std_AssocList_replace___at_Lean_Compiler_SpecState_addEntry___spec__11(x_1, x_2, x_8);
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
x_15 = l_Std_AssocList_replace___at_Lean_Compiler_SpecState_addEntry___spec__11(x_1, x_2, x_13);
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
lean_object* l_Std_HashMapImp_insert___at_Lean_Compiler_SpecState_addEntry___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; size_t x_9; size_t x_10; lean_object* x_11; uint8_t x_12; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = l_Lean_Name_hash(x_2);
x_9 = (size_t)x_8;
x_10 = lean_usize_modn(x_9, x_7);
x_11 = lean_array_uget(x_6, x_10);
x_12 = l_Std_AssocList_contains___at_Lean_Compiler_SpecState_addEntry___spec__7(x_2, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_5, x_13);
lean_dec(x_5);
x_15 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_3);
lean_ctor_set(x_15, 2, x_11);
x_16 = lean_array_uset(x_6, x_10, x_15);
x_17 = lean_nat_dec_le(x_14, x_7);
lean_dec(x_7);
if (x_17 == 0)
{
lean_object* x_18; 
lean_free_object(x_1);
x_18 = l_Std_HashMapImp_expand___at_Lean_Compiler_SpecState_addEntry___spec__8(x_14, x_16);
return x_18;
}
else
{
lean_ctor_set(x_1, 1, x_16);
lean_ctor_set(x_1, 0, x_14);
return x_1;
}
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_7);
x_19 = l_Std_AssocList_replace___at_Lean_Compiler_SpecState_addEntry___spec__11(x_2, x_3, x_11);
x_20 = lean_array_uset(x_6, x_10, x_19);
lean_ctor_set(x_1, 1, x_20);
return x_1;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint64_t x_24; size_t x_25; size_t x_26; lean_object* x_27; uint8_t x_28; 
x_21 = lean_ctor_get(x_1, 0);
x_22 = lean_ctor_get(x_1, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_1);
x_23 = lean_array_get_size(x_22);
x_24 = l_Lean_Name_hash(x_2);
x_25 = (size_t)x_24;
x_26 = lean_usize_modn(x_25, x_23);
x_27 = lean_array_uget(x_22, x_26);
x_28 = l_Std_AssocList_contains___at_Lean_Compiler_SpecState_addEntry___spec__7(x_2, x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_add(x_21, x_29);
lean_dec(x_21);
x_31 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_31, 0, x_2);
lean_ctor_set(x_31, 1, x_3);
lean_ctor_set(x_31, 2, x_27);
x_32 = lean_array_uset(x_22, x_26, x_31);
x_33 = lean_nat_dec_le(x_30, x_23);
lean_dec(x_23);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = l_Std_HashMapImp_expand___at_Lean_Compiler_SpecState_addEntry___spec__8(x_30, x_32);
return x_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_30);
lean_ctor_set(x_35, 1, x_32);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_23);
x_36 = l_Std_AssocList_replace___at_Lean_Compiler_SpecState_addEntry___spec__11(x_2, x_3, x_27);
x_37 = lean_array_uset(x_22, x_26, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_21);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
lean_object* l_Lean_SMap_insert___at_Lean_Compiler_SpecState_addEntry___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_7 = l_Std_PersistentHashMap_insert___at_Lean_Compiler_SpecState_addEntry___spec__2(x_6, x_2, x_3);
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
x_11 = l_Std_PersistentHashMap_insert___at_Lean_Compiler_SpecState_addEntry___spec__2(x_10, x_2, x_3);
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
x_16 = l_Std_HashMapImp_insert___at_Lean_Compiler_SpecState_addEntry___spec__6(x_15, x_2, x_3);
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
x_20 = l_Std_HashMapImp_insert___at_Lean_Compiler_SpecState_addEntry___spec__6(x_18, x_2, x_3);
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
lean_object* l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Compiler_SpecState_addEntry___spec__15(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_11 = l_Lean_Expr_hash(x_9);
x_12 = (size_t)x_11;
x_13 = 1;
x_14 = x_1 - x_13;
x_15 = 5;
x_16 = x_15 * x_14;
x_17 = x_12 >> x_16 % (sizeof(size_t) * 8);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_5, x_18);
lean_dec(x_5);
x_20 = l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_SpecState_addEntry___spec__14(x_6, x_17, x_1, x_9, x_10);
x_4 = lean_box(0);
x_5 = x_19;
x_6 = x_20;
goto _start;
}
}
}
lean_object* l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Compiler_SpecState_addEntry___spec__16(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_18 = lean_expr_eqv(x_3, x_17);
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
lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_SpecState_addEntry___spec__14(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
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
x_21 = lean_expr_eqv(x_4, x_19);
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
x_28 = lean_expr_eqv(x_4, x_26);
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
x_36 = x_2 >> x_9 % (sizeof(size_t) * 8);
x_37 = x_3 + x_8;
x_38 = l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_SpecState_addEntry___spec__14(x_35, x_36, x_37, x_4, x_5);
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
x_41 = x_2 >> x_9 % (sizeof(size_t) * 8);
x_42 = x_3 + x_8;
x_43 = l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_SpecState_addEntry___spec__14(x_40, x_41, x_42, x_4, x_5);
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
x_63 = lean_expr_eqv(x_4, x_60);
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
x_73 = x_2 >> x_50 % (sizeof(size_t) * 8);
x_74 = x_3 + x_49;
x_75 = l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_SpecState_addEntry___spec__14(x_71, x_73, x_74, x_4, x_5);
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
x_84 = l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Compiler_SpecState_addEntry___spec__16(x_1, x_83, x_4, x_5);
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
x_93 = l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Compiler_SpecState_addEntry___spec__15(x_3, x_90, x_91, lean_box(0), x_83, x_92);
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
x_98 = l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Compiler_SpecState_addEntry___spec__16(x_96, x_97, x_4, x_5);
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
x_107 = l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Compiler_SpecState_addEntry___spec__15(x_3, x_104, x_105, lean_box(0), x_97, x_106);
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
lean_object* l_Std_PersistentHashMap_insert___at_Lean_Compiler_SpecState_addEntry___spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint64_t x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_Expr_hash(x_2);
x_8 = (size_t)x_7;
x_9 = 1;
x_10 = l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_SpecState_addEntry___spec__14(x_5, x_8, x_9, x_2, x_3);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_6, x_11);
lean_dec(x_6);
lean_ctor_set(x_1, 1, x_12);
lean_ctor_set(x_1, 0, x_10);
return x_1;
}
else
{
lean_object* x_13; lean_object* x_14; uint64_t x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_1);
x_15 = l_Lean_Expr_hash(x_2);
x_16 = (size_t)x_15;
x_17 = 1;
x_18 = l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_SpecState_addEntry___spec__14(x_13, x_16, x_17, x_2, x_3);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_14, x_19);
lean_dec(x_14);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
uint8_t l_Std_AssocList_contains___at_Lean_Compiler_SpecState_addEntry___spec__18(lean_object* x_1, lean_object* x_2) {
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
x_6 = lean_expr_eqv(x_4, x_1);
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
lean_object* l_Std_AssocList_foldlM___at_Lean_Compiler_SpecState_addEntry___spec__21(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = l_Lean_Expr_hash(x_4);
x_8 = (size_t)x_7;
x_9 = lean_usize_modn(x_8, x_6);
lean_dec(x_6);
x_10 = lean_array_uget(x_1, x_9);
lean_ctor_set(x_2, 2, x_10);
x_11 = lean_array_uset(x_1, x_9, x_2);
x_1 = x_11;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint64_t x_17; size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_ctor_get(x_2, 1);
x_15 = lean_ctor_get(x_2, 2);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_2);
x_16 = lean_array_get_size(x_1);
x_17 = l_Lean_Expr_hash(x_13);
x_18 = (size_t)x_17;
x_19 = lean_usize_modn(x_18, x_16);
lean_dec(x_16);
x_20 = lean_array_uget(x_1, x_19);
x_21 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_21, 0, x_13);
lean_ctor_set(x_21, 1, x_14);
lean_ctor_set(x_21, 2, x_20);
x_22 = lean_array_uset(x_1, x_19, x_21);
x_1 = x_22;
x_2 = x_15;
goto _start;
}
}
}
}
lean_object* l_Std_HashMapImp_moveEntries___at_Lean_Compiler_SpecState_addEntry___spec__20(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_AssocList_foldlM___at_Lean_Compiler_SpecState_addEntry___spec__21(x_3, x_6);
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
lean_object* l_Std_HashMapImp_expand___at_Lean_Compiler_SpecState_addEntry___spec__19(lean_object* x_1, lean_object* x_2) {
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
x_9 = l_Std_HashMapImp_moveEntries___at_Lean_Compiler_SpecState_addEntry___spec__20(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
lean_object* l_Std_AssocList_replace___at_Lean_Compiler_SpecState_addEntry___spec__22(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = lean_expr_eqv(x_6, x_1);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = l_Std_AssocList_replace___at_Lean_Compiler_SpecState_addEntry___spec__22(x_1, x_2, x_8);
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
x_14 = lean_expr_eqv(x_11, x_1);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_Std_AssocList_replace___at_Lean_Compiler_SpecState_addEntry___spec__22(x_1, x_2, x_13);
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
lean_object* l_Std_HashMapImp_insert___at_Lean_Compiler_SpecState_addEntry___spec__17(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; size_t x_9; size_t x_10; lean_object* x_11; uint8_t x_12; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = l_Lean_Expr_hash(x_2);
x_9 = (size_t)x_8;
x_10 = lean_usize_modn(x_9, x_7);
x_11 = lean_array_uget(x_6, x_10);
x_12 = l_Std_AssocList_contains___at_Lean_Compiler_SpecState_addEntry___spec__18(x_2, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_5, x_13);
lean_dec(x_5);
x_15 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_3);
lean_ctor_set(x_15, 2, x_11);
x_16 = lean_array_uset(x_6, x_10, x_15);
x_17 = lean_nat_dec_le(x_14, x_7);
lean_dec(x_7);
if (x_17 == 0)
{
lean_object* x_18; 
lean_free_object(x_1);
x_18 = l_Std_HashMapImp_expand___at_Lean_Compiler_SpecState_addEntry___spec__19(x_14, x_16);
return x_18;
}
else
{
lean_ctor_set(x_1, 1, x_16);
lean_ctor_set(x_1, 0, x_14);
return x_1;
}
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_7);
x_19 = l_Std_AssocList_replace___at_Lean_Compiler_SpecState_addEntry___spec__22(x_2, x_3, x_11);
x_20 = lean_array_uset(x_6, x_10, x_19);
lean_ctor_set(x_1, 1, x_20);
return x_1;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint64_t x_24; size_t x_25; size_t x_26; lean_object* x_27; uint8_t x_28; 
x_21 = lean_ctor_get(x_1, 0);
x_22 = lean_ctor_get(x_1, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_1);
x_23 = lean_array_get_size(x_22);
x_24 = l_Lean_Expr_hash(x_2);
x_25 = (size_t)x_24;
x_26 = lean_usize_modn(x_25, x_23);
x_27 = lean_array_uget(x_22, x_26);
x_28 = l_Std_AssocList_contains___at_Lean_Compiler_SpecState_addEntry___spec__18(x_2, x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_add(x_21, x_29);
lean_dec(x_21);
x_31 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_31, 0, x_2);
lean_ctor_set(x_31, 1, x_3);
lean_ctor_set(x_31, 2, x_27);
x_32 = lean_array_uset(x_22, x_26, x_31);
x_33 = lean_nat_dec_le(x_30, x_23);
lean_dec(x_23);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = l_Std_HashMapImp_expand___at_Lean_Compiler_SpecState_addEntry___spec__19(x_30, x_32);
return x_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_30);
lean_ctor_set(x_35, 1, x_32);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_23);
x_36 = l_Std_AssocList_replace___at_Lean_Compiler_SpecState_addEntry___spec__22(x_2, x_3, x_27);
x_37 = lean_array_uset(x_22, x_26, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_21);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
lean_object* l_Lean_SMap_insert___at_Lean_Compiler_SpecState_addEntry___spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_7 = l_Std_PersistentHashMap_insert___at_Lean_Compiler_SpecState_addEntry___spec__13(x_6, x_2, x_3);
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
x_11 = l_Std_PersistentHashMap_insert___at_Lean_Compiler_SpecState_addEntry___spec__13(x_10, x_2, x_3);
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
x_16 = l_Std_HashMapImp_insert___at_Lean_Compiler_SpecState_addEntry___spec__17(x_15, x_2, x_3);
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
x_20 = l_Std_HashMapImp_insert___at_Lean_Compiler_SpecState_addEntry___spec__17(x_18, x_2, x_3);
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
lean_object* l_Lean_Compiler_SpecState_addEntry(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = l_Lean_SMap_insert___at_Lean_Compiler_SpecState_addEntry___spec__1(x_6, x_3, x_4);
lean_ctor_set(x_1, 0, x_7);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
x_10 = l_Lean_SMap_insert___at_Lean_Compiler_SpecState_addEntry___spec__1(x_8, x_3, x_4);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_dec(x_2);
x_14 = !lean_is_exclusive(x_1);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_1, 1);
x_16 = l_Lean_SMap_insert___at_Lean_Compiler_SpecState_addEntry___spec__12(x_15, x_12, x_13);
lean_ctor_set(x_1, 1, x_16);
return x_1;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_1, 0);
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_1);
x_19 = l_Lean_SMap_insert___at_Lean_Compiler_SpecState_addEntry___spec__12(x_18, x_12, x_13);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
lean_object* l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Compiler_SpecState_addEntry___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; lean_object* x_8; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Compiler_SpecState_addEntry___spec__4(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_SpecState_addEntry___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_SpecState_addEntry___spec__3(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
lean_object* l_Std_AssocList_contains___at_Lean_Compiler_SpecState_addEntry___spec__7___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_AssocList_contains___at_Lean_Compiler_SpecState_addEntry___spec__7(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Compiler_SpecState_addEntry___spec__15___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; lean_object* x_8; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Compiler_SpecState_addEntry___spec__15(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_SpecState_addEntry___spec__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Std_PersistentHashMap_insertAux___at_Lean_Compiler_SpecState_addEntry___spec__14(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
lean_object* l_Std_AssocList_contains___at_Lean_Compiler_SpecState_addEntry___spec__18___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_AssocList_contains___at_Lean_Compiler_SpecState_addEntry___spec__18(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_Compiler_SpecState_switch_match__1___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Compiler_SpecState_switch_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_SpecState_switch_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_SMap_switch___at_Lean_Compiler_SpecState_switch___spec__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
if (x_2 == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = 0;
lean_ctor_set_uint8(x_1, sizeof(void*)*2, x_4);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_7 = 0;
x_8 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_6);
lean_ctor_set_uint8(x_8, sizeof(void*)*2, x_7);
return x_8;
}
}
}
}
lean_object* l_Lean_SMap_switch___at_Lean_Compiler_SpecState_switch___spec__2(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
if (x_2 == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = 0;
lean_ctor_set_uint8(x_1, sizeof(void*)*2, x_4);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_7 = 0;
x_8 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_6);
lean_ctor_set_uint8(x_8, sizeof(void*)*2, x_7);
return x_8;
}
}
}
}
lean_object* l_Lean_Compiler_SpecState_switch(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_Lean_SMap_switch___at_Lean_Compiler_SpecState_switch___spec__1(x_3);
x_6 = l_Lean_SMap_switch___at_Lean_Compiler_SpecState_switch___spec__2(x_4);
lean_ctor_set(x_1, 1, x_6);
lean_ctor_set(x_1, 0, x_5);
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
x_9 = l_Lean_SMap_switch___at_Lean_Compiler_SpecState_switch___spec__1(x_7);
x_10 = l_Lean_SMap_switch___at_Lean_Compiler_SpecState_switch___spec__2(x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_323____spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_2 == x_3;
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Lean_Compiler_SpecState_addEntry(x_4, x_6);
x_8 = 1;
x_9 = x_2 + x_8;
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
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_323____spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_2 == x_3;
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; size_t x_10; size_t x_11; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_array_get_size(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_lt(x_8, x_7);
x_10 = 1;
x_11 = x_2 + x_10;
if (x_9 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
x_2 = x_11;
goto _start;
}
else
{
uint8_t x_13; 
x_13 = lean_nat_dec_le(x_7, x_7);
if (x_13 == 0)
{
lean_dec(x_7);
lean_dec(x_6);
x_2 = x_11;
goto _start;
}
else
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = 0;
x_16 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_17 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_323____spec__2(x_6, x_15, x_16, x_4);
lean_dec(x_6);
x_2 = x_11;
x_4 = x_17;
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
lean_object* l_Lean_mkStateFromImportedEntries___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_323____spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
lean_dec(x_3);
return x_1;
}
else
{
uint8_t x_6; 
x_6 = lean_nat_dec_le(x_3, x_3);
if (x_6 == 0)
{
lean_dec(x_3);
return x_1;
}
else
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = 0;
x_8 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_9 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_323____spec__3(x_2, x_7, x_8, x_1);
return x_9;
}
}
}
}
uint8_t l_Array_anyMUnsafe_any___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_323____spec__6(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
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
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_323____spec__5(lean_object* x_1, lean_object* x_2) {
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
x_18 = l_Array_anyMUnsafe_any___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_323____spec__6(x_1, x_6, x_16, x_17);
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
lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
lean_dec(x_1);
x_22 = 1;
x_23 = l_Lean_Name_toString(x_21, x_22);
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
x_41 = l_Array_anyMUnsafe_any___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_323____spec__6(x_1, x_29, x_39, x_40);
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
lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_44 = lean_ctor_get(x_1, 0);
lean_inc(x_44);
lean_dec(x_1);
x_45 = 1;
x_46 = l_Lean_Name_toString(x_44, x_45);
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
lean_object* l_Lean_registerSimplePersistentEnvExtension___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_323____spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
x_5 = lean_box(0);
x_6 = l_Array_empty___closed__1;
lean_inc(x_4);
x_7 = lean_apply_1(x_4, x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_alloc_closure((void*)(l_EStateM_pure___rarg), 2, 1);
lean_closure_set(x_9, 0, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__1___boxed), 5, 2);
lean_closure_set(x_10, 0, x_4);
lean_closure_set(x_10, 1, x_5);
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__2), 3, 1);
lean_closure_set(x_11, 0, x_1);
x_12 = lean_alloc_closure((void*)(l_Lean_registerSimplePersistentEnvExtension___rarg___lambda__3), 2, 1);
lean_closure_set(x_12, 0, x_1);
x_13 = l_Lean_registerSimplePersistentEnvExtension___rarg___closed__1;
x_14 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_14, 0, x_3);
lean_ctor_set(x_14, 1, x_9);
lean_ctor_set(x_14, 2, x_10);
lean_ctor_set(x_14, 3, x_11);
lean_ctor_set(x_14, 4, x_12);
lean_ctor_set(x_14, 5, x_13);
x_15 = l_Lean_registerPersistentEnvExtensionUnsafe___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_323____spec__5(x_14, x_2);
return x_15;
}
}
lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_323____lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Compiler_instInhabitedSpecState___closed__2;
x_3 = l_Lean_mkStateFromImportedEntries___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_323____spec__1(x_2, x_1);
x_4 = l_Lean_Compiler_SpecState_switch(x_3);
return x_4;
}
}
#define _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_323____closed__1(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_SpecState_addEntry), 2, 0);\
__INIT_VAR__ = x_1; goto l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_323____closed__1_end;\
}\
l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_323____closed__1_end: ((void) 0);}
#define _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_323____closed__2(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_323____lambda__1___boxed), 1, 0);\
__INIT_VAR__ = x_1; goto l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_323____closed__2_end;\
}\
l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_323____closed__2_end: ((void) 0);}
#define _init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_323____closed__3(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; \
x_1 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__4;\
x_2 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_323____closed__1;\
x_3 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_323____closed__2;\
x_4 = l_Lean_initFn____x40_Lean_Environment___hyg_3629____closed__4;\
x_5 = lean_alloc_ctor(0, 4, 0);\
lean_ctor_set(x_5, 0, x_1);\
lean_ctor_set(x_5, 1, x_2);\
lean_ctor_set(x_5, 2, x_3);\
lean_ctor_set(x_5, 3, x_4);\
__INIT_VAR__ = x_5; goto l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_323____closed__3_end;\
}\
l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_323____closed__3_end: ((void) 0);}
lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_323_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_323____closed__3;
x_3 = l_Lean_registerSimplePersistentEnvExtension___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_323____spec__4(x_2, x_1);
return x_3;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_323____spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_323____spec__2(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_323____spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_323____spec__3(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_mkStateFromImportedEntries___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_323____spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkStateFromImportedEntries___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_323____spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_anyMUnsafe_any___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_323____spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_323____spec__6(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
lean_object* l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_323____lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_323____lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Compiler_specExtension___elambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
lean_object* l_Lean_Compiler_specExtension___elambda__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Array_empty___closed__1;
return x_2;
}
}
lean_object* l_Lean_Compiler_specExtension___elambda__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
lean_object* l_Lean_Compiler_specExtension___elambda__4___rarg(lean_object* x_1) {
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
lean_object* l_Lean_Compiler_specExtension___elambda__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Compiler_specExtension___elambda__4___rarg), 1, 0);
return x_3;
}
}
#define _init_l_Lean_Compiler_specExtension___closed__1(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_specExtension___elambda__4___boxed), 2, 0);\
__INIT_VAR__ = x_1; goto l_Lean_Compiler_specExtension___closed__1_end;\
}\
l_Lean_Compiler_specExtension___closed__1_end: ((void) 0);}
#define _init_l_Lean_Compiler_specExtension___closed__2(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_specExtension___elambda__3___boxed), 2, 0);\
__INIT_VAR__ = x_1; goto l_Lean_Compiler_specExtension___closed__2_end;\
}\
l_Lean_Compiler_specExtension___closed__2_end: ((void) 0);}
#define _init_l_Lean_Compiler_specExtension___closed__3(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_specExtension___elambda__2___boxed), 1, 0);\
__INIT_VAR__ = x_1; goto l_Lean_Compiler_specExtension___closed__3_end;\
}\
l_Lean_Compiler_specExtension___closed__3_end: ((void) 0);}
#define _init_l_Lean_Compiler_specExtension___closed__4(__INIT_VAR__) { \
{\
lean_object* x_1; \
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_specExtension___elambda__1___boxed), 1, 0);\
__INIT_VAR__ = x_1; goto l_Lean_Compiler_specExtension___closed__4_end;\
}\
l_Lean_Compiler_specExtension___closed__4_end: ((void) 0);}
#define _init_l_Lean_Compiler_specExtension___closed__5(__INIT_VAR__) { \
{\
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; \
x_1 = l_Lean_EnvExtensionInterfaceUnsafe_instInhabitedExt___closed__2;\
x_2 = lean_box(0);\
x_3 = l_Lean_Compiler_specExtension___closed__1;\
x_4 = l_Lean_Compiler_specExtension___closed__2;\
x_5 = l_Lean_Compiler_specExtension___closed__3;\
x_6 = l_Lean_Compiler_specExtension___closed__4;\
x_7 = lean_alloc_ctor(0, 6, 0);\
lean_ctor_set(x_7, 0, x_1);\
lean_ctor_set(x_7, 1, x_2);\
lean_ctor_set(x_7, 2, x_3);\
lean_ctor_set(x_7, 3, x_4);\
lean_ctor_set(x_7, 4, x_5);\
lean_ctor_set(x_7, 5, x_6);\
__INIT_VAR__ = x_7; goto l_Lean_Compiler_specExtension___closed__5_end;\
}\
l_Lean_Compiler_specExtension___closed__5_end: ((void) 0);}
lean_object* l_Lean_Compiler_specExtension___elambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_specExtension___elambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Compiler_specExtension___elambda__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_specExtension___elambda__2(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Compiler_specExtension___elambda__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_specExtension___elambda__3(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Compiler_specExtension___elambda__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_specExtension___elambda__4(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* lean_add_specialization_info(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
x_5 = l_Lean_Compiler_specExtension;
x_6 = l_Lean_PersistentEnvExtension_addEntry___rarg(x_5, x_1, x_4);
return x_6;
}
}
lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Compiler_getSpecializationInfo___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Compiler_getSpecializationInfo___spec__3(lean_object* x_1, size_t x_2, lean_object* x_3) {
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
x_17 = x_2 >> x_5 % (sizeof(size_t) * 8);
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
x_23 = l_Std_PersistentHashMap_findAtAux___at_Lean_Compiler_getSpecializationInfo___spec__4(x_20, x_21, lean_box(0), x_22, x_3);
lean_dec(x_21);
lean_dec(x_20);
return x_23;
}
}
}
lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Compiler_getSpecializationInfo___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint64_t x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_Name_hash(x_2);
x_5 = (size_t)x_4;
x_6 = l_Std_PersistentHashMap_findAux___at_Lean_Compiler_getSpecializationInfo___spec__3(x_3, x_5, x_2);
return x_6;
}
}
lean_object* l_Std_AssocList_find_x3f___at_Lean_Compiler_getSpecializationInfo___spec__6(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Compiler_getSpecializationInfo___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Name_hash(x_2);
x_6 = (size_t)x_5;
x_7 = lean_usize_modn(x_6, x_4);
lean_dec(x_4);
x_8 = lean_array_uget(x_3, x_7);
x_9 = l_Std_AssocList_find_x3f___at_Lean_Compiler_getSpecializationInfo___spec__6(x_2, x_8);
lean_dec(x_8);
return x_9;
}
}
lean_object* l_Lean_SMap_find_x3f___at_Lean_Compiler_getSpecializationInfo___spec__1(lean_object* x_1, lean_object* x_2) {
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
x_6 = l_Std_PersistentHashMap_find_x3f___at_Lean_Compiler_getSpecializationInfo___spec__2(x_5, x_2);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = l_Std_HashMapImp_find_x3f___at_Lean_Compiler_getSpecializationInfo___spec__5(x_4, x_2);
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
x_12 = l_Std_HashMapImp_find_x3f___at_Lean_Compiler_getSpecializationInfo___spec__5(x_11, x_2);
lean_dec(x_11);
return x_12;
}
}
}
lean_object* lean_get_specialization_info(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = l_Lean_Compiler_specExtension;
x_4 = l_Lean_SimplePersistentEnvExtension_getState___rarg(x_3, x_1);
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = l_Lean_SMap_find_x3f___at_Lean_Compiler_getSpecializationInfo___spec__1(x_5, x_2);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Compiler_getSpecializationInfo___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_PersistentHashMap_findAtAux___at_Lean_Compiler_getSpecializationInfo___spec__4(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Compiler_getSpecializationInfo___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Std_PersistentHashMap_findAux___at_Lean_Compiler_getSpecializationInfo___spec__3(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Compiler_getSpecializationInfo___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_PersistentHashMap_find_x3f___at_Lean_Compiler_getSpecializationInfo___spec__2(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Std_AssocList_find_x3f___at_Lean_Compiler_getSpecializationInfo___spec__6___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_AssocList_find_x3f___at_Lean_Compiler_getSpecializationInfo___spec__6(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Compiler_getSpecializationInfo___spec__5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_HashMapImp_find_x3f___at_Lean_Compiler_getSpecializationInfo___spec__5(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_SMap_find_x3f___at_Lean_Compiler_getSpecializationInfo___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_SMap_find_x3f___at_Lean_Compiler_getSpecializationInfo___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* lean_cache_specialization(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
x_5 = l_Lean_Compiler_specExtension;
x_6 = l_Lean_PersistentEnvExtension_addEntry___rarg(x_5, x_1, x_4);
return x_6;
}
}
lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Compiler_getCachedSpecialization___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_10 = lean_expr_eqv(x_5, x_9);
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
lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Compiler_getCachedSpecialization___spec__3(lean_object* x_1, size_t x_2, lean_object* x_3) {
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
x_13 = lean_expr_eqv(x_3, x_11);
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
x_17 = x_2 >> x_5 % (sizeof(size_t) * 8);
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
x_23 = l_Std_PersistentHashMap_findAtAux___at_Lean_Compiler_getCachedSpecialization___spec__4(x_20, x_21, lean_box(0), x_22, x_3);
lean_dec(x_21);
lean_dec(x_20);
return x_23;
}
}
}
lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Compiler_getCachedSpecialization___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint64_t x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_Expr_hash(x_2);
x_5 = (size_t)x_4;
x_6 = l_Std_PersistentHashMap_findAux___at_Lean_Compiler_getCachedSpecialization___spec__3(x_3, x_5, x_2);
return x_6;
}
}
lean_object* l_Std_AssocList_find_x3f___at_Lean_Compiler_getCachedSpecialization___spec__6(lean_object* x_1, lean_object* x_2) {
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
x_7 = lean_expr_eqv(x_4, x_1);
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
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Compiler_getCachedSpecialization___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Expr_hash(x_2);
x_6 = (size_t)x_5;
x_7 = lean_usize_modn(x_6, x_4);
lean_dec(x_4);
x_8 = lean_array_uget(x_3, x_7);
x_9 = l_Std_AssocList_find_x3f___at_Lean_Compiler_getCachedSpecialization___spec__6(x_2, x_8);
lean_dec(x_8);
return x_9;
}
}
lean_object* l_Lean_SMap_find_x3f___at_Lean_Compiler_getCachedSpecialization___spec__1(lean_object* x_1, lean_object* x_2) {
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
x_6 = l_Std_PersistentHashMap_find_x3f___at_Lean_Compiler_getCachedSpecialization___spec__2(x_5, x_2);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = l_Std_HashMapImp_find_x3f___at_Lean_Compiler_getCachedSpecialization___spec__5(x_4, x_2);
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
x_12 = l_Std_HashMapImp_find_x3f___at_Lean_Compiler_getCachedSpecialization___spec__5(x_11, x_2);
lean_dec(x_11);
return x_12;
}
}
}
lean_object* lean_get_cached_specialization(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = l_Lean_Compiler_specExtension;
x_4 = l_Lean_SimplePersistentEnvExtension_getState___rarg(x_3, x_1);
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = l_Lean_SMap_find_x3f___at_Lean_Compiler_getCachedSpecialization___spec__1(x_5, x_2);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Compiler_getCachedSpecialization___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_PersistentHashMap_findAtAux___at_Lean_Compiler_getCachedSpecialization___spec__4(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Compiler_getCachedSpecialization___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Std_PersistentHashMap_findAux___at_Lean_Compiler_getCachedSpecialization___spec__3(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Compiler_getCachedSpecialization___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_PersistentHashMap_find_x3f___at_Lean_Compiler_getCachedSpecialization___spec__2(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Std_AssocList_find_x3f___at_Lean_Compiler_getCachedSpecialization___spec__6___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_AssocList_find_x3f___at_Lean_Compiler_getCachedSpecialization___spec__6(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Std_HashMapImp_find_x3f___at_Lean_Compiler_getCachedSpecialization___spec__5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_HashMapImp_find_x3f___at_Lean_Compiler_getCachedSpecialization___spec__5(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_SMap_find_x3f___at_Lean_Compiler_getCachedSpecialization___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_SMap_find_x3f___at_Lean_Compiler_getCachedSpecialization___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Attributes(lean_object*);
lean_object* initialize_Lean_Compiler_Util(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Compiler_Specialize(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Attributes(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_Util(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
_init_l_Lean_Compiler_instInhabitedSpecializeAttributeKind(l_Lean_Compiler_instInhabitedSpecializeAttributeKind);
_init_l_Lean_Compiler_instBEqSpecializeAttributeKind___closed__1(l_Lean_Compiler_instBEqSpecializeAttributeKind___closed__1);
lean_mark_persistent(l_Lean_Compiler_instBEqSpecializeAttributeKind___closed__1);
_init_l_Lean_Compiler_instBEqSpecializeAttributeKind(l_Lean_Compiler_instBEqSpecializeAttributeKind);
lean_mark_persistent(l_Lean_Compiler_instBEqSpecializeAttributeKind);
_init_l_Array_qpartition_loop___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__4___closed__1(l_Array_qpartition_loop___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__4___closed__1);
lean_mark_persistent(l_Array_qpartition_loop___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__4___closed__1);
_init_l_Lean_registerEnumAttributes___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__1___closed__1(l_Lean_registerEnumAttributes___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__1___closed__1);
lean_mark_persistent(l_Lean_registerEnumAttributes___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__1___closed__1);
_init_l_Lean_registerEnumAttributes___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__1___closed__2(l_Lean_registerEnumAttributes___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__1___closed__2);
lean_mark_persistent(l_Lean_registerEnumAttributes___at_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____spec__1___closed__2);
_init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__1(l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__1);
lean_mark_persistent(l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__1);
_init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__2(l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__2);
lean_mark_persistent(l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__2);
_init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__3(l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__3);
lean_mark_persistent(l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__3);
_init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__4(l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__4);
lean_mark_persistent(l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__4);
_init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__5(l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__5);
lean_mark_persistent(l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__5);
_init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__6(l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__6);
lean_mark_persistent(l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__6);
_init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__7(l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__7);
lean_mark_persistent(l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__7);
_init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__8(l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__8);
lean_mark_persistent(l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__8);
_init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__9(l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__9);
lean_mark_persistent(l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__9);
_init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__10(l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__10);
lean_mark_persistent(l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__10);
_init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__11(l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__11);
lean_mark_persistent(l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__11);
_init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__12(l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__12);
lean_mark_persistent(l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__12);
_init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__13(l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__13);
lean_mark_persistent(l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__13);
_init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__14(l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__14);
lean_mark_persistent(l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__14);
_init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__15(l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__15);
lean_mark_persistent(l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49____closed__15);
res = l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_49_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Compiler_specializeAttrs = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Compiler_specializeAttrs);
lean_dec_ref(res);
_init_l_Lean_Compiler_instInhabitedSpecArgKind(l_Lean_Compiler_instInhabitedSpecArgKind);
_init_l_Lean_Compiler_instInhabitedSpecInfo___closed__1(l_Lean_Compiler_instInhabitedSpecInfo___closed__1);
lean_mark_persistent(l_Lean_Compiler_instInhabitedSpecInfo___closed__1);
_init_l_Lean_Compiler_instInhabitedSpecInfo(l_Lean_Compiler_instInhabitedSpecInfo);
lean_mark_persistent(l_Lean_Compiler_instInhabitedSpecInfo);
_init_l_Lean_Compiler_SpecState_specInfo___default___closed__1(l_Lean_Compiler_SpecState_specInfo___default___closed__1);
lean_mark_persistent(l_Lean_Compiler_SpecState_specInfo___default___closed__1);
_init_l_Lean_Compiler_SpecState_specInfo___default___closed__2(l_Lean_Compiler_SpecState_specInfo___default___closed__2);
lean_mark_persistent(l_Lean_Compiler_SpecState_specInfo___default___closed__2);
_init_l_Lean_Compiler_SpecState_specInfo___default(l_Lean_Compiler_SpecState_specInfo___default);
lean_mark_persistent(l_Lean_Compiler_SpecState_specInfo___default);
_init_l_Lean_Compiler_SpecState_cache___default___closed__1(l_Lean_Compiler_SpecState_cache___default___closed__1);
lean_mark_persistent(l_Lean_Compiler_SpecState_cache___default___closed__1);
_init_l_Lean_Compiler_SpecState_cache___default___closed__2(l_Lean_Compiler_SpecState_cache___default___closed__2);
lean_mark_persistent(l_Lean_Compiler_SpecState_cache___default___closed__2);
_init_l_Lean_Compiler_SpecState_cache___default___closed__3(l_Lean_Compiler_SpecState_cache___default___closed__3);
lean_mark_persistent(l_Lean_Compiler_SpecState_cache___default___closed__3);
_init_l_Lean_Compiler_SpecState_cache___default(l_Lean_Compiler_SpecState_cache___default);
lean_mark_persistent(l_Lean_Compiler_SpecState_cache___default);
_init_l_Lean_Compiler_instInhabitedSpecState___closed__1(l_Lean_Compiler_instInhabitedSpecState___closed__1);
lean_mark_persistent(l_Lean_Compiler_instInhabitedSpecState___closed__1);
_init_l_Lean_Compiler_instInhabitedSpecState___closed__2(l_Lean_Compiler_instInhabitedSpecState___closed__2);
lean_mark_persistent(l_Lean_Compiler_instInhabitedSpecState___closed__2);
_init_l_Lean_Compiler_instInhabitedSpecState(l_Lean_Compiler_instInhabitedSpecState);
lean_mark_persistent(l_Lean_Compiler_instInhabitedSpecState);
_init_l_Lean_Compiler_instInhabitedSpecEntry___closed__1(l_Lean_Compiler_instInhabitedSpecEntry___closed__1);
lean_mark_persistent(l_Lean_Compiler_instInhabitedSpecEntry___closed__1);
_init_l_Lean_Compiler_instInhabitedSpecEntry(l_Lean_Compiler_instInhabitedSpecEntry);
lean_mark_persistent(l_Lean_Compiler_instInhabitedSpecEntry);
_init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_323____closed__1(l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_323____closed__1);
lean_mark_persistent(l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_323____closed__1);
_init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_323____closed__2(l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_323____closed__2);
lean_mark_persistent(l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_323____closed__2);
_init_l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_323____closed__3(l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_323____closed__3);
lean_mark_persistent(l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_323____closed__3);
_init_l_Lean_Compiler_specExtension___closed__1(l_Lean_Compiler_specExtension___closed__1);
lean_mark_persistent(l_Lean_Compiler_specExtension___closed__1);
_init_l_Lean_Compiler_specExtension___closed__2(l_Lean_Compiler_specExtension___closed__2);
lean_mark_persistent(l_Lean_Compiler_specExtension___closed__2);
_init_l_Lean_Compiler_specExtension___closed__3(l_Lean_Compiler_specExtension___closed__3);
lean_mark_persistent(l_Lean_Compiler_specExtension___closed__3);
_init_l_Lean_Compiler_specExtension___closed__4(l_Lean_Compiler_specExtension___closed__4);
lean_mark_persistent(l_Lean_Compiler_specExtension___closed__4);
_init_l_Lean_Compiler_specExtension___closed__5(l_Lean_Compiler_specExtension___closed__5);
lean_mark_persistent(l_Lean_Compiler_specExtension___closed__5);
res = l_Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_323_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Compiler_specExtension = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Compiler_specExtension);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
