// Lean compiler output
// Module: Lean.ResolveName
// Imports: Lean.Data.OpenDecl Lean.Hygiene Lean.Modifiers Lean.Exception Lean.Namespace
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
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___at_Lean_resolveGlobalConst___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveLocalName_loop___at_Lean_resolveLocalName___spec__11___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_unresolveNameGlobal___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getRevAliases___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_resolveLocalName___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveLocalName(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_ResolveName_resolveGlobalName_loop___spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_ensureNoOverload___spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveLocalName_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_ResolveName___hyg_392____lambda__1___closed__5;
uint8_t l_Lean_MacroScopesView_isSuffixOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___at_Lean_unresolveNameGlobalAvoidingLocals___spec__1___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveLocalName_go___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at_Lean_initFn____x40_Lean_ResolveName___hyg_392____spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at_Lean_resolveLocalName___spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_unresolveNameGlobalAvoidingLocals___spec__2___rarg___lambda__1(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___rarg___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_addAliasEntry___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_private_to_user_name(lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveLocalName_go___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveLocalName_loop___rarg___lambda__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__4;
static lean_object* l_Lean_initFn____x40_Lean_ResolveName___hyg_392____lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_getRevAliases___spec__5___rarg(lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_List_foldl___at_Lean_ensureNoOverload___spec__3___closed__1;
static lean_object* l_Lean_initFn____x40_Lean_ResolveName___hyg_392____closed__2;
uint8_t lean_usize_dec_le(size_t, size_t);
static lean_object* l_List_toString___at_Lean_ensureNoOverload___spec__2___closed__3;
lean_object* l_Lean_Syntax_formatStxAux(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_resolveNamespaceCore___rarg___lambda__3___closed__1;
static lean_object* l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__1;
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_unresolveNameGlobalAvoidingLocals___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___rarg___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_resolveLocalName___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_ensureNoOverload___spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ensureReservedNameAvailable___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_unresolveNameGlobal_unresolveNameCore___spec__1___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
size_t lean_usize_mul(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverloadCore___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_registerReservedNamePredicate___lambda__1___closed__1;
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_ensureNonAmbiguous___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_unresolveNameGlobal_unresolveNameCore___spec__1___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_unresolveNameGlobal_unresolveNameCore___spec__1___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_getRevAliases___spec__5(lean_object*);
static lean_object* l_Lean_ensureNoOverload___rarg___closed__3;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at_Lean_resolveLocalName___spec__3(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at_Lean_resolveLocalName___spec__6___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_getRevAliases___spec__2(lean_object*);
lean_object* l_Option_isNone___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveLocalName_loop___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_ensureNonAmbiguous___rarg___closed__2;
LEAN_EXPORT lean_object* l_Lean_resolveLocalName_go(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_unresolveNameGlobalAvoidingLocals___spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_addAliasEntry___spec__12(lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_unresolveNameCore___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_resolveLocalName___spec__4(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___rarg___lambda__5(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_unresolveNameCore___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_elem___at_Lean_addAliasEntry___spec__16___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveUsingNamespace(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___at_Lean_unresolveNameGlobalAvoidingLocals___spec__1___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
static lean_object* l_List_filterTR_loop___at_Lean_getAliases___spec__1___closed__1;
lean_object* l_Nat_nextPowerOfTwo_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_Lean_addAliasEntry___spec__7(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_resolveNamespace___rarg___closed__2;
LEAN_EXPORT lean_object* l_Lean_resolveLocalName_loop___at_Lean_resolveLocalName___spec__11___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveNamespace___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_filterFieldList(lean_object*);
static lean_object* l_Lean_addAlias___closed__1;
static lean_object* l_Lean_initFn____x40_Lean_ResolveName___hyg_392____closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at_Lean_resolveLocalName___spec__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getAliasState(lean_object*);
static lean_object* l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__2;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_addAliasEntry___spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ensureNoOverload___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___rarg___lambda__5(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
static lean_object* l_List_toString___at_Lean_ensureNoOverload___spec__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_addAliasEntry___spec__8(lean_object*, size_t, size_t, lean_object*, lean_object*);
static lean_object* l_Lean_ensureNonAmbiguous___rarg___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_initFn____x40_Lean_ResolveName___hyg_392____spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Lean_resolveUniqueNamespace___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ResolveName_resolveGlobalName_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_unresolveNameGlobalAvoidingLocals___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwReservedNameNotAvailable___rarg___closed__2;
static lean_object* l_Lean_unresolveNameGlobal___rarg___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_unresolveNameGlobal_unresolveNameCore___spec__1___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at_Lean_addAliasEntry___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___rarg___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_initializing(lean_object*);
LEAN_EXPORT uint8_t l_Lean_isReservedName(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at_Lean_preprocessSyntaxAndResolve___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_unresolveNameGlobal___spec__1___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___at_Lean_unresolveNameGlobalAvoidingLocals___spec__1___rarg___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_unresolveNameGlobal___spec__1(lean_object*);
lean_object* l_List_appendTR___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_ResolveName___hyg_392____closed__3;
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___at_Lean_unresolveNameGlobalAvoidingLocals___spec__1(lean_object*);
uint8_t l_Lean_TagDeclarationExtension_isTagged(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_addAliasEntry___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
static size_t l_Lean_PersistentHashMap_findAux___at_Lean_addAliasEntry___spec__3___closed__1;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_filterFieldList___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___rarg___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwReservedNameNotAvailable(lean_object*);
static lean_object* l_Lean_registerReservedNamePredicate___closed__2;
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_resolveLocalName___spec__10(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_unresolveNameGlobal_unresolveNameCore___rarg___lambda__2___closed__1;
LEAN_EXPORT uint8_t l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___rarg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT uint8_t l_List_elem___at_Lean_addAliasEntry___spec__16(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_unresolveNameGlobal_unresolveNameCore___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_resolveNamespaceCore___rarg___lambda__2(lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveLocalName_loop___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ResolveName_resolveNamespace(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___rarg___lambda__4(lean_object*, lean_object*, lean_object*);
static lean_object* l_List_toString___at_Lean_ensureNoOverload___spec__2___closed__1;
static lean_object* l_Lean_ensureNoOverload___rarg___closed__2;
lean_object* l_List_toArray___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveUniqueNamespace___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_resolveLocalName___spec__5(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_getRevAliases___spec__6(lean_object*);
LEAN_EXPORT lean_object* l_List_eraseDups___at_Lean_ResolveName_resolveGlobalName_loop___spec__1(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_ResolveName___hyg_269_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst(lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___rarg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_ResolveName_resolveGlobalName_loop___spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getRevAliases(lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_ResolveName___hyg_392____lambda__1___closed__2;
lean_object* l_Lean_Name_getPrefix(lean_object*);
static lean_object* l_Lean_throwReservedNameNotAvailable___rarg___closed__5;
LEAN_EXPORT lean_object* l_panic___at_Lean_ensureNonAmbiguous___spec__1___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lean_addAliasEntry___spec__13(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_isReservedName___spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_getRevAliases___spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_addAliasEntry___spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ResolveName_resolveNamespaceUsingOpenDecls(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_ResolveName___hyg_392____lambda__1___closed__3;
lean_object* l_Lean_Name_replacePrefix(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_foldlMAux___at_Lean_MetavarContext_getExprAssignmentDomain___spec__2___rarg(lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveNamespace___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveNamespace(lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_RBNode_find___at_Lean_instantiateLCtxMVars___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_getRevAliases___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_registerReservedNamePredicate___closed__1;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_ResolveName___hyg_269____lambda__1(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_ResolveName___hyg_392____lambda__1___closed__4;
LEAN_EXPORT lean_object* l_List_filterTR_loop___at_Lean_getAliases___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_addAliasEntry___spec__8___closed__1;
LEAN_EXPORT lean_object* l_Lean_ensureNonAmbiguous(lean_object*);
LEAN_EXPORT lean_object* l_List_toString___at_Lean_ensureNoOverload___spec__2___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveUniqueNamespace(lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwUnknownConstant___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_resolveLocalName___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___at_Lean_unresolveNameGlobalAvoidingLocals___spec__1___rarg___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_unresolveNameCore___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveLocalName_loop___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
lean_object* l_Lean_extractMacroScopes(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_ResolveName___hyg_392____lambda__1___closed__6;
lean_object* l_Lean_Name_componentsRev(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at_Lean_resolveNamespace___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
extern lean_object* l_Lean_rootNamespace;
LEAN_EXPORT lean_object* l_Lean_ResolveName_resolveNamespaceUsingScope_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reservedNamePredicatesExt;
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at_Lean_getRevAliases___spec__1___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_ResolveName___hyg_392____lambda__1___boxed(lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_ResolveName___hyg_269____closed__1;
lean_object* l_Lean_registerSimplePersistentEnvExtension___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ensureReservedNameAvailable___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_resolveLocalName___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_initFn____x40_Lean_ResolveName___hyg_392____spec__3(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_addAliasEntry___spec__9(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_isAuxDecl(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveQualifiedName(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerReservedNamePredicate___lambda__1(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_Format_defWidth;
static lean_object* l_Lean_resolveUniqueNamespace___rarg___lambda__1___closed__1;
lean_object* l_Lean_MacroScopesView_review(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_addAliasEntry___spec__10(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_getRevAliases___spec__4___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerReservedNamePredicate(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_add_alias(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___at_Lean_unresolveNameGlobalAvoidingLocals___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerEnvExtension___rarg(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_unresolveNameCore(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at_Lean_initFn____x40_Lean_ResolveName___hyg_392____spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveLocalName_loop___at_Lean_resolveLocalName___spec__11___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_Lean_addAliasEntry___spec__11___boxed(lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverload(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
static size_t l_Lean_PersistentHashMap_findAux___at_Lean_addAliasEntry___spec__3___closed__2;
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
uint8_t l_Lean_Environment_isNamespace(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerReservedNamePredicate___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getAliases___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___at_Lean_unresolveNameGlobalAvoidingLocals___spec__1___rarg___lambda__4(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_unresolveNameGlobal___spec__1___rarg___lambda__3(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveNamespace___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at_Lean_addAliasEntry___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadResolveNameOfMonadLift(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___rarg___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_Lean_addAliasEntry___spec__15(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_resolveNamespaceCore___rarg___lambda__3___closed__2;
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_resolveLocalName___spec__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverloadCore(lean_object*);
lean_object* l_Lean_throwErrorAt___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_resolveNamespace___rarg___closed__3;
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reservedNamePredicatesRef;
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_resolveLocalName___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at_Lean_addAliasEntry___spec__6(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_appendCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_getRevAliases___spec__6___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_ResolveName_resolveGlobalName_loop___spec__3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwReservedNameNotAvailable___rarg___closed__3;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_unresolveNameGlobal___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isAtomic(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_getRevAliases___spec__3___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isReservedName___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___at_Lean_resolveGlobalConst___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_ResolveName_resolveGlobalName_loop___spec__7(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_resolveUniqueNamespace___rarg___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_getRevAliases___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_getRevAliases___spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_ResolveName___hyg_126_(lean_object*);
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_resolveLocalName___spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_unresolveNameGlobalAvoidingLocals___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_unresolveNameGlobalAvoidingLocals___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_ResolveName___hyg_392____lambda__1(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_unresolveNameGlobalAvoidingLocals___spec__2___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_isReservedName___closed__1;
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_ResolveName___hyg_126____closed__1;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_unresolveNameGlobal_unresolveNameCore___spec__1___rarg___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveLocalName_loop___at_Lean_resolveLocalName___spec__11(lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_isReservedName___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_unresolveNameGlobal___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at_Lean_getRevAliases___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_ResolveName___hyg_392____closed__5;
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_resolveLocalName___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveOpenDecls(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Name_hash___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverload___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_addAliasEntry___spec__14(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_filterFieldList___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addAliasEntry(lean_object*, lean_object*);
static lean_object* l_Lean_resolveNamespaceCore___rarg___lambda__3___closed__3;
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveLocalName_loop___at_Lean_resolveLocalName___spec__11___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ensureReservedNameAvailable(lean_object*);
static lean_object* l_Lean_getAliasState___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_addAliasEntry___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_resolveLocalName___spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___rarg___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___rarg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve(lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveLocalName_loop(lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___rarg___lambda__2___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_getRevAliases___spec__2___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ensureNoOverload(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_isReservedName___closed__2;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_unresolveNameGlobal_unresolveNameCore___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_addAliasEntry___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_addAliasEntry___spec__3(lean_object*, size_t, lean_object*);
extern lean_object* l_Lean_protectedExt;
static lean_object* l_Lean_initFn____x40_Lean_ResolveName___hyg_392____closed__6;
LEAN_EXPORT lean_object* l_List_toString___at_Lean_ensureNoOverload___spec__2(lean_object*);
lean_object* l_List_reverse___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___at_Lean_unresolveNameGlobalAvoidingLocals___spec__1___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwReservedNameNotAvailable___rarg___closed__6;
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwReservedNameNotAvailable___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_unresolveNameGlobal___spec__1___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_unresolveNameGlobal___spec__1___rarg___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__3;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_getRevAliases___spec__5___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_ensureNonAmbiguous___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at_Lean_resolveLocalName___spec__8___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedName;
LEAN_EXPORT lean_object* l_panic___at_Lean_ensureNonAmbiguous___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveUniqueNamespace___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_ensureNoOverload___rarg___closed__1;
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_addAliasEntry___spec__3___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_getRevAliases___spec__4___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_instInhabited___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_addAliasEntry___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___rarg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_ResolveName___hyg_392_(lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
LEAN_EXPORT lean_object* l_List_eraseDups_loop___at_Lean_ResolveName_resolveGlobalName_loop___spec__2(lean_object*, lean_object*);
static lean_object* l_Lean_resolveNamespace___rarg___closed__1;
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_ensureNoOverload___spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_filterFieldList___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveExact(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___at_Lean_unresolveNameGlobalAvoidingLocals___spec__1___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___rarg___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_unresolveNameGlobalAvoidingLocals___rarg___lambda__1___closed__1;
extern lean_object* l_Lean_Name_instBEq;
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
static lean_object* l_Lean_throwReservedNameNotAvailable___rarg___closed__4;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveLocalName_loop___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_panic___at_Lean_ResolveName_resolveNamespaceUsingScope_x3f___spec__1(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_expr_dbg_to_string(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_unresolveNameGlobal_unresolveNameCore___spec__1___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___rarg(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_ResolveName___hyg_392____closed__7;
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_unresolveNameGlobal_unresolveNameCore___spec__1___rarg___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_unresolveNameGlobal___spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___at_Lean_unresolveNameGlobalAvoidingLocals___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_unresolveNameCore___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_addAliasEntry___spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at_Lean_getRevAliases___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_filterFieldList___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at_Lean_resolveLocalName___spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwReservedNameNotAvailable___rarg___closed__1;
static lean_object* l_Lean_initFn____x40_Lean_ResolveName___hyg_392____closed__4;
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_Lean_addAliasEntry___spec__11(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_ensureNoOverload___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_getRevAliases___spec__6___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at_Lean_filterFieldList___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___at_Lean_unresolveNameGlobalAvoidingLocals___spec__1___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_initFn____x40_Lean_ResolveName___hyg_392____spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at_Lean_resolveLocalName___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at_Lean_resolveLocalName___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_unresolveNameGlobal___spec__1___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveLocalName_loop___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_toString___at_Lean_Environment_AddConstAsyncResult_commitConst___spec__1(lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at_Lean_initFn____x40_Lean_ResolveName___hyg_392____spec__4(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_ResolveName_resolveGlobalName_loop___spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_aliasExtension;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_initFn____x40_Lean_ResolveName___hyg_392____spec__2(lean_object*, size_t, size_t, lean_object*);
extern lean_object* l_Lean_instHashableName;
LEAN_EXPORT lean_object* l_Lean_ResolveName_resolveGlobalName_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getAliases(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_instMonadResolveNameOfMonadLift___rarg(lean_object*, lean_object*);
static lean_object* _init_l_Lean_throwReservedNameNotAvailable___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed to declare `", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_throwReservedNameNotAvailable___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwReservedNameNotAvailable___rarg___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwReservedNameNotAvailable___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("` because `", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_throwReservedNameNotAvailable___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwReservedNameNotAvailable___rarg___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwReservedNameNotAvailable___rarg___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("` has already been declared", 27, 27);
return x_1;
}
}
static lean_object* _init_l_Lean_throwReservedNameNotAvailable___rarg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwReservedNameNotAvailable___rarg___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwReservedNameNotAvailable___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_5 = l_Lean_MessageData_ofName(x_3);
x_6 = l_Lean_throwReservedNameNotAvailable___rarg___closed__2;
x_7 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
x_8 = l_Lean_throwReservedNameNotAvailable___rarg___closed__4;
x_9 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = 1;
x_11 = l_Lean_MessageData_ofConstName(x_4, x_10);
x_12 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Lean_throwReservedNameNotAvailable___rarg___closed__6;
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_throwError___rarg(x_1, x_2, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_throwReservedNameNotAvailable(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwReservedNameNotAvailable___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureReservedNameAvailable___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
lean_inc(x_1);
x_6 = l_Lean_Environment_contains(x_5, x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_box(0);
x_10 = lean_apply_2(x_8, lean_box(0), x_9);
return x_10;
}
else
{
lean_object* x_11; 
x_11 = l_Lean_throwReservedNameNotAvailable___rarg(x_2, x_3, x_4, x_1);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureReservedNameAvailable___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_inc(x_4);
x_6 = l_Lean_Name_str___override(x_4, x_5);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_alloc_closure((void*)(l_Lean_ensureReservedNameAvailable___rarg___lambda__1), 5, 4);
lean_closure_set(x_9, 0, x_6);
lean_closure_set(x_9, 1, x_1);
lean_closure_set(x_9, 2, x_3);
lean_closure_set(x_9, 3, x_4);
x_10 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureReservedNameAvailable(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_ensureReservedNameAvailable___rarg), 5, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_ResolveName___hyg_126____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_ResolveName___hyg_126_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l_Lean_initFn____x40_Lean_ResolveName___hyg_126____closed__1;
x_3 = lean_st_mk_ref(x_2, x_1);
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
static lean_object* _init_l_Lean_registerReservedNamePredicate___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_reservedNamePredicatesRef;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_registerReservedNamePredicate___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_4 = l_Lean_registerReservedNamePredicate___lambda__1___closed__1;
x_5 = lean_st_ref_take(x_4, x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_array_push(x_6, x_1);
x_9 = lean_st_ref_set(x_4, x_8, x_7);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
return x_9;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
static lean_object* _init_l_Lean_registerReservedNamePredicate___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed to register reserved name suffix predicate, this operation can only be performed during initialization", 109, 109);
return x_1;
}
}
static lean_object* _init_l_Lean_registerReservedNamePredicate___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_registerReservedNamePredicate___closed__1;
x_2 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_registerReservedNamePredicate(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_initializing(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_unbox(x_4);
lean_dec(x_4);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_1);
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_3, 0);
lean_dec(x_7);
x_8 = l_Lean_registerReservedNamePredicate___closed__2;
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_8);
return x_3;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_dec(x_3);
x_10 = l_Lean_registerReservedNamePredicate___closed__2;
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_box(0);
x_14 = l_Lean_registerReservedNamePredicate___lambda__1(x_1, x_13, x_12);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerReservedNamePredicate___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_registerReservedNamePredicate___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_ResolveName___hyg_269____lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l_Lean_registerReservedNamePredicate___lambda__1___closed__1;
x_3 = lean_st_ref_get(x_2, x_1);
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
static lean_object* _init_l_Lean_initFn____x40_Lean_ResolveName___hyg_269____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_initFn____x40_Lean_ResolveName___hyg_269____lambda__1), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_ResolveName___hyg_269_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_2 = lean_box(0);
x_3 = l_Lean_initFn____x40_Lean_ResolveName___hyg_269____closed__1;
x_4 = 2;
x_5 = l_Lean_registerEnvExtension___rarg(x_3, x_2, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_isReservedName___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_array_uget(x_3, x_4);
lean_inc(x_2);
lean_inc(x_1);
x_8 = lean_apply_2(x_7, x_1, x_2);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
if (x_9 == 0)
{
size_t x_10; size_t x_11; 
x_10 = 1;
x_11 = lean_usize_add(x_4, x_10);
x_4 = x_11;
goto _start;
}
else
{
uint8_t x_13; 
lean_dec(x_2);
lean_dec(x_1);
x_13 = 1;
return x_13;
}
}
else
{
uint8_t x_14; 
lean_dec(x_2);
lean_dec(x_1);
x_14 = 0;
return x_14;
}
}
}
static lean_object* _init_l_Lean_isReservedName___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_isReservedName___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_reservedNamePredicatesExt;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_isReservedName(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_3 = l_Lean_reservedNamePredicatesExt;
x_4 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_5 = l_Lean_isReservedName___closed__1;
x_6 = l_Lean_isReservedName___closed__2;
lean_inc(x_1);
x_7 = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___rarg(x_5, x_6, x_1, x_4);
x_8 = lean_array_get_size(x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_lt(x_9, x_8);
if (x_10 == 0)
{
uint8_t x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_11 = 0;
return x_11;
}
else
{
size_t x_12; size_t x_13; uint8_t x_14; 
x_12 = 0;
x_13 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_14 = l_Array_anyMUnsafe_any___at_Lean_isReservedName___spec__1(x_1, x_2, x_7, x_12, x_13);
lean_dec(x_7);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_isReservedName___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l_Array_anyMUnsafe_any___at_Lean_isReservedName___spec__1(x_1, x_2, x_3, x_6, x_7);
lean_dec(x_3);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_isReservedName___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_isReservedName(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_addAliasEntry___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
static size_t _init_l_Lean_PersistentHashMap_findAux___at_Lean_addAliasEntry___spec__3___closed__1() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = 5;
x_3 = lean_usize_shift_left(x_1, x_2);
return x_3;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at_Lean_addAliasEntry___spec__3___closed__2() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = l_Lean_PersistentHashMap_findAux___at_Lean_addAliasEntry___spec__3___closed__1;
x_3 = lean_usize_sub(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_addAliasEntry___spec__3(lean_object* x_1, size_t x_2, lean_object* x_3) {
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
x_7 = l_Lean_PersistentHashMap_findAux___at_Lean_addAliasEntry___spec__3___closed__2;
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
x_14 = lean_name_eq(x_3, x_12);
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
x_22 = l_Lean_PersistentHashMap_findAux___at_Lean_addAliasEntry___spec__3___closed__2;
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
x_29 = lean_name_eq(x_3, x_27);
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
x_39 = l_Lean_PersistentHashMap_findAtAux___at_Lean_addAliasEntry___spec__4(x_36, x_37, lean_box(0), x_38, x_3);
lean_dec(x_37);
lean_dec(x_36);
return x_39;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_addAliasEntry___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; size_t x_4; lean_object* x_5; 
x_3 = l_Lean_Name_hash___override(x_2);
x_4 = lean_uint64_to_usize(x_3);
x_5 = l_Lean_PersistentHashMap_findAux___at_Lean_addAliasEntry___spec__3(x_1, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_addAliasEntry___spec__5(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at_Lean_addAliasEntry___spec__1(lean_object* x_1, lean_object* x_2) {
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
x_6 = l_Lean_PersistentHashMap_find_x3f___at_Lean_addAliasEntry___spec__2(x_5, x_2);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; 
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
x_8 = lean_array_get_size(x_7);
x_9 = l_Lean_Name_hash___override(x_2);
x_10 = 32;
x_11 = lean_uint64_shift_right(x_9, x_10);
x_12 = lean_uint64_xor(x_9, x_11);
x_13 = 16;
x_14 = lean_uint64_shift_right(x_12, x_13);
x_15 = lean_uint64_xor(x_12, x_14);
x_16 = lean_uint64_to_usize(x_15);
x_17 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_18 = 1;
x_19 = lean_usize_sub(x_17, x_18);
x_20 = lean_usize_land(x_16, x_19);
x_21 = lean_array_uget(x_7, x_20);
lean_dec(x_7);
x_22 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_addAliasEntry___spec__5(x_2, x_21);
lean_dec(x_21);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_4);
x_23 = !lean_is_exclusive(x_6);
if (x_23 == 0)
{
return x_6;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_6, 0);
lean_inc(x_24);
lean_dec(x_6);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; size_t x_36; size_t x_37; size_t x_38; size_t x_39; size_t x_40; lean_object* x_41; lean_object* x_42; 
x_26 = lean_ctor_get(x_1, 0);
lean_inc(x_26);
lean_dec(x_1);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_array_get_size(x_27);
x_29 = l_Lean_Name_hash___override(x_2);
x_30 = 32;
x_31 = lean_uint64_shift_right(x_29, x_30);
x_32 = lean_uint64_xor(x_29, x_31);
x_33 = 16;
x_34 = lean_uint64_shift_right(x_32, x_33);
x_35 = lean_uint64_xor(x_32, x_34);
x_36 = lean_uint64_to_usize(x_35);
x_37 = lean_usize_of_nat(x_28);
lean_dec(x_28);
x_38 = 1;
x_39 = lean_usize_sub(x_37, x_38);
x_40 = lean_usize_land(x_36, x_39);
x_41 = lean_array_uget(x_27, x_40);
lean_dec(x_27);
x_42 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_addAliasEntry___spec__5(x_2, x_41);
lean_dec(x_41);
return x_42;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_addAliasEntry___spec__9(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_11 = l_Lean_Name_hash___override(x_9);
x_12 = lean_uint64_to_usize(x_11);
x_13 = 1;
x_14 = lean_usize_sub(x_1, x_13);
x_15 = 5;
x_16 = lean_usize_mul(x_15, x_14);
x_17 = lean_usize_shift_right(x_12, x_16);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_5, x_18);
lean_dec(x_5);
x_20 = l_Lean_PersistentHashMap_insertAux___at_Lean_addAliasEntry___spec__8(x_6, x_17, x_1, x_9, x_10);
x_4 = lean_box(0);
x_5 = x_19;
x_6 = x_20;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_addAliasEntry___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at_Lean_addAliasEntry___spec__8___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_addAliasEntry___spec__8(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
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
x_10 = l_Lean_PersistentHashMap_findAux___at_Lean_addAliasEntry___spec__3___closed__2;
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
x_21 = lean_name_eq(x_4, x_19);
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
x_28 = lean_name_eq(x_4, x_26);
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
x_38 = l_Lean_PersistentHashMap_insertAux___at_Lean_addAliasEntry___spec__8(x_35, x_36, x_37, x_4, x_5);
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
x_43 = l_Lean_PersistentHashMap_insertAux___at_Lean_addAliasEntry___spec__8(x_40, x_41, x_42, x_4, x_5);
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
x_51 = l_Lean_PersistentHashMap_findAux___at_Lean_addAliasEntry___spec__3___closed__2;
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
x_63 = lean_name_eq(x_4, x_60);
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
x_75 = l_Lean_PersistentHashMap_insertAux___at_Lean_addAliasEntry___spec__8(x_71, x_73, x_74, x_4, x_5);
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
x_84 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_addAliasEntry___spec__10(x_1, x_83, x_4, x_5);
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
x_92 = l_Lean_PersistentHashMap_insertAux___at_Lean_addAliasEntry___spec__8___closed__1;
x_93 = l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_addAliasEntry___spec__9(x_3, x_90, x_91, lean_box(0), x_83, x_92);
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
x_98 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_addAliasEntry___spec__10(x_96, x_97, x_4, x_5);
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
x_106 = l_Lean_PersistentHashMap_insertAux___at_Lean_addAliasEntry___spec__8___closed__1;
x_107 = l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_addAliasEntry___spec__9(x_3, x_104, x_105, lean_box(0), x_97, x_106);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_Lean_addAliasEntry___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; size_t x_5; size_t x_6; lean_object* x_7; 
x_4 = l_Lean_Name_hash___override(x_2);
x_5 = lean_uint64_to_usize(x_4);
x_6 = 1;
x_7 = l_Lean_PersistentHashMap_insertAux___at_Lean_addAliasEntry___spec__8(x_1, x_5, x_6, x_2, x_3);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_Lean_addAliasEntry___spec__11(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_addAliasEntry___spec__14(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = l_Lean_Name_hash___override(x_4);
x_8 = 32;
x_9 = lean_uint64_shift_right(x_7, x_8);
x_10 = lean_uint64_xor(x_7, x_9);
x_11 = 16;
x_12 = lean_uint64_shift_right(x_10, x_11);
x_13 = lean_uint64_xor(x_10, x_12);
x_14 = lean_uint64_to_usize(x_13);
x_15 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_16 = 1;
x_17 = lean_usize_sub(x_15, x_16);
x_18 = lean_usize_land(x_14, x_17);
x_19 = lean_array_uget(x_1, x_18);
lean_ctor_set(x_2, 2, x_19);
x_20 = lean_array_uset(x_1, x_18, x_2);
x_1 = x_20;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; size_t x_33; size_t x_34; size_t x_35; size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_22 = lean_ctor_get(x_2, 0);
x_23 = lean_ctor_get(x_2, 1);
x_24 = lean_ctor_get(x_2, 2);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_2);
x_25 = lean_array_get_size(x_1);
x_26 = l_Lean_Name_hash___override(x_22);
x_27 = 32;
x_28 = lean_uint64_shift_right(x_26, x_27);
x_29 = lean_uint64_xor(x_26, x_28);
x_30 = 16;
x_31 = lean_uint64_shift_right(x_29, x_30);
x_32 = lean_uint64_xor(x_29, x_31);
x_33 = lean_uint64_to_usize(x_32);
x_34 = lean_usize_of_nat(x_25);
lean_dec(x_25);
x_35 = 1;
x_36 = lean_usize_sub(x_34, x_35);
x_37 = lean_usize_land(x_33, x_36);
x_38 = lean_array_uget(x_1, x_37);
x_39 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_39, 0, x_22);
lean_ctor_set(x_39, 1, x_23);
lean_ctor_set(x_39, 2, x_38);
x_40 = lean_array_uset(x_1, x_37, x_39);
x_1 = x_40;
x_2 = x_24;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lean_addAliasEntry___spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_addAliasEntry___spec__14(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_addAliasEntry___spec__12(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = lean_mk_array(x_4, x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lean_addAliasEntry___spec__13(x_7, x_1, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_Lean_addAliasEntry___spec__15(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_10 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_addAliasEntry___spec__15(x_1, x_2, x_8);
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
x_15 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_addAliasEntry___spec__15(x_1, x_2, x_13);
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
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at_Lean_addAliasEntry___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_7 = l_Lean_PersistentHashMap_insert___at_Lean_addAliasEntry___spec__7(x_6, x_2, x_3);
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
x_11 = l_Lean_PersistentHashMap_insert___at_Lean_addAliasEntry___spec__7(x_10, x_2, x_3);
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
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_1, 0);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; uint64_t x_24; uint64_t x_25; uint64_t x_26; size_t x_27; size_t x_28; size_t x_29; size_t x_30; size_t x_31; lean_object* x_32; uint8_t x_33; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
x_19 = lean_array_get_size(x_18);
x_20 = l_Lean_Name_hash___override(x_2);
x_21 = 32;
x_22 = lean_uint64_shift_right(x_20, x_21);
x_23 = lean_uint64_xor(x_20, x_22);
x_24 = 16;
x_25 = lean_uint64_shift_right(x_23, x_24);
x_26 = lean_uint64_xor(x_23, x_25);
x_27 = lean_uint64_to_usize(x_26);
x_28 = lean_usize_of_nat(x_19);
lean_dec(x_19);
x_29 = 1;
x_30 = lean_usize_sub(x_28, x_29);
x_31 = lean_usize_land(x_27, x_30);
x_32 = lean_array_uget(x_18, x_31);
x_33 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_addAliasEntry___spec__11(x_2, x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_nat_add(x_17, x_34);
lean_dec(x_17);
x_36 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_36, 0, x_2);
lean_ctor_set(x_36, 1, x_3);
lean_ctor_set(x_36, 2, x_32);
x_37 = lean_array_uset(x_18, x_31, x_36);
x_38 = lean_unsigned_to_nat(4u);
x_39 = lean_nat_mul(x_35, x_38);
x_40 = lean_unsigned_to_nat(3u);
x_41 = lean_nat_div(x_39, x_40);
lean_dec(x_39);
x_42 = lean_array_get_size(x_37);
x_43 = lean_nat_dec_le(x_41, x_42);
lean_dec(x_42);
lean_dec(x_41);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_addAliasEntry___spec__12(x_37);
lean_ctor_set(x_15, 1, x_44);
lean_ctor_set(x_15, 0, x_35);
x_45 = 1;
lean_ctor_set_uint8(x_1, sizeof(void*)*2, x_45);
return x_1;
}
else
{
uint8_t x_46; 
lean_ctor_set(x_15, 1, x_37);
lean_ctor_set(x_15, 0, x_35);
x_46 = 1;
lean_ctor_set_uint8(x_1, sizeof(void*)*2, x_46);
return x_1;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_47 = lean_box(0);
x_48 = lean_array_uset(x_18, x_31, x_47);
x_49 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_addAliasEntry___spec__15(x_2, x_3, x_32);
x_50 = lean_array_uset(x_48, x_31, x_49);
lean_ctor_set(x_15, 1, x_50);
x_51 = 1;
lean_ctor_set_uint8(x_1, sizeof(void*)*2, x_51);
return x_1;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint64_t x_55; uint64_t x_56; uint64_t x_57; uint64_t x_58; uint64_t x_59; uint64_t x_60; uint64_t x_61; size_t x_62; size_t x_63; size_t x_64; size_t x_65; size_t x_66; lean_object* x_67; uint8_t x_68; 
x_52 = lean_ctor_get(x_15, 0);
x_53 = lean_ctor_get(x_15, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_15);
x_54 = lean_array_get_size(x_53);
x_55 = l_Lean_Name_hash___override(x_2);
x_56 = 32;
x_57 = lean_uint64_shift_right(x_55, x_56);
x_58 = lean_uint64_xor(x_55, x_57);
x_59 = 16;
x_60 = lean_uint64_shift_right(x_58, x_59);
x_61 = lean_uint64_xor(x_58, x_60);
x_62 = lean_uint64_to_usize(x_61);
x_63 = lean_usize_of_nat(x_54);
lean_dec(x_54);
x_64 = 1;
x_65 = lean_usize_sub(x_63, x_64);
x_66 = lean_usize_land(x_62, x_65);
x_67 = lean_array_uget(x_53, x_66);
x_68 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_addAliasEntry___spec__11(x_2, x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_69 = lean_unsigned_to_nat(1u);
x_70 = lean_nat_add(x_52, x_69);
lean_dec(x_52);
x_71 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_71, 0, x_2);
lean_ctor_set(x_71, 1, x_3);
lean_ctor_set(x_71, 2, x_67);
x_72 = lean_array_uset(x_53, x_66, x_71);
x_73 = lean_unsigned_to_nat(4u);
x_74 = lean_nat_mul(x_70, x_73);
x_75 = lean_unsigned_to_nat(3u);
x_76 = lean_nat_div(x_74, x_75);
lean_dec(x_74);
x_77 = lean_array_get_size(x_72);
x_78 = lean_nat_dec_le(x_76, x_77);
lean_dec(x_77);
lean_dec(x_76);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_79 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_addAliasEntry___spec__12(x_72);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_70);
lean_ctor_set(x_80, 1, x_79);
x_81 = 1;
lean_ctor_set(x_1, 0, x_80);
lean_ctor_set_uint8(x_1, sizeof(void*)*2, x_81);
return x_1;
}
else
{
lean_object* x_82; uint8_t x_83; 
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_70);
lean_ctor_set(x_82, 1, x_72);
x_83 = 1;
lean_ctor_set(x_1, 0, x_82);
lean_ctor_set_uint8(x_1, sizeof(void*)*2, x_83);
return x_1;
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_84 = lean_box(0);
x_85 = lean_array_uset(x_53, x_66, x_84);
x_86 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_addAliasEntry___spec__15(x_2, x_3, x_67);
x_87 = lean_array_uset(x_85, x_66, x_86);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_52);
lean_ctor_set(x_88, 1, x_87);
x_89 = 1;
lean_ctor_set(x_1, 0, x_88);
lean_ctor_set_uint8(x_1, sizeof(void*)*2, x_89);
return x_1;
}
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint64_t x_96; uint64_t x_97; uint64_t x_98; uint64_t x_99; uint64_t x_100; uint64_t x_101; uint64_t x_102; size_t x_103; size_t x_104; size_t x_105; size_t x_106; size_t x_107; lean_object* x_108; uint8_t x_109; 
x_90 = lean_ctor_get(x_1, 0);
x_91 = lean_ctor_get(x_1, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_1);
x_92 = lean_ctor_get(x_90, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_90, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_94 = x_90;
} else {
 lean_dec_ref(x_90);
 x_94 = lean_box(0);
}
x_95 = lean_array_get_size(x_93);
x_96 = l_Lean_Name_hash___override(x_2);
x_97 = 32;
x_98 = lean_uint64_shift_right(x_96, x_97);
x_99 = lean_uint64_xor(x_96, x_98);
x_100 = 16;
x_101 = lean_uint64_shift_right(x_99, x_100);
x_102 = lean_uint64_xor(x_99, x_101);
x_103 = lean_uint64_to_usize(x_102);
x_104 = lean_usize_of_nat(x_95);
lean_dec(x_95);
x_105 = 1;
x_106 = lean_usize_sub(x_104, x_105);
x_107 = lean_usize_land(x_103, x_106);
x_108 = lean_array_uget(x_93, x_107);
x_109 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_addAliasEntry___spec__11(x_2, x_108);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; 
x_110 = lean_unsigned_to_nat(1u);
x_111 = lean_nat_add(x_92, x_110);
lean_dec(x_92);
x_112 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_112, 0, x_2);
lean_ctor_set(x_112, 1, x_3);
lean_ctor_set(x_112, 2, x_108);
x_113 = lean_array_uset(x_93, x_107, x_112);
x_114 = lean_unsigned_to_nat(4u);
x_115 = lean_nat_mul(x_111, x_114);
x_116 = lean_unsigned_to_nat(3u);
x_117 = lean_nat_div(x_115, x_116);
lean_dec(x_115);
x_118 = lean_array_get_size(x_113);
x_119 = lean_nat_dec_le(x_117, x_118);
lean_dec(x_118);
lean_dec(x_117);
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; uint8_t x_122; lean_object* x_123; 
x_120 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_addAliasEntry___spec__12(x_113);
if (lean_is_scalar(x_94)) {
 x_121 = lean_alloc_ctor(0, 2, 0);
} else {
 x_121 = x_94;
}
lean_ctor_set(x_121, 0, x_111);
lean_ctor_set(x_121, 1, x_120);
x_122 = 1;
x_123 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_91);
lean_ctor_set_uint8(x_123, sizeof(void*)*2, x_122);
return x_123;
}
else
{
lean_object* x_124; uint8_t x_125; lean_object* x_126; 
if (lean_is_scalar(x_94)) {
 x_124 = lean_alloc_ctor(0, 2, 0);
} else {
 x_124 = x_94;
}
lean_ctor_set(x_124, 0, x_111);
lean_ctor_set(x_124, 1, x_113);
x_125 = 1;
x_126 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_91);
lean_ctor_set_uint8(x_126, sizeof(void*)*2, x_125);
return x_126;
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; lean_object* x_133; 
x_127 = lean_box(0);
x_128 = lean_array_uset(x_93, x_107, x_127);
x_129 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_addAliasEntry___spec__15(x_2, x_3, x_108);
x_130 = lean_array_uset(x_128, x_107, x_129);
if (lean_is_scalar(x_94)) {
 x_131 = lean_alloc_ctor(0, 2, 0);
} else {
 x_131 = x_94;
}
lean_ctor_set(x_131, 0, x_92);
lean_ctor_set(x_131, 1, x_130);
x_132 = 1;
x_133 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_91);
lean_ctor_set_uint8(x_133, sizeof(void*)*2, x_132);
return x_133;
}
}
}
}
}
LEAN_EXPORT uint8_t l_List_elem___at_Lean_addAliasEntry___spec__16(lean_object* x_1, lean_object* x_2) {
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
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_name_eq(x_1, x_4);
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
LEAN_EXPORT lean_object* l_Lean_addAliasEntry(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_inc(x_1);
x_4 = l_Lean_SMap_find_x3f___at_Lean_addAliasEntry___spec__1(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
x_8 = l_Lean_SMap_insert___at_Lean_addAliasEntry___spec__6(x_1, x_3, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
lean_dec(x_4);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_dec(x_2);
x_11 = l_List_elem___at_Lean_addAliasEntry___spec__16(x_10, x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_9);
x_13 = l_Lean_SMap_insert___at_Lean_addAliasEntry___spec__6(x_1, x_3, x_12);
return x_13;
}
else
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
return x_1;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_addAliasEntry___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentHashMap_findAtAux___at_Lean_addAliasEntry___spec__4(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_addAliasEntry___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_findAux___at_Lean_addAliasEntry___spec__3(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_addAliasEntry___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PersistentHashMap_find_x3f___at_Lean_addAliasEntry___spec__2(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_addAliasEntry___spec__5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_addAliasEntry___spec__5(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at_Lean_addAliasEntry___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_SMap_find_x3f___at_Lean_addAliasEntry___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_addAliasEntry___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; lean_object* x_8; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_addAliasEntry___spec__9(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_addAliasEntry___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Lean_PersistentHashMap_insertAux___at_Lean_addAliasEntry___spec__8(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_Lean_addAliasEntry___spec__11___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_addAliasEntry___spec__11(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_elem___at_Lean_addAliasEntry___spec__16___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_elem___at_Lean_addAliasEntry___spec__16(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_initFn____x40_Lean_ResolveName___hyg_392____spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Lean_addAliasEntry(x_4, x_6);
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_initFn____x40_Lean_ResolveName___hyg_392____spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; size_t x_10; size_t x_11; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_array_get_size(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_lt(x_8, x_7);
x_10 = 1;
x_11 = lean_usize_add(x_2, x_10);
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
x_17 = l_Array_foldlMUnsafe_fold___at_Lean_initFn____x40_Lean_ResolveName___hyg_392____spec__2(x_6, x_15, x_16, x_4);
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
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at_Lean_initFn____x40_Lean_ResolveName___hyg_392____spec__1(lean_object* x_1, lean_object* x_2) {
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
x_9 = l_Array_foldlMUnsafe_fold___at_Lean_initFn____x40_Lean_ResolveName___hyg_392____spec__3(x_2, x_7, x_8, x_1);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at_Lean_initFn____x40_Lean_ResolveName___hyg_392____spec__4(lean_object* x_1) {
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
static lean_object* _init_l_Lean_initFn____x40_Lean_ResolveName___hyg_392____lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(10u);
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Nat_nextPowerOfTwo_go(x_1, x_2, lean_box(0));
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_ResolveName___hyg_392____lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_initFn____x40_Lean_ResolveName___hyg_392____lambda__1___closed__1;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_ResolveName___hyg_392____lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_initFn____x40_Lean_ResolveName___hyg_392____lambda__1___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_ResolveName___hyg_392____lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_ResolveName___hyg_392____lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_initFn____x40_Lean_ResolveName___hyg_392____lambda__1___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_ResolveName___hyg_392____lambda__1___closed__6() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = l_Lean_initFn____x40_Lean_ResolveName___hyg_392____lambda__1___closed__3;
x_3 = l_Lean_initFn____x40_Lean_ResolveName___hyg_392____lambda__1___closed__5;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_ResolveName___hyg_392____lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_initFn____x40_Lean_ResolveName___hyg_392____lambda__1___closed__6;
x_3 = l_Lean_mkStateFromImportedEntries___at_Lean_initFn____x40_Lean_ResolveName___hyg_392____spec__1(x_2, x_1);
x_4 = l_Lean_SMap_switch___at_Lean_initFn____x40_Lean_ResolveName___hyg_392____spec__4(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_ResolveName___hyg_392____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_ResolveName___hyg_392____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("aliasExtension", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_ResolveName___hyg_392____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_ResolveName___hyg_392____closed__1;
x_2 = l_Lean_initFn____x40_Lean_ResolveName___hyg_392____closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_ResolveName___hyg_392____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_addAliasEntry), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_ResolveName___hyg_392____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_initFn____x40_Lean_ResolveName___hyg_392____lambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_ResolveName___hyg_392____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_List_toArray___rarg), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_ResolveName___hyg_392____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_1 = lean_box(0);
x_2 = l_Lean_initFn____x40_Lean_ResolveName___hyg_392____closed__3;
x_3 = l_Lean_initFn____x40_Lean_ResolveName___hyg_392____closed__4;
x_4 = l_Lean_initFn____x40_Lean_ResolveName___hyg_392____closed__5;
x_5 = l_Lean_initFn____x40_Lean_ResolveName___hyg_392____closed__6;
x_6 = 2;
x_7 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_3);
lean_ctor_set(x_7, 2, x_4);
lean_ctor_set(x_7, 3, x_5);
lean_ctor_set(x_7, 4, x_1);
lean_ctor_set_uint8(x_7, sizeof(void*)*5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_ResolveName___hyg_392_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_initFn____x40_Lean_ResolveName___hyg_392____closed__7;
x_3 = l_Lean_registerSimplePersistentEnvExtension___rarg(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_initFn____x40_Lean_ResolveName___hyg_392____spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_initFn____x40_Lean_ResolveName___hyg_392____spec__2(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_initFn____x40_Lean_ResolveName___hyg_392____spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_initFn____x40_Lean_ResolveName___hyg_392____spec__3(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at_Lean_initFn____x40_Lean_ResolveName___hyg_392____spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkStateFromImportedEntries___at_Lean_initFn____x40_Lean_ResolveName___hyg_392____spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_ResolveName___hyg_392____lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_initFn____x40_Lean_ResolveName___hyg_392____lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addAlias___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_aliasExtension;
return x_1;
}
}
LEAN_EXPORT lean_object* lean_add_alias(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
x_5 = l_Lean_addAlias___closed__1;
x_6 = l_Lean_PersistentEnvExtension_addEntry___rarg(x_5, x_1, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_getAliasState___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Name_instBEq;
x_2 = l_Lean_instHashableName;
x_3 = l_Lean_SMap_instInhabited___rarg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_getAliasState(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = l_Lean_aliasExtension;
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
lean_dec(x_3);
x_5 = l_Lean_getAliasState___closed__1;
x_6 = l_Lean_addAlias___closed__1;
x_7 = l_Lean_SimplePersistentEnvExtension_getState___rarg(x_5, x_6, x_1, x_4);
return x_7;
}
}
static lean_object* _init_l_List_filterTR_loop___at_Lean_getAliases___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_protectedExt;
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at_Lean_getAliases___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
lean_dec(x_1);
x_4 = l_List_reverse___rarg(x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = l_List_filterTR_loop___at_Lean_getAliases___spec__1___closed__1;
lean_inc(x_6);
lean_inc(x_1);
x_9 = l_Lean_TagDeclarationExtension_isTagged(x_8, x_1, x_6);
if (x_9 == 0)
{
lean_ctor_set(x_2, 1, x_3);
{
lean_object* _tmp_1 = x_7;
lean_object* _tmp_2 = x_2;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
else
{
lean_free_object(x_2);
lean_dec(x_6);
x_2 = x_7;
goto _start;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_2);
x_14 = l_List_filterTR_loop___at_Lean_getAliases___spec__1___closed__1;
lean_inc(x_12);
lean_inc(x_1);
x_15 = l_Lean_TagDeclarationExtension_isTagged(x_14, x_1, x_12);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_3);
x_2 = x_13;
x_3 = x_16;
goto _start;
}
else
{
lean_dec(x_12);
x_2 = x_13;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getAliases(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = l_Lean_aliasExtension;
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get_uint8(x_5, sizeof(void*)*3);
lean_dec(x_5);
x_7 = l_Lean_getAliasState___closed__1;
x_8 = l_Lean_addAlias___closed__1;
lean_inc(x_1);
x_9 = l_Lean_SimplePersistentEnvExtension_getState___rarg(x_7, x_8, x_1, x_6);
x_10 = l_Lean_SMap_find_x3f___at_Lean_addAliasEntry___spec__1(x_9, x_2);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
lean_dec(x_1);
x_11 = lean_box(0);
return x_11;
}
else
{
if (x_3 == 0)
{
lean_object* x_12; 
lean_dec(x_1);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_box(0);
x_15 = l_List_filterTR_loop___at_Lean_getAliases___spec__1(x_1, x_13, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getAliases___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
lean_dec(x_3);
x_5 = l_Lean_getAliases(x_1, x_2, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_getRevAliases___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 2);
lean_inc(x_6);
lean_dec(x_3);
lean_inc(x_1);
x_7 = lean_apply_3(x_1, x_2, x_4, x_5);
x_2 = x_7;
x_3 = x_6;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_getRevAliases___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_getRevAliases___spec__2___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_getRevAliases___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_foldlMAux___at_Lean_MetavarContext_getExprAssignmentDomain___spec__2___rarg(x_2, x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_getRevAliases___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldlM___at_Lean_getRevAliases___spec__3___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_getRevAliases___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_foldlMAux___at_Lean_MetavarContext_getExprAssignmentDomain___spec__2___rarg(x_2, x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_getRevAliases___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldlM___at_Lean_getRevAliases___spec__4___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_getRevAliases___spec__5___rarg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_7 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_8 = l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_getRevAliases___spec__2___rarg(x_1, x_5, x_7);
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_getRevAliases___spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lean_getRevAliases___spec__5___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_getRevAliases___spec__6___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_foldlMAux___at_Lean_MetavarContext_getExprAssignmentDomain___spec__2___rarg(x_2, x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_getRevAliases___spec__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldlM___at_Lean_getRevAliases___spec__6___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at_Lean_getRevAliases___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_ctor_get(x_3, 1);
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_5, 1);
x_7 = lean_array_get_size(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_lt(x_8, x_7);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_7);
x_10 = l_Lean_PersistentHashMap_foldlMAux___at_Lean_MetavarContext_getExprAssignmentDomain___spec__2___rarg(x_1, x_4, x_2);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = lean_nat_dec_le(x_7, x_7);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_7);
x_12 = l_Lean_PersistentHashMap_foldlMAux___at_Lean_MetavarContext_getExprAssignmentDomain___spec__2___rarg(x_1, x_4, x_2);
return x_12;
}
else
{
size_t x_13; size_t x_14; lean_object* x_15; lean_object* x_16; 
x_13 = 0;
x_14 = lean_usize_of_nat(x_7);
lean_dec(x_7);
lean_inc(x_1);
x_15 = l_Array_foldlMUnsafe_fold___at_Lean_getRevAliases___spec__5___rarg(x_1, x_6, x_13, x_14, x_2);
x_16 = l_Lean_PersistentHashMap_foldlMAux___at_Lean_MetavarContext_getExprAssignmentDomain___spec__2___rarg(x_1, x_4, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at_Lean_getRevAliases___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_SMap_fold___at_Lean_getRevAliases___spec__1___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_getRevAliases___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_List_elem___at_Lean_addAliasEntry___spec__16(x_1, x_4);
if (x_5 == 0)
{
lean_dec(x_3);
return x_2;
}
else
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_2);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getRevAliases(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_3 = lean_alloc_closure((void*)(l_Lean_getRevAliases___lambda__1___boxed), 4, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = lean_box(0);
x_5 = l_Lean_aliasExtension;
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get_uint8(x_6, sizeof(void*)*3);
lean_dec(x_6);
x_8 = l_Lean_getAliasState___closed__1;
x_9 = l_Lean_addAlias___closed__1;
x_10 = l_Lean_SimplePersistentEnvExtension_getState___rarg(x_8, x_9, x_1, x_7);
x_11 = l_Lean_SMap_fold___at_Lean_getRevAliases___spec__1___rarg(x_3, x_4, x_10);
lean_dec(x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_getRevAliases___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_foldlM___at_Lean_getRevAliases___spec__3___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_getRevAliases___spec__4___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_foldlM___at_Lean_getRevAliases___spec__4___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_getRevAliases___spec__5___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lean_getRevAliases___spec__5___rarg(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at_Lean_getRevAliases___spec__6___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_foldlM___at_Lean_getRevAliases___spec__6___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at_Lean_getRevAliases___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_SMap_fold___at_Lean_getRevAliases___spec__1___rarg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_getRevAliases___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_getRevAliases___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT uint8_t l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
lean_inc(x_2);
lean_inc(x_1);
x_3 = l_Lean_Environment_contains(x_1, x_2);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = l_Lean_isReservedName(x_1, x_2);
return x_4;
}
else
{
uint8_t x_5; 
lean_dec(x_2);
lean_dec(x_1);
x_5 = 1;
return x_5;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveQualifiedName(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; uint8_t x_7; 
lean_inc(x_3);
x_4 = l_Lean_Name_append(x_2, x_3);
x_5 = l_Lean_Name_isAtomic(x_3);
lean_dec(x_3);
lean_inc(x_1);
x_6 = l_Lean_getAliases(x_1, x_4, x_5);
lean_inc(x_4);
lean_inc(x_1);
x_7 = l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(x_1, x_4);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lean_mkPrivateName(x_1, x_4);
lean_inc(x_8);
x_9 = l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(x_1, x_8);
if (x_9 == 0)
{
lean_dec(x_8);
return x_6;
}
else
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_6);
return x_10;
}
}
else
{
if (x_5 == 0)
{
lean_object* x_11; 
lean_dec(x_1);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_6);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = l_List_filterTR_loop___at_Lean_getAliases___spec__1___closed__1;
lean_inc(x_4);
lean_inc(x_1);
x_13 = l_Lean_TagDeclarationExtension_isTagged(x_12, x_1, x_4);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_1);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_6);
return x_14;
}
else
{
lean_object* x_15; uint8_t x_16; 
x_15 = l_Lean_mkPrivateName(x_1, x_4);
lean_inc(x_15);
x_16 = l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(x_1, x_15);
if (x_16 == 0)
{
lean_dec(x_15);
return x_6;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_6);
return x_17;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveUsingNamespace(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_1);
x_5 = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveQualifiedName(x_1, x_3, x_2);
if (lean_obj_tag(x_5) == 0)
{
x_3 = x_4;
goto _start;
}
else
{
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
else
{
lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(0);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveExact(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_Name_isAtomic(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = l_Lean_rootNamespace;
x_5 = lean_box(0);
x_6 = l_Lean_Name_replacePrefix(x_2, x_4, x_5);
lean_inc(x_6);
lean_inc(x_1);
x_7 = l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(x_1, x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lean_mkPrivateName(x_1, x_6);
lean_inc(x_8);
x_9 = l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(x_1, x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_8);
x_10 = lean_box(0);
return x_10;
}
else
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_8);
return x_11;
}
}
else
{
lean_object* x_12; 
lean_dec(x_1);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_6);
return x_12;
}
}
else
{
lean_object* x_13; 
lean_dec(x_2);
lean_dec(x_1);
x_13 = lean_box(0);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveOpenDecls(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = l_List_elem___at_Lean_addAliasEntry___spec__16(x_2, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_inc(x_2);
lean_inc(x_1);
x_10 = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveQualifiedName(x_1, x_7, x_2);
x_11 = l_List_appendTR___rarg(x_10, x_4);
x_3 = x_6;
x_4 = x_11;
goto _start;
}
else
{
lean_dec(x_7);
x_3 = x_6;
goto _start;
}
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_3);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_3, 1);
x_16 = lean_ctor_get(x_3, 0);
lean_dec(x_16);
x_17 = lean_ctor_get(x_5, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_5, 1);
lean_inc(x_18);
lean_dec(x_5);
x_19 = lean_name_eq(x_17, x_2);
if (x_19 == 0)
{
uint8_t x_20; 
x_20 = l_Lean_Name_isPrefixOf(x_17, x_2);
if (x_20 == 0)
{
lean_dec(x_18);
lean_dec(x_17);
lean_free_object(x_3);
x_3 = x_15;
goto _start;
}
else
{
lean_object* x_22; uint8_t x_23; 
lean_inc(x_2);
x_22 = l_Lean_Name_replacePrefix(x_2, x_17, x_18);
lean_dec(x_18);
lean_dec(x_17);
lean_inc(x_22);
lean_inc(x_1);
x_23 = l_Lean_Environment_contains(x_1, x_22);
if (x_23 == 0)
{
lean_dec(x_22);
lean_free_object(x_3);
x_3 = x_15;
goto _start;
}
else
{
lean_ctor_set(x_3, 1, x_4);
lean_ctor_set(x_3, 0, x_22);
{
lean_object* _tmp_2 = x_15;
lean_object* _tmp_3 = x_3;
x_3 = _tmp_2;
x_4 = _tmp_3;
}
goto _start;
}
}
}
else
{
lean_dec(x_17);
lean_ctor_set(x_3, 1, x_4);
lean_ctor_set(x_3, 0, x_18);
{
lean_object* _tmp_2 = x_15;
lean_object* _tmp_3 = x_3;
x_3 = _tmp_2;
x_4 = _tmp_3;
}
goto _start;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_3, 1);
lean_inc(x_27);
lean_dec(x_3);
x_28 = lean_ctor_get(x_5, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_5, 1);
lean_inc(x_29);
lean_dec(x_5);
x_30 = lean_name_eq(x_28, x_2);
if (x_30 == 0)
{
uint8_t x_31; 
x_31 = l_Lean_Name_isPrefixOf(x_28, x_2);
if (x_31 == 0)
{
lean_dec(x_29);
lean_dec(x_28);
x_3 = x_27;
goto _start;
}
else
{
lean_object* x_33; uint8_t x_34; 
lean_inc(x_2);
x_33 = l_Lean_Name_replacePrefix(x_2, x_28, x_29);
lean_dec(x_29);
lean_dec(x_28);
lean_inc(x_33);
lean_inc(x_1);
x_34 = l_Lean_Environment_contains(x_1, x_33);
if (x_34 == 0)
{
lean_dec(x_33);
x_3 = x_27;
goto _start;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_4);
x_3 = x_27;
x_4 = x_36;
goto _start;
}
}
}
else
{
lean_object* x_38; 
lean_dec(x_28);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_29);
lean_ctor_set(x_38, 1, x_4);
x_3 = x_27;
x_4 = x_38;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_eraseDups_loop___at_Lean_ResolveName_resolveGlobalName_loop___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___rarg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_List_elem___at_Lean_addAliasEntry___spec__16(x_5, x_2);
if (x_7 == 0)
{
lean_ctor_set(x_1, 1, x_2);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_free_object(x_1);
lean_dec(x_5);
x_1 = x_6;
goto _start;
}
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_1);
x_12 = l_List_elem___at_Lean_addAliasEntry___spec__16(x_10, x_2);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_2);
x_1 = x_11;
x_2 = x_13;
goto _start;
}
else
{
lean_dec(x_10);
x_1 = x_11;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_eraseDups___at_Lean_ResolveName_resolveGlobalName_loop___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = l_List_eraseDups_loop___at_Lean_ResolveName_resolveGlobalName_loop___spec__2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_ResolveName_resolveGlobalName_loop___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
lean_dec(x_1);
x_4 = l_List_reverse___rarg(x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_1);
lean_ctor_set(x_2, 1, x_3);
lean_ctor_set(x_2, 0, x_8);
{
lean_object* _tmp_1 = x_7;
lean_object* _tmp_2 = x_2;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_2);
lean_inc(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_1);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
x_2 = x_11;
x_3 = x_13;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_ResolveName_resolveGlobalName_loop___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
lean_dec(x_1);
x_4 = l_List_reverse___rarg(x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_1);
lean_ctor_set(x_2, 1, x_3);
lean_ctor_set(x_2, 0, x_8);
{
lean_object* _tmp_1 = x_7;
lean_object* _tmp_2 = x_2;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_2);
lean_inc(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_1);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
x_2 = x_11;
x_3 = x_13;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_ResolveName_resolveGlobalName_loop___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
lean_dec(x_1);
x_4 = l_List_reverse___rarg(x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_1);
lean_ctor_set(x_2, 1, x_3);
lean_ctor_set(x_2, 0, x_8);
{
lean_object* _tmp_1 = x_7;
lean_object* _tmp_2 = x_2;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_2);
lean_inc(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_1);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
x_2 = x_11;
x_3 = x_13;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_ResolveName_resolveGlobalName_loop___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
lean_dec(x_1);
x_4 = l_List_reverse___rarg(x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_1);
lean_ctor_set(x_2, 1, x_3);
lean_ctor_set(x_2, 0, x_8);
{
lean_object* _tmp_1 = x_7;
lean_object* _tmp_2 = x_2;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_2);
lean_inc(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_1);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
x_2 = x_11;
x_3 = x_13;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_ResolveName_resolveGlobalName_loop___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
lean_dec(x_1);
x_4 = l_List_reverse___rarg(x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_1);
lean_ctor_set(x_2, 1, x_3);
lean_ctor_set(x_2, 0, x_8);
{
lean_object* _tmp_1 = x_7;
lean_object* _tmp_2 = x_2;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_2);
lean_inc(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_1);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
x_2 = x_11;
x_3 = x_13;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ResolveName_resolveGlobalName_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_5) == 1)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_4, 1);
x_10 = lean_ctor_get(x_4, 2);
x_11 = lean_ctor_get(x_4, 3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_12 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_9);
lean_ctor_set(x_12, 2, x_10);
lean_ctor_set(x_12, 3, x_11);
x_13 = l_Lean_MacroScopesView_review(x_12);
lean_inc(x_2);
lean_inc(x_13);
lean_inc(x_1);
x_14 = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveUsingNamespace(x_1, x_13, x_2);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
lean_inc(x_13);
lean_inc(x_1);
x_15 = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveExact(x_1, x_13);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; 
lean_inc(x_13);
lean_inc(x_1);
x_16 = l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(x_1, x_13);
lean_inc(x_13);
x_17 = l_Lean_mkPrivateName(x_1, x_13);
lean_inc(x_17);
lean_inc(x_1);
x_18 = l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(x_1, x_17);
x_19 = l_Lean_Name_isAtomic(x_13);
lean_inc(x_1);
x_20 = l_Lean_getAliases(x_1, x_13, x_19);
if (x_16 == 0)
{
lean_object* x_21; 
x_21 = lean_box(0);
if (x_18 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_17);
lean_inc(x_3);
lean_inc(x_1);
x_22 = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveOpenDecls(x_1, x_13, x_3, x_21);
x_23 = l_List_appendTR___rarg(x_20, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_8);
lean_ctor_set(x_24, 1, x_6);
x_5 = x_7;
x_6 = x_24;
goto _start;
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_26 = l_List_eraseDups___at_Lean_ResolveName_resolveGlobalName_loop___spec__1(x_23);
x_27 = l_List_mapTR_loop___at_Lean_ResolveName_resolveGlobalName_loop___spec__3(x_6, x_26, x_21);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_17);
lean_ctor_set(x_28, 1, x_21);
x_29 = l_List_appendTR___rarg(x_28, x_21);
lean_inc(x_3);
lean_inc(x_1);
x_30 = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveOpenDecls(x_1, x_13, x_3, x_29);
x_31 = l_List_appendTR___rarg(x_20, x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_8);
lean_ctor_set(x_32, 1, x_6);
x_5 = x_7;
x_6 = x_32;
goto _start;
}
else
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_34 = l_List_eraseDups___at_Lean_ResolveName_resolveGlobalName_loop___spec__1(x_31);
x_35 = l_List_mapTR_loop___at_Lean_ResolveName_resolveGlobalName_loop___spec__4(x_6, x_34, x_21);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_box(0);
lean_inc(x_13);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_13);
lean_ctor_set(x_37, 1, x_36);
if (x_18 == 0)
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_17);
lean_inc(x_3);
lean_inc(x_1);
x_38 = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveOpenDecls(x_1, x_13, x_3, x_37);
x_39 = l_List_appendTR___rarg(x_20, x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_8);
lean_ctor_set(x_40, 1, x_6);
x_5 = x_7;
x_6 = x_40;
goto _start;
}
else
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_42 = l_List_eraseDups___at_Lean_ResolveName_resolveGlobalName_loop___spec__1(x_39);
x_43 = l_List_mapTR_loop___at_Lean_ResolveName_resolveGlobalName_loop___spec__5(x_6, x_42, x_36);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_17);
lean_ctor_set(x_44, 1, x_36);
x_45 = l_List_appendTR___rarg(x_44, x_37);
lean_inc(x_3);
lean_inc(x_1);
x_46 = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveOpenDecls(x_1, x_13, x_3, x_45);
x_47 = l_List_appendTR___rarg(x_20, x_46);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_8);
lean_ctor_set(x_48, 1, x_6);
x_5 = x_7;
x_6 = x_48;
goto _start;
}
else
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_50 = l_List_eraseDups___at_Lean_ResolveName_resolveGlobalName_loop___spec__1(x_47);
x_51 = l_List_mapTR_loop___at_Lean_ResolveName_resolveGlobalName_loop___spec__6(x_6, x_50, x_36);
return x_51;
}
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_52 = lean_ctor_get(x_15, 0);
lean_inc(x_52);
lean_dec(x_15);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_6);
x_54 = lean_box(0);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_56 = l_List_eraseDups___at_Lean_ResolveName_resolveGlobalName_loop___spec__1(x_14);
x_57 = lean_box(0);
x_58 = l_List_mapTR_loop___at_Lean_ResolveName_resolveGlobalName_loop___spec__7(x_6, x_56, x_57);
return x_58;
}
}
else
{
lean_object* x_59; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_59 = lean_box(0);
return x_59;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ResolveName_resolveGlobalName_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_ResolveName_resolveGlobalName_loop(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = l_Lean_extractMacroScopes(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_box(0);
x_8 = l_Lean_ResolveName_resolveGlobalName_loop(x_1, x_2, x_3, x_5, x_6, x_7);
lean_dec(x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_ResolveName_resolveNamespaceUsingScope_x3f___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.ResolveName", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.ResolveName.resolveNamespaceUsingScope\?", 44, 44);
return x_1;
}
}
static lean_object* _init_l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
return x_1;
}
}
static lean_object* _init_l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__1;
x_2 = l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__2;
x_3 = lean_unsigned_to_nat(201u);
x_4 = lean_unsigned_to_nat(9u);
x_5 = l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_ResolveName_resolveNamespaceUsingScope_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = l_Lean_rootNamespace;
x_5 = lean_box(0);
x_6 = l_Lean_Name_replacePrefix(x_2, x_4, x_5);
x_7 = l_Lean_Environment_isNamespace(x_1, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_6);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_6);
return x_9;
}
}
case 1:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
lean_inc(x_2);
x_11 = l_Lean_Name_append(x_3, x_2);
lean_inc(x_1);
x_12 = l_Lean_Environment_isNamespace(x_1, x_11);
if (x_12 == 0)
{
lean_dec(x_11);
x_3 = x_10;
goto _start;
}
else
{
lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_11);
return x_14;
}
}
default: 
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_15 = l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__4;
x_16 = l_panic___at_Lean_ResolveName_resolveNamespaceUsingScope_x3f___spec__1(x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ResolveName_resolveNamespaceUsingOpenDecls(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_5; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_ctor_get(x_3, 0);
lean_dec(x_8);
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_dec(x_5);
lean_inc(x_2);
x_11 = l_Lean_Name_append(x_9, x_2);
lean_inc(x_1);
x_12 = l_Lean_Environment_isNamespace(x_1, x_11);
if (x_12 == 0)
{
lean_dec(x_11);
lean_dec(x_10);
lean_free_object(x_3);
x_3 = x_7;
goto _start;
}
else
{
uint8_t x_14; 
x_14 = l_List_elem___at_Lean_addAliasEntry___spec__16(x_2, x_10);
lean_dec(x_10);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = l_Lean_ResolveName_resolveNamespaceUsingOpenDecls(x_1, x_2, x_7);
lean_ctor_set(x_3, 1, x_15);
lean_ctor_set(x_3, 0, x_11);
return x_3;
}
else
{
lean_dec(x_11);
lean_free_object(x_3);
x_3 = x_7;
goto _start;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = lean_ctor_get(x_3, 1);
lean_inc(x_17);
lean_dec(x_3);
x_18 = lean_ctor_get(x_5, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_5, 1);
lean_inc(x_19);
lean_dec(x_5);
lean_inc(x_2);
x_20 = l_Lean_Name_append(x_18, x_2);
lean_inc(x_1);
x_21 = l_Lean_Environment_isNamespace(x_1, x_20);
if (x_21 == 0)
{
lean_dec(x_20);
lean_dec(x_19);
x_3 = x_17;
goto _start;
}
else
{
uint8_t x_23; 
x_23 = l_List_elem___at_Lean_addAliasEntry___spec__16(x_2, x_19);
lean_dec(x_19);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = l_Lean_ResolveName_resolveNamespaceUsingOpenDecls(x_1, x_2, x_17);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
else
{
lean_dec(x_20);
x_3 = x_17;
goto _start;
}
}
}
}
else
{
lean_object* x_27; 
lean_dec(x_5);
x_27 = lean_ctor_get(x_3, 1);
lean_inc(x_27);
lean_dec(x_3);
x_3 = x_27;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ResolveName_resolveNamespace(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_4);
lean_inc(x_1);
x_5 = l_Lean_ResolveName_resolveNamespaceUsingScope_x3f(x_1, x_4, x_2);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = l_Lean_ResolveName_resolveNamespaceUsingOpenDecls(x_1, x_4, x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Lean_ResolveName_resolveNamespaceUsingOpenDecls(x_1, x_4, x_3);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadResolveNameOfMonadLift___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_inc(x_1);
x_4 = lean_apply_2(x_1, lean_box(0), x_3);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_apply_2(x_1, lean_box(0), x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadResolveNameOfMonadLift(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_instMonadResolveNameOfMonadLift___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Lean_ResolveName_resolveGlobalName(x_2, x_3, x_5, x_4);
x_9 = lean_apply_2(x_7, lean_box(0), x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_resolveGlobalName___rarg___lambda__1), 5, 4);
lean_closure_set(x_8, 0, x_2);
lean_closure_set(x_8, 1, x_3);
lean_closure_set(x_8, 2, x_6);
lean_closure_set(x_8, 3, x_4);
x_9 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_inc(x_4);
x_7 = lean_alloc_closure((void*)(l_Lean_resolveGlobalName___rarg___lambda__2), 6, 5);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_2);
lean_closure_set(x_7, 2, x_5);
lean_closure_set(x_7, 3, x_3);
lean_closure_set(x_7, 4, x_4);
x_8 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
lean_dec(x_3);
lean_inc(x_5);
x_7 = lean_alloc_closure((void*)(l_Lean_resolveGlobalName___rarg___lambda__3), 5, 4);
lean_closure_set(x_7, 0, x_2);
lean_closure_set(x_7, 1, x_1);
lean_closure_set(x_7, 2, x_4);
lean_closure_set(x_7, 3, x_5);
x_8 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_resolveGlobalName___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
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
}
LEAN_EXPORT uint8_t l_Lean_resolveNamespaceCore___rarg___lambda__2(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
}
static lean_object* _init_l_Lean_resolveNamespaceCore___rarg___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_resolveNamespaceCore___rarg___lambda__2___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_resolveNamespaceCore___rarg___lambda__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unknown namespace '", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_resolveNamespaceCore___rarg___lambda__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
lean_inc(x_3);
x_9 = l_Lean_ResolveName_resolveNamespace(x_1, x_2, x_8, x_3);
lean_inc(x_9);
lean_inc(x_4);
x_10 = lean_alloc_closure((void*)(l_Lean_resolveNamespaceCore___rarg___lambda__1___boxed), 3, 2);
lean_closure_set(x_10, 0, x_4);
lean_closure_set(x_10, 1, x_9);
if (x_5 == 0)
{
uint8_t x_11; 
x_11 = l_List_isEmpty___rarg(x_9);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_7);
lean_dec(x_3);
x_12 = lean_ctor_get(x_4, 0);
lean_inc(x_12);
lean_dec(x_4);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_box(0);
x_15 = lean_apply_2(x_13, lean_box(0), x_14);
x_16 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_15, x_10);
return x_16;
}
else
{
uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_17 = 1;
x_18 = l_Lean_resolveNamespaceCore___rarg___lambda__3___closed__1;
x_19 = l_Lean_Name_toString(x_3, x_17, x_18);
x_20 = l_Lean_resolveNamespaceCore___rarg___lambda__3___closed__2;
x_21 = lean_string_append(x_20, x_19);
lean_dec(x_19);
x_22 = l_Lean_resolveNamespaceCore___rarg___lambda__3___closed__3;
x_23 = lean_string_append(x_21, x_22);
x_24 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = l_Lean_MessageData_ofFormat(x_24);
x_26 = l_Lean_throwError___rarg(x_4, x_7, x_25);
x_27 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_26, x_10);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_3);
x_28 = lean_ctor_get(x_4, 0);
lean_inc(x_28);
lean_dec(x_4);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_box(0);
x_31 = lean_apply_2(x_29, lean_box(0), x_30);
x_32 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_31, x_10);
return x_32;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___rarg___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_box(x_5);
lean_inc(x_6);
x_11 = lean_alloc_closure((void*)(l_Lean_resolveNamespaceCore___rarg___lambda__3___boxed), 8, 7);
lean_closure_set(x_11, 0, x_2);
lean_closure_set(x_11, 1, x_8);
lean_closure_set(x_11, 2, x_3);
lean_closure_set(x_11, 3, x_4);
lean_closure_set(x_11, 4, x_10);
lean_closure_set(x_11, 5, x_6);
lean_closure_set(x_11, 6, x_7);
x_12 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_9, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___rarg___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_box(x_4);
lean_inc(x_5);
x_10 = lean_alloc_closure((void*)(l_Lean_resolveNamespaceCore___rarg___lambda__4___boxed), 8, 7);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_7);
lean_closure_set(x_10, 2, x_2);
lean_closure_set(x_10, 3, x_3);
lean_closure_set(x_10, 4, x_9);
lean_closure_set(x_10, 5, x_5);
lean_closure_set(x_10, 6, x_6);
x_11 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_8, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_box(x_6);
lean_inc(x_7);
x_10 = lean_alloc_closure((void*)(l_Lean_resolveNamespaceCore___rarg___lambda__5___boxed), 7, 6);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_5);
lean_closure_set(x_10, 2, x_1);
lean_closure_set(x_10, 3, x_9);
lean_closure_set(x_10, 4, x_7);
lean_closure_set(x_10, 5, x_4);
x_11 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_8, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_resolveNamespaceCore___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_resolveNamespaceCore___rarg___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___rarg___lambda__2___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_resolveNamespaceCore___rarg___lambda__2(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___rarg___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_5);
lean_dec(x_5);
x_10 = l_Lean_resolveNamespaceCore___rarg___lambda__3(x_1, x_2, x_3, x_4, x_9, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___rarg___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_5);
lean_dec(x_5);
x_10 = l_Lean_resolveNamespaceCore___rarg___lambda__4(x_1, x_2, x_3, x_4, x_9, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___rarg___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_4);
lean_dec(x_4);
x_9 = l_Lean_resolveNamespaceCore___rarg___lambda__5(x_1, x_2, x_3, x_8, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_6);
lean_dec(x_6);
x_8 = l_Lean_resolveNamespaceCore___rarg(x_1, x_2, x_3, x_4, x_5, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at_Lean_resolveNamespace___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_array_to_list(x_2);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_array_push(x_2, x_6);
x_1 = x_5;
x_2 = x_7;
goto _start;
}
else
{
lean_object* x_9; 
lean_dec(x_4);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec(x_1);
x_1 = x_9;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespace___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Lean_replaceRef(x_1, x_4);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_apply_3(x_6, lean_box(0), x_5, x_3);
return x_7;
}
}
static lean_object* _init_l_Lean_resolveNamespace___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expected identifier", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_resolveNamespace___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_resolveNamespace___rarg___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_resolveNamespace___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_resolveNamespace___rarg___closed__2;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespace___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 3)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 3);
lean_inc(x_7);
x_8 = l_Lean_initFn____x40_Lean_ResolveName___hyg_126____closed__1;
x_9 = l_List_filterMapTR_go___at_Lean_resolveNamespace___spec__1(x_7, x_8);
x_10 = l_List_isEmpty___rarg(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_apply_2(x_12, lean_box(0), x_9);
return x_13;
}
else
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_9);
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
x_15 = 0;
lean_inc(x_1);
x_16 = l_Lean_resolveNamespaceCore___rarg(x_1, x_2, x_3, x_4, x_6, x_15);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
lean_dec(x_1);
x_18 = lean_ctor_get(x_14, 0);
lean_inc(x_18);
x_19 = lean_alloc_closure((void*)(l_Lean_resolveNamespace___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_19, 0, x_5);
lean_closure_set(x_19, 1, x_14);
lean_closure_set(x_19, 2, x_16);
x_20 = lean_apply_4(x_17, lean_box(0), lean_box(0), x_18, x_19);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_3);
lean_dec(x_2);
x_21 = l_Lean_resolveNamespace___rarg___closed__3;
x_22 = l_Lean_throwErrorAt___rarg(x_1, x_4, x_5, x_21);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespace(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_resolveNamespace___rarg), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespace___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_resolveNamespace___rarg___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_resolveUniqueNamespace___rarg___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ambiguous namespace '", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lean_resolveUniqueNamespace___rarg___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("', possible interpretations: '", 30, 30);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveUniqueNamespace___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_5 = l_Lean_Syntax_getId(x_1);
x_6 = 1;
x_7 = l_Lean_resolveNamespaceCore___rarg___lambda__3___closed__1;
x_8 = l_Lean_Name_toString(x_5, x_6, x_7);
x_9 = l_Lean_resolveUniqueNamespace___rarg___lambda__1___closed__1;
x_10 = lean_string_append(x_9, x_8);
lean_dec(x_8);
x_11 = l_Lean_resolveUniqueNamespace___rarg___lambda__1___closed__2;
x_12 = lean_string_append(x_10, x_11);
x_13 = l_List_toString___at_Lean_Environment_AddConstAsyncResult_commitConst___spec__1(x_4);
x_14 = lean_string_append(x_12, x_13);
lean_dec(x_13);
x_15 = l_Lean_resolveNamespaceCore___rarg___lambda__3___closed__3;
x_16 = lean_string_append(x_14, x_15);
x_17 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = l_Lean_MessageData_ofFormat(x_17);
x_19 = l_Lean_throwError___rarg(x_2, x_3, x_18);
return x_19;
}
else
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_4, 1);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_3);
x_21 = lean_ctor_get(x_4, 0);
lean_inc(x_21);
lean_dec(x_4);
x_22 = lean_ctor_get(x_2, 0);
lean_inc(x_22);
lean_dec(x_2);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_apply_2(x_23, lean_box(0), x_21);
return x_24;
}
else
{
lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_20);
x_25 = l_Lean_Syntax_getId(x_1);
x_26 = 1;
x_27 = l_Lean_resolveNamespaceCore___rarg___lambda__3___closed__1;
x_28 = l_Lean_Name_toString(x_25, x_26, x_27);
x_29 = l_Lean_resolveUniqueNamespace___rarg___lambda__1___closed__1;
x_30 = lean_string_append(x_29, x_28);
lean_dec(x_28);
x_31 = l_Lean_resolveUniqueNamespace___rarg___lambda__1___closed__2;
x_32 = lean_string_append(x_30, x_31);
x_33 = l_List_toString___at_Lean_Environment_AddConstAsyncResult_commitConst___spec__1(x_4);
x_34 = lean_string_append(x_32, x_33);
lean_dec(x_33);
x_35 = l_Lean_resolveNamespaceCore___rarg___lambda__3___closed__3;
x_36 = lean_string_append(x_34, x_35);
x_37 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = l_Lean_MessageData_ofFormat(x_37);
x_39 = l_Lean_throwError___rarg(x_2, x_3, x_38);
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveUniqueNamespace___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_7 = l_Lean_resolveNamespace___rarg(x_1, x_2, x_3, x_4, x_5);
x_8 = lean_alloc_closure((void*)(l_Lean_resolveUniqueNamespace___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_8, 0, x_5);
lean_closure_set(x_8, 1, x_1);
lean_closure_set(x_8, 2, x_4);
x_9 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveUniqueNamespace(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_resolveUniqueNamespace___rarg), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveUniqueNamespace___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_resolveUniqueNamespace___rarg___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at_Lean_filterFieldList___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___rarg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
x_8 = l_List_isEmpty___rarg(x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_free_object(x_1);
lean_dec(x_5);
x_1 = x_6;
goto _start;
}
else
{
lean_ctor_set(x_1, 1, x_2);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_1);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
x_14 = l_List_isEmpty___rarg(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_dec(x_11);
x_1 = x_12;
goto _start;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_2);
x_1 = x_12;
x_2 = x_16;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_filterFieldList___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___rarg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_7);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_2);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_List_mapTR_loop___at_Lean_filterFieldList___spec__2(x_2, x_3);
x_8 = lean_apply_2(x_6, lean_box(0), x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_box(0);
x_6 = l_List_filterTR_loop___at_Lean_filterFieldList___spec__1(x_4, x_5);
lean_inc(x_6);
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_filterFieldList___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_6);
lean_closure_set(x_7, 2, x_5);
x_8 = l_List_isEmpty___rarg(x_6);
lean_dec(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_box(0);
x_13 = lean_apply_2(x_11, lean_box(0), x_12);
x_14 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_13, x_7);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
x_16 = l_Lean_throwUnknownConstant___rarg(x_1, x_2, x_3);
x_17 = lean_apply_4(x_15, lean_box(0), lean_box(0), x_16, x_7);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_filterFieldList___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_filterFieldList___rarg___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_7 = l_Lean_resolveGlobalName___rarg(x_1, x_2, x_3, x_5);
x_8 = lean_alloc_closure((void*)(l_Lean_filterFieldList___rarg), 4, 3);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_4);
lean_closure_set(x_8, 2, x_5);
x_9 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___rarg), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_ensureNoOverload___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
lean_dec(x_1);
x_4 = l_List_reverse___rarg(x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
x_8 = l_Lean_Expr_const___override(x_6, x_1);
lean_ctor_set(x_2, 1, x_3);
lean_ctor_set(x_2, 0, x_8);
{
lean_object* _tmp_1 = x_7;
lean_object* _tmp_2 = x_2;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_2);
lean_inc(x_1);
x_12 = l_Lean_Expr_const___override(x_10, x_1);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
x_2 = x_11;
x_3 = x_13;
goto _start;
}
}
}
}
static lean_object* _init_l_List_foldl___at_Lean_ensureNoOverload___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", ", 2, 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_ensureNoOverload___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_List_foldl___at_Lean_ensureNoOverload___spec__3___closed__1;
x_6 = lean_string_append(x_1, x_5);
x_7 = lean_expr_dbg_to_string(x_3);
x_8 = lean_string_append(x_6, x_7);
lean_dec(x_7);
x_1 = x_8;
x_2 = x_4;
goto _start;
}
}
}
static lean_object* _init_l_List_toString___at_Lean_ensureNoOverload___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("[]", 2, 2);
return x_1;
}
}
static lean_object* _init_l_List_toString___at_Lean_ensureNoOverload___spec__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("[", 1, 1);
return x_1;
}
}
static lean_object* _init_l_List_toString___at_Lean_ensureNoOverload___spec__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("]", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_toString___at_Lean_ensureNoOverload___spec__2(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_List_toString___at_Lean_ensureNoOverload___spec__2___closed__1;
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_expr_dbg_to_string(x_4);
x_6 = l_List_toString___at_Lean_ensureNoOverload___spec__2___closed__2;
x_7 = lean_string_append(x_6, x_5);
lean_dec(x_5);
x_8 = l_List_toString___at_Lean_ensureNoOverload___spec__2___closed__3;
x_9 = lean_string_append(x_7, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint32_t x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_expr_dbg_to_string(x_10);
x_12 = l_List_toString___at_Lean_ensureNoOverload___spec__2___closed__2;
x_13 = lean_string_append(x_12, x_11);
lean_dec(x_11);
x_14 = l_List_foldl___at_Lean_ensureNoOverload___spec__3(x_13, x_3);
x_15 = 93;
x_16 = lean_string_push(x_14, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_ensureNoOverload___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
lean_dec(x_1);
x_4 = l_List_reverse___rarg(x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
x_8 = l_Lean_Expr_const___override(x_6, x_1);
lean_ctor_set(x_2, 1, x_3);
lean_ctor_set(x_2, 0, x_8);
{
lean_object* _tmp_1 = x_7;
lean_object* _tmp_2 = x_2;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_2);
lean_inc(x_1);
x_12 = l_Lean_Expr_const___override(x_10, x_1);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
x_2 = x_11;
x_3 = x_13;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_ensureNoOverload___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ambiguous identifier '", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lean_ensureNoOverload___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("', possible interpretations: ", 29, 29);
return x_1;
}
}
static lean_object* _init_l_Lean_ensureNoOverload___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNoOverload___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_5 = lean_box(0);
x_6 = l_Lean_Expr_const___override(x_3, x_5);
x_7 = lean_expr_dbg_to_string(x_6);
lean_dec(x_6);
x_8 = l_Lean_ensureNoOverload___rarg___closed__1;
x_9 = lean_string_append(x_8, x_7);
lean_dec(x_7);
x_10 = l_Lean_ensureNoOverload___rarg___closed__2;
x_11 = lean_string_append(x_9, x_10);
x_12 = l_List_mapTR_loop___at_Lean_ensureNoOverload___spec__1(x_5, x_4, x_5);
x_13 = l_List_toString___at_Lean_ensureNoOverload___spec__2(x_12);
lean_dec(x_12);
x_14 = lean_string_append(x_11, x_13);
lean_dec(x_13);
x_15 = l_Lean_ensureNoOverload___rarg___closed__3;
x_16 = lean_string_append(x_14, x_15);
x_17 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = l_Lean_MessageData_ofFormat(x_17);
x_19 = l_Lean_throwError___rarg(x_1, x_2, x_18);
return x_19;
}
else
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_4, 1);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_3);
lean_dec(x_2);
x_21 = lean_ctor_get(x_4, 0);
lean_inc(x_21);
lean_dec(x_4);
x_22 = lean_ctor_get(x_1, 0);
lean_inc(x_22);
lean_dec(x_1);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_apply_2(x_23, lean_box(0), x_21);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_20);
x_25 = lean_box(0);
x_26 = l_Lean_Expr_const___override(x_3, x_25);
x_27 = lean_expr_dbg_to_string(x_26);
lean_dec(x_26);
x_28 = l_Lean_ensureNoOverload___rarg___closed__1;
x_29 = lean_string_append(x_28, x_27);
lean_dec(x_27);
x_30 = l_Lean_ensureNoOverload___rarg___closed__2;
x_31 = lean_string_append(x_29, x_30);
x_32 = l_List_mapTR_loop___at_Lean_ensureNoOverload___spec__4(x_25, x_4, x_25);
x_33 = l_List_toString___at_Lean_ensureNoOverload___spec__2(x_32);
lean_dec(x_32);
x_34 = lean_string_append(x_31, x_33);
lean_dec(x_33);
x_35 = l_Lean_ensureNoOverload___rarg___closed__3;
x_36 = lean_string_append(x_34, x_35);
x_37 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = l_Lean_MessageData_ofFormat(x_37);
x_39 = l_Lean_throwError___rarg(x_1, x_2, x_38);
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNoOverload(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_ensureNoOverload___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_Lean_ensureNoOverload___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_foldl___at_Lean_ensureNoOverload___spec__3(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_toString___at_Lean_ensureNoOverload___spec__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_toString___at_Lean_ensureNoOverload___spec__2(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverloadCore___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_7 = l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___rarg(x_1, x_2, x_3, x_4, x_5);
x_8 = lean_alloc_closure((void*)(l_Lean_ensureNoOverload___rarg), 4, 3);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_4);
lean_closure_set(x_8, 2, x_5);
x_9 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverloadCore(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_resolveGlobalConstNoOverloadCore___rarg), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at_Lean_preprocessSyntaxAndResolve___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_array_to_list(x_2);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
lean_dec(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_1 = x_5;
goto _start;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
lean_dec(x_4);
x_10 = lean_array_push(x_2, x_9);
x_1 = x_8;
x_2 = x_10;
goto _start;
}
else
{
lean_object* x_12; 
lean_dec(x_7);
lean_dec(x_4);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_dec(x_1);
x_1 = x_12;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 3)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_3, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 3);
lean_inc(x_6);
x_7 = l_Lean_initFn____x40_Lean_ResolveName___hyg_126____closed__1;
x_8 = l_List_filterMapTR_go___at_Lean_preprocessSyntaxAndResolve___spec__1(x_6, x_7);
x_9 = l_List_isEmpty___rarg(x_8);
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_8);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_dec(x_2);
x_14 = lean_apply_1(x_4, x_5);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
x_17 = lean_alloc_closure((void*)(l_Lean_resolveNamespace___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_17, 0, x_3);
lean_closure_set(x_17, 1, x_13);
lean_closure_set(x_17, 2, x_14);
x_18 = lean_apply_4(x_15, lean_box(0), lean_box(0), x_16, x_17);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_4);
x_19 = l_Lean_resolveNamespace___rarg___closed__3;
x_20 = l_Lean_throwErrorAt___rarg(x_1, x_2, x_3, x_19);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_preprocessSyntaxAndResolve___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___at_Lean_resolveGlobalConst___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 3)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_3, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 3);
lean_inc(x_6);
x_7 = l_Lean_initFn____x40_Lean_ResolveName___hyg_126____closed__1;
x_8 = l_List_filterMapTR_go___at_Lean_preprocessSyntaxAndResolve___spec__1(x_6, x_7);
x_9 = l_List_isEmpty___rarg(x_8);
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_8);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_dec(x_2);
x_14 = lean_apply_1(x_4, x_5);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
x_17 = lean_alloc_closure((void*)(l_Lean_resolveNamespace___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_17, 0, x_3);
lean_closure_set(x_17, 1, x_13);
lean_closure_set(x_17, 2, x_14);
x_18 = lean_apply_4(x_15, lean_box(0), lean_box(0), x_16, x_17);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_4);
x_19 = l_Lean_resolveNamespace___rarg___closed__3;
x_20 = l_Lean_throwErrorAt___rarg(x_1, x_2, x_3, x_19);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___at_Lean_resolveGlobalConst___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_preprocessSyntaxAndResolve___at_Lean_resolveGlobalConst___spec__1___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
lean_inc(x_4);
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___rarg), 5, 4);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_2);
lean_closure_set(x_6, 2, x_3);
lean_closure_set(x_6, 3, x_4);
x_7 = l_Lean_preprocessSyntaxAndResolve___at_Lean_resolveGlobalConst___spec__1___rarg(x_1, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_resolveGlobalConst___rarg), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_ensureNonAmbiguous___spec__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_instInhabitedName;
x_4 = l_instInhabitedOfMonad___rarg(x_1, x_3);
x_5 = lean_panic_fn(x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_ensureNonAmbiguous___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_panic___at_Lean_ensureNonAmbiguous___spec__1___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_ensureNonAmbiguous___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___rarg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_box(0);
x_8 = l_Lean_Expr_const___override(x_5, x_7);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_8);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = l_Lean_Expr_const___override(x_10, x_12);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_2);
x_1 = x_11;
x_2 = x_14;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_ensureNonAmbiguous___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.ensureNonAmbiguous", 23, 23);
return x_1;
}
}
static lean_object* _init_l_Lean_ensureNonAmbiguous___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__1;
x_2 = l_Lean_ensureNonAmbiguous___rarg___closed__1;
x_3 = lean_unsigned_to_nat(365u);
x_4 = lean_unsigned_to_nat(11u);
x_5 = l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNonAmbiguous___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
lean_dec(x_2);
x_5 = l_Lean_ensureNonAmbiguous___rarg___closed__2;
x_6 = l_panic___at_Lean_ensureNonAmbiguous___spec__1___rarg(x_1, x_5);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_3);
lean_dec(x_2);
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
lean_dec(x_4);
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
lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_7);
x_12 = lean_box(0);
x_13 = 0;
x_14 = lean_unsigned_to_nat(0u);
lean_inc(x_3);
x_15 = l_Lean_Syntax_formatStxAux(x_12, x_13, x_14, x_3);
x_16 = l_Std_Format_defWidth;
x_17 = lean_format_pretty(x_15, x_16, x_14, x_14);
x_18 = l_Lean_ensureNoOverload___rarg___closed__1;
x_19 = lean_string_append(x_18, x_17);
lean_dec(x_17);
x_20 = l_Lean_ensureNoOverload___rarg___closed__2;
x_21 = lean_string_append(x_19, x_20);
x_22 = lean_box(0);
x_23 = l_List_mapTR_loop___at_Lean_ensureNonAmbiguous___spec__2(x_4, x_22);
x_24 = l_List_toString___at_Lean_ensureNoOverload___spec__2(x_23);
lean_dec(x_23);
x_25 = lean_string_append(x_21, x_24);
lean_dec(x_24);
x_26 = l_Lean_ensureNoOverload___rarg___closed__3;
x_27 = lean_string_append(x_25, x_26);
x_28 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = l_Lean_MessageData_ofFormat(x_28);
x_30 = l_Lean_throwErrorAt___rarg(x_1, x_2, x_3, x_29);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNonAmbiguous(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_ensureNonAmbiguous___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverload___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_7 = l_Lean_resolveGlobalConst___rarg(x_1, x_2, x_3, x_4, x_5);
x_8 = lean_alloc_closure((void*)(l_Lean_ensureNonAmbiguous___rarg), 4, 3);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_4);
lean_closure_set(x_8, 2, x_5);
x_9 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverload(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_resolveGlobalConstNoOverload___rarg), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName_loop___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, uint8_t x_9, uint8_t x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
if (x_9 == 0)
{
uint8_t x_38; 
x_38 = 0;
x_12 = x_38;
goto block_37;
}
else
{
uint8_t x_39; 
x_39 = l_List_isEmpty___rarg(x_5);
if (x_39 == 0)
{
uint8_t x_40; 
x_40 = 1;
x_12 = x_40;
goto block_37;
}
else
{
uint8_t x_41; 
x_41 = 0;
x_12 = x_41;
goto block_37;
}
}
block_37:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(x_12);
lean_inc(x_1);
x_14 = lean_apply_2(x_1, x_2, x_13);
if (lean_obj_tag(x_14) == 0)
{
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_3, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_3, 1);
lean_inc(x_16);
lean_dec(x_3);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_5);
x_18 = l_Lean_resolveLocalName_loop___rarg(x_4, x_6, x_7, x_8, x_1, x_15, x_17, x_10);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_19 = lean_ctor_get(x_4, 0);
lean_inc(x_19);
lean_dec(x_4);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_box(0);
x_22 = lean_apply_2(x_20, lean_box(0), x_21);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_14);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_14, 0);
x_25 = lean_ctor_get(x_4, 0);
lean_inc(x_25);
lean_dec(x_4);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = l_Lean_LocalDecl_toExpr(x_24);
lean_dec(x_24);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_5);
lean_ctor_set(x_14, 0, x_28);
x_29 = lean_apply_2(x_26, lean_box(0), x_14);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_30 = lean_ctor_get(x_14, 0);
lean_inc(x_30);
lean_dec(x_14);
x_31 = lean_ctor_get(x_4, 0);
lean_inc(x_31);
lean_dec(x_4);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = l_Lean_LocalDecl_toExpr(x_30);
lean_dec(x_30);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_5);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_36 = lean_apply_2(x_32, lean_box(0), x_35);
return x_36;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName_loop___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_box(0);
x_7 = l_List_filterTR_loop___at_Lean_filterFieldList___spec__1(x_5, x_6);
x_8 = l_List_isEmpty___rarg(x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_box(0);
x_12 = lean_apply_2(x_10, lean_box(0), x_11);
x_13 = 1;
x_14 = lean_box(x_13);
x_15 = lean_apply_1(x_2, x_14);
x_16 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_12, x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
lean_dec(x_1);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_box(0);
x_20 = lean_apply_2(x_18, lean_box(0), x_19);
x_21 = lean_box(x_4);
x_22 = lean_apply_1(x_2, x_21);
x_23 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_20, x_22);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName_loop___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_4, 3);
lean_inc(x_11);
lean_inc(x_6);
x_12 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_12, 0, x_6);
lean_ctor_set(x_12, 1, x_9);
lean_ctor_set(x_12, 2, x_10);
lean_ctor_set(x_12, 3, x_11);
if (x_8 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_box(x_8);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
lean_inc(x_12);
x_14 = lean_alloc_closure((void*)(l_Lean_resolveLocalName_loop___rarg___lambda__1___boxed), 11, 9);
lean_closure_set(x_14, 0, x_5);
lean_closure_set(x_14, 1, x_12);
lean_closure_set(x_14, 2, x_6);
lean_closure_set(x_14, 3, x_1);
lean_closure_set(x_14, 4, x_7);
lean_closure_set(x_14, 5, x_2);
lean_closure_set(x_14, 6, x_3);
lean_closure_set(x_14, 7, x_4);
lean_closure_set(x_14, 8, x_13);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
x_16 = l_Lean_MacroScopesView_review(x_12);
lean_inc(x_1);
x_17 = l_Lean_resolveGlobalName___rarg(x_1, x_2, x_3, x_16);
x_18 = lean_box(x_8);
lean_inc(x_15);
x_19 = lean_alloc_closure((void*)(l_Lean_resolveLocalName_loop___rarg___lambda__2___boxed), 5, 4);
lean_closure_set(x_19, 0, x_1);
lean_closure_set(x_19, 1, x_14);
lean_closure_set(x_19, 2, x_15);
lean_closure_set(x_19, 3, x_18);
x_20 = lean_apply_4(x_15, lean_box(0), lean_box(0), x_17, x_19);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_1, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_box(0);
x_25 = lean_apply_2(x_23, lean_box(0), x_24);
x_26 = lean_box(x_8);
x_27 = lean_box(x_8);
x_28 = lean_alloc_closure((void*)(l_Lean_resolveLocalName_loop___rarg___lambda__1___boxed), 11, 10);
lean_closure_set(x_28, 0, x_5);
lean_closure_set(x_28, 1, x_12);
lean_closure_set(x_28, 2, x_6);
lean_closure_set(x_28, 3, x_1);
lean_closure_set(x_28, 4, x_7);
lean_closure_set(x_28, 5, x_2);
lean_closure_set(x_28, 6, x_3);
lean_closure_set(x_28, 7, x_4);
lean_closure_set(x_28, 8, x_26);
lean_closure_set(x_28, 9, x_27);
x_29 = lean_apply_4(x_21, lean_box(0), lean_box(0), x_25, x_28);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName_loop(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_resolveLocalName_loop___rarg___boxed), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName_loop___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_9);
lean_dec(x_9);
x_13 = lean_unbox(x_10);
lean_dec(x_10);
x_14 = l_Lean_resolveLocalName_loop___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12, x_13, x_11);
lean_dec(x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName_loop___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_4);
lean_dec(x_4);
x_7 = l_Lean_resolveLocalName_loop___rarg___lambda__2(x_1, x_2, x_3, x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName_loop___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_8);
lean_dec(x_8);
x_10 = l_Lean_resolveLocalName_loop___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName_go___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = l_Lean_resolveLocalName_go(x_2, x_3, x_4, x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(0);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 3);
lean_inc(x_8);
lean_inc(x_4);
x_9 = l_Lean_Name_append(x_4, x_5);
x_10 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
lean_ctor_set(x_10, 2, x_7);
lean_ctor_set(x_10, 3, x_8);
x_11 = l_Lean_MacroScopesView_review(x_10);
x_12 = lean_name_eq(x_11, x_3);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
x_14 = l_Lean_resolveLocalName_go___lambda__1(x_4, x_1, x_2, x_3, x_13);
return x_14;
}
else
{
lean_object* x_15; 
lean_dec(x_4);
lean_dec(x_2);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_1);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName_go___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_resolveLocalName_go___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_resolveLocalName_go(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_resolveLocalName___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_7, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_7, x_11);
lean_dec(x_7);
x_13 = lean_array_fget(x_6, x_12);
if (lean_obj_tag(x_13) == 0)
{
x_7 = x_12;
x_8 = lean_box(0);
goto _start;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_13, 0);
x_17 = l_Lean_LocalDecl_isAuxDecl(x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = l_Lean_LocalDecl_userName(x_16);
x_19 = lean_name_eq(x_18, x_5);
lean_dec(x_18);
if (x_19 == 0)
{
lean_free_object(x_13);
lean_dec(x_16);
x_7 = x_12;
x_8 = lean_box(0);
goto _start;
}
else
{
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
else
{
if (x_4 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = l_Lean_LocalDecl_fvarId(x_16);
x_22 = l_Lean_RBNode_find___at_Lean_instantiateLCtxMVars___spec__1(x_1, x_21);
lean_dec(x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = l_Lean_LocalDecl_userName(x_16);
x_24 = lean_name_eq(x_23, x_5);
lean_dec(x_23);
if (x_24 == 0)
{
lean_free_object(x_13);
lean_dec(x_16);
x_7 = x_12;
x_8 = lean_box(0);
goto _start;
}
else
{
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
else
{
uint8_t x_26; 
lean_free_object(x_13);
x_26 = !lean_is_exclusive(x_22);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_22, 0);
x_28 = l_Lean_extractMacroScopes(x_27);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
x_31 = lean_private_to_user_name(x_30);
x_32 = l_Lean_LocalDecl_userName(x_16);
x_33 = l_Lean_extractMacroScopes(x_32);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_34; uint8_t x_35; 
lean_inc(x_28);
x_34 = l_Lean_MacroScopesView_review(x_28);
x_35 = l_Lean_Name_isPrefixOf(x_2, x_34);
if (x_35 == 0)
{
lean_object* x_36; 
lean_dec(x_28);
lean_dec(x_33);
lean_free_object(x_22);
lean_inc(x_2);
lean_inc(x_3);
x_36 = l_Lean_resolveLocalName_go(x_16, x_3, x_34, x_2);
lean_dec(x_34);
if (lean_obj_tag(x_36) == 0)
{
x_7 = x_12;
x_8 = lean_box(0);
goto _start;
}
else
{
uint8_t x_38; 
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
x_38 = !lean_is_exclusive(x_36);
if (x_38 == 0)
{
return x_36;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_36, 0);
lean_inc(x_39);
lean_dec(x_36);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
return x_40;
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_34);
x_41 = l_Lean_MacroScopesView_isSuffixOf(x_33, x_3);
lean_dec(x_33);
if (x_41 == 0)
{
lean_dec(x_28);
lean_free_object(x_22);
lean_dec(x_16);
x_7 = x_12;
x_8 = lean_box(0);
goto _start;
}
else
{
uint8_t x_43; 
x_43 = l_Lean_MacroScopesView_isSuffixOf(x_3, x_28);
lean_dec(x_28);
if (x_43 == 0)
{
lean_free_object(x_22);
lean_dec(x_16);
x_7 = x_12;
x_8 = lean_box(0);
goto _start;
}
else
{
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
lean_ctor_set(x_22, 0, x_16);
return x_22;
}
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_30);
lean_free_object(x_22);
x_45 = !lean_is_exclusive(x_31);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_46 = lean_ctor_get(x_31, 0);
lean_ctor_set(x_28, 0, x_46);
lean_inc(x_28);
x_47 = l_Lean_MacroScopesView_review(x_28);
x_48 = l_Lean_Name_isPrefixOf(x_2, x_47);
if (x_48 == 0)
{
lean_object* x_49; 
lean_dec(x_28);
lean_free_object(x_31);
lean_dec(x_33);
lean_inc(x_2);
lean_inc(x_3);
x_49 = l_Lean_resolveLocalName_go(x_16, x_3, x_47, x_2);
lean_dec(x_47);
if (lean_obj_tag(x_49) == 0)
{
x_7 = x_12;
x_8 = lean_box(0);
goto _start;
}
else
{
uint8_t x_51; 
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
x_51 = !lean_is_exclusive(x_49);
if (x_51 == 0)
{
return x_49;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_49, 0);
lean_inc(x_52);
lean_dec(x_49);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_52);
return x_53;
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_47);
x_54 = l_Lean_MacroScopesView_isSuffixOf(x_33, x_3);
lean_dec(x_33);
if (x_54 == 0)
{
lean_dec(x_28);
lean_free_object(x_31);
lean_dec(x_16);
x_7 = x_12;
x_8 = lean_box(0);
goto _start;
}
else
{
uint8_t x_56; 
x_56 = l_Lean_MacroScopesView_isSuffixOf(x_3, x_28);
lean_dec(x_28);
if (x_56 == 0)
{
lean_free_object(x_31);
lean_dec(x_16);
x_7 = x_12;
x_8 = lean_box(0);
goto _start;
}
else
{
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
lean_ctor_set(x_31, 0, x_16);
return x_31;
}
}
}
}
else
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_58 = lean_ctor_get(x_31, 0);
lean_inc(x_58);
lean_dec(x_31);
lean_ctor_set(x_28, 0, x_58);
lean_inc(x_28);
x_59 = l_Lean_MacroScopesView_review(x_28);
x_60 = l_Lean_Name_isPrefixOf(x_2, x_59);
if (x_60 == 0)
{
lean_object* x_61; 
lean_dec(x_28);
lean_dec(x_33);
lean_inc(x_2);
lean_inc(x_3);
x_61 = l_Lean_resolveLocalName_go(x_16, x_3, x_59, x_2);
lean_dec(x_59);
if (lean_obj_tag(x_61) == 0)
{
x_7 = x_12;
x_8 = lean_box(0);
goto _start;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
x_63 = lean_ctor_get(x_61, 0);
lean_inc(x_63);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 x_64 = x_61;
} else {
 lean_dec_ref(x_61);
 x_64 = lean_box(0);
}
if (lean_is_scalar(x_64)) {
 x_65 = lean_alloc_ctor(1, 1, 0);
} else {
 x_65 = x_64;
}
lean_ctor_set(x_65, 0, x_63);
return x_65;
}
}
else
{
uint8_t x_66; 
lean_dec(x_59);
x_66 = l_Lean_MacroScopesView_isSuffixOf(x_33, x_3);
lean_dec(x_33);
if (x_66 == 0)
{
lean_dec(x_28);
lean_dec(x_16);
x_7 = x_12;
x_8 = lean_box(0);
goto _start;
}
else
{
uint8_t x_68; 
x_68 = l_Lean_MacroScopesView_isSuffixOf(x_3, x_28);
lean_dec(x_28);
if (x_68 == 0)
{
lean_dec(x_16);
x_7 = x_12;
x_8 = lean_box(0);
goto _start;
}
else
{
lean_object* x_70; 
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_16);
return x_70;
}
}
}
}
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_71 = lean_ctor_get(x_28, 0);
x_72 = lean_ctor_get(x_28, 1);
x_73 = lean_ctor_get(x_28, 2);
x_74 = lean_ctor_get(x_28, 3);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_28);
lean_inc(x_71);
x_75 = lean_private_to_user_name(x_71);
x_76 = l_Lean_LocalDecl_userName(x_16);
x_77 = l_Lean_extractMacroScopes(x_76);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_78 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_78, 0, x_71);
lean_ctor_set(x_78, 1, x_72);
lean_ctor_set(x_78, 2, x_73);
lean_ctor_set(x_78, 3, x_74);
lean_inc(x_78);
x_79 = l_Lean_MacroScopesView_review(x_78);
x_80 = l_Lean_Name_isPrefixOf(x_2, x_79);
if (x_80 == 0)
{
lean_object* x_81; 
lean_dec(x_78);
lean_dec(x_77);
lean_free_object(x_22);
lean_inc(x_2);
lean_inc(x_3);
x_81 = l_Lean_resolveLocalName_go(x_16, x_3, x_79, x_2);
lean_dec(x_79);
if (lean_obj_tag(x_81) == 0)
{
x_7 = x_12;
x_8 = lean_box(0);
goto _start;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
x_83 = lean_ctor_get(x_81, 0);
lean_inc(x_83);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 x_84 = x_81;
} else {
 lean_dec_ref(x_81);
 x_84 = lean_box(0);
}
if (lean_is_scalar(x_84)) {
 x_85 = lean_alloc_ctor(1, 1, 0);
} else {
 x_85 = x_84;
}
lean_ctor_set(x_85, 0, x_83);
return x_85;
}
}
else
{
uint8_t x_86; 
lean_dec(x_79);
x_86 = l_Lean_MacroScopesView_isSuffixOf(x_77, x_3);
lean_dec(x_77);
if (x_86 == 0)
{
lean_dec(x_78);
lean_free_object(x_22);
lean_dec(x_16);
x_7 = x_12;
x_8 = lean_box(0);
goto _start;
}
else
{
uint8_t x_88; 
x_88 = l_Lean_MacroScopesView_isSuffixOf(x_3, x_78);
lean_dec(x_78);
if (x_88 == 0)
{
lean_free_object(x_22);
lean_dec(x_16);
x_7 = x_12;
x_8 = lean_box(0);
goto _start;
}
else
{
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
lean_ctor_set(x_22, 0, x_16);
return x_22;
}
}
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; 
lean_dec(x_71);
lean_free_object(x_22);
x_90 = lean_ctor_get(x_75, 0);
lean_inc(x_90);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 x_91 = x_75;
} else {
 lean_dec_ref(x_75);
 x_91 = lean_box(0);
}
x_92 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_72);
lean_ctor_set(x_92, 2, x_73);
lean_ctor_set(x_92, 3, x_74);
lean_inc(x_92);
x_93 = l_Lean_MacroScopesView_review(x_92);
x_94 = l_Lean_Name_isPrefixOf(x_2, x_93);
if (x_94 == 0)
{
lean_object* x_95; 
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_77);
lean_inc(x_2);
lean_inc(x_3);
x_95 = l_Lean_resolveLocalName_go(x_16, x_3, x_93, x_2);
lean_dec(x_93);
if (lean_obj_tag(x_95) == 0)
{
x_7 = x_12;
x_8 = lean_box(0);
goto _start;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
x_97 = lean_ctor_get(x_95, 0);
lean_inc(x_97);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 x_98 = x_95;
} else {
 lean_dec_ref(x_95);
 x_98 = lean_box(0);
}
if (lean_is_scalar(x_98)) {
 x_99 = lean_alloc_ctor(1, 1, 0);
} else {
 x_99 = x_98;
}
lean_ctor_set(x_99, 0, x_97);
return x_99;
}
}
else
{
uint8_t x_100; 
lean_dec(x_93);
x_100 = l_Lean_MacroScopesView_isSuffixOf(x_77, x_3);
lean_dec(x_77);
if (x_100 == 0)
{
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_16);
x_7 = x_12;
x_8 = lean_box(0);
goto _start;
}
else
{
uint8_t x_102; 
x_102 = l_Lean_MacroScopesView_isSuffixOf(x_3, x_92);
lean_dec(x_92);
if (x_102 == 0)
{
lean_dec(x_91);
lean_dec(x_16);
x_7 = x_12;
x_8 = lean_box(0);
goto _start;
}
else
{
lean_object* x_104; 
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
if (lean_is_scalar(x_91)) {
 x_104 = lean_alloc_ctor(1, 1, 0);
} else {
 x_104 = x_91;
}
lean_ctor_set(x_104, 0, x_16);
return x_104;
}
}
}
}
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_105 = lean_ctor_get(x_22, 0);
lean_inc(x_105);
lean_dec(x_22);
x_106 = l_Lean_extractMacroScopes(x_105);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
x_109 = lean_ctor_get(x_106, 2);
lean_inc(x_109);
x_110 = lean_ctor_get(x_106, 3);
lean_inc(x_110);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 lean_ctor_release(x_106, 2);
 lean_ctor_release(x_106, 3);
 x_111 = x_106;
} else {
 lean_dec_ref(x_106);
 x_111 = lean_box(0);
}
lean_inc(x_107);
x_112 = lean_private_to_user_name(x_107);
x_113 = l_Lean_LocalDecl_userName(x_16);
x_114 = l_Lean_extractMacroScopes(x_113);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_115; lean_object* x_116; uint8_t x_117; 
if (lean_is_scalar(x_111)) {
 x_115 = lean_alloc_ctor(0, 4, 0);
} else {
 x_115 = x_111;
}
lean_ctor_set(x_115, 0, x_107);
lean_ctor_set(x_115, 1, x_108);
lean_ctor_set(x_115, 2, x_109);
lean_ctor_set(x_115, 3, x_110);
lean_inc(x_115);
x_116 = l_Lean_MacroScopesView_review(x_115);
x_117 = l_Lean_Name_isPrefixOf(x_2, x_116);
if (x_117 == 0)
{
lean_object* x_118; 
lean_dec(x_115);
lean_dec(x_114);
lean_inc(x_2);
lean_inc(x_3);
x_118 = l_Lean_resolveLocalName_go(x_16, x_3, x_116, x_2);
lean_dec(x_116);
if (lean_obj_tag(x_118) == 0)
{
x_7 = x_12;
x_8 = lean_box(0);
goto _start;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
x_120 = lean_ctor_get(x_118, 0);
lean_inc(x_120);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 x_121 = x_118;
} else {
 lean_dec_ref(x_118);
 x_121 = lean_box(0);
}
if (lean_is_scalar(x_121)) {
 x_122 = lean_alloc_ctor(1, 1, 0);
} else {
 x_122 = x_121;
}
lean_ctor_set(x_122, 0, x_120);
return x_122;
}
}
else
{
uint8_t x_123; 
lean_dec(x_116);
x_123 = l_Lean_MacroScopesView_isSuffixOf(x_114, x_3);
lean_dec(x_114);
if (x_123 == 0)
{
lean_dec(x_115);
lean_dec(x_16);
x_7 = x_12;
x_8 = lean_box(0);
goto _start;
}
else
{
uint8_t x_125; 
x_125 = l_Lean_MacroScopesView_isSuffixOf(x_3, x_115);
lean_dec(x_115);
if (x_125 == 0)
{
lean_dec(x_16);
x_7 = x_12;
x_8 = lean_box(0);
goto _start;
}
else
{
lean_object* x_127; 
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
x_127 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_127, 0, x_16);
return x_127;
}
}
}
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; 
lean_dec(x_107);
x_128 = lean_ctor_get(x_112, 0);
lean_inc(x_128);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 x_129 = x_112;
} else {
 lean_dec_ref(x_112);
 x_129 = lean_box(0);
}
if (lean_is_scalar(x_111)) {
 x_130 = lean_alloc_ctor(0, 4, 0);
} else {
 x_130 = x_111;
}
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_108);
lean_ctor_set(x_130, 2, x_109);
lean_ctor_set(x_130, 3, x_110);
lean_inc(x_130);
x_131 = l_Lean_MacroScopesView_review(x_130);
x_132 = l_Lean_Name_isPrefixOf(x_2, x_131);
if (x_132 == 0)
{
lean_object* x_133; 
lean_dec(x_130);
lean_dec(x_129);
lean_dec(x_114);
lean_inc(x_2);
lean_inc(x_3);
x_133 = l_Lean_resolveLocalName_go(x_16, x_3, x_131, x_2);
lean_dec(x_131);
if (lean_obj_tag(x_133) == 0)
{
x_7 = x_12;
x_8 = lean_box(0);
goto _start;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
x_135 = lean_ctor_get(x_133, 0);
lean_inc(x_135);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 x_136 = x_133;
} else {
 lean_dec_ref(x_133);
 x_136 = lean_box(0);
}
if (lean_is_scalar(x_136)) {
 x_137 = lean_alloc_ctor(1, 1, 0);
} else {
 x_137 = x_136;
}
lean_ctor_set(x_137, 0, x_135);
return x_137;
}
}
else
{
uint8_t x_138; 
lean_dec(x_131);
x_138 = l_Lean_MacroScopesView_isSuffixOf(x_114, x_3);
lean_dec(x_114);
if (x_138 == 0)
{
lean_dec(x_130);
lean_dec(x_129);
lean_dec(x_16);
x_7 = x_12;
x_8 = lean_box(0);
goto _start;
}
else
{
uint8_t x_140; 
x_140 = l_Lean_MacroScopesView_isSuffixOf(x_3, x_130);
lean_dec(x_130);
if (x_140 == 0)
{
lean_dec(x_129);
lean_dec(x_16);
x_7 = x_12;
x_8 = lean_box(0);
goto _start;
}
else
{
lean_object* x_142; 
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
if (lean_is_scalar(x_129)) {
 x_142 = lean_alloc_ctor(1, 1, 0);
} else {
 x_142 = x_129;
}
lean_ctor_set(x_142, 0, x_16);
return x_142;
}
}
}
}
}
}
}
else
{
lean_free_object(x_13);
lean_dec(x_16);
x_7 = x_12;
x_8 = lean_box(0);
goto _start;
}
}
}
else
{
lean_object* x_144; uint8_t x_145; 
x_144 = lean_ctor_get(x_13, 0);
lean_inc(x_144);
lean_dec(x_13);
x_145 = l_Lean_LocalDecl_isAuxDecl(x_144);
if (x_145 == 0)
{
lean_object* x_146; uint8_t x_147; 
x_146 = l_Lean_LocalDecl_userName(x_144);
x_147 = lean_name_eq(x_146, x_5);
lean_dec(x_146);
if (x_147 == 0)
{
lean_dec(x_144);
x_7 = x_12;
x_8 = lean_box(0);
goto _start;
}
else
{
lean_object* x_149; 
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
x_149 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_149, 0, x_144);
return x_149;
}
}
else
{
if (x_4 == 0)
{
lean_object* x_150; lean_object* x_151; 
x_150 = l_Lean_LocalDecl_fvarId(x_144);
x_151 = l_Lean_RBNode_find___at_Lean_instantiateLCtxMVars___spec__1(x_1, x_150);
lean_dec(x_150);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; uint8_t x_153; 
x_152 = l_Lean_LocalDecl_userName(x_144);
x_153 = lean_name_eq(x_152, x_5);
lean_dec(x_152);
if (x_153 == 0)
{
lean_dec(x_144);
x_7 = x_12;
x_8 = lean_box(0);
goto _start;
}
else
{
lean_object* x_155; 
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
x_155 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_155, 0, x_144);
return x_155;
}
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_156 = lean_ctor_get(x_151, 0);
lean_inc(x_156);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 x_157 = x_151;
} else {
 lean_dec_ref(x_151);
 x_157 = lean_box(0);
}
x_158 = l_Lean_extractMacroScopes(x_156);
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_158, 1);
lean_inc(x_160);
x_161 = lean_ctor_get(x_158, 2);
lean_inc(x_161);
x_162 = lean_ctor_get(x_158, 3);
lean_inc(x_162);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 lean_ctor_release(x_158, 2);
 lean_ctor_release(x_158, 3);
 x_163 = x_158;
} else {
 lean_dec_ref(x_158);
 x_163 = lean_box(0);
}
lean_inc(x_159);
x_164 = lean_private_to_user_name(x_159);
x_165 = l_Lean_LocalDecl_userName(x_144);
x_166 = l_Lean_extractMacroScopes(x_165);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_167; lean_object* x_168; uint8_t x_169; 
if (lean_is_scalar(x_163)) {
 x_167 = lean_alloc_ctor(0, 4, 0);
} else {
 x_167 = x_163;
}
lean_ctor_set(x_167, 0, x_159);
lean_ctor_set(x_167, 1, x_160);
lean_ctor_set(x_167, 2, x_161);
lean_ctor_set(x_167, 3, x_162);
lean_inc(x_167);
x_168 = l_Lean_MacroScopesView_review(x_167);
x_169 = l_Lean_Name_isPrefixOf(x_2, x_168);
if (x_169 == 0)
{
lean_object* x_170; 
lean_dec(x_167);
lean_dec(x_166);
lean_dec(x_157);
lean_inc(x_2);
lean_inc(x_3);
x_170 = l_Lean_resolveLocalName_go(x_144, x_3, x_168, x_2);
lean_dec(x_168);
if (lean_obj_tag(x_170) == 0)
{
x_7 = x_12;
x_8 = lean_box(0);
goto _start;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
x_172 = lean_ctor_get(x_170, 0);
lean_inc(x_172);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 x_173 = x_170;
} else {
 lean_dec_ref(x_170);
 x_173 = lean_box(0);
}
if (lean_is_scalar(x_173)) {
 x_174 = lean_alloc_ctor(1, 1, 0);
} else {
 x_174 = x_173;
}
lean_ctor_set(x_174, 0, x_172);
return x_174;
}
}
else
{
uint8_t x_175; 
lean_dec(x_168);
x_175 = l_Lean_MacroScopesView_isSuffixOf(x_166, x_3);
lean_dec(x_166);
if (x_175 == 0)
{
lean_dec(x_167);
lean_dec(x_157);
lean_dec(x_144);
x_7 = x_12;
x_8 = lean_box(0);
goto _start;
}
else
{
uint8_t x_177; 
x_177 = l_Lean_MacroScopesView_isSuffixOf(x_3, x_167);
lean_dec(x_167);
if (x_177 == 0)
{
lean_dec(x_157);
lean_dec(x_144);
x_7 = x_12;
x_8 = lean_box(0);
goto _start;
}
else
{
lean_object* x_179; 
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
if (lean_is_scalar(x_157)) {
 x_179 = lean_alloc_ctor(1, 1, 0);
} else {
 x_179 = x_157;
}
lean_ctor_set(x_179, 0, x_144);
return x_179;
}
}
}
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; uint8_t x_184; 
lean_dec(x_159);
lean_dec(x_157);
x_180 = lean_ctor_get(x_164, 0);
lean_inc(x_180);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 x_181 = x_164;
} else {
 lean_dec_ref(x_164);
 x_181 = lean_box(0);
}
if (lean_is_scalar(x_163)) {
 x_182 = lean_alloc_ctor(0, 4, 0);
} else {
 x_182 = x_163;
}
lean_ctor_set(x_182, 0, x_180);
lean_ctor_set(x_182, 1, x_160);
lean_ctor_set(x_182, 2, x_161);
lean_ctor_set(x_182, 3, x_162);
lean_inc(x_182);
x_183 = l_Lean_MacroScopesView_review(x_182);
x_184 = l_Lean_Name_isPrefixOf(x_2, x_183);
if (x_184 == 0)
{
lean_object* x_185; 
lean_dec(x_182);
lean_dec(x_181);
lean_dec(x_166);
lean_inc(x_2);
lean_inc(x_3);
x_185 = l_Lean_resolveLocalName_go(x_144, x_3, x_183, x_2);
lean_dec(x_183);
if (lean_obj_tag(x_185) == 0)
{
x_7 = x_12;
x_8 = lean_box(0);
goto _start;
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; 
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
x_187 = lean_ctor_get(x_185, 0);
lean_inc(x_187);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 x_188 = x_185;
} else {
 lean_dec_ref(x_185);
 x_188 = lean_box(0);
}
if (lean_is_scalar(x_188)) {
 x_189 = lean_alloc_ctor(1, 1, 0);
} else {
 x_189 = x_188;
}
lean_ctor_set(x_189, 0, x_187);
return x_189;
}
}
else
{
uint8_t x_190; 
lean_dec(x_183);
x_190 = l_Lean_MacroScopesView_isSuffixOf(x_166, x_3);
lean_dec(x_166);
if (x_190 == 0)
{
lean_dec(x_182);
lean_dec(x_181);
lean_dec(x_144);
x_7 = x_12;
x_8 = lean_box(0);
goto _start;
}
else
{
uint8_t x_192; 
x_192 = l_Lean_MacroScopesView_isSuffixOf(x_3, x_182);
lean_dec(x_182);
if (x_192 == 0)
{
lean_dec(x_181);
lean_dec(x_144);
x_7 = x_12;
x_8 = lean_box(0);
goto _start;
}
else
{
lean_object* x_194; 
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
if (lean_is_scalar(x_181)) {
 x_194 = lean_alloc_ctor(1, 1, 0);
} else {
 x_194 = x_181;
}
lean_ctor_set(x_194, 0, x_144);
return x_194;
}
}
}
}
}
}
else
{
lean_dec(x_144);
x_7 = x_12;
x_8 = lean_box(0);
goto _start;
}
}
}
}
}
else
{
lean_object* x_196; 
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_196 = lean_box(0);
return x_196;
}
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_resolveLocalName___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_7, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_7, x_11);
lean_dec(x_7);
x_13 = lean_array_fget(x_6, x_12);
lean_inc(x_3);
lean_inc(x_2);
x_14 = l_Lean_PersistentArray_findSomeRevMAux___at_Lean_resolveLocalName___spec__3(x_1, x_2, x_3, x_4, x_5, x_13);
lean_dec(x_13);
if (lean_obj_tag(x_14) == 0)
{
x_7 = x_12;
x_8 = lean_box(0);
goto _start;
}
else
{
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
return x_14;
}
}
else
{
lean_object* x_16; 
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_16 = lean_box(0);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_resolveLocalName___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_7, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_7, x_11);
lean_dec(x_7);
x_13 = lean_array_fget(x_6, x_12);
if (lean_obj_tag(x_13) == 0)
{
x_7 = x_12;
x_8 = lean_box(0);
goto _start;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_13, 0);
x_17 = l_Lean_LocalDecl_isAuxDecl(x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = l_Lean_LocalDecl_userName(x_16);
x_19 = lean_name_eq(x_18, x_5);
lean_dec(x_18);
if (x_19 == 0)
{
lean_free_object(x_13);
lean_dec(x_16);
x_7 = x_12;
x_8 = lean_box(0);
goto _start;
}
else
{
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
else
{
if (x_4 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = l_Lean_LocalDecl_fvarId(x_16);
x_22 = l_Lean_RBNode_find___at_Lean_instantiateLCtxMVars___spec__1(x_1, x_21);
lean_dec(x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = l_Lean_LocalDecl_userName(x_16);
x_24 = lean_name_eq(x_23, x_5);
lean_dec(x_23);
if (x_24 == 0)
{
lean_free_object(x_13);
lean_dec(x_16);
x_7 = x_12;
x_8 = lean_box(0);
goto _start;
}
else
{
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
else
{
uint8_t x_26; 
lean_free_object(x_13);
x_26 = !lean_is_exclusive(x_22);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_22, 0);
x_28 = l_Lean_extractMacroScopes(x_27);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
x_31 = lean_private_to_user_name(x_30);
x_32 = l_Lean_LocalDecl_userName(x_16);
x_33 = l_Lean_extractMacroScopes(x_32);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_34; uint8_t x_35; 
lean_inc(x_28);
x_34 = l_Lean_MacroScopesView_review(x_28);
x_35 = l_Lean_Name_isPrefixOf(x_2, x_34);
if (x_35 == 0)
{
lean_object* x_36; 
lean_dec(x_28);
lean_dec(x_33);
lean_free_object(x_22);
lean_inc(x_2);
lean_inc(x_3);
x_36 = l_Lean_resolveLocalName_go(x_16, x_3, x_34, x_2);
lean_dec(x_34);
if (lean_obj_tag(x_36) == 0)
{
x_7 = x_12;
x_8 = lean_box(0);
goto _start;
}
else
{
uint8_t x_38; 
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
x_38 = !lean_is_exclusive(x_36);
if (x_38 == 0)
{
return x_36;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_36, 0);
lean_inc(x_39);
lean_dec(x_36);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
return x_40;
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_34);
x_41 = l_Lean_MacroScopesView_isSuffixOf(x_33, x_3);
lean_dec(x_33);
if (x_41 == 0)
{
lean_dec(x_28);
lean_free_object(x_22);
lean_dec(x_16);
x_7 = x_12;
x_8 = lean_box(0);
goto _start;
}
else
{
uint8_t x_43; 
x_43 = l_Lean_MacroScopesView_isSuffixOf(x_3, x_28);
lean_dec(x_28);
if (x_43 == 0)
{
lean_free_object(x_22);
lean_dec(x_16);
x_7 = x_12;
x_8 = lean_box(0);
goto _start;
}
else
{
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
lean_ctor_set(x_22, 0, x_16);
return x_22;
}
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_30);
lean_free_object(x_22);
x_45 = !lean_is_exclusive(x_31);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_46 = lean_ctor_get(x_31, 0);
lean_ctor_set(x_28, 0, x_46);
lean_inc(x_28);
x_47 = l_Lean_MacroScopesView_review(x_28);
x_48 = l_Lean_Name_isPrefixOf(x_2, x_47);
if (x_48 == 0)
{
lean_object* x_49; 
lean_dec(x_28);
lean_free_object(x_31);
lean_dec(x_33);
lean_inc(x_2);
lean_inc(x_3);
x_49 = l_Lean_resolveLocalName_go(x_16, x_3, x_47, x_2);
lean_dec(x_47);
if (lean_obj_tag(x_49) == 0)
{
x_7 = x_12;
x_8 = lean_box(0);
goto _start;
}
else
{
uint8_t x_51; 
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
x_51 = !lean_is_exclusive(x_49);
if (x_51 == 0)
{
return x_49;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_49, 0);
lean_inc(x_52);
lean_dec(x_49);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_52);
return x_53;
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_47);
x_54 = l_Lean_MacroScopesView_isSuffixOf(x_33, x_3);
lean_dec(x_33);
if (x_54 == 0)
{
lean_dec(x_28);
lean_free_object(x_31);
lean_dec(x_16);
x_7 = x_12;
x_8 = lean_box(0);
goto _start;
}
else
{
uint8_t x_56; 
x_56 = l_Lean_MacroScopesView_isSuffixOf(x_3, x_28);
lean_dec(x_28);
if (x_56 == 0)
{
lean_free_object(x_31);
lean_dec(x_16);
x_7 = x_12;
x_8 = lean_box(0);
goto _start;
}
else
{
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
lean_ctor_set(x_31, 0, x_16);
return x_31;
}
}
}
}
else
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_58 = lean_ctor_get(x_31, 0);
lean_inc(x_58);
lean_dec(x_31);
lean_ctor_set(x_28, 0, x_58);
lean_inc(x_28);
x_59 = l_Lean_MacroScopesView_review(x_28);
x_60 = l_Lean_Name_isPrefixOf(x_2, x_59);
if (x_60 == 0)
{
lean_object* x_61; 
lean_dec(x_28);
lean_dec(x_33);
lean_inc(x_2);
lean_inc(x_3);
x_61 = l_Lean_resolveLocalName_go(x_16, x_3, x_59, x_2);
lean_dec(x_59);
if (lean_obj_tag(x_61) == 0)
{
x_7 = x_12;
x_8 = lean_box(0);
goto _start;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
x_63 = lean_ctor_get(x_61, 0);
lean_inc(x_63);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 x_64 = x_61;
} else {
 lean_dec_ref(x_61);
 x_64 = lean_box(0);
}
if (lean_is_scalar(x_64)) {
 x_65 = lean_alloc_ctor(1, 1, 0);
} else {
 x_65 = x_64;
}
lean_ctor_set(x_65, 0, x_63);
return x_65;
}
}
else
{
uint8_t x_66; 
lean_dec(x_59);
x_66 = l_Lean_MacroScopesView_isSuffixOf(x_33, x_3);
lean_dec(x_33);
if (x_66 == 0)
{
lean_dec(x_28);
lean_dec(x_16);
x_7 = x_12;
x_8 = lean_box(0);
goto _start;
}
else
{
uint8_t x_68; 
x_68 = l_Lean_MacroScopesView_isSuffixOf(x_3, x_28);
lean_dec(x_28);
if (x_68 == 0)
{
lean_dec(x_16);
x_7 = x_12;
x_8 = lean_box(0);
goto _start;
}
else
{
lean_object* x_70; 
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_16);
return x_70;
}
}
}
}
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_71 = lean_ctor_get(x_28, 0);
x_72 = lean_ctor_get(x_28, 1);
x_73 = lean_ctor_get(x_28, 2);
x_74 = lean_ctor_get(x_28, 3);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_28);
lean_inc(x_71);
x_75 = lean_private_to_user_name(x_71);
x_76 = l_Lean_LocalDecl_userName(x_16);
x_77 = l_Lean_extractMacroScopes(x_76);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_78 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_78, 0, x_71);
lean_ctor_set(x_78, 1, x_72);
lean_ctor_set(x_78, 2, x_73);
lean_ctor_set(x_78, 3, x_74);
lean_inc(x_78);
x_79 = l_Lean_MacroScopesView_review(x_78);
x_80 = l_Lean_Name_isPrefixOf(x_2, x_79);
if (x_80 == 0)
{
lean_object* x_81; 
lean_dec(x_78);
lean_dec(x_77);
lean_free_object(x_22);
lean_inc(x_2);
lean_inc(x_3);
x_81 = l_Lean_resolveLocalName_go(x_16, x_3, x_79, x_2);
lean_dec(x_79);
if (lean_obj_tag(x_81) == 0)
{
x_7 = x_12;
x_8 = lean_box(0);
goto _start;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
x_83 = lean_ctor_get(x_81, 0);
lean_inc(x_83);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 x_84 = x_81;
} else {
 lean_dec_ref(x_81);
 x_84 = lean_box(0);
}
if (lean_is_scalar(x_84)) {
 x_85 = lean_alloc_ctor(1, 1, 0);
} else {
 x_85 = x_84;
}
lean_ctor_set(x_85, 0, x_83);
return x_85;
}
}
else
{
uint8_t x_86; 
lean_dec(x_79);
x_86 = l_Lean_MacroScopesView_isSuffixOf(x_77, x_3);
lean_dec(x_77);
if (x_86 == 0)
{
lean_dec(x_78);
lean_free_object(x_22);
lean_dec(x_16);
x_7 = x_12;
x_8 = lean_box(0);
goto _start;
}
else
{
uint8_t x_88; 
x_88 = l_Lean_MacroScopesView_isSuffixOf(x_3, x_78);
lean_dec(x_78);
if (x_88 == 0)
{
lean_free_object(x_22);
lean_dec(x_16);
x_7 = x_12;
x_8 = lean_box(0);
goto _start;
}
else
{
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
lean_ctor_set(x_22, 0, x_16);
return x_22;
}
}
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; 
lean_dec(x_71);
lean_free_object(x_22);
x_90 = lean_ctor_get(x_75, 0);
lean_inc(x_90);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 x_91 = x_75;
} else {
 lean_dec_ref(x_75);
 x_91 = lean_box(0);
}
x_92 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_72);
lean_ctor_set(x_92, 2, x_73);
lean_ctor_set(x_92, 3, x_74);
lean_inc(x_92);
x_93 = l_Lean_MacroScopesView_review(x_92);
x_94 = l_Lean_Name_isPrefixOf(x_2, x_93);
if (x_94 == 0)
{
lean_object* x_95; 
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_77);
lean_inc(x_2);
lean_inc(x_3);
x_95 = l_Lean_resolveLocalName_go(x_16, x_3, x_93, x_2);
lean_dec(x_93);
if (lean_obj_tag(x_95) == 0)
{
x_7 = x_12;
x_8 = lean_box(0);
goto _start;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
x_97 = lean_ctor_get(x_95, 0);
lean_inc(x_97);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 x_98 = x_95;
} else {
 lean_dec_ref(x_95);
 x_98 = lean_box(0);
}
if (lean_is_scalar(x_98)) {
 x_99 = lean_alloc_ctor(1, 1, 0);
} else {
 x_99 = x_98;
}
lean_ctor_set(x_99, 0, x_97);
return x_99;
}
}
else
{
uint8_t x_100; 
lean_dec(x_93);
x_100 = l_Lean_MacroScopesView_isSuffixOf(x_77, x_3);
lean_dec(x_77);
if (x_100 == 0)
{
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_16);
x_7 = x_12;
x_8 = lean_box(0);
goto _start;
}
else
{
uint8_t x_102; 
x_102 = l_Lean_MacroScopesView_isSuffixOf(x_3, x_92);
lean_dec(x_92);
if (x_102 == 0)
{
lean_dec(x_91);
lean_dec(x_16);
x_7 = x_12;
x_8 = lean_box(0);
goto _start;
}
else
{
lean_object* x_104; 
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
if (lean_is_scalar(x_91)) {
 x_104 = lean_alloc_ctor(1, 1, 0);
} else {
 x_104 = x_91;
}
lean_ctor_set(x_104, 0, x_16);
return x_104;
}
}
}
}
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_105 = lean_ctor_get(x_22, 0);
lean_inc(x_105);
lean_dec(x_22);
x_106 = l_Lean_extractMacroScopes(x_105);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
x_109 = lean_ctor_get(x_106, 2);
lean_inc(x_109);
x_110 = lean_ctor_get(x_106, 3);
lean_inc(x_110);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 lean_ctor_release(x_106, 2);
 lean_ctor_release(x_106, 3);
 x_111 = x_106;
} else {
 lean_dec_ref(x_106);
 x_111 = lean_box(0);
}
lean_inc(x_107);
x_112 = lean_private_to_user_name(x_107);
x_113 = l_Lean_LocalDecl_userName(x_16);
x_114 = l_Lean_extractMacroScopes(x_113);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_115; lean_object* x_116; uint8_t x_117; 
if (lean_is_scalar(x_111)) {
 x_115 = lean_alloc_ctor(0, 4, 0);
} else {
 x_115 = x_111;
}
lean_ctor_set(x_115, 0, x_107);
lean_ctor_set(x_115, 1, x_108);
lean_ctor_set(x_115, 2, x_109);
lean_ctor_set(x_115, 3, x_110);
lean_inc(x_115);
x_116 = l_Lean_MacroScopesView_review(x_115);
x_117 = l_Lean_Name_isPrefixOf(x_2, x_116);
if (x_117 == 0)
{
lean_object* x_118; 
lean_dec(x_115);
lean_dec(x_114);
lean_inc(x_2);
lean_inc(x_3);
x_118 = l_Lean_resolveLocalName_go(x_16, x_3, x_116, x_2);
lean_dec(x_116);
if (lean_obj_tag(x_118) == 0)
{
x_7 = x_12;
x_8 = lean_box(0);
goto _start;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
x_120 = lean_ctor_get(x_118, 0);
lean_inc(x_120);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 x_121 = x_118;
} else {
 lean_dec_ref(x_118);
 x_121 = lean_box(0);
}
if (lean_is_scalar(x_121)) {
 x_122 = lean_alloc_ctor(1, 1, 0);
} else {
 x_122 = x_121;
}
lean_ctor_set(x_122, 0, x_120);
return x_122;
}
}
else
{
uint8_t x_123; 
lean_dec(x_116);
x_123 = l_Lean_MacroScopesView_isSuffixOf(x_114, x_3);
lean_dec(x_114);
if (x_123 == 0)
{
lean_dec(x_115);
lean_dec(x_16);
x_7 = x_12;
x_8 = lean_box(0);
goto _start;
}
else
{
uint8_t x_125; 
x_125 = l_Lean_MacroScopesView_isSuffixOf(x_3, x_115);
lean_dec(x_115);
if (x_125 == 0)
{
lean_dec(x_16);
x_7 = x_12;
x_8 = lean_box(0);
goto _start;
}
else
{
lean_object* x_127; 
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
x_127 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_127, 0, x_16);
return x_127;
}
}
}
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; 
lean_dec(x_107);
x_128 = lean_ctor_get(x_112, 0);
lean_inc(x_128);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 x_129 = x_112;
} else {
 lean_dec_ref(x_112);
 x_129 = lean_box(0);
}
if (lean_is_scalar(x_111)) {
 x_130 = lean_alloc_ctor(0, 4, 0);
} else {
 x_130 = x_111;
}
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_108);
lean_ctor_set(x_130, 2, x_109);
lean_ctor_set(x_130, 3, x_110);
lean_inc(x_130);
x_131 = l_Lean_MacroScopesView_review(x_130);
x_132 = l_Lean_Name_isPrefixOf(x_2, x_131);
if (x_132 == 0)
{
lean_object* x_133; 
lean_dec(x_130);
lean_dec(x_129);
lean_dec(x_114);
lean_inc(x_2);
lean_inc(x_3);
x_133 = l_Lean_resolveLocalName_go(x_16, x_3, x_131, x_2);
lean_dec(x_131);
if (lean_obj_tag(x_133) == 0)
{
x_7 = x_12;
x_8 = lean_box(0);
goto _start;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
x_135 = lean_ctor_get(x_133, 0);
lean_inc(x_135);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 x_136 = x_133;
} else {
 lean_dec_ref(x_133);
 x_136 = lean_box(0);
}
if (lean_is_scalar(x_136)) {
 x_137 = lean_alloc_ctor(1, 1, 0);
} else {
 x_137 = x_136;
}
lean_ctor_set(x_137, 0, x_135);
return x_137;
}
}
else
{
uint8_t x_138; 
lean_dec(x_131);
x_138 = l_Lean_MacroScopesView_isSuffixOf(x_114, x_3);
lean_dec(x_114);
if (x_138 == 0)
{
lean_dec(x_130);
lean_dec(x_129);
lean_dec(x_16);
x_7 = x_12;
x_8 = lean_box(0);
goto _start;
}
else
{
uint8_t x_140; 
x_140 = l_Lean_MacroScopesView_isSuffixOf(x_3, x_130);
lean_dec(x_130);
if (x_140 == 0)
{
lean_dec(x_129);
lean_dec(x_16);
x_7 = x_12;
x_8 = lean_box(0);
goto _start;
}
else
{
lean_object* x_142; 
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
if (lean_is_scalar(x_129)) {
 x_142 = lean_alloc_ctor(1, 1, 0);
} else {
 x_142 = x_129;
}
lean_ctor_set(x_142, 0, x_16);
return x_142;
}
}
}
}
}
}
}
else
{
lean_free_object(x_13);
lean_dec(x_16);
x_7 = x_12;
x_8 = lean_box(0);
goto _start;
}
}
}
else
{
lean_object* x_144; uint8_t x_145; 
x_144 = lean_ctor_get(x_13, 0);
lean_inc(x_144);
lean_dec(x_13);
x_145 = l_Lean_LocalDecl_isAuxDecl(x_144);
if (x_145 == 0)
{
lean_object* x_146; uint8_t x_147; 
x_146 = l_Lean_LocalDecl_userName(x_144);
x_147 = lean_name_eq(x_146, x_5);
lean_dec(x_146);
if (x_147 == 0)
{
lean_dec(x_144);
x_7 = x_12;
x_8 = lean_box(0);
goto _start;
}
else
{
lean_object* x_149; 
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
x_149 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_149, 0, x_144);
return x_149;
}
}
else
{
if (x_4 == 0)
{
lean_object* x_150; lean_object* x_151; 
x_150 = l_Lean_LocalDecl_fvarId(x_144);
x_151 = l_Lean_RBNode_find___at_Lean_instantiateLCtxMVars___spec__1(x_1, x_150);
lean_dec(x_150);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; uint8_t x_153; 
x_152 = l_Lean_LocalDecl_userName(x_144);
x_153 = lean_name_eq(x_152, x_5);
lean_dec(x_152);
if (x_153 == 0)
{
lean_dec(x_144);
x_7 = x_12;
x_8 = lean_box(0);
goto _start;
}
else
{
lean_object* x_155; 
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
x_155 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_155, 0, x_144);
return x_155;
}
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_156 = lean_ctor_get(x_151, 0);
lean_inc(x_156);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 x_157 = x_151;
} else {
 lean_dec_ref(x_151);
 x_157 = lean_box(0);
}
x_158 = l_Lean_extractMacroScopes(x_156);
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_158, 1);
lean_inc(x_160);
x_161 = lean_ctor_get(x_158, 2);
lean_inc(x_161);
x_162 = lean_ctor_get(x_158, 3);
lean_inc(x_162);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 lean_ctor_release(x_158, 2);
 lean_ctor_release(x_158, 3);
 x_163 = x_158;
} else {
 lean_dec_ref(x_158);
 x_163 = lean_box(0);
}
lean_inc(x_159);
x_164 = lean_private_to_user_name(x_159);
x_165 = l_Lean_LocalDecl_userName(x_144);
x_166 = l_Lean_extractMacroScopes(x_165);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_167; lean_object* x_168; uint8_t x_169; 
if (lean_is_scalar(x_163)) {
 x_167 = lean_alloc_ctor(0, 4, 0);
} else {
 x_167 = x_163;
}
lean_ctor_set(x_167, 0, x_159);
lean_ctor_set(x_167, 1, x_160);
lean_ctor_set(x_167, 2, x_161);
lean_ctor_set(x_167, 3, x_162);
lean_inc(x_167);
x_168 = l_Lean_MacroScopesView_review(x_167);
x_169 = l_Lean_Name_isPrefixOf(x_2, x_168);
if (x_169 == 0)
{
lean_object* x_170; 
lean_dec(x_167);
lean_dec(x_166);
lean_dec(x_157);
lean_inc(x_2);
lean_inc(x_3);
x_170 = l_Lean_resolveLocalName_go(x_144, x_3, x_168, x_2);
lean_dec(x_168);
if (lean_obj_tag(x_170) == 0)
{
x_7 = x_12;
x_8 = lean_box(0);
goto _start;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
x_172 = lean_ctor_get(x_170, 0);
lean_inc(x_172);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 x_173 = x_170;
} else {
 lean_dec_ref(x_170);
 x_173 = lean_box(0);
}
if (lean_is_scalar(x_173)) {
 x_174 = lean_alloc_ctor(1, 1, 0);
} else {
 x_174 = x_173;
}
lean_ctor_set(x_174, 0, x_172);
return x_174;
}
}
else
{
uint8_t x_175; 
lean_dec(x_168);
x_175 = l_Lean_MacroScopesView_isSuffixOf(x_166, x_3);
lean_dec(x_166);
if (x_175 == 0)
{
lean_dec(x_167);
lean_dec(x_157);
lean_dec(x_144);
x_7 = x_12;
x_8 = lean_box(0);
goto _start;
}
else
{
uint8_t x_177; 
x_177 = l_Lean_MacroScopesView_isSuffixOf(x_3, x_167);
lean_dec(x_167);
if (x_177 == 0)
{
lean_dec(x_157);
lean_dec(x_144);
x_7 = x_12;
x_8 = lean_box(0);
goto _start;
}
else
{
lean_object* x_179; 
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
if (lean_is_scalar(x_157)) {
 x_179 = lean_alloc_ctor(1, 1, 0);
} else {
 x_179 = x_157;
}
lean_ctor_set(x_179, 0, x_144);
return x_179;
}
}
}
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; uint8_t x_184; 
lean_dec(x_159);
lean_dec(x_157);
x_180 = lean_ctor_get(x_164, 0);
lean_inc(x_180);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 x_181 = x_164;
} else {
 lean_dec_ref(x_164);
 x_181 = lean_box(0);
}
if (lean_is_scalar(x_163)) {
 x_182 = lean_alloc_ctor(0, 4, 0);
} else {
 x_182 = x_163;
}
lean_ctor_set(x_182, 0, x_180);
lean_ctor_set(x_182, 1, x_160);
lean_ctor_set(x_182, 2, x_161);
lean_ctor_set(x_182, 3, x_162);
lean_inc(x_182);
x_183 = l_Lean_MacroScopesView_review(x_182);
x_184 = l_Lean_Name_isPrefixOf(x_2, x_183);
if (x_184 == 0)
{
lean_object* x_185; 
lean_dec(x_182);
lean_dec(x_181);
lean_dec(x_166);
lean_inc(x_2);
lean_inc(x_3);
x_185 = l_Lean_resolveLocalName_go(x_144, x_3, x_183, x_2);
lean_dec(x_183);
if (lean_obj_tag(x_185) == 0)
{
x_7 = x_12;
x_8 = lean_box(0);
goto _start;
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; 
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
x_187 = lean_ctor_get(x_185, 0);
lean_inc(x_187);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 x_188 = x_185;
} else {
 lean_dec_ref(x_185);
 x_188 = lean_box(0);
}
if (lean_is_scalar(x_188)) {
 x_189 = lean_alloc_ctor(1, 1, 0);
} else {
 x_189 = x_188;
}
lean_ctor_set(x_189, 0, x_187);
return x_189;
}
}
else
{
uint8_t x_190; 
lean_dec(x_183);
x_190 = l_Lean_MacroScopesView_isSuffixOf(x_166, x_3);
lean_dec(x_166);
if (x_190 == 0)
{
lean_dec(x_182);
lean_dec(x_181);
lean_dec(x_144);
x_7 = x_12;
x_8 = lean_box(0);
goto _start;
}
else
{
uint8_t x_192; 
x_192 = l_Lean_MacroScopesView_isSuffixOf(x_3, x_182);
lean_dec(x_182);
if (x_192 == 0)
{
lean_dec(x_181);
lean_dec(x_144);
x_7 = x_12;
x_8 = lean_box(0);
goto _start;
}
else
{
lean_object* x_194; 
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
if (lean_is_scalar(x_181)) {
 x_194 = lean_alloc_ctor(1, 1, 0);
} else {
 x_194 = x_181;
}
lean_ctor_set(x_194, 0, x_144);
return x_194;
}
}
}
}
}
}
else
{
lean_dec(x_144);
x_7 = x_12;
x_8 = lean_box(0);
goto _start;
}
}
}
}
}
else
{
lean_object* x_196; 
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_196 = lean_box(0);
return x_196;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at_Lean_resolveLocalName___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 0);
x_8 = lean_array_get_size(x_7);
x_9 = l_Array_findSomeRevM_x3f_find___at_Lean_resolveLocalName___spec__4(x_1, x_2, x_3, x_4, x_5, x_7, x_8, lean_box(0));
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_6, 0);
x_11 = lean_array_get_size(x_10);
x_12 = l_Array_findSomeRevM_x3f_find___at_Lean_resolveLocalName___spec__5(x_1, x_2, x_3, x_4, x_5, x_10, x_11, lean_box(0));
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at_Lean_resolveLocalName___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 1);
x_8 = lean_array_get_size(x_7);
lean_inc(x_3);
lean_inc(x_2);
x_9 = l_Array_findSomeRevM_x3f_find___at_Lean_resolveLocalName___spec__2(x_1, x_2, x_3, x_4, x_5, x_7, x_8, lean_box(0));
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_6, 0);
x_11 = l_Lean_PersistentArray_findSomeRevMAux___at_Lean_resolveLocalName___spec__3(x_1, x_2, x_3, x_4, x_5, x_10);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_3);
lean_dec(x_2);
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_9, 0);
lean_inc(x_13);
lean_dec(x_9);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_resolveLocalName___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_3, x_7);
lean_dec(x_3);
x_9 = lean_array_fget(x_2, x_8);
if (lean_obj_tag(x_9) == 0)
{
x_3 = x_8;
x_4 = lean_box(0);
goto _start;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = l_Lean_LocalDecl_isAuxDecl(x_12);
if (x_13 == 0)
{
lean_free_object(x_9);
lean_dec(x_12);
x_3 = x_8;
x_4 = lean_box(0);
goto _start;
}
else
{
lean_object* x_15; uint8_t x_16; 
x_15 = l_Lean_LocalDecl_userName(x_12);
x_16 = lean_name_eq(x_15, x_1);
lean_dec(x_15);
if (x_16 == 0)
{
lean_free_object(x_9);
lean_dec(x_12);
x_3 = x_8;
x_4 = lean_box(0);
goto _start;
}
else
{
lean_dec(x_8);
return x_9;
}
}
}
else
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_9, 0);
lean_inc(x_18);
lean_dec(x_9);
x_19 = l_Lean_LocalDecl_isAuxDecl(x_18);
if (x_19 == 0)
{
lean_dec(x_18);
x_3 = x_8;
x_4 = lean_box(0);
goto _start;
}
else
{
lean_object* x_21; uint8_t x_22; 
x_21 = l_Lean_LocalDecl_userName(x_18);
x_22 = lean_name_eq(x_21, x_1);
lean_dec(x_21);
if (x_22 == 0)
{
lean_dec(x_18);
x_3 = x_8;
x_4 = lean_box(0);
goto _start;
}
else
{
lean_object* x_24; 
lean_dec(x_8);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_18);
return x_24;
}
}
}
}
}
else
{
lean_object* x_25; 
lean_dec(x_3);
x_25 = lean_box(0);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_resolveLocalName___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_3, x_7);
lean_dec(x_3);
x_9 = lean_array_fget(x_2, x_8);
x_10 = l_Lean_PersistentArray_findSomeRevMAux___at_Lean_resolveLocalName___spec__8(x_1, x_9);
lean_dec(x_9);
if (lean_obj_tag(x_10) == 0)
{
x_3 = x_8;
x_4 = lean_box(0);
goto _start;
}
else
{
lean_dec(x_8);
return x_10;
}
}
else
{
lean_object* x_12; 
lean_dec(x_3);
x_12 = lean_box(0);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_resolveLocalName___spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_3, x_7);
lean_dec(x_3);
x_9 = lean_array_fget(x_2, x_8);
if (lean_obj_tag(x_9) == 0)
{
x_3 = x_8;
x_4 = lean_box(0);
goto _start;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = l_Lean_LocalDecl_isAuxDecl(x_12);
if (x_13 == 0)
{
lean_free_object(x_9);
lean_dec(x_12);
x_3 = x_8;
x_4 = lean_box(0);
goto _start;
}
else
{
lean_object* x_15; uint8_t x_16; 
x_15 = l_Lean_LocalDecl_userName(x_12);
x_16 = lean_name_eq(x_15, x_1);
lean_dec(x_15);
if (x_16 == 0)
{
lean_free_object(x_9);
lean_dec(x_12);
x_3 = x_8;
x_4 = lean_box(0);
goto _start;
}
else
{
lean_dec(x_8);
return x_9;
}
}
}
else
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_9, 0);
lean_inc(x_18);
lean_dec(x_9);
x_19 = l_Lean_LocalDecl_isAuxDecl(x_18);
if (x_19 == 0)
{
lean_dec(x_18);
x_3 = x_8;
x_4 = lean_box(0);
goto _start;
}
else
{
lean_object* x_21; uint8_t x_22; 
x_21 = l_Lean_LocalDecl_userName(x_18);
x_22 = lean_name_eq(x_21, x_1);
lean_dec(x_21);
if (x_22 == 0)
{
lean_dec(x_18);
x_3 = x_8;
x_4 = lean_box(0);
goto _start;
}
else
{
lean_object* x_24; 
lean_dec(x_8);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_18);
return x_24;
}
}
}
}
}
else
{
lean_object* x_25; 
lean_dec(x_3);
x_25 = lean_box(0);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at_Lean_resolveLocalName___spec__8(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_array_get_size(x_3);
x_5 = l_Array_findSomeRevM_x3f_find___at_Lean_resolveLocalName___spec__9(x_1, x_3, x_4, lean_box(0));
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_array_get_size(x_6);
x_8 = l_Array_findSomeRevM_x3f_find___at_Lean_resolveLocalName___spec__10(x_1, x_6, x_7, lean_box(0));
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at_Lean_resolveLocalName___spec__6(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Array_findSomeRevM_x3f_find___at_Lean_resolveLocalName___spec__7(x_1, x_3, x_4, lean_box(0));
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = l_Lean_PersistentArray_findSomeRevMAux___at_Lean_resolveLocalName___spec__8(x_1, x_6);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
return x_5;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
lean_dec(x_5);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName_loop___at_Lean_resolveLocalName___spec__11___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, uint8_t x_9, uint8_t x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
if (x_9 == 0)
{
uint8_t x_38; 
x_38 = 0;
x_12 = x_38;
goto block_37;
}
else
{
uint8_t x_39; 
x_39 = l_List_isEmpty___rarg(x_5);
if (x_39 == 0)
{
uint8_t x_40; 
x_40 = 1;
x_12 = x_40;
goto block_37;
}
else
{
uint8_t x_41; 
x_41 = 0;
x_12 = x_41;
goto block_37;
}
}
block_37:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(x_12);
lean_inc(x_1);
x_14 = lean_apply_2(x_1, x_2, x_13);
if (lean_obj_tag(x_14) == 0)
{
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_3, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_3, 1);
lean_inc(x_16);
lean_dec(x_3);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_5);
x_18 = l_Lean_resolveLocalName_loop___at_Lean_resolveLocalName___spec__11___rarg(x_4, x_6, x_7, x_8, x_1, x_15, x_17, x_10);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_19 = lean_ctor_get(x_4, 0);
lean_inc(x_19);
lean_dec(x_4);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_box(0);
x_22 = lean_apply_2(x_20, lean_box(0), x_21);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_14);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_14, 0);
x_25 = lean_ctor_get(x_4, 0);
lean_inc(x_25);
lean_dec(x_4);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = l_Lean_LocalDecl_toExpr(x_24);
lean_dec(x_24);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_5);
lean_ctor_set(x_14, 0, x_28);
x_29 = lean_apply_2(x_26, lean_box(0), x_14);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_30 = lean_ctor_get(x_14, 0);
lean_inc(x_30);
lean_dec(x_14);
x_31 = lean_ctor_get(x_4, 0);
lean_inc(x_31);
lean_dec(x_4);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = l_Lean_LocalDecl_toExpr(x_30);
lean_dec(x_30);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_5);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_36 = lean_apply_2(x_32, lean_box(0), x_35);
return x_36;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName_loop___at_Lean_resolveLocalName___spec__11___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_4, 3);
lean_inc(x_11);
lean_inc(x_6);
x_12 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_12, 0, x_6);
lean_ctor_set(x_12, 1, x_9);
lean_ctor_set(x_12, 2, x_10);
lean_ctor_set(x_12, 3, x_11);
if (x_8 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_box(x_8);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
lean_inc(x_12);
x_14 = lean_alloc_closure((void*)(l_Lean_resolveLocalName_loop___at_Lean_resolveLocalName___spec__11___rarg___lambda__1___boxed), 11, 9);
lean_closure_set(x_14, 0, x_5);
lean_closure_set(x_14, 1, x_12);
lean_closure_set(x_14, 2, x_6);
lean_closure_set(x_14, 3, x_1);
lean_closure_set(x_14, 4, x_7);
lean_closure_set(x_14, 5, x_2);
lean_closure_set(x_14, 6, x_3);
lean_closure_set(x_14, 7, x_4);
lean_closure_set(x_14, 8, x_13);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
x_16 = l_Lean_MacroScopesView_review(x_12);
lean_inc(x_1);
x_17 = l_Lean_resolveGlobalName___rarg(x_1, x_2, x_3, x_16);
x_18 = lean_box(x_8);
lean_inc(x_15);
x_19 = lean_alloc_closure((void*)(l_Lean_resolveLocalName_loop___rarg___lambda__2___boxed), 5, 4);
lean_closure_set(x_19, 0, x_1);
lean_closure_set(x_19, 1, x_14);
lean_closure_set(x_19, 2, x_15);
lean_closure_set(x_19, 3, x_18);
x_20 = lean_apply_4(x_15, lean_box(0), lean_box(0), x_17, x_19);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_1, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_box(0);
x_25 = lean_apply_2(x_23, lean_box(0), x_24);
x_26 = lean_box(x_8);
x_27 = lean_box(x_8);
x_28 = lean_alloc_closure((void*)(l_Lean_resolveLocalName_loop___at_Lean_resolveLocalName___spec__11___rarg___lambda__1___boxed), 11, 10);
lean_closure_set(x_28, 0, x_5);
lean_closure_set(x_28, 1, x_12);
lean_closure_set(x_28, 2, x_6);
lean_closure_set(x_28, 3, x_1);
lean_closure_set(x_28, 4, x_7);
lean_closure_set(x_28, 5, x_2);
lean_closure_set(x_28, 6, x_3);
lean_closure_set(x_28, 7, x_4);
lean_closure_set(x_28, 8, x_26);
lean_closure_set(x_28, 9, x_27);
x_29 = lean_apply_4(x_21, lean_box(0), lean_box(0), x_25, x_28);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName_loop___at_Lean_resolveLocalName___spec__11(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_resolveLocalName_loop___at_Lean_resolveLocalName___spec__11___rarg___boxed), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_inc(x_4);
x_6 = l_Lean_MacroScopesView_review(x_4);
x_7 = lean_ctor_get(x_1, 1);
x_8 = l_Lean_PersistentArray_findSomeRevM_x3f___at_Lean_resolveLocalName___spec__1(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
if (x_5 == 0)
{
lean_object* x_9; 
x_9 = l_Lean_PersistentArray_findSomeRevM_x3f___at_Lean_resolveLocalName___spec__6(x_6, x_7);
lean_dec(x_6);
return x_9;
}
else
{
lean_dec(x_6);
return x_8;
}
}
else
{
lean_dec(x_6);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_8 = l_Lean_extractMacroScopes(x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_resolveLocalName___rarg___lambda__1___boxed), 5, 3);
lean_closure_set(x_9, 0, x_2);
lean_closure_set(x_9, 1, x_3);
lean_closure_set(x_9, 2, x_7);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
x_11 = lean_box(0);
x_12 = 0;
x_13 = l_Lean_resolveLocalName_loop___at_Lean_resolveLocalName___spec__11___rarg(x_4, x_5, x_6, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_7, 2);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_alloc_closure((void*)(l_Lean_resolveLocalName___rarg___lambda__2), 7, 6);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_3);
lean_closure_set(x_10, 2, x_8);
lean_closure_set(x_10, 3, x_4);
lean_closure_set(x_10, 4, x_1);
lean_closure_set(x_10, 5, x_5);
x_11 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___rarg___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
lean_inc(x_5);
x_8 = lean_alloc_closure((void*)(l_Lean_resolveLocalName___rarg___lambda__3), 7, 6);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_2);
lean_closure_set(x_8, 2, x_7);
lean_closure_set(x_8, 3, x_3);
lean_closure_set(x_8, 4, x_4);
lean_closure_set(x_8, 5, x_5);
x_9 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_6, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_6);
x_7 = lean_alloc_closure((void*)(l_Lean_resolveLocalName___rarg___lambda__4), 7, 6);
lean_closure_set(x_7, 0, x_2);
lean_closure_set(x_7, 1, x_5);
lean_closure_set(x_7, 2, x_1);
lean_closure_set(x_7, 3, x_3);
lean_closure_set(x_7, 4, x_6);
lean_closure_set(x_7, 5, x_4);
x_8 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_4, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_resolveLocalName___rarg), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_resolveLocalName___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_4);
lean_dec(x_4);
x_10 = l_Array_findSomeRevM_x3f_find___at_Lean_resolveLocalName___spec__2(x_1, x_2, x_3, x_9, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_resolveLocalName___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_4);
lean_dec(x_4);
x_10 = l_Array_findSomeRevM_x3f_find___at_Lean_resolveLocalName___spec__4(x_1, x_2, x_3, x_9, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_resolveLocalName___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_4);
lean_dec(x_4);
x_10 = l_Array_findSomeRevM_x3f_find___at_Lean_resolveLocalName___spec__5(x_1, x_2, x_3, x_9, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at_Lean_resolveLocalName___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_4);
lean_dec(x_4);
x_8 = l_Lean_PersistentArray_findSomeRevMAux___at_Lean_resolveLocalName___spec__3(x_1, x_2, x_3, x_7, x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at_Lean_resolveLocalName___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_4);
lean_dec(x_4);
x_8 = l_Lean_PersistentArray_findSomeRevM_x3f___at_Lean_resolveLocalName___spec__1(x_1, x_2, x_3, x_7, x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_resolveLocalName___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_findSomeRevM_x3f_find___at_Lean_resolveLocalName___spec__7(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_resolveLocalName___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_findSomeRevM_x3f_find___at_Lean_resolveLocalName___spec__9(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_findSomeRevM_x3f_find___at_Lean_resolveLocalName___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_findSomeRevM_x3f_find___at_Lean_resolveLocalName___spec__10(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevMAux___at_Lean_resolveLocalName___spec__8___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PersistentArray_findSomeRevMAux___at_Lean_resolveLocalName___spec__8(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___at_Lean_resolveLocalName___spec__6___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PersistentArray_findSomeRevM_x3f___at_Lean_resolveLocalName___spec__6(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName_loop___at_Lean_resolveLocalName___spec__11___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_9);
lean_dec(x_9);
x_13 = lean_unbox(x_10);
lean_dec(x_10);
x_14 = l_Lean_resolveLocalName_loop___at_Lean_resolveLocalName___spec__11___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12, x_13, x_11);
lean_dec(x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName_loop___at_Lean_resolveLocalName___spec__11___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_8);
lean_dec(x_8);
x_10 = l_Lean_resolveLocalName_loop___at_Lean_resolveLocalName___spec__11___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_5);
lean_dec(x_5);
x_7 = l_Lean_resolveLocalName___rarg___lambda__1(x_1, x_2, x_3, x_4, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_unresolveNameGlobal_unresolveNameCore___spec__1___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_apply_2(x_3, lean_box(0), x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_unresolveNameGlobal_unresolveNameCore___spec__1___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_box(0);
lean_inc(x_7);
x_9 = lean_apply_2(x_7, lean_box(0), x_8);
x_10 = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at_Lean_unresolveNameGlobal_unresolveNameCore___spec__1___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_3);
lean_closure_set(x_10, 2, x_7);
x_11 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_9, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_4);
lean_dec(x_2);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
lean_inc(x_3);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_3);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_3);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_apply_2(x_13, lean_box(0), x_17);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_unresolveNameGlobal_unresolveNameCore___spec__1___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_6);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
lean_inc(x_9);
x_11 = lean_apply_2(x_9, lean_box(0), x_10);
x_12 = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at_Lean_unresolveNameGlobal_unresolveNameCore___spec__1___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_12, 0, x_2);
lean_closure_set(x_12, 1, x_3);
lean_closure_set(x_12, 2, x_9);
x_13 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_11, x_12);
return x_13;
}
else
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_7, 1);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_7, 0);
x_16 = lean_ctor_get(x_15, 0);
x_17 = lean_name_eq(x_16, x_5);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_6);
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
lean_dec(x_1);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_box(0);
lean_inc(x_19);
x_21 = lean_apply_2(x_19, lean_box(0), x_20);
x_22 = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at_Lean_unresolveNameGlobal_unresolveNameCore___spec__1___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_22, 0, x_2);
lean_closure_set(x_22, 1, x_3);
lean_closure_set(x_22, 2, x_19);
x_23 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_21, x_22);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_inc(x_3);
x_24 = lean_apply_1(x_6, x_3);
lean_inc(x_4);
x_25 = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at_Lean_unresolveNameGlobal_unresolveNameCore___spec__1___rarg___lambda__2___boxed), 5, 4);
lean_closure_set(x_25, 0, x_1);
lean_closure_set(x_25, 1, x_2);
lean_closure_set(x_25, 2, x_3);
lean_closure_set(x_25, 3, x_4);
x_26 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_24, x_25);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_6);
x_27 = lean_ctor_get(x_1, 0);
lean_inc(x_27);
lean_dec(x_1);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_box(0);
lean_inc(x_28);
x_30 = lean_apply_2(x_28, lean_box(0), x_29);
x_31 = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at_Lean_unresolveNameGlobal_unresolveNameCore___spec__1___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_31, 0, x_2);
lean_closure_set(x_31, 1, x_3);
lean_closure_set(x_31, 2, x_28);
x_32 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_30, x_31);
return x_32;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_unresolveNameGlobal_unresolveNameCore___spec__1___rarg___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_apply_2(x_15, lean_box(0), x_13);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_12, 0);
lean_inc(x_17);
lean_dec(x_12);
x_18 = l_List_forIn_x27_loop___at_Lean_unresolveNameGlobal_unresolveNameCore___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_17, lean_box(0));
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_unresolveNameGlobal_unresolveNameCore___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_apply_2(x_15, lean_box(0), x_12);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_17 = lean_ctor_get(x_11, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_dec(x_11);
x_19 = lean_ctor_get(x_1, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_dec(x_12);
x_21 = l_Lean_Name_appendCore(x_17, x_20);
lean_dec(x_17);
lean_inc(x_21);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_22 = l_Lean_resolveGlobalName___rarg(x_1, x_2, x_3, x_21);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_7);
lean_inc(x_9);
lean_inc(x_1);
x_23 = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at_Lean_unresolveNameGlobal_unresolveNameCore___spec__1___rarg___lambda__3___boxed), 7, 6);
lean_closure_set(x_23, 0, x_1);
lean_closure_set(x_23, 1, x_9);
lean_closure_set(x_23, 2, x_21);
lean_closure_set(x_23, 3, x_7);
lean_closure_set(x_23, 4, x_4);
lean_closure_set(x_23, 5, x_5);
lean_inc(x_7);
x_24 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_22, x_23);
x_25 = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at_Lean_unresolveNameGlobal_unresolveNameCore___spec__1___rarg___lambda__4), 12, 11);
lean_closure_set(x_25, 0, x_1);
lean_closure_set(x_25, 1, x_2);
lean_closure_set(x_25, 2, x_3);
lean_closure_set(x_25, 3, x_4);
lean_closure_set(x_25, 4, x_5);
lean_closure_set(x_25, 5, x_6);
lean_closure_set(x_25, 6, x_7);
lean_closure_set(x_25, 7, x_8);
lean_closure_set(x_25, 8, x_9);
lean_closure_set(x_25, 9, x_10);
lean_closure_set(x_25, 10, x_18);
x_26 = lean_apply_4(x_19, lean_box(0), lean_box(0), x_24, x_25);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_unresolveNameGlobal_unresolveNameCore___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at_Lean_unresolveNameGlobal_unresolveNameCore___spec__1___rarg), 13, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_unresolveNameCore___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l_Lean_resolveNamespaceCore___rarg___lambda__1___boxed), 3, 2);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_box(0);
x_10 = lean_apply_2(x_8, lean_box(0), x_9);
x_11 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_10, x_6);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_ctor_get(x_5, 0);
lean_inc(x_12);
lean_dec(x_5);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_apply_2(x_14, lean_box(0), x_12);
return x_15;
}
}
}
static lean_object* _init_l_Lean_unresolveNameGlobal_unresolveNameCore___rarg___lambda__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_unresolveNameCore___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = l_Lean_Name_componentsRev(x_1);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
x_10 = lean_box(0);
x_11 = lean_box(0);
x_12 = l_Lean_unresolveNameGlobal_unresolveNameCore___rarg___lambda__2___closed__1;
lean_inc(x_9);
lean_inc_n(x_8, 2);
lean_inc(x_2);
x_13 = l_List_forIn_x27_loop___at_Lean_unresolveNameGlobal_unresolveNameCore___spec__1___rarg(x_2, x_3, x_4, x_5, x_6, x_8, x_9, x_10, x_11, x_8, x_8, x_12, lean_box(0));
lean_inc(x_9);
x_14 = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal_unresolveNameCore___rarg___lambda__1), 4, 3);
lean_closure_set(x_14, 0, x_2);
lean_closure_set(x_14, 1, x_11);
lean_closure_set(x_14, 2, x_9);
x_15 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_13, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_unresolveNameCore___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
lean_inc(x_1);
lean_inc(x_6);
x_7 = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal_unresolveNameCore___rarg___lambda__2___boxed), 7, 6);
lean_closure_set(x_7, 0, x_6);
lean_closure_set(x_7, 1, x_1);
lean_closure_set(x_7, 2, x_2);
lean_closure_set(x_7, 3, x_3);
lean_closure_set(x_7, 4, x_4);
lean_closure_set(x_7, 5, x_5);
x_8 = l_Lean_Name_hasMacroScopes(x_6);
lean_dec(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_box(0);
x_13 = lean_apply_2(x_11, lean_box(0), x_12);
x_14 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_13, x_7);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_7);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_box(0);
x_18 = lean_apply_2(x_16, lean_box(0), x_17);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_unresolveNameCore(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal_unresolveNameCore___rarg), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_unresolveNameGlobal_unresolveNameCore___spec__1___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_forIn_x27_loop___at_Lean_unresolveNameGlobal_unresolveNameCore___spec__1___rarg___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_unresolveNameGlobal_unresolveNameCore___spec__1___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_5);
lean_dec(x_5);
x_7 = l_List_forIn_x27_loop___at_Lean_unresolveNameGlobal_unresolveNameCore___spec__1___rarg___lambda__2(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lean_unresolveNameGlobal_unresolveNameCore___spec__1___rarg___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_forIn_x27_loop___at_Lean_unresolveNameGlobal_unresolveNameCore___spec__1___rarg___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_unresolveNameCore___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_unresolveNameGlobal_unresolveNameCore___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_unresolveNameGlobal___spec__1___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_1);
x_5 = lean_apply_2(x_2, lean_box(0), x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_unresolveNameGlobal___spec__1___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_box(0);
lean_inc(x_6);
x_8 = lean_apply_2(x_6, lean_box(0), x_7);
x_9 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at_Lean_unresolveNameGlobal___spec__1___rarg___lambda__1___boxed), 3, 2);
lean_closure_set(x_9, 0, x_2);
lean_closure_set(x_9, 1, x_6);
x_10 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
else
{
uint8_t x_11; 
lean_dec(x_3);
lean_dec(x_2);
x_11 = !lean_is_exclusive(x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_apply_2(x_13, lean_box(0), x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_18 = lean_ctor_get(x_4, 0);
lean_inc(x_18);
lean_dec(x_4);
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
lean_dec(x_1);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_18);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_apply_2(x_20, lean_box(0), x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_unresolveNameGlobal___spec__1___rarg___lambda__3(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, size_t x_12, lean_object* x_13) {
_start:
{
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_apply_2(x_16, lean_box(0), x_14);
return x_17;
}
else
{
lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_13, 0);
lean_inc(x_18);
lean_dec(x_13);
x_19 = 1;
x_20 = lean_usize_add(x_2, x_19);
x_21 = l_Array_forIn_x27Unsafe_loop___at_Lean_unresolveNameGlobal___spec__1___rarg(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_20, x_18);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_unresolveNameGlobal___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, size_t x_11, size_t x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_12, x_11);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_apply_2(x_16, lean_box(0), x_13);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_13);
x_18 = lean_array_uget(x_10, x_12);
x_19 = lean_ctor_get(x_1, 1);
lean_inc(x_19);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_20 = l_Lean_unresolveNameGlobal_unresolveNameCore___rarg(x_1, x_2, x_3, x_4, x_5, x_18);
lean_inc(x_6);
lean_inc(x_9);
lean_inc(x_1);
x_21 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at_Lean_unresolveNameGlobal___spec__1___rarg___lambda__2), 4, 3);
lean_closure_set(x_21, 0, x_1);
lean_closure_set(x_21, 1, x_9);
lean_closure_set(x_21, 2, x_6);
lean_inc(x_6);
x_22 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_20, x_21);
x_23 = lean_box_usize(x_12);
x_24 = lean_box_usize(x_11);
x_25 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at_Lean_unresolveNameGlobal___spec__1___rarg___lambda__3___boxed), 13, 12);
lean_closure_set(x_25, 0, x_1);
lean_closure_set(x_25, 1, x_23);
lean_closure_set(x_25, 2, x_2);
lean_closure_set(x_25, 3, x_3);
lean_closure_set(x_25, 4, x_4);
lean_closure_set(x_25, 5, x_5);
lean_closure_set(x_25, 6, x_6);
lean_closure_set(x_25, 7, x_7);
lean_closure_set(x_25, 8, x_8);
lean_closure_set(x_25, 9, x_9);
lean_closure_set(x_25, 10, x_10);
lean_closure_set(x_25, 11, x_24);
x_26 = lean_apply_4(x_19, lean_box(0), lean_box(0), x_22, x_25);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_unresolveNameGlobal___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at_Lean_unresolveNameGlobal___spec__1___rarg___boxed), 13, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_unresolveNameGlobal___spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; size_t x_11; size_t x_12; 
x_7 = lean_array_uget(x_2, x_3);
x_8 = l_Lean_Name_getPrefix(x_7);
x_9 = l_Lean_Name_getPrefix(x_1);
x_10 = l_Lean_Name_isPrefixOf(x_8, x_9);
lean_dec(x_9);
lean_dec(x_8);
x_11 = 1;
x_12 = lean_usize_add(x_3, x_11);
if (x_10 == 0)
{
lean_dec(x_7);
x_3 = x_12;
goto _start;
}
else
{
lean_object* x_14; 
x_14 = lean_array_push(x_5, x_7);
x_3 = x_12;
x_5 = x_14;
goto _start;
}
}
else
{
return x_5;
}
}
}
static lean_object* _init_l_Lean_unresolveNameGlobal___rarg___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_9 = l_Lean_rootNamespace;
lean_inc(x_1);
x_10 = l_Lean_Name_append(x_9, x_1);
x_11 = lean_array_push(x_7, x_10);
x_12 = lean_box(0);
x_13 = lean_array_size(x_11);
x_14 = 0;
x_15 = l_Lean_unresolveNameGlobal___rarg___lambda__1___closed__1;
lean_inc(x_11);
lean_inc(x_6);
lean_inc(x_1);
lean_inc(x_2);
x_16 = l_Array_forIn_x27Unsafe_loop___at_Lean_unresolveNameGlobal___spec__1___rarg(x_2, x_3, x_4, x_1, x_5, x_6, x_11, x_12, x_15, x_11, x_13, x_14, x_15);
lean_inc(x_6);
x_17 = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal_unresolveNameCore___rarg___lambda__1), 4, 3);
lean_closure_set(x_17, 0, x_2);
lean_closure_set(x_17, 1, x_1);
lean_closure_set(x_17, 2, x_6);
x_18 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_16, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
lean_inc(x_1);
x_9 = l_Lean_getRevAliases(x_8, x_1);
x_10 = lean_array_mk(x_9);
if (x_7 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_array_get_size(x_10);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_lt(x_12, x_11);
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = lean_apply_2(x_15, lean_box(0), x_16);
if (x_13 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_11);
lean_dec(x_10);
x_18 = l_Lean_initFn____x40_Lean_ResolveName___hyg_126____closed__1;
lean_inc(x_6);
x_19 = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal___rarg___lambda__1___boxed), 8, 7);
lean_closure_set(x_19, 0, x_1);
lean_closure_set(x_19, 1, x_2);
lean_closure_set(x_19, 2, x_3);
lean_closure_set(x_19, 3, x_4);
lean_closure_set(x_19, 4, x_5);
lean_closure_set(x_19, 5, x_6);
lean_closure_set(x_19, 6, x_18);
x_20 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_17, x_19);
return x_20;
}
else
{
uint8_t x_21; 
x_21 = lean_nat_dec_le(x_11, x_11);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_11);
lean_dec(x_10);
x_22 = l_Lean_initFn____x40_Lean_ResolveName___hyg_126____closed__1;
lean_inc(x_6);
x_23 = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal___rarg___lambda__1___boxed), 8, 7);
lean_closure_set(x_23, 0, x_1);
lean_closure_set(x_23, 1, x_2);
lean_closure_set(x_23, 2, x_3);
lean_closure_set(x_23, 3, x_4);
lean_closure_set(x_23, 4, x_5);
lean_closure_set(x_23, 5, x_6);
lean_closure_set(x_23, 6, x_22);
x_24 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_17, x_23);
return x_24;
}
else
{
size_t x_25; size_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = 0;
x_26 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_27 = l_Lean_initFn____x40_Lean_ResolveName___hyg_126____closed__1;
x_28 = l_Array_foldlMUnsafe_fold___at_Lean_unresolveNameGlobal___spec__2(x_1, x_10, x_25, x_26, x_27);
lean_dec(x_10);
lean_inc(x_6);
x_29 = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal___rarg___lambda__1___boxed), 8, 7);
lean_closure_set(x_29, 0, x_1);
lean_closure_set(x_29, 1, x_2);
lean_closure_set(x_29, 2, x_3);
lean_closure_set(x_29, 3, x_4);
lean_closure_set(x_29, 4, x_5);
lean_closure_set(x_29, 5, x_6);
lean_closure_set(x_29, 6, x_28);
x_30 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_17, x_29);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_31 = lean_ctor_get(x_2, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_box(0);
x_34 = lean_apply_2(x_32, lean_box(0), x_33);
lean_inc(x_6);
x_35 = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal___rarg___lambda__1___boxed), 8, 7);
lean_closure_set(x_35, 0, x_1);
lean_closure_set(x_35, 1, x_2);
lean_closure_set(x_35, 2, x_3);
lean_closure_set(x_35, 3, x_4);
lean_closure_set(x_35, 4, x_5);
lean_closure_set(x_35, 5, x_6);
lean_closure_set(x_35, 6, x_10);
x_36 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_34, x_35);
return x_36;
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
x_10 = lean_box(x_6);
lean_inc(x_8);
x_11 = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal___rarg___lambda__2___boxed), 8, 7);
lean_closure_set(x_11, 0, x_3);
lean_closure_set(x_11, 1, x_1);
lean_closure_set(x_11, 2, x_4);
lean_closure_set(x_11, 3, x_2);
lean_closure_set(x_11, 4, x_5);
lean_closure_set(x_11, 5, x_8);
lean_closure_set(x_11, 6, x_10);
x_12 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_9, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___rarg___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
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
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_dec(x_3);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_9);
x_10 = lean_private_to_user_name(x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = lean_name_eq(x_9, x_2);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_Lean_rootNamespace;
x_15 = l_Lean_Name_append(x_14, x_2);
x_16 = lean_apply_2(x_13, lean_box(0), x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
lean_dec(x_1);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_apply_2(x_18, lean_box(0), x_2);
return x_19;
}
}
else
{
lean_object* x_20; uint8_t x_21; 
lean_dec(x_9);
x_20 = lean_ctor_get(x_10, 0);
lean_inc(x_20);
lean_dec(x_10);
x_21 = lean_name_eq(x_20, x_2);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_1, 0);
lean_inc(x_22);
lean_dec(x_1);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = l_Lean_rootNamespace;
x_25 = l_Lean_Name_append(x_24, x_2);
x_26 = lean_apply_2(x_23, lean_box(0), x_25);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_1, 0);
lean_inc(x_27);
lean_dec(x_1);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_apply_2(x_28, lean_box(0), x_2);
return x_29;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_8);
lean_dec(x_7);
x_30 = lean_ctor_get(x_1, 0);
lean_inc(x_30);
lean_dec(x_1);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_apply_2(x_31, lean_box(0), x_2);
return x_32;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___rarg___lambda__5(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8) {
_start:
{
if (x_1 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_box(x_7);
lean_inc(x_2);
x_10 = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal___rarg___lambda__3___boxed), 7, 6);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_3);
lean_closure_set(x_10, 2, x_4);
lean_closure_set(x_10, 3, x_5);
lean_closure_set(x_10, 4, x_6);
lean_closure_set(x_10, 5, x_9);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
lean_dec(x_2);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_box(0);
x_15 = lean_apply_2(x_13, lean_box(0), x_14);
x_16 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_15, x_10);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_6);
x_17 = lean_ctor_get(x_2, 1);
lean_inc(x_17);
lean_inc(x_4);
lean_inc(x_2);
x_18 = l_Lean_resolveGlobalName___rarg(x_2, x_5, x_3, x_4);
x_19 = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal___rarg___lambda__4), 3, 2);
lean_closure_set(x_19, 0, x_2);
lean_closure_set(x_19, 1, x_4);
x_20 = lean_apply_4(x_17, lean_box(0), lean_box(0), x_18, x_19);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_box(x_5);
x_9 = lean_box(x_6);
lean_inc(x_4);
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal___rarg___lambda__5___boxed), 8, 7);
lean_closure_set(x_10, 0, x_8);
lean_closure_set(x_10, 1, x_1);
lean_closure_set(x_10, 2, x_3);
lean_closure_set(x_10, 3, x_4);
lean_closure_set(x_10, 4, x_2);
lean_closure_set(x_10, 5, x_7);
lean_closure_set(x_10, 6, x_9);
x_11 = l_Lean_Name_hasMacroScopes(x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_4);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = lean_apply_2(x_14, lean_box(0), x_15);
x_17 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_16, x_10);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_10);
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
lean_dec(x_1);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_apply_2(x_19, lean_box(0), x_4);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal___rarg___boxed), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_unresolveNameGlobal___spec__1___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_forIn_x27Unsafe_loop___at_Lean_unresolveNameGlobal___spec__1___rarg___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_unresolveNameGlobal___spec__1___rarg___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_15 = lean_unbox_usize(x_12);
lean_dec(x_12);
x_16 = l_Array_forIn_x27Unsafe_loop___at_Lean_unresolveNameGlobal___spec__1___rarg___lambda__3(x_1, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_15, x_13);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_unresolveNameGlobal___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_11);
lean_dec(x_11);
x_15 = lean_unbox_usize(x_12);
lean_dec(x_12);
x_16 = l_Array_forIn_x27Unsafe_loop___at_Lean_unresolveNameGlobal___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_14, x_15, x_13);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_unresolveNameGlobal___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lean_unresolveNameGlobal___spec__2(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_unresolveNameGlobal___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_7);
lean_dec(x_7);
x_10 = l_Lean_unresolveNameGlobal___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_9, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___rarg___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_6);
lean_dec(x_6);
x_9 = l_Lean_unresolveNameGlobal___rarg___lambda__3(x_1, x_2, x_3, x_4, x_5, x_8, x_7);
lean_dec(x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___rarg___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = lean_unbox(x_7);
lean_dec(x_7);
x_11 = l_Lean_unresolveNameGlobal___rarg___lambda__5(x_9, x_2, x_3, x_4, x_5, x_6, x_10, x_8);
lean_dec(x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_unbox(x_5);
lean_dec(x_5);
x_9 = lean_unbox(x_6);
lean_dec(x_6);
x_10 = l_Lean_unresolveNameGlobal___rarg(x_1, x_2, x_3, x_4, x_8, x_9, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_unresolveNameGlobalAvoidingLocals___spec__2___rarg___lambda__1(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, size_t x_12, lean_object* x_13) {
_start:
{
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_apply_2(x_16, lean_box(0), x_14);
return x_17;
}
else
{
lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_13, 0);
lean_inc(x_18);
lean_dec(x_13);
x_19 = 1;
x_20 = lean_usize_add(x_2, x_19);
x_21 = l_Array_forIn_x27Unsafe_loop___at_Lean_unresolveNameGlobalAvoidingLocals___spec__2___rarg(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_20, x_18);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_unresolveNameGlobalAvoidingLocals___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, size_t x_11, size_t x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_12, x_11);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_apply_2(x_16, lean_box(0), x_13);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_13);
x_18 = lean_array_uget(x_10, x_12);
x_19 = lean_ctor_get(x_1, 1);
lean_inc(x_19);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_20 = l_Lean_unresolveNameGlobal_unresolveNameCore___rarg(x_1, x_2, x_3, x_4, x_5, x_18);
lean_inc(x_6);
lean_inc(x_9);
lean_inc(x_1);
x_21 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at_Lean_unresolveNameGlobal___spec__1___rarg___lambda__2), 4, 3);
lean_closure_set(x_21, 0, x_1);
lean_closure_set(x_21, 1, x_9);
lean_closure_set(x_21, 2, x_6);
lean_inc(x_6);
x_22 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_20, x_21);
x_23 = lean_box_usize(x_12);
x_24 = lean_box_usize(x_11);
x_25 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at_Lean_unresolveNameGlobalAvoidingLocals___spec__2___rarg___lambda__1___boxed), 13, 12);
lean_closure_set(x_25, 0, x_1);
lean_closure_set(x_25, 1, x_23);
lean_closure_set(x_25, 2, x_2);
lean_closure_set(x_25, 3, x_3);
lean_closure_set(x_25, 4, x_4);
lean_closure_set(x_25, 5, x_5);
lean_closure_set(x_25, 6, x_6);
lean_closure_set(x_25, 7, x_7);
lean_closure_set(x_25, 8, x_8);
lean_closure_set(x_25, 9, x_9);
lean_closure_set(x_25, 10, x_10);
lean_closure_set(x_25, 11, x_24);
x_26 = lean_apply_4(x_19, lean_box(0), lean_box(0), x_22, x_25);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_unresolveNameGlobalAvoidingLocals___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_forIn_x27Unsafe_loop___at_Lean_unresolveNameGlobalAvoidingLocals___spec__2___rarg___boxed), 13, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_unresolveNameGlobalAvoidingLocals___spec__3(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; size_t x_11; size_t x_12; 
x_7 = lean_array_uget(x_2, x_3);
x_8 = l_Lean_Name_getPrefix(x_7);
x_9 = l_Lean_Name_getPrefix(x_1);
x_10 = l_Lean_Name_isPrefixOf(x_8, x_9);
lean_dec(x_9);
lean_dec(x_8);
x_11 = 1;
x_12 = lean_usize_add(x_3, x_11);
if (x_10 == 0)
{
lean_dec(x_7);
x_3 = x_12;
goto _start;
}
else
{
lean_object* x_14; 
x_14 = lean_array_push(x_5, x_7);
x_3 = x_12;
x_5 = x_14;
goto _start;
}
}
else
{
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___at_Lean_unresolveNameGlobalAvoidingLocals___spec__1___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_9 = l_Lean_rootNamespace;
lean_inc(x_1);
x_10 = l_Lean_Name_append(x_9, x_1);
x_11 = lean_array_push(x_7, x_10);
x_12 = lean_box(0);
x_13 = lean_array_size(x_11);
x_14 = 0;
x_15 = l_Lean_unresolveNameGlobal___rarg___lambda__1___closed__1;
lean_inc(x_11);
lean_inc(x_6);
lean_inc(x_1);
lean_inc(x_2);
x_16 = l_Array_forIn_x27Unsafe_loop___at_Lean_unresolveNameGlobalAvoidingLocals___spec__2___rarg(x_2, x_3, x_4, x_1, x_5, x_6, x_11, x_12, x_15, x_11, x_13, x_14, x_15);
lean_inc(x_6);
x_17 = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal_unresolveNameCore___rarg___lambda__1), 4, 3);
lean_closure_set(x_17, 0, x_2);
lean_closure_set(x_17, 1, x_1);
lean_closure_set(x_17, 2, x_6);
x_18 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_16, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___at_Lean_unresolveNameGlobalAvoidingLocals___spec__1___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
lean_inc(x_1);
x_9 = l_Lean_getRevAliases(x_8, x_1);
x_10 = lean_array_mk(x_9);
if (x_7 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_array_get_size(x_10);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_lt(x_12, x_11);
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_box(0);
x_17 = lean_apply_2(x_15, lean_box(0), x_16);
if (x_13 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_11);
lean_dec(x_10);
x_18 = l_Lean_initFn____x40_Lean_ResolveName___hyg_126____closed__1;
lean_inc(x_6);
x_19 = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal___at_Lean_unresolveNameGlobalAvoidingLocals___spec__1___rarg___lambda__1___boxed), 8, 7);
lean_closure_set(x_19, 0, x_1);
lean_closure_set(x_19, 1, x_2);
lean_closure_set(x_19, 2, x_3);
lean_closure_set(x_19, 3, x_4);
lean_closure_set(x_19, 4, x_5);
lean_closure_set(x_19, 5, x_6);
lean_closure_set(x_19, 6, x_18);
x_20 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_17, x_19);
return x_20;
}
else
{
uint8_t x_21; 
x_21 = lean_nat_dec_le(x_11, x_11);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_11);
lean_dec(x_10);
x_22 = l_Lean_initFn____x40_Lean_ResolveName___hyg_126____closed__1;
lean_inc(x_6);
x_23 = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal___at_Lean_unresolveNameGlobalAvoidingLocals___spec__1___rarg___lambda__1___boxed), 8, 7);
lean_closure_set(x_23, 0, x_1);
lean_closure_set(x_23, 1, x_2);
lean_closure_set(x_23, 2, x_3);
lean_closure_set(x_23, 3, x_4);
lean_closure_set(x_23, 4, x_5);
lean_closure_set(x_23, 5, x_6);
lean_closure_set(x_23, 6, x_22);
x_24 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_17, x_23);
return x_24;
}
else
{
size_t x_25; size_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = 0;
x_26 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_27 = l_Lean_initFn____x40_Lean_ResolveName___hyg_126____closed__1;
x_28 = l_Array_foldlMUnsafe_fold___at_Lean_unresolveNameGlobalAvoidingLocals___spec__3(x_1, x_10, x_25, x_26, x_27);
lean_dec(x_10);
lean_inc(x_6);
x_29 = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal___at_Lean_unresolveNameGlobalAvoidingLocals___spec__1___rarg___lambda__1___boxed), 8, 7);
lean_closure_set(x_29, 0, x_1);
lean_closure_set(x_29, 1, x_2);
lean_closure_set(x_29, 2, x_3);
lean_closure_set(x_29, 3, x_4);
lean_closure_set(x_29, 4, x_5);
lean_closure_set(x_29, 5, x_6);
lean_closure_set(x_29, 6, x_28);
x_30 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_17, x_29);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_31 = lean_ctor_get(x_2, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_box(0);
x_34 = lean_apply_2(x_32, lean_box(0), x_33);
lean_inc(x_6);
x_35 = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal___at_Lean_unresolveNameGlobalAvoidingLocals___spec__1___rarg___lambda__1___boxed), 8, 7);
lean_closure_set(x_35, 0, x_1);
lean_closure_set(x_35, 1, x_2);
lean_closure_set(x_35, 2, x_3);
lean_closure_set(x_35, 3, x_4);
lean_closure_set(x_35, 4, x_5);
lean_closure_set(x_35, 5, x_6);
lean_closure_set(x_35, 6, x_10);
x_36 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_34, x_35);
return x_36;
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___at_Lean_unresolveNameGlobalAvoidingLocals___spec__1___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
x_10 = lean_box(x_6);
lean_inc(x_8);
x_11 = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal___at_Lean_unresolveNameGlobalAvoidingLocals___spec__1___rarg___lambda__2___boxed), 8, 7);
lean_closure_set(x_11, 0, x_3);
lean_closure_set(x_11, 1, x_1);
lean_closure_set(x_11, 2, x_4);
lean_closure_set(x_11, 3, x_2);
lean_closure_set(x_11, 4, x_5);
lean_closure_set(x_11, 5, x_8);
lean_closure_set(x_11, 6, x_10);
x_12 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_9, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___at_Lean_unresolveNameGlobalAvoidingLocals___spec__1___rarg___lambda__4(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8) {
_start:
{
if (x_1 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_box(x_7);
lean_inc(x_2);
x_10 = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal___at_Lean_unresolveNameGlobalAvoidingLocals___spec__1___rarg___lambda__3___boxed), 7, 6);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_3);
lean_closure_set(x_10, 2, x_4);
lean_closure_set(x_10, 3, x_5);
lean_closure_set(x_10, 4, x_6);
lean_closure_set(x_10, 5, x_9);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
lean_dec(x_2);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_box(0);
x_15 = lean_apply_2(x_13, lean_box(0), x_14);
x_16 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_15, x_10);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_6);
x_17 = lean_ctor_get(x_2, 1);
lean_inc(x_17);
lean_inc(x_4);
lean_inc(x_2);
x_18 = l_Lean_resolveGlobalName___rarg(x_2, x_5, x_3, x_4);
x_19 = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal___rarg___lambda__4), 3, 2);
lean_closure_set(x_19, 0, x_2);
lean_closure_set(x_19, 1, x_4);
x_20 = lean_apply_4(x_17, lean_box(0), lean_box(0), x_18, x_19);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___at_Lean_unresolveNameGlobalAvoidingLocals___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_box(x_5);
x_9 = lean_box(x_6);
lean_inc(x_4);
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal___at_Lean_unresolveNameGlobalAvoidingLocals___spec__1___rarg___lambda__4___boxed), 8, 7);
lean_closure_set(x_10, 0, x_8);
lean_closure_set(x_10, 1, x_1);
lean_closure_set(x_10, 2, x_3);
lean_closure_set(x_10, 3, x_4);
lean_closure_set(x_10, 4, x_2);
lean_closure_set(x_10, 5, x_7);
lean_closure_set(x_10, 6, x_9);
x_11 = l_Lean_Name_hasMacroScopes(x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_4);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = lean_apply_2(x_14, lean_box(0), x_15);
x_17 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_16, x_10);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_10);
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
lean_dec(x_1);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_apply_2(x_19, lean_box(0), x_4);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___at_Lean_unresolveNameGlobalAvoidingLocals___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal___at_Lean_unresolveNameGlobalAvoidingLocals___spec__1___rarg___boxed), 7, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_unresolveNameGlobalAvoidingLocals___rarg___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Option_isNone___rarg___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_resolveLocalName___rarg(x_1, x_2, x_3, x_4, x_5);
x_10 = l_Lean_unresolveNameGlobalAvoidingLocals___rarg___lambda__1___closed__1;
x_11 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_10, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; 
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobalAvoidingLocals___rarg___lambda__1), 5, 4);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_2);
lean_closure_set(x_7, 2, x_3);
lean_closure_set(x_7, 3, x_4);
x_8 = 0;
x_9 = l_Lean_unresolveNameGlobal___at_Lean_unresolveNameGlobalAvoidingLocals___spec__1___rarg(x_1, x_2, x_3, x_5, x_6, x_8, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobalAvoidingLocals___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_unresolveNameGlobalAvoidingLocals___spec__2___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_15 = lean_unbox_usize(x_12);
lean_dec(x_12);
x_16 = l_Array_forIn_x27Unsafe_loop___at_Lean_unresolveNameGlobalAvoidingLocals___spec__2___rarg___lambda__1(x_1, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_15, x_13);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_unresolveNameGlobalAvoidingLocals___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_11);
lean_dec(x_11);
x_15 = lean_unbox_usize(x_12);
lean_dec(x_12);
x_16 = l_Array_forIn_x27Unsafe_loop___at_Lean_unresolveNameGlobalAvoidingLocals___spec__2___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_14, x_15, x_13);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_unresolveNameGlobalAvoidingLocals___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lean_unresolveNameGlobalAvoidingLocals___spec__3(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___at_Lean_unresolveNameGlobalAvoidingLocals___spec__1___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_unresolveNameGlobal___at_Lean_unresolveNameGlobalAvoidingLocals___spec__1___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___at_Lean_unresolveNameGlobalAvoidingLocals___spec__1___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_7);
lean_dec(x_7);
x_10 = l_Lean_unresolveNameGlobal___at_Lean_unresolveNameGlobalAvoidingLocals___spec__1___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_9, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___at_Lean_unresolveNameGlobalAvoidingLocals___spec__1___rarg___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_6);
lean_dec(x_6);
x_9 = l_Lean_unresolveNameGlobal___at_Lean_unresolveNameGlobalAvoidingLocals___spec__1___rarg___lambda__3(x_1, x_2, x_3, x_4, x_5, x_8, x_7);
lean_dec(x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___at_Lean_unresolveNameGlobalAvoidingLocals___spec__1___rarg___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = lean_unbox(x_7);
lean_dec(x_7);
x_11 = l_Lean_unresolveNameGlobal___at_Lean_unresolveNameGlobalAvoidingLocals___spec__1___rarg___lambda__4(x_9, x_2, x_3, x_4, x_5, x_6, x_10, x_8);
lean_dec(x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___at_Lean_unresolveNameGlobalAvoidingLocals___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_unbox(x_5);
lean_dec(x_5);
x_9 = lean_unbox(x_6);
lean_dec(x_6);
x_10 = l_Lean_unresolveNameGlobal___at_Lean_unresolveNameGlobalAvoidingLocals___spec__1___rarg(x_1, x_2, x_3, x_4, x_8, x_9, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_6);
lean_dec(x_6);
x_8 = l_Lean_unresolveNameGlobalAvoidingLocals___rarg(x_1, x_2, x_3, x_4, x_5, x_7);
return x_8;
}
}
lean_object* initialize_Lean_Data_OpenDecl(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Hygiene(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Modifiers(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Exception(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Namespace(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_ResolveName(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_OpenDecl(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Hygiene(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Modifiers(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Exception(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Namespace(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_throwReservedNameNotAvailable___rarg___closed__1 = _init_l_Lean_throwReservedNameNotAvailable___rarg___closed__1();
lean_mark_persistent(l_Lean_throwReservedNameNotAvailable___rarg___closed__1);
l_Lean_throwReservedNameNotAvailable___rarg___closed__2 = _init_l_Lean_throwReservedNameNotAvailable___rarg___closed__2();
lean_mark_persistent(l_Lean_throwReservedNameNotAvailable___rarg___closed__2);
l_Lean_throwReservedNameNotAvailable___rarg___closed__3 = _init_l_Lean_throwReservedNameNotAvailable___rarg___closed__3();
lean_mark_persistent(l_Lean_throwReservedNameNotAvailable___rarg___closed__3);
l_Lean_throwReservedNameNotAvailable___rarg___closed__4 = _init_l_Lean_throwReservedNameNotAvailable___rarg___closed__4();
lean_mark_persistent(l_Lean_throwReservedNameNotAvailable___rarg___closed__4);
l_Lean_throwReservedNameNotAvailable___rarg___closed__5 = _init_l_Lean_throwReservedNameNotAvailable___rarg___closed__5();
lean_mark_persistent(l_Lean_throwReservedNameNotAvailable___rarg___closed__5);
l_Lean_throwReservedNameNotAvailable___rarg___closed__6 = _init_l_Lean_throwReservedNameNotAvailable___rarg___closed__6();
lean_mark_persistent(l_Lean_throwReservedNameNotAvailable___rarg___closed__6);
l_Lean_initFn____x40_Lean_ResolveName___hyg_126____closed__1 = _init_l_Lean_initFn____x40_Lean_ResolveName___hyg_126____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_ResolveName___hyg_126____closed__1);
if (builtin) {res = l_Lean_initFn____x40_Lean_ResolveName___hyg_126_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_reservedNamePredicatesRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_reservedNamePredicatesRef);
lean_dec_ref(res);
}l_Lean_registerReservedNamePredicate___lambda__1___closed__1 = _init_l_Lean_registerReservedNamePredicate___lambda__1___closed__1();
lean_mark_persistent(l_Lean_registerReservedNamePredicate___lambda__1___closed__1);
l_Lean_registerReservedNamePredicate___closed__1 = _init_l_Lean_registerReservedNamePredicate___closed__1();
lean_mark_persistent(l_Lean_registerReservedNamePredicate___closed__1);
l_Lean_registerReservedNamePredicate___closed__2 = _init_l_Lean_registerReservedNamePredicate___closed__2();
lean_mark_persistent(l_Lean_registerReservedNamePredicate___closed__2);
l_Lean_initFn____x40_Lean_ResolveName___hyg_269____closed__1 = _init_l_Lean_initFn____x40_Lean_ResolveName___hyg_269____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_ResolveName___hyg_269____closed__1);
if (builtin) {res = l_Lean_initFn____x40_Lean_ResolveName___hyg_269_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_reservedNamePredicatesExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_reservedNamePredicatesExt);
lean_dec_ref(res);
}l_Lean_isReservedName___closed__1 = _init_l_Lean_isReservedName___closed__1();
lean_mark_persistent(l_Lean_isReservedName___closed__1);
l_Lean_isReservedName___closed__2 = _init_l_Lean_isReservedName___closed__2();
lean_mark_persistent(l_Lean_isReservedName___closed__2);
l_Lean_PersistentHashMap_findAux___at_Lean_addAliasEntry___spec__3___closed__1 = _init_l_Lean_PersistentHashMap_findAux___at_Lean_addAliasEntry___spec__3___closed__1();
l_Lean_PersistentHashMap_findAux___at_Lean_addAliasEntry___spec__3___closed__2 = _init_l_Lean_PersistentHashMap_findAux___at_Lean_addAliasEntry___spec__3___closed__2();
l_Lean_PersistentHashMap_insertAux___at_Lean_addAliasEntry___spec__8___closed__1 = _init_l_Lean_PersistentHashMap_insertAux___at_Lean_addAliasEntry___spec__8___closed__1();
lean_mark_persistent(l_Lean_PersistentHashMap_insertAux___at_Lean_addAliasEntry___spec__8___closed__1);
l_Lean_initFn____x40_Lean_ResolveName___hyg_392____lambda__1___closed__1 = _init_l_Lean_initFn____x40_Lean_ResolveName___hyg_392____lambda__1___closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_ResolveName___hyg_392____lambda__1___closed__1);
l_Lean_initFn____x40_Lean_ResolveName___hyg_392____lambda__1___closed__2 = _init_l_Lean_initFn____x40_Lean_ResolveName___hyg_392____lambda__1___closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_ResolveName___hyg_392____lambda__1___closed__2);
l_Lean_initFn____x40_Lean_ResolveName___hyg_392____lambda__1___closed__3 = _init_l_Lean_initFn____x40_Lean_ResolveName___hyg_392____lambda__1___closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_ResolveName___hyg_392____lambda__1___closed__3);
l_Lean_initFn____x40_Lean_ResolveName___hyg_392____lambda__1___closed__4 = _init_l_Lean_initFn____x40_Lean_ResolveName___hyg_392____lambda__1___closed__4();
lean_mark_persistent(l_Lean_initFn____x40_Lean_ResolveName___hyg_392____lambda__1___closed__4);
l_Lean_initFn____x40_Lean_ResolveName___hyg_392____lambda__1___closed__5 = _init_l_Lean_initFn____x40_Lean_ResolveName___hyg_392____lambda__1___closed__5();
lean_mark_persistent(l_Lean_initFn____x40_Lean_ResolveName___hyg_392____lambda__1___closed__5);
l_Lean_initFn____x40_Lean_ResolveName___hyg_392____lambda__1___closed__6 = _init_l_Lean_initFn____x40_Lean_ResolveName___hyg_392____lambda__1___closed__6();
lean_mark_persistent(l_Lean_initFn____x40_Lean_ResolveName___hyg_392____lambda__1___closed__6);
l_Lean_initFn____x40_Lean_ResolveName___hyg_392____closed__1 = _init_l_Lean_initFn____x40_Lean_ResolveName___hyg_392____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_ResolveName___hyg_392____closed__1);
l_Lean_initFn____x40_Lean_ResolveName___hyg_392____closed__2 = _init_l_Lean_initFn____x40_Lean_ResolveName___hyg_392____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_ResolveName___hyg_392____closed__2);
l_Lean_initFn____x40_Lean_ResolveName___hyg_392____closed__3 = _init_l_Lean_initFn____x40_Lean_ResolveName___hyg_392____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_ResolveName___hyg_392____closed__3);
l_Lean_initFn____x40_Lean_ResolveName___hyg_392____closed__4 = _init_l_Lean_initFn____x40_Lean_ResolveName___hyg_392____closed__4();
lean_mark_persistent(l_Lean_initFn____x40_Lean_ResolveName___hyg_392____closed__4);
l_Lean_initFn____x40_Lean_ResolveName___hyg_392____closed__5 = _init_l_Lean_initFn____x40_Lean_ResolveName___hyg_392____closed__5();
lean_mark_persistent(l_Lean_initFn____x40_Lean_ResolveName___hyg_392____closed__5);
l_Lean_initFn____x40_Lean_ResolveName___hyg_392____closed__6 = _init_l_Lean_initFn____x40_Lean_ResolveName___hyg_392____closed__6();
lean_mark_persistent(l_Lean_initFn____x40_Lean_ResolveName___hyg_392____closed__6);
l_Lean_initFn____x40_Lean_ResolveName___hyg_392____closed__7 = _init_l_Lean_initFn____x40_Lean_ResolveName___hyg_392____closed__7();
lean_mark_persistent(l_Lean_initFn____x40_Lean_ResolveName___hyg_392____closed__7);
if (builtin) {res = l_Lean_initFn____x40_Lean_ResolveName___hyg_392_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_aliasExtension = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_aliasExtension);
lean_dec_ref(res);
}l_Lean_addAlias___closed__1 = _init_l_Lean_addAlias___closed__1();
lean_mark_persistent(l_Lean_addAlias___closed__1);
l_Lean_getAliasState___closed__1 = _init_l_Lean_getAliasState___closed__1();
lean_mark_persistent(l_Lean_getAliasState___closed__1);
l_List_filterTR_loop___at_Lean_getAliases___spec__1___closed__1 = _init_l_List_filterTR_loop___at_Lean_getAliases___spec__1___closed__1();
lean_mark_persistent(l_List_filterTR_loop___at_Lean_getAliases___spec__1___closed__1);
l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__1 = _init_l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__1();
lean_mark_persistent(l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__1);
l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__2 = _init_l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__2();
lean_mark_persistent(l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__2);
l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__3 = _init_l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__3();
lean_mark_persistent(l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__3);
l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__4 = _init_l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__4();
lean_mark_persistent(l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__4);
l_Lean_resolveNamespaceCore___rarg___lambda__3___closed__1 = _init_l_Lean_resolveNamespaceCore___rarg___lambda__3___closed__1();
lean_mark_persistent(l_Lean_resolveNamespaceCore___rarg___lambda__3___closed__1);
l_Lean_resolveNamespaceCore___rarg___lambda__3___closed__2 = _init_l_Lean_resolveNamespaceCore___rarg___lambda__3___closed__2();
lean_mark_persistent(l_Lean_resolveNamespaceCore___rarg___lambda__3___closed__2);
l_Lean_resolveNamespaceCore___rarg___lambda__3___closed__3 = _init_l_Lean_resolveNamespaceCore___rarg___lambda__3___closed__3();
lean_mark_persistent(l_Lean_resolveNamespaceCore___rarg___lambda__3___closed__3);
l_Lean_resolveNamespace___rarg___closed__1 = _init_l_Lean_resolveNamespace___rarg___closed__1();
lean_mark_persistent(l_Lean_resolveNamespace___rarg___closed__1);
l_Lean_resolveNamespace___rarg___closed__2 = _init_l_Lean_resolveNamespace___rarg___closed__2();
lean_mark_persistent(l_Lean_resolveNamespace___rarg___closed__2);
l_Lean_resolveNamespace___rarg___closed__3 = _init_l_Lean_resolveNamespace___rarg___closed__3();
lean_mark_persistent(l_Lean_resolveNamespace___rarg___closed__3);
l_Lean_resolveUniqueNamespace___rarg___lambda__1___closed__1 = _init_l_Lean_resolveUniqueNamespace___rarg___lambda__1___closed__1();
lean_mark_persistent(l_Lean_resolveUniqueNamespace___rarg___lambda__1___closed__1);
l_Lean_resolveUniqueNamespace___rarg___lambda__1___closed__2 = _init_l_Lean_resolveUniqueNamespace___rarg___lambda__1___closed__2();
lean_mark_persistent(l_Lean_resolveUniqueNamespace___rarg___lambda__1___closed__2);
l_List_foldl___at_Lean_ensureNoOverload___spec__3___closed__1 = _init_l_List_foldl___at_Lean_ensureNoOverload___spec__3___closed__1();
lean_mark_persistent(l_List_foldl___at_Lean_ensureNoOverload___spec__3___closed__1);
l_List_toString___at_Lean_ensureNoOverload___spec__2___closed__1 = _init_l_List_toString___at_Lean_ensureNoOverload___spec__2___closed__1();
lean_mark_persistent(l_List_toString___at_Lean_ensureNoOverload___spec__2___closed__1);
l_List_toString___at_Lean_ensureNoOverload___spec__2___closed__2 = _init_l_List_toString___at_Lean_ensureNoOverload___spec__2___closed__2();
lean_mark_persistent(l_List_toString___at_Lean_ensureNoOverload___spec__2___closed__2);
l_List_toString___at_Lean_ensureNoOverload___spec__2___closed__3 = _init_l_List_toString___at_Lean_ensureNoOverload___spec__2___closed__3();
lean_mark_persistent(l_List_toString___at_Lean_ensureNoOverload___spec__2___closed__3);
l_Lean_ensureNoOverload___rarg___closed__1 = _init_l_Lean_ensureNoOverload___rarg___closed__1();
lean_mark_persistent(l_Lean_ensureNoOverload___rarg___closed__1);
l_Lean_ensureNoOverload___rarg___closed__2 = _init_l_Lean_ensureNoOverload___rarg___closed__2();
lean_mark_persistent(l_Lean_ensureNoOverload___rarg___closed__2);
l_Lean_ensureNoOverload___rarg___closed__3 = _init_l_Lean_ensureNoOverload___rarg___closed__3();
lean_mark_persistent(l_Lean_ensureNoOverload___rarg___closed__3);
l_Lean_ensureNonAmbiguous___rarg___closed__1 = _init_l_Lean_ensureNonAmbiguous___rarg___closed__1();
lean_mark_persistent(l_Lean_ensureNonAmbiguous___rarg___closed__1);
l_Lean_ensureNonAmbiguous___rarg___closed__2 = _init_l_Lean_ensureNonAmbiguous___rarg___closed__2();
lean_mark_persistent(l_Lean_ensureNonAmbiguous___rarg___closed__2);
l_Lean_unresolveNameGlobal_unresolveNameCore___rarg___lambda__2___closed__1 = _init_l_Lean_unresolveNameGlobal_unresolveNameCore___rarg___lambda__2___closed__1();
lean_mark_persistent(l_Lean_unresolveNameGlobal_unresolveNameCore___rarg___lambda__2___closed__1);
l_Lean_unresolveNameGlobal___rarg___lambda__1___closed__1 = _init_l_Lean_unresolveNameGlobal___rarg___lambda__1___closed__1();
lean_mark_persistent(l_Lean_unresolveNameGlobal___rarg___lambda__1___closed__1);
l_Lean_unresolveNameGlobalAvoidingLocals___rarg___lambda__1___closed__1 = _init_l_Lean_unresolveNameGlobalAvoidingLocals___rarg___lambda__1___closed__1();
lean_mark_persistent(l_Lean_unresolveNameGlobalAvoidingLocals___rarg___lambda__1___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
