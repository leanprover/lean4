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
static lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveExact___closed__0;
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___redArg___lam__17(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___Lean_addAliasEntry_spec__6___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn___lam__1___closed__7____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_;
lean_object* lean_format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveLocalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ensureNonAmbiguous___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverload___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f___at___Lean_addAliasEntry_spec__0_spec__0_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_resolveLocalName___redArg___lam__4___closed__9;
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at___Lean_PersistentHashMap_foldl___at___Lean_SMap_fold___at___Lean_getRevAliases_spec__0_spec__1_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveUniqueNamespace___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f___at___Lean_addAliasEntry_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_containsOnBranch(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_mkStateFromImportedEntries___at___Lean_initFn____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_ensureNonAmbiguous___redArg___closed__4;
lean_object* l_Lean_Syntax_formatStx(lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_resolveLocalName___redArg___lam__4___closed__3;
static lean_object* l_Lean_unresolveNameGlobal___redArg___lam__5___closed__0;
uint8_t l_Lean_MacroScopesView_isSuffixOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___redArg___lam__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
size_t lean_usize_shift_right(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___redArg___lam__16(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getRevAliases___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn___lam__1___closed__4____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_Lean_ensureNoOverload___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_eraseDups___at_____private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__0___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_private_to_user_name(lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__6_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0____x40_Lean_ResolveName_405991711____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static lean_object* l_Lean_resolveLocalName___redArg___lam__4___closed__8;
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadResolveNameOfMonadLift___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at___Lean_PersistentHashMap_foldl___at___Lean_SMap_fold___at___Lean_getRevAliases_spec__0_spec__1_spec__1_spec__1_spec__1___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Environment_header(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__6_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__11_spec__11___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___Lean_addAliasEntry_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__1;
LEAN_EXPORT uint8_t l_Lean_filterFieldList___redArg___lam__0(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
lean_object* l_List_mapTR_loop___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at___Lean_initFn____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__4___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___Lean_SMap_find_x3f___at___Lean_addAliasEntry_spec__0_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getRevAliases___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_unresolveNameCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f___at___Lean_addAliasEntry_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_resolveLocalName___redArg___lam__4___closed__0;
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
static lean_object* l_Lean_initFn___lam__1___closed__2____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_SMap_fold___at___Lean_getRevAliases_spec__0_spec__6___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_initFn___closed__0____x40_Lean_ResolveName_2351709485____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_go(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ensureNoOverload___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_SMap_fold___at___Lean_getRevAliases_spec__0_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_unresolveNameCore___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_registerEnvExtension___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_resolveNamespace___redArg___closed__0;
lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_mkStateFromImportedEntries___at___Lean_initFn____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__1(lean_object*, size_t, size_t, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___Lean_SMap_find_x3f___at___Lean_addAliasEntry_spec__0_spec__3_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___Lean_SMap_find_x3f___at___Lean_addAliasEntry_spec__0_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_unresolveNameCore___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___Lean_addAliasEntry_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
static lean_object* l_Lean_ensureNonAmbiguous___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_ensureNonAmbiguous___redArg___closed__6;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_mkStateFromImportedEntries___at___Lean_initFn____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f___at___Lean_addAliasEntry_spec__0_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at___Lean_PersistentHashMap_foldl___at___Lean_SMap_fold___at___Lean_getRevAliases_spec__0_spec__1_spec__1_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveUsingNamespace(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___redArg___lam__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_ensureNoOverload___redArg___closed__4;
lean_object* l_panic___redArg(lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___redArg___lam__6(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_resolveNamespace___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_filterFieldList(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___Lean_PersistentHashMap_foldl___at___Lean_SMap_fold___at___Lean_getRevAliases_spec__0_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___Lean_addAliasEntry_spec__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_ensureNoOverload___redArg___closed__1;
lean_object* l_List_filterTR_loop___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___redArg___lam__15(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_getAliasState(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_mkStateFromImportedEntries___at___Lean_initFn____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__2;
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwReservedNameNotAvailable___redArg___closed__2;
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__11_spec__12(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_____private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__11_spec__12_spec__12_spec__12(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_ensureNoOverload___redArg___closed__6;
static lean_object* l_Lean_initFn___closed__2____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___Lean_PersistentHashMap_foldl___at___Lean_SMap_fold___at___Lean_getRevAliases_spec__0_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___Lean_PersistentHashMap_foldl___at___Lean_SMap_fold___at___Lean_getRevAliases_spec__0_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_elem___at___Lean_addAliasEntry_spec__18___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___redArg___lam__12(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_SMap_fold___at___Lean_getRevAliases_spec__0_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_initializing(lean_object*);
LEAN_EXPORT uint8_t lean_is_reserved_name(lean_object*, lean_object*);
static lean_object* l_Lean_resolveNamespace___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___redArg___lam__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_resolveLocalName___redArg___lam__4___closed__5;
LEAN_EXPORT lean_object* l_Lean_resolveUniqueNamespace___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Option_isNone___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Expr_dbgToString___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__11_spec__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwReservedNameNotAvailable(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_registerReservedNamePredicate___closed__2;
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___Lean_getAliases_spec__0(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(lean_object*, lean_object*);
static lean_object* l_Lean_resolveUniqueNamespace___redArg___lam__0___closed__1;
static lean_object* l_Lean_isReservedName___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_____private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__11_spec__12_spec__12_spec__12___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_List_filterMapTR_go___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ResolveName_resolveNamespace(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0____x40_Lean_ResolveName_405991711____hygCtx___hyg_2_(lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___Lean_SMap_fold___at___Lean_getRevAliases_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_unresolveNameGlobalAvoidingLocals___redArg___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___Lean_SMap_find_x3f___at___Lean_addAliasEntry_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ensureReservedNameAvailable___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getRevAliases(lean_object*, lean_object*);
lean_object* l_Lean_Name_getPrefix(lean_object*);
static lean_object* l_Lean_throwReservedNameNotAvailable___redArg___closed__1;
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_panic___at___Lean_ResolveName_resolveNamespaceUsingScope_x3f_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___Lean_SMap_find_x3f___at___Lean_addAliasEntry_spec__0_spec__3___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_resolveLocalName___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__1____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ResolveName_resolveNamespaceUsingOpenDecls(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f___at___Lean_addAliasEntry_spec__0_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_SMap_fold___at___Lean_getRevAliases_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___Lean_PersistentHashMap_insertAtCollisionNode___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__6_spec__6_spec__6_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_unresolveNameCore___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_replacePrefix(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__6_spec__6_spec__8___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_unresolveNameCore___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at___Lean_initFn____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___redArg___lam__2(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_resolveNamespaceCore___redArg___lam__2___closed__1;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveNamespace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__11_spec__12_spec__12(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__11_spec__11(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
static lean_object* l_Lean_registerReservedNamePredicate___closed__1;
lean_object* l_List_forIn_x27_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at___Lean_addAliasEntry_spec__18(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___Lean_getAliases_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at___Lean_PersistentHashMap_foldl___at___Lean_SMap_fold___at___Lean_getRevAliases_spec__0_spec__1_spec__1_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ensureNonAmbiguous(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveUniqueNamespace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_privateToUserName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___redArg___lam__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwReservedNameNotAvailable___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at___Lean_PersistentHashMap_foldl___at___Lean_SMap_fold___at___Lean_getRevAliases_spec__0_spec__1_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_mk_io_user_error(lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveNamespace___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___redArg___lam__11(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_mkStateFromImportedEntries___at___Lean_initFn____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_resolveNamespaceCore___redArg___lam__2___closed__0;
uint8_t l_Lean_isProtected(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f___at___Lean_addAliasEntry_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_extractMacroScopes(lean_object*);
lean_object* l_Lean_Name_componentsRev(lean_object*);
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_rootNamespace;
static lean_object* l_Lean_resolveNamespace___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_ResolveName_resolveNamespaceUsingScope_x3f(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_ensureNonAmbiguous___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___Lean_getRevAliases_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn___closed__0____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_unresolveNameCore___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_ensureNoOverload___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_reservedNamePredicatesExt;
static lean_object* l_Lean_initFn___lam__1___closed__5____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveNamespace___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg___lam__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_ensureNonAmbiguous___redArg___closed__1;
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* l_Lean_throwUnknownConstantAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_isAuxDecl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___redArg___lam__13(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___redArg___lam__7(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_ensureNonAmbiguous___redArg___closed__2;
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveQualifiedName(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Lean_MacroScopesView_review(lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveNamespace___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___Lean_SMap_find_x3f___at___Lean_addAliasEntry_spec__0_spec__3_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerReservedNamePredicate(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_add_alias(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_SMap_fold___at___Lean_getRevAliases_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__6_spec__6___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverload(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_resolveLocalName___redArg___lam__4___closed__7;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg___lam__1(lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_Environment_isNamespace(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at___Lean_PersistentHashMap_foldl___at___Lean_SMap_fold___at___Lean_getRevAliases_spec__0_spec__1_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getAliases___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___Lean_addAliasEntry_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn___closed__1____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_;
static lean_object* l_Lean_resolveLocalName___redArg___lam__4___closed__4;
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___redArg___lam__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__11_spec__15(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(lean_object*, uint8_t);
static lean_object* l_Lean_throwReservedNameNotAvailable___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_instMonadResolveNameOfMonadLift(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
static lean_object* l_Lean_initFn___lam__1___closed__3____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at___Lean_PersistentHashMap_foldl___at___Lean_SMap_fold___at___Lean_getRevAliases_spec__0_spec__1_spec__1_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_ensureNonAmbiguous___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_resolveUniqueNamespace___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverloadCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverload___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___Lean_initFn____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_getAliasState___closed__2;
static lean_object* l_Lean_initFn___lam__1___closed__0____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f___at___Lean_addAliasEntry_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__6_spec__6_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Name_instToString___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_ResolveName_2351709485____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___redArg___lam__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___Lean_SMap_find_x3f___at___Lean_addAliasEntry_spec__0_spec__3_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_reservedNamePredicatesRef;
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___Lean_getRevAliases_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___Lean_SMap_fold___at___Lean_getRevAliases_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__6_spec__6_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_appendCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isAtomic(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ensureReservedNameAvailable___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isReservedName___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__6_spec__6_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_unresolveNameCore___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwReservedNameNotAvailable___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___Lean_PersistentHashMap_insertAtCollisionNode___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__6_spec__6_spec__6_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_unresolveNameCore___redArg___lam__6___closed__0;
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__6_spec__6_spec__8(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__6_spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
static lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName___closed__0;
static lean_object* l_Lean_initFn___lam__1___closed__1____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_;
static lean_object* l_Lean_resolveUniqueNamespace___redArg___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___Lean_SMap_fold___at___Lean_getRevAliases_spec__0_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static size_t l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f___at___Lean_addAliasEntry_spec__0_spec__0_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_unresolveNameCore___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__2(lean_object*, uint8_t, lean_object*);
static lean_object* l_Lean_isReservedName___closed__1;
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lean_isReservedName_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveOpenDecls(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_resolveUniqueNamespace___redArg___closed__0;
static lean_object* l_Lean_throwReservedNameNotAvailable___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_unresolveNameCore___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static size_t l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f___at___Lean_addAliasEntry_spec__0_spec__0_spec__0___redArg___closed__0;
uint64_t l_Lean_Name_hash___override(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__1____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_mkStateFromImportedEntries___at___Lean_initFn____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__1_spec__1(lean_object*, size_t, size_t, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___Lean_getRevAliases_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_SMap_fold___at___Lean_getRevAliases_spec__0_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at___Lean_PersistentHashMap_foldl___at___Lean_SMap_fold___at___Lean_getRevAliases_spec__0_spec__1_spec__1_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_resolveLocalName___redArg___lam__4___closed__6;
lean_object* l_List_toString___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addAliasEntry(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ensureReservedNameAvailable(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getAliasState___closed__1;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_____private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__11_spec__15___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__11___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ensureNoOverload(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_registerReservedNamePredicate___closed__0;
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_unresolveNameCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addAlias___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f___at___Lean_addAliasEntry_spec__0_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___redArg___lam__0(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f___at___Lean_addAliasEntry_spec__0_spec__0_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___Lean_addAliasEntry_spec__0___redArg___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_initFn___closed__3____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_;
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l_List_eraseDups___at_____private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at___Lean_PersistentHashMap_foldl___at___Lean_SMap_fold___at___Lean_getRevAliases_spec__0_spec__1_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
static lean_object* l_Lean_resolveLocalName___redArg___lam__4___closed__1;
uint8_t l_Lean_Name_quickCmp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___Lean_SMap_fold___at___Lean_getRevAliases_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__3;
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___Lean_initFn____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___redArg___lam__9(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at___Lean_PersistentHashMap_foldl___at___Lean_SMap_fold___at___Lean_getRevAliases_spec__0_spec__1_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_unresolveNameCore___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverloadCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_eraseDups___at_____private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__0___lam__0(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f___at___Lean_addAliasEntry_spec__0_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_ensureNoOverload___redArg___closed__0;
static lean_object* l_Lean_initFn___lam__1___closed__6____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
static lean_object* l_Lean_throwReservedNameNotAvailable___redArg___closed__4;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___Lean_SMap_fold___at___Lean_getRevAliases_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_getAliasState___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveExact(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f___at___Lean_addAliasEntry_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___Lean_SMap_find_x3f___at___Lean_addAliasEntry_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverloadCore___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_ResolveName_405991711____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___Lean_getRevAliases_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__6_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_List_eraseDupsBy___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__0;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__6_spec__6___redArg___closed__0;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__11_spec__11___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lean_isReservedName_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at___Lean_PersistentHashMap_foldl___at___Lean_SMap_fold___at___Lean_getRevAliases_spec__0_spec__1_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_unresolveNameCore___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_resolveLocalName___redArg___lam__4___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__3(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f___at___Lean_addAliasEntry_spec__0_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__11_spec__12___redArg(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__11_spec__12_spec__12___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_mkPrivateNameCore(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_ensureNoOverload___redArg___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg___lam__3(lean_object*, lean_object*);
static lean_object* l_Lean_ensureNoOverload___redArg___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at___Lean_PersistentHashMap_foldl___at___Lean_SMap_fold___at___Lean_getRevAliases_spec__0_spec__1_spec__1_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___redArg___lam__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__6___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
size_t lean_usize_land(size_t, size_t);
lean_object* l_Lean_throwErrorAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_aliasExtension;
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveNamespace___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___Lean_PersistentHashMap_foldl___at___Lean_SMap_fold___at___Lean_getRevAliases_spec__0_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getAliases(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT uint8_t l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__0(lean_object*);
static lean_object* _init_l_Lean_throwReservedNameNotAvailable___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed to declare `", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_throwReservedNameNotAvailable___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwReservedNameNotAvailable___redArg___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwReservedNameNotAvailable___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("` because `", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_throwReservedNameNotAvailable___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwReservedNameNotAvailable___redArg___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwReservedNameNotAvailable___redArg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("` has already been declared", 27, 27);
return x_1;
}
}
static lean_object* _init_l_Lean_throwReservedNameNotAvailable___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwReservedNameNotAvailable___redArg___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwReservedNameNotAvailable___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_5 = l_Lean_throwReservedNameNotAvailable___redArg___closed__1;
x_6 = 0;
x_7 = l_Lean_MessageData_ofConstName(x_3, x_6);
x_8 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_7);
x_9 = l_Lean_throwReservedNameNotAvailable___redArg___closed__3;
x_10 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = 1;
x_12 = l_Lean_MessageData_ofConstName(x_4, x_11);
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Lean_throwReservedNameNotAvailable___redArg___closed__5;
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_throwError___redArg(x_1, x_2, x_15);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_throwReservedNameNotAvailable(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwReservedNameNotAvailable___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureReservedNameAvailable___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_8; 
x_7 = 1;
lean_inc(x_1);
x_8 = l_Lean_Environment_contains(x_6, x_1, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_dec_ref(x_2);
x_10 = lean_box(0);
x_11 = lean_apply_2(x_9, lean_box(0), x_10);
return x_11;
}
else
{
lean_object* x_12; 
lean_dec_ref(x_2);
x_12 = l_Lean_throwReservedNameNotAvailable___redArg(x_3, x_4, x_5, x_1);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureReservedNameAvailable___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec_ref(x_2);
lean_inc(x_4);
x_9 = l_Lean_Name_str___override(x_4, x_5);
x_10 = lean_alloc_closure((void*)(l_Lean_ensureReservedNameAvailable___redArg___lam__0), 6, 5);
lean_closure_set(x_10, 0, x_9);
lean_closure_set(x_10, 1, x_6);
lean_closure_set(x_10, 2, x_1);
lean_closure_set(x_10, 3, x_3);
lean_closure_set(x_10, 4, x_4);
x_11 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_8, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureReservedNameAvailable(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_ensureReservedNameAvailable___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_ResolveName_2351709485____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_ResolveName_2351709485____hygCtx___hyg_2_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l_Lean_initFn___closed__0____x40_Lean_ResolveName_2351709485____hygCtx___hyg_2_;
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
static lean_object* _init_l_Lean_registerReservedNamePredicate___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed to register reserved name suffix predicate, this operation can only be performed during initialization", 109, 109);
return x_1;
}
}
static lean_object* _init_l_Lean_registerReservedNamePredicate___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_registerReservedNamePredicate___closed__0;
x_2 = lean_mk_io_user_error(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_registerReservedNamePredicate___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_reservedNamePredicatesRef;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_registerReservedNamePredicate(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_initializing(x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_unbox(x_4);
lean_dec(x_4);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec_ref(x_1);
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_3, 0);
lean_dec(x_7);
x_8 = l_Lean_registerReservedNamePredicate___closed__1;
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
x_10 = l_Lean_registerReservedNamePredicate___closed__1;
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_dec_ref(x_3);
x_13 = l_Lean_registerReservedNamePredicate___closed__2;
x_14 = lean_st_ref_take(x_13, x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec_ref(x_14);
x_17 = lean_array_push(x_15, x_1);
x_18 = lean_st_ref_set(x_13, x_17, x_16);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
return x_18;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
else
{
uint8_t x_23; 
lean_dec_ref(x_1);
x_23 = !lean_is_exclusive(x_3);
if (x_23 == 0)
{
return x_3;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_3, 0);
x_25 = lean_ctor_get(x_3, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_3);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0____x40_Lean_ResolveName_405991711____hygCtx___hyg_2_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_st_ref_get(x_1, x_2);
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
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_ResolveName_405991711____hygCtx___hyg_2_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_registerReservedNamePredicate___closed__2;
x_3 = lean_alloc_closure((void*)(l_Lean_initFn___lam__0____x40_Lean_ResolveName_405991711____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = lean_box(0);
x_5 = lean_box(2);
x_6 = l_Lean_registerEnvExtension___redArg(x_3, x_4, x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0____x40_Lean_ResolveName_405991711____hygCtx___hyg_2____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_initFn___lam__0____x40_Lean_ResolveName_405991711____hygCtx___hyg_2_(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lean_isReservedName_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_array_uget(x_3, x_4);
lean_inc(x_2);
lean_inc_ref(x_1);
x_8 = lean_apply_2(x_7, x_1, x_2);
x_9 = lean_unbox(x_8);
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
lean_dec_ref(x_1);
x_13 = lean_unbox(x_8);
return x_13;
}
}
else
{
uint8_t x_14; 
lean_dec(x_2);
lean_dec_ref(x_1);
x_14 = 0;
return x_14;
}
}
}
static lean_object* _init_l_Lean_isReservedName___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_reservedNamePredicatesExt;
return x_1;
}
}
static lean_object* _init_l_Lean_isReservedName___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty(lean_box(0));
return x_1;
}
}
LEAN_EXPORT uint8_t lean_is_reserved_name(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_3 = l_Lean_isReservedName___closed__0;
x_4 = lean_ctor_get(x_3, 2);
lean_inc(x_4);
x_5 = l_Lean_isReservedName___closed__1;
x_6 = lean_box(0);
lean_inc_ref(x_1);
x_7 = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(x_5, x_3, x_1, x_4, x_6);
lean_dec(x_4);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_get_size(x_7);
x_10 = lean_nat_dec_lt(x_8, x_9);
if (x_10 == 0)
{
lean_dec(x_9);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_10;
}
else
{
if (x_10 == 0)
{
lean_dec(x_9);
lean_dec_ref(x_7);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_10;
}
else
{
size_t x_11; size_t x_12; uint8_t x_13; 
x_11 = 0;
x_12 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_13 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lean_isReservedName_spec__0(x_1, x_2, x_7, x_11, x_12);
lean_dec_ref(x_7);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lean_isReservedName_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___Lean_isReservedName_spec__0(x_1, x_2, x_3, x_6, x_7);
lean_dec_ref(x_3);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_isReservedName___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_is_reserved_name(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f___at___Lean_addAliasEntry_spec__0_spec__0_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_1);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_3);
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_fget_borrowed(x_1, x_3);
x_9 = lean_name_eq(x_4, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_3, x_10);
lean_dec(x_3);
x_3 = x_11;
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_array_fget_borrowed(x_2, x_3);
lean_dec(x_3);
lean_inc(x_13);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f___at___Lean_addAliasEntry_spec__0_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f___at___Lean_addAliasEntry_spec__0_spec__0_spec__0_spec__0___redArg(x_2, x_3, x_5, x_6);
return x_7;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f___at___Lean_addAliasEntry_spec__0_spec__0_spec__0___redArg___closed__0() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 5;
x_2 = 1;
x_3 = lean_usize_shift_left(x_2, x_1);
return x_3;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f___at___Lean_addAliasEntry_spec__0_spec__0_spec__0___redArg___closed__1() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f___at___Lean_addAliasEntry_spec__0_spec__0_spec__0___redArg___closed__0;
x_3 = lean_usize_sub(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f___at___Lean_addAliasEntry_spec__0_spec__0_spec__0___redArg(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_box(2);
x_7 = 5;
x_8 = l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f___at___Lean_addAliasEntry_spec__0_spec__0_spec__0___redArg___closed__1;
x_9 = lean_usize_land(x_2, x_8);
x_10 = lean_usize_to_nat(x_9);
x_11 = lean_array_get(x_6, x_5, x_10);
lean_dec(x_10);
lean_dec_ref(x_5);
switch (lean_obj_tag(x_11)) {
case 0:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
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
lean_dec_ref(x_11);
x_17 = lean_usize_shift_right(x_2, x_7);
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
lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; size_t x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
lean_dec(x_1);
x_21 = lean_box(2);
x_22 = 5;
x_23 = l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f___at___Lean_addAliasEntry_spec__0_spec__0_spec__0___redArg___closed__1;
x_24 = lean_usize_land(x_2, x_23);
x_25 = lean_usize_to_nat(x_24);
x_26 = lean_array_get(x_21, x_20, x_25);
lean_dec(x_25);
lean_dec_ref(x_20);
switch (lean_obj_tag(x_26)) {
case 0:
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec_ref(x_26);
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
lean_dec_ref(x_26);
x_33 = lean_usize_shift_right(x_2, x_22);
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
lean_inc_ref(x_36);
x_37 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_37);
lean_dec_ref(x_1);
x_38 = lean_unsigned_to_nat(0u);
x_39 = l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f___at___Lean_addAliasEntry_spec__0_spec__0_spec__0_spec__0___redArg(x_36, x_37, x_38, x_3);
lean_dec_ref(x_37);
lean_dec_ref(x_36);
return x_39;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f___at___Lean_addAliasEntry_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f___at___Lean_addAliasEntry_spec__0_spec__0_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f___at___Lean_addAliasEntry_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; size_t x_4; lean_object* x_5; 
x_3 = l_Lean_Name_hash___override(x_2);
x_4 = lean_uint64_to_usize(x_3);
x_5 = l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f___at___Lean_addAliasEntry_spec__0_spec__0_spec__0___redArg(x_1, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f___at___Lean_addAliasEntry_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f___at___Lean_addAliasEntry_spec__0_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___Lean_SMap_find_x3f___at___Lean_addAliasEntry_spec__0_spec__3_spec__3___redArg(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___Lean_SMap_find_x3f___at___Lean_addAliasEntry_spec__0_spec__3_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___Lean_SMap_find_x3f___at___Lean_addAliasEntry_spec__0_spec__3_spec__3___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___Lean_SMap_find_x3f___at___Lean_addAliasEntry_spec__0_spec__3___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Name_hash___override(x_2);
x_6 = 32;
x_7 = lean_uint64_shift_right(x_5, x_6);
x_8 = lean_uint64_xor(x_5, x_7);
x_9 = 16;
x_10 = lean_uint64_shift_right(x_8, x_9);
x_11 = lean_uint64_xor(x_8, x_10);
x_12 = lean_uint64_to_usize(x_11);
x_13 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_14 = 1;
x_15 = lean_usize_sub(x_13, x_14);
x_16 = lean_usize_land(x_12, x_15);
x_17 = lean_array_uget(x_3, x_16);
x_18 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___Lean_SMap_find_x3f___at___Lean_addAliasEntry_spec__0_spec__3_spec__3___redArg(x_2, x_17);
lean_dec(x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___Lean_SMap_find_x3f___at___Lean_addAliasEntry_spec__0_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___Lean_SMap_find_x3f___at___Lean_addAliasEntry_spec__0_spec__3___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___Lean_addAliasEntry_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_5);
lean_dec_ref(x_1);
x_6 = l_Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f___at___Lean_addAliasEntry_spec__0_spec__0___redArg(x_5, x_2);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___Lean_SMap_find_x3f___at___Lean_addAliasEntry_spec__0_spec__3___redArg(x_4, x_2);
lean_dec_ref(x_4);
return x_7;
}
else
{
lean_dec_ref(x_4);
return x_6;
}
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_8);
lean_dec_ref(x_1);
x_9 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___Lean_SMap_find_x3f___at___Lean_addAliasEntry_spec__0_spec__3___redArg(x_8, x_2);
lean_dec_ref(x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___Lean_addAliasEntry_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_SMap_find_x3f___at___Lean_addAliasEntry_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___Lean_PersistentHashMap_insertAtCollisionNode___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__6_spec__6_spec__6_spec__6___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_array_get_size(x_6);
x_9 = lean_nat_dec_lt(x_2, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
x_10 = lean_array_push(x_6, x_3);
x_11 = lean_array_push(x_7, x_4);
lean_ctor_set(x_1, 1, x_11);
lean_ctor_set(x_1, 0, x_10);
return x_1;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_fget_borrowed(x_6, x_2);
x_13 = lean_name_eq(x_3, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_2, x_14);
lean_dec(x_2);
x_2 = x_15;
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_array_fset(x_6, x_2, x_3);
x_18 = lean_array_fset(x_7, x_2, x_4);
lean_dec(x_2);
lean_ctor_set(x_1, 1, x_18);
lean_ctor_set(x_1, 0, x_17);
return x_1;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_1, 0);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_1);
x_21 = lean_array_get_size(x_19);
x_22 = lean_nat_dec_lt(x_2, x_21);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_2);
x_23 = lean_array_push(x_19, x_3);
x_24 = lean_array_push(x_20, x_4);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
else
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_array_fget_borrowed(x_19, x_2);
x_27 = lean_name_eq(x_3, x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_19);
lean_ctor_set(x_28, 1, x_20);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_add(x_2, x_29);
lean_dec(x_2);
x_1 = x_28;
x_2 = x_30;
goto _start;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_array_fset(x_19, x_2, x_3);
x_33 = lean_array_fset(x_20, x_2, x_4);
lean_dec(x_2);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___Lean_PersistentHashMap_insertAtCollisionNode___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__6_spec__6_spec__6_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___Lean_PersistentHashMap_insertAtCollisionNode___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__6_spec__6_spec__6_spec__6___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__6_spec__6_spec__6___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___Lean_PersistentHashMap_insertAtCollisionNode___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__6_spec__6_spec__6_spec__6___redArg(x_1, x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__6_spec__6_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_insertAtCollisionNode___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__6_spec__6_spec__6___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__6_spec__6_spec__8___redArg(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; uint64_t x_10; size_t x_11; size_t x_12; lean_object* x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; 
x_8 = lean_array_fget_borrowed(x_2, x_4);
x_9 = lean_array_fget_borrowed(x_3, x_4);
x_10 = l_Lean_Name_hash___override(x_8);
x_11 = lean_uint64_to_usize(x_10);
x_12 = 5;
x_13 = lean_unsigned_to_nat(1u);
x_14 = 1;
x_15 = lean_usize_sub(x_1, x_14);
x_16 = lean_usize_mul(x_12, x_15);
x_17 = lean_usize_shift_right(x_11, x_16);
x_18 = lean_nat_add(x_4, x_13);
lean_dec(x_4);
lean_inc(x_9);
lean_inc(x_8);
x_19 = l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__6_spec__6___redArg(x_5, x_17, x_1, x_8, x_9);
x_4 = x_18;
x_5 = x_19;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__6_spec__6_spec__8(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__6_spec__6_spec__8___redArg(x_2, x_3, x_4, x_6, x_7);
return x_8;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__6_spec__6___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__6_spec__6___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; size_t x_7; size_t x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = 5;
x_8 = 1;
x_9 = l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f___at___Lean_addAliasEntry_spec__0_spec__0_spec__0___redArg___closed__1;
x_10 = lean_usize_land(x_2, x_9);
x_11 = lean_usize_to_nat(x_10);
x_12 = lean_array_get_size(x_6);
x_13 = lean_nat_dec_lt(x_11, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_4);
return x_1;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_inc_ref(x_6);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_14 = x_1;
} else {
 lean_dec_ref(x_1);
 x_14 = lean_box(0);
}
x_15 = lean_array_fget(x_6, x_11);
x_16 = lean_box(0);
x_17 = lean_array_fset(x_6, x_11, x_16);
switch (lean_obj_tag(x_15)) {
case 0:
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_15);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_15, 0);
x_24 = lean_ctor_get(x_15, 1);
x_25 = lean_name_eq(x_4, x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_free_object(x_15);
x_26 = l_Lean_PersistentHashMap_mkCollisionNode___redArg(x_23, x_24, x_4, x_5);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_18 = x_27;
goto block_21;
}
else
{
lean_dec(x_24);
lean_dec(x_23);
lean_ctor_set(x_15, 1, x_5);
lean_ctor_set(x_15, 0, x_4);
x_18 = x_15;
goto block_21;
}
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_ctor_get(x_15, 0);
x_29 = lean_ctor_get(x_15, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_15);
x_30 = lean_name_eq(x_4, x_28);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = l_Lean_PersistentHashMap_mkCollisionNode___redArg(x_28, x_29, x_4, x_5);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_18 = x_32;
goto block_21;
}
else
{
lean_object* x_33; 
lean_dec(x_29);
lean_dec(x_28);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_4);
lean_ctor_set(x_33, 1, x_5);
x_18 = x_33;
goto block_21;
}
}
}
case 1:
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_15);
if (x_34 == 0)
{
lean_object* x_35; size_t x_36; size_t x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_15, 0);
x_36 = lean_usize_shift_right(x_2, x_7);
x_37 = lean_usize_add(x_3, x_8);
x_38 = l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__6_spec__6___redArg(x_35, x_36, x_37, x_4, x_5);
lean_ctor_set(x_15, 0, x_38);
x_18 = x_15;
goto block_21;
}
else
{
lean_object* x_39; size_t x_40; size_t x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_15, 0);
lean_inc(x_39);
lean_dec(x_15);
x_40 = lean_usize_shift_right(x_2, x_7);
x_41 = lean_usize_add(x_3, x_8);
x_42 = l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__6_spec__6___redArg(x_39, x_40, x_41, x_4, x_5);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_18 = x_43;
goto block_21;
}
}
default: 
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_4);
lean_ctor_set(x_44, 1, x_5);
x_18 = x_44;
goto block_21;
}
}
block_21:
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_array_fset(x_17, x_11, x_18);
lean_dec(x_11);
if (lean_is_scalar(x_14)) {
 x_20 = lean_alloc_ctor(0, 1, 0);
} else {
 x_20 = x_14;
}
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
else
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_1);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; size_t x_54; uint8_t x_55; 
x_46 = l_Lean_PersistentHashMap_insertAtCollisionNode___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__6_spec__6_spec__6___redArg(x_1, x_4, x_5);
x_54 = 7;
x_55 = lean_usize_dec_le(x_54, x_3);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_56 = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(x_46);
x_57 = lean_unsigned_to_nat(4u);
x_58 = lean_nat_dec_lt(x_56, x_57);
lean_dec(x_56);
x_47 = x_58;
goto block_53;
}
else
{
x_47 = x_55;
goto block_53;
}
block_53:
{
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_48 = lean_ctor_get(x_46, 0);
lean_inc_ref(x_48);
x_49 = lean_ctor_get(x_46, 1);
lean_inc_ref(x_49);
lean_dec_ref(x_46);
x_50 = lean_unsigned_to_nat(0u);
x_51 = l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__6_spec__6___redArg___closed__0;
x_52 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__6_spec__6_spec__8___redArg(x_3, x_48, x_49, x_50, x_51);
lean_dec_ref(x_49);
lean_dec_ref(x_48);
return x_52;
}
else
{
return x_46;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; size_t x_70; uint8_t x_71; 
x_59 = lean_ctor_get(x_1, 0);
x_60 = lean_ctor_get(x_1, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_1);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = l_Lean_PersistentHashMap_insertAtCollisionNode___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__6_spec__6_spec__6___redArg(x_61, x_4, x_5);
x_70 = 7;
x_71 = lean_usize_dec_le(x_70, x_3);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_72 = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(x_62);
x_73 = lean_unsigned_to_nat(4u);
x_74 = lean_nat_dec_lt(x_72, x_73);
lean_dec(x_72);
x_63 = x_74;
goto block_69;
}
else
{
x_63 = x_71;
goto block_69;
}
block_69:
{
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_64 = lean_ctor_get(x_62, 0);
lean_inc_ref(x_64);
x_65 = lean_ctor_get(x_62, 1);
lean_inc_ref(x_65);
lean_dec_ref(x_62);
x_66 = lean_unsigned_to_nat(0u);
x_67 = l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__6_spec__6___redArg___closed__0;
x_68 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__6_spec__6_spec__8___redArg(x_3, x_64, x_65, x_66, x_67);
lean_dec_ref(x_65);
lean_dec_ref(x_64);
return x_68;
}
else
{
return x_62;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__6_spec__6(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__6_spec__6___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__6___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; size_t x_5; size_t x_6; lean_object* x_7; 
x_4 = l_Lean_Name_hash___override(x_2);
x_5 = lean_uint64_to_usize(x_4);
x_6 = 1;
x_7 = l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__6_spec__6___redArg(x_1, x_5, x_6, x_2, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__6___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__11_spec__11___redArg(lean_object* x_1, lean_object* x_2) {
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
return x_6;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__11_spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__11_spec__11___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_____private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__11_spec__12_spec__12_spec__12___redArg(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_____private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__11_spec__12_spec__12_spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at_____private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__11_spec__12_spec__12_spec__12___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__11_spec__12_spec__12___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at_____private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__11_spec__12_spec__12_spec__12___redArg(x_3, x_6);
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
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__11_spec__12_spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__11_spec__12_spec__12___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__11_spec__12___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
lean_dec(x_2);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_4, x_6);
x_8 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__11_spec__12_spec__12___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__11_spec__12(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__11_spec__12___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__11_spec__15___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 2);
x_8 = lean_name_eq(x_5, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_Std_DHashMap_Internal_AssocList_replace___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__11_spec__15___redArg(x_1, x_2, x_7);
lean_ctor_set(x_3, 2, x_9);
return x_3;
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
x_12 = lean_ctor_get(x_3, 2);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_13 = lean_name_eq(x_10, x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Std_DHashMap_Internal_AssocList_replace___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__11_spec__15___redArg(x_1, x_2, x_12);
x_15 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set(x_15, 2, x_14);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_10);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_2);
lean_ctor_set(x_16, 2, x_12);
return x_16;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__11_spec__15(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_replace___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__11_spec__15___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__11___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; lean_object* x_20; uint8_t x_21; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = l_Lean_Name_hash___override(x_2);
x_9 = 32;
x_10 = lean_uint64_shift_right(x_8, x_9);
x_11 = lean_uint64_xor(x_8, x_10);
x_12 = 16;
x_13 = lean_uint64_shift_right(x_11, x_12);
x_14 = lean_uint64_xor(x_11, x_13);
x_15 = lean_uint64_to_usize(x_14);
x_16 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_17 = 1;
x_18 = lean_usize_sub(x_16, x_17);
x_19 = lean_usize_land(x_15, x_18);
x_20 = lean_array_uget(x_6, x_19);
x_21 = l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__11_spec__11___redArg(x_2, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_5, x_22);
lean_dec(x_5);
x_24 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_24, 0, x_2);
lean_ctor_set(x_24, 1, x_3);
lean_ctor_set(x_24, 2, x_20);
x_25 = lean_array_uset(x_6, x_19, x_24);
x_26 = lean_unsigned_to_nat(4u);
x_27 = lean_nat_mul(x_23, x_26);
x_28 = lean_unsigned_to_nat(3u);
x_29 = lean_nat_div(x_27, x_28);
lean_dec(x_27);
x_30 = lean_array_get_size(x_25);
x_31 = lean_nat_dec_le(x_29, x_30);
lean_dec(x_30);
lean_dec(x_29);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__11_spec__12___redArg(x_25);
lean_ctor_set(x_1, 1, x_32);
lean_ctor_set(x_1, 0, x_23);
return x_1;
}
else
{
lean_ctor_set(x_1, 1, x_25);
lean_ctor_set(x_1, 0, x_23);
return x_1;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_box(0);
x_34 = lean_array_uset(x_6, x_19, x_33);
x_35 = l_Std_DHashMap_Internal_AssocList_replace___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__11_spec__15___redArg(x_2, x_3, x_20);
x_36 = lean_array_uset(x_34, x_19, x_35);
lean_ctor_set(x_1, 1, x_36);
return x_1;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint64_t x_40; uint64_t x_41; uint64_t x_42; uint64_t x_43; uint64_t x_44; uint64_t x_45; uint64_t x_46; size_t x_47; size_t x_48; size_t x_49; size_t x_50; size_t x_51; lean_object* x_52; uint8_t x_53; 
x_37 = lean_ctor_get(x_1, 0);
x_38 = lean_ctor_get(x_1, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_1);
x_39 = lean_array_get_size(x_38);
x_40 = l_Lean_Name_hash___override(x_2);
x_41 = 32;
x_42 = lean_uint64_shift_right(x_40, x_41);
x_43 = lean_uint64_xor(x_40, x_42);
x_44 = 16;
x_45 = lean_uint64_shift_right(x_43, x_44);
x_46 = lean_uint64_xor(x_43, x_45);
x_47 = lean_uint64_to_usize(x_46);
x_48 = lean_usize_of_nat(x_39);
lean_dec(x_39);
x_49 = 1;
x_50 = lean_usize_sub(x_48, x_49);
x_51 = lean_usize_land(x_47, x_50);
x_52 = lean_array_uget(x_38, x_51);
x_53 = l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__11_spec__11___redArg(x_2, x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_54 = lean_unsigned_to_nat(1u);
x_55 = lean_nat_add(x_37, x_54);
lean_dec(x_37);
x_56 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_56, 0, x_2);
lean_ctor_set(x_56, 1, x_3);
lean_ctor_set(x_56, 2, x_52);
x_57 = lean_array_uset(x_38, x_51, x_56);
x_58 = lean_unsigned_to_nat(4u);
x_59 = lean_nat_mul(x_55, x_58);
x_60 = lean_unsigned_to_nat(3u);
x_61 = lean_nat_div(x_59, x_60);
lean_dec(x_59);
x_62 = lean_array_get_size(x_57);
x_63 = lean_nat_dec_le(x_61, x_62);
lean_dec(x_62);
lean_dec(x_61);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__11_spec__12___redArg(x_57);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_55);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
else
{
lean_object* x_66; 
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_55);
lean_ctor_set(x_66, 1, x_57);
return x_66;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_67 = lean_box(0);
x_68 = lean_array_uset(x_38, x_51, x_67);
x_69 = l_Std_DHashMap_Internal_AssocList_replace___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__11_spec__15___redArg(x_2, x_3, x_52);
x_70 = lean_array_uset(x_68, x_51, x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_37);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__11___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___Lean_addAliasEntry_spec__6___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__6___redArg(x_6, x_2, x_3);
lean_ctor_set(x_1, 1, x_7);
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
x_10 = l_Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__6___redArg(x_9, x_2, x_3);
x_11 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*2, x_4);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_1);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__11___redArg(x_13, x_2, x_3);
lean_ctor_set(x_1, 0, x_14);
return x_1;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_1, 0);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_1);
x_17 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__11___redArg(x_15, x_2, x_3);
x_18 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
lean_ctor_set_uint8(x_18, sizeof(void*)*2, x_4);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___Lean_addAliasEntry_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_SMap_insert___at___Lean_addAliasEntry_spec__6___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___Lean_addAliasEntry_spec__18(lean_object* x_1, lean_object* x_2) {
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
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addAliasEntry(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_1);
x_6 = l_Lean_SMap_find_x3f___at___Lean_addAliasEntry_spec__0___redArg(x_1, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
lean_ctor_set_tag(x_2, 1);
lean_ctor_set(x_2, 1, x_7);
lean_ctor_set(x_2, 0, x_5);
x_8 = l_Lean_SMap_insert___at___Lean_addAliasEntry_spec__6___redArg(x_1, x_4, x_2);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec_ref(x_6);
x_10 = l_List_elem___at___Lean_addAliasEntry_spec__18(x_5, x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_ctor_set_tag(x_2, 1);
lean_ctor_set(x_2, 1, x_9);
lean_ctor_set(x_2, 0, x_5);
x_11 = l_Lean_SMap_insert___at___Lean_addAliasEntry_spec__6___redArg(x_1, x_4, x_2);
return x_11;
}
else
{
lean_dec(x_9);
lean_free_object(x_2);
lean_dec(x_5);
lean_dec(x_4);
return x_1;
}
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_2);
lean_inc_ref(x_1);
x_14 = l_Lean_SMap_find_x3f___at___Lean_addAliasEntry_spec__0___redArg(x_1, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_SMap_insert___at___Lean_addAliasEntry_spec__6___redArg(x_1, x_12, x_16);
return x_17;
}
else
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_14, 0);
lean_inc(x_18);
lean_dec_ref(x_14);
x_19 = l_List_elem___at___Lean_addAliasEntry_spec__18(x_13, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_13);
lean_ctor_set(x_20, 1, x_18);
x_21 = l_Lean_SMap_insert___at___Lean_addAliasEntry_spec__6___redArg(x_1, x_12, x_20);
return x_21;
}
else
{
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_12);
return x_1;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f___at___Lean_addAliasEntry_spec__0_spec__0_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f___at___Lean_addAliasEntry_spec__0_spec__0_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f___at___Lean_addAliasEntry_spec__0_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f___at___Lean_addAliasEntry_spec__0_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f___at___Lean_addAliasEntry_spec__0_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f___at___Lean_addAliasEntry_spec__0_spec__0_spec__0___redArg(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f___at___Lean_addAliasEntry_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f___at___Lean_addAliasEntry_spec__0_spec__0_spec__0(x_1, x_2, x_5, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f___at___Lean_addAliasEntry_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f___at___Lean_addAliasEntry_spec__0_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f___at___Lean_addAliasEntry_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f___at___Lean_addAliasEntry_spec__0_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___Lean_SMap_find_x3f___at___Lean_addAliasEntry_spec__0_spec__3_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___Lean_SMap_find_x3f___at___Lean_addAliasEntry_spec__0_spec__3_spec__3___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___Lean_SMap_find_x3f___at___Lean_addAliasEntry_spec__0_spec__3_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___Lean_SMap_find_x3f___at___Lean_addAliasEntry_spec__0_spec__3_spec__3(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___Lean_SMap_find_x3f___at___Lean_addAliasEntry_spec__0_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___Lean_SMap_find_x3f___at___Lean_addAliasEntry_spec__0_spec__3___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___Lean_SMap_find_x3f___at___Lean_addAliasEntry_spec__0_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___Lean_SMap_find_x3f___at___Lean_addAliasEntry_spec__0_spec__3(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___Lean_addAliasEntry_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_SMap_find_x3f___at___Lean_addAliasEntry_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___Lean_addAliasEntry_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_SMap_find_x3f___at___Lean_addAliasEntry_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__6_spec__6_spec__8___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; lean_object* x_7; 
x_6 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_7 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__6_spec__6_spec__8___redArg(x_6, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__6_spec__6_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; lean_object* x_9; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__6_spec__6_spec__8(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__6_spec__6___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__6_spec__6___redArg(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__6_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__6_spec__6(x_1, x_2, x_7, x_8, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__11_spec__11___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__11_spec__11___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__11_spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___Std_DHashMap_Internal_Raw_u2080_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__11_spec__11(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_elem___at___Lean_addAliasEntry_spec__18___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_elem___at___Lean_addAliasEntry_spec__18(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_mkStateFromImportedEntries___at___Lean_initFn____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_mkStateFromImportedEntries___at___Lean_initFn____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__1_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_2, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_array_uget(x_1, x_2);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_get_size(x_11);
x_14 = lean_nat_dec_lt(x_12, x_13);
if (x_14 == 0)
{
lean_dec(x_13);
lean_dec_ref(x_11);
x_5 = x_4;
goto block_9;
}
else
{
uint8_t x_15; 
x_15 = lean_nat_dec_le(x_13, x_13);
if (x_15 == 0)
{
lean_dec(x_13);
lean_dec_ref(x_11);
x_5 = x_4;
goto block_9;
}
else
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_18 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_mkStateFromImportedEntries___at___Lean_initFn____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__0(x_11, x_16, x_17, x_4);
lean_dec_ref(x_11);
x_5 = x_18;
goto block_9;
}
}
}
else
{
return x_4;
}
block_9:
{
size_t x_6; size_t x_7; 
x_6 = 1;
x_7 = lean_usize_add(x_2, x_6);
x_2 = x_7;
x_4 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_mkStateFromImportedEntries___at___Lean_initFn____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_2, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_array_uget(x_1, x_2);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_get_size(x_11);
x_14 = lean_nat_dec_lt(x_12, x_13);
if (x_14 == 0)
{
lean_dec(x_13);
lean_dec_ref(x_11);
x_5 = x_4;
goto block_9;
}
else
{
uint8_t x_15; 
x_15 = lean_nat_dec_le(x_13, x_13);
if (x_15 == 0)
{
lean_dec(x_13);
lean_dec_ref(x_11);
x_5 = x_4;
goto block_9;
}
else
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_18 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_mkStateFromImportedEntries___at___Lean_initFn____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__0(x_11, x_16, x_17, x_4);
lean_dec_ref(x_11);
x_5 = x_18;
goto block_9;
}
}
}
else
{
return x_4;
}
block_9:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = 1;
x_7 = lean_usize_add(x_2, x_6);
x_8 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_mkStateFromImportedEntries___at___Lean_initFn____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__1_spec__1(x_1, x_7, x_3, x_5);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___Lean_initFn____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
lean_dec(x_4);
return x_1;
}
else
{
uint8_t x_6; 
x_6 = lean_nat_dec_le(x_4, x_4);
if (x_6 == 0)
{
lean_dec(x_4);
return x_1;
}
else
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = 0;
x_8 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_mkStateFromImportedEntries___at___Lean_initFn____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__1(x_2, x_7, x_8, x_1);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at___Lean_initFn____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__4___redArg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at___Lean_initFn____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_SMap_switch___at___Lean_initFn____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__4___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_initFn___lam__1___closed__0____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(8u);
x_3 = lean_nat_mul(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn___lam__1___closed__1____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = l_Lean_initFn___lam__1___closed__0____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_;
x_3 = lean_nat_div(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn___lam__1___closed__2____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_initFn___lam__1___closed__1____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_;
x_2 = l_Nat_nextPowerOfTwo(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_initFn___lam__1___closed__3____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_initFn___lam__1___closed__2____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn___lam__1___closed__4____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___lam__1___closed__3____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn___lam__1___closed__5____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___lam__1___closed__6____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_initFn___lam__1___closed__5____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_initFn___lam__1___closed__7____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_1 = l_Lean_initFn___lam__1___closed__6____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_;
x_2 = l_Lean_initFn___lam__1___closed__4____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_;
x_3 = 1;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_1);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__1____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_initFn___lam__1___closed__7____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_;
x_3 = l_Lean_mkStateFromImportedEntries___at___Lean_initFn____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0(x_2, x_1);
x_4 = l_Lean_SMap_switch___at___Lean_initFn____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__4___redArg(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("aliasExtension", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__1____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_;
x_2 = l_Lean_initFn___closed__0____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn___closed__3____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_addAliasEntry), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_alloc_closure((void*)(l_Lean_initFn___lam__0____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_), 1, 0);
x_3 = lean_alloc_closure((void*)(l_Lean_initFn___lam__1____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2____boxed), 1, 0);
x_4 = l_Lean_initFn___closed__2____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_;
x_5 = l_Lean_initFn___closed__3____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_;
x_6 = lean_box(0);
x_7 = lean_box(2);
x_8 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_5);
lean_ctor_set(x_8, 2, x_3);
lean_ctor_set(x_8, 3, x_2);
lean_ctor_set(x_8, 4, x_6);
lean_ctor_set(x_8, 5, x_7);
lean_ctor_set(x_8, 6, x_6);
x_9 = l_Lean_registerSimplePersistentEnvExtension___redArg(x_8, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_mkStateFromImportedEntries___at___Lean_initFn____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_mkStateFromImportedEntries___at___Lean_initFn____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__0(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_mkStateFromImportedEntries___at___Lean_initFn____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at_____private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_mkStateFromImportedEntries___at___Lean_initFn____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__1_spec__1(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_mkStateFromImportedEntries___at___Lean_initFn____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_mkStateFromImportedEntries___at___Lean_initFn____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__1(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___Lean_initFn____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkStateFromImportedEntries___at___Lean_initFn____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__1____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_initFn___lam__1____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addAlias___closed__0() {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = l_Lean_addAlias___closed__0;
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
lean_dec_ref(x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_3);
x_8 = lean_box(0);
x_9 = l_Lean_PersistentEnvExtension_addEntry___redArg(x_4, x_1, x_7, x_6, x_8);
lean_dec(x_6);
return x_9;
}
}
static lean_object* _init_l_Lean_getAliasState___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Name_beq___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_getAliasState___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Name_hash___override___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_getAliasState___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_getAliasState___closed__1;
x_2 = l_Lean_getAliasState___closed__0;
x_3 = l_Lean_SMap_instInhabited(lean_box(0), lean_box(0), x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_getAliasState(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = l_Lean_addAlias___closed__0;
x_3 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_3, 2);
lean_inc(x_4);
lean_dec_ref(x_3);
x_5 = l_Lean_getAliasState___closed__2;
x_6 = lean_box(0);
x_7 = l_Lean_SimplePersistentEnvExtension_getState___redArg(x_5, x_2, x_1, x_4, x_6);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___Lean_getAliases_spec__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; 
lean_dec_ref(x_1);
x_5 = l_List_reverse___redArg(x_4);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
lean_inc_ref(x_1);
x_9 = l_Lean_isProtected(x_1, x_7);
if (x_9 == 0)
{
if (x_2 == 0)
{
lean_free_object(x_3);
lean_dec(x_7);
x_3 = x_8;
goto _start;
}
else
{
lean_ctor_set(x_3, 1, x_4);
{
lean_object* _tmp_2 = x_8;
lean_object* _tmp_3 = x_3;
x_3 = _tmp_2;
x_4 = _tmp_3;
}
goto _start;
}
}
else
{
lean_free_object(x_3);
lean_dec(x_7);
x_3 = x_8;
goto _start;
}
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_3, 0);
x_14 = lean_ctor_get(x_3, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_3);
lean_inc(x_13);
lean_inc_ref(x_1);
x_15 = l_Lean_isProtected(x_1, x_13);
if (x_15 == 0)
{
if (x_2 == 0)
{
lean_dec(x_13);
x_3 = x_14;
goto _start;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_13);
lean_ctor_set(x_17, 1, x_4);
x_3 = x_14;
x_4 = x_17;
goto _start;
}
}
else
{
lean_dec(x_13);
x_3 = x_14;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getAliases(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = l_Lean_addAlias___closed__0;
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
lean_dec_ref(x_5);
x_7 = l_Lean_getAliasState___closed__2;
x_8 = lean_box(0);
lean_inc_ref(x_1);
x_9 = l_Lean_SimplePersistentEnvExtension_getState___redArg(x_7, x_4, x_1, x_6, x_8);
lean_dec(x_6);
x_10 = l_Lean_SMap_find_x3f___at___Lean_addAliasEntry_spec__0___redArg(x_9, x_2);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
lean_dec_ref(x_1);
x_11 = lean_box(0);
return x_11;
}
else
{
if (x_3 == 0)
{
lean_object* x_12; 
lean_dec_ref(x_1);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec_ref(x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec_ref(x_10);
x_14 = lean_box(0);
x_15 = l_List_filterTR_loop___at___Lean_getAliases_spec__0(x_1, x_3, x_13, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___Lean_getAliases_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_List_filterTR_loop___at___Lean_getAliases_spec__0(x_1, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_getAliases___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
x_5 = l_Lean_getAliases(x_1, x_2, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_SMap_fold___at___Lean_getRevAliases_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_dec_ref(x_3);
lean_inc(x_1);
x_7 = lean_apply_3(x_1, x_2, x_4, x_5);
x_2 = x_7;
x_3 = x_6;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_SMap_fold___at___Lean_getRevAliases_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_SMap_fold___at___Lean_getRevAliases_spec__0_spec__0___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at___Lean_PersistentHashMap_foldl___at___Lean_SMap_fold___at___Lean_getRevAliases_spec__0_spec__1_spec__1_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_3, x_4);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_array_uget(x_2, x_3);
switch (lean_obj_tag(x_12)) {
case 0:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
lean_inc(x_1);
x_15 = lean_apply_3(x_1, x_5, x_13, x_14);
x_6 = x_15;
goto block_10;
}
case 1:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
lean_dec_ref(x_12);
lean_inc(x_1);
x_17 = l_Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at___Lean_PersistentHashMap_foldl___at___Lean_SMap_fold___at___Lean_getRevAliases_spec__0_spec__1_spec__1_spec__1___redArg(x_1, x_16, x_5);
lean_dec(x_16);
x_6 = x_17;
goto block_10;
}
default: 
{
x_6 = x_5;
goto block_10;
}
}
}
else
{
lean_dec(x_1);
return x_5;
}
block_10:
{
size_t x_7; size_t x_8; 
x_7 = 1;
x_8 = lean_usize_add(x_3, x_7);
x_3 = x_8;
x_5 = x_6;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at___Lean_PersistentHashMap_foldl___at___Lean_SMap_fold___at___Lean_getRevAliases_spec__0_spec__1_spec__1_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at___Lean_PersistentHashMap_foldl___at___Lean_SMap_fold___at___Lean_getRevAliases_spec__0_spec__1_spec__1_spec__1_spec__1___redArg(x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at___Lean_PersistentHashMap_foldl___at___Lean_SMap_fold___at___Lean_getRevAliases_spec__0_spec__1_spec__1_spec__1_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_dec(x_4);
lean_dec(x_1);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_array_fget_borrowed(x_2, x_4);
x_9 = lean_array_fget_borrowed(x_3, x_4);
lean_inc(x_1);
lean_inc(x_9);
lean_inc(x_8);
x_10 = lean_apply_3(x_1, x_5, x_8, x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
x_4 = x_12;
x_5 = x_10;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at___Lean_PersistentHashMap_foldl___at___Lean_SMap_fold___at___Lean_getRevAliases_spec__0_spec__1_spec__1_spec__1_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at___Lean_PersistentHashMap_foldl___at___Lean_SMap_fold___at___Lean_getRevAliases_spec__0_spec__1_spec__1_spec__1_spec__2___redArg(x_4, x_5, x_6, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at___Lean_PersistentHashMap_foldl___at___Lean_SMap_fold___at___Lean_getRevAliases_spec__0_spec__1_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_array_get_size(x_4);
x_7 = lean_nat_dec_lt(x_5, x_6);
if (x_7 == 0)
{
lean_dec(x_6);
lean_dec(x_1);
return x_3;
}
else
{
uint8_t x_8; 
x_8 = lean_nat_dec_le(x_6, x_6);
if (x_8 == 0)
{
lean_dec(x_6);
lean_dec(x_1);
return x_3;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = 0;
x_10 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_11 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at___Lean_PersistentHashMap_foldl___at___Lean_SMap_fold___at___Lean_getRevAliases_spec__0_spec__1_spec__1_spec__1_spec__1___redArg(x_1, x_4, x_9, x_10, x_3);
return x_11;
}
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
x_14 = lean_unsigned_to_nat(0u);
x_15 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at___Lean_PersistentHashMap_foldl___at___Lean_SMap_fold___at___Lean_getRevAliases_spec__0_spec__1_spec__1_spec__1_spec__2___redArg(x_1, x_12, x_13, x_14, x_3);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at___Lean_PersistentHashMap_foldl___at___Lean_SMap_fold___at___Lean_getRevAliases_spec__0_spec__1_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at___Lean_PersistentHashMap_foldl___at___Lean_SMap_fold___at___Lean_getRevAliases_spec__0_spec__1_spec__1_spec__1___redArg(x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___Lean_PersistentHashMap_foldl___at___Lean_SMap_fold___at___Lean_getRevAliases_spec__0_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at___Lean_PersistentHashMap_foldl___at___Lean_SMap_fold___at___Lean_getRevAliases_spec__0_spec__1_spec__1_spec__1___redArg(x_2, x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___Lean_PersistentHashMap_foldl___at___Lean_SMap_fold___at___Lean_getRevAliases_spec__0_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at___Lean_PersistentHashMap_foldl___at___Lean_SMap_fold___at___Lean_getRevAliases_spec__0_spec__1_spec__1_spec__1___redArg(x_4, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___Lean_SMap_fold___at___Lean_getRevAliases_spec__0_spec__1___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_3(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___Lean_SMap_fold___at___Lean_getRevAliases_spec__0_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___Lean_SMap_fold___at___Lean_getRevAliases_spec__0_spec__1___redArg___lam__0), 4, 1);
lean_closure_set(x_4, 0, x_2);
x_5 = l_Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at___Lean_PersistentHashMap_foldl___at___Lean_SMap_fold___at___Lean_getRevAliases_spec__0_spec__1_spec__1_spec__1___redArg(x_4, x_1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___Lean_SMap_fold___at___Lean_getRevAliases_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentHashMap_foldl___at___Lean_SMap_fold___at___Lean_getRevAliases_spec__0_spec__1___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_SMap_fold___at___Lean_getRevAliases_spec__0_spec__6___redArg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_7 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_8 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_SMap_fold___at___Lean_getRevAliases_spec__0_spec__0___redArg(x_1, x_5, x_7);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_SMap_fold___at___Lean_getRevAliases_spec__0_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_SMap_fold___at___Lean_getRevAliases_spec__0_spec__6___redArg(x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___Lean_getRevAliases_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_4, 1);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_get_size(x_6);
x_9 = lean_nat_dec_lt(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_8);
x_10 = l_Lean_PersistentHashMap_foldl___at___Lean_SMap_fold___at___Lean_getRevAliases_spec__0_spec__1___redArg(x_5, x_1, x_2);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = lean_nat_dec_le(x_8, x_8);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
x_12 = l_Lean_PersistentHashMap_foldl___at___Lean_SMap_fold___at___Lean_getRevAliases_spec__0_spec__1___redArg(x_5, x_1, x_2);
return x_12;
}
else
{
size_t x_13; size_t x_14; lean_object* x_15; lean_object* x_16; 
x_13 = 0;
x_14 = lean_usize_of_nat(x_8);
lean_dec(x_8);
lean_inc(x_1);
x_15 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_SMap_fold___at___Lean_getRevAliases_spec__0_spec__6___redArg(x_1, x_6, x_13, x_14, x_2);
x_16 = l_Lean_PersistentHashMap_foldl___at___Lean_SMap_fold___at___Lean_getRevAliases_spec__0_spec__1___redArg(x_5, x_1, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___Lean_getRevAliases_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_SMap_fold___at___Lean_getRevAliases_spec__0___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_getRevAliases___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_List_elem___at___Lean_addAliasEntry_spec__18(x_1, x_4);
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
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_3 = l_Lean_addAlias___closed__0;
x_4 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_4, 2);
lean_inc(x_5);
lean_dec_ref(x_4);
x_6 = lean_alloc_closure((void*)(l_Lean_getRevAliases___lam__0___boxed), 4, 1);
lean_closure_set(x_6, 0, x_2);
x_7 = l_Lean_getAliasState___closed__2;
x_8 = lean_box(0);
x_9 = lean_box(0);
x_10 = l_Lean_SimplePersistentEnvExtension_getState___redArg(x_7, x_3, x_1, x_5, x_9);
lean_dec(x_5);
x_11 = l_Lean_SMap_fold___at___Lean_getRevAliases_spec__0___redArg(x_6, x_8, x_10);
lean_dec_ref(x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at___Lean_PersistentHashMap_foldl___at___Lean_SMap_fold___at___Lean_getRevAliases_spec__0_spec__1_spec__1_spec__1_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at___Lean_PersistentHashMap_foldl___at___Lean_SMap_fold___at___Lean_getRevAliases_spec__0_spec__1_spec__1_spec__1_spec__1___redArg(x_1, x_2, x_6, x_7, x_5);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at___Lean_PersistentHashMap_foldl___at___Lean_SMap_fold___at___Lean_getRevAliases_spec__0_spec__1_spec__1_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_11 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at___Lean_PersistentHashMap_foldl___at___Lean_SMap_fold___at___Lean_getRevAliases_spec__0_spec__1_spec__1_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5, x_9, x_10, x_8);
lean_dec_ref(x_5);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at___Lean_PersistentHashMap_foldl___at___Lean_SMap_fold___at___Lean_getRevAliases_spec__0_spec__1_spec__1_spec__1_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at___Lean_PersistentHashMap_foldl___at___Lean_SMap_fold___at___Lean_getRevAliases_spec__0_spec__1_spec__1_spec__1_spec__2___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at___Lean_PersistentHashMap_foldl___at___Lean_SMap_fold___at___Lean_getRevAliases_spec__0_spec__1_spec__1_spec__1_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at___Lean_PersistentHashMap_foldl___at___Lean_SMap_fold___at___Lean_getRevAliases_spec__0_spec__1_spec__1_spec__1_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at___Lean_PersistentHashMap_foldl___at___Lean_SMap_fold___at___Lean_getRevAliases_spec__0_spec__1_spec__1_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at___Lean_PersistentHashMap_foldl___at___Lean_SMap_fold___at___Lean_getRevAliases_spec__0_spec__1_spec__1_spec__1___redArg(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at___Lean_PersistentHashMap_foldl___at___Lean_SMap_fold___at___Lean_getRevAliases_spec__0_spec__1_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_foldlMAux___at___Lean_PersistentHashMap_foldlM___at___Lean_PersistentHashMap_foldl___at___Lean_SMap_fold___at___Lean_getRevAliases_spec__0_spec__1_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___Lean_PersistentHashMap_foldl___at___Lean_SMap_fold___at___Lean_getRevAliases_spec__0_spec__1_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_foldlM___at___Lean_PersistentHashMap_foldl___at___Lean_SMap_fold___at___Lean_getRevAliases_spec__0_spec__1_spec__1___redArg(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___Lean_PersistentHashMap_foldl___at___Lean_SMap_fold___at___Lean_getRevAliases_spec__0_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentHashMap_foldlM___at___Lean_PersistentHashMap_foldl___at___Lean_SMap_fold___at___Lean_getRevAliases_spec__0_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___Lean_SMap_fold___at___Lean_getRevAliases_spec__0_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_foldl___at___Lean_SMap_fold___at___Lean_getRevAliases_spec__0_spec__1___redArg(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___Lean_SMap_fold___at___Lean_getRevAliases_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentHashMap_foldl___at___Lean_SMap_fold___at___Lean_getRevAliases_spec__0_spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_SMap_fold___at___Lean_getRevAliases_spec__0_spec__6___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_SMap_fold___at___Lean_getRevAliases_spec__0_spec__6___redArg(x_1, x_2, x_6, x_7, x_5);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_SMap_fold___at___Lean_getRevAliases_spec__0_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_SMap_fold___at___Lean_getRevAliases_spec__0_spec__6(x_1, x_2, x_3, x_4, x_8, x_9, x_7);
lean_dec_ref(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___Lean_getRevAliases_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_SMap_fold___at___Lean_getRevAliases_spec__0___redArg(x_1, x_2, x_3);
lean_dec_ref(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___Lean_getRevAliases_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_SMap_fold___at___Lean_getRevAliases_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_getRevAliases___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_getRevAliases___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT uint8_t l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_7; 
lean_inc_ref(x_1);
x_7 = l_Lean_Environment_containsOnBranch(x_1, x_2);
if (x_7 == 0)
{
uint8_t x_8; 
lean_inc(x_2);
lean_inc_ref(x_1);
x_8 = lean_is_reserved_name(x_1, x_2);
x_3 = x_8;
goto block_6;
}
else
{
x_3 = x_7;
goto block_6;
}
block_6:
{
if (x_3 == 0)
{
uint8_t x_4; uint8_t x_5; 
x_4 = 1;
x_5 = l_Lean_Environment_contains(x_1, x_2, x_4);
return x_5;
}
else
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_7, x_6);
if (x_14 == 0)
{
lean_dec_ref(x_3);
lean_dec(x_2);
lean_inc_ref(x_8);
return x_8;
}
else
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_array_uget(x_5, x_7);
x_16 = lean_ctor_get_uint8(x_15, sizeof(void*)*1);
if (x_16 == 0)
{
lean_dec_ref(x_15);
x_9 = x_1;
goto block_13;
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec_ref(x_15);
lean_inc(x_2);
x_18 = l_Lean_mkPrivateNameCore(x_17, x_2);
lean_inc(x_18);
lean_inc_ref(x_3);
x_19 = l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(x_3, x_18);
if (x_19 == 0)
{
lean_dec(x_18);
x_9 = x_1;
goto block_13;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec_ref(x_3);
lean_dec(x_2);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_18);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_4);
return x_22;
}
}
}
block_13:
{
size_t x_10; size_t x_11; 
x_10 = 1;
x_11 = lean_usize_add(x_7, x_10);
x_7 = x_11;
x_8 = x_9;
goto _start;
}
}
}
static lean_object* _init_l___private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*8);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
lean_inc(x_2);
x_4 = l_Lean_mkPrivateName(x_1, x_2);
lean_inc(x_4);
lean_inc_ref(x_1);
x_5 = l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
lean_dec(x_4);
x_6 = l_Lean_Environment_header(x_1);
x_7 = lean_ctor_get_uint8(x_6, sizeof(void*)*5 + 4);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec_ref(x_6);
lean_dec(x_2);
lean_dec_ref(x_1);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_ctor_get(x_6, 1);
lean_inc_ref(x_9);
lean_dec_ref(x_6);
x_10 = lean_box(0);
x_11 = lean_box(0);
x_12 = l___private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName___closed__0;
x_13 = lean_array_size(x_9);
x_14 = 0;
x_15 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0(x_12, x_2, x_1, x_11, x_9, x_13, x_14, x_12);
lean_dec_ref(x_9);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
if (lean_obj_tag(x_16) == 0)
{
return x_10;
}
else
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
return x_17;
}
}
}
else
{
lean_object* x_18; 
lean_dec(x_2);
lean_dec_ref(x_1);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_4);
return x_18;
}
}
else
{
lean_object* x_19; 
lean_dec(x_2);
lean_dec_ref(x_1);
x_19 = lean_box(0);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_11 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0(x_1, x_2, x_3, x_4, x_5, x_9, x_10, x_8);
lean_dec_ref(x_8);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveQualifiedName(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; uint8_t x_11; uint8_t x_14; 
lean_inc(x_3);
x_4 = l_Lean_Name_append(x_2, x_3);
x_5 = l_Lean_Name_isAtomic(x_3);
lean_dec(x_3);
lean_inc_ref(x_1);
x_6 = l_Lean_getAliases(x_1, x_4, x_5);
lean_inc(x_4);
lean_inc_ref(x_1);
x_14 = l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(x_1, x_4);
if (x_14 == 0)
{
x_11 = x_14;
goto block_13;
}
else
{
if (x_5 == 0)
{
x_11 = x_14;
goto block_13;
}
else
{
uint8_t x_15; 
lean_inc(x_4);
lean_inc_ref(x_1);
x_15 = l_Lean_isProtected(x_1, x_4);
if (x_15 == 0)
{
x_11 = x_14;
goto block_13;
}
else
{
goto block_10;
}
}
}
block_10:
{
lean_object* x_7; 
x_7 = l___private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName(x_1, x_4);
if (lean_obj_tag(x_7) == 0)
{
return x_6;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec_ref(x_7);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
}
block_13:
{
if (x_11 == 0)
{
goto block_10;
}
else
{
lean_object* x_12; 
lean_dec_ref(x_1);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_6);
return x_12;
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
lean_inc_ref(x_1);
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
lean_dec_ref(x_1);
return x_5;
}
}
else
{
lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_7 = lean_box(0);
return x_7;
}
}
}
static lean_object* _init_l___private_Lean_ResolveName_0__Lean_ResolveName_resolveExact___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_rootNamespace;
return x_1;
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
x_4 = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveExact___closed__0;
x_5 = lean_box(0);
x_6 = l_Lean_Name_replacePrefix(x_2, x_4, x_5);
lean_inc(x_6);
lean_inc_ref(x_1);
x_7 = l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(x_1, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = l___private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName(x_1, x_6);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec_ref(x_1);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_6);
return x_9;
}
}
else
{
lean_object* x_10; 
lean_dec(x_2);
lean_dec_ref(x_1);
x_10 = lean_box(0);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveOpenDecls(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_dec_ref(x_1);
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
lean_dec_ref(x_3);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec_ref(x_5);
x_9 = l_List_elem___at___Lean_addAliasEntry_spec__18(x_2, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_inc(x_2);
lean_inc_ref(x_1);
x_10 = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveQualifiedName(x_1, x_7, x_2);
x_11 = l_List_appendTR___redArg(x_10, x_4);
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
lean_dec_ref(x_5);
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
lean_inc_ref(x_1);
x_23 = l_Lean_Environment_contains(x_1, x_22, x_20);
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
lean_dec_ref(x_5);
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
lean_inc_ref(x_1);
x_34 = l_Lean_Environment_contains(x_1, x_33, x_31);
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
LEAN_EXPORT uint8_t l_List_eraseDups___at_____private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__0___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_name_eq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_eraseDups___at_____private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_alloc_closure((void*)(l_List_eraseDups___at_____private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__0___lam__0___boxed), 2, 0);
x_3 = l_List_eraseDupsBy___redArg(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_____private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
lean_dec(x_1);
x_4 = l_List_reverse___redArg(x_3);
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
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_5) == 1)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_25; lean_object* x_26; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc_ref(x_8);
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
lean_inc_ref(x_1);
x_25 = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveUsingNamespace(x_1, x_13, x_2);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_32; 
lean_inc(x_13);
lean_inc_ref(x_1);
x_32 = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveExact(x_1, x_13);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
lean_inc(x_13);
lean_inc_ref(x_1);
x_33 = l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(x_1, x_13);
if (x_33 == 0)
{
x_26 = x_25;
goto block_31;
}
else
{
lean_object* x_34; 
lean_inc(x_13);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_13);
lean_ctor_set(x_34, 1, x_25);
x_26 = x_34;
goto block_31;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_13);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_35 = lean_ctor_get(x_32, 0);
lean_inc(x_35);
lean_dec_ref(x_32);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_6);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_13);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_39 = l_List_eraseDups___at_____private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__0(x_25);
x_40 = lean_box(0);
x_41 = l_List_mapTR_loop___at_____private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__1(x_6, x_39, x_40);
return x_41;
}
block_24:
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
lean_inc(x_3);
lean_inc(x_13);
lean_inc_ref(x_1);
x_15 = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveOpenDecls(x_1, x_13, x_3, x_14);
x_16 = l_Lean_Name_isAtomic(x_13);
lean_inc_ref(x_1);
x_17 = l_Lean_getAliases(x_1, x_13, x_16);
lean_dec(x_13);
x_18 = l_List_appendTR___redArg(x_17, x_15);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_8);
lean_ctor_set(x_19, 1, x_6);
x_5 = x_7;
x_6 = x_19;
goto _start;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_21 = l_List_eraseDups___at_____private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__0(x_18);
x_22 = lean_box(0);
x_23 = l_List_mapTR_loop___at_____private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__1(x_6, x_21, x_22);
return x_23;
}
}
block_31:
{
lean_object* x_27; 
lean_inc(x_13);
lean_inc_ref(x_1);
x_27 = l___private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName(x_1, x_13);
if (lean_obj_tag(x_27) == 0)
{
lean_dec(x_25);
x_14 = x_26;
goto block_24;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec_ref(x_27);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_25);
x_30 = l_List_appendTR___redArg(x_29, x_26);
x_14 = x_30;
goto block_24;
}
}
}
else
{
lean_object* x_42; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_42 = lean_box(0);
return x_42;
}
}
}
LEAN_EXPORT lean_object* l_List_eraseDups___at_____private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_eraseDups___at_____private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__0___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_4);
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
x_8 = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop(x_1, x_2, x_3, x_5, x_6, x_7);
lean_dec_ref(x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_ResolveName_resolveNamespaceUsingScope_x3f_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.ResolveName", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.ResolveName.resolveNamespaceUsingScope\?", 44, 44);
return x_1;
}
}
static lean_object* _init_l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
return x_1;
}
}
static lean_object* _init_l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__2;
x_2 = lean_unsigned_to_nat(9u);
x_3 = lean_unsigned_to_nat(219u);
x_4 = l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__1;
x_5 = l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_ResolveName_resolveNamespaceUsingScope_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveExact___closed__0;
x_5 = l_Lean_Name_replacePrefix(x_2, x_4, x_3);
x_6 = l_Lean_Environment_isNamespace(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_5);
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_5);
return x_8;
}
}
case 1:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
lean_inc(x_2);
x_10 = l_Lean_Name_append(x_3, x_2);
lean_inc_ref(x_1);
x_11 = l_Lean_Environment_isNamespace(x_1, x_10);
if (x_11 == 0)
{
lean_dec(x_10);
x_3 = x_9;
goto _start;
}
else
{
lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_2);
lean_dec_ref(x_1);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_10);
return x_13;
}
}
default: 
{
lean_object* x_14; lean_object* x_15; 
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_14 = l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__3;
x_15 = l_panic___at___Lean_ResolveName_resolveNamespaceUsingScope_x3f_spec__0(x_14);
return x_15;
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
lean_dec_ref(x_1);
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_3, 0);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_16; 
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_7 = x_3;
} else {
 lean_dec_ref(x_3);
 x_7 = lean_box(0);
}
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
lean_dec_ref(x_5);
lean_inc(x_2);
x_10 = l_Lean_Name_append(x_8, x_2);
lean_inc_ref(x_1);
x_16 = l_Lean_Environment_isNamespace(x_1, x_10);
if (x_16 == 0)
{
lean_dec(x_9);
x_11 = x_16;
goto block_15;
}
else
{
uint8_t x_17; 
x_17 = l_List_elem___at___Lean_addAliasEntry_spec__18(x_2, x_9);
lean_dec(x_9);
if (x_17 == 0)
{
x_11 = x_16;
goto block_15;
}
else
{
lean_dec(x_10);
lean_dec(x_7);
x_3 = x_6;
goto _start;
}
}
block_15:
{
if (x_11 == 0)
{
lean_dec(x_10);
lean_dec(x_7);
x_3 = x_6;
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = l_Lean_ResolveName_resolveNamespaceUsingOpenDecls(x_1, x_2, x_6);
if (lean_is_scalar(x_7)) {
 x_14 = lean_alloc_ctor(1, 2, 0);
} else {
 x_14 = x_7;
}
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
else
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_3, 1);
lean_inc(x_19);
lean_dec_ref(x_3);
x_3 = x_19;
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
lean_inc_ref(x_1);
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
lean_dec_ref(x_5);
x_8 = l_Lean_ResolveName_resolveNamespaceUsingOpenDecls(x_1, x_4, x_3);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadResolveNameOfMonadLift___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
x_6 = lean_apply_2(x_1, lean_box(0), x_4);
x_7 = lean_apply_2(x_1, lean_box(0), x_5);
lean_ctor_set(x_2, 1, x_7);
lean_ctor_set(x_2, 0, x_6);
return x_2;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_2);
lean_inc(x_1);
x_10 = lean_apply_2(x_1, lean_box(0), x_8);
x_11 = lean_apply_2(x_1, lean_box(0), x_9);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadResolveNameOfMonadLift(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_instMonadResolveNameOfMonadLift___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_ResolveName_resolveGlobalName(x_1, x_2, x_5, x_3);
x_7 = lean_apply_2(x_4, lean_box(0), x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_closure((void*)(l_Lean_resolveGlobalName___redArg___lam__0), 5, 4);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_6);
lean_closure_set(x_7, 2, x_2);
lean_closure_set(x_7, 3, x_3);
x_8 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_5, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec_ref(x_1);
lean_inc(x_4);
x_8 = lean_alloc_closure((void*)(l_Lean_resolveGlobalName___redArg___lam__1), 6, 5);
lean_closure_set(x_8, 0, x_5);
lean_closure_set(x_8, 1, x_2);
lean_closure_set(x_8, 2, x_3);
lean_closure_set(x_8, 3, x_4);
lean_closure_set(x_8, 4, x_7);
x_9 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_6, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
lean_dec_ref(x_3);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec_ref(x_5);
lean_inc(x_6);
x_9 = lean_alloc_closure((void*)(l_Lean_resolveGlobalName___redArg___lam__2), 5, 4);
lean_closure_set(x_9, 0, x_2);
lean_closure_set(x_9, 1, x_4);
lean_closure_set(x_9, 2, x_8);
lean_closure_set(x_9, 3, x_6);
x_10 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_7, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_resolveGlobalName___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, lean_box(0), x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_resolveNamespaceCore___redArg___lam__2___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unknown namespace `", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_resolveNamespaceCore___redArg___lam__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
lean_inc(x_3);
x_10 = l_Lean_ResolveName_resolveNamespace(x_1, x_2, x_9, x_3);
lean_inc(x_10);
lean_inc(x_4);
x_11 = lean_alloc_closure((void*)(l_Lean_resolveNamespaceCore___redArg___lam__0), 3, 2);
lean_closure_set(x_11, 0, x_4);
lean_closure_set(x_11, 1, x_10);
if (x_6 == 0)
{
uint8_t x_16; 
x_16 = l_List_isEmpty___redArg(x_10);
lean_dec(x_10);
if (x_16 == 0)
{
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_3);
goto block_15;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_4);
x_17 = l_Lean_resolveNamespaceCore___redArg___lam__2___closed__0;
x_18 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_3, x_16);
x_19 = lean_string_append(x_17, x_18);
lean_dec_ref(x_18);
x_20 = l_Lean_resolveNamespaceCore___redArg___lam__2___closed__1;
x_21 = lean_string_append(x_19, x_20);
x_22 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = l_Lean_MessageData_ofFormat(x_22);
x_24 = l_Lean_throwError___redArg(x_7, x_8, x_23);
x_25 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_24, x_11);
return x_25;
}
}
else
{
lean_dec(x_10);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_3);
goto block_15;
}
block_15:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_box(0);
x_13 = lean_apply_2(x_4, lean_box(0), x_12);
x_14 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_13, x_11);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_box(x_5);
lean_inc(x_4);
x_11 = lean_alloc_closure((void*)(l_Lean_resolveNamespaceCore___redArg___lam__2___boxed), 9, 8);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_9);
lean_closure_set(x_11, 2, x_2);
lean_closure_set(x_11, 3, x_3);
lean_closure_set(x_11, 4, x_4);
lean_closure_set(x_11, 5, x_10);
lean_closure_set(x_11, 6, x_6);
lean_closure_set(x_11, 7, x_7);
x_12 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_8, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec_ref(x_1);
x_11 = lean_box(x_5);
lean_inc(x_4);
x_12 = lean_alloc_closure((void*)(l_Lean_resolveNamespaceCore___redArg___lam__1___boxed), 9, 8);
lean_closure_set(x_12, 0, x_8);
lean_closure_set(x_12, 1, x_2);
lean_closure_set(x_12, 2, x_3);
lean_closure_set(x_12, 3, x_4);
lean_closure_set(x_12, 4, x_11);
lean_closure_set(x_12, 5, x_6);
lean_closure_set(x_12, 6, x_7);
lean_closure_set(x_12, 7, x_10);
x_13 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_9, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
lean_dec_ref(x_3);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
x_11 = lean_box(x_6);
lean_inc(x_8);
x_12 = lean_alloc_closure((void*)(l_Lean_resolveNamespaceCore___redArg___lam__3___boxed), 8, 7);
lean_closure_set(x_12, 0, x_2);
lean_closure_set(x_12, 1, x_5);
lean_closure_set(x_12, 2, x_10);
lean_closure_set(x_12, 3, x_8);
lean_closure_set(x_12, 4, x_11);
lean_closure_set(x_12, 5, x_1);
lean_closure_set(x_12, 6, x_4);
x_13 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_9, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_resolveNamespaceCore___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_6);
x_11 = l_Lean_resolveNamespaceCore___redArg___lam__2(x_1, x_2, x_3, x_4, x_5, x_10, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_5);
x_11 = l_Lean_resolveNamespaceCore___redArg___lam__1(x_1, x_2, x_3, x_4, x_10, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_5);
x_10 = l_Lean_resolveNamespaceCore___redArg___lam__3(x_1, x_2, x_3, x_4, x_9, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_6);
x_8 = l_Lean_resolveNamespaceCore___redArg(x_1, x_2, x_3, x_4, x_5, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_7);
x_9 = l_Lean_resolveNamespaceCore(x_1, x_2, x_3, x_4, x_5, x_6, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespace___redArg___lam__0(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_ctor_set_tag(x_1, 1);
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
else
{
lean_object* x_5; 
lean_dec_ref(x_1);
x_5 = lean_box(0);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespace___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_replaceRef(x_1, x_4);
x_6 = lean_apply_3(x_2, lean_box(0), x_5, x_3);
return x_6;
}
}
static lean_object* _init_l_Lean_resolveNamespace___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_resolveNamespace___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expected identifier", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_resolveNamespace___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_resolveNamespace___redArg___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_resolveNamespace___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_resolveNamespace___redArg___closed__2;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespace___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 3)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_6 = lean_ctor_get(x_5, 2);
x_7 = lean_ctor_get(x_5, 3);
x_8 = lean_alloc_closure((void*)(l_Lean_resolveNamespace___redArg___lam__0), 1, 0);
x_9 = l_Lean_resolveNamespace___redArg___closed__0;
lean_inc(x_7);
x_10 = l_List_filterMapTR_go___redArg(x_8, x_7, x_9);
x_11 = l_List_isEmpty___redArg(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_12 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_12);
lean_dec_ref(x_1);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = lean_apply_2(x_13, lean_box(0), x_10);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_10);
x_15 = lean_ctor_get(x_4, 1);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
x_19 = 0;
lean_inc(x_6);
x_20 = l_Lean_resolveNamespaceCore___redArg(x_1, x_2, x_3, x_4, x_6, x_19);
x_21 = lean_alloc_closure((void*)(l_Lean_resolveNamespace___redArg___lam__1___boxed), 4, 3);
lean_closure_set(x_21, 0, x_5);
lean_closure_set(x_21, 1, x_18);
lean_closure_set(x_21, 2, x_20);
x_22 = lean_apply_4(x_16, lean_box(0), lean_box(0), x_17, x_21);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_23 = l_Lean_resolveNamespace___redArg___closed__3;
x_24 = l_Lean_throwErrorAt___redArg(x_1, x_4, x_5, x_23);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespace(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_resolveNamespace___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespace___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_resolveNamespace___redArg___lam__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_resolveUniqueNamespace___redArg___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ambiguous namespace `", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lean_resolveUniqueNamespace___redArg___lam__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`, possible interpretations: `", 30, 30);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveUniqueNamespace___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
lean_dec(x_5);
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_6, 1);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_23 = lean_ctor_get(x_6, 0);
lean_inc(x_23);
lean_dec_ref(x_6);
x_24 = lean_apply_2(x_5, lean_box(0), x_23);
return x_24;
}
else
{
lean_dec(x_5);
goto block_21;
}
}
block_21:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_7 = l_Lean_resolveUniqueNamespace___redArg___lam__0___closed__0;
x_8 = l_Lean_TSyntax_getId(x_1);
x_9 = 1;
x_10 = l_Lean_Name_toStringWithToken___at___Lean_Name_toString_spec__0(x_8, x_9);
x_11 = lean_string_append(x_7, x_10);
lean_dec_ref(x_10);
x_12 = l_Lean_resolveUniqueNamespace___redArg___lam__0___closed__1;
x_13 = lean_string_append(x_11, x_12);
x_14 = l_List_toString___redArg(x_2, x_6);
x_15 = lean_string_append(x_13, x_14);
lean_dec_ref(x_14);
x_16 = l_Lean_resolveNamespaceCore___redArg___lam__2___closed__1;
x_17 = lean_string_append(x_15, x_16);
x_18 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = l_Lean_MessageData_ofFormat(x_18);
x_20 = l_Lean_throwError___redArg(x_3, x_4, x_19);
return x_20;
}
}
}
static lean_object* _init_l_Lean_resolveUniqueNamespace___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Name_instToString___lam__0), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveUniqueNamespace___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
x_9 = l_Lean_resolveUniqueNamespace___redArg___closed__0;
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_1);
x_10 = l_Lean_resolveNamespace___redArg(x_1, x_2, x_3, x_4, x_5);
x_11 = lean_alloc_closure((void*)(l_Lean_resolveUniqueNamespace___redArg___lam__0___boxed), 6, 5);
lean_closure_set(x_11, 0, x_5);
lean_closure_set(x_11, 1, x_9);
lean_closure_set(x_11, 2, x_1);
lean_closure_set(x_11, 3, x_4);
lean_closure_set(x_11, 4, x_8);
x_12 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveUniqueNamespace(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_resolveUniqueNamespace___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveUniqueNamespace___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_resolveUniqueNamespace___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lean_filterFieldList___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = l_List_isEmpty___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg___lam__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_box(0);
x_6 = l_List_mapTR_loop___redArg(x_1, x_2, x_5);
x_7 = lean_apply_2(x_3, lean_box(0), x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg___lam__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg___lam__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_throwUnknownConstantAt___redArg(x_1, x_2, x_3, x_7, x_4);
x_9 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_8, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
x_9 = lean_alloc_closure((void*)(l_Lean_filterFieldList___redArg___lam__0___boxed), 1, 0);
x_10 = lean_alloc_closure((void*)(l_Lean_filterFieldList___redArg___lam__1___boxed), 1, 0);
x_11 = lean_box(0);
x_12 = l_List_filterTR_loop___redArg(x_9, x_5, x_11);
lean_inc(x_8);
lean_inc(x_12);
x_13 = lean_alloc_closure((void*)(l_Lean_filterFieldList___redArg___lam__2), 4, 3);
lean_closure_set(x_13, 0, x_10);
lean_closure_set(x_13, 1, x_12);
lean_closure_set(x_13, 2, x_8);
x_14 = l_List_isEmpty___redArg(x_12);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_inc(x_8);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_15 = lean_alloc_closure((void*)(l_Lean_filterFieldList___redArg___lam__3), 2, 1);
lean_closure_set(x_15, 0, x_13);
x_16 = lean_box(0);
x_17 = lean_apply_2(x_8, lean_box(0), x_16);
x_18 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_17, x_15);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_3, 1);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_alloc_closure((void*)(l_Lean_filterFieldList___redArg___lam__3), 2, 1);
lean_closure_set(x_21, 0, x_13);
lean_inc(x_7);
x_22 = lean_alloc_closure((void*)(l_Lean_filterFieldList___redArg___lam__5), 7, 6);
lean_closure_set(x_22, 0, x_1);
lean_closure_set(x_22, 1, x_2);
lean_closure_set(x_22, 2, x_3);
lean_closure_set(x_22, 3, x_4);
lean_closure_set(x_22, 4, x_7);
lean_closure_set(x_22, 5, x_21);
x_23 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_20, x_22);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_filterFieldList___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_filterFieldList___redArg___lam__0(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg___lam__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_filterFieldList___redArg___lam__1(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_filterFieldList___redArg(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc_ref(x_3);
lean_inc_ref(x_1);
x_7 = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___redArg___lam__0), 5, 4);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_3);
lean_closure_set(x_7, 2, x_4);
lean_closure_set(x_7, 3, x_5);
x_8 = l_Lean_resolveGlobalName___redArg(x_1, x_2, x_3, x_5);
x_9 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_8, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNoOverload___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = l_Lean_mkConst(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_ensureNoOverload___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Ambiguous identifier `", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lean_ensureNoOverload___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_ensureNoOverload___redArg___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_ensureNoOverload___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`; possible interpretations: ", 29, 29);
return x_1;
}
}
static lean_object* _init_l_Lean_ensureNoOverload___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_ensureNoOverload___redArg___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_ensureNoOverload___redArg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_MessageData_ofExpr), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_ensureNoOverload___redArg___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_ensureNoOverload___redArg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_ensureNoOverload___redArg___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNoOverload___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_5, 1);
x_7 = lean_alloc_closure((void*)(l_Lean_ensureNoOverload___redArg___lam__0), 1, 0);
if (lean_obj_tag(x_4) == 0)
{
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_4, 1);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec_ref(x_7);
lean_inc(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_24 = lean_ctor_get(x_4, 0);
lean_inc(x_24);
lean_dec_ref(x_4);
x_25 = lean_apply_2(x_6, lean_box(0), x_24);
return x_25;
}
else
{
goto block_22;
}
}
block_22:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_8 = l_Lean_ensureNoOverload___redArg___closed__1;
x_9 = l_Lean_MessageData_ofName(x_3);
x_10 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = l_Lean_ensureNoOverload___redArg___closed__3;
x_12 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_box(0);
x_14 = l_List_mapTR_loop___redArg(x_7, x_4, x_13);
x_15 = l_Lean_ensureNoOverload___redArg___closed__4;
x_16 = l_List_mapTR_loop___redArg(x_15, x_14, x_13);
x_17 = l_Lean_MessageData_ofList(x_16);
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_ensureNoOverload___redArg___closed__6;
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_throwError___redArg(x_1, x_2, x_20);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNoOverload(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_ensureNoOverload___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverloadCore___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_ensureNoOverload___redArg(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverloadCore___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_resolveGlobalConstNoOverloadCore___redArg___lam__0), 4, 3);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_4);
lean_closure_set(x_7, 2, x_5);
x_8 = l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___redArg(x_1, x_2, x_3, x_4, x_5);
x_9 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_8, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverloadCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_resolveGlobalConstNoOverloadCore___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___redArg___lam__0(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_box(0);
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_replaceRef(x_1, x_4);
x_6 = lean_apply_3(x_2, lean_box(0), x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 3)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_ctor_get(x_3, 2);
x_6 = lean_ctor_get(x_3, 3);
x_7 = lean_alloc_closure((void*)(l_Lean_preprocessSyntaxAndResolve___redArg___lam__0___boxed), 1, 0);
x_8 = l_Lean_resolveNamespace___redArg___closed__0;
lean_inc(x_6);
x_9 = l_List_filterMapTR_go___redArg(x_7, x_6, x_8);
x_10 = l_List_isEmpty___redArg(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_11 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_11);
lean_dec_ref(x_1);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = lean_apply_2(x_12, lean_box(0), x_9);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_9);
x_14 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_14);
lean_dec_ref(x_2);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
lean_dec_ref(x_1);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec_ref(x_14);
lean_inc(x_5);
x_18 = lean_apply_1(x_4, x_5);
x_19 = lean_alloc_closure((void*)(l_Lean_preprocessSyntaxAndResolve___redArg___lam__1___boxed), 4, 3);
lean_closure_set(x_19, 0, x_3);
lean_closure_set(x_19, 1, x_17);
lean_closure_set(x_19, 2, x_18);
x_20 = lean_apply_4(x_15, lean_box(0), lean_box(0), x_16, x_19);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_4);
x_21 = l_Lean_resolveNamespace___redArg___closed__3;
x_22 = l_Lean_throwErrorAt___redArg(x_1, x_2, x_3, x_21);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_preprocessSyntaxAndResolve___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___redArg___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_preprocessSyntaxAndResolve___redArg___lam__0(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_preprocessSyntaxAndResolve___redArg___lam__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
lean_inc_ref(x_4);
lean_inc_ref(x_1);
x_6 = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore), 6, 5);
lean_closure_set(x_6, 0, lean_box(0));
lean_closure_set(x_6, 1, x_1);
lean_closure_set(x_6, 2, x_2);
lean_closure_set(x_6, 3, x_3);
lean_closure_set(x_6, 4, x_4);
x_7 = l_Lean_preprocessSyntaxAndResolve___redArg(x_1, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_resolveGlobalConst___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_ensureNonAmbiguous___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.ensureNonAmbiguous", 23, 23);
return x_1;
}
}
static lean_object* _init_l_Lean_ensureNonAmbiguous___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__2;
x_2 = lean_unsigned_to_nat(11u);
x_3 = lean_unsigned_to_nat(383u);
x_4 = l_Lean_ensureNonAmbiguous___redArg___closed__0;
x_5 = l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_ensureNonAmbiguous___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_ensureNoOverload___redArg___lam__0), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_ensureNonAmbiguous___redArg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Expr_dbgToString___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_ensureNonAmbiguous___redArg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ambiguous identifier `", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lean_ensureNonAmbiguous___redArg___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_Format_defWidth;
return x_1;
}
}
static lean_object* _init_l_Lean_ensureNonAmbiguous___redArg___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`, possible interpretations: ", 29, 29);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNonAmbiguous___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
lean_dec_ref(x_2);
x_5 = lean_box(0);
x_6 = l_instInhabitedOfMonad___redArg(x_1, x_5);
x_7 = l_Lean_ensureNonAmbiguous___redArg___closed__1;
x_8 = l_panic___redArg(x_6, x_7);
return x_8;
}
else
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_4, 1);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_10);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = lean_ctor_get(x_4, 0);
lean_inc(x_12);
lean_dec_ref(x_4);
x_13 = lean_apply_2(x_11, lean_box(0), x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_14 = l_Lean_ensureNonAmbiguous___redArg___closed__2;
x_15 = l_Lean_ensureNonAmbiguous___redArg___closed__3;
x_16 = l_Lean_ensureNonAmbiguous___redArg___closed__4;
x_17 = lean_box(0);
x_18 = 0;
lean_inc(x_3);
x_19 = l_Lean_Syntax_formatStx(x_3, x_17, x_18);
x_20 = l_Lean_ensureNonAmbiguous___redArg___closed__5;
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_format_pretty(x_19, x_20, x_21, x_21);
x_23 = lean_string_append(x_16, x_22);
lean_dec_ref(x_22);
x_24 = l_Lean_ensureNonAmbiguous___redArg___closed__6;
x_25 = lean_string_append(x_23, x_24);
x_26 = lean_box(0);
x_27 = l_List_mapTR_loop___redArg(x_14, x_4, x_26);
x_28 = l_List_toString___redArg(x_15, x_27);
x_29 = lean_string_append(x_25, x_28);
lean_dec_ref(x_28);
x_30 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = l_Lean_MessageData_ofFormat(x_30);
x_32 = l_Lean_throwErrorAt___redArg(x_1, x_2, x_3, x_31);
return x_32;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNonAmbiguous(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_ensureNonAmbiguous___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverload___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_ensureNonAmbiguous___redArg(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverload___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_resolveGlobalConstNoOverload___redArg___lam__0), 4, 3);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_4);
lean_closure_set(x_7, 2, x_5);
x_8 = l_Lean_resolveGlobalConst___redArg(x_1, x_2, x_3, x_4, x_5);
x_9 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_8, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverload(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_resolveGlobalConstNoOverload___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = l_List_isEmpty___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, uint8_t x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_2);
x_12 = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg(x_3, x_4, x_5, x_6, x_7, x_8, x_11, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__2(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(x_2);
x_5 = lean_apply_2(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__3(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(x_2);
x_5 = lean_apply_2(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_box(0);
x_8 = l_List_filterTR_loop___redArg(x_1, x_6, x_7);
x_9 = l_List_isEmpty___redArg(x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
x_10 = lean_box(0);
x_11 = lean_apply_2(x_2, lean_box(0), x_10);
x_12 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_11, x_4);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
x_13 = lean_box(0);
x_14 = lean_apply_2(x_2, lean_box(0), x_13);
x_15 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_14, x_5);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_4, 1);
x_11 = lean_ctor_get(x_4, 2);
x_12 = lean_ctor_get(x_4, 3);
x_13 = lean_ctor_get(x_1, 1);
x_14 = lean_ctor_get(x_9, 1);
x_15 = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__0___boxed), 1, 0);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_6);
x_16 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_16, 0, x_6);
lean_ctor_set(x_16, 1, x_10);
lean_ctor_set(x_16, 2, x_11);
lean_ctor_set(x_16, 3, x_12);
if (x_8 == 0)
{
x_17 = x_8;
goto block_56;
}
else
{
uint8_t x_57; 
x_57 = l_List_isEmpty___redArg(x_7);
if (x_57 == 0)
{
x_17 = x_8;
goto block_56;
}
else
{
uint8_t x_58; 
x_58 = 0;
x_17 = x_58;
goto block_56;
}
}
block_56:
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_box(x_17);
lean_inc_ref(x_5);
lean_inc_ref(x_16);
x_19 = lean_apply_2(x_5, x_16, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_inc(x_13);
if (lean_obj_tag(x_6) == 1)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_6, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_6, 1);
lean_inc_ref(x_21);
lean_dec_ref(x_6);
lean_inc_ref(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_22 = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__1___boxed), 10, 8);
lean_closure_set(x_22, 0, x_21);
lean_closure_set(x_22, 1, x_7);
lean_closure_set(x_22, 2, x_1);
lean_closure_set(x_22, 3, x_2);
lean_closure_set(x_22, 4, x_3);
lean_closure_set(x_22, 5, x_4);
lean_closure_set(x_22, 6, x_5);
lean_closure_set(x_22, 7, x_20);
if (x_8 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_23 = lean_box(x_8);
lean_inc_ref(x_22);
x_24 = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__2___boxed), 3, 2);
lean_closure_set(x_24, 0, x_22);
lean_closure_set(x_24, 1, x_23);
x_25 = 1;
x_26 = lean_box(x_25);
x_27 = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__3___boxed), 3, 2);
lean_closure_set(x_27, 0, x_22);
lean_closure_set(x_27, 1, x_26);
lean_inc(x_13);
lean_inc(x_14);
x_28 = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__4), 6, 5);
lean_closure_set(x_28, 0, x_15);
lean_closure_set(x_28, 1, x_14);
lean_closure_set(x_28, 2, x_13);
lean_closure_set(x_28, 3, x_27);
lean_closure_set(x_28, 4, x_24);
x_29 = l_Lean_MacroScopesView_review(x_16);
x_30 = l_Lean_resolveGlobalName___redArg(x_1, x_2, x_3, x_29);
x_31 = lean_apply_4(x_13, lean_box(0), lean_box(0), x_30, x_28);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_inc(x_14);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_32 = lean_box(x_8);
x_33 = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__2___boxed), 3, 2);
lean_closure_set(x_33, 0, x_22);
lean_closure_set(x_33, 1, x_32);
x_34 = lean_box(0);
x_35 = lean_apply_2(x_14, lean_box(0), x_34);
x_36 = lean_apply_4(x_13, lean_box(0), lean_box(0), x_35, x_33);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; 
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_inc(x_14);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_37 = lean_box(0);
x_38 = lean_apply_2(x_14, lean_box(0), x_37);
return x_38;
}
}
else
{
uint8_t x_39; 
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_inc(x_14);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_39 = !lean_is_exclusive(x_1);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_40 = lean_ctor_get(x_1, 1);
lean_dec(x_40);
x_41 = lean_ctor_get(x_1, 0);
lean_dec(x_41);
x_42 = !lean_is_exclusive(x_19);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_19, 0);
x_44 = l_Lean_LocalDecl_toExpr(x_43);
lean_ctor_set(x_1, 1, x_7);
lean_ctor_set(x_1, 0, x_44);
lean_ctor_set(x_19, 0, x_1);
x_45 = lean_apply_2(x_14, lean_box(0), x_19);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_ctor_get(x_19, 0);
lean_inc(x_46);
lean_dec(x_19);
x_47 = l_Lean_LocalDecl_toExpr(x_46);
lean_ctor_set(x_1, 1, x_7);
lean_ctor_set(x_1, 0, x_47);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_1);
x_49 = lean_apply_2(x_14, lean_box(0), x_48);
return x_49;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_1);
x_50 = lean_ctor_get(x_19, 0);
lean_inc(x_50);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 x_51 = x_19;
} else {
 lean_dec_ref(x_19);
 x_51 = lean_box(0);
}
x_52 = l_Lean_LocalDecl_toExpr(x_50);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_7);
if (lean_is_scalar(x_51)) {
 x_54 = lean_alloc_ctor(1, 1, 0);
} else {
 x_54 = x_51;
}
lean_ctor_set(x_54, 0, x_53);
x_55 = lean_apply_2(x_14, lean_box(0), x_54);
return x_55;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, uint8_t x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__0(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_9);
x_12 = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_11, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
x_5 = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__2(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
x_5 = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__3(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_8);
x_10 = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_9);
x_11 = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get(x_2, 2);
x_8 = lean_ctor_get(x_2, 3);
lean_inc(x_5);
lean_inc(x_4);
x_9 = l_Lean_Name_append(x_4, x_5);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
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
if (lean_obj_tag(x_4) == 1)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_4, 0);
lean_inc(x_13);
lean_dec_ref(x_4);
x_4 = x_13;
goto _start;
}
else
{
lean_object* x_15; 
lean_dec(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_15 = lean_box(0);
return x_15;
}
}
else
{
lean_object* x_16; 
lean_dec(x_4);
lean_dec_ref(x_2);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_1);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_ResolveName_0__Lean_resolveLocalName_go(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_resolveLocalName___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_Name_quickCmp(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_LocalDecl_userName(x_1);
x_4 = lean_name_eq(x_3, x_2);
lean_dec(x_3);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec_ref(x_1);
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_1);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_8) == 0)
{
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_8, 0);
x_10 = l_Lean_LocalDecl_isAuxDecl(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_inc(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_11 = lean_apply_2(x_1, x_9, x_2);
return x_11;
}
else
{
if (x_3 == 0)
{
if (x_10 == 0)
{
lean_object* x_12; 
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_12 = lean_box(0);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = l_Lean_LocalDecl_fvarId(x_9);
x_14 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(x_4, x_5, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
lean_inc(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
x_15 = lean_apply_2(x_1, x_9, x_2);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_44; lean_object* x_45; 
lean_dec(x_2);
lean_dec_ref(x_1);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec_ref(x_14);
x_17 = l_Lean_extractMacroScopes(x_16);
x_44 = lean_ctor_get(x_17, 0);
lean_inc(x_44);
lean_inc(x_44);
x_45 = lean_private_to_user_name(x_44);
if (lean_obj_tag(x_45) == 0)
{
x_18 = x_44;
goto block_43;
}
else
{
lean_object* x_46; 
lean_dec(x_44);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
lean_dec_ref(x_45);
x_18 = x_46;
goto block_43;
}
block_43:
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_17, 0);
lean_dec(x_20);
lean_ctor_set(x_17, 0, x_18);
lean_inc_ref(x_17);
x_21 = l_Lean_MacroScopesView_review(x_17);
x_22 = l_Lean_Name_isPrefixOf(x_6, x_21);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec_ref(x_17);
lean_inc(x_9);
lean_dec_ref(x_8);
x_23 = l___private_Lean_ResolveName_0__Lean_resolveLocalName_go(x_9, x_7, x_21, x_6);
lean_dec(x_21);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
lean_dec(x_21);
lean_dec(x_6);
x_24 = l_Lean_LocalDecl_userName(x_9);
x_25 = l_Lean_extractMacroScopes(x_24);
x_26 = l_Lean_MacroScopesView_isSuffixOf(x_25, x_7);
lean_dec_ref(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec_ref(x_17);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
x_27 = lean_box(0);
return x_27;
}
else
{
uint8_t x_28; 
x_28 = l_Lean_MacroScopesView_isSuffixOf(x_7, x_17);
lean_dec_ref(x_17);
lean_dec_ref(x_7);
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec_ref(x_8);
x_29 = lean_box(0);
return x_29;
}
else
{
return x_8;
}
}
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_30 = lean_ctor_get(x_17, 1);
x_31 = lean_ctor_get(x_17, 2);
x_32 = lean_ctor_get(x_17, 3);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_17);
x_33 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_33, 0, x_18);
lean_ctor_set(x_33, 1, x_30);
lean_ctor_set(x_33, 2, x_31);
lean_ctor_set(x_33, 3, x_32);
lean_inc_ref(x_33);
x_34 = l_Lean_MacroScopesView_review(x_33);
x_35 = l_Lean_Name_isPrefixOf(x_6, x_34);
if (x_35 == 0)
{
lean_object* x_36; 
lean_dec_ref(x_33);
lean_inc(x_9);
lean_dec_ref(x_8);
x_36 = l___private_Lean_ResolveName_0__Lean_resolveLocalName_go(x_9, x_7, x_34, x_6);
lean_dec(x_34);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
lean_dec(x_34);
lean_dec(x_6);
x_37 = l_Lean_LocalDecl_userName(x_9);
x_38 = l_Lean_extractMacroScopes(x_37);
x_39 = l_Lean_MacroScopesView_isSuffixOf(x_38, x_7);
lean_dec_ref(x_38);
if (x_39 == 0)
{
lean_object* x_40; 
lean_dec_ref(x_33);
lean_dec_ref(x_8);
lean_dec_ref(x_7);
x_40 = lean_box(0);
return x_40;
}
else
{
uint8_t x_41; 
x_41 = l_Lean_MacroScopesView_isSuffixOf(x_7, x_33);
lean_dec_ref(x_33);
lean_dec_ref(x_7);
if (x_41 == 0)
{
lean_object* x_42; 
lean_dec_ref(x_8);
x_42 = lean_box(0);
return x_42;
}
else
{
return x_8;
}
}
}
}
}
}
}
}
else
{
lean_object* x_47; 
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_47 = lean_box(0);
return x_47;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_dec(x_3);
lean_dec_ref(x_2);
return x_4;
}
else
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec_ref(x_4);
x_6 = l_Lean_LocalDecl_isAuxDecl(x_5);
if (x_6 == 0)
{
lean_dec(x_5);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_inc(x_1);
return x_1;
}
else
{
lean_object* x_7; 
x_7 = lean_apply_2(x_2, x_5, x_3);
return x_7;
}
}
}
}
static lean_object* _init_l_Lean_resolveLocalName___redArg___lam__4___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_resolveLocalName___redArg___lam__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_resolveLocalName___redArg___lam__4___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_resolveLocalName___redArg___lam__4___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_resolveLocalName___redArg___lam__4___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_resolveLocalName___redArg___lam__4___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_resolveLocalName___redArg___lam__4___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_resolveLocalName___redArg___lam__4___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_resolveLocalName___redArg___lam__4___closed__1;
x_2 = l_Lean_resolveLocalName___redArg___lam__4___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_resolveLocalName___redArg___lam__4___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_resolveLocalName___redArg___lam__4___closed__5;
x_2 = l_Lean_resolveLocalName___redArg___lam__4___closed__4;
x_3 = l_Lean_resolveLocalName___redArg___lam__4___closed__3;
x_4 = l_Lean_resolveLocalName___redArg___lam__4___closed__2;
x_5 = l_Lean_resolveLocalName___redArg___lam__4___closed__7;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_2);
lean_ctor_set(x_6, 4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_resolveLocalName___redArg___lam__4___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_resolveLocalName___redArg___lam__4___closed__6;
x_2 = l_Lean_resolveLocalName___redArg___lam__4___closed__8;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_8);
lean_dec_ref(x_1);
lean_inc_ref(x_6);
x_9 = l_Lean_MacroScopesView_review(x_6);
x_10 = lean_box(x_7);
lean_inc(x_9);
lean_inc_ref(x_2);
x_11 = lean_alloc_closure((void*)(l_Lean_resolveLocalName___redArg___lam__2___boxed), 8, 7);
lean_closure_set(x_11, 0, x_2);
lean_closure_set(x_11, 1, x_9);
lean_closure_set(x_11, 2, x_10);
lean_closure_set(x_11, 3, x_3);
lean_closure_set(x_11, 4, x_4);
lean_closure_set(x_11, 5, x_5);
lean_closure_set(x_11, 6, x_6);
x_12 = l_Lean_resolveLocalName___redArg___lam__4___closed__9;
lean_inc_ref(x_8);
x_13 = l_Lean_PersistentArray_findSomeRevM_x3f___redArg(x_12, x_8, x_11);
if (lean_obj_tag(x_13) == 0)
{
if (x_7 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_alloc_closure((void*)(l_Lean_resolveLocalName___redArg___lam__3___boxed), 4, 3);
lean_closure_set(x_14, 0, x_13);
lean_closure_set(x_14, 1, x_2);
lean_closure_set(x_14, 2, x_9);
x_15 = l_Lean_PersistentArray_findSomeRevM_x3f___redArg(x_12, x_8, x_14);
return x_15;
}
else
{
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_2);
return x_13;
}
}
else
{
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_2);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_10 = l_Lean_extractMacroScopes(x_1);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_alloc_closure((void*)(l_Lean_resolveLocalName___redArg___lam__4___boxed), 7, 5);
lean_closure_set(x_12, 0, x_2);
lean_closure_set(x_12, 1, x_3);
lean_closure_set(x_12, 2, x_4);
lean_closure_set(x_12, 3, x_5);
lean_closure_set(x_12, 4, x_9);
x_13 = lean_box(0);
x_14 = 0;
x_15 = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg(x_6, x_7, x_8, x_10, x_12, x_11, x_13, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_9, 2);
lean_inc(x_10);
lean_dec_ref(x_9);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_alloc_closure((void*)(l_Lean_resolveLocalName___redArg___lam__5), 9, 8);
lean_closure_set(x_12, 0, x_2);
lean_closure_set(x_12, 1, x_3);
lean_closure_set(x_12, 2, x_4);
lean_closure_set(x_12, 3, x_5);
lean_closure_set(x_12, 4, x_10);
lean_closure_set(x_12, 5, x_6);
lean_closure_set(x_12, 6, x_1);
lean_closure_set(x_12, 7, x_7);
x_13 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
lean_inc(x_7);
x_10 = lean_alloc_closure((void*)(l_Lean_resolveLocalName___redArg___lam__6), 9, 8);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_2);
lean_closure_set(x_10, 2, x_9);
lean_closure_set(x_10, 3, x_3);
lean_closure_set(x_10, 4, x_4);
lean_closure_set(x_10, 5, x_5);
lean_closure_set(x_10, 6, x_6);
lean_closure_set(x_10, 7, x_7);
x_11 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_8, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_alloc_closure((void*)(l_Lean_resolveLocalName___redArg___lam__0___boxed), 2, 0);
x_8 = lean_alloc_closure((void*)(l_Lean_resolveLocalName___redArg___lam__1___boxed), 2, 0);
lean_inc(x_4);
lean_inc(x_6);
x_9 = lean_alloc_closure((void*)(l_Lean_resolveLocalName___redArg___lam__7), 9, 8);
lean_closure_set(x_9, 0, x_2);
lean_closure_set(x_9, 1, x_5);
lean_closure_set(x_9, 2, x_8);
lean_closure_set(x_9, 3, x_7);
lean_closure_set(x_9, 4, x_1);
lean_closure_set(x_9, 5, x_3);
lean_closure_set(x_9, 6, x_6);
lean_closure_set(x_9, 7, x_4);
x_10 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_4, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_resolveLocalName___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_resolveLocalName___redArg___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_resolveLocalName___redArg___lam__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
x_10 = l_Lean_resolveLocalName___redArg___lam__2(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_resolveLocalName___redArg___lam__3(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_7);
x_9 = l_Lean_resolveLocalName___redArg___lam__4(x_1, x_2, x_3, x_4, x_5, x_6, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_unresolveNameCore___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = lean_apply_2(x_1, lean_box(0), x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_unresolveNameCore___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec_ref(x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_box(0);
x_7 = lean_apply_2(x_1, lean_box(0), x_6);
x_8 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_7, x_3);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
lean_dec_ref(x_5);
x_10 = lean_apply_2(x_1, lean_box(0), x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_unresolveNameCore___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_unresolveNameCore___redArg___lam__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
x_6 = lean_box(0);
x_7 = lean_apply_2(x_1, lean_box(0), x_6);
x_8 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_7, x_3);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_3);
lean_dec(x_2);
lean_inc(x_4);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_4);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_4);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_apply_2(x_1, lean_box(0), x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_unresolveNameCore___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_9) == 0)
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
goto block_13;
}
else
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_9, 1);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_9, 0);
lean_dec(x_3);
x_16 = lean_ctor_get(x_15, 0);
x_17 = lean_name_eq(x_16, x_4);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_18 = lean_box(0);
x_19 = lean_apply_2(x_1, lean_box(0), x_18);
x_20 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_19, x_5);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_5);
lean_dec(x_1);
x_21 = lean_apply_1(x_6, x_7);
x_22 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_21, x_8);
return x_22;
}
}
else
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
goto block_13;
}
}
block_13:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_box(0);
x_11 = lean_apply_2(x_1, lean_box(0), x_10);
x_12 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_11, x_3);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_unresolveNameCore___redArg___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = l_Lean_Name_appendCore(x_9, x_12);
lean_inc(x_2);
lean_inc(x_13);
x_14 = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_unresolveNameCore___redArg___lam__2), 4, 3);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_13);
lean_closure_set(x_14, 2, x_2);
lean_inc(x_13);
lean_inc_ref(x_14);
lean_inc(x_3);
lean_inc(x_2);
x_15 = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_unresolveNameCore___redArg___lam__5___boxed), 5, 4);
lean_closure_set(x_15, 0, x_2);
lean_closure_set(x_15, 1, x_3);
lean_closure_set(x_15, 2, x_14);
lean_closure_set(x_15, 3, x_13);
lean_inc(x_13);
lean_inc_ref(x_14);
lean_inc(x_3);
x_16 = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_unresolveNameCore___redArg___lam__3___boxed), 9, 8);
lean_closure_set(x_16, 0, x_2);
lean_closure_set(x_16, 1, x_3);
lean_closure_set(x_16, 2, x_14);
lean_closure_set(x_16, 3, x_4);
lean_closure_set(x_16, 4, x_14);
lean_closure_set(x_16, 5, x_5);
lean_closure_set(x_16, 6, x_13);
lean_closure_set(x_16, 7, x_15);
x_17 = l_Lean_resolveGlobalName___redArg(x_6, x_7, x_8, x_13);
x_18 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_17, x_16);
return x_18;
}
}
static lean_object* _init_l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_unresolveNameCore___redArg___lam__6___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_unresolveNameCore___redArg___lam__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = l_Lean_privateToUserName(x_1);
x_12 = l_Lean_Name_componentsRev(x_11);
x_13 = lean_box(0);
lean_inc_ref(x_6);
lean_inc(x_3);
x_14 = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_unresolveNameCore___redArg___lam__4___boxed), 11, 8);
lean_closure_set(x_14, 0, x_13);
lean_closure_set(x_14, 1, x_2);
lean_closure_set(x_14, 2, x_3);
lean_closure_set(x_14, 3, x_4);
lean_closure_set(x_14, 4, x_5);
lean_closure_set(x_14, 5, x_6);
lean_closure_set(x_14, 6, x_7);
lean_closure_set(x_14, 7, x_8);
x_15 = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_unresolveNameCore___redArg___lam__6___closed__0;
x_16 = l_List_forIn_x27_loop___redArg(x_6, x_14, x_12, x_15);
x_17 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_16, x_9);
return x_17;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_unresolveNameCore___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
x_10 = l_Lean_Name_hasMacroScopes(x_6);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_inc(x_9);
x_11 = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_unresolveNameCore___redArg___lam__0), 2, 1);
lean_closure_set(x_11, 0, x_9);
lean_inc(x_8);
lean_inc(x_9);
x_12 = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_unresolveNameCore___redArg___lam__1), 4, 3);
lean_closure_set(x_12, 0, x_9);
lean_closure_set(x_12, 1, x_8);
lean_closure_set(x_12, 2, x_11);
lean_inc(x_8);
lean_inc(x_9);
x_13 = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_unresolveNameCore___redArg___lam__6), 10, 9);
lean_closure_set(x_13, 0, x_6);
lean_closure_set(x_13, 1, x_9);
lean_closure_set(x_13, 2, x_8);
lean_closure_set(x_13, 3, x_4);
lean_closure_set(x_13, 4, x_5);
lean_closure_set(x_13, 5, x_1);
lean_closure_set(x_13, 6, x_2);
lean_closure_set(x_13, 7, x_3);
lean_closure_set(x_13, 8, x_12);
x_14 = lean_box(0);
x_15 = lean_apply_2(x_9, lean_box(0), x_14);
x_16 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_15, x_13);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_17 = lean_box(0);
x_18 = lean_apply_2(x_9, lean_box(0), x_17);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_unresolveNameCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_unresolveNameCore___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_unresolveNameCore___redArg___lam__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_5);
x_7 = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_unresolveNameCore___redArg___lam__5(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_unresolveNameCore___redArg___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_unresolveNameCore___redArg___lam__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_unresolveNameCore___redArg___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_unresolveNameCore___redArg___lam__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, lean_box(0), x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec_ref(x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_apply_2(x_1, lean_box(0), x_2);
x_8 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_7, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
lean_dec(x_3);
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec_ref(x_6);
x_10 = lean_apply_2(x_1, lean_box(0), x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_1);
x_5 = lean_apply_2(x_2, lean_box(0), x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_apply_2(x_1, lean_box(0), x_2);
x_7 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_6, x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
lean_dec(x_3);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_2);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_apply_2(x_1, lean_box(0), x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___redArg___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_unresolveNameCore___redArg(x_1, x_2, x_3, x_4, x_5, x_8);
x_12 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_11, x_7);
return x_12;
}
}
static lean_object* _init_l_Lean_unresolveNameGlobal___redArg___lam__5___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___redArg___lam__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; 
x_11 = lean_box(0);
lean_inc(x_2);
lean_inc(x_1);
x_12 = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal___redArg___lam__1), 5, 4);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_11);
lean_closure_set(x_12, 2, x_2);
lean_closure_set(x_12, 3, x_3);
x_13 = l_Lean_unresolveNameGlobal___redArg___lam__5___closed__0;
lean_inc(x_1);
x_14 = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal___redArg___lam__2), 3, 2);
lean_closure_set(x_14, 0, x_13);
lean_closure_set(x_14, 1, x_1);
lean_inc(x_2);
x_15 = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal___redArg___lam__3), 5, 4);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_11);
lean_closure_set(x_15, 2, x_2);
lean_closure_set(x_15, 3, x_14);
lean_inc(x_2);
lean_inc_ref(x_4);
x_16 = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal___redArg___lam__4___boxed), 10, 7);
lean_closure_set(x_16, 0, x_4);
lean_closure_set(x_16, 1, x_5);
lean_closure_set(x_16, 2, x_6);
lean_closure_set(x_16, 3, x_7);
lean_closure_set(x_16, 4, x_8);
lean_closure_set(x_16, 5, x_2);
lean_closure_set(x_16, 6, x_15);
x_17 = lean_array_size(x_9);
x_18 = 0;
x_19 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), x_4, x_9, x_16, x_17, x_18, x_13);
x_20 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_19, x_12);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___redArg___lam__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___redArg___lam__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal___redArg___lam__6), 3, 2);
lean_closure_set(x_7, 0, x_2);
lean_closure_set(x_7, 1, x_5);
x_8 = lean_box(0);
x_9 = lean_apply_2(x_3, lean_box(0), x_8);
x_10 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_9, x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec_ref(x_1);
x_12 = lean_array_push(x_5, x_11);
x_13 = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal___redArg___lam__6), 3, 2);
lean_closure_set(x_13, 0, x_2);
lean_closure_set(x_13, 1, x_12);
x_14 = lean_box(0);
x_15 = lean_apply_2(x_3, lean_box(0), x_14);
x_16 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_15, x_13);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___redArg___lam__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = l_Lean_Name_getPrefix(x_3);
x_5 = l_Lean_Name_getPrefix(x_1);
x_6 = l_Lean_Name_isPrefixOf(x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
if (x_6 == 0)
{
lean_dec(x_3);
return x_2;
}
else
{
lean_object* x_7; 
x_7 = lean_array_push(x_2, x_3);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___redArg___lam__9(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___redArg___lam__11(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_14; lean_object* x_15; 
x_14 = l_Lean_getRevAliases(x_7, x_1);
x_15 = lean_array_mk(x_14);
if (x_2 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_get_size(x_15);
x_18 = l_Lean_resolveNamespace___redArg___closed__0;
x_19 = l_Lean_resolveLocalName___redArg___lam__4___closed__9;
x_20 = lean_nat_dec_lt(x_16, x_17);
if (x_20 == 0)
{
lean_dec(x_17);
lean_dec_ref(x_15);
lean_dec_ref(x_6);
x_8 = x_18;
goto block_13;
}
else
{
uint8_t x_21; 
x_21 = lean_nat_dec_le(x_17, x_17);
if (x_21 == 0)
{
lean_dec(x_17);
lean_dec_ref(x_15);
lean_dec_ref(x_6);
x_8 = x_18;
goto block_13;
}
else
{
size_t x_22; size_t x_23; lean_object* x_24; 
x_22 = 0;
x_23 = lean_usize_of_nat(x_17);
lean_dec(x_17);
x_24 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_19, x_6, x_15, x_22, x_23, x_18);
x_8 = x_24;
goto block_13;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec_ref(x_6);
x_25 = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal___redArg___lam__6), 3, 2);
lean_closure_set(x_25, 0, x_3);
lean_closure_set(x_25, 1, x_15);
x_26 = lean_box(0);
x_27 = lean_apply_2(x_4, lean_box(0), x_26);
x_28 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_27, x_25);
return x_28;
}
block_13:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal___redArg___lam__9), 3, 2);
lean_closure_set(x_9, 0, x_3);
lean_closure_set(x_9, 1, x_8);
x_10 = lean_box(0);
x_11 = lean_apply_2(x_4, lean_box(0), x_10);
x_12 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_11, x_9);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___redArg___lam__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_4(x_1, lean_box(0), lean_box(0), x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___redArg___lam__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; 
x_5 = lean_apply_2(x_2, lean_box(0), x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_apply_2(x_2, lean_box(0), x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___redArg___lam__15(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
x_6 = lean_apply_2(x_1, lean_box(0), x_5);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_3);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___redArg___lam__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
x_6 = lean_box(0);
x_7 = lean_apply_2(x_1, lean_box(0), x_6);
x_8 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_7, x_3);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_apply_2(x_1, lean_box(0), x_4);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___redArg___lam__14(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_7) == 0)
{
lean_dec(x_6);
lean_dec(x_5);
goto block_11;
}
else
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_7, 1);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_7, 0);
lean_dec(x_3);
x_14 = lean_ctor_get(x_13, 0);
x_15 = lean_name_eq(x_14, x_4);
x_16 = lean_box(x_15);
x_17 = lean_apply_2(x_1, lean_box(0), x_16);
lean_inc(x_2);
x_18 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_17, x_5);
x_19 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_18, x_6);
return x_19;
}
else
{
lean_dec(x_6);
lean_dec(x_5);
goto block_11;
}
}
block_11:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_box(0);
x_9 = lean_apply_2(x_1, lean_box(0), x_8);
x_10 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_9, x_3);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___redArg___lam__16(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_31; 
lean_inc(x_5);
x_31 = lean_private_to_user_name(x_5);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveExact___closed__0;
lean_inc(x_5);
x_33 = l_Lean_Name_append(x_32, x_5);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
lean_inc(x_5);
x_13 = x_5;
x_14 = x_34;
goto block_30;
}
else
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_31);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = lean_ctor_get(x_31, 0);
lean_inc(x_36);
x_37 = l_Lean_mkPrivateName(x_12, x_36);
x_38 = lean_name_eq(x_5, x_37);
lean_dec(x_37);
if (x_38 == 0)
{
lean_object* x_39; 
lean_free_object(x_31);
x_39 = lean_box(0);
x_13 = x_36;
x_14 = x_39;
goto block_30;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveExact___closed__0;
lean_inc(x_36);
x_41 = l_Lean_Name_append(x_40, x_36);
lean_ctor_set(x_31, 0, x_41);
x_13 = x_36;
x_14 = x_31;
goto block_30;
}
}
else
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_42 = lean_ctor_get(x_31, 0);
lean_inc(x_42);
lean_dec(x_31);
lean_inc(x_42);
x_43 = l_Lean_mkPrivateName(x_12, x_42);
x_44 = lean_name_eq(x_5, x_43);
lean_dec(x_43);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = lean_box(0);
x_13 = x_42;
x_14 = x_45;
goto block_30;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveExact___closed__0;
lean_inc(x_42);
x_47 = l_Lean_Name_append(x_46, x_42);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_13 = x_42;
x_14 = x_48;
goto block_30;
}
}
}
block_30:
{
if (x_1 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_inc(x_4);
lean_inc(x_3);
x_15 = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal___redArg___lam__8), 6, 4);
lean_closure_set(x_15, 0, x_14);
lean_closure_set(x_15, 1, x_2);
lean_closure_set(x_15, 2, x_3);
lean_closure_set(x_15, 3, x_4);
x_16 = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal___redArg___lam__7___boxed), 3, 1);
lean_closure_set(x_16, 0, x_13);
x_17 = lean_box(x_6);
lean_inc(x_4);
lean_inc(x_3);
x_18 = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal___redArg___lam__11___boxed), 7, 6);
lean_closure_set(x_18, 0, x_5);
lean_closure_set(x_18, 1, x_17);
lean_closure_set(x_18, 2, x_15);
lean_closure_set(x_18, 3, x_3);
lean_closure_set(x_18, 4, x_4);
lean_closure_set(x_18, 5, x_16);
lean_inc(x_4);
x_19 = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal___redArg___lam__10), 4, 3);
lean_closure_set(x_19, 0, x_4);
lean_closure_set(x_19, 1, x_7);
lean_closure_set(x_19, 2, x_18);
x_20 = lean_box(0);
x_21 = lean_apply_2(x_3, lean_box(0), x_20);
x_22 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_21, x_19);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_7);
lean_dec(x_2);
lean_inc(x_5);
lean_inc(x_3);
x_23 = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal___redArg___lam__12), 4, 3);
lean_closure_set(x_23, 0, x_14);
lean_closure_set(x_23, 1, x_3);
lean_closure_set(x_23, 2, x_5);
x_24 = lean_alloc_closure((void*)(l_Lean_filterFieldList___redArg___lam__3), 2, 1);
lean_closure_set(x_24, 0, x_23);
lean_inc(x_13);
lean_inc(x_3);
x_25 = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal___redArg___lam__15___boxed), 4, 3);
lean_closure_set(x_25, 0, x_3);
lean_closure_set(x_25, 1, x_8);
lean_closure_set(x_25, 2, x_13);
lean_inc(x_13);
lean_inc_ref(x_24);
lean_inc(x_4);
lean_inc(x_3);
x_26 = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal___redArg___lam__13___boxed), 5, 4);
lean_closure_set(x_26, 0, x_3);
lean_closure_set(x_26, 1, x_4);
lean_closure_set(x_26, 2, x_24);
lean_closure_set(x_26, 3, x_13);
lean_inc(x_4);
x_27 = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal___redArg___lam__14___boxed), 7, 6);
lean_closure_set(x_27, 0, x_3);
lean_closure_set(x_27, 1, x_4);
lean_closure_set(x_27, 2, x_24);
lean_closure_set(x_27, 3, x_5);
lean_closure_set(x_27, 4, x_25);
lean_closure_set(x_27, 5, x_26);
x_28 = l_Lean_resolveGlobalName___redArg(x_9, x_10, x_11, x_13);
x_29 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_28, x_27);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___redArg___lam__17(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_box(x_2);
x_14 = lean_box(x_7);
lean_inc(x_12);
lean_inc(x_5);
x_15 = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal___redArg___lam__16___boxed), 12, 11);
lean_closure_set(x_15, 0, x_13);
lean_closure_set(x_15, 1, x_3);
lean_closure_set(x_15, 2, x_4);
lean_closure_set(x_15, 3, x_5);
lean_closure_set(x_15, 4, x_6);
lean_closure_set(x_15, 5, x_14);
lean_closure_set(x_15, 6, x_12);
lean_closure_set(x_15, 7, x_8);
lean_closure_set(x_15, 8, x_9);
lean_closure_set(x_15, 9, x_10);
lean_closure_set(x_15, 10, x_1);
x_16 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_12, x_15);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
x_11 = l_Lean_Name_hasMacroScopes(x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_inc(x_4);
lean_inc(x_10);
x_12 = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal___redArg___lam__0), 3, 2);
lean_closure_set(x_12, 0, x_10);
lean_closure_set(x_12, 1, x_4);
lean_inc(x_7);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
lean_inc(x_9);
lean_inc(x_10);
x_13 = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal___redArg___lam__5), 10, 8);
lean_closure_set(x_13, 0, x_10);
lean_closure_set(x_13, 1, x_9);
lean_closure_set(x_13, 2, x_12);
lean_closure_set(x_13, 3, x_1);
lean_closure_set(x_13, 4, x_2);
lean_closure_set(x_13, 5, x_3);
lean_closure_set(x_13, 6, x_4);
lean_closure_set(x_13, 7, x_7);
x_14 = lean_box(x_5);
x_15 = lean_box(x_6);
lean_inc(x_9);
lean_inc(x_10);
x_16 = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal___redArg___lam__17___boxed), 11, 10);
lean_closure_set(x_16, 0, x_3);
lean_closure_set(x_16, 1, x_14);
lean_closure_set(x_16, 2, x_13);
lean_closure_set(x_16, 3, x_10);
lean_closure_set(x_16, 4, x_9);
lean_closure_set(x_16, 5, x_4);
lean_closure_set(x_16, 6, x_15);
lean_closure_set(x_16, 7, x_7);
lean_closure_set(x_16, 8, x_1);
lean_closure_set(x_16, 9, x_2);
x_17 = lean_box(0);
x_18 = lean_apply_2(x_10, lean_box(0), x_17);
x_19 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_18, x_16);
return x_19;
}
else
{
lean_object* x_20; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_20 = lean_apply_2(x_10, lean_box(0), x_4);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, uint8_t x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_unresolveNameGlobal___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___redArg___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_unresolveNameGlobal___redArg___lam__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___redArg___lam__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_unresolveNameGlobal___redArg___lam__7(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___redArg___lam__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
x_9 = l_Lean_unresolveNameGlobal___redArg___lam__11(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___redArg___lam__15___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_4);
x_6 = l_Lean_unresolveNameGlobal___redArg___lam__15(x_1, x_2, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___redArg___lam__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_5);
x_7 = l_Lean_unresolveNameGlobal___redArg___lam__13(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___redArg___lam__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_unresolveNameGlobal___redArg___lam__14(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___redArg___lam__16___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_unbox(x_1);
x_14 = lean_unbox(x_6);
x_15 = l_Lean_unresolveNameGlobal___redArg___lam__16(x_13, x_2, x_3, x_4, x_5, x_14, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_12);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___redArg___lam__17___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_2);
x_13 = lean_unbox(x_7);
x_14 = l_Lean_unresolveNameGlobal___redArg___lam__17(x_1, x_12, x_3, x_4, x_5, x_6, x_13, x_8, x_9, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_unbox(x_5);
x_9 = lean_unbox(x_6);
x_10 = l_Lean_unresolveNameGlobal___redArg(x_1, x_2, x_3, x_4, x_8, x_9, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_unbox(x_6);
x_10 = lean_unbox(x_7);
x_11 = l_Lean_unresolveNameGlobal(x_1, x_2, x_3, x_4, x_5, x_9, x_10, x_8);
return x_11;
}
}
static lean_object* _init_l_Lean_unresolveNameGlobalAvoidingLocals___redArg___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Option_isNone___boxed), 2, 1);
lean_closure_set(x_1, 0, lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = l_Lean_unresolveNameGlobalAvoidingLocals___redArg___lam__0___closed__0;
x_9 = l_Lean_resolveLocalName___redArg(x_2, x_3, x_4, x_5, x_6);
x_10 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_7, 0);
x_9 = 0;
lean_inc_ref(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
lean_inc_ref(x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobalAvoidingLocals___redArg___lam__0), 6, 5);
lean_closure_set(x_10, 0, x_8);
lean_closure_set(x_10, 1, x_1);
lean_closure_set(x_10, 2, x_2);
lean_closure_set(x_10, 3, x_3);
lean_closure_set(x_10, 4, x_4);
x_11 = l_Lean_unresolveNameGlobal___redArg(x_1, x_2, x_3, x_5, x_6, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_unresolveNameGlobalAvoidingLocals___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_6);
x_8 = l_Lean_unresolveNameGlobalAvoidingLocals___redArg(x_1, x_2, x_3, x_4, x_5, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_7);
x_9 = l_Lean_unresolveNameGlobalAvoidingLocals(x_1, x_2, x_3, x_4, x_5, x_6, x_8);
return x_9;
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
l_Lean_throwReservedNameNotAvailable___redArg___closed__0 = _init_l_Lean_throwReservedNameNotAvailable___redArg___closed__0();
lean_mark_persistent(l_Lean_throwReservedNameNotAvailable___redArg___closed__0);
l_Lean_throwReservedNameNotAvailable___redArg___closed__1 = _init_l_Lean_throwReservedNameNotAvailable___redArg___closed__1();
lean_mark_persistent(l_Lean_throwReservedNameNotAvailable___redArg___closed__1);
l_Lean_throwReservedNameNotAvailable___redArg___closed__2 = _init_l_Lean_throwReservedNameNotAvailable___redArg___closed__2();
lean_mark_persistent(l_Lean_throwReservedNameNotAvailable___redArg___closed__2);
l_Lean_throwReservedNameNotAvailable___redArg___closed__3 = _init_l_Lean_throwReservedNameNotAvailable___redArg___closed__3();
lean_mark_persistent(l_Lean_throwReservedNameNotAvailable___redArg___closed__3);
l_Lean_throwReservedNameNotAvailable___redArg___closed__4 = _init_l_Lean_throwReservedNameNotAvailable___redArg___closed__4();
lean_mark_persistent(l_Lean_throwReservedNameNotAvailable___redArg___closed__4);
l_Lean_throwReservedNameNotAvailable___redArg___closed__5 = _init_l_Lean_throwReservedNameNotAvailable___redArg___closed__5();
lean_mark_persistent(l_Lean_throwReservedNameNotAvailable___redArg___closed__5);
l_Lean_initFn___closed__0____x40_Lean_ResolveName_2351709485____hygCtx___hyg_2_ = _init_l_Lean_initFn___closed__0____x40_Lean_ResolveName_2351709485____hygCtx___hyg_2_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_ResolveName_2351709485____hygCtx___hyg_2_);
if (builtin) {res = l_Lean_initFn____x40_Lean_ResolveName_2351709485____hygCtx___hyg_2_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_reservedNamePredicatesRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_reservedNamePredicatesRef);
lean_dec_ref(res);
}l_Lean_registerReservedNamePredicate___closed__0 = _init_l_Lean_registerReservedNamePredicate___closed__0();
lean_mark_persistent(l_Lean_registerReservedNamePredicate___closed__0);
l_Lean_registerReservedNamePredicate___closed__1 = _init_l_Lean_registerReservedNamePredicate___closed__1();
lean_mark_persistent(l_Lean_registerReservedNamePredicate___closed__1);
l_Lean_registerReservedNamePredicate___closed__2 = _init_l_Lean_registerReservedNamePredicate___closed__2();
lean_mark_persistent(l_Lean_registerReservedNamePredicate___closed__2);
if (builtin) {res = l_Lean_initFn____x40_Lean_ResolveName_405991711____hygCtx___hyg_2_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_reservedNamePredicatesExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_reservedNamePredicatesExt);
lean_dec_ref(res);
}l_Lean_isReservedName___closed__0 = _init_l_Lean_isReservedName___closed__0();
lean_mark_persistent(l_Lean_isReservedName___closed__0);
l_Lean_isReservedName___closed__1 = _init_l_Lean_isReservedName___closed__1();
lean_mark_persistent(l_Lean_isReservedName___closed__1);
l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f___at___Lean_addAliasEntry_spec__0_spec__0_spec__0___redArg___closed__0 = _init_l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f___at___Lean_addAliasEntry_spec__0_spec__0_spec__0___redArg___closed__0();
l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f___at___Lean_addAliasEntry_spec__0_spec__0_spec__0___redArg___closed__1 = _init_l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_SMap_find_x3f___at___Lean_addAliasEntry_spec__0_spec__0_spec__0___redArg___closed__1();
l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__6_spec__6___redArg___closed__0 = _init_l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__6_spec__6___redArg___closed__0();
lean_mark_persistent(l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at___Lean_addAliasEntry_spec__6_spec__6_spec__6___redArg___closed__0);
l_Lean_initFn___lam__1___closed__0____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_ = _init_l_Lean_initFn___lam__1___closed__0____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_();
lean_mark_persistent(l_Lean_initFn___lam__1___closed__0____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_);
l_Lean_initFn___lam__1___closed__1____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_ = _init_l_Lean_initFn___lam__1___closed__1____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_();
lean_mark_persistent(l_Lean_initFn___lam__1___closed__1____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_);
l_Lean_initFn___lam__1___closed__2____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_ = _init_l_Lean_initFn___lam__1___closed__2____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_();
lean_mark_persistent(l_Lean_initFn___lam__1___closed__2____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_);
l_Lean_initFn___lam__1___closed__3____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_ = _init_l_Lean_initFn___lam__1___closed__3____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_();
lean_mark_persistent(l_Lean_initFn___lam__1___closed__3____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_);
l_Lean_initFn___lam__1___closed__4____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_ = _init_l_Lean_initFn___lam__1___closed__4____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_();
lean_mark_persistent(l_Lean_initFn___lam__1___closed__4____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_);
l_Lean_initFn___lam__1___closed__5____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_ = _init_l_Lean_initFn___lam__1___closed__5____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_();
lean_mark_persistent(l_Lean_initFn___lam__1___closed__5____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_);
l_Lean_initFn___lam__1___closed__6____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_ = _init_l_Lean_initFn___lam__1___closed__6____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_();
lean_mark_persistent(l_Lean_initFn___lam__1___closed__6____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_);
l_Lean_initFn___lam__1___closed__7____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_ = _init_l_Lean_initFn___lam__1___closed__7____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_();
lean_mark_persistent(l_Lean_initFn___lam__1___closed__7____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_);
l_Lean_initFn___closed__0____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_ = _init_l_Lean_initFn___closed__0____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_);
l_Lean_initFn___closed__1____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_ = _init_l_Lean_initFn___closed__1____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_);
l_Lean_initFn___closed__2____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_ = _init_l_Lean_initFn___closed__2____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_);
l_Lean_initFn___closed__3____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_ = _init_l_Lean_initFn___closed__3____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_();
lean_mark_persistent(l_Lean_initFn___closed__3____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_);
if (builtin) {res = l_Lean_initFn____x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_aliasExtension = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_aliasExtension);
lean_dec_ref(res);
}l_Lean_addAlias___closed__0 = _init_l_Lean_addAlias___closed__0();
lean_mark_persistent(l_Lean_addAlias___closed__0);
l_Lean_getAliasState___closed__0 = _init_l_Lean_getAliasState___closed__0();
lean_mark_persistent(l_Lean_getAliasState___closed__0);
l_Lean_getAliasState___closed__1 = _init_l_Lean_getAliasState___closed__1();
lean_mark_persistent(l_Lean_getAliasState___closed__1);
l_Lean_getAliasState___closed__2 = _init_l_Lean_getAliasState___closed__2();
lean_mark_persistent(l_Lean_getAliasState___closed__2);
l___private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName___closed__0 = _init_l___private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName___closed__0();
lean_mark_persistent(l___private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName___closed__0);
l___private_Lean_ResolveName_0__Lean_ResolveName_resolveExact___closed__0 = _init_l___private_Lean_ResolveName_0__Lean_ResolveName_resolveExact___closed__0();
lean_mark_persistent(l___private_Lean_ResolveName_0__Lean_ResolveName_resolveExact___closed__0);
l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__0 = _init_l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__0();
lean_mark_persistent(l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__0);
l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__1 = _init_l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__1();
lean_mark_persistent(l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__1);
l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__2 = _init_l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__2();
lean_mark_persistent(l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__2);
l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__3 = _init_l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__3();
lean_mark_persistent(l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__3);
l_Lean_resolveNamespaceCore___redArg___lam__2___closed__0 = _init_l_Lean_resolveNamespaceCore___redArg___lam__2___closed__0();
lean_mark_persistent(l_Lean_resolveNamespaceCore___redArg___lam__2___closed__0);
l_Lean_resolveNamespaceCore___redArg___lam__2___closed__1 = _init_l_Lean_resolveNamespaceCore___redArg___lam__2___closed__1();
lean_mark_persistent(l_Lean_resolveNamespaceCore___redArg___lam__2___closed__1);
l_Lean_resolveNamespace___redArg___closed__0 = _init_l_Lean_resolveNamespace___redArg___closed__0();
lean_mark_persistent(l_Lean_resolveNamespace___redArg___closed__0);
l_Lean_resolveNamespace___redArg___closed__1 = _init_l_Lean_resolveNamespace___redArg___closed__1();
lean_mark_persistent(l_Lean_resolveNamespace___redArg___closed__1);
l_Lean_resolveNamespace___redArg___closed__2 = _init_l_Lean_resolveNamespace___redArg___closed__2();
lean_mark_persistent(l_Lean_resolveNamespace___redArg___closed__2);
l_Lean_resolveNamespace___redArg___closed__3 = _init_l_Lean_resolveNamespace___redArg___closed__3();
lean_mark_persistent(l_Lean_resolveNamespace___redArg___closed__3);
l_Lean_resolveUniqueNamespace___redArg___lam__0___closed__0 = _init_l_Lean_resolveUniqueNamespace___redArg___lam__0___closed__0();
lean_mark_persistent(l_Lean_resolveUniqueNamespace___redArg___lam__0___closed__0);
l_Lean_resolveUniqueNamespace___redArg___lam__0___closed__1 = _init_l_Lean_resolveUniqueNamespace___redArg___lam__0___closed__1();
lean_mark_persistent(l_Lean_resolveUniqueNamespace___redArg___lam__0___closed__1);
l_Lean_resolveUniqueNamespace___redArg___closed__0 = _init_l_Lean_resolveUniqueNamespace___redArg___closed__0();
lean_mark_persistent(l_Lean_resolveUniqueNamespace___redArg___closed__0);
l_Lean_ensureNoOverload___redArg___closed__0 = _init_l_Lean_ensureNoOverload___redArg___closed__0();
lean_mark_persistent(l_Lean_ensureNoOverload___redArg___closed__0);
l_Lean_ensureNoOverload___redArg___closed__1 = _init_l_Lean_ensureNoOverload___redArg___closed__1();
lean_mark_persistent(l_Lean_ensureNoOverload___redArg___closed__1);
l_Lean_ensureNoOverload___redArg___closed__2 = _init_l_Lean_ensureNoOverload___redArg___closed__2();
lean_mark_persistent(l_Lean_ensureNoOverload___redArg___closed__2);
l_Lean_ensureNoOverload___redArg___closed__3 = _init_l_Lean_ensureNoOverload___redArg___closed__3();
lean_mark_persistent(l_Lean_ensureNoOverload___redArg___closed__3);
l_Lean_ensureNoOverload___redArg___closed__4 = _init_l_Lean_ensureNoOverload___redArg___closed__4();
lean_mark_persistent(l_Lean_ensureNoOverload___redArg___closed__4);
l_Lean_ensureNoOverload___redArg___closed__5 = _init_l_Lean_ensureNoOverload___redArg___closed__5();
lean_mark_persistent(l_Lean_ensureNoOverload___redArg___closed__5);
l_Lean_ensureNoOverload___redArg___closed__6 = _init_l_Lean_ensureNoOverload___redArg___closed__6();
lean_mark_persistent(l_Lean_ensureNoOverload___redArg___closed__6);
l_Lean_ensureNonAmbiguous___redArg___closed__0 = _init_l_Lean_ensureNonAmbiguous___redArg___closed__0();
lean_mark_persistent(l_Lean_ensureNonAmbiguous___redArg___closed__0);
l_Lean_ensureNonAmbiguous___redArg___closed__1 = _init_l_Lean_ensureNonAmbiguous___redArg___closed__1();
lean_mark_persistent(l_Lean_ensureNonAmbiguous___redArg___closed__1);
l_Lean_ensureNonAmbiguous___redArg___closed__2 = _init_l_Lean_ensureNonAmbiguous___redArg___closed__2();
lean_mark_persistent(l_Lean_ensureNonAmbiguous___redArg___closed__2);
l_Lean_ensureNonAmbiguous___redArg___closed__3 = _init_l_Lean_ensureNonAmbiguous___redArg___closed__3();
lean_mark_persistent(l_Lean_ensureNonAmbiguous___redArg___closed__3);
l_Lean_ensureNonAmbiguous___redArg___closed__4 = _init_l_Lean_ensureNonAmbiguous___redArg___closed__4();
lean_mark_persistent(l_Lean_ensureNonAmbiguous___redArg___closed__4);
l_Lean_ensureNonAmbiguous___redArg___closed__5 = _init_l_Lean_ensureNonAmbiguous___redArg___closed__5();
lean_mark_persistent(l_Lean_ensureNonAmbiguous___redArg___closed__5);
l_Lean_ensureNonAmbiguous___redArg___closed__6 = _init_l_Lean_ensureNonAmbiguous___redArg___closed__6();
lean_mark_persistent(l_Lean_ensureNonAmbiguous___redArg___closed__6);
l_Lean_resolveLocalName___redArg___lam__4___closed__0 = _init_l_Lean_resolveLocalName___redArg___lam__4___closed__0();
lean_mark_persistent(l_Lean_resolveLocalName___redArg___lam__4___closed__0);
l_Lean_resolveLocalName___redArg___lam__4___closed__1 = _init_l_Lean_resolveLocalName___redArg___lam__4___closed__1();
lean_mark_persistent(l_Lean_resolveLocalName___redArg___lam__4___closed__1);
l_Lean_resolveLocalName___redArg___lam__4___closed__2 = _init_l_Lean_resolveLocalName___redArg___lam__4___closed__2();
lean_mark_persistent(l_Lean_resolveLocalName___redArg___lam__4___closed__2);
l_Lean_resolveLocalName___redArg___lam__4___closed__3 = _init_l_Lean_resolveLocalName___redArg___lam__4___closed__3();
lean_mark_persistent(l_Lean_resolveLocalName___redArg___lam__4___closed__3);
l_Lean_resolveLocalName___redArg___lam__4___closed__4 = _init_l_Lean_resolveLocalName___redArg___lam__4___closed__4();
lean_mark_persistent(l_Lean_resolveLocalName___redArg___lam__4___closed__4);
l_Lean_resolveLocalName___redArg___lam__4___closed__5 = _init_l_Lean_resolveLocalName___redArg___lam__4___closed__5();
lean_mark_persistent(l_Lean_resolveLocalName___redArg___lam__4___closed__5);
l_Lean_resolveLocalName___redArg___lam__4___closed__6 = _init_l_Lean_resolveLocalName___redArg___lam__4___closed__6();
lean_mark_persistent(l_Lean_resolveLocalName___redArg___lam__4___closed__6);
l_Lean_resolveLocalName___redArg___lam__4___closed__7 = _init_l_Lean_resolveLocalName___redArg___lam__4___closed__7();
lean_mark_persistent(l_Lean_resolveLocalName___redArg___lam__4___closed__7);
l_Lean_resolveLocalName___redArg___lam__4___closed__8 = _init_l_Lean_resolveLocalName___redArg___lam__4___closed__8();
lean_mark_persistent(l_Lean_resolveLocalName___redArg___lam__4___closed__8);
l_Lean_resolveLocalName___redArg___lam__4___closed__9 = _init_l_Lean_resolveLocalName___redArg___lam__4___closed__9();
lean_mark_persistent(l_Lean_resolveLocalName___redArg___lam__4___closed__9);
l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_unresolveNameCore___redArg___lam__6___closed__0 = _init_l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_unresolveNameCore___redArg___lam__6___closed__0();
lean_mark_persistent(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_unresolveNameCore___redArg___lam__6___closed__0);
l_Lean_unresolveNameGlobal___redArg___lam__5___closed__0 = _init_l_Lean_unresolveNameGlobal___redArg___lam__5___closed__0();
lean_mark_persistent(l_Lean_unresolveNameGlobal___redArg___lam__5___closed__0);
l_Lean_unresolveNameGlobalAvoidingLocals___redArg___lam__0___closed__0 = _init_l_Lean_unresolveNameGlobalAvoidingLocals___redArg___lam__0___closed__0();
lean_mark_persistent(l_Lean_unresolveNameGlobalAvoidingLocals___redArg___lam__0___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
