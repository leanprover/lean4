// Lean compiler output
// Module: Lean.ResolveName
// Imports: public import Lean.Modifiers public import Lean.Exception public import Lean.Namespace public import Lean.Log
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
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_noption_get(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_MacroScopesView_review(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_List_filterTR_loop___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwUnknownConstantAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_getPrefix(lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Expr_dbgToString___boxed(lean_object*);
lean_object* l_Lean_Syntax_formatStx(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_List_toString___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_throwErrorAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
lean_object* l_Lean_extractMacroScopes(lean_object*);
uint8_t l_Lean_LocalDecl_isAuxDecl(lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_MacroScopesView_isSuffixOf(lean_object*, lean_object*);
lean_object* l_Lean_privateToUserName_x3f(lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_findSomeRevM_x3f___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
uint8_t l_Lean_Name_isAtomic(lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg(lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_SMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
uint8_t l_Lean_isProtected(lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_Environment_containsOnBranch(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_registerEnvExtension___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_instInhabited(lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_mkPrivateNameCore(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_replacePrefix(lean_object*, lean_object*, lean_object*);
lean_object* l_List_eraseDupsBy___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_rootNamespace;
lean_object* l_List_find_x3f___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_KVMap_instValueBool;
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_logWarning___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Option_getM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
uint8_t l_Lean_Environment_isNamespace(lean_object*, lean_object*);
uint8_t l_Lean_initializing();
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_OptionT_instAlternative___redArg(lean_object*);
lean_object* l_OptionT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_OptionT_instMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_OptionT_instMonad___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_OptionT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_OptionT_instMonad___redArg___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_OptionT_pure(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_OptionT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_privateToUserName(lean_object*);
lean_object* l_Lean_Name_componentsRev(lean_object*);
lean_object* l_Lean_Name_appendCore(lean_object*, lean_object*);
lean_object* l_OptionT_lift(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instMonadEnvOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_OptionT_lift___redArg___lam__0(lean_object*, lean_object*);
lean_object* l_Lean_instMonadLogOfMonadLift___redArg(lean_object*, lean_object*);
lean_object* l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_List_forIn_x27_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_firstM_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Name_instToString___lam__0(lean_object*);
lean_object* l_List_filterMapTR_go___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Option_isNone___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwReservedNameNotAvailable___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "failed to declare `"};
static const lean_object* l_Lean_throwReservedNameNotAvailable___redArg___closed__0 = (const lean_object*)&l_Lean_throwReservedNameNotAvailable___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwReservedNameNotAvailable___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwReservedNameNotAvailable___redArg___closed__1;
static const lean_string_object l_Lean_throwReservedNameNotAvailable___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "` because `"};
static const lean_object* l_Lean_throwReservedNameNotAvailable___redArg___closed__2 = (const lean_object*)&l_Lean_throwReservedNameNotAvailable___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwReservedNameNotAvailable___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwReservedNameNotAvailable___redArg___closed__3;
static const lean_string_object l_Lean_throwReservedNameNotAvailable___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "` has already been declared"};
static const lean_object* l_Lean_throwReservedNameNotAvailable___redArg___closed__4 = (const lean_object*)&l_Lean_throwReservedNameNotAvailable___redArg___closed__4_value;
static lean_once_cell_t l_Lean_throwReservedNameNotAvailable___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwReservedNameNotAvailable___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwReservedNameNotAvailable___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwReservedNameNotAvailable(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ensureReservedNameAvailable___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ensureReservedNameAvailable___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ensureReservedNameAvailable(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_ResolveName_0__Lean_initFn___closed__0_00___x40_Lean_ResolveName_2351709485____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_ResolveName_0__Lean_initFn___closed__0_00___x40_Lean_ResolveName_2351709485____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ResolveName_0__Lean_initFn___closed__0_00___x40_Lean_ResolveName_2351709485____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_2351709485____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_2351709485____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_reservedNamePredicatesRef;
static const lean_string_object l_Lean_registerReservedNamePredicate___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 110, .m_capacity = 110, .m_length = 109, .m_data = "failed to register reserved name suffix predicate, this operation can only be performed during initialization"};
static const lean_object* l_Lean_registerReservedNamePredicate___closed__0 = (const lean_object*)&l_Lean_registerReservedNamePredicate___closed__0_value;
static lean_once_cell_t l_Lean_registerReservedNamePredicate___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_registerReservedNamePredicate___closed__1;
LEAN_EXPORT lean_object* l_Lean_registerReservedNamePredicate(lean_object*);
LEAN_EXPORT lean_object* l_Lean_registerReservedNamePredicate___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn___lam__0_00___x40_Lean_ResolveName_405991711____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn___lam__0_00___x40_Lean_ResolveName_405991711____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_ResolveName_0__Lean_initFn___closed__0_00___x40_Lean_ResolveName_405991711____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ResolveName_0__Lean_initFn___closed__0_00___x40_Lean_ResolveName_405991711____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_405991711____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_405991711____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_reservedNamePredicatesExt;
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_isReservedName_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_isReservedName_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_isReservedName___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_isReservedName___closed__0;
LEAN_EXPORT uint8_t lean_is_reserved_name(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isReservedName___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8_spec__11_spec__13___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8_spec__11___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8_spec__12___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__5_spec__10_spec__15___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__5_spec__10_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__5_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__5_spec__10___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__5___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__5___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_addAliasEntry_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_addAliasEntry_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addAliasEntry(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__5_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__5_spec__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8_spec__11(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8_spec__12(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__5_spec__10_spec__15(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__5_spec__10_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8_spec__11_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn___lam__0_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__4_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__4_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__5_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__5_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn___lam__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn___lam__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2____boxed(lean_object*);
static const lean_closure_object l___private_Lean_ResolveName_0__Lean_initFn___closed__0_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_ResolveName_0__Lean_initFn___lam__0_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ResolveName_0__Lean_initFn___closed__0_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ResolveName_0__Lean_initFn___closed__0_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_ResolveName_0__Lean_initFn___closed__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_ResolveName_0__Lean_initFn___lam__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ResolveName_0__Lean_initFn___closed__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ResolveName_0__Lean_initFn___closed__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_ResolveName_0__Lean_initFn___closed__2_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_ResolveName_0__Lean_initFn___closed__2_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ResolveName_0__Lean_initFn___closed__2_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_ResolveName_0__Lean_initFn___closed__3_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "aliasExtension"};
static const lean_object* l___private_Lean_ResolveName_0__Lean_initFn___closed__3_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ResolveName_0__Lean_initFn___closed__3_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ResolveName_0__Lean_initFn___closed__4_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ResolveName_0__Lean_initFn___closed__2_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_ResolveName_0__Lean_initFn___closed__4_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ResolveName_0__Lean_initFn___closed__4_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_ResolveName_0__Lean_initFn___closed__3_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(255, 78, 120, 122, 20, 252, 110, 252)}};
static const lean_object* l___private_Lean_ResolveName_0__Lean_initFn___closed__4_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ResolveName_0__Lean_initFn___closed__4_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_ResolveName_0__Lean_initFn___closed__5_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_addAliasEntry, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ResolveName_0__Lean_initFn___closed__5_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ResolveName_0__Lean_initFn___closed__5_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ResolveName_0__Lean_initFn___closed__6_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 0, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_ResolveName_0__Lean_initFn___closed__4_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ResolveName_0__Lean_initFn___closed__5_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ResolveName_0__Lean_initFn___closed__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ResolveName_0__Lean_initFn___closed__0_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_ResolveName_0__Lean_initFn___closed__6_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ResolveName_0__Lean_initFn___closed__6_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_aliasExtension;
LEAN_EXPORT lean_object* l_Lean_addAlias(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_getAliasState___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_getAliasState___closed__0 = (const lean_object*)&l_Lean_getAliasState___closed__0_value;
static const lean_closure_object l_Lean_getAliasState___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_getAliasState___closed__1 = (const lean_object*)&l_Lean_getAliasState___closed__1_value;
static lean_once_cell_t l_Lean_getAliasState___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getAliasState___closed__2;
LEAN_EXPORT lean_object* l_Lean_getAliasState(lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_getAliases_spec__0(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_getAliases_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getAliases(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_getAliases___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getRevAliases___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getRevAliases___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__3_spec__4_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__3_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getRevAliases(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__3_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__3_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__3_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__3_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__0_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "backward"};
static const lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__0_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__0_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__1_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "privateInPublic"};
static const lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__1_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__1_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__2_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__0_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(77, 196, 98, 49, 58, 220, 29, 220)}};
static const lean_ctor_object l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__2_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__2_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__1_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(200, 137, 140, 74, 72, 128, 49, 11)}};
static const lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__2_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__2_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__3_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 227, .m_capacity = 227, .m_length = 226, .m_data = "(module system) Export `private` declarations, allowing for arbitrary access to them while code is being ported to the module system. Such accesses will generate warnings\n    unless `backward.privateInPublic.warn` is disabled."};
static const lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__3_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__3_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__4_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__3_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__4_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__4_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__5_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "ResolveName"};
static const lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__5_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__5_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__6_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ResolveName_0__Lean_initFn___closed__2_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__6_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__6_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__5_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(213, 127, 67, 6, 186, 49, 191, 64)}};
static const lean_ctor_object l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__6_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__6_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__0_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(131, 161, 136, 183, 131, 203, 158, 84)}};
static const lean_ctor_object l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__6_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__6_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__1_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(94, 154, 217, 244, 61, 155, 3, 144)}};
static const lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__6_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__6_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ResolveName_backward_privateInPublic;
static const lean_string_object l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__0_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "warn"};
static const lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__0_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__0_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__1_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__0_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(77, 196, 98, 49, 58, 220, 29, 220)}};
static const lean_ctor_object l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__1_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__1_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__1_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(200, 137, 140, 74, 72, 128, 49, 11)}};
static const lean_ctor_object l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__1_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__1_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__0_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(44, 52, 68, 203, 224, 27, 156, 169)}};
static const lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__1_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__1_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__2_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 126, .m_capacity = 126, .m_length = 125, .m_data = "(module system) Warn on accesses to `private` declarations that are allowed only by `backward.privateInPublic` being enabled."};
static const lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__2_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__2_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__3_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__2_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__3_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__3_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__4_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ResolveName_0__Lean_initFn___closed__2_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__4_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__4_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__5_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(213, 127, 67, 6, 186, 49, 191, 64)}};
static const lean_ctor_object l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__4_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__4_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__0_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(131, 161, 136, 183, 131, 203, 158, 84)}};
static const lean_ctor_object l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__4_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__4_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__1_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(94, 154, 217, 244, 61, 155, 3, 144)}};
static const lean_ctor_object l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__4_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__4_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4__value_aux_3),((lean_object*)&l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__0_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(50, 1, 203, 3, 164, 240, 100, 244)}};
static const lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__4_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__4_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ResolveName_backward_privateInPublic_warn;
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__1___boxed(lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveQualifiedName(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveQualifiedName___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveUsingNamespace(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveUsingNamespace___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveExact(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveExact___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveOpenDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveOpenDecls___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_List_eraseDups___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_List_eraseDups___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__0___closed__0 = (const lean_object*)&l_List_eraseDups___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_List_eraseDups___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ResolveName_resolveGlobalName___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_ResolveName_resolveNamespaceUsingScope_x3f_spec__0(lean_object*);
static const lean_string_object l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Lean.ResolveName"};
static const lean_object* l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__0 = (const lean_object*)&l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__0_value;
static const lean_string_object l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "Lean.ResolveName.resolveNamespaceUsingScope\?"};
static const lean_object* l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__1 = (const lean_object*)&l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__1_value;
static const lean_string_object l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__2 = (const lean_object*)&l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__2_value;
static lean_once_cell_t l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__3;
LEAN_EXPORT lean_object* l_Lean_ResolveName_resolveNamespaceUsingScope_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ResolveName_resolveNamespaceUsingOpenDecls(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ResolveName_resolveNamespace(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadResolveNameOfMonadLift___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadResolveNameOfMonadLift(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_checkPrivateInPublic___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Private declaration `"};
static const lean_object* l_Lean_checkPrivateInPublic___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_checkPrivateInPublic___redArg___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_checkPrivateInPublic___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_checkPrivateInPublic___redArg___lam__0___closed__1;
static const lean_string_object l_Lean_checkPrivateInPublic___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 167, .m_capacity = 167, .m_length = 166, .m_data = "` accessed publicly; this is allowed only because the `backward.privateInPublic` option is enabled. \n\nDisable `backward.privateInPublic.warn` to silence this warning."};
static const lean_object* l_Lean_checkPrivateInPublic___redArg___lam__0___closed__2 = (const lean_object*)&l_Lean_checkPrivateInPublic___redArg___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_checkPrivateInPublic___redArg___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_checkPrivateInPublic___redArg___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg___lam__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_resolveGlobalName___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__6(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_resolveGlobalName___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_resolveGlobalName___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_resolveGlobalName___redArg___closed__0 = (const lean_object*)&l_Lean_resolveGlobalName___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_resolveNamespaceCore___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "unknown namespace `"};
static const lean_object* l_Lean_resolveNamespaceCore___redArg___lam__1___closed__0 = (const lean_object*)&l_Lean_resolveNamespaceCore___redArg___lam__1___closed__0_value;
static const lean_string_object l_Lean_resolveNamespaceCore___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_resolveNamespaceCore___redArg___lam__1___closed__1 = (const lean_object*)&l_Lean_resolveNamespaceCore___redArg___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveNamespace___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveNamespace___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveNamespace___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_resolveNamespace___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_resolveNamespace___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_resolveNamespace___redArg___closed__0 = (const lean_object*)&l_Lean_resolveNamespace___redArg___closed__0_value;
static const lean_array_object l_Lean_resolveNamespace___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_resolveNamespace___redArg___closed__1 = (const lean_object*)&l_Lean_resolveNamespace___redArg___closed__1_value;
static const lean_string_object l_Lean_resolveNamespace___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "expected identifier"};
static const lean_object* l_Lean_resolveNamespace___redArg___closed__2 = (const lean_object*)&l_Lean_resolveNamespace___redArg___closed__2_value;
static const lean_ctor_object l_Lean_resolveNamespace___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_resolveNamespace___redArg___closed__2_value)}};
static const lean_object* l_Lean_resolveNamespace___redArg___closed__3 = (const lean_object*)&l_Lean_resolveNamespace___redArg___closed__3_value;
static lean_once_cell_t l_Lean_resolveNamespace___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_resolveNamespace___redArg___closed__4;
LEAN_EXPORT lean_object* l_Lean_resolveNamespace___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveNamespace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_resolveUniqueNamespace___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "ambiguous namespace `"};
static const lean_object* l_Lean_resolveUniqueNamespace___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_resolveUniqueNamespace___redArg___lam__0___closed__0_value;
static const lean_string_object l_Lean_resolveUniqueNamespace___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "`, possible interpretations: `"};
static const lean_object* l_Lean_resolveUniqueNamespace___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_resolveUniqueNamespace___redArg___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_resolveUniqueNamespace___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveUniqueNamespace___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_resolveUniqueNamespace___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_instToString___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_resolveUniqueNamespace___redArg___closed__0 = (const lean_object*)&l_Lean_resolveUniqueNamespace___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_resolveUniqueNamespace___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveUniqueNamespace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_filterFieldList___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg___lam__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_filterFieldList___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_filterFieldList___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_filterFieldList___redArg___closed__0 = (const lean_object*)&l_Lean_filterFieldList___redArg___closed__0_value;
static const lean_closure_object l_Lean_filterFieldList___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_filterFieldList___redArg___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_filterFieldList___redArg___closed__1 = (const lean_object*)&l_Lean_filterFieldList___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_filterFieldList(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ensureNoOverload___redArg___lam__0(lean_object*);
static const lean_closure_object l_Lean_ensureNoOverload___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_ensureNoOverload___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ensureNoOverload___redArg___closed__0 = (const lean_object*)&l_Lean_ensureNoOverload___redArg___closed__0_value;
static const lean_string_object l_Lean_ensureNoOverload___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Ambiguous identifier `"};
static const lean_object* l_Lean_ensureNoOverload___redArg___closed__1 = (const lean_object*)&l_Lean_ensureNoOverload___redArg___closed__1_value;
static lean_once_cell_t l_Lean_ensureNoOverload___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ensureNoOverload___redArg___closed__2;
static const lean_string_object l_Lean_ensureNoOverload___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "`; possible interpretations: "};
static const lean_object* l_Lean_ensureNoOverload___redArg___closed__3 = (const lean_object*)&l_Lean_ensureNoOverload___redArg___closed__3_value;
static lean_once_cell_t l_Lean_ensureNoOverload___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ensureNoOverload___redArg___closed__4;
static const lean_closure_object l_Lean_ensureNoOverload___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_MessageData_ofExpr, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ensureNoOverload___redArg___closed__5 = (const lean_object*)&l_Lean_ensureNoOverload___redArg___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_ensureNoOverload___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ensureNoOverload(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverloadCore___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverloadCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverloadCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_preprocessSyntaxAndResolve___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_preprocessSyntaxAndResolve___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_preprocessSyntaxAndResolve___redArg___closed__0 = (const lean_object*)&l_Lean_preprocessSyntaxAndResolve___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_ensureNonAmbiguous___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Lean.ensureNonAmbiguous"};
static const lean_object* l_Lean_ensureNonAmbiguous___redArg___closed__0 = (const lean_object*)&l_Lean_ensureNonAmbiguous___redArg___closed__0_value;
static lean_once_cell_t l_Lean_ensureNonAmbiguous___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ensureNonAmbiguous___redArg___closed__1;
static const lean_closure_object l_Lean_ensureNonAmbiguous___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Expr_dbgToString___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ensureNonAmbiguous___redArg___closed__2 = (const lean_object*)&l_Lean_ensureNonAmbiguous___redArg___closed__2_value;
static const lean_string_object l_Lean_ensureNonAmbiguous___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "ambiguous identifier `"};
static const lean_object* l_Lean_ensureNonAmbiguous___redArg___closed__3 = (const lean_object*)&l_Lean_ensureNonAmbiguous___redArg___closed__3_value;
static const lean_string_object l_Lean_ensureNonAmbiguous___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "`, possible interpretations: "};
static const lean_object* l_Lean_ensureNonAmbiguous___redArg___closed__4 = (const lean_object*)&l_Lean_ensureNonAmbiguous___redArg___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_ensureNonAmbiguous___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ensureNonAmbiguous(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverload___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverload___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverload(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__0(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_go(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_resolveLocalName___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_resolveLocalName___redArg___lam__3___closed__0 = (const lean_object*)&l_Lean_resolveLocalName___redArg___lam__3___closed__0_value;
static const lean_closure_object l_Lean_resolveLocalName___redArg___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_resolveLocalName___redArg___lam__3___closed__1 = (const lean_object*)&l_Lean_resolveLocalName___redArg___lam__3___closed__1_value;
static const lean_closure_object l_Lean_resolveLocalName___redArg___lam__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_resolveLocalName___redArg___lam__3___closed__2 = (const lean_object*)&l_Lean_resolveLocalName___redArg___lam__3___closed__2_value;
static const lean_closure_object l_Lean_resolveLocalName___redArg___lam__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_resolveLocalName___redArg___lam__3___closed__3 = (const lean_object*)&l_Lean_resolveLocalName___redArg___lam__3___closed__3_value;
static const lean_closure_object l_Lean_resolveLocalName___redArg___lam__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_resolveLocalName___redArg___lam__3___closed__4 = (const lean_object*)&l_Lean_resolveLocalName___redArg___lam__3___closed__4_value;
static const lean_closure_object l_Lean_resolveLocalName___redArg___lam__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_resolveLocalName___redArg___lam__3___closed__5 = (const lean_object*)&l_Lean_resolveLocalName___redArg___lam__3___closed__5_value;
static const lean_closure_object l_Lean_resolveLocalName___redArg___lam__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_resolveLocalName___redArg___lam__3___closed__6 = (const lean_object*)&l_Lean_resolveLocalName___redArg___lam__3___closed__6_value;
static const lean_ctor_object l_Lean_resolveLocalName___redArg___lam__3___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_resolveLocalName___redArg___lam__3___closed__0_value),((lean_object*)&l_Lean_resolveLocalName___redArg___lam__3___closed__1_value)}};
static const lean_object* l_Lean_resolveLocalName___redArg___lam__3___closed__7 = (const lean_object*)&l_Lean_resolveLocalName___redArg___lam__3___closed__7_value;
static const lean_ctor_object l_Lean_resolveLocalName___redArg___lam__3___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_resolveLocalName___redArg___lam__3___closed__7_value),((lean_object*)&l_Lean_resolveLocalName___redArg___lam__3___closed__2_value),((lean_object*)&l_Lean_resolveLocalName___redArg___lam__3___closed__3_value),((lean_object*)&l_Lean_resolveLocalName___redArg___lam__3___closed__4_value),((lean_object*)&l_Lean_resolveLocalName___redArg___lam__3___closed__5_value)}};
static const lean_object* l_Lean_resolveLocalName___redArg___lam__3___closed__8 = (const lean_object*)&l_Lean_resolveLocalName___redArg___lam__3___closed__8_value;
static const lean_ctor_object l_Lean_resolveLocalName___redArg___lam__3___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_resolveLocalName___redArg___lam__3___closed__8_value),((lean_object*)&l_Lean_resolveLocalName___redArg___lam__3___closed__6_value)}};
static const lean_object* l_Lean_resolveLocalName___redArg___lam__3___closed__9 = (const lean_object*)&l_Lean_resolveLocalName___redArg___lam__3___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_resolveLocalName___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_resolveLocalName___redArg___closed__0 = (const lean_object*)&l_Lean_resolveLocalName___redArg___closed__0_value;
static const lean_closure_object l_Lean_resolveLocalName___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_resolveLocalName___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_resolveLocalName___redArg___closed__1 = (const lean_object*)&l_Lean_resolveLocalName___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveLocalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__0(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__1(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2___closed__0 = (const lean_object*)&l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__0___closed__0 = (const lean_object*)&l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__0___closed__0_value;
static const lean_ctor_object l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__0___closed__0_value)}};
static const lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__0___closed__1 = (const lean_object*)&l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__4___boxed(lean_object**);
static const lean_ctor_object l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__5___closed__0 = (const lean_object*)&l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__5___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Option_isNone___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_throwReservedNameNotAvailable___redArg___closed__1(void){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = ((lean_object*)(l_Lean_throwReservedNameNotAvailable___redArg___closed__0));
v___x_3_ = l_Lean_stringToMessageData(v___x_2_);
return v___x_3_;
}
}
static lean_object* _init_l_Lean_throwReservedNameNotAvailable___redArg___closed__3(void){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = ((lean_object*)(l_Lean_throwReservedNameNotAvailable___redArg___closed__2));
v___x_6_ = l_Lean_stringToMessageData(v___x_5_);
return v___x_6_;
}
}
static lean_object* _init_l_Lean_throwReservedNameNotAvailable___redArg___closed__5(void){
_start:
{
lean_object* v___x_8_; lean_object* v___x_9_; 
v___x_8_ = ((lean_object*)(l_Lean_throwReservedNameNotAvailable___redArg___closed__4));
v___x_9_ = l_Lean_stringToMessageData(v___x_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwReservedNameNotAvailable___redArg(lean_object* v_inst_10_, lean_object* v_inst_11_, lean_object* v_declName_12_, lean_object* v_reservedName_13_){
_start:
{
lean_object* v___x_14_; uint8_t v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; uint8_t v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; 
v___x_14_ = lean_obj_once(&l_Lean_throwReservedNameNotAvailable___redArg___closed__1, &l_Lean_throwReservedNameNotAvailable___redArg___closed__1_once, _init_l_Lean_throwReservedNameNotAvailable___redArg___closed__1);
v___x_15_ = 0;
v___x_16_ = l_Lean_MessageData_ofConstName(v_declName_12_, v___x_15_);
v___x_17_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_17_, 0, v___x_14_);
lean_ctor_set(v___x_17_, 1, v___x_16_);
v___x_18_ = lean_obj_once(&l_Lean_throwReservedNameNotAvailable___redArg___closed__3, &l_Lean_throwReservedNameNotAvailable___redArg___closed__3_once, _init_l_Lean_throwReservedNameNotAvailable___redArg___closed__3);
v___x_19_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_19_, 0, v___x_17_);
lean_ctor_set(v___x_19_, 1, v___x_18_);
v___x_20_ = 1;
v___x_21_ = l_Lean_MessageData_ofConstName(v_reservedName_13_, v___x_20_);
v___x_22_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_22_, 0, v___x_19_);
lean_ctor_set(v___x_22_, 1, v___x_21_);
v___x_23_ = lean_obj_once(&l_Lean_throwReservedNameNotAvailable___redArg___closed__5, &l_Lean_throwReservedNameNotAvailable___redArg___closed__5_once, _init_l_Lean_throwReservedNameNotAvailable___redArg___closed__5);
v___x_24_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_24_, 0, v___x_22_);
lean_ctor_set(v___x_24_, 1, v___x_23_);
v___x_25_ = l_Lean_throwError___redArg(v_inst_10_, v_inst_11_, v___x_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwReservedNameNotAvailable(lean_object* v_m_26_, lean_object* v_inst_27_, lean_object* v_inst_28_, lean_object* v_declName_29_, lean_object* v_reservedName_30_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = l_Lean_throwReservedNameNotAvailable___redArg(v_inst_27_, v_inst_28_, v_declName_29_, v_reservedName_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureReservedNameAvailable___redArg___lam__0(lean_object* v_reservedName_32_, lean_object* v_toApplicative_33_, lean_object* v_inst_34_, lean_object* v_inst_35_, lean_object* v_declName_36_, lean_object* v_____do__lift_37_){
_start:
{
uint8_t v___x_38_; uint8_t v___x_39_; 
v___x_38_ = 1;
lean_inc(v_reservedName_32_);
v___x_39_ = l_Lean_Environment_contains(v_____do__lift_37_, v_reservedName_32_, v___x_38_);
if (v___x_39_ == 0)
{
lean_object* v_toPure_40_; lean_object* v___x_41_; lean_object* v___x_42_; 
lean_dec(v_declName_36_);
lean_dec_ref(v_inst_35_);
lean_dec_ref(v_inst_34_);
lean_dec(v_reservedName_32_);
v_toPure_40_ = lean_ctor_get(v_toApplicative_33_, 1);
lean_inc(v_toPure_40_);
lean_dec_ref(v_toApplicative_33_);
v___x_41_ = lean_box(0);
v___x_42_ = lean_apply_2(v_toPure_40_, lean_box(0), v___x_41_);
return v___x_42_;
}
else
{
lean_object* v___x_43_; 
lean_dec_ref(v_toApplicative_33_);
v___x_43_ = l_Lean_throwReservedNameNotAvailable___redArg(v_inst_34_, v_inst_35_, v_declName_36_, v_reservedName_32_);
return v___x_43_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureReservedNameAvailable___redArg(lean_object* v_inst_44_, lean_object* v_inst_45_, lean_object* v_inst_46_, lean_object* v_declName_47_, lean_object* v_suffix_48_){
_start:
{
lean_object* v_toApplicative_49_; lean_object* v_toBind_50_; lean_object* v_getEnv_51_; lean_object* v_reservedName_52_; lean_object* v___f_53_; lean_object* v___x_54_; 
v_toApplicative_49_ = lean_ctor_get(v_inst_44_, 0);
lean_inc_ref(v_toApplicative_49_);
v_toBind_50_ = lean_ctor_get(v_inst_44_, 1);
lean_inc(v_toBind_50_);
v_getEnv_51_ = lean_ctor_get(v_inst_45_, 0);
lean_inc(v_getEnv_51_);
lean_dec_ref(v_inst_45_);
lean_inc(v_declName_47_);
v_reservedName_52_ = l_Lean_Name_str___override(v_declName_47_, v_suffix_48_);
v___f_53_ = lean_alloc_closure((void*)(l_Lean_ensureReservedNameAvailable___redArg___lam__0), 6, 5);
lean_closure_set(v___f_53_, 0, v_reservedName_52_);
lean_closure_set(v___f_53_, 1, v_toApplicative_49_);
lean_closure_set(v___f_53_, 2, v_inst_44_);
lean_closure_set(v___f_53_, 3, v_inst_46_);
lean_closure_set(v___f_53_, 4, v_declName_47_);
v___x_54_ = lean_apply_4(v_toBind_50_, lean_box(0), lean_box(0), v_getEnv_51_, v___f_53_);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureReservedNameAvailable(lean_object* v_m_55_, lean_object* v_inst_56_, lean_object* v_inst_57_, lean_object* v_inst_58_, lean_object* v_declName_59_, lean_object* v_suffix_60_){
_start:
{
lean_object* v___x_61_; 
v___x_61_ = l_Lean_ensureReservedNameAvailable___redArg(v_inst_56_, v_inst_57_, v_inst_58_, v_declName_59_, v_suffix_60_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_2351709485____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_65_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_initFn___closed__0_00___x40_Lean_ResolveName_2351709485____hygCtx___hyg_2_));
v___x_66_ = lean_st_mk_ref(v___x_65_);
v___x_67_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_67_, 0, v___x_66_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_2351709485____hygCtx___hyg_2____boxed(lean_object* v_a_68_){
_start:
{
lean_object* v_res_69_; 
v_res_69_ = l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_2351709485____hygCtx___hyg_2_();
return v_res_69_;
}
}
static lean_object* _init_l_Lean_registerReservedNamePredicate___closed__1(void){
_start:
{
lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_71_ = ((lean_object*)(l_Lean_registerReservedNamePredicate___closed__0));
v___x_72_ = lean_mk_io_user_error(v___x_71_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l_Lean_registerReservedNamePredicate(lean_object* v_p_73_){
_start:
{
uint8_t v___x_75_; 
v___x_75_ = l_Lean_initializing();
if (v___x_75_ == 0)
{
lean_object* v___x_76_; lean_object* v___x_77_; 
lean_dec_ref(v_p_73_);
v___x_76_ = lean_obj_once(&l_Lean_registerReservedNamePredicate___closed__1, &l_Lean_registerReservedNamePredicate___closed__1_once, _init_l_Lean_registerReservedNamePredicate___closed__1);
v___x_77_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_77_, 0, v___x_76_);
return v___x_77_;
}
else
{
lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_78_ = l_Lean_reservedNamePredicatesRef;
v___x_79_ = lean_st_ref_take(v___x_78_);
v___x_80_ = lean_array_push(v___x_79_, v_p_73_);
v___x_81_ = lean_st_ref_put(v___x_78_, v___x_80_);
v___x_82_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_82_, 0, v___x_81_);
return v___x_82_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerReservedNamePredicate___boxed(lean_object* v_p_83_, lean_object* v_a_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = l_Lean_registerReservedNamePredicate(v_p_83_);
return v_res_85_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn___lam__0_00___x40_Lean_ResolveName_405991711____hygCtx___hyg_2_(lean_object* v___x_86_){
_start:
{
lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_88_ = lean_st_ref_get(v___x_86_);
v___x_89_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_89_, 0, v___x_88_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn___lam__0_00___x40_Lean_ResolveName_405991711____hygCtx___hyg_2____boxed(lean_object* v___x_90_, lean_object* v___y_91_){
_start:
{
lean_object* v_res_92_; 
v_res_92_ = l___private_Lean_ResolveName_0__Lean_initFn___lam__0_00___x40_Lean_ResolveName_405991711____hygCtx___hyg_2_(v___x_90_);
lean_dec(v___x_90_);
return v_res_92_;
}
}
static lean_object* _init_l___private_Lean_ResolveName_0__Lean_initFn___closed__0_00___x40_Lean_ResolveName_405991711____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_93_; lean_object* v___f_94_; 
v___x_93_ = l_Lean_reservedNamePredicatesRef;
v___f_94_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_initFn___lam__0_00___x40_Lean_ResolveName_405991711____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_94_, 0, v___x_93_);
return v___f_94_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_405991711____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
v___f_96_ = lean_obj_once(&l___private_Lean_ResolveName_0__Lean_initFn___closed__0_00___x40_Lean_ResolveName_405991711____hygCtx___hyg_2_, &l___private_Lean_ResolveName_0__Lean_initFn___closed__0_00___x40_Lean_ResolveName_405991711____hygCtx___hyg_2__once, _init_l___private_Lean_ResolveName_0__Lean_initFn___closed__0_00___x40_Lean_ResolveName_405991711____hygCtx___hyg_2_);
v___x_97_ = lean_box(0);
v___x_98_ = lean_box(2);
v___x_99_ = l_Lean_registerEnvExtension___redArg(v___f_96_, v___x_97_, v___x_98_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_405991711____hygCtx___hyg_2____boxed(lean_object* v_a_100_){
_start:
{
lean_object* v_res_101_; 
v_res_101_ = l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_405991711____hygCtx___hyg_2_();
return v_res_101_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_isReservedName_spec__0(lean_object* v_env_102_, lean_object* v_name_103_, lean_object* v_as_104_, size_t v_i_105_, size_t v_stop_106_){
_start:
{
uint8_t v___x_107_; 
v___x_107_ = lean_usize_dec_eq(v_i_105_, v_stop_106_);
if (v___x_107_ == 0)
{
lean_object* v___x_161__overap_108_; lean_object* v___x_109_; uint8_t v___x_110_; 
v___x_161__overap_108_ = lean_array_uget_borrowed(v_as_104_, v_i_105_);
lean_inc(v___x_161__overap_108_);
lean_inc(v_name_103_);
lean_inc_ref(v_env_102_);
v___x_109_ = lean_apply_2(v___x_161__overap_108_, v_env_102_, v_name_103_);
v___x_110_ = lean_unbox(v___x_109_);
if (v___x_110_ == 0)
{
size_t v___x_111_; size_t v___x_112_; 
v___x_111_ = ((size_t)1ULL);
v___x_112_ = lean_usize_add(v_i_105_, v___x_111_);
v_i_105_ = v___x_112_;
goto _start;
}
else
{
uint8_t v___x_114_; 
lean_dec(v_name_103_);
lean_dec_ref(v_env_102_);
v___x_114_ = lean_unbox(v___x_109_);
return v___x_114_;
}
}
else
{
uint8_t v___x_115_; 
lean_dec(v_name_103_);
lean_dec_ref(v_env_102_);
v___x_115_ = 0;
return v___x_115_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_isReservedName_spec__0___boxed(lean_object* v_env_116_, lean_object* v_name_117_, lean_object* v_as_118_, lean_object* v_i_119_, lean_object* v_stop_120_){
_start:
{
size_t v_i_boxed_121_; size_t v_stop_boxed_122_; uint8_t v_res_123_; lean_object* v_r_124_; 
v_i_boxed_121_ = lean_unbox_usize(v_i_119_);
lean_dec(v_i_119_);
v_stop_boxed_122_ = lean_unbox_usize(v_stop_120_);
lean_dec(v_stop_120_);
v_res_123_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_isReservedName_spec__0(v_env_116_, v_name_117_, v_as_118_, v_i_boxed_121_, v_stop_boxed_122_);
lean_dec_ref(v_as_118_);
v_r_124_ = lean_box(v_res_123_);
return v_r_124_;
}
}
static lean_object* _init_l_Lean_isReservedName___closed__0(void){
_start:
{
lean_object* v___x_125_; 
v___x_125_ = l_Array_instInhabited(lean_box(0));
return v___x_125_;
}
}
LEAN_EXPORT uint8_t lean_is_reserved_name(lean_object* v_env_126_, lean_object* v_name_127_){
_start:
{
lean_object* v___x_128_; lean_object* v_asyncMode_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; uint8_t v___x_135_; 
v___x_128_ = l_Lean_reservedNamePredicatesExt;
v_asyncMode_129_ = lean_ctor_get(v___x_128_, 2);
v___x_130_ = lean_obj_once(&l_Lean_isReservedName___closed__0, &l_Lean_isReservedName___closed__0_once, _init_l_Lean_isReservedName___closed__0);
v___x_131_ = lean_box(0);
lean_inc_ref(v_env_126_);
v___x_132_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_130_, v___x_128_, v_env_126_, v_asyncMode_129_, v___x_131_);
v___x_133_ = lean_unsigned_to_nat(0u);
v___x_134_ = lean_array_get_size(v___x_132_);
v___x_135_ = lean_nat_dec_lt(v___x_133_, v___x_134_);
if (v___x_135_ == 0)
{
lean_dec(v___x_132_);
lean_dec(v_name_127_);
lean_dec_ref(v_env_126_);
return v___x_135_;
}
else
{
if (v___x_135_ == 0)
{
lean_dec(v___x_132_);
lean_dec(v_name_127_);
lean_dec_ref(v_env_126_);
return v___x_135_;
}
else
{
size_t v___x_136_; size_t v___x_137_; uint8_t v___x_138_; 
v___x_136_ = ((size_t)0ULL);
v___x_137_ = lean_usize_of_nat(v___x_134_);
v___x_138_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_isReservedName_spec__0(v_env_126_, v_name_127_, v___x_132_, v___x_136_, v___x_137_);
lean_dec(v___x_132_);
return v___x_138_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isReservedName___boxed(lean_object* v_env_139_, lean_object* v_name_140_){
_start:
{
uint8_t v_res_141_; lean_object* v_r_142_; 
v_res_141_ = lean_is_reserved_name(v_env_139_, v_name_140_);
v_r_142_ = lean_box(v_res_141_);
return v_r_142_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8_spec__11_spec__13___redArg(lean_object* v_x_143_, lean_object* v_x_144_, lean_object* v_x_145_, lean_object* v_x_146_){
_start:
{
lean_object* v_ks_147_; lean_object* v_vs_148_; lean_object* v___x_150_; uint8_t v_isShared_151_; uint8_t v_isSharedCheck_172_; 
v_ks_147_ = lean_ctor_get(v_x_143_, 0);
v_vs_148_ = lean_ctor_get(v_x_143_, 1);
v_isSharedCheck_172_ = !lean_is_exclusive(v_x_143_);
if (v_isSharedCheck_172_ == 0)
{
v___x_150_ = v_x_143_;
v_isShared_151_ = v_isSharedCheck_172_;
goto v_resetjp_149_;
}
else
{
lean_inc(v_vs_148_);
lean_inc(v_ks_147_);
lean_dec(v_x_143_);
v___x_150_ = lean_box(0);
v_isShared_151_ = v_isSharedCheck_172_;
goto v_resetjp_149_;
}
v_resetjp_149_:
{
lean_object* v___x_152_; uint8_t v___x_153_; 
v___x_152_ = lean_array_get_size(v_ks_147_);
v___x_153_ = lean_nat_dec_lt(v_x_144_, v___x_152_);
if (v___x_153_ == 0)
{
lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_157_; 
lean_dec(v_x_144_);
v___x_154_ = lean_array_push(v_ks_147_, v_x_145_);
v___x_155_ = lean_array_push(v_vs_148_, v_x_146_);
if (v_isShared_151_ == 0)
{
lean_ctor_set(v___x_150_, 1, v___x_155_);
lean_ctor_set(v___x_150_, 0, v___x_154_);
v___x_157_ = v___x_150_;
goto v_reusejp_156_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v___x_154_);
lean_ctor_set(v_reuseFailAlloc_158_, 1, v___x_155_);
v___x_157_ = v_reuseFailAlloc_158_;
goto v_reusejp_156_;
}
v_reusejp_156_:
{
return v___x_157_;
}
}
else
{
lean_object* v_k_x27_159_; uint8_t v___x_160_; 
v_k_x27_159_ = lean_array_fget_borrowed(v_ks_147_, v_x_144_);
v___x_160_ = lean_name_eq(v_x_145_, v_k_x27_159_);
if (v___x_160_ == 0)
{
lean_object* v___x_162_; 
if (v_isShared_151_ == 0)
{
v___x_162_ = v___x_150_;
goto v_reusejp_161_;
}
else
{
lean_object* v_reuseFailAlloc_166_; 
v_reuseFailAlloc_166_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_166_, 0, v_ks_147_);
lean_ctor_set(v_reuseFailAlloc_166_, 1, v_vs_148_);
v___x_162_ = v_reuseFailAlloc_166_;
goto v_reusejp_161_;
}
v_reusejp_161_:
{
lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_163_ = lean_unsigned_to_nat(1u);
v___x_164_ = lean_nat_add(v_x_144_, v___x_163_);
lean_dec(v_x_144_);
v_x_143_ = v___x_162_;
v_x_144_ = v___x_164_;
goto _start;
}
}
else
{
lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_170_; 
v___x_167_ = lean_array_fset(v_ks_147_, v_x_144_, v_x_145_);
v___x_168_ = lean_array_fset(v_vs_148_, v_x_144_, v_x_146_);
lean_dec(v_x_144_);
if (v_isShared_151_ == 0)
{
lean_ctor_set(v___x_150_, 1, v___x_168_);
lean_ctor_set(v___x_150_, 0, v___x_167_);
v___x_170_ = v___x_150_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v___x_167_);
lean_ctor_set(v_reuseFailAlloc_171_, 1, v___x_168_);
v___x_170_ = v_reuseFailAlloc_171_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
return v___x_170_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8_spec__11___redArg(lean_object* v_n_173_, lean_object* v_k_174_, lean_object* v_v_175_){
_start:
{
lean_object* v___x_176_; lean_object* v___x_177_; 
v___x_176_ = lean_unsigned_to_nat(0u);
v___x_177_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8_spec__11_spec__13___redArg(v_n_173_, v___x_176_, v_k_174_, v_v_175_);
return v___x_177_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_178_; 
v___x_178_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8___redArg(lean_object* v_x_179_, size_t v_x_180_, size_t v_x_181_, lean_object* v_x_182_, lean_object* v_x_183_){
_start:
{
if (lean_obj_tag(v_x_179_) == 0)
{
lean_object* v_es_184_; size_t v___x_185_; size_t v___x_186_; lean_object* v_j_187_; lean_object* v___x_188_; uint8_t v___x_189_; 
v_es_184_ = lean_ctor_get(v_x_179_, 0);
v___x_185_ = ((size_t)31ULL);
v___x_186_ = lean_usize_land(v_x_180_, v___x_185_);
v_j_187_ = lean_usize_to_nat(v___x_186_);
v___x_188_ = lean_array_get_size(v_es_184_);
v___x_189_ = lean_nat_dec_lt(v_j_187_, v___x_188_);
if (v___x_189_ == 0)
{
lean_dec(v_j_187_);
lean_dec(v_x_183_);
lean_dec(v_x_182_);
return v_x_179_;
}
else
{
lean_object* v___x_191_; uint8_t v_isShared_192_; uint8_t v_isSharedCheck_228_; 
lean_inc_ref(v_es_184_);
v_isSharedCheck_228_ = !lean_is_exclusive(v_x_179_);
if (v_isSharedCheck_228_ == 0)
{
lean_object* v_unused_229_; 
v_unused_229_ = lean_ctor_get(v_x_179_, 0);
lean_dec(v_unused_229_);
v___x_191_ = v_x_179_;
v_isShared_192_ = v_isSharedCheck_228_;
goto v_resetjp_190_;
}
else
{
lean_dec(v_x_179_);
v___x_191_ = lean_box(0);
v_isShared_192_ = v_isSharedCheck_228_;
goto v_resetjp_190_;
}
v_resetjp_190_:
{
lean_object* v_v_193_; lean_object* v___x_194_; lean_object* v_xs_x27_195_; lean_object* v___y_197_; 
v_v_193_ = lean_array_fget(v_es_184_, v_j_187_);
v___x_194_ = lean_box(0);
v_xs_x27_195_ = lean_array_fset(v_es_184_, v_j_187_, v___x_194_);
switch(lean_obj_tag(v_v_193_))
{
case 0:
{
lean_object* v_key_202_; lean_object* v_val_203_; lean_object* v___x_205_; uint8_t v_isShared_206_; uint8_t v_isSharedCheck_213_; 
v_key_202_ = lean_ctor_get(v_v_193_, 0);
v_val_203_ = lean_ctor_get(v_v_193_, 1);
v_isSharedCheck_213_ = !lean_is_exclusive(v_v_193_);
if (v_isSharedCheck_213_ == 0)
{
v___x_205_ = v_v_193_;
v_isShared_206_ = v_isSharedCheck_213_;
goto v_resetjp_204_;
}
else
{
lean_inc(v_val_203_);
lean_inc(v_key_202_);
lean_dec(v_v_193_);
v___x_205_ = lean_box(0);
v_isShared_206_ = v_isSharedCheck_213_;
goto v_resetjp_204_;
}
v_resetjp_204_:
{
uint8_t v___x_207_; 
v___x_207_ = lean_name_eq(v_x_182_, v_key_202_);
if (v___x_207_ == 0)
{
lean_object* v___x_208_; lean_object* v___x_209_; 
lean_del_object(v___x_205_);
v___x_208_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_202_, v_val_203_, v_x_182_, v_x_183_);
v___x_209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_209_, 0, v___x_208_);
v___y_197_ = v___x_209_;
goto v___jp_196_;
}
else
{
lean_object* v___x_211_; 
lean_dec(v_val_203_);
lean_dec(v_key_202_);
if (v_isShared_206_ == 0)
{
lean_ctor_set(v___x_205_, 1, v_x_183_);
lean_ctor_set(v___x_205_, 0, v_x_182_);
v___x_211_ = v___x_205_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v_x_182_);
lean_ctor_set(v_reuseFailAlloc_212_, 1, v_x_183_);
v___x_211_ = v_reuseFailAlloc_212_;
goto v_reusejp_210_;
}
v_reusejp_210_:
{
v___y_197_ = v___x_211_;
goto v___jp_196_;
}
}
}
}
case 1:
{
lean_object* v_node_214_; lean_object* v___x_216_; uint8_t v_isShared_217_; uint8_t v_isSharedCheck_226_; 
v_node_214_ = lean_ctor_get(v_v_193_, 0);
v_isSharedCheck_226_ = !lean_is_exclusive(v_v_193_);
if (v_isSharedCheck_226_ == 0)
{
v___x_216_ = v_v_193_;
v_isShared_217_ = v_isSharedCheck_226_;
goto v_resetjp_215_;
}
else
{
lean_inc(v_node_214_);
lean_dec(v_v_193_);
v___x_216_ = lean_box(0);
v_isShared_217_ = v_isSharedCheck_226_;
goto v_resetjp_215_;
}
v_resetjp_215_:
{
size_t v___x_218_; size_t v___x_219_; size_t v___x_220_; size_t v___x_221_; lean_object* v___x_222_; lean_object* v___x_224_; 
v___x_218_ = ((size_t)5ULL);
v___x_219_ = lean_usize_shift_right(v_x_180_, v___x_218_);
v___x_220_ = ((size_t)1ULL);
v___x_221_ = lean_usize_add(v_x_181_, v___x_220_);
v___x_222_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8___redArg(v_node_214_, v___x_219_, v___x_221_, v_x_182_, v_x_183_);
if (v_isShared_217_ == 0)
{
lean_ctor_set(v___x_216_, 0, v___x_222_);
v___x_224_ = v___x_216_;
goto v_reusejp_223_;
}
else
{
lean_object* v_reuseFailAlloc_225_; 
v_reuseFailAlloc_225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_225_, 0, v___x_222_);
v___x_224_ = v_reuseFailAlloc_225_;
goto v_reusejp_223_;
}
v_reusejp_223_:
{
v___y_197_ = v___x_224_;
goto v___jp_196_;
}
}
}
default: 
{
lean_object* v___x_227_; 
v___x_227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_227_, 0, v_x_182_);
lean_ctor_set(v___x_227_, 1, v_x_183_);
v___y_197_ = v___x_227_;
goto v___jp_196_;
}
}
v___jp_196_:
{
lean_object* v___x_198_; lean_object* v___x_200_; 
v___x_198_ = lean_array_fset(v_xs_x27_195_, v_j_187_, v___y_197_);
lean_dec(v_j_187_);
if (v_isShared_192_ == 0)
{
lean_ctor_set(v___x_191_, 0, v___x_198_);
v___x_200_ = v___x_191_;
goto v_reusejp_199_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v___x_198_);
v___x_200_ = v_reuseFailAlloc_201_;
goto v_reusejp_199_;
}
v_reusejp_199_:
{
return v___x_200_;
}
}
}
}
}
else
{
lean_object* v_ks_230_; lean_object* v_vs_231_; lean_object* v___x_233_; uint8_t v_isShared_234_; uint8_t v_isSharedCheck_251_; 
v_ks_230_ = lean_ctor_get(v_x_179_, 0);
v_vs_231_ = lean_ctor_get(v_x_179_, 1);
v_isSharedCheck_251_ = !lean_is_exclusive(v_x_179_);
if (v_isSharedCheck_251_ == 0)
{
v___x_233_ = v_x_179_;
v_isShared_234_ = v_isSharedCheck_251_;
goto v_resetjp_232_;
}
else
{
lean_inc(v_vs_231_);
lean_inc(v_ks_230_);
lean_dec(v_x_179_);
v___x_233_ = lean_box(0);
v_isShared_234_ = v_isSharedCheck_251_;
goto v_resetjp_232_;
}
v_resetjp_232_:
{
lean_object* v___x_236_; 
if (v_isShared_234_ == 0)
{
v___x_236_ = v___x_233_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v_ks_230_);
lean_ctor_set(v_reuseFailAlloc_250_, 1, v_vs_231_);
v___x_236_ = v_reuseFailAlloc_250_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
lean_object* v_newNode_237_; uint8_t v___y_239_; size_t v___x_245_; uint8_t v___x_246_; 
v_newNode_237_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8_spec__11___redArg(v___x_236_, v_x_182_, v_x_183_);
v___x_245_ = ((size_t)7ULL);
v___x_246_ = lean_usize_dec_le(v___x_245_, v_x_181_);
if (v___x_246_ == 0)
{
lean_object* v___x_247_; lean_object* v___x_248_; uint8_t v___x_249_; 
v___x_247_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_237_);
v___x_248_ = lean_unsigned_to_nat(4u);
v___x_249_ = lean_nat_dec_lt(v___x_247_, v___x_248_);
lean_dec(v___x_247_);
v___y_239_ = v___x_249_;
goto v___jp_238_;
}
else
{
v___y_239_ = v___x_246_;
goto v___jp_238_;
}
v___jp_238_:
{
if (v___y_239_ == 0)
{
lean_object* v_ks_240_; lean_object* v_vs_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; 
v_ks_240_ = lean_ctor_get(v_newNode_237_, 0);
lean_inc_ref(v_ks_240_);
v_vs_241_ = lean_ctor_get(v_newNode_237_, 1);
lean_inc_ref(v_vs_241_);
lean_dec_ref(v_newNode_237_);
v___x_242_ = lean_unsigned_to_nat(0u);
v___x_243_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8___redArg___closed__0);
v___x_244_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8_spec__12___redArg(v_x_181_, v_ks_240_, v_vs_241_, v___x_242_, v___x_243_);
lean_dec_ref(v_vs_241_);
lean_dec_ref(v_ks_240_);
return v___x_244_;
}
else
{
return v_newNode_237_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8_spec__12___redArg(size_t v_depth_252_, lean_object* v_keys_253_, lean_object* v_vals_254_, lean_object* v_i_255_, lean_object* v_entries_256_){
_start:
{
lean_object* v___x_257_; uint8_t v___x_258_; 
v___x_257_ = lean_array_get_size(v_keys_253_);
v___x_258_ = lean_nat_dec_lt(v_i_255_, v___x_257_);
if (v___x_258_ == 0)
{
lean_dec(v_i_255_);
return v_entries_256_;
}
else
{
lean_object* v_k_259_; lean_object* v_v_260_; uint64_t v___y_262_; 
v_k_259_ = lean_array_fget_borrowed(v_keys_253_, v_i_255_);
v_v_260_ = lean_array_fget_borrowed(v_vals_254_, v_i_255_);
if (lean_obj_tag(v_k_259_) == 0)
{
uint64_t v___x_273_; 
v___x_273_ = 1723ULL;
v___y_262_ = v___x_273_;
goto v___jp_261_;
}
else
{
uint64_t v_hash_274_; 
v_hash_274_ = lean_ctor_get_uint64(v_k_259_, sizeof(void*)*2);
v___y_262_ = v_hash_274_;
goto v___jp_261_;
}
v___jp_261_:
{
size_t v_h_263_; size_t v___x_264_; lean_object* v___x_265_; size_t v___x_266_; size_t v___x_267_; size_t v___x_268_; size_t v_h_269_; lean_object* v___x_270_; lean_object* v___x_271_; 
v_h_263_ = lean_uint64_to_usize(v___y_262_);
v___x_264_ = ((size_t)5ULL);
v___x_265_ = lean_unsigned_to_nat(1u);
v___x_266_ = ((size_t)1ULL);
v___x_267_ = lean_usize_sub(v_depth_252_, v___x_266_);
v___x_268_ = lean_usize_mul(v___x_264_, v___x_267_);
v_h_269_ = lean_usize_shift_right(v_h_263_, v___x_268_);
v___x_270_ = lean_nat_add(v_i_255_, v___x_265_);
lean_dec(v_i_255_);
lean_inc(v_v_260_);
lean_inc(v_k_259_);
v___x_271_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8___redArg(v_entries_256_, v_h_269_, v_depth_252_, v_k_259_, v_v_260_);
v_i_255_ = v___x_270_;
v_entries_256_ = v___x_271_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8_spec__12___redArg___boxed(lean_object* v_depth_275_, lean_object* v_keys_276_, lean_object* v_vals_277_, lean_object* v_i_278_, lean_object* v_entries_279_){
_start:
{
size_t v_depth_boxed_280_; lean_object* v_res_281_; 
v_depth_boxed_280_ = lean_unbox_usize(v_depth_275_);
lean_dec(v_depth_275_);
v_res_281_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8_spec__12___redArg(v_depth_boxed_280_, v_keys_276_, v_vals_277_, v_i_278_, v_entries_279_);
lean_dec_ref(v_vals_277_);
lean_dec_ref(v_keys_276_);
return v_res_281_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8___redArg___boxed(lean_object* v_x_282_, lean_object* v_x_283_, lean_object* v_x_284_, lean_object* v_x_285_, lean_object* v_x_286_){
_start:
{
size_t v_x_1375__boxed_287_; size_t v_x_1376__boxed_288_; lean_object* v_res_289_; 
v_x_1375__boxed_287_ = lean_unbox_usize(v_x_283_);
lean_dec(v_x_283_);
v_x_1376__boxed_288_ = lean_unbox_usize(v_x_284_);
lean_dec(v_x_284_);
v_res_289_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8___redArg(v_x_282_, v_x_1375__boxed_287_, v_x_1376__boxed_288_, v_x_285_, v_x_286_);
return v_res_289_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4___redArg(lean_object* v_x_290_, lean_object* v_x_291_, lean_object* v_x_292_){
_start:
{
uint64_t v___y_294_; 
if (lean_obj_tag(v_x_291_) == 0)
{
uint64_t v___x_298_; 
v___x_298_ = 1723ULL;
v___y_294_ = v___x_298_;
goto v___jp_293_;
}
else
{
uint64_t v_hash_299_; 
v_hash_299_ = lean_ctor_get_uint64(v_x_291_, sizeof(void*)*2);
v___y_294_ = v_hash_299_;
goto v___jp_293_;
}
v___jp_293_:
{
size_t v___x_295_; size_t v___x_296_; lean_object* v___x_297_; 
v___x_295_ = lean_uint64_to_usize(v___y_294_);
v___x_296_ = ((size_t)1ULL);
v___x_297_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8___redArg(v_x_290_, v___x_295_, v___x_296_, v_x_291_, v_x_292_);
return v___x_297_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg(lean_object* v_m_300_, lean_object* v_query_301_, lean_object* v_x_302_, lean_object* v_x_303_, lean_object* v_x_304_){
_start:
{
lean_object* v_zero_305_; uint8_t v_isZero_306_; 
v_zero_305_ = lean_unsigned_to_nat(0u);
v_isZero_306_ = lean_nat_dec_eq(v_x_303_, v_zero_305_);
if (v_isZero_306_ == 1)
{
lean_dec(v_x_304_);
lean_dec(v_x_303_);
if (lean_obj_tag(v_x_302_) == 0)
{
lean_object* v___x_307_; 
v___x_307_ = lean_box(2);
return v___x_307_;
}
else
{
lean_object* v_val_308_; lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_315_; 
v_val_308_ = lean_ctor_get(v_x_302_, 0);
v_isSharedCheck_315_ = !lean_is_exclusive(v_x_302_);
if (v_isSharedCheck_315_ == 0)
{
v___x_310_ = v_x_302_;
v_isShared_311_ = v_isSharedCheck_315_;
goto v_resetjp_309_;
}
else
{
lean_inc(v_val_308_);
lean_dec(v_x_302_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_315_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
lean_object* v___x_313_; 
if (v_isShared_311_ == 0)
{
v___x_313_ = v___x_310_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v_val_308_);
v___x_313_ = v_reuseFailAlloc_314_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
return v___x_313_;
}
}
}
}
else
{
lean_object* v_keyArray_316_; lean_object* v_valueArray_317_; lean_object* v___x_318_; uint8_t v_isSome_319_; 
v_keyArray_316_ = lean_ctor_get(v_m_300_, 1);
v_valueArray_317_ = lean_ctor_get(v_m_300_, 2);
v___x_318_ = lean_array_fget_borrowed(v_keyArray_316_, v_x_304_);
v_isSome_319_ = lean_noption_is_some(v___x_318_);
if (v_isSome_319_ == 0)
{
lean_dec(v_x_303_);
if (lean_obj_tag(v_x_302_) == 0)
{
lean_object* v___x_320_; 
v___x_320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_320_, 0, v_x_304_);
return v___x_320_;
}
else
{
lean_object* v_val_321_; lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_328_; 
lean_dec(v_x_304_);
v_val_321_ = lean_ctor_get(v_x_302_, 0);
v_isSharedCheck_328_ = !lean_is_exclusive(v_x_302_);
if (v_isSharedCheck_328_ == 0)
{
v___x_323_ = v_x_302_;
v_isShared_324_ = v_isSharedCheck_328_;
goto v_resetjp_322_;
}
else
{
lean_inc(v_val_321_);
lean_dec(v_x_302_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_328_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
lean_object* v___x_326_; 
if (v_isShared_324_ == 0)
{
v___x_326_ = v___x_323_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v_val_321_);
v___x_326_ = v_reuseFailAlloc_327_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
return v___x_326_;
}
}
}
}
else
{
lean_object* v_one_329_; lean_object* v_n_330_; lean_object* v___y_332_; 
v_one_329_ = lean_unsigned_to_nat(1u);
v_n_330_ = lean_nat_sub(v_x_303_, v_one_329_);
lean_dec(v_x_303_);
if (v_isSome_319_ == 0)
{
goto v___jp_338_;
}
else
{
lean_object* v___x_340_; uint8_t v_isSome_341_; 
v___x_340_ = lean_array_fget_borrowed(v_valueArray_317_, v_x_304_);
v_isSome_341_ = lean_noption_is_some(v___x_340_);
if (v_isSome_341_ == 0)
{
goto v___jp_338_;
}
else
{
lean_object* v_val_342_; uint8_t v___x_343_; 
lean_inc(v___x_318_);
v_val_342_ = lean_noption_get(v___x_318_);
v___x_343_ = lean_name_eq(v_val_342_, v_query_301_);
if (v___x_343_ == 0)
{
lean_object* v___x_344_; lean_object* v___x_345_; uint8_t v___x_346_; 
lean_dec(v_val_342_);
v___x_344_ = lean_array_get_size(v_keyArray_316_);
v___x_345_ = lean_nat_add(v_x_304_, v_one_329_);
lean_dec(v_x_304_);
v___x_346_ = lean_nat_dec_lt(v___x_345_, v___x_344_);
if (v___x_346_ == 0)
{
lean_dec(v___x_345_);
v_x_303_ = v_n_330_;
v_x_304_ = v_zero_305_;
goto _start;
}
else
{
v_x_303_ = v_n_330_;
v_x_304_ = v___x_345_;
goto _start;
}
}
else
{
lean_object* v_val_349_; lean_object* v___x_350_; 
lean_dec(v_n_330_);
lean_dec(v_x_302_);
lean_inc(v___x_340_);
v_val_349_ = lean_noption_get(v___x_340_);
v___x_350_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_350_, 0, v_x_304_);
lean_ctor_set(v___x_350_, 1, v_val_342_);
lean_ctor_set(v___x_350_, 2, v_val_349_);
return v___x_350_;
}
}
}
v___jp_331_:
{
lean_object* v___x_333_; lean_object* v___x_334_; uint8_t v___x_335_; 
v___x_333_ = lean_array_get_size(v_keyArray_316_);
v___x_334_ = lean_nat_add(v_x_304_, v_one_329_);
lean_dec(v_x_304_);
v___x_335_ = lean_nat_dec_lt(v___x_334_, v___x_333_);
if (v___x_335_ == 0)
{
lean_dec(v___x_334_);
v_x_302_ = v___y_332_;
v_x_303_ = v_n_330_;
v_x_304_ = v_zero_305_;
goto _start;
}
else
{
v_x_302_ = v___y_332_;
v_x_303_ = v_n_330_;
v_x_304_ = v___x_334_;
goto _start;
}
}
v___jp_338_:
{
if (lean_obj_tag(v_x_302_) == 0)
{
lean_object* v___x_339_; 
lean_inc(v_x_304_);
v___x_339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_339_, 0, v_x_304_);
v___y_332_ = v___x_339_;
goto v___jp_331_;
}
else
{
v___y_332_ = v_x_302_;
goto v___jp_331_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg___boxed(lean_object* v_m_351_, lean_object* v_query_352_, lean_object* v_x_353_, lean_object* v_x_354_, lean_object* v_x_355_){
_start:
{
lean_object* v_res_356_; 
v_res_356_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg(v_m_351_, v_query_352_, v_x_353_, v_x_354_, v_x_355_);
lean_dec(v_query_352_);
lean_dec_ref(v_m_351_);
return v_res_356_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3___redArg(lean_object* v_m_357_, lean_object* v_query_358_){
_start:
{
lean_object* v_keyArray_359_; lean_object* v___x_360_; uint64_t v___y_362_; 
v_keyArray_359_ = lean_ctor_get(v_m_357_, 1);
v___x_360_ = lean_array_get_size(v_keyArray_359_);
if (lean_obj_tag(v_query_358_) == 0)
{
uint64_t v___x_377_; 
v___x_377_ = 1723ULL;
v___y_362_ = v___x_377_;
goto v___jp_361_;
}
else
{
uint64_t v_hash_378_; 
v_hash_378_ = lean_ctor_get_uint64(v_query_358_, sizeof(void*)*2);
v___y_362_ = v_hash_378_;
goto v___jp_361_;
}
v___jp_361_:
{
uint64_t v___x_363_; uint64_t v___x_364_; uint64_t v_fold_365_; uint64_t v___x_366_; uint64_t v___x_367_; uint64_t v___x_368_; size_t v___x_369_; size_t v___x_370_; size_t v___x_371_; size_t v___x_372_; size_t v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_363_ = 32ULL;
v___x_364_ = lean_uint64_shift_right(v___y_362_, v___x_363_);
v_fold_365_ = lean_uint64_xor(v___y_362_, v___x_364_);
v___x_366_ = 16ULL;
v___x_367_ = lean_uint64_shift_right(v_fold_365_, v___x_366_);
v___x_368_ = lean_uint64_xor(v_fold_365_, v___x_367_);
v___x_369_ = lean_uint64_to_usize(v___x_368_);
v___x_370_ = lean_usize_of_nat(v___x_360_);
v___x_371_ = ((size_t)1ULL);
v___x_372_ = lean_usize_sub(v___x_370_, v___x_371_);
v___x_373_ = lean_usize_land(v___x_369_, v___x_372_);
v___x_374_ = lean_usize_to_nat(v___x_373_);
v___x_375_ = lean_box(0);
v___x_376_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg(v_m_357_, v_query_358_, v___x_375_, v___x_360_, v___x_374_);
return v___x_376_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3___redArg___boxed(lean_object* v_m_379_, lean_object* v_query_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3___redArg(v_m_379_, v_query_380_);
lean_dec(v_query_380_);
lean_dec_ref(v_m_379_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__5_spec__10_spec__15___redArg(lean_object* v_b_382_, lean_object* v_acc_383_, lean_object* v_i_384_){
_start:
{
lean_object* v___y_386_; lean_object* v_keyArray_394_; lean_object* v_valueArray_395_; lean_object* v___x_396_; uint8_t v___x_397_; 
v_keyArray_394_ = lean_ctor_get(v_b_382_, 1);
v_valueArray_395_ = lean_ctor_get(v_b_382_, 2);
v___x_396_ = lean_array_get_size(v_keyArray_394_);
v___x_397_ = lean_nat_dec_lt(v_i_384_, v___x_396_);
if (v___x_397_ == 0)
{
lean_dec(v_i_384_);
return v_acc_383_;
}
else
{
lean_object* v___x_398_; uint8_t v_isSome_399_; 
v___x_398_ = lean_array_fget_borrowed(v_keyArray_394_, v_i_384_);
v_isSome_399_ = lean_noption_is_some(v___x_398_);
if (v_isSome_399_ == 0)
{
goto v___jp_390_;
}
else
{
lean_object* v___x_400_; uint8_t v_isSome_401_; 
v___x_400_ = lean_array_fget_borrowed(v_valueArray_395_, v_i_384_);
v_isSome_401_ = lean_noption_is_some(v___x_400_);
if (v_isSome_401_ == 0)
{
goto v___jp_390_;
}
else
{
lean_object* v_val_402_; lean_object* v_val_403_; lean_object* v_i_405_; lean_object* v___x_410_; 
lean_inc(v___x_398_);
v_val_402_ = lean_noption_get(v___x_398_);
lean_inc(v___x_400_);
v_val_403_ = lean_noption_get(v___x_400_);
v___x_410_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3___redArg(v_acc_383_, v_val_402_);
switch(lean_obj_tag(v___x_410_))
{
case 0:
{
lean_object* v_index_411_; lean_object* v_size_412_; lean_object* v___x_413_; 
v_index_411_ = lean_ctor_get(v___x_410_, 0);
lean_inc(v_index_411_);
lean_dec_ref_known(v___x_410_, 3);
v_size_412_ = lean_ctor_get(v_acc_383_, 0);
lean_inc(v_size_412_);
v___x_413_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_383_, v_size_412_, v_index_411_, v_val_402_, v_val_403_);
lean_dec(v_index_411_);
v___y_386_ = v___x_413_;
goto v___jp_385_;
}
case 1:
{
lean_object* v_index_414_; 
v_index_414_ = lean_ctor_get(v___x_410_, 0);
lean_inc(v_index_414_);
lean_dec_ref_known(v___x_410_, 1);
v_i_405_ = v_index_414_;
goto v___jp_404_;
}
default: 
{
lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_415_ = lean_unsigned_to_nat(0u);
v___x_416_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_383_, v___x_415_);
if (lean_obj_tag(v___x_416_) == 0)
{
lean_object* v_index_417_; 
v_index_417_ = lean_ctor_get(v___x_416_, 0);
lean_inc(v_index_417_);
lean_dec_ref_known(v___x_416_, 1);
v_i_405_ = v_index_417_;
goto v___jp_404_;
}
else
{
lean_dec(v_val_403_);
lean_dec(v_val_402_);
v___y_386_ = v_acc_383_;
goto v___jp_385_;
}
}
}
v___jp_404_:
{
lean_object* v_size_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; 
v_size_406_ = lean_ctor_get(v_acc_383_, 0);
v___x_407_ = lean_unsigned_to_nat(1u);
v___x_408_ = lean_nat_add(v_size_406_, v___x_407_);
v___x_409_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_383_, v___x_408_, v_i_405_, v_val_402_, v_val_403_);
lean_dec(v_i_405_);
v___y_386_ = v___x_409_;
goto v___jp_385_;
}
}
}
}
v___jp_385_:
{
lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_387_ = lean_unsigned_to_nat(1u);
v___x_388_ = lean_nat_add(v_i_384_, v___x_387_);
lean_dec(v_i_384_);
v_acc_383_ = v___y_386_;
v_i_384_ = v___x_388_;
goto _start;
}
v___jp_390_:
{
lean_object* v___x_391_; lean_object* v___x_392_; 
v___x_391_ = lean_unsigned_to_nat(1u);
v___x_392_ = lean_nat_add(v_i_384_, v___x_391_);
lean_dec(v_i_384_);
v_i_384_ = v___x_392_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__5_spec__10_spec__15___redArg___boxed(lean_object* v_b_418_, lean_object* v_acc_419_, lean_object* v_i_420_){
_start:
{
lean_object* v_res_421_; 
v_res_421_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__5_spec__10_spec__15___redArg(v_b_418_, v_acc_419_, v_i_420_);
lean_dec_ref(v_b_418_);
return v_res_421_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__5_spec__10___redArg(lean_object* v_init_422_, lean_object* v_b_423_){
_start:
{
lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_424_ = lean_unsigned_to_nat(0u);
v___x_425_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__5_spec__10_spec__15___redArg(v_b_423_, v_init_422_, v___x_424_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__5_spec__10___redArg___boxed(lean_object* v_init_426_, lean_object* v_b_427_){
_start:
{
lean_object* v_res_428_; 
v_res_428_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__5_spec__10___redArg(v_init_426_, v_b_427_);
lean_dec_ref(v_b_427_);
return v_res_428_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__5___redArg(lean_object* v_m_429_){
_start:
{
lean_object* v_keyArray_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v_cellCount_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v_target_437_; lean_object* v___x_438_; 
v_keyArray_430_ = lean_ctor_get(v_m_429_, 1);
v___x_431_ = lean_array_get_size(v_keyArray_430_);
v___x_432_ = lean_unsigned_to_nat(2u);
v_cellCount_433_ = lean_nat_mul(v___x_431_, v___x_432_);
v___x_434_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_433_);
v___x_435_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_433_);
v___x_436_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_433_);
v_target_437_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_437_, 0, v___x_434_);
lean_ctor_set(v_target_437_, 1, v___x_435_);
lean_ctor_set(v_target_437_, 2, v___x_436_);
v___x_438_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__5_spec__10___redArg(v_target_437_, v_m_429_);
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__5___redArg___boxed(lean_object* v_m_439_){
_start:
{
lean_object* v_res_440_; 
v_res_440_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__5___redArg(v_m_439_);
lean_dec_ref(v_m_439_);
return v_res_440_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1___redArg(lean_object* v_x_441_, lean_object* v_x_442_, lean_object* v_x_443_){
_start:
{
uint8_t v_stage_u2081_444_; lean_object* v_map_u2081_445_; lean_object* v_map_u2082_446_; lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_526_; 
v_stage_u2081_444_ = lean_ctor_get_uint8(v_x_441_, sizeof(void*)*2);
v_map_u2081_445_ = lean_ctor_get(v_x_441_, 0);
v_map_u2082_446_ = lean_ctor_get(v_x_441_, 1);
v_isSharedCheck_526_ = !lean_is_exclusive(v_x_441_);
if (v_isSharedCheck_526_ == 0)
{
v___x_448_ = v_x_441_;
v_isShared_449_ = v_isSharedCheck_526_;
goto v_resetjp_447_;
}
else
{
lean_inc(v_map_u2082_446_);
lean_inc(v_map_u2081_445_);
lean_dec(v_x_441_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_526_;
goto v_resetjp_447_;
}
v_resetjp_447_:
{
lean_object* v___y_451_; lean_object* v_i_452_; lean_object* v___y_461_; lean_object* v___y_473_; lean_object* v_i_474_; 
if (v_stage_u2081_444_ == 0)
{
lean_object* v___x_492_; lean_object* v___x_493_; 
lean_del_object(v___x_448_);
v___x_492_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4___redArg(v_map_u2082_446_, v_x_442_, v_x_443_);
v___x_493_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_493_, 0, v_map_u2081_445_);
lean_ctor_set(v___x_493_, 1, v___x_492_);
lean_ctor_set_uint8(v___x_493_, sizeof(void*)*2, v_stage_u2081_444_);
return v___x_493_;
}
else
{
lean_object* v___x_494_; 
v___x_494_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3___redArg(v_map_u2081_445_, v_x_442_);
switch(lean_obj_tag(v___x_494_))
{
case 0:
{
lean_object* v_index_495_; lean_object* v_size_496_; lean_object* v___x_497_; lean_object* v___x_498_; 
lean_del_object(v___x_448_);
v_index_495_ = lean_ctor_get(v___x_494_, 0);
lean_inc(v_index_495_);
lean_dec_ref_known(v___x_494_, 3);
v_size_496_ = lean_ctor_get(v_map_u2081_445_, 0);
lean_inc(v_size_496_);
v___x_497_ = l_Std_DHashMap_Raw_setEntry___redArg(v_map_u2081_445_, v_size_496_, v_index_495_, v_x_442_, v_x_443_);
lean_dec(v_index_495_);
v___x_498_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_498_, 0, v___x_497_);
lean_ctor_set(v___x_498_, 1, v_map_u2082_446_);
lean_ctor_set_uint8(v___x_498_, sizeof(void*)*2, v_stage_u2081_444_);
return v___x_498_;
}
case 1:
{
lean_object* v_index_499_; lean_object* v_size_500_; lean_object* v_keyArray_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; uint8_t v___x_505_; 
lean_del_object(v___x_448_);
v_index_499_ = lean_ctor_get(v___x_494_, 0);
lean_inc(v_index_499_);
lean_dec_ref_known(v___x_494_, 1);
v_size_500_ = lean_ctor_get(v_map_u2081_445_, 0);
v_keyArray_501_ = lean_ctor_get(v_map_u2081_445_, 1);
v___x_502_ = lean_unsigned_to_nat(1u);
v___x_503_ = lean_nat_add(v_size_500_, v___x_502_);
v___x_504_ = lean_array_get_size(v_keyArray_501_);
v___x_505_ = lean_nat_dec_lt(v___x_503_, v___x_504_);
if (v___x_505_ == 0)
{
lean_dec(v___x_503_);
lean_dec(v_index_499_);
goto v___jp_480_;
}
else
{
lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; uint8_t v___x_510_; 
v___x_506_ = lean_unsigned_to_nat(4u);
v___x_507_ = lean_nat_mul(v___x_503_, v___x_506_);
v___x_508_ = lean_unsigned_to_nat(3u);
v___x_509_ = lean_nat_mul(v___x_504_, v___x_508_);
v___x_510_ = lean_nat_dec_le(v___x_507_, v___x_509_);
lean_dec(v___x_509_);
lean_dec(v___x_507_);
if (v___x_510_ == 0)
{
lean_dec(v___x_503_);
lean_dec(v_index_499_);
goto v___jp_480_;
}
else
{
lean_object* v___x_511_; lean_object* v___x_512_; 
v___x_511_ = l_Std_DHashMap_Raw_setEntry___redArg(v_map_u2081_445_, v___x_503_, v_index_499_, v_x_442_, v_x_443_);
lean_dec(v_index_499_);
v___x_512_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_512_, 0, v___x_511_);
lean_ctor_set(v___x_512_, 1, v_map_u2082_446_);
lean_ctor_set_uint8(v___x_512_, sizeof(void*)*2, v_stage_u2081_444_);
return v___x_512_;
}
}
}
default: 
{
lean_object* v_size_513_; lean_object* v_keyArray_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; uint8_t v___x_518_; 
v_size_513_ = lean_ctor_get(v_map_u2081_445_, 0);
v_keyArray_514_ = lean_ctor_get(v_map_u2081_445_, 1);
v___x_515_ = lean_unsigned_to_nat(1u);
v___x_516_ = lean_nat_add(v_size_513_, v___x_515_);
v___x_517_ = lean_array_get_size(v_keyArray_514_);
v___x_518_ = lean_nat_dec_lt(v___x_516_, v___x_517_);
if (v___x_518_ == 0)
{
lean_object* v___x_519_; 
lean_dec(v___x_516_);
v___x_519_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__5___redArg(v_map_u2081_445_);
lean_dec_ref(v_map_u2081_445_);
v___y_461_ = v___x_519_;
goto v___jp_460_;
}
else
{
lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; uint8_t v___x_524_; 
v___x_520_ = lean_unsigned_to_nat(4u);
v___x_521_ = lean_nat_mul(v___x_516_, v___x_520_);
lean_dec(v___x_516_);
v___x_522_ = lean_unsigned_to_nat(3u);
v___x_523_ = lean_nat_mul(v___x_517_, v___x_522_);
v___x_524_ = lean_nat_dec_le(v___x_521_, v___x_523_);
lean_dec(v___x_523_);
lean_dec(v___x_521_);
if (v___x_524_ == 0)
{
lean_object* v___x_525_; 
v___x_525_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__5___redArg(v_map_u2081_445_);
lean_dec_ref(v_map_u2081_445_);
v___y_461_ = v___x_525_;
goto v___jp_460_;
}
else
{
v___y_461_ = v_map_u2081_445_;
goto v___jp_460_;
}
}
}
}
}
v___jp_450_:
{
lean_object* v_size_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_458_; 
v_size_453_ = lean_ctor_get(v___y_451_, 0);
v___x_454_ = lean_unsigned_to_nat(1u);
v___x_455_ = lean_nat_add(v_size_453_, v___x_454_);
v___x_456_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_451_, v___x_455_, v_i_452_, v_x_442_, v_x_443_);
lean_dec(v_i_452_);
if (v_isShared_449_ == 0)
{
lean_ctor_set(v___x_448_, 0, v___x_456_);
v___x_458_ = v___x_448_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v___x_456_);
lean_ctor_set(v_reuseFailAlloc_459_, 1, v_map_u2082_446_);
lean_ctor_set_uint8(v_reuseFailAlloc_459_, sizeof(void*)*2, v_stage_u2081_444_);
v___x_458_ = v_reuseFailAlloc_459_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
return v___x_458_;
}
}
v___jp_460_:
{
lean_object* v___x_462_; 
v___x_462_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3___redArg(v___y_461_, v_x_442_);
switch(lean_obj_tag(v___x_462_))
{
case 0:
{
lean_object* v_index_463_; lean_object* v_size_464_; lean_object* v___x_465_; lean_object* v___x_466_; 
lean_del_object(v___x_448_);
v_index_463_ = lean_ctor_get(v___x_462_, 0);
lean_inc(v_index_463_);
lean_dec_ref_known(v___x_462_, 3);
v_size_464_ = lean_ctor_get(v___y_461_, 0);
lean_inc(v_size_464_);
v___x_465_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_461_, v_size_464_, v_index_463_, v_x_442_, v_x_443_);
lean_dec(v_index_463_);
v___x_466_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_466_, 0, v___x_465_);
lean_ctor_set(v___x_466_, 1, v_map_u2082_446_);
lean_ctor_set_uint8(v___x_466_, sizeof(void*)*2, v_stage_u2081_444_);
return v___x_466_;
}
case 1:
{
lean_object* v_index_467_; 
v_index_467_ = lean_ctor_get(v___x_462_, 0);
lean_inc(v_index_467_);
lean_dec_ref_known(v___x_462_, 1);
v___y_451_ = v___y_461_;
v_i_452_ = v_index_467_;
goto v___jp_450_;
}
default: 
{
lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_468_ = lean_unsigned_to_nat(0u);
v___x_469_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_461_, v___x_468_);
if (lean_obj_tag(v___x_469_) == 0)
{
lean_object* v_index_470_; 
v_index_470_ = lean_ctor_get(v___x_469_, 0);
lean_inc(v_index_470_);
lean_dec_ref_known(v___x_469_, 1);
v___y_451_ = v___y_461_;
v_i_452_ = v_index_470_;
goto v___jp_450_;
}
else
{
lean_object* v___x_471_; 
lean_del_object(v___x_448_);
lean_dec(v_x_443_);
lean_dec(v_x_442_);
v___x_471_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_471_, 0, v___y_461_);
lean_ctor_set(v___x_471_, 1, v_map_u2082_446_);
lean_ctor_set_uint8(v___x_471_, sizeof(void*)*2, v_stage_u2081_444_);
return v___x_471_;
}
}
}
}
v___jp_472_:
{
lean_object* v_size_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; 
v_size_475_ = lean_ctor_get(v___y_473_, 0);
v___x_476_ = lean_unsigned_to_nat(1u);
v___x_477_ = lean_nat_add(v_size_475_, v___x_476_);
v___x_478_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_473_, v___x_477_, v_i_474_, v_x_442_, v_x_443_);
lean_dec(v_i_474_);
v___x_479_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_479_, 0, v___x_478_);
lean_ctor_set(v___x_479_, 1, v_map_u2082_446_);
lean_ctor_set_uint8(v___x_479_, sizeof(void*)*2, v_stage_u2081_444_);
return v___x_479_;
}
v___jp_480_:
{
lean_object* v___x_481_; lean_object* v___x_482_; 
v___x_481_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__5___redArg(v_map_u2081_445_);
lean_dec_ref(v_map_u2081_445_);
v___x_482_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3___redArg(v___x_481_, v_x_442_);
switch(lean_obj_tag(v___x_482_))
{
case 0:
{
lean_object* v_index_483_; lean_object* v_size_484_; lean_object* v___x_485_; lean_object* v___x_486_; 
v_index_483_ = lean_ctor_get(v___x_482_, 0);
lean_inc(v_index_483_);
lean_dec_ref_known(v___x_482_, 3);
v_size_484_ = lean_ctor_get(v___x_481_, 0);
lean_inc(v_size_484_);
v___x_485_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_481_, v_size_484_, v_index_483_, v_x_442_, v_x_443_);
lean_dec(v_index_483_);
v___x_486_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_486_, 0, v___x_485_);
lean_ctor_set(v___x_486_, 1, v_map_u2082_446_);
lean_ctor_set_uint8(v___x_486_, sizeof(void*)*2, v_stage_u2081_444_);
return v___x_486_;
}
case 1:
{
lean_object* v_index_487_; 
v_index_487_ = lean_ctor_get(v___x_482_, 0);
lean_inc(v_index_487_);
lean_dec_ref_known(v___x_482_, 1);
v___y_473_ = v___x_481_;
v_i_474_ = v_index_487_;
goto v___jp_472_;
}
default: 
{
lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_488_ = lean_unsigned_to_nat(0u);
v___x_489_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_481_, v___x_488_);
if (lean_obj_tag(v___x_489_) == 0)
{
lean_object* v_index_490_; 
v_index_490_ = lean_ctor_get(v___x_489_, 0);
lean_inc(v_index_490_);
lean_dec_ref_known(v___x_489_, 1);
v___y_473_ = v___x_481_;
v_i_474_ = v_index_490_;
goto v___jp_472_;
}
else
{
lean_object* v___x_491_; 
lean_dec(v_x_443_);
lean_dec(v_x_442_);
v___x_491_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_491_, 0, v___x_481_);
lean_ctor_set(v___x_491_, 1, v_map_u2082_446_);
lean_ctor_set_uint8(v___x_491_, sizeof(void*)*2, v_stage_u2081_444_);
return v___x_491_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3___redArg(lean_object* v_m_527_, lean_object* v_query_528_){
_start:
{
lean_object* v___x_529_; 
v___x_529_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3___redArg(v_m_527_, v_query_528_);
if (lean_obj_tag(v___x_529_) == 0)
{
lean_object* v_index_530_; lean_object* v_key_531_; lean_object* v_value_532_; lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_539_; 
v_index_530_ = lean_ctor_get(v___x_529_, 0);
v_key_531_ = lean_ctor_get(v___x_529_, 1);
v_value_532_ = lean_ctor_get(v___x_529_, 2);
v_isSharedCheck_539_ = !lean_is_exclusive(v___x_529_);
if (v_isSharedCheck_539_ == 0)
{
v___x_534_ = v___x_529_;
v_isShared_535_ = v_isSharedCheck_539_;
goto v_resetjp_533_;
}
else
{
lean_inc(v_value_532_);
lean_inc(v_key_531_);
lean_inc(v_index_530_);
lean_dec(v___x_529_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_539_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
lean_object* v___x_537_; 
if (v_isShared_535_ == 0)
{
v___x_537_ = v___x_534_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v_index_530_);
lean_ctor_set(v_reuseFailAlloc_538_, 1, v_key_531_);
lean_ctor_set(v_reuseFailAlloc_538_, 2, v_value_532_);
v___x_537_ = v_reuseFailAlloc_538_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
return v___x_537_;
}
}
}
else
{
lean_object* v___x_540_; 
lean_dec(v___x_529_);
v___x_540_ = lean_box(1);
return v___x_540_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_m_541_, lean_object* v_query_542_){
_start:
{
lean_object* v_res_543_; 
v_res_543_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3___redArg(v_m_541_, v_query_542_);
lean_dec(v_query_542_);
lean_dec_ref(v_m_541_);
return v_res_543_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1___redArg(lean_object* v_m_544_, lean_object* v_a_545_){
_start:
{
lean_object* v___x_546_; 
v___x_546_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3___redArg(v_m_544_, v_a_545_);
if (lean_obj_tag(v___x_546_) == 0)
{
lean_object* v_value_547_; lean_object* v___x_548_; 
v_value_547_ = lean_ctor_get(v___x_546_, 2);
lean_inc(v_value_547_);
lean_dec_ref_known(v___x_546_, 3);
v___x_548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_548_, 0, v_value_547_);
return v___x_548_;
}
else
{
lean_object* v___x_549_; 
v___x_549_ = lean_box(0);
return v___x_549_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1___redArg___boxed(lean_object* v_m_550_, lean_object* v_a_551_){
_start:
{
lean_object* v_res_552_; 
v_res_552_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1___redArg(v_m_550_, v_a_551_);
lean_dec(v_a_551_);
lean_dec_ref(v_m_550_);
return v_res_552_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_keys_553_, lean_object* v_vals_554_, lean_object* v_i_555_, lean_object* v_k_556_){
_start:
{
lean_object* v___x_557_; uint8_t v___x_558_; 
v___x_557_ = lean_array_get_size(v_keys_553_);
v___x_558_ = lean_nat_dec_lt(v_i_555_, v___x_557_);
if (v___x_558_ == 0)
{
lean_object* v___x_559_; 
lean_dec(v_i_555_);
v___x_559_ = lean_box(0);
return v___x_559_;
}
else
{
lean_object* v_k_x27_560_; uint8_t v___x_561_; 
v_k_x27_560_ = lean_array_fget_borrowed(v_keys_553_, v_i_555_);
v___x_561_ = lean_name_eq(v_k_556_, v_k_x27_560_);
if (v___x_561_ == 0)
{
lean_object* v___x_562_; lean_object* v___x_563_; 
v___x_562_ = lean_unsigned_to_nat(1u);
v___x_563_ = lean_nat_add(v_i_555_, v___x_562_);
lean_dec(v_i_555_);
v_i_555_ = v___x_563_;
goto _start;
}
else
{
lean_object* v___x_565_; lean_object* v___x_566_; 
v___x_565_ = lean_array_fget_borrowed(v_vals_554_, v_i_555_);
lean_dec(v_i_555_);
lean_inc(v___x_565_);
v___x_566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_566_, 0, v___x_565_);
return v___x_566_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_keys_567_, lean_object* v_vals_568_, lean_object* v_i_569_, lean_object* v_k_570_){
_start:
{
lean_object* v_res_571_; 
v_res_571_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4___redArg(v_keys_567_, v_vals_568_, v_i_569_, v_k_570_);
lean_dec(v_k_570_);
lean_dec_ref(v_vals_568_);
lean_dec_ref(v_keys_567_);
return v_res_571_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1___redArg(lean_object* v_x_572_, size_t v_x_573_, lean_object* v_x_574_){
_start:
{
if (lean_obj_tag(v_x_572_) == 0)
{
lean_object* v_es_575_; lean_object* v___x_576_; size_t v___x_577_; size_t v___x_578_; lean_object* v_j_579_; lean_object* v___x_580_; 
v_es_575_ = lean_ctor_get(v_x_572_, 0);
v___x_576_ = lean_box(2);
v___x_577_ = ((size_t)31ULL);
v___x_578_ = lean_usize_land(v_x_573_, v___x_577_);
v_j_579_ = lean_usize_to_nat(v___x_578_);
v___x_580_ = lean_array_get_borrowed(v___x_576_, v_es_575_, v_j_579_);
lean_dec(v_j_579_);
switch(lean_obj_tag(v___x_580_))
{
case 0:
{
lean_object* v_key_581_; lean_object* v_val_582_; uint8_t v___x_583_; 
v_key_581_ = lean_ctor_get(v___x_580_, 0);
v_val_582_ = lean_ctor_get(v___x_580_, 1);
v___x_583_ = lean_name_eq(v_x_574_, v_key_581_);
if (v___x_583_ == 0)
{
lean_object* v___x_584_; 
v___x_584_ = lean_box(0);
return v___x_584_;
}
else
{
lean_object* v___x_585_; 
lean_inc(v_val_582_);
v___x_585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_585_, 0, v_val_582_);
return v___x_585_;
}
}
case 1:
{
lean_object* v_node_586_; size_t v___x_587_; size_t v___x_588_; 
v_node_586_ = lean_ctor_get(v___x_580_, 0);
v___x_587_ = ((size_t)5ULL);
v___x_588_ = lean_usize_shift_right(v_x_573_, v___x_587_);
v_x_572_ = v_node_586_;
v_x_573_ = v___x_588_;
goto _start;
}
default: 
{
lean_object* v___x_590_; 
v___x_590_ = lean_box(0);
return v___x_590_;
}
}
}
else
{
lean_object* v_ks_591_; lean_object* v_vs_592_; lean_object* v___x_593_; lean_object* v___x_594_; 
v_ks_591_ = lean_ctor_get(v_x_572_, 0);
v_vs_592_ = lean_ctor_get(v_x_572_, 1);
v___x_593_ = lean_unsigned_to_nat(0u);
v___x_594_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4___redArg(v_ks_591_, v_vs_592_, v___x_593_, v_x_574_);
return v___x_594_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_595_, lean_object* v_x_596_, lean_object* v_x_597_){
_start:
{
size_t v_x_1943__boxed_598_; lean_object* v_res_599_; 
v_x_1943__boxed_598_ = lean_unbox_usize(v_x_596_);
lean_dec(v_x_596_);
v_res_599_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1___redArg(v_x_595_, v_x_1943__boxed_598_, v_x_597_);
lean_dec(v_x_597_);
lean_dec_ref(v_x_595_);
return v_res_599_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0___redArg(lean_object* v_x_600_, lean_object* v_x_601_){
_start:
{
uint64_t v___y_603_; 
if (lean_obj_tag(v_x_601_) == 0)
{
uint64_t v___x_606_; 
v___x_606_ = 1723ULL;
v___y_603_ = v___x_606_;
goto v___jp_602_;
}
else
{
uint64_t v_hash_607_; 
v_hash_607_ = lean_ctor_get_uint64(v_x_601_, sizeof(void*)*2);
v___y_603_ = v_hash_607_;
goto v___jp_602_;
}
v___jp_602_:
{
size_t v___x_604_; lean_object* v___x_605_; 
v___x_604_ = lean_uint64_to_usize(v___y_603_);
v___x_605_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1___redArg(v_x_600_, v___x_604_, v_x_601_);
return v___x_605_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0___redArg___boxed(lean_object* v_x_608_, lean_object* v_x_609_){
_start:
{
lean_object* v_res_610_; 
v_res_610_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0___redArg(v_x_608_, v_x_609_);
lean_dec(v_x_609_);
lean_dec_ref(v_x_608_);
return v_res_610_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0___redArg(lean_object* v_x_611_, lean_object* v_x_612_){
_start:
{
uint8_t v_stage_u2081_613_; 
v_stage_u2081_613_ = lean_ctor_get_uint8(v_x_611_, sizeof(void*)*2);
if (v_stage_u2081_613_ == 0)
{
lean_object* v_map_u2081_614_; lean_object* v_map_u2082_615_; lean_object* v___x_616_; 
v_map_u2081_614_ = lean_ctor_get(v_x_611_, 0);
v_map_u2082_615_ = lean_ctor_get(v_x_611_, 1);
v___x_616_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0___redArg(v_map_u2082_615_, v_x_612_);
if (lean_obj_tag(v___x_616_) == 0)
{
lean_object* v___x_617_; 
v___x_617_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1___redArg(v_map_u2081_614_, v_x_612_);
return v___x_617_;
}
else
{
return v___x_616_;
}
}
else
{
lean_object* v_map_u2081_618_; lean_object* v___x_619_; 
v_map_u2081_618_ = lean_ctor_get(v_x_611_, 0);
v___x_619_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1___redArg(v_map_u2081_618_, v_x_612_);
return v___x_619_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0___redArg___boxed(lean_object* v_x_620_, lean_object* v_x_621_){
_start:
{
lean_object* v_res_622_; 
v_res_622_ = l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0___redArg(v_x_620_, v_x_621_);
lean_dec(v_x_621_);
lean_dec_ref(v_x_620_);
return v_res_622_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_addAliasEntry_spec__2(lean_object* v_a_623_, lean_object* v_x_624_){
_start:
{
if (lean_obj_tag(v_x_624_) == 0)
{
uint8_t v___x_625_; 
v___x_625_ = 0;
return v___x_625_;
}
else
{
lean_object* v_head_626_; lean_object* v_tail_627_; uint8_t v___x_628_; 
v_head_626_ = lean_ctor_get(v_x_624_, 0);
v_tail_627_ = lean_ctor_get(v_x_624_, 1);
v___x_628_ = lean_name_eq(v_a_623_, v_head_626_);
if (v___x_628_ == 0)
{
v_x_624_ = v_tail_627_;
goto _start;
}
else
{
return v___x_628_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_addAliasEntry_spec__2___boxed(lean_object* v_a_630_, lean_object* v_x_631_){
_start:
{
uint8_t v_res_632_; lean_object* v_r_633_; 
v_res_632_ = l_List_elem___at___00Lean_addAliasEntry_spec__2(v_a_630_, v_x_631_);
lean_dec(v_x_631_);
lean_dec(v_a_630_);
v_r_633_ = lean_box(v_res_632_);
return v_r_633_;
}
}
LEAN_EXPORT lean_object* l_Lean_addAliasEntry(lean_object* v_s_634_, lean_object* v_e_635_){
_start:
{
lean_object* v_fst_636_; lean_object* v_snd_637_; lean_object* v___x_639_; uint8_t v_isShared_640_; uint8_t v_isSharedCheck_653_; 
v_fst_636_ = lean_ctor_get(v_e_635_, 0);
v_snd_637_ = lean_ctor_get(v_e_635_, 1);
v_isSharedCheck_653_ = !lean_is_exclusive(v_e_635_);
if (v_isSharedCheck_653_ == 0)
{
v___x_639_ = v_e_635_;
v_isShared_640_ = v_isSharedCheck_653_;
goto v_resetjp_638_;
}
else
{
lean_inc(v_snd_637_);
lean_inc(v_fst_636_);
lean_dec(v_e_635_);
v___x_639_ = lean_box(0);
v_isShared_640_ = v_isSharedCheck_653_;
goto v_resetjp_638_;
}
v_resetjp_638_:
{
lean_object* v___x_641_; 
v___x_641_ = l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0___redArg(v_s_634_, v_fst_636_);
if (lean_obj_tag(v___x_641_) == 0)
{
lean_object* v___x_642_; lean_object* v___x_644_; 
v___x_642_ = lean_box(0);
if (v_isShared_640_ == 0)
{
lean_ctor_set_tag(v___x_639_, 1);
lean_ctor_set(v___x_639_, 1, v___x_642_);
lean_ctor_set(v___x_639_, 0, v_snd_637_);
v___x_644_ = v___x_639_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v_snd_637_);
lean_ctor_set(v_reuseFailAlloc_646_, 1, v___x_642_);
v___x_644_ = v_reuseFailAlloc_646_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
lean_object* v___x_645_; 
v___x_645_ = l_Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1___redArg(v_s_634_, v_fst_636_, v___x_644_);
return v___x_645_;
}
}
else
{
lean_object* v_val_647_; uint8_t v___x_648_; 
v_val_647_ = lean_ctor_get(v___x_641_, 0);
lean_inc(v_val_647_);
lean_dec_ref_known(v___x_641_, 1);
v___x_648_ = l_List_elem___at___00Lean_addAliasEntry_spec__2(v_snd_637_, v_val_647_);
if (v___x_648_ == 0)
{
lean_object* v___x_650_; 
if (v_isShared_640_ == 0)
{
lean_ctor_set_tag(v___x_639_, 1);
lean_ctor_set(v___x_639_, 1, v_val_647_);
lean_ctor_set(v___x_639_, 0, v_snd_637_);
v___x_650_ = v___x_639_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v_snd_637_);
lean_ctor_set(v_reuseFailAlloc_652_, 1, v_val_647_);
v___x_650_ = v_reuseFailAlloc_652_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
lean_object* v___x_651_; 
v___x_651_ = l_Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1___redArg(v_s_634_, v_fst_636_, v___x_650_);
return v___x_651_;
}
}
else
{
lean_dec(v_val_647_);
lean_del_object(v___x_639_);
lean_dec(v_snd_637_);
lean_dec(v_fst_636_);
return v_s_634_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0(lean_object* v_00_u03b2_654_, lean_object* v_x_655_, lean_object* v_x_656_){
_start:
{
lean_object* v___x_657_; 
v___x_657_ = l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0___redArg(v_x_655_, v_x_656_);
return v___x_657_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0___boxed(lean_object* v_00_u03b2_658_, lean_object* v_x_659_, lean_object* v_x_660_){
_start:
{
lean_object* v_res_661_; 
v_res_661_ = l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0(v_00_u03b2_658_, v_x_659_, v_x_660_);
lean_dec(v_x_660_);
lean_dec_ref(v_x_659_);
return v_res_661_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1(lean_object* v_00_u03b2_662_, lean_object* v_x_663_, lean_object* v_x_664_, lean_object* v_x_665_){
_start:
{
lean_object* v___x_666_; 
v___x_666_ = l_Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1___redArg(v_x_663_, v_x_664_, v_x_665_);
return v___x_666_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0(lean_object* v_00_u03b2_667_, lean_object* v_x_668_, lean_object* v_x_669_){
_start:
{
lean_object* v___x_670_; 
v___x_670_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0___redArg(v_x_668_, v_x_669_);
return v___x_670_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0___boxed(lean_object* v_00_u03b2_671_, lean_object* v_x_672_, lean_object* v_x_673_){
_start:
{
lean_object* v_res_674_; 
v_res_674_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0(v_00_u03b2_671_, v_x_672_, v_x_673_);
lean_dec(v_x_673_);
lean_dec_ref(v_x_672_);
return v_res_674_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1(lean_object* v_00_u03b2_675_, lean_object* v_m_676_, lean_object* v_a_677_){
_start:
{
lean_object* v___x_678_; 
v___x_678_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1___redArg(v_m_676_, v_a_677_);
return v___x_678_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1___boxed(lean_object* v_00_u03b2_679_, lean_object* v_m_680_, lean_object* v_a_681_){
_start:
{
lean_object* v_res_682_; 
v_res_682_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1(v_00_u03b2_679_, v_m_680_, v_a_681_);
lean_dec(v_a_681_);
lean_dec_ref(v_m_680_);
return v_res_682_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3(lean_object* v_00_u03b2_683_, lean_object* v_m_684_, lean_object* v_query_685_){
_start:
{
lean_object* v___x_686_; 
v___x_686_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3___redArg(v_m_684_, v_query_685_);
return v___x_686_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3___boxed(lean_object* v_00_u03b2_687_, lean_object* v_m_688_, lean_object* v_query_689_){
_start:
{
lean_object* v_res_690_; 
v_res_690_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3(v_00_u03b2_687_, v_m_688_, v_query_689_);
lean_dec(v_query_689_);
lean_dec_ref(v_m_688_);
return v_res_690_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4(lean_object* v_00_u03b2_691_, lean_object* v_x_692_, lean_object* v_x_693_, lean_object* v_x_694_){
_start:
{
lean_object* v___x_695_; 
v___x_695_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4___redArg(v_x_692_, v_x_693_, v_x_694_);
return v___x_695_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__5(lean_object* v_00_u03b2_696_, lean_object* v_m_697_){
_start:
{
lean_object* v___x_698_; 
v___x_698_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__5___redArg(v_m_697_);
return v___x_698_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__5___boxed(lean_object* v_00_u03b2_699_, lean_object* v_m_700_){
_start:
{
lean_object* v_res_701_; 
v_res_701_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__5(v_00_u03b2_699_, v_m_700_);
lean_dec_ref(v_m_700_);
return v_res_701_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_702_, lean_object* v_x_703_, size_t v_x_704_, lean_object* v_x_705_){
_start:
{
lean_object* v___x_706_; 
v___x_706_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1___redArg(v_x_703_, v_x_704_, v_x_705_);
return v___x_706_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_707_, lean_object* v_x_708_, lean_object* v_x_709_, lean_object* v_x_710_){
_start:
{
size_t v_x_2110__boxed_711_; lean_object* v_res_712_; 
v_x_2110__boxed_711_ = lean_unbox_usize(v_x_709_);
lean_dec(v_x_709_);
v_res_712_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1(v_00_u03b2_707_, v_x_708_, v_x_2110__boxed_711_, v_x_710_);
lean_dec(v_x_710_);
lean_dec_ref(v_x_708_);
return v_res_712_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_713_, lean_object* v_m_714_, lean_object* v_query_715_){
_start:
{
lean_object* v___x_716_; 
v___x_716_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3___redArg(v_m_714_, v_query_715_);
return v___x_716_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_717_, lean_object* v_m_718_, lean_object* v_query_719_){
_start:
{
lean_object* v_res_720_; 
v_res_720_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3(v_00_u03b2_717_, v_m_718_, v_query_719_);
lean_dec(v_query_719_);
lean_dec_ref(v_m_718_);
return v_res_720_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_721_, lean_object* v_m_722_, lean_object* v_query_723_, lean_object* v_x_724_, lean_object* v_x_725_, lean_object* v_x_726_, lean_object* v_x_727_){
_start:
{
lean_object* v___x_728_; 
v___x_728_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg(v_m_722_, v_query_723_, v_x_724_, v_x_725_, v_x_726_);
return v___x_728_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___boxed(lean_object* v_00_u03b2_729_, lean_object* v_m_730_, lean_object* v_query_731_, lean_object* v_x_732_, lean_object* v_x_733_, lean_object* v_x_734_, lean_object* v_x_735_){
_start:
{
lean_object* v_res_736_; 
v_res_736_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6(v_00_u03b2_729_, v_m_730_, v_query_731_, v_x_732_, v_x_733_, v_x_734_, v_x_735_);
lean_dec(v_query_731_);
lean_dec_ref(v_m_730_);
return v_res_736_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8(lean_object* v_00_u03b2_737_, lean_object* v_x_738_, size_t v_x_739_, size_t v_x_740_, lean_object* v_x_741_, lean_object* v_x_742_){
_start:
{
lean_object* v___x_743_; 
v___x_743_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8___redArg(v_x_738_, v_x_739_, v_x_740_, v_x_741_, v_x_742_);
return v___x_743_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8___boxed(lean_object* v_00_u03b2_744_, lean_object* v_x_745_, lean_object* v_x_746_, lean_object* v_x_747_, lean_object* v_x_748_, lean_object* v_x_749_){
_start:
{
size_t v_x_2137__boxed_750_; size_t v_x_2138__boxed_751_; lean_object* v_res_752_; 
v_x_2137__boxed_750_ = lean_unbox_usize(v_x_746_);
lean_dec(v_x_746_);
v_x_2138__boxed_751_ = lean_unbox_usize(v_x_747_);
lean_dec(v_x_747_);
v_res_752_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8(v_00_u03b2_744_, v_x_745_, v_x_2137__boxed_750_, v_x_2138__boxed_751_, v_x_748_, v_x_749_);
return v_res_752_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__5_spec__10(lean_object* v_00_u03b2_753_, lean_object* v_init_754_, lean_object* v_b_755_){
_start:
{
lean_object* v___x_756_; 
v___x_756_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__5_spec__10___redArg(v_init_754_, v_b_755_);
return v___x_756_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__5_spec__10___boxed(lean_object* v_00_u03b2_757_, lean_object* v_init_758_, lean_object* v_b_759_){
_start:
{
lean_object* v_res_760_; 
v_res_760_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__5_spec__10(v_00_u03b2_757_, v_init_758_, v_b_759_);
lean_dec_ref(v_b_759_);
return v_res_760_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_761_, lean_object* v_keys_762_, lean_object* v_vals_763_, lean_object* v_heq_764_, lean_object* v_i_765_, lean_object* v_k_766_){
_start:
{
lean_object* v___x_767_; 
v___x_767_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4___redArg(v_keys_762_, v_vals_763_, v_i_765_, v_k_766_);
return v___x_767_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b2_768_, lean_object* v_keys_769_, lean_object* v_vals_770_, lean_object* v_heq_771_, lean_object* v_i_772_, lean_object* v_k_773_){
_start:
{
lean_object* v_res_774_; 
v_res_774_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4(v_00_u03b2_768_, v_keys_769_, v_vals_770_, v_heq_771_, v_i_772_, v_k_773_);
lean_dec(v_k_773_);
lean_dec_ref(v_vals_770_);
lean_dec_ref(v_keys_769_);
return v_res_774_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8_spec__11(lean_object* v_00_u03b2_775_, lean_object* v_n_776_, lean_object* v_k_777_, lean_object* v_v_778_){
_start:
{
lean_object* v___x_779_; 
v___x_779_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8_spec__11___redArg(v_n_776_, v_k_777_, v_v_778_);
return v___x_779_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8_spec__12(lean_object* v_00_u03b2_780_, size_t v_depth_781_, lean_object* v_keys_782_, lean_object* v_vals_783_, lean_object* v_heq_784_, lean_object* v_i_785_, lean_object* v_entries_786_){
_start:
{
lean_object* v___x_787_; 
v___x_787_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8_spec__12___redArg(v_depth_781_, v_keys_782_, v_vals_783_, v_i_785_, v_entries_786_);
return v___x_787_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8_spec__12___boxed(lean_object* v_00_u03b2_788_, lean_object* v_depth_789_, lean_object* v_keys_790_, lean_object* v_vals_791_, lean_object* v_heq_792_, lean_object* v_i_793_, lean_object* v_entries_794_){
_start:
{
size_t v_depth_boxed_795_; lean_object* v_res_796_; 
v_depth_boxed_795_ = lean_unbox_usize(v_depth_789_);
lean_dec(v_depth_789_);
v_res_796_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8_spec__12(v_00_u03b2_788_, v_depth_boxed_795_, v_keys_790_, v_vals_791_, v_heq_792_, v_i_793_, v_entries_794_);
lean_dec_ref(v_vals_791_);
lean_dec_ref(v_keys_790_);
return v_res_796_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__5_spec__10_spec__15(lean_object* v_00_u03b2_797_, lean_object* v_b_798_, lean_object* v_acc_799_, lean_object* v_i_800_){
_start:
{
lean_object* v___x_801_; 
v___x_801_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__5_spec__10_spec__15___redArg(v_b_798_, v_acc_799_, v_i_800_);
return v___x_801_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__5_spec__10_spec__15___boxed(lean_object* v_00_u03b2_802_, lean_object* v_b_803_, lean_object* v_acc_804_, lean_object* v_i_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__5_spec__10_spec__15(v_00_u03b2_802_, v_b_803_, v_acc_804_, v_i_805_);
lean_dec_ref(v_b_803_);
return v_res_806_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8_spec__11_spec__13(lean_object* v_00_u03b2_807_, lean_object* v_x_808_, lean_object* v_x_809_, lean_object* v_x_810_, lean_object* v_x_811_){
_start:
{
lean_object* v___x_812_; 
v___x_812_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8_spec__11_spec__13___redArg(v_x_808_, v_x_809_, v_x_810_, v_x_811_);
return v___x_812_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__1___redArg(lean_object* v_m_813_){
_start:
{
uint8_t v_stage_u2081_814_; 
v_stage_u2081_814_ = lean_ctor_get_uint8(v_m_813_, sizeof(void*)*2);
if (v_stage_u2081_814_ == 0)
{
return v_m_813_;
}
else
{
lean_object* v_map_u2081_815_; lean_object* v_map_u2082_816_; lean_object* v___x_818_; uint8_t v_isShared_819_; uint8_t v_isSharedCheck_824_; 
v_map_u2081_815_ = lean_ctor_get(v_m_813_, 0);
v_map_u2082_816_ = lean_ctor_get(v_m_813_, 1);
v_isSharedCheck_824_ = !lean_is_exclusive(v_m_813_);
if (v_isSharedCheck_824_ == 0)
{
v___x_818_ = v_m_813_;
v_isShared_819_ = v_isSharedCheck_824_;
goto v_resetjp_817_;
}
else
{
lean_inc(v_map_u2082_816_);
lean_inc(v_map_u2081_815_);
lean_dec(v_m_813_);
v___x_818_ = lean_box(0);
v_isShared_819_ = v_isSharedCheck_824_;
goto v_resetjp_817_;
}
v_resetjp_817_:
{
uint8_t v___x_820_; lean_object* v___x_822_; 
v___x_820_ = 0;
if (v_isShared_819_ == 0)
{
v___x_822_ = v___x_818_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v_map_u2081_815_);
lean_ctor_set(v_reuseFailAlloc_823_, 1, v_map_u2082_816_);
v___x_822_ = v_reuseFailAlloc_823_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
lean_ctor_set_uint8(v___x_822_, sizeof(void*)*2, v___x_820_);
return v___x_822_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__1(lean_object* v_00_u03b2_825_, lean_object* v_m_826_){
_start:
{
lean_object* v___x_827_; 
v___x_827_ = l_Lean_SMap_switch___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__1___redArg(v_m_826_);
return v___x_827_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn___lam__0_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(lean_object* v_es_828_){
_start:
{
lean_object* v___x_829_; 
v___x_829_ = lean_array_mk(v_es_828_);
return v___x_829_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_as_830_, size_t v_i_831_, size_t v_stop_832_, lean_object* v_b_833_){
_start:
{
uint8_t v___x_834_; 
v___x_834_ = lean_usize_dec_eq(v_i_831_, v_stop_832_);
if (v___x_834_ == 0)
{
lean_object* v___x_835_; lean_object* v___x_836_; size_t v___x_837_; size_t v___x_838_; 
v___x_835_ = lean_array_uget_borrowed(v_as_830_, v_i_831_);
lean_inc(v___x_835_);
v___x_836_ = l_Lean_addAliasEntry(v_b_833_, v___x_835_);
v___x_837_ = ((size_t)1ULL);
v___x_838_ = lean_usize_add(v_i_831_, v___x_837_);
v_i_831_ = v___x_838_;
v_b_833_ = v___x_836_;
goto _start;
}
else
{
return v_b_833_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_as_840_, lean_object* v_i_841_, lean_object* v_stop_842_, lean_object* v_b_843_){
_start:
{
size_t v_i_boxed_844_; size_t v_stop_boxed_845_; lean_object* v_res_846_; 
v_i_boxed_844_ = lean_unbox_usize(v_i_841_);
lean_dec(v_i_841_);
v_stop_boxed_845_ = lean_unbox_usize(v_stop_842_);
lean_dec(v_stop_842_);
v_res_846_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__0(v_as_840_, v_i_boxed_844_, v_stop_boxed_845_, v_b_843_);
lean_dec_ref(v_as_840_);
return v_res_846_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_as_847_, size_t v_i_848_, size_t v_stop_849_, lean_object* v_b_850_){
_start:
{
lean_object* v___y_852_; uint8_t v___x_856_; 
v___x_856_ = lean_usize_dec_eq(v_i_848_, v_stop_849_);
if (v___x_856_ == 0)
{
lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; uint8_t v___x_860_; 
v___x_857_ = lean_array_uget_borrowed(v_as_847_, v_i_848_);
v___x_858_ = lean_unsigned_to_nat(0u);
v___x_859_ = lean_array_get_size(v___x_857_);
v___x_860_ = lean_nat_dec_lt(v___x_858_, v___x_859_);
if (v___x_860_ == 0)
{
v___y_852_ = v_b_850_;
goto v___jp_851_;
}
else
{
uint8_t v___x_861_; 
v___x_861_ = lean_nat_dec_le(v___x_859_, v___x_859_);
if (v___x_861_ == 0)
{
if (v___x_860_ == 0)
{
v___y_852_ = v_b_850_;
goto v___jp_851_;
}
else
{
size_t v___x_862_; size_t v___x_863_; lean_object* v___x_864_; 
v___x_862_ = ((size_t)0ULL);
v___x_863_ = lean_usize_of_nat(v___x_859_);
v___x_864_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__0(v___x_857_, v___x_862_, v___x_863_, v_b_850_);
v___y_852_ = v___x_864_;
goto v___jp_851_;
}
}
else
{
size_t v___x_865_; size_t v___x_866_; lean_object* v___x_867_; 
v___x_865_ = ((size_t)0ULL);
v___x_866_ = lean_usize_of_nat(v___x_859_);
v___x_867_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__0(v___x_857_, v___x_865_, v___x_866_, v_b_850_);
v___y_852_ = v___x_867_;
goto v___jp_851_;
}
}
}
else
{
return v_b_850_;
}
v___jp_851_:
{
size_t v___x_853_; size_t v___x_854_; 
v___x_853_ = ((size_t)1ULL);
v___x_854_ = lean_usize_add(v_i_848_, v___x_853_);
v_i_848_ = v___x_854_;
v_b_850_ = v___y_852_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object* v_as_868_, lean_object* v_i_869_, lean_object* v_stop_870_, lean_object* v_b_871_){
_start:
{
size_t v_i_boxed_872_; size_t v_stop_boxed_873_; lean_object* v_res_874_; 
v_i_boxed_872_ = lean_unbox_usize(v_i_869_);
lean_dec(v_i_869_);
v_stop_boxed_873_ = lean_unbox_usize(v_stop_870_);
lean_dec(v_stop_870_);
v_res_874_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__1(v_as_868_, v_i_boxed_872_, v_stop_boxed_873_, v_b_871_);
lean_dec_ref(v_as_868_);
return v_res_874_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0(lean_object* v_initState_875_, lean_object* v_as_876_){
_start:
{
lean_object* v___x_877_; lean_object* v___x_878_; uint8_t v___x_879_; 
v___x_877_ = lean_unsigned_to_nat(0u);
v___x_878_ = lean_array_get_size(v_as_876_);
v___x_879_ = lean_nat_dec_lt(v___x_877_, v___x_878_);
if (v___x_879_ == 0)
{
return v_initState_875_;
}
else
{
uint8_t v___x_880_; 
v___x_880_ = lean_nat_dec_le(v___x_878_, v___x_878_);
if (v___x_880_ == 0)
{
if (v___x_879_ == 0)
{
return v_initState_875_;
}
else
{
size_t v___x_881_; size_t v___x_882_; lean_object* v___x_883_; 
v___x_881_ = ((size_t)0ULL);
v___x_882_ = lean_usize_of_nat(v___x_878_);
v___x_883_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__1(v_as_876_, v___x_881_, v___x_882_, v_initState_875_);
return v___x_883_;
}
}
else
{
size_t v___x_884_; size_t v___x_885_; lean_object* v___x_886_; 
v___x_884_ = ((size_t)0ULL);
v___x_885_ = lean_usize_of_nat(v___x_878_);
v___x_886_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__1(v_as_876_, v___x_884_, v___x_885_, v_initState_875_);
return v___x_886_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0___boxed(lean_object* v_initState_887_, lean_object* v_as_888_){
_start:
{
lean_object* v_res_889_; 
v_res_889_ = l_Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0(v_initState_887_, v_as_888_);
lean_dec_ref(v_as_888_);
return v_res_889_;
}
}
static lean_object* _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(void){
_start:
{
lean_object* v_cellCount_890_; lean_object* v___x_891_; 
v_cellCount_890_ = lean_unsigned_to_nat(16u);
v___x_891_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_890_);
return v___x_891_;
}
}
static lean_object* _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(void){
_start:
{
lean_object* v_cellCount_892_; lean_object* v___x_893_; 
v_cellCount_892_ = lean_unsigned_to_nat(16u);
v___x_893_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_892_);
return v___x_893_;
}
}
static lean_object* _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; 
v___x_894_ = lean_obj_once(&l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_, &l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__once, _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_);
v___x_895_ = lean_obj_once(&l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_, &l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__once, _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_);
v___x_896_ = lean_unsigned_to_nat(0u);
v___x_897_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_897_, 0, v___x_896_);
lean_ctor_set(v___x_897_, 1, v___x_895_);
lean_ctor_set(v___x_897_, 2, v___x_894_);
return v___x_897_;
}
}
static lean_object* _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_898_; 
v___x_898_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_898_;
}
}
static lean_object* _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__4_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_899_; lean_object* v___x_900_; 
v___x_899_ = lean_obj_once(&l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_, &l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__once, _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_);
v___x_900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_900_, 0, v___x_899_);
return v___x_900_;
}
}
static lean_object* _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__5_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_901_; lean_object* v___x_902_; uint8_t v___x_903_; lean_object* v___x_904_; 
v___x_901_ = lean_obj_once(&l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__4_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_, &l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__4_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__once, _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__4_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_);
v___x_902_ = lean_obj_once(&l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_, &l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__once, _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_);
v___x_903_ = 1;
v___x_904_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_904_, 0, v___x_902_);
lean_ctor_set(v___x_904_, 1, v___x_901_);
lean_ctor_set_uint8(v___x_904_, sizeof(void*)*2, v___x_903_);
return v___x_904_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn___lam__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(lean_object* v_es_905_){
_start:
{
lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; 
v___x_906_ = lean_obj_once(&l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__5_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_, &l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__5_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__once, _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__5_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_);
v___x_907_ = l_Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0(v___x_906_, v_es_905_);
v___x_908_ = l_Lean_SMap_switch___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__1___redArg(v___x_907_);
return v___x_908_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn___lam__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2____boxed(lean_object* v_es_909_){
_start:
{
lean_object* v_res_910_; 
v_res_910_ = l___private_Lean_ResolveName_0__Lean_initFn___lam__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(v_es_909_);
lean_dec_ref(v_es_909_);
return v_res_910_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_927_; lean_object* v___x_928_; 
v___x_927_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_initFn___closed__6_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_));
v___x_928_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_927_);
return v___x_928_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2____boxed(lean_object* v_a_929_){
_start:
{
lean_object* v_res_930_; 
v_res_930_ = l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_();
return v_res_930_;
}
}
LEAN_EXPORT lean_object* l_Lean_addAlias(lean_object* v_env_931_, lean_object* v_a_932_, lean_object* v_e_933_){
_start:
{
lean_object* v___x_934_; lean_object* v_toEnvExtension_935_; lean_object* v_asyncMode_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; 
v___x_934_ = l_Lean_aliasExtension;
v_toEnvExtension_935_ = lean_ctor_get(v___x_934_, 0);
v_asyncMode_936_ = lean_ctor_get(v_toEnvExtension_935_, 2);
v___x_937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_937_, 0, v_a_932_);
lean_ctor_set(v___x_937_, 1, v_e_933_);
v___x_938_ = lean_box(0);
v___x_939_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_934_, v_env_931_, v___x_937_, v_asyncMode_936_, v___x_938_);
return v___x_939_;
}
}
static lean_object* _init_l_Lean_getAliasState___closed__2(void){
_start:
{
lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; 
v___x_942_ = ((lean_object*)(l_Lean_getAliasState___closed__1));
v___x_943_ = ((lean_object*)(l_Lean_getAliasState___closed__0));
v___x_944_ = l_Lean_SMap_instInhabited(lean_box(0), lean_box(0), v___x_943_, v___x_942_);
return v___x_944_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAliasState(lean_object* v_env_945_){
_start:
{
lean_object* v___x_946_; lean_object* v_toEnvExtension_947_; lean_object* v_asyncMode_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; 
v___x_946_ = l_Lean_aliasExtension;
v_toEnvExtension_947_ = lean_ctor_get(v___x_946_, 0);
v_asyncMode_948_ = lean_ctor_get(v_toEnvExtension_947_, 2);
v___x_949_ = lean_obj_once(&l_Lean_getAliasState___closed__2, &l_Lean_getAliasState___closed__2_once, _init_l_Lean_getAliasState___closed__2);
v___x_950_ = lean_box(0);
v___x_951_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_949_, v___x_946_, v_env_945_, v_asyncMode_948_, v___x_950_);
return v___x_951_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_getAliases_spec__0(lean_object* v_env_952_, uint8_t v_skipProtected_953_, lean_object* v_a_954_, lean_object* v_a_955_){
_start:
{
if (lean_obj_tag(v_a_954_) == 0)
{
lean_object* v___x_956_; 
lean_dec_ref(v_env_952_);
v___x_956_ = l_List_reverse___redArg(v_a_955_);
return v___x_956_;
}
else
{
lean_object* v_head_957_; lean_object* v_tail_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_969_; 
v_head_957_ = lean_ctor_get(v_a_954_, 0);
v_tail_958_ = lean_ctor_get(v_a_954_, 1);
v_isSharedCheck_969_ = !lean_is_exclusive(v_a_954_);
if (v_isSharedCheck_969_ == 0)
{
v___x_960_ = v_a_954_;
v_isShared_961_ = v_isSharedCheck_969_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_tail_958_);
lean_inc(v_head_957_);
lean_dec(v_a_954_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_969_;
goto v_resetjp_959_;
}
v_resetjp_959_:
{
uint8_t v___x_962_; 
lean_inc(v_head_957_);
lean_inc_ref(v_env_952_);
v___x_962_ = l_Lean_isProtected(v_env_952_, v_head_957_);
if (v___x_962_ == 0)
{
if (v_skipProtected_953_ == 0)
{
lean_del_object(v___x_960_);
lean_dec(v_head_957_);
v_a_954_ = v_tail_958_;
goto _start;
}
else
{
lean_object* v___x_965_; 
if (v_isShared_961_ == 0)
{
lean_ctor_set(v___x_960_, 1, v_a_955_);
v___x_965_ = v___x_960_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v_head_957_);
lean_ctor_set(v_reuseFailAlloc_967_, 1, v_a_955_);
v___x_965_ = v_reuseFailAlloc_967_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
v_a_954_ = v_tail_958_;
v_a_955_ = v___x_965_;
goto _start;
}
}
}
else
{
lean_del_object(v___x_960_);
lean_dec(v_head_957_);
v_a_954_ = v_tail_958_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_getAliases_spec__0___boxed(lean_object* v_env_970_, lean_object* v_skipProtected_971_, lean_object* v_a_972_, lean_object* v_a_973_){
_start:
{
uint8_t v_skipProtected_boxed_974_; lean_object* v_res_975_; 
v_skipProtected_boxed_974_ = lean_unbox(v_skipProtected_971_);
v_res_975_ = l_List_filterTR_loop___at___00Lean_getAliases_spec__0(v_env_970_, v_skipProtected_boxed_974_, v_a_972_, v_a_973_);
return v_res_975_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAliases(lean_object* v_env_976_, lean_object* v_a_977_, uint8_t v_skipProtected_978_){
_start:
{
lean_object* v___x_979_; lean_object* v_toEnvExtension_980_; lean_object* v_asyncMode_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; 
v___x_979_ = l_Lean_aliasExtension;
v_toEnvExtension_980_ = lean_ctor_get(v___x_979_, 0);
v_asyncMode_981_ = lean_ctor_get(v_toEnvExtension_980_, 2);
v___x_982_ = lean_obj_once(&l_Lean_getAliasState___closed__2, &l_Lean_getAliasState___closed__2_once, _init_l_Lean_getAliasState___closed__2);
v___x_983_ = lean_box(0);
lean_inc_ref(v_env_976_);
v___x_984_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_982_, v___x_979_, v_env_976_, v_asyncMode_981_, v___x_983_);
v___x_985_ = l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0___redArg(v___x_984_, v_a_977_);
lean_dec(v___x_984_);
if (lean_obj_tag(v___x_985_) == 0)
{
lean_object* v___x_986_; 
lean_dec_ref(v_env_976_);
v___x_986_ = lean_box(0);
return v___x_986_;
}
else
{
if (v_skipProtected_978_ == 0)
{
lean_object* v_val_987_; 
lean_dec_ref(v_env_976_);
v_val_987_ = lean_ctor_get(v___x_985_, 0);
lean_inc(v_val_987_);
lean_dec_ref_known(v___x_985_, 1);
return v_val_987_;
}
else
{
lean_object* v_val_988_; lean_object* v___x_989_; lean_object* v___x_990_; 
v_val_988_ = lean_ctor_get(v___x_985_, 0);
lean_inc(v_val_988_);
lean_dec_ref_known(v___x_985_, 1);
v___x_989_ = lean_box(0);
v___x_990_ = l_List_filterTR_loop___at___00Lean_getAliases_spec__0(v_env_976_, v_skipProtected_978_, v_val_988_, v___x_989_);
return v___x_990_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getAliases___boxed(lean_object* v_env_991_, lean_object* v_a_992_, lean_object* v_skipProtected_993_){
_start:
{
uint8_t v_skipProtected_boxed_994_; lean_object* v_res_995_; 
v_skipProtected_boxed_994_ = lean_unbox(v_skipProtected_993_);
v_res_995_ = l_Lean_getAliases(v_env_991_, v_a_992_, v_skipProtected_boxed_994_);
lean_dec(v_a_992_);
return v_res_995_;
}
}
LEAN_EXPORT lean_object* l_Lean_getRevAliases___lam__0(lean_object* v_e_996_, lean_object* v_as_997_, lean_object* v_a_998_, lean_object* v_es_999_){
_start:
{
uint8_t v___x_1000_; 
v___x_1000_ = l_List_elem___at___00Lean_addAliasEntry_spec__2(v_e_996_, v_es_999_);
if (v___x_1000_ == 0)
{
lean_dec(v_a_998_);
return v_as_997_;
}
else
{
lean_object* v___x_1001_; 
v___x_1001_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1001_, 0, v_a_998_);
lean_ctor_set(v___x_1001_, 1, v_as_997_);
return v___x_1001_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getRevAliases___lam__0___boxed(lean_object* v_e_1002_, lean_object* v_as_1003_, lean_object* v_a_1004_, lean_object* v_es_1005_){
_start:
{
lean_object* v_res_1006_; 
v_res_1006_ = l_Lean_getRevAliases___lam__0(v_e_1002_, v_as_1003_, v_a_1004_, v_es_1005_);
lean_dec(v_es_1005_);
lean_dec(v_e_1002_);
return v_res_1006_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__0_spec__1___redArg(lean_object* v_f_1007_, lean_object* v_b_1008_, lean_object* v_acc_1009_, lean_object* v_i_1010_){
_start:
{
lean_object* v_keyArray_1015_; lean_object* v_valueArray_1016_; lean_object* v___x_1017_; uint8_t v___x_1018_; 
v_keyArray_1015_ = lean_ctor_get(v_b_1008_, 1);
v_valueArray_1016_ = lean_ctor_get(v_b_1008_, 2);
v___x_1017_ = lean_array_get_size(v_keyArray_1015_);
v___x_1018_ = lean_nat_dec_lt(v_i_1010_, v___x_1017_);
if (v___x_1018_ == 0)
{
lean_dec(v_i_1010_);
lean_dec(v_f_1007_);
return v_acc_1009_;
}
else
{
lean_object* v___x_1019_; uint8_t v_isSome_1020_; 
v___x_1019_ = lean_array_fget_borrowed(v_keyArray_1015_, v_i_1010_);
v_isSome_1020_ = lean_noption_is_some(v___x_1019_);
if (v_isSome_1020_ == 0)
{
goto v___jp_1011_;
}
else
{
lean_object* v___x_1021_; uint8_t v_isSome_1022_; 
v___x_1021_ = lean_array_fget_borrowed(v_valueArray_1016_, v_i_1010_);
v_isSome_1022_ = lean_noption_is_some(v___x_1021_);
if (v_isSome_1022_ == 0)
{
goto v___jp_1011_;
}
else
{
lean_object* v_val_1023_; lean_object* v_val_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; 
lean_inc(v___x_1019_);
v_val_1023_ = lean_noption_get(v___x_1019_);
lean_inc(v___x_1021_);
v_val_1024_ = lean_noption_get(v___x_1021_);
lean_inc(v_f_1007_);
v___x_1025_ = lean_apply_3(v_f_1007_, v_acc_1009_, v_val_1023_, v_val_1024_);
v___x_1026_ = lean_unsigned_to_nat(1u);
v___x_1027_ = lean_nat_add(v_i_1010_, v___x_1026_);
lean_dec(v_i_1010_);
v_acc_1009_ = v___x_1025_;
v_i_1010_ = v___x_1027_;
goto _start;
}
}
}
v___jp_1011_:
{
lean_object* v___x_1012_; lean_object* v___x_1013_; 
v___x_1012_ = lean_unsigned_to_nat(1u);
v___x_1013_ = lean_nat_add(v_i_1010_, v___x_1012_);
lean_dec(v_i_1010_);
v_i_1010_ = v___x_1013_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_f_1029_, lean_object* v_b_1030_, lean_object* v_acc_1031_, lean_object* v_i_1032_){
_start:
{
lean_object* v_res_1033_; 
v_res_1033_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__0_spec__1___redArg(v_f_1029_, v_b_1030_, v_acc_1031_, v_i_1032_);
lean_dec_ref(v_b_1030_);
return v_res_1033_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__0___redArg(lean_object* v_f_1034_, lean_object* v_init_1035_, lean_object* v_b_1036_){
_start:
{
lean_object* v___x_1037_; lean_object* v___x_1038_; 
v___x_1037_ = lean_unsigned_to_nat(0u);
v___x_1038_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__0_spec__1___redArg(v_f_1034_, v_b_1036_, v_init_1035_, v___x_1037_);
return v___x_1038_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__0___redArg___boxed(lean_object* v_f_1039_, lean_object* v_init_1040_, lean_object* v_b_1041_){
_start:
{
lean_object* v_res_1042_; 
v_res_1042_ = l_Std_DHashMap_Raw_foldM___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__0___redArg(v_f_1039_, v_init_1040_, v_b_1041_);
lean_dec_ref(v_b_1041_);
return v_res_1042_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__3_spec__4_spec__6___redArg(lean_object* v_f_1043_, lean_object* v_keys_1044_, lean_object* v_vals_1045_, lean_object* v_i_1046_, lean_object* v_acc_1047_){
_start:
{
lean_object* v___x_1048_; uint8_t v___x_1049_; 
v___x_1048_ = lean_array_get_size(v_keys_1044_);
v___x_1049_ = lean_nat_dec_lt(v_i_1046_, v___x_1048_);
if (v___x_1049_ == 0)
{
lean_dec(v_i_1046_);
lean_dec(v_f_1043_);
return v_acc_1047_;
}
else
{
lean_object* v_k_1050_; lean_object* v_v_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; 
v_k_1050_ = lean_array_fget_borrowed(v_keys_1044_, v_i_1046_);
v_v_1051_ = lean_array_fget_borrowed(v_vals_1045_, v_i_1046_);
lean_inc(v_f_1043_);
lean_inc(v_v_1051_);
lean_inc(v_k_1050_);
v___x_1052_ = lean_apply_3(v_f_1043_, v_acc_1047_, v_k_1050_, v_v_1051_);
v___x_1053_ = lean_unsigned_to_nat(1u);
v___x_1054_ = lean_nat_add(v_i_1046_, v___x_1053_);
lean_dec(v_i_1046_);
v_i_1046_ = v___x_1054_;
v_acc_1047_ = v___x_1052_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__3_spec__4_spec__6___redArg___boxed(lean_object* v_f_1056_, lean_object* v_keys_1057_, lean_object* v_vals_1058_, lean_object* v_i_1059_, lean_object* v_acc_1060_){
_start:
{
lean_object* v_res_1061_; 
v_res_1061_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__3_spec__4_spec__6___redArg(v_f_1056_, v_keys_1057_, v_vals_1058_, v_i_1059_, v_acc_1060_);
lean_dec_ref(v_vals_1058_);
lean_dec_ref(v_keys_1057_);
return v_res_1061_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__3_spec__4___redArg(lean_object* v_f_1062_, lean_object* v_x_1063_, lean_object* v_x_1064_){
_start:
{
if (lean_obj_tag(v_x_1063_) == 0)
{
lean_object* v_es_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; uint8_t v___x_1068_; 
v_es_1065_ = lean_ctor_get(v_x_1063_, 0);
v___x_1066_ = lean_unsigned_to_nat(0u);
v___x_1067_ = lean_array_get_size(v_es_1065_);
v___x_1068_ = lean_nat_dec_lt(v___x_1066_, v___x_1067_);
if (v___x_1068_ == 0)
{
lean_dec(v_f_1062_);
return v_x_1064_;
}
else
{
uint8_t v___x_1069_; 
v___x_1069_ = lean_nat_dec_le(v___x_1067_, v___x_1067_);
if (v___x_1069_ == 0)
{
if (v___x_1068_ == 0)
{
lean_dec(v_f_1062_);
return v_x_1064_;
}
else
{
size_t v___x_1070_; size_t v___x_1071_; lean_object* v___x_1072_; 
v___x_1070_ = ((size_t)0ULL);
v___x_1071_ = lean_usize_of_nat(v___x_1067_);
v___x_1072_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_f_1062_, v_es_1065_, v___x_1070_, v___x_1071_, v_x_1064_);
return v___x_1072_;
}
}
else
{
size_t v___x_1073_; size_t v___x_1074_; lean_object* v___x_1075_; 
v___x_1073_ = ((size_t)0ULL);
v___x_1074_ = lean_usize_of_nat(v___x_1067_);
v___x_1075_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_f_1062_, v_es_1065_, v___x_1073_, v___x_1074_, v_x_1064_);
return v___x_1075_;
}
}
}
else
{
lean_object* v_ks_1076_; lean_object* v_vs_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; 
v_ks_1076_ = lean_ctor_get(v_x_1063_, 0);
v_vs_1077_ = lean_ctor_get(v_x_1063_, 1);
v___x_1078_ = lean_unsigned_to_nat(0u);
v___x_1079_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__3_spec__4_spec__6___redArg(v_f_1062_, v_ks_1076_, v_vs_1077_, v___x_1078_, v_x_1064_);
return v___x_1079_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_f_1080_, lean_object* v_as_1081_, size_t v_i_1082_, size_t v_stop_1083_, lean_object* v_b_1084_){
_start:
{
lean_object* v___y_1086_; uint8_t v___x_1090_; 
v___x_1090_ = lean_usize_dec_eq(v_i_1082_, v_stop_1083_);
if (v___x_1090_ == 0)
{
lean_object* v___x_1091_; 
v___x_1091_ = lean_array_uget_borrowed(v_as_1081_, v_i_1082_);
switch(lean_obj_tag(v___x_1091_))
{
case 0:
{
lean_object* v_key_1092_; lean_object* v_val_1093_; lean_object* v___x_1094_; 
v_key_1092_ = lean_ctor_get(v___x_1091_, 0);
v_val_1093_ = lean_ctor_get(v___x_1091_, 1);
lean_inc(v_f_1080_);
lean_inc(v_val_1093_);
lean_inc(v_key_1092_);
v___x_1094_ = lean_apply_3(v_f_1080_, v_b_1084_, v_key_1092_, v_val_1093_);
v___y_1086_ = v___x_1094_;
goto v___jp_1085_;
}
case 1:
{
lean_object* v_node_1095_; lean_object* v___x_1096_; 
v_node_1095_ = lean_ctor_get(v___x_1091_, 0);
lean_inc(v_f_1080_);
v___x_1096_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__3_spec__4___redArg(v_f_1080_, v_node_1095_, v_b_1084_);
v___y_1086_ = v___x_1096_;
goto v___jp_1085_;
}
default: 
{
v___y_1086_ = v_b_1084_;
goto v___jp_1085_;
}
}
}
else
{
lean_dec(v_f_1080_);
return v_b_1084_;
}
v___jp_1085_:
{
size_t v___x_1087_; size_t v___x_1088_; 
v___x_1087_ = ((size_t)1ULL);
v___x_1088_ = lean_usize_add(v_i_1082_, v___x_1087_);
v_i_1082_ = v___x_1088_;
v_b_1084_ = v___y_1086_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_f_1097_, lean_object* v_as_1098_, lean_object* v_i_1099_, lean_object* v_stop_1100_, lean_object* v_b_1101_){
_start:
{
size_t v_i_boxed_1102_; size_t v_stop_boxed_1103_; lean_object* v_res_1104_; 
v_i_boxed_1102_ = lean_unbox_usize(v_i_1099_);
lean_dec(v_i_1099_);
v_stop_boxed_1103_ = lean_unbox_usize(v_stop_1100_);
lean_dec(v_stop_1100_);
v_res_1104_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_f_1097_, v_as_1098_, v_i_boxed_1102_, v_stop_boxed_1103_, v_b_1101_);
lean_dec_ref(v_as_1098_);
return v_res_1104_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__3_spec__4___redArg___boxed(lean_object* v_f_1105_, lean_object* v_x_1106_, lean_object* v_x_1107_){
_start:
{
lean_object* v_res_1108_; 
v_res_1108_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__3_spec__4___redArg(v_f_1105_, v_x_1106_, v_x_1107_);
lean_dec_ref(v_x_1106_);
return v_res_1108_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg___lam__0(lean_object* v_f_1109_, lean_object* v_x1_1110_, lean_object* v_x2_1111_, lean_object* v_x3_1112_){
_start:
{
lean_object* v___x_1113_; 
v___x_1113_ = lean_apply_3(v_f_1109_, v_x1_1110_, v_x2_1111_, v_x3_1112_);
return v___x_1113_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg(lean_object* v_map_1114_, lean_object* v_f_1115_, lean_object* v_init_1116_){
_start:
{
lean_object* v___f_1117_; lean_object* v___x_1118_; 
v___f_1117_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1117_, 0, v_f_1115_);
v___x_1118_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__3_spec__4___redArg(v___f_1117_, v_map_1114_, v_init_1116_);
return v___x_1118_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg___boxed(lean_object* v_map_1119_, lean_object* v_f_1120_, lean_object* v_init_1121_){
_start:
{
lean_object* v_res_1122_; 
v_res_1122_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg(v_map_1119_, v_f_1120_, v_init_1121_);
lean_dec_ref(v_map_1119_);
return v_res_1122_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0___redArg(lean_object* v_f_1123_, lean_object* v_init_1124_, lean_object* v_m_1125_){
_start:
{
lean_object* v_map_u2081_1126_; lean_object* v_map_u2082_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; 
v_map_u2081_1126_ = lean_ctor_get(v_m_1125_, 0);
v_map_u2082_1127_ = lean_ctor_get(v_m_1125_, 1);
lean_inc(v_f_1123_);
v___x_1128_ = l_Std_DHashMap_Raw_foldM___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__0___redArg(v_f_1123_, v_init_1124_, v_map_u2081_1126_);
v___x_1129_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg(v_map_u2082_1127_, v_f_1123_, v___x_1128_);
return v___x_1129_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0___redArg___boxed(lean_object* v_f_1130_, lean_object* v_init_1131_, lean_object* v_m_1132_){
_start:
{
lean_object* v_res_1133_; 
v_res_1133_ = l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0___redArg(v_f_1130_, v_init_1131_, v_m_1132_);
lean_dec_ref(v_m_1132_);
return v_res_1133_;
}
}
LEAN_EXPORT lean_object* l_Lean_getRevAliases(lean_object* v_env_1134_, lean_object* v_e_1135_){
_start:
{
lean_object* v___x_1136_; lean_object* v_toEnvExtension_1137_; lean_object* v_asyncMode_1138_; lean_object* v___f_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; 
v___x_1136_ = l_Lean_aliasExtension;
v_toEnvExtension_1137_ = lean_ctor_get(v___x_1136_, 0);
v_asyncMode_1138_ = lean_ctor_get(v_toEnvExtension_1137_, 2);
v___f_1139_ = lean_alloc_closure((void*)(l_Lean_getRevAliases___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1139_, 0, v_e_1135_);
v___x_1140_ = lean_obj_once(&l_Lean_getAliasState___closed__2, &l_Lean_getAliasState___closed__2_once, _init_l_Lean_getAliasState___closed__2);
v___x_1141_ = lean_box(0);
v___x_1142_ = lean_box(0);
v___x_1143_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1140_, v___x_1136_, v_env_1134_, v_asyncMode_1138_, v___x_1142_);
v___x_1144_ = l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0___redArg(v___f_1139_, v___x_1141_, v___x_1143_);
lean_dec(v___x_1143_);
return v___x_1144_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0(lean_object* v_00_u03b2_1145_, lean_object* v_00_u03c3_1146_, lean_object* v_f_1147_, lean_object* v_init_1148_, lean_object* v_m_1149_){
_start:
{
lean_object* v___x_1150_; 
v___x_1150_ = l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0___redArg(v_f_1147_, v_init_1148_, v_m_1149_);
return v___x_1150_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0___boxed(lean_object* v_00_u03b2_1151_, lean_object* v_00_u03c3_1152_, lean_object* v_f_1153_, lean_object* v_init_1154_, lean_object* v_m_1155_){
_start:
{
lean_object* v_res_1156_; 
v_res_1156_ = l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0(v_00_u03b2_1151_, v_00_u03c3_1152_, v_f_1153_, v_init_1154_, v_m_1155_);
lean_dec_ref(v_m_1155_);
return v_res_1156_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__0(lean_object* v_00_u03b2_1157_, lean_object* v_00_u03c3_1158_, lean_object* v_f_1159_, lean_object* v_init_1160_, lean_object* v_b_1161_){
_start:
{
lean_object* v___x_1162_; 
v___x_1162_ = l_Std_DHashMap_Raw_foldM___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__0___redArg(v_f_1159_, v_init_1160_, v_b_1161_);
return v___x_1162_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1163_, lean_object* v_00_u03c3_1164_, lean_object* v_f_1165_, lean_object* v_init_1166_, lean_object* v_b_1167_){
_start:
{
lean_object* v_res_1168_; 
v_res_1168_ = l_Std_DHashMap_Raw_foldM___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__0(v_00_u03b2_1163_, v_00_u03c3_1164_, v_f_1165_, v_init_1166_, v_b_1167_);
lean_dec_ref(v_b_1167_);
return v_res_1168_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1(lean_object* v_00_u03c3_1169_, lean_object* v_00_u03b2_1170_, lean_object* v_map_1171_, lean_object* v_f_1172_, lean_object* v_init_1173_){
_start:
{
lean_object* v___x_1174_; 
v___x_1174_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg(v_map_1171_, v_f_1172_, v_init_1173_);
return v___x_1174_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___boxed(lean_object* v_00_u03c3_1175_, lean_object* v_00_u03b2_1176_, lean_object* v_map_1177_, lean_object* v_f_1178_, lean_object* v_init_1179_){
_start:
{
lean_object* v_res_1180_; 
v_res_1180_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1(v_00_u03c3_1175_, v_00_u03b2_1176_, v_map_1177_, v_f_1178_, v_init_1179_);
lean_dec_ref(v_map_1177_);
return v_res_1180_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_1181_, lean_object* v_00_u03c3_1182_, lean_object* v_f_1183_, lean_object* v_b_1184_, lean_object* v_acc_1185_, lean_object* v_i_1186_){
_start:
{
lean_object* v___x_1187_; 
v___x_1187_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__0_spec__1___redArg(v_f_1183_, v_b_1184_, v_acc_1185_, v_i_1186_);
return v___x_1187_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1188_, lean_object* v_00_u03c3_1189_, lean_object* v_f_1190_, lean_object* v_b_1191_, lean_object* v_acc_1192_, lean_object* v_i_1193_){
_start:
{
lean_object* v_res_1194_; 
v_res_1194_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__0_spec__1(v_00_u03b2_1188_, v_00_u03c3_1189_, v_f_1190_, v_b_1191_, v_acc_1192_, v_i_1193_);
lean_dec_ref(v_b_1191_);
return v_res_1194_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__3___redArg(lean_object* v_map_1195_, lean_object* v_f_1196_, lean_object* v_init_1197_){
_start:
{
lean_object* v___x_1198_; 
v___x_1198_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__3_spec__4___redArg(v_f_1196_, v_map_1195_, v_init_1197_);
return v___x_1198_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_map_1199_, lean_object* v_f_1200_, lean_object* v_init_1201_){
_start:
{
lean_object* v_res_1202_; 
v_res_1202_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__3___redArg(v_map_1199_, v_f_1200_, v_init_1201_);
lean_dec_ref(v_map_1199_);
return v_res_1202_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__3(lean_object* v_00_u03c3_1203_, lean_object* v_00_u03b2_1204_, lean_object* v_map_1205_, lean_object* v_f_1206_, lean_object* v_init_1207_){
_start:
{
lean_object* v___x_1208_; 
v___x_1208_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__3_spec__4___redArg(v_f_1206_, v_map_1205_, v_init_1207_);
return v___x_1208_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03c3_1209_, lean_object* v_00_u03b2_1210_, lean_object* v_map_1211_, lean_object* v_f_1212_, lean_object* v_init_1213_){
_start:
{
lean_object* v_res_1214_; 
v_res_1214_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__3(v_00_u03c3_1209_, v_00_u03b2_1210_, v_map_1211_, v_f_1212_, v_init_1213_);
lean_dec_ref(v_map_1211_);
return v_res_1214_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__3_spec__4(lean_object* v_00_u03c3_1215_, lean_object* v_00_u03b1_1216_, lean_object* v_00_u03b2_1217_, lean_object* v_f_1218_, lean_object* v_x_1219_, lean_object* v_x_1220_){
_start:
{
lean_object* v___x_1221_; 
v___x_1221_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__3_spec__4___redArg(v_f_1218_, v_x_1219_, v_x_1220_);
return v___x_1221_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__3_spec__4___boxed(lean_object* v_00_u03c3_1222_, lean_object* v_00_u03b1_1223_, lean_object* v_00_u03b2_1224_, lean_object* v_f_1225_, lean_object* v_x_1226_, lean_object* v_x_1227_){
_start:
{
lean_object* v_res_1228_; 
v_res_1228_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__3_spec__4(v_00_u03c3_1222_, v_00_u03b1_1223_, v_00_u03b2_1224_, v_f_1225_, v_x_1226_, v_x_1227_);
lean_dec_ref(v_x_1226_);
return v_res_1228_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__3_spec__4_spec__5(lean_object* v_00_u03b1_1229_, lean_object* v_00_u03b2_1230_, lean_object* v_00_u03c3_1231_, lean_object* v_f_1232_, lean_object* v_as_1233_, size_t v_i_1234_, size_t v_stop_1235_, lean_object* v_b_1236_){
_start:
{
lean_object* v___x_1237_; 
v___x_1237_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_f_1232_, v_as_1233_, v_i_1234_, v_stop_1235_, v_b_1236_);
return v___x_1237_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__3_spec__4_spec__5___boxed(lean_object* v_00_u03b1_1238_, lean_object* v_00_u03b2_1239_, lean_object* v_00_u03c3_1240_, lean_object* v_f_1241_, lean_object* v_as_1242_, lean_object* v_i_1243_, lean_object* v_stop_1244_, lean_object* v_b_1245_){
_start:
{
size_t v_i_boxed_1246_; size_t v_stop_boxed_1247_; lean_object* v_res_1248_; 
v_i_boxed_1246_ = lean_unbox_usize(v_i_1243_);
lean_dec(v_i_1243_);
v_stop_boxed_1247_ = lean_unbox_usize(v_stop_1244_);
lean_dec(v_stop_1244_);
v_res_1248_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__3_spec__4_spec__5(v_00_u03b1_1238_, v_00_u03b2_1239_, v_00_u03c3_1240_, v_f_1241_, v_as_1242_, v_i_boxed_1246_, v_stop_boxed_1247_, v_b_1245_);
lean_dec_ref(v_as_1242_);
return v_res_1248_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__3_spec__4_spec__6(lean_object* v_00_u03c3_1249_, lean_object* v_00_u03b1_1250_, lean_object* v_00_u03b2_1251_, lean_object* v_f_1252_, lean_object* v_keys_1253_, lean_object* v_vals_1254_, lean_object* v_heq_1255_, lean_object* v_i_1256_, lean_object* v_acc_1257_){
_start:
{
lean_object* v___x_1258_; 
v___x_1258_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__3_spec__4_spec__6___redArg(v_f_1252_, v_keys_1253_, v_vals_1254_, v_i_1256_, v_acc_1257_);
return v___x_1258_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__3_spec__4_spec__6___boxed(lean_object* v_00_u03c3_1259_, lean_object* v_00_u03b1_1260_, lean_object* v_00_u03b2_1261_, lean_object* v_f_1262_, lean_object* v_keys_1263_, lean_object* v_vals_1264_, lean_object* v_heq_1265_, lean_object* v_i_1266_, lean_object* v_acc_1267_){
_start:
{
lean_object* v_res_1268_; 
v_res_1268_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__3_spec__4_spec__6(v_00_u03c3_1259_, v_00_u03b1_1260_, v_00_u03b2_1261_, v_f_1262_, v_keys_1263_, v_vals_1264_, v_heq_1265_, v_i_1266_, v_acc_1267_);
lean_dec_ref(v_vals_1264_);
lean_dec_ref(v_keys_1263_);
return v_res_1268_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(lean_object* v_env_1269_, lean_object* v_declName_1270_){
_start:
{
uint8_t v___y_1272_; uint8_t v___x_1275_; 
v___x_1275_ = l_Lean_Environment_containsOnBranch(v_env_1269_, v_declName_1270_);
if (v___x_1275_ == 0)
{
uint8_t v___x_1276_; 
lean_inc(v_declName_1270_);
lean_inc_ref(v_env_1269_);
v___x_1276_ = lean_is_reserved_name(v_env_1269_, v_declName_1270_);
v___y_1272_ = v___x_1276_;
goto v___jp_1271_;
}
else
{
v___y_1272_ = v___x_1275_;
goto v___jp_1271_;
}
v___jp_1271_:
{
if (v___y_1272_ == 0)
{
uint8_t v___x_1273_; uint8_t v___x_1274_; 
v___x_1273_ = 1;
v___x_1274_ = l_Lean_Environment_contains(v_env_1269_, v_declName_1270_, v___x_1273_);
return v___x_1274_;
}
else
{
lean_dec(v_declName_1270_);
lean_dec_ref(v_env_1269_);
return v___y_1272_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved___boxed(lean_object* v_env_1277_, lean_object* v_declName_1278_){
_start:
{
uint8_t v_res_1279_; lean_object* v_r_1280_; 
v_res_1279_ = l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(v_env_1277_, v_declName_1278_);
v_r_1280_ = lean_box(v_res_1279_);
return v_r_1280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__spec__0(lean_object* v_name_1281_, lean_object* v_decl_1282_, lean_object* v_ref_1283_){
_start:
{
lean_object* v_defValue_1285_; lean_object* v_descr_1286_; lean_object* v_deprecation_x3f_1287_; lean_object* v___x_1288_; uint8_t v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; 
v_defValue_1285_ = lean_ctor_get(v_decl_1282_, 0);
v_descr_1286_ = lean_ctor_get(v_decl_1282_, 1);
v_deprecation_x3f_1287_ = lean_ctor_get(v_decl_1282_, 2);
v___x_1288_ = lean_alloc_ctor(1, 0, 1);
v___x_1289_ = lean_unbox(v_defValue_1285_);
lean_ctor_set_uint8(v___x_1288_, 0, v___x_1289_);
lean_inc(v_deprecation_x3f_1287_);
lean_inc_ref(v_descr_1286_);
lean_inc_n(v_name_1281_, 2);
v___x_1290_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1290_, 0, v_name_1281_);
lean_ctor_set(v___x_1290_, 1, v_ref_1283_);
lean_ctor_set(v___x_1290_, 2, v___x_1288_);
lean_ctor_set(v___x_1290_, 3, v_descr_1286_);
lean_ctor_set(v___x_1290_, 4, v_deprecation_x3f_1287_);
v___x_1291_ = lean_register_option(v_name_1281_, v___x_1290_);
if (lean_obj_tag(v___x_1291_) == 0)
{
lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1299_; 
v_isSharedCheck_1299_ = !lean_is_exclusive(v___x_1291_);
if (v_isSharedCheck_1299_ == 0)
{
lean_object* v_unused_1300_; 
v_unused_1300_ = lean_ctor_get(v___x_1291_, 0);
lean_dec(v_unused_1300_);
v___x_1293_ = v___x_1291_;
v_isShared_1294_ = v_isSharedCheck_1299_;
goto v_resetjp_1292_;
}
else
{
lean_dec(v___x_1291_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1299_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v___x_1295_; lean_object* v___x_1297_; 
lean_inc(v_defValue_1285_);
v___x_1295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1295_, 0, v_name_1281_);
lean_ctor_set(v___x_1295_, 1, v_defValue_1285_);
if (v_isShared_1294_ == 0)
{
lean_ctor_set(v___x_1293_, 0, v___x_1295_);
v___x_1297_ = v___x_1293_;
goto v_reusejp_1296_;
}
else
{
lean_object* v_reuseFailAlloc_1298_; 
v_reuseFailAlloc_1298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1298_, 0, v___x_1295_);
v___x_1297_ = v_reuseFailAlloc_1298_;
goto v_reusejp_1296_;
}
v_reusejp_1296_:
{
return v___x_1297_;
}
}
}
else
{
lean_object* v_a_1301_; lean_object* v___x_1303_; uint8_t v_isShared_1304_; uint8_t v_isSharedCheck_1308_; 
lean_dec(v_name_1281_);
v_a_1301_ = lean_ctor_get(v___x_1291_, 0);
v_isSharedCheck_1308_ = !lean_is_exclusive(v___x_1291_);
if (v_isSharedCheck_1308_ == 0)
{
v___x_1303_ = v___x_1291_;
v_isShared_1304_ = v_isSharedCheck_1308_;
goto v_resetjp_1302_;
}
else
{
lean_inc(v_a_1301_);
lean_dec(v___x_1291_);
v___x_1303_ = lean_box(0);
v_isShared_1304_ = v_isSharedCheck_1308_;
goto v_resetjp_1302_;
}
v_resetjp_1302_:
{
lean_object* v___x_1306_; 
if (v_isShared_1304_ == 0)
{
v___x_1306_ = v___x_1303_;
goto v_reusejp_1305_;
}
else
{
lean_object* v_reuseFailAlloc_1307_; 
v_reuseFailAlloc_1307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1307_, 0, v_a_1301_);
v___x_1306_ = v_reuseFailAlloc_1307_;
goto v_reusejp_1305_;
}
v_reusejp_1305_:
{
return v___x_1306_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_1309_, lean_object* v_decl_1310_, lean_object* v_ref_1311_, lean_object* v_a_1312_){
_start:
{
lean_object* v_res_1313_; 
v_res_1313_ = l_Lean_Option_register___at___00__private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__spec__0(v_name_1309_, v_decl_1310_, v_ref_1311_);
lean_dec_ref(v_decl_1310_);
return v_res_1313_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; 
v___x_1332_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__2_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_));
v___x_1333_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__4_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_));
v___x_1334_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__6_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_));
v___x_1335_ = l_Lean_Option_register___at___00__private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__spec__0(v___x_1332_, v___x_1333_, v___x_1334_);
return v___x_1335_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4____boxed(lean_object* v_a_1336_){
_start:
{
lean_object* v_res_1337_; 
v_res_1337_ = l___private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_();
return v_res_1337_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; 
v___x_1356_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__1_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4_));
v___x_1357_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__3_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4_));
v___x_1358_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__4_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4_));
v___x_1359_ = l_Lean_Option_register___at___00__private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__spec__0(v___x_1356_, v___x_1357_, v___x_1358_);
return v___x_1359_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4____boxed(lean_object* v_a_1360_){
_start:
{
lean_object* v_res_1361_; 
v_res_1361_ = l___private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4_();
return v_res_1361_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__1(lean_object* v_opts_1362_, lean_object* v_opt_1363_){
_start:
{
lean_object* v_name_1364_; lean_object* v_defValue_1365_; lean_object* v_map_1366_; lean_object* v___x_1367_; 
v_name_1364_ = lean_ctor_get(v_opt_1363_, 0);
v_defValue_1365_ = lean_ctor_get(v_opt_1363_, 1);
v_map_1366_ = lean_ctor_get(v_opts_1362_, 0);
v___x_1367_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1366_, v_name_1364_);
if (lean_obj_tag(v___x_1367_) == 0)
{
uint8_t v___x_1368_; 
v___x_1368_ = lean_unbox(v_defValue_1365_);
return v___x_1368_;
}
else
{
lean_object* v_val_1369_; 
v_val_1369_ = lean_ctor_get(v___x_1367_, 0);
lean_inc(v_val_1369_);
lean_dec_ref_known(v___x_1367_, 1);
if (lean_obj_tag(v_val_1369_) == 1)
{
uint8_t v_v_1370_; 
v_v_1370_ = lean_ctor_get_uint8(v_val_1369_, 0);
lean_dec_ref_known(v_val_1369_, 0);
return v_v_1370_;
}
else
{
uint8_t v___x_1371_; 
lean_dec(v_val_1369_);
v___x_1371_ = lean_unbox(v_defValue_1365_);
return v___x_1371_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__1___boxed(lean_object* v_opts_1372_, lean_object* v_opt_1373_){
_start:
{
uint8_t v_res_1374_; lean_object* v_r_1375_; 
v_res_1374_ = l_Lean_Option_get___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__1(v_opts_1372_, v_opt_1373_);
lean_dec_ref(v_opt_1373_);
lean_dec_ref(v_opts_1372_);
v_r_1375_ = lean_box(v_res_1374_);
return v_r_1375_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0(lean_object* v_declName_1379_, lean_object* v_env_1380_, lean_object* v_as_1381_, size_t v_sz_1382_, size_t v_i_1383_, lean_object* v_b_1384_){
_start:
{
uint8_t v___x_1385_; 
v___x_1385_ = lean_usize_dec_lt(v_i_1383_, v_sz_1382_);
if (v___x_1385_ == 0)
{
lean_dec_ref(v_env_1380_);
lean_dec(v_declName_1379_);
lean_inc_ref(v_b_1384_);
return v_b_1384_;
}
else
{
lean_object* v_a_1386_; lean_object* v_toImport_1387_; lean_object* v_module_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; uint8_t v___x_1391_; 
v_a_1386_ = lean_array_uget_borrowed(v_as_1381_, v_i_1383_);
v_toImport_1387_ = lean_ctor_get(v_a_1386_, 0);
v_module_1388_ = lean_ctor_get(v_toImport_1387_, 0);
v___x_1389_ = lean_box(0);
lean_inc(v_declName_1379_);
lean_inc(v_module_1388_);
v___x_1390_ = l_Lean_mkPrivateNameCore(v_module_1388_, v_declName_1379_);
lean_inc(v___x_1390_);
lean_inc_ref(v_env_1380_);
v___x_1391_ = l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(v_env_1380_, v___x_1390_);
if (v___x_1391_ == 0)
{
lean_object* v___x_1392_; size_t v___x_1393_; size_t v___x_1394_; 
lean_dec(v___x_1390_);
v___x_1392_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0___closed__0));
v___x_1393_ = ((size_t)1ULL);
v___x_1394_ = lean_usize_add(v_i_1383_, v___x_1393_);
v_i_1383_ = v___x_1394_;
v_b_1384_ = v___x_1392_;
goto _start;
}
else
{
lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; 
lean_dec_ref(v_env_1380_);
lean_dec(v_declName_1379_);
v___x_1396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1396_, 0, v___x_1390_);
v___x_1397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1397_, 0, v___x_1396_);
v___x_1398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1398_, 0, v___x_1397_);
lean_ctor_set(v___x_1398_, 1, v___x_1389_);
return v___x_1398_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0___boxed(lean_object* v_declName_1399_, lean_object* v_env_1400_, lean_object* v_as_1401_, lean_object* v_sz_1402_, lean_object* v_i_1403_, lean_object* v_b_1404_){
_start:
{
size_t v_sz_boxed_1405_; size_t v_i_boxed_1406_; lean_object* v_res_1407_; 
v_sz_boxed_1405_ = lean_unbox_usize(v_sz_1402_);
lean_dec(v_sz_1402_);
v_i_boxed_1406_ = lean_unbox_usize(v_i_1403_);
lean_dec(v_i_1403_);
v_res_1407_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0(v_declName_1399_, v_env_1400_, v_as_1401_, v_sz_boxed_1405_, v_i_boxed_1406_, v_b_1404_);
lean_dec_ref(v_b_1404_);
lean_dec_ref(v_as_1401_);
return v_res_1407_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName(lean_object* v_env_1408_, lean_object* v_opts_1409_, lean_object* v_declName_1410_){
_start:
{
uint8_t v_isExporting_1426_; 
v_isExporting_1426_ = lean_ctor_get_uint8(v_env_1408_, sizeof(void*)*8);
if (v_isExporting_1426_ == 0)
{
goto v___jp_1411_;
}
else
{
lean_object* v___x_1427_; uint8_t v___x_1428_; 
v___x_1427_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_1428_ = l_Lean_Option_get___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__1(v_opts_1409_, v___x_1427_);
if (v___x_1428_ == 0)
{
lean_object* v___x_1429_; 
lean_dec(v_declName_1410_);
lean_dec_ref(v_env_1408_);
v___x_1429_ = lean_box(0);
return v___x_1429_;
}
else
{
goto v___jp_1411_;
}
}
v___jp_1411_:
{
lean_object* v___x_1412_; uint8_t v___x_1413_; 
lean_inc(v_declName_1410_);
v___x_1412_ = l_Lean_mkPrivateName(v_env_1408_, v_declName_1410_);
lean_inc(v___x_1412_);
lean_inc_ref(v_env_1408_);
v___x_1413_ = l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(v_env_1408_, v___x_1412_);
if (v___x_1413_ == 0)
{
lean_object* v___x_1414_; uint8_t v_isModule_1415_; 
lean_dec(v___x_1412_);
v___x_1414_ = l_Lean_Environment_header(v_env_1408_);
v_isModule_1415_ = lean_ctor_get_uint8(v___x_1414_, sizeof(void*)*7 + 4);
if (v_isModule_1415_ == 0)
{
lean_object* v___x_1416_; 
lean_dec_ref(v___x_1414_);
lean_dec(v_declName_1410_);
lean_dec_ref(v_env_1408_);
v___x_1416_ = lean_box(0);
return v___x_1416_;
}
else
{
lean_object* v_importAllModules_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; size_t v_sz_1420_; size_t v___x_1421_; lean_object* v___x_1422_; lean_object* v_fst_1423_; 
v_importAllModules_1417_ = lean_ctor_get(v___x_1414_, 5);
lean_inc_ref(v_importAllModules_1417_);
lean_dec_ref(v___x_1414_);
v___x_1418_ = lean_box(0);
v___x_1419_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0___closed__0));
v_sz_1420_ = lean_array_size(v_importAllModules_1417_);
v___x_1421_ = ((size_t)0ULL);
v___x_1422_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0(v_declName_1410_, v_env_1408_, v_importAllModules_1417_, v_sz_1420_, v___x_1421_, v___x_1419_);
lean_dec_ref(v_importAllModules_1417_);
v_fst_1423_ = lean_ctor_get(v___x_1422_, 0);
lean_inc(v_fst_1423_);
lean_dec_ref(v___x_1422_);
if (lean_obj_tag(v_fst_1423_) == 0)
{
return v___x_1418_;
}
else
{
lean_object* v_val_1424_; 
v_val_1424_ = lean_ctor_get(v_fst_1423_, 0);
lean_inc(v_val_1424_);
lean_dec_ref_known(v_fst_1423_, 1);
return v_val_1424_;
}
}
}
else
{
lean_object* v___x_1425_; 
lean_dec(v_declName_1410_);
lean_dec_ref(v_env_1408_);
v___x_1425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1425_, 0, v___x_1412_);
return v___x_1425_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName___boxed(lean_object* v_env_1430_, lean_object* v_opts_1431_, lean_object* v_declName_1432_){
_start:
{
lean_object* v_res_1433_; 
v_res_1433_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName(v_env_1430_, v_opts_1431_, v_declName_1432_);
lean_dec_ref(v_opts_1431_);
return v_res_1433_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveQualifiedName(lean_object* v_env_1434_, lean_object* v_opts_1435_, lean_object* v_ns_1436_, lean_object* v_id_1437_){
_start:
{
lean_object* v_resolvedId_1438_; uint8_t v___x_1439_; lean_object* v_resolvedIds_1440_; 
lean_inc(v_id_1437_);
v_resolvedId_1438_ = l_Lean_Name_append(v_ns_1436_, v_id_1437_);
v___x_1439_ = l_Lean_Name_isAtomic(v_id_1437_);
lean_dec(v_id_1437_);
lean_inc_ref(v_env_1434_);
v_resolvedIds_1440_ = l_Lean_getAliases(v_env_1434_, v_resolvedId_1438_, v___x_1439_);
if (v___x_1439_ == 0)
{
goto v___jp_1441_;
}
else
{
uint8_t v___x_1447_; 
lean_inc(v_resolvedId_1438_);
lean_inc_ref(v_env_1434_);
v___x_1447_ = l_Lean_isProtected(v_env_1434_, v_resolvedId_1438_);
if (v___x_1447_ == 0)
{
goto v___jp_1441_;
}
else
{
lean_dec(v_resolvedId_1438_);
lean_dec_ref(v_env_1434_);
return v_resolvedIds_1440_;
}
}
v___jp_1441_:
{
uint8_t v___x_1442_; 
lean_inc(v_resolvedId_1438_);
lean_inc_ref(v_env_1434_);
v___x_1442_ = l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(v_env_1434_, v_resolvedId_1438_);
if (v___x_1442_ == 0)
{
lean_object* v___x_1443_; 
v___x_1443_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName(v_env_1434_, v_opts_1435_, v_resolvedId_1438_);
if (lean_obj_tag(v___x_1443_) == 1)
{
lean_object* v_val_1444_; lean_object* v___x_1445_; 
v_val_1444_ = lean_ctor_get(v___x_1443_, 0);
lean_inc(v_val_1444_);
lean_dec_ref_known(v___x_1443_, 1);
v___x_1445_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1445_, 0, v_val_1444_);
lean_ctor_set(v___x_1445_, 1, v_resolvedIds_1440_);
return v___x_1445_;
}
else
{
lean_dec(v___x_1443_);
return v_resolvedIds_1440_;
}
}
else
{
lean_object* v___x_1446_; 
lean_dec_ref(v_env_1434_);
v___x_1446_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1446_, 0, v_resolvedId_1438_);
lean_ctor_set(v___x_1446_, 1, v_resolvedIds_1440_);
return v___x_1446_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveQualifiedName___boxed(lean_object* v_env_1448_, lean_object* v_opts_1449_, lean_object* v_ns_1450_, lean_object* v_id_1451_){
_start:
{
lean_object* v_res_1452_; 
v_res_1452_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveQualifiedName(v_env_1448_, v_opts_1449_, v_ns_1450_, v_id_1451_);
lean_dec_ref(v_opts_1449_);
return v_res_1452_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveUsingNamespace(lean_object* v_env_1453_, lean_object* v_opts_1454_, lean_object* v_id_1455_, lean_object* v_x_1456_){
_start:
{
if (lean_obj_tag(v_x_1456_) == 1)
{
lean_object* v_pre_1457_; lean_object* v___x_1458_; 
v_pre_1457_ = lean_ctor_get(v_x_1456_, 0);
lean_inc(v_pre_1457_);
lean_inc(v_id_1455_);
lean_inc_ref(v_env_1453_);
v___x_1458_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveQualifiedName(v_env_1453_, v_opts_1454_, v_x_1456_, v_id_1455_);
if (lean_obj_tag(v___x_1458_) == 0)
{
v_x_1456_ = v_pre_1457_;
goto _start;
}
else
{
lean_dec(v_pre_1457_);
lean_dec(v_id_1455_);
lean_dec_ref(v_env_1453_);
return v___x_1458_;
}
}
else
{
lean_object* v___x_1460_; 
lean_dec(v_x_1456_);
lean_dec(v_id_1455_);
lean_dec_ref(v_env_1453_);
v___x_1460_ = lean_box(0);
return v___x_1460_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveUsingNamespace___boxed(lean_object* v_env_1461_, lean_object* v_opts_1462_, lean_object* v_id_1463_, lean_object* v_x_1464_){
_start:
{
lean_object* v_res_1465_; 
v_res_1465_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveUsingNamespace(v_env_1461_, v_opts_1462_, v_id_1463_, v_x_1464_);
lean_dec_ref(v_opts_1462_);
return v_res_1465_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveExact(lean_object* v_env_1466_, lean_object* v_opts_1467_, lean_object* v_id_1468_){
_start:
{
uint8_t v___x_1469_; 
v___x_1469_ = l_Lean_Name_isAtomic(v_id_1468_);
if (v___x_1469_ == 0)
{
lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v_resolvedId_1472_; uint8_t v___x_1473_; 
v___x_1470_ = l_Lean_rootNamespace;
v___x_1471_ = lean_box(0);
v_resolvedId_1472_ = l_Lean_Name_replacePrefix(v_id_1468_, v___x_1470_, v___x_1471_);
lean_inc(v_resolvedId_1472_);
lean_inc_ref(v_env_1466_);
v___x_1473_ = l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(v_env_1466_, v_resolvedId_1472_);
if (v___x_1473_ == 0)
{
lean_object* v___x_1474_; 
v___x_1474_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName(v_env_1466_, v_opts_1467_, v_resolvedId_1472_);
return v___x_1474_;
}
else
{
lean_object* v___x_1475_; 
lean_dec_ref(v_env_1466_);
v___x_1475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1475_, 0, v_resolvedId_1472_);
return v___x_1475_;
}
}
else
{
lean_object* v___x_1476_; 
lean_dec(v_id_1468_);
lean_dec_ref(v_env_1466_);
v___x_1476_ = lean_box(0);
return v___x_1476_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveExact___boxed(lean_object* v_env_1477_, lean_object* v_opts_1478_, lean_object* v_id_1479_){
_start:
{
lean_object* v_res_1480_; 
v_res_1480_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveExact(v_env_1477_, v_opts_1478_, v_id_1479_);
lean_dec_ref(v_opts_1478_);
return v_res_1480_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveOpenDecls(lean_object* v_env_1481_, lean_object* v_opts_1482_, lean_object* v_id_1483_, lean_object* v_x_1484_, lean_object* v_x_1485_){
_start:
{
if (lean_obj_tag(v_x_1484_) == 0)
{
lean_dec(v_id_1483_);
lean_dec_ref(v_env_1481_);
return v_x_1485_;
}
else
{
lean_object* v_head_1486_; 
v_head_1486_ = lean_ctor_get(v_x_1484_, 0);
lean_inc(v_head_1486_);
if (lean_obj_tag(v_head_1486_) == 0)
{
lean_object* v_tail_1487_; lean_object* v_ns_1488_; lean_object* v_except_1489_; uint8_t v___x_1490_; 
v_tail_1487_ = lean_ctor_get(v_x_1484_, 1);
lean_inc(v_tail_1487_);
lean_dec_ref_known(v_x_1484_, 2);
v_ns_1488_ = lean_ctor_get(v_head_1486_, 0);
lean_inc(v_ns_1488_);
v_except_1489_ = lean_ctor_get(v_head_1486_, 1);
lean_inc(v_except_1489_);
lean_dec_ref_known(v_head_1486_, 2);
v___x_1490_ = l_List_elem___at___00Lean_addAliasEntry_spec__2(v_id_1483_, v_except_1489_);
lean_dec(v_except_1489_);
if (v___x_1490_ == 0)
{
lean_object* v_newResolvedIds_1491_; lean_object* v___x_1492_; 
lean_inc(v_id_1483_);
lean_inc_ref(v_env_1481_);
v_newResolvedIds_1491_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveQualifiedName(v_env_1481_, v_opts_1482_, v_ns_1488_, v_id_1483_);
v___x_1492_ = l_List_appendTR___redArg(v_newResolvedIds_1491_, v_x_1485_);
v_x_1484_ = v_tail_1487_;
v_x_1485_ = v___x_1492_;
goto _start;
}
else
{
lean_dec(v_ns_1488_);
v_x_1484_ = v_tail_1487_;
goto _start;
}
}
else
{
lean_object* v_tail_1495_; lean_object* v___x_1497_; uint8_t v_isShared_1498_; uint8_t v_isSharedCheck_1515_; 
v_tail_1495_ = lean_ctor_get(v_x_1484_, 1);
v_isSharedCheck_1515_ = !lean_is_exclusive(v_x_1484_);
if (v_isSharedCheck_1515_ == 0)
{
lean_object* v_unused_1516_; 
v_unused_1516_ = lean_ctor_get(v_x_1484_, 0);
lean_dec(v_unused_1516_);
v___x_1497_ = v_x_1484_;
v_isShared_1498_ = v_isSharedCheck_1515_;
goto v_resetjp_1496_;
}
else
{
lean_inc(v_tail_1495_);
lean_dec(v_x_1484_);
v___x_1497_ = lean_box(0);
v_isShared_1498_ = v_isSharedCheck_1515_;
goto v_resetjp_1496_;
}
v_resetjp_1496_:
{
lean_object* v_id_1499_; lean_object* v_declName_1500_; uint8_t v___x_1501_; 
v_id_1499_ = lean_ctor_get(v_head_1486_, 0);
lean_inc(v_id_1499_);
v_declName_1500_ = lean_ctor_get(v_head_1486_, 1);
lean_inc(v_declName_1500_);
lean_dec_ref_known(v_head_1486_, 2);
v___x_1501_ = lean_name_eq(v_id_1499_, v_id_1483_);
if (v___x_1501_ == 0)
{
uint8_t v___x_1502_; 
v___x_1502_ = l_Lean_Name_isPrefixOf(v_id_1499_, v_id_1483_);
if (v___x_1502_ == 0)
{
lean_dec(v_declName_1500_);
lean_dec(v_id_1499_);
lean_del_object(v___x_1497_);
v_x_1484_ = v_tail_1495_;
goto _start;
}
else
{
lean_object* v_candidate_1504_; uint8_t v___x_1505_; 
lean_inc(v_id_1483_);
v_candidate_1504_ = l_Lean_Name_replacePrefix(v_id_1483_, v_id_1499_, v_declName_1500_);
lean_dec(v_declName_1500_);
lean_dec(v_id_1499_);
lean_inc(v_candidate_1504_);
lean_inc_ref(v_env_1481_);
v___x_1505_ = l_Lean_Environment_contains(v_env_1481_, v_candidate_1504_, v___x_1502_);
if (v___x_1505_ == 0)
{
lean_dec(v_candidate_1504_);
lean_del_object(v___x_1497_);
v_x_1484_ = v_tail_1495_;
goto _start;
}
else
{
lean_object* v___x_1508_; 
if (v_isShared_1498_ == 0)
{
lean_ctor_set(v___x_1497_, 1, v_x_1485_);
lean_ctor_set(v___x_1497_, 0, v_candidate_1504_);
v___x_1508_ = v___x_1497_;
goto v_reusejp_1507_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1510_, 0, v_candidate_1504_);
lean_ctor_set(v_reuseFailAlloc_1510_, 1, v_x_1485_);
v___x_1508_ = v_reuseFailAlloc_1510_;
goto v_reusejp_1507_;
}
v_reusejp_1507_:
{
v_x_1484_ = v_tail_1495_;
v_x_1485_ = v___x_1508_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_1512_; 
lean_dec(v_id_1499_);
if (v_isShared_1498_ == 0)
{
lean_ctor_set(v___x_1497_, 1, v_x_1485_);
lean_ctor_set(v___x_1497_, 0, v_declName_1500_);
v___x_1512_ = v___x_1497_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1514_; 
v_reuseFailAlloc_1514_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1514_, 0, v_declName_1500_);
lean_ctor_set(v_reuseFailAlloc_1514_, 1, v_x_1485_);
v___x_1512_ = v_reuseFailAlloc_1514_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
v_x_1484_ = v_tail_1495_;
v_x_1485_ = v___x_1512_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveOpenDecls___boxed(lean_object* v_env_1517_, lean_object* v_opts_1518_, lean_object* v_id_1519_, lean_object* v_x_1520_, lean_object* v_x_1521_){
_start:
{
lean_object* v_res_1522_; 
v_res_1522_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveOpenDecls(v_env_1517_, v_opts_1518_, v_id_1519_, v_x_1520_, v_x_1521_);
lean_dec_ref(v_opts_1518_);
return v_res_1522_;
}
}
LEAN_EXPORT lean_object* l_List_eraseDups___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__0(lean_object* v_as_1524_){
_start:
{
lean_object* v___f_1525_; lean_object* v___x_1526_; 
v___f_1525_ = ((lean_object*)(l_List_eraseDups___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__0___closed__0));
v___x_1526_ = l_List_eraseDupsBy___redArg(v___f_1525_, v_as_1524_);
return v___x_1526_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__1(lean_object* v_projs_1527_, lean_object* v_a_1528_, lean_object* v_a_1529_){
_start:
{
if (lean_obj_tag(v_a_1528_) == 0)
{
lean_object* v___x_1530_; 
lean_dec(v_projs_1527_);
v___x_1530_ = l_List_reverse___redArg(v_a_1529_);
return v___x_1530_;
}
else
{
lean_object* v_head_1531_; lean_object* v_tail_1532_; lean_object* v___x_1534_; uint8_t v_isShared_1535_; uint8_t v_isSharedCheck_1541_; 
v_head_1531_ = lean_ctor_get(v_a_1528_, 0);
v_tail_1532_ = lean_ctor_get(v_a_1528_, 1);
v_isSharedCheck_1541_ = !lean_is_exclusive(v_a_1528_);
if (v_isSharedCheck_1541_ == 0)
{
v___x_1534_ = v_a_1528_;
v_isShared_1535_ = v_isSharedCheck_1541_;
goto v_resetjp_1533_;
}
else
{
lean_inc(v_tail_1532_);
lean_inc(v_head_1531_);
lean_dec(v_a_1528_);
v___x_1534_ = lean_box(0);
v_isShared_1535_ = v_isSharedCheck_1541_;
goto v_resetjp_1533_;
}
v_resetjp_1533_:
{
lean_object* v___x_1536_; lean_object* v___x_1538_; 
lean_inc(v_projs_1527_);
v___x_1536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1536_, 0, v_head_1531_);
lean_ctor_set(v___x_1536_, 1, v_projs_1527_);
if (v_isShared_1535_ == 0)
{
lean_ctor_set(v___x_1534_, 1, v_a_1529_);
lean_ctor_set(v___x_1534_, 0, v___x_1536_);
v___x_1538_ = v___x_1534_;
goto v_reusejp_1537_;
}
else
{
lean_object* v_reuseFailAlloc_1540_; 
v_reuseFailAlloc_1540_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1540_, 0, v___x_1536_);
lean_ctor_set(v_reuseFailAlloc_1540_, 1, v_a_1529_);
v___x_1538_ = v_reuseFailAlloc_1540_;
goto v_reusejp_1537_;
}
v_reusejp_1537_:
{
v_a_1528_ = v_tail_1532_;
v_a_1529_ = v___x_1538_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop(lean_object* v_env_1542_, lean_object* v_opts_1543_, lean_object* v_ns_1544_, lean_object* v_openDecls_1545_, lean_object* v_extractionResult_1546_, lean_object* v_id_1547_, lean_object* v_projs_1548_){
_start:
{
if (lean_obj_tag(v_id_1547_) == 1)
{
lean_object* v_pre_1549_; lean_object* v_str_1550_; lean_object* v_imported_1551_; lean_object* v_ctx_1552_; lean_object* v_scopes_1553_; lean_object* v___x_1554_; lean_object* v_id_1555_; lean_object* v___y_1557_; lean_object* v___x_1567_; lean_object* v___y_1569_; 
v_pre_1549_ = lean_ctor_get(v_id_1547_, 0);
lean_inc(v_pre_1549_);
v_str_1550_ = lean_ctor_get(v_id_1547_, 1);
lean_inc_ref(v_str_1550_);
v_imported_1551_ = lean_ctor_get(v_extractionResult_1546_, 1);
v_ctx_1552_ = lean_ctor_get(v_extractionResult_1546_, 2);
v_scopes_1553_ = lean_ctor_get(v_extractionResult_1546_, 3);
lean_inc(v_scopes_1553_);
lean_inc(v_ctx_1552_);
lean_inc(v_imported_1551_);
v___x_1554_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1554_, 0, v_id_1547_);
lean_ctor_set(v___x_1554_, 1, v_imported_1551_);
lean_ctor_set(v___x_1554_, 2, v_ctx_1552_);
lean_ctor_set(v___x_1554_, 3, v_scopes_1553_);
v_id_1555_ = l_Lean_MacroScopesView_review(v___x_1554_);
lean_inc(v_ns_1544_);
lean_inc(v_id_1555_);
lean_inc_ref(v_env_1542_);
v___x_1567_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveUsingNamespace(v_env_1542_, v_opts_1543_, v_id_1555_, v_ns_1544_);
if (lean_obj_tag(v___x_1567_) == 0)
{
lean_object* v___x_1574_; 
lean_inc(v_id_1555_);
lean_inc_ref(v_env_1542_);
v___x_1574_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveExact(v_env_1542_, v_opts_1543_, v_id_1555_);
if (lean_obj_tag(v___x_1574_) == 0)
{
uint8_t v___x_1575_; 
lean_inc(v_id_1555_);
lean_inc_ref(v_env_1542_);
v___x_1575_ = l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(v_env_1542_, v_id_1555_);
if (v___x_1575_ == 0)
{
v___y_1569_ = v___x_1567_;
goto v___jp_1568_;
}
else
{
lean_object* v___x_1576_; 
lean_inc(v_id_1555_);
v___x_1576_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1576_, 0, v_id_1555_);
lean_ctor_set(v___x_1576_, 1, v___x_1567_);
v___y_1569_ = v___x_1576_;
goto v___jp_1568_;
}
}
else
{
lean_object* v_val_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; 
lean_dec(v_id_1555_);
lean_dec_ref(v_str_1550_);
lean_dec(v_pre_1549_);
lean_dec(v_openDecls_1545_);
lean_dec(v_ns_1544_);
lean_dec_ref(v_env_1542_);
v_val_1577_ = lean_ctor_get(v___x_1574_, 0);
lean_inc(v_val_1577_);
lean_dec_ref_known(v___x_1574_, 1);
v___x_1578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1578_, 0, v_val_1577_);
lean_ctor_set(v___x_1578_, 1, v_projs_1548_);
v___x_1579_ = lean_box(0);
v___x_1580_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1580_, 0, v___x_1578_);
lean_ctor_set(v___x_1580_, 1, v___x_1579_);
return v___x_1580_;
}
}
else
{
lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; 
lean_dec(v_id_1555_);
lean_dec_ref(v_str_1550_);
lean_dec(v_pre_1549_);
lean_dec(v_openDecls_1545_);
lean_dec(v_ns_1544_);
lean_dec_ref(v_env_1542_);
v___x_1581_ = l_List_eraseDups___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__0(v___x_1567_);
v___x_1582_ = lean_box(0);
v___x_1583_ = l_List_mapTR_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__1(v_projs_1548_, v___x_1581_, v___x_1582_);
return v___x_1583_;
}
v___jp_1556_:
{
lean_object* v_resolvedIds_1558_; uint8_t v___x_1559_; lean_object* v___x_1560_; lean_object* v_resolvedIds_1561_; 
lean_inc(v_openDecls_1545_);
lean_inc(v_id_1555_);
lean_inc_ref_n(v_env_1542_, 2);
v_resolvedIds_1558_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveOpenDecls(v_env_1542_, v_opts_1543_, v_id_1555_, v_openDecls_1545_, v___y_1557_);
v___x_1559_ = l_Lean_Name_isAtomic(v_id_1555_);
v___x_1560_ = l_Lean_getAliases(v_env_1542_, v_id_1555_, v___x_1559_);
lean_dec(v_id_1555_);
v_resolvedIds_1561_ = l_List_appendTR___redArg(v___x_1560_, v_resolvedIds_1558_);
if (lean_obj_tag(v_resolvedIds_1561_) == 0)
{
lean_object* v___x_1562_; 
v___x_1562_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1562_, 0, v_str_1550_);
lean_ctor_set(v___x_1562_, 1, v_projs_1548_);
v_id_1547_ = v_pre_1549_;
v_projs_1548_ = v___x_1562_;
goto _start;
}
else
{
lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; 
lean_dec_ref(v_str_1550_);
lean_dec(v_pre_1549_);
lean_dec(v_openDecls_1545_);
lean_dec(v_ns_1544_);
lean_dec_ref(v_env_1542_);
v___x_1564_ = l_List_eraseDups___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__0(v_resolvedIds_1561_);
v___x_1565_ = lean_box(0);
v___x_1566_ = l_List_mapTR_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__1(v_projs_1548_, v___x_1564_, v___x_1565_);
return v___x_1566_;
}
}
v___jp_1568_:
{
lean_object* v___x_1570_; 
lean_inc(v_id_1555_);
lean_inc_ref(v_env_1542_);
v___x_1570_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName(v_env_1542_, v_opts_1543_, v_id_1555_);
if (lean_obj_tag(v___x_1570_) == 1)
{
lean_object* v_val_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; 
v_val_1571_ = lean_ctor_get(v___x_1570_, 0);
lean_inc(v_val_1571_);
lean_dec_ref_known(v___x_1570_, 1);
v___x_1572_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1572_, 0, v_val_1571_);
lean_ctor_set(v___x_1572_, 1, v___x_1567_);
v___x_1573_ = l_List_appendTR___redArg(v___x_1572_, v___y_1569_);
v___y_1557_ = v___x_1573_;
goto v___jp_1556_;
}
else
{
lean_dec(v___x_1570_);
lean_dec(v___x_1567_);
v___y_1557_ = v___y_1569_;
goto v___jp_1556_;
}
}
}
else
{
lean_object* v___x_1584_; 
lean_dec(v_projs_1548_);
lean_dec(v_id_1547_);
lean_dec(v_openDecls_1545_);
lean_dec(v_ns_1544_);
lean_dec_ref(v_env_1542_);
v___x_1584_ = lean_box(0);
return v___x_1584_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop___boxed(lean_object* v_env_1585_, lean_object* v_opts_1586_, lean_object* v_ns_1587_, lean_object* v_openDecls_1588_, lean_object* v_extractionResult_1589_, lean_object* v_id_1590_, lean_object* v_projs_1591_){
_start:
{
lean_object* v_res_1592_; 
v_res_1592_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop(v_env_1585_, v_opts_1586_, v_ns_1587_, v_openDecls_1588_, v_extractionResult_1589_, v_id_1590_, v_projs_1591_);
lean_dec_ref(v_extractionResult_1589_);
lean_dec_ref(v_opts_1586_);
return v_res_1592_;
}
}
LEAN_EXPORT lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object* v_env_1593_, lean_object* v_opts_1594_, lean_object* v_ns_1595_, lean_object* v_openDecls_1596_, lean_object* v_id_1597_){
_start:
{
lean_object* v_extractionResult_1598_; lean_object* v_name_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; 
v_extractionResult_1598_ = l_Lean_extractMacroScopes(v_id_1597_);
v_name_1599_ = lean_ctor_get(v_extractionResult_1598_, 0);
lean_inc(v_name_1599_);
v___x_1600_ = lean_box(0);
v___x_1601_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop(v_env_1593_, v_opts_1594_, v_ns_1595_, v_openDecls_1596_, v_extractionResult_1598_, v_name_1599_, v___x_1600_);
lean_dec_ref(v_extractionResult_1598_);
return v___x_1601_;
}
}
LEAN_EXPORT lean_object* l_Lean_ResolveName_resolveGlobalName___boxed(lean_object* v_env_1602_, lean_object* v_opts_1603_, lean_object* v_ns_1604_, lean_object* v_openDecls_1605_, lean_object* v_id_1606_){
_start:
{
lean_object* v_res_1607_; 
v_res_1607_ = l_Lean_ResolveName_resolveGlobalName(v_env_1602_, v_opts_1603_, v_ns_1604_, v_openDecls_1605_, v_id_1606_);
lean_dec_ref(v_opts_1603_);
return v_res_1607_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_ResolveName_resolveNamespaceUsingScope_x3f_spec__0(lean_object* v_msg_1608_){
_start:
{
lean_object* v___x_1609_; lean_object* v___x_1610_; 
v___x_1609_ = lean_box(0);
v___x_1610_ = lean_panic_fn_borrowed(v___x_1609_, v_msg_1608_);
return v___x_1610_;
}
}
static lean_object* _init_l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__3(void){
_start:
{
lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; 
v___x_1614_ = ((lean_object*)(l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__2));
v___x_1615_ = lean_unsigned_to_nat(9u);
v___x_1616_ = lean_unsigned_to_nat(230u);
v___x_1617_ = ((lean_object*)(l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__1));
v___x_1618_ = ((lean_object*)(l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__0));
v___x_1619_ = l_mkPanicMessageWithDecl(v___x_1618_, v___x_1617_, v___x_1616_, v___x_1615_, v___x_1614_);
return v___x_1619_;
}
}
LEAN_EXPORT lean_object* l_Lean_ResolveName_resolveNamespaceUsingScope_x3f(lean_object* v_env_1620_, lean_object* v_n_1621_, lean_object* v_ns_1622_){
_start:
{
switch(lean_obj_tag(v_ns_1622_))
{
case 1:
{
lean_object* v_pre_1623_; lean_object* v___x_1624_; uint8_t v___x_1625_; 
v_pre_1623_ = lean_ctor_get(v_ns_1622_, 0);
lean_inc(v_pre_1623_);
lean_inc(v_n_1621_);
v___x_1624_ = l_Lean_Name_append(v_ns_1622_, v_n_1621_);
lean_inc_ref(v_env_1620_);
v___x_1625_ = l_Lean_Environment_isNamespace(v_env_1620_, v___x_1624_);
if (v___x_1625_ == 0)
{
lean_dec(v___x_1624_);
v_ns_1622_ = v_pre_1623_;
goto _start;
}
else
{
lean_object* v___x_1627_; 
lean_dec(v_pre_1623_);
lean_dec(v_n_1621_);
lean_dec_ref(v_env_1620_);
v___x_1627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1627_, 0, v___x_1624_);
return v___x_1627_;
}
}
case 0:
{
lean_object* v___x_1628_; lean_object* v_n_1629_; uint8_t v___x_1630_; 
v___x_1628_ = l_Lean_rootNamespace;
v_n_1629_ = l_Lean_Name_replacePrefix(v_n_1621_, v___x_1628_, v_ns_1622_);
v___x_1630_ = l_Lean_Environment_isNamespace(v_env_1620_, v_n_1629_);
if (v___x_1630_ == 0)
{
lean_object* v___x_1631_; 
lean_dec(v_n_1629_);
v___x_1631_ = lean_box(0);
return v___x_1631_;
}
else
{
lean_object* v___x_1632_; 
v___x_1632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1632_, 0, v_n_1629_);
return v___x_1632_;
}
}
default: 
{
lean_object* v___x_1633_; lean_object* v___x_1634_; 
lean_dec(v_ns_1622_);
lean_dec(v_n_1621_);
lean_dec_ref(v_env_1620_);
v___x_1633_ = lean_obj_once(&l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__3, &l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__3_once, _init_l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__3);
v___x_1634_ = l_panic___at___00Lean_ResolveName_resolveNamespaceUsingScope_x3f_spec__0(v___x_1633_);
return v___x_1634_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ResolveName_resolveNamespaceUsingOpenDecls(lean_object* v_env_1635_, lean_object* v_n_1636_, lean_object* v_x_1637_){
_start:
{
if (lean_obj_tag(v_x_1637_) == 0)
{
lean_object* v___x_1638_; 
lean_dec(v_n_1636_);
lean_dec_ref(v_env_1635_);
v___x_1638_ = lean_box(0);
return v___x_1638_;
}
else
{
lean_object* v_head_1639_; 
v_head_1639_ = lean_ctor_get(v_x_1637_, 0);
if (lean_obj_tag(v_head_1639_) == 0)
{
lean_object* v_tail_1640_; lean_object* v___x_1642_; uint8_t v_isShared_1643_; uint8_t v_isSharedCheck_1657_; 
lean_inc_ref(v_head_1639_);
v_tail_1640_ = lean_ctor_get(v_x_1637_, 1);
v_isSharedCheck_1657_ = !lean_is_exclusive(v_x_1637_);
if (v_isSharedCheck_1657_ == 0)
{
lean_object* v_unused_1658_; 
v_unused_1658_ = lean_ctor_get(v_x_1637_, 0);
lean_dec(v_unused_1658_);
v___x_1642_ = v_x_1637_;
v_isShared_1643_ = v_isSharedCheck_1657_;
goto v_resetjp_1641_;
}
else
{
lean_inc(v_tail_1640_);
lean_dec(v_x_1637_);
v___x_1642_ = lean_box(0);
v_isShared_1643_ = v_isSharedCheck_1657_;
goto v_resetjp_1641_;
}
v_resetjp_1641_:
{
lean_object* v_ns_1644_; lean_object* v_except_1645_; lean_object* v___x_1646_; uint8_t v___y_1648_; uint8_t v___x_1654_; 
v_ns_1644_ = lean_ctor_get(v_head_1639_, 0);
lean_inc(v_ns_1644_);
v_except_1645_ = lean_ctor_get(v_head_1639_, 1);
lean_inc(v_except_1645_);
lean_dec_ref_known(v_head_1639_, 2);
lean_inc(v_n_1636_);
v___x_1646_ = l_Lean_Name_append(v_ns_1644_, v_n_1636_);
lean_inc_ref(v_env_1635_);
v___x_1654_ = l_Lean_Environment_isNamespace(v_env_1635_, v___x_1646_);
if (v___x_1654_ == 0)
{
lean_dec(v_except_1645_);
v___y_1648_ = v___x_1654_;
goto v___jp_1647_;
}
else
{
uint8_t v___x_1655_; 
v___x_1655_ = l_List_elem___at___00Lean_addAliasEntry_spec__2(v_n_1636_, v_except_1645_);
lean_dec(v_except_1645_);
if (v___x_1655_ == 0)
{
v___y_1648_ = v___x_1654_;
goto v___jp_1647_;
}
else
{
lean_dec(v___x_1646_);
lean_del_object(v___x_1642_);
v_x_1637_ = v_tail_1640_;
goto _start;
}
}
v___jp_1647_:
{
if (v___y_1648_ == 0)
{
lean_dec(v___x_1646_);
lean_del_object(v___x_1642_);
v_x_1637_ = v_tail_1640_;
goto _start;
}
else
{
lean_object* v___x_1650_; lean_object* v___x_1652_; 
v___x_1650_ = l_Lean_ResolveName_resolveNamespaceUsingOpenDecls(v_env_1635_, v_n_1636_, v_tail_1640_);
if (v_isShared_1643_ == 0)
{
lean_ctor_set(v___x_1642_, 1, v___x_1650_);
lean_ctor_set(v___x_1642_, 0, v___x_1646_);
v___x_1652_ = v___x_1642_;
goto v_reusejp_1651_;
}
else
{
lean_object* v_reuseFailAlloc_1653_; 
v_reuseFailAlloc_1653_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1653_, 0, v___x_1646_);
lean_ctor_set(v_reuseFailAlloc_1653_, 1, v___x_1650_);
v___x_1652_ = v_reuseFailAlloc_1653_;
goto v_reusejp_1651_;
}
v_reusejp_1651_:
{
return v___x_1652_;
}
}
}
}
}
else
{
lean_object* v_tail_1659_; 
v_tail_1659_ = lean_ctor_get(v_x_1637_, 1);
lean_inc(v_tail_1659_);
lean_dec_ref_known(v_x_1637_, 2);
v_x_1637_ = v_tail_1659_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ResolveName_resolveNamespace(lean_object* v_env_1661_, lean_object* v_ns_1662_, lean_object* v_openDecls_1663_, lean_object* v_id_1664_){
_start:
{
lean_object* v___x_1665_; 
lean_inc(v_id_1664_);
lean_inc_ref(v_env_1661_);
v___x_1665_ = l_Lean_ResolveName_resolveNamespaceUsingScope_x3f(v_env_1661_, v_id_1664_, v_ns_1662_);
if (lean_obj_tag(v___x_1665_) == 0)
{
lean_object* v___x_1666_; 
v___x_1666_ = l_Lean_ResolveName_resolveNamespaceUsingOpenDecls(v_env_1661_, v_id_1664_, v_openDecls_1663_);
return v___x_1666_;
}
else
{
lean_object* v_val_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; 
v_val_1667_ = lean_ctor_get(v___x_1665_, 0);
lean_inc(v_val_1667_);
lean_dec_ref_known(v___x_1665_, 1);
v___x_1668_ = l_Lean_ResolveName_resolveNamespaceUsingOpenDecls(v_env_1661_, v_id_1664_, v_openDecls_1663_);
v___x_1669_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1669_, 0, v_val_1667_);
lean_ctor_set(v___x_1669_, 1, v___x_1668_);
return v___x_1669_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadResolveNameOfMonadLift___redArg(lean_object* v_inst_1670_, lean_object* v_inst_1671_){
_start:
{
lean_object* v_getCurrNamespace_1672_; lean_object* v_getOpenDecls_1673_; lean_object* v___x_1675_; uint8_t v_isShared_1676_; uint8_t v_isSharedCheck_1682_; 
v_getCurrNamespace_1672_ = lean_ctor_get(v_inst_1671_, 0);
v_getOpenDecls_1673_ = lean_ctor_get(v_inst_1671_, 1);
v_isSharedCheck_1682_ = !lean_is_exclusive(v_inst_1671_);
if (v_isSharedCheck_1682_ == 0)
{
v___x_1675_ = v_inst_1671_;
v_isShared_1676_ = v_isSharedCheck_1682_;
goto v_resetjp_1674_;
}
else
{
lean_inc(v_getOpenDecls_1673_);
lean_inc(v_getCurrNamespace_1672_);
lean_dec(v_inst_1671_);
v___x_1675_ = lean_box(0);
v_isShared_1676_ = v_isSharedCheck_1682_;
goto v_resetjp_1674_;
}
v_resetjp_1674_:
{
lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1680_; 
lean_inc(v_inst_1670_);
v___x_1677_ = lean_apply_2(v_inst_1670_, lean_box(0), v_getCurrNamespace_1672_);
v___x_1678_ = lean_apply_2(v_inst_1670_, lean_box(0), v_getOpenDecls_1673_);
if (v_isShared_1676_ == 0)
{
lean_ctor_set(v___x_1675_, 1, v___x_1678_);
lean_ctor_set(v___x_1675_, 0, v___x_1677_);
v___x_1680_ = v___x_1675_;
goto v_reusejp_1679_;
}
else
{
lean_object* v_reuseFailAlloc_1681_; 
v_reuseFailAlloc_1681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1681_, 0, v___x_1677_);
lean_ctor_set(v_reuseFailAlloc_1681_, 1, v___x_1678_);
v___x_1680_ = v_reuseFailAlloc_1681_;
goto v_reusejp_1679_;
}
v_reusejp_1679_:
{
return v___x_1680_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadResolveNameOfMonadLift(lean_object* v_m_1683_, lean_object* v_n_1684_, lean_object* v_inst_1685_, lean_object* v_inst_1686_){
_start:
{
lean_object* v___x_1687_; 
v___x_1687_ = l_Lean_instMonadResolveNameOfMonadLift___redArg(v_inst_1685_, v_inst_1686_);
return v___x_1687_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1689_; lean_object* v___x_1690_; 
v___x_1689_ = ((lean_object*)(l_Lean_checkPrivateInPublic___redArg___lam__0___closed__0));
v___x_1690_ = l_Lean_stringToMessageData(v___x_1689_);
return v___x_1690_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1692_; lean_object* v___x_1693_; 
v___x_1692_ = ((lean_object*)(l_Lean_checkPrivateInPublic___redArg___lam__0___closed__2));
v___x_1693_ = l_Lean_stringToMessageData(v___x_1692_);
return v___x_1693_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___redArg___lam__0(lean_object* v_____do__lift_1694_, lean_object* v_toApplicative_1695_, lean_object* v_id_1696_, lean_object* v_inst_1697_, lean_object* v_inst_1698_, lean_object* v_inst_1699_, lean_object* v_inst_1700_, uint8_t v_____do__lift_1701_){
_start:
{
uint8_t v_isExporting_1706_; 
v_isExporting_1706_ = lean_ctor_get_uint8(v_____do__lift_1694_, sizeof(void*)*8);
if (v_isExporting_1706_ == 0)
{
lean_dec(v_inst_1700_);
lean_dec(v_inst_1699_);
lean_dec_ref(v_inst_1698_);
lean_dec_ref(v_inst_1697_);
lean_dec(v_id_1696_);
goto v___jp_1702_;
}
else
{
uint8_t v___x_1707_; 
v___x_1707_ = l_Lean_isPrivateName(v_id_1696_);
if (v___x_1707_ == 0)
{
lean_dec(v_inst_1700_);
lean_dec(v_inst_1699_);
lean_dec_ref(v_inst_1698_);
lean_dec_ref(v_inst_1697_);
lean_dec(v_id_1696_);
goto v___jp_1702_;
}
else
{
if (v_____do__lift_1701_ == 0)
{
lean_dec(v_inst_1700_);
lean_dec(v_inst_1699_);
lean_dec_ref(v_inst_1698_);
lean_dec_ref(v_inst_1697_);
lean_dec(v_id_1696_);
goto v___jp_1702_;
}
else
{
lean_object* v___x_1708_; uint8_t v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; 
lean_dec_ref(v_toApplicative_1695_);
v___x_1708_ = lean_obj_once(&l_Lean_checkPrivateInPublic___redArg___lam__0___closed__1, &l_Lean_checkPrivateInPublic___redArg___lam__0___closed__1_once, _init_l_Lean_checkPrivateInPublic___redArg___lam__0___closed__1);
v___x_1709_ = 0;
v___x_1710_ = l_Lean_MessageData_ofConstName(v_id_1696_, v___x_1709_);
v___x_1711_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1711_, 0, v___x_1708_);
lean_ctor_set(v___x_1711_, 1, v___x_1710_);
v___x_1712_ = lean_obj_once(&l_Lean_checkPrivateInPublic___redArg___lam__0___closed__3, &l_Lean_checkPrivateInPublic___redArg___lam__0___closed__3_once, _init_l_Lean_checkPrivateInPublic___redArg___lam__0___closed__3);
v___x_1713_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1713_, 0, v___x_1711_);
lean_ctor_set(v___x_1713_, 1, v___x_1712_);
v___x_1714_ = l_Lean_logWarning___redArg(v_inst_1697_, v_inst_1698_, v_inst_1699_, v_inst_1700_, v___x_1713_);
return v___x_1714_;
}
}
}
v___jp_1702_:
{
lean_object* v_toPure_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; 
v_toPure_1703_ = lean_ctor_get(v_toApplicative_1695_, 1);
lean_inc(v_toPure_1703_);
lean_dec_ref(v_toApplicative_1695_);
v___x_1704_ = lean_box(0);
v___x_1705_ = lean_apply_2(v_toPure_1703_, lean_box(0), v___x_1704_);
return v___x_1705_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___redArg___lam__0___boxed(lean_object* v_____do__lift_1715_, lean_object* v_toApplicative_1716_, lean_object* v_id_1717_, lean_object* v_inst_1718_, lean_object* v_inst_1719_, lean_object* v_inst_1720_, lean_object* v_inst_1721_, lean_object* v_____do__lift_1722_){
_start:
{
uint8_t v_____do__lift_231__boxed_1723_; lean_object* v_res_1724_; 
v_____do__lift_231__boxed_1723_ = lean_unbox(v_____do__lift_1722_);
v_res_1724_ = l_Lean_checkPrivateInPublic___redArg___lam__0(v_____do__lift_1715_, v_toApplicative_1716_, v_id_1717_, v_inst_1718_, v_inst_1719_, v_inst_1720_, v_inst_1721_, v_____do__lift_231__boxed_1723_);
lean_dec_ref(v_____do__lift_1715_);
return v_res_1724_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___redArg___lam__1(lean_object* v_toApplicative_1725_, lean_object* v_id_1726_, lean_object* v_inst_1727_, lean_object* v_inst_1728_, lean_object* v_inst_1729_, lean_object* v_inst_1730_, lean_object* v___x_1731_, lean_object* v_toBind_1732_, lean_object* v_____do__lift_1733_){
_start:
{
lean_object* v___f_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; 
lean_inc(v_inst_1730_);
lean_inc_ref(v_inst_1727_);
v___f_1734_ = lean_alloc_closure((void*)(l_Lean_checkPrivateInPublic___redArg___lam__0___boxed), 8, 7);
lean_closure_set(v___f_1734_, 0, v_____do__lift_1733_);
lean_closure_set(v___f_1734_, 1, v_toApplicative_1725_);
lean_closure_set(v___f_1734_, 2, v_id_1726_);
lean_closure_set(v___f_1734_, 3, v_inst_1727_);
lean_closure_set(v___f_1734_, 4, v_inst_1728_);
lean_closure_set(v___f_1734_, 5, v_inst_1729_);
lean_closure_set(v___f_1734_, 6, v_inst_1730_);
v___x_1735_ = l_Lean_ResolveName_backward_privateInPublic_warn;
v___x_1736_ = l_Lean_Option_getM___redArg(v_inst_1727_, v_inst_1730_, v___x_1731_, v___x_1735_);
v___x_1737_ = lean_apply_4(v_toBind_1732_, lean_box(0), lean_box(0), v___x_1736_, v___f_1734_);
return v___x_1737_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___redArg(lean_object* v_inst_1738_, lean_object* v_inst_1739_, lean_object* v_inst_1740_, lean_object* v_inst_1741_, lean_object* v_inst_1742_, lean_object* v_id_1743_){
_start:
{
lean_object* v___x_1744_; lean_object* v_toApplicative_1745_; lean_object* v_toBind_1746_; lean_object* v_getEnv_1747_; lean_object* v___f_1748_; lean_object* v___x_1749_; 
v___x_1744_ = l_Lean_KVMap_instValueBool;
v_toApplicative_1745_ = lean_ctor_get(v_inst_1738_, 0);
lean_inc_ref(v_toApplicative_1745_);
v_toBind_1746_ = lean_ctor_get(v_inst_1738_, 1);
lean_inc_n(v_toBind_1746_, 2);
v_getEnv_1747_ = lean_ctor_get(v_inst_1739_, 0);
lean_inc(v_getEnv_1747_);
lean_dec_ref(v_inst_1739_);
v___f_1748_ = lean_alloc_closure((void*)(l_Lean_checkPrivateInPublic___redArg___lam__1), 9, 8);
lean_closure_set(v___f_1748_, 0, v_toApplicative_1745_);
lean_closure_set(v___f_1748_, 1, v_id_1743_);
lean_closure_set(v___f_1748_, 2, v_inst_1738_);
lean_closure_set(v___f_1748_, 3, v_inst_1741_);
lean_closure_set(v___f_1748_, 4, v_inst_1742_);
lean_closure_set(v___f_1748_, 5, v_inst_1740_);
lean_closure_set(v___f_1748_, 6, v___x_1744_);
lean_closure_set(v___f_1748_, 7, v_toBind_1746_);
v___x_1749_ = lean_apply_4(v_toBind_1746_, lean_box(0), lean_box(0), v_getEnv_1747_, v___f_1748_);
return v___x_1749_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic(lean_object* v_m_1750_, lean_object* v_inst_1751_, lean_object* v_inst_1752_, lean_object* v_inst_1753_, lean_object* v_inst_1754_, lean_object* v_inst_1755_, lean_object* v_id_1756_){
_start:
{
lean_object* v___x_1757_; 
v___x_1757_ = l_Lean_checkPrivateInPublic___redArg(v_inst_1751_, v_inst_1752_, v_inst_1753_, v_inst_1754_, v_inst_1755_, v_id_1756_);
return v___x_1757_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg___lam__0(lean_object* v_env_1758_, lean_object* v_n_1759_, lean_object* v_toApplicative_1760_, uint8_t v___y_1761_, uint8_t v___x_1762_, lean_object* v_____r_1763_){
_start:
{
lean_object* v___x_1764_; 
v___x_1764_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1758_, v_n_1759_);
if (lean_obj_tag(v___x_1764_) == 0)
{
lean_object* v_toPure_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; 
v_toPure_1765_ = lean_ctor_get(v_toApplicative_1760_, 1);
lean_inc(v_toPure_1765_);
lean_dec_ref(v_toApplicative_1760_);
v___x_1766_ = lean_box(v___y_1761_);
v___x_1767_ = lean_apply_2(v_toPure_1765_, lean_box(0), v___x_1766_);
return v___x_1767_;
}
else
{
lean_object* v_val_1768_; lean_object* v_toPure_1769_; lean_object* v___x_1770_; uint8_t v_isModule_1771_; 
v_val_1768_ = lean_ctor_get(v___x_1764_, 0);
lean_inc(v_val_1768_);
lean_dec_ref_known(v___x_1764_, 1);
v_toPure_1769_ = lean_ctor_get(v_toApplicative_1760_, 1);
lean_inc(v_toPure_1769_);
lean_dec_ref(v_toApplicative_1760_);
v___x_1770_ = l_Lean_Environment_header(v_env_1758_);
v_isModule_1771_ = lean_ctor_get_uint8(v___x_1770_, sizeof(void*)*7 + 4);
if (v_isModule_1771_ == 0)
{
lean_object* v___x_1772_; lean_object* v___x_1773_; 
lean_dec_ref(v___x_1770_);
lean_dec(v_val_1768_);
v___x_1772_ = lean_box(v___x_1762_);
v___x_1773_ = lean_apply_2(v_toPure_1769_, lean_box(0), v___x_1772_);
return v___x_1773_;
}
else
{
lean_object* v_modules_1774_; lean_object* v___x_1775_; uint8_t v___x_1776_; 
v_modules_1774_ = lean_ctor_get(v___x_1770_, 3);
lean_inc_ref(v_modules_1774_);
lean_dec_ref(v___x_1770_);
v___x_1775_ = lean_array_get_size(v_modules_1774_);
v___x_1776_ = lean_nat_dec_lt(v_val_1768_, v___x_1775_);
if (v___x_1776_ == 0)
{
lean_object* v___x_1777_; lean_object* v___x_1778_; 
lean_dec_ref(v_modules_1774_);
lean_dec(v_val_1768_);
v___x_1777_ = lean_box(v_isModule_1771_);
v___x_1778_ = lean_apply_2(v_toPure_1769_, lean_box(0), v___x_1777_);
return v___x_1778_;
}
else
{
lean_object* v___x_1779_; lean_object* v_toImport_1780_; uint8_t v_importAll_1781_; 
v___x_1779_ = lean_array_fget(v_modules_1774_, v_val_1768_);
lean_dec(v_val_1768_);
lean_dec_ref(v_modules_1774_);
v_toImport_1780_ = lean_ctor_get(v___x_1779_, 0);
lean_inc_ref(v_toImport_1780_);
lean_dec(v___x_1779_);
v_importAll_1781_ = lean_ctor_get_uint8(v_toImport_1780_, sizeof(void*)*1);
lean_dec_ref(v_toImport_1780_);
if (v_importAll_1781_ == 0)
{
lean_object* v___x_1782_; lean_object* v___x_1783_; 
v___x_1782_ = lean_box(v_isModule_1771_);
v___x_1783_ = lean_apply_2(v_toPure_1769_, lean_box(0), v___x_1782_);
return v___x_1783_;
}
else
{
lean_object* v___x_1784_; lean_object* v___x_1785_; 
v___x_1784_ = lean_box(v___y_1761_);
v___x_1785_ = lean_apply_2(v_toPure_1769_, lean_box(0), v___x_1784_);
return v___x_1785_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg___lam__0___boxed(lean_object* v_env_1786_, lean_object* v_n_1787_, lean_object* v_toApplicative_1788_, lean_object* v___y_1789_, lean_object* v___x_1790_, lean_object* v_____r_1791_){
_start:
{
uint8_t v___y_758__boxed_1792_; uint8_t v___x_759__boxed_1793_; lean_object* v_res_1794_; 
v___y_758__boxed_1792_ = lean_unbox(v___y_1789_);
v___x_759__boxed_1793_ = lean_unbox(v___x_1790_);
v_res_1794_ = l_Lean_isInaccessiblePrivateName___redArg___lam__0(v_env_1786_, v_n_1787_, v_toApplicative_1788_, v___y_758__boxed_1792_, v___x_759__boxed_1793_, v_____r_1791_);
lean_dec(v_n_1787_);
lean_dec_ref(v_env_1786_);
return v_res_1794_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg___lam__1(lean_object* v_env_1795_, lean_object* v_n_1796_, lean_object* v_toApplicative_1797_, uint8_t v___x_1798_, lean_object* v_inst_1799_, lean_object* v_inst_1800_, lean_object* v_inst_1801_, lean_object* v_inst_1802_, lean_object* v_inst_1803_, lean_object* v_toBind_1804_, uint8_t v___x_1805_, uint8_t v_____do__lift_1806_){
_start:
{
uint8_t v___y_1808_; uint8_t v_isExporting_1814_; 
v_isExporting_1814_ = lean_ctor_get_uint8(v_env_1795_, sizeof(void*)*8);
if (v_isExporting_1814_ == 0)
{
v___y_1808_ = v_isExporting_1814_;
goto v___jp_1807_;
}
else
{
if (v_____do__lift_1806_ == 0)
{
lean_object* v_toPure_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; 
lean_dec(v_toBind_1804_);
lean_dec(v_inst_1803_);
lean_dec_ref(v_inst_1802_);
lean_dec(v_inst_1801_);
lean_dec_ref(v_inst_1800_);
lean_dec_ref(v_inst_1799_);
lean_dec(v_n_1796_);
lean_dec_ref(v_env_1795_);
v_toPure_1815_ = lean_ctor_get(v_toApplicative_1797_, 1);
lean_inc(v_toPure_1815_);
lean_dec_ref(v_toApplicative_1797_);
v___x_1816_ = lean_box(v___x_1798_);
v___x_1817_ = lean_apply_2(v_toPure_1815_, lean_box(0), v___x_1816_);
return v___x_1817_;
}
else
{
v___y_1808_ = v___x_1805_;
goto v___jp_1807_;
}
}
v___jp_1807_:
{
lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___f_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; 
v___x_1809_ = lean_box(v___y_1808_);
v___x_1810_ = lean_box(v___x_1798_);
lean_inc(v_n_1796_);
v___f_1811_ = lean_alloc_closure((void*)(l_Lean_isInaccessiblePrivateName___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1811_, 0, v_env_1795_);
lean_closure_set(v___f_1811_, 1, v_n_1796_);
lean_closure_set(v___f_1811_, 2, v_toApplicative_1797_);
lean_closure_set(v___f_1811_, 3, v___x_1809_);
lean_closure_set(v___f_1811_, 4, v___x_1810_);
v___x_1812_ = l_Lean_checkPrivateInPublic___redArg(v_inst_1799_, v_inst_1800_, v_inst_1801_, v_inst_1802_, v_inst_1803_, v_n_1796_);
v___x_1813_ = lean_apply_4(v_toBind_1804_, lean_box(0), lean_box(0), v___x_1812_, v___f_1811_);
return v___x_1813_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg___lam__1___boxed(lean_object* v_env_1818_, lean_object* v_n_1819_, lean_object* v_toApplicative_1820_, lean_object* v___x_1821_, lean_object* v_inst_1822_, lean_object* v_inst_1823_, lean_object* v_inst_1824_, lean_object* v_inst_1825_, lean_object* v_inst_1826_, lean_object* v_toBind_1827_, lean_object* v___x_1828_, lean_object* v_____do__lift_1829_){
_start:
{
uint8_t v___x_799__boxed_1830_; uint8_t v___x_805__boxed_1831_; uint8_t v_____do__lift_806__boxed_1832_; lean_object* v_res_1833_; 
v___x_799__boxed_1830_ = lean_unbox(v___x_1821_);
v___x_805__boxed_1831_ = lean_unbox(v___x_1828_);
v_____do__lift_806__boxed_1832_ = lean_unbox(v_____do__lift_1829_);
v_res_1833_ = l_Lean_isInaccessiblePrivateName___redArg___lam__1(v_env_1818_, v_n_1819_, v_toApplicative_1820_, v___x_799__boxed_1830_, v_inst_1822_, v_inst_1823_, v_inst_1824_, v_inst_1825_, v_inst_1826_, v_toBind_1827_, v___x_805__boxed_1831_, v_____do__lift_806__boxed_1832_);
return v_res_1833_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg___lam__2(lean_object* v_n_1834_, lean_object* v_toApplicative_1835_, uint8_t v___x_1836_, lean_object* v_inst_1837_, lean_object* v_inst_1838_, lean_object* v_inst_1839_, lean_object* v_inst_1840_, lean_object* v_inst_1841_, lean_object* v_toBind_1842_, uint8_t v___x_1843_, lean_object* v_env_1844_){
_start:
{
lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___f_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; 
v___x_1845_ = lean_box(v___x_1836_);
v___x_1846_ = lean_box(v___x_1843_);
lean_inc(v_toBind_1842_);
lean_inc(v_inst_1839_);
lean_inc_ref(v_inst_1837_);
v___f_1847_ = lean_alloc_closure((void*)(l_Lean_isInaccessiblePrivateName___redArg___lam__1___boxed), 12, 11);
lean_closure_set(v___f_1847_, 0, v_env_1844_);
lean_closure_set(v___f_1847_, 1, v_n_1834_);
lean_closure_set(v___f_1847_, 2, v_toApplicative_1835_);
lean_closure_set(v___f_1847_, 3, v___x_1845_);
lean_closure_set(v___f_1847_, 4, v_inst_1837_);
lean_closure_set(v___f_1847_, 5, v_inst_1838_);
lean_closure_set(v___f_1847_, 6, v_inst_1839_);
lean_closure_set(v___f_1847_, 7, v_inst_1840_);
lean_closure_set(v___f_1847_, 8, v_inst_1841_);
lean_closure_set(v___f_1847_, 9, v_toBind_1842_);
lean_closure_set(v___f_1847_, 10, v___x_1846_);
v___x_1848_ = l_Lean_KVMap_instValueBool;
v___x_1849_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_1850_ = l_Lean_Option_getM___redArg(v_inst_1837_, v_inst_1839_, v___x_1848_, v___x_1849_);
v___x_1851_ = lean_apply_4(v_toBind_1842_, lean_box(0), lean_box(0), v___x_1850_, v___f_1847_);
return v___x_1851_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg___lam__2___boxed(lean_object* v_n_1852_, lean_object* v_toApplicative_1853_, lean_object* v___x_1854_, lean_object* v_inst_1855_, lean_object* v_inst_1856_, lean_object* v_inst_1857_, lean_object* v_inst_1858_, lean_object* v_inst_1859_, lean_object* v_toBind_1860_, lean_object* v___x_1861_, lean_object* v_env_1862_){
_start:
{
uint8_t v___x_841__boxed_1863_; uint8_t v___x_847__boxed_1864_; lean_object* v_res_1865_; 
v___x_841__boxed_1863_ = lean_unbox(v___x_1854_);
v___x_847__boxed_1864_ = lean_unbox(v___x_1861_);
v_res_1865_ = l_Lean_isInaccessiblePrivateName___redArg___lam__2(v_n_1852_, v_toApplicative_1853_, v___x_841__boxed_1863_, v_inst_1855_, v_inst_1856_, v_inst_1857_, v_inst_1858_, v_inst_1859_, v_toBind_1860_, v___x_847__boxed_1864_, v_env_1862_);
return v_res_1865_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg(lean_object* v_inst_1866_, lean_object* v_inst_1867_, lean_object* v_inst_1868_, lean_object* v_inst_1869_, lean_object* v_inst_1870_, lean_object* v_n_1871_){
_start:
{
uint8_t v___x_1872_; 
v___x_1872_ = l_Lean_isPrivateName(v_n_1871_);
if (v___x_1872_ == 0)
{
lean_object* v_toApplicative_1873_; lean_object* v_toPure_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; 
lean_dec(v_n_1871_);
lean_dec(v_inst_1870_);
lean_dec_ref(v_inst_1869_);
lean_dec(v_inst_1867_);
lean_dec_ref(v_inst_1866_);
v_toApplicative_1873_ = lean_ctor_get(v_inst_1868_, 0);
lean_inc_ref(v_toApplicative_1873_);
lean_dec_ref(v_inst_1868_);
v_toPure_1874_ = lean_ctor_get(v_toApplicative_1873_, 1);
lean_inc(v_toPure_1874_);
lean_dec_ref(v_toApplicative_1873_);
v___x_1875_ = lean_box(v___x_1872_);
v___x_1876_ = lean_apply_2(v_toPure_1874_, lean_box(0), v___x_1875_);
return v___x_1876_;
}
else
{
lean_object* v_toApplicative_1877_; lean_object* v_toBind_1878_; lean_object* v_getEnv_1879_; uint8_t v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___f_1883_; lean_object* v___x_1884_; 
v_toApplicative_1877_ = lean_ctor_get(v_inst_1868_, 0);
lean_inc_ref(v_toApplicative_1877_);
v_toBind_1878_ = lean_ctor_get(v_inst_1868_, 1);
lean_inc_n(v_toBind_1878_, 2);
v_getEnv_1879_ = lean_ctor_get(v_inst_1869_, 0);
lean_inc(v_getEnv_1879_);
v___x_1880_ = 0;
v___x_1881_ = lean_box(v___x_1872_);
v___x_1882_ = lean_box(v___x_1880_);
v___f_1883_ = lean_alloc_closure((void*)(l_Lean_isInaccessiblePrivateName___redArg___lam__2___boxed), 11, 10);
lean_closure_set(v___f_1883_, 0, v_n_1871_);
lean_closure_set(v___f_1883_, 1, v_toApplicative_1877_);
lean_closure_set(v___f_1883_, 2, v___x_1881_);
lean_closure_set(v___f_1883_, 3, v_inst_1868_);
lean_closure_set(v___f_1883_, 4, v_inst_1869_);
lean_closure_set(v___f_1883_, 5, v_inst_1870_);
lean_closure_set(v___f_1883_, 6, v_inst_1866_);
lean_closure_set(v___f_1883_, 7, v_inst_1867_);
lean_closure_set(v___f_1883_, 8, v_toBind_1878_);
lean_closure_set(v___f_1883_, 9, v___x_1882_);
v___x_1884_ = lean_apply_4(v_toBind_1878_, lean_box(0), lean_box(0), v_getEnv_1879_, v___f_1883_);
return v___x_1884_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName(lean_object* v_m_1885_, lean_object* v_inst_1886_, lean_object* v_inst_1887_, lean_object* v_inst_1888_, lean_object* v_inst_1889_, lean_object* v_inst_1890_, lean_object* v_n_1891_){
_start:
{
lean_object* v___x_1892_; 
v___x_1892_ = l_Lean_isInaccessiblePrivateName___redArg(v_inst_1886_, v_inst_1887_, v_inst_1888_, v_inst_1889_, v_inst_1890_, v_n_1891_);
return v___x_1892_;
}
}
LEAN_EXPORT uint8_t l_Lean_resolveGlobalName___redArg___lam__0(lean_object* v_x_1893_){
_start:
{
lean_object* v_fst_1894_; uint8_t v___x_1895_; 
v_fst_1894_ = lean_ctor_get(v_x_1893_, 0);
v___x_1895_ = l_Lean_isPrivateName(v_fst_1894_);
return v___x_1895_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__0___boxed(lean_object* v_x_1896_){
_start:
{
uint8_t v_res_1897_; lean_object* v_r_1898_; 
v_res_1897_ = l_Lean_resolveGlobalName___redArg___lam__0(v_x_1896_);
lean_dec_ref(v_x_1896_);
v_r_1898_ = lean_box(v_res_1897_);
return v_r_1898_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__1(lean_object* v_toPure_1899_, lean_object* v_res_1900_, lean_object* v_____r_1901_){
_start:
{
lean_object* v___x_1902_; 
v___x_1902_ = lean_apply_2(v_toPure_1899_, lean_box(0), v_res_1900_);
return v___x_1902_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__2(uint8_t v_enableLog_1903_, lean_object* v_toPure_1904_, lean_object* v_res_1905_, lean_object* v___f_1906_, lean_object* v_inst_1907_, lean_object* v_inst_1908_, lean_object* v_inst_1909_, lean_object* v_inst_1910_, lean_object* v_inst_1911_, lean_object* v_toBind_1912_, lean_object* v___f_1913_, lean_object* v_____do__lift_1914_){
_start:
{
if (v_enableLog_1903_ == 0)
{
lean_object* v___x_1915_; 
lean_dec(v___f_1913_);
lean_dec(v_toBind_1912_);
lean_dec(v_inst_1911_);
lean_dec_ref(v_inst_1910_);
lean_dec(v_inst_1909_);
lean_dec_ref(v_inst_1908_);
lean_dec_ref(v_inst_1907_);
lean_dec_ref(v___f_1906_);
v___x_1915_ = lean_apply_2(v_toPure_1904_, lean_box(0), v_res_1905_);
return v___x_1915_;
}
else
{
uint8_t v_isExporting_1916_; 
v_isExporting_1916_ = lean_ctor_get_uint8(v_____do__lift_1914_, sizeof(void*)*8);
if (v_isExporting_1916_ == 0)
{
lean_object* v___x_1917_; 
lean_dec(v___f_1913_);
lean_dec(v_toBind_1912_);
lean_dec(v_inst_1911_);
lean_dec_ref(v_inst_1910_);
lean_dec(v_inst_1909_);
lean_dec_ref(v_inst_1908_);
lean_dec_ref(v_inst_1907_);
lean_dec_ref(v___f_1906_);
v___x_1917_ = lean_apply_2(v_toPure_1904_, lean_box(0), v_res_1905_);
return v___x_1917_;
}
else
{
lean_object* v___x_1918_; 
lean_inc(v_res_1905_);
v___x_1918_ = l_List_find_x3f___redArg(v___f_1906_, v_res_1905_);
if (lean_obj_tag(v___x_1918_) == 1)
{
lean_object* v_val_1919_; lean_object* v_fst_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; 
lean_dec(v_res_1905_);
lean_dec(v_toPure_1904_);
v_val_1919_ = lean_ctor_get(v___x_1918_, 0);
lean_inc(v_val_1919_);
lean_dec_ref_known(v___x_1918_, 1);
v_fst_1920_ = lean_ctor_get(v_val_1919_, 0);
lean_inc(v_fst_1920_);
lean_dec(v_val_1919_);
v___x_1921_ = l_Lean_checkPrivateInPublic___redArg(v_inst_1907_, v_inst_1908_, v_inst_1909_, v_inst_1910_, v_inst_1911_, v_fst_1920_);
v___x_1922_ = lean_apply_4(v_toBind_1912_, lean_box(0), lean_box(0), v___x_1921_, v___f_1913_);
return v___x_1922_;
}
else
{
lean_object* v___x_1923_; 
lean_dec(v___x_1918_);
lean_dec(v___f_1913_);
lean_dec(v_toBind_1912_);
lean_dec(v_inst_1911_);
lean_dec_ref(v_inst_1910_);
lean_dec(v_inst_1909_);
lean_dec_ref(v_inst_1908_);
lean_dec_ref(v_inst_1907_);
v___x_1923_ = lean_apply_2(v_toPure_1904_, lean_box(0), v_res_1905_);
return v___x_1923_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__2___boxed(lean_object* v_enableLog_1924_, lean_object* v_toPure_1925_, lean_object* v_res_1926_, lean_object* v___f_1927_, lean_object* v_inst_1928_, lean_object* v_inst_1929_, lean_object* v_inst_1930_, lean_object* v_inst_1931_, lean_object* v_inst_1932_, lean_object* v_toBind_1933_, lean_object* v___f_1934_, lean_object* v_____do__lift_1935_){
_start:
{
uint8_t v_enableLog_boxed_1936_; lean_object* v_res_1937_; 
v_enableLog_boxed_1936_ = lean_unbox(v_enableLog_1924_);
v_res_1937_ = l_Lean_resolveGlobalName___redArg___lam__2(v_enableLog_boxed_1936_, v_toPure_1925_, v_res_1926_, v___f_1927_, v_inst_1928_, v_inst_1929_, v_inst_1930_, v_inst_1931_, v_inst_1932_, v_toBind_1933_, v___f_1934_, v_____do__lift_1935_);
lean_dec_ref(v_____do__lift_1935_);
return v_res_1937_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__3(lean_object* v_____do__lift_1938_, lean_object* v_____do__lift_1939_, lean_object* v_____do__lift_1940_, lean_object* v_id_1941_, lean_object* v_toPure_1942_, uint8_t v_enableLog_1943_, lean_object* v___f_1944_, lean_object* v_inst_1945_, lean_object* v_inst_1946_, lean_object* v_inst_1947_, lean_object* v_inst_1948_, lean_object* v_inst_1949_, lean_object* v_toBind_1950_, lean_object* v_getEnv_1951_, lean_object* v_____do__lift_1952_){
_start:
{
lean_object* v_res_1953_; lean_object* v___f_1954_; lean_object* v___x_1955_; lean_object* v___f_1956_; lean_object* v___x_1957_; 
v_res_1953_ = l_Lean_ResolveName_resolveGlobalName(v_____do__lift_1938_, v_____do__lift_1939_, v_____do__lift_1940_, v_____do__lift_1952_, v_id_1941_);
lean_inc(v_res_1953_);
lean_inc(v_toPure_1942_);
v___f_1954_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalName___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1954_, 0, v_toPure_1942_);
lean_closure_set(v___f_1954_, 1, v_res_1953_);
v___x_1955_ = lean_box(v_enableLog_1943_);
lean_inc(v_toBind_1950_);
v___f_1956_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalName___redArg___lam__2___boxed), 12, 11);
lean_closure_set(v___f_1956_, 0, v___x_1955_);
lean_closure_set(v___f_1956_, 1, v_toPure_1942_);
lean_closure_set(v___f_1956_, 2, v_res_1953_);
lean_closure_set(v___f_1956_, 3, v___f_1944_);
lean_closure_set(v___f_1956_, 4, v_inst_1945_);
lean_closure_set(v___f_1956_, 5, v_inst_1946_);
lean_closure_set(v___f_1956_, 6, v_inst_1947_);
lean_closure_set(v___f_1956_, 7, v_inst_1948_);
lean_closure_set(v___f_1956_, 8, v_inst_1949_);
lean_closure_set(v___f_1956_, 9, v_toBind_1950_);
lean_closure_set(v___f_1956_, 10, v___f_1954_);
v___x_1957_ = lean_apply_4(v_toBind_1950_, lean_box(0), lean_box(0), v_getEnv_1951_, v___f_1956_);
return v___x_1957_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__3___boxed(lean_object* v_____do__lift_1958_, lean_object* v_____do__lift_1959_, lean_object* v_____do__lift_1960_, lean_object* v_id_1961_, lean_object* v_toPure_1962_, lean_object* v_enableLog_1963_, lean_object* v___f_1964_, lean_object* v_inst_1965_, lean_object* v_inst_1966_, lean_object* v_inst_1967_, lean_object* v_inst_1968_, lean_object* v_inst_1969_, lean_object* v_toBind_1970_, lean_object* v_getEnv_1971_, lean_object* v_____do__lift_1972_){
_start:
{
uint8_t v_enableLog_boxed_1973_; lean_object* v_res_1974_; 
v_enableLog_boxed_1973_ = lean_unbox(v_enableLog_1963_);
v_res_1974_ = l_Lean_resolveGlobalName___redArg___lam__3(v_____do__lift_1958_, v_____do__lift_1959_, v_____do__lift_1960_, v_id_1961_, v_toPure_1962_, v_enableLog_boxed_1973_, v___f_1964_, v_inst_1965_, v_inst_1966_, v_inst_1967_, v_inst_1968_, v_inst_1969_, v_toBind_1970_, v_getEnv_1971_, v_____do__lift_1972_);
lean_dec_ref(v_____do__lift_1959_);
return v_res_1974_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__4(lean_object* v_____do__lift_1975_, lean_object* v_____do__lift_1976_, lean_object* v_id_1977_, lean_object* v_toPure_1978_, uint8_t v_enableLog_1979_, lean_object* v___f_1980_, lean_object* v_inst_1981_, lean_object* v_inst_1982_, lean_object* v_inst_1983_, lean_object* v_inst_1984_, lean_object* v_inst_1985_, lean_object* v_toBind_1986_, lean_object* v_getEnv_1987_, lean_object* v_getOpenDecls_1988_, lean_object* v_____do__lift_1989_){
_start:
{
lean_object* v___x_1990_; lean_object* v___f_1991_; lean_object* v___x_1992_; 
v___x_1990_ = lean_box(v_enableLog_1979_);
lean_inc(v_toBind_1986_);
v___f_1991_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalName___redArg___lam__3___boxed), 15, 14);
lean_closure_set(v___f_1991_, 0, v_____do__lift_1975_);
lean_closure_set(v___f_1991_, 1, v_____do__lift_1976_);
lean_closure_set(v___f_1991_, 2, v_____do__lift_1989_);
lean_closure_set(v___f_1991_, 3, v_id_1977_);
lean_closure_set(v___f_1991_, 4, v_toPure_1978_);
lean_closure_set(v___f_1991_, 5, v___x_1990_);
lean_closure_set(v___f_1991_, 6, v___f_1980_);
lean_closure_set(v___f_1991_, 7, v_inst_1981_);
lean_closure_set(v___f_1991_, 8, v_inst_1982_);
lean_closure_set(v___f_1991_, 9, v_inst_1983_);
lean_closure_set(v___f_1991_, 10, v_inst_1984_);
lean_closure_set(v___f_1991_, 11, v_inst_1985_);
lean_closure_set(v___f_1991_, 12, v_toBind_1986_);
lean_closure_set(v___f_1991_, 13, v_getEnv_1987_);
v___x_1992_ = lean_apply_4(v_toBind_1986_, lean_box(0), lean_box(0), v_getOpenDecls_1988_, v___f_1991_);
return v___x_1992_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__4___boxed(lean_object* v_____do__lift_1993_, lean_object* v_____do__lift_1994_, lean_object* v_id_1995_, lean_object* v_toPure_1996_, lean_object* v_enableLog_1997_, lean_object* v___f_1998_, lean_object* v_inst_1999_, lean_object* v_inst_2000_, lean_object* v_inst_2001_, lean_object* v_inst_2002_, lean_object* v_inst_2003_, lean_object* v_toBind_2004_, lean_object* v_getEnv_2005_, lean_object* v_getOpenDecls_2006_, lean_object* v_____do__lift_2007_){
_start:
{
uint8_t v_enableLog_boxed_2008_; lean_object* v_res_2009_; 
v_enableLog_boxed_2008_ = lean_unbox(v_enableLog_1997_);
v_res_2009_ = l_Lean_resolveGlobalName___redArg___lam__4(v_____do__lift_1993_, v_____do__lift_1994_, v_id_1995_, v_toPure_1996_, v_enableLog_boxed_2008_, v___f_1998_, v_inst_1999_, v_inst_2000_, v_inst_2001_, v_inst_2002_, v_inst_2003_, v_toBind_2004_, v_getEnv_2005_, v_getOpenDecls_2006_, v_____do__lift_2007_);
return v_res_2009_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__5(lean_object* v_inst_2010_, lean_object* v_____do__lift_2011_, lean_object* v_id_2012_, lean_object* v_toPure_2013_, uint8_t v_enableLog_2014_, lean_object* v___f_2015_, lean_object* v_inst_2016_, lean_object* v_inst_2017_, lean_object* v_inst_2018_, lean_object* v_inst_2019_, lean_object* v_inst_2020_, lean_object* v_toBind_2021_, lean_object* v_getEnv_2022_, lean_object* v_____do__lift_2023_){
_start:
{
lean_object* v_getCurrNamespace_2024_; lean_object* v_getOpenDecls_2025_; lean_object* v___x_2026_; lean_object* v___f_2027_; lean_object* v___x_2028_; 
v_getCurrNamespace_2024_ = lean_ctor_get(v_inst_2010_, 0);
lean_inc(v_getCurrNamespace_2024_);
v_getOpenDecls_2025_ = lean_ctor_get(v_inst_2010_, 1);
lean_inc(v_getOpenDecls_2025_);
lean_dec_ref(v_inst_2010_);
v___x_2026_ = lean_box(v_enableLog_2014_);
lean_inc(v_toBind_2021_);
v___f_2027_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalName___redArg___lam__4___boxed), 15, 14);
lean_closure_set(v___f_2027_, 0, v_____do__lift_2011_);
lean_closure_set(v___f_2027_, 1, v_____do__lift_2023_);
lean_closure_set(v___f_2027_, 2, v_id_2012_);
lean_closure_set(v___f_2027_, 3, v_toPure_2013_);
lean_closure_set(v___f_2027_, 4, v___x_2026_);
lean_closure_set(v___f_2027_, 5, v___f_2015_);
lean_closure_set(v___f_2027_, 6, v_inst_2016_);
lean_closure_set(v___f_2027_, 7, v_inst_2017_);
lean_closure_set(v___f_2027_, 8, v_inst_2018_);
lean_closure_set(v___f_2027_, 9, v_inst_2019_);
lean_closure_set(v___f_2027_, 10, v_inst_2020_);
lean_closure_set(v___f_2027_, 11, v_toBind_2021_);
lean_closure_set(v___f_2027_, 12, v_getEnv_2022_);
lean_closure_set(v___f_2027_, 13, v_getOpenDecls_2025_);
v___x_2028_ = lean_apply_4(v_toBind_2021_, lean_box(0), lean_box(0), v_getCurrNamespace_2024_, v___f_2027_);
return v___x_2028_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__5___boxed(lean_object* v_inst_2029_, lean_object* v_____do__lift_2030_, lean_object* v_id_2031_, lean_object* v_toPure_2032_, lean_object* v_enableLog_2033_, lean_object* v___f_2034_, lean_object* v_inst_2035_, lean_object* v_inst_2036_, lean_object* v_inst_2037_, lean_object* v_inst_2038_, lean_object* v_inst_2039_, lean_object* v_toBind_2040_, lean_object* v_getEnv_2041_, lean_object* v_____do__lift_2042_){
_start:
{
uint8_t v_enableLog_boxed_2043_; lean_object* v_res_2044_; 
v_enableLog_boxed_2043_ = lean_unbox(v_enableLog_2033_);
v_res_2044_ = l_Lean_resolveGlobalName___redArg___lam__5(v_inst_2029_, v_____do__lift_2030_, v_id_2031_, v_toPure_2032_, v_enableLog_boxed_2043_, v___f_2034_, v_inst_2035_, v_inst_2036_, v_inst_2037_, v_inst_2038_, v_inst_2039_, v_toBind_2040_, v_getEnv_2041_, v_____do__lift_2042_);
return v_res_2044_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__6(lean_object* v_inst_2045_, lean_object* v_id_2046_, lean_object* v_toPure_2047_, uint8_t v_enableLog_2048_, lean_object* v___f_2049_, lean_object* v_inst_2050_, lean_object* v_inst_2051_, lean_object* v_inst_2052_, lean_object* v_inst_2053_, lean_object* v_inst_2054_, lean_object* v_toBind_2055_, lean_object* v_getEnv_2056_, lean_object* v_____do__lift_2057_){
_start:
{
lean_object* v___x_2058_; lean_object* v___f_2059_; lean_object* v___x_2060_; 
v___x_2058_ = lean_box(v_enableLog_2048_);
lean_inc(v_toBind_2055_);
lean_inc(v_inst_2052_);
v___f_2059_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalName___redArg___lam__5___boxed), 14, 13);
lean_closure_set(v___f_2059_, 0, v_inst_2045_);
lean_closure_set(v___f_2059_, 1, v_____do__lift_2057_);
lean_closure_set(v___f_2059_, 2, v_id_2046_);
lean_closure_set(v___f_2059_, 3, v_toPure_2047_);
lean_closure_set(v___f_2059_, 4, v___x_2058_);
lean_closure_set(v___f_2059_, 5, v___f_2049_);
lean_closure_set(v___f_2059_, 6, v_inst_2050_);
lean_closure_set(v___f_2059_, 7, v_inst_2051_);
lean_closure_set(v___f_2059_, 8, v_inst_2052_);
lean_closure_set(v___f_2059_, 9, v_inst_2053_);
lean_closure_set(v___f_2059_, 10, v_inst_2054_);
lean_closure_set(v___f_2059_, 11, v_toBind_2055_);
lean_closure_set(v___f_2059_, 12, v_getEnv_2056_);
v___x_2060_ = lean_apply_4(v_toBind_2055_, lean_box(0), lean_box(0), v_inst_2052_, v___f_2059_);
return v___x_2060_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__6___boxed(lean_object* v_inst_2061_, lean_object* v_id_2062_, lean_object* v_toPure_2063_, lean_object* v_enableLog_2064_, lean_object* v___f_2065_, lean_object* v_inst_2066_, lean_object* v_inst_2067_, lean_object* v_inst_2068_, lean_object* v_inst_2069_, lean_object* v_inst_2070_, lean_object* v_toBind_2071_, lean_object* v_getEnv_2072_, lean_object* v_____do__lift_2073_){
_start:
{
uint8_t v_enableLog_boxed_2074_; lean_object* v_res_2075_; 
v_enableLog_boxed_2074_ = lean_unbox(v_enableLog_2064_);
v_res_2075_ = l_Lean_resolveGlobalName___redArg___lam__6(v_inst_2061_, v_id_2062_, v_toPure_2063_, v_enableLog_boxed_2074_, v___f_2065_, v_inst_2066_, v_inst_2067_, v_inst_2068_, v_inst_2069_, v_inst_2070_, v_toBind_2071_, v_getEnv_2072_, v_____do__lift_2073_);
return v_res_2075_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg(lean_object* v_inst_2077_, lean_object* v_inst_2078_, lean_object* v_inst_2079_, lean_object* v_inst_2080_, lean_object* v_inst_2081_, lean_object* v_inst_2082_, lean_object* v_id_2083_, uint8_t v_enableLog_2084_){
_start:
{
lean_object* v_toApplicative_2085_; lean_object* v_toBind_2086_; lean_object* v_getEnv_2087_; lean_object* v_toPure_2088_; lean_object* v___f_2089_; lean_object* v___x_2090_; lean_object* v___f_2091_; lean_object* v___x_2092_; 
v_toApplicative_2085_ = lean_ctor_get(v_inst_2077_, 0);
v_toBind_2086_ = lean_ctor_get(v_inst_2077_, 1);
lean_inc_n(v_toBind_2086_, 2);
v_getEnv_2087_ = lean_ctor_get(v_inst_2079_, 0);
lean_inc_n(v_getEnv_2087_, 2);
v_toPure_2088_ = lean_ctor_get(v_toApplicative_2085_, 1);
lean_inc(v_toPure_2088_);
v___f_2089_ = ((lean_object*)(l_Lean_resolveGlobalName___redArg___closed__0));
v___x_2090_ = lean_box(v_enableLog_2084_);
v___f_2091_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalName___redArg___lam__6___boxed), 13, 12);
lean_closure_set(v___f_2091_, 0, v_inst_2078_);
lean_closure_set(v___f_2091_, 1, v_id_2083_);
lean_closure_set(v___f_2091_, 2, v_toPure_2088_);
lean_closure_set(v___f_2091_, 3, v___x_2090_);
lean_closure_set(v___f_2091_, 4, v___f_2089_);
lean_closure_set(v___f_2091_, 5, v_inst_2077_);
lean_closure_set(v___f_2091_, 6, v_inst_2079_);
lean_closure_set(v___f_2091_, 7, v_inst_2080_);
lean_closure_set(v___f_2091_, 8, v_inst_2081_);
lean_closure_set(v___f_2091_, 9, v_inst_2082_);
lean_closure_set(v___f_2091_, 10, v_toBind_2086_);
lean_closure_set(v___f_2091_, 11, v_getEnv_2087_);
v___x_2092_ = lean_apply_4(v_toBind_2086_, lean_box(0), lean_box(0), v_getEnv_2087_, v___f_2091_);
return v___x_2092_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___boxed(lean_object* v_inst_2093_, lean_object* v_inst_2094_, lean_object* v_inst_2095_, lean_object* v_inst_2096_, lean_object* v_inst_2097_, lean_object* v_inst_2098_, lean_object* v_id_2099_, lean_object* v_enableLog_2100_){
_start:
{
uint8_t v_enableLog_boxed_2101_; lean_object* v_res_2102_; 
v_enableLog_boxed_2101_ = lean_unbox(v_enableLog_2100_);
v_res_2102_ = l_Lean_resolveGlobalName___redArg(v_inst_2093_, v_inst_2094_, v_inst_2095_, v_inst_2096_, v_inst_2097_, v_inst_2098_, v_id_2099_, v_enableLog_boxed_2101_);
return v_res_2102_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName(lean_object* v_m_2103_, lean_object* v_inst_2104_, lean_object* v_inst_2105_, lean_object* v_inst_2106_, lean_object* v_inst_2107_, lean_object* v_inst_2108_, lean_object* v_inst_2109_, lean_object* v_id_2110_, uint8_t v_enableLog_2111_){
_start:
{
lean_object* v___x_2112_; 
v___x_2112_ = l_Lean_resolveGlobalName___redArg(v_inst_2104_, v_inst_2105_, v_inst_2106_, v_inst_2107_, v_inst_2108_, v_inst_2109_, v_id_2110_, v_enableLog_2111_);
return v___x_2112_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___boxed(lean_object* v_m_2113_, lean_object* v_inst_2114_, lean_object* v_inst_2115_, lean_object* v_inst_2116_, lean_object* v_inst_2117_, lean_object* v_inst_2118_, lean_object* v_inst_2119_, lean_object* v_id_2120_, lean_object* v_enableLog_2121_){
_start:
{
uint8_t v_enableLog_boxed_2122_; lean_object* v_res_2123_; 
v_enableLog_boxed_2122_ = lean_unbox(v_enableLog_2121_);
v_res_2123_ = l_Lean_resolveGlobalName(v_m_2113_, v_inst_2114_, v_inst_2115_, v_inst_2116_, v_inst_2117_, v_inst_2118_, v_inst_2119_, v_id_2120_, v_enableLog_boxed_2122_);
return v_res_2123_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__0(lean_object* v_toPure_2124_, lean_object* v_nss_2125_, lean_object* v_____r_2126_){
_start:
{
lean_object* v___x_2127_; 
v___x_2127_ = lean_apply_2(v_toPure_2124_, lean_box(0), v_nss_2125_);
return v___x_2127_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__1(lean_object* v_____do__lift_2130_, lean_object* v_____do__lift_2131_, lean_object* v_id_2132_, uint8_t v_allowEmpty_2133_, lean_object* v_toPure_2134_, lean_object* v_inst_2135_, lean_object* v_inst_2136_, lean_object* v_toBind_2137_, lean_object* v_____do__lift_2138_){
_start:
{
lean_object* v_nss_2139_; 
lean_inc(v_id_2132_);
v_nss_2139_ = l_Lean_ResolveName_resolveNamespace(v_____do__lift_2130_, v_____do__lift_2131_, v_____do__lift_2138_, v_id_2132_);
if (v_allowEmpty_2133_ == 0)
{
uint8_t v___x_2140_; 
v___x_2140_ = l_List_isEmpty___redArg(v_nss_2139_);
if (v___x_2140_ == 0)
{
lean_object* v___x_2141_; 
lean_dec(v_toBind_2137_);
lean_dec_ref(v_inst_2136_);
lean_dec_ref(v_inst_2135_);
lean_dec(v_id_2132_);
v___x_2141_ = lean_apply_2(v_toPure_2134_, lean_box(0), v_nss_2139_);
return v___x_2141_;
}
else
{
lean_object* v___f_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; 
v___f_2142_ = lean_alloc_closure((void*)(l_Lean_resolveNamespaceCore___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2142_, 0, v_toPure_2134_);
lean_closure_set(v___f_2142_, 1, v_nss_2139_);
v___x_2143_ = ((lean_object*)(l_Lean_resolveNamespaceCore___redArg___lam__1___closed__0));
v___x_2144_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_id_2132_, v___x_2140_);
v___x_2145_ = lean_string_append(v___x_2143_, v___x_2144_);
lean_dec_ref(v___x_2144_);
v___x_2146_ = ((lean_object*)(l_Lean_resolveNamespaceCore___redArg___lam__1___closed__1));
v___x_2147_ = lean_string_append(v___x_2145_, v___x_2146_);
v___x_2148_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2148_, 0, v___x_2147_);
v___x_2149_ = l_Lean_MessageData_ofFormat(v___x_2148_);
v___x_2150_ = l_Lean_throwError___redArg(v_inst_2135_, v_inst_2136_, v___x_2149_);
v___x_2151_ = lean_apply_4(v_toBind_2137_, lean_box(0), lean_box(0), v___x_2150_, v___f_2142_);
return v___x_2151_;
}
}
else
{
lean_object* v___x_2152_; 
lean_dec(v_toBind_2137_);
lean_dec_ref(v_inst_2136_);
lean_dec_ref(v_inst_2135_);
lean_dec(v_id_2132_);
v___x_2152_ = lean_apply_2(v_toPure_2134_, lean_box(0), v_nss_2139_);
return v___x_2152_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__1___boxed(lean_object* v_____do__lift_2153_, lean_object* v_____do__lift_2154_, lean_object* v_id_2155_, lean_object* v_allowEmpty_2156_, lean_object* v_toPure_2157_, lean_object* v_inst_2158_, lean_object* v_inst_2159_, lean_object* v_toBind_2160_, lean_object* v_____do__lift_2161_){
_start:
{
uint8_t v_allowEmpty_boxed_2162_; lean_object* v_res_2163_; 
v_allowEmpty_boxed_2162_ = lean_unbox(v_allowEmpty_2156_);
v_res_2163_ = l_Lean_resolveNamespaceCore___redArg___lam__1(v_____do__lift_2153_, v_____do__lift_2154_, v_id_2155_, v_allowEmpty_boxed_2162_, v_toPure_2157_, v_inst_2158_, v_inst_2159_, v_toBind_2160_, v_____do__lift_2161_);
return v_res_2163_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__2(lean_object* v_____do__lift_2164_, lean_object* v_id_2165_, uint8_t v_allowEmpty_2166_, lean_object* v_toPure_2167_, lean_object* v_inst_2168_, lean_object* v_inst_2169_, lean_object* v_toBind_2170_, lean_object* v_getOpenDecls_2171_, lean_object* v_____do__lift_2172_){
_start:
{
lean_object* v___x_2173_; lean_object* v___f_2174_; lean_object* v___x_2175_; 
v___x_2173_ = lean_box(v_allowEmpty_2166_);
lean_inc(v_toBind_2170_);
v___f_2174_ = lean_alloc_closure((void*)(l_Lean_resolveNamespaceCore___redArg___lam__1___boxed), 9, 8);
lean_closure_set(v___f_2174_, 0, v_____do__lift_2164_);
lean_closure_set(v___f_2174_, 1, v_____do__lift_2172_);
lean_closure_set(v___f_2174_, 2, v_id_2165_);
lean_closure_set(v___f_2174_, 3, v___x_2173_);
lean_closure_set(v___f_2174_, 4, v_toPure_2167_);
lean_closure_set(v___f_2174_, 5, v_inst_2168_);
lean_closure_set(v___f_2174_, 6, v_inst_2169_);
lean_closure_set(v___f_2174_, 7, v_toBind_2170_);
v___x_2175_ = lean_apply_4(v_toBind_2170_, lean_box(0), lean_box(0), v_getOpenDecls_2171_, v___f_2174_);
return v___x_2175_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__2___boxed(lean_object* v_____do__lift_2176_, lean_object* v_id_2177_, lean_object* v_allowEmpty_2178_, lean_object* v_toPure_2179_, lean_object* v_inst_2180_, lean_object* v_inst_2181_, lean_object* v_toBind_2182_, lean_object* v_getOpenDecls_2183_, lean_object* v_____do__lift_2184_){
_start:
{
uint8_t v_allowEmpty_boxed_2185_; lean_object* v_res_2186_; 
v_allowEmpty_boxed_2185_ = lean_unbox(v_allowEmpty_2178_);
v_res_2186_ = l_Lean_resolveNamespaceCore___redArg___lam__2(v_____do__lift_2176_, v_id_2177_, v_allowEmpty_boxed_2185_, v_toPure_2179_, v_inst_2180_, v_inst_2181_, v_toBind_2182_, v_getOpenDecls_2183_, v_____do__lift_2184_);
return v_res_2186_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__3(lean_object* v_inst_2187_, lean_object* v_id_2188_, uint8_t v_allowEmpty_2189_, lean_object* v_toPure_2190_, lean_object* v_inst_2191_, lean_object* v_inst_2192_, lean_object* v_toBind_2193_, lean_object* v_____do__lift_2194_){
_start:
{
lean_object* v_getCurrNamespace_2195_; lean_object* v_getOpenDecls_2196_; lean_object* v___x_2197_; lean_object* v___f_2198_; lean_object* v___x_2199_; 
v_getCurrNamespace_2195_ = lean_ctor_get(v_inst_2187_, 0);
lean_inc(v_getCurrNamespace_2195_);
v_getOpenDecls_2196_ = lean_ctor_get(v_inst_2187_, 1);
lean_inc(v_getOpenDecls_2196_);
lean_dec_ref(v_inst_2187_);
v___x_2197_ = lean_box(v_allowEmpty_2189_);
lean_inc(v_toBind_2193_);
v___f_2198_ = lean_alloc_closure((void*)(l_Lean_resolveNamespaceCore___redArg___lam__2___boxed), 9, 8);
lean_closure_set(v___f_2198_, 0, v_____do__lift_2194_);
lean_closure_set(v___f_2198_, 1, v_id_2188_);
lean_closure_set(v___f_2198_, 2, v___x_2197_);
lean_closure_set(v___f_2198_, 3, v_toPure_2190_);
lean_closure_set(v___f_2198_, 4, v_inst_2191_);
lean_closure_set(v___f_2198_, 5, v_inst_2192_);
lean_closure_set(v___f_2198_, 6, v_toBind_2193_);
lean_closure_set(v___f_2198_, 7, v_getOpenDecls_2196_);
v___x_2199_ = lean_apply_4(v_toBind_2193_, lean_box(0), lean_box(0), v_getCurrNamespace_2195_, v___f_2198_);
return v___x_2199_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__3___boxed(lean_object* v_inst_2200_, lean_object* v_id_2201_, lean_object* v_allowEmpty_2202_, lean_object* v_toPure_2203_, lean_object* v_inst_2204_, lean_object* v_inst_2205_, lean_object* v_toBind_2206_, lean_object* v_____do__lift_2207_){
_start:
{
uint8_t v_allowEmpty_boxed_2208_; lean_object* v_res_2209_; 
v_allowEmpty_boxed_2208_ = lean_unbox(v_allowEmpty_2202_);
v_res_2209_ = l_Lean_resolveNamespaceCore___redArg___lam__3(v_inst_2200_, v_id_2201_, v_allowEmpty_boxed_2208_, v_toPure_2203_, v_inst_2204_, v_inst_2205_, v_toBind_2206_, v_____do__lift_2207_);
return v_res_2209_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg(lean_object* v_inst_2210_, lean_object* v_inst_2211_, lean_object* v_inst_2212_, lean_object* v_inst_2213_, lean_object* v_id_2214_, uint8_t v_allowEmpty_2215_){
_start:
{
lean_object* v_toApplicative_2216_; lean_object* v_toBind_2217_; lean_object* v_getEnv_2218_; lean_object* v_toPure_2219_; lean_object* v___x_2220_; lean_object* v___f_2221_; lean_object* v___x_2222_; 
v_toApplicative_2216_ = lean_ctor_get(v_inst_2210_, 0);
v_toBind_2217_ = lean_ctor_get(v_inst_2210_, 1);
lean_inc_n(v_toBind_2217_, 2);
v_getEnv_2218_ = lean_ctor_get(v_inst_2212_, 0);
lean_inc(v_getEnv_2218_);
lean_dec_ref(v_inst_2212_);
v_toPure_2219_ = lean_ctor_get(v_toApplicative_2216_, 1);
lean_inc(v_toPure_2219_);
v___x_2220_ = lean_box(v_allowEmpty_2215_);
v___f_2221_ = lean_alloc_closure((void*)(l_Lean_resolveNamespaceCore___redArg___lam__3___boxed), 8, 7);
lean_closure_set(v___f_2221_, 0, v_inst_2211_);
lean_closure_set(v___f_2221_, 1, v_id_2214_);
lean_closure_set(v___f_2221_, 2, v___x_2220_);
lean_closure_set(v___f_2221_, 3, v_toPure_2219_);
lean_closure_set(v___f_2221_, 4, v_inst_2210_);
lean_closure_set(v___f_2221_, 5, v_inst_2213_);
lean_closure_set(v___f_2221_, 6, v_toBind_2217_);
v___x_2222_ = lean_apply_4(v_toBind_2217_, lean_box(0), lean_box(0), v_getEnv_2218_, v___f_2221_);
return v___x_2222_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___boxed(lean_object* v_inst_2223_, lean_object* v_inst_2224_, lean_object* v_inst_2225_, lean_object* v_inst_2226_, lean_object* v_id_2227_, lean_object* v_allowEmpty_2228_){
_start:
{
uint8_t v_allowEmpty_boxed_2229_; lean_object* v_res_2230_; 
v_allowEmpty_boxed_2229_ = lean_unbox(v_allowEmpty_2228_);
v_res_2230_ = l_Lean_resolveNamespaceCore___redArg(v_inst_2223_, v_inst_2224_, v_inst_2225_, v_inst_2226_, v_id_2227_, v_allowEmpty_boxed_2229_);
return v_res_2230_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore(lean_object* v_m_2231_, lean_object* v_inst_2232_, lean_object* v_inst_2233_, lean_object* v_inst_2234_, lean_object* v_inst_2235_, lean_object* v_id_2236_, uint8_t v_allowEmpty_2237_){
_start:
{
lean_object* v___x_2238_; 
v___x_2238_ = l_Lean_resolveNamespaceCore___redArg(v_inst_2232_, v_inst_2233_, v_inst_2234_, v_inst_2235_, v_id_2236_, v_allowEmpty_2237_);
return v___x_2238_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___boxed(lean_object* v_m_2239_, lean_object* v_inst_2240_, lean_object* v_inst_2241_, lean_object* v_inst_2242_, lean_object* v_inst_2243_, lean_object* v_id_2244_, lean_object* v_allowEmpty_2245_){
_start:
{
uint8_t v_allowEmpty_boxed_2246_; lean_object* v_res_2247_; 
v_allowEmpty_boxed_2246_ = lean_unbox(v_allowEmpty_2245_);
v_res_2247_ = l_Lean_resolveNamespaceCore(v_m_2239_, v_inst_2240_, v_inst_2241_, v_inst_2242_, v_inst_2243_, v_id_2244_, v_allowEmpty_boxed_2246_);
return v_res_2247_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespace___redArg___lam__0(lean_object* v_x_2248_){
_start:
{
if (lean_obj_tag(v_x_2248_) == 0)
{
lean_object* v_ns_2249_; lean_object* v___x_2251_; uint8_t v_isShared_2252_; uint8_t v_isSharedCheck_2256_; 
v_ns_2249_ = lean_ctor_get(v_x_2248_, 0);
v_isSharedCheck_2256_ = !lean_is_exclusive(v_x_2248_);
if (v_isSharedCheck_2256_ == 0)
{
v___x_2251_ = v_x_2248_;
v_isShared_2252_ = v_isSharedCheck_2256_;
goto v_resetjp_2250_;
}
else
{
lean_inc(v_ns_2249_);
lean_dec(v_x_2248_);
v___x_2251_ = lean_box(0);
v_isShared_2252_ = v_isSharedCheck_2256_;
goto v_resetjp_2250_;
}
v_resetjp_2250_:
{
lean_object* v___x_2254_; 
if (v_isShared_2252_ == 0)
{
lean_ctor_set_tag(v___x_2251_, 1);
v___x_2254_ = v___x_2251_;
goto v_reusejp_2253_;
}
else
{
lean_object* v_reuseFailAlloc_2255_; 
v_reuseFailAlloc_2255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2255_, 0, v_ns_2249_);
v___x_2254_ = v_reuseFailAlloc_2255_;
goto v_reusejp_2253_;
}
v_reusejp_2253_:
{
return v___x_2254_;
}
}
}
else
{
lean_object* v___x_2257_; 
lean_dec_ref(v_x_2248_);
v___x_2257_ = lean_box(0);
return v___x_2257_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespace___redArg___lam__1(lean_object* v_x_2258_, lean_object* v_withRef_2259_, lean_object* v___x_2260_, lean_object* v_oldRef_2261_){
_start:
{
lean_object* v_ref_2262_; lean_object* v___x_2263_; 
v_ref_2262_ = l_Lean_replaceRef(v_x_2258_, v_oldRef_2261_);
v___x_2263_ = lean_apply_3(v_withRef_2259_, lean_box(0), v_ref_2262_, v___x_2260_);
return v___x_2263_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespace___redArg___lam__1___boxed(lean_object* v_x_2264_, lean_object* v_withRef_2265_, lean_object* v___x_2266_, lean_object* v_oldRef_2267_){
_start:
{
lean_object* v_res_2268_; 
v_res_2268_ = l_Lean_resolveNamespace___redArg___lam__1(v_x_2264_, v_withRef_2265_, v___x_2266_, v_oldRef_2267_);
lean_dec(v_oldRef_2267_);
lean_dec(v_x_2264_);
return v_res_2268_;
}
}
static lean_object* _init_l_Lean_resolveNamespace___redArg___closed__4(void){
_start:
{
lean_object* v___x_2275_; lean_object* v___x_2276_; 
v___x_2275_ = ((lean_object*)(l_Lean_resolveNamespace___redArg___closed__3));
v___x_2276_ = l_Lean_MessageData_ofFormat(v___x_2275_);
return v___x_2276_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespace___redArg(lean_object* v_inst_2277_, lean_object* v_inst_2278_, lean_object* v_inst_2279_, lean_object* v_inst_2280_, lean_object* v_x_2281_){
_start:
{
if (lean_obj_tag(v_x_2281_) == 3)
{
lean_object* v_val_2282_; lean_object* v_preresolved_2283_; lean_object* v___f_2284_; lean_object* v___x_2285_; lean_object* v_pre_2286_; uint8_t v___x_2287_; 
v_val_2282_ = lean_ctor_get(v_x_2281_, 2);
v_preresolved_2283_ = lean_ctor_get(v_x_2281_, 3);
v___f_2284_ = ((lean_object*)(l_Lean_resolveNamespace___redArg___closed__0));
v___x_2285_ = ((lean_object*)(l_Lean_resolveNamespace___redArg___closed__1));
lean_inc(v_preresolved_2283_);
v_pre_2286_ = l_List_filterMapTR_go___redArg(v___f_2284_, v_preresolved_2283_, v___x_2285_);
v___x_2287_ = l_List_isEmpty___redArg(v_pre_2286_);
if (v___x_2287_ == 0)
{
lean_object* v_toApplicative_2288_; lean_object* v_toPure_2289_; lean_object* v___x_2290_; 
lean_dec_ref_known(v_x_2281_, 4);
lean_dec_ref(v_inst_2280_);
lean_dec_ref(v_inst_2279_);
lean_dec_ref(v_inst_2278_);
v_toApplicative_2288_ = lean_ctor_get(v_inst_2277_, 0);
lean_inc_ref(v_toApplicative_2288_);
lean_dec_ref(v_inst_2277_);
v_toPure_2289_ = lean_ctor_get(v_toApplicative_2288_, 1);
lean_inc(v_toPure_2289_);
lean_dec_ref(v_toApplicative_2288_);
v___x_2290_ = lean_apply_2(v_toPure_2289_, lean_box(0), v_pre_2286_);
return v___x_2290_;
}
else
{
lean_object* v_toMonadRef_2291_; lean_object* v_toBind_2292_; lean_object* v_getRef_2293_; lean_object* v_withRef_2294_; uint8_t v___x_2295_; lean_object* v___x_2296_; lean_object* v___f_2297_; lean_object* v___x_2298_; 
lean_dec(v_pre_2286_);
v_toMonadRef_2291_ = lean_ctor_get(v_inst_2280_, 1);
v_toBind_2292_ = lean_ctor_get(v_inst_2277_, 1);
lean_inc(v_toBind_2292_);
v_getRef_2293_ = lean_ctor_get(v_toMonadRef_2291_, 0);
lean_inc(v_getRef_2293_);
v_withRef_2294_ = lean_ctor_get(v_toMonadRef_2291_, 1);
lean_inc(v_withRef_2294_);
v___x_2295_ = 0;
lean_inc(v_val_2282_);
v___x_2296_ = l_Lean_resolveNamespaceCore___redArg(v_inst_2277_, v_inst_2278_, v_inst_2279_, v_inst_2280_, v_val_2282_, v___x_2295_);
v___f_2297_ = lean_alloc_closure((void*)(l_Lean_resolveNamespace___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_2297_, 0, v_x_2281_);
lean_closure_set(v___f_2297_, 1, v_withRef_2294_);
lean_closure_set(v___f_2297_, 2, v___x_2296_);
v___x_2298_ = lean_apply_4(v_toBind_2292_, lean_box(0), lean_box(0), v_getRef_2293_, v___f_2297_);
return v___x_2298_;
}
}
else
{
lean_object* v___x_2299_; lean_object* v___x_2300_; 
lean_dec_ref(v_inst_2279_);
lean_dec_ref(v_inst_2278_);
v___x_2299_ = lean_obj_once(&l_Lean_resolveNamespace___redArg___closed__4, &l_Lean_resolveNamespace___redArg___closed__4_once, _init_l_Lean_resolveNamespace___redArg___closed__4);
v___x_2300_ = l_Lean_throwErrorAt___redArg(v_inst_2277_, v_inst_2280_, v_x_2281_, v___x_2299_);
return v___x_2300_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespace(lean_object* v_m_2301_, lean_object* v_inst_2302_, lean_object* v_inst_2303_, lean_object* v_inst_2304_, lean_object* v_inst_2305_, lean_object* v_x_2306_){
_start:
{
lean_object* v___x_2307_; 
v___x_2307_ = l_Lean_resolveNamespace___redArg(v_inst_2302_, v_inst_2303_, v_inst_2304_, v_inst_2305_, v_x_2306_);
return v___x_2307_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveUniqueNamespace___redArg___lam__0(lean_object* v_id_2310_, lean_object* v___f_2311_, lean_object* v_inst_2312_, lean_object* v_inst_2313_, lean_object* v_toPure_2314_, lean_object* v_____do__lift_2315_){
_start:
{
if (lean_obj_tag(v_____do__lift_2315_) == 1)
{
lean_object* v_tail_2331_; 
v_tail_2331_ = lean_ctor_get(v_____do__lift_2315_, 1);
if (lean_obj_tag(v_tail_2331_) == 0)
{
lean_object* v_head_2332_; lean_object* v___x_2333_; 
lean_dec_ref(v_inst_2313_);
lean_dec_ref(v_inst_2312_);
lean_dec_ref(v___f_2311_);
v_head_2332_ = lean_ctor_get(v_____do__lift_2315_, 0);
lean_inc(v_head_2332_);
lean_dec_ref_known(v_____do__lift_2315_, 2);
v___x_2333_ = lean_apply_2(v_toPure_2314_, lean_box(0), v_head_2332_);
return v___x_2333_;
}
else
{
lean_dec(v_toPure_2314_);
goto v___jp_2316_;
}
}
else
{
lean_dec(v_toPure_2314_);
goto v___jp_2316_;
}
v___jp_2316_:
{
lean_object* v___x_2317_; lean_object* v___x_2318_; uint8_t v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; 
v___x_2317_ = ((lean_object*)(l_Lean_resolveUniqueNamespace___redArg___lam__0___closed__0));
v___x_2318_ = l_Lean_TSyntax_getId(v_id_2310_);
v___x_2319_ = 1;
v___x_2320_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2318_, v___x_2319_);
v___x_2321_ = lean_string_append(v___x_2317_, v___x_2320_);
lean_dec_ref(v___x_2320_);
v___x_2322_ = ((lean_object*)(l_Lean_resolveUniqueNamespace___redArg___lam__0___closed__1));
v___x_2323_ = lean_string_append(v___x_2321_, v___x_2322_);
v___x_2324_ = l_List_toString___redArg(v___f_2311_, v_____do__lift_2315_);
v___x_2325_ = lean_string_append(v___x_2323_, v___x_2324_);
lean_dec_ref(v___x_2324_);
v___x_2326_ = ((lean_object*)(l_Lean_resolveNamespaceCore___redArg___lam__1___closed__1));
v___x_2327_ = lean_string_append(v___x_2325_, v___x_2326_);
v___x_2328_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2328_, 0, v___x_2327_);
v___x_2329_ = l_Lean_MessageData_ofFormat(v___x_2328_);
v___x_2330_ = l_Lean_throwError___redArg(v_inst_2312_, v_inst_2313_, v___x_2329_);
return v___x_2330_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveUniqueNamespace___redArg___lam__0___boxed(lean_object* v_id_2334_, lean_object* v___f_2335_, lean_object* v_inst_2336_, lean_object* v_inst_2337_, lean_object* v_toPure_2338_, lean_object* v_____do__lift_2339_){
_start:
{
lean_object* v_res_2340_; 
v_res_2340_ = l_Lean_resolveUniqueNamespace___redArg___lam__0(v_id_2334_, v___f_2335_, v_inst_2336_, v_inst_2337_, v_toPure_2338_, v_____do__lift_2339_);
lean_dec(v_id_2334_);
return v_res_2340_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveUniqueNamespace___redArg(lean_object* v_inst_2342_, lean_object* v_inst_2343_, lean_object* v_inst_2344_, lean_object* v_inst_2345_, lean_object* v_id_2346_){
_start:
{
lean_object* v_toApplicative_2347_; lean_object* v_toBind_2348_; lean_object* v_toPure_2349_; lean_object* v___f_2350_; lean_object* v___x_2351_; lean_object* v___f_2352_; lean_object* v___x_2353_; 
v_toApplicative_2347_ = lean_ctor_get(v_inst_2342_, 0);
v_toBind_2348_ = lean_ctor_get(v_inst_2342_, 1);
lean_inc(v_toBind_2348_);
v_toPure_2349_ = lean_ctor_get(v_toApplicative_2347_, 1);
lean_inc(v_toPure_2349_);
v___f_2350_ = ((lean_object*)(l_Lean_resolveUniqueNamespace___redArg___closed__0));
lean_inc(v_id_2346_);
lean_inc_ref(v_inst_2345_);
lean_inc_ref(v_inst_2342_);
v___x_2351_ = l_Lean_resolveNamespace___redArg(v_inst_2342_, v_inst_2343_, v_inst_2344_, v_inst_2345_, v_id_2346_);
v___f_2352_ = lean_alloc_closure((void*)(l_Lean_resolveUniqueNamespace___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_2352_, 0, v_id_2346_);
lean_closure_set(v___f_2352_, 1, v___f_2350_);
lean_closure_set(v___f_2352_, 2, v_inst_2342_);
lean_closure_set(v___f_2352_, 3, v_inst_2345_);
lean_closure_set(v___f_2352_, 4, v_toPure_2349_);
v___x_2353_ = lean_apply_4(v_toBind_2348_, lean_box(0), lean_box(0), v___x_2351_, v___f_2352_);
return v___x_2353_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveUniqueNamespace(lean_object* v_m_2354_, lean_object* v_inst_2355_, lean_object* v_inst_2356_, lean_object* v_inst_2357_, lean_object* v_inst_2358_, lean_object* v_id_2359_){
_start:
{
lean_object* v___x_2360_; 
v___x_2360_ = l_Lean_resolveUniqueNamespace___redArg(v_inst_2355_, v_inst_2356_, v_inst_2357_, v_inst_2358_, v_id_2359_);
return v___x_2360_;
}
}
LEAN_EXPORT uint8_t l_Lean_filterFieldList___redArg___lam__0(lean_object* v_x_2361_){
_start:
{
lean_object* v_snd_2362_; uint8_t v___x_2363_; 
v_snd_2362_ = lean_ctor_get(v_x_2361_, 1);
v___x_2363_ = l_List_isEmpty___redArg(v_snd_2362_);
return v___x_2363_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg___lam__0___boxed(lean_object* v_x_2364_){
_start:
{
uint8_t v_res_2365_; lean_object* v_r_2366_; 
v_res_2365_ = l_Lean_filterFieldList___redArg___lam__0(v_x_2364_);
lean_dec_ref(v_x_2364_);
v_r_2366_ = lean_box(v_res_2365_);
return v_r_2366_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg___lam__1(lean_object* v_x_2367_){
_start:
{
lean_object* v_fst_2368_; 
v_fst_2368_ = lean_ctor_get(v_x_2367_, 0);
lean_inc(v_fst_2368_);
return v_fst_2368_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg___lam__1___boxed(lean_object* v_x_2369_){
_start:
{
lean_object* v_res_2370_; 
v_res_2370_ = l_Lean_filterFieldList___redArg___lam__1(v_x_2369_);
lean_dec_ref(v_x_2369_);
return v_res_2370_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg___lam__2(lean_object* v___f_2371_, lean_object* v_cs_2372_, lean_object* v_toPure_2373_, lean_object* v_____r_2374_){
_start:
{
lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; 
v___x_2375_ = lean_box(0);
v___x_2376_ = l_List_mapTR_loop___redArg(v___f_2371_, v_cs_2372_, v___x_2375_);
v___x_2377_ = lean_apply_2(v_toPure_2373_, lean_box(0), v___x_2376_);
return v___x_2377_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg___lam__3(lean_object* v___f_2378_, lean_object* v_____r_2379_){
_start:
{
lean_object* v___x_2380_; 
v___x_2380_ = lean_apply_1(v___f_2378_, v_____r_2379_);
return v___x_2380_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg___lam__4(lean_object* v_inst_2381_, lean_object* v_inst_2382_, lean_object* v_inst_2383_, lean_object* v_n_2384_, lean_object* v_toBind_2385_, lean_object* v___f_2386_, lean_object* v_____do__lift_2387_){
_start:
{
lean_object* v___x_2388_; lean_object* v___x_2389_; 
v___x_2388_ = l_Lean_throwUnknownConstantAt___redArg(v_inst_2381_, v_inst_2382_, v_inst_2383_, v_____do__lift_2387_, v_n_2384_);
v___x_2389_ = lean_apply_4(v_toBind_2385_, lean_box(0), lean_box(0), v___x_2388_, v___f_2386_);
return v___x_2389_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg(lean_object* v_inst_2392_, lean_object* v_inst_2393_, lean_object* v_inst_2394_, lean_object* v_n_2395_, lean_object* v_cs_2396_){
_start:
{
lean_object* v_toApplicative_2397_; lean_object* v_toBind_2398_; lean_object* v_toPure_2399_; lean_object* v___f_2400_; lean_object* v___f_2401_; lean_object* v___x_2402_; lean_object* v_cs_2403_; lean_object* v___f_2404_; uint8_t v___x_2405_; 
v_toApplicative_2397_ = lean_ctor_get(v_inst_2392_, 0);
v_toBind_2398_ = lean_ctor_get(v_inst_2392_, 1);
lean_inc(v_toBind_2398_);
v_toPure_2399_ = lean_ctor_get(v_toApplicative_2397_, 1);
v___f_2400_ = ((lean_object*)(l_Lean_filterFieldList___redArg___closed__0));
v___f_2401_ = ((lean_object*)(l_Lean_filterFieldList___redArg___closed__1));
v___x_2402_ = lean_box(0);
v_cs_2403_ = l_List_filterTR_loop___redArg(v___f_2400_, v_cs_2396_, v___x_2402_);
lean_inc(v_toPure_2399_);
lean_inc(v_cs_2403_);
v___f_2404_ = lean_alloc_closure((void*)(l_Lean_filterFieldList___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2404_, 0, v___f_2401_);
lean_closure_set(v___f_2404_, 1, v_cs_2403_);
lean_closure_set(v___f_2404_, 2, v_toPure_2399_);
v___x_2405_ = l_List_isEmpty___redArg(v_cs_2403_);
if (v___x_2405_ == 0)
{
lean_object* v___x_2406_; lean_object* v___x_2407_; 
lean_inc(v_toPure_2399_);
lean_dec_ref(v___f_2404_);
lean_dec(v_toBind_2398_);
lean_dec(v_n_2395_);
lean_dec_ref(v_inst_2394_);
lean_dec_ref(v_inst_2393_);
lean_dec_ref(v_inst_2392_);
v___x_2406_ = lean_box(0);
v___x_2407_ = l_Lean_filterFieldList___redArg___lam__2(v___f_2401_, v_cs_2403_, v_toPure_2399_, v___x_2406_);
return v___x_2407_;
}
else
{
lean_object* v_toMonadRef_2408_; lean_object* v_getRef_2409_; lean_object* v___f_2410_; lean_object* v___f_2411_; lean_object* v___x_2412_; 
lean_dec(v_cs_2403_);
v_toMonadRef_2408_ = lean_ctor_get(v_inst_2394_, 1);
v_getRef_2409_ = lean_ctor_get(v_toMonadRef_2408_, 0);
lean_inc(v_getRef_2409_);
v___f_2410_ = lean_alloc_closure((void*)(l_Lean_filterFieldList___redArg___lam__3), 2, 1);
lean_closure_set(v___f_2410_, 0, v___f_2404_);
lean_inc(v_toBind_2398_);
v___f_2411_ = lean_alloc_closure((void*)(l_Lean_filterFieldList___redArg___lam__4), 7, 6);
lean_closure_set(v___f_2411_, 0, v_inst_2392_);
lean_closure_set(v___f_2411_, 1, v_inst_2393_);
lean_closure_set(v___f_2411_, 2, v_inst_2394_);
lean_closure_set(v___f_2411_, 3, v_n_2395_);
lean_closure_set(v___f_2411_, 4, v_toBind_2398_);
lean_closure_set(v___f_2411_, 5, v___f_2410_);
v___x_2412_ = lean_apply_4(v_toBind_2398_, lean_box(0), lean_box(0), v_getRef_2409_, v___f_2411_);
return v___x_2412_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList(lean_object* v_m_2413_, lean_object* v_inst_2414_, lean_object* v_inst_2415_, lean_object* v_inst_2416_, lean_object* v_n_2417_, lean_object* v_cs_2418_){
_start:
{
lean_object* v___x_2419_; 
v___x_2419_ = l_Lean_filterFieldList___redArg(v_inst_2414_, v_inst_2415_, v_inst_2416_, v_n_2417_, v_cs_2418_);
return v___x_2419_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___redArg___lam__0(lean_object* v_inst_2420_, lean_object* v_inst_2421_, lean_object* v_inst_2422_, lean_object* v_n_2423_, lean_object* v_cs_2424_){
_start:
{
lean_object* v___x_2425_; 
v___x_2425_ = l_Lean_filterFieldList___redArg(v_inst_2420_, v_inst_2421_, v_inst_2422_, v_n_2423_, v_cs_2424_);
return v___x_2425_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___redArg(lean_object* v_inst_2426_, lean_object* v_inst_2427_, lean_object* v_inst_2428_, lean_object* v_inst_2429_, lean_object* v_inst_2430_, lean_object* v_inst_2431_, lean_object* v_inst_2432_, lean_object* v_n_2433_){
_start:
{
lean_object* v_toBind_2434_; lean_object* v___f_2435_; uint8_t v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; 
v_toBind_2434_ = lean_ctor_get(v_inst_2426_, 1);
lean_inc(v_toBind_2434_);
lean_inc(v_n_2433_);
lean_inc_ref(v_inst_2428_);
lean_inc_ref(v_inst_2426_);
v___f_2435_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___redArg___lam__0), 5, 4);
lean_closure_set(v___f_2435_, 0, v_inst_2426_);
lean_closure_set(v___f_2435_, 1, v_inst_2428_);
lean_closure_set(v___f_2435_, 2, v_inst_2432_);
lean_closure_set(v___f_2435_, 3, v_n_2433_);
v___x_2436_ = 1;
v___x_2437_ = l_Lean_resolveGlobalName___redArg(v_inst_2426_, v_inst_2427_, v_inst_2428_, v_inst_2429_, v_inst_2430_, v_inst_2431_, v_n_2433_, v___x_2436_);
v___x_2438_ = lean_apply_4(v_toBind_2434_, lean_box(0), lean_box(0), v___x_2437_, v___f_2435_);
return v___x_2438_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore(lean_object* v_m_2439_, lean_object* v_inst_2440_, lean_object* v_inst_2441_, lean_object* v_inst_2442_, lean_object* v_inst_2443_, lean_object* v_inst_2444_, lean_object* v_inst_2445_, lean_object* v_inst_2446_, lean_object* v_n_2447_){
_start:
{
lean_object* v___x_2448_; 
v___x_2448_ = l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___redArg(v_inst_2440_, v_inst_2441_, v_inst_2442_, v_inst_2443_, v_inst_2444_, v_inst_2445_, v_inst_2446_, v_n_2447_);
return v___x_2448_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNoOverload___redArg___lam__0(lean_object* v_declName_2449_){
_start:
{
lean_object* v___x_2450_; lean_object* v___x_2451_; 
v___x_2450_ = lean_box(0);
v___x_2451_ = l_Lean_mkConst(v_declName_2449_, v___x_2450_);
return v___x_2451_;
}
}
static lean_object* _init_l_Lean_ensureNoOverload___redArg___closed__2(void){
_start:
{
lean_object* v___x_2454_; lean_object* v___x_2455_; 
v___x_2454_ = ((lean_object*)(l_Lean_ensureNoOverload___redArg___closed__1));
v___x_2455_ = l_Lean_stringToMessageData(v___x_2454_);
return v___x_2455_;
}
}
static lean_object* _init_l_Lean_ensureNoOverload___redArg___closed__4(void){
_start:
{
lean_object* v___x_2457_; lean_object* v___x_2458_; 
v___x_2457_ = ((lean_object*)(l_Lean_ensureNoOverload___redArg___closed__3));
v___x_2458_ = l_Lean_stringToMessageData(v___x_2457_);
return v___x_2458_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNoOverload___redArg(lean_object* v_inst_2460_, lean_object* v_inst_2461_, lean_object* v_n_2462_, lean_object* v_cs_2463_){
_start:
{
lean_object* v_toApplicative_2464_; lean_object* v_toPure_2465_; lean_object* v___f_2466_; 
v_toApplicative_2464_ = lean_ctor_get(v_inst_2460_, 0);
v_toPure_2465_ = lean_ctor_get(v_toApplicative_2464_, 1);
v___f_2466_ = ((lean_object*)(l_Lean_ensureNoOverload___redArg___closed__0));
if (lean_obj_tag(v_cs_2463_) == 1)
{
lean_object* v_tail_2480_; 
v_tail_2480_ = lean_ctor_get(v_cs_2463_, 1);
if (lean_obj_tag(v_tail_2480_) == 0)
{
lean_object* v_head_2481_; lean_object* v___x_2482_; 
lean_inc(v_toPure_2465_);
lean_dec(v_n_2462_);
lean_dec_ref(v_inst_2461_);
lean_dec_ref(v_inst_2460_);
v_head_2481_ = lean_ctor_get(v_cs_2463_, 0);
lean_inc(v_head_2481_);
lean_dec_ref_known(v_cs_2463_, 2);
v___x_2482_ = lean_apply_2(v_toPure_2465_, lean_box(0), v_head_2481_);
return v___x_2482_;
}
else
{
goto v___jp_2467_;
}
}
else
{
goto v___jp_2467_;
}
v___jp_2467_:
{
lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; 
v___x_2468_ = lean_obj_once(&l_Lean_ensureNoOverload___redArg___closed__2, &l_Lean_ensureNoOverload___redArg___closed__2_once, _init_l_Lean_ensureNoOverload___redArg___closed__2);
v___x_2469_ = l_Lean_MessageData_ofName(v_n_2462_);
v___x_2470_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2470_, 0, v___x_2468_);
lean_ctor_set(v___x_2470_, 1, v___x_2469_);
v___x_2471_ = lean_obj_once(&l_Lean_ensureNoOverload___redArg___closed__4, &l_Lean_ensureNoOverload___redArg___closed__4_once, _init_l_Lean_ensureNoOverload___redArg___closed__4);
v___x_2472_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2472_, 0, v___x_2470_);
lean_ctor_set(v___x_2472_, 1, v___x_2471_);
v___x_2473_ = lean_box(0);
v___x_2474_ = l_List_mapTR_loop___redArg(v___f_2466_, v_cs_2463_, v___x_2473_);
v___x_2475_ = ((lean_object*)(l_Lean_ensureNoOverload___redArg___closed__5));
v___x_2476_ = l_List_mapTR_loop___redArg(v___x_2475_, v___x_2474_, v___x_2473_);
v___x_2477_ = l_Lean_MessageData_ofList(v___x_2476_);
v___x_2478_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2478_, 0, v___x_2472_);
lean_ctor_set(v___x_2478_, 1, v___x_2477_);
v___x_2479_ = l_Lean_throwError___redArg(v_inst_2460_, v_inst_2461_, v___x_2478_);
return v___x_2479_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNoOverload(lean_object* v_m_2483_, lean_object* v_inst_2484_, lean_object* v_inst_2485_, lean_object* v_n_2486_, lean_object* v_cs_2487_){
_start:
{
lean_object* v___x_2488_; 
v___x_2488_ = l_Lean_ensureNoOverload___redArg(v_inst_2484_, v_inst_2485_, v_n_2486_, v_cs_2487_);
return v___x_2488_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverloadCore___redArg___lam__0(lean_object* v_inst_2489_, lean_object* v_inst_2490_, lean_object* v_n_2491_, lean_object* v_____do__lift_2492_){
_start:
{
lean_object* v___x_2493_; 
v___x_2493_ = l_Lean_ensureNoOverload___redArg(v_inst_2489_, v_inst_2490_, v_n_2491_, v_____do__lift_2492_);
return v___x_2493_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverloadCore___redArg(lean_object* v_inst_2494_, lean_object* v_inst_2495_, lean_object* v_inst_2496_, lean_object* v_inst_2497_, lean_object* v_inst_2498_, lean_object* v_inst_2499_, lean_object* v_inst_2500_, lean_object* v_n_2501_){
_start:
{
lean_object* v_toBind_2502_; lean_object* v___f_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; 
v_toBind_2502_ = lean_ctor_get(v_inst_2494_, 1);
lean_inc(v_toBind_2502_);
lean_inc(v_n_2501_);
lean_inc_ref(v_inst_2500_);
lean_inc_ref(v_inst_2494_);
v___f_2503_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalConstNoOverloadCore___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2503_, 0, v_inst_2494_);
lean_closure_set(v___f_2503_, 1, v_inst_2500_);
lean_closure_set(v___f_2503_, 2, v_n_2501_);
v___x_2504_ = l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___redArg(v_inst_2494_, v_inst_2495_, v_inst_2496_, v_inst_2497_, v_inst_2498_, v_inst_2499_, v_inst_2500_, v_n_2501_);
v___x_2505_ = lean_apply_4(v_toBind_2502_, lean_box(0), lean_box(0), v___x_2504_, v___f_2503_);
return v___x_2505_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverloadCore(lean_object* v_m_2506_, lean_object* v_inst_2507_, lean_object* v_inst_2508_, lean_object* v_inst_2509_, lean_object* v_inst_2510_, lean_object* v_inst_2511_, lean_object* v_inst_2512_, lean_object* v_inst_2513_, lean_object* v_n_2514_){
_start:
{
lean_object* v___x_2515_; 
v___x_2515_ = l_Lean_resolveGlobalConstNoOverloadCore___redArg(v_inst_2507_, v_inst_2508_, v_inst_2509_, v_inst_2510_, v_inst_2511_, v_inst_2512_, v_inst_2513_, v_n_2514_);
return v___x_2515_;
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___redArg___lam__0(lean_object* v_x_2516_){
_start:
{
if (lean_obj_tag(v_x_2516_) == 1)
{
lean_object* v_fields_2517_; 
v_fields_2517_ = lean_ctor_get(v_x_2516_, 1);
if (lean_obj_tag(v_fields_2517_) == 0)
{
lean_object* v_n_2518_; lean_object* v___x_2519_; 
v_n_2518_ = lean_ctor_get(v_x_2516_, 0);
lean_inc(v_n_2518_);
v___x_2519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2519_, 0, v_n_2518_);
return v___x_2519_;
}
else
{
lean_object* v___x_2520_; 
v___x_2520_ = lean_box(0);
return v___x_2520_;
}
}
else
{
lean_object* v___x_2521_; 
v___x_2521_ = lean_box(0);
return v___x_2521_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___redArg___lam__0___boxed(lean_object* v_x_2522_){
_start:
{
lean_object* v_res_2523_; 
v_res_2523_ = l_Lean_preprocessSyntaxAndResolve___redArg___lam__0(v_x_2522_);
lean_dec_ref(v_x_2522_);
return v_res_2523_;
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___redArg___lam__1(lean_object* v_stx_2524_, lean_object* v_withRef_2525_, lean_object* v___x_2526_, lean_object* v_oldRef_2527_){
_start:
{
lean_object* v_ref_2528_; lean_object* v___x_2529_; 
v_ref_2528_ = l_Lean_replaceRef(v_stx_2524_, v_oldRef_2527_);
v___x_2529_ = lean_apply_3(v_withRef_2525_, lean_box(0), v_ref_2528_, v___x_2526_);
return v___x_2529_;
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___redArg___lam__1___boxed(lean_object* v_stx_2530_, lean_object* v_withRef_2531_, lean_object* v___x_2532_, lean_object* v_oldRef_2533_){
_start:
{
lean_object* v_res_2534_; 
v_res_2534_ = l_Lean_preprocessSyntaxAndResolve___redArg___lam__1(v_stx_2530_, v_withRef_2531_, v___x_2532_, v_oldRef_2533_);
lean_dec(v_oldRef_2533_);
lean_dec(v_stx_2530_);
return v_res_2534_;
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___redArg(lean_object* v_inst_2536_, lean_object* v_inst_2537_, lean_object* v_stx_2538_, lean_object* v_k_2539_){
_start:
{
if (lean_obj_tag(v_stx_2538_) == 3)
{
lean_object* v_val_2540_; lean_object* v_preresolved_2541_; lean_object* v___f_2542_; lean_object* v___x_2543_; lean_object* v_pre_2544_; uint8_t v___x_2545_; 
v_val_2540_ = lean_ctor_get(v_stx_2538_, 2);
v_preresolved_2541_ = lean_ctor_get(v_stx_2538_, 3);
v___f_2542_ = ((lean_object*)(l_Lean_preprocessSyntaxAndResolve___redArg___closed__0));
v___x_2543_ = ((lean_object*)(l_Lean_resolveNamespace___redArg___closed__1));
lean_inc(v_preresolved_2541_);
v_pre_2544_ = l_List_filterMapTR_go___redArg(v___f_2542_, v_preresolved_2541_, v___x_2543_);
v___x_2545_ = l_List_isEmpty___redArg(v_pre_2544_);
if (v___x_2545_ == 0)
{
lean_object* v_toApplicative_2546_; lean_object* v_toPure_2547_; lean_object* v___x_2548_; 
lean_dec_ref_known(v_stx_2538_, 4);
lean_dec(v_k_2539_);
lean_dec_ref(v_inst_2537_);
v_toApplicative_2546_ = lean_ctor_get(v_inst_2536_, 0);
lean_inc_ref(v_toApplicative_2546_);
lean_dec_ref(v_inst_2536_);
v_toPure_2547_ = lean_ctor_get(v_toApplicative_2546_, 1);
lean_inc(v_toPure_2547_);
lean_dec_ref(v_toApplicative_2546_);
v___x_2548_ = lean_apply_2(v_toPure_2547_, lean_box(0), v_pre_2544_);
return v___x_2548_;
}
else
{
lean_object* v_toMonadRef_2549_; lean_object* v_toBind_2550_; lean_object* v_getRef_2551_; lean_object* v_withRef_2552_; lean_object* v___x_2553_; lean_object* v___f_2554_; lean_object* v___x_2555_; 
lean_dec(v_pre_2544_);
v_toMonadRef_2549_ = lean_ctor_get(v_inst_2537_, 1);
lean_inc_ref(v_toMonadRef_2549_);
lean_dec_ref(v_inst_2537_);
v_toBind_2550_ = lean_ctor_get(v_inst_2536_, 1);
lean_inc(v_toBind_2550_);
lean_dec_ref(v_inst_2536_);
v_getRef_2551_ = lean_ctor_get(v_toMonadRef_2549_, 0);
lean_inc(v_getRef_2551_);
v_withRef_2552_ = lean_ctor_get(v_toMonadRef_2549_, 1);
lean_inc(v_withRef_2552_);
lean_dec_ref(v_toMonadRef_2549_);
lean_inc(v_val_2540_);
v___x_2553_ = lean_apply_1(v_k_2539_, v_val_2540_);
v___f_2554_ = lean_alloc_closure((void*)(l_Lean_preprocessSyntaxAndResolve___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_2554_, 0, v_stx_2538_);
lean_closure_set(v___f_2554_, 1, v_withRef_2552_);
lean_closure_set(v___f_2554_, 2, v___x_2553_);
v___x_2555_ = lean_apply_4(v_toBind_2550_, lean_box(0), lean_box(0), v_getRef_2551_, v___f_2554_);
return v___x_2555_;
}
}
else
{
lean_object* v___x_2556_; lean_object* v___x_2557_; 
lean_dec(v_k_2539_);
v___x_2556_ = lean_obj_once(&l_Lean_resolveNamespace___redArg___closed__4, &l_Lean_resolveNamespace___redArg___closed__4_once, _init_l_Lean_resolveNamespace___redArg___closed__4);
v___x_2557_ = l_Lean_throwErrorAt___redArg(v_inst_2536_, v_inst_2537_, v_stx_2538_, v___x_2556_);
return v___x_2557_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve(lean_object* v_m_2558_, lean_object* v_inst_2559_, lean_object* v_inst_2560_, lean_object* v_stx_2561_, lean_object* v_k_2562_){
_start:
{
lean_object* v___x_2563_; 
v___x_2563_ = l_Lean_preprocessSyntaxAndResolve___redArg(v_inst_2559_, v_inst_2560_, v_stx_2561_, v_k_2562_);
return v___x_2563_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst___redArg(lean_object* v_inst_2564_, lean_object* v_inst_2565_, lean_object* v_inst_2566_, lean_object* v_inst_2567_, lean_object* v_inst_2568_, lean_object* v_inst_2569_, lean_object* v_inst_2570_, lean_object* v_stx_2571_){
_start:
{
lean_object* v___x_2572_; lean_object* v___x_2573_; 
lean_inc_ref(v_inst_2570_);
lean_inc_ref(v_inst_2564_);
v___x_2572_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore), 9, 8);
lean_closure_set(v___x_2572_, 0, lean_box(0));
lean_closure_set(v___x_2572_, 1, v_inst_2564_);
lean_closure_set(v___x_2572_, 2, v_inst_2565_);
lean_closure_set(v___x_2572_, 3, v_inst_2566_);
lean_closure_set(v___x_2572_, 4, v_inst_2567_);
lean_closure_set(v___x_2572_, 5, v_inst_2568_);
lean_closure_set(v___x_2572_, 6, v_inst_2569_);
lean_closure_set(v___x_2572_, 7, v_inst_2570_);
v___x_2573_ = l_Lean_preprocessSyntaxAndResolve___redArg(v_inst_2564_, v_inst_2570_, v_stx_2571_, v___x_2572_);
return v___x_2573_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst(lean_object* v_m_2574_, lean_object* v_inst_2575_, lean_object* v_inst_2576_, lean_object* v_inst_2577_, lean_object* v_inst_2578_, lean_object* v_inst_2579_, lean_object* v_inst_2580_, lean_object* v_inst_2581_, lean_object* v_stx_2582_){
_start:
{
lean_object* v___x_2583_; 
v___x_2583_ = l_Lean_resolveGlobalConst___redArg(v_inst_2575_, v_inst_2576_, v_inst_2577_, v_inst_2578_, v_inst_2579_, v_inst_2580_, v_inst_2581_, v_stx_2582_);
return v___x_2583_;
}
}
static lean_object* _init_l_Lean_ensureNonAmbiguous___redArg___closed__1(void){
_start:
{
lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; 
v___x_2585_ = ((lean_object*)(l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__2));
v___x_2586_ = lean_unsigned_to_nat(11u);
v___x_2587_ = lean_unsigned_to_nat(429u);
v___x_2588_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___redArg___closed__0));
v___x_2589_ = ((lean_object*)(l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__0));
v___x_2590_ = l_mkPanicMessageWithDecl(v___x_2589_, v___x_2588_, v___x_2587_, v___x_2586_, v___x_2585_);
return v___x_2590_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNonAmbiguous___redArg(lean_object* v_inst_2594_, lean_object* v_inst_2595_, lean_object* v_id_2596_, lean_object* v_cs_2597_){
_start:
{
if (lean_obj_tag(v_cs_2597_) == 0)
{
lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; 
lean_dec(v_id_2596_);
lean_dec_ref(v_inst_2595_);
v___x_2598_ = lean_box(0);
v___x_2599_ = l_instInhabitedOfMonad___redArg(v_inst_2594_, v___x_2598_);
v___x_2600_ = lean_obj_once(&l_Lean_ensureNonAmbiguous___redArg___closed__1, &l_Lean_ensureNonAmbiguous___redArg___closed__1_once, _init_l_Lean_ensureNonAmbiguous___redArg___closed__1);
v___x_2601_ = l_panic___redArg(v___x_2599_, v___x_2600_);
lean_dec(v___x_2599_);
return v___x_2601_;
}
else
{
lean_object* v_tail_2602_; 
v_tail_2602_ = lean_ctor_get(v_cs_2597_, 1);
if (lean_obj_tag(v_tail_2602_) == 0)
{
lean_object* v_toApplicative_2603_; lean_object* v_toPure_2604_; lean_object* v_head_2605_; lean_object* v___x_2606_; 
v_toApplicative_2603_ = lean_ctor_get(v_inst_2594_, 0);
lean_inc_ref(v_toApplicative_2603_);
lean_dec(v_id_2596_);
lean_dec_ref(v_inst_2595_);
lean_dec_ref(v_inst_2594_);
v_toPure_2604_ = lean_ctor_get(v_toApplicative_2603_, 1);
lean_inc(v_toPure_2604_);
lean_dec_ref(v_toApplicative_2603_);
v_head_2605_ = lean_ctor_get(v_cs_2597_, 0);
lean_inc(v_head_2605_);
lean_dec_ref_known(v_cs_2597_, 2);
v___x_2606_ = lean_apply_2(v_toPure_2604_, lean_box(0), v_head_2605_);
return v___x_2606_;
}
else
{
lean_object* v___f_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; uint8_t v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; 
v___f_2607_ = ((lean_object*)(l_Lean_ensureNoOverload___redArg___closed__0));
v___x_2608_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___redArg___closed__2));
v___x_2609_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___redArg___closed__3));
v___x_2610_ = lean_box(0);
v___x_2611_ = 0;
lean_inc(v_id_2596_);
v___x_2612_ = l_Lean_Syntax_formatStx(v_id_2596_, v___x_2610_, v___x_2611_);
v___x_2613_ = l_Std_Format_defWidth;
v___x_2614_ = lean_unsigned_to_nat(0u);
v___x_2615_ = l_Std_Format_pretty(v___x_2612_, v___x_2613_, v___x_2614_, v___x_2614_);
v___x_2616_ = lean_string_append(v___x_2609_, v___x_2615_);
lean_dec_ref(v___x_2615_);
v___x_2617_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___redArg___closed__4));
v___x_2618_ = lean_string_append(v___x_2616_, v___x_2617_);
v___x_2619_ = lean_box(0);
v___x_2620_ = l_List_mapTR_loop___redArg(v___f_2607_, v_cs_2597_, v___x_2619_);
v___x_2621_ = l_List_toString___redArg(v___x_2608_, v___x_2620_);
v___x_2622_ = lean_string_append(v___x_2618_, v___x_2621_);
lean_dec_ref(v___x_2621_);
v___x_2623_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2623_, 0, v___x_2622_);
v___x_2624_ = l_Lean_MessageData_ofFormat(v___x_2623_);
v___x_2625_ = l_Lean_throwErrorAt___redArg(v_inst_2594_, v_inst_2595_, v_id_2596_, v___x_2624_);
return v___x_2625_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNonAmbiguous(lean_object* v_m_2626_, lean_object* v_inst_2627_, lean_object* v_inst_2628_, lean_object* v_id_2629_, lean_object* v_cs_2630_){
_start:
{
lean_object* v___x_2631_; 
v___x_2631_ = l_Lean_ensureNonAmbiguous___redArg(v_inst_2627_, v_inst_2628_, v_id_2629_, v_cs_2630_);
return v___x_2631_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverload___redArg___lam__0(lean_object* v_inst_2632_, lean_object* v_inst_2633_, lean_object* v_id_2634_, lean_object* v_____do__lift_2635_){
_start:
{
lean_object* v___x_2636_; 
v___x_2636_ = l_Lean_ensureNonAmbiguous___redArg(v_inst_2632_, v_inst_2633_, v_id_2634_, v_____do__lift_2635_);
return v___x_2636_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverload___redArg(lean_object* v_inst_2637_, lean_object* v_inst_2638_, lean_object* v_inst_2639_, lean_object* v_inst_2640_, lean_object* v_inst_2641_, lean_object* v_inst_2642_, lean_object* v_inst_2643_, lean_object* v_id_2644_){
_start:
{
lean_object* v_toBind_2645_; lean_object* v___f_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; 
v_toBind_2645_ = lean_ctor_get(v_inst_2637_, 1);
lean_inc(v_toBind_2645_);
lean_inc(v_id_2644_);
lean_inc_ref(v_inst_2643_);
lean_inc_ref(v_inst_2637_);
v___f_2646_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalConstNoOverload___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2646_, 0, v_inst_2637_);
lean_closure_set(v___f_2646_, 1, v_inst_2643_);
lean_closure_set(v___f_2646_, 2, v_id_2644_);
v___x_2647_ = l_Lean_resolveGlobalConst___redArg(v_inst_2637_, v_inst_2638_, v_inst_2639_, v_inst_2640_, v_inst_2641_, v_inst_2642_, v_inst_2643_, v_id_2644_);
v___x_2648_ = lean_apply_4(v_toBind_2645_, lean_box(0), lean_box(0), v___x_2647_, v___f_2646_);
return v___x_2648_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverload(lean_object* v_m_2649_, lean_object* v_inst_2650_, lean_object* v_inst_2651_, lean_object* v_inst_2652_, lean_object* v_inst_2653_, lean_object* v_inst_2654_, lean_object* v_inst_2655_, lean_object* v_inst_2656_, lean_object* v_id_2657_){
_start:
{
lean_object* v___x_2658_; 
v___x_2658_ = l_Lean_resolveGlobalConstNoOverload___redArg(v_inst_2650_, v_inst_2651_, v_inst_2652_, v_inst_2653_, v_inst_2654_, v_inst_2655_, v_inst_2656_, v_id_2657_);
return v___x_2658_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__0(lean_object* v___f_2659_, lean_object* v___f_2660_, uint8_t v_globalDeclFoundNext_2661_, uint8_t v_globalDeclFound_2662_, lean_object* v_r_2663_){
_start:
{
lean_object* v___x_2664_; lean_object* v_r_2665_; uint8_t v___x_2666_; 
v___x_2664_ = lean_box(0);
v_r_2665_ = l_List_filterTR_loop___redArg(v___f_2659_, v_r_2663_, v___x_2664_);
v___x_2666_ = l_List_isEmpty___redArg(v_r_2665_);
lean_dec(v_r_2665_);
if (v___x_2666_ == 0)
{
lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; 
v___x_2667_ = lean_box(0);
v___x_2668_ = lean_box(v_globalDeclFoundNext_2661_);
v___x_2669_ = lean_apply_2(v___f_2660_, v___x_2667_, v___x_2668_);
return v___x_2669_;
}
else
{
lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; 
v___x_2670_ = lean_box(0);
v___x_2671_ = lean_box(v_globalDeclFound_2662_);
v___x_2672_ = lean_apply_2(v___f_2660_, v___x_2670_, v___x_2671_);
return v___x_2672_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__0___boxed(lean_object* v___f_2673_, lean_object* v___f_2674_, lean_object* v_globalDeclFoundNext_2675_, lean_object* v_globalDeclFound_2676_, lean_object* v_r_2677_){
_start:
{
uint8_t v_globalDeclFoundNext_boxed_2678_; uint8_t v_globalDeclFound_boxed_2679_; lean_object* v_res_2680_; 
v_globalDeclFoundNext_boxed_2678_ = lean_unbox(v_globalDeclFoundNext_2675_);
v_globalDeclFound_boxed_2679_ = lean_unbox(v_globalDeclFound_2676_);
v_res_2680_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__0(v___f_2673_, v___f_2674_, v_globalDeclFoundNext_boxed_2678_, v_globalDeclFound_boxed_2679_, v_r_2677_);
return v_res_2680_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__1___boxed(lean_object* v_str_2681_, lean_object* v_projs_2682_, lean_object* v_inst_2683_, lean_object* v_inst_2684_, lean_object* v_inst_2685_, lean_object* v_inst_2686_, lean_object* v_inst_2687_, lean_object* v_inst_2688_, lean_object* v_view_2689_, lean_object* v_findLocalDecl_x3f_2690_, lean_object* v_pre_2691_, lean_object* v_____r_2692_, lean_object* v_globalDeclFoundNext_2693_){
_start:
{
uint8_t v_globalDeclFoundNext_boxed_2694_; lean_object* v_res_2695_; 
v_globalDeclFoundNext_boxed_2694_ = lean_unbox(v_globalDeclFoundNext_2693_);
v_res_2695_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__1(v_str_2681_, v_projs_2682_, v_inst_2683_, v_inst_2684_, v_inst_2685_, v_inst_2686_, v_inst_2687_, v_inst_2688_, v_view_2689_, v_findLocalDecl_x3f_2690_, v_pre_2691_, v_____r_2692_, v_globalDeclFoundNext_boxed_2694_);
return v_res_2695_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg(lean_object* v_inst_2696_, lean_object* v_inst_2697_, lean_object* v_inst_2698_, lean_object* v_inst_2699_, lean_object* v_inst_2700_, lean_object* v_inst_2701_, lean_object* v_view_2702_, lean_object* v_findLocalDecl_x3f_2703_, lean_object* v_n_2704_, lean_object* v_projs_2705_, uint8_t v_globalDeclFound_2706_){
_start:
{
lean_object* v_toApplicative_2707_; lean_object* v_imported_2708_; lean_object* v_ctx_2709_; lean_object* v_scopes_2710_; lean_object* v_toBind_2711_; lean_object* v_toPure_2712_; lean_object* v___f_2713_; lean_object* v_givenNameView_2714_; uint8_t v___y_2716_; 
v_toApplicative_2707_ = lean_ctor_get(v_inst_2696_, 0);
v_imported_2708_ = lean_ctor_get(v_view_2702_, 1);
v_ctx_2709_ = lean_ctor_get(v_view_2702_, 2);
v_scopes_2710_ = lean_ctor_get(v_view_2702_, 3);
v_toBind_2711_ = lean_ctor_get(v_inst_2696_, 1);
v_toPure_2712_ = lean_ctor_get(v_toApplicative_2707_, 1);
v___f_2713_ = ((lean_object*)(l_Lean_filterFieldList___redArg___closed__0));
lean_inc(v_scopes_2710_);
lean_inc(v_ctx_2709_);
lean_inc(v_imported_2708_);
lean_inc(v_n_2704_);
v_givenNameView_2714_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_givenNameView_2714_, 0, v_n_2704_);
lean_ctor_set(v_givenNameView_2714_, 1, v_imported_2708_);
lean_ctor_set(v_givenNameView_2714_, 2, v_ctx_2709_);
lean_ctor_set(v_givenNameView_2714_, 3, v_scopes_2710_);
if (v_globalDeclFound_2706_ == 0)
{
v___y_2716_ = v_globalDeclFound_2706_;
goto v___jp_2715_;
}
else
{
uint8_t v___x_2752_; 
v___x_2752_ = l_List_isEmpty___redArg(v_projs_2705_);
if (v___x_2752_ == 0)
{
v___y_2716_ = v_globalDeclFound_2706_;
goto v___jp_2715_;
}
else
{
uint8_t v___x_2753_; 
v___x_2753_ = 0;
v___y_2716_ = v___x_2753_;
goto v___jp_2715_;
}
}
v___jp_2715_:
{
lean_object* v___x_2717_; lean_object* v___x_2718_; 
v___x_2717_ = lean_box(v___y_2716_);
lean_inc_ref(v_findLocalDecl_x3f_2703_);
lean_inc_ref(v_givenNameView_2714_);
v___x_2718_ = lean_apply_2(v_findLocalDecl_x3f_2703_, v_givenNameView_2714_, v___x_2717_);
if (lean_obj_tag(v___x_2718_) == 0)
{
if (lean_obj_tag(v_n_2704_) == 1)
{
lean_object* v_pre_2719_; lean_object* v_str_2720_; lean_object* v___f_2721_; 
v_pre_2719_ = lean_ctor_get(v_n_2704_, 0);
lean_inc_n(v_pre_2719_, 2);
v_str_2720_ = lean_ctor_get(v_n_2704_, 1);
lean_inc_ref_n(v_str_2720_, 2);
lean_dec_ref_known(v_n_2704_, 2);
lean_inc_ref(v_findLocalDecl_x3f_2703_);
lean_inc_ref(v_view_2702_);
lean_inc(v_inst_2701_);
lean_inc_ref(v_inst_2700_);
lean_inc(v_inst_2699_);
lean_inc_ref(v_inst_2698_);
lean_inc_ref(v_inst_2697_);
lean_inc_ref(v_inst_2696_);
lean_inc(v_projs_2705_);
v___f_2721_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__1___boxed), 13, 11);
lean_closure_set(v___f_2721_, 0, v_str_2720_);
lean_closure_set(v___f_2721_, 1, v_projs_2705_);
lean_closure_set(v___f_2721_, 2, v_inst_2696_);
lean_closure_set(v___f_2721_, 3, v_inst_2697_);
lean_closure_set(v___f_2721_, 4, v_inst_2698_);
lean_closure_set(v___f_2721_, 5, v_inst_2699_);
lean_closure_set(v___f_2721_, 6, v_inst_2700_);
lean_closure_set(v___f_2721_, 7, v_inst_2701_);
lean_closure_set(v___f_2721_, 8, v_view_2702_);
lean_closure_set(v___f_2721_, 9, v_findLocalDecl_x3f_2703_);
lean_closure_set(v___f_2721_, 10, v_pre_2719_);
if (v_globalDeclFound_2706_ == 0)
{
uint8_t v_globalDeclFoundNext_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___f_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; 
lean_inc(v_toBind_2711_);
lean_dec_ref(v_str_2720_);
lean_dec(v_pre_2719_);
lean_dec(v_projs_2705_);
lean_dec_ref(v_findLocalDecl_x3f_2703_);
lean_dec_ref(v_view_2702_);
v_globalDeclFoundNext_2722_ = 1;
v___x_2723_ = lean_box(v_globalDeclFoundNext_2722_);
v___x_2724_ = lean_box(v_globalDeclFound_2706_);
v___f_2725_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2725_, 0, v___f_2713_);
lean_closure_set(v___f_2725_, 1, v___f_2721_);
lean_closure_set(v___f_2725_, 2, v___x_2723_);
lean_closure_set(v___f_2725_, 3, v___x_2724_);
v___x_2726_ = l_Lean_MacroScopesView_review(v_givenNameView_2714_);
v___x_2727_ = l_Lean_resolveGlobalName___redArg(v_inst_2696_, v_inst_2697_, v_inst_2698_, v_inst_2699_, v_inst_2700_, v_inst_2701_, v___x_2726_, v_globalDeclFound_2706_);
v___x_2728_ = lean_apply_4(v_toBind_2711_, lean_box(0), lean_box(0), v___x_2727_, v___f_2725_);
return v___x_2728_;
}
else
{
lean_object* v___x_2729_; lean_object* v___x_2730_; 
lean_dec_ref(v___f_2721_);
lean_dec_ref_known(v_givenNameView_2714_, 4);
v___x_2729_ = lean_box(0);
v___x_2730_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__1(v_str_2720_, v_projs_2705_, v_inst_2696_, v_inst_2697_, v_inst_2698_, v_inst_2699_, v_inst_2700_, v_inst_2701_, v_view_2702_, v_findLocalDecl_x3f_2703_, v_pre_2719_, v___x_2729_, v_globalDeclFound_2706_);
return v___x_2730_;
}
}
else
{
lean_object* v___x_2731_; lean_object* v___x_2732_; 
lean_inc(v_toPure_2712_);
lean_dec_ref_known(v_givenNameView_2714_, 4);
lean_dec(v_projs_2705_);
lean_dec(v_n_2704_);
lean_dec_ref(v_findLocalDecl_x3f_2703_);
lean_dec_ref(v_view_2702_);
lean_dec(v_inst_2701_);
lean_dec_ref(v_inst_2700_);
lean_dec(v_inst_2699_);
lean_dec_ref(v_inst_2698_);
lean_dec_ref(v_inst_2697_);
lean_dec_ref(v_inst_2696_);
v___x_2731_ = lean_box(0);
v___x_2732_ = lean_apply_2(v_toPure_2712_, lean_box(0), v___x_2731_);
return v___x_2732_;
}
}
else
{
lean_object* v___x_2734_; uint8_t v_isShared_2735_; uint8_t v_isSharedCheck_2749_; 
lean_inc(v_toPure_2712_);
lean_dec_ref_known(v_givenNameView_2714_, 4);
lean_dec(v_n_2704_);
lean_dec_ref(v_findLocalDecl_x3f_2703_);
lean_dec_ref(v_view_2702_);
lean_dec(v_inst_2701_);
lean_dec_ref(v_inst_2700_);
lean_dec(v_inst_2699_);
lean_dec_ref(v_inst_2698_);
lean_dec_ref(v_inst_2697_);
v_isSharedCheck_2749_ = !lean_is_exclusive(v_inst_2696_);
if (v_isSharedCheck_2749_ == 0)
{
lean_object* v_unused_2750_; lean_object* v_unused_2751_; 
v_unused_2750_ = lean_ctor_get(v_inst_2696_, 1);
lean_dec(v_unused_2750_);
v_unused_2751_ = lean_ctor_get(v_inst_2696_, 0);
lean_dec(v_unused_2751_);
v___x_2734_ = v_inst_2696_;
v_isShared_2735_ = v_isSharedCheck_2749_;
goto v_resetjp_2733_;
}
else
{
lean_dec(v_inst_2696_);
v___x_2734_ = lean_box(0);
v_isShared_2735_ = v_isSharedCheck_2749_;
goto v_resetjp_2733_;
}
v_resetjp_2733_:
{
lean_object* v_val_2736_; lean_object* v___x_2738_; uint8_t v_isShared_2739_; uint8_t v_isSharedCheck_2748_; 
v_val_2736_ = lean_ctor_get(v___x_2718_, 0);
v_isSharedCheck_2748_ = !lean_is_exclusive(v___x_2718_);
if (v_isSharedCheck_2748_ == 0)
{
v___x_2738_ = v___x_2718_;
v_isShared_2739_ = v_isSharedCheck_2748_;
goto v_resetjp_2737_;
}
else
{
lean_inc(v_val_2736_);
lean_dec(v___x_2718_);
v___x_2738_ = lean_box(0);
v_isShared_2739_ = v_isSharedCheck_2748_;
goto v_resetjp_2737_;
}
v_resetjp_2737_:
{
lean_object* v___x_2740_; lean_object* v___x_2742_; 
v___x_2740_ = l_Lean_LocalDecl_toExpr(v_val_2736_);
if (v_isShared_2735_ == 0)
{
lean_ctor_set(v___x_2734_, 1, v_projs_2705_);
lean_ctor_set(v___x_2734_, 0, v___x_2740_);
v___x_2742_ = v___x_2734_;
goto v_reusejp_2741_;
}
else
{
lean_object* v_reuseFailAlloc_2747_; 
v_reuseFailAlloc_2747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2747_, 0, v___x_2740_);
lean_ctor_set(v_reuseFailAlloc_2747_, 1, v_projs_2705_);
v___x_2742_ = v_reuseFailAlloc_2747_;
goto v_reusejp_2741_;
}
v_reusejp_2741_:
{
lean_object* v___x_2744_; 
if (v_isShared_2739_ == 0)
{
lean_ctor_set(v___x_2738_, 0, v___x_2742_);
v___x_2744_ = v___x_2738_;
goto v_reusejp_2743_;
}
else
{
lean_object* v_reuseFailAlloc_2746_; 
v_reuseFailAlloc_2746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2746_, 0, v___x_2742_);
v___x_2744_ = v_reuseFailAlloc_2746_;
goto v_reusejp_2743_;
}
v_reusejp_2743_:
{
lean_object* v___x_2745_; 
v___x_2745_ = lean_apply_2(v_toPure_2712_, lean_box(0), v___x_2744_);
return v___x_2745_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__1(lean_object* v_str_2754_, lean_object* v_projs_2755_, lean_object* v_inst_2756_, lean_object* v_inst_2757_, lean_object* v_inst_2758_, lean_object* v_inst_2759_, lean_object* v_inst_2760_, lean_object* v_inst_2761_, lean_object* v_view_2762_, lean_object* v_findLocalDecl_x3f_2763_, lean_object* v_pre_2764_, lean_object* v_____r_2765_, uint8_t v_globalDeclFoundNext_2766_){
_start:
{
lean_object* v___x_2767_; lean_object* v___x_2768_; 
v___x_2767_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2767_, 0, v_str_2754_);
lean_ctor_set(v___x_2767_, 1, v_projs_2755_);
v___x_2768_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg(v_inst_2756_, v_inst_2757_, v_inst_2758_, v_inst_2759_, v_inst_2760_, v_inst_2761_, v_view_2762_, v_findLocalDecl_x3f_2763_, v_pre_2764_, v___x_2767_, v_globalDeclFoundNext_2766_);
return v___x_2768_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___boxed(lean_object* v_inst_2769_, lean_object* v_inst_2770_, lean_object* v_inst_2771_, lean_object* v_inst_2772_, lean_object* v_inst_2773_, lean_object* v_inst_2774_, lean_object* v_view_2775_, lean_object* v_findLocalDecl_x3f_2776_, lean_object* v_n_2777_, lean_object* v_projs_2778_, lean_object* v_globalDeclFound_2779_){
_start:
{
uint8_t v_globalDeclFound_boxed_2780_; lean_object* v_res_2781_; 
v_globalDeclFound_boxed_2780_ = lean_unbox(v_globalDeclFound_2779_);
v_res_2781_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg(v_inst_2769_, v_inst_2770_, v_inst_2771_, v_inst_2772_, v_inst_2773_, v_inst_2774_, v_view_2775_, v_findLocalDecl_x3f_2776_, v_n_2777_, v_projs_2778_, v_globalDeclFound_boxed_2780_);
return v_res_2781_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop(lean_object* v_m_2782_, lean_object* v_inst_2783_, lean_object* v_inst_2784_, lean_object* v_inst_2785_, lean_object* v_inst_2786_, lean_object* v_inst_2787_, lean_object* v_inst_2788_, lean_object* v_view_2789_, lean_object* v_findLocalDecl_x3f_2790_, lean_object* v_n_2791_, lean_object* v_projs_2792_, uint8_t v_globalDeclFound_2793_){
_start:
{
lean_object* v___x_2794_; 
v___x_2794_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg(v_inst_2783_, v_inst_2784_, v_inst_2785_, v_inst_2786_, v_inst_2787_, v_inst_2788_, v_view_2789_, v_findLocalDecl_x3f_2790_, v_n_2791_, v_projs_2792_, v_globalDeclFound_2793_);
return v___x_2794_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___boxed(lean_object* v_m_2795_, lean_object* v_inst_2796_, lean_object* v_inst_2797_, lean_object* v_inst_2798_, lean_object* v_inst_2799_, lean_object* v_inst_2800_, lean_object* v_inst_2801_, lean_object* v_view_2802_, lean_object* v_findLocalDecl_x3f_2803_, lean_object* v_n_2804_, lean_object* v_projs_2805_, lean_object* v_globalDeclFound_2806_){
_start:
{
uint8_t v_globalDeclFound_boxed_2807_; lean_object* v_res_2808_; 
v_globalDeclFound_boxed_2807_ = lean_unbox(v_globalDeclFound_2806_);
v_res_2808_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop(v_m_2795_, v_inst_2796_, v_inst_2797_, v_inst_2798_, v_inst_2799_, v_inst_2800_, v_inst_2801_, v_view_2802_, v_findLocalDecl_x3f_2803_, v_n_2804_, v_projs_2805_, v_globalDeclFound_boxed_2807_);
return v_res_2808_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_go(lean_object* v_localDecl_2809_, lean_object* v_givenNameView_2810_, lean_object* v_fullDeclName_2811_, lean_object* v_ns_2812_){
_start:
{
lean_object* v_name_2813_; lean_object* v_imported_2814_; lean_object* v_ctx_2815_; lean_object* v_scopes_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; uint8_t v___x_2820_; 
v_name_2813_ = lean_ctor_get(v_givenNameView_2810_, 0);
v_imported_2814_ = lean_ctor_get(v_givenNameView_2810_, 1);
v_ctx_2815_ = lean_ctor_get(v_givenNameView_2810_, 2);
v_scopes_2816_ = lean_ctor_get(v_givenNameView_2810_, 3);
lean_inc(v_name_2813_);
lean_inc(v_ns_2812_);
v___x_2817_ = l_Lean_Name_append(v_ns_2812_, v_name_2813_);
lean_inc(v_scopes_2816_);
lean_inc(v_ctx_2815_);
lean_inc(v_imported_2814_);
v___x_2818_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2818_, 0, v___x_2817_);
lean_ctor_set(v___x_2818_, 1, v_imported_2814_);
lean_ctor_set(v___x_2818_, 2, v_ctx_2815_);
lean_ctor_set(v___x_2818_, 3, v_scopes_2816_);
v___x_2819_ = l_Lean_MacroScopesView_review(v___x_2818_);
v___x_2820_ = lean_name_eq(v___x_2819_, v_fullDeclName_2811_);
lean_dec(v___x_2819_);
if (v___x_2820_ == 0)
{
if (lean_obj_tag(v_ns_2812_) == 1)
{
lean_object* v_pre_2821_; 
v_pre_2821_ = lean_ctor_get(v_ns_2812_, 0);
lean_inc(v_pre_2821_);
lean_dec_ref_known(v_ns_2812_, 2);
v_ns_2812_ = v_pre_2821_;
goto _start;
}
else
{
lean_object* v___x_2823_; 
lean_dec(v_ns_2812_);
lean_dec_ref(v_givenNameView_2810_);
lean_dec_ref(v_localDecl_2809_);
v___x_2823_ = lean_box(0);
return v___x_2823_;
}
}
else
{
lean_object* v___x_2824_; 
lean_dec(v_ns_2812_);
lean_dec_ref(v_givenNameView_2810_);
v___x_2824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2824_, 0, v_localDecl_2809_);
return v___x_2824_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_go___boxed(lean_object* v_localDecl_2825_, lean_object* v_givenNameView_2826_, lean_object* v_fullDeclName_2827_, lean_object* v_ns_2828_){
_start:
{
lean_object* v_res_2829_; 
v_res_2829_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_go(v_localDecl_2825_, v_givenNameView_2826_, v_fullDeclName_2827_, v_ns_2828_);
lean_dec(v_fullDeclName_2827_);
return v_res_2829_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__0(lean_object* v_localDecl_2830_, lean_object* v_givenName_2831_){
_start:
{
lean_object* v___x_2832_; uint8_t v___x_2833_; 
v___x_2832_ = l_Lean_LocalDecl_userName(v_localDecl_2830_);
v___x_2833_ = lean_name_eq(v___x_2832_, v_givenName_2831_);
lean_dec(v___x_2832_);
if (v___x_2833_ == 0)
{
lean_object* v___x_2834_; 
lean_dec_ref(v_localDecl_2830_);
v___x_2834_ = lean_box(0);
return v___x_2834_;
}
else
{
lean_object* v___x_2835_; 
v___x_2835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2835_, 0, v_localDecl_2830_);
return v___x_2835_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__0___boxed(lean_object* v_localDecl_2836_, lean_object* v_givenName_2837_){
_start:
{
lean_object* v_res_2838_; 
v_res_2838_ = l_Lean_resolveLocalName___redArg___lam__0(v_localDecl_2836_, v_givenName_2837_);
lean_dec(v_givenName_2837_);
return v_res_2838_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__1(lean_object* v_matchLocalDecl_x3f_2839_, lean_object* v_givenName_2840_, uint8_t v_skipAuxDecl_2841_, lean_object* v___f_2842_, lean_object* v_auxDeclToFullName_2843_, lean_object* v_currNamespace_2844_, lean_object* v_givenNameView_2845_, lean_object* v_x_2846_){
_start:
{
if (lean_obj_tag(v_x_2846_) == 0)
{
lean_dec_ref(v_givenNameView_2845_);
lean_dec(v_currNamespace_2844_);
lean_dec(v_auxDeclToFullName_2843_);
lean_dec_ref(v___f_2842_);
lean_dec(v_givenName_2840_);
lean_dec_ref(v_matchLocalDecl_x3f_2839_);
return v_x_2846_;
}
else
{
lean_object* v_val_2847_; uint8_t v___x_2848_; 
v_val_2847_ = lean_ctor_get(v_x_2846_, 0);
v___x_2848_ = l_Lean_LocalDecl_isAuxDecl(v_val_2847_);
if (v___x_2848_ == 0)
{
lean_object* v___x_2849_; 
lean_inc(v_val_2847_);
lean_dec_ref_known(v_x_2846_, 1);
lean_dec_ref(v_givenNameView_2845_);
lean_dec(v_currNamespace_2844_);
lean_dec(v_auxDeclToFullName_2843_);
lean_dec_ref(v___f_2842_);
v___x_2849_ = lean_apply_2(v_matchLocalDecl_x3f_2839_, v_val_2847_, v_givenName_2840_);
return v___x_2849_;
}
else
{
if (v_skipAuxDecl_2841_ == 0)
{
if (v___x_2848_ == 0)
{
lean_object* v___x_2850_; 
lean_dec_ref_known(v_x_2846_, 1);
lean_dec_ref(v_givenNameView_2845_);
lean_dec(v_currNamespace_2844_);
lean_dec(v_auxDeclToFullName_2843_);
lean_dec_ref(v___f_2842_);
lean_dec(v_givenName_2840_);
lean_dec_ref(v_matchLocalDecl_x3f_2839_);
v___x_2850_ = lean_box(0);
return v___x_2850_;
}
else
{
lean_object* v___x_2851_; lean_object* v___x_2852_; 
v___x_2851_ = l_Lean_LocalDecl_fvarId(v_val_2847_);
v___x_2852_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v___f_2842_, v_auxDeclToFullName_2843_, v___x_2851_);
if (lean_obj_tag(v___x_2852_) == 1)
{
lean_object* v_val_2853_; lean_object* v_fullDeclView_2854_; lean_object* v___y_2856_; lean_object* v_name_2877_; lean_object* v___x_2878_; 
lean_dec(v_givenName_2840_);
lean_dec_ref(v_matchLocalDecl_x3f_2839_);
v_val_2853_ = lean_ctor_get(v___x_2852_, 0);
lean_inc(v_val_2853_);
lean_dec_ref_known(v___x_2852_, 1);
v_fullDeclView_2854_ = l_Lean_extractMacroScopes(v_val_2853_);
v_name_2877_ = lean_ctor_get(v_fullDeclView_2854_, 0);
lean_inc_n(v_name_2877_, 2);
v___x_2878_ = l_Lean_privateToUserName_x3f(v_name_2877_);
if (lean_obj_tag(v___x_2878_) == 0)
{
v___y_2856_ = v_name_2877_;
goto v___jp_2855_;
}
else
{
lean_object* v_val_2879_; 
lean_dec(v_name_2877_);
v_val_2879_ = lean_ctor_get(v___x_2878_, 0);
lean_inc(v_val_2879_);
lean_dec_ref_known(v___x_2878_, 1);
v___y_2856_ = v_val_2879_;
goto v___jp_2855_;
}
v___jp_2855_:
{
lean_object* v_imported_2857_; lean_object* v_ctx_2858_; lean_object* v_scopes_2859_; lean_object* v___x_2861_; uint8_t v_isShared_2862_; uint8_t v_isSharedCheck_2875_; 
v_imported_2857_ = lean_ctor_get(v_fullDeclView_2854_, 1);
v_ctx_2858_ = lean_ctor_get(v_fullDeclView_2854_, 2);
v_scopes_2859_ = lean_ctor_get(v_fullDeclView_2854_, 3);
v_isSharedCheck_2875_ = !lean_is_exclusive(v_fullDeclView_2854_);
if (v_isSharedCheck_2875_ == 0)
{
lean_object* v_unused_2876_; 
v_unused_2876_ = lean_ctor_get(v_fullDeclView_2854_, 0);
lean_dec(v_unused_2876_);
v___x_2861_ = v_fullDeclView_2854_;
v_isShared_2862_ = v_isSharedCheck_2875_;
goto v_resetjp_2860_;
}
else
{
lean_inc(v_scopes_2859_);
lean_inc(v_ctx_2858_);
lean_inc(v_imported_2857_);
lean_dec(v_fullDeclView_2854_);
v___x_2861_ = lean_box(0);
v_isShared_2862_ = v_isSharedCheck_2875_;
goto v_resetjp_2860_;
}
v_resetjp_2860_:
{
lean_object* v_fullDeclView_2864_; 
if (v_isShared_2862_ == 0)
{
lean_ctor_set(v___x_2861_, 0, v___y_2856_);
v_fullDeclView_2864_ = v___x_2861_;
goto v_reusejp_2863_;
}
else
{
lean_object* v_reuseFailAlloc_2874_; 
v_reuseFailAlloc_2874_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2874_, 0, v___y_2856_);
lean_ctor_set(v_reuseFailAlloc_2874_, 1, v_imported_2857_);
lean_ctor_set(v_reuseFailAlloc_2874_, 2, v_ctx_2858_);
lean_ctor_set(v_reuseFailAlloc_2874_, 3, v_scopes_2859_);
v_fullDeclView_2864_ = v_reuseFailAlloc_2874_;
goto v_reusejp_2863_;
}
v_reusejp_2863_:
{
lean_object* v_fullDeclName_2865_; uint8_t v___x_2866_; 
lean_inc_ref(v_fullDeclView_2864_);
v_fullDeclName_2865_ = l_Lean_MacroScopesView_review(v_fullDeclView_2864_);
v___x_2866_ = l_Lean_Name_isPrefixOf(v_currNamespace_2844_, v_fullDeclName_2865_);
if (v___x_2866_ == 0)
{
lean_object* v___x_2867_; 
lean_inc(v_val_2847_);
lean_dec_ref(v_fullDeclView_2864_);
lean_dec_ref_known(v_x_2846_, 1);
v___x_2867_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_go(v_val_2847_, v_givenNameView_2845_, v_fullDeclName_2865_, v_currNamespace_2844_);
lean_dec(v_fullDeclName_2865_);
return v___x_2867_;
}
else
{
lean_object* v___x_2868_; lean_object* v_localDeclNameView_2869_; uint8_t v___x_2870_; 
lean_dec(v_fullDeclName_2865_);
lean_dec(v_currNamespace_2844_);
v___x_2868_ = l_Lean_LocalDecl_userName(v_val_2847_);
v_localDeclNameView_2869_ = l_Lean_extractMacroScopes(v___x_2868_);
v___x_2870_ = l_Lean_MacroScopesView_isSuffixOf(v_localDeclNameView_2869_, v_givenNameView_2845_);
lean_dec_ref(v_localDeclNameView_2869_);
if (v___x_2870_ == 0)
{
lean_object* v___x_2871_; 
lean_dec_ref(v_fullDeclView_2864_);
lean_dec_ref_known(v_x_2846_, 1);
lean_dec_ref(v_givenNameView_2845_);
v___x_2871_ = lean_box(0);
return v___x_2871_;
}
else
{
uint8_t v___x_2872_; 
v___x_2872_ = l_Lean_MacroScopesView_isSuffixOf(v_givenNameView_2845_, v_fullDeclView_2864_);
lean_dec_ref(v_fullDeclView_2864_);
lean_dec_ref(v_givenNameView_2845_);
if (v___x_2872_ == 0)
{
lean_object* v___x_2873_; 
lean_dec_ref_known(v_x_2846_, 1);
v___x_2873_ = lean_box(0);
return v___x_2873_;
}
else
{
return v_x_2846_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2880_; 
lean_inc(v_val_2847_);
lean_dec(v___x_2852_);
lean_dec_ref_known(v_x_2846_, 1);
lean_dec_ref(v_givenNameView_2845_);
lean_dec(v_currNamespace_2844_);
v___x_2880_ = lean_apply_2(v_matchLocalDecl_x3f_2839_, v_val_2847_, v_givenName_2840_);
return v___x_2880_;
}
}
}
else
{
lean_object* v___x_2881_; 
lean_dec_ref_known(v_x_2846_, 1);
lean_dec_ref(v_givenNameView_2845_);
lean_dec(v_currNamespace_2844_);
lean_dec(v_auxDeclToFullName_2843_);
lean_dec_ref(v___f_2842_);
lean_dec(v_givenName_2840_);
lean_dec_ref(v_matchLocalDecl_x3f_2839_);
v___x_2881_ = lean_box(0);
return v___x_2881_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__1___boxed(lean_object* v_matchLocalDecl_x3f_2882_, lean_object* v_givenName_2883_, lean_object* v_skipAuxDecl_2884_, lean_object* v___f_2885_, lean_object* v_auxDeclToFullName_2886_, lean_object* v_currNamespace_2887_, lean_object* v_givenNameView_2888_, lean_object* v_x_2889_){
_start:
{
uint8_t v_skipAuxDecl_boxed_2890_; lean_object* v_res_2891_; 
v_skipAuxDecl_boxed_2890_ = lean_unbox(v_skipAuxDecl_2884_);
v_res_2891_ = l_Lean_resolveLocalName___redArg___lam__1(v_matchLocalDecl_x3f_2882_, v_givenName_2883_, v_skipAuxDecl_boxed_2890_, v___f_2885_, v_auxDeclToFullName_2886_, v_currNamespace_2887_, v_givenNameView_2888_, v_x_2889_);
return v_res_2891_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__2(lean_object* v_localDecl_x3f_2892_, lean_object* v_matchLocalDecl_x3f_2893_, lean_object* v_givenName_2894_, lean_object* v_x_2895_){
_start:
{
if (lean_obj_tag(v_x_2895_) == 0)
{
lean_dec(v_givenName_2894_);
lean_dec_ref(v_matchLocalDecl_x3f_2893_);
return v_x_2895_;
}
else
{
lean_object* v_val_2896_; uint8_t v___x_2897_; 
v_val_2896_ = lean_ctor_get(v_x_2895_, 0);
lean_inc(v_val_2896_);
lean_dec_ref_known(v_x_2895_, 1);
v___x_2897_ = l_Lean_LocalDecl_isAuxDecl(v_val_2896_);
if (v___x_2897_ == 0)
{
lean_dec(v_val_2896_);
lean_dec(v_givenName_2894_);
lean_dec_ref(v_matchLocalDecl_x3f_2893_);
lean_inc(v_localDecl_x3f_2892_);
return v_localDecl_x3f_2892_;
}
else
{
lean_object* v___x_2898_; 
v___x_2898_ = lean_apply_2(v_matchLocalDecl_x3f_2893_, v_val_2896_, v_givenName_2894_);
return v___x_2898_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__2___boxed(lean_object* v_localDecl_x3f_2899_, lean_object* v_matchLocalDecl_x3f_2900_, lean_object* v_givenName_2901_, lean_object* v_x_2902_){
_start:
{
lean_object* v_res_2903_; 
v_res_2903_ = l_Lean_resolveLocalName___redArg___lam__2(v_localDecl_x3f_2899_, v_matchLocalDecl_x3f_2900_, v_givenName_2901_, v_x_2902_);
lean_dec(v_localDecl_x3f_2899_);
return v_res_2903_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__3(lean_object* v_lctx_2923_, lean_object* v_matchLocalDecl_x3f_2924_, lean_object* v___f_2925_, lean_object* v_auxDeclToFullName_2926_, lean_object* v_currNamespace_2927_, lean_object* v_givenNameView_2928_, uint8_t v_skipAuxDecl_2929_){
_start:
{
lean_object* v_decls_2930_; lean_object* v_givenName_2931_; lean_object* v___x_2932_; lean_object* v___f_2933_; lean_object* v___x_2934_; lean_object* v_localDecl_x3f_2935_; 
v_decls_2930_ = lean_ctor_get(v_lctx_2923_, 1);
lean_inc_ref_n(v_decls_2930_, 2);
lean_dec_ref(v_lctx_2923_);
lean_inc_ref(v_givenNameView_2928_);
v_givenName_2931_ = l_Lean_MacroScopesView_review(v_givenNameView_2928_);
v___x_2932_ = lean_box(v_skipAuxDecl_2929_);
lean_inc(v_givenName_2931_);
lean_inc_ref(v_matchLocalDecl_x3f_2924_);
v___f_2933_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_2933_, 0, v_matchLocalDecl_x3f_2924_);
lean_closure_set(v___f_2933_, 1, v_givenName_2931_);
lean_closure_set(v___f_2933_, 2, v___x_2932_);
lean_closure_set(v___f_2933_, 3, v___f_2925_);
lean_closure_set(v___f_2933_, 4, v_auxDeclToFullName_2926_);
lean_closure_set(v___f_2933_, 5, v_currNamespace_2927_);
lean_closure_set(v___f_2933_, 6, v_givenNameView_2928_);
v___x_2934_ = ((lean_object*)(l_Lean_resolveLocalName___redArg___lam__3___closed__9));
v_localDecl_x3f_2935_ = l_Lean_PersistentArray_findSomeRevM_x3f___redArg(v___x_2934_, v_decls_2930_, v___f_2933_);
if (lean_obj_tag(v_localDecl_x3f_2935_) == 0)
{
if (v_skipAuxDecl_2929_ == 0)
{
lean_object* v___f_2936_; lean_object* v___x_2937_; 
v___f_2936_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_2936_, 0, v_localDecl_x3f_2935_);
lean_closure_set(v___f_2936_, 1, v_matchLocalDecl_x3f_2924_);
lean_closure_set(v___f_2936_, 2, v_givenName_2931_);
v___x_2937_ = l_Lean_PersistentArray_findSomeRevM_x3f___redArg(v___x_2934_, v_decls_2930_, v___f_2936_);
return v___x_2937_;
}
else
{
lean_dec(v_givenName_2931_);
lean_dec_ref(v_decls_2930_);
lean_dec_ref(v_matchLocalDecl_x3f_2924_);
return v_localDecl_x3f_2935_;
}
}
else
{
lean_dec(v_givenName_2931_);
lean_dec_ref(v_decls_2930_);
lean_dec_ref(v_matchLocalDecl_x3f_2924_);
return v_localDecl_x3f_2935_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__3___boxed(lean_object* v_lctx_2938_, lean_object* v_matchLocalDecl_x3f_2939_, lean_object* v___f_2940_, lean_object* v_auxDeclToFullName_2941_, lean_object* v_currNamespace_2942_, lean_object* v_givenNameView_2943_, lean_object* v_skipAuxDecl_2944_){
_start:
{
uint8_t v_skipAuxDecl_boxed_2945_; lean_object* v_res_2946_; 
v_skipAuxDecl_boxed_2945_ = lean_unbox(v_skipAuxDecl_2944_);
v_res_2946_ = l_Lean_resolveLocalName___redArg___lam__3(v_lctx_2938_, v_matchLocalDecl_x3f_2939_, v___f_2940_, v_auxDeclToFullName_2941_, v_currNamespace_2942_, v_givenNameView_2943_, v_skipAuxDecl_boxed_2945_);
return v_res_2946_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__4(lean_object* v_n_2947_, lean_object* v_lctx_2948_, lean_object* v_matchLocalDecl_x3f_2949_, lean_object* v___f_2950_, lean_object* v_auxDeclToFullName_2951_, lean_object* v_inst_2952_, lean_object* v_inst_2953_, lean_object* v_inst_2954_, lean_object* v_inst_2955_, lean_object* v_inst_2956_, lean_object* v_inst_2957_, lean_object* v_currNamespace_2958_){
_start:
{
lean_object* v_view_2959_; lean_object* v_name_2960_; lean_object* v_findLocalDecl_x3f_2961_; lean_object* v___x_2962_; uint8_t v___x_2963_; lean_object* v___x_2964_; 
v_view_2959_ = l_Lean_extractMacroScopes(v_n_2947_);
v_name_2960_ = lean_ctor_get(v_view_2959_, 0);
lean_inc(v_name_2960_);
v_findLocalDecl_x3f_2961_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___redArg___lam__3___boxed), 7, 5);
lean_closure_set(v_findLocalDecl_x3f_2961_, 0, v_lctx_2948_);
lean_closure_set(v_findLocalDecl_x3f_2961_, 1, v_matchLocalDecl_x3f_2949_);
lean_closure_set(v_findLocalDecl_x3f_2961_, 2, v___f_2950_);
lean_closure_set(v_findLocalDecl_x3f_2961_, 3, v_auxDeclToFullName_2951_);
lean_closure_set(v_findLocalDecl_x3f_2961_, 4, v_currNamespace_2958_);
v___x_2962_ = lean_box(0);
v___x_2963_ = 0;
v___x_2964_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg(v_inst_2952_, v_inst_2953_, v_inst_2954_, v_inst_2955_, v_inst_2956_, v_inst_2957_, v_view_2959_, v_findLocalDecl_x3f_2961_, v_name_2960_, v___x_2962_, v___x_2963_);
return v___x_2964_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__5(lean_object* v_inst_2965_, lean_object* v_n_2966_, lean_object* v_lctx_2967_, lean_object* v_matchLocalDecl_x3f_2968_, lean_object* v___f_2969_, lean_object* v_inst_2970_, lean_object* v_inst_2971_, lean_object* v_inst_2972_, lean_object* v_inst_2973_, lean_object* v_inst_2974_, lean_object* v_toBind_2975_, lean_object* v_____do__lift_2976_){
_start:
{
lean_object* v_auxDeclToFullName_2977_; lean_object* v_getCurrNamespace_2978_; lean_object* v___f_2979_; lean_object* v___x_2980_; 
v_auxDeclToFullName_2977_ = lean_ctor_get(v_____do__lift_2976_, 2);
lean_inc(v_auxDeclToFullName_2977_);
lean_dec_ref(v_____do__lift_2976_);
v_getCurrNamespace_2978_ = lean_ctor_get(v_inst_2965_, 0);
lean_inc(v_getCurrNamespace_2978_);
v___f_2979_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___redArg___lam__4), 12, 11);
lean_closure_set(v___f_2979_, 0, v_n_2966_);
lean_closure_set(v___f_2979_, 1, v_lctx_2967_);
lean_closure_set(v___f_2979_, 2, v_matchLocalDecl_x3f_2968_);
lean_closure_set(v___f_2979_, 3, v___f_2969_);
lean_closure_set(v___f_2979_, 4, v_auxDeclToFullName_2977_);
lean_closure_set(v___f_2979_, 5, v_inst_2970_);
lean_closure_set(v___f_2979_, 6, v_inst_2965_);
lean_closure_set(v___f_2979_, 7, v_inst_2971_);
lean_closure_set(v___f_2979_, 8, v_inst_2972_);
lean_closure_set(v___f_2979_, 9, v_inst_2973_);
lean_closure_set(v___f_2979_, 10, v_inst_2974_);
v___x_2980_ = lean_apply_4(v_toBind_2975_, lean_box(0), lean_box(0), v_getCurrNamespace_2978_, v___f_2979_);
return v___x_2980_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__6(lean_object* v_inst_2981_, lean_object* v_n_2982_, lean_object* v_matchLocalDecl_x3f_2983_, lean_object* v___f_2984_, lean_object* v_inst_2985_, lean_object* v_inst_2986_, lean_object* v_inst_2987_, lean_object* v_inst_2988_, lean_object* v_inst_2989_, lean_object* v_toBind_2990_, lean_object* v_inst_2991_, lean_object* v_lctx_2992_){
_start:
{
lean_object* v___f_2993_; lean_object* v___x_2994_; 
lean_inc(v_toBind_2990_);
v___f_2993_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___redArg___lam__5), 12, 11);
lean_closure_set(v___f_2993_, 0, v_inst_2981_);
lean_closure_set(v___f_2993_, 1, v_n_2982_);
lean_closure_set(v___f_2993_, 2, v_lctx_2992_);
lean_closure_set(v___f_2993_, 3, v_matchLocalDecl_x3f_2983_);
lean_closure_set(v___f_2993_, 4, v___f_2984_);
lean_closure_set(v___f_2993_, 5, v_inst_2985_);
lean_closure_set(v___f_2993_, 6, v_inst_2986_);
lean_closure_set(v___f_2993_, 7, v_inst_2987_);
lean_closure_set(v___f_2993_, 8, v_inst_2988_);
lean_closure_set(v___f_2993_, 9, v_inst_2989_);
lean_closure_set(v___f_2993_, 10, v_toBind_2990_);
v___x_2994_ = lean_apply_4(v_toBind_2990_, lean_box(0), lean_box(0), v_inst_2991_, v___f_2993_);
return v___x_2994_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg(lean_object* v_inst_2997_, lean_object* v_inst_2998_, lean_object* v_inst_2999_, lean_object* v_inst_3000_, lean_object* v_inst_3001_, lean_object* v_inst_3002_, lean_object* v_inst_3003_, lean_object* v_n_3004_){
_start:
{
lean_object* v_toBind_3005_; lean_object* v___f_3006_; lean_object* v_matchLocalDecl_x3f_3007_; lean_object* v___f_3008_; lean_object* v___x_3009_; 
v_toBind_3005_ = lean_ctor_get(v_inst_2997_, 1);
lean_inc_n(v_toBind_3005_, 2);
v___f_3006_ = ((lean_object*)(l_Lean_resolveLocalName___redArg___closed__0));
v_matchLocalDecl_x3f_3007_ = ((lean_object*)(l_Lean_resolveLocalName___redArg___closed__1));
lean_inc(v_inst_3003_);
v___f_3008_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___redArg___lam__6), 12, 11);
lean_closure_set(v___f_3008_, 0, v_inst_2998_);
lean_closure_set(v___f_3008_, 1, v_n_3004_);
lean_closure_set(v___f_3008_, 2, v_matchLocalDecl_x3f_3007_);
lean_closure_set(v___f_3008_, 3, v___f_3006_);
lean_closure_set(v___f_3008_, 4, v_inst_2997_);
lean_closure_set(v___f_3008_, 5, v_inst_2999_);
lean_closure_set(v___f_3008_, 6, v_inst_3000_);
lean_closure_set(v___f_3008_, 7, v_inst_3001_);
lean_closure_set(v___f_3008_, 8, v_inst_3002_);
lean_closure_set(v___f_3008_, 9, v_toBind_3005_);
lean_closure_set(v___f_3008_, 10, v_inst_3003_);
v___x_3009_ = lean_apply_4(v_toBind_3005_, lean_box(0), lean_box(0), v_inst_3003_, v___f_3008_);
return v___x_3009_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName(lean_object* v_m_3010_, lean_object* v_inst_3011_, lean_object* v_inst_3012_, lean_object* v_inst_3013_, lean_object* v_inst_3014_, lean_object* v_inst_3015_, lean_object* v_inst_3016_, lean_object* v_inst_3017_, lean_object* v_n_3018_){
_start:
{
lean_object* v___x_3019_; 
v___x_3019_ = l_Lean_resolveLocalName___redArg(v_inst_3011_, v_inst_3012_, v_inst_3013_, v_inst_3014_, v_inst_3015_, v_inst_3016_, v_inst_3017_, v_n_3018_);
return v___x_3019_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__0(lean_object* v_toPure_3020_, uint8_t v_____do__lift_3021_){
_start:
{
lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; 
v___x_3022_ = lean_box(v_____do__lift_3021_);
v___x_3023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3023_, 0, v___x_3022_);
v___x_3024_ = lean_apply_2(v_toPure_3020_, lean_box(0), v___x_3023_);
return v___x_3024_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__0___boxed(lean_object* v_toPure_3025_, lean_object* v_____do__lift_3026_){
_start:
{
uint8_t v_____do__lift_1160__boxed_3027_; lean_object* v_res_3028_; 
v_____do__lift_1160__boxed_3027_ = lean_unbox(v_____do__lift_3026_);
v_res_3028_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__0(v_toPure_3025_, v_____do__lift_1160__boxed_3027_);
return v_res_3028_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__1(lean_object* v_toPure_3029_, lean_object* v___y_3030_, lean_object* v_____do__lift_3031_){
_start:
{
if (lean_obj_tag(v_____do__lift_3031_) == 0)
{
lean_object* v___x_3032_; lean_object* v___x_3033_; 
lean_dec(v___y_3030_);
v___x_3032_ = lean_box(0);
v___x_3033_ = lean_apply_2(v_toPure_3029_, lean_box(0), v___x_3032_);
return v___x_3033_;
}
else
{
lean_object* v___x_3035_; uint8_t v_isShared_3036_; uint8_t v_isSharedCheck_3041_; 
v_isSharedCheck_3041_ = !lean_is_exclusive(v_____do__lift_3031_);
if (v_isSharedCheck_3041_ == 0)
{
lean_object* v_unused_3042_; 
v_unused_3042_ = lean_ctor_get(v_____do__lift_3031_, 0);
lean_dec(v_unused_3042_);
v___x_3035_ = v_____do__lift_3031_;
v_isShared_3036_ = v_isSharedCheck_3041_;
goto v_resetjp_3034_;
}
else
{
lean_dec(v_____do__lift_3031_);
v___x_3035_ = lean_box(0);
v_isShared_3036_ = v_isSharedCheck_3041_;
goto v_resetjp_3034_;
}
v_resetjp_3034_:
{
lean_object* v___x_3038_; 
if (v_isShared_3036_ == 0)
{
lean_ctor_set(v___x_3035_, 0, v___y_3030_);
v___x_3038_ = v___x_3035_;
goto v_reusejp_3037_;
}
else
{
lean_object* v_reuseFailAlloc_3040_; 
v_reuseFailAlloc_3040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3040_, 0, v___y_3030_);
v___x_3038_ = v_reuseFailAlloc_3040_;
goto v_reusejp_3037_;
}
v_reusejp_3037_:
{
lean_object* v___x_3039_; 
v___x_3039_ = lean_apply_2(v_toPure_3029_, lean_box(0), v___x_3038_);
return v___x_3039_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2(lean_object* v_toPure_3045_, lean_object* v_toBind_3046_, lean_object* v___f_3047_, lean_object* v_____do__lift_3048_){
_start:
{
if (lean_obj_tag(v_____do__lift_3048_) == 0)
{
lean_object* v___x_3049_; lean_object* v___x_3050_; 
lean_dec(v___f_3047_);
lean_dec(v_toBind_3046_);
v___x_3049_ = lean_box(0);
v___x_3050_ = lean_apply_2(v_toPure_3045_, lean_box(0), v___x_3049_);
return v___x_3050_;
}
else
{
lean_object* v_val_3051_; uint8_t v___x_3052_; 
v_val_3051_ = lean_ctor_get(v_____do__lift_3048_, 0);
v___x_3052_ = lean_unbox(v_val_3051_);
if (v___x_3052_ == 0)
{
lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; 
v___x_3053_ = lean_box(0);
v___x_3054_ = lean_apply_2(v_toPure_3045_, lean_box(0), v___x_3053_);
v___x_3055_ = lean_apply_4(v_toBind_3046_, lean_box(0), lean_box(0), v___x_3054_, v___f_3047_);
return v___x_3055_;
}
else
{
lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; 
v___x_3056_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2___closed__0));
v___x_3057_ = lean_apply_2(v_toPure_3045_, lean_box(0), v___x_3056_);
v___x_3058_ = lean_apply_4(v_toBind_3046_, lean_box(0), lean_box(0), v___x_3057_, v___f_3047_);
return v___x_3058_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2___boxed(lean_object* v_toPure_3059_, lean_object* v_toBind_3060_, lean_object* v___f_3061_, lean_object* v_____do__lift_3062_){
_start:
{
lean_object* v_res_3063_; 
v_res_3063_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2(v_toPure_3059_, v_toBind_3060_, v___f_3061_, v_____do__lift_3062_);
lean_dec(v_____do__lift_3062_);
return v_res_3063_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__3(lean_object* v_toPure_3064_, lean_object* v_filter_3065_, lean_object* v___y_3066_, lean_object* v_toBind_3067_, lean_object* v___f_3068_, lean_object* v___f_3069_, lean_object* v_____do__lift_3070_){
_start:
{
if (lean_obj_tag(v_____do__lift_3070_) == 0)
{
lean_object* v___x_3071_; lean_object* v___x_3072_; 
lean_dec(v___f_3069_);
lean_dec(v___f_3068_);
lean_dec(v_toBind_3067_);
lean_dec(v___y_3066_);
lean_dec(v_filter_3065_);
v___x_3071_ = lean_box(0);
v___x_3072_ = lean_apply_2(v_toPure_3064_, lean_box(0), v___x_3071_);
return v___x_3072_;
}
else
{
lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; 
lean_dec(v_toPure_3064_);
v___x_3073_ = lean_apply_1(v_filter_3065_, v___y_3066_);
lean_inc(v_toBind_3067_);
v___x_3074_ = lean_apply_4(v_toBind_3067_, lean_box(0), lean_box(0), v___x_3073_, v___f_3068_);
v___x_3075_ = lean_apply_4(v_toBind_3067_, lean_box(0), lean_box(0), v___x_3074_, v___f_3069_);
return v___x_3075_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__3___boxed(lean_object* v_toPure_3076_, lean_object* v_filter_3077_, lean_object* v___y_3078_, lean_object* v_toBind_3079_, lean_object* v___f_3080_, lean_object* v___f_3081_, lean_object* v_____do__lift_3082_){
_start:
{
lean_object* v_res_3083_; 
v_res_3083_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__3(v_toPure_3076_, v_filter_3077_, v___y_3078_, v_toBind_3079_, v___f_3080_, v___f_3081_, v_____do__lift_3082_);
lean_dec(v_____do__lift_3082_);
return v_res_3083_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__4(lean_object* v_toPure_3084_, lean_object* v_n_u2080_3085_, lean_object* v_toBind_3086_, lean_object* v___f_3087_, lean_object* v_____do__lift_3088_){
_start:
{
if (lean_obj_tag(v_____do__lift_3088_) == 0)
{
lean_object* v___x_3092_; lean_object* v___x_3093_; 
lean_dec(v___f_3087_);
lean_dec(v_toBind_3086_);
v___x_3092_ = lean_box(0);
v___x_3093_ = lean_apply_2(v_toPure_3084_, lean_box(0), v___x_3092_);
return v___x_3093_;
}
else
{
lean_object* v_val_3094_; 
v_val_3094_ = lean_ctor_get(v_____do__lift_3088_, 0);
if (lean_obj_tag(v_val_3094_) == 1)
{
lean_object* v_tail_3095_; 
v_tail_3095_ = lean_ctor_get(v_val_3094_, 1);
if (lean_obj_tag(v_tail_3095_) == 0)
{
lean_object* v_head_3096_; lean_object* v_fst_3097_; uint8_t v___x_3098_; 
v_head_3096_ = lean_ctor_get(v_val_3094_, 0);
v_fst_3097_ = lean_ctor_get(v_head_3096_, 0);
v___x_3098_ = lean_name_eq(v_fst_3097_, v_n_u2080_3085_);
if (v___x_3098_ == 0)
{
lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; 
v___x_3099_ = lean_box(0);
v___x_3100_ = lean_apply_2(v_toPure_3084_, lean_box(0), v___x_3099_);
v___x_3101_ = lean_apply_4(v_toBind_3086_, lean_box(0), lean_box(0), v___x_3100_, v___f_3087_);
return v___x_3101_;
}
else
{
lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; 
v___x_3102_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2___closed__0));
v___x_3103_ = lean_apply_2(v_toPure_3084_, lean_box(0), v___x_3102_);
v___x_3104_ = lean_apply_4(v_toBind_3086_, lean_box(0), lean_box(0), v___x_3103_, v___f_3087_);
return v___x_3104_;
}
}
else
{
lean_dec(v___f_3087_);
lean_dec(v_toBind_3086_);
goto v___jp_3089_;
}
}
else
{
lean_dec(v___f_3087_);
lean_dec(v_toBind_3086_);
goto v___jp_3089_;
}
}
v___jp_3089_:
{
lean_object* v___x_3090_; lean_object* v___x_3091_; 
v___x_3090_ = lean_box(0);
v___x_3091_ = lean_apply_2(v_toPure_3084_, lean_box(0), v___x_3090_);
return v___x_3091_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__4___boxed(lean_object* v_toPure_3105_, lean_object* v_n_u2080_3106_, lean_object* v_toBind_3107_, lean_object* v___f_3108_, lean_object* v_____do__lift_3109_){
_start:
{
lean_object* v_res_3110_; 
v_res_3110_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__4(v_toPure_3105_, v_n_u2080_3106_, v_toBind_3107_, v___f_3108_, v_____do__lift_3109_);
lean_dec(v_____do__lift_3109_);
lean_dec(v_n_u2080_3106_);
return v_res_3110_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg(lean_object* v_inst_3111_, lean_object* v_inst_3112_, lean_object* v_inst_3113_, lean_object* v_inst_3114_, lean_object* v_inst_3115_, lean_object* v_inst_3116_, lean_object* v_n_u2080_3117_, lean_object* v_filter_3118_, lean_object* v_view_x3f_3119_, lean_object* v_n_3120_){
_start:
{
lean_object* v___f_3121_; lean_object* v___f_3122_; lean_object* v___f_3123_; lean_object* v___f_3124_; lean_object* v___f_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v_toApplicative_3133_; lean_object* v_getEnv_3134_; lean_object* v_modifyEnv_3135_; lean_object* v___x_3137_; uint8_t v_isShared_3138_; uint8_t v_isSharedCheck_3173_; 
lean_inc_ref_n(v_inst_3111_, 8);
v___f_3121_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_3121_, 0, v_inst_3111_);
v___f_3122_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__3), 5, 1);
lean_closure_set(v___f_3122_, 0, v_inst_3111_);
v___f_3123_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__6), 5, 1);
lean_closure_set(v___f_3123_, 0, v_inst_3111_);
v___f_3124_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_3124_, 0, v_inst_3111_);
v___f_3125_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__11), 5, 1);
lean_closure_set(v___f_3125_, 0, v_inst_3111_);
v___x_3126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3126_, 0, v___f_3121_);
lean_ctor_set(v___x_3126_, 1, v___f_3122_);
v___x_3127_ = lean_alloc_closure((void*)(l_OptionT_pure), 4, 2);
lean_closure_set(v___x_3127_, 0, lean_box(0));
lean_closure_set(v___x_3127_, 1, v_inst_3111_);
v___x_3128_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3128_, 0, v___x_3126_);
lean_ctor_set(v___x_3128_, 1, v___x_3127_);
lean_ctor_set(v___x_3128_, 2, v___f_3123_);
lean_ctor_set(v___x_3128_, 3, v___f_3124_);
lean_ctor_set(v___x_3128_, 4, v___f_3125_);
v___x_3129_ = lean_alloc_closure((void*)(l_OptionT_bind), 6, 2);
lean_closure_set(v___x_3129_, 0, lean_box(0));
lean_closure_set(v___x_3129_, 1, v_inst_3111_);
v___x_3130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3130_, 0, v___x_3128_);
lean_ctor_set(v___x_3130_, 1, v___x_3129_);
v___x_3131_ = lean_alloc_closure((void*)(l_OptionT_lift), 4, 2);
lean_closure_set(v___x_3131_, 0, lean_box(0));
lean_closure_set(v___x_3131_, 1, v_inst_3111_);
lean_inc_ref(v___x_3131_);
v___x_3132_ = l_Lean_instMonadResolveNameOfMonadLift___redArg(v___x_3131_, v_inst_3112_);
v_toApplicative_3133_ = lean_ctor_get(v_inst_3111_, 0);
lean_inc_ref(v_toApplicative_3133_);
v_getEnv_3134_ = lean_ctor_get(v_inst_3113_, 0);
v_modifyEnv_3135_ = lean_ctor_get(v_inst_3113_, 1);
v_isSharedCheck_3173_ = !lean_is_exclusive(v_inst_3113_);
if (v_isSharedCheck_3173_ == 0)
{
v___x_3137_ = v_inst_3113_;
v_isShared_3138_ = v_isSharedCheck_3173_;
goto v_resetjp_3136_;
}
else
{
lean_inc(v_modifyEnv_3135_);
lean_inc(v_getEnv_3134_);
lean_dec(v_inst_3113_);
v___x_3137_ = lean_box(0);
v_isShared_3138_ = v_isSharedCheck_3173_;
goto v_resetjp_3136_;
}
v_resetjp_3136_:
{
lean_object* v_toBind_3139_; lean_object* v_toPure_3140_; lean_object* v___f_3141_; lean_object* v___f_3142_; lean_object* v___f_3143_; lean_object* v___x_3144_; lean_object* v___x_3146_; 
v_toBind_3139_ = lean_ctor_get(v_inst_3111_, 1);
lean_inc_n(v_toBind_3139_, 2);
lean_dec_ref(v_inst_3111_);
v_toPure_3140_ = lean_ctor_get(v_toApplicative_3133_, 1);
lean_inc_n(v_toPure_3140_, 3);
lean_dec_ref(v_toApplicative_3133_);
lean_inc_ref(v___x_3131_);
v___f_3141_ = lean_alloc_closure((void*)(l_Lean_instMonadEnvOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3141_, 0, v_modifyEnv_3135_);
lean_closure_set(v___f_3141_, 1, v___x_3131_);
v___f_3142_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3142_, 0, v_toPure_3140_);
v___f_3143_ = lean_alloc_closure((void*)(l_OptionT_lift___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3143_, 0, v_toPure_3140_);
lean_inc_ref(v___f_3143_);
v___x_3144_ = lean_apply_4(v_toBind_3139_, lean_box(0), lean_box(0), v_getEnv_3134_, v___f_3143_);
if (v_isShared_3138_ == 0)
{
lean_ctor_set(v___x_3137_, 1, v___f_3141_);
lean_ctor_set(v___x_3137_, 0, v___x_3144_);
v___x_3146_ = v___x_3137_;
goto v_reusejp_3145_;
}
else
{
lean_object* v_reuseFailAlloc_3172_; 
v_reuseFailAlloc_3172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3172_, 0, v___x_3144_);
lean_ctor_set(v_reuseFailAlloc_3172_, 1, v___f_3141_);
v___x_3146_ = v_reuseFailAlloc_3172_;
goto v_reusejp_3145_;
}
v_reusejp_3145_:
{
lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___f_3149_; lean_object* v___y_3151_; 
lean_inc(v_toBind_3139_);
v___x_3147_ = lean_apply_4(v_toBind_3139_, lean_box(0), lean_box(0), v_inst_3114_, v___f_3143_);
lean_inc_ref(v___x_3131_);
v___x_3148_ = l_Lean_instMonadLogOfMonadLift___redArg(v___x_3131_, v_inst_3115_);
v___f_3149_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3149_, 0, v_inst_3116_);
lean_closure_set(v___f_3149_, 1, v___x_3131_);
if (lean_obj_tag(v_view_x3f_3119_) == 1)
{
lean_object* v_val_3159_; lean_object* v_imported_3160_; lean_object* v_ctx_3161_; lean_object* v_scopes_3162_; lean_object* v___x_3164_; uint8_t v_isShared_3165_; uint8_t v_isSharedCheck_3170_; 
v_val_3159_ = lean_ctor_get(v_view_x3f_3119_, 0);
lean_inc(v_val_3159_);
lean_dec_ref_known(v_view_x3f_3119_, 1);
v_imported_3160_ = lean_ctor_get(v_val_3159_, 1);
v_ctx_3161_ = lean_ctor_get(v_val_3159_, 2);
v_scopes_3162_ = lean_ctor_get(v_val_3159_, 3);
v_isSharedCheck_3170_ = !lean_is_exclusive(v_val_3159_);
if (v_isSharedCheck_3170_ == 0)
{
lean_object* v_unused_3171_; 
v_unused_3171_ = lean_ctor_get(v_val_3159_, 0);
lean_dec(v_unused_3171_);
v___x_3164_ = v_val_3159_;
v_isShared_3165_ = v_isSharedCheck_3170_;
goto v_resetjp_3163_;
}
else
{
lean_inc(v_scopes_3162_);
lean_inc(v_ctx_3161_);
lean_inc(v_imported_3160_);
lean_dec(v_val_3159_);
v___x_3164_ = lean_box(0);
v_isShared_3165_ = v_isSharedCheck_3170_;
goto v_resetjp_3163_;
}
v_resetjp_3163_:
{
lean_object* v___x_3167_; 
if (v_isShared_3165_ == 0)
{
lean_ctor_set(v___x_3164_, 0, v_n_3120_);
v___x_3167_ = v___x_3164_;
goto v_reusejp_3166_;
}
else
{
lean_object* v_reuseFailAlloc_3169_; 
v_reuseFailAlloc_3169_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3169_, 0, v_n_3120_);
lean_ctor_set(v_reuseFailAlloc_3169_, 1, v_imported_3160_);
lean_ctor_set(v_reuseFailAlloc_3169_, 2, v_ctx_3161_);
lean_ctor_set(v_reuseFailAlloc_3169_, 3, v_scopes_3162_);
v___x_3167_ = v_reuseFailAlloc_3169_;
goto v_reusejp_3166_;
}
v_reusejp_3166_:
{
lean_object* v___x_3168_; 
v___x_3168_ = l_Lean_MacroScopesView_review(v___x_3167_);
v___y_3151_ = v___x_3168_;
goto v___jp_3150_;
}
}
}
else
{
lean_dec(v_view_x3f_3119_);
v___y_3151_ = v_n_3120_;
goto v___jp_3150_;
}
v___jp_3150_:
{
lean_object* v___f_3152_; lean_object* v___f_3153_; lean_object* v___f_3154_; lean_object* v___f_3155_; uint8_t v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; 
lean_inc_n(v___y_3151_, 2);
lean_inc_n(v_toPure_3140_, 3);
v___f_3152_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__1), 3, 2);
lean_closure_set(v___f_3152_, 0, v_toPure_3140_);
lean_closure_set(v___f_3152_, 1, v___y_3151_);
lean_inc_n(v_toBind_3139_, 3);
v___f_3153_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_3153_, 0, v_toPure_3140_);
lean_closure_set(v___f_3153_, 1, v_toBind_3139_);
lean_closure_set(v___f_3153_, 2, v___f_3152_);
v___f_3154_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__3___boxed), 7, 6);
lean_closure_set(v___f_3154_, 0, v_toPure_3140_);
lean_closure_set(v___f_3154_, 1, v_filter_3118_);
lean_closure_set(v___f_3154_, 2, v___y_3151_);
lean_closure_set(v___f_3154_, 3, v_toBind_3139_);
lean_closure_set(v___f_3154_, 4, v___f_3142_);
lean_closure_set(v___f_3154_, 5, v___f_3153_);
v___f_3155_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__4___boxed), 5, 4);
lean_closure_set(v___f_3155_, 0, v_toPure_3140_);
lean_closure_set(v___f_3155_, 1, v_n_u2080_3117_);
lean_closure_set(v___f_3155_, 2, v_toBind_3139_);
lean_closure_set(v___f_3155_, 3, v___f_3154_);
v___x_3156_ = 0;
v___x_3157_ = l_Lean_resolveGlobalName___redArg(v___x_3130_, v___x_3132_, v___x_3146_, v___x_3147_, v___x_3148_, v___f_3149_, v___y_3151_, v___x_3156_);
v___x_3158_ = lean_apply_4(v_toBind_3139_, lean_box(0), lean_box(0), v___x_3157_, v___f_3155_);
return v___x_3158_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve(lean_object* v_m_3174_, lean_object* v_inst_3175_, lean_object* v_inst_3176_, lean_object* v_inst_3177_, lean_object* v_inst_3178_, lean_object* v_inst_3179_, lean_object* v_inst_3180_, lean_object* v_n_u2080_3181_, lean_object* v_filter_3182_, lean_object* v_view_x3f_3183_, lean_object* v_n_3184_){
_start:
{
lean_object* v___x_3185_; 
v___x_3185_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg(v_inst_3175_, v_inst_3176_, v_inst_3177_, v_inst_3178_, v_inst_3179_, v_inst_3180_, v_n_u2080_3181_, v_filter_3182_, v_view_x3f_3183_, v_n_3184_);
return v___x_3185_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__0(lean_object* v_toPure_3190_, lean_object* v_____x_3191_){
_start:
{
if (lean_obj_tag(v_____x_3191_) == 0)
{
lean_object* v___x_3192_; lean_object* v___x_3193_; 
v___x_3192_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__0___closed__1));
v___x_3193_ = lean_apply_2(v_toPure_3190_, lean_box(0), v___x_3192_);
return v___x_3193_;
}
else
{
lean_object* v___x_3194_; 
v___x_3194_ = lean_apply_2(v_toPure_3190_, lean_box(0), v_____x_3191_);
return v___x_3194_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__1(lean_object* v_toPure_3195_, lean_object* v_____do__lift_3196_){
_start:
{
if (lean_obj_tag(v_____do__lift_3196_) == 0)
{
lean_object* v___x_3197_; lean_object* v___x_3198_; 
v___x_3197_ = lean_box(0);
v___x_3198_ = lean_apply_2(v_toPure_3195_, lean_box(0), v___x_3197_);
return v___x_3198_;
}
else
{
lean_object* v_val_3199_; lean_object* v___x_3201_; uint8_t v_isShared_3202_; uint8_t v_isSharedCheck_3208_; 
v_val_3199_ = lean_ctor_get(v_____do__lift_3196_, 0);
v_isSharedCheck_3208_ = !lean_is_exclusive(v_____do__lift_3196_);
if (v_isSharedCheck_3208_ == 0)
{
v___x_3201_ = v_____do__lift_3196_;
v_isShared_3202_ = v_isSharedCheck_3208_;
goto v_resetjp_3200_;
}
else
{
lean_inc(v_val_3199_);
lean_dec(v_____do__lift_3196_);
v___x_3201_ = lean_box(0);
v_isShared_3202_ = v_isSharedCheck_3208_;
goto v_resetjp_3200_;
}
v_resetjp_3200_:
{
lean_object* v___x_3203_; lean_object* v___x_3205_; 
v___x_3203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3203_, 0, v_val_3199_);
if (v_isShared_3202_ == 0)
{
lean_ctor_set(v___x_3201_, 0, v___x_3203_);
v___x_3205_ = v___x_3201_;
goto v_reusejp_3204_;
}
else
{
lean_object* v_reuseFailAlloc_3207_; 
v_reuseFailAlloc_3207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3207_, 0, v___x_3203_);
v___x_3205_ = v_reuseFailAlloc_3207_;
goto v_reusejp_3204_;
}
v_reusejp_3204_:
{
lean_object* v___x_3206_; 
v___x_3206_ = lean_apply_2(v_toPure_3195_, lean_box(0), v___x_3205_);
return v___x_3206_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__2(lean_object* v_toPure_3209_, lean_object* v___x_3210_, lean_object* v_____do__lift_3211_){
_start:
{
if (lean_obj_tag(v_____do__lift_3211_) == 0)
{
lean_object* v___x_3212_; 
v___x_3212_ = lean_apply_2(v_toPure_3209_, lean_box(0), v___x_3210_);
return v___x_3212_;
}
else
{
lean_object* v_val_3213_; lean_object* v_fst_3214_; lean_object* v___x_3215_; 
lean_dec(v___x_3210_);
v_val_3213_ = lean_ctor_get(v_____do__lift_3211_, 0);
lean_inc(v_val_3213_);
lean_dec_ref_known(v_____do__lift_3211_, 1);
v_fst_3214_ = lean_ctor_get(v_val_3213_, 0);
lean_inc(v_fst_3214_);
lean_dec(v_val_3213_);
v___x_3215_ = lean_apply_2(v_toPure_3209_, lean_box(0), v_fst_3214_);
return v___x_3215_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__3(lean_object* v_toPure_3216_, lean_object* v___x_3217_, lean_object* v___x_3218_, lean_object* v_____do__lift_3219_){
_start:
{
if (lean_obj_tag(v_____do__lift_3219_) == 0)
{
lean_object* v___x_3220_; lean_object* v___x_3221_; 
lean_dec(v___x_3218_);
lean_dec(v___x_3217_);
v___x_3220_ = lean_box(0);
v___x_3221_ = lean_apply_2(v_toPure_3216_, lean_box(0), v___x_3220_);
return v___x_3221_;
}
else
{
lean_object* v_val_3222_; lean_object* v___x_3224_; uint8_t v_isShared_3225_; uint8_t v_isSharedCheck_3253_; 
v_val_3222_ = lean_ctor_get(v_____do__lift_3219_, 0);
v_isSharedCheck_3253_ = !lean_is_exclusive(v_____do__lift_3219_);
if (v_isSharedCheck_3253_ == 0)
{
v___x_3224_ = v_____do__lift_3219_;
v_isShared_3225_ = v_isSharedCheck_3253_;
goto v_resetjp_3223_;
}
else
{
lean_inc(v_val_3222_);
lean_dec(v_____do__lift_3219_);
v___x_3224_ = lean_box(0);
v_isShared_3225_ = v_isSharedCheck_3253_;
goto v_resetjp_3223_;
}
v_resetjp_3223_:
{
if (lean_obj_tag(v_val_3222_) == 0)
{
lean_object* v_a_3226_; lean_object* v___x_3228_; uint8_t v_isShared_3229_; uint8_t v_isSharedCheck_3239_; 
lean_dec(v___x_3218_);
v_a_3226_ = lean_ctor_get(v_val_3222_, 0);
v_isSharedCheck_3239_ = !lean_is_exclusive(v_val_3222_);
if (v_isSharedCheck_3239_ == 0)
{
v___x_3228_ = v_val_3222_;
v_isShared_3229_ = v_isSharedCheck_3239_;
goto v_resetjp_3227_;
}
else
{
lean_inc(v_a_3226_);
lean_dec(v_val_3222_);
v___x_3228_ = lean_box(0);
v_isShared_3229_ = v_isSharedCheck_3239_;
goto v_resetjp_3227_;
}
v_resetjp_3227_:
{
lean_object* v___x_3231_; 
if (v_isShared_3225_ == 0)
{
lean_ctor_set(v___x_3224_, 0, v_a_3226_);
v___x_3231_ = v___x_3224_;
goto v_reusejp_3230_;
}
else
{
lean_object* v_reuseFailAlloc_3238_; 
v_reuseFailAlloc_3238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3238_, 0, v_a_3226_);
v___x_3231_ = v_reuseFailAlloc_3238_;
goto v_reusejp_3230_;
}
v_reusejp_3230_:
{
lean_object* v___x_3232_; lean_object* v___x_3234_; 
v___x_3232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3232_, 0, v___x_3231_);
lean_ctor_set(v___x_3232_, 1, v___x_3217_);
if (v_isShared_3229_ == 0)
{
lean_ctor_set(v___x_3228_, 0, v___x_3232_);
v___x_3234_ = v___x_3228_;
goto v_reusejp_3233_;
}
else
{
lean_object* v_reuseFailAlloc_3237_; 
v_reuseFailAlloc_3237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3237_, 0, v___x_3232_);
v___x_3234_ = v_reuseFailAlloc_3237_;
goto v_reusejp_3233_;
}
v_reusejp_3233_:
{
lean_object* v___x_3235_; lean_object* v___x_3236_; 
v___x_3235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3235_, 0, v___x_3234_);
v___x_3236_ = lean_apply_2(v_toPure_3216_, lean_box(0), v___x_3235_);
return v___x_3236_;
}
}
}
}
else
{
lean_object* v___x_3241_; uint8_t v_isShared_3242_; uint8_t v_isSharedCheck_3251_; 
v_isSharedCheck_3251_ = !lean_is_exclusive(v_val_3222_);
if (v_isSharedCheck_3251_ == 0)
{
lean_object* v_unused_3252_; 
v_unused_3252_ = lean_ctor_get(v_val_3222_, 0);
lean_dec(v_unused_3252_);
v___x_3241_ = v_val_3222_;
v_isShared_3242_ = v_isSharedCheck_3251_;
goto v_resetjp_3240_;
}
else
{
lean_dec(v_val_3222_);
v___x_3241_ = lean_box(0);
v_isShared_3242_ = v_isSharedCheck_3251_;
goto v_resetjp_3240_;
}
v_resetjp_3240_:
{
lean_object* v___x_3243_; lean_object* v___x_3245_; 
v___x_3243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3243_, 0, v___x_3218_);
lean_ctor_set(v___x_3243_, 1, v___x_3217_);
if (v_isShared_3242_ == 0)
{
lean_ctor_set(v___x_3241_, 0, v___x_3243_);
v___x_3245_ = v___x_3241_;
goto v_reusejp_3244_;
}
else
{
lean_object* v_reuseFailAlloc_3250_; 
v_reuseFailAlloc_3250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3250_, 0, v___x_3243_);
v___x_3245_ = v_reuseFailAlloc_3250_;
goto v_reusejp_3244_;
}
v_reusejp_3244_:
{
lean_object* v___x_3247_; 
if (v_isShared_3225_ == 0)
{
lean_ctor_set(v___x_3224_, 0, v___x_3245_);
v___x_3247_ = v___x_3224_;
goto v_reusejp_3246_;
}
else
{
lean_object* v_reuseFailAlloc_3249_; 
v_reuseFailAlloc_3249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3249_, 0, v___x_3245_);
v___x_3247_ = v_reuseFailAlloc_3249_;
goto v_reusejp_3246_;
}
v_reusejp_3246_:
{
lean_object* v___x_3248_; 
v___x_3248_ = lean_apply_2(v_toPure_3216_, lean_box(0), v___x_3247_);
return v___x_3248_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__4(lean_object* v_toPure_3254_, lean_object* v___x_3255_, lean_object* v_inst_3256_, lean_object* v_inst_3257_, lean_object* v_inst_3258_, lean_object* v_inst_3259_, lean_object* v_inst_3260_, lean_object* v_inst_3261_, lean_object* v_n_u2080_3262_, lean_object* v_filter_3263_, lean_object* v_view_x3f_3264_, lean_object* v_toBind_3265_, lean_object* v___f_3266_, lean_object* v___f_3267_, lean_object* v_a_3268_, lean_object* v_x_3269_, lean_object* v___y_3270_){
_start:
{
lean_object* v_snd_3271_; lean_object* v___x_3272_; lean_object* v___f_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; 
v_snd_3271_ = lean_ctor_get(v___y_3270_, 1);
lean_inc(v_snd_3271_);
lean_dec_ref(v___y_3270_);
v___x_3272_ = l_Lean_Name_appendCore(v_a_3268_, v_snd_3271_);
lean_inc(v___x_3272_);
v___f_3273_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__3), 4, 3);
lean_closure_set(v___f_3273_, 0, v_toPure_3254_);
lean_closure_set(v___f_3273_, 1, v___x_3272_);
lean_closure_set(v___f_3273_, 2, v___x_3255_);
v___x_3274_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg(v_inst_3256_, v_inst_3257_, v_inst_3258_, v_inst_3259_, v_inst_3260_, v_inst_3261_, v_n_u2080_3262_, v_filter_3263_, v_view_x3f_3264_, v___x_3272_);
lean_inc_n(v_toBind_3265_, 2);
v___x_3275_ = lean_apply_4(v_toBind_3265_, lean_box(0), lean_box(0), v___x_3274_, v___f_3266_);
v___x_3276_ = lean_apply_4(v_toBind_3265_, lean_box(0), lean_box(0), v___x_3275_, v___f_3267_);
v___x_3277_ = lean_apply_4(v_toBind_3265_, lean_box(0), lean_box(0), v___x_3276_, v___f_3273_);
return v___x_3277_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__4___boxed(lean_object** _args){
lean_object* v_toPure_3278_ = _args[0];
lean_object* v___x_3279_ = _args[1];
lean_object* v_inst_3280_ = _args[2];
lean_object* v_inst_3281_ = _args[3];
lean_object* v_inst_3282_ = _args[4];
lean_object* v_inst_3283_ = _args[5];
lean_object* v_inst_3284_ = _args[6];
lean_object* v_inst_3285_ = _args[7];
lean_object* v_n_u2080_3286_ = _args[8];
lean_object* v_filter_3287_ = _args[9];
lean_object* v_view_x3f_3288_ = _args[10];
lean_object* v_toBind_3289_ = _args[11];
lean_object* v___f_3290_ = _args[12];
lean_object* v___f_3291_ = _args[13];
lean_object* v_a_3292_ = _args[14];
lean_object* v_x_3293_ = _args[15];
lean_object* v___y_3294_ = _args[16];
_start:
{
lean_object* v_res_3295_; 
v_res_3295_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__4(v_toPure_3278_, v___x_3279_, v_inst_3280_, v_inst_3281_, v_inst_3282_, v_inst_3283_, v_inst_3284_, v_inst_3285_, v_n_u2080_3286_, v_filter_3287_, v_view_x3f_3288_, v_toBind_3289_, v___f_3290_, v___f_3291_, v_a_3292_, v_x_3293_, v___y_3294_);
lean_dec(v_a_3292_);
return v_res_3295_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__5(lean_object* v_toPure_3299_, lean_object* v_n_3300_, lean_object* v_inst_3301_, lean_object* v_inst_3302_, lean_object* v_inst_3303_, lean_object* v_inst_3304_, lean_object* v_inst_3305_, lean_object* v_inst_3306_, lean_object* v_n_u2080_3307_, lean_object* v_filter_3308_, lean_object* v_view_x3f_3309_, lean_object* v_toBind_3310_, lean_object* v___f_3311_, lean_object* v___f_3312_, lean_object* v___x_3313_, lean_object* v_____do__lift_3314_){
_start:
{
if (lean_obj_tag(v_____do__lift_3314_) == 0)
{
lean_object* v___x_3315_; lean_object* v___x_3316_; 
lean_dec_ref(v___x_3313_);
lean_dec(v___f_3312_);
lean_dec(v___f_3311_);
lean_dec(v_toBind_3310_);
lean_dec(v_view_x3f_3309_);
lean_dec(v_filter_3308_);
lean_dec(v_n_u2080_3307_);
lean_dec(v_inst_3306_);
lean_dec_ref(v_inst_3305_);
lean_dec(v_inst_3304_);
lean_dec_ref(v_inst_3303_);
lean_dec_ref(v_inst_3302_);
lean_dec_ref(v_inst_3301_);
lean_dec(v_n_3300_);
v___x_3315_ = lean_box(0);
v___x_3316_ = lean_apply_2(v_toPure_3299_, lean_box(0), v___x_3315_);
return v___x_3316_;
}
else
{
lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___f_3320_; lean_object* v___f_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; 
v___x_3317_ = l_Lean_privateToUserName(v_n_3300_);
v___x_3318_ = l_Lean_Name_componentsRev(v___x_3317_);
v___x_3319_ = lean_box(0);
lean_inc(v_toPure_3299_);
v___f_3320_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__2), 3, 2);
lean_closure_set(v___f_3320_, 0, v_toPure_3299_);
lean_closure_set(v___f_3320_, 1, v___x_3319_);
lean_inc(v_toBind_3310_);
v___f_3321_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__4___boxed), 17, 14);
lean_closure_set(v___f_3321_, 0, v_toPure_3299_);
lean_closure_set(v___f_3321_, 1, v___x_3319_);
lean_closure_set(v___f_3321_, 2, v_inst_3301_);
lean_closure_set(v___f_3321_, 3, v_inst_3302_);
lean_closure_set(v___f_3321_, 4, v_inst_3303_);
lean_closure_set(v___f_3321_, 5, v_inst_3304_);
lean_closure_set(v___f_3321_, 6, v_inst_3305_);
lean_closure_set(v___f_3321_, 7, v_inst_3306_);
lean_closure_set(v___f_3321_, 8, v_n_u2080_3307_);
lean_closure_set(v___f_3321_, 9, v_filter_3308_);
lean_closure_set(v___f_3321_, 10, v_view_x3f_3309_);
lean_closure_set(v___f_3321_, 11, v_toBind_3310_);
lean_closure_set(v___f_3321_, 12, v___f_3311_);
lean_closure_set(v___f_3321_, 13, v___f_3312_);
v___x_3322_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__5___closed__0));
v___x_3323_ = l_List_forIn_x27_loop___redArg(v___x_3313_, v___f_3321_, v___x_3318_, v___x_3322_);
lean_dec(v___x_3318_);
v___x_3324_ = lean_apply_4(v_toBind_3310_, lean_box(0), lean_box(0), v___x_3323_, v___f_3320_);
return v___x_3324_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__5___boxed(lean_object* v_toPure_3325_, lean_object* v_n_3326_, lean_object* v_inst_3327_, lean_object* v_inst_3328_, lean_object* v_inst_3329_, lean_object* v_inst_3330_, lean_object* v_inst_3331_, lean_object* v_inst_3332_, lean_object* v_n_u2080_3333_, lean_object* v_filter_3334_, lean_object* v_view_x3f_3335_, lean_object* v_toBind_3336_, lean_object* v___f_3337_, lean_object* v___f_3338_, lean_object* v___x_3339_, lean_object* v_____do__lift_3340_){
_start:
{
lean_object* v_res_3341_; 
v_res_3341_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__5(v_toPure_3325_, v_n_3326_, v_inst_3327_, v_inst_3328_, v_inst_3329_, v_inst_3330_, v_inst_3331_, v_inst_3332_, v_n_u2080_3333_, v_filter_3334_, v_view_x3f_3335_, v_toBind_3336_, v___f_3337_, v___f_3338_, v___x_3339_, v_____do__lift_3340_);
lean_dec(v_____do__lift_3340_);
return v_res_3341_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg(lean_object* v_inst_3342_, lean_object* v_inst_3343_, lean_object* v_inst_3344_, lean_object* v_inst_3345_, lean_object* v_inst_3346_, lean_object* v_inst_3347_, lean_object* v_n_u2080_3348_, lean_object* v_filter_3349_, lean_object* v_view_x3f_3350_, lean_object* v_n_3351_){
_start:
{
lean_object* v___f_3352_; lean_object* v___f_3353_; lean_object* v___f_3354_; lean_object* v___f_3355_; lean_object* v___f_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___y_3363_; uint8_t v___x_3371_; 
lean_inc_ref_n(v_inst_3342_, 7);
v___f_3352_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_3352_, 0, v_inst_3342_);
v___f_3353_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__3), 5, 1);
lean_closure_set(v___f_3353_, 0, v_inst_3342_);
v___f_3354_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__6), 5, 1);
lean_closure_set(v___f_3354_, 0, v_inst_3342_);
v___f_3355_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_3355_, 0, v_inst_3342_);
v___f_3356_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__11), 5, 1);
lean_closure_set(v___f_3356_, 0, v_inst_3342_);
v___x_3357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3357_, 0, v___f_3352_);
lean_ctor_set(v___x_3357_, 1, v___f_3353_);
v___x_3358_ = lean_alloc_closure((void*)(l_OptionT_pure), 4, 2);
lean_closure_set(v___x_3358_, 0, lean_box(0));
lean_closure_set(v___x_3358_, 1, v_inst_3342_);
v___x_3359_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3359_, 0, v___x_3357_);
lean_ctor_set(v___x_3359_, 1, v___x_3358_);
lean_ctor_set(v___x_3359_, 2, v___f_3354_);
lean_ctor_set(v___x_3359_, 3, v___f_3355_);
lean_ctor_set(v___x_3359_, 4, v___f_3356_);
v___x_3360_ = lean_alloc_closure((void*)(l_OptionT_bind), 6, 2);
lean_closure_set(v___x_3360_, 0, lean_box(0));
lean_closure_set(v___x_3360_, 1, v_inst_3342_);
v___x_3361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3361_, 0, v___x_3359_);
lean_ctor_set(v___x_3361_, 1, v___x_3360_);
v___x_3371_ = l_Lean_Name_hasMacroScopes(v_n_3351_);
if (v___x_3371_ == 0)
{
lean_object* v_toApplicative_3372_; lean_object* v_toPure_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; 
v_toApplicative_3372_ = lean_ctor_get(v_inst_3342_, 0);
v_toPure_3373_ = lean_ctor_get(v_toApplicative_3372_, 1);
v___x_3374_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2___closed__0));
lean_inc(v_toPure_3373_);
v___x_3375_ = lean_apply_2(v_toPure_3373_, lean_box(0), v___x_3374_);
v___y_3363_ = v___x_3375_;
goto v___jp_3362_;
}
else
{
lean_object* v_toApplicative_3376_; lean_object* v_toPure_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; 
v_toApplicative_3376_ = lean_ctor_get(v_inst_3342_, 0);
v_toPure_3377_ = lean_ctor_get(v_toApplicative_3376_, 1);
v___x_3378_ = lean_box(0);
lean_inc(v_toPure_3377_);
v___x_3379_ = lean_apply_2(v_toPure_3377_, lean_box(0), v___x_3378_);
v___y_3363_ = v___x_3379_;
goto v___jp_3362_;
}
v___jp_3362_:
{
lean_object* v_toApplicative_3364_; lean_object* v_toBind_3365_; lean_object* v_toPure_3366_; lean_object* v___f_3367_; lean_object* v___f_3368_; lean_object* v___f_3369_; lean_object* v___x_3370_; 
v_toApplicative_3364_ = lean_ctor_get(v_inst_3342_, 0);
v_toBind_3365_ = lean_ctor_get(v_inst_3342_, 1);
lean_inc_n(v_toBind_3365_, 2);
v_toPure_3366_ = lean_ctor_get(v_toApplicative_3364_, 1);
lean_inc_n(v_toPure_3366_, 3);
v___f_3367_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3367_, 0, v_toPure_3366_);
v___f_3368_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__1), 2, 1);
lean_closure_set(v___f_3368_, 0, v_toPure_3366_);
v___f_3369_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__5___boxed), 16, 15);
lean_closure_set(v___f_3369_, 0, v_toPure_3366_);
lean_closure_set(v___f_3369_, 1, v_n_3351_);
lean_closure_set(v___f_3369_, 2, v_inst_3342_);
lean_closure_set(v___f_3369_, 3, v_inst_3343_);
lean_closure_set(v___f_3369_, 4, v_inst_3344_);
lean_closure_set(v___f_3369_, 5, v_inst_3345_);
lean_closure_set(v___f_3369_, 6, v_inst_3346_);
lean_closure_set(v___f_3369_, 7, v_inst_3347_);
lean_closure_set(v___f_3369_, 8, v_n_u2080_3348_);
lean_closure_set(v___f_3369_, 9, v_filter_3349_);
lean_closure_set(v___f_3369_, 10, v_view_x3f_3350_);
lean_closure_set(v___f_3369_, 11, v_toBind_3365_);
lean_closure_set(v___f_3369_, 12, v___f_3368_);
lean_closure_set(v___f_3369_, 13, v___f_3367_);
lean_closure_set(v___f_3369_, 14, v___x_3361_);
v___x_3370_ = lean_apply_4(v_toBind_3365_, lean_box(0), lean_box(0), v___y_3363_, v___f_3369_);
return v___x_3370_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore(lean_object* v_m_3380_, lean_object* v_inst_3381_, lean_object* v_inst_3382_, lean_object* v_inst_3383_, lean_object* v_inst_3384_, lean_object* v_inst_3385_, lean_object* v_inst_3386_, lean_object* v_n_u2080_3387_, lean_object* v_filter_3388_, lean_object* v_view_x3f_3389_, lean_object* v_n_3390_){
_start:
{
lean_object* v___x_3391_; 
v___x_3391_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg(v_inst_3381_, v_inst_3382_, v_inst_3383_, v_inst_3384_, v_inst_3385_, v_inst_3386_, v_n_u2080_3387_, v_filter_3388_, v_view_x3f_3389_, v_n_3390_);
return v___x_3391_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___lam__0(lean_object* v_n_u2081_3392_, lean_object* v_x1_3393_, lean_object* v_x2_3394_){
_start:
{
lean_object* v___x_3395_; lean_object* v___x_3396_; uint8_t v___x_3397_; 
v___x_3395_ = l_Lean_Name_getPrefix(v_x2_3394_);
v___x_3396_ = l_Lean_Name_getPrefix(v_n_u2081_3392_);
v___x_3397_ = l_Lean_Name_isPrefixOf(v___x_3395_, v___x_3396_);
lean_dec(v___x_3396_);
lean_dec(v___x_3395_);
if (v___x_3397_ == 0)
{
lean_dec(v_x2_3394_);
return v_x1_3393_;
}
else
{
lean_object* v___x_3398_; 
v___x_3398_ = lean_array_push(v_x1_3393_, v_x2_3394_);
return v___x_3398_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___lam__0___boxed(lean_object* v_n_u2081_3399_, lean_object* v_x1_3400_, lean_object* v_x2_3401_){
_start:
{
lean_object* v_res_3402_; 
v_res_3402_ = l_Lean_unresolveNameGlobal_x3f___redArg___lam__0(v_n_u2081_3399_, v_x1_3400_, v_x2_3401_);
lean_dec(v_n_u2081_3399_);
return v_res_3402_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___lam__1(lean_object* v_view_3403_, lean_object* v_n_u2081_3404_, lean_object* v_inst_3405_, lean_object* v_inst_3406_, lean_object* v_inst_3407_, lean_object* v_inst_3408_, lean_object* v_inst_3409_, lean_object* v_inst_3410_, lean_object* v_n_u2080_3411_, lean_object* v_filter_3412_, lean_object* v_toPure_3413_, lean_object* v_____do__lift_3414_){
_start:
{
if (lean_obj_tag(v_____do__lift_3414_) == 0)
{
lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; 
lean_dec(v_toPure_3413_);
v___x_3415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3415_, 0, v_view_3403_);
v___x_3416_ = l_Lean_rootNamespace;
v___x_3417_ = l_Lean_Name_append(v___x_3416_, v_n_u2081_3404_);
v___x_3418_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg(v_inst_3405_, v_inst_3406_, v_inst_3407_, v_inst_3408_, v_inst_3409_, v_inst_3410_, v_n_u2080_3411_, v_filter_3412_, v___x_3415_, v___x_3417_);
return v___x_3418_;
}
else
{
lean_object* v___x_3419_; 
lean_dec(v_filter_3412_);
lean_dec(v_n_u2080_3411_);
lean_dec(v_inst_3410_);
lean_dec_ref(v_inst_3409_);
lean_dec(v_inst_3408_);
lean_dec_ref(v_inst_3407_);
lean_dec_ref(v_inst_3406_);
lean_dec_ref(v_inst_3405_);
lean_dec(v_n_u2081_3404_);
lean_dec_ref(v_view_3403_);
v___x_3419_ = lean_apply_2(v_toPure_3413_, lean_box(0), v_____do__lift_3414_);
return v___x_3419_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___lam__2(lean_object* v_toPure_3420_, lean_object* v_inst_3421_, lean_object* v_inst_3422_, lean_object* v_inst_3423_, lean_object* v_inst_3424_, lean_object* v_inst_3425_, lean_object* v_inst_3426_, lean_object* v_n_u2080_3427_, lean_object* v_filter_3428_, lean_object* v_toBind_3429_, lean_object* v___f_3430_, uint8_t v_allowHorizAliases_3431_, lean_object* v___f_3432_, lean_object* v_____do__lift_3433_){
_start:
{
lean_object* v_aliases_3435_; 
if (lean_obj_tag(v_____do__lift_3433_) == 0)
{
lean_object* v___x_3442_; lean_object* v___x_3443_; 
lean_dec_ref(v___f_3432_);
lean_dec(v___f_3430_);
lean_dec(v_toBind_3429_);
lean_dec(v_filter_3428_);
lean_dec(v_n_u2080_3427_);
lean_dec(v_inst_3426_);
lean_dec_ref(v_inst_3425_);
lean_dec(v_inst_3424_);
lean_dec_ref(v_inst_3423_);
lean_dec_ref(v_inst_3422_);
lean_dec_ref(v_inst_3421_);
v___x_3442_ = lean_box(0);
v___x_3443_ = lean_apply_2(v_toPure_3420_, lean_box(0), v___x_3442_);
return v___x_3443_;
}
else
{
lean_object* v_val_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; 
lean_dec(v_toPure_3420_);
v_val_3444_ = lean_ctor_get(v_____do__lift_3433_, 0);
lean_inc(v_val_3444_);
lean_dec_ref_known(v_____do__lift_3433_, 1);
lean_inc(v_n_u2080_3427_);
v___x_3445_ = l_Lean_getRevAliases(v_val_3444_, v_n_u2080_3427_);
v___x_3446_ = lean_array_mk(v___x_3445_);
if (v_allowHorizAliases_3431_ == 0)
{
lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; uint8_t v___x_3451_; 
v___x_3447_ = lean_unsigned_to_nat(0u);
v___x_3448_ = lean_array_get_size(v___x_3446_);
v___x_3449_ = ((lean_object*)(l_Lean_resolveNamespace___redArg___closed__1));
v___x_3450_ = ((lean_object*)(l_Lean_resolveLocalName___redArg___lam__3___closed__9));
v___x_3451_ = lean_nat_dec_lt(v___x_3447_, v___x_3448_);
if (v___x_3451_ == 0)
{
lean_dec_ref(v___x_3446_);
lean_dec_ref(v___f_3432_);
v_aliases_3435_ = v___x_3449_;
goto v___jp_3434_;
}
else
{
uint8_t v___x_3452_; 
v___x_3452_ = lean_nat_dec_le(v___x_3448_, v___x_3448_);
if (v___x_3452_ == 0)
{
if (v___x_3451_ == 0)
{
lean_dec_ref(v___x_3446_);
lean_dec_ref(v___f_3432_);
v_aliases_3435_ = v___x_3449_;
goto v___jp_3434_;
}
else
{
size_t v___x_3453_; size_t v___x_3454_; lean_object* v___x_3455_; 
v___x_3453_ = ((size_t)0ULL);
v___x_3454_ = lean_usize_of_nat(v___x_3448_);
v___x_3455_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3450_, v___f_3432_, v___x_3446_, v___x_3453_, v___x_3454_, v___x_3449_);
v_aliases_3435_ = v___x_3455_;
goto v___jp_3434_;
}
}
else
{
size_t v___x_3456_; size_t v___x_3457_; lean_object* v___x_3458_; 
v___x_3456_ = ((size_t)0ULL);
v___x_3457_ = lean_usize_of_nat(v___x_3448_);
v___x_3458_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3450_, v___f_3432_, v___x_3446_, v___x_3456_, v___x_3457_, v___x_3449_);
v_aliases_3435_ = v___x_3458_;
goto v___jp_3434_;
}
}
}
else
{
lean_dec_ref(v___f_3432_);
v_aliases_3435_ = v___x_3446_;
goto v___jp_3434_;
}
}
v___jp_3434_:
{
lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; 
lean_inc_ref(v_inst_3421_);
v___x_3436_ = l_OptionT_instAlternative___redArg(v_inst_3421_);
v___x_3437_ = lean_box(0);
v___x_3438_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore), 11, 10);
lean_closure_set(v___x_3438_, 0, lean_box(0));
lean_closure_set(v___x_3438_, 1, v_inst_3421_);
lean_closure_set(v___x_3438_, 2, v_inst_3422_);
lean_closure_set(v___x_3438_, 3, v_inst_3423_);
lean_closure_set(v___x_3438_, 4, v_inst_3424_);
lean_closure_set(v___x_3438_, 5, v_inst_3425_);
lean_closure_set(v___x_3438_, 6, v_inst_3426_);
lean_closure_set(v___x_3438_, 7, v_n_u2080_3427_);
lean_closure_set(v___x_3438_, 8, v_filter_3428_);
lean_closure_set(v___x_3438_, 9, v___x_3437_);
v___x_3439_ = lean_unsigned_to_nat(0u);
v___x_3440_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go(lean_box(0), lean_box(0), lean_box(0), v___x_3436_, v___x_3438_, v_aliases_3435_, v___x_3439_);
v___x_3441_ = lean_apply_4(v_toBind_3429_, lean_box(0), lean_box(0), v___x_3440_, v___f_3430_);
return v___x_3441_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___lam__2___boxed(lean_object* v_toPure_3459_, lean_object* v_inst_3460_, lean_object* v_inst_3461_, lean_object* v_inst_3462_, lean_object* v_inst_3463_, lean_object* v_inst_3464_, lean_object* v_inst_3465_, lean_object* v_n_u2080_3466_, lean_object* v_filter_3467_, lean_object* v_toBind_3468_, lean_object* v___f_3469_, lean_object* v_allowHorizAliases_3470_, lean_object* v___f_3471_, lean_object* v_____do__lift_3472_){
_start:
{
uint8_t v_allowHorizAliases_boxed_3473_; lean_object* v_res_3474_; 
v_allowHorizAliases_boxed_3473_ = lean_unbox(v_allowHorizAliases_3470_);
v_res_3474_ = l_Lean_unresolveNameGlobal_x3f___redArg___lam__2(v_toPure_3459_, v_inst_3460_, v_inst_3461_, v_inst_3462_, v_inst_3463_, v_inst_3464_, v_inst_3465_, v_n_u2080_3466_, v_filter_3467_, v_toBind_3468_, v___f_3469_, v_allowHorizAliases_boxed_3473_, v___f_3471_, v_____do__lift_3472_);
return v_res_3474_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___lam__3(lean_object* v_toPure_3475_, lean_object* v_____do__lift_3476_){
_start:
{
lean_object* v___x_3477_; lean_object* v___x_3478_; 
v___x_3477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3477_, 0, v_____do__lift_3476_);
v___x_3478_ = lean_apply_2(v_toPure_3475_, lean_box(0), v___x_3477_);
return v___x_3478_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___lam__4(lean_object* v_n_u2081_3479_, lean_object* v_inst_3480_, lean_object* v_inst_3481_, lean_object* v_inst_3482_, lean_object* v_inst_3483_, lean_object* v_inst_3484_, lean_object* v_inst_3485_, lean_object* v_n_u2080_3486_, lean_object* v_filter_3487_, lean_object* v___x_3488_, lean_object* v_toPure_3489_, lean_object* v_____do__lift_3490_){
_start:
{
if (lean_obj_tag(v_____do__lift_3490_) == 0)
{
lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; 
lean_dec(v_toPure_3489_);
v___x_3491_ = l_Lean_rootNamespace;
v___x_3492_ = l_Lean_Name_append(v___x_3491_, v_n_u2081_3479_);
v___x_3493_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg(v_inst_3480_, v_inst_3481_, v_inst_3482_, v_inst_3483_, v_inst_3484_, v_inst_3485_, v_n_u2080_3486_, v_filter_3487_, v___x_3488_, v___x_3492_);
return v___x_3493_;
}
else
{
lean_object* v___x_3494_; 
lean_dec(v___x_3488_);
lean_dec(v_filter_3487_);
lean_dec(v_n_u2080_3486_);
lean_dec(v_inst_3485_);
lean_dec_ref(v_inst_3484_);
lean_dec(v_inst_3483_);
lean_dec_ref(v_inst_3482_);
lean_dec_ref(v_inst_3481_);
lean_dec_ref(v_inst_3480_);
lean_dec(v_n_u2081_3479_);
v___x_3494_ = lean_apply_2(v_toPure_3489_, lean_box(0), v_____do__lift_3490_);
return v___x_3494_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg(lean_object* v_inst_3495_, lean_object* v_inst_3496_, lean_object* v_inst_3497_, lean_object* v_inst_3498_, lean_object* v_inst_3499_, lean_object* v_inst_3500_, lean_object* v_n_u2080_3501_, uint8_t v_fullNames_3502_, uint8_t v_allowHorizAliases_3503_, lean_object* v_filter_3504_){
_start:
{
lean_object* v_view_3505_; lean_object* v_name_3506_; lean_object* v_n_u2081_3507_; 
lean_inc(v_n_u2080_3501_);
v_view_3505_ = l_Lean_extractMacroScopes(v_n_u2080_3501_);
v_name_3506_ = lean_ctor_get(v_view_3505_, 0);
lean_inc(v_name_3506_);
v_n_u2081_3507_ = l_Lean_privateToUserName(v_name_3506_);
if (v_fullNames_3502_ == 0)
{
lean_object* v_toApplicative_3508_; lean_object* v_getEnv_3509_; lean_object* v_toBind_3510_; lean_object* v_toPure_3511_; lean_object* v___f_3512_; lean_object* v___f_3513_; lean_object* v___x_3514_; lean_object* v___f_3515_; lean_object* v___f_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; 
v_toApplicative_3508_ = lean_ctor_get(v_inst_3495_, 0);
v_getEnv_3509_ = lean_ctor_get(v_inst_3497_, 0);
lean_inc(v_getEnv_3509_);
v_toBind_3510_ = lean_ctor_get(v_inst_3495_, 1);
lean_inc_n(v_toBind_3510_, 3);
v_toPure_3511_ = lean_ctor_get(v_toApplicative_3508_, 1);
lean_inc_n(v_toPure_3511_, 3);
lean_inc(v_n_u2081_3507_);
v___f_3512_ = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal_x3f___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3512_, 0, v_n_u2081_3507_);
lean_inc(v_filter_3504_);
lean_inc(v_n_u2080_3501_);
lean_inc(v_inst_3500_);
lean_inc_ref(v_inst_3499_);
lean_inc(v_inst_3498_);
lean_inc_ref(v_inst_3497_);
lean_inc_ref(v_inst_3496_);
lean_inc_ref(v_inst_3495_);
v___f_3513_ = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal_x3f___redArg___lam__1), 12, 11);
lean_closure_set(v___f_3513_, 0, v_view_3505_);
lean_closure_set(v___f_3513_, 1, v_n_u2081_3507_);
lean_closure_set(v___f_3513_, 2, v_inst_3495_);
lean_closure_set(v___f_3513_, 3, v_inst_3496_);
lean_closure_set(v___f_3513_, 4, v_inst_3497_);
lean_closure_set(v___f_3513_, 5, v_inst_3498_);
lean_closure_set(v___f_3513_, 6, v_inst_3499_);
lean_closure_set(v___f_3513_, 7, v_inst_3500_);
lean_closure_set(v___f_3513_, 8, v_n_u2080_3501_);
lean_closure_set(v___f_3513_, 9, v_filter_3504_);
lean_closure_set(v___f_3513_, 10, v_toPure_3511_);
v___x_3514_ = lean_box(v_allowHorizAliases_3503_);
v___f_3515_ = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal_x3f___redArg___lam__2___boxed), 14, 13);
lean_closure_set(v___f_3515_, 0, v_toPure_3511_);
lean_closure_set(v___f_3515_, 1, v_inst_3495_);
lean_closure_set(v___f_3515_, 2, v_inst_3496_);
lean_closure_set(v___f_3515_, 3, v_inst_3497_);
lean_closure_set(v___f_3515_, 4, v_inst_3498_);
lean_closure_set(v___f_3515_, 5, v_inst_3499_);
lean_closure_set(v___f_3515_, 6, v_inst_3500_);
lean_closure_set(v___f_3515_, 7, v_n_u2080_3501_);
lean_closure_set(v___f_3515_, 8, v_filter_3504_);
lean_closure_set(v___f_3515_, 9, v_toBind_3510_);
lean_closure_set(v___f_3515_, 10, v___f_3513_);
lean_closure_set(v___f_3515_, 11, v___x_3514_);
lean_closure_set(v___f_3515_, 12, v___f_3512_);
v___f_3516_ = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal_x3f___redArg___lam__3), 2, 1);
lean_closure_set(v___f_3516_, 0, v_toPure_3511_);
v___x_3517_ = lean_apply_4(v_toBind_3510_, lean_box(0), lean_box(0), v_getEnv_3509_, v___f_3516_);
v___x_3518_ = lean_apply_4(v_toBind_3510_, lean_box(0), lean_box(0), v___x_3517_, v___f_3515_);
return v___x_3518_;
}
else
{
lean_object* v_toApplicative_3519_; lean_object* v_toBind_3520_; lean_object* v_toPure_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___f_3524_; lean_object* v___x_3525_; 
v_toApplicative_3519_ = lean_ctor_get(v_inst_3495_, 0);
v_toBind_3520_ = lean_ctor_get(v_inst_3495_, 1);
lean_inc(v_toBind_3520_);
v_toPure_3521_ = lean_ctor_get(v_toApplicative_3519_, 1);
lean_inc(v_toPure_3521_);
v___x_3522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3522_, 0, v_view_3505_);
lean_inc(v_n_u2081_3507_);
lean_inc_ref(v___x_3522_);
lean_inc(v_filter_3504_);
lean_inc(v_n_u2080_3501_);
lean_inc(v_inst_3500_);
lean_inc_ref(v_inst_3499_);
lean_inc(v_inst_3498_);
lean_inc_ref(v_inst_3497_);
lean_inc_ref(v_inst_3496_);
lean_inc_ref(v_inst_3495_);
v___x_3523_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg(v_inst_3495_, v_inst_3496_, v_inst_3497_, v_inst_3498_, v_inst_3499_, v_inst_3500_, v_n_u2080_3501_, v_filter_3504_, v___x_3522_, v_n_u2081_3507_);
v___f_3524_ = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal_x3f___redArg___lam__4), 12, 11);
lean_closure_set(v___f_3524_, 0, v_n_u2081_3507_);
lean_closure_set(v___f_3524_, 1, v_inst_3495_);
lean_closure_set(v___f_3524_, 2, v_inst_3496_);
lean_closure_set(v___f_3524_, 3, v_inst_3497_);
lean_closure_set(v___f_3524_, 4, v_inst_3498_);
lean_closure_set(v___f_3524_, 5, v_inst_3499_);
lean_closure_set(v___f_3524_, 6, v_inst_3500_);
lean_closure_set(v___f_3524_, 7, v_n_u2080_3501_);
lean_closure_set(v___f_3524_, 8, v_filter_3504_);
lean_closure_set(v___f_3524_, 9, v___x_3522_);
lean_closure_set(v___f_3524_, 10, v_toPure_3521_);
v___x_3525_ = lean_apply_4(v_toBind_3520_, lean_box(0), lean_box(0), v___x_3523_, v___f_3524_);
return v___x_3525_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___boxed(lean_object* v_inst_3526_, lean_object* v_inst_3527_, lean_object* v_inst_3528_, lean_object* v_inst_3529_, lean_object* v_inst_3530_, lean_object* v_inst_3531_, lean_object* v_n_u2080_3532_, lean_object* v_fullNames_3533_, lean_object* v_allowHorizAliases_3534_, lean_object* v_filter_3535_){
_start:
{
uint8_t v_fullNames_boxed_3536_; uint8_t v_allowHorizAliases_boxed_3537_; lean_object* v_res_3538_; 
v_fullNames_boxed_3536_ = lean_unbox(v_fullNames_3533_);
v_allowHorizAliases_boxed_3537_ = lean_unbox(v_allowHorizAliases_3534_);
v_res_3538_ = l_Lean_unresolveNameGlobal_x3f___redArg(v_inst_3526_, v_inst_3527_, v_inst_3528_, v_inst_3529_, v_inst_3530_, v_inst_3531_, v_n_u2080_3532_, v_fullNames_boxed_3536_, v_allowHorizAliases_boxed_3537_, v_filter_3535_);
return v_res_3538_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f(lean_object* v_m_3539_, lean_object* v_inst_3540_, lean_object* v_inst_3541_, lean_object* v_inst_3542_, lean_object* v_inst_3543_, lean_object* v_inst_3544_, lean_object* v_inst_3545_, lean_object* v_n_u2080_3546_, uint8_t v_fullNames_3547_, uint8_t v_allowHorizAliases_3548_, lean_object* v_filter_3549_){
_start:
{
lean_object* v___x_3550_; 
v___x_3550_ = l_Lean_unresolveNameGlobal_x3f___redArg(v_inst_3540_, v_inst_3541_, v_inst_3542_, v_inst_3543_, v_inst_3544_, v_inst_3545_, v_n_u2080_3546_, v_fullNames_3547_, v_allowHorizAliases_3548_, v_filter_3549_);
return v___x_3550_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___boxed(lean_object* v_m_3551_, lean_object* v_inst_3552_, lean_object* v_inst_3553_, lean_object* v_inst_3554_, lean_object* v_inst_3555_, lean_object* v_inst_3556_, lean_object* v_inst_3557_, lean_object* v_n_u2080_3558_, lean_object* v_fullNames_3559_, lean_object* v_allowHorizAliases_3560_, lean_object* v_filter_3561_){
_start:
{
uint8_t v_fullNames_boxed_3562_; uint8_t v_allowHorizAliases_boxed_3563_; lean_object* v_res_3564_; 
v_fullNames_boxed_3562_ = lean_unbox(v_fullNames_3559_);
v_allowHorizAliases_boxed_3563_ = lean_unbox(v_allowHorizAliases_3560_);
v_res_3564_ = l_Lean_unresolveNameGlobal_x3f(v_m_3551_, v_inst_3552_, v_inst_3553_, v_inst_3554_, v_inst_3555_, v_inst_3556_, v_inst_3557_, v_n_u2080_3558_, v_fullNames_boxed_3562_, v_allowHorizAliases_boxed_3563_, v_filter_3561_);
return v_res_3564_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___redArg___lam__0(lean_object* v_toPure_3565_, lean_object* v_n_u2080_3566_, lean_object* v_n_x3f_3567_){
_start:
{
if (lean_obj_tag(v_n_x3f_3567_) == 0)
{
lean_object* v___x_3568_; 
v___x_3568_ = lean_apply_2(v_toPure_3565_, lean_box(0), v_n_u2080_3566_);
return v___x_3568_;
}
else
{
lean_object* v_val_3569_; lean_object* v___x_3570_; 
lean_dec(v_n_u2080_3566_);
v_val_3569_ = lean_ctor_get(v_n_x3f_3567_, 0);
lean_inc(v_val_3569_);
lean_dec_ref_known(v_n_x3f_3567_, 1);
v___x_3570_ = lean_apply_2(v_toPure_3565_, lean_box(0), v_val_3569_);
return v___x_3570_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___redArg(lean_object* v_inst_3571_, lean_object* v_inst_3572_, lean_object* v_inst_3573_, lean_object* v_inst_3574_, lean_object* v_inst_3575_, lean_object* v_inst_3576_, lean_object* v_n_u2080_3577_, uint8_t v_fullNames_3578_, uint8_t v_allowHorizAliases_3579_, lean_object* v_filter_3580_){
_start:
{
lean_object* v_toApplicative_3581_; lean_object* v_toBind_3582_; lean_object* v_toPure_3583_; lean_object* v___x_3584_; lean_object* v___f_3585_; lean_object* v___x_3586_; 
v_toApplicative_3581_ = lean_ctor_get(v_inst_3571_, 0);
v_toBind_3582_ = lean_ctor_get(v_inst_3571_, 1);
lean_inc(v_toBind_3582_);
v_toPure_3583_ = lean_ctor_get(v_toApplicative_3581_, 1);
lean_inc(v_toPure_3583_);
lean_inc(v_n_u2080_3577_);
v___x_3584_ = l_Lean_unresolveNameGlobal_x3f___redArg(v_inst_3571_, v_inst_3572_, v_inst_3573_, v_inst_3574_, v_inst_3575_, v_inst_3576_, v_n_u2080_3577_, v_fullNames_3578_, v_allowHorizAliases_3579_, v_filter_3580_);
v___f_3585_ = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3585_, 0, v_toPure_3583_);
lean_closure_set(v___f_3585_, 1, v_n_u2080_3577_);
v___x_3586_ = lean_apply_4(v_toBind_3582_, lean_box(0), lean_box(0), v___x_3584_, v___f_3585_);
return v___x_3586_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___redArg___boxed(lean_object* v_inst_3587_, lean_object* v_inst_3588_, lean_object* v_inst_3589_, lean_object* v_inst_3590_, lean_object* v_inst_3591_, lean_object* v_inst_3592_, lean_object* v_n_u2080_3593_, lean_object* v_fullNames_3594_, lean_object* v_allowHorizAliases_3595_, lean_object* v_filter_3596_){
_start:
{
uint8_t v_fullNames_boxed_3597_; uint8_t v_allowHorizAliases_boxed_3598_; lean_object* v_res_3599_; 
v_fullNames_boxed_3597_ = lean_unbox(v_fullNames_3594_);
v_allowHorizAliases_boxed_3598_ = lean_unbox(v_allowHorizAliases_3595_);
v_res_3599_ = l_Lean_unresolveNameGlobal___redArg(v_inst_3587_, v_inst_3588_, v_inst_3589_, v_inst_3590_, v_inst_3591_, v_inst_3592_, v_n_u2080_3593_, v_fullNames_boxed_3597_, v_allowHorizAliases_boxed_3598_, v_filter_3596_);
return v_res_3599_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal(lean_object* v_m_3600_, lean_object* v_inst_3601_, lean_object* v_inst_3602_, lean_object* v_inst_3603_, lean_object* v_inst_3604_, lean_object* v_inst_3605_, lean_object* v_inst_3606_, lean_object* v_n_u2080_3607_, uint8_t v_fullNames_3608_, uint8_t v_allowHorizAliases_3609_, lean_object* v_filter_3610_){
_start:
{
lean_object* v___x_3611_; 
v___x_3611_ = l_Lean_unresolveNameGlobal___redArg(v_inst_3601_, v_inst_3602_, v_inst_3603_, v_inst_3604_, v_inst_3605_, v_inst_3606_, v_n_u2080_3607_, v_fullNames_3608_, v_allowHorizAliases_3609_, v_filter_3610_);
return v___x_3611_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___boxed(lean_object* v_m_3612_, lean_object* v_inst_3613_, lean_object* v_inst_3614_, lean_object* v_inst_3615_, lean_object* v_inst_3616_, lean_object* v_inst_3617_, lean_object* v_inst_3618_, lean_object* v_n_u2080_3619_, lean_object* v_fullNames_3620_, lean_object* v_allowHorizAliases_3621_, lean_object* v_filter_3622_){
_start:
{
uint8_t v_fullNames_boxed_3623_; uint8_t v_allowHorizAliases_boxed_3624_; lean_object* v_res_3625_; 
v_fullNames_boxed_3623_ = lean_unbox(v_fullNames_3620_);
v_allowHorizAliases_boxed_3624_ = lean_unbox(v_allowHorizAliases_3621_);
v_res_3625_ = l_Lean_unresolveNameGlobal(v_m_3612_, v_inst_3613_, v_inst_3614_, v_inst_3615_, v_inst_3616_, v_inst_3617_, v_inst_3618_, v_n_u2080_3619_, v_fullNames_boxed_3623_, v_allowHorizAliases_boxed_3624_, v_filter_3622_);
return v_res_3625_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg___lam__0(lean_object* v_toFunctor_3627_, lean_object* v_inst_3628_, lean_object* v_inst_3629_, lean_object* v_inst_3630_, lean_object* v_inst_3631_, lean_object* v_inst_3632_, lean_object* v_inst_3633_, lean_object* v_inst_3634_, lean_object* v_n_3635_){
_start:
{
lean_object* v_map_3636_; lean_object* v___x_3637_; lean_object* v___x_3638_; lean_object* v___x_3639_; 
v_map_3636_ = lean_ctor_get(v_toFunctor_3627_, 0);
lean_inc(v_map_3636_);
lean_dec_ref(v_toFunctor_3627_);
v___x_3637_ = ((lean_object*)(l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg___lam__0___closed__0));
v___x_3638_ = l_Lean_resolveLocalName___redArg(v_inst_3628_, v_inst_3629_, v_inst_3630_, v_inst_3631_, v_inst_3632_, v_inst_3633_, v_inst_3634_, v_n_3635_);
v___x_3639_ = lean_apply_4(v_map_3636_, lean_box(0), lean_box(0), v___x_3637_, v___x_3638_);
return v___x_3639_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg(lean_object* v_inst_3640_, lean_object* v_inst_3641_, lean_object* v_inst_3642_, lean_object* v_inst_3643_, lean_object* v_inst_3644_, lean_object* v_inst_3645_, lean_object* v_inst_3646_, lean_object* v_n_u2080_3647_, uint8_t v_fullNames_3648_){
_start:
{
lean_object* v_toApplicative_3649_; lean_object* v_toFunctor_3650_; uint8_t v___x_3651_; lean_object* v___f_3652_; lean_object* v___x_3653_; 
v_toApplicative_3649_ = lean_ctor_get(v_inst_3640_, 0);
v_toFunctor_3650_ = lean_ctor_get(v_toApplicative_3649_, 0);
v___x_3651_ = 0;
lean_inc(v_inst_3645_);
lean_inc_ref(v_inst_3644_);
lean_inc(v_inst_3643_);
lean_inc_ref(v_inst_3642_);
lean_inc_ref(v_inst_3641_);
lean_inc_ref(v_inst_3640_);
lean_inc_ref(v_toFunctor_3650_);
v___f_3652_ = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg___lam__0), 9, 8);
lean_closure_set(v___f_3652_, 0, v_toFunctor_3650_);
lean_closure_set(v___f_3652_, 1, v_inst_3640_);
lean_closure_set(v___f_3652_, 2, v_inst_3641_);
lean_closure_set(v___f_3652_, 3, v_inst_3642_);
lean_closure_set(v___f_3652_, 4, v_inst_3643_);
lean_closure_set(v___f_3652_, 5, v_inst_3644_);
lean_closure_set(v___f_3652_, 6, v_inst_3645_);
lean_closure_set(v___f_3652_, 7, v_inst_3646_);
v___x_3653_ = l_Lean_unresolveNameGlobal_x3f___redArg(v_inst_3640_, v_inst_3641_, v_inst_3642_, v_inst_3643_, v_inst_3644_, v_inst_3645_, v_n_u2080_3647_, v_fullNames_3648_, v___x_3651_, v___f_3652_);
return v___x_3653_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg___boxed(lean_object* v_inst_3654_, lean_object* v_inst_3655_, lean_object* v_inst_3656_, lean_object* v_inst_3657_, lean_object* v_inst_3658_, lean_object* v_inst_3659_, lean_object* v_inst_3660_, lean_object* v_n_u2080_3661_, lean_object* v_fullNames_3662_){
_start:
{
uint8_t v_fullNames_boxed_3663_; lean_object* v_res_3664_; 
v_fullNames_boxed_3663_ = lean_unbox(v_fullNames_3662_);
v_res_3664_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg(v_inst_3654_, v_inst_3655_, v_inst_3656_, v_inst_3657_, v_inst_3658_, v_inst_3659_, v_inst_3660_, v_n_u2080_3661_, v_fullNames_boxed_3663_);
return v_res_3664_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f(lean_object* v_m_3665_, lean_object* v_inst_3666_, lean_object* v_inst_3667_, lean_object* v_inst_3668_, lean_object* v_inst_3669_, lean_object* v_inst_3670_, lean_object* v_inst_3671_, lean_object* v_inst_3672_, lean_object* v_n_u2080_3673_, uint8_t v_fullNames_3674_){
_start:
{
lean_object* v___x_3675_; 
v___x_3675_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg(v_inst_3666_, v_inst_3667_, v_inst_3668_, v_inst_3669_, v_inst_3670_, v_inst_3671_, v_inst_3672_, v_n_u2080_3673_, v_fullNames_3674_);
return v___x_3675_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___boxed(lean_object* v_m_3676_, lean_object* v_inst_3677_, lean_object* v_inst_3678_, lean_object* v_inst_3679_, lean_object* v_inst_3680_, lean_object* v_inst_3681_, lean_object* v_inst_3682_, lean_object* v_inst_3683_, lean_object* v_n_u2080_3684_, lean_object* v_fullNames_3685_){
_start:
{
uint8_t v_fullNames_boxed_3686_; lean_object* v_res_3687_; 
v_fullNames_boxed_3686_ = lean_unbox(v_fullNames_3685_);
v_res_3687_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f(v_m_3676_, v_inst_3677_, v_inst_3678_, v_inst_3679_, v_inst_3680_, v_inst_3681_, v_inst_3682_, v_inst_3683_, v_n_u2080_3684_, v_fullNames_boxed_3686_);
return v_res_3687_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals___redArg(lean_object* v_inst_3688_, lean_object* v_inst_3689_, lean_object* v_inst_3690_, lean_object* v_inst_3691_, lean_object* v_inst_3692_, lean_object* v_inst_3693_, lean_object* v_inst_3694_, lean_object* v_n_u2080_3695_, uint8_t v_fullNames_3696_){
_start:
{
lean_object* v_toApplicative_3697_; lean_object* v_toBind_3698_; lean_object* v_toPure_3699_; lean_object* v___x_3700_; lean_object* v___f_3701_; lean_object* v___x_3702_; 
v_toApplicative_3697_ = lean_ctor_get(v_inst_3688_, 0);
v_toBind_3698_ = lean_ctor_get(v_inst_3688_, 1);
lean_inc(v_toBind_3698_);
v_toPure_3699_ = lean_ctor_get(v_toApplicative_3697_, 1);
lean_inc(v_toPure_3699_);
lean_inc(v_n_u2080_3695_);
v___x_3700_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg(v_inst_3688_, v_inst_3689_, v_inst_3690_, v_inst_3691_, v_inst_3692_, v_inst_3693_, v_inst_3694_, v_n_u2080_3695_, v_fullNames_3696_);
v___f_3701_ = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3701_, 0, v_toPure_3699_);
lean_closure_set(v___f_3701_, 1, v_n_u2080_3695_);
v___x_3702_ = lean_apply_4(v_toBind_3698_, lean_box(0), lean_box(0), v___x_3700_, v___f_3701_);
return v___x_3702_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals___redArg___boxed(lean_object* v_inst_3703_, lean_object* v_inst_3704_, lean_object* v_inst_3705_, lean_object* v_inst_3706_, lean_object* v_inst_3707_, lean_object* v_inst_3708_, lean_object* v_inst_3709_, lean_object* v_n_u2080_3710_, lean_object* v_fullNames_3711_){
_start:
{
uint8_t v_fullNames_boxed_3712_; lean_object* v_res_3713_; 
v_fullNames_boxed_3712_ = lean_unbox(v_fullNames_3711_);
v_res_3713_ = l_Lean_unresolveNameGlobalAvoidingLocals___redArg(v_inst_3703_, v_inst_3704_, v_inst_3705_, v_inst_3706_, v_inst_3707_, v_inst_3708_, v_inst_3709_, v_n_u2080_3710_, v_fullNames_boxed_3712_);
return v_res_3713_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals(lean_object* v_m_3714_, lean_object* v_inst_3715_, lean_object* v_inst_3716_, lean_object* v_inst_3717_, lean_object* v_inst_3718_, lean_object* v_inst_3719_, lean_object* v_inst_3720_, lean_object* v_inst_3721_, lean_object* v_n_u2080_3722_, uint8_t v_fullNames_3723_){
_start:
{
lean_object* v___x_3724_; 
v___x_3724_ = l_Lean_unresolveNameGlobalAvoidingLocals___redArg(v_inst_3715_, v_inst_3716_, v_inst_3717_, v_inst_3718_, v_inst_3719_, v_inst_3720_, v_inst_3721_, v_n_u2080_3722_, v_fullNames_3723_);
return v___x_3724_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals___boxed(lean_object* v_m_3725_, lean_object* v_inst_3726_, lean_object* v_inst_3727_, lean_object* v_inst_3728_, lean_object* v_inst_3729_, lean_object* v_inst_3730_, lean_object* v_inst_3731_, lean_object* v_inst_3732_, lean_object* v_n_u2080_3733_, lean_object* v_fullNames_3734_){
_start:
{
uint8_t v_fullNames_boxed_3735_; lean_object* v_res_3736_; 
v_fullNames_boxed_3735_ = lean_unbox(v_fullNames_3734_);
v_res_3736_ = l_Lean_unresolveNameGlobalAvoidingLocals(v_m_3725_, v_inst_3726_, v_inst_3727_, v_inst_3728_, v_inst_3729_, v_inst_3730_, v_inst_3731_, v_inst_3732_, v_n_u2080_3733_, v_fullNames_boxed_3735_);
return v_res_3736_;
}
}
lean_object* runtime_initialize_Lean_Modifiers(uint8_t builtin);
lean_object* runtime_initialize_Lean_Exception(uint8_t builtin);
lean_object* runtime_initialize_Lean_Namespace(uint8_t builtin);
lean_object* runtime_initialize_Lean_Log(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_ResolveName(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Modifiers(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Exception(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Namespace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Log(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_2351709485____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_reservedNamePredicatesRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_reservedNamePredicatesRef);
lean_dec_ref(res);
res = l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_405991711____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_reservedNamePredicatesExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_reservedNamePredicatesExt);
lean_dec_ref(res);
res = l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_aliasExtension = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_aliasExtension);
lean_dec_ref(res);
res = l___private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_ResolveName_backward_privateInPublic = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_ResolveName_backward_privateInPublic);
lean_dec_ref(res);
res = l___private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_ResolveName_backward_privateInPublic_warn = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_ResolveName_backward_privateInPublic_warn);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_ResolveName(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Modifiers(uint8_t builtin);
lean_object* initialize_Lean_Exception(uint8_t builtin);
lean_object* initialize_Lean_Namespace(uint8_t builtin);
lean_object* initialize_Lean_Log(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_ResolveName(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Modifiers(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Exception(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Namespace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Log(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_ResolveName(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_ResolveName(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_ResolveName(builtin);
}
#ifdef __cplusplus
}
#endif
