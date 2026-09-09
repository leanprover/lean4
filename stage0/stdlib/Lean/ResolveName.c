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
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_MacroScopesView_review(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
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
lean_object* lean_mk_array(lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
lean_object* l_OptionT_instAlternative___redArg(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__9_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__9___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9_spec__14_spec__16___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9_spec__14___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__10___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__10(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9_spec__14(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__9_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9_spec__14_spec__16(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getRevAliases(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg___lam__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_ensureReservedNameAvailable___redArg___lam__0(lean_object* v_reservedName_32_, lean_object* v_toPure_33_, lean_object* v_inst_34_, lean_object* v_inst_35_, lean_object* v_declName_36_, lean_object* v_____do__lift_37_){
_start:
{
uint8_t v___x_38_; uint8_t v___x_39_; 
v___x_38_ = 1;
lean_inc(v_reservedName_32_);
v___x_39_ = l_Lean_Environment_contains(v_____do__lift_37_, v_reservedName_32_, v___x_38_);
if (v___x_39_ == 0)
{
lean_object* v___x_40_; lean_object* v___x_41_; 
lean_dec(v_declName_36_);
lean_dec_ref(v_inst_35_);
lean_dec_ref(v_inst_34_);
lean_dec(v_reservedName_32_);
v___x_40_ = lean_box(0);
v___x_41_ = lean_apply_2(v_toPure_33_, lean_box(0), v___x_40_);
return v___x_41_;
}
else
{
lean_object* v___x_42_; 
lean_dec(v_toPure_33_);
v___x_42_ = l_Lean_throwReservedNameNotAvailable___redArg(v_inst_34_, v_inst_35_, v_declName_36_, v_reservedName_32_);
return v___x_42_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureReservedNameAvailable___redArg(lean_object* v_inst_43_, lean_object* v_inst_44_, lean_object* v_inst_45_, lean_object* v_declName_46_, lean_object* v_suffix_47_){
_start:
{
lean_object* v_toApplicative_48_; lean_object* v_toBind_49_; lean_object* v_getEnv_50_; lean_object* v_toPure_51_; lean_object* v_reservedName_52_; lean_object* v___f_53_; lean_object* v___x_54_; 
v_toApplicative_48_ = lean_ctor_get(v_inst_43_, 0);
v_toBind_49_ = lean_ctor_get(v_inst_43_, 1);
lean_inc(v_toBind_49_);
v_getEnv_50_ = lean_ctor_get(v_inst_44_, 0);
lean_inc(v_getEnv_50_);
lean_dec_ref(v_inst_44_);
v_toPure_51_ = lean_ctor_get(v_toApplicative_48_, 1);
lean_inc(v_toPure_51_);
lean_inc(v_declName_46_);
v_reservedName_52_ = l_Lean_Name_str___override(v_declName_46_, v_suffix_47_);
v___f_53_ = lean_alloc_closure((void*)(l_Lean_ensureReservedNameAvailable___redArg___lam__0), 6, 5);
lean_closure_set(v___f_53_, 0, v_reservedName_52_);
lean_closure_set(v___f_53_, 1, v_toPure_51_);
lean_closure_set(v___f_53_, 2, v_inst_43_);
lean_closure_set(v___f_53_, 3, v_inst_45_);
lean_closure_set(v___f_53_, 4, v_declName_46_);
v___x_54_ = lean_apply_4(v_toBind_49_, lean_box(0), lean_box(0), v_getEnv_50_, v___f_53_);
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
lean_object* v___x_153__overap_108_; lean_object* v___x_109_; uint8_t v___x_110_; 
v___x_153__overap_108_ = lean_array_uget_borrowed(v_as_104_, v_i_105_);
lean_inc(v___x_153__overap_108_);
lean_inc(v_name_103_);
lean_inc_ref(v_env_102_);
v___x_109_ = lean_apply_2(v___x_153__overap_108_, v_env_102_, v_name_103_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__9_spec__11___redArg(lean_object* v_x_143_, lean_object* v_x_144_, lean_object* v_x_145_, lean_object* v_x_146_){
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__9___redArg(lean_object* v_n_173_, lean_object* v_k_174_, lean_object* v_v_175_){
_start:
{
lean_object* v___x_176_; lean_object* v___x_177_; 
v___x_176_ = lean_unsigned_to_nat(0u);
v___x_177_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__9_spec__11___redArg(v_n_173_, v___x_176_, v_k_174_, v_v_175_);
return v___x_177_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_178_; 
v___x_178_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg(lean_object* v_x_179_, size_t v_x_180_, size_t v_x_181_, lean_object* v_x_182_, lean_object* v_x_183_){
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
v___x_222_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg(v_node_214_, v___x_219_, v___x_221_, v_x_182_, v_x_183_);
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
lean_object* v_ks_230_; lean_object* v_vs_231_; lean_object* v___x_233_; uint8_t v_isShared_234_; uint8_t v_isSharedCheck_249_; 
v_ks_230_ = lean_ctor_get(v_x_179_, 0);
v_vs_231_ = lean_ctor_get(v_x_179_, 1);
v_isSharedCheck_249_ = !lean_is_exclusive(v_x_179_);
if (v_isSharedCheck_249_ == 0)
{
v___x_233_ = v_x_179_;
v_isShared_234_ = v_isSharedCheck_249_;
goto v_resetjp_232_;
}
else
{
lean_inc(v_vs_231_);
lean_inc(v_ks_230_);
lean_dec(v_x_179_);
v___x_233_ = lean_box(0);
v_isShared_234_ = v_isSharedCheck_249_;
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
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v_ks_230_);
lean_ctor_set(v_reuseFailAlloc_248_, 1, v_vs_231_);
v___x_236_ = v_reuseFailAlloc_248_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
lean_object* v_newNode_237_; size_t v___x_238_; uint8_t v___x_239_; 
v_newNode_237_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__9___redArg(v___x_236_, v_x_182_, v_x_183_);
v___x_238_ = ((size_t)7ULL);
v___x_239_ = lean_usize_dec_le(v___x_238_, v_x_181_);
if (v___x_239_ == 0)
{
lean_object* v___x_240_; lean_object* v___x_241_; uint8_t v___x_242_; 
v___x_240_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_237_);
v___x_241_ = lean_unsigned_to_nat(4u);
v___x_242_ = lean_nat_dec_lt(v___x_240_, v___x_241_);
lean_dec(v___x_240_);
if (v___x_242_ == 0)
{
lean_object* v_ks_243_; lean_object* v_vs_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; 
v_ks_243_ = lean_ctor_get(v_newNode_237_, 0);
lean_inc_ref(v_ks_243_);
v_vs_244_ = lean_ctor_get(v_newNode_237_, 1);
lean_inc_ref(v_vs_244_);
lean_dec_ref(v_newNode_237_);
v___x_245_ = lean_unsigned_to_nat(0u);
v___x_246_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg___closed__0);
v___x_247_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg(v_x_181_, v_ks_243_, v_vs_244_, v___x_245_, v___x_246_);
lean_dec_ref(v_vs_244_);
lean_dec_ref(v_ks_243_);
return v___x_247_;
}
else
{
return v_newNode_237_;
}
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
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg(size_t v_depth_250_, lean_object* v_keys_251_, lean_object* v_vals_252_, lean_object* v_i_253_, lean_object* v_entries_254_){
_start:
{
lean_object* v___x_255_; uint8_t v___x_256_; 
v___x_255_ = lean_array_get_size(v_keys_251_);
v___x_256_ = lean_nat_dec_lt(v_i_253_, v___x_255_);
if (v___x_256_ == 0)
{
lean_dec(v_i_253_);
return v_entries_254_;
}
else
{
lean_object* v_k_257_; lean_object* v_v_258_; uint64_t v___y_260_; 
v_k_257_ = lean_array_fget_borrowed(v_keys_251_, v_i_253_);
v_v_258_ = lean_array_fget_borrowed(v_vals_252_, v_i_253_);
if (lean_obj_tag(v_k_257_) == 0)
{
uint64_t v___x_271_; 
v___x_271_ = 1723ULL;
v___y_260_ = v___x_271_;
goto v___jp_259_;
}
else
{
uint64_t v_hash_272_; 
v_hash_272_ = lean_ctor_get_uint64(v_k_257_, sizeof(void*)*2);
v___y_260_ = v_hash_272_;
goto v___jp_259_;
}
v___jp_259_:
{
size_t v_h_261_; size_t v___x_262_; lean_object* v___x_263_; size_t v___x_264_; size_t v___x_265_; size_t v___x_266_; size_t v_h_267_; lean_object* v___x_268_; lean_object* v___x_269_; 
v_h_261_ = lean_uint64_to_usize(v___y_260_);
v___x_262_ = ((size_t)5ULL);
v___x_263_ = lean_unsigned_to_nat(1u);
v___x_264_ = ((size_t)1ULL);
v___x_265_ = lean_usize_sub(v_depth_250_, v___x_264_);
v___x_266_ = lean_usize_mul(v___x_262_, v___x_265_);
v_h_267_ = lean_usize_shift_right(v_h_261_, v___x_266_);
v___x_268_ = lean_nat_add(v_i_253_, v___x_263_);
lean_dec(v_i_253_);
lean_inc(v_v_258_);
lean_inc(v_k_257_);
v___x_269_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg(v_entries_254_, v_h_267_, v_depth_250_, v_k_257_, v_v_258_);
v_i_253_ = v___x_268_;
v_entries_254_ = v___x_269_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg___boxed(lean_object* v_depth_273_, lean_object* v_keys_274_, lean_object* v_vals_275_, lean_object* v_i_276_, lean_object* v_entries_277_){
_start:
{
size_t v_depth_boxed_278_; lean_object* v_res_279_; 
v_depth_boxed_278_ = lean_unbox_usize(v_depth_273_);
lean_dec(v_depth_273_);
v_res_279_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg(v_depth_boxed_278_, v_keys_274_, v_vals_275_, v_i_276_, v_entries_277_);
lean_dec_ref(v_vals_275_);
lean_dec_ref(v_keys_274_);
return v_res_279_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg___boxed(lean_object* v_x_280_, lean_object* v_x_281_, lean_object* v_x_282_, lean_object* v_x_283_, lean_object* v_x_284_){
_start:
{
size_t v_x_1070__boxed_285_; size_t v_x_1071__boxed_286_; lean_object* v_res_287_; 
v_x_1070__boxed_285_ = lean_unbox_usize(v_x_281_);
lean_dec(v_x_281_);
v_x_1071__boxed_286_ = lean_unbox_usize(v_x_282_);
lean_dec(v_x_282_);
v_res_287_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg(v_x_280_, v_x_1070__boxed_285_, v_x_1071__boxed_286_, v_x_283_, v_x_284_);
return v_res_287_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3___redArg(lean_object* v_x_288_, lean_object* v_x_289_, lean_object* v_x_290_){
_start:
{
uint64_t v___y_292_; 
if (lean_obj_tag(v_x_289_) == 0)
{
uint64_t v___x_296_; 
v___x_296_ = 1723ULL;
v___y_292_ = v___x_296_;
goto v___jp_291_;
}
else
{
uint64_t v_hash_297_; 
v_hash_297_ = lean_ctor_get_uint64(v_x_289_, sizeof(void*)*2);
v___y_292_ = v_hash_297_;
goto v___jp_291_;
}
v___jp_291_:
{
size_t v___x_293_; size_t v___x_294_; lean_object* v___x_295_; 
v___x_293_ = lean_uint64_to_usize(v___y_292_);
v___x_294_ = ((size_t)1ULL);
v___x_295_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg(v_x_288_, v___x_293_, v___x_294_, v_x_289_, v_x_290_);
return v___x_295_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9_spec__14_spec__16___redArg(lean_object* v_x_298_, lean_object* v_x_299_){
_start:
{
if (lean_obj_tag(v_x_299_) == 0)
{
return v_x_298_;
}
else
{
lean_object* v_key_300_; lean_object* v_value_301_; lean_object* v_tail_302_; lean_object* v___x_304_; uint8_t v_isShared_305_; uint8_t v_isSharedCheck_328_; 
v_key_300_ = lean_ctor_get(v_x_299_, 0);
v_value_301_ = lean_ctor_get(v_x_299_, 1);
v_tail_302_ = lean_ctor_get(v_x_299_, 2);
v_isSharedCheck_328_ = !lean_is_exclusive(v_x_299_);
if (v_isSharedCheck_328_ == 0)
{
v___x_304_ = v_x_299_;
v_isShared_305_ = v_isSharedCheck_328_;
goto v_resetjp_303_;
}
else
{
lean_inc(v_tail_302_);
lean_inc(v_value_301_);
lean_inc(v_key_300_);
lean_dec(v_x_299_);
v___x_304_ = lean_box(0);
v_isShared_305_ = v_isSharedCheck_328_;
goto v_resetjp_303_;
}
v_resetjp_303_:
{
lean_object* v___x_306_; uint64_t v___y_308_; 
v___x_306_ = lean_array_get_size(v_x_298_);
if (lean_obj_tag(v_key_300_) == 0)
{
uint64_t v___x_326_; 
v___x_326_ = 1723ULL;
v___y_308_ = v___x_326_;
goto v___jp_307_;
}
else
{
uint64_t v_hash_327_; 
v_hash_327_ = lean_ctor_get_uint64(v_key_300_, sizeof(void*)*2);
v___y_308_ = v_hash_327_;
goto v___jp_307_;
}
v___jp_307_:
{
uint64_t v___x_309_; uint64_t v___x_310_; uint64_t v_fold_311_; uint64_t v___x_312_; uint64_t v___x_313_; uint64_t v___x_314_; size_t v___x_315_; size_t v___x_316_; size_t v___x_317_; size_t v___x_318_; size_t v___x_319_; lean_object* v___x_320_; lean_object* v___x_322_; 
v___x_309_ = 32ULL;
v___x_310_ = lean_uint64_shift_right(v___y_308_, v___x_309_);
v_fold_311_ = lean_uint64_xor(v___y_308_, v___x_310_);
v___x_312_ = 16ULL;
v___x_313_ = lean_uint64_shift_right(v_fold_311_, v___x_312_);
v___x_314_ = lean_uint64_xor(v_fold_311_, v___x_313_);
v___x_315_ = lean_uint64_to_usize(v___x_314_);
v___x_316_ = lean_usize_of_nat(v___x_306_);
v___x_317_ = ((size_t)1ULL);
v___x_318_ = lean_usize_sub(v___x_316_, v___x_317_);
v___x_319_ = lean_usize_land(v___x_315_, v___x_318_);
v___x_320_ = lean_array_uget_borrowed(v_x_298_, v___x_319_);
lean_inc(v___x_320_);
if (v_isShared_305_ == 0)
{
lean_ctor_set(v___x_304_, 2, v___x_320_);
v___x_322_ = v___x_304_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v_key_300_);
lean_ctor_set(v_reuseFailAlloc_325_, 1, v_value_301_);
lean_ctor_set(v_reuseFailAlloc_325_, 2, v___x_320_);
v___x_322_ = v_reuseFailAlloc_325_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
lean_object* v___x_323_; 
v___x_323_ = lean_array_uset(v_x_298_, v___x_319_, v___x_322_);
v_x_298_ = v___x_323_;
v_x_299_ = v_tail_302_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9_spec__14___redArg(lean_object* v_i_329_, lean_object* v_source_330_, lean_object* v_target_331_){
_start:
{
lean_object* v___x_332_; uint8_t v___x_333_; 
v___x_332_ = lean_array_get_size(v_source_330_);
v___x_333_ = lean_nat_dec_lt(v_i_329_, v___x_332_);
if (v___x_333_ == 0)
{
lean_dec_ref(v_source_330_);
lean_dec(v_i_329_);
return v_target_331_;
}
else
{
lean_object* v_es_334_; lean_object* v___x_335_; lean_object* v_source_336_; lean_object* v_target_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
v_es_334_ = lean_array_fget(v_source_330_, v_i_329_);
v___x_335_ = lean_box(0);
v_source_336_ = lean_array_fset(v_source_330_, v_i_329_, v___x_335_);
v_target_337_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9_spec__14_spec__16___redArg(v_target_331_, v_es_334_);
v___x_338_ = lean_unsigned_to_nat(1u);
v___x_339_ = lean_nat_add(v_i_329_, v___x_338_);
lean_dec(v_i_329_);
v_i_329_ = v___x_339_;
v_source_330_ = v_source_336_;
v_target_331_ = v_target_337_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9___redArg(lean_object* v_data_341_){
_start:
{
lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v_nbuckets_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_342_ = lean_array_get_size(v_data_341_);
v___x_343_ = lean_unsigned_to_nat(2u);
v_nbuckets_344_ = lean_nat_mul(v___x_342_, v___x_343_);
v___x_345_ = lean_unsigned_to_nat(0u);
v___x_346_ = lean_box(0);
v___x_347_ = lean_mk_array(v_nbuckets_344_, v___x_346_);
v___x_348_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9_spec__14___redArg(v___x_345_, v_data_341_, v___x_347_);
return v___x_348_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8___redArg(lean_object* v_a_349_, lean_object* v_x_350_){
_start:
{
if (lean_obj_tag(v_x_350_) == 0)
{
uint8_t v___x_351_; 
v___x_351_ = 0;
return v___x_351_;
}
else
{
lean_object* v_key_352_; lean_object* v_tail_353_; uint8_t v___x_354_; 
v_key_352_ = lean_ctor_get(v_x_350_, 0);
v_tail_353_ = lean_ctor_get(v_x_350_, 2);
v___x_354_ = lean_name_eq(v_key_352_, v_a_349_);
if (v___x_354_ == 0)
{
v_x_350_ = v_tail_353_;
goto _start;
}
else
{
return v___x_354_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8___redArg___boxed(lean_object* v_a_356_, lean_object* v_x_357_){
_start:
{
uint8_t v_res_358_; lean_object* v_r_359_; 
v_res_358_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8___redArg(v_a_356_, v_x_357_);
lean_dec(v_x_357_);
lean_dec(v_a_356_);
v_r_359_ = lean_box(v_res_358_);
return v_r_359_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__10___redArg(lean_object* v_a_360_, lean_object* v_b_361_, lean_object* v_x_362_){
_start:
{
if (lean_obj_tag(v_x_362_) == 0)
{
lean_dec(v_b_361_);
lean_dec(v_a_360_);
return v_x_362_;
}
else
{
lean_object* v_key_363_; lean_object* v_value_364_; lean_object* v_tail_365_; lean_object* v___x_367_; uint8_t v_isShared_368_; uint8_t v_isSharedCheck_377_; 
v_key_363_ = lean_ctor_get(v_x_362_, 0);
v_value_364_ = lean_ctor_get(v_x_362_, 1);
v_tail_365_ = lean_ctor_get(v_x_362_, 2);
v_isSharedCheck_377_ = !lean_is_exclusive(v_x_362_);
if (v_isSharedCheck_377_ == 0)
{
v___x_367_ = v_x_362_;
v_isShared_368_ = v_isSharedCheck_377_;
goto v_resetjp_366_;
}
else
{
lean_inc(v_tail_365_);
lean_inc(v_value_364_);
lean_inc(v_key_363_);
lean_dec(v_x_362_);
v___x_367_ = lean_box(0);
v_isShared_368_ = v_isSharedCheck_377_;
goto v_resetjp_366_;
}
v_resetjp_366_:
{
uint8_t v___x_369_; 
v___x_369_ = lean_name_eq(v_key_363_, v_a_360_);
if (v___x_369_ == 0)
{
lean_object* v___x_370_; lean_object* v___x_372_; 
v___x_370_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__10___redArg(v_a_360_, v_b_361_, v_tail_365_);
if (v_isShared_368_ == 0)
{
lean_ctor_set(v___x_367_, 2, v___x_370_);
v___x_372_ = v___x_367_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v_key_363_);
lean_ctor_set(v_reuseFailAlloc_373_, 1, v_value_364_);
lean_ctor_set(v_reuseFailAlloc_373_, 2, v___x_370_);
v___x_372_ = v_reuseFailAlloc_373_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
return v___x_372_;
}
}
else
{
lean_object* v___x_375_; 
lean_dec(v_value_364_);
lean_dec(v_key_363_);
if (v_isShared_368_ == 0)
{
lean_ctor_set(v___x_367_, 1, v_b_361_);
lean_ctor_set(v___x_367_, 0, v_a_360_);
v___x_375_ = v___x_367_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v_a_360_);
lean_ctor_set(v_reuseFailAlloc_376_, 1, v_b_361_);
lean_ctor_set(v_reuseFailAlloc_376_, 2, v_tail_365_);
v___x_375_ = v_reuseFailAlloc_376_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
return v___x_375_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4___redArg(lean_object* v_m_378_, lean_object* v_a_379_, lean_object* v_b_380_){
_start:
{
lean_object* v_size_381_; lean_object* v_buckets_382_; lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_428_; 
v_size_381_ = lean_ctor_get(v_m_378_, 0);
v_buckets_382_ = lean_ctor_get(v_m_378_, 1);
v_isSharedCheck_428_ = !lean_is_exclusive(v_m_378_);
if (v_isSharedCheck_428_ == 0)
{
v___x_384_ = v_m_378_;
v_isShared_385_ = v_isSharedCheck_428_;
goto v_resetjp_383_;
}
else
{
lean_inc(v_buckets_382_);
lean_inc(v_size_381_);
lean_dec(v_m_378_);
v___x_384_ = lean_box(0);
v_isShared_385_ = v_isSharedCheck_428_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
lean_object* v___x_386_; uint64_t v___y_388_; 
v___x_386_ = lean_array_get_size(v_buckets_382_);
if (lean_obj_tag(v_a_379_) == 0)
{
uint64_t v___x_426_; 
v___x_426_ = 1723ULL;
v___y_388_ = v___x_426_;
goto v___jp_387_;
}
else
{
uint64_t v_hash_427_; 
v_hash_427_ = lean_ctor_get_uint64(v_a_379_, sizeof(void*)*2);
v___y_388_ = v_hash_427_;
goto v___jp_387_;
}
v___jp_387_:
{
uint64_t v___x_389_; uint64_t v___x_390_; uint64_t v_fold_391_; uint64_t v___x_392_; uint64_t v___x_393_; uint64_t v___x_394_; size_t v___x_395_; size_t v___x_396_; size_t v___x_397_; size_t v___x_398_; size_t v___x_399_; lean_object* v_bkt_400_; uint8_t v___x_401_; 
v___x_389_ = 32ULL;
v___x_390_ = lean_uint64_shift_right(v___y_388_, v___x_389_);
v_fold_391_ = lean_uint64_xor(v___y_388_, v___x_390_);
v___x_392_ = 16ULL;
v___x_393_ = lean_uint64_shift_right(v_fold_391_, v___x_392_);
v___x_394_ = lean_uint64_xor(v_fold_391_, v___x_393_);
v___x_395_ = lean_uint64_to_usize(v___x_394_);
v___x_396_ = lean_usize_of_nat(v___x_386_);
v___x_397_ = ((size_t)1ULL);
v___x_398_ = lean_usize_sub(v___x_396_, v___x_397_);
v___x_399_ = lean_usize_land(v___x_395_, v___x_398_);
v_bkt_400_ = lean_array_uget_borrowed(v_buckets_382_, v___x_399_);
v___x_401_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8___redArg(v_a_379_, v_bkt_400_);
if (v___x_401_ == 0)
{
lean_object* v___x_402_; lean_object* v_size_x27_403_; lean_object* v___x_404_; lean_object* v_buckets_x27_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; uint8_t v___x_411_; 
v___x_402_ = lean_unsigned_to_nat(1u);
v_size_x27_403_ = lean_nat_add(v_size_381_, v___x_402_);
lean_dec(v_size_381_);
lean_inc(v_bkt_400_);
v___x_404_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_404_, 0, v_a_379_);
lean_ctor_set(v___x_404_, 1, v_b_380_);
lean_ctor_set(v___x_404_, 2, v_bkt_400_);
v_buckets_x27_405_ = lean_array_uset(v_buckets_382_, v___x_399_, v___x_404_);
v___x_406_ = lean_unsigned_to_nat(4u);
v___x_407_ = lean_nat_mul(v_size_x27_403_, v___x_406_);
v___x_408_ = lean_unsigned_to_nat(3u);
v___x_409_ = lean_nat_div(v___x_407_, v___x_408_);
lean_dec(v___x_407_);
v___x_410_ = lean_array_get_size(v_buckets_x27_405_);
v___x_411_ = lean_nat_dec_le(v___x_409_, v___x_410_);
lean_dec(v___x_409_);
if (v___x_411_ == 0)
{
lean_object* v_val_412_; lean_object* v___x_414_; 
v_val_412_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9___redArg(v_buckets_x27_405_);
if (v_isShared_385_ == 0)
{
lean_ctor_set(v___x_384_, 1, v_val_412_);
lean_ctor_set(v___x_384_, 0, v_size_x27_403_);
v___x_414_ = v___x_384_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_415_; 
v_reuseFailAlloc_415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_415_, 0, v_size_x27_403_);
lean_ctor_set(v_reuseFailAlloc_415_, 1, v_val_412_);
v___x_414_ = v_reuseFailAlloc_415_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
return v___x_414_;
}
}
else
{
lean_object* v___x_417_; 
if (v_isShared_385_ == 0)
{
lean_ctor_set(v___x_384_, 1, v_buckets_x27_405_);
lean_ctor_set(v___x_384_, 0, v_size_x27_403_);
v___x_417_ = v___x_384_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v_size_x27_403_);
lean_ctor_set(v_reuseFailAlloc_418_, 1, v_buckets_x27_405_);
v___x_417_ = v_reuseFailAlloc_418_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
return v___x_417_;
}
}
}
else
{
lean_object* v___x_419_; lean_object* v_buckets_x27_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_424_; 
lean_inc(v_bkt_400_);
v___x_419_ = lean_box(0);
v_buckets_x27_420_ = lean_array_uset(v_buckets_382_, v___x_399_, v___x_419_);
v___x_421_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__10___redArg(v_a_379_, v_b_380_, v_bkt_400_);
v___x_422_ = lean_array_uset(v_buckets_x27_420_, v___x_399_, v___x_421_);
if (v_isShared_385_ == 0)
{
lean_ctor_set(v___x_384_, 1, v___x_422_);
v___x_424_ = v___x_384_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v_size_381_);
lean_ctor_set(v_reuseFailAlloc_425_, 1, v___x_422_);
v___x_424_ = v_reuseFailAlloc_425_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
return v___x_424_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1___redArg(lean_object* v_x_429_, lean_object* v_x_430_, lean_object* v_x_431_){
_start:
{
uint8_t v_stage_u2081_432_; 
v_stage_u2081_432_ = lean_ctor_get_uint8(v_x_429_, sizeof(void*)*2);
if (v_stage_u2081_432_ == 0)
{
lean_object* v_map_u2081_433_; lean_object* v_map_u2082_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_442_; 
v_map_u2081_433_ = lean_ctor_get(v_x_429_, 0);
v_map_u2082_434_ = lean_ctor_get(v_x_429_, 1);
v_isSharedCheck_442_ = !lean_is_exclusive(v_x_429_);
if (v_isSharedCheck_442_ == 0)
{
v___x_436_ = v_x_429_;
v_isShared_437_ = v_isSharedCheck_442_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_map_u2082_434_);
lean_inc(v_map_u2081_433_);
lean_dec(v_x_429_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_442_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
lean_object* v___x_438_; lean_object* v___x_440_; 
v___x_438_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3___redArg(v_map_u2082_434_, v_x_430_, v_x_431_);
if (v_isShared_437_ == 0)
{
lean_ctor_set(v___x_436_, 1, v___x_438_);
v___x_440_ = v___x_436_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_441_; 
v_reuseFailAlloc_441_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_441_, 0, v_map_u2081_433_);
lean_ctor_set(v_reuseFailAlloc_441_, 1, v___x_438_);
lean_ctor_set_uint8(v_reuseFailAlloc_441_, sizeof(void*)*2, v_stage_u2081_432_);
v___x_440_ = v_reuseFailAlloc_441_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
return v___x_440_;
}
}
}
else
{
lean_object* v_map_u2081_443_; lean_object* v_map_u2082_444_; lean_object* v___x_446_; uint8_t v_isShared_447_; uint8_t v_isSharedCheck_452_; 
v_map_u2081_443_ = lean_ctor_get(v_x_429_, 0);
v_map_u2082_444_ = lean_ctor_get(v_x_429_, 1);
v_isSharedCheck_452_ = !lean_is_exclusive(v_x_429_);
if (v_isSharedCheck_452_ == 0)
{
v___x_446_ = v_x_429_;
v_isShared_447_ = v_isSharedCheck_452_;
goto v_resetjp_445_;
}
else
{
lean_inc(v_map_u2082_444_);
lean_inc(v_map_u2081_443_);
lean_dec(v_x_429_);
v___x_446_ = lean_box(0);
v_isShared_447_ = v_isSharedCheck_452_;
goto v_resetjp_445_;
}
v_resetjp_445_:
{
lean_object* v___x_448_; lean_object* v___x_450_; 
v___x_448_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4___redArg(v_map_u2081_443_, v_x_430_, v_x_431_);
if (v_isShared_447_ == 0)
{
lean_ctor_set(v___x_446_, 0, v___x_448_);
v___x_450_ = v___x_446_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_451_; 
v_reuseFailAlloc_451_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_451_, 0, v___x_448_);
lean_ctor_set(v_reuseFailAlloc_451_, 1, v_map_u2082_444_);
lean_ctor_set_uint8(v_reuseFailAlloc_451_, sizeof(void*)*2, v_stage_u2081_432_);
v___x_450_ = v_reuseFailAlloc_451_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
return v___x_450_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3___redArg(lean_object* v_a_453_, lean_object* v_x_454_){
_start:
{
if (lean_obj_tag(v_x_454_) == 0)
{
lean_object* v___x_455_; 
v___x_455_ = lean_box(0);
return v___x_455_;
}
else
{
lean_object* v_key_456_; lean_object* v_value_457_; lean_object* v_tail_458_; uint8_t v___x_459_; 
v_key_456_ = lean_ctor_get(v_x_454_, 0);
v_value_457_ = lean_ctor_get(v_x_454_, 1);
v_tail_458_ = lean_ctor_get(v_x_454_, 2);
v___x_459_ = lean_name_eq(v_key_456_, v_a_453_);
if (v___x_459_ == 0)
{
v_x_454_ = v_tail_458_;
goto _start;
}
else
{
lean_object* v___x_461_; 
lean_inc(v_value_457_);
v___x_461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_461_, 0, v_value_457_);
return v___x_461_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_a_462_, lean_object* v_x_463_){
_start:
{
lean_object* v_res_464_; 
v_res_464_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3___redArg(v_a_462_, v_x_463_);
lean_dec(v_x_463_);
lean_dec(v_a_462_);
return v_res_464_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1___redArg(lean_object* v_m_465_, lean_object* v_a_466_){
_start:
{
lean_object* v_buckets_467_; lean_object* v___x_468_; uint64_t v___y_470_; 
v_buckets_467_ = lean_ctor_get(v_m_465_, 1);
v___x_468_ = lean_array_get_size(v_buckets_467_);
if (lean_obj_tag(v_a_466_) == 0)
{
uint64_t v___x_484_; 
v___x_484_ = 1723ULL;
v___y_470_ = v___x_484_;
goto v___jp_469_;
}
else
{
uint64_t v_hash_485_; 
v_hash_485_ = lean_ctor_get_uint64(v_a_466_, sizeof(void*)*2);
v___y_470_ = v_hash_485_;
goto v___jp_469_;
}
v___jp_469_:
{
uint64_t v___x_471_; uint64_t v___x_472_; uint64_t v_fold_473_; uint64_t v___x_474_; uint64_t v___x_475_; uint64_t v___x_476_; size_t v___x_477_; size_t v___x_478_; size_t v___x_479_; size_t v___x_480_; size_t v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_471_ = 32ULL;
v___x_472_ = lean_uint64_shift_right(v___y_470_, v___x_471_);
v_fold_473_ = lean_uint64_xor(v___y_470_, v___x_472_);
v___x_474_ = 16ULL;
v___x_475_ = lean_uint64_shift_right(v_fold_473_, v___x_474_);
v___x_476_ = lean_uint64_xor(v_fold_473_, v___x_475_);
v___x_477_ = lean_uint64_to_usize(v___x_476_);
v___x_478_ = lean_usize_of_nat(v___x_468_);
v___x_479_ = ((size_t)1ULL);
v___x_480_ = lean_usize_sub(v___x_478_, v___x_479_);
v___x_481_ = lean_usize_land(v___x_477_, v___x_480_);
v___x_482_ = lean_array_uget_borrowed(v_buckets_467_, v___x_481_);
v___x_483_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3___redArg(v_a_466_, v___x_482_);
return v___x_483_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1___redArg___boxed(lean_object* v_m_486_, lean_object* v_a_487_){
_start:
{
lean_object* v_res_488_; 
v_res_488_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1___redArg(v_m_486_, v_a_487_);
lean_dec(v_a_487_);
lean_dec_ref(v_m_486_);
return v_res_488_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_keys_489_, lean_object* v_vals_490_, lean_object* v_i_491_, lean_object* v_k_492_){
_start:
{
lean_object* v___x_493_; uint8_t v___x_494_; 
v___x_493_ = lean_array_get_size(v_keys_489_);
v___x_494_ = lean_nat_dec_lt(v_i_491_, v___x_493_);
if (v___x_494_ == 0)
{
lean_object* v___x_495_; 
lean_dec(v_i_491_);
v___x_495_ = lean_box(0);
return v___x_495_;
}
else
{
lean_object* v_k_x27_496_; uint8_t v___x_497_; 
v_k_x27_496_ = lean_array_fget_borrowed(v_keys_489_, v_i_491_);
v___x_497_ = lean_name_eq(v_k_492_, v_k_x27_496_);
if (v___x_497_ == 0)
{
lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_498_ = lean_unsigned_to_nat(1u);
v___x_499_ = lean_nat_add(v_i_491_, v___x_498_);
lean_dec(v_i_491_);
v_i_491_ = v___x_499_;
goto _start;
}
else
{
lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_501_ = lean_array_fget_borrowed(v_vals_490_, v_i_491_);
lean_dec(v_i_491_);
lean_inc(v___x_501_);
v___x_502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_502_, 0, v___x_501_);
return v___x_502_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_keys_503_, lean_object* v_vals_504_, lean_object* v_i_505_, lean_object* v_k_506_){
_start:
{
lean_object* v_res_507_; 
v_res_507_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4___redArg(v_keys_503_, v_vals_504_, v_i_505_, v_k_506_);
lean_dec(v_k_506_);
lean_dec_ref(v_vals_504_);
lean_dec_ref(v_keys_503_);
return v_res_507_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1___redArg(lean_object* v_x_508_, size_t v_x_509_, lean_object* v_x_510_){
_start:
{
if (lean_obj_tag(v_x_508_) == 0)
{
lean_object* v_es_511_; lean_object* v___x_512_; size_t v___x_513_; size_t v___x_514_; lean_object* v_j_515_; lean_object* v___x_516_; 
v_es_511_ = lean_ctor_get(v_x_508_, 0);
v___x_512_ = lean_box(2);
v___x_513_ = ((size_t)31ULL);
v___x_514_ = lean_usize_land(v_x_509_, v___x_513_);
v_j_515_ = lean_usize_to_nat(v___x_514_);
v___x_516_ = lean_array_get_borrowed(v___x_512_, v_es_511_, v_j_515_);
lean_dec(v_j_515_);
switch(lean_obj_tag(v___x_516_))
{
case 0:
{
lean_object* v_key_517_; lean_object* v_val_518_; uint8_t v___x_519_; 
v_key_517_ = lean_ctor_get(v___x_516_, 0);
v_val_518_ = lean_ctor_get(v___x_516_, 1);
v___x_519_ = lean_name_eq(v_x_510_, v_key_517_);
if (v___x_519_ == 0)
{
lean_object* v___x_520_; 
v___x_520_ = lean_box(0);
return v___x_520_;
}
else
{
lean_object* v___x_521_; 
lean_inc(v_val_518_);
v___x_521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_521_, 0, v_val_518_);
return v___x_521_;
}
}
case 1:
{
lean_object* v_node_522_; size_t v___x_523_; size_t v___x_524_; 
v_node_522_ = lean_ctor_get(v___x_516_, 0);
v___x_523_ = ((size_t)5ULL);
v___x_524_ = lean_usize_shift_right(v_x_509_, v___x_523_);
v_x_508_ = v_node_522_;
v_x_509_ = v___x_524_;
goto _start;
}
default: 
{
lean_object* v___x_526_; 
v___x_526_ = lean_box(0);
return v___x_526_;
}
}
}
else
{
lean_object* v_ks_527_; lean_object* v_vs_528_; lean_object* v___x_529_; lean_object* v___x_530_; 
v_ks_527_ = lean_ctor_get(v_x_508_, 0);
v_vs_528_ = lean_ctor_get(v_x_508_, 1);
v___x_529_ = lean_unsigned_to_nat(0u);
v___x_530_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4___redArg(v_ks_527_, v_vs_528_, v___x_529_, v_x_510_);
return v___x_530_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_531_, lean_object* v_x_532_, lean_object* v_x_533_){
_start:
{
size_t v_x_1572__boxed_534_; lean_object* v_res_535_; 
v_x_1572__boxed_534_ = lean_unbox_usize(v_x_532_);
lean_dec(v_x_532_);
v_res_535_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1___redArg(v_x_531_, v_x_1572__boxed_534_, v_x_533_);
lean_dec(v_x_533_);
lean_dec_ref(v_x_531_);
return v_res_535_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0___redArg(lean_object* v_x_536_, lean_object* v_x_537_){
_start:
{
uint64_t v___y_539_; 
if (lean_obj_tag(v_x_537_) == 0)
{
uint64_t v___x_542_; 
v___x_542_ = 1723ULL;
v___y_539_ = v___x_542_;
goto v___jp_538_;
}
else
{
uint64_t v_hash_543_; 
v_hash_543_ = lean_ctor_get_uint64(v_x_537_, sizeof(void*)*2);
v___y_539_ = v_hash_543_;
goto v___jp_538_;
}
v___jp_538_:
{
size_t v___x_540_; lean_object* v___x_541_; 
v___x_540_ = lean_uint64_to_usize(v___y_539_);
v___x_541_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1___redArg(v_x_536_, v___x_540_, v_x_537_);
return v___x_541_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0___redArg___boxed(lean_object* v_x_544_, lean_object* v_x_545_){
_start:
{
lean_object* v_res_546_; 
v_res_546_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0___redArg(v_x_544_, v_x_545_);
lean_dec(v_x_545_);
lean_dec_ref(v_x_544_);
return v_res_546_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0___redArg(lean_object* v_x_547_, lean_object* v_x_548_){
_start:
{
uint8_t v_stage_u2081_549_; 
v_stage_u2081_549_ = lean_ctor_get_uint8(v_x_547_, sizeof(void*)*2);
if (v_stage_u2081_549_ == 0)
{
lean_object* v_map_u2081_550_; lean_object* v_map_u2082_551_; lean_object* v___x_552_; 
v_map_u2081_550_ = lean_ctor_get(v_x_547_, 0);
v_map_u2082_551_ = lean_ctor_get(v_x_547_, 1);
v___x_552_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0___redArg(v_map_u2082_551_, v_x_548_);
if (lean_obj_tag(v___x_552_) == 0)
{
lean_object* v___x_553_; 
v___x_553_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1___redArg(v_map_u2081_550_, v_x_548_);
return v___x_553_;
}
else
{
return v___x_552_;
}
}
else
{
lean_object* v_map_u2081_554_; lean_object* v___x_555_; 
v_map_u2081_554_ = lean_ctor_get(v_x_547_, 0);
v___x_555_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1___redArg(v_map_u2081_554_, v_x_548_);
return v___x_555_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0___redArg___boxed(lean_object* v_x_556_, lean_object* v_x_557_){
_start:
{
lean_object* v_res_558_; 
v_res_558_ = l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0___redArg(v_x_556_, v_x_557_);
lean_dec(v_x_557_);
lean_dec_ref(v_x_556_);
return v_res_558_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_addAliasEntry_spec__2(lean_object* v_a_559_, lean_object* v_x_560_){
_start:
{
if (lean_obj_tag(v_x_560_) == 0)
{
uint8_t v___x_561_; 
v___x_561_ = 0;
return v___x_561_;
}
else
{
lean_object* v_head_562_; lean_object* v_tail_563_; uint8_t v___x_564_; 
v_head_562_ = lean_ctor_get(v_x_560_, 0);
v_tail_563_ = lean_ctor_get(v_x_560_, 1);
v___x_564_ = lean_name_eq(v_a_559_, v_head_562_);
if (v___x_564_ == 0)
{
v_x_560_ = v_tail_563_;
goto _start;
}
else
{
return v___x_564_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_addAliasEntry_spec__2___boxed(lean_object* v_a_566_, lean_object* v_x_567_){
_start:
{
uint8_t v_res_568_; lean_object* v_r_569_; 
v_res_568_ = l_List_elem___at___00Lean_addAliasEntry_spec__2(v_a_566_, v_x_567_);
lean_dec(v_x_567_);
lean_dec(v_a_566_);
v_r_569_ = lean_box(v_res_568_);
return v_r_569_;
}
}
LEAN_EXPORT lean_object* l_Lean_addAliasEntry(lean_object* v_s_570_, lean_object* v_e_571_){
_start:
{
lean_object* v_fst_572_; lean_object* v_snd_573_; lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_589_; 
v_fst_572_ = lean_ctor_get(v_e_571_, 0);
v_snd_573_ = lean_ctor_get(v_e_571_, 1);
v_isSharedCheck_589_ = !lean_is_exclusive(v_e_571_);
if (v_isSharedCheck_589_ == 0)
{
v___x_575_ = v_e_571_;
v_isShared_576_ = v_isSharedCheck_589_;
goto v_resetjp_574_;
}
else
{
lean_inc(v_snd_573_);
lean_inc(v_fst_572_);
lean_dec(v_e_571_);
v___x_575_ = lean_box(0);
v_isShared_576_ = v_isSharedCheck_589_;
goto v_resetjp_574_;
}
v_resetjp_574_:
{
lean_object* v___x_577_; 
v___x_577_ = l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0___redArg(v_s_570_, v_fst_572_);
if (lean_obj_tag(v___x_577_) == 0)
{
lean_object* v___x_578_; lean_object* v___x_580_; 
v___x_578_ = lean_box(0);
if (v_isShared_576_ == 0)
{
lean_ctor_set_tag(v___x_575_, 1);
lean_ctor_set(v___x_575_, 1, v___x_578_);
lean_ctor_set(v___x_575_, 0, v_snd_573_);
v___x_580_ = v___x_575_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v_snd_573_);
lean_ctor_set(v_reuseFailAlloc_582_, 1, v___x_578_);
v___x_580_ = v_reuseFailAlloc_582_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
lean_object* v___x_581_; 
v___x_581_ = l_Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1___redArg(v_s_570_, v_fst_572_, v___x_580_);
return v___x_581_;
}
}
else
{
lean_object* v_val_583_; uint8_t v___x_584_; 
v_val_583_ = lean_ctor_get(v___x_577_, 0);
lean_inc(v_val_583_);
lean_dec_ref_known(v___x_577_, 1);
v___x_584_ = l_List_elem___at___00Lean_addAliasEntry_spec__2(v_snd_573_, v_val_583_);
if (v___x_584_ == 0)
{
lean_object* v___x_586_; 
if (v_isShared_576_ == 0)
{
lean_ctor_set_tag(v___x_575_, 1);
lean_ctor_set(v___x_575_, 1, v_val_583_);
lean_ctor_set(v___x_575_, 0, v_snd_573_);
v___x_586_ = v___x_575_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v_snd_573_);
lean_ctor_set(v_reuseFailAlloc_588_, 1, v_val_583_);
v___x_586_ = v_reuseFailAlloc_588_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
lean_object* v___x_587_; 
v___x_587_ = l_Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1___redArg(v_s_570_, v_fst_572_, v___x_586_);
return v___x_587_;
}
}
else
{
lean_dec(v_val_583_);
lean_del_object(v___x_575_);
lean_dec(v_snd_573_);
lean_dec(v_fst_572_);
return v_s_570_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0(lean_object* v_00_u03b2_590_, lean_object* v_x_591_, lean_object* v_x_592_){
_start:
{
lean_object* v___x_593_; 
v___x_593_ = l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0___redArg(v_x_591_, v_x_592_);
return v___x_593_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0___boxed(lean_object* v_00_u03b2_594_, lean_object* v_x_595_, lean_object* v_x_596_){
_start:
{
lean_object* v_res_597_; 
v_res_597_ = l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0(v_00_u03b2_594_, v_x_595_, v_x_596_);
lean_dec(v_x_596_);
lean_dec_ref(v_x_595_);
return v_res_597_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1(lean_object* v_00_u03b2_598_, lean_object* v_x_599_, lean_object* v_x_600_, lean_object* v_x_601_){
_start:
{
lean_object* v___x_602_; 
v___x_602_ = l_Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1___redArg(v_x_599_, v_x_600_, v_x_601_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0(lean_object* v_00_u03b2_603_, lean_object* v_x_604_, lean_object* v_x_605_){
_start:
{
lean_object* v___x_606_; 
v___x_606_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0___redArg(v_x_604_, v_x_605_);
return v___x_606_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0___boxed(lean_object* v_00_u03b2_607_, lean_object* v_x_608_, lean_object* v_x_609_){
_start:
{
lean_object* v_res_610_; 
v_res_610_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0(v_00_u03b2_607_, v_x_608_, v_x_609_);
lean_dec(v_x_609_);
lean_dec_ref(v_x_608_);
return v_res_610_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1(lean_object* v_00_u03b2_611_, lean_object* v_m_612_, lean_object* v_a_613_){
_start:
{
lean_object* v___x_614_; 
v___x_614_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1___redArg(v_m_612_, v_a_613_);
return v___x_614_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1___boxed(lean_object* v_00_u03b2_615_, lean_object* v_m_616_, lean_object* v_a_617_){
_start:
{
lean_object* v_res_618_; 
v_res_618_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1(v_00_u03b2_615_, v_m_616_, v_a_617_);
lean_dec(v_a_617_);
lean_dec_ref(v_m_616_);
return v_res_618_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3(lean_object* v_00_u03b2_619_, lean_object* v_x_620_, lean_object* v_x_621_, lean_object* v_x_622_){
_start:
{
lean_object* v___x_623_; 
v___x_623_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3___redArg(v_x_620_, v_x_621_, v_x_622_);
return v___x_623_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4(lean_object* v_00_u03b2_624_, lean_object* v_m_625_, lean_object* v_a_626_, lean_object* v_b_627_){
_start:
{
lean_object* v___x_628_; 
v___x_628_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4___redArg(v_m_625_, v_a_626_, v_b_627_);
return v___x_628_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_629_, lean_object* v_x_630_, size_t v_x_631_, lean_object* v_x_632_){
_start:
{
lean_object* v___x_633_; 
v___x_633_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1___redArg(v_x_630_, v_x_631_, v_x_632_);
return v___x_633_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_634_, lean_object* v_x_635_, lean_object* v_x_636_, lean_object* v_x_637_){
_start:
{
size_t v_x_1737__boxed_638_; lean_object* v_res_639_; 
v_x_1737__boxed_638_ = lean_unbox_usize(v_x_636_);
lean_dec(v_x_636_);
v_res_639_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1(v_00_u03b2_634_, v_x_635_, v_x_1737__boxed_638_, v_x_637_);
lean_dec(v_x_637_);
lean_dec_ref(v_x_635_);
return v_res_639_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_640_, lean_object* v_a_641_, lean_object* v_x_642_){
_start:
{
lean_object* v___x_643_; 
v___x_643_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3___redArg(v_a_641_, v_x_642_);
return v___x_643_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_644_, lean_object* v_a_645_, lean_object* v_x_646_){
_start:
{
lean_object* v_res_647_; 
v_res_647_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3(v_00_u03b2_644_, v_a_645_, v_x_646_);
lean_dec(v_x_646_);
lean_dec(v_a_645_);
return v_res_647_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_648_, lean_object* v_x_649_, size_t v_x_650_, size_t v_x_651_, lean_object* v_x_652_, lean_object* v_x_653_){
_start:
{
lean_object* v___x_654_; 
v___x_654_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg(v_x_649_, v_x_650_, v_x_651_, v_x_652_, v_x_653_);
return v___x_654_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___boxed(lean_object* v_00_u03b2_655_, lean_object* v_x_656_, lean_object* v_x_657_, lean_object* v_x_658_, lean_object* v_x_659_, lean_object* v_x_660_){
_start:
{
size_t v_x_1753__boxed_661_; size_t v_x_1754__boxed_662_; lean_object* v_res_663_; 
v_x_1753__boxed_661_ = lean_unbox_usize(v_x_657_);
lean_dec(v_x_657_);
v_x_1754__boxed_662_ = lean_unbox_usize(v_x_658_);
lean_dec(v_x_658_);
v_res_663_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6(v_00_u03b2_655_, v_x_656_, v_x_1753__boxed_661_, v_x_1754__boxed_662_, v_x_659_, v_x_660_);
return v_res_663_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8(lean_object* v_00_u03b2_664_, lean_object* v_a_665_, lean_object* v_x_666_){
_start:
{
uint8_t v___x_667_; 
v___x_667_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8___redArg(v_a_665_, v_x_666_);
return v___x_667_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8___boxed(lean_object* v_00_u03b2_668_, lean_object* v_a_669_, lean_object* v_x_670_){
_start:
{
uint8_t v_res_671_; lean_object* v_r_672_; 
v_res_671_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8(v_00_u03b2_668_, v_a_669_, v_x_670_);
lean_dec(v_x_670_);
lean_dec(v_a_669_);
v_r_672_ = lean_box(v_res_671_);
return v_r_672_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9(lean_object* v_00_u03b2_673_, lean_object* v_data_674_){
_start:
{
lean_object* v___x_675_; 
v___x_675_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9___redArg(v_data_674_);
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__10(lean_object* v_00_u03b2_676_, lean_object* v_a_677_, lean_object* v_b_678_, lean_object* v_x_679_){
_start:
{
lean_object* v___x_680_; 
v___x_680_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__10___redArg(v_a_677_, v_b_678_, v_x_679_);
return v___x_680_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_681_, lean_object* v_keys_682_, lean_object* v_vals_683_, lean_object* v_heq_684_, lean_object* v_i_685_, lean_object* v_k_686_){
_start:
{
lean_object* v___x_687_; 
v___x_687_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4___redArg(v_keys_682_, v_vals_683_, v_i_685_, v_k_686_);
return v___x_687_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b2_688_, lean_object* v_keys_689_, lean_object* v_vals_690_, lean_object* v_heq_691_, lean_object* v_i_692_, lean_object* v_k_693_){
_start:
{
lean_object* v_res_694_; 
v_res_694_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4(v_00_u03b2_688_, v_keys_689_, v_vals_690_, v_heq_691_, v_i_692_, v_k_693_);
lean_dec(v_k_693_);
lean_dec_ref(v_vals_690_);
lean_dec_ref(v_keys_689_);
return v_res_694_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__9(lean_object* v_00_u03b2_695_, lean_object* v_n_696_, lean_object* v_k_697_, lean_object* v_v_698_){
_start:
{
lean_object* v___x_699_; 
v___x_699_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__9___redArg(v_n_696_, v_k_697_, v_v_698_);
return v___x_699_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10(lean_object* v_00_u03b2_700_, size_t v_depth_701_, lean_object* v_keys_702_, lean_object* v_vals_703_, lean_object* v_heq_704_, lean_object* v_i_705_, lean_object* v_entries_706_){
_start:
{
lean_object* v___x_707_; 
v___x_707_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg(v_depth_701_, v_keys_702_, v_vals_703_, v_i_705_, v_entries_706_);
return v___x_707_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___boxed(lean_object* v_00_u03b2_708_, lean_object* v_depth_709_, lean_object* v_keys_710_, lean_object* v_vals_711_, lean_object* v_heq_712_, lean_object* v_i_713_, lean_object* v_entries_714_){
_start:
{
size_t v_depth_boxed_715_; lean_object* v_res_716_; 
v_depth_boxed_715_ = lean_unbox_usize(v_depth_709_);
lean_dec(v_depth_709_);
v_res_716_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10(v_00_u03b2_708_, v_depth_boxed_715_, v_keys_710_, v_vals_711_, v_heq_712_, v_i_713_, v_entries_714_);
lean_dec_ref(v_vals_711_);
lean_dec_ref(v_keys_710_);
return v_res_716_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9_spec__14(lean_object* v_00_u03b2_717_, lean_object* v_i_718_, lean_object* v_source_719_, lean_object* v_target_720_){
_start:
{
lean_object* v___x_721_; 
v___x_721_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9_spec__14___redArg(v_i_718_, v_source_719_, v_target_720_);
return v___x_721_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__9_spec__11(lean_object* v_00_u03b2_722_, lean_object* v_x_723_, lean_object* v_x_724_, lean_object* v_x_725_, lean_object* v_x_726_){
_start:
{
lean_object* v___x_727_; 
v___x_727_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__9_spec__11___redArg(v_x_723_, v_x_724_, v_x_725_, v_x_726_);
return v___x_727_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9_spec__14_spec__16(lean_object* v_00_u03b2_728_, lean_object* v_x_729_, lean_object* v_x_730_){
_start:
{
lean_object* v___x_731_; 
v___x_731_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9_spec__14_spec__16___redArg(v_x_729_, v_x_730_);
return v___x_731_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__1___redArg(lean_object* v_m_732_){
_start:
{
uint8_t v_stage_u2081_733_; 
v_stage_u2081_733_ = lean_ctor_get_uint8(v_m_732_, sizeof(void*)*2);
if (v_stage_u2081_733_ == 0)
{
return v_m_732_;
}
else
{
lean_object* v_map_u2081_734_; lean_object* v_map_u2082_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_743_; 
v_map_u2081_734_ = lean_ctor_get(v_m_732_, 0);
v_map_u2082_735_ = lean_ctor_get(v_m_732_, 1);
v_isSharedCheck_743_ = !lean_is_exclusive(v_m_732_);
if (v_isSharedCheck_743_ == 0)
{
v___x_737_ = v_m_732_;
v_isShared_738_ = v_isSharedCheck_743_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_map_u2082_735_);
lean_inc(v_map_u2081_734_);
lean_dec(v_m_732_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_743_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
uint8_t v___x_739_; lean_object* v___x_741_; 
v___x_739_ = 0;
if (v_isShared_738_ == 0)
{
v___x_741_ = v___x_737_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v_map_u2081_734_);
lean_ctor_set(v_reuseFailAlloc_742_, 1, v_map_u2082_735_);
v___x_741_ = v_reuseFailAlloc_742_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
lean_ctor_set_uint8(v___x_741_, sizeof(void*)*2, v___x_739_);
return v___x_741_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__1(lean_object* v_00_u03b2_744_, lean_object* v_m_745_){
_start:
{
lean_object* v___x_746_; 
v___x_746_ = l_Lean_SMap_switch___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__1___redArg(v_m_745_);
return v___x_746_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn___lam__0_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(lean_object* v_es_747_){
_start:
{
lean_object* v___x_748_; 
v___x_748_ = lean_array_mk(v_es_747_);
return v___x_748_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_as_749_, size_t v_i_750_, size_t v_stop_751_, lean_object* v_b_752_){
_start:
{
uint8_t v___x_753_; 
v___x_753_ = lean_usize_dec_eq(v_i_750_, v_stop_751_);
if (v___x_753_ == 0)
{
lean_object* v___x_754_; lean_object* v___x_755_; size_t v___x_756_; size_t v___x_757_; 
v___x_754_ = lean_array_uget_borrowed(v_as_749_, v_i_750_);
lean_inc(v___x_754_);
v___x_755_ = l_Lean_addAliasEntry(v_b_752_, v___x_754_);
v___x_756_ = ((size_t)1ULL);
v___x_757_ = lean_usize_add(v_i_750_, v___x_756_);
v_i_750_ = v___x_757_;
v_b_752_ = v___x_755_;
goto _start;
}
else
{
return v_b_752_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_as_759_, lean_object* v_i_760_, lean_object* v_stop_761_, lean_object* v_b_762_){
_start:
{
size_t v_i_boxed_763_; size_t v_stop_boxed_764_; lean_object* v_res_765_; 
v_i_boxed_763_ = lean_unbox_usize(v_i_760_);
lean_dec(v_i_760_);
v_stop_boxed_764_ = lean_unbox_usize(v_stop_761_);
lean_dec(v_stop_761_);
v_res_765_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__0(v_as_759_, v_i_boxed_763_, v_stop_boxed_764_, v_b_762_);
lean_dec_ref(v_as_759_);
return v_res_765_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_as_766_, size_t v_i_767_, size_t v_stop_768_, lean_object* v_b_769_){
_start:
{
lean_object* v___y_771_; uint8_t v___x_775_; 
v___x_775_ = lean_usize_dec_eq(v_i_767_, v_stop_768_);
if (v___x_775_ == 0)
{
lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; uint8_t v___x_779_; 
v___x_776_ = lean_array_uget_borrowed(v_as_766_, v_i_767_);
v___x_777_ = lean_unsigned_to_nat(0u);
v___x_778_ = lean_array_get_size(v___x_776_);
v___x_779_ = lean_nat_dec_lt(v___x_777_, v___x_778_);
if (v___x_779_ == 0)
{
v___y_771_ = v_b_769_;
goto v___jp_770_;
}
else
{
size_t v___x_780_; size_t v___x_781_; lean_object* v___x_782_; 
v___x_780_ = ((size_t)0ULL);
v___x_781_ = lean_usize_of_nat(v___x_778_);
v___x_782_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__0(v___x_776_, v___x_780_, v___x_781_, v_b_769_);
v___y_771_ = v___x_782_;
goto v___jp_770_;
}
}
else
{
return v_b_769_;
}
v___jp_770_:
{
size_t v___x_772_; size_t v___x_773_; 
v___x_772_ = ((size_t)1ULL);
v___x_773_ = lean_usize_add(v_i_767_, v___x_772_);
v_i_767_ = v___x_773_;
v_b_769_ = v___y_771_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object* v_as_783_, lean_object* v_i_784_, lean_object* v_stop_785_, lean_object* v_b_786_){
_start:
{
size_t v_i_boxed_787_; size_t v_stop_boxed_788_; lean_object* v_res_789_; 
v_i_boxed_787_ = lean_unbox_usize(v_i_784_);
lean_dec(v_i_784_);
v_stop_boxed_788_ = lean_unbox_usize(v_stop_785_);
lean_dec(v_stop_785_);
v_res_789_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__1(v_as_783_, v_i_boxed_787_, v_stop_boxed_788_, v_b_786_);
lean_dec_ref(v_as_783_);
return v_res_789_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0(lean_object* v_initState_790_, lean_object* v_as_791_){
_start:
{
lean_object* v___x_792_; lean_object* v___x_793_; uint8_t v___x_794_; 
v___x_792_ = lean_unsigned_to_nat(0u);
v___x_793_ = lean_array_get_size(v_as_791_);
v___x_794_ = lean_nat_dec_lt(v___x_792_, v___x_793_);
if (v___x_794_ == 0)
{
return v_initState_790_;
}
else
{
size_t v___x_795_; size_t v___x_796_; lean_object* v___x_797_; 
v___x_795_ = ((size_t)0ULL);
v___x_796_ = lean_usize_of_nat(v___x_793_);
v___x_797_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__1(v_as_791_, v___x_795_, v___x_796_, v_initState_790_);
return v___x_797_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0___boxed(lean_object* v_initState_798_, lean_object* v_as_799_){
_start:
{
lean_object* v_res_800_; 
v_res_800_ = l_Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0(v_initState_798_, v_as_799_);
lean_dec_ref(v_as_799_);
return v_res_800_;
}
}
static lean_object* _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; 
v___x_801_ = lean_box(0);
v___x_802_ = lean_unsigned_to_nat(16u);
v___x_803_ = lean_mk_array(v___x_802_, v___x_801_);
return v___x_803_;
}
}
static lean_object* _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; 
v___x_804_ = lean_obj_once(&l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_, &l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__once, _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_);
v___x_805_ = lean_unsigned_to_nat(0u);
v___x_806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_806_, 0, v___x_805_);
lean_ctor_set(v___x_806_, 1, v___x_804_);
return v___x_806_;
}
}
static lean_object* _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_807_; 
v___x_807_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_807_;
}
}
static lean_object* _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_808_; lean_object* v___x_809_; 
v___x_808_ = lean_obj_once(&l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_, &l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__once, _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_);
v___x_809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_809_, 0, v___x_808_);
return v___x_809_;
}
}
static lean_object* _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__4_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_810_; lean_object* v___x_811_; uint8_t v___x_812_; lean_object* v___x_813_; 
v___x_810_ = lean_obj_once(&l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_, &l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__once, _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_);
v___x_811_ = lean_obj_once(&l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_, &l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__once, _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_);
v___x_812_ = 1;
v___x_813_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_813_, 0, v___x_811_);
lean_ctor_set(v___x_813_, 1, v___x_810_);
lean_ctor_set_uint8(v___x_813_, sizeof(void*)*2, v___x_812_);
return v___x_813_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn___lam__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(lean_object* v_es_814_){
_start:
{
lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; 
v___x_815_ = lean_obj_once(&l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__4_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_, &l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__4_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__once, _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__4_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_);
v___x_816_ = l_Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0(v___x_815_, v_es_814_);
v___x_817_ = l_Lean_SMap_switch___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__1___redArg(v___x_816_);
return v___x_817_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn___lam__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2____boxed(lean_object* v_es_818_){
_start:
{
lean_object* v_res_819_; 
v_res_819_ = l___private_Lean_ResolveName_0__Lean_initFn___lam__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(v_es_818_);
lean_dec_ref(v_es_818_);
return v_res_819_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_836_; lean_object* v___x_837_; 
v___x_836_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_initFn___closed__6_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_));
v___x_837_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_836_);
return v___x_837_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2____boxed(lean_object* v_a_838_){
_start:
{
lean_object* v_res_839_; 
v_res_839_ = l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_();
return v_res_839_;
}
}
LEAN_EXPORT lean_object* l_Lean_addAlias(lean_object* v_env_840_, lean_object* v_a_841_, lean_object* v_e_842_){
_start:
{
lean_object* v___x_843_; lean_object* v_toEnvExtension_844_; lean_object* v_asyncMode_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; 
v___x_843_ = l_Lean_aliasExtension;
v_toEnvExtension_844_ = lean_ctor_get(v___x_843_, 0);
v_asyncMode_845_ = lean_ctor_get(v_toEnvExtension_844_, 2);
v___x_846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_846_, 0, v_a_841_);
lean_ctor_set(v___x_846_, 1, v_e_842_);
v___x_847_ = lean_box(0);
v___x_848_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_843_, v_env_840_, v___x_846_, v_asyncMode_845_, v___x_847_);
return v___x_848_;
}
}
static lean_object* _init_l_Lean_getAliasState___closed__2(void){
_start:
{
lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; 
v___x_851_ = ((lean_object*)(l_Lean_getAliasState___closed__1));
v___x_852_ = ((lean_object*)(l_Lean_getAliasState___closed__0));
v___x_853_ = l_Lean_SMap_instInhabited(lean_box(0), lean_box(0), v___x_852_, v___x_851_);
return v___x_853_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAliasState(lean_object* v_env_854_){
_start:
{
lean_object* v___x_855_; lean_object* v_toEnvExtension_856_; lean_object* v_asyncMode_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; 
v___x_855_ = l_Lean_aliasExtension;
v_toEnvExtension_856_ = lean_ctor_get(v___x_855_, 0);
v_asyncMode_857_ = lean_ctor_get(v_toEnvExtension_856_, 2);
v___x_858_ = lean_obj_once(&l_Lean_getAliasState___closed__2, &l_Lean_getAliasState___closed__2_once, _init_l_Lean_getAliasState___closed__2);
v___x_859_ = lean_box(0);
v___x_860_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_858_, v___x_855_, v_env_854_, v_asyncMode_857_, v___x_859_);
return v___x_860_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_getAliases_spec__0(lean_object* v_env_861_, uint8_t v_skipProtected_862_, lean_object* v_a_863_, lean_object* v_a_864_){
_start:
{
if (lean_obj_tag(v_a_863_) == 0)
{
lean_object* v___x_865_; 
lean_dec_ref(v_env_861_);
v___x_865_ = l_List_reverse___redArg(v_a_864_);
return v___x_865_;
}
else
{
lean_object* v_head_866_; lean_object* v_tail_867_; lean_object* v___x_869_; uint8_t v_isShared_870_; uint8_t v_isSharedCheck_878_; 
v_head_866_ = lean_ctor_get(v_a_863_, 0);
v_tail_867_ = lean_ctor_get(v_a_863_, 1);
v_isSharedCheck_878_ = !lean_is_exclusive(v_a_863_);
if (v_isSharedCheck_878_ == 0)
{
v___x_869_ = v_a_863_;
v_isShared_870_ = v_isSharedCheck_878_;
goto v_resetjp_868_;
}
else
{
lean_inc(v_tail_867_);
lean_inc(v_head_866_);
lean_dec(v_a_863_);
v___x_869_ = lean_box(0);
v_isShared_870_ = v_isSharedCheck_878_;
goto v_resetjp_868_;
}
v_resetjp_868_:
{
uint8_t v___x_871_; 
lean_inc(v_head_866_);
lean_inc_ref(v_env_861_);
v___x_871_ = l_Lean_isProtected(v_env_861_, v_head_866_);
if (v___x_871_ == 0)
{
if (v_skipProtected_862_ == 0)
{
lean_del_object(v___x_869_);
lean_dec(v_head_866_);
v_a_863_ = v_tail_867_;
goto _start;
}
else
{
lean_object* v___x_874_; 
if (v_isShared_870_ == 0)
{
lean_ctor_set(v___x_869_, 1, v_a_864_);
v___x_874_ = v___x_869_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v_head_866_);
lean_ctor_set(v_reuseFailAlloc_876_, 1, v_a_864_);
v___x_874_ = v_reuseFailAlloc_876_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
v_a_863_ = v_tail_867_;
v_a_864_ = v___x_874_;
goto _start;
}
}
}
else
{
lean_del_object(v___x_869_);
lean_dec(v_head_866_);
v_a_863_ = v_tail_867_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_getAliases_spec__0___boxed(lean_object* v_env_879_, lean_object* v_skipProtected_880_, lean_object* v_a_881_, lean_object* v_a_882_){
_start:
{
uint8_t v_skipProtected_boxed_883_; lean_object* v_res_884_; 
v_skipProtected_boxed_883_ = lean_unbox(v_skipProtected_880_);
v_res_884_ = l_List_filterTR_loop___at___00Lean_getAliases_spec__0(v_env_879_, v_skipProtected_boxed_883_, v_a_881_, v_a_882_);
return v_res_884_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAliases(lean_object* v_env_885_, lean_object* v_a_886_, uint8_t v_skipProtected_887_){
_start:
{
lean_object* v___x_888_; lean_object* v_toEnvExtension_889_; lean_object* v_asyncMode_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; 
v___x_888_ = l_Lean_aliasExtension;
v_toEnvExtension_889_ = lean_ctor_get(v___x_888_, 0);
v_asyncMode_890_ = lean_ctor_get(v_toEnvExtension_889_, 2);
v___x_891_ = lean_obj_once(&l_Lean_getAliasState___closed__2, &l_Lean_getAliasState___closed__2_once, _init_l_Lean_getAliasState___closed__2);
v___x_892_ = lean_box(0);
lean_inc_ref(v_env_885_);
v___x_893_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_891_, v___x_888_, v_env_885_, v_asyncMode_890_, v___x_892_);
v___x_894_ = l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0___redArg(v___x_893_, v_a_886_);
lean_dec(v___x_893_);
if (lean_obj_tag(v___x_894_) == 0)
{
lean_object* v___x_895_; 
lean_dec_ref(v_env_885_);
v___x_895_ = lean_box(0);
return v___x_895_;
}
else
{
if (v_skipProtected_887_ == 0)
{
lean_object* v_val_896_; 
lean_dec_ref(v_env_885_);
v_val_896_ = lean_ctor_get(v___x_894_, 0);
lean_inc(v_val_896_);
lean_dec_ref_known(v___x_894_, 1);
return v_val_896_;
}
else
{
lean_object* v_val_897_; lean_object* v___x_898_; lean_object* v___x_899_; 
v_val_897_ = lean_ctor_get(v___x_894_, 0);
lean_inc(v_val_897_);
lean_dec_ref_known(v___x_894_, 1);
v___x_898_ = lean_box(0);
v___x_899_ = l_List_filterTR_loop___at___00Lean_getAliases_spec__0(v_env_885_, v_skipProtected_887_, v_val_897_, v___x_898_);
return v___x_899_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getAliases___boxed(lean_object* v_env_900_, lean_object* v_a_901_, lean_object* v_skipProtected_902_){
_start:
{
uint8_t v_skipProtected_boxed_903_; lean_object* v_res_904_; 
v_skipProtected_boxed_903_ = lean_unbox(v_skipProtected_902_);
v_res_904_ = l_Lean_getAliases(v_env_900_, v_a_901_, v_skipProtected_boxed_903_);
lean_dec(v_a_901_);
return v_res_904_;
}
}
LEAN_EXPORT lean_object* l_Lean_getRevAliases___lam__0(lean_object* v_e_905_, lean_object* v_as_906_, lean_object* v_a_907_, lean_object* v_es_908_){
_start:
{
uint8_t v___x_909_; 
v___x_909_ = l_List_elem___at___00Lean_addAliasEntry_spec__2(v_e_905_, v_es_908_);
if (v___x_909_ == 0)
{
lean_dec(v_a_907_);
return v_as_906_;
}
else
{
lean_object* v___x_910_; 
v___x_910_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_910_, 0, v_a_907_);
lean_ctor_set(v___x_910_, 1, v_as_906_);
return v___x_910_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getRevAliases___lam__0___boxed(lean_object* v_e_911_, lean_object* v_as_912_, lean_object* v_a_913_, lean_object* v_es_914_){
_start:
{
lean_object* v_res_915_; 
v_res_915_ = l_Lean_getRevAliases___lam__0(v_e_911_, v_as_912_, v_a_913_, v_es_914_);
lean_dec(v_es_914_);
lean_dec(v_e_911_);
return v_res_915_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6___redArg(lean_object* v_f_916_, lean_object* v_keys_917_, lean_object* v_vals_918_, lean_object* v_i_919_, lean_object* v_acc_920_){
_start:
{
lean_object* v___x_921_; uint8_t v___x_922_; 
v___x_921_ = lean_array_get_size(v_keys_917_);
v___x_922_ = lean_nat_dec_lt(v_i_919_, v___x_921_);
if (v___x_922_ == 0)
{
lean_dec(v_i_919_);
lean_dec(v_f_916_);
return v_acc_920_;
}
else
{
lean_object* v_k_923_; lean_object* v_v_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; 
v_k_923_ = lean_array_fget_borrowed(v_keys_917_, v_i_919_);
v_v_924_ = lean_array_fget_borrowed(v_vals_918_, v_i_919_);
lean_inc(v_f_916_);
lean_inc(v_v_924_);
lean_inc(v_k_923_);
v___x_925_ = lean_apply_3(v_f_916_, v_acc_920_, v_k_923_, v_v_924_);
v___x_926_ = lean_unsigned_to_nat(1u);
v___x_927_ = lean_nat_add(v_i_919_, v___x_926_);
lean_dec(v_i_919_);
v_i_919_ = v___x_927_;
v_acc_920_ = v___x_925_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_f_929_, lean_object* v_keys_930_, lean_object* v_vals_931_, lean_object* v_i_932_, lean_object* v_acc_933_){
_start:
{
lean_object* v_res_934_; 
v_res_934_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6___redArg(v_f_929_, v_keys_930_, v_vals_931_, v_i_932_, v_acc_933_);
lean_dec_ref(v_vals_931_);
lean_dec_ref(v_keys_930_);
return v_res_934_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(lean_object* v_f_935_, lean_object* v_as_936_, size_t v_i_937_, size_t v_stop_938_, lean_object* v_b_939_){
_start:
{
lean_object* v___y_941_; uint8_t v___x_945_; 
v___x_945_ = lean_usize_dec_eq(v_i_937_, v_stop_938_);
if (v___x_945_ == 0)
{
lean_object* v___x_946_; 
v___x_946_ = lean_array_uget_borrowed(v_as_936_, v_i_937_);
switch(lean_obj_tag(v___x_946_))
{
case 0:
{
lean_object* v_key_947_; lean_object* v_val_948_; lean_object* v___x_949_; 
v_key_947_ = lean_ctor_get(v___x_946_, 0);
v_val_948_ = lean_ctor_get(v___x_946_, 1);
lean_inc(v_f_935_);
lean_inc(v_val_948_);
lean_inc(v_key_947_);
v___x_949_ = lean_apply_3(v_f_935_, v_b_939_, v_key_947_, v_val_948_);
v___y_941_ = v___x_949_;
goto v___jp_940_;
}
case 1:
{
lean_object* v_node_950_; lean_object* v___x_951_; 
v_node_950_ = lean_ctor_get(v___x_946_, 0);
lean_inc(v_f_935_);
v___x_951_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg(v_f_935_, v_node_950_, v_b_939_);
v___y_941_ = v___x_951_;
goto v___jp_940_;
}
default: 
{
v___y_941_ = v_b_939_;
goto v___jp_940_;
}
}
}
else
{
lean_dec(v_f_935_);
return v_b_939_;
}
v___jp_940_:
{
size_t v___x_942_; size_t v___x_943_; 
v___x_942_ = ((size_t)1ULL);
v___x_943_ = lean_usize_add(v_i_937_, v___x_942_);
v_i_937_ = v___x_943_;
v_b_939_ = v___y_941_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_f_952_, lean_object* v_x_953_, lean_object* v_x_954_){
_start:
{
if (lean_obj_tag(v_x_953_) == 0)
{
lean_object* v_es_955_; lean_object* v___x_956_; lean_object* v___x_957_; uint8_t v___x_958_; 
v_es_955_ = lean_ctor_get(v_x_953_, 0);
v___x_956_ = lean_unsigned_to_nat(0u);
v___x_957_ = lean_array_get_size(v_es_955_);
v___x_958_ = lean_nat_dec_lt(v___x_956_, v___x_957_);
if (v___x_958_ == 0)
{
lean_dec(v_f_952_);
return v_x_954_;
}
else
{
size_t v___x_959_; size_t v___x_960_; lean_object* v___x_961_; 
v___x_959_ = ((size_t)0ULL);
v___x_960_ = lean_usize_of_nat(v___x_957_);
v___x_961_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(v_f_952_, v_es_955_, v___x_959_, v___x_960_, v_x_954_);
return v___x_961_;
}
}
else
{
lean_object* v_ks_962_; lean_object* v_vs_963_; lean_object* v___x_964_; lean_object* v___x_965_; 
v_ks_962_ = lean_ctor_get(v_x_953_, 0);
v_vs_963_ = lean_ctor_get(v_x_953_, 1);
v___x_964_ = lean_unsigned_to_nat(0u);
v___x_965_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6___redArg(v_f_952_, v_ks_962_, v_vs_963_, v___x_964_, v_x_954_);
return v___x_965_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_f_966_, lean_object* v_x_967_, lean_object* v_x_968_){
_start:
{
lean_object* v_res_969_; 
v_res_969_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg(v_f_966_, v_x_967_, v_x_968_);
lean_dec_ref(v_x_967_);
return v_res_969_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v_f_970_, lean_object* v_as_971_, lean_object* v_i_972_, lean_object* v_stop_973_, lean_object* v_b_974_){
_start:
{
size_t v_i_boxed_975_; size_t v_stop_boxed_976_; lean_object* v_res_977_; 
v_i_boxed_975_ = lean_unbox_usize(v_i_972_);
lean_dec(v_i_972_);
v_stop_boxed_976_ = lean_unbox_usize(v_stop_973_);
lean_dec(v_stop_973_);
v_res_977_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(v_f_970_, v_as_971_, v_i_boxed_975_, v_stop_boxed_976_, v_b_974_);
lean_dec_ref(v_as_971_);
return v_res_977_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg___lam__0(lean_object* v_f_978_, lean_object* v_x1_979_, lean_object* v_x2_980_, lean_object* v_x3_981_){
_start:
{
lean_object* v___x_982_; 
v___x_982_ = lean_apply_3(v_f_978_, v_x1_979_, v_x2_980_, v_x3_981_);
return v___x_982_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg(lean_object* v_map_983_, lean_object* v_f_984_, lean_object* v_init_985_){
_start:
{
lean_object* v___f_986_; lean_object* v___x_987_; 
v___f_986_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_986_, 0, v_f_984_);
v___x_987_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg(v___f_986_, v_map_983_, v_init_985_);
return v___x_987_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg___boxed(lean_object* v_map_988_, lean_object* v_f_989_, lean_object* v_init_990_){
_start:
{
lean_object* v_res_991_; 
v_res_991_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg(v_map_988_, v_f_989_, v_init_990_);
lean_dec_ref(v_map_988_);
return v_res_991_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__0___redArg(lean_object* v_f_992_, lean_object* v_x_993_, lean_object* v_x_994_){
_start:
{
if (lean_obj_tag(v_x_994_) == 0)
{
lean_dec(v_f_992_);
return v_x_993_;
}
else
{
lean_object* v_key_995_; lean_object* v_value_996_; lean_object* v_tail_997_; lean_object* v___x_998_; 
v_key_995_ = lean_ctor_get(v_x_994_, 0);
lean_inc(v_key_995_);
v_value_996_ = lean_ctor_get(v_x_994_, 1);
lean_inc(v_value_996_);
v_tail_997_ = lean_ctor_get(v_x_994_, 2);
lean_inc(v_tail_997_);
lean_dec_ref_known(v_x_994_, 3);
lean_inc(v_f_992_);
v___x_998_ = lean_apply_3(v_f_992_, v_x_993_, v_key_995_, v_value_996_);
v_x_993_ = v___x_998_;
v_x_994_ = v_tail_997_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2___redArg(lean_object* v_f_1000_, lean_object* v_as_1001_, size_t v_i_1002_, size_t v_stop_1003_, lean_object* v_b_1004_){
_start:
{
uint8_t v___x_1005_; 
v___x_1005_ = lean_usize_dec_eq(v_i_1002_, v_stop_1003_);
if (v___x_1005_ == 0)
{
lean_object* v___x_1006_; lean_object* v___x_1007_; size_t v___x_1008_; size_t v___x_1009_; 
v___x_1006_ = lean_array_uget_borrowed(v_as_1001_, v_i_1002_);
lean_inc(v___x_1006_);
lean_inc(v_f_1000_);
v___x_1007_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__0___redArg(v_f_1000_, v_b_1004_, v___x_1006_);
v___x_1008_ = ((size_t)1ULL);
v___x_1009_ = lean_usize_add(v_i_1002_, v___x_1008_);
v_i_1002_ = v___x_1009_;
v_b_1004_ = v___x_1007_;
goto _start;
}
else
{
lean_dec(v_f_1000_);
return v_b_1004_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2___redArg___boxed(lean_object* v_f_1011_, lean_object* v_as_1012_, lean_object* v_i_1013_, lean_object* v_stop_1014_, lean_object* v_b_1015_){
_start:
{
size_t v_i_boxed_1016_; size_t v_stop_boxed_1017_; lean_object* v_res_1018_; 
v_i_boxed_1016_ = lean_unbox_usize(v_i_1013_);
lean_dec(v_i_1013_);
v_stop_boxed_1017_ = lean_unbox_usize(v_stop_1014_);
lean_dec(v_stop_1014_);
v_res_1018_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2___redArg(v_f_1011_, v_as_1012_, v_i_boxed_1016_, v_stop_boxed_1017_, v_b_1015_);
lean_dec_ref(v_as_1012_);
return v_res_1018_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0___redArg(lean_object* v_f_1019_, lean_object* v_init_1020_, lean_object* v_m_1021_){
_start:
{
lean_object* v_map_u2081_1022_; lean_object* v_map_u2082_1023_; lean_object* v_buckets_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; uint8_t v___x_1027_; 
v_map_u2081_1022_ = lean_ctor_get(v_m_1021_, 0);
v_map_u2082_1023_ = lean_ctor_get(v_m_1021_, 1);
v_buckets_1024_ = lean_ctor_get(v_map_u2081_1022_, 1);
v___x_1025_ = lean_unsigned_to_nat(0u);
v___x_1026_ = lean_array_get_size(v_buckets_1024_);
v___x_1027_ = lean_nat_dec_lt(v___x_1025_, v___x_1026_);
if (v___x_1027_ == 0)
{
lean_object* v___x_1028_; 
v___x_1028_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg(v_map_u2082_1023_, v_f_1019_, v_init_1020_);
return v___x_1028_;
}
else
{
size_t v___x_1029_; size_t v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; 
v___x_1029_ = ((size_t)0ULL);
v___x_1030_ = lean_usize_of_nat(v___x_1026_);
lean_inc(v_f_1019_);
v___x_1031_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2___redArg(v_f_1019_, v_buckets_1024_, v___x_1029_, v___x_1030_, v_init_1020_);
v___x_1032_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg(v_map_u2082_1023_, v_f_1019_, v___x_1031_);
return v___x_1032_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0___redArg___boxed(lean_object* v_f_1033_, lean_object* v_init_1034_, lean_object* v_m_1035_){
_start:
{
lean_object* v_res_1036_; 
v_res_1036_ = l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0___redArg(v_f_1033_, v_init_1034_, v_m_1035_);
lean_dec_ref(v_m_1035_);
return v_res_1036_;
}
}
LEAN_EXPORT lean_object* l_Lean_getRevAliases(lean_object* v_env_1037_, lean_object* v_e_1038_){
_start:
{
lean_object* v___x_1039_; lean_object* v_toEnvExtension_1040_; lean_object* v_asyncMode_1041_; lean_object* v___f_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; 
v___x_1039_ = l_Lean_aliasExtension;
v_toEnvExtension_1040_ = lean_ctor_get(v___x_1039_, 0);
v_asyncMode_1041_ = lean_ctor_get(v_toEnvExtension_1040_, 2);
v___f_1042_ = lean_alloc_closure((void*)(l_Lean_getRevAliases___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1042_, 0, v_e_1038_);
v___x_1043_ = lean_obj_once(&l_Lean_getAliasState___closed__2, &l_Lean_getAliasState___closed__2_once, _init_l_Lean_getAliasState___closed__2);
v___x_1044_ = lean_box(0);
v___x_1045_ = lean_box(0);
v___x_1046_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1043_, v___x_1039_, v_env_1037_, v_asyncMode_1041_, v___x_1045_);
v___x_1047_ = l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0___redArg(v___f_1042_, v___x_1044_, v___x_1046_);
lean_dec(v___x_1046_);
return v___x_1047_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0(lean_object* v_00_u03b2_1048_, lean_object* v_00_u03c3_1049_, lean_object* v_f_1050_, lean_object* v_init_1051_, lean_object* v_m_1052_){
_start:
{
lean_object* v___x_1053_; 
v___x_1053_ = l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0___redArg(v_f_1050_, v_init_1051_, v_m_1052_);
return v___x_1053_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0___boxed(lean_object* v_00_u03b2_1054_, lean_object* v_00_u03c3_1055_, lean_object* v_f_1056_, lean_object* v_init_1057_, lean_object* v_m_1058_){
_start:
{
lean_object* v_res_1059_; 
v_res_1059_ = l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0(v_00_u03b2_1054_, v_00_u03c3_1055_, v_f_1056_, v_init_1057_, v_m_1058_);
lean_dec_ref(v_m_1058_);
return v_res_1059_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__0(lean_object* v_00_u03b2_1060_, lean_object* v_00_u03c3_1061_, lean_object* v_f_1062_, lean_object* v_x_1063_, lean_object* v_x_1064_){
_start:
{
lean_object* v___x_1065_; 
v___x_1065_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__0___redArg(v_f_1062_, v_x_1063_, v_x_1064_);
return v___x_1065_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1(lean_object* v_00_u03c3_1066_, lean_object* v_00_u03b2_1067_, lean_object* v_map_1068_, lean_object* v_f_1069_, lean_object* v_init_1070_){
_start:
{
lean_object* v___x_1071_; 
v___x_1071_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg(v_map_1068_, v_f_1069_, v_init_1070_);
return v___x_1071_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___boxed(lean_object* v_00_u03c3_1072_, lean_object* v_00_u03b2_1073_, lean_object* v_map_1074_, lean_object* v_f_1075_, lean_object* v_init_1076_){
_start:
{
lean_object* v_res_1077_; 
v_res_1077_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1(v_00_u03c3_1072_, v_00_u03b2_1073_, v_map_1074_, v_f_1075_, v_init_1076_);
lean_dec_ref(v_map_1074_);
return v_res_1077_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2(lean_object* v_00_u03b2_1078_, lean_object* v_00_u03c3_1079_, lean_object* v_f_1080_, lean_object* v_as_1081_, size_t v_i_1082_, size_t v_stop_1083_, lean_object* v_b_1084_){
_start:
{
lean_object* v___x_1085_; 
v___x_1085_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2___redArg(v_f_1080_, v_as_1081_, v_i_1082_, v_stop_1083_, v_b_1084_);
return v___x_1085_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1086_, lean_object* v_00_u03c3_1087_, lean_object* v_f_1088_, lean_object* v_as_1089_, lean_object* v_i_1090_, lean_object* v_stop_1091_, lean_object* v_b_1092_){
_start:
{
size_t v_i_boxed_1093_; size_t v_stop_boxed_1094_; lean_object* v_res_1095_; 
v_i_boxed_1093_ = lean_unbox_usize(v_i_1090_);
lean_dec(v_i_1090_);
v_stop_boxed_1094_ = lean_unbox_usize(v_stop_1091_);
lean_dec(v_stop_1091_);
v_res_1095_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2(v_00_u03b2_1086_, v_00_u03c3_1087_, v_f_1088_, v_as_1089_, v_i_boxed_1093_, v_stop_boxed_1094_, v_b_1092_);
lean_dec_ref(v_as_1089_);
return v_res_1095_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2___redArg(lean_object* v_map_1096_, lean_object* v_f_1097_, lean_object* v_init_1098_){
_start:
{
lean_object* v___x_1099_; 
v___x_1099_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg(v_f_1097_, v_map_1096_, v_init_1098_);
return v___x_1099_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_map_1100_, lean_object* v_f_1101_, lean_object* v_init_1102_){
_start:
{
lean_object* v_res_1103_; 
v_res_1103_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2___redArg(v_map_1100_, v_f_1101_, v_init_1102_);
lean_dec_ref(v_map_1100_);
return v_res_1103_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2(lean_object* v_00_u03c3_1104_, lean_object* v_00_u03b2_1105_, lean_object* v_map_1106_, lean_object* v_f_1107_, lean_object* v_init_1108_){
_start:
{
lean_object* v___x_1109_; 
v___x_1109_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg(v_f_1107_, v_map_1106_, v_init_1108_);
return v___x_1109_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03c3_1110_, lean_object* v_00_u03b2_1111_, lean_object* v_map_1112_, lean_object* v_f_1113_, lean_object* v_init_1114_){
_start:
{
lean_object* v_res_1115_; 
v_res_1115_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2(v_00_u03c3_1110_, v_00_u03b2_1111_, v_map_1112_, v_f_1113_, v_init_1114_);
lean_dec_ref(v_map_1112_);
return v_res_1115_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03c3_1116_, lean_object* v_00_u03b1_1117_, lean_object* v_00_u03b2_1118_, lean_object* v_f_1119_, lean_object* v_x_1120_, lean_object* v_x_1121_){
_start:
{
lean_object* v___x_1122_; 
v___x_1122_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg(v_f_1119_, v_x_1120_, v_x_1121_);
return v___x_1122_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03c3_1123_, lean_object* v_00_u03b1_1124_, lean_object* v_00_u03b2_1125_, lean_object* v_f_1126_, lean_object* v_x_1127_, lean_object* v_x_1128_){
_start:
{
lean_object* v_res_1129_; 
v_res_1129_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3(v_00_u03c3_1123_, v_00_u03b1_1124_, v_00_u03b2_1125_, v_f_1126_, v_x_1127_, v_x_1128_);
lean_dec_ref(v_x_1127_);
return v_res_1129_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5(lean_object* v_00_u03b1_1130_, lean_object* v_00_u03b2_1131_, lean_object* v_00_u03c3_1132_, lean_object* v_f_1133_, lean_object* v_as_1134_, size_t v_i_1135_, size_t v_stop_1136_, lean_object* v_b_1137_){
_start:
{
lean_object* v___x_1138_; 
v___x_1138_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(v_f_1133_, v_as_1134_, v_i_1135_, v_stop_1136_, v_b_1137_);
return v___x_1138_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5___boxed(lean_object* v_00_u03b1_1139_, lean_object* v_00_u03b2_1140_, lean_object* v_00_u03c3_1141_, lean_object* v_f_1142_, lean_object* v_as_1143_, lean_object* v_i_1144_, lean_object* v_stop_1145_, lean_object* v_b_1146_){
_start:
{
size_t v_i_boxed_1147_; size_t v_stop_boxed_1148_; lean_object* v_res_1149_; 
v_i_boxed_1147_ = lean_unbox_usize(v_i_1144_);
lean_dec(v_i_1144_);
v_stop_boxed_1148_ = lean_unbox_usize(v_stop_1145_);
lean_dec(v_stop_1145_);
v_res_1149_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5(v_00_u03b1_1139_, v_00_u03b2_1140_, v_00_u03c3_1141_, v_f_1142_, v_as_1143_, v_i_boxed_1147_, v_stop_boxed_1148_, v_b_1146_);
lean_dec_ref(v_as_1143_);
return v_res_1149_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6(lean_object* v_00_u03c3_1150_, lean_object* v_00_u03b1_1151_, lean_object* v_00_u03b2_1152_, lean_object* v_f_1153_, lean_object* v_keys_1154_, lean_object* v_vals_1155_, lean_object* v_heq_1156_, lean_object* v_i_1157_, lean_object* v_acc_1158_){
_start:
{
lean_object* v___x_1159_; 
v___x_1159_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6___redArg(v_f_1153_, v_keys_1154_, v_vals_1155_, v_i_1157_, v_acc_1158_);
return v___x_1159_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03c3_1160_, lean_object* v_00_u03b1_1161_, lean_object* v_00_u03b2_1162_, lean_object* v_f_1163_, lean_object* v_keys_1164_, lean_object* v_vals_1165_, lean_object* v_heq_1166_, lean_object* v_i_1167_, lean_object* v_acc_1168_){
_start:
{
lean_object* v_res_1169_; 
v_res_1169_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6(v_00_u03c3_1160_, v_00_u03b1_1161_, v_00_u03b2_1162_, v_f_1163_, v_keys_1164_, v_vals_1165_, v_heq_1166_, v_i_1167_, v_acc_1168_);
lean_dec_ref(v_vals_1165_);
lean_dec_ref(v_keys_1164_);
return v_res_1169_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(lean_object* v_env_1170_, lean_object* v_declName_1171_){
_start:
{
uint8_t v___y_1173_; uint8_t v___x_1176_; 
v___x_1176_ = l_Lean_Environment_containsOnBranch(v_env_1170_, v_declName_1171_);
if (v___x_1176_ == 0)
{
uint8_t v___x_1177_; 
lean_inc(v_declName_1171_);
lean_inc_ref(v_env_1170_);
v___x_1177_ = lean_is_reserved_name(v_env_1170_, v_declName_1171_);
v___y_1173_ = v___x_1177_;
goto v___jp_1172_;
}
else
{
v___y_1173_ = v___x_1176_;
goto v___jp_1172_;
}
v___jp_1172_:
{
if (v___y_1173_ == 0)
{
uint8_t v___x_1174_; uint8_t v___x_1175_; 
v___x_1174_ = 1;
v___x_1175_ = l_Lean_Environment_contains(v_env_1170_, v_declName_1171_, v___x_1174_);
return v___x_1175_;
}
else
{
lean_dec(v_declName_1171_);
lean_dec_ref(v_env_1170_);
return v___y_1173_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved___boxed(lean_object* v_env_1178_, lean_object* v_declName_1179_){
_start:
{
uint8_t v_res_1180_; lean_object* v_r_1181_; 
v_res_1180_ = l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(v_env_1178_, v_declName_1179_);
v_r_1181_ = lean_box(v_res_1180_);
return v_r_1181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__spec__0(lean_object* v_name_1182_, lean_object* v_decl_1183_, lean_object* v_ref_1184_){
_start:
{
lean_object* v_defValue_1186_; lean_object* v_descr_1187_; lean_object* v_deprecation_x3f_1188_; lean_object* v___x_1189_; uint8_t v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; 
v_defValue_1186_ = lean_ctor_get(v_decl_1183_, 0);
v_descr_1187_ = lean_ctor_get(v_decl_1183_, 1);
v_deprecation_x3f_1188_ = lean_ctor_get(v_decl_1183_, 2);
v___x_1189_ = lean_alloc_ctor(1, 0, 1);
v___x_1190_ = lean_unbox(v_defValue_1186_);
lean_ctor_set_uint8(v___x_1189_, 0, v___x_1190_);
lean_inc(v_deprecation_x3f_1188_);
lean_inc_ref(v_descr_1187_);
lean_inc_n(v_name_1182_, 2);
v___x_1191_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1191_, 0, v_name_1182_);
lean_ctor_set(v___x_1191_, 1, v_ref_1184_);
lean_ctor_set(v___x_1191_, 2, v___x_1189_);
lean_ctor_set(v___x_1191_, 3, v_descr_1187_);
lean_ctor_set(v___x_1191_, 4, v_deprecation_x3f_1188_);
v___x_1192_ = lean_register_option(v_name_1182_, v___x_1191_);
if (lean_obj_tag(v___x_1192_) == 0)
{
lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1200_; 
v_isSharedCheck_1200_ = !lean_is_exclusive(v___x_1192_);
if (v_isSharedCheck_1200_ == 0)
{
lean_object* v_unused_1201_; 
v_unused_1201_ = lean_ctor_get(v___x_1192_, 0);
lean_dec(v_unused_1201_);
v___x_1194_ = v___x_1192_;
v_isShared_1195_ = v_isSharedCheck_1200_;
goto v_resetjp_1193_;
}
else
{
lean_dec(v___x_1192_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1200_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
lean_object* v___x_1196_; lean_object* v___x_1198_; 
lean_inc(v_defValue_1186_);
v___x_1196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1196_, 0, v_name_1182_);
lean_ctor_set(v___x_1196_, 1, v_defValue_1186_);
if (v_isShared_1195_ == 0)
{
lean_ctor_set(v___x_1194_, 0, v___x_1196_);
v___x_1198_ = v___x_1194_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v___x_1196_);
v___x_1198_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
return v___x_1198_;
}
}
}
else
{
lean_object* v_a_1202_; lean_object* v___x_1204_; uint8_t v_isShared_1205_; uint8_t v_isSharedCheck_1209_; 
lean_dec(v_name_1182_);
v_a_1202_ = lean_ctor_get(v___x_1192_, 0);
v_isSharedCheck_1209_ = !lean_is_exclusive(v___x_1192_);
if (v_isSharedCheck_1209_ == 0)
{
v___x_1204_ = v___x_1192_;
v_isShared_1205_ = v_isSharedCheck_1209_;
goto v_resetjp_1203_;
}
else
{
lean_inc(v_a_1202_);
lean_dec(v___x_1192_);
v___x_1204_ = lean_box(0);
v_isShared_1205_ = v_isSharedCheck_1209_;
goto v_resetjp_1203_;
}
v_resetjp_1203_:
{
lean_object* v___x_1207_; 
if (v_isShared_1205_ == 0)
{
v___x_1207_ = v___x_1204_;
goto v_reusejp_1206_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v_a_1202_);
v___x_1207_ = v_reuseFailAlloc_1208_;
goto v_reusejp_1206_;
}
v_reusejp_1206_:
{
return v___x_1207_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_1210_, lean_object* v_decl_1211_, lean_object* v_ref_1212_, lean_object* v_a_1213_){
_start:
{
lean_object* v_res_1214_; 
v_res_1214_ = l_Lean_Option_register___at___00__private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__spec__0(v_name_1210_, v_decl_1211_, v_ref_1212_);
lean_dec_ref(v_decl_1211_);
return v_res_1214_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; 
v___x_1233_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__2_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_));
v___x_1234_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__4_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_));
v___x_1235_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__6_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_));
v___x_1236_ = l_Lean_Option_register___at___00__private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__spec__0(v___x_1233_, v___x_1234_, v___x_1235_);
return v___x_1236_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4____boxed(lean_object* v_a_1237_){
_start:
{
lean_object* v_res_1238_; 
v_res_1238_ = l___private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_();
return v_res_1238_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; 
v___x_1257_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__1_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4_));
v___x_1258_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__3_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4_));
v___x_1259_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__4_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4_));
v___x_1260_ = l_Lean_Option_register___at___00__private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__spec__0(v___x_1257_, v___x_1258_, v___x_1259_);
return v___x_1260_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4____boxed(lean_object* v_a_1261_){
_start:
{
lean_object* v_res_1262_; 
v_res_1262_ = l___private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4_();
return v_res_1262_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__1(lean_object* v_opts_1263_, lean_object* v_opt_1264_){
_start:
{
lean_object* v_name_1265_; lean_object* v_defValue_1266_; lean_object* v_map_1267_; lean_object* v___x_1268_; 
v_name_1265_ = lean_ctor_get(v_opt_1264_, 0);
v_defValue_1266_ = lean_ctor_get(v_opt_1264_, 1);
v_map_1267_ = lean_ctor_get(v_opts_1263_, 0);
v___x_1268_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1267_, v_name_1265_);
if (lean_obj_tag(v___x_1268_) == 0)
{
uint8_t v___x_1269_; 
v___x_1269_ = lean_unbox(v_defValue_1266_);
return v___x_1269_;
}
else
{
lean_object* v_val_1270_; 
v_val_1270_ = lean_ctor_get(v___x_1268_, 0);
lean_inc(v_val_1270_);
lean_dec_ref_known(v___x_1268_, 1);
if (lean_obj_tag(v_val_1270_) == 1)
{
uint8_t v_v_1271_; 
v_v_1271_ = lean_ctor_get_uint8(v_val_1270_, 0);
lean_dec_ref_known(v_val_1270_, 0);
return v_v_1271_;
}
else
{
uint8_t v___x_1272_; 
lean_dec(v_val_1270_);
v___x_1272_ = lean_unbox(v_defValue_1266_);
return v___x_1272_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__1___boxed(lean_object* v_opts_1273_, lean_object* v_opt_1274_){
_start:
{
uint8_t v_res_1275_; lean_object* v_r_1276_; 
v_res_1275_ = l_Lean_Option_get___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__1(v_opts_1273_, v_opt_1274_);
lean_dec_ref(v_opt_1274_);
lean_dec_ref(v_opts_1273_);
v_r_1276_ = lean_box(v_res_1275_);
return v_r_1276_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0(lean_object* v_declName_1280_, lean_object* v_env_1281_, lean_object* v_as_1282_, size_t v_sz_1283_, size_t v_i_1284_, lean_object* v_b_1285_){
_start:
{
uint8_t v___x_1286_; 
v___x_1286_ = lean_usize_dec_lt(v_i_1284_, v_sz_1283_);
if (v___x_1286_ == 0)
{
lean_dec_ref(v_env_1281_);
lean_dec(v_declName_1280_);
lean_inc_ref(v_b_1285_);
return v_b_1285_;
}
else
{
lean_object* v_a_1287_; lean_object* v_toImport_1288_; lean_object* v_module_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; uint8_t v___x_1292_; 
v_a_1287_ = lean_array_uget_borrowed(v_as_1282_, v_i_1284_);
v_toImport_1288_ = lean_ctor_get(v_a_1287_, 0);
v_module_1289_ = lean_ctor_get(v_toImport_1288_, 0);
v___x_1290_ = lean_box(0);
lean_inc(v_declName_1280_);
lean_inc(v_module_1289_);
v___x_1291_ = l_Lean_mkPrivateNameCore(v_module_1289_, v_declName_1280_);
lean_inc(v___x_1291_);
lean_inc_ref(v_env_1281_);
v___x_1292_ = l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(v_env_1281_, v___x_1291_);
if (v___x_1292_ == 0)
{
lean_object* v___x_1293_; size_t v___x_1294_; size_t v___x_1295_; 
lean_dec(v___x_1291_);
v___x_1293_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0___closed__0));
v___x_1294_ = ((size_t)1ULL);
v___x_1295_ = lean_usize_add(v_i_1284_, v___x_1294_);
v_i_1284_ = v___x_1295_;
v_b_1285_ = v___x_1293_;
goto _start;
}
else
{
lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; 
lean_dec_ref(v_env_1281_);
lean_dec(v_declName_1280_);
v___x_1297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1297_, 0, v___x_1291_);
v___x_1298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1298_, 0, v___x_1297_);
v___x_1299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1299_, 0, v___x_1298_);
lean_ctor_set(v___x_1299_, 1, v___x_1290_);
return v___x_1299_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0___boxed(lean_object* v_declName_1300_, lean_object* v_env_1301_, lean_object* v_as_1302_, lean_object* v_sz_1303_, lean_object* v_i_1304_, lean_object* v_b_1305_){
_start:
{
size_t v_sz_boxed_1306_; size_t v_i_boxed_1307_; lean_object* v_res_1308_; 
v_sz_boxed_1306_ = lean_unbox_usize(v_sz_1303_);
lean_dec(v_sz_1303_);
v_i_boxed_1307_ = lean_unbox_usize(v_i_1304_);
lean_dec(v_i_1304_);
v_res_1308_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0(v_declName_1300_, v_env_1301_, v_as_1302_, v_sz_boxed_1306_, v_i_boxed_1307_, v_b_1305_);
lean_dec_ref(v_b_1305_);
lean_dec_ref(v_as_1302_);
return v_res_1308_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName(lean_object* v_env_1309_, lean_object* v_opts_1310_, lean_object* v_declName_1311_){
_start:
{
uint8_t v_isExporting_1327_; 
v_isExporting_1327_ = lean_ctor_get_uint8(v_env_1309_, sizeof(void*)*8);
if (v_isExporting_1327_ == 0)
{
goto v___jp_1312_;
}
else
{
lean_object* v___x_1328_; uint8_t v___x_1329_; 
v___x_1328_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_1329_ = l_Lean_Option_get___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__1(v_opts_1310_, v___x_1328_);
if (v___x_1329_ == 0)
{
lean_object* v___x_1330_; 
lean_dec(v_declName_1311_);
lean_dec_ref(v_env_1309_);
v___x_1330_ = lean_box(0);
return v___x_1330_;
}
else
{
goto v___jp_1312_;
}
}
v___jp_1312_:
{
lean_object* v___x_1313_; uint8_t v___x_1314_; 
lean_inc(v_declName_1311_);
v___x_1313_ = l_Lean_mkPrivateName(v_env_1309_, v_declName_1311_);
lean_inc(v___x_1313_);
lean_inc_ref(v_env_1309_);
v___x_1314_ = l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(v_env_1309_, v___x_1313_);
if (v___x_1314_ == 0)
{
lean_object* v___x_1315_; uint8_t v_isModule_1316_; 
lean_dec(v___x_1313_);
v___x_1315_ = l_Lean_Environment_header(v_env_1309_);
v_isModule_1316_ = lean_ctor_get_uint8(v___x_1315_, sizeof(void*)*7 + 4);
if (v_isModule_1316_ == 0)
{
lean_object* v___x_1317_; 
lean_dec_ref(v___x_1315_);
lean_dec(v_declName_1311_);
lean_dec_ref(v_env_1309_);
v___x_1317_ = lean_box(0);
return v___x_1317_;
}
else
{
lean_object* v_importAllModules_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; size_t v_sz_1321_; size_t v___x_1322_; lean_object* v___x_1323_; lean_object* v_fst_1324_; 
v_importAllModules_1318_ = lean_ctor_get(v___x_1315_, 5);
lean_inc_ref(v_importAllModules_1318_);
lean_dec_ref(v___x_1315_);
v___x_1319_ = lean_box(0);
v___x_1320_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0___closed__0));
v_sz_1321_ = lean_array_size(v_importAllModules_1318_);
v___x_1322_ = ((size_t)0ULL);
v___x_1323_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0(v_declName_1311_, v_env_1309_, v_importAllModules_1318_, v_sz_1321_, v___x_1322_, v___x_1320_);
lean_dec_ref(v_importAllModules_1318_);
v_fst_1324_ = lean_ctor_get(v___x_1323_, 0);
lean_inc(v_fst_1324_);
lean_dec_ref(v___x_1323_);
if (lean_obj_tag(v_fst_1324_) == 0)
{
return v___x_1319_;
}
else
{
lean_object* v_val_1325_; 
v_val_1325_ = lean_ctor_get(v_fst_1324_, 0);
lean_inc(v_val_1325_);
lean_dec_ref_known(v_fst_1324_, 1);
return v_val_1325_;
}
}
}
else
{
lean_object* v___x_1326_; 
lean_dec(v_declName_1311_);
lean_dec_ref(v_env_1309_);
v___x_1326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1326_, 0, v___x_1313_);
return v___x_1326_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName___boxed(lean_object* v_env_1331_, lean_object* v_opts_1332_, lean_object* v_declName_1333_){
_start:
{
lean_object* v_res_1334_; 
v_res_1334_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName(v_env_1331_, v_opts_1332_, v_declName_1333_);
lean_dec_ref(v_opts_1332_);
return v_res_1334_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveQualifiedName(lean_object* v_env_1335_, lean_object* v_opts_1336_, lean_object* v_ns_1337_, lean_object* v_id_1338_){
_start:
{
lean_object* v_resolvedId_1339_; uint8_t v___x_1340_; lean_object* v_resolvedIds_1341_; 
lean_inc(v_id_1338_);
v_resolvedId_1339_ = l_Lean_Name_append(v_ns_1337_, v_id_1338_);
v___x_1340_ = l_Lean_Name_isAtomic(v_id_1338_);
lean_dec(v_id_1338_);
lean_inc_ref(v_env_1335_);
v_resolvedIds_1341_ = l_Lean_getAliases(v_env_1335_, v_resolvedId_1339_, v___x_1340_);
if (v___x_1340_ == 0)
{
goto v___jp_1342_;
}
else
{
uint8_t v___x_1348_; 
lean_inc(v_resolvedId_1339_);
lean_inc_ref(v_env_1335_);
v___x_1348_ = l_Lean_isProtected(v_env_1335_, v_resolvedId_1339_);
if (v___x_1348_ == 0)
{
goto v___jp_1342_;
}
else
{
lean_dec(v_resolvedId_1339_);
lean_dec_ref(v_env_1335_);
return v_resolvedIds_1341_;
}
}
v___jp_1342_:
{
uint8_t v___x_1343_; 
lean_inc(v_resolvedId_1339_);
lean_inc_ref(v_env_1335_);
v___x_1343_ = l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(v_env_1335_, v_resolvedId_1339_);
if (v___x_1343_ == 0)
{
lean_object* v___x_1344_; 
v___x_1344_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName(v_env_1335_, v_opts_1336_, v_resolvedId_1339_);
if (lean_obj_tag(v___x_1344_) == 1)
{
lean_object* v_val_1345_; lean_object* v___x_1346_; 
v_val_1345_ = lean_ctor_get(v___x_1344_, 0);
lean_inc(v_val_1345_);
lean_dec_ref_known(v___x_1344_, 1);
v___x_1346_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1346_, 0, v_val_1345_);
lean_ctor_set(v___x_1346_, 1, v_resolvedIds_1341_);
return v___x_1346_;
}
else
{
lean_dec(v___x_1344_);
return v_resolvedIds_1341_;
}
}
else
{
lean_object* v___x_1347_; 
lean_dec_ref(v_env_1335_);
v___x_1347_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1347_, 0, v_resolvedId_1339_);
lean_ctor_set(v___x_1347_, 1, v_resolvedIds_1341_);
return v___x_1347_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveQualifiedName___boxed(lean_object* v_env_1349_, lean_object* v_opts_1350_, lean_object* v_ns_1351_, lean_object* v_id_1352_){
_start:
{
lean_object* v_res_1353_; 
v_res_1353_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveQualifiedName(v_env_1349_, v_opts_1350_, v_ns_1351_, v_id_1352_);
lean_dec_ref(v_opts_1350_);
return v_res_1353_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveUsingNamespace(lean_object* v_env_1354_, lean_object* v_opts_1355_, lean_object* v_id_1356_, lean_object* v_x_1357_){
_start:
{
if (lean_obj_tag(v_x_1357_) == 1)
{
lean_object* v_pre_1358_; lean_object* v___x_1359_; 
v_pre_1358_ = lean_ctor_get(v_x_1357_, 0);
lean_inc(v_pre_1358_);
lean_inc(v_id_1356_);
lean_inc_ref(v_env_1354_);
v___x_1359_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveQualifiedName(v_env_1354_, v_opts_1355_, v_x_1357_, v_id_1356_);
if (lean_obj_tag(v___x_1359_) == 0)
{
v_x_1357_ = v_pre_1358_;
goto _start;
}
else
{
lean_dec(v_pre_1358_);
lean_dec(v_id_1356_);
lean_dec_ref(v_env_1354_);
return v___x_1359_;
}
}
else
{
lean_object* v___x_1361_; 
lean_dec(v_x_1357_);
lean_dec(v_id_1356_);
lean_dec_ref(v_env_1354_);
v___x_1361_ = lean_box(0);
return v___x_1361_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveUsingNamespace___boxed(lean_object* v_env_1362_, lean_object* v_opts_1363_, lean_object* v_id_1364_, lean_object* v_x_1365_){
_start:
{
lean_object* v_res_1366_; 
v_res_1366_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveUsingNamespace(v_env_1362_, v_opts_1363_, v_id_1364_, v_x_1365_);
lean_dec_ref(v_opts_1363_);
return v_res_1366_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveExact(lean_object* v_env_1367_, lean_object* v_opts_1368_, lean_object* v_id_1369_){
_start:
{
uint8_t v___x_1370_; 
v___x_1370_ = l_Lean_Name_isAtomic(v_id_1369_);
if (v___x_1370_ == 0)
{
lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v_resolvedId_1373_; uint8_t v___x_1374_; 
v___x_1371_ = l_Lean_rootNamespace;
v___x_1372_ = lean_box(0);
v_resolvedId_1373_ = l_Lean_Name_replacePrefix(v_id_1369_, v___x_1371_, v___x_1372_);
lean_inc(v_resolvedId_1373_);
lean_inc_ref(v_env_1367_);
v___x_1374_ = l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(v_env_1367_, v_resolvedId_1373_);
if (v___x_1374_ == 0)
{
lean_object* v___x_1375_; 
v___x_1375_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName(v_env_1367_, v_opts_1368_, v_resolvedId_1373_);
return v___x_1375_;
}
else
{
lean_object* v___x_1376_; 
lean_dec_ref(v_env_1367_);
v___x_1376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1376_, 0, v_resolvedId_1373_);
return v___x_1376_;
}
}
else
{
lean_object* v___x_1377_; 
lean_dec(v_id_1369_);
lean_dec_ref(v_env_1367_);
v___x_1377_ = lean_box(0);
return v___x_1377_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveExact___boxed(lean_object* v_env_1378_, lean_object* v_opts_1379_, lean_object* v_id_1380_){
_start:
{
lean_object* v_res_1381_; 
v_res_1381_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveExact(v_env_1378_, v_opts_1379_, v_id_1380_);
lean_dec_ref(v_opts_1379_);
return v_res_1381_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveOpenDecls(lean_object* v_env_1382_, lean_object* v_opts_1383_, lean_object* v_id_1384_, lean_object* v_x_1385_, lean_object* v_x_1386_){
_start:
{
if (lean_obj_tag(v_x_1385_) == 0)
{
lean_dec(v_id_1384_);
lean_dec_ref(v_env_1382_);
return v_x_1386_;
}
else
{
lean_object* v_head_1387_; 
v_head_1387_ = lean_ctor_get(v_x_1385_, 0);
lean_inc(v_head_1387_);
if (lean_obj_tag(v_head_1387_) == 0)
{
lean_object* v_tail_1388_; lean_object* v_ns_1389_; lean_object* v_except_1390_; uint8_t v___x_1391_; 
v_tail_1388_ = lean_ctor_get(v_x_1385_, 1);
lean_inc(v_tail_1388_);
lean_dec_ref_known(v_x_1385_, 2);
v_ns_1389_ = lean_ctor_get(v_head_1387_, 0);
lean_inc(v_ns_1389_);
v_except_1390_ = lean_ctor_get(v_head_1387_, 1);
lean_inc(v_except_1390_);
lean_dec_ref_known(v_head_1387_, 2);
v___x_1391_ = l_List_elem___at___00Lean_addAliasEntry_spec__2(v_id_1384_, v_except_1390_);
lean_dec(v_except_1390_);
if (v___x_1391_ == 0)
{
lean_object* v_newResolvedIds_1392_; lean_object* v___x_1393_; 
lean_inc(v_id_1384_);
lean_inc_ref(v_env_1382_);
v_newResolvedIds_1392_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveQualifiedName(v_env_1382_, v_opts_1383_, v_ns_1389_, v_id_1384_);
v___x_1393_ = l_List_appendTR___redArg(v_newResolvedIds_1392_, v_x_1386_);
v_x_1385_ = v_tail_1388_;
v_x_1386_ = v___x_1393_;
goto _start;
}
else
{
lean_dec(v_ns_1389_);
v_x_1385_ = v_tail_1388_;
goto _start;
}
}
else
{
lean_object* v_tail_1396_; lean_object* v___x_1398_; uint8_t v_isShared_1399_; uint8_t v_isSharedCheck_1416_; 
v_tail_1396_ = lean_ctor_get(v_x_1385_, 1);
v_isSharedCheck_1416_ = !lean_is_exclusive(v_x_1385_);
if (v_isSharedCheck_1416_ == 0)
{
lean_object* v_unused_1417_; 
v_unused_1417_ = lean_ctor_get(v_x_1385_, 0);
lean_dec(v_unused_1417_);
v___x_1398_ = v_x_1385_;
v_isShared_1399_ = v_isSharedCheck_1416_;
goto v_resetjp_1397_;
}
else
{
lean_inc(v_tail_1396_);
lean_dec(v_x_1385_);
v___x_1398_ = lean_box(0);
v_isShared_1399_ = v_isSharedCheck_1416_;
goto v_resetjp_1397_;
}
v_resetjp_1397_:
{
lean_object* v_id_1400_; lean_object* v_declName_1401_; uint8_t v___x_1402_; 
v_id_1400_ = lean_ctor_get(v_head_1387_, 0);
lean_inc(v_id_1400_);
v_declName_1401_ = lean_ctor_get(v_head_1387_, 1);
lean_inc(v_declName_1401_);
lean_dec_ref_known(v_head_1387_, 2);
v___x_1402_ = lean_name_eq(v_id_1400_, v_id_1384_);
if (v___x_1402_ == 0)
{
uint8_t v___x_1403_; 
v___x_1403_ = l_Lean_Name_isPrefixOf(v_id_1400_, v_id_1384_);
if (v___x_1403_ == 0)
{
lean_dec(v_declName_1401_);
lean_dec(v_id_1400_);
lean_del_object(v___x_1398_);
v_x_1385_ = v_tail_1396_;
goto _start;
}
else
{
lean_object* v_candidate_1405_; uint8_t v___x_1406_; 
lean_inc(v_id_1384_);
v_candidate_1405_ = l_Lean_Name_replacePrefix(v_id_1384_, v_id_1400_, v_declName_1401_);
lean_dec(v_declName_1401_);
lean_dec(v_id_1400_);
lean_inc(v_candidate_1405_);
lean_inc_ref(v_env_1382_);
v___x_1406_ = l_Lean_Environment_contains(v_env_1382_, v_candidate_1405_, v___x_1403_);
if (v___x_1406_ == 0)
{
lean_dec(v_candidate_1405_);
lean_del_object(v___x_1398_);
v_x_1385_ = v_tail_1396_;
goto _start;
}
else
{
lean_object* v___x_1409_; 
if (v_isShared_1399_ == 0)
{
lean_ctor_set(v___x_1398_, 1, v_x_1386_);
lean_ctor_set(v___x_1398_, 0, v_candidate_1405_);
v___x_1409_ = v___x_1398_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v_candidate_1405_);
lean_ctor_set(v_reuseFailAlloc_1411_, 1, v_x_1386_);
v___x_1409_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
v_x_1385_ = v_tail_1396_;
v_x_1386_ = v___x_1409_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_1413_; 
lean_dec(v_id_1400_);
if (v_isShared_1399_ == 0)
{
lean_ctor_set(v___x_1398_, 1, v_x_1386_);
lean_ctor_set(v___x_1398_, 0, v_declName_1401_);
v___x_1413_ = v___x_1398_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v_declName_1401_);
lean_ctor_set(v_reuseFailAlloc_1415_, 1, v_x_1386_);
v___x_1413_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
v_x_1385_ = v_tail_1396_;
v_x_1386_ = v___x_1413_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveOpenDecls___boxed(lean_object* v_env_1418_, lean_object* v_opts_1419_, lean_object* v_id_1420_, lean_object* v_x_1421_, lean_object* v_x_1422_){
_start:
{
lean_object* v_res_1423_; 
v_res_1423_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveOpenDecls(v_env_1418_, v_opts_1419_, v_id_1420_, v_x_1421_, v_x_1422_);
lean_dec_ref(v_opts_1419_);
return v_res_1423_;
}
}
LEAN_EXPORT lean_object* l_List_eraseDups___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__0(lean_object* v_as_1425_){
_start:
{
lean_object* v___f_1426_; lean_object* v___x_1427_; 
v___f_1426_ = ((lean_object*)(l_List_eraseDups___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__0___closed__0));
v___x_1427_ = l_List_eraseDupsBy___redArg(v___f_1426_, v_as_1425_);
return v___x_1427_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__1(lean_object* v_projs_1428_, lean_object* v_a_1429_, lean_object* v_a_1430_){
_start:
{
if (lean_obj_tag(v_a_1429_) == 0)
{
lean_object* v___x_1431_; 
lean_dec(v_projs_1428_);
v___x_1431_ = l_List_reverse___redArg(v_a_1430_);
return v___x_1431_;
}
else
{
lean_object* v_head_1432_; lean_object* v_tail_1433_; lean_object* v___x_1435_; uint8_t v_isShared_1436_; uint8_t v_isSharedCheck_1442_; 
v_head_1432_ = lean_ctor_get(v_a_1429_, 0);
v_tail_1433_ = lean_ctor_get(v_a_1429_, 1);
v_isSharedCheck_1442_ = !lean_is_exclusive(v_a_1429_);
if (v_isSharedCheck_1442_ == 0)
{
v___x_1435_ = v_a_1429_;
v_isShared_1436_ = v_isSharedCheck_1442_;
goto v_resetjp_1434_;
}
else
{
lean_inc(v_tail_1433_);
lean_inc(v_head_1432_);
lean_dec(v_a_1429_);
v___x_1435_ = lean_box(0);
v_isShared_1436_ = v_isSharedCheck_1442_;
goto v_resetjp_1434_;
}
v_resetjp_1434_:
{
lean_object* v___x_1437_; lean_object* v___x_1439_; 
lean_inc(v_projs_1428_);
v___x_1437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1437_, 0, v_head_1432_);
lean_ctor_set(v___x_1437_, 1, v_projs_1428_);
if (v_isShared_1436_ == 0)
{
lean_ctor_set(v___x_1435_, 1, v_a_1430_);
lean_ctor_set(v___x_1435_, 0, v___x_1437_);
v___x_1439_ = v___x_1435_;
goto v_reusejp_1438_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v___x_1437_);
lean_ctor_set(v_reuseFailAlloc_1441_, 1, v_a_1430_);
v___x_1439_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1438_;
}
v_reusejp_1438_:
{
v_a_1429_ = v_tail_1433_;
v_a_1430_ = v___x_1439_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop(lean_object* v_env_1443_, lean_object* v_opts_1444_, lean_object* v_ns_1445_, lean_object* v_openDecls_1446_, lean_object* v_extractionResult_1447_, lean_object* v_id_1448_, lean_object* v_projs_1449_){
_start:
{
if (lean_obj_tag(v_id_1448_) == 1)
{
lean_object* v_pre_1450_; lean_object* v_str_1451_; lean_object* v_imported_1452_; lean_object* v_ctx_1453_; lean_object* v_scopes_1454_; lean_object* v___x_1455_; lean_object* v_id_1456_; lean_object* v___y_1458_; lean_object* v___x_1468_; lean_object* v___y_1470_; 
v_pre_1450_ = lean_ctor_get(v_id_1448_, 0);
lean_inc(v_pre_1450_);
v_str_1451_ = lean_ctor_get(v_id_1448_, 1);
lean_inc_ref(v_str_1451_);
v_imported_1452_ = lean_ctor_get(v_extractionResult_1447_, 1);
v_ctx_1453_ = lean_ctor_get(v_extractionResult_1447_, 2);
v_scopes_1454_ = lean_ctor_get(v_extractionResult_1447_, 3);
lean_inc(v_scopes_1454_);
lean_inc(v_ctx_1453_);
lean_inc(v_imported_1452_);
v___x_1455_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1455_, 0, v_id_1448_);
lean_ctor_set(v___x_1455_, 1, v_imported_1452_);
lean_ctor_set(v___x_1455_, 2, v_ctx_1453_);
lean_ctor_set(v___x_1455_, 3, v_scopes_1454_);
v_id_1456_ = l_Lean_MacroScopesView_review(v___x_1455_);
lean_inc(v_ns_1445_);
lean_inc(v_id_1456_);
lean_inc_ref(v_env_1443_);
v___x_1468_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveUsingNamespace(v_env_1443_, v_opts_1444_, v_id_1456_, v_ns_1445_);
if (lean_obj_tag(v___x_1468_) == 0)
{
lean_object* v___x_1475_; 
lean_inc(v_id_1456_);
lean_inc_ref(v_env_1443_);
v___x_1475_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveExact(v_env_1443_, v_opts_1444_, v_id_1456_);
if (lean_obj_tag(v___x_1475_) == 0)
{
uint8_t v___x_1476_; 
lean_inc(v_id_1456_);
lean_inc_ref(v_env_1443_);
v___x_1476_ = l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(v_env_1443_, v_id_1456_);
if (v___x_1476_ == 0)
{
v___y_1470_ = v___x_1468_;
goto v___jp_1469_;
}
else
{
lean_object* v___x_1477_; 
lean_inc(v_id_1456_);
v___x_1477_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1477_, 0, v_id_1456_);
lean_ctor_set(v___x_1477_, 1, v___x_1468_);
v___y_1470_ = v___x_1477_;
goto v___jp_1469_;
}
}
else
{
lean_object* v_val_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; 
lean_dec(v_id_1456_);
lean_dec_ref(v_str_1451_);
lean_dec(v_pre_1450_);
lean_dec(v_openDecls_1446_);
lean_dec(v_ns_1445_);
lean_dec_ref(v_env_1443_);
v_val_1478_ = lean_ctor_get(v___x_1475_, 0);
lean_inc(v_val_1478_);
lean_dec_ref_known(v___x_1475_, 1);
v___x_1479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1479_, 0, v_val_1478_);
lean_ctor_set(v___x_1479_, 1, v_projs_1449_);
v___x_1480_ = lean_box(0);
v___x_1481_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1481_, 0, v___x_1479_);
lean_ctor_set(v___x_1481_, 1, v___x_1480_);
return v___x_1481_;
}
}
else
{
lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; 
lean_dec(v_id_1456_);
lean_dec_ref(v_str_1451_);
lean_dec(v_pre_1450_);
lean_dec(v_openDecls_1446_);
lean_dec(v_ns_1445_);
lean_dec_ref(v_env_1443_);
v___x_1482_ = l_List_eraseDups___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__0(v___x_1468_);
v___x_1483_ = lean_box(0);
v___x_1484_ = l_List_mapTR_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__1(v_projs_1449_, v___x_1482_, v___x_1483_);
return v___x_1484_;
}
v___jp_1457_:
{
lean_object* v_resolvedIds_1459_; uint8_t v___x_1460_; lean_object* v___x_1461_; lean_object* v_resolvedIds_1462_; 
lean_inc(v_openDecls_1446_);
lean_inc(v_id_1456_);
lean_inc_ref_n(v_env_1443_, 2);
v_resolvedIds_1459_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveOpenDecls(v_env_1443_, v_opts_1444_, v_id_1456_, v_openDecls_1446_, v___y_1458_);
v___x_1460_ = l_Lean_Name_isAtomic(v_id_1456_);
v___x_1461_ = l_Lean_getAliases(v_env_1443_, v_id_1456_, v___x_1460_);
lean_dec(v_id_1456_);
v_resolvedIds_1462_ = l_List_appendTR___redArg(v___x_1461_, v_resolvedIds_1459_);
if (lean_obj_tag(v_resolvedIds_1462_) == 0)
{
lean_object* v___x_1463_; 
v___x_1463_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1463_, 0, v_str_1451_);
lean_ctor_set(v___x_1463_, 1, v_projs_1449_);
v_id_1448_ = v_pre_1450_;
v_projs_1449_ = v___x_1463_;
goto _start;
}
else
{
lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; 
lean_dec_ref(v_str_1451_);
lean_dec(v_pre_1450_);
lean_dec(v_openDecls_1446_);
lean_dec(v_ns_1445_);
lean_dec_ref(v_env_1443_);
v___x_1465_ = l_List_eraseDups___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__0(v_resolvedIds_1462_);
v___x_1466_ = lean_box(0);
v___x_1467_ = l_List_mapTR_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__1(v_projs_1449_, v___x_1465_, v___x_1466_);
return v___x_1467_;
}
}
v___jp_1469_:
{
lean_object* v___x_1471_; 
lean_inc(v_id_1456_);
lean_inc_ref(v_env_1443_);
v___x_1471_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName(v_env_1443_, v_opts_1444_, v_id_1456_);
if (lean_obj_tag(v___x_1471_) == 1)
{
lean_object* v_val_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; 
v_val_1472_ = lean_ctor_get(v___x_1471_, 0);
lean_inc(v_val_1472_);
lean_dec_ref_known(v___x_1471_, 1);
v___x_1473_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1473_, 0, v_val_1472_);
lean_ctor_set(v___x_1473_, 1, v___x_1468_);
v___x_1474_ = l_List_appendTR___redArg(v___x_1473_, v___y_1470_);
v___y_1458_ = v___x_1474_;
goto v___jp_1457_;
}
else
{
lean_dec(v___x_1471_);
lean_dec(v___x_1468_);
v___y_1458_ = v___y_1470_;
goto v___jp_1457_;
}
}
}
else
{
lean_object* v___x_1485_; 
lean_dec(v_projs_1449_);
lean_dec(v_id_1448_);
lean_dec(v_openDecls_1446_);
lean_dec(v_ns_1445_);
lean_dec_ref(v_env_1443_);
v___x_1485_ = lean_box(0);
return v___x_1485_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop___boxed(lean_object* v_env_1486_, lean_object* v_opts_1487_, lean_object* v_ns_1488_, lean_object* v_openDecls_1489_, lean_object* v_extractionResult_1490_, lean_object* v_id_1491_, lean_object* v_projs_1492_){
_start:
{
lean_object* v_res_1493_; 
v_res_1493_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop(v_env_1486_, v_opts_1487_, v_ns_1488_, v_openDecls_1489_, v_extractionResult_1490_, v_id_1491_, v_projs_1492_);
lean_dec_ref(v_extractionResult_1490_);
lean_dec_ref(v_opts_1487_);
return v_res_1493_;
}
}
LEAN_EXPORT lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object* v_env_1494_, lean_object* v_opts_1495_, lean_object* v_ns_1496_, lean_object* v_openDecls_1497_, lean_object* v_id_1498_){
_start:
{
lean_object* v_extractionResult_1499_; lean_object* v_name_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; 
v_extractionResult_1499_ = l_Lean_extractMacroScopes(v_id_1498_);
v_name_1500_ = lean_ctor_get(v_extractionResult_1499_, 0);
lean_inc(v_name_1500_);
v___x_1501_ = lean_box(0);
v___x_1502_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop(v_env_1494_, v_opts_1495_, v_ns_1496_, v_openDecls_1497_, v_extractionResult_1499_, v_name_1500_, v___x_1501_);
lean_dec_ref(v_extractionResult_1499_);
return v___x_1502_;
}
}
LEAN_EXPORT lean_object* l_Lean_ResolveName_resolveGlobalName___boxed(lean_object* v_env_1503_, lean_object* v_opts_1504_, lean_object* v_ns_1505_, lean_object* v_openDecls_1506_, lean_object* v_id_1507_){
_start:
{
lean_object* v_res_1508_; 
v_res_1508_ = l_Lean_ResolveName_resolveGlobalName(v_env_1503_, v_opts_1504_, v_ns_1505_, v_openDecls_1506_, v_id_1507_);
lean_dec_ref(v_opts_1504_);
return v_res_1508_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_ResolveName_resolveNamespaceUsingScope_x3f_spec__0(lean_object* v_msg_1509_){
_start:
{
lean_object* v___x_1510_; lean_object* v___x_1511_; 
v___x_1510_ = lean_box(0);
v___x_1511_ = lean_panic_fn_borrowed(v___x_1510_, v_msg_1509_);
return v___x_1511_;
}
}
static lean_object* _init_l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__3(void){
_start:
{
lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; 
v___x_1515_ = ((lean_object*)(l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__2));
v___x_1516_ = lean_unsigned_to_nat(9u);
v___x_1517_ = lean_unsigned_to_nat(230u);
v___x_1518_ = ((lean_object*)(l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__1));
v___x_1519_ = ((lean_object*)(l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__0));
v___x_1520_ = l_mkPanicMessageWithDecl(v___x_1519_, v___x_1518_, v___x_1517_, v___x_1516_, v___x_1515_);
return v___x_1520_;
}
}
LEAN_EXPORT lean_object* l_Lean_ResolveName_resolveNamespaceUsingScope_x3f(lean_object* v_env_1521_, lean_object* v_n_1522_, lean_object* v_ns_1523_){
_start:
{
switch(lean_obj_tag(v_ns_1523_))
{
case 1:
{
lean_object* v_pre_1524_; lean_object* v___x_1525_; uint8_t v___x_1526_; 
v_pre_1524_ = lean_ctor_get(v_ns_1523_, 0);
lean_inc(v_pre_1524_);
lean_inc(v_n_1522_);
v___x_1525_ = l_Lean_Name_append(v_ns_1523_, v_n_1522_);
lean_inc_ref(v_env_1521_);
v___x_1526_ = l_Lean_Environment_isNamespace(v_env_1521_, v___x_1525_);
if (v___x_1526_ == 0)
{
lean_dec(v___x_1525_);
v_ns_1523_ = v_pre_1524_;
goto _start;
}
else
{
lean_object* v___x_1528_; 
lean_dec(v_pre_1524_);
lean_dec(v_n_1522_);
lean_dec_ref(v_env_1521_);
v___x_1528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1528_, 0, v___x_1525_);
return v___x_1528_;
}
}
case 0:
{
lean_object* v___x_1529_; lean_object* v_n_1530_; uint8_t v___x_1531_; 
v___x_1529_ = l_Lean_rootNamespace;
v_n_1530_ = l_Lean_Name_replacePrefix(v_n_1522_, v___x_1529_, v_ns_1523_);
v___x_1531_ = l_Lean_Environment_isNamespace(v_env_1521_, v_n_1530_);
if (v___x_1531_ == 0)
{
lean_object* v___x_1532_; 
lean_dec(v_n_1530_);
v___x_1532_ = lean_box(0);
return v___x_1532_;
}
else
{
lean_object* v___x_1533_; 
v___x_1533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1533_, 0, v_n_1530_);
return v___x_1533_;
}
}
default: 
{
lean_object* v___x_1534_; lean_object* v___x_1535_; 
lean_dec(v_ns_1523_);
lean_dec(v_n_1522_);
lean_dec_ref(v_env_1521_);
v___x_1534_ = lean_obj_once(&l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__3, &l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__3_once, _init_l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__3);
v___x_1535_ = l_panic___at___00Lean_ResolveName_resolveNamespaceUsingScope_x3f_spec__0(v___x_1534_);
return v___x_1535_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ResolveName_resolveNamespaceUsingOpenDecls(lean_object* v_env_1536_, lean_object* v_n_1537_, lean_object* v_x_1538_){
_start:
{
if (lean_obj_tag(v_x_1538_) == 0)
{
lean_object* v___x_1539_; 
lean_dec(v_n_1537_);
lean_dec_ref(v_env_1536_);
v___x_1539_ = lean_box(0);
return v___x_1539_;
}
else
{
lean_object* v_head_1540_; 
v_head_1540_ = lean_ctor_get(v_x_1538_, 0);
if (lean_obj_tag(v_head_1540_) == 0)
{
lean_object* v_tail_1541_; lean_object* v___x_1543_; uint8_t v_isShared_1544_; uint8_t v_isSharedCheck_1558_; 
lean_inc_ref(v_head_1540_);
v_tail_1541_ = lean_ctor_get(v_x_1538_, 1);
v_isSharedCheck_1558_ = !lean_is_exclusive(v_x_1538_);
if (v_isSharedCheck_1558_ == 0)
{
lean_object* v_unused_1559_; 
v_unused_1559_ = lean_ctor_get(v_x_1538_, 0);
lean_dec(v_unused_1559_);
v___x_1543_ = v_x_1538_;
v_isShared_1544_ = v_isSharedCheck_1558_;
goto v_resetjp_1542_;
}
else
{
lean_inc(v_tail_1541_);
lean_dec(v_x_1538_);
v___x_1543_ = lean_box(0);
v_isShared_1544_ = v_isSharedCheck_1558_;
goto v_resetjp_1542_;
}
v_resetjp_1542_:
{
lean_object* v_ns_1545_; lean_object* v_except_1546_; lean_object* v___x_1547_; uint8_t v___y_1549_; uint8_t v___x_1555_; 
v_ns_1545_ = lean_ctor_get(v_head_1540_, 0);
lean_inc(v_ns_1545_);
v_except_1546_ = lean_ctor_get(v_head_1540_, 1);
lean_inc(v_except_1546_);
lean_dec_ref_known(v_head_1540_, 2);
lean_inc(v_n_1537_);
v___x_1547_ = l_Lean_Name_append(v_ns_1545_, v_n_1537_);
lean_inc_ref(v_env_1536_);
v___x_1555_ = l_Lean_Environment_isNamespace(v_env_1536_, v___x_1547_);
if (v___x_1555_ == 0)
{
lean_dec(v_except_1546_);
v___y_1549_ = v___x_1555_;
goto v___jp_1548_;
}
else
{
uint8_t v___x_1556_; 
v___x_1556_ = l_List_elem___at___00Lean_addAliasEntry_spec__2(v_n_1537_, v_except_1546_);
lean_dec(v_except_1546_);
if (v___x_1556_ == 0)
{
v___y_1549_ = v___x_1555_;
goto v___jp_1548_;
}
else
{
lean_dec(v___x_1547_);
lean_del_object(v___x_1543_);
v_x_1538_ = v_tail_1541_;
goto _start;
}
}
v___jp_1548_:
{
if (v___y_1549_ == 0)
{
lean_dec(v___x_1547_);
lean_del_object(v___x_1543_);
v_x_1538_ = v_tail_1541_;
goto _start;
}
else
{
lean_object* v___x_1551_; lean_object* v___x_1553_; 
v___x_1551_ = l_Lean_ResolveName_resolveNamespaceUsingOpenDecls(v_env_1536_, v_n_1537_, v_tail_1541_);
if (v_isShared_1544_ == 0)
{
lean_ctor_set(v___x_1543_, 1, v___x_1551_);
lean_ctor_set(v___x_1543_, 0, v___x_1547_);
v___x_1553_ = v___x_1543_;
goto v_reusejp_1552_;
}
else
{
lean_object* v_reuseFailAlloc_1554_; 
v_reuseFailAlloc_1554_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1554_, 0, v___x_1547_);
lean_ctor_set(v_reuseFailAlloc_1554_, 1, v___x_1551_);
v___x_1553_ = v_reuseFailAlloc_1554_;
goto v_reusejp_1552_;
}
v_reusejp_1552_:
{
return v___x_1553_;
}
}
}
}
}
else
{
lean_object* v_tail_1560_; 
v_tail_1560_ = lean_ctor_get(v_x_1538_, 1);
lean_inc(v_tail_1560_);
lean_dec_ref_known(v_x_1538_, 2);
v_x_1538_ = v_tail_1560_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ResolveName_resolveNamespace(lean_object* v_env_1562_, lean_object* v_ns_1563_, lean_object* v_openDecls_1564_, lean_object* v_id_1565_){
_start:
{
lean_object* v___x_1566_; 
lean_inc(v_id_1565_);
lean_inc_ref(v_env_1562_);
v___x_1566_ = l_Lean_ResolveName_resolveNamespaceUsingScope_x3f(v_env_1562_, v_id_1565_, v_ns_1563_);
if (lean_obj_tag(v___x_1566_) == 0)
{
lean_object* v___x_1567_; 
v___x_1567_ = l_Lean_ResolveName_resolveNamespaceUsingOpenDecls(v_env_1562_, v_id_1565_, v_openDecls_1564_);
return v___x_1567_;
}
else
{
lean_object* v_val_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; 
v_val_1568_ = lean_ctor_get(v___x_1566_, 0);
lean_inc(v_val_1568_);
lean_dec_ref_known(v___x_1566_, 1);
v___x_1569_ = l_Lean_ResolveName_resolveNamespaceUsingOpenDecls(v_env_1562_, v_id_1565_, v_openDecls_1564_);
v___x_1570_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1570_, 0, v_val_1568_);
lean_ctor_set(v___x_1570_, 1, v___x_1569_);
return v___x_1570_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadResolveNameOfMonadLift___redArg(lean_object* v_inst_1571_, lean_object* v_inst_1572_){
_start:
{
lean_object* v_getCurrNamespace_1573_; lean_object* v_getOpenDecls_1574_; lean_object* v___x_1576_; uint8_t v_isShared_1577_; uint8_t v_isSharedCheck_1583_; 
v_getCurrNamespace_1573_ = lean_ctor_get(v_inst_1572_, 0);
v_getOpenDecls_1574_ = lean_ctor_get(v_inst_1572_, 1);
v_isSharedCheck_1583_ = !lean_is_exclusive(v_inst_1572_);
if (v_isSharedCheck_1583_ == 0)
{
v___x_1576_ = v_inst_1572_;
v_isShared_1577_ = v_isSharedCheck_1583_;
goto v_resetjp_1575_;
}
else
{
lean_inc(v_getOpenDecls_1574_);
lean_inc(v_getCurrNamespace_1573_);
lean_dec(v_inst_1572_);
v___x_1576_ = lean_box(0);
v_isShared_1577_ = v_isSharedCheck_1583_;
goto v_resetjp_1575_;
}
v_resetjp_1575_:
{
lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1581_; 
lean_inc(v_inst_1571_);
v___x_1578_ = lean_apply_2(v_inst_1571_, lean_box(0), v_getCurrNamespace_1573_);
v___x_1579_ = lean_apply_2(v_inst_1571_, lean_box(0), v_getOpenDecls_1574_);
if (v_isShared_1577_ == 0)
{
lean_ctor_set(v___x_1576_, 1, v___x_1579_);
lean_ctor_set(v___x_1576_, 0, v___x_1578_);
v___x_1581_ = v___x_1576_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1582_; 
v_reuseFailAlloc_1582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1582_, 0, v___x_1578_);
lean_ctor_set(v_reuseFailAlloc_1582_, 1, v___x_1579_);
v___x_1581_ = v_reuseFailAlloc_1582_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
return v___x_1581_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadResolveNameOfMonadLift(lean_object* v_m_1584_, lean_object* v_n_1585_, lean_object* v_inst_1586_, lean_object* v_inst_1587_){
_start:
{
lean_object* v___x_1588_; 
v___x_1588_ = l_Lean_instMonadResolveNameOfMonadLift___redArg(v_inst_1586_, v_inst_1587_);
return v___x_1588_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1590_; lean_object* v___x_1591_; 
v___x_1590_ = ((lean_object*)(l_Lean_checkPrivateInPublic___redArg___lam__0___closed__0));
v___x_1591_ = l_Lean_stringToMessageData(v___x_1590_);
return v___x_1591_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1593_; lean_object* v___x_1594_; 
v___x_1593_ = ((lean_object*)(l_Lean_checkPrivateInPublic___redArg___lam__0___closed__2));
v___x_1594_ = l_Lean_stringToMessageData(v___x_1593_);
return v___x_1594_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___redArg___lam__0(lean_object* v_____do__lift_1595_, lean_object* v_toPure_1596_, lean_object* v_id_1597_, lean_object* v_inst_1598_, lean_object* v_inst_1599_, lean_object* v_inst_1600_, lean_object* v_inst_1601_, uint8_t v_____do__lift_1602_){
_start:
{
uint8_t v_isExporting_1606_; 
v_isExporting_1606_ = lean_ctor_get_uint8(v_____do__lift_1595_, sizeof(void*)*8);
if (v_isExporting_1606_ == 0)
{
lean_dec(v_inst_1601_);
lean_dec(v_inst_1600_);
lean_dec_ref(v_inst_1599_);
lean_dec_ref(v_inst_1598_);
lean_dec(v_id_1597_);
goto v___jp_1603_;
}
else
{
uint8_t v___x_1607_; 
v___x_1607_ = l_Lean_isPrivateName(v_id_1597_);
if (v___x_1607_ == 0)
{
lean_dec(v_inst_1601_);
lean_dec(v_inst_1600_);
lean_dec_ref(v_inst_1599_);
lean_dec_ref(v_inst_1598_);
lean_dec(v_id_1597_);
goto v___jp_1603_;
}
else
{
if (v_____do__lift_1602_ == 0)
{
lean_dec(v_inst_1601_);
lean_dec(v_inst_1600_);
lean_dec_ref(v_inst_1599_);
lean_dec_ref(v_inst_1598_);
lean_dec(v_id_1597_);
goto v___jp_1603_;
}
else
{
lean_object* v___x_1608_; uint8_t v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; 
lean_dec(v_toPure_1596_);
v___x_1608_ = lean_obj_once(&l_Lean_checkPrivateInPublic___redArg___lam__0___closed__1, &l_Lean_checkPrivateInPublic___redArg___lam__0___closed__1_once, _init_l_Lean_checkPrivateInPublic___redArg___lam__0___closed__1);
v___x_1609_ = 0;
v___x_1610_ = l_Lean_MessageData_ofConstName(v_id_1597_, v___x_1609_);
v___x_1611_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1611_, 0, v___x_1608_);
lean_ctor_set(v___x_1611_, 1, v___x_1610_);
v___x_1612_ = lean_obj_once(&l_Lean_checkPrivateInPublic___redArg___lam__0___closed__3, &l_Lean_checkPrivateInPublic___redArg___lam__0___closed__3_once, _init_l_Lean_checkPrivateInPublic___redArg___lam__0___closed__3);
v___x_1613_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1613_, 0, v___x_1611_);
lean_ctor_set(v___x_1613_, 1, v___x_1612_);
v___x_1614_ = l_Lean_logWarning___redArg(v_inst_1598_, v_inst_1599_, v_inst_1600_, v_inst_1601_, v___x_1613_);
return v___x_1614_;
}
}
}
v___jp_1603_:
{
lean_object* v___x_1604_; lean_object* v___x_1605_; 
v___x_1604_ = lean_box(0);
v___x_1605_ = lean_apply_2(v_toPure_1596_, lean_box(0), v___x_1604_);
return v___x_1605_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___redArg___lam__0___boxed(lean_object* v_____do__lift_1615_, lean_object* v_toPure_1616_, lean_object* v_id_1617_, lean_object* v_inst_1618_, lean_object* v_inst_1619_, lean_object* v_inst_1620_, lean_object* v_inst_1621_, lean_object* v_____do__lift_1622_){
_start:
{
uint8_t v_____do__lift_197__boxed_1623_; lean_object* v_res_1624_; 
v_____do__lift_197__boxed_1623_ = lean_unbox(v_____do__lift_1622_);
v_res_1624_ = l_Lean_checkPrivateInPublic___redArg___lam__0(v_____do__lift_1615_, v_toPure_1616_, v_id_1617_, v_inst_1618_, v_inst_1619_, v_inst_1620_, v_inst_1621_, v_____do__lift_197__boxed_1623_);
lean_dec_ref(v_____do__lift_1615_);
return v_res_1624_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___redArg___lam__1(lean_object* v_toPure_1625_, lean_object* v_id_1626_, lean_object* v_inst_1627_, lean_object* v_inst_1628_, lean_object* v_inst_1629_, lean_object* v_inst_1630_, lean_object* v___x_1631_, lean_object* v_toBind_1632_, lean_object* v_____do__lift_1633_){
_start:
{
lean_object* v___f_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; 
lean_inc(v_inst_1630_);
lean_inc_ref(v_inst_1627_);
v___f_1634_ = lean_alloc_closure((void*)(l_Lean_checkPrivateInPublic___redArg___lam__0___boxed), 8, 7);
lean_closure_set(v___f_1634_, 0, v_____do__lift_1633_);
lean_closure_set(v___f_1634_, 1, v_toPure_1625_);
lean_closure_set(v___f_1634_, 2, v_id_1626_);
lean_closure_set(v___f_1634_, 3, v_inst_1627_);
lean_closure_set(v___f_1634_, 4, v_inst_1628_);
lean_closure_set(v___f_1634_, 5, v_inst_1629_);
lean_closure_set(v___f_1634_, 6, v_inst_1630_);
v___x_1635_ = l_Lean_ResolveName_backward_privateInPublic_warn;
v___x_1636_ = l_Lean_Option_getM___redArg(v_inst_1627_, v_inst_1630_, v___x_1631_, v___x_1635_);
v___x_1637_ = lean_apply_4(v_toBind_1632_, lean_box(0), lean_box(0), v___x_1636_, v___f_1634_);
return v___x_1637_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___redArg(lean_object* v_inst_1638_, lean_object* v_inst_1639_, lean_object* v_inst_1640_, lean_object* v_inst_1641_, lean_object* v_inst_1642_, lean_object* v_id_1643_){
_start:
{
lean_object* v___x_1644_; lean_object* v_toApplicative_1645_; lean_object* v_toBind_1646_; lean_object* v_getEnv_1647_; lean_object* v_toPure_1648_; lean_object* v___f_1649_; lean_object* v___x_1650_; 
v___x_1644_ = l_Lean_KVMap_instValueBool;
v_toApplicative_1645_ = lean_ctor_get(v_inst_1638_, 0);
v_toBind_1646_ = lean_ctor_get(v_inst_1638_, 1);
lean_inc_n(v_toBind_1646_, 2);
v_getEnv_1647_ = lean_ctor_get(v_inst_1639_, 0);
lean_inc(v_getEnv_1647_);
lean_dec_ref(v_inst_1639_);
v_toPure_1648_ = lean_ctor_get(v_toApplicative_1645_, 1);
lean_inc(v_toPure_1648_);
v___f_1649_ = lean_alloc_closure((void*)(l_Lean_checkPrivateInPublic___redArg___lam__1), 9, 8);
lean_closure_set(v___f_1649_, 0, v_toPure_1648_);
lean_closure_set(v___f_1649_, 1, v_id_1643_);
lean_closure_set(v___f_1649_, 2, v_inst_1638_);
lean_closure_set(v___f_1649_, 3, v_inst_1641_);
lean_closure_set(v___f_1649_, 4, v_inst_1642_);
lean_closure_set(v___f_1649_, 5, v_inst_1640_);
lean_closure_set(v___f_1649_, 6, v___x_1644_);
lean_closure_set(v___f_1649_, 7, v_toBind_1646_);
v___x_1650_ = lean_apply_4(v_toBind_1646_, lean_box(0), lean_box(0), v_getEnv_1647_, v___f_1649_);
return v___x_1650_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic(lean_object* v_m_1651_, lean_object* v_inst_1652_, lean_object* v_inst_1653_, lean_object* v_inst_1654_, lean_object* v_inst_1655_, lean_object* v_inst_1656_, lean_object* v_id_1657_){
_start:
{
lean_object* v___x_1658_; 
v___x_1658_ = l_Lean_checkPrivateInPublic___redArg(v_inst_1652_, v_inst_1653_, v_inst_1654_, v_inst_1655_, v_inst_1656_, v_id_1657_);
return v___x_1658_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg___lam__0(lean_object* v_env_1659_, lean_object* v_n_1660_, lean_object* v_toPure_1661_, uint8_t v___y_1662_, uint8_t v___x_1663_, lean_object* v_____r_1664_){
_start:
{
lean_object* v___x_1665_; 
v___x_1665_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1659_, v_n_1660_);
if (lean_obj_tag(v___x_1665_) == 0)
{
lean_object* v___x_1666_; lean_object* v___x_1667_; 
v___x_1666_ = lean_box(v___y_1662_);
v___x_1667_ = lean_apply_2(v_toPure_1661_, lean_box(0), v___x_1666_);
return v___x_1667_;
}
else
{
lean_object* v_val_1668_; lean_object* v___x_1669_; uint8_t v_isModule_1670_; 
v_val_1668_ = lean_ctor_get(v___x_1665_, 0);
lean_inc(v_val_1668_);
lean_dec_ref_known(v___x_1665_, 1);
v___x_1669_ = l_Lean_Environment_header(v_env_1659_);
v_isModule_1670_ = lean_ctor_get_uint8(v___x_1669_, sizeof(void*)*7 + 4);
if (v_isModule_1670_ == 0)
{
lean_object* v___x_1671_; lean_object* v___x_1672_; 
lean_dec_ref(v___x_1669_);
lean_dec(v_val_1668_);
v___x_1671_ = lean_box(v___x_1663_);
v___x_1672_ = lean_apply_2(v_toPure_1661_, lean_box(0), v___x_1671_);
return v___x_1672_;
}
else
{
lean_object* v_modules_1673_; lean_object* v___x_1674_; uint8_t v___x_1675_; 
v_modules_1673_ = lean_ctor_get(v___x_1669_, 3);
lean_inc_ref(v_modules_1673_);
lean_dec_ref(v___x_1669_);
v___x_1674_ = lean_array_get_size(v_modules_1673_);
v___x_1675_ = lean_nat_dec_lt(v_val_1668_, v___x_1674_);
if (v___x_1675_ == 0)
{
lean_object* v___x_1676_; lean_object* v___x_1677_; 
lean_dec_ref(v_modules_1673_);
lean_dec(v_val_1668_);
v___x_1676_ = lean_box(v_isModule_1670_);
v___x_1677_ = lean_apply_2(v_toPure_1661_, lean_box(0), v___x_1676_);
return v___x_1677_;
}
else
{
lean_object* v___x_1678_; lean_object* v_toImport_1679_; uint8_t v_importAll_1680_; 
v___x_1678_ = lean_array_fget(v_modules_1673_, v_val_1668_);
lean_dec(v_val_1668_);
lean_dec_ref(v_modules_1673_);
v_toImport_1679_ = lean_ctor_get(v___x_1678_, 0);
lean_inc_ref(v_toImport_1679_);
lean_dec(v___x_1678_);
v_importAll_1680_ = lean_ctor_get_uint8(v_toImport_1679_, sizeof(void*)*1);
lean_dec_ref(v_toImport_1679_);
if (v_importAll_1680_ == 0)
{
lean_object* v___x_1681_; lean_object* v___x_1682_; 
v___x_1681_ = lean_box(v_isModule_1670_);
v___x_1682_ = lean_apply_2(v_toPure_1661_, lean_box(0), v___x_1681_);
return v___x_1682_;
}
else
{
lean_object* v___x_1683_; lean_object* v___x_1684_; 
v___x_1683_ = lean_box(v___y_1662_);
v___x_1684_ = lean_apply_2(v_toPure_1661_, lean_box(0), v___x_1683_);
return v___x_1684_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg___lam__0___boxed(lean_object* v_env_1685_, lean_object* v_n_1686_, lean_object* v_toPure_1687_, lean_object* v___y_1688_, lean_object* v___x_1689_, lean_object* v_____r_1690_){
_start:
{
uint8_t v___y_384__boxed_1691_; uint8_t v___x_385__boxed_1692_; lean_object* v_res_1693_; 
v___y_384__boxed_1691_ = lean_unbox(v___y_1688_);
v___x_385__boxed_1692_ = lean_unbox(v___x_1689_);
v_res_1693_ = l_Lean_isInaccessiblePrivateName___redArg___lam__0(v_env_1685_, v_n_1686_, v_toPure_1687_, v___y_384__boxed_1691_, v___x_385__boxed_1692_, v_____r_1690_);
lean_dec(v_n_1686_);
lean_dec_ref(v_env_1685_);
return v_res_1693_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg___lam__1(lean_object* v_env_1694_, lean_object* v_n_1695_, lean_object* v_toPure_1696_, uint8_t v___x_1697_, lean_object* v_inst_1698_, lean_object* v_inst_1699_, lean_object* v_inst_1700_, lean_object* v_inst_1701_, lean_object* v_inst_1702_, lean_object* v_toBind_1703_, uint8_t v___y_1704_, uint8_t v_____do__lift_1705_){
_start:
{
uint8_t v___y_1707_; uint8_t v_isExporting_1713_; 
v_isExporting_1713_ = lean_ctor_get_uint8(v_env_1694_, sizeof(void*)*8);
if (v_isExporting_1713_ == 0)
{
v___y_1707_ = v___y_1704_;
goto v___jp_1706_;
}
else
{
if (v_____do__lift_1705_ == 0)
{
lean_object* v___x_1714_; lean_object* v___x_1715_; 
lean_dec(v_toBind_1703_);
lean_dec(v_inst_1702_);
lean_dec_ref(v_inst_1701_);
lean_dec(v_inst_1700_);
lean_dec_ref(v_inst_1699_);
lean_dec_ref(v_inst_1698_);
lean_dec(v_n_1695_);
lean_dec_ref(v_env_1694_);
v___x_1714_ = lean_box(v___x_1697_);
v___x_1715_ = lean_apply_2(v_toPure_1696_, lean_box(0), v___x_1714_);
return v___x_1715_;
}
else
{
v___y_1707_ = v___y_1704_;
goto v___jp_1706_;
}
}
v___jp_1706_:
{
lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___f_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; 
v___x_1708_ = lean_box(v___y_1707_);
v___x_1709_ = lean_box(v___x_1697_);
lean_inc(v_n_1695_);
v___f_1710_ = lean_alloc_closure((void*)(l_Lean_isInaccessiblePrivateName___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1710_, 0, v_env_1694_);
lean_closure_set(v___f_1710_, 1, v_n_1695_);
lean_closure_set(v___f_1710_, 2, v_toPure_1696_);
lean_closure_set(v___f_1710_, 3, v___x_1708_);
lean_closure_set(v___f_1710_, 4, v___x_1709_);
v___x_1711_ = l_Lean_checkPrivateInPublic___redArg(v_inst_1698_, v_inst_1699_, v_inst_1700_, v_inst_1701_, v_inst_1702_, v_n_1695_);
v___x_1712_ = lean_apply_4(v_toBind_1703_, lean_box(0), lean_box(0), v___x_1711_, v___f_1710_);
return v___x_1712_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg___lam__1___boxed(lean_object* v_env_1716_, lean_object* v_n_1717_, lean_object* v_toPure_1718_, lean_object* v___x_1719_, lean_object* v_inst_1720_, lean_object* v_inst_1721_, lean_object* v_inst_1722_, lean_object* v_inst_1723_, lean_object* v_inst_1724_, lean_object* v_toBind_1725_, lean_object* v___y_1726_, lean_object* v_____do__lift_1727_){
_start:
{
uint8_t v___x_425__boxed_1728_; uint8_t v___y_431__boxed_1729_; uint8_t v_____do__lift_432__boxed_1730_; lean_object* v_res_1731_; 
v___x_425__boxed_1728_ = lean_unbox(v___x_1719_);
v___y_431__boxed_1729_ = lean_unbox(v___y_1726_);
v_____do__lift_432__boxed_1730_ = lean_unbox(v_____do__lift_1727_);
v_res_1731_ = l_Lean_isInaccessiblePrivateName___redArg___lam__1(v_env_1716_, v_n_1717_, v_toPure_1718_, v___x_425__boxed_1728_, v_inst_1720_, v_inst_1721_, v_inst_1722_, v_inst_1723_, v_inst_1724_, v_toBind_1725_, v___y_431__boxed_1729_, v_____do__lift_432__boxed_1730_);
return v_res_1731_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg___lam__2(lean_object* v_n_1732_, lean_object* v_toPure_1733_, uint8_t v___x_1734_, lean_object* v_inst_1735_, lean_object* v_inst_1736_, lean_object* v_inst_1737_, lean_object* v_inst_1738_, lean_object* v_inst_1739_, lean_object* v_toBind_1740_, uint8_t v___y_1741_, lean_object* v___x_1742_, lean_object* v_env_1743_){
_start:
{
lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___f_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; 
v___x_1744_ = lean_box(v___x_1734_);
v___x_1745_ = lean_box(v___y_1741_);
lean_inc(v_toBind_1740_);
lean_inc(v_inst_1737_);
lean_inc_ref(v_inst_1735_);
v___f_1746_ = lean_alloc_closure((void*)(l_Lean_isInaccessiblePrivateName___redArg___lam__1___boxed), 12, 11);
lean_closure_set(v___f_1746_, 0, v_env_1743_);
lean_closure_set(v___f_1746_, 1, v_n_1732_);
lean_closure_set(v___f_1746_, 2, v_toPure_1733_);
lean_closure_set(v___f_1746_, 3, v___x_1744_);
lean_closure_set(v___f_1746_, 4, v_inst_1735_);
lean_closure_set(v___f_1746_, 5, v_inst_1736_);
lean_closure_set(v___f_1746_, 6, v_inst_1737_);
lean_closure_set(v___f_1746_, 7, v_inst_1738_);
lean_closure_set(v___f_1746_, 8, v_inst_1739_);
lean_closure_set(v___f_1746_, 9, v_toBind_1740_);
lean_closure_set(v___f_1746_, 10, v___x_1745_);
v___x_1747_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_1748_ = l_Lean_Option_getM___redArg(v_inst_1735_, v_inst_1737_, v___x_1742_, v___x_1747_);
v___x_1749_ = lean_apply_4(v_toBind_1740_, lean_box(0), lean_box(0), v___x_1748_, v___f_1746_);
return v___x_1749_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg___lam__2___boxed(lean_object* v_n_1750_, lean_object* v_toPure_1751_, lean_object* v___x_1752_, lean_object* v_inst_1753_, lean_object* v_inst_1754_, lean_object* v_inst_1755_, lean_object* v_inst_1756_, lean_object* v_inst_1757_, lean_object* v_toBind_1758_, lean_object* v___y_1759_, lean_object* v___x_1760_, lean_object* v_env_1761_){
_start:
{
uint8_t v___x_467__boxed_1762_; uint8_t v___y_473__boxed_1763_; lean_object* v_res_1764_; 
v___x_467__boxed_1762_ = lean_unbox(v___x_1752_);
v___y_473__boxed_1763_ = lean_unbox(v___y_1759_);
v_res_1764_ = l_Lean_isInaccessiblePrivateName___redArg___lam__2(v_n_1750_, v_toPure_1751_, v___x_467__boxed_1762_, v_inst_1753_, v_inst_1754_, v_inst_1755_, v_inst_1756_, v_inst_1757_, v_toBind_1758_, v___y_473__boxed_1763_, v___x_1760_, v_env_1761_);
return v_res_1764_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg(lean_object* v_inst_1765_, lean_object* v_inst_1766_, lean_object* v_inst_1767_, lean_object* v_inst_1768_, lean_object* v_inst_1769_, lean_object* v_n_1770_){
_start:
{
lean_object* v___x_1771_; uint8_t v___y_1773_; uint8_t v___x_1788_; 
v___x_1771_ = l_Lean_KVMap_instValueBool;
v___x_1788_ = l_Lean_isPrivateName(v_n_1770_);
if (v___x_1788_ == 0)
{
uint8_t v___x_1789_; 
v___x_1789_ = 1;
v___y_1773_ = v___x_1789_;
goto v___jp_1772_;
}
else
{
uint8_t v___x_1790_; 
v___x_1790_ = 0;
v___y_1773_ = v___x_1790_;
goto v___jp_1772_;
}
v___jp_1772_:
{
if (v___y_1773_ == 0)
{
lean_object* v_toApplicative_1774_; lean_object* v_toBind_1775_; lean_object* v_toPure_1776_; lean_object* v_getEnv_1777_; uint8_t v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___f_1781_; lean_object* v___x_1782_; 
v_toApplicative_1774_ = lean_ctor_get(v_inst_1767_, 0);
v_toBind_1775_ = lean_ctor_get(v_inst_1767_, 1);
lean_inc_n(v_toBind_1775_, 2);
v_toPure_1776_ = lean_ctor_get(v_toApplicative_1774_, 1);
lean_inc(v_toPure_1776_);
v_getEnv_1777_ = lean_ctor_get(v_inst_1768_, 0);
lean_inc(v_getEnv_1777_);
v___x_1778_ = 1;
v___x_1779_ = lean_box(v___x_1778_);
v___x_1780_ = lean_box(v___y_1773_);
v___f_1781_ = lean_alloc_closure((void*)(l_Lean_isInaccessiblePrivateName___redArg___lam__2___boxed), 12, 11);
lean_closure_set(v___f_1781_, 0, v_n_1770_);
lean_closure_set(v___f_1781_, 1, v_toPure_1776_);
lean_closure_set(v___f_1781_, 2, v___x_1779_);
lean_closure_set(v___f_1781_, 3, v_inst_1767_);
lean_closure_set(v___f_1781_, 4, v_inst_1768_);
lean_closure_set(v___f_1781_, 5, v_inst_1769_);
lean_closure_set(v___f_1781_, 6, v_inst_1765_);
lean_closure_set(v___f_1781_, 7, v_inst_1766_);
lean_closure_set(v___f_1781_, 8, v_toBind_1775_);
lean_closure_set(v___f_1781_, 9, v___x_1780_);
lean_closure_set(v___f_1781_, 10, v___x_1771_);
v___x_1782_ = lean_apply_4(v_toBind_1775_, lean_box(0), lean_box(0), v_getEnv_1777_, v___f_1781_);
return v___x_1782_;
}
else
{
lean_object* v_toApplicative_1783_; lean_object* v_toPure_1784_; uint8_t v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; 
v_toApplicative_1783_ = lean_ctor_get(v_inst_1767_, 0);
lean_inc_ref(v_toApplicative_1783_);
lean_dec(v_n_1770_);
lean_dec(v_inst_1769_);
lean_dec_ref(v_inst_1768_);
lean_dec_ref(v_inst_1767_);
lean_dec(v_inst_1766_);
lean_dec_ref(v_inst_1765_);
v_toPure_1784_ = lean_ctor_get(v_toApplicative_1783_, 1);
lean_inc(v_toPure_1784_);
lean_dec_ref(v_toApplicative_1783_);
v___x_1785_ = 0;
v___x_1786_ = lean_box(v___x_1785_);
v___x_1787_ = lean_apply_2(v_toPure_1784_, lean_box(0), v___x_1786_);
return v___x_1787_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName(lean_object* v_m_1791_, lean_object* v_inst_1792_, lean_object* v_inst_1793_, lean_object* v_inst_1794_, lean_object* v_inst_1795_, lean_object* v_inst_1796_, lean_object* v_n_1797_){
_start:
{
lean_object* v___x_1798_; 
v___x_1798_ = l_Lean_isInaccessiblePrivateName___redArg(v_inst_1792_, v_inst_1793_, v_inst_1794_, v_inst_1795_, v_inst_1796_, v_n_1797_);
return v___x_1798_;
}
}
LEAN_EXPORT uint8_t l_Lean_resolveGlobalName___redArg___lam__0(lean_object* v_x_1799_){
_start:
{
lean_object* v_fst_1800_; uint8_t v___x_1801_; 
v_fst_1800_ = lean_ctor_get(v_x_1799_, 0);
v___x_1801_ = l_Lean_isPrivateName(v_fst_1800_);
return v___x_1801_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__0___boxed(lean_object* v_x_1802_){
_start:
{
uint8_t v_res_1803_; lean_object* v_r_1804_; 
v_res_1803_ = l_Lean_resolveGlobalName___redArg___lam__0(v_x_1802_);
lean_dec_ref(v_x_1802_);
v_r_1804_ = lean_box(v_res_1803_);
return v_r_1804_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__1(lean_object* v_toPure_1805_, lean_object* v_res_1806_, lean_object* v_____r_1807_){
_start:
{
lean_object* v___x_1808_; 
v___x_1808_ = lean_apply_2(v_toPure_1805_, lean_box(0), v_res_1806_);
return v___x_1808_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__2(uint8_t v_enableLog_1809_, lean_object* v_toPure_1810_, lean_object* v_res_1811_, lean_object* v___f_1812_, lean_object* v_inst_1813_, lean_object* v_inst_1814_, lean_object* v_inst_1815_, lean_object* v_inst_1816_, lean_object* v_inst_1817_, lean_object* v_toBind_1818_, lean_object* v___f_1819_, lean_object* v_____do__lift_1820_){
_start:
{
if (v_enableLog_1809_ == 0)
{
lean_object* v___x_1821_; 
lean_dec(v___f_1819_);
lean_dec(v_toBind_1818_);
lean_dec(v_inst_1817_);
lean_dec_ref(v_inst_1816_);
lean_dec(v_inst_1815_);
lean_dec_ref(v_inst_1814_);
lean_dec_ref(v_inst_1813_);
lean_dec_ref(v___f_1812_);
v___x_1821_ = lean_apply_2(v_toPure_1810_, lean_box(0), v_res_1811_);
return v___x_1821_;
}
else
{
uint8_t v_isExporting_1822_; 
v_isExporting_1822_ = lean_ctor_get_uint8(v_____do__lift_1820_, sizeof(void*)*8);
if (v_isExporting_1822_ == 0)
{
lean_object* v___x_1823_; 
lean_dec(v___f_1819_);
lean_dec(v_toBind_1818_);
lean_dec(v_inst_1817_);
lean_dec_ref(v_inst_1816_);
lean_dec(v_inst_1815_);
lean_dec_ref(v_inst_1814_);
lean_dec_ref(v_inst_1813_);
lean_dec_ref(v___f_1812_);
v___x_1823_ = lean_apply_2(v_toPure_1810_, lean_box(0), v_res_1811_);
return v___x_1823_;
}
else
{
lean_object* v___x_1824_; 
lean_inc(v_res_1811_);
v___x_1824_ = l_List_find_x3f___redArg(v___f_1812_, v_res_1811_);
if (lean_obj_tag(v___x_1824_) == 1)
{
lean_object* v_val_1825_; lean_object* v_fst_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; 
lean_dec(v_res_1811_);
lean_dec(v_toPure_1810_);
v_val_1825_ = lean_ctor_get(v___x_1824_, 0);
lean_inc(v_val_1825_);
lean_dec_ref_known(v___x_1824_, 1);
v_fst_1826_ = lean_ctor_get(v_val_1825_, 0);
lean_inc(v_fst_1826_);
lean_dec(v_val_1825_);
v___x_1827_ = l_Lean_checkPrivateInPublic___redArg(v_inst_1813_, v_inst_1814_, v_inst_1815_, v_inst_1816_, v_inst_1817_, v_fst_1826_);
v___x_1828_ = lean_apply_4(v_toBind_1818_, lean_box(0), lean_box(0), v___x_1827_, v___f_1819_);
return v___x_1828_;
}
else
{
lean_object* v___x_1829_; 
lean_dec(v___x_1824_);
lean_dec(v___f_1819_);
lean_dec(v_toBind_1818_);
lean_dec(v_inst_1817_);
lean_dec_ref(v_inst_1816_);
lean_dec(v_inst_1815_);
lean_dec_ref(v_inst_1814_);
lean_dec_ref(v_inst_1813_);
v___x_1829_ = lean_apply_2(v_toPure_1810_, lean_box(0), v_res_1811_);
return v___x_1829_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__2___boxed(lean_object* v_enableLog_1830_, lean_object* v_toPure_1831_, lean_object* v_res_1832_, lean_object* v___f_1833_, lean_object* v_inst_1834_, lean_object* v_inst_1835_, lean_object* v_inst_1836_, lean_object* v_inst_1837_, lean_object* v_inst_1838_, lean_object* v_toBind_1839_, lean_object* v___f_1840_, lean_object* v_____do__lift_1841_){
_start:
{
uint8_t v_enableLog_boxed_1842_; lean_object* v_res_1843_; 
v_enableLog_boxed_1842_ = lean_unbox(v_enableLog_1830_);
v_res_1843_ = l_Lean_resolveGlobalName___redArg___lam__2(v_enableLog_boxed_1842_, v_toPure_1831_, v_res_1832_, v___f_1833_, v_inst_1834_, v_inst_1835_, v_inst_1836_, v_inst_1837_, v_inst_1838_, v_toBind_1839_, v___f_1840_, v_____do__lift_1841_);
lean_dec_ref(v_____do__lift_1841_);
return v_res_1843_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__3(lean_object* v_____do__lift_1844_, lean_object* v_____do__lift_1845_, lean_object* v_____do__lift_1846_, lean_object* v_id_1847_, lean_object* v_toPure_1848_, uint8_t v_enableLog_1849_, lean_object* v___f_1850_, lean_object* v_inst_1851_, lean_object* v_inst_1852_, lean_object* v_inst_1853_, lean_object* v_inst_1854_, lean_object* v_inst_1855_, lean_object* v_toBind_1856_, lean_object* v_getEnv_1857_, lean_object* v_____do__lift_1858_){
_start:
{
lean_object* v_res_1859_; lean_object* v___f_1860_; lean_object* v___x_1861_; lean_object* v___f_1862_; lean_object* v___x_1863_; 
v_res_1859_ = l_Lean_ResolveName_resolveGlobalName(v_____do__lift_1844_, v_____do__lift_1845_, v_____do__lift_1846_, v_____do__lift_1858_, v_id_1847_);
lean_inc(v_res_1859_);
lean_inc(v_toPure_1848_);
v___f_1860_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalName___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1860_, 0, v_toPure_1848_);
lean_closure_set(v___f_1860_, 1, v_res_1859_);
v___x_1861_ = lean_box(v_enableLog_1849_);
lean_inc(v_toBind_1856_);
v___f_1862_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalName___redArg___lam__2___boxed), 12, 11);
lean_closure_set(v___f_1862_, 0, v___x_1861_);
lean_closure_set(v___f_1862_, 1, v_toPure_1848_);
lean_closure_set(v___f_1862_, 2, v_res_1859_);
lean_closure_set(v___f_1862_, 3, v___f_1850_);
lean_closure_set(v___f_1862_, 4, v_inst_1851_);
lean_closure_set(v___f_1862_, 5, v_inst_1852_);
lean_closure_set(v___f_1862_, 6, v_inst_1853_);
lean_closure_set(v___f_1862_, 7, v_inst_1854_);
lean_closure_set(v___f_1862_, 8, v_inst_1855_);
lean_closure_set(v___f_1862_, 9, v_toBind_1856_);
lean_closure_set(v___f_1862_, 10, v___f_1860_);
v___x_1863_ = lean_apply_4(v_toBind_1856_, lean_box(0), lean_box(0), v_getEnv_1857_, v___f_1862_);
return v___x_1863_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__3___boxed(lean_object* v_____do__lift_1864_, lean_object* v_____do__lift_1865_, lean_object* v_____do__lift_1866_, lean_object* v_id_1867_, lean_object* v_toPure_1868_, lean_object* v_enableLog_1869_, lean_object* v___f_1870_, lean_object* v_inst_1871_, lean_object* v_inst_1872_, lean_object* v_inst_1873_, lean_object* v_inst_1874_, lean_object* v_inst_1875_, lean_object* v_toBind_1876_, lean_object* v_getEnv_1877_, lean_object* v_____do__lift_1878_){
_start:
{
uint8_t v_enableLog_boxed_1879_; lean_object* v_res_1880_; 
v_enableLog_boxed_1879_ = lean_unbox(v_enableLog_1869_);
v_res_1880_ = l_Lean_resolveGlobalName___redArg___lam__3(v_____do__lift_1864_, v_____do__lift_1865_, v_____do__lift_1866_, v_id_1867_, v_toPure_1868_, v_enableLog_boxed_1879_, v___f_1870_, v_inst_1871_, v_inst_1872_, v_inst_1873_, v_inst_1874_, v_inst_1875_, v_toBind_1876_, v_getEnv_1877_, v_____do__lift_1878_);
lean_dec_ref(v_____do__lift_1865_);
return v_res_1880_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__4(lean_object* v_____do__lift_1881_, lean_object* v_____do__lift_1882_, lean_object* v_id_1883_, lean_object* v_toPure_1884_, uint8_t v_enableLog_1885_, lean_object* v___f_1886_, lean_object* v_inst_1887_, lean_object* v_inst_1888_, lean_object* v_inst_1889_, lean_object* v_inst_1890_, lean_object* v_inst_1891_, lean_object* v_toBind_1892_, lean_object* v_getEnv_1893_, lean_object* v_getOpenDecls_1894_, lean_object* v_____do__lift_1895_){
_start:
{
lean_object* v___x_1896_; lean_object* v___f_1897_; lean_object* v___x_1898_; 
v___x_1896_ = lean_box(v_enableLog_1885_);
lean_inc(v_toBind_1892_);
v___f_1897_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalName___redArg___lam__3___boxed), 15, 14);
lean_closure_set(v___f_1897_, 0, v_____do__lift_1881_);
lean_closure_set(v___f_1897_, 1, v_____do__lift_1882_);
lean_closure_set(v___f_1897_, 2, v_____do__lift_1895_);
lean_closure_set(v___f_1897_, 3, v_id_1883_);
lean_closure_set(v___f_1897_, 4, v_toPure_1884_);
lean_closure_set(v___f_1897_, 5, v___x_1896_);
lean_closure_set(v___f_1897_, 6, v___f_1886_);
lean_closure_set(v___f_1897_, 7, v_inst_1887_);
lean_closure_set(v___f_1897_, 8, v_inst_1888_);
lean_closure_set(v___f_1897_, 9, v_inst_1889_);
lean_closure_set(v___f_1897_, 10, v_inst_1890_);
lean_closure_set(v___f_1897_, 11, v_inst_1891_);
lean_closure_set(v___f_1897_, 12, v_toBind_1892_);
lean_closure_set(v___f_1897_, 13, v_getEnv_1893_);
v___x_1898_ = lean_apply_4(v_toBind_1892_, lean_box(0), lean_box(0), v_getOpenDecls_1894_, v___f_1897_);
return v___x_1898_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__4___boxed(lean_object* v_____do__lift_1899_, lean_object* v_____do__lift_1900_, lean_object* v_id_1901_, lean_object* v_toPure_1902_, lean_object* v_enableLog_1903_, lean_object* v___f_1904_, lean_object* v_inst_1905_, lean_object* v_inst_1906_, lean_object* v_inst_1907_, lean_object* v_inst_1908_, lean_object* v_inst_1909_, lean_object* v_toBind_1910_, lean_object* v_getEnv_1911_, lean_object* v_getOpenDecls_1912_, lean_object* v_____do__lift_1913_){
_start:
{
uint8_t v_enableLog_boxed_1914_; lean_object* v_res_1915_; 
v_enableLog_boxed_1914_ = lean_unbox(v_enableLog_1903_);
v_res_1915_ = l_Lean_resolveGlobalName___redArg___lam__4(v_____do__lift_1899_, v_____do__lift_1900_, v_id_1901_, v_toPure_1902_, v_enableLog_boxed_1914_, v___f_1904_, v_inst_1905_, v_inst_1906_, v_inst_1907_, v_inst_1908_, v_inst_1909_, v_toBind_1910_, v_getEnv_1911_, v_getOpenDecls_1912_, v_____do__lift_1913_);
return v_res_1915_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__5(lean_object* v_inst_1916_, lean_object* v_____do__lift_1917_, lean_object* v_id_1918_, lean_object* v_toPure_1919_, uint8_t v_enableLog_1920_, lean_object* v___f_1921_, lean_object* v_inst_1922_, lean_object* v_inst_1923_, lean_object* v_inst_1924_, lean_object* v_inst_1925_, lean_object* v_inst_1926_, lean_object* v_toBind_1927_, lean_object* v_getEnv_1928_, lean_object* v_____do__lift_1929_){
_start:
{
lean_object* v_getCurrNamespace_1930_; lean_object* v_getOpenDecls_1931_; lean_object* v___x_1932_; lean_object* v___f_1933_; lean_object* v___x_1934_; 
v_getCurrNamespace_1930_ = lean_ctor_get(v_inst_1916_, 0);
lean_inc(v_getCurrNamespace_1930_);
v_getOpenDecls_1931_ = lean_ctor_get(v_inst_1916_, 1);
lean_inc(v_getOpenDecls_1931_);
lean_dec_ref(v_inst_1916_);
v___x_1932_ = lean_box(v_enableLog_1920_);
lean_inc(v_toBind_1927_);
v___f_1933_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalName___redArg___lam__4___boxed), 15, 14);
lean_closure_set(v___f_1933_, 0, v_____do__lift_1917_);
lean_closure_set(v___f_1933_, 1, v_____do__lift_1929_);
lean_closure_set(v___f_1933_, 2, v_id_1918_);
lean_closure_set(v___f_1933_, 3, v_toPure_1919_);
lean_closure_set(v___f_1933_, 4, v___x_1932_);
lean_closure_set(v___f_1933_, 5, v___f_1921_);
lean_closure_set(v___f_1933_, 6, v_inst_1922_);
lean_closure_set(v___f_1933_, 7, v_inst_1923_);
lean_closure_set(v___f_1933_, 8, v_inst_1924_);
lean_closure_set(v___f_1933_, 9, v_inst_1925_);
lean_closure_set(v___f_1933_, 10, v_inst_1926_);
lean_closure_set(v___f_1933_, 11, v_toBind_1927_);
lean_closure_set(v___f_1933_, 12, v_getEnv_1928_);
lean_closure_set(v___f_1933_, 13, v_getOpenDecls_1931_);
v___x_1934_ = lean_apply_4(v_toBind_1927_, lean_box(0), lean_box(0), v_getCurrNamespace_1930_, v___f_1933_);
return v___x_1934_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__5___boxed(lean_object* v_inst_1935_, lean_object* v_____do__lift_1936_, lean_object* v_id_1937_, lean_object* v_toPure_1938_, lean_object* v_enableLog_1939_, lean_object* v___f_1940_, lean_object* v_inst_1941_, lean_object* v_inst_1942_, lean_object* v_inst_1943_, lean_object* v_inst_1944_, lean_object* v_inst_1945_, lean_object* v_toBind_1946_, lean_object* v_getEnv_1947_, lean_object* v_____do__lift_1948_){
_start:
{
uint8_t v_enableLog_boxed_1949_; lean_object* v_res_1950_; 
v_enableLog_boxed_1949_ = lean_unbox(v_enableLog_1939_);
v_res_1950_ = l_Lean_resolveGlobalName___redArg___lam__5(v_inst_1935_, v_____do__lift_1936_, v_id_1937_, v_toPure_1938_, v_enableLog_boxed_1949_, v___f_1940_, v_inst_1941_, v_inst_1942_, v_inst_1943_, v_inst_1944_, v_inst_1945_, v_toBind_1946_, v_getEnv_1947_, v_____do__lift_1948_);
return v_res_1950_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__6(lean_object* v_inst_1951_, lean_object* v_id_1952_, lean_object* v_toPure_1953_, uint8_t v_enableLog_1954_, lean_object* v___f_1955_, lean_object* v_inst_1956_, lean_object* v_inst_1957_, lean_object* v_inst_1958_, lean_object* v_inst_1959_, lean_object* v_inst_1960_, lean_object* v_toBind_1961_, lean_object* v_getEnv_1962_, lean_object* v_____do__lift_1963_){
_start:
{
lean_object* v___x_1964_; lean_object* v___f_1965_; lean_object* v___x_1966_; 
v___x_1964_ = lean_box(v_enableLog_1954_);
lean_inc(v_toBind_1961_);
lean_inc(v_inst_1958_);
v___f_1965_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalName___redArg___lam__5___boxed), 14, 13);
lean_closure_set(v___f_1965_, 0, v_inst_1951_);
lean_closure_set(v___f_1965_, 1, v_____do__lift_1963_);
lean_closure_set(v___f_1965_, 2, v_id_1952_);
lean_closure_set(v___f_1965_, 3, v_toPure_1953_);
lean_closure_set(v___f_1965_, 4, v___x_1964_);
lean_closure_set(v___f_1965_, 5, v___f_1955_);
lean_closure_set(v___f_1965_, 6, v_inst_1956_);
lean_closure_set(v___f_1965_, 7, v_inst_1957_);
lean_closure_set(v___f_1965_, 8, v_inst_1958_);
lean_closure_set(v___f_1965_, 9, v_inst_1959_);
lean_closure_set(v___f_1965_, 10, v_inst_1960_);
lean_closure_set(v___f_1965_, 11, v_toBind_1961_);
lean_closure_set(v___f_1965_, 12, v_getEnv_1962_);
v___x_1966_ = lean_apply_4(v_toBind_1961_, lean_box(0), lean_box(0), v_inst_1958_, v___f_1965_);
return v___x_1966_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__6___boxed(lean_object* v_inst_1967_, lean_object* v_id_1968_, lean_object* v_toPure_1969_, lean_object* v_enableLog_1970_, lean_object* v___f_1971_, lean_object* v_inst_1972_, lean_object* v_inst_1973_, lean_object* v_inst_1974_, lean_object* v_inst_1975_, lean_object* v_inst_1976_, lean_object* v_toBind_1977_, lean_object* v_getEnv_1978_, lean_object* v_____do__lift_1979_){
_start:
{
uint8_t v_enableLog_boxed_1980_; lean_object* v_res_1981_; 
v_enableLog_boxed_1980_ = lean_unbox(v_enableLog_1970_);
v_res_1981_ = l_Lean_resolveGlobalName___redArg___lam__6(v_inst_1967_, v_id_1968_, v_toPure_1969_, v_enableLog_boxed_1980_, v___f_1971_, v_inst_1972_, v_inst_1973_, v_inst_1974_, v_inst_1975_, v_inst_1976_, v_toBind_1977_, v_getEnv_1978_, v_____do__lift_1979_);
return v_res_1981_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg(lean_object* v_inst_1983_, lean_object* v_inst_1984_, lean_object* v_inst_1985_, lean_object* v_inst_1986_, lean_object* v_inst_1987_, lean_object* v_inst_1988_, lean_object* v_id_1989_, uint8_t v_enableLog_1990_){
_start:
{
lean_object* v_toApplicative_1991_; lean_object* v_toBind_1992_; lean_object* v_getEnv_1993_; lean_object* v_toPure_1994_; lean_object* v___f_1995_; lean_object* v___x_1996_; lean_object* v___f_1997_; lean_object* v___x_1998_; 
v_toApplicative_1991_ = lean_ctor_get(v_inst_1983_, 0);
v_toBind_1992_ = lean_ctor_get(v_inst_1983_, 1);
lean_inc_n(v_toBind_1992_, 2);
v_getEnv_1993_ = lean_ctor_get(v_inst_1985_, 0);
lean_inc_n(v_getEnv_1993_, 2);
v_toPure_1994_ = lean_ctor_get(v_toApplicative_1991_, 1);
lean_inc(v_toPure_1994_);
v___f_1995_ = ((lean_object*)(l_Lean_resolveGlobalName___redArg___closed__0));
v___x_1996_ = lean_box(v_enableLog_1990_);
v___f_1997_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalName___redArg___lam__6___boxed), 13, 12);
lean_closure_set(v___f_1997_, 0, v_inst_1984_);
lean_closure_set(v___f_1997_, 1, v_id_1989_);
lean_closure_set(v___f_1997_, 2, v_toPure_1994_);
lean_closure_set(v___f_1997_, 3, v___x_1996_);
lean_closure_set(v___f_1997_, 4, v___f_1995_);
lean_closure_set(v___f_1997_, 5, v_inst_1983_);
lean_closure_set(v___f_1997_, 6, v_inst_1985_);
lean_closure_set(v___f_1997_, 7, v_inst_1986_);
lean_closure_set(v___f_1997_, 8, v_inst_1987_);
lean_closure_set(v___f_1997_, 9, v_inst_1988_);
lean_closure_set(v___f_1997_, 10, v_toBind_1992_);
lean_closure_set(v___f_1997_, 11, v_getEnv_1993_);
v___x_1998_ = lean_apply_4(v_toBind_1992_, lean_box(0), lean_box(0), v_getEnv_1993_, v___f_1997_);
return v___x_1998_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___boxed(lean_object* v_inst_1999_, lean_object* v_inst_2000_, lean_object* v_inst_2001_, lean_object* v_inst_2002_, lean_object* v_inst_2003_, lean_object* v_inst_2004_, lean_object* v_id_2005_, lean_object* v_enableLog_2006_){
_start:
{
uint8_t v_enableLog_boxed_2007_; lean_object* v_res_2008_; 
v_enableLog_boxed_2007_ = lean_unbox(v_enableLog_2006_);
v_res_2008_ = l_Lean_resolveGlobalName___redArg(v_inst_1999_, v_inst_2000_, v_inst_2001_, v_inst_2002_, v_inst_2003_, v_inst_2004_, v_id_2005_, v_enableLog_boxed_2007_);
return v_res_2008_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName(lean_object* v_m_2009_, lean_object* v_inst_2010_, lean_object* v_inst_2011_, lean_object* v_inst_2012_, lean_object* v_inst_2013_, lean_object* v_inst_2014_, lean_object* v_inst_2015_, lean_object* v_id_2016_, uint8_t v_enableLog_2017_){
_start:
{
lean_object* v___x_2018_; 
v___x_2018_ = l_Lean_resolveGlobalName___redArg(v_inst_2010_, v_inst_2011_, v_inst_2012_, v_inst_2013_, v_inst_2014_, v_inst_2015_, v_id_2016_, v_enableLog_2017_);
return v___x_2018_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___boxed(lean_object* v_m_2019_, lean_object* v_inst_2020_, lean_object* v_inst_2021_, lean_object* v_inst_2022_, lean_object* v_inst_2023_, lean_object* v_inst_2024_, lean_object* v_inst_2025_, lean_object* v_id_2026_, lean_object* v_enableLog_2027_){
_start:
{
uint8_t v_enableLog_boxed_2028_; lean_object* v_res_2029_; 
v_enableLog_boxed_2028_ = lean_unbox(v_enableLog_2027_);
v_res_2029_ = l_Lean_resolveGlobalName(v_m_2019_, v_inst_2020_, v_inst_2021_, v_inst_2022_, v_inst_2023_, v_inst_2024_, v_inst_2025_, v_id_2026_, v_enableLog_boxed_2028_);
return v_res_2029_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__0(lean_object* v_toPure_2030_, lean_object* v_nss_2031_, lean_object* v_____r_2032_){
_start:
{
lean_object* v___x_2033_; 
v___x_2033_ = lean_apply_2(v_toPure_2030_, lean_box(0), v_nss_2031_);
return v___x_2033_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__1(lean_object* v_____do__lift_2036_, lean_object* v_____do__lift_2037_, lean_object* v_id_2038_, uint8_t v_allowEmpty_2039_, lean_object* v_toPure_2040_, lean_object* v_inst_2041_, lean_object* v_inst_2042_, lean_object* v_toBind_2043_, lean_object* v_____do__lift_2044_){
_start:
{
lean_object* v_nss_2045_; 
lean_inc(v_id_2038_);
v_nss_2045_ = l_Lean_ResolveName_resolveNamespace(v_____do__lift_2036_, v_____do__lift_2037_, v_____do__lift_2044_, v_id_2038_);
if (v_allowEmpty_2039_ == 0)
{
uint8_t v___x_2046_; 
v___x_2046_ = l_List_isEmpty___redArg(v_nss_2045_);
if (v___x_2046_ == 0)
{
lean_object* v___x_2047_; 
lean_dec(v_toBind_2043_);
lean_dec_ref(v_inst_2042_);
lean_dec_ref(v_inst_2041_);
lean_dec(v_id_2038_);
v___x_2047_ = lean_apply_2(v_toPure_2040_, lean_box(0), v_nss_2045_);
return v___x_2047_;
}
else
{
lean_object* v___f_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; 
v___f_2048_ = lean_alloc_closure((void*)(l_Lean_resolveNamespaceCore___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2048_, 0, v_toPure_2040_);
lean_closure_set(v___f_2048_, 1, v_nss_2045_);
v___x_2049_ = ((lean_object*)(l_Lean_resolveNamespaceCore___redArg___lam__1___closed__0));
v___x_2050_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_id_2038_, v___x_2046_);
v___x_2051_ = lean_string_append(v___x_2049_, v___x_2050_);
lean_dec_ref(v___x_2050_);
v___x_2052_ = ((lean_object*)(l_Lean_resolveNamespaceCore___redArg___lam__1___closed__1));
v___x_2053_ = lean_string_append(v___x_2051_, v___x_2052_);
v___x_2054_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2054_, 0, v___x_2053_);
v___x_2055_ = l_Lean_MessageData_ofFormat(v___x_2054_);
v___x_2056_ = l_Lean_throwError___redArg(v_inst_2041_, v_inst_2042_, v___x_2055_);
v___x_2057_ = lean_apply_4(v_toBind_2043_, lean_box(0), lean_box(0), v___x_2056_, v___f_2048_);
return v___x_2057_;
}
}
else
{
lean_object* v___x_2058_; 
lean_dec(v_toBind_2043_);
lean_dec_ref(v_inst_2042_);
lean_dec_ref(v_inst_2041_);
lean_dec(v_id_2038_);
v___x_2058_ = lean_apply_2(v_toPure_2040_, lean_box(0), v_nss_2045_);
return v___x_2058_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__1___boxed(lean_object* v_____do__lift_2059_, lean_object* v_____do__lift_2060_, lean_object* v_id_2061_, lean_object* v_allowEmpty_2062_, lean_object* v_toPure_2063_, lean_object* v_inst_2064_, lean_object* v_inst_2065_, lean_object* v_toBind_2066_, lean_object* v_____do__lift_2067_){
_start:
{
uint8_t v_allowEmpty_boxed_2068_; lean_object* v_res_2069_; 
v_allowEmpty_boxed_2068_ = lean_unbox(v_allowEmpty_2062_);
v_res_2069_ = l_Lean_resolveNamespaceCore___redArg___lam__1(v_____do__lift_2059_, v_____do__lift_2060_, v_id_2061_, v_allowEmpty_boxed_2068_, v_toPure_2063_, v_inst_2064_, v_inst_2065_, v_toBind_2066_, v_____do__lift_2067_);
return v_res_2069_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__2(lean_object* v_____do__lift_2070_, lean_object* v_id_2071_, uint8_t v_allowEmpty_2072_, lean_object* v_toPure_2073_, lean_object* v_inst_2074_, lean_object* v_inst_2075_, lean_object* v_toBind_2076_, lean_object* v_getOpenDecls_2077_, lean_object* v_____do__lift_2078_){
_start:
{
lean_object* v___x_2079_; lean_object* v___f_2080_; lean_object* v___x_2081_; 
v___x_2079_ = lean_box(v_allowEmpty_2072_);
lean_inc(v_toBind_2076_);
v___f_2080_ = lean_alloc_closure((void*)(l_Lean_resolveNamespaceCore___redArg___lam__1___boxed), 9, 8);
lean_closure_set(v___f_2080_, 0, v_____do__lift_2070_);
lean_closure_set(v___f_2080_, 1, v_____do__lift_2078_);
lean_closure_set(v___f_2080_, 2, v_id_2071_);
lean_closure_set(v___f_2080_, 3, v___x_2079_);
lean_closure_set(v___f_2080_, 4, v_toPure_2073_);
lean_closure_set(v___f_2080_, 5, v_inst_2074_);
lean_closure_set(v___f_2080_, 6, v_inst_2075_);
lean_closure_set(v___f_2080_, 7, v_toBind_2076_);
v___x_2081_ = lean_apply_4(v_toBind_2076_, lean_box(0), lean_box(0), v_getOpenDecls_2077_, v___f_2080_);
return v___x_2081_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__2___boxed(lean_object* v_____do__lift_2082_, lean_object* v_id_2083_, lean_object* v_allowEmpty_2084_, lean_object* v_toPure_2085_, lean_object* v_inst_2086_, lean_object* v_inst_2087_, lean_object* v_toBind_2088_, lean_object* v_getOpenDecls_2089_, lean_object* v_____do__lift_2090_){
_start:
{
uint8_t v_allowEmpty_boxed_2091_; lean_object* v_res_2092_; 
v_allowEmpty_boxed_2091_ = lean_unbox(v_allowEmpty_2084_);
v_res_2092_ = l_Lean_resolveNamespaceCore___redArg___lam__2(v_____do__lift_2082_, v_id_2083_, v_allowEmpty_boxed_2091_, v_toPure_2085_, v_inst_2086_, v_inst_2087_, v_toBind_2088_, v_getOpenDecls_2089_, v_____do__lift_2090_);
return v_res_2092_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__3(lean_object* v_inst_2093_, lean_object* v_id_2094_, uint8_t v_allowEmpty_2095_, lean_object* v_toPure_2096_, lean_object* v_inst_2097_, lean_object* v_inst_2098_, lean_object* v_toBind_2099_, lean_object* v_____do__lift_2100_){
_start:
{
lean_object* v_getCurrNamespace_2101_; lean_object* v_getOpenDecls_2102_; lean_object* v___x_2103_; lean_object* v___f_2104_; lean_object* v___x_2105_; 
v_getCurrNamespace_2101_ = lean_ctor_get(v_inst_2093_, 0);
lean_inc(v_getCurrNamespace_2101_);
v_getOpenDecls_2102_ = lean_ctor_get(v_inst_2093_, 1);
lean_inc(v_getOpenDecls_2102_);
lean_dec_ref(v_inst_2093_);
v___x_2103_ = lean_box(v_allowEmpty_2095_);
lean_inc(v_toBind_2099_);
v___f_2104_ = lean_alloc_closure((void*)(l_Lean_resolveNamespaceCore___redArg___lam__2___boxed), 9, 8);
lean_closure_set(v___f_2104_, 0, v_____do__lift_2100_);
lean_closure_set(v___f_2104_, 1, v_id_2094_);
lean_closure_set(v___f_2104_, 2, v___x_2103_);
lean_closure_set(v___f_2104_, 3, v_toPure_2096_);
lean_closure_set(v___f_2104_, 4, v_inst_2097_);
lean_closure_set(v___f_2104_, 5, v_inst_2098_);
lean_closure_set(v___f_2104_, 6, v_toBind_2099_);
lean_closure_set(v___f_2104_, 7, v_getOpenDecls_2102_);
v___x_2105_ = lean_apply_4(v_toBind_2099_, lean_box(0), lean_box(0), v_getCurrNamespace_2101_, v___f_2104_);
return v___x_2105_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__3___boxed(lean_object* v_inst_2106_, lean_object* v_id_2107_, lean_object* v_allowEmpty_2108_, lean_object* v_toPure_2109_, lean_object* v_inst_2110_, lean_object* v_inst_2111_, lean_object* v_toBind_2112_, lean_object* v_____do__lift_2113_){
_start:
{
uint8_t v_allowEmpty_boxed_2114_; lean_object* v_res_2115_; 
v_allowEmpty_boxed_2114_ = lean_unbox(v_allowEmpty_2108_);
v_res_2115_ = l_Lean_resolveNamespaceCore___redArg___lam__3(v_inst_2106_, v_id_2107_, v_allowEmpty_boxed_2114_, v_toPure_2109_, v_inst_2110_, v_inst_2111_, v_toBind_2112_, v_____do__lift_2113_);
return v_res_2115_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg(lean_object* v_inst_2116_, lean_object* v_inst_2117_, lean_object* v_inst_2118_, lean_object* v_inst_2119_, lean_object* v_id_2120_, uint8_t v_allowEmpty_2121_){
_start:
{
lean_object* v_toApplicative_2122_; lean_object* v_toBind_2123_; lean_object* v_getEnv_2124_; lean_object* v_toPure_2125_; lean_object* v___x_2126_; lean_object* v___f_2127_; lean_object* v___x_2128_; 
v_toApplicative_2122_ = lean_ctor_get(v_inst_2116_, 0);
v_toBind_2123_ = lean_ctor_get(v_inst_2116_, 1);
lean_inc_n(v_toBind_2123_, 2);
v_getEnv_2124_ = lean_ctor_get(v_inst_2118_, 0);
lean_inc(v_getEnv_2124_);
lean_dec_ref(v_inst_2118_);
v_toPure_2125_ = lean_ctor_get(v_toApplicative_2122_, 1);
lean_inc(v_toPure_2125_);
v___x_2126_ = lean_box(v_allowEmpty_2121_);
v___f_2127_ = lean_alloc_closure((void*)(l_Lean_resolveNamespaceCore___redArg___lam__3___boxed), 8, 7);
lean_closure_set(v___f_2127_, 0, v_inst_2117_);
lean_closure_set(v___f_2127_, 1, v_id_2120_);
lean_closure_set(v___f_2127_, 2, v___x_2126_);
lean_closure_set(v___f_2127_, 3, v_toPure_2125_);
lean_closure_set(v___f_2127_, 4, v_inst_2116_);
lean_closure_set(v___f_2127_, 5, v_inst_2119_);
lean_closure_set(v___f_2127_, 6, v_toBind_2123_);
v___x_2128_ = lean_apply_4(v_toBind_2123_, lean_box(0), lean_box(0), v_getEnv_2124_, v___f_2127_);
return v___x_2128_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___boxed(lean_object* v_inst_2129_, lean_object* v_inst_2130_, lean_object* v_inst_2131_, lean_object* v_inst_2132_, lean_object* v_id_2133_, lean_object* v_allowEmpty_2134_){
_start:
{
uint8_t v_allowEmpty_boxed_2135_; lean_object* v_res_2136_; 
v_allowEmpty_boxed_2135_ = lean_unbox(v_allowEmpty_2134_);
v_res_2136_ = l_Lean_resolveNamespaceCore___redArg(v_inst_2129_, v_inst_2130_, v_inst_2131_, v_inst_2132_, v_id_2133_, v_allowEmpty_boxed_2135_);
return v_res_2136_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore(lean_object* v_m_2137_, lean_object* v_inst_2138_, lean_object* v_inst_2139_, lean_object* v_inst_2140_, lean_object* v_inst_2141_, lean_object* v_id_2142_, uint8_t v_allowEmpty_2143_){
_start:
{
lean_object* v___x_2144_; 
v___x_2144_ = l_Lean_resolveNamespaceCore___redArg(v_inst_2138_, v_inst_2139_, v_inst_2140_, v_inst_2141_, v_id_2142_, v_allowEmpty_2143_);
return v___x_2144_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___boxed(lean_object* v_m_2145_, lean_object* v_inst_2146_, lean_object* v_inst_2147_, lean_object* v_inst_2148_, lean_object* v_inst_2149_, lean_object* v_id_2150_, lean_object* v_allowEmpty_2151_){
_start:
{
uint8_t v_allowEmpty_boxed_2152_; lean_object* v_res_2153_; 
v_allowEmpty_boxed_2152_ = lean_unbox(v_allowEmpty_2151_);
v_res_2153_ = l_Lean_resolveNamespaceCore(v_m_2145_, v_inst_2146_, v_inst_2147_, v_inst_2148_, v_inst_2149_, v_id_2150_, v_allowEmpty_boxed_2152_);
return v_res_2153_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespace___redArg___lam__0(lean_object* v_x_2154_){
_start:
{
if (lean_obj_tag(v_x_2154_) == 0)
{
lean_object* v_ns_2155_; lean_object* v___x_2157_; uint8_t v_isShared_2158_; uint8_t v_isSharedCheck_2162_; 
v_ns_2155_ = lean_ctor_get(v_x_2154_, 0);
v_isSharedCheck_2162_ = !lean_is_exclusive(v_x_2154_);
if (v_isSharedCheck_2162_ == 0)
{
v___x_2157_ = v_x_2154_;
v_isShared_2158_ = v_isSharedCheck_2162_;
goto v_resetjp_2156_;
}
else
{
lean_inc(v_ns_2155_);
lean_dec(v_x_2154_);
v___x_2157_ = lean_box(0);
v_isShared_2158_ = v_isSharedCheck_2162_;
goto v_resetjp_2156_;
}
v_resetjp_2156_:
{
lean_object* v___x_2160_; 
if (v_isShared_2158_ == 0)
{
lean_ctor_set_tag(v___x_2157_, 1);
v___x_2160_ = v___x_2157_;
goto v_reusejp_2159_;
}
else
{
lean_object* v_reuseFailAlloc_2161_; 
v_reuseFailAlloc_2161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2161_, 0, v_ns_2155_);
v___x_2160_ = v_reuseFailAlloc_2161_;
goto v_reusejp_2159_;
}
v_reusejp_2159_:
{
return v___x_2160_;
}
}
}
else
{
lean_object* v___x_2163_; 
lean_dec_ref(v_x_2154_);
v___x_2163_ = lean_box(0);
return v___x_2163_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespace___redArg___lam__1(lean_object* v_x_2164_, lean_object* v_withRef_2165_, lean_object* v___x_2166_, lean_object* v_oldRef_2167_){
_start:
{
lean_object* v_ref_2168_; lean_object* v___x_2169_; 
v_ref_2168_ = l_Lean_replaceRef(v_x_2164_, v_oldRef_2167_);
v___x_2169_ = lean_apply_3(v_withRef_2165_, lean_box(0), v_ref_2168_, v___x_2166_);
return v___x_2169_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespace___redArg___lam__1___boxed(lean_object* v_x_2170_, lean_object* v_withRef_2171_, lean_object* v___x_2172_, lean_object* v_oldRef_2173_){
_start:
{
lean_object* v_res_2174_; 
v_res_2174_ = l_Lean_resolveNamespace___redArg___lam__1(v_x_2170_, v_withRef_2171_, v___x_2172_, v_oldRef_2173_);
lean_dec(v_oldRef_2173_);
lean_dec(v_x_2170_);
return v_res_2174_;
}
}
static lean_object* _init_l_Lean_resolveNamespace___redArg___closed__4(void){
_start:
{
lean_object* v___x_2181_; lean_object* v___x_2182_; 
v___x_2181_ = ((lean_object*)(l_Lean_resolveNamespace___redArg___closed__3));
v___x_2182_ = l_Lean_MessageData_ofFormat(v___x_2181_);
return v___x_2182_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespace___redArg(lean_object* v_inst_2183_, lean_object* v_inst_2184_, lean_object* v_inst_2185_, lean_object* v_inst_2186_, lean_object* v_x_2187_){
_start:
{
if (lean_obj_tag(v_x_2187_) == 3)
{
lean_object* v_toApplicative_2188_; lean_object* v_toBind_2189_; lean_object* v_toPure_2190_; lean_object* v_toMonadRef_2191_; lean_object* v_val_2192_; lean_object* v_preresolved_2193_; lean_object* v___f_2194_; lean_object* v___x_2195_; lean_object* v_pre_2196_; uint8_t v___x_2197_; 
v_toApplicative_2188_ = lean_ctor_get(v_inst_2183_, 0);
v_toBind_2189_ = lean_ctor_get(v_inst_2183_, 1);
lean_inc(v_toBind_2189_);
v_toPure_2190_ = lean_ctor_get(v_toApplicative_2188_, 1);
v_toMonadRef_2191_ = lean_ctor_get(v_inst_2186_, 1);
v_val_2192_ = lean_ctor_get(v_x_2187_, 2);
v_preresolved_2193_ = lean_ctor_get(v_x_2187_, 3);
v___f_2194_ = ((lean_object*)(l_Lean_resolveNamespace___redArg___closed__0));
v___x_2195_ = ((lean_object*)(l_Lean_resolveNamespace___redArg___closed__1));
lean_inc(v_preresolved_2193_);
v_pre_2196_ = l_List_filterMapTR_go___redArg(v___f_2194_, v_preresolved_2193_, v___x_2195_);
v___x_2197_ = l_List_isEmpty___redArg(v_pre_2196_);
if (v___x_2197_ == 0)
{
lean_object* v___x_2198_; 
lean_inc(v_toPure_2190_);
lean_dec(v_toBind_2189_);
lean_dec_ref_known(v_x_2187_, 4);
lean_dec_ref(v_inst_2186_);
lean_dec_ref(v_inst_2185_);
lean_dec_ref(v_inst_2184_);
lean_dec_ref(v_inst_2183_);
v___x_2198_ = lean_apply_2(v_toPure_2190_, lean_box(0), v_pre_2196_);
return v___x_2198_;
}
else
{
lean_object* v_getRef_2199_; lean_object* v_withRef_2200_; uint8_t v___x_2201_; lean_object* v___x_2202_; lean_object* v___f_2203_; lean_object* v___x_2204_; 
lean_dec(v_pre_2196_);
v_getRef_2199_ = lean_ctor_get(v_toMonadRef_2191_, 0);
lean_inc(v_getRef_2199_);
v_withRef_2200_ = lean_ctor_get(v_toMonadRef_2191_, 1);
lean_inc(v_withRef_2200_);
v___x_2201_ = 0;
lean_inc(v_val_2192_);
v___x_2202_ = l_Lean_resolveNamespaceCore___redArg(v_inst_2183_, v_inst_2184_, v_inst_2185_, v_inst_2186_, v_val_2192_, v___x_2201_);
v___f_2203_ = lean_alloc_closure((void*)(l_Lean_resolveNamespace___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_2203_, 0, v_x_2187_);
lean_closure_set(v___f_2203_, 1, v_withRef_2200_);
lean_closure_set(v___f_2203_, 2, v___x_2202_);
v___x_2204_ = lean_apply_4(v_toBind_2189_, lean_box(0), lean_box(0), v_getRef_2199_, v___f_2203_);
return v___x_2204_;
}
}
else
{
lean_object* v___x_2205_; lean_object* v___x_2206_; 
lean_dec_ref(v_inst_2185_);
lean_dec_ref(v_inst_2184_);
v___x_2205_ = lean_obj_once(&l_Lean_resolveNamespace___redArg___closed__4, &l_Lean_resolveNamespace___redArg___closed__4_once, _init_l_Lean_resolveNamespace___redArg___closed__4);
v___x_2206_ = l_Lean_throwErrorAt___redArg(v_inst_2183_, v_inst_2186_, v_x_2187_, v___x_2205_);
return v___x_2206_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespace(lean_object* v_m_2207_, lean_object* v_inst_2208_, lean_object* v_inst_2209_, lean_object* v_inst_2210_, lean_object* v_inst_2211_, lean_object* v_x_2212_){
_start:
{
lean_object* v___x_2213_; 
v___x_2213_ = l_Lean_resolveNamespace___redArg(v_inst_2208_, v_inst_2209_, v_inst_2210_, v_inst_2211_, v_x_2212_);
return v___x_2213_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveUniqueNamespace___redArg___lam__0(lean_object* v_id_2216_, lean_object* v___f_2217_, lean_object* v_inst_2218_, lean_object* v_inst_2219_, lean_object* v_toPure_2220_, lean_object* v_____do__lift_2221_){
_start:
{
if (lean_obj_tag(v_____do__lift_2221_) == 1)
{
lean_object* v_tail_2237_; 
v_tail_2237_ = lean_ctor_get(v_____do__lift_2221_, 1);
if (lean_obj_tag(v_tail_2237_) == 0)
{
lean_object* v_head_2238_; lean_object* v___x_2239_; 
lean_dec_ref(v_inst_2219_);
lean_dec_ref(v_inst_2218_);
lean_dec_ref(v___f_2217_);
v_head_2238_ = lean_ctor_get(v_____do__lift_2221_, 0);
lean_inc(v_head_2238_);
lean_dec_ref_known(v_____do__lift_2221_, 2);
v___x_2239_ = lean_apply_2(v_toPure_2220_, lean_box(0), v_head_2238_);
return v___x_2239_;
}
else
{
lean_dec(v_toPure_2220_);
goto v___jp_2222_;
}
}
else
{
lean_dec(v_toPure_2220_);
goto v___jp_2222_;
}
v___jp_2222_:
{
lean_object* v___x_2223_; lean_object* v___x_2224_; uint8_t v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; 
v___x_2223_ = ((lean_object*)(l_Lean_resolveUniqueNamespace___redArg___lam__0___closed__0));
v___x_2224_ = l_Lean_TSyntax_getId(v_id_2216_);
v___x_2225_ = 1;
v___x_2226_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2224_, v___x_2225_);
v___x_2227_ = lean_string_append(v___x_2223_, v___x_2226_);
lean_dec_ref(v___x_2226_);
v___x_2228_ = ((lean_object*)(l_Lean_resolveUniqueNamespace___redArg___lam__0___closed__1));
v___x_2229_ = lean_string_append(v___x_2227_, v___x_2228_);
v___x_2230_ = l_List_toString___redArg(v___f_2217_, v_____do__lift_2221_);
v___x_2231_ = lean_string_append(v___x_2229_, v___x_2230_);
lean_dec_ref(v___x_2230_);
v___x_2232_ = ((lean_object*)(l_Lean_resolveNamespaceCore___redArg___lam__1___closed__1));
v___x_2233_ = lean_string_append(v___x_2231_, v___x_2232_);
v___x_2234_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2234_, 0, v___x_2233_);
v___x_2235_ = l_Lean_MessageData_ofFormat(v___x_2234_);
v___x_2236_ = l_Lean_throwError___redArg(v_inst_2218_, v_inst_2219_, v___x_2235_);
return v___x_2236_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveUniqueNamespace___redArg___lam__0___boxed(lean_object* v_id_2240_, lean_object* v___f_2241_, lean_object* v_inst_2242_, lean_object* v_inst_2243_, lean_object* v_toPure_2244_, lean_object* v_____do__lift_2245_){
_start:
{
lean_object* v_res_2246_; 
v_res_2246_ = l_Lean_resolveUniqueNamespace___redArg___lam__0(v_id_2240_, v___f_2241_, v_inst_2242_, v_inst_2243_, v_toPure_2244_, v_____do__lift_2245_);
lean_dec(v_id_2240_);
return v_res_2246_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveUniqueNamespace___redArg(lean_object* v_inst_2248_, lean_object* v_inst_2249_, lean_object* v_inst_2250_, lean_object* v_inst_2251_, lean_object* v_id_2252_){
_start:
{
lean_object* v_toApplicative_2253_; lean_object* v_toBind_2254_; lean_object* v_toPure_2255_; lean_object* v___f_2256_; lean_object* v___x_2257_; lean_object* v___f_2258_; lean_object* v___x_2259_; 
v_toApplicative_2253_ = lean_ctor_get(v_inst_2248_, 0);
v_toBind_2254_ = lean_ctor_get(v_inst_2248_, 1);
lean_inc(v_toBind_2254_);
v_toPure_2255_ = lean_ctor_get(v_toApplicative_2253_, 1);
lean_inc(v_toPure_2255_);
v___f_2256_ = ((lean_object*)(l_Lean_resolveUniqueNamespace___redArg___closed__0));
lean_inc(v_id_2252_);
lean_inc_ref(v_inst_2251_);
lean_inc_ref(v_inst_2248_);
v___x_2257_ = l_Lean_resolveNamespace___redArg(v_inst_2248_, v_inst_2249_, v_inst_2250_, v_inst_2251_, v_id_2252_);
v___f_2258_ = lean_alloc_closure((void*)(l_Lean_resolveUniqueNamespace___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_2258_, 0, v_id_2252_);
lean_closure_set(v___f_2258_, 1, v___f_2256_);
lean_closure_set(v___f_2258_, 2, v_inst_2248_);
lean_closure_set(v___f_2258_, 3, v_inst_2251_);
lean_closure_set(v___f_2258_, 4, v_toPure_2255_);
v___x_2259_ = lean_apply_4(v_toBind_2254_, lean_box(0), lean_box(0), v___x_2257_, v___f_2258_);
return v___x_2259_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveUniqueNamespace(lean_object* v_m_2260_, lean_object* v_inst_2261_, lean_object* v_inst_2262_, lean_object* v_inst_2263_, lean_object* v_inst_2264_, lean_object* v_id_2265_){
_start:
{
lean_object* v___x_2266_; 
v___x_2266_ = l_Lean_resolveUniqueNamespace___redArg(v_inst_2261_, v_inst_2262_, v_inst_2263_, v_inst_2264_, v_id_2265_);
return v___x_2266_;
}
}
LEAN_EXPORT uint8_t l_Lean_filterFieldList___redArg___lam__0(lean_object* v_x_2267_){
_start:
{
lean_object* v_snd_2268_; uint8_t v___x_2269_; 
v_snd_2268_ = lean_ctor_get(v_x_2267_, 1);
v___x_2269_ = l_List_isEmpty___redArg(v_snd_2268_);
return v___x_2269_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg___lam__0___boxed(lean_object* v_x_2270_){
_start:
{
uint8_t v_res_2271_; lean_object* v_r_2272_; 
v_res_2271_ = l_Lean_filterFieldList___redArg___lam__0(v_x_2270_);
lean_dec_ref(v_x_2270_);
v_r_2272_ = lean_box(v_res_2271_);
return v_r_2272_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg___lam__1(lean_object* v_x_2273_){
_start:
{
lean_object* v_fst_2274_; 
v_fst_2274_ = lean_ctor_get(v_x_2273_, 0);
lean_inc(v_fst_2274_);
return v_fst_2274_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg___lam__1___boxed(lean_object* v_x_2275_){
_start:
{
lean_object* v_res_2276_; 
v_res_2276_ = l_Lean_filterFieldList___redArg___lam__1(v_x_2275_);
lean_dec_ref(v_x_2275_);
return v_res_2276_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg___lam__2(lean_object* v___f_2277_, lean_object* v_cs_2278_, lean_object* v_toPure_2279_, lean_object* v_____r_2280_){
_start:
{
lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; 
v___x_2281_ = lean_box(0);
v___x_2282_ = l_List_mapTR_loop___redArg(v___f_2277_, v_cs_2278_, v___x_2281_);
v___x_2283_ = lean_apply_2(v_toPure_2279_, lean_box(0), v___x_2282_);
return v___x_2283_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg___lam__3(lean_object* v___f_2284_, lean_object* v_____r_2285_){
_start:
{
lean_object* v___x_2286_; 
v___x_2286_ = lean_apply_1(v___f_2284_, v_____r_2285_);
return v___x_2286_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg___lam__4(lean_object* v_inst_2287_, lean_object* v_inst_2288_, lean_object* v_inst_2289_, lean_object* v_n_2290_, lean_object* v_toBind_2291_, lean_object* v___f_2292_, lean_object* v_____do__lift_2293_){
_start:
{
lean_object* v___x_2294_; lean_object* v___x_2295_; 
v___x_2294_ = l_Lean_throwUnknownConstantAt___redArg(v_inst_2287_, v_inst_2288_, v_inst_2289_, v_____do__lift_2293_, v_n_2290_);
v___x_2295_ = lean_apply_4(v_toBind_2291_, lean_box(0), lean_box(0), v___x_2294_, v___f_2292_);
return v___x_2295_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg(lean_object* v_inst_2298_, lean_object* v_inst_2299_, lean_object* v_inst_2300_, lean_object* v_n_2301_, lean_object* v_cs_2302_){
_start:
{
lean_object* v_toApplicative_2303_; lean_object* v_toBind_2304_; lean_object* v_toPure_2305_; lean_object* v_toMonadRef_2306_; lean_object* v___f_2307_; lean_object* v___f_2308_; lean_object* v___x_2309_; lean_object* v_cs_2310_; lean_object* v___f_2311_; uint8_t v___x_2312_; 
v_toApplicative_2303_ = lean_ctor_get(v_inst_2298_, 0);
v_toBind_2304_ = lean_ctor_get(v_inst_2298_, 1);
lean_inc(v_toBind_2304_);
v_toPure_2305_ = lean_ctor_get(v_toApplicative_2303_, 1);
v_toMonadRef_2306_ = lean_ctor_get(v_inst_2300_, 1);
v___f_2307_ = ((lean_object*)(l_Lean_filterFieldList___redArg___closed__0));
v___f_2308_ = ((lean_object*)(l_Lean_filterFieldList___redArg___closed__1));
v___x_2309_ = lean_box(0);
v_cs_2310_ = l_List_filterTR_loop___redArg(v___f_2307_, v_cs_2302_, v___x_2309_);
lean_inc(v_toPure_2305_);
lean_inc(v_cs_2310_);
v___f_2311_ = lean_alloc_closure((void*)(l_Lean_filterFieldList___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2311_, 0, v___f_2308_);
lean_closure_set(v___f_2311_, 1, v_cs_2310_);
lean_closure_set(v___f_2311_, 2, v_toPure_2305_);
v___x_2312_ = l_List_isEmpty___redArg(v_cs_2310_);
if (v___x_2312_ == 0)
{
lean_object* v___x_2313_; lean_object* v___x_2314_; 
lean_inc(v_toPure_2305_);
lean_dec_ref(v___f_2311_);
lean_dec(v_toBind_2304_);
lean_dec(v_n_2301_);
lean_dec_ref(v_inst_2300_);
lean_dec_ref(v_inst_2299_);
lean_dec_ref(v_inst_2298_);
v___x_2313_ = lean_box(0);
v___x_2314_ = l_Lean_filterFieldList___redArg___lam__2(v___f_2308_, v_cs_2310_, v_toPure_2305_, v___x_2313_);
return v___x_2314_;
}
else
{
lean_object* v_getRef_2315_; lean_object* v___f_2316_; lean_object* v___f_2317_; lean_object* v___x_2318_; 
lean_dec(v_cs_2310_);
v_getRef_2315_ = lean_ctor_get(v_toMonadRef_2306_, 0);
lean_inc(v_getRef_2315_);
v___f_2316_ = lean_alloc_closure((void*)(l_Lean_filterFieldList___redArg___lam__3), 2, 1);
lean_closure_set(v___f_2316_, 0, v___f_2311_);
lean_inc(v_toBind_2304_);
v___f_2317_ = lean_alloc_closure((void*)(l_Lean_filterFieldList___redArg___lam__4), 7, 6);
lean_closure_set(v___f_2317_, 0, v_inst_2298_);
lean_closure_set(v___f_2317_, 1, v_inst_2299_);
lean_closure_set(v___f_2317_, 2, v_inst_2300_);
lean_closure_set(v___f_2317_, 3, v_n_2301_);
lean_closure_set(v___f_2317_, 4, v_toBind_2304_);
lean_closure_set(v___f_2317_, 5, v___f_2316_);
v___x_2318_ = lean_apply_4(v_toBind_2304_, lean_box(0), lean_box(0), v_getRef_2315_, v___f_2317_);
return v___x_2318_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList(lean_object* v_m_2319_, lean_object* v_inst_2320_, lean_object* v_inst_2321_, lean_object* v_inst_2322_, lean_object* v_n_2323_, lean_object* v_cs_2324_){
_start:
{
lean_object* v___x_2325_; 
v___x_2325_ = l_Lean_filterFieldList___redArg(v_inst_2320_, v_inst_2321_, v_inst_2322_, v_n_2323_, v_cs_2324_);
return v___x_2325_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___redArg___lam__0(lean_object* v_inst_2326_, lean_object* v_inst_2327_, lean_object* v_inst_2328_, lean_object* v_n_2329_, lean_object* v_cs_2330_){
_start:
{
lean_object* v___x_2331_; 
v___x_2331_ = l_Lean_filterFieldList___redArg(v_inst_2326_, v_inst_2327_, v_inst_2328_, v_n_2329_, v_cs_2330_);
return v___x_2331_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___redArg(lean_object* v_inst_2332_, lean_object* v_inst_2333_, lean_object* v_inst_2334_, lean_object* v_inst_2335_, lean_object* v_inst_2336_, lean_object* v_inst_2337_, lean_object* v_inst_2338_, lean_object* v_n_2339_){
_start:
{
lean_object* v_toBind_2340_; lean_object* v___f_2341_; uint8_t v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; 
v_toBind_2340_ = lean_ctor_get(v_inst_2332_, 1);
lean_inc(v_toBind_2340_);
lean_inc(v_n_2339_);
lean_inc_ref(v_inst_2334_);
lean_inc_ref(v_inst_2332_);
v___f_2341_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___redArg___lam__0), 5, 4);
lean_closure_set(v___f_2341_, 0, v_inst_2332_);
lean_closure_set(v___f_2341_, 1, v_inst_2334_);
lean_closure_set(v___f_2341_, 2, v_inst_2338_);
lean_closure_set(v___f_2341_, 3, v_n_2339_);
v___x_2342_ = 1;
v___x_2343_ = l_Lean_resolveGlobalName___redArg(v_inst_2332_, v_inst_2333_, v_inst_2334_, v_inst_2335_, v_inst_2336_, v_inst_2337_, v_n_2339_, v___x_2342_);
v___x_2344_ = lean_apply_4(v_toBind_2340_, lean_box(0), lean_box(0), v___x_2343_, v___f_2341_);
return v___x_2344_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore(lean_object* v_m_2345_, lean_object* v_inst_2346_, lean_object* v_inst_2347_, lean_object* v_inst_2348_, lean_object* v_inst_2349_, lean_object* v_inst_2350_, lean_object* v_inst_2351_, lean_object* v_inst_2352_, lean_object* v_n_2353_){
_start:
{
lean_object* v___x_2354_; 
v___x_2354_ = l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___redArg(v_inst_2346_, v_inst_2347_, v_inst_2348_, v_inst_2349_, v_inst_2350_, v_inst_2351_, v_inst_2352_, v_n_2353_);
return v___x_2354_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNoOverload___redArg___lam__0(lean_object* v_declName_2355_){
_start:
{
lean_object* v___x_2356_; lean_object* v___x_2357_; 
v___x_2356_ = lean_box(0);
v___x_2357_ = l_Lean_mkConst(v_declName_2355_, v___x_2356_);
return v___x_2357_;
}
}
static lean_object* _init_l_Lean_ensureNoOverload___redArg___closed__2(void){
_start:
{
lean_object* v___x_2360_; lean_object* v___x_2361_; 
v___x_2360_ = ((lean_object*)(l_Lean_ensureNoOverload___redArg___closed__1));
v___x_2361_ = l_Lean_stringToMessageData(v___x_2360_);
return v___x_2361_;
}
}
static lean_object* _init_l_Lean_ensureNoOverload___redArg___closed__4(void){
_start:
{
lean_object* v___x_2363_; lean_object* v___x_2364_; 
v___x_2363_ = ((lean_object*)(l_Lean_ensureNoOverload___redArg___closed__3));
v___x_2364_ = l_Lean_stringToMessageData(v___x_2363_);
return v___x_2364_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNoOverload___redArg(lean_object* v_inst_2366_, lean_object* v_inst_2367_, lean_object* v_n_2368_, lean_object* v_cs_2369_){
_start:
{
lean_object* v_toApplicative_2370_; lean_object* v_toPure_2371_; lean_object* v___f_2372_; 
v_toApplicative_2370_ = lean_ctor_get(v_inst_2366_, 0);
v_toPure_2371_ = lean_ctor_get(v_toApplicative_2370_, 1);
v___f_2372_ = ((lean_object*)(l_Lean_ensureNoOverload___redArg___closed__0));
if (lean_obj_tag(v_cs_2369_) == 1)
{
lean_object* v_tail_2386_; 
v_tail_2386_ = lean_ctor_get(v_cs_2369_, 1);
if (lean_obj_tag(v_tail_2386_) == 0)
{
lean_object* v_head_2387_; lean_object* v___x_2388_; 
lean_inc(v_toPure_2371_);
lean_dec(v_n_2368_);
lean_dec_ref(v_inst_2367_);
lean_dec_ref(v_inst_2366_);
v_head_2387_ = lean_ctor_get(v_cs_2369_, 0);
lean_inc(v_head_2387_);
lean_dec_ref_known(v_cs_2369_, 2);
v___x_2388_ = lean_apply_2(v_toPure_2371_, lean_box(0), v_head_2387_);
return v___x_2388_;
}
else
{
goto v___jp_2373_;
}
}
else
{
goto v___jp_2373_;
}
v___jp_2373_:
{
lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; 
v___x_2374_ = lean_obj_once(&l_Lean_ensureNoOverload___redArg___closed__2, &l_Lean_ensureNoOverload___redArg___closed__2_once, _init_l_Lean_ensureNoOverload___redArg___closed__2);
v___x_2375_ = l_Lean_MessageData_ofName(v_n_2368_);
v___x_2376_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2376_, 0, v___x_2374_);
lean_ctor_set(v___x_2376_, 1, v___x_2375_);
v___x_2377_ = lean_obj_once(&l_Lean_ensureNoOverload___redArg___closed__4, &l_Lean_ensureNoOverload___redArg___closed__4_once, _init_l_Lean_ensureNoOverload___redArg___closed__4);
v___x_2378_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2378_, 0, v___x_2376_);
lean_ctor_set(v___x_2378_, 1, v___x_2377_);
v___x_2379_ = lean_box(0);
v___x_2380_ = l_List_mapTR_loop___redArg(v___f_2372_, v_cs_2369_, v___x_2379_);
v___x_2381_ = ((lean_object*)(l_Lean_ensureNoOverload___redArg___closed__5));
v___x_2382_ = l_List_mapTR_loop___redArg(v___x_2381_, v___x_2380_, v___x_2379_);
v___x_2383_ = l_Lean_MessageData_ofList(v___x_2382_);
v___x_2384_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2384_, 0, v___x_2378_);
lean_ctor_set(v___x_2384_, 1, v___x_2383_);
v___x_2385_ = l_Lean_throwError___redArg(v_inst_2366_, v_inst_2367_, v___x_2384_);
return v___x_2385_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNoOverload(lean_object* v_m_2389_, lean_object* v_inst_2390_, lean_object* v_inst_2391_, lean_object* v_n_2392_, lean_object* v_cs_2393_){
_start:
{
lean_object* v___x_2394_; 
v___x_2394_ = l_Lean_ensureNoOverload___redArg(v_inst_2390_, v_inst_2391_, v_n_2392_, v_cs_2393_);
return v___x_2394_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverloadCore___redArg___lam__0(lean_object* v_inst_2395_, lean_object* v_inst_2396_, lean_object* v_n_2397_, lean_object* v_____do__lift_2398_){
_start:
{
lean_object* v___x_2399_; 
v___x_2399_ = l_Lean_ensureNoOverload___redArg(v_inst_2395_, v_inst_2396_, v_n_2397_, v_____do__lift_2398_);
return v___x_2399_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverloadCore___redArg(lean_object* v_inst_2400_, lean_object* v_inst_2401_, lean_object* v_inst_2402_, lean_object* v_inst_2403_, lean_object* v_inst_2404_, lean_object* v_inst_2405_, lean_object* v_inst_2406_, lean_object* v_n_2407_){
_start:
{
lean_object* v_toBind_2408_; lean_object* v___f_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; 
v_toBind_2408_ = lean_ctor_get(v_inst_2400_, 1);
lean_inc(v_toBind_2408_);
lean_inc(v_n_2407_);
lean_inc_ref(v_inst_2406_);
lean_inc_ref(v_inst_2400_);
v___f_2409_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalConstNoOverloadCore___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2409_, 0, v_inst_2400_);
lean_closure_set(v___f_2409_, 1, v_inst_2406_);
lean_closure_set(v___f_2409_, 2, v_n_2407_);
v___x_2410_ = l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___redArg(v_inst_2400_, v_inst_2401_, v_inst_2402_, v_inst_2403_, v_inst_2404_, v_inst_2405_, v_inst_2406_, v_n_2407_);
v___x_2411_ = lean_apply_4(v_toBind_2408_, lean_box(0), lean_box(0), v___x_2410_, v___f_2409_);
return v___x_2411_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverloadCore(lean_object* v_m_2412_, lean_object* v_inst_2413_, lean_object* v_inst_2414_, lean_object* v_inst_2415_, lean_object* v_inst_2416_, lean_object* v_inst_2417_, lean_object* v_inst_2418_, lean_object* v_inst_2419_, lean_object* v_n_2420_){
_start:
{
lean_object* v___x_2421_; 
v___x_2421_ = l_Lean_resolveGlobalConstNoOverloadCore___redArg(v_inst_2413_, v_inst_2414_, v_inst_2415_, v_inst_2416_, v_inst_2417_, v_inst_2418_, v_inst_2419_, v_n_2420_);
return v___x_2421_;
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___redArg___lam__0(lean_object* v_x_2422_){
_start:
{
if (lean_obj_tag(v_x_2422_) == 1)
{
lean_object* v_fields_2423_; 
v_fields_2423_ = lean_ctor_get(v_x_2422_, 1);
if (lean_obj_tag(v_fields_2423_) == 0)
{
lean_object* v_n_2424_; lean_object* v___x_2425_; 
v_n_2424_ = lean_ctor_get(v_x_2422_, 0);
lean_inc(v_n_2424_);
v___x_2425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2425_, 0, v_n_2424_);
return v___x_2425_;
}
else
{
lean_object* v___x_2426_; 
v___x_2426_ = lean_box(0);
return v___x_2426_;
}
}
else
{
lean_object* v___x_2427_; 
v___x_2427_ = lean_box(0);
return v___x_2427_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___redArg___lam__0___boxed(lean_object* v_x_2428_){
_start:
{
lean_object* v_res_2429_; 
v_res_2429_ = l_Lean_preprocessSyntaxAndResolve___redArg___lam__0(v_x_2428_);
lean_dec_ref(v_x_2428_);
return v_res_2429_;
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___redArg___lam__1(lean_object* v_stx_2430_, lean_object* v_withRef_2431_, lean_object* v___x_2432_, lean_object* v_oldRef_2433_){
_start:
{
lean_object* v_ref_2434_; lean_object* v___x_2435_; 
v_ref_2434_ = l_Lean_replaceRef(v_stx_2430_, v_oldRef_2433_);
v___x_2435_ = lean_apply_3(v_withRef_2431_, lean_box(0), v_ref_2434_, v___x_2432_);
return v___x_2435_;
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___redArg___lam__1___boxed(lean_object* v_stx_2436_, lean_object* v_withRef_2437_, lean_object* v___x_2438_, lean_object* v_oldRef_2439_){
_start:
{
lean_object* v_res_2440_; 
v_res_2440_ = l_Lean_preprocessSyntaxAndResolve___redArg___lam__1(v_stx_2436_, v_withRef_2437_, v___x_2438_, v_oldRef_2439_);
lean_dec(v_oldRef_2439_);
lean_dec(v_stx_2436_);
return v_res_2440_;
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___redArg(lean_object* v_inst_2442_, lean_object* v_inst_2443_, lean_object* v_stx_2444_, lean_object* v_k_2445_){
_start:
{
if (lean_obj_tag(v_stx_2444_) == 3)
{
lean_object* v_toApplicative_2446_; lean_object* v_toBind_2447_; lean_object* v_toPure_2448_; lean_object* v_toMonadRef_2449_; lean_object* v_val_2450_; lean_object* v_preresolved_2451_; lean_object* v___f_2452_; lean_object* v___x_2453_; lean_object* v_pre_2454_; uint8_t v___x_2455_; 
v_toApplicative_2446_ = lean_ctor_get(v_inst_2442_, 0);
lean_inc_ref(v_toApplicative_2446_);
v_toBind_2447_ = lean_ctor_get(v_inst_2442_, 1);
lean_inc(v_toBind_2447_);
lean_dec_ref(v_inst_2442_);
v_toPure_2448_ = lean_ctor_get(v_toApplicative_2446_, 1);
lean_inc(v_toPure_2448_);
lean_dec_ref(v_toApplicative_2446_);
v_toMonadRef_2449_ = lean_ctor_get(v_inst_2443_, 1);
lean_inc_ref(v_toMonadRef_2449_);
lean_dec_ref(v_inst_2443_);
v_val_2450_ = lean_ctor_get(v_stx_2444_, 2);
v_preresolved_2451_ = lean_ctor_get(v_stx_2444_, 3);
v___f_2452_ = ((lean_object*)(l_Lean_preprocessSyntaxAndResolve___redArg___closed__0));
v___x_2453_ = ((lean_object*)(l_Lean_resolveNamespace___redArg___closed__1));
lean_inc(v_preresolved_2451_);
v_pre_2454_ = l_List_filterMapTR_go___redArg(v___f_2452_, v_preresolved_2451_, v___x_2453_);
v___x_2455_ = l_List_isEmpty___redArg(v_pre_2454_);
if (v___x_2455_ == 0)
{
lean_object* v___x_2456_; 
lean_dec_ref(v_toMonadRef_2449_);
lean_dec_ref_known(v_stx_2444_, 4);
lean_dec(v_toBind_2447_);
lean_dec(v_k_2445_);
v___x_2456_ = lean_apply_2(v_toPure_2448_, lean_box(0), v_pre_2454_);
return v___x_2456_;
}
else
{
lean_object* v_getRef_2457_; lean_object* v_withRef_2458_; lean_object* v___x_2459_; lean_object* v___f_2460_; lean_object* v___x_2461_; 
lean_dec(v_pre_2454_);
lean_dec(v_toPure_2448_);
v_getRef_2457_ = lean_ctor_get(v_toMonadRef_2449_, 0);
lean_inc(v_getRef_2457_);
v_withRef_2458_ = lean_ctor_get(v_toMonadRef_2449_, 1);
lean_inc(v_withRef_2458_);
lean_dec_ref(v_toMonadRef_2449_);
lean_inc(v_val_2450_);
v___x_2459_ = lean_apply_1(v_k_2445_, v_val_2450_);
v___f_2460_ = lean_alloc_closure((void*)(l_Lean_preprocessSyntaxAndResolve___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_2460_, 0, v_stx_2444_);
lean_closure_set(v___f_2460_, 1, v_withRef_2458_);
lean_closure_set(v___f_2460_, 2, v___x_2459_);
v___x_2461_ = lean_apply_4(v_toBind_2447_, lean_box(0), lean_box(0), v_getRef_2457_, v___f_2460_);
return v___x_2461_;
}
}
else
{
lean_object* v___x_2462_; lean_object* v___x_2463_; 
lean_dec(v_k_2445_);
v___x_2462_ = lean_obj_once(&l_Lean_resolveNamespace___redArg___closed__4, &l_Lean_resolveNamespace___redArg___closed__4_once, _init_l_Lean_resolveNamespace___redArg___closed__4);
v___x_2463_ = l_Lean_throwErrorAt___redArg(v_inst_2442_, v_inst_2443_, v_stx_2444_, v___x_2462_);
return v___x_2463_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve(lean_object* v_m_2464_, lean_object* v_inst_2465_, lean_object* v_inst_2466_, lean_object* v_stx_2467_, lean_object* v_k_2468_){
_start:
{
lean_object* v___x_2469_; 
v___x_2469_ = l_Lean_preprocessSyntaxAndResolve___redArg(v_inst_2465_, v_inst_2466_, v_stx_2467_, v_k_2468_);
return v___x_2469_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst___redArg(lean_object* v_inst_2470_, lean_object* v_inst_2471_, lean_object* v_inst_2472_, lean_object* v_inst_2473_, lean_object* v_inst_2474_, lean_object* v_inst_2475_, lean_object* v_inst_2476_, lean_object* v_stx_2477_){
_start:
{
lean_object* v___x_2478_; lean_object* v___x_2479_; 
lean_inc_ref(v_inst_2476_);
lean_inc_ref(v_inst_2470_);
v___x_2478_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore), 9, 8);
lean_closure_set(v___x_2478_, 0, lean_box(0));
lean_closure_set(v___x_2478_, 1, v_inst_2470_);
lean_closure_set(v___x_2478_, 2, v_inst_2471_);
lean_closure_set(v___x_2478_, 3, v_inst_2472_);
lean_closure_set(v___x_2478_, 4, v_inst_2473_);
lean_closure_set(v___x_2478_, 5, v_inst_2474_);
lean_closure_set(v___x_2478_, 6, v_inst_2475_);
lean_closure_set(v___x_2478_, 7, v_inst_2476_);
v___x_2479_ = l_Lean_preprocessSyntaxAndResolve___redArg(v_inst_2470_, v_inst_2476_, v_stx_2477_, v___x_2478_);
return v___x_2479_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst(lean_object* v_m_2480_, lean_object* v_inst_2481_, lean_object* v_inst_2482_, lean_object* v_inst_2483_, lean_object* v_inst_2484_, lean_object* v_inst_2485_, lean_object* v_inst_2486_, lean_object* v_inst_2487_, lean_object* v_stx_2488_){
_start:
{
lean_object* v___x_2489_; 
v___x_2489_ = l_Lean_resolveGlobalConst___redArg(v_inst_2481_, v_inst_2482_, v_inst_2483_, v_inst_2484_, v_inst_2485_, v_inst_2486_, v_inst_2487_, v_stx_2488_);
return v___x_2489_;
}
}
static lean_object* _init_l_Lean_ensureNonAmbiguous___redArg___closed__1(void){
_start:
{
lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; 
v___x_2491_ = ((lean_object*)(l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__2));
v___x_2492_ = lean_unsigned_to_nat(11u);
v___x_2493_ = lean_unsigned_to_nat(429u);
v___x_2494_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___redArg___closed__0));
v___x_2495_ = ((lean_object*)(l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__0));
v___x_2496_ = l_mkPanicMessageWithDecl(v___x_2495_, v___x_2494_, v___x_2493_, v___x_2492_, v___x_2491_);
return v___x_2496_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNonAmbiguous___redArg(lean_object* v_inst_2500_, lean_object* v_inst_2501_, lean_object* v_id_2502_, lean_object* v_cs_2503_){
_start:
{
if (lean_obj_tag(v_cs_2503_) == 0)
{
lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; 
lean_dec(v_id_2502_);
lean_dec_ref(v_inst_2501_);
v___x_2504_ = lean_box(0);
v___x_2505_ = l_instInhabitedOfMonad___redArg(v_inst_2500_, v___x_2504_);
v___x_2506_ = lean_obj_once(&l_Lean_ensureNonAmbiguous___redArg___closed__1, &l_Lean_ensureNonAmbiguous___redArg___closed__1_once, _init_l_Lean_ensureNonAmbiguous___redArg___closed__1);
v___x_2507_ = l_panic___redArg(v___x_2505_, v___x_2506_);
lean_dec(v___x_2505_);
return v___x_2507_;
}
else
{
lean_object* v_tail_2508_; 
v_tail_2508_ = lean_ctor_get(v_cs_2503_, 1);
if (lean_obj_tag(v_tail_2508_) == 0)
{
lean_object* v_toApplicative_2509_; lean_object* v_toPure_2510_; lean_object* v_head_2511_; lean_object* v___x_2512_; 
v_toApplicative_2509_ = lean_ctor_get(v_inst_2500_, 0);
lean_inc_ref(v_toApplicative_2509_);
lean_dec(v_id_2502_);
lean_dec_ref(v_inst_2501_);
lean_dec_ref(v_inst_2500_);
v_toPure_2510_ = lean_ctor_get(v_toApplicative_2509_, 1);
lean_inc(v_toPure_2510_);
lean_dec_ref(v_toApplicative_2509_);
v_head_2511_ = lean_ctor_get(v_cs_2503_, 0);
lean_inc(v_head_2511_);
lean_dec_ref_known(v_cs_2503_, 2);
v___x_2512_ = lean_apply_2(v_toPure_2510_, lean_box(0), v_head_2511_);
return v___x_2512_;
}
else
{
lean_object* v___f_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; uint8_t v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; 
v___f_2513_ = ((lean_object*)(l_Lean_ensureNoOverload___redArg___closed__0));
v___x_2514_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___redArg___closed__2));
v___x_2515_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___redArg___closed__3));
v___x_2516_ = lean_box(0);
v___x_2517_ = 0;
lean_inc(v_id_2502_);
v___x_2518_ = l_Lean_Syntax_formatStx(v_id_2502_, v___x_2516_, v___x_2517_);
v___x_2519_ = l_Std_Format_defWidth;
v___x_2520_ = lean_unsigned_to_nat(0u);
v___x_2521_ = l_Std_Format_pretty(v___x_2518_, v___x_2519_, v___x_2520_, v___x_2520_);
v___x_2522_ = lean_string_append(v___x_2515_, v___x_2521_);
lean_dec_ref(v___x_2521_);
v___x_2523_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___redArg___closed__4));
v___x_2524_ = lean_string_append(v___x_2522_, v___x_2523_);
v___x_2525_ = lean_box(0);
v___x_2526_ = l_List_mapTR_loop___redArg(v___f_2513_, v_cs_2503_, v___x_2525_);
v___x_2527_ = l_List_toString___redArg(v___x_2514_, v___x_2526_);
v___x_2528_ = lean_string_append(v___x_2524_, v___x_2527_);
lean_dec_ref(v___x_2527_);
v___x_2529_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2529_, 0, v___x_2528_);
v___x_2530_ = l_Lean_MessageData_ofFormat(v___x_2529_);
v___x_2531_ = l_Lean_throwErrorAt___redArg(v_inst_2500_, v_inst_2501_, v_id_2502_, v___x_2530_);
return v___x_2531_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNonAmbiguous(lean_object* v_m_2532_, lean_object* v_inst_2533_, lean_object* v_inst_2534_, lean_object* v_id_2535_, lean_object* v_cs_2536_){
_start:
{
lean_object* v___x_2537_; 
v___x_2537_ = l_Lean_ensureNonAmbiguous___redArg(v_inst_2533_, v_inst_2534_, v_id_2535_, v_cs_2536_);
return v___x_2537_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverload___redArg___lam__0(lean_object* v_inst_2538_, lean_object* v_inst_2539_, lean_object* v_id_2540_, lean_object* v_____do__lift_2541_){
_start:
{
lean_object* v___x_2542_; 
v___x_2542_ = l_Lean_ensureNonAmbiguous___redArg(v_inst_2538_, v_inst_2539_, v_id_2540_, v_____do__lift_2541_);
return v___x_2542_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverload___redArg(lean_object* v_inst_2543_, lean_object* v_inst_2544_, lean_object* v_inst_2545_, lean_object* v_inst_2546_, lean_object* v_inst_2547_, lean_object* v_inst_2548_, lean_object* v_inst_2549_, lean_object* v_id_2550_){
_start:
{
lean_object* v_toBind_2551_; lean_object* v___f_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; 
v_toBind_2551_ = lean_ctor_get(v_inst_2543_, 1);
lean_inc(v_toBind_2551_);
lean_inc(v_id_2550_);
lean_inc_ref(v_inst_2549_);
lean_inc_ref(v_inst_2543_);
v___f_2552_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalConstNoOverload___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2552_, 0, v_inst_2543_);
lean_closure_set(v___f_2552_, 1, v_inst_2549_);
lean_closure_set(v___f_2552_, 2, v_id_2550_);
v___x_2553_ = l_Lean_resolveGlobalConst___redArg(v_inst_2543_, v_inst_2544_, v_inst_2545_, v_inst_2546_, v_inst_2547_, v_inst_2548_, v_inst_2549_, v_id_2550_);
v___x_2554_ = lean_apply_4(v_toBind_2551_, lean_box(0), lean_box(0), v___x_2553_, v___f_2552_);
return v___x_2554_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverload(lean_object* v_m_2555_, lean_object* v_inst_2556_, lean_object* v_inst_2557_, lean_object* v_inst_2558_, lean_object* v_inst_2559_, lean_object* v_inst_2560_, lean_object* v_inst_2561_, lean_object* v_inst_2562_, lean_object* v_id_2563_){
_start:
{
lean_object* v___x_2564_; 
v___x_2564_ = l_Lean_resolveGlobalConstNoOverload___redArg(v_inst_2556_, v_inst_2557_, v_inst_2558_, v_inst_2559_, v_inst_2560_, v_inst_2561_, v_inst_2562_, v_id_2563_);
return v___x_2564_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__0(lean_object* v___f_2565_, lean_object* v___f_2566_, uint8_t v_globalDeclFoundNext_2567_, uint8_t v_globalDeclFound_2568_, lean_object* v_r_2569_){
_start:
{
lean_object* v___x_2570_; lean_object* v_r_2571_; uint8_t v___x_2572_; 
v___x_2570_ = lean_box(0);
v_r_2571_ = l_List_filterTR_loop___redArg(v___f_2565_, v_r_2569_, v___x_2570_);
v___x_2572_ = l_List_isEmpty___redArg(v_r_2571_);
lean_dec(v_r_2571_);
if (v___x_2572_ == 0)
{
lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; 
v___x_2573_ = lean_box(0);
v___x_2574_ = lean_box(v_globalDeclFoundNext_2567_);
v___x_2575_ = lean_apply_2(v___f_2566_, v___x_2573_, v___x_2574_);
return v___x_2575_;
}
else
{
lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; 
v___x_2576_ = lean_box(0);
v___x_2577_ = lean_box(v_globalDeclFound_2568_);
v___x_2578_ = lean_apply_2(v___f_2566_, v___x_2576_, v___x_2577_);
return v___x_2578_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__0___boxed(lean_object* v___f_2579_, lean_object* v___f_2580_, lean_object* v_globalDeclFoundNext_2581_, lean_object* v_globalDeclFound_2582_, lean_object* v_r_2583_){
_start:
{
uint8_t v_globalDeclFoundNext_boxed_2584_; uint8_t v_globalDeclFound_boxed_2585_; lean_object* v_res_2586_; 
v_globalDeclFoundNext_boxed_2584_ = lean_unbox(v_globalDeclFoundNext_2581_);
v_globalDeclFound_boxed_2585_ = lean_unbox(v_globalDeclFound_2582_);
v_res_2586_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__0(v___f_2579_, v___f_2580_, v_globalDeclFoundNext_boxed_2584_, v_globalDeclFound_boxed_2585_, v_r_2583_);
return v_res_2586_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__1___boxed(lean_object* v_str_2587_, lean_object* v_projs_2588_, lean_object* v_inst_2589_, lean_object* v_inst_2590_, lean_object* v_inst_2591_, lean_object* v_inst_2592_, lean_object* v_inst_2593_, lean_object* v_inst_2594_, lean_object* v_view_2595_, lean_object* v_findLocalDecl_x3f_2596_, lean_object* v_pre_2597_, lean_object* v_____r_2598_, lean_object* v_globalDeclFoundNext_2599_){
_start:
{
uint8_t v_globalDeclFoundNext_boxed_2600_; lean_object* v_res_2601_; 
v_globalDeclFoundNext_boxed_2600_ = lean_unbox(v_globalDeclFoundNext_2599_);
v_res_2601_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__1(v_str_2587_, v_projs_2588_, v_inst_2589_, v_inst_2590_, v_inst_2591_, v_inst_2592_, v_inst_2593_, v_inst_2594_, v_view_2595_, v_findLocalDecl_x3f_2596_, v_pre_2597_, v_____r_2598_, v_globalDeclFoundNext_boxed_2600_);
return v_res_2601_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg(lean_object* v_inst_2602_, lean_object* v_inst_2603_, lean_object* v_inst_2604_, lean_object* v_inst_2605_, lean_object* v_inst_2606_, lean_object* v_inst_2607_, lean_object* v_view_2608_, lean_object* v_findLocalDecl_x3f_2609_, lean_object* v_n_2610_, lean_object* v_projs_2611_, uint8_t v_globalDeclFound_2612_){
_start:
{
lean_object* v_toApplicative_2613_; lean_object* v_imported_2614_; lean_object* v_ctx_2615_; lean_object* v_scopes_2616_; lean_object* v_toBind_2617_; lean_object* v_toPure_2618_; lean_object* v___f_2619_; lean_object* v_givenNameView_2620_; uint8_t v___y_2622_; 
v_toApplicative_2613_ = lean_ctor_get(v_inst_2602_, 0);
v_imported_2614_ = lean_ctor_get(v_view_2608_, 1);
v_ctx_2615_ = lean_ctor_get(v_view_2608_, 2);
v_scopes_2616_ = lean_ctor_get(v_view_2608_, 3);
v_toBind_2617_ = lean_ctor_get(v_inst_2602_, 1);
v_toPure_2618_ = lean_ctor_get(v_toApplicative_2613_, 1);
v___f_2619_ = ((lean_object*)(l_Lean_filterFieldList___redArg___closed__0));
lean_inc(v_scopes_2616_);
lean_inc(v_ctx_2615_);
lean_inc(v_imported_2614_);
lean_inc(v_n_2610_);
v_givenNameView_2620_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_givenNameView_2620_, 0, v_n_2610_);
lean_ctor_set(v_givenNameView_2620_, 1, v_imported_2614_);
lean_ctor_set(v_givenNameView_2620_, 2, v_ctx_2615_);
lean_ctor_set(v_givenNameView_2620_, 3, v_scopes_2616_);
if (v_globalDeclFound_2612_ == 0)
{
v___y_2622_ = v_globalDeclFound_2612_;
goto v___jp_2621_;
}
else
{
uint8_t v___x_2658_; 
v___x_2658_ = l_List_isEmpty___redArg(v_projs_2611_);
if (v___x_2658_ == 0)
{
v___y_2622_ = v_globalDeclFound_2612_;
goto v___jp_2621_;
}
else
{
uint8_t v___x_2659_; 
v___x_2659_ = 0;
v___y_2622_ = v___x_2659_;
goto v___jp_2621_;
}
}
v___jp_2621_:
{
lean_object* v___x_2623_; lean_object* v___x_2624_; 
v___x_2623_ = lean_box(v___y_2622_);
lean_inc_ref(v_findLocalDecl_x3f_2609_);
lean_inc_ref(v_givenNameView_2620_);
v___x_2624_ = lean_apply_2(v_findLocalDecl_x3f_2609_, v_givenNameView_2620_, v___x_2623_);
if (lean_obj_tag(v___x_2624_) == 0)
{
if (lean_obj_tag(v_n_2610_) == 1)
{
lean_object* v_pre_2625_; lean_object* v_str_2626_; lean_object* v___f_2627_; 
v_pre_2625_ = lean_ctor_get(v_n_2610_, 0);
lean_inc_n(v_pre_2625_, 2);
v_str_2626_ = lean_ctor_get(v_n_2610_, 1);
lean_inc_ref_n(v_str_2626_, 2);
lean_dec_ref_known(v_n_2610_, 2);
lean_inc_ref(v_findLocalDecl_x3f_2609_);
lean_inc_ref(v_view_2608_);
lean_inc(v_inst_2607_);
lean_inc_ref(v_inst_2606_);
lean_inc(v_inst_2605_);
lean_inc_ref(v_inst_2604_);
lean_inc_ref(v_inst_2603_);
lean_inc_ref(v_inst_2602_);
lean_inc(v_projs_2611_);
v___f_2627_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__1___boxed), 13, 11);
lean_closure_set(v___f_2627_, 0, v_str_2626_);
lean_closure_set(v___f_2627_, 1, v_projs_2611_);
lean_closure_set(v___f_2627_, 2, v_inst_2602_);
lean_closure_set(v___f_2627_, 3, v_inst_2603_);
lean_closure_set(v___f_2627_, 4, v_inst_2604_);
lean_closure_set(v___f_2627_, 5, v_inst_2605_);
lean_closure_set(v___f_2627_, 6, v_inst_2606_);
lean_closure_set(v___f_2627_, 7, v_inst_2607_);
lean_closure_set(v___f_2627_, 8, v_view_2608_);
lean_closure_set(v___f_2627_, 9, v_findLocalDecl_x3f_2609_);
lean_closure_set(v___f_2627_, 10, v_pre_2625_);
if (v_globalDeclFound_2612_ == 0)
{
uint8_t v_globalDeclFoundNext_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___f_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; 
lean_inc(v_toBind_2617_);
lean_dec_ref(v_str_2626_);
lean_dec(v_pre_2625_);
lean_dec(v_projs_2611_);
lean_dec_ref(v_findLocalDecl_x3f_2609_);
lean_dec_ref(v_view_2608_);
v_globalDeclFoundNext_2628_ = 1;
v___x_2629_ = lean_box(v_globalDeclFoundNext_2628_);
v___x_2630_ = lean_box(v_globalDeclFound_2612_);
v___f_2631_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2631_, 0, v___f_2619_);
lean_closure_set(v___f_2631_, 1, v___f_2627_);
lean_closure_set(v___f_2631_, 2, v___x_2629_);
lean_closure_set(v___f_2631_, 3, v___x_2630_);
v___x_2632_ = l_Lean_MacroScopesView_review(v_givenNameView_2620_);
v___x_2633_ = l_Lean_resolveGlobalName___redArg(v_inst_2602_, v_inst_2603_, v_inst_2604_, v_inst_2605_, v_inst_2606_, v_inst_2607_, v___x_2632_, v_globalDeclFound_2612_);
v___x_2634_ = lean_apply_4(v_toBind_2617_, lean_box(0), lean_box(0), v___x_2633_, v___f_2631_);
return v___x_2634_;
}
else
{
lean_object* v___x_2635_; lean_object* v___x_2636_; 
lean_dec_ref(v___f_2627_);
lean_dec_ref_known(v_givenNameView_2620_, 4);
v___x_2635_ = lean_box(0);
v___x_2636_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__1(v_str_2626_, v_projs_2611_, v_inst_2602_, v_inst_2603_, v_inst_2604_, v_inst_2605_, v_inst_2606_, v_inst_2607_, v_view_2608_, v_findLocalDecl_x3f_2609_, v_pre_2625_, v___x_2635_, v_globalDeclFound_2612_);
return v___x_2636_;
}
}
else
{
lean_object* v___x_2637_; lean_object* v___x_2638_; 
lean_inc(v_toPure_2618_);
lean_dec_ref_known(v_givenNameView_2620_, 4);
lean_dec(v_projs_2611_);
lean_dec(v_n_2610_);
lean_dec_ref(v_findLocalDecl_x3f_2609_);
lean_dec_ref(v_view_2608_);
lean_dec(v_inst_2607_);
lean_dec_ref(v_inst_2606_);
lean_dec(v_inst_2605_);
lean_dec_ref(v_inst_2604_);
lean_dec_ref(v_inst_2603_);
lean_dec_ref(v_inst_2602_);
v___x_2637_ = lean_box(0);
v___x_2638_ = lean_apply_2(v_toPure_2618_, lean_box(0), v___x_2637_);
return v___x_2638_;
}
}
else
{
lean_object* v___x_2640_; uint8_t v_isShared_2641_; uint8_t v_isSharedCheck_2655_; 
lean_inc(v_toPure_2618_);
lean_dec_ref_known(v_givenNameView_2620_, 4);
lean_dec(v_n_2610_);
lean_dec_ref(v_findLocalDecl_x3f_2609_);
lean_dec_ref(v_view_2608_);
lean_dec(v_inst_2607_);
lean_dec_ref(v_inst_2606_);
lean_dec(v_inst_2605_);
lean_dec_ref(v_inst_2604_);
lean_dec_ref(v_inst_2603_);
v_isSharedCheck_2655_ = !lean_is_exclusive(v_inst_2602_);
if (v_isSharedCheck_2655_ == 0)
{
lean_object* v_unused_2656_; lean_object* v_unused_2657_; 
v_unused_2656_ = lean_ctor_get(v_inst_2602_, 1);
lean_dec(v_unused_2656_);
v_unused_2657_ = lean_ctor_get(v_inst_2602_, 0);
lean_dec(v_unused_2657_);
v___x_2640_ = v_inst_2602_;
v_isShared_2641_ = v_isSharedCheck_2655_;
goto v_resetjp_2639_;
}
else
{
lean_dec(v_inst_2602_);
v___x_2640_ = lean_box(0);
v_isShared_2641_ = v_isSharedCheck_2655_;
goto v_resetjp_2639_;
}
v_resetjp_2639_:
{
lean_object* v_val_2642_; lean_object* v___x_2644_; uint8_t v_isShared_2645_; uint8_t v_isSharedCheck_2654_; 
v_val_2642_ = lean_ctor_get(v___x_2624_, 0);
v_isSharedCheck_2654_ = !lean_is_exclusive(v___x_2624_);
if (v_isSharedCheck_2654_ == 0)
{
v___x_2644_ = v___x_2624_;
v_isShared_2645_ = v_isSharedCheck_2654_;
goto v_resetjp_2643_;
}
else
{
lean_inc(v_val_2642_);
lean_dec(v___x_2624_);
v___x_2644_ = lean_box(0);
v_isShared_2645_ = v_isSharedCheck_2654_;
goto v_resetjp_2643_;
}
v_resetjp_2643_:
{
lean_object* v___x_2646_; lean_object* v___x_2648_; 
v___x_2646_ = l_Lean_LocalDecl_toExpr(v_val_2642_);
if (v_isShared_2641_ == 0)
{
lean_ctor_set(v___x_2640_, 1, v_projs_2611_);
lean_ctor_set(v___x_2640_, 0, v___x_2646_);
v___x_2648_ = v___x_2640_;
goto v_reusejp_2647_;
}
else
{
lean_object* v_reuseFailAlloc_2653_; 
v_reuseFailAlloc_2653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2653_, 0, v___x_2646_);
lean_ctor_set(v_reuseFailAlloc_2653_, 1, v_projs_2611_);
v___x_2648_ = v_reuseFailAlloc_2653_;
goto v_reusejp_2647_;
}
v_reusejp_2647_:
{
lean_object* v___x_2650_; 
if (v_isShared_2645_ == 0)
{
lean_ctor_set(v___x_2644_, 0, v___x_2648_);
v___x_2650_ = v___x_2644_;
goto v_reusejp_2649_;
}
else
{
lean_object* v_reuseFailAlloc_2652_; 
v_reuseFailAlloc_2652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2652_, 0, v___x_2648_);
v___x_2650_ = v_reuseFailAlloc_2652_;
goto v_reusejp_2649_;
}
v_reusejp_2649_:
{
lean_object* v___x_2651_; 
v___x_2651_ = lean_apply_2(v_toPure_2618_, lean_box(0), v___x_2650_);
return v___x_2651_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__1(lean_object* v_str_2660_, lean_object* v_projs_2661_, lean_object* v_inst_2662_, lean_object* v_inst_2663_, lean_object* v_inst_2664_, lean_object* v_inst_2665_, lean_object* v_inst_2666_, lean_object* v_inst_2667_, lean_object* v_view_2668_, lean_object* v_findLocalDecl_x3f_2669_, lean_object* v_pre_2670_, lean_object* v_____r_2671_, uint8_t v_globalDeclFoundNext_2672_){
_start:
{
lean_object* v___x_2673_; lean_object* v___x_2674_; 
v___x_2673_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2673_, 0, v_str_2660_);
lean_ctor_set(v___x_2673_, 1, v_projs_2661_);
v___x_2674_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg(v_inst_2662_, v_inst_2663_, v_inst_2664_, v_inst_2665_, v_inst_2666_, v_inst_2667_, v_view_2668_, v_findLocalDecl_x3f_2669_, v_pre_2670_, v___x_2673_, v_globalDeclFoundNext_2672_);
return v___x_2674_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___boxed(lean_object* v_inst_2675_, lean_object* v_inst_2676_, lean_object* v_inst_2677_, lean_object* v_inst_2678_, lean_object* v_inst_2679_, lean_object* v_inst_2680_, lean_object* v_view_2681_, lean_object* v_findLocalDecl_x3f_2682_, lean_object* v_n_2683_, lean_object* v_projs_2684_, lean_object* v_globalDeclFound_2685_){
_start:
{
uint8_t v_globalDeclFound_boxed_2686_; lean_object* v_res_2687_; 
v_globalDeclFound_boxed_2686_ = lean_unbox(v_globalDeclFound_2685_);
v_res_2687_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg(v_inst_2675_, v_inst_2676_, v_inst_2677_, v_inst_2678_, v_inst_2679_, v_inst_2680_, v_view_2681_, v_findLocalDecl_x3f_2682_, v_n_2683_, v_projs_2684_, v_globalDeclFound_boxed_2686_);
return v_res_2687_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop(lean_object* v_m_2688_, lean_object* v_inst_2689_, lean_object* v_inst_2690_, lean_object* v_inst_2691_, lean_object* v_inst_2692_, lean_object* v_inst_2693_, lean_object* v_inst_2694_, lean_object* v_view_2695_, lean_object* v_findLocalDecl_x3f_2696_, lean_object* v_n_2697_, lean_object* v_projs_2698_, uint8_t v_globalDeclFound_2699_){
_start:
{
lean_object* v___x_2700_; 
v___x_2700_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg(v_inst_2689_, v_inst_2690_, v_inst_2691_, v_inst_2692_, v_inst_2693_, v_inst_2694_, v_view_2695_, v_findLocalDecl_x3f_2696_, v_n_2697_, v_projs_2698_, v_globalDeclFound_2699_);
return v___x_2700_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___boxed(lean_object* v_m_2701_, lean_object* v_inst_2702_, lean_object* v_inst_2703_, lean_object* v_inst_2704_, lean_object* v_inst_2705_, lean_object* v_inst_2706_, lean_object* v_inst_2707_, lean_object* v_view_2708_, lean_object* v_findLocalDecl_x3f_2709_, lean_object* v_n_2710_, lean_object* v_projs_2711_, lean_object* v_globalDeclFound_2712_){
_start:
{
uint8_t v_globalDeclFound_boxed_2713_; lean_object* v_res_2714_; 
v_globalDeclFound_boxed_2713_ = lean_unbox(v_globalDeclFound_2712_);
v_res_2714_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop(v_m_2701_, v_inst_2702_, v_inst_2703_, v_inst_2704_, v_inst_2705_, v_inst_2706_, v_inst_2707_, v_view_2708_, v_findLocalDecl_x3f_2709_, v_n_2710_, v_projs_2711_, v_globalDeclFound_boxed_2713_);
return v_res_2714_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_go(lean_object* v_localDecl_2715_, lean_object* v_givenNameView_2716_, lean_object* v_fullDeclName_2717_, lean_object* v_ns_2718_){
_start:
{
lean_object* v_name_2719_; lean_object* v_imported_2720_; lean_object* v_ctx_2721_; lean_object* v_scopes_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; uint8_t v___x_2726_; 
v_name_2719_ = lean_ctor_get(v_givenNameView_2716_, 0);
v_imported_2720_ = lean_ctor_get(v_givenNameView_2716_, 1);
v_ctx_2721_ = lean_ctor_get(v_givenNameView_2716_, 2);
v_scopes_2722_ = lean_ctor_get(v_givenNameView_2716_, 3);
lean_inc(v_name_2719_);
lean_inc(v_ns_2718_);
v___x_2723_ = l_Lean_Name_append(v_ns_2718_, v_name_2719_);
lean_inc(v_scopes_2722_);
lean_inc(v_ctx_2721_);
lean_inc(v_imported_2720_);
v___x_2724_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2724_, 0, v___x_2723_);
lean_ctor_set(v___x_2724_, 1, v_imported_2720_);
lean_ctor_set(v___x_2724_, 2, v_ctx_2721_);
lean_ctor_set(v___x_2724_, 3, v_scopes_2722_);
v___x_2725_ = l_Lean_MacroScopesView_review(v___x_2724_);
v___x_2726_ = lean_name_eq(v___x_2725_, v_fullDeclName_2717_);
lean_dec(v___x_2725_);
if (v___x_2726_ == 0)
{
if (lean_obj_tag(v_ns_2718_) == 1)
{
lean_object* v_pre_2727_; 
v_pre_2727_ = lean_ctor_get(v_ns_2718_, 0);
lean_inc(v_pre_2727_);
lean_dec_ref_known(v_ns_2718_, 2);
v_ns_2718_ = v_pre_2727_;
goto _start;
}
else
{
lean_object* v___x_2729_; 
lean_dec(v_ns_2718_);
lean_dec_ref(v_givenNameView_2716_);
lean_dec_ref(v_localDecl_2715_);
v___x_2729_ = lean_box(0);
return v___x_2729_;
}
}
else
{
lean_object* v___x_2730_; 
lean_dec(v_ns_2718_);
lean_dec_ref(v_givenNameView_2716_);
v___x_2730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2730_, 0, v_localDecl_2715_);
return v___x_2730_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_go___boxed(lean_object* v_localDecl_2731_, lean_object* v_givenNameView_2732_, lean_object* v_fullDeclName_2733_, lean_object* v_ns_2734_){
_start:
{
lean_object* v_res_2735_; 
v_res_2735_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_go(v_localDecl_2731_, v_givenNameView_2732_, v_fullDeclName_2733_, v_ns_2734_);
lean_dec(v_fullDeclName_2733_);
return v_res_2735_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__0(lean_object* v_localDecl_2736_, lean_object* v_givenName_2737_){
_start:
{
lean_object* v___x_2738_; uint8_t v___x_2739_; 
v___x_2738_ = l_Lean_LocalDecl_userName(v_localDecl_2736_);
v___x_2739_ = lean_name_eq(v___x_2738_, v_givenName_2737_);
lean_dec(v___x_2738_);
if (v___x_2739_ == 0)
{
lean_object* v___x_2740_; 
lean_dec_ref(v_localDecl_2736_);
v___x_2740_ = lean_box(0);
return v___x_2740_;
}
else
{
lean_object* v___x_2741_; 
v___x_2741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2741_, 0, v_localDecl_2736_);
return v___x_2741_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__0___boxed(lean_object* v_localDecl_2742_, lean_object* v_givenName_2743_){
_start:
{
lean_object* v_res_2744_; 
v_res_2744_ = l_Lean_resolveLocalName___redArg___lam__0(v_localDecl_2742_, v_givenName_2743_);
lean_dec(v_givenName_2743_);
return v_res_2744_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__1(lean_object* v_matchLocalDecl_x3f_2745_, lean_object* v_givenName_2746_, uint8_t v_skipAuxDecl_2747_, lean_object* v___f_2748_, lean_object* v_auxDeclToFullName_2749_, lean_object* v_currNamespace_2750_, lean_object* v_givenNameView_2751_, lean_object* v_x_2752_){
_start:
{
if (lean_obj_tag(v_x_2752_) == 0)
{
lean_dec_ref(v_givenNameView_2751_);
lean_dec(v_currNamespace_2750_);
lean_dec(v_auxDeclToFullName_2749_);
lean_dec_ref(v___f_2748_);
lean_dec(v_givenName_2746_);
lean_dec_ref(v_matchLocalDecl_x3f_2745_);
return v_x_2752_;
}
else
{
lean_object* v_val_2753_; uint8_t v___x_2754_; 
v_val_2753_ = lean_ctor_get(v_x_2752_, 0);
v___x_2754_ = l_Lean_LocalDecl_isAuxDecl(v_val_2753_);
if (v___x_2754_ == 0)
{
lean_object* v___x_2755_; 
lean_inc(v_val_2753_);
lean_dec_ref_known(v_x_2752_, 1);
lean_dec_ref(v_givenNameView_2751_);
lean_dec(v_currNamespace_2750_);
lean_dec(v_auxDeclToFullName_2749_);
lean_dec_ref(v___f_2748_);
v___x_2755_ = lean_apply_2(v_matchLocalDecl_x3f_2745_, v_val_2753_, v_givenName_2746_);
return v___x_2755_;
}
else
{
if (v_skipAuxDecl_2747_ == 0)
{
if (v___x_2754_ == 0)
{
lean_object* v___x_2756_; 
lean_dec_ref_known(v_x_2752_, 1);
lean_dec_ref(v_givenNameView_2751_);
lean_dec(v_currNamespace_2750_);
lean_dec(v_auxDeclToFullName_2749_);
lean_dec_ref(v___f_2748_);
lean_dec(v_givenName_2746_);
lean_dec_ref(v_matchLocalDecl_x3f_2745_);
v___x_2756_ = lean_box(0);
return v___x_2756_;
}
else
{
lean_object* v___x_2757_; lean_object* v___x_2758_; 
v___x_2757_ = l_Lean_LocalDecl_fvarId(v_val_2753_);
v___x_2758_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v___f_2748_, v_auxDeclToFullName_2749_, v___x_2757_);
if (lean_obj_tag(v___x_2758_) == 1)
{
lean_object* v_val_2759_; lean_object* v_fullDeclView_2760_; lean_object* v___y_2762_; lean_object* v_name_2783_; lean_object* v___x_2784_; 
lean_dec(v_givenName_2746_);
lean_dec_ref(v_matchLocalDecl_x3f_2745_);
v_val_2759_ = lean_ctor_get(v___x_2758_, 0);
lean_inc(v_val_2759_);
lean_dec_ref_known(v___x_2758_, 1);
v_fullDeclView_2760_ = l_Lean_extractMacroScopes(v_val_2759_);
v_name_2783_ = lean_ctor_get(v_fullDeclView_2760_, 0);
lean_inc_n(v_name_2783_, 2);
v___x_2784_ = l_Lean_privateToUserName_x3f(v_name_2783_);
if (lean_obj_tag(v___x_2784_) == 0)
{
v___y_2762_ = v_name_2783_;
goto v___jp_2761_;
}
else
{
lean_object* v_val_2785_; 
lean_dec(v_name_2783_);
v_val_2785_ = lean_ctor_get(v___x_2784_, 0);
lean_inc(v_val_2785_);
lean_dec_ref_known(v___x_2784_, 1);
v___y_2762_ = v_val_2785_;
goto v___jp_2761_;
}
v___jp_2761_:
{
lean_object* v_imported_2763_; lean_object* v_ctx_2764_; lean_object* v_scopes_2765_; lean_object* v___x_2767_; uint8_t v_isShared_2768_; uint8_t v_isSharedCheck_2781_; 
v_imported_2763_ = lean_ctor_get(v_fullDeclView_2760_, 1);
v_ctx_2764_ = lean_ctor_get(v_fullDeclView_2760_, 2);
v_scopes_2765_ = lean_ctor_get(v_fullDeclView_2760_, 3);
v_isSharedCheck_2781_ = !lean_is_exclusive(v_fullDeclView_2760_);
if (v_isSharedCheck_2781_ == 0)
{
lean_object* v_unused_2782_; 
v_unused_2782_ = lean_ctor_get(v_fullDeclView_2760_, 0);
lean_dec(v_unused_2782_);
v___x_2767_ = v_fullDeclView_2760_;
v_isShared_2768_ = v_isSharedCheck_2781_;
goto v_resetjp_2766_;
}
else
{
lean_inc(v_scopes_2765_);
lean_inc(v_ctx_2764_);
lean_inc(v_imported_2763_);
lean_dec(v_fullDeclView_2760_);
v___x_2767_ = lean_box(0);
v_isShared_2768_ = v_isSharedCheck_2781_;
goto v_resetjp_2766_;
}
v_resetjp_2766_:
{
lean_object* v_fullDeclView_2770_; 
if (v_isShared_2768_ == 0)
{
lean_ctor_set(v___x_2767_, 0, v___y_2762_);
v_fullDeclView_2770_ = v___x_2767_;
goto v_reusejp_2769_;
}
else
{
lean_object* v_reuseFailAlloc_2780_; 
v_reuseFailAlloc_2780_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2780_, 0, v___y_2762_);
lean_ctor_set(v_reuseFailAlloc_2780_, 1, v_imported_2763_);
lean_ctor_set(v_reuseFailAlloc_2780_, 2, v_ctx_2764_);
lean_ctor_set(v_reuseFailAlloc_2780_, 3, v_scopes_2765_);
v_fullDeclView_2770_ = v_reuseFailAlloc_2780_;
goto v_reusejp_2769_;
}
v_reusejp_2769_:
{
lean_object* v_fullDeclName_2771_; uint8_t v___x_2772_; 
lean_inc_ref(v_fullDeclView_2770_);
v_fullDeclName_2771_ = l_Lean_MacroScopesView_review(v_fullDeclView_2770_);
v___x_2772_ = l_Lean_Name_isPrefixOf(v_currNamespace_2750_, v_fullDeclName_2771_);
if (v___x_2772_ == 0)
{
lean_object* v___x_2773_; 
lean_inc(v_val_2753_);
lean_dec_ref(v_fullDeclView_2770_);
lean_dec_ref_known(v_x_2752_, 1);
v___x_2773_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_go(v_val_2753_, v_givenNameView_2751_, v_fullDeclName_2771_, v_currNamespace_2750_);
lean_dec(v_fullDeclName_2771_);
return v___x_2773_;
}
else
{
lean_object* v___x_2774_; lean_object* v_localDeclNameView_2775_; uint8_t v___x_2776_; 
lean_dec(v_fullDeclName_2771_);
lean_dec(v_currNamespace_2750_);
v___x_2774_ = l_Lean_LocalDecl_userName(v_val_2753_);
v_localDeclNameView_2775_ = l_Lean_extractMacroScopes(v___x_2774_);
v___x_2776_ = l_Lean_MacroScopesView_isSuffixOf(v_localDeclNameView_2775_, v_givenNameView_2751_);
lean_dec_ref(v_localDeclNameView_2775_);
if (v___x_2776_ == 0)
{
lean_object* v___x_2777_; 
lean_dec_ref(v_fullDeclView_2770_);
lean_dec_ref_known(v_x_2752_, 1);
lean_dec_ref(v_givenNameView_2751_);
v___x_2777_ = lean_box(0);
return v___x_2777_;
}
else
{
uint8_t v___x_2778_; 
v___x_2778_ = l_Lean_MacroScopesView_isSuffixOf(v_givenNameView_2751_, v_fullDeclView_2770_);
lean_dec_ref(v_fullDeclView_2770_);
lean_dec_ref(v_givenNameView_2751_);
if (v___x_2778_ == 0)
{
lean_object* v___x_2779_; 
lean_dec_ref_known(v_x_2752_, 1);
v___x_2779_ = lean_box(0);
return v___x_2779_;
}
else
{
return v_x_2752_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2786_; 
lean_inc(v_val_2753_);
lean_dec(v___x_2758_);
lean_dec_ref_known(v_x_2752_, 1);
lean_dec_ref(v_givenNameView_2751_);
lean_dec(v_currNamespace_2750_);
v___x_2786_ = lean_apply_2(v_matchLocalDecl_x3f_2745_, v_val_2753_, v_givenName_2746_);
return v___x_2786_;
}
}
}
else
{
lean_object* v___x_2787_; 
lean_dec_ref_known(v_x_2752_, 1);
lean_dec_ref(v_givenNameView_2751_);
lean_dec(v_currNamespace_2750_);
lean_dec(v_auxDeclToFullName_2749_);
lean_dec_ref(v___f_2748_);
lean_dec(v_givenName_2746_);
lean_dec_ref(v_matchLocalDecl_x3f_2745_);
v___x_2787_ = lean_box(0);
return v___x_2787_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__1___boxed(lean_object* v_matchLocalDecl_x3f_2788_, lean_object* v_givenName_2789_, lean_object* v_skipAuxDecl_2790_, lean_object* v___f_2791_, lean_object* v_auxDeclToFullName_2792_, lean_object* v_currNamespace_2793_, lean_object* v_givenNameView_2794_, lean_object* v_x_2795_){
_start:
{
uint8_t v_skipAuxDecl_boxed_2796_; lean_object* v_res_2797_; 
v_skipAuxDecl_boxed_2796_ = lean_unbox(v_skipAuxDecl_2790_);
v_res_2797_ = l_Lean_resolveLocalName___redArg___lam__1(v_matchLocalDecl_x3f_2788_, v_givenName_2789_, v_skipAuxDecl_boxed_2796_, v___f_2791_, v_auxDeclToFullName_2792_, v_currNamespace_2793_, v_givenNameView_2794_, v_x_2795_);
return v_res_2797_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__2(lean_object* v_localDecl_x3f_2798_, lean_object* v_matchLocalDecl_x3f_2799_, lean_object* v_givenName_2800_, lean_object* v_x_2801_){
_start:
{
if (lean_obj_tag(v_x_2801_) == 0)
{
lean_dec(v_givenName_2800_);
lean_dec_ref(v_matchLocalDecl_x3f_2799_);
return v_x_2801_;
}
else
{
lean_object* v_val_2802_; uint8_t v___x_2803_; 
v_val_2802_ = lean_ctor_get(v_x_2801_, 0);
lean_inc(v_val_2802_);
lean_dec_ref_known(v_x_2801_, 1);
v___x_2803_ = l_Lean_LocalDecl_isAuxDecl(v_val_2802_);
if (v___x_2803_ == 0)
{
lean_dec(v_val_2802_);
lean_dec(v_givenName_2800_);
lean_dec_ref(v_matchLocalDecl_x3f_2799_);
lean_inc(v_localDecl_x3f_2798_);
return v_localDecl_x3f_2798_;
}
else
{
lean_object* v___x_2804_; 
v___x_2804_ = lean_apply_2(v_matchLocalDecl_x3f_2799_, v_val_2802_, v_givenName_2800_);
return v___x_2804_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__2___boxed(lean_object* v_localDecl_x3f_2805_, lean_object* v_matchLocalDecl_x3f_2806_, lean_object* v_givenName_2807_, lean_object* v_x_2808_){
_start:
{
lean_object* v_res_2809_; 
v_res_2809_ = l_Lean_resolveLocalName___redArg___lam__2(v_localDecl_x3f_2805_, v_matchLocalDecl_x3f_2806_, v_givenName_2807_, v_x_2808_);
lean_dec(v_localDecl_x3f_2805_);
return v_res_2809_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__3(lean_object* v_lctx_2829_, lean_object* v_matchLocalDecl_x3f_2830_, lean_object* v___f_2831_, lean_object* v_auxDeclToFullName_2832_, lean_object* v_currNamespace_2833_, lean_object* v_givenNameView_2834_, uint8_t v_skipAuxDecl_2835_){
_start:
{
lean_object* v_decls_2836_; lean_object* v_givenName_2837_; lean_object* v___x_2838_; lean_object* v___f_2839_; lean_object* v___x_2840_; lean_object* v_localDecl_x3f_2841_; 
v_decls_2836_ = lean_ctor_get(v_lctx_2829_, 1);
lean_inc_ref_n(v_decls_2836_, 2);
lean_dec_ref(v_lctx_2829_);
lean_inc_ref(v_givenNameView_2834_);
v_givenName_2837_ = l_Lean_MacroScopesView_review(v_givenNameView_2834_);
v___x_2838_ = lean_box(v_skipAuxDecl_2835_);
lean_inc(v_givenName_2837_);
lean_inc_ref(v_matchLocalDecl_x3f_2830_);
v___f_2839_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_2839_, 0, v_matchLocalDecl_x3f_2830_);
lean_closure_set(v___f_2839_, 1, v_givenName_2837_);
lean_closure_set(v___f_2839_, 2, v___x_2838_);
lean_closure_set(v___f_2839_, 3, v___f_2831_);
lean_closure_set(v___f_2839_, 4, v_auxDeclToFullName_2832_);
lean_closure_set(v___f_2839_, 5, v_currNamespace_2833_);
lean_closure_set(v___f_2839_, 6, v_givenNameView_2834_);
v___x_2840_ = ((lean_object*)(l_Lean_resolveLocalName___redArg___lam__3___closed__9));
v_localDecl_x3f_2841_ = l_Lean_PersistentArray_findSomeRevM_x3f___redArg(v___x_2840_, v_decls_2836_, v___f_2839_);
if (lean_obj_tag(v_localDecl_x3f_2841_) == 0)
{
if (v_skipAuxDecl_2835_ == 0)
{
lean_object* v___f_2842_; lean_object* v___x_2843_; 
v___f_2842_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_2842_, 0, v_localDecl_x3f_2841_);
lean_closure_set(v___f_2842_, 1, v_matchLocalDecl_x3f_2830_);
lean_closure_set(v___f_2842_, 2, v_givenName_2837_);
v___x_2843_ = l_Lean_PersistentArray_findSomeRevM_x3f___redArg(v___x_2840_, v_decls_2836_, v___f_2842_);
return v___x_2843_;
}
else
{
lean_dec(v_givenName_2837_);
lean_dec_ref(v_decls_2836_);
lean_dec_ref(v_matchLocalDecl_x3f_2830_);
return v_localDecl_x3f_2841_;
}
}
else
{
lean_dec(v_givenName_2837_);
lean_dec_ref(v_decls_2836_);
lean_dec_ref(v_matchLocalDecl_x3f_2830_);
return v_localDecl_x3f_2841_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__3___boxed(lean_object* v_lctx_2844_, lean_object* v_matchLocalDecl_x3f_2845_, lean_object* v___f_2846_, lean_object* v_auxDeclToFullName_2847_, lean_object* v_currNamespace_2848_, lean_object* v_givenNameView_2849_, lean_object* v_skipAuxDecl_2850_){
_start:
{
uint8_t v_skipAuxDecl_boxed_2851_; lean_object* v_res_2852_; 
v_skipAuxDecl_boxed_2851_ = lean_unbox(v_skipAuxDecl_2850_);
v_res_2852_ = l_Lean_resolveLocalName___redArg___lam__3(v_lctx_2844_, v_matchLocalDecl_x3f_2845_, v___f_2846_, v_auxDeclToFullName_2847_, v_currNamespace_2848_, v_givenNameView_2849_, v_skipAuxDecl_boxed_2851_);
return v_res_2852_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__4(lean_object* v_n_2853_, lean_object* v_lctx_2854_, lean_object* v_matchLocalDecl_x3f_2855_, lean_object* v___f_2856_, lean_object* v_auxDeclToFullName_2857_, lean_object* v_inst_2858_, lean_object* v_inst_2859_, lean_object* v_inst_2860_, lean_object* v_inst_2861_, lean_object* v_inst_2862_, lean_object* v_inst_2863_, lean_object* v_currNamespace_2864_){
_start:
{
lean_object* v_view_2865_; lean_object* v_name_2866_; lean_object* v_findLocalDecl_x3f_2867_; lean_object* v___x_2868_; uint8_t v___x_2869_; lean_object* v___x_2870_; 
v_view_2865_ = l_Lean_extractMacroScopes(v_n_2853_);
v_name_2866_ = lean_ctor_get(v_view_2865_, 0);
lean_inc(v_name_2866_);
v_findLocalDecl_x3f_2867_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___redArg___lam__3___boxed), 7, 5);
lean_closure_set(v_findLocalDecl_x3f_2867_, 0, v_lctx_2854_);
lean_closure_set(v_findLocalDecl_x3f_2867_, 1, v_matchLocalDecl_x3f_2855_);
lean_closure_set(v_findLocalDecl_x3f_2867_, 2, v___f_2856_);
lean_closure_set(v_findLocalDecl_x3f_2867_, 3, v_auxDeclToFullName_2857_);
lean_closure_set(v_findLocalDecl_x3f_2867_, 4, v_currNamespace_2864_);
v___x_2868_ = lean_box(0);
v___x_2869_ = 0;
v___x_2870_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg(v_inst_2858_, v_inst_2859_, v_inst_2860_, v_inst_2861_, v_inst_2862_, v_inst_2863_, v_view_2865_, v_findLocalDecl_x3f_2867_, v_name_2866_, v___x_2868_, v___x_2869_);
return v___x_2870_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__5(lean_object* v_inst_2871_, lean_object* v_n_2872_, lean_object* v_lctx_2873_, lean_object* v_matchLocalDecl_x3f_2874_, lean_object* v___f_2875_, lean_object* v_inst_2876_, lean_object* v_inst_2877_, lean_object* v_inst_2878_, lean_object* v_inst_2879_, lean_object* v_inst_2880_, lean_object* v_toBind_2881_, lean_object* v_____do__lift_2882_){
_start:
{
lean_object* v_auxDeclToFullName_2883_; lean_object* v_getCurrNamespace_2884_; lean_object* v___f_2885_; lean_object* v___x_2886_; 
v_auxDeclToFullName_2883_ = lean_ctor_get(v_____do__lift_2882_, 2);
lean_inc(v_auxDeclToFullName_2883_);
lean_dec_ref(v_____do__lift_2882_);
v_getCurrNamespace_2884_ = lean_ctor_get(v_inst_2871_, 0);
lean_inc(v_getCurrNamespace_2884_);
v___f_2885_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___redArg___lam__4), 12, 11);
lean_closure_set(v___f_2885_, 0, v_n_2872_);
lean_closure_set(v___f_2885_, 1, v_lctx_2873_);
lean_closure_set(v___f_2885_, 2, v_matchLocalDecl_x3f_2874_);
lean_closure_set(v___f_2885_, 3, v___f_2875_);
lean_closure_set(v___f_2885_, 4, v_auxDeclToFullName_2883_);
lean_closure_set(v___f_2885_, 5, v_inst_2876_);
lean_closure_set(v___f_2885_, 6, v_inst_2871_);
lean_closure_set(v___f_2885_, 7, v_inst_2877_);
lean_closure_set(v___f_2885_, 8, v_inst_2878_);
lean_closure_set(v___f_2885_, 9, v_inst_2879_);
lean_closure_set(v___f_2885_, 10, v_inst_2880_);
v___x_2886_ = lean_apply_4(v_toBind_2881_, lean_box(0), lean_box(0), v_getCurrNamespace_2884_, v___f_2885_);
return v___x_2886_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__6(lean_object* v_inst_2887_, lean_object* v_n_2888_, lean_object* v_matchLocalDecl_x3f_2889_, lean_object* v___f_2890_, lean_object* v_inst_2891_, lean_object* v_inst_2892_, lean_object* v_inst_2893_, lean_object* v_inst_2894_, lean_object* v_inst_2895_, lean_object* v_toBind_2896_, lean_object* v_inst_2897_, lean_object* v_lctx_2898_){
_start:
{
lean_object* v___f_2899_; lean_object* v___x_2900_; 
lean_inc(v_toBind_2896_);
v___f_2899_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___redArg___lam__5), 12, 11);
lean_closure_set(v___f_2899_, 0, v_inst_2887_);
lean_closure_set(v___f_2899_, 1, v_n_2888_);
lean_closure_set(v___f_2899_, 2, v_lctx_2898_);
lean_closure_set(v___f_2899_, 3, v_matchLocalDecl_x3f_2889_);
lean_closure_set(v___f_2899_, 4, v___f_2890_);
lean_closure_set(v___f_2899_, 5, v_inst_2891_);
lean_closure_set(v___f_2899_, 6, v_inst_2892_);
lean_closure_set(v___f_2899_, 7, v_inst_2893_);
lean_closure_set(v___f_2899_, 8, v_inst_2894_);
lean_closure_set(v___f_2899_, 9, v_inst_2895_);
lean_closure_set(v___f_2899_, 10, v_toBind_2896_);
v___x_2900_ = lean_apply_4(v_toBind_2896_, lean_box(0), lean_box(0), v_inst_2897_, v___f_2899_);
return v___x_2900_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg(lean_object* v_inst_2903_, lean_object* v_inst_2904_, lean_object* v_inst_2905_, lean_object* v_inst_2906_, lean_object* v_inst_2907_, lean_object* v_inst_2908_, lean_object* v_inst_2909_, lean_object* v_n_2910_){
_start:
{
lean_object* v_toBind_2911_; lean_object* v___f_2912_; lean_object* v_matchLocalDecl_x3f_2913_; lean_object* v___f_2914_; lean_object* v___x_2915_; 
v_toBind_2911_ = lean_ctor_get(v_inst_2903_, 1);
lean_inc_n(v_toBind_2911_, 2);
v___f_2912_ = ((lean_object*)(l_Lean_resolveLocalName___redArg___closed__0));
v_matchLocalDecl_x3f_2913_ = ((lean_object*)(l_Lean_resolveLocalName___redArg___closed__1));
lean_inc(v_inst_2909_);
v___f_2914_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___redArg___lam__6), 12, 11);
lean_closure_set(v___f_2914_, 0, v_inst_2904_);
lean_closure_set(v___f_2914_, 1, v_n_2910_);
lean_closure_set(v___f_2914_, 2, v_matchLocalDecl_x3f_2913_);
lean_closure_set(v___f_2914_, 3, v___f_2912_);
lean_closure_set(v___f_2914_, 4, v_inst_2903_);
lean_closure_set(v___f_2914_, 5, v_inst_2905_);
lean_closure_set(v___f_2914_, 6, v_inst_2906_);
lean_closure_set(v___f_2914_, 7, v_inst_2907_);
lean_closure_set(v___f_2914_, 8, v_inst_2908_);
lean_closure_set(v___f_2914_, 9, v_toBind_2911_);
lean_closure_set(v___f_2914_, 10, v_inst_2909_);
v___x_2915_ = lean_apply_4(v_toBind_2911_, lean_box(0), lean_box(0), v_inst_2909_, v___f_2914_);
return v___x_2915_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName(lean_object* v_m_2916_, lean_object* v_inst_2917_, lean_object* v_inst_2918_, lean_object* v_inst_2919_, lean_object* v_inst_2920_, lean_object* v_inst_2921_, lean_object* v_inst_2922_, lean_object* v_inst_2923_, lean_object* v_n_2924_){
_start:
{
lean_object* v___x_2925_; 
v___x_2925_ = l_Lean_resolveLocalName___redArg(v_inst_2917_, v_inst_2918_, v_inst_2919_, v_inst_2920_, v_inst_2921_, v_inst_2922_, v_inst_2923_, v_n_2924_);
return v___x_2925_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__0(lean_object* v_toPure_2926_, uint8_t v_____do__lift_2927_){
_start:
{
lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; 
v___x_2928_ = lean_box(v_____do__lift_2927_);
v___x_2929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2929_, 0, v___x_2928_);
v___x_2930_ = lean_apply_2(v_toPure_2926_, lean_box(0), v___x_2929_);
return v___x_2930_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__0___boxed(lean_object* v_toPure_2931_, lean_object* v_____do__lift_2932_){
_start:
{
uint8_t v_____do__lift_1059__boxed_2933_; lean_object* v_res_2934_; 
v_____do__lift_1059__boxed_2933_ = lean_unbox(v_____do__lift_2932_);
v_res_2934_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__0(v_toPure_2931_, v_____do__lift_1059__boxed_2933_);
return v_res_2934_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__1(lean_object* v_toPure_2935_, lean_object* v___y_2936_, lean_object* v_____do__lift_2937_){
_start:
{
if (lean_obj_tag(v_____do__lift_2937_) == 0)
{
lean_object* v___x_2938_; lean_object* v___x_2939_; 
lean_dec(v___y_2936_);
v___x_2938_ = lean_box(0);
v___x_2939_ = lean_apply_2(v_toPure_2935_, lean_box(0), v___x_2938_);
return v___x_2939_;
}
else
{
lean_object* v___x_2941_; uint8_t v_isShared_2942_; uint8_t v_isSharedCheck_2947_; 
v_isSharedCheck_2947_ = !lean_is_exclusive(v_____do__lift_2937_);
if (v_isSharedCheck_2947_ == 0)
{
lean_object* v_unused_2948_; 
v_unused_2948_ = lean_ctor_get(v_____do__lift_2937_, 0);
lean_dec(v_unused_2948_);
v___x_2941_ = v_____do__lift_2937_;
v_isShared_2942_ = v_isSharedCheck_2947_;
goto v_resetjp_2940_;
}
else
{
lean_dec(v_____do__lift_2937_);
v___x_2941_ = lean_box(0);
v_isShared_2942_ = v_isSharedCheck_2947_;
goto v_resetjp_2940_;
}
v_resetjp_2940_:
{
lean_object* v___x_2944_; 
if (v_isShared_2942_ == 0)
{
lean_ctor_set(v___x_2941_, 0, v___y_2936_);
v___x_2944_ = v___x_2941_;
goto v_reusejp_2943_;
}
else
{
lean_object* v_reuseFailAlloc_2946_; 
v_reuseFailAlloc_2946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2946_, 0, v___y_2936_);
v___x_2944_ = v_reuseFailAlloc_2946_;
goto v_reusejp_2943_;
}
v_reusejp_2943_:
{
lean_object* v___x_2945_; 
v___x_2945_ = lean_apply_2(v_toPure_2935_, lean_box(0), v___x_2944_);
return v___x_2945_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2(lean_object* v_toPure_2951_, lean_object* v_toBind_2952_, lean_object* v___f_2953_, lean_object* v_____do__lift_2954_){
_start:
{
if (lean_obj_tag(v_____do__lift_2954_) == 0)
{
lean_object* v___x_2955_; lean_object* v___x_2956_; 
lean_dec(v___f_2953_);
lean_dec(v_toBind_2952_);
v___x_2955_ = lean_box(0);
v___x_2956_ = lean_apply_2(v_toPure_2951_, lean_box(0), v___x_2955_);
return v___x_2956_;
}
else
{
lean_object* v_val_2957_; uint8_t v___x_2958_; 
v_val_2957_ = lean_ctor_get(v_____do__lift_2954_, 0);
v___x_2958_ = lean_unbox(v_val_2957_);
if (v___x_2958_ == 0)
{
lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; 
v___x_2959_ = lean_box(0);
v___x_2960_ = lean_apply_2(v_toPure_2951_, lean_box(0), v___x_2959_);
v___x_2961_ = lean_apply_4(v_toBind_2952_, lean_box(0), lean_box(0), v___x_2960_, v___f_2953_);
return v___x_2961_;
}
else
{
lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; 
v___x_2962_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2___closed__0));
v___x_2963_ = lean_apply_2(v_toPure_2951_, lean_box(0), v___x_2962_);
v___x_2964_ = lean_apply_4(v_toBind_2952_, lean_box(0), lean_box(0), v___x_2963_, v___f_2953_);
return v___x_2964_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2___boxed(lean_object* v_toPure_2965_, lean_object* v_toBind_2966_, lean_object* v___f_2967_, lean_object* v_____do__lift_2968_){
_start:
{
lean_object* v_res_2969_; 
v_res_2969_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2(v_toPure_2965_, v_toBind_2966_, v___f_2967_, v_____do__lift_2968_);
lean_dec(v_____do__lift_2968_);
return v_res_2969_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__3(lean_object* v_toPure_2970_, lean_object* v_filter_2971_, lean_object* v___y_2972_, lean_object* v_toBind_2973_, lean_object* v___f_2974_, lean_object* v___f_2975_, lean_object* v_____do__lift_2976_){
_start:
{
if (lean_obj_tag(v_____do__lift_2976_) == 0)
{
lean_object* v___x_2977_; lean_object* v___x_2978_; 
lean_dec(v___f_2975_);
lean_dec(v___f_2974_);
lean_dec(v_toBind_2973_);
lean_dec(v___y_2972_);
lean_dec(v_filter_2971_);
v___x_2977_ = lean_box(0);
v___x_2978_ = lean_apply_2(v_toPure_2970_, lean_box(0), v___x_2977_);
return v___x_2978_;
}
else
{
lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; 
lean_dec(v_toPure_2970_);
v___x_2979_ = lean_apply_1(v_filter_2971_, v___y_2972_);
lean_inc(v_toBind_2973_);
v___x_2980_ = lean_apply_4(v_toBind_2973_, lean_box(0), lean_box(0), v___x_2979_, v___f_2974_);
v___x_2981_ = lean_apply_4(v_toBind_2973_, lean_box(0), lean_box(0), v___x_2980_, v___f_2975_);
return v___x_2981_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__3___boxed(lean_object* v_toPure_2982_, lean_object* v_filter_2983_, lean_object* v___y_2984_, lean_object* v_toBind_2985_, lean_object* v___f_2986_, lean_object* v___f_2987_, lean_object* v_____do__lift_2988_){
_start:
{
lean_object* v_res_2989_; 
v_res_2989_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__3(v_toPure_2982_, v_filter_2983_, v___y_2984_, v_toBind_2985_, v___f_2986_, v___f_2987_, v_____do__lift_2988_);
lean_dec(v_____do__lift_2988_);
return v_res_2989_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__4(lean_object* v_toPure_2990_, lean_object* v_n_u2080_2991_, lean_object* v_toBind_2992_, lean_object* v___f_2993_, lean_object* v_____do__lift_2994_){
_start:
{
if (lean_obj_tag(v_____do__lift_2994_) == 0)
{
lean_object* v___x_2998_; lean_object* v___x_2999_; 
lean_dec(v___f_2993_);
lean_dec(v_toBind_2992_);
v___x_2998_ = lean_box(0);
v___x_2999_ = lean_apply_2(v_toPure_2990_, lean_box(0), v___x_2998_);
return v___x_2999_;
}
else
{
lean_object* v_val_3000_; 
v_val_3000_ = lean_ctor_get(v_____do__lift_2994_, 0);
if (lean_obj_tag(v_val_3000_) == 1)
{
lean_object* v_tail_3001_; 
v_tail_3001_ = lean_ctor_get(v_val_3000_, 1);
if (lean_obj_tag(v_tail_3001_) == 0)
{
lean_object* v_head_3002_; lean_object* v_fst_3003_; uint8_t v___x_3004_; 
v_head_3002_ = lean_ctor_get(v_val_3000_, 0);
v_fst_3003_ = lean_ctor_get(v_head_3002_, 0);
v___x_3004_ = lean_name_eq(v_fst_3003_, v_n_u2080_2991_);
if (v___x_3004_ == 0)
{
lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; 
v___x_3005_ = lean_box(0);
v___x_3006_ = lean_apply_2(v_toPure_2990_, lean_box(0), v___x_3005_);
v___x_3007_ = lean_apply_4(v_toBind_2992_, lean_box(0), lean_box(0), v___x_3006_, v___f_2993_);
return v___x_3007_;
}
else
{
lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; 
v___x_3008_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2___closed__0));
v___x_3009_ = lean_apply_2(v_toPure_2990_, lean_box(0), v___x_3008_);
v___x_3010_ = lean_apply_4(v_toBind_2992_, lean_box(0), lean_box(0), v___x_3009_, v___f_2993_);
return v___x_3010_;
}
}
else
{
lean_dec(v___f_2993_);
lean_dec(v_toBind_2992_);
goto v___jp_2995_;
}
}
else
{
lean_dec(v___f_2993_);
lean_dec(v_toBind_2992_);
goto v___jp_2995_;
}
}
v___jp_2995_:
{
lean_object* v___x_2996_; lean_object* v___x_2997_; 
v___x_2996_ = lean_box(0);
v___x_2997_ = lean_apply_2(v_toPure_2990_, lean_box(0), v___x_2996_);
return v___x_2997_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__4___boxed(lean_object* v_toPure_3011_, lean_object* v_n_u2080_3012_, lean_object* v_toBind_3013_, lean_object* v___f_3014_, lean_object* v_____do__lift_3015_){
_start:
{
lean_object* v_res_3016_; 
v_res_3016_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__4(v_toPure_3011_, v_n_u2080_3012_, v_toBind_3013_, v___f_3014_, v_____do__lift_3015_);
lean_dec(v_____do__lift_3015_);
lean_dec(v_n_u2080_3012_);
return v_res_3016_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg(lean_object* v_inst_3017_, lean_object* v_inst_3018_, lean_object* v_inst_3019_, lean_object* v_inst_3020_, lean_object* v_inst_3021_, lean_object* v_inst_3022_, lean_object* v_n_u2080_3023_, lean_object* v_filter_3024_, lean_object* v_view_x3f_3025_, lean_object* v_n_3026_){
_start:
{
lean_object* v___f_3027_; lean_object* v___f_3028_; lean_object* v___f_3029_; lean_object* v___f_3030_; lean_object* v___f_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v_toApplicative_3039_; lean_object* v_getEnv_3040_; lean_object* v_modifyEnv_3041_; lean_object* v___x_3043_; uint8_t v_isShared_3044_; uint8_t v_isSharedCheck_3079_; 
lean_inc_ref_n(v_inst_3017_, 8);
v___f_3027_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_3027_, 0, v_inst_3017_);
v___f_3028_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__3), 5, 1);
lean_closure_set(v___f_3028_, 0, v_inst_3017_);
v___f_3029_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__6), 5, 1);
lean_closure_set(v___f_3029_, 0, v_inst_3017_);
v___f_3030_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_3030_, 0, v_inst_3017_);
v___f_3031_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__11), 5, 1);
lean_closure_set(v___f_3031_, 0, v_inst_3017_);
v___x_3032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3032_, 0, v___f_3027_);
lean_ctor_set(v___x_3032_, 1, v___f_3028_);
v___x_3033_ = lean_alloc_closure((void*)(l_OptionT_pure), 4, 2);
lean_closure_set(v___x_3033_, 0, lean_box(0));
lean_closure_set(v___x_3033_, 1, v_inst_3017_);
v___x_3034_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3034_, 0, v___x_3032_);
lean_ctor_set(v___x_3034_, 1, v___x_3033_);
lean_ctor_set(v___x_3034_, 2, v___f_3029_);
lean_ctor_set(v___x_3034_, 3, v___f_3030_);
lean_ctor_set(v___x_3034_, 4, v___f_3031_);
v___x_3035_ = lean_alloc_closure((void*)(l_OptionT_bind), 6, 2);
lean_closure_set(v___x_3035_, 0, lean_box(0));
lean_closure_set(v___x_3035_, 1, v_inst_3017_);
v___x_3036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3036_, 0, v___x_3034_);
lean_ctor_set(v___x_3036_, 1, v___x_3035_);
v___x_3037_ = lean_alloc_closure((void*)(l_OptionT_lift), 4, 2);
lean_closure_set(v___x_3037_, 0, lean_box(0));
lean_closure_set(v___x_3037_, 1, v_inst_3017_);
lean_inc_ref(v___x_3037_);
v___x_3038_ = l_Lean_instMonadResolveNameOfMonadLift___redArg(v___x_3037_, v_inst_3018_);
v_toApplicative_3039_ = lean_ctor_get(v_inst_3017_, 0);
lean_inc_ref(v_toApplicative_3039_);
v_getEnv_3040_ = lean_ctor_get(v_inst_3019_, 0);
v_modifyEnv_3041_ = lean_ctor_get(v_inst_3019_, 1);
v_isSharedCheck_3079_ = !lean_is_exclusive(v_inst_3019_);
if (v_isSharedCheck_3079_ == 0)
{
v___x_3043_ = v_inst_3019_;
v_isShared_3044_ = v_isSharedCheck_3079_;
goto v_resetjp_3042_;
}
else
{
lean_inc(v_modifyEnv_3041_);
lean_inc(v_getEnv_3040_);
lean_dec(v_inst_3019_);
v___x_3043_ = lean_box(0);
v_isShared_3044_ = v_isSharedCheck_3079_;
goto v_resetjp_3042_;
}
v_resetjp_3042_:
{
lean_object* v_toBind_3045_; lean_object* v_toPure_3046_; lean_object* v___f_3047_; lean_object* v___f_3048_; lean_object* v___f_3049_; lean_object* v___x_3050_; lean_object* v___x_3052_; 
v_toBind_3045_ = lean_ctor_get(v_inst_3017_, 1);
lean_inc_n(v_toBind_3045_, 2);
lean_dec_ref(v_inst_3017_);
v_toPure_3046_ = lean_ctor_get(v_toApplicative_3039_, 1);
lean_inc_n(v_toPure_3046_, 3);
lean_dec_ref(v_toApplicative_3039_);
lean_inc_ref(v___x_3037_);
v___f_3047_ = lean_alloc_closure((void*)(l_Lean_instMonadEnvOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3047_, 0, v_modifyEnv_3041_);
lean_closure_set(v___f_3047_, 1, v___x_3037_);
v___f_3048_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3048_, 0, v_toPure_3046_);
v___f_3049_ = lean_alloc_closure((void*)(l_OptionT_lift___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3049_, 0, v_toPure_3046_);
lean_inc_ref(v___f_3049_);
v___x_3050_ = lean_apply_4(v_toBind_3045_, lean_box(0), lean_box(0), v_getEnv_3040_, v___f_3049_);
if (v_isShared_3044_ == 0)
{
lean_ctor_set(v___x_3043_, 1, v___f_3047_);
lean_ctor_set(v___x_3043_, 0, v___x_3050_);
v___x_3052_ = v___x_3043_;
goto v_reusejp_3051_;
}
else
{
lean_object* v_reuseFailAlloc_3078_; 
v_reuseFailAlloc_3078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3078_, 0, v___x_3050_);
lean_ctor_set(v_reuseFailAlloc_3078_, 1, v___f_3047_);
v___x_3052_ = v_reuseFailAlloc_3078_;
goto v_reusejp_3051_;
}
v_reusejp_3051_:
{
lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___f_3055_; lean_object* v___y_3057_; 
lean_inc(v_toBind_3045_);
v___x_3053_ = lean_apply_4(v_toBind_3045_, lean_box(0), lean_box(0), v_inst_3020_, v___f_3049_);
lean_inc_ref(v___x_3037_);
v___x_3054_ = l_Lean_instMonadLogOfMonadLift___redArg(v___x_3037_, v_inst_3021_);
v___f_3055_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3055_, 0, v_inst_3022_);
lean_closure_set(v___f_3055_, 1, v___x_3037_);
if (lean_obj_tag(v_view_x3f_3025_) == 1)
{
lean_object* v_val_3065_; lean_object* v_imported_3066_; lean_object* v_ctx_3067_; lean_object* v_scopes_3068_; lean_object* v___x_3070_; uint8_t v_isShared_3071_; uint8_t v_isSharedCheck_3076_; 
v_val_3065_ = lean_ctor_get(v_view_x3f_3025_, 0);
lean_inc(v_val_3065_);
lean_dec_ref_known(v_view_x3f_3025_, 1);
v_imported_3066_ = lean_ctor_get(v_val_3065_, 1);
v_ctx_3067_ = lean_ctor_get(v_val_3065_, 2);
v_scopes_3068_ = lean_ctor_get(v_val_3065_, 3);
v_isSharedCheck_3076_ = !lean_is_exclusive(v_val_3065_);
if (v_isSharedCheck_3076_ == 0)
{
lean_object* v_unused_3077_; 
v_unused_3077_ = lean_ctor_get(v_val_3065_, 0);
lean_dec(v_unused_3077_);
v___x_3070_ = v_val_3065_;
v_isShared_3071_ = v_isSharedCheck_3076_;
goto v_resetjp_3069_;
}
else
{
lean_inc(v_scopes_3068_);
lean_inc(v_ctx_3067_);
lean_inc(v_imported_3066_);
lean_dec(v_val_3065_);
v___x_3070_ = lean_box(0);
v_isShared_3071_ = v_isSharedCheck_3076_;
goto v_resetjp_3069_;
}
v_resetjp_3069_:
{
lean_object* v___x_3073_; 
if (v_isShared_3071_ == 0)
{
lean_ctor_set(v___x_3070_, 0, v_n_3026_);
v___x_3073_ = v___x_3070_;
goto v_reusejp_3072_;
}
else
{
lean_object* v_reuseFailAlloc_3075_; 
v_reuseFailAlloc_3075_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3075_, 0, v_n_3026_);
lean_ctor_set(v_reuseFailAlloc_3075_, 1, v_imported_3066_);
lean_ctor_set(v_reuseFailAlloc_3075_, 2, v_ctx_3067_);
lean_ctor_set(v_reuseFailAlloc_3075_, 3, v_scopes_3068_);
v___x_3073_ = v_reuseFailAlloc_3075_;
goto v_reusejp_3072_;
}
v_reusejp_3072_:
{
lean_object* v___x_3074_; 
v___x_3074_ = l_Lean_MacroScopesView_review(v___x_3073_);
v___y_3057_ = v___x_3074_;
goto v___jp_3056_;
}
}
}
else
{
lean_dec(v_view_x3f_3025_);
v___y_3057_ = v_n_3026_;
goto v___jp_3056_;
}
v___jp_3056_:
{
lean_object* v___f_3058_; lean_object* v___f_3059_; lean_object* v___f_3060_; lean_object* v___f_3061_; uint8_t v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; 
lean_inc_n(v___y_3057_, 2);
lean_inc_n(v_toPure_3046_, 3);
v___f_3058_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__1), 3, 2);
lean_closure_set(v___f_3058_, 0, v_toPure_3046_);
lean_closure_set(v___f_3058_, 1, v___y_3057_);
lean_inc_n(v_toBind_3045_, 3);
v___f_3059_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_3059_, 0, v_toPure_3046_);
lean_closure_set(v___f_3059_, 1, v_toBind_3045_);
lean_closure_set(v___f_3059_, 2, v___f_3058_);
v___f_3060_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__3___boxed), 7, 6);
lean_closure_set(v___f_3060_, 0, v_toPure_3046_);
lean_closure_set(v___f_3060_, 1, v_filter_3024_);
lean_closure_set(v___f_3060_, 2, v___y_3057_);
lean_closure_set(v___f_3060_, 3, v_toBind_3045_);
lean_closure_set(v___f_3060_, 4, v___f_3048_);
lean_closure_set(v___f_3060_, 5, v___f_3059_);
v___f_3061_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__4___boxed), 5, 4);
lean_closure_set(v___f_3061_, 0, v_toPure_3046_);
lean_closure_set(v___f_3061_, 1, v_n_u2080_3023_);
lean_closure_set(v___f_3061_, 2, v_toBind_3045_);
lean_closure_set(v___f_3061_, 3, v___f_3060_);
v___x_3062_ = 0;
v___x_3063_ = l_Lean_resolveGlobalName___redArg(v___x_3036_, v___x_3038_, v___x_3052_, v___x_3053_, v___x_3054_, v___f_3055_, v___y_3057_, v___x_3062_);
v___x_3064_ = lean_apply_4(v_toBind_3045_, lean_box(0), lean_box(0), v___x_3063_, v___f_3061_);
return v___x_3064_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve(lean_object* v_m_3080_, lean_object* v_inst_3081_, lean_object* v_inst_3082_, lean_object* v_inst_3083_, lean_object* v_inst_3084_, lean_object* v_inst_3085_, lean_object* v_inst_3086_, lean_object* v_n_u2080_3087_, lean_object* v_filter_3088_, lean_object* v_view_x3f_3089_, lean_object* v_n_3090_){
_start:
{
lean_object* v___x_3091_; 
v___x_3091_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg(v_inst_3081_, v_inst_3082_, v_inst_3083_, v_inst_3084_, v_inst_3085_, v_inst_3086_, v_n_u2080_3087_, v_filter_3088_, v_view_x3f_3089_, v_n_3090_);
return v___x_3091_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__0(lean_object* v_toPure_3096_, lean_object* v_____x_3097_){
_start:
{
if (lean_obj_tag(v_____x_3097_) == 0)
{
lean_object* v___x_3098_; lean_object* v___x_3099_; 
v___x_3098_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__0___closed__1));
v___x_3099_ = lean_apply_2(v_toPure_3096_, lean_box(0), v___x_3098_);
return v___x_3099_;
}
else
{
lean_object* v___x_3100_; 
v___x_3100_ = lean_apply_2(v_toPure_3096_, lean_box(0), v_____x_3097_);
return v___x_3100_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__1(lean_object* v_toPure_3101_, lean_object* v_____do__lift_3102_){
_start:
{
if (lean_obj_tag(v_____do__lift_3102_) == 0)
{
lean_object* v___x_3103_; lean_object* v___x_3104_; 
v___x_3103_ = lean_box(0);
v___x_3104_ = lean_apply_2(v_toPure_3101_, lean_box(0), v___x_3103_);
return v___x_3104_;
}
else
{
lean_object* v_val_3105_; lean_object* v___x_3107_; uint8_t v_isShared_3108_; uint8_t v_isSharedCheck_3114_; 
v_val_3105_ = lean_ctor_get(v_____do__lift_3102_, 0);
v_isSharedCheck_3114_ = !lean_is_exclusive(v_____do__lift_3102_);
if (v_isSharedCheck_3114_ == 0)
{
v___x_3107_ = v_____do__lift_3102_;
v_isShared_3108_ = v_isSharedCheck_3114_;
goto v_resetjp_3106_;
}
else
{
lean_inc(v_val_3105_);
lean_dec(v_____do__lift_3102_);
v___x_3107_ = lean_box(0);
v_isShared_3108_ = v_isSharedCheck_3114_;
goto v_resetjp_3106_;
}
v_resetjp_3106_:
{
lean_object* v___x_3109_; lean_object* v___x_3111_; 
v___x_3109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3109_, 0, v_val_3105_);
if (v_isShared_3108_ == 0)
{
lean_ctor_set(v___x_3107_, 0, v___x_3109_);
v___x_3111_ = v___x_3107_;
goto v_reusejp_3110_;
}
else
{
lean_object* v_reuseFailAlloc_3113_; 
v_reuseFailAlloc_3113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3113_, 0, v___x_3109_);
v___x_3111_ = v_reuseFailAlloc_3113_;
goto v_reusejp_3110_;
}
v_reusejp_3110_:
{
lean_object* v___x_3112_; 
v___x_3112_ = lean_apply_2(v_toPure_3101_, lean_box(0), v___x_3111_);
return v___x_3112_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__2(lean_object* v_toPure_3115_, lean_object* v___x_3116_, lean_object* v_____do__lift_3117_){
_start:
{
if (lean_obj_tag(v_____do__lift_3117_) == 0)
{
lean_object* v___x_3118_; 
v___x_3118_ = lean_apply_2(v_toPure_3115_, lean_box(0), v___x_3116_);
return v___x_3118_;
}
else
{
lean_object* v_val_3119_; lean_object* v_fst_3120_; lean_object* v___x_3121_; 
lean_dec(v___x_3116_);
v_val_3119_ = lean_ctor_get(v_____do__lift_3117_, 0);
lean_inc(v_val_3119_);
lean_dec_ref_known(v_____do__lift_3117_, 1);
v_fst_3120_ = lean_ctor_get(v_val_3119_, 0);
lean_inc(v_fst_3120_);
lean_dec(v_val_3119_);
v___x_3121_ = lean_apply_2(v_toPure_3115_, lean_box(0), v_fst_3120_);
return v___x_3121_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__3(lean_object* v_toPure_3122_, lean_object* v___x_3123_, lean_object* v___x_3124_, lean_object* v_____do__lift_3125_){
_start:
{
if (lean_obj_tag(v_____do__lift_3125_) == 0)
{
lean_object* v___x_3126_; lean_object* v___x_3127_; 
lean_dec(v___x_3124_);
lean_dec(v___x_3123_);
v___x_3126_ = lean_box(0);
v___x_3127_ = lean_apply_2(v_toPure_3122_, lean_box(0), v___x_3126_);
return v___x_3127_;
}
else
{
lean_object* v_val_3128_; lean_object* v___x_3130_; uint8_t v_isShared_3131_; uint8_t v_isSharedCheck_3159_; 
v_val_3128_ = lean_ctor_get(v_____do__lift_3125_, 0);
v_isSharedCheck_3159_ = !lean_is_exclusive(v_____do__lift_3125_);
if (v_isSharedCheck_3159_ == 0)
{
v___x_3130_ = v_____do__lift_3125_;
v_isShared_3131_ = v_isSharedCheck_3159_;
goto v_resetjp_3129_;
}
else
{
lean_inc(v_val_3128_);
lean_dec(v_____do__lift_3125_);
v___x_3130_ = lean_box(0);
v_isShared_3131_ = v_isSharedCheck_3159_;
goto v_resetjp_3129_;
}
v_resetjp_3129_:
{
if (lean_obj_tag(v_val_3128_) == 0)
{
lean_object* v_a_3132_; lean_object* v___x_3134_; uint8_t v_isShared_3135_; uint8_t v_isSharedCheck_3145_; 
lean_dec(v___x_3124_);
v_a_3132_ = lean_ctor_get(v_val_3128_, 0);
v_isSharedCheck_3145_ = !lean_is_exclusive(v_val_3128_);
if (v_isSharedCheck_3145_ == 0)
{
v___x_3134_ = v_val_3128_;
v_isShared_3135_ = v_isSharedCheck_3145_;
goto v_resetjp_3133_;
}
else
{
lean_inc(v_a_3132_);
lean_dec(v_val_3128_);
v___x_3134_ = lean_box(0);
v_isShared_3135_ = v_isSharedCheck_3145_;
goto v_resetjp_3133_;
}
v_resetjp_3133_:
{
lean_object* v___x_3137_; 
if (v_isShared_3131_ == 0)
{
lean_ctor_set(v___x_3130_, 0, v_a_3132_);
v___x_3137_ = v___x_3130_;
goto v_reusejp_3136_;
}
else
{
lean_object* v_reuseFailAlloc_3144_; 
v_reuseFailAlloc_3144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3144_, 0, v_a_3132_);
v___x_3137_ = v_reuseFailAlloc_3144_;
goto v_reusejp_3136_;
}
v_reusejp_3136_:
{
lean_object* v___x_3138_; lean_object* v___x_3140_; 
v___x_3138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3138_, 0, v___x_3137_);
lean_ctor_set(v___x_3138_, 1, v___x_3123_);
if (v_isShared_3135_ == 0)
{
lean_ctor_set(v___x_3134_, 0, v___x_3138_);
v___x_3140_ = v___x_3134_;
goto v_reusejp_3139_;
}
else
{
lean_object* v_reuseFailAlloc_3143_; 
v_reuseFailAlloc_3143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3143_, 0, v___x_3138_);
v___x_3140_ = v_reuseFailAlloc_3143_;
goto v_reusejp_3139_;
}
v_reusejp_3139_:
{
lean_object* v___x_3141_; lean_object* v___x_3142_; 
v___x_3141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3141_, 0, v___x_3140_);
v___x_3142_ = lean_apply_2(v_toPure_3122_, lean_box(0), v___x_3141_);
return v___x_3142_;
}
}
}
}
else
{
lean_object* v___x_3147_; uint8_t v_isShared_3148_; uint8_t v_isSharedCheck_3157_; 
v_isSharedCheck_3157_ = !lean_is_exclusive(v_val_3128_);
if (v_isSharedCheck_3157_ == 0)
{
lean_object* v_unused_3158_; 
v_unused_3158_ = lean_ctor_get(v_val_3128_, 0);
lean_dec(v_unused_3158_);
v___x_3147_ = v_val_3128_;
v_isShared_3148_ = v_isSharedCheck_3157_;
goto v_resetjp_3146_;
}
else
{
lean_dec(v_val_3128_);
v___x_3147_ = lean_box(0);
v_isShared_3148_ = v_isSharedCheck_3157_;
goto v_resetjp_3146_;
}
v_resetjp_3146_:
{
lean_object* v___x_3149_; lean_object* v___x_3151_; 
v___x_3149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3149_, 0, v___x_3124_);
lean_ctor_set(v___x_3149_, 1, v___x_3123_);
if (v_isShared_3148_ == 0)
{
lean_ctor_set(v___x_3147_, 0, v___x_3149_);
v___x_3151_ = v___x_3147_;
goto v_reusejp_3150_;
}
else
{
lean_object* v_reuseFailAlloc_3156_; 
v_reuseFailAlloc_3156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3156_, 0, v___x_3149_);
v___x_3151_ = v_reuseFailAlloc_3156_;
goto v_reusejp_3150_;
}
v_reusejp_3150_:
{
lean_object* v___x_3153_; 
if (v_isShared_3131_ == 0)
{
lean_ctor_set(v___x_3130_, 0, v___x_3151_);
v___x_3153_ = v___x_3130_;
goto v_reusejp_3152_;
}
else
{
lean_object* v_reuseFailAlloc_3155_; 
v_reuseFailAlloc_3155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3155_, 0, v___x_3151_);
v___x_3153_ = v_reuseFailAlloc_3155_;
goto v_reusejp_3152_;
}
v_reusejp_3152_:
{
lean_object* v___x_3154_; 
v___x_3154_ = lean_apply_2(v_toPure_3122_, lean_box(0), v___x_3153_);
return v___x_3154_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__4(lean_object* v_toPure_3160_, lean_object* v___x_3161_, lean_object* v_inst_3162_, lean_object* v_inst_3163_, lean_object* v_inst_3164_, lean_object* v_inst_3165_, lean_object* v_inst_3166_, lean_object* v_inst_3167_, lean_object* v_n_u2080_3168_, lean_object* v_filter_3169_, lean_object* v_view_x3f_3170_, lean_object* v_toBind_3171_, lean_object* v___f_3172_, lean_object* v___f_3173_, lean_object* v_a_3174_, lean_object* v_x_3175_, lean_object* v___y_3176_){
_start:
{
lean_object* v_snd_3177_; lean_object* v___x_3178_; lean_object* v___f_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; 
v_snd_3177_ = lean_ctor_get(v___y_3176_, 1);
lean_inc(v_snd_3177_);
lean_dec_ref(v___y_3176_);
v___x_3178_ = l_Lean_Name_appendCore(v_a_3174_, v_snd_3177_);
lean_inc(v___x_3178_);
v___f_3179_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__3), 4, 3);
lean_closure_set(v___f_3179_, 0, v_toPure_3160_);
lean_closure_set(v___f_3179_, 1, v___x_3178_);
lean_closure_set(v___f_3179_, 2, v___x_3161_);
v___x_3180_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg(v_inst_3162_, v_inst_3163_, v_inst_3164_, v_inst_3165_, v_inst_3166_, v_inst_3167_, v_n_u2080_3168_, v_filter_3169_, v_view_x3f_3170_, v___x_3178_);
lean_inc_n(v_toBind_3171_, 2);
v___x_3181_ = lean_apply_4(v_toBind_3171_, lean_box(0), lean_box(0), v___x_3180_, v___f_3172_);
v___x_3182_ = lean_apply_4(v_toBind_3171_, lean_box(0), lean_box(0), v___x_3181_, v___f_3173_);
v___x_3183_ = lean_apply_4(v_toBind_3171_, lean_box(0), lean_box(0), v___x_3182_, v___f_3179_);
return v___x_3183_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__4___boxed(lean_object** _args){
lean_object* v_toPure_3184_ = _args[0];
lean_object* v___x_3185_ = _args[1];
lean_object* v_inst_3186_ = _args[2];
lean_object* v_inst_3187_ = _args[3];
lean_object* v_inst_3188_ = _args[4];
lean_object* v_inst_3189_ = _args[5];
lean_object* v_inst_3190_ = _args[6];
lean_object* v_inst_3191_ = _args[7];
lean_object* v_n_u2080_3192_ = _args[8];
lean_object* v_filter_3193_ = _args[9];
lean_object* v_view_x3f_3194_ = _args[10];
lean_object* v_toBind_3195_ = _args[11];
lean_object* v___f_3196_ = _args[12];
lean_object* v___f_3197_ = _args[13];
lean_object* v_a_3198_ = _args[14];
lean_object* v_x_3199_ = _args[15];
lean_object* v___y_3200_ = _args[16];
_start:
{
lean_object* v_res_3201_; 
v_res_3201_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__4(v_toPure_3184_, v___x_3185_, v_inst_3186_, v_inst_3187_, v_inst_3188_, v_inst_3189_, v_inst_3190_, v_inst_3191_, v_n_u2080_3192_, v_filter_3193_, v_view_x3f_3194_, v_toBind_3195_, v___f_3196_, v___f_3197_, v_a_3198_, v_x_3199_, v___y_3200_);
lean_dec(v_a_3198_);
return v_res_3201_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__5(lean_object* v_toPure_3205_, lean_object* v_n_3206_, lean_object* v_inst_3207_, lean_object* v_inst_3208_, lean_object* v_inst_3209_, lean_object* v_inst_3210_, lean_object* v_inst_3211_, lean_object* v_inst_3212_, lean_object* v_n_u2080_3213_, lean_object* v_filter_3214_, lean_object* v_view_x3f_3215_, lean_object* v_toBind_3216_, lean_object* v___f_3217_, lean_object* v___f_3218_, lean_object* v___x_3219_, lean_object* v_____do__lift_3220_){
_start:
{
if (lean_obj_tag(v_____do__lift_3220_) == 0)
{
lean_object* v___x_3221_; lean_object* v___x_3222_; 
lean_dec_ref(v___x_3219_);
lean_dec(v___f_3218_);
lean_dec(v___f_3217_);
lean_dec(v_toBind_3216_);
lean_dec(v_view_x3f_3215_);
lean_dec(v_filter_3214_);
lean_dec(v_n_u2080_3213_);
lean_dec(v_inst_3212_);
lean_dec_ref(v_inst_3211_);
lean_dec(v_inst_3210_);
lean_dec_ref(v_inst_3209_);
lean_dec_ref(v_inst_3208_);
lean_dec_ref(v_inst_3207_);
lean_dec(v_n_3206_);
v___x_3221_ = lean_box(0);
v___x_3222_ = lean_apply_2(v_toPure_3205_, lean_box(0), v___x_3221_);
return v___x_3222_;
}
else
{
lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___f_3226_; lean_object* v___f_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; 
v___x_3223_ = l_Lean_privateToUserName(v_n_3206_);
v___x_3224_ = l_Lean_Name_componentsRev(v___x_3223_);
v___x_3225_ = lean_box(0);
lean_inc(v_toPure_3205_);
v___f_3226_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__2), 3, 2);
lean_closure_set(v___f_3226_, 0, v_toPure_3205_);
lean_closure_set(v___f_3226_, 1, v___x_3225_);
lean_inc(v_toBind_3216_);
v___f_3227_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__4___boxed), 17, 14);
lean_closure_set(v___f_3227_, 0, v_toPure_3205_);
lean_closure_set(v___f_3227_, 1, v___x_3225_);
lean_closure_set(v___f_3227_, 2, v_inst_3207_);
lean_closure_set(v___f_3227_, 3, v_inst_3208_);
lean_closure_set(v___f_3227_, 4, v_inst_3209_);
lean_closure_set(v___f_3227_, 5, v_inst_3210_);
lean_closure_set(v___f_3227_, 6, v_inst_3211_);
lean_closure_set(v___f_3227_, 7, v_inst_3212_);
lean_closure_set(v___f_3227_, 8, v_n_u2080_3213_);
lean_closure_set(v___f_3227_, 9, v_filter_3214_);
lean_closure_set(v___f_3227_, 10, v_view_x3f_3215_);
lean_closure_set(v___f_3227_, 11, v_toBind_3216_);
lean_closure_set(v___f_3227_, 12, v___f_3217_);
lean_closure_set(v___f_3227_, 13, v___f_3218_);
v___x_3228_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__5___closed__0));
v___x_3229_ = l_List_forIn_x27_loop___redArg(v___x_3219_, v___f_3227_, v___x_3224_, v___x_3228_);
lean_dec(v___x_3224_);
v___x_3230_ = lean_apply_4(v_toBind_3216_, lean_box(0), lean_box(0), v___x_3229_, v___f_3226_);
return v___x_3230_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__5___boxed(lean_object* v_toPure_3231_, lean_object* v_n_3232_, lean_object* v_inst_3233_, lean_object* v_inst_3234_, lean_object* v_inst_3235_, lean_object* v_inst_3236_, lean_object* v_inst_3237_, lean_object* v_inst_3238_, lean_object* v_n_u2080_3239_, lean_object* v_filter_3240_, lean_object* v_view_x3f_3241_, lean_object* v_toBind_3242_, lean_object* v___f_3243_, lean_object* v___f_3244_, lean_object* v___x_3245_, lean_object* v_____do__lift_3246_){
_start:
{
lean_object* v_res_3247_; 
v_res_3247_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__5(v_toPure_3231_, v_n_3232_, v_inst_3233_, v_inst_3234_, v_inst_3235_, v_inst_3236_, v_inst_3237_, v_inst_3238_, v_n_u2080_3239_, v_filter_3240_, v_view_x3f_3241_, v_toBind_3242_, v___f_3243_, v___f_3244_, v___x_3245_, v_____do__lift_3246_);
lean_dec(v_____do__lift_3246_);
return v_res_3247_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg(lean_object* v_inst_3248_, lean_object* v_inst_3249_, lean_object* v_inst_3250_, lean_object* v_inst_3251_, lean_object* v_inst_3252_, lean_object* v_inst_3253_, lean_object* v_n_u2080_3254_, lean_object* v_filter_3255_, lean_object* v_view_x3f_3256_, lean_object* v_n_3257_){
_start:
{
lean_object* v___f_3258_; lean_object* v___f_3259_; lean_object* v___f_3260_; lean_object* v___f_3261_; lean_object* v___f_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___y_3269_; uint8_t v___x_3277_; 
lean_inc_ref_n(v_inst_3248_, 7);
v___f_3258_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_3258_, 0, v_inst_3248_);
v___f_3259_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__3), 5, 1);
lean_closure_set(v___f_3259_, 0, v_inst_3248_);
v___f_3260_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__6), 5, 1);
lean_closure_set(v___f_3260_, 0, v_inst_3248_);
v___f_3261_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_3261_, 0, v_inst_3248_);
v___f_3262_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__11), 5, 1);
lean_closure_set(v___f_3262_, 0, v_inst_3248_);
v___x_3263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3263_, 0, v___f_3258_);
lean_ctor_set(v___x_3263_, 1, v___f_3259_);
v___x_3264_ = lean_alloc_closure((void*)(l_OptionT_pure), 4, 2);
lean_closure_set(v___x_3264_, 0, lean_box(0));
lean_closure_set(v___x_3264_, 1, v_inst_3248_);
v___x_3265_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3265_, 0, v___x_3263_);
lean_ctor_set(v___x_3265_, 1, v___x_3264_);
lean_ctor_set(v___x_3265_, 2, v___f_3260_);
lean_ctor_set(v___x_3265_, 3, v___f_3261_);
lean_ctor_set(v___x_3265_, 4, v___f_3262_);
v___x_3266_ = lean_alloc_closure((void*)(l_OptionT_bind), 6, 2);
lean_closure_set(v___x_3266_, 0, lean_box(0));
lean_closure_set(v___x_3266_, 1, v_inst_3248_);
v___x_3267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3267_, 0, v___x_3265_);
lean_ctor_set(v___x_3267_, 1, v___x_3266_);
v___x_3277_ = l_Lean_Name_hasMacroScopes(v_n_3257_);
if (v___x_3277_ == 0)
{
lean_object* v_toApplicative_3278_; lean_object* v_toPure_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; 
v_toApplicative_3278_ = lean_ctor_get(v_inst_3248_, 0);
v_toPure_3279_ = lean_ctor_get(v_toApplicative_3278_, 1);
v___x_3280_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2___closed__0));
lean_inc(v_toPure_3279_);
v___x_3281_ = lean_apply_2(v_toPure_3279_, lean_box(0), v___x_3280_);
v___y_3269_ = v___x_3281_;
goto v___jp_3268_;
}
else
{
lean_object* v_toApplicative_3282_; lean_object* v_toPure_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; 
v_toApplicative_3282_ = lean_ctor_get(v_inst_3248_, 0);
v_toPure_3283_ = lean_ctor_get(v_toApplicative_3282_, 1);
v___x_3284_ = lean_box(0);
lean_inc(v_toPure_3283_);
v___x_3285_ = lean_apply_2(v_toPure_3283_, lean_box(0), v___x_3284_);
v___y_3269_ = v___x_3285_;
goto v___jp_3268_;
}
v___jp_3268_:
{
lean_object* v_toApplicative_3270_; lean_object* v_toBind_3271_; lean_object* v_toPure_3272_; lean_object* v___f_3273_; lean_object* v___f_3274_; lean_object* v___f_3275_; lean_object* v___x_3276_; 
v_toApplicative_3270_ = lean_ctor_get(v_inst_3248_, 0);
v_toBind_3271_ = lean_ctor_get(v_inst_3248_, 1);
lean_inc_n(v_toBind_3271_, 2);
v_toPure_3272_ = lean_ctor_get(v_toApplicative_3270_, 1);
lean_inc_n(v_toPure_3272_, 3);
v___f_3273_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3273_, 0, v_toPure_3272_);
v___f_3274_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__1), 2, 1);
lean_closure_set(v___f_3274_, 0, v_toPure_3272_);
v___f_3275_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__5___boxed), 16, 15);
lean_closure_set(v___f_3275_, 0, v_toPure_3272_);
lean_closure_set(v___f_3275_, 1, v_n_3257_);
lean_closure_set(v___f_3275_, 2, v_inst_3248_);
lean_closure_set(v___f_3275_, 3, v_inst_3249_);
lean_closure_set(v___f_3275_, 4, v_inst_3250_);
lean_closure_set(v___f_3275_, 5, v_inst_3251_);
lean_closure_set(v___f_3275_, 6, v_inst_3252_);
lean_closure_set(v___f_3275_, 7, v_inst_3253_);
lean_closure_set(v___f_3275_, 8, v_n_u2080_3254_);
lean_closure_set(v___f_3275_, 9, v_filter_3255_);
lean_closure_set(v___f_3275_, 10, v_view_x3f_3256_);
lean_closure_set(v___f_3275_, 11, v_toBind_3271_);
lean_closure_set(v___f_3275_, 12, v___f_3274_);
lean_closure_set(v___f_3275_, 13, v___f_3273_);
lean_closure_set(v___f_3275_, 14, v___x_3267_);
v___x_3276_ = lean_apply_4(v_toBind_3271_, lean_box(0), lean_box(0), v___y_3269_, v___f_3275_);
return v___x_3276_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore(lean_object* v_m_3286_, lean_object* v_inst_3287_, lean_object* v_inst_3288_, lean_object* v_inst_3289_, lean_object* v_inst_3290_, lean_object* v_inst_3291_, lean_object* v_inst_3292_, lean_object* v_n_u2080_3293_, lean_object* v_filter_3294_, lean_object* v_view_x3f_3295_, lean_object* v_n_3296_){
_start:
{
lean_object* v___x_3297_; 
v___x_3297_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg(v_inst_3287_, v_inst_3288_, v_inst_3289_, v_inst_3290_, v_inst_3291_, v_inst_3292_, v_n_u2080_3293_, v_filter_3294_, v_view_x3f_3295_, v_n_3296_);
return v___x_3297_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___lam__0(lean_object* v_n_u2081_3298_, lean_object* v_x1_3299_, lean_object* v_x2_3300_){
_start:
{
lean_object* v___x_3301_; lean_object* v___x_3302_; uint8_t v___x_3303_; 
v___x_3301_ = l_Lean_Name_getPrefix(v_x2_3300_);
v___x_3302_ = l_Lean_Name_getPrefix(v_n_u2081_3298_);
v___x_3303_ = l_Lean_Name_isPrefixOf(v___x_3301_, v___x_3302_);
lean_dec(v___x_3302_);
lean_dec(v___x_3301_);
if (v___x_3303_ == 0)
{
lean_dec(v_x2_3300_);
return v_x1_3299_;
}
else
{
lean_object* v___x_3304_; 
v___x_3304_ = lean_array_push(v_x1_3299_, v_x2_3300_);
return v___x_3304_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___lam__0___boxed(lean_object* v_n_u2081_3305_, lean_object* v_x1_3306_, lean_object* v_x2_3307_){
_start:
{
lean_object* v_res_3308_; 
v_res_3308_ = l_Lean_unresolveNameGlobal_x3f___redArg___lam__0(v_n_u2081_3305_, v_x1_3306_, v_x2_3307_);
lean_dec(v_n_u2081_3305_);
return v_res_3308_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___lam__1(lean_object* v_view_3309_, lean_object* v_n_u2081_3310_, lean_object* v_inst_3311_, lean_object* v_inst_3312_, lean_object* v_inst_3313_, lean_object* v_inst_3314_, lean_object* v_inst_3315_, lean_object* v_inst_3316_, lean_object* v_n_u2080_3317_, lean_object* v_filter_3318_, lean_object* v_toPure_3319_, lean_object* v_____do__lift_3320_){
_start:
{
if (lean_obj_tag(v_____do__lift_3320_) == 0)
{
lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; 
lean_dec(v_toPure_3319_);
v___x_3321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3321_, 0, v_view_3309_);
v___x_3322_ = l_Lean_rootNamespace;
v___x_3323_ = l_Lean_Name_append(v___x_3322_, v_n_u2081_3310_);
v___x_3324_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg(v_inst_3311_, v_inst_3312_, v_inst_3313_, v_inst_3314_, v_inst_3315_, v_inst_3316_, v_n_u2080_3317_, v_filter_3318_, v___x_3321_, v___x_3323_);
return v___x_3324_;
}
else
{
lean_object* v___x_3325_; 
lean_dec(v_filter_3318_);
lean_dec(v_n_u2080_3317_);
lean_dec(v_inst_3316_);
lean_dec_ref(v_inst_3315_);
lean_dec(v_inst_3314_);
lean_dec_ref(v_inst_3313_);
lean_dec_ref(v_inst_3312_);
lean_dec_ref(v_inst_3311_);
lean_dec(v_n_u2081_3310_);
lean_dec_ref(v_view_3309_);
v___x_3325_ = lean_apply_2(v_toPure_3319_, lean_box(0), v_____do__lift_3320_);
return v___x_3325_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___lam__2(lean_object* v_toPure_3326_, lean_object* v_inst_3327_, lean_object* v_inst_3328_, lean_object* v_inst_3329_, lean_object* v_inst_3330_, lean_object* v_inst_3331_, lean_object* v_inst_3332_, lean_object* v_n_u2080_3333_, lean_object* v_filter_3334_, lean_object* v___x_3335_, lean_object* v_toBind_3336_, lean_object* v___f_3337_, uint8_t v_allowHorizAliases_3338_, lean_object* v___f_3339_, lean_object* v_____do__lift_3340_){
_start:
{
lean_object* v_aliases_3342_; 
if (lean_obj_tag(v_____do__lift_3340_) == 0)
{
lean_object* v___x_3348_; lean_object* v___x_3349_; 
lean_dec_ref(v___f_3339_);
lean_dec(v___f_3337_);
lean_dec(v_toBind_3336_);
lean_dec_ref(v___x_3335_);
lean_dec(v_filter_3334_);
lean_dec(v_n_u2080_3333_);
lean_dec(v_inst_3332_);
lean_dec_ref(v_inst_3331_);
lean_dec(v_inst_3330_);
lean_dec_ref(v_inst_3329_);
lean_dec_ref(v_inst_3328_);
lean_dec_ref(v_inst_3327_);
v___x_3348_ = lean_box(0);
v___x_3349_ = lean_apply_2(v_toPure_3326_, lean_box(0), v___x_3348_);
return v___x_3349_;
}
else
{
lean_object* v_val_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; 
lean_dec(v_toPure_3326_);
v_val_3350_ = lean_ctor_get(v_____do__lift_3340_, 0);
lean_inc(v_val_3350_);
lean_dec_ref_known(v_____do__lift_3340_, 1);
lean_inc(v_n_u2080_3333_);
v___x_3351_ = l_Lean_getRevAliases(v_val_3350_, v_n_u2080_3333_);
v___x_3352_ = lean_array_mk(v___x_3351_);
if (v_allowHorizAliases_3338_ == 0)
{
lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; uint8_t v___x_3357_; 
v___x_3353_ = lean_unsigned_to_nat(0u);
v___x_3354_ = lean_array_get_size(v___x_3352_);
v___x_3355_ = ((lean_object*)(l_Lean_resolveNamespace___redArg___closed__1));
v___x_3356_ = ((lean_object*)(l_Lean_resolveLocalName___redArg___lam__3___closed__9));
v___x_3357_ = lean_nat_dec_lt(v___x_3353_, v___x_3354_);
if (v___x_3357_ == 0)
{
lean_dec_ref(v___x_3352_);
lean_dec_ref(v___f_3339_);
v_aliases_3342_ = v___x_3355_;
goto v___jp_3341_;
}
else
{
uint8_t v___x_3358_; 
v___x_3358_ = lean_nat_dec_le(v___x_3354_, v___x_3354_);
if (v___x_3358_ == 0)
{
if (v___x_3357_ == 0)
{
lean_dec_ref(v___x_3352_);
lean_dec_ref(v___f_3339_);
v_aliases_3342_ = v___x_3355_;
goto v___jp_3341_;
}
else
{
size_t v___x_3359_; size_t v___x_3360_; lean_object* v___x_3361_; 
v___x_3359_ = ((size_t)0ULL);
v___x_3360_ = lean_usize_of_nat(v___x_3354_);
v___x_3361_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3356_, v___f_3339_, v___x_3352_, v___x_3359_, v___x_3360_, v___x_3355_);
v_aliases_3342_ = v___x_3361_;
goto v___jp_3341_;
}
}
else
{
size_t v___x_3362_; size_t v___x_3363_; lean_object* v___x_3364_; 
v___x_3362_ = ((size_t)0ULL);
v___x_3363_ = lean_usize_of_nat(v___x_3354_);
v___x_3364_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3356_, v___f_3339_, v___x_3352_, v___x_3362_, v___x_3363_, v___x_3355_);
v_aliases_3342_ = v___x_3364_;
goto v___jp_3341_;
}
}
}
else
{
lean_dec_ref(v___f_3339_);
v_aliases_3342_ = v___x_3352_;
goto v___jp_3341_;
}
}
v___jp_3341_:
{
lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; 
v___x_3343_ = lean_box(0);
v___x_3344_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore), 11, 10);
lean_closure_set(v___x_3344_, 0, lean_box(0));
lean_closure_set(v___x_3344_, 1, v_inst_3327_);
lean_closure_set(v___x_3344_, 2, v_inst_3328_);
lean_closure_set(v___x_3344_, 3, v_inst_3329_);
lean_closure_set(v___x_3344_, 4, v_inst_3330_);
lean_closure_set(v___x_3344_, 5, v_inst_3331_);
lean_closure_set(v___x_3344_, 6, v_inst_3332_);
lean_closure_set(v___x_3344_, 7, v_n_u2080_3333_);
lean_closure_set(v___x_3344_, 8, v_filter_3334_);
lean_closure_set(v___x_3344_, 9, v___x_3343_);
v___x_3345_ = lean_unsigned_to_nat(0u);
v___x_3346_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go(lean_box(0), lean_box(0), lean_box(0), v___x_3335_, v___x_3344_, v_aliases_3342_, v___x_3345_);
v___x_3347_ = lean_apply_4(v_toBind_3336_, lean_box(0), lean_box(0), v___x_3346_, v___f_3337_);
return v___x_3347_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___lam__2___boxed(lean_object* v_toPure_3365_, lean_object* v_inst_3366_, lean_object* v_inst_3367_, lean_object* v_inst_3368_, lean_object* v_inst_3369_, lean_object* v_inst_3370_, lean_object* v_inst_3371_, lean_object* v_n_u2080_3372_, lean_object* v_filter_3373_, lean_object* v___x_3374_, lean_object* v_toBind_3375_, lean_object* v___f_3376_, lean_object* v_allowHorizAliases_3377_, lean_object* v___f_3378_, lean_object* v_____do__lift_3379_){
_start:
{
uint8_t v_allowHorizAliases_boxed_3380_; lean_object* v_res_3381_; 
v_allowHorizAliases_boxed_3380_ = lean_unbox(v_allowHorizAliases_3377_);
v_res_3381_ = l_Lean_unresolveNameGlobal_x3f___redArg___lam__2(v_toPure_3365_, v_inst_3366_, v_inst_3367_, v_inst_3368_, v_inst_3369_, v_inst_3370_, v_inst_3371_, v_n_u2080_3372_, v_filter_3373_, v___x_3374_, v_toBind_3375_, v___f_3376_, v_allowHorizAliases_boxed_3380_, v___f_3378_, v_____do__lift_3379_);
return v_res_3381_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___lam__3(lean_object* v_toPure_3382_, lean_object* v_____do__lift_3383_){
_start:
{
lean_object* v___x_3384_; lean_object* v___x_3385_; 
v___x_3384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3384_, 0, v_____do__lift_3383_);
v___x_3385_ = lean_apply_2(v_toPure_3382_, lean_box(0), v___x_3384_);
return v___x_3385_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___lam__4(lean_object* v_n_u2081_3386_, lean_object* v_inst_3387_, lean_object* v_inst_3388_, lean_object* v_inst_3389_, lean_object* v_inst_3390_, lean_object* v_inst_3391_, lean_object* v_inst_3392_, lean_object* v_n_u2080_3393_, lean_object* v_filter_3394_, lean_object* v___x_3395_, lean_object* v_toPure_3396_, lean_object* v_____do__lift_3397_){
_start:
{
if (lean_obj_tag(v_____do__lift_3397_) == 0)
{
lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; 
lean_dec(v_toPure_3396_);
v___x_3398_ = l_Lean_rootNamespace;
v___x_3399_ = l_Lean_Name_append(v___x_3398_, v_n_u2081_3386_);
v___x_3400_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg(v_inst_3387_, v_inst_3388_, v_inst_3389_, v_inst_3390_, v_inst_3391_, v_inst_3392_, v_n_u2080_3393_, v_filter_3394_, v___x_3395_, v___x_3399_);
return v___x_3400_;
}
else
{
lean_object* v___x_3401_; 
lean_dec(v___x_3395_);
lean_dec(v_filter_3394_);
lean_dec(v_n_u2080_3393_);
lean_dec(v_inst_3392_);
lean_dec_ref(v_inst_3391_);
lean_dec(v_inst_3390_);
lean_dec_ref(v_inst_3389_);
lean_dec_ref(v_inst_3388_);
lean_dec_ref(v_inst_3387_);
lean_dec(v_n_u2081_3386_);
v___x_3401_ = lean_apply_2(v_toPure_3396_, lean_box(0), v_____do__lift_3397_);
return v___x_3401_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg(lean_object* v_inst_3402_, lean_object* v_inst_3403_, lean_object* v_inst_3404_, lean_object* v_inst_3405_, lean_object* v_inst_3406_, lean_object* v_inst_3407_, lean_object* v_n_u2080_3408_, uint8_t v_fullNames_3409_, uint8_t v_allowHorizAliases_3410_, lean_object* v_filter_3411_){
_start:
{
lean_object* v_view_3412_; lean_object* v_name_3413_; lean_object* v_n_u2081_3414_; lean_object* v___x_3415_; 
lean_inc(v_n_u2080_3408_);
v_view_3412_ = l_Lean_extractMacroScopes(v_n_u2080_3408_);
v_name_3413_ = lean_ctor_get(v_view_3412_, 0);
lean_inc(v_name_3413_);
v_n_u2081_3414_ = l_Lean_privateToUserName(v_name_3413_);
lean_inc_ref(v_inst_3402_);
v___x_3415_ = l_OptionT_instAlternative___redArg(v_inst_3402_);
if (v_fullNames_3409_ == 0)
{
lean_object* v_toApplicative_3416_; lean_object* v_getEnv_3417_; lean_object* v_toBind_3418_; lean_object* v_toPure_3419_; lean_object* v___f_3420_; lean_object* v___f_3421_; lean_object* v___x_3422_; lean_object* v___f_3423_; lean_object* v___f_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; 
v_toApplicative_3416_ = lean_ctor_get(v_inst_3402_, 0);
v_getEnv_3417_ = lean_ctor_get(v_inst_3404_, 0);
lean_inc(v_getEnv_3417_);
v_toBind_3418_ = lean_ctor_get(v_inst_3402_, 1);
lean_inc_n(v_toBind_3418_, 3);
v_toPure_3419_ = lean_ctor_get(v_toApplicative_3416_, 1);
lean_inc_n(v_toPure_3419_, 3);
lean_inc(v_n_u2081_3414_);
v___f_3420_ = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal_x3f___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3420_, 0, v_n_u2081_3414_);
lean_inc(v_filter_3411_);
lean_inc(v_n_u2080_3408_);
lean_inc(v_inst_3407_);
lean_inc_ref(v_inst_3406_);
lean_inc(v_inst_3405_);
lean_inc_ref(v_inst_3404_);
lean_inc_ref(v_inst_3403_);
lean_inc_ref(v_inst_3402_);
v___f_3421_ = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal_x3f___redArg___lam__1), 12, 11);
lean_closure_set(v___f_3421_, 0, v_view_3412_);
lean_closure_set(v___f_3421_, 1, v_n_u2081_3414_);
lean_closure_set(v___f_3421_, 2, v_inst_3402_);
lean_closure_set(v___f_3421_, 3, v_inst_3403_);
lean_closure_set(v___f_3421_, 4, v_inst_3404_);
lean_closure_set(v___f_3421_, 5, v_inst_3405_);
lean_closure_set(v___f_3421_, 6, v_inst_3406_);
lean_closure_set(v___f_3421_, 7, v_inst_3407_);
lean_closure_set(v___f_3421_, 8, v_n_u2080_3408_);
lean_closure_set(v___f_3421_, 9, v_filter_3411_);
lean_closure_set(v___f_3421_, 10, v_toPure_3419_);
v___x_3422_ = lean_box(v_allowHorizAliases_3410_);
v___f_3423_ = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal_x3f___redArg___lam__2___boxed), 15, 14);
lean_closure_set(v___f_3423_, 0, v_toPure_3419_);
lean_closure_set(v___f_3423_, 1, v_inst_3402_);
lean_closure_set(v___f_3423_, 2, v_inst_3403_);
lean_closure_set(v___f_3423_, 3, v_inst_3404_);
lean_closure_set(v___f_3423_, 4, v_inst_3405_);
lean_closure_set(v___f_3423_, 5, v_inst_3406_);
lean_closure_set(v___f_3423_, 6, v_inst_3407_);
lean_closure_set(v___f_3423_, 7, v_n_u2080_3408_);
lean_closure_set(v___f_3423_, 8, v_filter_3411_);
lean_closure_set(v___f_3423_, 9, v___x_3415_);
lean_closure_set(v___f_3423_, 10, v_toBind_3418_);
lean_closure_set(v___f_3423_, 11, v___f_3421_);
lean_closure_set(v___f_3423_, 12, v___x_3422_);
lean_closure_set(v___f_3423_, 13, v___f_3420_);
v___f_3424_ = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal_x3f___redArg___lam__3), 2, 1);
lean_closure_set(v___f_3424_, 0, v_toPure_3419_);
v___x_3425_ = lean_apply_4(v_toBind_3418_, lean_box(0), lean_box(0), v_getEnv_3417_, v___f_3424_);
v___x_3426_ = lean_apply_4(v_toBind_3418_, lean_box(0), lean_box(0), v___x_3425_, v___f_3423_);
return v___x_3426_;
}
else
{
lean_object* v_toApplicative_3427_; lean_object* v_toBind_3428_; lean_object* v_toPure_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___f_3432_; lean_object* v___x_3433_; 
lean_dec_ref(v___x_3415_);
v_toApplicative_3427_ = lean_ctor_get(v_inst_3402_, 0);
v_toBind_3428_ = lean_ctor_get(v_inst_3402_, 1);
lean_inc(v_toBind_3428_);
v_toPure_3429_ = lean_ctor_get(v_toApplicative_3427_, 1);
lean_inc(v_toPure_3429_);
v___x_3430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3430_, 0, v_view_3412_);
lean_inc(v_n_u2081_3414_);
lean_inc_ref(v___x_3430_);
lean_inc(v_filter_3411_);
lean_inc(v_n_u2080_3408_);
lean_inc(v_inst_3407_);
lean_inc_ref(v_inst_3406_);
lean_inc(v_inst_3405_);
lean_inc_ref(v_inst_3404_);
lean_inc_ref(v_inst_3403_);
lean_inc_ref(v_inst_3402_);
v___x_3431_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg(v_inst_3402_, v_inst_3403_, v_inst_3404_, v_inst_3405_, v_inst_3406_, v_inst_3407_, v_n_u2080_3408_, v_filter_3411_, v___x_3430_, v_n_u2081_3414_);
v___f_3432_ = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal_x3f___redArg___lam__4), 12, 11);
lean_closure_set(v___f_3432_, 0, v_n_u2081_3414_);
lean_closure_set(v___f_3432_, 1, v_inst_3402_);
lean_closure_set(v___f_3432_, 2, v_inst_3403_);
lean_closure_set(v___f_3432_, 3, v_inst_3404_);
lean_closure_set(v___f_3432_, 4, v_inst_3405_);
lean_closure_set(v___f_3432_, 5, v_inst_3406_);
lean_closure_set(v___f_3432_, 6, v_inst_3407_);
lean_closure_set(v___f_3432_, 7, v_n_u2080_3408_);
lean_closure_set(v___f_3432_, 8, v_filter_3411_);
lean_closure_set(v___f_3432_, 9, v___x_3430_);
lean_closure_set(v___f_3432_, 10, v_toPure_3429_);
v___x_3433_ = lean_apply_4(v_toBind_3428_, lean_box(0), lean_box(0), v___x_3431_, v___f_3432_);
return v___x_3433_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___boxed(lean_object* v_inst_3434_, lean_object* v_inst_3435_, lean_object* v_inst_3436_, lean_object* v_inst_3437_, lean_object* v_inst_3438_, lean_object* v_inst_3439_, lean_object* v_n_u2080_3440_, lean_object* v_fullNames_3441_, lean_object* v_allowHorizAliases_3442_, lean_object* v_filter_3443_){
_start:
{
uint8_t v_fullNames_boxed_3444_; uint8_t v_allowHorizAliases_boxed_3445_; lean_object* v_res_3446_; 
v_fullNames_boxed_3444_ = lean_unbox(v_fullNames_3441_);
v_allowHorizAliases_boxed_3445_ = lean_unbox(v_allowHorizAliases_3442_);
v_res_3446_ = l_Lean_unresolveNameGlobal_x3f___redArg(v_inst_3434_, v_inst_3435_, v_inst_3436_, v_inst_3437_, v_inst_3438_, v_inst_3439_, v_n_u2080_3440_, v_fullNames_boxed_3444_, v_allowHorizAliases_boxed_3445_, v_filter_3443_);
return v_res_3446_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f(lean_object* v_m_3447_, lean_object* v_inst_3448_, lean_object* v_inst_3449_, lean_object* v_inst_3450_, lean_object* v_inst_3451_, lean_object* v_inst_3452_, lean_object* v_inst_3453_, lean_object* v_n_u2080_3454_, uint8_t v_fullNames_3455_, uint8_t v_allowHorizAliases_3456_, lean_object* v_filter_3457_){
_start:
{
lean_object* v___x_3458_; 
v___x_3458_ = l_Lean_unresolveNameGlobal_x3f___redArg(v_inst_3448_, v_inst_3449_, v_inst_3450_, v_inst_3451_, v_inst_3452_, v_inst_3453_, v_n_u2080_3454_, v_fullNames_3455_, v_allowHorizAliases_3456_, v_filter_3457_);
return v___x_3458_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___boxed(lean_object* v_m_3459_, lean_object* v_inst_3460_, lean_object* v_inst_3461_, lean_object* v_inst_3462_, lean_object* v_inst_3463_, lean_object* v_inst_3464_, lean_object* v_inst_3465_, lean_object* v_n_u2080_3466_, lean_object* v_fullNames_3467_, lean_object* v_allowHorizAliases_3468_, lean_object* v_filter_3469_){
_start:
{
uint8_t v_fullNames_boxed_3470_; uint8_t v_allowHorizAliases_boxed_3471_; lean_object* v_res_3472_; 
v_fullNames_boxed_3470_ = lean_unbox(v_fullNames_3467_);
v_allowHorizAliases_boxed_3471_ = lean_unbox(v_allowHorizAliases_3468_);
v_res_3472_ = l_Lean_unresolveNameGlobal_x3f(v_m_3459_, v_inst_3460_, v_inst_3461_, v_inst_3462_, v_inst_3463_, v_inst_3464_, v_inst_3465_, v_n_u2080_3466_, v_fullNames_boxed_3470_, v_allowHorizAliases_boxed_3471_, v_filter_3469_);
return v_res_3472_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___redArg___lam__0(lean_object* v_toPure_3473_, lean_object* v_n_u2080_3474_, lean_object* v_n_x3f_3475_){
_start:
{
if (lean_obj_tag(v_n_x3f_3475_) == 0)
{
lean_object* v___x_3476_; 
v___x_3476_ = lean_apply_2(v_toPure_3473_, lean_box(0), v_n_u2080_3474_);
return v___x_3476_;
}
else
{
lean_object* v_val_3477_; lean_object* v___x_3478_; 
lean_dec(v_n_u2080_3474_);
v_val_3477_ = lean_ctor_get(v_n_x3f_3475_, 0);
lean_inc(v_val_3477_);
lean_dec_ref_known(v_n_x3f_3475_, 1);
v___x_3478_ = lean_apply_2(v_toPure_3473_, lean_box(0), v_val_3477_);
return v___x_3478_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___redArg(lean_object* v_inst_3479_, lean_object* v_inst_3480_, lean_object* v_inst_3481_, lean_object* v_inst_3482_, lean_object* v_inst_3483_, lean_object* v_inst_3484_, lean_object* v_n_u2080_3485_, uint8_t v_fullNames_3486_, uint8_t v_allowHorizAliases_3487_, lean_object* v_filter_3488_){
_start:
{
lean_object* v_toApplicative_3489_; lean_object* v_toBind_3490_; lean_object* v_toPure_3491_; lean_object* v___x_3492_; lean_object* v___f_3493_; lean_object* v___x_3494_; 
v_toApplicative_3489_ = lean_ctor_get(v_inst_3479_, 0);
v_toBind_3490_ = lean_ctor_get(v_inst_3479_, 1);
lean_inc(v_toBind_3490_);
v_toPure_3491_ = lean_ctor_get(v_toApplicative_3489_, 1);
lean_inc(v_toPure_3491_);
lean_inc(v_n_u2080_3485_);
v___x_3492_ = l_Lean_unresolveNameGlobal_x3f___redArg(v_inst_3479_, v_inst_3480_, v_inst_3481_, v_inst_3482_, v_inst_3483_, v_inst_3484_, v_n_u2080_3485_, v_fullNames_3486_, v_allowHorizAliases_3487_, v_filter_3488_);
v___f_3493_ = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3493_, 0, v_toPure_3491_);
lean_closure_set(v___f_3493_, 1, v_n_u2080_3485_);
v___x_3494_ = lean_apply_4(v_toBind_3490_, lean_box(0), lean_box(0), v___x_3492_, v___f_3493_);
return v___x_3494_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___redArg___boxed(lean_object* v_inst_3495_, lean_object* v_inst_3496_, lean_object* v_inst_3497_, lean_object* v_inst_3498_, lean_object* v_inst_3499_, lean_object* v_inst_3500_, lean_object* v_n_u2080_3501_, lean_object* v_fullNames_3502_, lean_object* v_allowHorizAliases_3503_, lean_object* v_filter_3504_){
_start:
{
uint8_t v_fullNames_boxed_3505_; uint8_t v_allowHorizAliases_boxed_3506_; lean_object* v_res_3507_; 
v_fullNames_boxed_3505_ = lean_unbox(v_fullNames_3502_);
v_allowHorizAliases_boxed_3506_ = lean_unbox(v_allowHorizAliases_3503_);
v_res_3507_ = l_Lean_unresolveNameGlobal___redArg(v_inst_3495_, v_inst_3496_, v_inst_3497_, v_inst_3498_, v_inst_3499_, v_inst_3500_, v_n_u2080_3501_, v_fullNames_boxed_3505_, v_allowHorizAliases_boxed_3506_, v_filter_3504_);
return v_res_3507_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal(lean_object* v_m_3508_, lean_object* v_inst_3509_, lean_object* v_inst_3510_, lean_object* v_inst_3511_, lean_object* v_inst_3512_, lean_object* v_inst_3513_, lean_object* v_inst_3514_, lean_object* v_n_u2080_3515_, uint8_t v_fullNames_3516_, uint8_t v_allowHorizAliases_3517_, lean_object* v_filter_3518_){
_start:
{
lean_object* v___x_3519_; 
v___x_3519_ = l_Lean_unresolveNameGlobal___redArg(v_inst_3509_, v_inst_3510_, v_inst_3511_, v_inst_3512_, v_inst_3513_, v_inst_3514_, v_n_u2080_3515_, v_fullNames_3516_, v_allowHorizAliases_3517_, v_filter_3518_);
return v___x_3519_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___boxed(lean_object* v_m_3520_, lean_object* v_inst_3521_, lean_object* v_inst_3522_, lean_object* v_inst_3523_, lean_object* v_inst_3524_, lean_object* v_inst_3525_, lean_object* v_inst_3526_, lean_object* v_n_u2080_3527_, lean_object* v_fullNames_3528_, lean_object* v_allowHorizAliases_3529_, lean_object* v_filter_3530_){
_start:
{
uint8_t v_fullNames_boxed_3531_; uint8_t v_allowHorizAliases_boxed_3532_; lean_object* v_res_3533_; 
v_fullNames_boxed_3531_ = lean_unbox(v_fullNames_3528_);
v_allowHorizAliases_boxed_3532_ = lean_unbox(v_allowHorizAliases_3529_);
v_res_3533_ = l_Lean_unresolveNameGlobal(v_m_3520_, v_inst_3521_, v_inst_3522_, v_inst_3523_, v_inst_3524_, v_inst_3525_, v_inst_3526_, v_n_u2080_3527_, v_fullNames_boxed_3531_, v_allowHorizAliases_boxed_3532_, v_filter_3530_);
return v_res_3533_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg___lam__0(lean_object* v_toFunctor_3535_, lean_object* v_inst_3536_, lean_object* v_inst_3537_, lean_object* v_inst_3538_, lean_object* v_inst_3539_, lean_object* v_inst_3540_, lean_object* v_inst_3541_, lean_object* v_inst_3542_, lean_object* v_n_3543_){
_start:
{
lean_object* v_map_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; 
v_map_3544_ = lean_ctor_get(v_toFunctor_3535_, 0);
lean_inc(v_map_3544_);
lean_dec_ref(v_toFunctor_3535_);
v___x_3545_ = ((lean_object*)(l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg___lam__0___closed__0));
v___x_3546_ = l_Lean_resolveLocalName___redArg(v_inst_3536_, v_inst_3537_, v_inst_3538_, v_inst_3539_, v_inst_3540_, v_inst_3541_, v_inst_3542_, v_n_3543_);
v___x_3547_ = lean_apply_4(v_map_3544_, lean_box(0), lean_box(0), v___x_3545_, v___x_3546_);
return v___x_3547_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg(lean_object* v_inst_3548_, lean_object* v_inst_3549_, lean_object* v_inst_3550_, lean_object* v_inst_3551_, lean_object* v_inst_3552_, lean_object* v_inst_3553_, lean_object* v_inst_3554_, lean_object* v_n_u2080_3555_, uint8_t v_fullNames_3556_){
_start:
{
lean_object* v_toApplicative_3557_; lean_object* v_toFunctor_3558_; uint8_t v___x_3559_; lean_object* v___f_3560_; lean_object* v___x_3561_; 
v_toApplicative_3557_ = lean_ctor_get(v_inst_3548_, 0);
v_toFunctor_3558_ = lean_ctor_get(v_toApplicative_3557_, 0);
v___x_3559_ = 0;
lean_inc(v_inst_3553_);
lean_inc_ref(v_inst_3552_);
lean_inc(v_inst_3551_);
lean_inc_ref(v_inst_3550_);
lean_inc_ref(v_inst_3549_);
lean_inc_ref(v_inst_3548_);
lean_inc_ref(v_toFunctor_3558_);
v___f_3560_ = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg___lam__0), 9, 8);
lean_closure_set(v___f_3560_, 0, v_toFunctor_3558_);
lean_closure_set(v___f_3560_, 1, v_inst_3548_);
lean_closure_set(v___f_3560_, 2, v_inst_3549_);
lean_closure_set(v___f_3560_, 3, v_inst_3550_);
lean_closure_set(v___f_3560_, 4, v_inst_3551_);
lean_closure_set(v___f_3560_, 5, v_inst_3552_);
lean_closure_set(v___f_3560_, 6, v_inst_3553_);
lean_closure_set(v___f_3560_, 7, v_inst_3554_);
v___x_3561_ = l_Lean_unresolveNameGlobal_x3f___redArg(v_inst_3548_, v_inst_3549_, v_inst_3550_, v_inst_3551_, v_inst_3552_, v_inst_3553_, v_n_u2080_3555_, v_fullNames_3556_, v___x_3559_, v___f_3560_);
return v___x_3561_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg___boxed(lean_object* v_inst_3562_, lean_object* v_inst_3563_, lean_object* v_inst_3564_, lean_object* v_inst_3565_, lean_object* v_inst_3566_, lean_object* v_inst_3567_, lean_object* v_inst_3568_, lean_object* v_n_u2080_3569_, lean_object* v_fullNames_3570_){
_start:
{
uint8_t v_fullNames_boxed_3571_; lean_object* v_res_3572_; 
v_fullNames_boxed_3571_ = lean_unbox(v_fullNames_3570_);
v_res_3572_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg(v_inst_3562_, v_inst_3563_, v_inst_3564_, v_inst_3565_, v_inst_3566_, v_inst_3567_, v_inst_3568_, v_n_u2080_3569_, v_fullNames_boxed_3571_);
return v_res_3572_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f(lean_object* v_m_3573_, lean_object* v_inst_3574_, lean_object* v_inst_3575_, lean_object* v_inst_3576_, lean_object* v_inst_3577_, lean_object* v_inst_3578_, lean_object* v_inst_3579_, lean_object* v_inst_3580_, lean_object* v_n_u2080_3581_, uint8_t v_fullNames_3582_){
_start:
{
lean_object* v___x_3583_; 
v___x_3583_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg(v_inst_3574_, v_inst_3575_, v_inst_3576_, v_inst_3577_, v_inst_3578_, v_inst_3579_, v_inst_3580_, v_n_u2080_3581_, v_fullNames_3582_);
return v___x_3583_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___boxed(lean_object* v_m_3584_, lean_object* v_inst_3585_, lean_object* v_inst_3586_, lean_object* v_inst_3587_, lean_object* v_inst_3588_, lean_object* v_inst_3589_, lean_object* v_inst_3590_, lean_object* v_inst_3591_, lean_object* v_n_u2080_3592_, lean_object* v_fullNames_3593_){
_start:
{
uint8_t v_fullNames_boxed_3594_; lean_object* v_res_3595_; 
v_fullNames_boxed_3594_ = lean_unbox(v_fullNames_3593_);
v_res_3595_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f(v_m_3584_, v_inst_3585_, v_inst_3586_, v_inst_3587_, v_inst_3588_, v_inst_3589_, v_inst_3590_, v_inst_3591_, v_n_u2080_3592_, v_fullNames_boxed_3594_);
return v_res_3595_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals___redArg(lean_object* v_inst_3596_, lean_object* v_inst_3597_, lean_object* v_inst_3598_, lean_object* v_inst_3599_, lean_object* v_inst_3600_, lean_object* v_inst_3601_, lean_object* v_inst_3602_, lean_object* v_n_u2080_3603_, uint8_t v_fullNames_3604_){
_start:
{
lean_object* v_toApplicative_3605_; lean_object* v_toBind_3606_; lean_object* v_toPure_3607_; lean_object* v___x_3608_; lean_object* v___f_3609_; lean_object* v___x_3610_; 
v_toApplicative_3605_ = lean_ctor_get(v_inst_3596_, 0);
v_toBind_3606_ = lean_ctor_get(v_inst_3596_, 1);
lean_inc(v_toBind_3606_);
v_toPure_3607_ = lean_ctor_get(v_toApplicative_3605_, 1);
lean_inc(v_toPure_3607_);
lean_inc(v_n_u2080_3603_);
v___x_3608_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg(v_inst_3596_, v_inst_3597_, v_inst_3598_, v_inst_3599_, v_inst_3600_, v_inst_3601_, v_inst_3602_, v_n_u2080_3603_, v_fullNames_3604_);
v___f_3609_ = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3609_, 0, v_toPure_3607_);
lean_closure_set(v___f_3609_, 1, v_n_u2080_3603_);
v___x_3610_ = lean_apply_4(v_toBind_3606_, lean_box(0), lean_box(0), v___x_3608_, v___f_3609_);
return v___x_3610_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals___redArg___boxed(lean_object* v_inst_3611_, lean_object* v_inst_3612_, lean_object* v_inst_3613_, lean_object* v_inst_3614_, lean_object* v_inst_3615_, lean_object* v_inst_3616_, lean_object* v_inst_3617_, lean_object* v_n_u2080_3618_, lean_object* v_fullNames_3619_){
_start:
{
uint8_t v_fullNames_boxed_3620_; lean_object* v_res_3621_; 
v_fullNames_boxed_3620_ = lean_unbox(v_fullNames_3619_);
v_res_3621_ = l_Lean_unresolveNameGlobalAvoidingLocals___redArg(v_inst_3611_, v_inst_3612_, v_inst_3613_, v_inst_3614_, v_inst_3615_, v_inst_3616_, v_inst_3617_, v_n_u2080_3618_, v_fullNames_boxed_3620_);
return v_res_3621_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals(lean_object* v_m_3622_, lean_object* v_inst_3623_, lean_object* v_inst_3624_, lean_object* v_inst_3625_, lean_object* v_inst_3626_, lean_object* v_inst_3627_, lean_object* v_inst_3628_, lean_object* v_inst_3629_, lean_object* v_n_u2080_3630_, uint8_t v_fullNames_3631_){
_start:
{
lean_object* v___x_3632_; 
v___x_3632_ = l_Lean_unresolveNameGlobalAvoidingLocals___redArg(v_inst_3623_, v_inst_3624_, v_inst_3625_, v_inst_3626_, v_inst_3627_, v_inst_3628_, v_inst_3629_, v_n_u2080_3630_, v_fullNames_3631_);
return v___x_3632_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals___boxed(lean_object* v_m_3633_, lean_object* v_inst_3634_, lean_object* v_inst_3635_, lean_object* v_inst_3636_, lean_object* v_inst_3637_, lean_object* v_inst_3638_, lean_object* v_inst_3639_, lean_object* v_inst_3640_, lean_object* v_n_u2080_3641_, lean_object* v_fullNames_3642_){
_start:
{
uint8_t v_fullNames_boxed_3643_; lean_object* v_res_3644_; 
v_fullNames_boxed_3643_ = lean_unbox(v_fullNames_3642_);
v_res_3644_ = l_Lean_unresolveNameGlobalAvoidingLocals(v_m_3633_, v_inst_3634_, v_inst_3635_, v_inst_3636_, v_inst_3637_, v_inst_3638_, v_inst_3639_, v_inst_3640_, v_n_u2080_3641_, v_fullNames_boxed_3643_);
return v_res_3644_;
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
