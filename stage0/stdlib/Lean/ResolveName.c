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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
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
v___x_81_ = lean_st_ref_set(v___x_78_, v___x_80_);
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
v_newNode_237_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__9___redArg(v___x_236_, v_x_182_, v_x_183_);
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
v___x_243_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg___closed__0);
v___x_244_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg(v_x_181_, v_ks_240_, v_vs_241_, v___x_242_, v___x_243_);
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
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg(size_t v_depth_252_, lean_object* v_keys_253_, lean_object* v_vals_254_, lean_object* v_i_255_, lean_object* v_entries_256_){
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
v___x_271_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg(v_entries_256_, v_h_269_, v_depth_252_, v_k_259_, v_v_260_);
v_i_255_ = v___x_270_;
v_entries_256_ = v___x_271_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg___boxed(lean_object* v_depth_275_, lean_object* v_keys_276_, lean_object* v_vals_277_, lean_object* v_i_278_, lean_object* v_entries_279_){
_start:
{
size_t v_depth_boxed_280_; lean_object* v_res_281_; 
v_depth_boxed_280_ = lean_unbox_usize(v_depth_275_);
lean_dec(v_depth_275_);
v_res_281_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg(v_depth_boxed_280_, v_keys_276_, v_vals_277_, v_i_278_, v_entries_279_);
lean_dec_ref(v_vals_277_);
lean_dec_ref(v_keys_276_);
return v_res_281_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg___boxed(lean_object* v_x_282_, lean_object* v_x_283_, lean_object* v_x_284_, lean_object* v_x_285_, lean_object* v_x_286_){
_start:
{
size_t v_x_1084__boxed_287_; size_t v_x_1085__boxed_288_; lean_object* v_res_289_; 
v_x_1084__boxed_287_ = lean_unbox_usize(v_x_283_);
lean_dec(v_x_283_);
v_x_1085__boxed_288_ = lean_unbox_usize(v_x_284_);
lean_dec(v_x_284_);
v_res_289_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg(v_x_282_, v_x_1084__boxed_287_, v_x_1085__boxed_288_, v_x_285_, v_x_286_);
return v_res_289_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3___redArg(lean_object* v_x_290_, lean_object* v_x_291_, lean_object* v_x_292_){
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
v___x_297_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg(v_x_290_, v___x_295_, v___x_296_, v_x_291_, v_x_292_);
return v___x_297_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9_spec__14_spec__16___redArg(lean_object* v_x_300_, lean_object* v_x_301_){
_start:
{
if (lean_obj_tag(v_x_301_) == 0)
{
return v_x_300_;
}
else
{
lean_object* v_key_302_; lean_object* v_value_303_; lean_object* v_tail_304_; lean_object* v___x_306_; uint8_t v_isShared_307_; uint8_t v_isSharedCheck_330_; 
v_key_302_ = lean_ctor_get(v_x_301_, 0);
v_value_303_ = lean_ctor_get(v_x_301_, 1);
v_tail_304_ = lean_ctor_get(v_x_301_, 2);
v_isSharedCheck_330_ = !lean_is_exclusive(v_x_301_);
if (v_isSharedCheck_330_ == 0)
{
v___x_306_ = v_x_301_;
v_isShared_307_ = v_isSharedCheck_330_;
goto v_resetjp_305_;
}
else
{
lean_inc(v_tail_304_);
lean_inc(v_value_303_);
lean_inc(v_key_302_);
lean_dec(v_x_301_);
v___x_306_ = lean_box(0);
v_isShared_307_ = v_isSharedCheck_330_;
goto v_resetjp_305_;
}
v_resetjp_305_:
{
lean_object* v___x_308_; uint64_t v___y_310_; 
v___x_308_ = lean_array_get_size(v_x_300_);
if (lean_obj_tag(v_key_302_) == 0)
{
uint64_t v___x_328_; 
v___x_328_ = 1723ULL;
v___y_310_ = v___x_328_;
goto v___jp_309_;
}
else
{
uint64_t v_hash_329_; 
v_hash_329_ = lean_ctor_get_uint64(v_key_302_, sizeof(void*)*2);
v___y_310_ = v_hash_329_;
goto v___jp_309_;
}
v___jp_309_:
{
uint64_t v___x_311_; uint64_t v___x_312_; uint64_t v_fold_313_; uint64_t v___x_314_; uint64_t v___x_315_; uint64_t v___x_316_; size_t v___x_317_; size_t v___x_318_; size_t v___x_319_; size_t v___x_320_; size_t v___x_321_; lean_object* v___x_322_; lean_object* v___x_324_; 
v___x_311_ = 32ULL;
v___x_312_ = lean_uint64_shift_right(v___y_310_, v___x_311_);
v_fold_313_ = lean_uint64_xor(v___y_310_, v___x_312_);
v___x_314_ = 16ULL;
v___x_315_ = lean_uint64_shift_right(v_fold_313_, v___x_314_);
v___x_316_ = lean_uint64_xor(v_fold_313_, v___x_315_);
v___x_317_ = lean_uint64_to_usize(v___x_316_);
v___x_318_ = lean_usize_of_nat(v___x_308_);
v___x_319_ = ((size_t)1ULL);
v___x_320_ = lean_usize_sub(v___x_318_, v___x_319_);
v___x_321_ = lean_usize_land(v___x_317_, v___x_320_);
v___x_322_ = lean_array_uget_borrowed(v_x_300_, v___x_321_);
lean_inc(v___x_322_);
if (v_isShared_307_ == 0)
{
lean_ctor_set(v___x_306_, 2, v___x_322_);
v___x_324_ = v___x_306_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v_key_302_);
lean_ctor_set(v_reuseFailAlloc_327_, 1, v_value_303_);
lean_ctor_set(v_reuseFailAlloc_327_, 2, v___x_322_);
v___x_324_ = v_reuseFailAlloc_327_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
lean_object* v___x_325_; 
v___x_325_ = lean_array_uset(v_x_300_, v___x_321_, v___x_324_);
v_x_300_ = v___x_325_;
v_x_301_ = v_tail_304_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9_spec__14___redArg(lean_object* v_i_331_, lean_object* v_source_332_, lean_object* v_target_333_){
_start:
{
lean_object* v___x_334_; uint8_t v___x_335_; 
v___x_334_ = lean_array_get_size(v_source_332_);
v___x_335_ = lean_nat_dec_lt(v_i_331_, v___x_334_);
if (v___x_335_ == 0)
{
lean_dec_ref(v_source_332_);
lean_dec(v_i_331_);
return v_target_333_;
}
else
{
lean_object* v_es_336_; lean_object* v___x_337_; lean_object* v_source_338_; lean_object* v_target_339_; lean_object* v___x_340_; lean_object* v___x_341_; 
v_es_336_ = lean_array_fget(v_source_332_, v_i_331_);
v___x_337_ = lean_box(0);
v_source_338_ = lean_array_fset(v_source_332_, v_i_331_, v___x_337_);
v_target_339_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9_spec__14_spec__16___redArg(v_target_333_, v_es_336_);
v___x_340_ = lean_unsigned_to_nat(1u);
v___x_341_ = lean_nat_add(v_i_331_, v___x_340_);
lean_dec(v_i_331_);
v_i_331_ = v___x_341_;
v_source_332_ = v_source_338_;
v_target_333_ = v_target_339_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9___redArg(lean_object* v_data_343_){
_start:
{
lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v_nbuckets_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_344_ = lean_array_get_size(v_data_343_);
v___x_345_ = lean_unsigned_to_nat(2u);
v_nbuckets_346_ = lean_nat_mul(v___x_344_, v___x_345_);
v___x_347_ = lean_unsigned_to_nat(0u);
v___x_348_ = lean_box(0);
v___x_349_ = lean_mk_array(v_nbuckets_346_, v___x_348_);
v___x_350_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9_spec__14___redArg(v___x_347_, v_data_343_, v___x_349_);
return v___x_350_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8___redArg(lean_object* v_a_351_, lean_object* v_x_352_){
_start:
{
if (lean_obj_tag(v_x_352_) == 0)
{
uint8_t v___x_353_; 
v___x_353_ = 0;
return v___x_353_;
}
else
{
lean_object* v_key_354_; lean_object* v_tail_355_; uint8_t v___x_356_; 
v_key_354_ = lean_ctor_get(v_x_352_, 0);
v_tail_355_ = lean_ctor_get(v_x_352_, 2);
v___x_356_ = lean_name_eq(v_key_354_, v_a_351_);
if (v___x_356_ == 0)
{
v_x_352_ = v_tail_355_;
goto _start;
}
else
{
return v___x_356_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8___redArg___boxed(lean_object* v_a_358_, lean_object* v_x_359_){
_start:
{
uint8_t v_res_360_; lean_object* v_r_361_; 
v_res_360_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8___redArg(v_a_358_, v_x_359_);
lean_dec(v_x_359_);
lean_dec(v_a_358_);
v_r_361_ = lean_box(v_res_360_);
return v_r_361_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__10___redArg(lean_object* v_a_362_, lean_object* v_b_363_, lean_object* v_x_364_){
_start:
{
if (lean_obj_tag(v_x_364_) == 0)
{
lean_dec(v_b_363_);
lean_dec(v_a_362_);
return v_x_364_;
}
else
{
lean_object* v_key_365_; lean_object* v_value_366_; lean_object* v_tail_367_; lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_379_; 
v_key_365_ = lean_ctor_get(v_x_364_, 0);
v_value_366_ = lean_ctor_get(v_x_364_, 1);
v_tail_367_ = lean_ctor_get(v_x_364_, 2);
v_isSharedCheck_379_ = !lean_is_exclusive(v_x_364_);
if (v_isSharedCheck_379_ == 0)
{
v___x_369_ = v_x_364_;
v_isShared_370_ = v_isSharedCheck_379_;
goto v_resetjp_368_;
}
else
{
lean_inc(v_tail_367_);
lean_inc(v_value_366_);
lean_inc(v_key_365_);
lean_dec(v_x_364_);
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_379_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
uint8_t v___x_371_; 
v___x_371_ = lean_name_eq(v_key_365_, v_a_362_);
if (v___x_371_ == 0)
{
lean_object* v___x_372_; lean_object* v___x_374_; 
v___x_372_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__10___redArg(v_a_362_, v_b_363_, v_tail_367_);
if (v_isShared_370_ == 0)
{
lean_ctor_set(v___x_369_, 2, v___x_372_);
v___x_374_ = v___x_369_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v_key_365_);
lean_ctor_set(v_reuseFailAlloc_375_, 1, v_value_366_);
lean_ctor_set(v_reuseFailAlloc_375_, 2, v___x_372_);
v___x_374_ = v_reuseFailAlloc_375_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
return v___x_374_;
}
}
else
{
lean_object* v___x_377_; 
lean_dec(v_value_366_);
lean_dec(v_key_365_);
if (v_isShared_370_ == 0)
{
lean_ctor_set(v___x_369_, 1, v_b_363_);
lean_ctor_set(v___x_369_, 0, v_a_362_);
v___x_377_ = v___x_369_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v_a_362_);
lean_ctor_set(v_reuseFailAlloc_378_, 1, v_b_363_);
lean_ctor_set(v_reuseFailAlloc_378_, 2, v_tail_367_);
v___x_377_ = v_reuseFailAlloc_378_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
return v___x_377_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4___redArg(lean_object* v_m_380_, lean_object* v_a_381_, lean_object* v_b_382_){
_start:
{
lean_object* v_size_383_; lean_object* v_buckets_384_; lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_430_; 
v_size_383_ = lean_ctor_get(v_m_380_, 0);
v_buckets_384_ = lean_ctor_get(v_m_380_, 1);
v_isSharedCheck_430_ = !lean_is_exclusive(v_m_380_);
if (v_isSharedCheck_430_ == 0)
{
v___x_386_ = v_m_380_;
v_isShared_387_ = v_isSharedCheck_430_;
goto v_resetjp_385_;
}
else
{
lean_inc(v_buckets_384_);
lean_inc(v_size_383_);
lean_dec(v_m_380_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_430_;
goto v_resetjp_385_;
}
v_resetjp_385_:
{
lean_object* v___x_388_; uint64_t v___y_390_; 
v___x_388_ = lean_array_get_size(v_buckets_384_);
if (lean_obj_tag(v_a_381_) == 0)
{
uint64_t v___x_428_; 
v___x_428_ = 1723ULL;
v___y_390_ = v___x_428_;
goto v___jp_389_;
}
else
{
uint64_t v_hash_429_; 
v_hash_429_ = lean_ctor_get_uint64(v_a_381_, sizeof(void*)*2);
v___y_390_ = v_hash_429_;
goto v___jp_389_;
}
v___jp_389_:
{
uint64_t v___x_391_; uint64_t v___x_392_; uint64_t v_fold_393_; uint64_t v___x_394_; uint64_t v___x_395_; uint64_t v___x_396_; size_t v___x_397_; size_t v___x_398_; size_t v___x_399_; size_t v___x_400_; size_t v___x_401_; lean_object* v_bkt_402_; uint8_t v___x_403_; 
v___x_391_ = 32ULL;
v___x_392_ = lean_uint64_shift_right(v___y_390_, v___x_391_);
v_fold_393_ = lean_uint64_xor(v___y_390_, v___x_392_);
v___x_394_ = 16ULL;
v___x_395_ = lean_uint64_shift_right(v_fold_393_, v___x_394_);
v___x_396_ = lean_uint64_xor(v_fold_393_, v___x_395_);
v___x_397_ = lean_uint64_to_usize(v___x_396_);
v___x_398_ = lean_usize_of_nat(v___x_388_);
v___x_399_ = ((size_t)1ULL);
v___x_400_ = lean_usize_sub(v___x_398_, v___x_399_);
v___x_401_ = lean_usize_land(v___x_397_, v___x_400_);
v_bkt_402_ = lean_array_uget_borrowed(v_buckets_384_, v___x_401_);
v___x_403_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8___redArg(v_a_381_, v_bkt_402_);
if (v___x_403_ == 0)
{
lean_object* v___x_404_; lean_object* v_size_x27_405_; lean_object* v___x_406_; lean_object* v_buckets_x27_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; uint8_t v___x_413_; 
v___x_404_ = lean_unsigned_to_nat(1u);
v_size_x27_405_ = lean_nat_add(v_size_383_, v___x_404_);
lean_dec(v_size_383_);
lean_inc(v_bkt_402_);
v___x_406_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_406_, 0, v_a_381_);
lean_ctor_set(v___x_406_, 1, v_b_382_);
lean_ctor_set(v___x_406_, 2, v_bkt_402_);
v_buckets_x27_407_ = lean_array_uset(v_buckets_384_, v___x_401_, v___x_406_);
v___x_408_ = lean_unsigned_to_nat(4u);
v___x_409_ = lean_nat_mul(v_size_x27_405_, v___x_408_);
v___x_410_ = lean_unsigned_to_nat(3u);
v___x_411_ = lean_nat_div(v___x_409_, v___x_410_);
lean_dec(v___x_409_);
v___x_412_ = lean_array_get_size(v_buckets_x27_407_);
v___x_413_ = lean_nat_dec_le(v___x_411_, v___x_412_);
lean_dec(v___x_411_);
if (v___x_413_ == 0)
{
lean_object* v_val_414_; lean_object* v___x_416_; 
v_val_414_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9___redArg(v_buckets_x27_407_);
if (v_isShared_387_ == 0)
{
lean_ctor_set(v___x_386_, 1, v_val_414_);
lean_ctor_set(v___x_386_, 0, v_size_x27_405_);
v___x_416_ = v___x_386_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v_size_x27_405_);
lean_ctor_set(v_reuseFailAlloc_417_, 1, v_val_414_);
v___x_416_ = v_reuseFailAlloc_417_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
return v___x_416_;
}
}
else
{
lean_object* v___x_419_; 
if (v_isShared_387_ == 0)
{
lean_ctor_set(v___x_386_, 1, v_buckets_x27_407_);
lean_ctor_set(v___x_386_, 0, v_size_x27_405_);
v___x_419_ = v___x_386_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v_size_x27_405_);
lean_ctor_set(v_reuseFailAlloc_420_, 1, v_buckets_x27_407_);
v___x_419_ = v_reuseFailAlloc_420_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
return v___x_419_;
}
}
}
else
{
lean_object* v___x_421_; lean_object* v_buckets_x27_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_426_; 
lean_inc(v_bkt_402_);
v___x_421_ = lean_box(0);
v_buckets_x27_422_ = lean_array_uset(v_buckets_384_, v___x_401_, v___x_421_);
v___x_423_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__10___redArg(v_a_381_, v_b_382_, v_bkt_402_);
v___x_424_ = lean_array_uset(v_buckets_x27_422_, v___x_401_, v___x_423_);
if (v_isShared_387_ == 0)
{
lean_ctor_set(v___x_386_, 1, v___x_424_);
v___x_426_ = v___x_386_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_427_; 
v_reuseFailAlloc_427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_427_, 0, v_size_383_);
lean_ctor_set(v_reuseFailAlloc_427_, 1, v___x_424_);
v___x_426_ = v_reuseFailAlloc_427_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
return v___x_426_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1___redArg(lean_object* v_x_431_, lean_object* v_x_432_, lean_object* v_x_433_){
_start:
{
uint8_t v_stage_u2081_434_; 
v_stage_u2081_434_ = lean_ctor_get_uint8(v_x_431_, sizeof(void*)*2);
if (v_stage_u2081_434_ == 0)
{
lean_object* v_map_u2081_435_; lean_object* v_map_u2082_436_; lean_object* v___x_438_; uint8_t v_isShared_439_; uint8_t v_isSharedCheck_444_; 
v_map_u2081_435_ = lean_ctor_get(v_x_431_, 0);
v_map_u2082_436_ = lean_ctor_get(v_x_431_, 1);
v_isSharedCheck_444_ = !lean_is_exclusive(v_x_431_);
if (v_isSharedCheck_444_ == 0)
{
v___x_438_ = v_x_431_;
v_isShared_439_ = v_isSharedCheck_444_;
goto v_resetjp_437_;
}
else
{
lean_inc(v_map_u2082_436_);
lean_inc(v_map_u2081_435_);
lean_dec(v_x_431_);
v___x_438_ = lean_box(0);
v_isShared_439_ = v_isSharedCheck_444_;
goto v_resetjp_437_;
}
v_resetjp_437_:
{
lean_object* v___x_440_; lean_object* v___x_442_; 
v___x_440_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3___redArg(v_map_u2082_436_, v_x_432_, v_x_433_);
if (v_isShared_439_ == 0)
{
lean_ctor_set(v___x_438_, 1, v___x_440_);
v___x_442_ = v___x_438_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v_map_u2081_435_);
lean_ctor_set(v_reuseFailAlloc_443_, 1, v___x_440_);
lean_ctor_set_uint8(v_reuseFailAlloc_443_, sizeof(void*)*2, v_stage_u2081_434_);
v___x_442_ = v_reuseFailAlloc_443_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
return v___x_442_;
}
}
}
else
{
lean_object* v_map_u2081_445_; lean_object* v_map_u2082_446_; lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_454_; 
v_map_u2081_445_ = lean_ctor_get(v_x_431_, 0);
v_map_u2082_446_ = lean_ctor_get(v_x_431_, 1);
v_isSharedCheck_454_ = !lean_is_exclusive(v_x_431_);
if (v_isSharedCheck_454_ == 0)
{
v___x_448_ = v_x_431_;
v_isShared_449_ = v_isSharedCheck_454_;
goto v_resetjp_447_;
}
else
{
lean_inc(v_map_u2082_446_);
lean_inc(v_map_u2081_445_);
lean_dec(v_x_431_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_454_;
goto v_resetjp_447_;
}
v_resetjp_447_:
{
lean_object* v___x_450_; lean_object* v___x_452_; 
v___x_450_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4___redArg(v_map_u2081_445_, v_x_432_, v_x_433_);
if (v_isShared_449_ == 0)
{
lean_ctor_set(v___x_448_, 0, v___x_450_);
v___x_452_ = v___x_448_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v___x_450_);
lean_ctor_set(v_reuseFailAlloc_453_, 1, v_map_u2082_446_);
lean_ctor_set_uint8(v_reuseFailAlloc_453_, sizeof(void*)*2, v_stage_u2081_434_);
v___x_452_ = v_reuseFailAlloc_453_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
return v___x_452_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3___redArg(lean_object* v_a_455_, lean_object* v_x_456_){
_start:
{
if (lean_obj_tag(v_x_456_) == 0)
{
lean_object* v___x_457_; 
v___x_457_ = lean_box(0);
return v___x_457_;
}
else
{
lean_object* v_key_458_; lean_object* v_value_459_; lean_object* v_tail_460_; uint8_t v___x_461_; 
v_key_458_ = lean_ctor_get(v_x_456_, 0);
v_value_459_ = lean_ctor_get(v_x_456_, 1);
v_tail_460_ = lean_ctor_get(v_x_456_, 2);
v___x_461_ = lean_name_eq(v_key_458_, v_a_455_);
if (v___x_461_ == 0)
{
v_x_456_ = v_tail_460_;
goto _start;
}
else
{
lean_object* v___x_463_; 
lean_inc(v_value_459_);
v___x_463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_463_, 0, v_value_459_);
return v___x_463_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_a_464_, lean_object* v_x_465_){
_start:
{
lean_object* v_res_466_; 
v_res_466_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3___redArg(v_a_464_, v_x_465_);
lean_dec(v_x_465_);
lean_dec(v_a_464_);
return v_res_466_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1___redArg(lean_object* v_m_467_, lean_object* v_a_468_){
_start:
{
lean_object* v_buckets_469_; lean_object* v___x_470_; uint64_t v___y_472_; 
v_buckets_469_ = lean_ctor_get(v_m_467_, 1);
v___x_470_ = lean_array_get_size(v_buckets_469_);
if (lean_obj_tag(v_a_468_) == 0)
{
uint64_t v___x_486_; 
v___x_486_ = 1723ULL;
v___y_472_ = v___x_486_;
goto v___jp_471_;
}
else
{
uint64_t v_hash_487_; 
v_hash_487_ = lean_ctor_get_uint64(v_a_468_, sizeof(void*)*2);
v___y_472_ = v_hash_487_;
goto v___jp_471_;
}
v___jp_471_:
{
uint64_t v___x_473_; uint64_t v___x_474_; uint64_t v_fold_475_; uint64_t v___x_476_; uint64_t v___x_477_; uint64_t v___x_478_; size_t v___x_479_; size_t v___x_480_; size_t v___x_481_; size_t v___x_482_; size_t v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; 
v___x_473_ = 32ULL;
v___x_474_ = lean_uint64_shift_right(v___y_472_, v___x_473_);
v_fold_475_ = lean_uint64_xor(v___y_472_, v___x_474_);
v___x_476_ = 16ULL;
v___x_477_ = lean_uint64_shift_right(v_fold_475_, v___x_476_);
v___x_478_ = lean_uint64_xor(v_fold_475_, v___x_477_);
v___x_479_ = lean_uint64_to_usize(v___x_478_);
v___x_480_ = lean_usize_of_nat(v___x_470_);
v___x_481_ = ((size_t)1ULL);
v___x_482_ = lean_usize_sub(v___x_480_, v___x_481_);
v___x_483_ = lean_usize_land(v___x_479_, v___x_482_);
v___x_484_ = lean_array_uget_borrowed(v_buckets_469_, v___x_483_);
v___x_485_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3___redArg(v_a_468_, v___x_484_);
return v___x_485_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1___redArg___boxed(lean_object* v_m_488_, lean_object* v_a_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1___redArg(v_m_488_, v_a_489_);
lean_dec(v_a_489_);
lean_dec_ref(v_m_488_);
return v_res_490_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_keys_491_, lean_object* v_vals_492_, lean_object* v_i_493_, lean_object* v_k_494_){
_start:
{
lean_object* v___x_495_; uint8_t v___x_496_; 
v___x_495_ = lean_array_get_size(v_keys_491_);
v___x_496_ = lean_nat_dec_lt(v_i_493_, v___x_495_);
if (v___x_496_ == 0)
{
lean_object* v___x_497_; 
lean_dec(v_i_493_);
v___x_497_ = lean_box(0);
return v___x_497_;
}
else
{
lean_object* v_k_x27_498_; uint8_t v___x_499_; 
v_k_x27_498_ = lean_array_fget_borrowed(v_keys_491_, v_i_493_);
v___x_499_ = lean_name_eq(v_k_494_, v_k_x27_498_);
if (v___x_499_ == 0)
{
lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_500_ = lean_unsigned_to_nat(1u);
v___x_501_ = lean_nat_add(v_i_493_, v___x_500_);
lean_dec(v_i_493_);
v_i_493_ = v___x_501_;
goto _start;
}
else
{
lean_object* v___x_503_; lean_object* v___x_504_; 
v___x_503_ = lean_array_fget_borrowed(v_vals_492_, v_i_493_);
lean_dec(v_i_493_);
lean_inc(v___x_503_);
v___x_504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_504_, 0, v___x_503_);
return v___x_504_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_keys_505_, lean_object* v_vals_506_, lean_object* v_i_507_, lean_object* v_k_508_){
_start:
{
lean_object* v_res_509_; 
v_res_509_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4___redArg(v_keys_505_, v_vals_506_, v_i_507_, v_k_508_);
lean_dec(v_k_508_);
lean_dec_ref(v_vals_506_);
lean_dec_ref(v_keys_505_);
return v_res_509_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1___redArg(lean_object* v_x_510_, size_t v_x_511_, lean_object* v_x_512_){
_start:
{
if (lean_obj_tag(v_x_510_) == 0)
{
lean_object* v_es_513_; lean_object* v___x_514_; size_t v___x_515_; size_t v___x_516_; lean_object* v_j_517_; lean_object* v___x_518_; 
v_es_513_ = lean_ctor_get(v_x_510_, 0);
v___x_514_ = lean_box(2);
v___x_515_ = ((size_t)31ULL);
v___x_516_ = lean_usize_land(v_x_511_, v___x_515_);
v_j_517_ = lean_usize_to_nat(v___x_516_);
v___x_518_ = lean_array_get_borrowed(v___x_514_, v_es_513_, v_j_517_);
lean_dec(v_j_517_);
switch(lean_obj_tag(v___x_518_))
{
case 0:
{
lean_object* v_key_519_; lean_object* v_val_520_; uint8_t v___x_521_; 
v_key_519_ = lean_ctor_get(v___x_518_, 0);
v_val_520_ = lean_ctor_get(v___x_518_, 1);
v___x_521_ = lean_name_eq(v_x_512_, v_key_519_);
if (v___x_521_ == 0)
{
lean_object* v___x_522_; 
v___x_522_ = lean_box(0);
return v___x_522_;
}
else
{
lean_object* v___x_523_; 
lean_inc(v_val_520_);
v___x_523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_523_, 0, v_val_520_);
return v___x_523_;
}
}
case 1:
{
lean_object* v_node_524_; size_t v___x_525_; size_t v___x_526_; 
v_node_524_ = lean_ctor_get(v___x_518_, 0);
v___x_525_ = ((size_t)5ULL);
v___x_526_ = lean_usize_shift_right(v_x_511_, v___x_525_);
v_x_510_ = v_node_524_;
v_x_511_ = v___x_526_;
goto _start;
}
default: 
{
lean_object* v___x_528_; 
v___x_528_ = lean_box(0);
return v___x_528_;
}
}
}
else
{
lean_object* v_ks_529_; lean_object* v_vs_530_; lean_object* v___x_531_; lean_object* v___x_532_; 
v_ks_529_ = lean_ctor_get(v_x_510_, 0);
v_vs_530_ = lean_ctor_get(v_x_510_, 1);
v___x_531_ = lean_unsigned_to_nat(0u);
v___x_532_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4___redArg(v_ks_529_, v_vs_530_, v___x_531_, v_x_512_);
return v___x_532_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_533_, lean_object* v_x_534_, lean_object* v_x_535_){
_start:
{
size_t v_x_1590__boxed_536_; lean_object* v_res_537_; 
v_x_1590__boxed_536_ = lean_unbox_usize(v_x_534_);
lean_dec(v_x_534_);
v_res_537_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1___redArg(v_x_533_, v_x_1590__boxed_536_, v_x_535_);
lean_dec(v_x_535_);
lean_dec_ref(v_x_533_);
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0___redArg(lean_object* v_x_538_, lean_object* v_x_539_){
_start:
{
uint64_t v___y_541_; 
if (lean_obj_tag(v_x_539_) == 0)
{
uint64_t v___x_544_; 
v___x_544_ = 1723ULL;
v___y_541_ = v___x_544_;
goto v___jp_540_;
}
else
{
uint64_t v_hash_545_; 
v_hash_545_ = lean_ctor_get_uint64(v_x_539_, sizeof(void*)*2);
v___y_541_ = v_hash_545_;
goto v___jp_540_;
}
v___jp_540_:
{
size_t v___x_542_; lean_object* v___x_543_; 
v___x_542_ = lean_uint64_to_usize(v___y_541_);
v___x_543_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1___redArg(v_x_538_, v___x_542_, v_x_539_);
return v___x_543_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0___redArg___boxed(lean_object* v_x_546_, lean_object* v_x_547_){
_start:
{
lean_object* v_res_548_; 
v_res_548_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0___redArg(v_x_546_, v_x_547_);
lean_dec(v_x_547_);
lean_dec_ref(v_x_546_);
return v_res_548_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0___redArg(lean_object* v_x_549_, lean_object* v_x_550_){
_start:
{
uint8_t v_stage_u2081_551_; 
v_stage_u2081_551_ = lean_ctor_get_uint8(v_x_549_, sizeof(void*)*2);
if (v_stage_u2081_551_ == 0)
{
lean_object* v_map_u2081_552_; lean_object* v_map_u2082_553_; lean_object* v___x_554_; 
v_map_u2081_552_ = lean_ctor_get(v_x_549_, 0);
v_map_u2082_553_ = lean_ctor_get(v_x_549_, 1);
v___x_554_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0___redArg(v_map_u2082_553_, v_x_550_);
if (lean_obj_tag(v___x_554_) == 0)
{
lean_object* v___x_555_; 
v___x_555_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1___redArg(v_map_u2081_552_, v_x_550_);
return v___x_555_;
}
else
{
return v___x_554_;
}
}
else
{
lean_object* v_map_u2081_556_; lean_object* v___x_557_; 
v_map_u2081_556_ = lean_ctor_get(v_x_549_, 0);
v___x_557_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1___redArg(v_map_u2081_556_, v_x_550_);
return v___x_557_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0___redArg___boxed(lean_object* v_x_558_, lean_object* v_x_559_){
_start:
{
lean_object* v_res_560_; 
v_res_560_ = l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0___redArg(v_x_558_, v_x_559_);
lean_dec(v_x_559_);
lean_dec_ref(v_x_558_);
return v_res_560_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_addAliasEntry_spec__2(lean_object* v_a_561_, lean_object* v_x_562_){
_start:
{
if (lean_obj_tag(v_x_562_) == 0)
{
uint8_t v___x_563_; 
v___x_563_ = 0;
return v___x_563_;
}
else
{
lean_object* v_head_564_; lean_object* v_tail_565_; uint8_t v___x_566_; 
v_head_564_ = lean_ctor_get(v_x_562_, 0);
v_tail_565_ = lean_ctor_get(v_x_562_, 1);
v___x_566_ = lean_name_eq(v_a_561_, v_head_564_);
if (v___x_566_ == 0)
{
v_x_562_ = v_tail_565_;
goto _start;
}
else
{
return v___x_566_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_addAliasEntry_spec__2___boxed(lean_object* v_a_568_, lean_object* v_x_569_){
_start:
{
uint8_t v_res_570_; lean_object* v_r_571_; 
v_res_570_ = l_List_elem___at___00Lean_addAliasEntry_spec__2(v_a_568_, v_x_569_);
lean_dec(v_x_569_);
lean_dec(v_a_568_);
v_r_571_ = lean_box(v_res_570_);
return v_r_571_;
}
}
LEAN_EXPORT lean_object* l_Lean_addAliasEntry(lean_object* v_s_572_, lean_object* v_e_573_){
_start:
{
lean_object* v_fst_574_; lean_object* v_snd_575_; lean_object* v___x_577_; uint8_t v_isShared_578_; uint8_t v_isSharedCheck_591_; 
v_fst_574_ = lean_ctor_get(v_e_573_, 0);
v_snd_575_ = lean_ctor_get(v_e_573_, 1);
v_isSharedCheck_591_ = !lean_is_exclusive(v_e_573_);
if (v_isSharedCheck_591_ == 0)
{
v___x_577_ = v_e_573_;
v_isShared_578_ = v_isSharedCheck_591_;
goto v_resetjp_576_;
}
else
{
lean_inc(v_snd_575_);
lean_inc(v_fst_574_);
lean_dec(v_e_573_);
v___x_577_ = lean_box(0);
v_isShared_578_ = v_isSharedCheck_591_;
goto v_resetjp_576_;
}
v_resetjp_576_:
{
lean_object* v___x_579_; 
v___x_579_ = l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0___redArg(v_s_572_, v_fst_574_);
if (lean_obj_tag(v___x_579_) == 0)
{
lean_object* v___x_580_; lean_object* v___x_582_; 
v___x_580_ = lean_box(0);
if (v_isShared_578_ == 0)
{
lean_ctor_set_tag(v___x_577_, 1);
lean_ctor_set(v___x_577_, 1, v___x_580_);
lean_ctor_set(v___x_577_, 0, v_snd_575_);
v___x_582_ = v___x_577_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v_snd_575_);
lean_ctor_set(v_reuseFailAlloc_584_, 1, v___x_580_);
v___x_582_ = v_reuseFailAlloc_584_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
lean_object* v___x_583_; 
v___x_583_ = l_Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1___redArg(v_s_572_, v_fst_574_, v___x_582_);
return v___x_583_;
}
}
else
{
lean_object* v_val_585_; uint8_t v___x_586_; 
v_val_585_ = lean_ctor_get(v___x_579_, 0);
lean_inc(v_val_585_);
lean_dec_ref_known(v___x_579_, 1);
v___x_586_ = l_List_elem___at___00Lean_addAliasEntry_spec__2(v_snd_575_, v_val_585_);
if (v___x_586_ == 0)
{
lean_object* v___x_588_; 
if (v_isShared_578_ == 0)
{
lean_ctor_set_tag(v___x_577_, 1);
lean_ctor_set(v___x_577_, 1, v_val_585_);
lean_ctor_set(v___x_577_, 0, v_snd_575_);
v___x_588_ = v___x_577_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v_snd_575_);
lean_ctor_set(v_reuseFailAlloc_590_, 1, v_val_585_);
v___x_588_ = v_reuseFailAlloc_590_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
lean_object* v___x_589_; 
v___x_589_ = l_Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1___redArg(v_s_572_, v_fst_574_, v___x_588_);
return v___x_589_;
}
}
else
{
lean_dec(v_val_585_);
lean_del_object(v___x_577_);
lean_dec(v_snd_575_);
lean_dec(v_fst_574_);
return v_s_572_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0(lean_object* v_00_u03b2_592_, lean_object* v_x_593_, lean_object* v_x_594_){
_start:
{
lean_object* v___x_595_; 
v___x_595_ = l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0___redArg(v_x_593_, v_x_594_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0___boxed(lean_object* v_00_u03b2_596_, lean_object* v_x_597_, lean_object* v_x_598_){
_start:
{
lean_object* v_res_599_; 
v_res_599_ = l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0(v_00_u03b2_596_, v_x_597_, v_x_598_);
lean_dec(v_x_598_);
lean_dec_ref(v_x_597_);
return v_res_599_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1(lean_object* v_00_u03b2_600_, lean_object* v_x_601_, lean_object* v_x_602_, lean_object* v_x_603_){
_start:
{
lean_object* v___x_604_; 
v___x_604_ = l_Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1___redArg(v_x_601_, v_x_602_, v_x_603_);
return v___x_604_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0(lean_object* v_00_u03b2_605_, lean_object* v_x_606_, lean_object* v_x_607_){
_start:
{
lean_object* v___x_608_; 
v___x_608_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0___redArg(v_x_606_, v_x_607_);
return v___x_608_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0___boxed(lean_object* v_00_u03b2_609_, lean_object* v_x_610_, lean_object* v_x_611_){
_start:
{
lean_object* v_res_612_; 
v_res_612_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0(v_00_u03b2_609_, v_x_610_, v_x_611_);
lean_dec(v_x_611_);
lean_dec_ref(v_x_610_);
return v_res_612_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1(lean_object* v_00_u03b2_613_, lean_object* v_m_614_, lean_object* v_a_615_){
_start:
{
lean_object* v___x_616_; 
v___x_616_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1___redArg(v_m_614_, v_a_615_);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1___boxed(lean_object* v_00_u03b2_617_, lean_object* v_m_618_, lean_object* v_a_619_){
_start:
{
lean_object* v_res_620_; 
v_res_620_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1(v_00_u03b2_617_, v_m_618_, v_a_619_);
lean_dec(v_a_619_);
lean_dec_ref(v_m_618_);
return v_res_620_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3(lean_object* v_00_u03b2_621_, lean_object* v_x_622_, lean_object* v_x_623_, lean_object* v_x_624_){
_start:
{
lean_object* v___x_625_; 
v___x_625_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3___redArg(v_x_622_, v_x_623_, v_x_624_);
return v___x_625_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4(lean_object* v_00_u03b2_626_, lean_object* v_m_627_, lean_object* v_a_628_, lean_object* v_b_629_){
_start:
{
lean_object* v___x_630_; 
v___x_630_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4___redArg(v_m_627_, v_a_628_, v_b_629_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_631_, lean_object* v_x_632_, size_t v_x_633_, lean_object* v_x_634_){
_start:
{
lean_object* v___x_635_; 
v___x_635_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1___redArg(v_x_632_, v_x_633_, v_x_634_);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_636_, lean_object* v_x_637_, lean_object* v_x_638_, lean_object* v_x_639_){
_start:
{
size_t v_x_1755__boxed_640_; lean_object* v_res_641_; 
v_x_1755__boxed_640_ = lean_unbox_usize(v_x_638_);
lean_dec(v_x_638_);
v_res_641_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1(v_00_u03b2_636_, v_x_637_, v_x_1755__boxed_640_, v_x_639_);
lean_dec(v_x_639_);
lean_dec_ref(v_x_637_);
return v_res_641_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_642_, lean_object* v_a_643_, lean_object* v_x_644_){
_start:
{
lean_object* v___x_645_; 
v___x_645_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3___redArg(v_a_643_, v_x_644_);
return v___x_645_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_646_, lean_object* v_a_647_, lean_object* v_x_648_){
_start:
{
lean_object* v_res_649_; 
v_res_649_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3(v_00_u03b2_646_, v_a_647_, v_x_648_);
lean_dec(v_x_648_);
lean_dec(v_a_647_);
return v_res_649_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_650_, lean_object* v_x_651_, size_t v_x_652_, size_t v_x_653_, lean_object* v_x_654_, lean_object* v_x_655_){
_start:
{
lean_object* v___x_656_; 
v___x_656_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg(v_x_651_, v_x_652_, v_x_653_, v_x_654_, v_x_655_);
return v___x_656_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___boxed(lean_object* v_00_u03b2_657_, lean_object* v_x_658_, lean_object* v_x_659_, lean_object* v_x_660_, lean_object* v_x_661_, lean_object* v_x_662_){
_start:
{
size_t v_x_1771__boxed_663_; size_t v_x_1772__boxed_664_; lean_object* v_res_665_; 
v_x_1771__boxed_663_ = lean_unbox_usize(v_x_659_);
lean_dec(v_x_659_);
v_x_1772__boxed_664_ = lean_unbox_usize(v_x_660_);
lean_dec(v_x_660_);
v_res_665_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6(v_00_u03b2_657_, v_x_658_, v_x_1771__boxed_663_, v_x_1772__boxed_664_, v_x_661_, v_x_662_);
return v_res_665_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8(lean_object* v_00_u03b2_666_, lean_object* v_a_667_, lean_object* v_x_668_){
_start:
{
uint8_t v___x_669_; 
v___x_669_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8___redArg(v_a_667_, v_x_668_);
return v___x_669_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8___boxed(lean_object* v_00_u03b2_670_, lean_object* v_a_671_, lean_object* v_x_672_){
_start:
{
uint8_t v_res_673_; lean_object* v_r_674_; 
v_res_673_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8(v_00_u03b2_670_, v_a_671_, v_x_672_);
lean_dec(v_x_672_);
lean_dec(v_a_671_);
v_r_674_ = lean_box(v_res_673_);
return v_r_674_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9(lean_object* v_00_u03b2_675_, lean_object* v_data_676_){
_start:
{
lean_object* v___x_677_; 
v___x_677_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9___redArg(v_data_676_);
return v___x_677_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__10(lean_object* v_00_u03b2_678_, lean_object* v_a_679_, lean_object* v_b_680_, lean_object* v_x_681_){
_start:
{
lean_object* v___x_682_; 
v___x_682_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__10___redArg(v_a_679_, v_b_680_, v_x_681_);
return v___x_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_683_, lean_object* v_keys_684_, lean_object* v_vals_685_, lean_object* v_heq_686_, lean_object* v_i_687_, lean_object* v_k_688_){
_start:
{
lean_object* v___x_689_; 
v___x_689_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4___redArg(v_keys_684_, v_vals_685_, v_i_687_, v_k_688_);
return v___x_689_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b2_690_, lean_object* v_keys_691_, lean_object* v_vals_692_, lean_object* v_heq_693_, lean_object* v_i_694_, lean_object* v_k_695_){
_start:
{
lean_object* v_res_696_; 
v_res_696_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4(v_00_u03b2_690_, v_keys_691_, v_vals_692_, v_heq_693_, v_i_694_, v_k_695_);
lean_dec(v_k_695_);
lean_dec_ref(v_vals_692_);
lean_dec_ref(v_keys_691_);
return v_res_696_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__9(lean_object* v_00_u03b2_697_, lean_object* v_n_698_, lean_object* v_k_699_, lean_object* v_v_700_){
_start:
{
lean_object* v___x_701_; 
v___x_701_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__9___redArg(v_n_698_, v_k_699_, v_v_700_);
return v___x_701_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10(lean_object* v_00_u03b2_702_, size_t v_depth_703_, lean_object* v_keys_704_, lean_object* v_vals_705_, lean_object* v_heq_706_, lean_object* v_i_707_, lean_object* v_entries_708_){
_start:
{
lean_object* v___x_709_; 
v___x_709_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg(v_depth_703_, v_keys_704_, v_vals_705_, v_i_707_, v_entries_708_);
return v___x_709_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___boxed(lean_object* v_00_u03b2_710_, lean_object* v_depth_711_, lean_object* v_keys_712_, lean_object* v_vals_713_, lean_object* v_heq_714_, lean_object* v_i_715_, lean_object* v_entries_716_){
_start:
{
size_t v_depth_boxed_717_; lean_object* v_res_718_; 
v_depth_boxed_717_ = lean_unbox_usize(v_depth_711_);
lean_dec(v_depth_711_);
v_res_718_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10(v_00_u03b2_710_, v_depth_boxed_717_, v_keys_712_, v_vals_713_, v_heq_714_, v_i_715_, v_entries_716_);
lean_dec_ref(v_vals_713_);
lean_dec_ref(v_keys_712_);
return v_res_718_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9_spec__14(lean_object* v_00_u03b2_719_, lean_object* v_i_720_, lean_object* v_source_721_, lean_object* v_target_722_){
_start:
{
lean_object* v___x_723_; 
v___x_723_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9_spec__14___redArg(v_i_720_, v_source_721_, v_target_722_);
return v___x_723_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__9_spec__11(lean_object* v_00_u03b2_724_, lean_object* v_x_725_, lean_object* v_x_726_, lean_object* v_x_727_, lean_object* v_x_728_){
_start:
{
lean_object* v___x_729_; 
v___x_729_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__9_spec__11___redArg(v_x_725_, v_x_726_, v_x_727_, v_x_728_);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9_spec__14_spec__16(lean_object* v_00_u03b2_730_, lean_object* v_x_731_, lean_object* v_x_732_){
_start:
{
lean_object* v___x_733_; 
v___x_733_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9_spec__14_spec__16___redArg(v_x_731_, v_x_732_);
return v___x_733_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__1___redArg(lean_object* v_m_734_){
_start:
{
uint8_t v_stage_u2081_735_; 
v_stage_u2081_735_ = lean_ctor_get_uint8(v_m_734_, sizeof(void*)*2);
if (v_stage_u2081_735_ == 0)
{
return v_m_734_;
}
else
{
lean_object* v_map_u2081_736_; lean_object* v_map_u2082_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_745_; 
v_map_u2081_736_ = lean_ctor_get(v_m_734_, 0);
v_map_u2082_737_ = lean_ctor_get(v_m_734_, 1);
v_isSharedCheck_745_ = !lean_is_exclusive(v_m_734_);
if (v_isSharedCheck_745_ == 0)
{
v___x_739_ = v_m_734_;
v_isShared_740_ = v_isSharedCheck_745_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_map_u2082_737_);
lean_inc(v_map_u2081_736_);
lean_dec(v_m_734_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_745_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
uint8_t v___x_741_; lean_object* v___x_743_; 
v___x_741_ = 0;
if (v_isShared_740_ == 0)
{
v___x_743_ = v___x_739_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v_map_u2081_736_);
lean_ctor_set(v_reuseFailAlloc_744_, 1, v_map_u2082_737_);
v___x_743_ = v_reuseFailAlloc_744_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
lean_ctor_set_uint8(v___x_743_, sizeof(void*)*2, v___x_741_);
return v___x_743_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__1(lean_object* v_00_u03b2_746_, lean_object* v_m_747_){
_start:
{
lean_object* v___x_748_; 
v___x_748_ = l_Lean_SMap_switch___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__1___redArg(v_m_747_);
return v___x_748_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn___lam__0_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(lean_object* v_es_749_){
_start:
{
lean_object* v___x_750_; 
v___x_750_ = lean_array_mk(v_es_749_);
return v___x_750_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_as_751_, size_t v_i_752_, size_t v_stop_753_, lean_object* v_b_754_){
_start:
{
uint8_t v___x_755_; 
v___x_755_ = lean_usize_dec_eq(v_i_752_, v_stop_753_);
if (v___x_755_ == 0)
{
lean_object* v___x_756_; lean_object* v___x_757_; size_t v___x_758_; size_t v___x_759_; 
v___x_756_ = lean_array_uget_borrowed(v_as_751_, v_i_752_);
lean_inc(v___x_756_);
v___x_757_ = l_Lean_addAliasEntry(v_b_754_, v___x_756_);
v___x_758_ = ((size_t)1ULL);
v___x_759_ = lean_usize_add(v_i_752_, v___x_758_);
v_i_752_ = v___x_759_;
v_b_754_ = v___x_757_;
goto _start;
}
else
{
return v_b_754_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_as_761_, lean_object* v_i_762_, lean_object* v_stop_763_, lean_object* v_b_764_){
_start:
{
size_t v_i_boxed_765_; size_t v_stop_boxed_766_; lean_object* v_res_767_; 
v_i_boxed_765_ = lean_unbox_usize(v_i_762_);
lean_dec(v_i_762_);
v_stop_boxed_766_ = lean_unbox_usize(v_stop_763_);
lean_dec(v_stop_763_);
v_res_767_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__0(v_as_761_, v_i_boxed_765_, v_stop_boxed_766_, v_b_764_);
lean_dec_ref(v_as_761_);
return v_res_767_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_as_768_, size_t v_i_769_, size_t v_stop_770_, lean_object* v_b_771_){
_start:
{
lean_object* v___y_773_; uint8_t v___x_777_; 
v___x_777_ = lean_usize_dec_eq(v_i_769_, v_stop_770_);
if (v___x_777_ == 0)
{
lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; uint8_t v___x_781_; 
v___x_778_ = lean_array_uget_borrowed(v_as_768_, v_i_769_);
v___x_779_ = lean_unsigned_to_nat(0u);
v___x_780_ = lean_array_get_size(v___x_778_);
v___x_781_ = lean_nat_dec_lt(v___x_779_, v___x_780_);
if (v___x_781_ == 0)
{
v___y_773_ = v_b_771_;
goto v___jp_772_;
}
else
{
uint8_t v___x_782_; 
v___x_782_ = lean_nat_dec_le(v___x_780_, v___x_780_);
if (v___x_782_ == 0)
{
if (v___x_781_ == 0)
{
v___y_773_ = v_b_771_;
goto v___jp_772_;
}
else
{
size_t v___x_783_; size_t v___x_784_; lean_object* v___x_785_; 
v___x_783_ = ((size_t)0ULL);
v___x_784_ = lean_usize_of_nat(v___x_780_);
v___x_785_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__0(v___x_778_, v___x_783_, v___x_784_, v_b_771_);
v___y_773_ = v___x_785_;
goto v___jp_772_;
}
}
else
{
size_t v___x_786_; size_t v___x_787_; lean_object* v___x_788_; 
v___x_786_ = ((size_t)0ULL);
v___x_787_ = lean_usize_of_nat(v___x_780_);
v___x_788_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__0(v___x_778_, v___x_786_, v___x_787_, v_b_771_);
v___y_773_ = v___x_788_;
goto v___jp_772_;
}
}
}
else
{
return v_b_771_;
}
v___jp_772_:
{
size_t v___x_774_; size_t v___x_775_; 
v___x_774_ = ((size_t)1ULL);
v___x_775_ = lean_usize_add(v_i_769_, v___x_774_);
v_i_769_ = v___x_775_;
v_b_771_ = v___y_773_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object* v_as_789_, lean_object* v_i_790_, lean_object* v_stop_791_, lean_object* v_b_792_){
_start:
{
size_t v_i_boxed_793_; size_t v_stop_boxed_794_; lean_object* v_res_795_; 
v_i_boxed_793_ = lean_unbox_usize(v_i_790_);
lean_dec(v_i_790_);
v_stop_boxed_794_ = lean_unbox_usize(v_stop_791_);
lean_dec(v_stop_791_);
v_res_795_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__1(v_as_789_, v_i_boxed_793_, v_stop_boxed_794_, v_b_792_);
lean_dec_ref(v_as_789_);
return v_res_795_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0(lean_object* v_initState_796_, lean_object* v_as_797_){
_start:
{
lean_object* v___x_798_; lean_object* v___x_799_; uint8_t v___x_800_; 
v___x_798_ = lean_unsigned_to_nat(0u);
v___x_799_ = lean_array_get_size(v_as_797_);
v___x_800_ = lean_nat_dec_lt(v___x_798_, v___x_799_);
if (v___x_800_ == 0)
{
return v_initState_796_;
}
else
{
uint8_t v___x_801_; 
v___x_801_ = lean_nat_dec_le(v___x_799_, v___x_799_);
if (v___x_801_ == 0)
{
if (v___x_800_ == 0)
{
return v_initState_796_;
}
else
{
size_t v___x_802_; size_t v___x_803_; lean_object* v___x_804_; 
v___x_802_ = ((size_t)0ULL);
v___x_803_ = lean_usize_of_nat(v___x_799_);
v___x_804_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__1(v_as_797_, v___x_802_, v___x_803_, v_initState_796_);
return v___x_804_;
}
}
else
{
size_t v___x_805_; size_t v___x_806_; lean_object* v___x_807_; 
v___x_805_ = ((size_t)0ULL);
v___x_806_ = lean_usize_of_nat(v___x_799_);
v___x_807_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__1(v_as_797_, v___x_805_, v___x_806_, v_initState_796_);
return v___x_807_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0___boxed(lean_object* v_initState_808_, lean_object* v_as_809_){
_start:
{
lean_object* v_res_810_; 
v_res_810_ = l_Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0(v_initState_808_, v_as_809_);
lean_dec_ref(v_as_809_);
return v_res_810_;
}
}
static lean_object* _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; 
v___x_811_ = lean_box(0);
v___x_812_ = lean_unsigned_to_nat(16u);
v___x_813_ = lean_mk_array(v___x_812_, v___x_811_);
return v___x_813_;
}
}
static lean_object* _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; 
v___x_814_ = lean_obj_once(&l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_, &l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__once, _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_);
v___x_815_ = lean_unsigned_to_nat(0u);
v___x_816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_816_, 0, v___x_815_);
lean_ctor_set(v___x_816_, 1, v___x_814_);
return v___x_816_;
}
}
static lean_object* _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_817_; 
v___x_817_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_817_;
}
}
static lean_object* _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_818_; lean_object* v___x_819_; 
v___x_818_ = lean_obj_once(&l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_, &l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__once, _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_);
v___x_819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_819_, 0, v___x_818_);
return v___x_819_;
}
}
static lean_object* _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__4_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_820_; lean_object* v___x_821_; uint8_t v___x_822_; lean_object* v___x_823_; 
v___x_820_ = lean_obj_once(&l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_, &l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__once, _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_);
v___x_821_ = lean_obj_once(&l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_, &l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__once, _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_);
v___x_822_ = 1;
v___x_823_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_823_, 0, v___x_821_);
lean_ctor_set(v___x_823_, 1, v___x_820_);
lean_ctor_set_uint8(v___x_823_, sizeof(void*)*2, v___x_822_);
return v___x_823_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn___lam__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(lean_object* v_es_824_){
_start:
{
lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; 
v___x_825_ = lean_obj_once(&l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__4_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_, &l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__4_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__once, _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__4_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_);
v___x_826_ = l_Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0(v___x_825_, v_es_824_);
v___x_827_ = l_Lean_SMap_switch___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__1___redArg(v___x_826_);
return v___x_827_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn___lam__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2____boxed(lean_object* v_es_828_){
_start:
{
lean_object* v_res_829_; 
v_res_829_ = l___private_Lean_ResolveName_0__Lean_initFn___lam__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(v_es_828_);
lean_dec_ref(v_es_828_);
return v_res_829_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_846_; lean_object* v___x_847_; 
v___x_846_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_initFn___closed__6_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_));
v___x_847_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_846_);
return v___x_847_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2____boxed(lean_object* v_a_848_){
_start:
{
lean_object* v_res_849_; 
v_res_849_ = l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_();
return v_res_849_;
}
}
LEAN_EXPORT lean_object* l_Lean_addAlias(lean_object* v_env_850_, lean_object* v_a_851_, lean_object* v_e_852_){
_start:
{
lean_object* v___x_853_; lean_object* v_toEnvExtension_854_; lean_object* v_asyncMode_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; 
v___x_853_ = l_Lean_aliasExtension;
v_toEnvExtension_854_ = lean_ctor_get(v___x_853_, 0);
v_asyncMode_855_ = lean_ctor_get(v_toEnvExtension_854_, 2);
v___x_856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_856_, 0, v_a_851_);
lean_ctor_set(v___x_856_, 1, v_e_852_);
v___x_857_ = lean_box(0);
v___x_858_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_853_, v_env_850_, v___x_856_, v_asyncMode_855_, v___x_857_);
return v___x_858_;
}
}
static lean_object* _init_l_Lean_getAliasState___closed__2(void){
_start:
{
lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; 
v___x_861_ = ((lean_object*)(l_Lean_getAliasState___closed__1));
v___x_862_ = ((lean_object*)(l_Lean_getAliasState___closed__0));
v___x_863_ = l_Lean_SMap_instInhabited(lean_box(0), lean_box(0), v___x_862_, v___x_861_);
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAliasState(lean_object* v_env_864_){
_start:
{
lean_object* v___x_865_; lean_object* v_toEnvExtension_866_; lean_object* v_asyncMode_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; 
v___x_865_ = l_Lean_aliasExtension;
v_toEnvExtension_866_ = lean_ctor_get(v___x_865_, 0);
v_asyncMode_867_ = lean_ctor_get(v_toEnvExtension_866_, 2);
v___x_868_ = lean_obj_once(&l_Lean_getAliasState___closed__2, &l_Lean_getAliasState___closed__2_once, _init_l_Lean_getAliasState___closed__2);
v___x_869_ = lean_box(0);
v___x_870_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_868_, v___x_865_, v_env_864_, v_asyncMode_867_, v___x_869_);
return v___x_870_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_getAliases_spec__0(lean_object* v_env_871_, uint8_t v_skipProtected_872_, lean_object* v_a_873_, lean_object* v_a_874_){
_start:
{
if (lean_obj_tag(v_a_873_) == 0)
{
lean_object* v___x_875_; 
lean_dec_ref(v_env_871_);
v___x_875_ = l_List_reverse___redArg(v_a_874_);
return v___x_875_;
}
else
{
lean_object* v_head_876_; lean_object* v_tail_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_888_; 
v_head_876_ = lean_ctor_get(v_a_873_, 0);
v_tail_877_ = lean_ctor_get(v_a_873_, 1);
v_isSharedCheck_888_ = !lean_is_exclusive(v_a_873_);
if (v_isSharedCheck_888_ == 0)
{
v___x_879_ = v_a_873_;
v_isShared_880_ = v_isSharedCheck_888_;
goto v_resetjp_878_;
}
else
{
lean_inc(v_tail_877_);
lean_inc(v_head_876_);
lean_dec(v_a_873_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_888_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
uint8_t v___x_881_; 
lean_inc(v_head_876_);
lean_inc_ref(v_env_871_);
v___x_881_ = l_Lean_isProtected(v_env_871_, v_head_876_);
if (v___x_881_ == 0)
{
if (v_skipProtected_872_ == 0)
{
lean_del_object(v___x_879_);
lean_dec(v_head_876_);
v_a_873_ = v_tail_877_;
goto _start;
}
else
{
lean_object* v___x_884_; 
if (v_isShared_880_ == 0)
{
lean_ctor_set(v___x_879_, 1, v_a_874_);
v___x_884_ = v___x_879_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v_head_876_);
lean_ctor_set(v_reuseFailAlloc_886_, 1, v_a_874_);
v___x_884_ = v_reuseFailAlloc_886_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
v_a_873_ = v_tail_877_;
v_a_874_ = v___x_884_;
goto _start;
}
}
}
else
{
lean_del_object(v___x_879_);
lean_dec(v_head_876_);
v_a_873_ = v_tail_877_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_getAliases_spec__0___boxed(lean_object* v_env_889_, lean_object* v_skipProtected_890_, lean_object* v_a_891_, lean_object* v_a_892_){
_start:
{
uint8_t v_skipProtected_boxed_893_; lean_object* v_res_894_; 
v_skipProtected_boxed_893_ = lean_unbox(v_skipProtected_890_);
v_res_894_ = l_List_filterTR_loop___at___00Lean_getAliases_spec__0(v_env_889_, v_skipProtected_boxed_893_, v_a_891_, v_a_892_);
return v_res_894_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAliases(lean_object* v_env_895_, lean_object* v_a_896_, uint8_t v_skipProtected_897_){
_start:
{
lean_object* v___x_898_; lean_object* v_toEnvExtension_899_; lean_object* v_asyncMode_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; 
v___x_898_ = l_Lean_aliasExtension;
v_toEnvExtension_899_ = lean_ctor_get(v___x_898_, 0);
v_asyncMode_900_ = lean_ctor_get(v_toEnvExtension_899_, 2);
v___x_901_ = lean_obj_once(&l_Lean_getAliasState___closed__2, &l_Lean_getAliasState___closed__2_once, _init_l_Lean_getAliasState___closed__2);
v___x_902_ = lean_box(0);
lean_inc_ref(v_env_895_);
v___x_903_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_901_, v___x_898_, v_env_895_, v_asyncMode_900_, v___x_902_);
v___x_904_ = l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0___redArg(v___x_903_, v_a_896_);
lean_dec(v___x_903_);
if (lean_obj_tag(v___x_904_) == 0)
{
lean_object* v___x_905_; 
lean_dec_ref(v_env_895_);
v___x_905_ = lean_box(0);
return v___x_905_;
}
else
{
if (v_skipProtected_897_ == 0)
{
lean_object* v_val_906_; 
lean_dec_ref(v_env_895_);
v_val_906_ = lean_ctor_get(v___x_904_, 0);
lean_inc(v_val_906_);
lean_dec_ref_known(v___x_904_, 1);
return v_val_906_;
}
else
{
lean_object* v_val_907_; lean_object* v___x_908_; lean_object* v___x_909_; 
v_val_907_ = lean_ctor_get(v___x_904_, 0);
lean_inc(v_val_907_);
lean_dec_ref_known(v___x_904_, 1);
v___x_908_ = lean_box(0);
v___x_909_ = l_List_filterTR_loop___at___00Lean_getAliases_spec__0(v_env_895_, v_skipProtected_897_, v_val_907_, v___x_908_);
return v___x_909_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getAliases___boxed(lean_object* v_env_910_, lean_object* v_a_911_, lean_object* v_skipProtected_912_){
_start:
{
uint8_t v_skipProtected_boxed_913_; lean_object* v_res_914_; 
v_skipProtected_boxed_913_ = lean_unbox(v_skipProtected_912_);
v_res_914_ = l_Lean_getAliases(v_env_910_, v_a_911_, v_skipProtected_boxed_913_);
lean_dec(v_a_911_);
return v_res_914_;
}
}
LEAN_EXPORT lean_object* l_Lean_getRevAliases___lam__0(lean_object* v_e_915_, lean_object* v_as_916_, lean_object* v_a_917_, lean_object* v_es_918_){
_start:
{
uint8_t v___x_919_; 
v___x_919_ = l_List_elem___at___00Lean_addAliasEntry_spec__2(v_e_915_, v_es_918_);
if (v___x_919_ == 0)
{
lean_dec(v_a_917_);
return v_as_916_;
}
else
{
lean_object* v___x_920_; 
v___x_920_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_920_, 0, v_a_917_);
lean_ctor_set(v___x_920_, 1, v_as_916_);
return v___x_920_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getRevAliases___lam__0___boxed(lean_object* v_e_921_, lean_object* v_as_922_, lean_object* v_a_923_, lean_object* v_es_924_){
_start:
{
lean_object* v_res_925_; 
v_res_925_ = l_Lean_getRevAliases___lam__0(v_e_921_, v_as_922_, v_a_923_, v_es_924_);
lean_dec(v_es_924_);
lean_dec(v_e_921_);
return v_res_925_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6___redArg(lean_object* v_f_926_, lean_object* v_keys_927_, lean_object* v_vals_928_, lean_object* v_i_929_, lean_object* v_acc_930_){
_start:
{
lean_object* v___x_931_; uint8_t v___x_932_; 
v___x_931_ = lean_array_get_size(v_keys_927_);
v___x_932_ = lean_nat_dec_lt(v_i_929_, v___x_931_);
if (v___x_932_ == 0)
{
lean_dec(v_i_929_);
lean_dec(v_f_926_);
return v_acc_930_;
}
else
{
lean_object* v_k_933_; lean_object* v_v_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; 
v_k_933_ = lean_array_fget_borrowed(v_keys_927_, v_i_929_);
v_v_934_ = lean_array_fget_borrowed(v_vals_928_, v_i_929_);
lean_inc(v_f_926_);
lean_inc(v_v_934_);
lean_inc(v_k_933_);
v___x_935_ = lean_apply_3(v_f_926_, v_acc_930_, v_k_933_, v_v_934_);
v___x_936_ = lean_unsigned_to_nat(1u);
v___x_937_ = lean_nat_add(v_i_929_, v___x_936_);
lean_dec(v_i_929_);
v_i_929_ = v___x_937_;
v_acc_930_ = v___x_935_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_f_939_, lean_object* v_keys_940_, lean_object* v_vals_941_, lean_object* v_i_942_, lean_object* v_acc_943_){
_start:
{
lean_object* v_res_944_; 
v_res_944_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6___redArg(v_f_939_, v_keys_940_, v_vals_941_, v_i_942_, v_acc_943_);
lean_dec_ref(v_vals_941_);
lean_dec_ref(v_keys_940_);
return v_res_944_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_f_945_, lean_object* v_x_946_, lean_object* v_x_947_){
_start:
{
if (lean_obj_tag(v_x_946_) == 0)
{
lean_object* v_es_948_; lean_object* v___x_949_; lean_object* v___x_950_; uint8_t v___x_951_; 
v_es_948_ = lean_ctor_get(v_x_946_, 0);
v___x_949_ = lean_unsigned_to_nat(0u);
v___x_950_ = lean_array_get_size(v_es_948_);
v___x_951_ = lean_nat_dec_lt(v___x_949_, v___x_950_);
if (v___x_951_ == 0)
{
lean_dec(v_f_945_);
return v_x_947_;
}
else
{
uint8_t v___x_952_; 
v___x_952_ = lean_nat_dec_le(v___x_950_, v___x_950_);
if (v___x_952_ == 0)
{
if (v___x_951_ == 0)
{
lean_dec(v_f_945_);
return v_x_947_;
}
else
{
size_t v___x_953_; size_t v___x_954_; lean_object* v___x_955_; 
v___x_953_ = ((size_t)0ULL);
v___x_954_ = lean_usize_of_nat(v___x_950_);
v___x_955_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(v_f_945_, v_es_948_, v___x_953_, v___x_954_, v_x_947_);
return v___x_955_;
}
}
else
{
size_t v___x_956_; size_t v___x_957_; lean_object* v___x_958_; 
v___x_956_ = ((size_t)0ULL);
v___x_957_ = lean_usize_of_nat(v___x_950_);
v___x_958_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(v_f_945_, v_es_948_, v___x_956_, v___x_957_, v_x_947_);
return v___x_958_;
}
}
}
else
{
lean_object* v_ks_959_; lean_object* v_vs_960_; lean_object* v___x_961_; lean_object* v___x_962_; 
v_ks_959_ = lean_ctor_get(v_x_946_, 0);
v_vs_960_ = lean_ctor_get(v_x_946_, 1);
v___x_961_ = lean_unsigned_to_nat(0u);
v___x_962_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6___redArg(v_f_945_, v_ks_959_, v_vs_960_, v___x_961_, v_x_947_);
return v___x_962_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(lean_object* v_f_963_, lean_object* v_as_964_, size_t v_i_965_, size_t v_stop_966_, lean_object* v_b_967_){
_start:
{
lean_object* v___y_969_; uint8_t v___x_973_; 
v___x_973_ = lean_usize_dec_eq(v_i_965_, v_stop_966_);
if (v___x_973_ == 0)
{
lean_object* v___x_974_; 
v___x_974_ = lean_array_uget_borrowed(v_as_964_, v_i_965_);
switch(lean_obj_tag(v___x_974_))
{
case 0:
{
lean_object* v_key_975_; lean_object* v_val_976_; lean_object* v___x_977_; 
v_key_975_ = lean_ctor_get(v___x_974_, 0);
v_val_976_ = lean_ctor_get(v___x_974_, 1);
lean_inc(v_f_963_);
lean_inc(v_val_976_);
lean_inc(v_key_975_);
v___x_977_ = lean_apply_3(v_f_963_, v_b_967_, v_key_975_, v_val_976_);
v___y_969_ = v___x_977_;
goto v___jp_968_;
}
case 1:
{
lean_object* v_node_978_; lean_object* v___x_979_; 
v_node_978_ = lean_ctor_get(v___x_974_, 0);
lean_inc(v_f_963_);
v___x_979_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg(v_f_963_, v_node_978_, v_b_967_);
v___y_969_ = v___x_979_;
goto v___jp_968_;
}
default: 
{
v___y_969_ = v_b_967_;
goto v___jp_968_;
}
}
}
else
{
lean_dec(v_f_963_);
return v_b_967_;
}
v___jp_968_:
{
size_t v___x_970_; size_t v___x_971_; 
v___x_970_ = ((size_t)1ULL);
v___x_971_ = lean_usize_add(v_i_965_, v___x_970_);
v_i_965_ = v___x_971_;
v_b_967_ = v___y_969_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v_f_980_, lean_object* v_as_981_, lean_object* v_i_982_, lean_object* v_stop_983_, lean_object* v_b_984_){
_start:
{
size_t v_i_boxed_985_; size_t v_stop_boxed_986_; lean_object* v_res_987_; 
v_i_boxed_985_ = lean_unbox_usize(v_i_982_);
lean_dec(v_i_982_);
v_stop_boxed_986_ = lean_unbox_usize(v_stop_983_);
lean_dec(v_stop_983_);
v_res_987_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(v_f_980_, v_as_981_, v_i_boxed_985_, v_stop_boxed_986_, v_b_984_);
lean_dec_ref(v_as_981_);
return v_res_987_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_f_988_, lean_object* v_x_989_, lean_object* v_x_990_){
_start:
{
lean_object* v_res_991_; 
v_res_991_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg(v_f_988_, v_x_989_, v_x_990_);
lean_dec_ref(v_x_989_);
return v_res_991_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg___lam__0(lean_object* v_f_992_, lean_object* v_x1_993_, lean_object* v_x2_994_, lean_object* v_x3_995_){
_start:
{
lean_object* v___x_996_; 
v___x_996_ = lean_apply_3(v_f_992_, v_x1_993_, v_x2_994_, v_x3_995_);
return v___x_996_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg(lean_object* v_map_997_, lean_object* v_f_998_, lean_object* v_init_999_){
_start:
{
lean_object* v___f_1000_; lean_object* v___x_1001_; 
v___f_1000_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1000_, 0, v_f_998_);
v___x_1001_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg(v___f_1000_, v_map_997_, v_init_999_);
return v___x_1001_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg___boxed(lean_object* v_map_1002_, lean_object* v_f_1003_, lean_object* v_init_1004_){
_start:
{
lean_object* v_res_1005_; 
v_res_1005_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg(v_map_1002_, v_f_1003_, v_init_1004_);
lean_dec_ref(v_map_1002_);
return v_res_1005_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__0___redArg(lean_object* v_f_1006_, lean_object* v_x_1007_, lean_object* v_x_1008_){
_start:
{
if (lean_obj_tag(v_x_1008_) == 0)
{
lean_dec(v_f_1006_);
return v_x_1007_;
}
else
{
lean_object* v_key_1009_; lean_object* v_value_1010_; lean_object* v_tail_1011_; lean_object* v___x_1012_; 
v_key_1009_ = lean_ctor_get(v_x_1008_, 0);
lean_inc(v_key_1009_);
v_value_1010_ = lean_ctor_get(v_x_1008_, 1);
lean_inc(v_value_1010_);
v_tail_1011_ = lean_ctor_get(v_x_1008_, 2);
lean_inc(v_tail_1011_);
lean_dec_ref_known(v_x_1008_, 3);
lean_inc(v_f_1006_);
v___x_1012_ = lean_apply_3(v_f_1006_, v_x_1007_, v_key_1009_, v_value_1010_);
v_x_1007_ = v___x_1012_;
v_x_1008_ = v_tail_1011_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2___redArg(lean_object* v_f_1014_, lean_object* v_as_1015_, size_t v_i_1016_, size_t v_stop_1017_, lean_object* v_b_1018_){
_start:
{
uint8_t v___x_1019_; 
v___x_1019_ = lean_usize_dec_eq(v_i_1016_, v_stop_1017_);
if (v___x_1019_ == 0)
{
lean_object* v___x_1020_; lean_object* v___x_1021_; size_t v___x_1022_; size_t v___x_1023_; 
v___x_1020_ = lean_array_uget_borrowed(v_as_1015_, v_i_1016_);
lean_inc(v___x_1020_);
lean_inc(v_f_1014_);
v___x_1021_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__0___redArg(v_f_1014_, v_b_1018_, v___x_1020_);
v___x_1022_ = ((size_t)1ULL);
v___x_1023_ = lean_usize_add(v_i_1016_, v___x_1022_);
v_i_1016_ = v___x_1023_;
v_b_1018_ = v___x_1021_;
goto _start;
}
else
{
lean_dec(v_f_1014_);
return v_b_1018_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2___redArg___boxed(lean_object* v_f_1025_, lean_object* v_as_1026_, lean_object* v_i_1027_, lean_object* v_stop_1028_, lean_object* v_b_1029_){
_start:
{
size_t v_i_boxed_1030_; size_t v_stop_boxed_1031_; lean_object* v_res_1032_; 
v_i_boxed_1030_ = lean_unbox_usize(v_i_1027_);
lean_dec(v_i_1027_);
v_stop_boxed_1031_ = lean_unbox_usize(v_stop_1028_);
lean_dec(v_stop_1028_);
v_res_1032_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2___redArg(v_f_1025_, v_as_1026_, v_i_boxed_1030_, v_stop_boxed_1031_, v_b_1029_);
lean_dec_ref(v_as_1026_);
return v_res_1032_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0___redArg(lean_object* v_f_1033_, lean_object* v_init_1034_, lean_object* v_m_1035_){
_start:
{
lean_object* v_map_u2081_1036_; lean_object* v_map_u2082_1037_; lean_object* v_buckets_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; uint8_t v___x_1041_; 
v_map_u2081_1036_ = lean_ctor_get(v_m_1035_, 0);
v_map_u2082_1037_ = lean_ctor_get(v_m_1035_, 1);
v_buckets_1038_ = lean_ctor_get(v_map_u2081_1036_, 1);
v___x_1039_ = lean_unsigned_to_nat(0u);
v___x_1040_ = lean_array_get_size(v_buckets_1038_);
v___x_1041_ = lean_nat_dec_lt(v___x_1039_, v___x_1040_);
if (v___x_1041_ == 0)
{
lean_object* v___x_1042_; 
v___x_1042_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg(v_map_u2082_1037_, v_f_1033_, v_init_1034_);
return v___x_1042_;
}
else
{
uint8_t v___x_1043_; 
v___x_1043_ = lean_nat_dec_le(v___x_1040_, v___x_1040_);
if (v___x_1043_ == 0)
{
if (v___x_1041_ == 0)
{
lean_object* v___x_1044_; 
v___x_1044_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg(v_map_u2082_1037_, v_f_1033_, v_init_1034_);
return v___x_1044_;
}
else
{
size_t v___x_1045_; size_t v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; 
v___x_1045_ = ((size_t)0ULL);
v___x_1046_ = lean_usize_of_nat(v___x_1040_);
lean_inc(v_f_1033_);
v___x_1047_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2___redArg(v_f_1033_, v_buckets_1038_, v___x_1045_, v___x_1046_, v_init_1034_);
v___x_1048_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg(v_map_u2082_1037_, v_f_1033_, v___x_1047_);
return v___x_1048_;
}
}
else
{
size_t v___x_1049_; size_t v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; 
v___x_1049_ = ((size_t)0ULL);
v___x_1050_ = lean_usize_of_nat(v___x_1040_);
lean_inc(v_f_1033_);
v___x_1051_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2___redArg(v_f_1033_, v_buckets_1038_, v___x_1049_, v___x_1050_, v_init_1034_);
v___x_1052_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg(v_map_u2082_1037_, v_f_1033_, v___x_1051_);
return v___x_1052_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0___redArg___boxed(lean_object* v_f_1053_, lean_object* v_init_1054_, lean_object* v_m_1055_){
_start:
{
lean_object* v_res_1056_; 
v_res_1056_ = l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0___redArg(v_f_1053_, v_init_1054_, v_m_1055_);
lean_dec_ref(v_m_1055_);
return v_res_1056_;
}
}
LEAN_EXPORT lean_object* l_Lean_getRevAliases(lean_object* v_env_1057_, lean_object* v_e_1058_){
_start:
{
lean_object* v___x_1059_; lean_object* v_toEnvExtension_1060_; lean_object* v_asyncMode_1061_; lean_object* v___f_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___x_1059_ = l_Lean_aliasExtension;
v_toEnvExtension_1060_ = lean_ctor_get(v___x_1059_, 0);
v_asyncMode_1061_ = lean_ctor_get(v_toEnvExtension_1060_, 2);
v___f_1062_ = lean_alloc_closure((void*)(l_Lean_getRevAliases___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1062_, 0, v_e_1058_);
v___x_1063_ = lean_obj_once(&l_Lean_getAliasState___closed__2, &l_Lean_getAliasState___closed__2_once, _init_l_Lean_getAliasState___closed__2);
v___x_1064_ = lean_box(0);
v___x_1065_ = lean_box(0);
v___x_1066_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1063_, v___x_1059_, v_env_1057_, v_asyncMode_1061_, v___x_1065_);
v___x_1067_ = l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0___redArg(v___f_1062_, v___x_1064_, v___x_1066_);
lean_dec(v___x_1066_);
return v___x_1067_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0(lean_object* v_00_u03b2_1068_, lean_object* v_00_u03c3_1069_, lean_object* v_f_1070_, lean_object* v_init_1071_, lean_object* v_m_1072_){
_start:
{
lean_object* v___x_1073_; 
v___x_1073_ = l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0___redArg(v_f_1070_, v_init_1071_, v_m_1072_);
return v___x_1073_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0___boxed(lean_object* v_00_u03b2_1074_, lean_object* v_00_u03c3_1075_, lean_object* v_f_1076_, lean_object* v_init_1077_, lean_object* v_m_1078_){
_start:
{
lean_object* v_res_1079_; 
v_res_1079_ = l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0(v_00_u03b2_1074_, v_00_u03c3_1075_, v_f_1076_, v_init_1077_, v_m_1078_);
lean_dec_ref(v_m_1078_);
return v_res_1079_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__0(lean_object* v_00_u03b2_1080_, lean_object* v_00_u03c3_1081_, lean_object* v_f_1082_, lean_object* v_x_1083_, lean_object* v_x_1084_){
_start:
{
lean_object* v___x_1085_; 
v___x_1085_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__0___redArg(v_f_1082_, v_x_1083_, v_x_1084_);
return v___x_1085_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1(lean_object* v_00_u03c3_1086_, lean_object* v_00_u03b2_1087_, lean_object* v_map_1088_, lean_object* v_f_1089_, lean_object* v_init_1090_){
_start:
{
lean_object* v___x_1091_; 
v___x_1091_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg(v_map_1088_, v_f_1089_, v_init_1090_);
return v___x_1091_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___boxed(lean_object* v_00_u03c3_1092_, lean_object* v_00_u03b2_1093_, lean_object* v_map_1094_, lean_object* v_f_1095_, lean_object* v_init_1096_){
_start:
{
lean_object* v_res_1097_; 
v_res_1097_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1(v_00_u03c3_1092_, v_00_u03b2_1093_, v_map_1094_, v_f_1095_, v_init_1096_);
lean_dec_ref(v_map_1094_);
return v_res_1097_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2(lean_object* v_00_u03b2_1098_, lean_object* v_00_u03c3_1099_, lean_object* v_f_1100_, lean_object* v_as_1101_, size_t v_i_1102_, size_t v_stop_1103_, lean_object* v_b_1104_){
_start:
{
lean_object* v___x_1105_; 
v___x_1105_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2___redArg(v_f_1100_, v_as_1101_, v_i_1102_, v_stop_1103_, v_b_1104_);
return v___x_1105_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1106_, lean_object* v_00_u03c3_1107_, lean_object* v_f_1108_, lean_object* v_as_1109_, lean_object* v_i_1110_, lean_object* v_stop_1111_, lean_object* v_b_1112_){
_start:
{
size_t v_i_boxed_1113_; size_t v_stop_boxed_1114_; lean_object* v_res_1115_; 
v_i_boxed_1113_ = lean_unbox_usize(v_i_1110_);
lean_dec(v_i_1110_);
v_stop_boxed_1114_ = lean_unbox_usize(v_stop_1111_);
lean_dec(v_stop_1111_);
v_res_1115_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2(v_00_u03b2_1106_, v_00_u03c3_1107_, v_f_1108_, v_as_1109_, v_i_boxed_1113_, v_stop_boxed_1114_, v_b_1112_);
lean_dec_ref(v_as_1109_);
return v_res_1115_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2___redArg(lean_object* v_map_1116_, lean_object* v_f_1117_, lean_object* v_init_1118_){
_start:
{
lean_object* v___x_1119_; 
v___x_1119_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg(v_f_1117_, v_map_1116_, v_init_1118_);
return v___x_1119_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_map_1120_, lean_object* v_f_1121_, lean_object* v_init_1122_){
_start:
{
lean_object* v_res_1123_; 
v_res_1123_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2___redArg(v_map_1120_, v_f_1121_, v_init_1122_);
lean_dec_ref(v_map_1120_);
return v_res_1123_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2(lean_object* v_00_u03c3_1124_, lean_object* v_00_u03b2_1125_, lean_object* v_map_1126_, lean_object* v_f_1127_, lean_object* v_init_1128_){
_start:
{
lean_object* v___x_1129_; 
v___x_1129_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg(v_f_1127_, v_map_1126_, v_init_1128_);
return v___x_1129_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03c3_1130_, lean_object* v_00_u03b2_1131_, lean_object* v_map_1132_, lean_object* v_f_1133_, lean_object* v_init_1134_){
_start:
{
lean_object* v_res_1135_; 
v_res_1135_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2(v_00_u03c3_1130_, v_00_u03b2_1131_, v_map_1132_, v_f_1133_, v_init_1134_);
lean_dec_ref(v_map_1132_);
return v_res_1135_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03c3_1136_, lean_object* v_00_u03b1_1137_, lean_object* v_00_u03b2_1138_, lean_object* v_f_1139_, lean_object* v_x_1140_, lean_object* v_x_1141_){
_start:
{
lean_object* v___x_1142_; 
v___x_1142_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg(v_f_1139_, v_x_1140_, v_x_1141_);
return v___x_1142_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03c3_1143_, lean_object* v_00_u03b1_1144_, lean_object* v_00_u03b2_1145_, lean_object* v_f_1146_, lean_object* v_x_1147_, lean_object* v_x_1148_){
_start:
{
lean_object* v_res_1149_; 
v_res_1149_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3(v_00_u03c3_1143_, v_00_u03b1_1144_, v_00_u03b2_1145_, v_f_1146_, v_x_1147_, v_x_1148_);
lean_dec_ref(v_x_1147_);
return v_res_1149_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5(lean_object* v_00_u03b1_1150_, lean_object* v_00_u03b2_1151_, lean_object* v_00_u03c3_1152_, lean_object* v_f_1153_, lean_object* v_as_1154_, size_t v_i_1155_, size_t v_stop_1156_, lean_object* v_b_1157_){
_start:
{
lean_object* v___x_1158_; 
v___x_1158_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(v_f_1153_, v_as_1154_, v_i_1155_, v_stop_1156_, v_b_1157_);
return v___x_1158_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5___boxed(lean_object* v_00_u03b1_1159_, lean_object* v_00_u03b2_1160_, lean_object* v_00_u03c3_1161_, lean_object* v_f_1162_, lean_object* v_as_1163_, lean_object* v_i_1164_, lean_object* v_stop_1165_, lean_object* v_b_1166_){
_start:
{
size_t v_i_boxed_1167_; size_t v_stop_boxed_1168_; lean_object* v_res_1169_; 
v_i_boxed_1167_ = lean_unbox_usize(v_i_1164_);
lean_dec(v_i_1164_);
v_stop_boxed_1168_ = lean_unbox_usize(v_stop_1165_);
lean_dec(v_stop_1165_);
v_res_1169_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5(v_00_u03b1_1159_, v_00_u03b2_1160_, v_00_u03c3_1161_, v_f_1162_, v_as_1163_, v_i_boxed_1167_, v_stop_boxed_1168_, v_b_1166_);
lean_dec_ref(v_as_1163_);
return v_res_1169_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6(lean_object* v_00_u03c3_1170_, lean_object* v_00_u03b1_1171_, lean_object* v_00_u03b2_1172_, lean_object* v_f_1173_, lean_object* v_keys_1174_, lean_object* v_vals_1175_, lean_object* v_heq_1176_, lean_object* v_i_1177_, lean_object* v_acc_1178_){
_start:
{
lean_object* v___x_1179_; 
v___x_1179_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6___redArg(v_f_1173_, v_keys_1174_, v_vals_1175_, v_i_1177_, v_acc_1178_);
return v___x_1179_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03c3_1180_, lean_object* v_00_u03b1_1181_, lean_object* v_00_u03b2_1182_, lean_object* v_f_1183_, lean_object* v_keys_1184_, lean_object* v_vals_1185_, lean_object* v_heq_1186_, lean_object* v_i_1187_, lean_object* v_acc_1188_){
_start:
{
lean_object* v_res_1189_; 
v_res_1189_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6(v_00_u03c3_1180_, v_00_u03b1_1181_, v_00_u03b2_1182_, v_f_1183_, v_keys_1184_, v_vals_1185_, v_heq_1186_, v_i_1187_, v_acc_1188_);
lean_dec_ref(v_vals_1185_);
lean_dec_ref(v_keys_1184_);
return v_res_1189_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(lean_object* v_env_1190_, lean_object* v_declName_1191_){
_start:
{
uint8_t v___y_1193_; uint8_t v___x_1196_; 
v___x_1196_ = l_Lean_Environment_containsOnBranch(v_env_1190_, v_declName_1191_);
if (v___x_1196_ == 0)
{
uint8_t v___x_1197_; 
lean_inc(v_declName_1191_);
lean_inc_ref(v_env_1190_);
v___x_1197_ = lean_is_reserved_name(v_env_1190_, v_declName_1191_);
v___y_1193_ = v___x_1197_;
goto v___jp_1192_;
}
else
{
v___y_1193_ = v___x_1196_;
goto v___jp_1192_;
}
v___jp_1192_:
{
if (v___y_1193_ == 0)
{
uint8_t v___x_1194_; uint8_t v___x_1195_; 
v___x_1194_ = 1;
v___x_1195_ = l_Lean_Environment_contains(v_env_1190_, v_declName_1191_, v___x_1194_);
return v___x_1195_;
}
else
{
lean_dec(v_declName_1191_);
lean_dec_ref(v_env_1190_);
return v___y_1193_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved___boxed(lean_object* v_env_1198_, lean_object* v_declName_1199_){
_start:
{
uint8_t v_res_1200_; lean_object* v_r_1201_; 
v_res_1200_ = l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(v_env_1198_, v_declName_1199_);
v_r_1201_ = lean_box(v_res_1200_);
return v_r_1201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__spec__0(lean_object* v_name_1202_, lean_object* v_decl_1203_, lean_object* v_ref_1204_){
_start:
{
lean_object* v_defValue_1206_; lean_object* v_descr_1207_; lean_object* v_deprecation_x3f_1208_; lean_object* v___x_1209_; uint8_t v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; 
v_defValue_1206_ = lean_ctor_get(v_decl_1203_, 0);
v_descr_1207_ = lean_ctor_get(v_decl_1203_, 1);
v_deprecation_x3f_1208_ = lean_ctor_get(v_decl_1203_, 2);
v___x_1209_ = lean_alloc_ctor(1, 0, 1);
v___x_1210_ = lean_unbox(v_defValue_1206_);
lean_ctor_set_uint8(v___x_1209_, 0, v___x_1210_);
lean_inc(v_deprecation_x3f_1208_);
lean_inc_ref(v_descr_1207_);
lean_inc_n(v_name_1202_, 2);
v___x_1211_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1211_, 0, v_name_1202_);
lean_ctor_set(v___x_1211_, 1, v_ref_1204_);
lean_ctor_set(v___x_1211_, 2, v___x_1209_);
lean_ctor_set(v___x_1211_, 3, v_descr_1207_);
lean_ctor_set(v___x_1211_, 4, v_deprecation_x3f_1208_);
v___x_1212_ = lean_register_option(v_name_1202_, v___x_1211_);
if (lean_obj_tag(v___x_1212_) == 0)
{
lean_object* v___x_1214_; uint8_t v_isShared_1215_; uint8_t v_isSharedCheck_1220_; 
v_isSharedCheck_1220_ = !lean_is_exclusive(v___x_1212_);
if (v_isSharedCheck_1220_ == 0)
{
lean_object* v_unused_1221_; 
v_unused_1221_ = lean_ctor_get(v___x_1212_, 0);
lean_dec(v_unused_1221_);
v___x_1214_ = v___x_1212_;
v_isShared_1215_ = v_isSharedCheck_1220_;
goto v_resetjp_1213_;
}
else
{
lean_dec(v___x_1212_);
v___x_1214_ = lean_box(0);
v_isShared_1215_ = v_isSharedCheck_1220_;
goto v_resetjp_1213_;
}
v_resetjp_1213_:
{
lean_object* v___x_1216_; lean_object* v___x_1218_; 
lean_inc(v_defValue_1206_);
v___x_1216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1216_, 0, v_name_1202_);
lean_ctor_set(v___x_1216_, 1, v_defValue_1206_);
if (v_isShared_1215_ == 0)
{
lean_ctor_set(v___x_1214_, 0, v___x_1216_);
v___x_1218_ = v___x_1214_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v___x_1216_);
v___x_1218_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
return v___x_1218_;
}
}
}
else
{
lean_object* v_a_1222_; lean_object* v___x_1224_; uint8_t v_isShared_1225_; uint8_t v_isSharedCheck_1229_; 
lean_dec(v_name_1202_);
v_a_1222_ = lean_ctor_get(v___x_1212_, 0);
v_isSharedCheck_1229_ = !lean_is_exclusive(v___x_1212_);
if (v_isSharedCheck_1229_ == 0)
{
v___x_1224_ = v___x_1212_;
v_isShared_1225_ = v_isSharedCheck_1229_;
goto v_resetjp_1223_;
}
else
{
lean_inc(v_a_1222_);
lean_dec(v___x_1212_);
v___x_1224_ = lean_box(0);
v_isShared_1225_ = v_isSharedCheck_1229_;
goto v_resetjp_1223_;
}
v_resetjp_1223_:
{
lean_object* v___x_1227_; 
if (v_isShared_1225_ == 0)
{
v___x_1227_ = v___x_1224_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v_a_1222_);
v___x_1227_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
return v___x_1227_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_1230_, lean_object* v_decl_1231_, lean_object* v_ref_1232_, lean_object* v_a_1233_){
_start:
{
lean_object* v_res_1234_; 
v_res_1234_ = l_Lean_Option_register___at___00__private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__spec__0(v_name_1230_, v_decl_1231_, v_ref_1232_);
lean_dec_ref(v_decl_1231_);
return v_res_1234_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; 
v___x_1253_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__2_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_));
v___x_1254_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__4_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_));
v___x_1255_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__6_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_));
v___x_1256_ = l_Lean_Option_register___at___00__private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__spec__0(v___x_1253_, v___x_1254_, v___x_1255_);
return v___x_1256_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4____boxed(lean_object* v_a_1257_){
_start:
{
lean_object* v_res_1258_; 
v_res_1258_ = l___private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_();
return v_res_1258_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; 
v___x_1277_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__1_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4_));
v___x_1278_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__3_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4_));
v___x_1279_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__4_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4_));
v___x_1280_ = l_Lean_Option_register___at___00__private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__spec__0(v___x_1277_, v___x_1278_, v___x_1279_);
return v___x_1280_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4____boxed(lean_object* v_a_1281_){
_start:
{
lean_object* v_res_1282_; 
v_res_1282_ = l___private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4_();
return v_res_1282_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__1(lean_object* v_opts_1283_, lean_object* v_opt_1284_){
_start:
{
lean_object* v_name_1285_; lean_object* v_defValue_1286_; lean_object* v_map_1287_; lean_object* v___x_1288_; 
v_name_1285_ = lean_ctor_get(v_opt_1284_, 0);
v_defValue_1286_ = lean_ctor_get(v_opt_1284_, 1);
v_map_1287_ = lean_ctor_get(v_opts_1283_, 0);
v___x_1288_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1287_, v_name_1285_);
if (lean_obj_tag(v___x_1288_) == 0)
{
uint8_t v___x_1289_; 
v___x_1289_ = lean_unbox(v_defValue_1286_);
return v___x_1289_;
}
else
{
lean_object* v_val_1290_; 
v_val_1290_ = lean_ctor_get(v___x_1288_, 0);
lean_inc(v_val_1290_);
lean_dec_ref_known(v___x_1288_, 1);
if (lean_obj_tag(v_val_1290_) == 1)
{
uint8_t v_v_1291_; 
v_v_1291_ = lean_ctor_get_uint8(v_val_1290_, 0);
lean_dec_ref_known(v_val_1290_, 0);
return v_v_1291_;
}
else
{
uint8_t v___x_1292_; 
lean_dec(v_val_1290_);
v___x_1292_ = lean_unbox(v_defValue_1286_);
return v___x_1292_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__1___boxed(lean_object* v_opts_1293_, lean_object* v_opt_1294_){
_start:
{
uint8_t v_res_1295_; lean_object* v_r_1296_; 
v_res_1295_ = l_Lean_Option_get___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__1(v_opts_1293_, v_opt_1294_);
lean_dec_ref(v_opt_1294_);
lean_dec_ref(v_opts_1293_);
v_r_1296_ = lean_box(v_res_1295_);
return v_r_1296_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0(lean_object* v_declName_1300_, lean_object* v_env_1301_, lean_object* v_as_1302_, size_t v_sz_1303_, size_t v_i_1304_, lean_object* v_b_1305_){
_start:
{
uint8_t v___x_1306_; 
v___x_1306_ = lean_usize_dec_lt(v_i_1304_, v_sz_1303_);
if (v___x_1306_ == 0)
{
lean_dec_ref(v_env_1301_);
lean_dec(v_declName_1300_);
lean_inc_ref(v_b_1305_);
return v_b_1305_;
}
else
{
lean_object* v_a_1307_; lean_object* v_toImport_1308_; lean_object* v_module_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; uint8_t v___x_1312_; 
v_a_1307_ = lean_array_uget_borrowed(v_as_1302_, v_i_1304_);
v_toImport_1308_ = lean_ctor_get(v_a_1307_, 0);
v_module_1309_ = lean_ctor_get(v_toImport_1308_, 0);
v___x_1310_ = lean_box(0);
lean_inc(v_declName_1300_);
lean_inc(v_module_1309_);
v___x_1311_ = l_Lean_mkPrivateNameCore(v_module_1309_, v_declName_1300_);
lean_inc(v___x_1311_);
lean_inc_ref(v_env_1301_);
v___x_1312_ = l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(v_env_1301_, v___x_1311_);
if (v___x_1312_ == 0)
{
lean_object* v___x_1313_; size_t v___x_1314_; size_t v___x_1315_; 
lean_dec(v___x_1311_);
v___x_1313_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0___closed__0));
v___x_1314_ = ((size_t)1ULL);
v___x_1315_ = lean_usize_add(v_i_1304_, v___x_1314_);
v_i_1304_ = v___x_1315_;
v_b_1305_ = v___x_1313_;
goto _start;
}
else
{
lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; 
lean_dec_ref(v_env_1301_);
lean_dec(v_declName_1300_);
v___x_1317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1317_, 0, v___x_1311_);
v___x_1318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1318_, 0, v___x_1317_);
v___x_1319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1319_, 0, v___x_1318_);
lean_ctor_set(v___x_1319_, 1, v___x_1310_);
return v___x_1319_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0___boxed(lean_object* v_declName_1320_, lean_object* v_env_1321_, lean_object* v_as_1322_, lean_object* v_sz_1323_, lean_object* v_i_1324_, lean_object* v_b_1325_){
_start:
{
size_t v_sz_boxed_1326_; size_t v_i_boxed_1327_; lean_object* v_res_1328_; 
v_sz_boxed_1326_ = lean_unbox_usize(v_sz_1323_);
lean_dec(v_sz_1323_);
v_i_boxed_1327_ = lean_unbox_usize(v_i_1324_);
lean_dec(v_i_1324_);
v_res_1328_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0(v_declName_1320_, v_env_1321_, v_as_1322_, v_sz_boxed_1326_, v_i_boxed_1327_, v_b_1325_);
lean_dec_ref(v_b_1325_);
lean_dec_ref(v_as_1322_);
return v_res_1328_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName(lean_object* v_env_1329_, lean_object* v_opts_1330_, lean_object* v_declName_1331_){
_start:
{
uint8_t v_isExporting_1347_; 
v_isExporting_1347_ = lean_ctor_get_uint8(v_env_1329_, sizeof(void*)*8);
if (v_isExporting_1347_ == 0)
{
goto v___jp_1332_;
}
else
{
lean_object* v___x_1348_; uint8_t v___x_1349_; 
v___x_1348_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_1349_ = l_Lean_Option_get___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__1(v_opts_1330_, v___x_1348_);
if (v___x_1349_ == 0)
{
lean_object* v___x_1350_; 
lean_dec(v_declName_1331_);
lean_dec_ref(v_env_1329_);
v___x_1350_ = lean_box(0);
return v___x_1350_;
}
else
{
goto v___jp_1332_;
}
}
v___jp_1332_:
{
lean_object* v___x_1333_; uint8_t v___x_1334_; 
lean_inc(v_declName_1331_);
v___x_1333_ = l_Lean_mkPrivateName(v_env_1329_, v_declName_1331_);
lean_inc(v___x_1333_);
lean_inc_ref(v_env_1329_);
v___x_1334_ = l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(v_env_1329_, v___x_1333_);
if (v___x_1334_ == 0)
{
lean_object* v___x_1335_; uint8_t v_isModule_1336_; 
lean_dec(v___x_1333_);
v___x_1335_ = l_Lean_Environment_header(v_env_1329_);
v_isModule_1336_ = lean_ctor_get_uint8(v___x_1335_, sizeof(void*)*7 + 4);
if (v_isModule_1336_ == 0)
{
lean_object* v___x_1337_; 
lean_dec_ref(v___x_1335_);
lean_dec(v_declName_1331_);
lean_dec_ref(v_env_1329_);
v___x_1337_ = lean_box(0);
return v___x_1337_;
}
else
{
lean_object* v_importAllModules_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; size_t v_sz_1341_; size_t v___x_1342_; lean_object* v___x_1343_; lean_object* v_fst_1344_; 
v_importAllModules_1338_ = lean_ctor_get(v___x_1335_, 5);
lean_inc_ref(v_importAllModules_1338_);
lean_dec_ref(v___x_1335_);
v___x_1339_ = lean_box(0);
v___x_1340_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0___closed__0));
v_sz_1341_ = lean_array_size(v_importAllModules_1338_);
v___x_1342_ = ((size_t)0ULL);
v___x_1343_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0(v_declName_1331_, v_env_1329_, v_importAllModules_1338_, v_sz_1341_, v___x_1342_, v___x_1340_);
lean_dec_ref(v_importAllModules_1338_);
v_fst_1344_ = lean_ctor_get(v___x_1343_, 0);
lean_inc(v_fst_1344_);
lean_dec_ref(v___x_1343_);
if (lean_obj_tag(v_fst_1344_) == 0)
{
return v___x_1339_;
}
else
{
lean_object* v_val_1345_; 
v_val_1345_ = lean_ctor_get(v_fst_1344_, 0);
lean_inc(v_val_1345_);
lean_dec_ref_known(v_fst_1344_, 1);
return v_val_1345_;
}
}
}
else
{
lean_object* v___x_1346_; 
lean_dec(v_declName_1331_);
lean_dec_ref(v_env_1329_);
v___x_1346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1346_, 0, v___x_1333_);
return v___x_1346_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName___boxed(lean_object* v_env_1351_, lean_object* v_opts_1352_, lean_object* v_declName_1353_){
_start:
{
lean_object* v_res_1354_; 
v_res_1354_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName(v_env_1351_, v_opts_1352_, v_declName_1353_);
lean_dec_ref(v_opts_1352_);
return v_res_1354_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveQualifiedName(lean_object* v_env_1355_, lean_object* v_opts_1356_, lean_object* v_ns_1357_, lean_object* v_id_1358_){
_start:
{
lean_object* v_resolvedId_1359_; uint8_t v___x_1360_; lean_object* v_resolvedIds_1361_; 
lean_inc(v_id_1358_);
v_resolvedId_1359_ = l_Lean_Name_append(v_ns_1357_, v_id_1358_);
v___x_1360_ = l_Lean_Name_isAtomic(v_id_1358_);
lean_dec(v_id_1358_);
lean_inc_ref(v_env_1355_);
v_resolvedIds_1361_ = l_Lean_getAliases(v_env_1355_, v_resolvedId_1359_, v___x_1360_);
if (v___x_1360_ == 0)
{
goto v___jp_1362_;
}
else
{
uint8_t v___x_1368_; 
lean_inc(v_resolvedId_1359_);
lean_inc_ref(v_env_1355_);
v___x_1368_ = l_Lean_isProtected(v_env_1355_, v_resolvedId_1359_);
if (v___x_1368_ == 0)
{
goto v___jp_1362_;
}
else
{
lean_dec(v_resolvedId_1359_);
lean_dec_ref(v_env_1355_);
return v_resolvedIds_1361_;
}
}
v___jp_1362_:
{
uint8_t v___x_1363_; 
lean_inc(v_resolvedId_1359_);
lean_inc_ref(v_env_1355_);
v___x_1363_ = l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(v_env_1355_, v_resolvedId_1359_);
if (v___x_1363_ == 0)
{
lean_object* v___x_1364_; 
v___x_1364_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName(v_env_1355_, v_opts_1356_, v_resolvedId_1359_);
if (lean_obj_tag(v___x_1364_) == 1)
{
lean_object* v_val_1365_; lean_object* v___x_1366_; 
v_val_1365_ = lean_ctor_get(v___x_1364_, 0);
lean_inc(v_val_1365_);
lean_dec_ref_known(v___x_1364_, 1);
v___x_1366_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1366_, 0, v_val_1365_);
lean_ctor_set(v___x_1366_, 1, v_resolvedIds_1361_);
return v___x_1366_;
}
else
{
lean_dec(v___x_1364_);
return v_resolvedIds_1361_;
}
}
else
{
lean_object* v___x_1367_; 
lean_dec_ref(v_env_1355_);
v___x_1367_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1367_, 0, v_resolvedId_1359_);
lean_ctor_set(v___x_1367_, 1, v_resolvedIds_1361_);
return v___x_1367_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveQualifiedName___boxed(lean_object* v_env_1369_, lean_object* v_opts_1370_, lean_object* v_ns_1371_, lean_object* v_id_1372_){
_start:
{
lean_object* v_res_1373_; 
v_res_1373_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveQualifiedName(v_env_1369_, v_opts_1370_, v_ns_1371_, v_id_1372_);
lean_dec_ref(v_opts_1370_);
return v_res_1373_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveUsingNamespace(lean_object* v_env_1374_, lean_object* v_opts_1375_, lean_object* v_id_1376_, lean_object* v_x_1377_){
_start:
{
if (lean_obj_tag(v_x_1377_) == 1)
{
lean_object* v_pre_1378_; lean_object* v___x_1379_; 
v_pre_1378_ = lean_ctor_get(v_x_1377_, 0);
lean_inc(v_pre_1378_);
lean_inc(v_id_1376_);
lean_inc_ref(v_env_1374_);
v___x_1379_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveQualifiedName(v_env_1374_, v_opts_1375_, v_x_1377_, v_id_1376_);
if (lean_obj_tag(v___x_1379_) == 0)
{
v_x_1377_ = v_pre_1378_;
goto _start;
}
else
{
lean_dec(v_pre_1378_);
lean_dec(v_id_1376_);
lean_dec_ref(v_env_1374_);
return v___x_1379_;
}
}
else
{
lean_object* v___x_1381_; 
lean_dec(v_x_1377_);
lean_dec(v_id_1376_);
lean_dec_ref(v_env_1374_);
v___x_1381_ = lean_box(0);
return v___x_1381_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveUsingNamespace___boxed(lean_object* v_env_1382_, lean_object* v_opts_1383_, lean_object* v_id_1384_, lean_object* v_x_1385_){
_start:
{
lean_object* v_res_1386_; 
v_res_1386_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveUsingNamespace(v_env_1382_, v_opts_1383_, v_id_1384_, v_x_1385_);
lean_dec_ref(v_opts_1383_);
return v_res_1386_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveExact(lean_object* v_env_1387_, lean_object* v_opts_1388_, lean_object* v_id_1389_){
_start:
{
uint8_t v___x_1390_; 
v___x_1390_ = l_Lean_Name_isAtomic(v_id_1389_);
if (v___x_1390_ == 0)
{
lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v_resolvedId_1393_; uint8_t v___x_1394_; 
v___x_1391_ = l_Lean_rootNamespace;
v___x_1392_ = lean_box(0);
v_resolvedId_1393_ = l_Lean_Name_replacePrefix(v_id_1389_, v___x_1391_, v___x_1392_);
lean_inc(v_resolvedId_1393_);
lean_inc_ref(v_env_1387_);
v___x_1394_ = l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(v_env_1387_, v_resolvedId_1393_);
if (v___x_1394_ == 0)
{
lean_object* v___x_1395_; 
v___x_1395_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName(v_env_1387_, v_opts_1388_, v_resolvedId_1393_);
return v___x_1395_;
}
else
{
lean_object* v___x_1396_; 
lean_dec_ref(v_env_1387_);
v___x_1396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1396_, 0, v_resolvedId_1393_);
return v___x_1396_;
}
}
else
{
lean_object* v___x_1397_; 
lean_dec(v_id_1389_);
lean_dec_ref(v_env_1387_);
v___x_1397_ = lean_box(0);
return v___x_1397_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveExact___boxed(lean_object* v_env_1398_, lean_object* v_opts_1399_, lean_object* v_id_1400_){
_start:
{
lean_object* v_res_1401_; 
v_res_1401_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveExact(v_env_1398_, v_opts_1399_, v_id_1400_);
lean_dec_ref(v_opts_1399_);
return v_res_1401_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveOpenDecls(lean_object* v_env_1402_, lean_object* v_opts_1403_, lean_object* v_id_1404_, lean_object* v_x_1405_, lean_object* v_x_1406_){
_start:
{
if (lean_obj_tag(v_x_1405_) == 0)
{
lean_dec(v_id_1404_);
lean_dec_ref(v_env_1402_);
return v_x_1406_;
}
else
{
lean_object* v_head_1407_; 
v_head_1407_ = lean_ctor_get(v_x_1405_, 0);
lean_inc(v_head_1407_);
if (lean_obj_tag(v_head_1407_) == 0)
{
lean_object* v_tail_1408_; lean_object* v_ns_1409_; lean_object* v_except_1410_; uint8_t v___x_1411_; 
v_tail_1408_ = lean_ctor_get(v_x_1405_, 1);
lean_inc(v_tail_1408_);
lean_dec_ref_known(v_x_1405_, 2);
v_ns_1409_ = lean_ctor_get(v_head_1407_, 0);
lean_inc(v_ns_1409_);
v_except_1410_ = lean_ctor_get(v_head_1407_, 1);
lean_inc(v_except_1410_);
lean_dec_ref_known(v_head_1407_, 2);
v___x_1411_ = l_List_elem___at___00Lean_addAliasEntry_spec__2(v_id_1404_, v_except_1410_);
lean_dec(v_except_1410_);
if (v___x_1411_ == 0)
{
lean_object* v_newResolvedIds_1412_; lean_object* v___x_1413_; 
lean_inc(v_id_1404_);
lean_inc_ref(v_env_1402_);
v_newResolvedIds_1412_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveQualifiedName(v_env_1402_, v_opts_1403_, v_ns_1409_, v_id_1404_);
v___x_1413_ = l_List_appendTR___redArg(v_newResolvedIds_1412_, v_x_1406_);
v_x_1405_ = v_tail_1408_;
v_x_1406_ = v___x_1413_;
goto _start;
}
else
{
lean_dec(v_ns_1409_);
v_x_1405_ = v_tail_1408_;
goto _start;
}
}
else
{
lean_object* v_tail_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1436_; 
v_tail_1416_ = lean_ctor_get(v_x_1405_, 1);
v_isSharedCheck_1436_ = !lean_is_exclusive(v_x_1405_);
if (v_isSharedCheck_1436_ == 0)
{
lean_object* v_unused_1437_; 
v_unused_1437_ = lean_ctor_get(v_x_1405_, 0);
lean_dec(v_unused_1437_);
v___x_1418_ = v_x_1405_;
v_isShared_1419_ = v_isSharedCheck_1436_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_tail_1416_);
lean_dec(v_x_1405_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1436_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v_id_1420_; lean_object* v_declName_1421_; uint8_t v___x_1422_; 
v_id_1420_ = lean_ctor_get(v_head_1407_, 0);
lean_inc(v_id_1420_);
v_declName_1421_ = lean_ctor_get(v_head_1407_, 1);
lean_inc(v_declName_1421_);
lean_dec_ref_known(v_head_1407_, 2);
v___x_1422_ = lean_name_eq(v_id_1420_, v_id_1404_);
if (v___x_1422_ == 0)
{
uint8_t v___x_1423_; 
v___x_1423_ = l_Lean_Name_isPrefixOf(v_id_1420_, v_id_1404_);
if (v___x_1423_ == 0)
{
lean_dec(v_declName_1421_);
lean_dec(v_id_1420_);
lean_del_object(v___x_1418_);
v_x_1405_ = v_tail_1416_;
goto _start;
}
else
{
lean_object* v_candidate_1425_; uint8_t v___x_1426_; 
lean_inc(v_id_1404_);
v_candidate_1425_ = l_Lean_Name_replacePrefix(v_id_1404_, v_id_1420_, v_declName_1421_);
lean_dec(v_declName_1421_);
lean_dec(v_id_1420_);
lean_inc(v_candidate_1425_);
lean_inc_ref(v_env_1402_);
v___x_1426_ = l_Lean_Environment_contains(v_env_1402_, v_candidate_1425_, v___x_1423_);
if (v___x_1426_ == 0)
{
lean_dec(v_candidate_1425_);
lean_del_object(v___x_1418_);
v_x_1405_ = v_tail_1416_;
goto _start;
}
else
{
lean_object* v___x_1429_; 
if (v_isShared_1419_ == 0)
{
lean_ctor_set(v___x_1418_, 1, v_x_1406_);
lean_ctor_set(v___x_1418_, 0, v_candidate_1425_);
v___x_1429_ = v___x_1418_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v_candidate_1425_);
lean_ctor_set(v_reuseFailAlloc_1431_, 1, v_x_1406_);
v___x_1429_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
v_x_1405_ = v_tail_1416_;
v_x_1406_ = v___x_1429_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_1433_; 
lean_dec(v_id_1420_);
if (v_isShared_1419_ == 0)
{
lean_ctor_set(v___x_1418_, 1, v_x_1406_);
lean_ctor_set(v___x_1418_, 0, v_declName_1421_);
v___x_1433_ = v___x_1418_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1435_; 
v_reuseFailAlloc_1435_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1435_, 0, v_declName_1421_);
lean_ctor_set(v_reuseFailAlloc_1435_, 1, v_x_1406_);
v___x_1433_ = v_reuseFailAlloc_1435_;
goto v_reusejp_1432_;
}
v_reusejp_1432_:
{
v_x_1405_ = v_tail_1416_;
v_x_1406_ = v___x_1433_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveOpenDecls___boxed(lean_object* v_env_1438_, lean_object* v_opts_1439_, lean_object* v_id_1440_, lean_object* v_x_1441_, lean_object* v_x_1442_){
_start:
{
lean_object* v_res_1443_; 
v_res_1443_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveOpenDecls(v_env_1438_, v_opts_1439_, v_id_1440_, v_x_1441_, v_x_1442_);
lean_dec_ref(v_opts_1439_);
return v_res_1443_;
}
}
LEAN_EXPORT lean_object* l_List_eraseDups___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__0(lean_object* v_as_1445_){
_start:
{
lean_object* v___f_1446_; lean_object* v___x_1447_; 
v___f_1446_ = ((lean_object*)(l_List_eraseDups___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__0___closed__0));
v___x_1447_ = l_List_eraseDupsBy___redArg(v___f_1446_, v_as_1445_);
return v___x_1447_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__1(lean_object* v_projs_1448_, lean_object* v_a_1449_, lean_object* v_a_1450_){
_start:
{
if (lean_obj_tag(v_a_1449_) == 0)
{
lean_object* v___x_1451_; 
lean_dec(v_projs_1448_);
v___x_1451_ = l_List_reverse___redArg(v_a_1450_);
return v___x_1451_;
}
else
{
lean_object* v_head_1452_; lean_object* v_tail_1453_; lean_object* v___x_1455_; uint8_t v_isShared_1456_; uint8_t v_isSharedCheck_1462_; 
v_head_1452_ = lean_ctor_get(v_a_1449_, 0);
v_tail_1453_ = lean_ctor_get(v_a_1449_, 1);
v_isSharedCheck_1462_ = !lean_is_exclusive(v_a_1449_);
if (v_isSharedCheck_1462_ == 0)
{
v___x_1455_ = v_a_1449_;
v_isShared_1456_ = v_isSharedCheck_1462_;
goto v_resetjp_1454_;
}
else
{
lean_inc(v_tail_1453_);
lean_inc(v_head_1452_);
lean_dec(v_a_1449_);
v___x_1455_ = lean_box(0);
v_isShared_1456_ = v_isSharedCheck_1462_;
goto v_resetjp_1454_;
}
v_resetjp_1454_:
{
lean_object* v___x_1457_; lean_object* v___x_1459_; 
lean_inc(v_projs_1448_);
v___x_1457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1457_, 0, v_head_1452_);
lean_ctor_set(v___x_1457_, 1, v_projs_1448_);
if (v_isShared_1456_ == 0)
{
lean_ctor_set(v___x_1455_, 1, v_a_1450_);
lean_ctor_set(v___x_1455_, 0, v___x_1457_);
v___x_1459_ = v___x_1455_;
goto v_reusejp_1458_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v___x_1457_);
lean_ctor_set(v_reuseFailAlloc_1461_, 1, v_a_1450_);
v___x_1459_ = v_reuseFailAlloc_1461_;
goto v_reusejp_1458_;
}
v_reusejp_1458_:
{
v_a_1449_ = v_tail_1453_;
v_a_1450_ = v___x_1459_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop(lean_object* v_env_1463_, lean_object* v_opts_1464_, lean_object* v_ns_1465_, lean_object* v_openDecls_1466_, lean_object* v_extractionResult_1467_, lean_object* v_id_1468_, lean_object* v_projs_1469_){
_start:
{
if (lean_obj_tag(v_id_1468_) == 1)
{
lean_object* v_pre_1470_; lean_object* v_str_1471_; lean_object* v_imported_1472_; lean_object* v_ctx_1473_; lean_object* v_scopes_1474_; lean_object* v___x_1475_; lean_object* v_id_1476_; lean_object* v___y_1478_; lean_object* v___x_1488_; lean_object* v___y_1490_; 
v_pre_1470_ = lean_ctor_get(v_id_1468_, 0);
lean_inc(v_pre_1470_);
v_str_1471_ = lean_ctor_get(v_id_1468_, 1);
lean_inc_ref(v_str_1471_);
v_imported_1472_ = lean_ctor_get(v_extractionResult_1467_, 1);
v_ctx_1473_ = lean_ctor_get(v_extractionResult_1467_, 2);
v_scopes_1474_ = lean_ctor_get(v_extractionResult_1467_, 3);
lean_inc(v_scopes_1474_);
lean_inc(v_ctx_1473_);
lean_inc(v_imported_1472_);
v___x_1475_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1475_, 0, v_id_1468_);
lean_ctor_set(v___x_1475_, 1, v_imported_1472_);
lean_ctor_set(v___x_1475_, 2, v_ctx_1473_);
lean_ctor_set(v___x_1475_, 3, v_scopes_1474_);
v_id_1476_ = l_Lean_MacroScopesView_review(v___x_1475_);
lean_inc(v_ns_1465_);
lean_inc(v_id_1476_);
lean_inc_ref(v_env_1463_);
v___x_1488_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveUsingNamespace(v_env_1463_, v_opts_1464_, v_id_1476_, v_ns_1465_);
if (lean_obj_tag(v___x_1488_) == 0)
{
lean_object* v___x_1495_; 
lean_inc(v_id_1476_);
lean_inc_ref(v_env_1463_);
v___x_1495_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveExact(v_env_1463_, v_opts_1464_, v_id_1476_);
if (lean_obj_tag(v___x_1495_) == 0)
{
uint8_t v___x_1496_; 
lean_inc(v_id_1476_);
lean_inc_ref(v_env_1463_);
v___x_1496_ = l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(v_env_1463_, v_id_1476_);
if (v___x_1496_ == 0)
{
v___y_1490_ = v___x_1488_;
goto v___jp_1489_;
}
else
{
lean_object* v___x_1497_; 
lean_inc(v_id_1476_);
v___x_1497_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1497_, 0, v_id_1476_);
lean_ctor_set(v___x_1497_, 1, v___x_1488_);
v___y_1490_ = v___x_1497_;
goto v___jp_1489_;
}
}
else
{
lean_object* v_val_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; 
lean_dec(v_id_1476_);
lean_dec_ref(v_str_1471_);
lean_dec(v_pre_1470_);
lean_dec(v_openDecls_1466_);
lean_dec(v_ns_1465_);
lean_dec_ref(v_env_1463_);
v_val_1498_ = lean_ctor_get(v___x_1495_, 0);
lean_inc(v_val_1498_);
lean_dec_ref_known(v___x_1495_, 1);
v___x_1499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1499_, 0, v_val_1498_);
lean_ctor_set(v___x_1499_, 1, v_projs_1469_);
v___x_1500_ = lean_box(0);
v___x_1501_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1501_, 0, v___x_1499_);
lean_ctor_set(v___x_1501_, 1, v___x_1500_);
return v___x_1501_;
}
}
else
{
lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; 
lean_dec(v_id_1476_);
lean_dec_ref(v_str_1471_);
lean_dec(v_pre_1470_);
lean_dec(v_openDecls_1466_);
lean_dec(v_ns_1465_);
lean_dec_ref(v_env_1463_);
v___x_1502_ = l_List_eraseDups___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__0(v___x_1488_);
v___x_1503_ = lean_box(0);
v___x_1504_ = l_List_mapTR_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__1(v_projs_1469_, v___x_1502_, v___x_1503_);
return v___x_1504_;
}
v___jp_1477_:
{
lean_object* v_resolvedIds_1479_; uint8_t v___x_1480_; lean_object* v___x_1481_; lean_object* v_resolvedIds_1482_; 
lean_inc(v_openDecls_1466_);
lean_inc(v_id_1476_);
lean_inc_ref_n(v_env_1463_, 2);
v_resolvedIds_1479_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveOpenDecls(v_env_1463_, v_opts_1464_, v_id_1476_, v_openDecls_1466_, v___y_1478_);
v___x_1480_ = l_Lean_Name_isAtomic(v_id_1476_);
v___x_1481_ = l_Lean_getAliases(v_env_1463_, v_id_1476_, v___x_1480_);
lean_dec(v_id_1476_);
v_resolvedIds_1482_ = l_List_appendTR___redArg(v___x_1481_, v_resolvedIds_1479_);
if (lean_obj_tag(v_resolvedIds_1482_) == 0)
{
lean_object* v___x_1483_; 
v___x_1483_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1483_, 0, v_str_1471_);
lean_ctor_set(v___x_1483_, 1, v_projs_1469_);
v_id_1468_ = v_pre_1470_;
v_projs_1469_ = v___x_1483_;
goto _start;
}
else
{
lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; 
lean_dec_ref(v_str_1471_);
lean_dec(v_pre_1470_);
lean_dec(v_openDecls_1466_);
lean_dec(v_ns_1465_);
lean_dec_ref(v_env_1463_);
v___x_1485_ = l_List_eraseDups___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__0(v_resolvedIds_1482_);
v___x_1486_ = lean_box(0);
v___x_1487_ = l_List_mapTR_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__1(v_projs_1469_, v___x_1485_, v___x_1486_);
return v___x_1487_;
}
}
v___jp_1489_:
{
lean_object* v___x_1491_; 
lean_inc(v_id_1476_);
lean_inc_ref(v_env_1463_);
v___x_1491_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName(v_env_1463_, v_opts_1464_, v_id_1476_);
if (lean_obj_tag(v___x_1491_) == 1)
{
lean_object* v_val_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; 
v_val_1492_ = lean_ctor_get(v___x_1491_, 0);
lean_inc(v_val_1492_);
lean_dec_ref_known(v___x_1491_, 1);
v___x_1493_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1493_, 0, v_val_1492_);
lean_ctor_set(v___x_1493_, 1, v___x_1488_);
v___x_1494_ = l_List_appendTR___redArg(v___x_1493_, v___y_1490_);
v___y_1478_ = v___x_1494_;
goto v___jp_1477_;
}
else
{
lean_dec(v___x_1491_);
lean_dec(v___x_1488_);
v___y_1478_ = v___y_1490_;
goto v___jp_1477_;
}
}
}
else
{
lean_object* v___x_1505_; 
lean_dec(v_projs_1469_);
lean_dec(v_id_1468_);
lean_dec(v_openDecls_1466_);
lean_dec(v_ns_1465_);
lean_dec_ref(v_env_1463_);
v___x_1505_ = lean_box(0);
return v___x_1505_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop___boxed(lean_object* v_env_1506_, lean_object* v_opts_1507_, lean_object* v_ns_1508_, lean_object* v_openDecls_1509_, lean_object* v_extractionResult_1510_, lean_object* v_id_1511_, lean_object* v_projs_1512_){
_start:
{
lean_object* v_res_1513_; 
v_res_1513_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop(v_env_1506_, v_opts_1507_, v_ns_1508_, v_openDecls_1509_, v_extractionResult_1510_, v_id_1511_, v_projs_1512_);
lean_dec_ref(v_extractionResult_1510_);
lean_dec_ref(v_opts_1507_);
return v_res_1513_;
}
}
LEAN_EXPORT lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object* v_env_1514_, lean_object* v_opts_1515_, lean_object* v_ns_1516_, lean_object* v_openDecls_1517_, lean_object* v_id_1518_){
_start:
{
lean_object* v_extractionResult_1519_; lean_object* v_name_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; 
v_extractionResult_1519_ = l_Lean_extractMacroScopes(v_id_1518_);
v_name_1520_ = lean_ctor_get(v_extractionResult_1519_, 0);
lean_inc(v_name_1520_);
v___x_1521_ = lean_box(0);
v___x_1522_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop(v_env_1514_, v_opts_1515_, v_ns_1516_, v_openDecls_1517_, v_extractionResult_1519_, v_name_1520_, v___x_1521_);
lean_dec_ref(v_extractionResult_1519_);
return v___x_1522_;
}
}
LEAN_EXPORT lean_object* l_Lean_ResolveName_resolveGlobalName___boxed(lean_object* v_env_1523_, lean_object* v_opts_1524_, lean_object* v_ns_1525_, lean_object* v_openDecls_1526_, lean_object* v_id_1527_){
_start:
{
lean_object* v_res_1528_; 
v_res_1528_ = l_Lean_ResolveName_resolveGlobalName(v_env_1523_, v_opts_1524_, v_ns_1525_, v_openDecls_1526_, v_id_1527_);
lean_dec_ref(v_opts_1524_);
return v_res_1528_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_ResolveName_resolveNamespaceUsingScope_x3f_spec__0(lean_object* v_msg_1529_){
_start:
{
lean_object* v___x_1530_; lean_object* v___x_1531_; 
v___x_1530_ = lean_box(0);
v___x_1531_ = lean_panic_fn_borrowed(v___x_1530_, v_msg_1529_);
return v___x_1531_;
}
}
static lean_object* _init_l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__3(void){
_start:
{
lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; 
v___x_1535_ = ((lean_object*)(l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__2));
v___x_1536_ = lean_unsigned_to_nat(9u);
v___x_1537_ = lean_unsigned_to_nat(230u);
v___x_1538_ = ((lean_object*)(l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__1));
v___x_1539_ = ((lean_object*)(l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__0));
v___x_1540_ = l_mkPanicMessageWithDecl(v___x_1539_, v___x_1538_, v___x_1537_, v___x_1536_, v___x_1535_);
return v___x_1540_;
}
}
LEAN_EXPORT lean_object* l_Lean_ResolveName_resolveNamespaceUsingScope_x3f(lean_object* v_env_1541_, lean_object* v_n_1542_, lean_object* v_ns_1543_){
_start:
{
switch(lean_obj_tag(v_ns_1543_))
{
case 1:
{
lean_object* v_pre_1544_; lean_object* v___x_1545_; uint8_t v___x_1546_; 
v_pre_1544_ = lean_ctor_get(v_ns_1543_, 0);
lean_inc(v_pre_1544_);
lean_inc(v_n_1542_);
v___x_1545_ = l_Lean_Name_append(v_ns_1543_, v_n_1542_);
lean_inc_ref(v_env_1541_);
v___x_1546_ = l_Lean_Environment_isNamespace(v_env_1541_, v___x_1545_);
if (v___x_1546_ == 0)
{
lean_dec(v___x_1545_);
v_ns_1543_ = v_pre_1544_;
goto _start;
}
else
{
lean_object* v___x_1548_; 
lean_dec(v_pre_1544_);
lean_dec(v_n_1542_);
lean_dec_ref(v_env_1541_);
v___x_1548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1548_, 0, v___x_1545_);
return v___x_1548_;
}
}
case 0:
{
lean_object* v___x_1549_; lean_object* v_n_1550_; uint8_t v___x_1551_; 
v___x_1549_ = l_Lean_rootNamespace;
v_n_1550_ = l_Lean_Name_replacePrefix(v_n_1542_, v___x_1549_, v_ns_1543_);
v___x_1551_ = l_Lean_Environment_isNamespace(v_env_1541_, v_n_1550_);
if (v___x_1551_ == 0)
{
lean_object* v___x_1552_; 
lean_dec(v_n_1550_);
v___x_1552_ = lean_box(0);
return v___x_1552_;
}
else
{
lean_object* v___x_1553_; 
v___x_1553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1553_, 0, v_n_1550_);
return v___x_1553_;
}
}
default: 
{
lean_object* v___x_1554_; lean_object* v___x_1555_; 
lean_dec(v_ns_1543_);
lean_dec(v_n_1542_);
lean_dec_ref(v_env_1541_);
v___x_1554_ = lean_obj_once(&l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__3, &l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__3_once, _init_l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__3);
v___x_1555_ = l_panic___at___00Lean_ResolveName_resolveNamespaceUsingScope_x3f_spec__0(v___x_1554_);
return v___x_1555_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ResolveName_resolveNamespaceUsingOpenDecls(lean_object* v_env_1556_, lean_object* v_n_1557_, lean_object* v_x_1558_){
_start:
{
if (lean_obj_tag(v_x_1558_) == 0)
{
lean_object* v___x_1559_; 
lean_dec(v_n_1557_);
lean_dec_ref(v_env_1556_);
v___x_1559_ = lean_box(0);
return v___x_1559_;
}
else
{
lean_object* v_head_1560_; 
v_head_1560_ = lean_ctor_get(v_x_1558_, 0);
if (lean_obj_tag(v_head_1560_) == 0)
{
lean_object* v_tail_1561_; lean_object* v___x_1563_; uint8_t v_isShared_1564_; uint8_t v_isSharedCheck_1578_; 
lean_inc_ref(v_head_1560_);
v_tail_1561_ = lean_ctor_get(v_x_1558_, 1);
v_isSharedCheck_1578_ = !lean_is_exclusive(v_x_1558_);
if (v_isSharedCheck_1578_ == 0)
{
lean_object* v_unused_1579_; 
v_unused_1579_ = lean_ctor_get(v_x_1558_, 0);
lean_dec(v_unused_1579_);
v___x_1563_ = v_x_1558_;
v_isShared_1564_ = v_isSharedCheck_1578_;
goto v_resetjp_1562_;
}
else
{
lean_inc(v_tail_1561_);
lean_dec(v_x_1558_);
v___x_1563_ = lean_box(0);
v_isShared_1564_ = v_isSharedCheck_1578_;
goto v_resetjp_1562_;
}
v_resetjp_1562_:
{
lean_object* v_ns_1565_; lean_object* v_except_1566_; lean_object* v___x_1567_; uint8_t v___y_1569_; uint8_t v___x_1575_; 
v_ns_1565_ = lean_ctor_get(v_head_1560_, 0);
lean_inc(v_ns_1565_);
v_except_1566_ = lean_ctor_get(v_head_1560_, 1);
lean_inc(v_except_1566_);
lean_dec_ref_known(v_head_1560_, 2);
lean_inc(v_n_1557_);
v___x_1567_ = l_Lean_Name_append(v_ns_1565_, v_n_1557_);
lean_inc_ref(v_env_1556_);
v___x_1575_ = l_Lean_Environment_isNamespace(v_env_1556_, v___x_1567_);
if (v___x_1575_ == 0)
{
lean_dec(v_except_1566_);
v___y_1569_ = v___x_1575_;
goto v___jp_1568_;
}
else
{
uint8_t v___x_1576_; 
v___x_1576_ = l_List_elem___at___00Lean_addAliasEntry_spec__2(v_n_1557_, v_except_1566_);
lean_dec(v_except_1566_);
if (v___x_1576_ == 0)
{
v___y_1569_ = v___x_1575_;
goto v___jp_1568_;
}
else
{
lean_dec(v___x_1567_);
lean_del_object(v___x_1563_);
v_x_1558_ = v_tail_1561_;
goto _start;
}
}
v___jp_1568_:
{
if (v___y_1569_ == 0)
{
lean_dec(v___x_1567_);
lean_del_object(v___x_1563_);
v_x_1558_ = v_tail_1561_;
goto _start;
}
else
{
lean_object* v___x_1571_; lean_object* v___x_1573_; 
v___x_1571_ = l_Lean_ResolveName_resolveNamespaceUsingOpenDecls(v_env_1556_, v_n_1557_, v_tail_1561_);
if (v_isShared_1564_ == 0)
{
lean_ctor_set(v___x_1563_, 1, v___x_1571_);
lean_ctor_set(v___x_1563_, 0, v___x_1567_);
v___x_1573_ = v___x_1563_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1574_; 
v_reuseFailAlloc_1574_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1574_, 0, v___x_1567_);
lean_ctor_set(v_reuseFailAlloc_1574_, 1, v___x_1571_);
v___x_1573_ = v_reuseFailAlloc_1574_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
return v___x_1573_;
}
}
}
}
}
else
{
lean_object* v_tail_1580_; 
v_tail_1580_ = lean_ctor_get(v_x_1558_, 1);
lean_inc(v_tail_1580_);
lean_dec_ref_known(v_x_1558_, 2);
v_x_1558_ = v_tail_1580_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ResolveName_resolveNamespace(lean_object* v_env_1582_, lean_object* v_ns_1583_, lean_object* v_openDecls_1584_, lean_object* v_id_1585_){
_start:
{
lean_object* v___x_1586_; 
lean_inc(v_id_1585_);
lean_inc_ref(v_env_1582_);
v___x_1586_ = l_Lean_ResolveName_resolveNamespaceUsingScope_x3f(v_env_1582_, v_id_1585_, v_ns_1583_);
if (lean_obj_tag(v___x_1586_) == 0)
{
lean_object* v___x_1587_; 
v___x_1587_ = l_Lean_ResolveName_resolveNamespaceUsingOpenDecls(v_env_1582_, v_id_1585_, v_openDecls_1584_);
return v___x_1587_;
}
else
{
lean_object* v_val_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; 
v_val_1588_ = lean_ctor_get(v___x_1586_, 0);
lean_inc(v_val_1588_);
lean_dec_ref_known(v___x_1586_, 1);
v___x_1589_ = l_Lean_ResolveName_resolveNamespaceUsingOpenDecls(v_env_1582_, v_id_1585_, v_openDecls_1584_);
v___x_1590_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1590_, 0, v_val_1588_);
lean_ctor_set(v___x_1590_, 1, v___x_1589_);
return v___x_1590_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadResolveNameOfMonadLift___redArg(lean_object* v_inst_1591_, lean_object* v_inst_1592_){
_start:
{
lean_object* v_getCurrNamespace_1593_; lean_object* v_getOpenDecls_1594_; lean_object* v___x_1596_; uint8_t v_isShared_1597_; uint8_t v_isSharedCheck_1603_; 
v_getCurrNamespace_1593_ = lean_ctor_get(v_inst_1592_, 0);
v_getOpenDecls_1594_ = lean_ctor_get(v_inst_1592_, 1);
v_isSharedCheck_1603_ = !lean_is_exclusive(v_inst_1592_);
if (v_isSharedCheck_1603_ == 0)
{
v___x_1596_ = v_inst_1592_;
v_isShared_1597_ = v_isSharedCheck_1603_;
goto v_resetjp_1595_;
}
else
{
lean_inc(v_getOpenDecls_1594_);
lean_inc(v_getCurrNamespace_1593_);
lean_dec(v_inst_1592_);
v___x_1596_ = lean_box(0);
v_isShared_1597_ = v_isSharedCheck_1603_;
goto v_resetjp_1595_;
}
v_resetjp_1595_:
{
lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1601_; 
lean_inc(v_inst_1591_);
v___x_1598_ = lean_apply_2(v_inst_1591_, lean_box(0), v_getCurrNamespace_1593_);
v___x_1599_ = lean_apply_2(v_inst_1591_, lean_box(0), v_getOpenDecls_1594_);
if (v_isShared_1597_ == 0)
{
lean_ctor_set(v___x_1596_, 1, v___x_1599_);
lean_ctor_set(v___x_1596_, 0, v___x_1598_);
v___x_1601_ = v___x_1596_;
goto v_reusejp_1600_;
}
else
{
lean_object* v_reuseFailAlloc_1602_; 
v_reuseFailAlloc_1602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1602_, 0, v___x_1598_);
lean_ctor_set(v_reuseFailAlloc_1602_, 1, v___x_1599_);
v___x_1601_ = v_reuseFailAlloc_1602_;
goto v_reusejp_1600_;
}
v_reusejp_1600_:
{
return v___x_1601_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadResolveNameOfMonadLift(lean_object* v_m_1604_, lean_object* v_n_1605_, lean_object* v_inst_1606_, lean_object* v_inst_1607_){
_start:
{
lean_object* v___x_1608_; 
v___x_1608_ = l_Lean_instMonadResolveNameOfMonadLift___redArg(v_inst_1606_, v_inst_1607_);
return v___x_1608_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1610_; lean_object* v___x_1611_; 
v___x_1610_ = ((lean_object*)(l_Lean_checkPrivateInPublic___redArg___lam__0___closed__0));
v___x_1611_ = l_Lean_stringToMessageData(v___x_1610_);
return v___x_1611_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1613_; lean_object* v___x_1614_; 
v___x_1613_ = ((lean_object*)(l_Lean_checkPrivateInPublic___redArg___lam__0___closed__2));
v___x_1614_ = l_Lean_stringToMessageData(v___x_1613_);
return v___x_1614_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___redArg___lam__0(lean_object* v_____do__lift_1615_, lean_object* v_toApplicative_1616_, lean_object* v_id_1617_, lean_object* v_inst_1618_, lean_object* v_inst_1619_, lean_object* v_inst_1620_, lean_object* v_inst_1621_, uint8_t v_____do__lift_1622_){
_start:
{
uint8_t v_isExporting_1627_; 
v_isExporting_1627_ = lean_ctor_get_uint8(v_____do__lift_1615_, sizeof(void*)*8);
if (v_isExporting_1627_ == 0)
{
lean_dec(v_inst_1621_);
lean_dec(v_inst_1620_);
lean_dec_ref(v_inst_1619_);
lean_dec_ref(v_inst_1618_);
lean_dec(v_id_1617_);
goto v___jp_1623_;
}
else
{
uint8_t v___x_1628_; 
v___x_1628_ = l_Lean_isPrivateName(v_id_1617_);
if (v___x_1628_ == 0)
{
lean_dec(v_inst_1621_);
lean_dec(v_inst_1620_);
lean_dec_ref(v_inst_1619_);
lean_dec_ref(v_inst_1618_);
lean_dec(v_id_1617_);
goto v___jp_1623_;
}
else
{
if (v_____do__lift_1622_ == 0)
{
lean_dec(v_inst_1621_);
lean_dec(v_inst_1620_);
lean_dec_ref(v_inst_1619_);
lean_dec_ref(v_inst_1618_);
lean_dec(v_id_1617_);
goto v___jp_1623_;
}
else
{
lean_object* v___x_1629_; uint8_t v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; 
lean_dec_ref(v_toApplicative_1616_);
v___x_1629_ = lean_obj_once(&l_Lean_checkPrivateInPublic___redArg___lam__0___closed__1, &l_Lean_checkPrivateInPublic___redArg___lam__0___closed__1_once, _init_l_Lean_checkPrivateInPublic___redArg___lam__0___closed__1);
v___x_1630_ = 0;
v___x_1631_ = l_Lean_MessageData_ofConstName(v_id_1617_, v___x_1630_);
v___x_1632_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1632_, 0, v___x_1629_);
lean_ctor_set(v___x_1632_, 1, v___x_1631_);
v___x_1633_ = lean_obj_once(&l_Lean_checkPrivateInPublic___redArg___lam__0___closed__3, &l_Lean_checkPrivateInPublic___redArg___lam__0___closed__3_once, _init_l_Lean_checkPrivateInPublic___redArg___lam__0___closed__3);
v___x_1634_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1634_, 0, v___x_1632_);
lean_ctor_set(v___x_1634_, 1, v___x_1633_);
v___x_1635_ = l_Lean_logWarning___redArg(v_inst_1618_, v_inst_1619_, v_inst_1620_, v_inst_1621_, v___x_1634_);
return v___x_1635_;
}
}
}
v___jp_1623_:
{
lean_object* v_toPure_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; 
v_toPure_1624_ = lean_ctor_get(v_toApplicative_1616_, 1);
lean_inc(v_toPure_1624_);
lean_dec_ref(v_toApplicative_1616_);
v___x_1625_ = lean_box(0);
v___x_1626_ = lean_apply_2(v_toPure_1624_, lean_box(0), v___x_1625_);
return v___x_1626_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___redArg___lam__0___boxed(lean_object* v_____do__lift_1636_, lean_object* v_toApplicative_1637_, lean_object* v_id_1638_, lean_object* v_inst_1639_, lean_object* v_inst_1640_, lean_object* v_inst_1641_, lean_object* v_inst_1642_, lean_object* v_____do__lift_1643_){
_start:
{
uint8_t v_____do__lift_231__boxed_1644_; lean_object* v_res_1645_; 
v_____do__lift_231__boxed_1644_ = lean_unbox(v_____do__lift_1643_);
v_res_1645_ = l_Lean_checkPrivateInPublic___redArg___lam__0(v_____do__lift_1636_, v_toApplicative_1637_, v_id_1638_, v_inst_1639_, v_inst_1640_, v_inst_1641_, v_inst_1642_, v_____do__lift_231__boxed_1644_);
lean_dec_ref(v_____do__lift_1636_);
return v_res_1645_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___redArg___lam__1(lean_object* v_toApplicative_1646_, lean_object* v_id_1647_, lean_object* v_inst_1648_, lean_object* v_inst_1649_, lean_object* v_inst_1650_, lean_object* v_inst_1651_, lean_object* v___x_1652_, lean_object* v_toBind_1653_, lean_object* v_____do__lift_1654_){
_start:
{
lean_object* v___f_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; 
lean_inc(v_inst_1651_);
lean_inc_ref(v_inst_1648_);
v___f_1655_ = lean_alloc_closure((void*)(l_Lean_checkPrivateInPublic___redArg___lam__0___boxed), 8, 7);
lean_closure_set(v___f_1655_, 0, v_____do__lift_1654_);
lean_closure_set(v___f_1655_, 1, v_toApplicative_1646_);
lean_closure_set(v___f_1655_, 2, v_id_1647_);
lean_closure_set(v___f_1655_, 3, v_inst_1648_);
lean_closure_set(v___f_1655_, 4, v_inst_1649_);
lean_closure_set(v___f_1655_, 5, v_inst_1650_);
lean_closure_set(v___f_1655_, 6, v_inst_1651_);
v___x_1656_ = l_Lean_ResolveName_backward_privateInPublic_warn;
v___x_1657_ = l_Lean_Option_getM___redArg(v_inst_1648_, v_inst_1651_, v___x_1652_, v___x_1656_);
v___x_1658_ = lean_apply_4(v_toBind_1653_, lean_box(0), lean_box(0), v___x_1657_, v___f_1655_);
return v___x_1658_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___redArg(lean_object* v_inst_1659_, lean_object* v_inst_1660_, lean_object* v_inst_1661_, lean_object* v_inst_1662_, lean_object* v_inst_1663_, lean_object* v_id_1664_){
_start:
{
lean_object* v___x_1665_; lean_object* v_toApplicative_1666_; lean_object* v_toBind_1667_; lean_object* v_getEnv_1668_; lean_object* v___f_1669_; lean_object* v___x_1670_; 
v___x_1665_ = l_Lean_KVMap_instValueBool;
v_toApplicative_1666_ = lean_ctor_get(v_inst_1659_, 0);
lean_inc_ref(v_toApplicative_1666_);
v_toBind_1667_ = lean_ctor_get(v_inst_1659_, 1);
lean_inc_n(v_toBind_1667_, 2);
v_getEnv_1668_ = lean_ctor_get(v_inst_1660_, 0);
lean_inc(v_getEnv_1668_);
lean_dec_ref(v_inst_1660_);
v___f_1669_ = lean_alloc_closure((void*)(l_Lean_checkPrivateInPublic___redArg___lam__1), 9, 8);
lean_closure_set(v___f_1669_, 0, v_toApplicative_1666_);
lean_closure_set(v___f_1669_, 1, v_id_1664_);
lean_closure_set(v___f_1669_, 2, v_inst_1659_);
lean_closure_set(v___f_1669_, 3, v_inst_1662_);
lean_closure_set(v___f_1669_, 4, v_inst_1663_);
lean_closure_set(v___f_1669_, 5, v_inst_1661_);
lean_closure_set(v___f_1669_, 6, v___x_1665_);
lean_closure_set(v___f_1669_, 7, v_toBind_1667_);
v___x_1670_ = lean_apply_4(v_toBind_1667_, lean_box(0), lean_box(0), v_getEnv_1668_, v___f_1669_);
return v___x_1670_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic(lean_object* v_m_1671_, lean_object* v_inst_1672_, lean_object* v_inst_1673_, lean_object* v_inst_1674_, lean_object* v_inst_1675_, lean_object* v_inst_1676_, lean_object* v_id_1677_){
_start:
{
lean_object* v___x_1678_; 
v___x_1678_ = l_Lean_checkPrivateInPublic___redArg(v_inst_1672_, v_inst_1673_, v_inst_1674_, v_inst_1675_, v_inst_1676_, v_id_1677_);
return v___x_1678_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg___lam__0(lean_object* v_env_1679_, lean_object* v_n_1680_, lean_object* v_toApplicative_1681_, uint8_t v___y_1682_, uint8_t v___x_1683_, lean_object* v_____r_1684_){
_start:
{
lean_object* v___x_1685_; 
v___x_1685_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1679_, v_n_1680_);
if (lean_obj_tag(v___x_1685_) == 0)
{
lean_object* v_toPure_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; 
v_toPure_1686_ = lean_ctor_get(v_toApplicative_1681_, 1);
lean_inc(v_toPure_1686_);
lean_dec_ref(v_toApplicative_1681_);
v___x_1687_ = lean_box(v___y_1682_);
v___x_1688_ = lean_apply_2(v_toPure_1686_, lean_box(0), v___x_1687_);
return v___x_1688_;
}
else
{
lean_object* v_val_1689_; lean_object* v_toPure_1690_; lean_object* v___x_1691_; uint8_t v_isModule_1692_; 
v_val_1689_ = lean_ctor_get(v___x_1685_, 0);
lean_inc(v_val_1689_);
lean_dec_ref_known(v___x_1685_, 1);
v_toPure_1690_ = lean_ctor_get(v_toApplicative_1681_, 1);
lean_inc(v_toPure_1690_);
lean_dec_ref(v_toApplicative_1681_);
v___x_1691_ = l_Lean_Environment_header(v_env_1679_);
v_isModule_1692_ = lean_ctor_get_uint8(v___x_1691_, sizeof(void*)*7 + 4);
if (v_isModule_1692_ == 0)
{
lean_object* v___x_1693_; lean_object* v___x_1694_; 
lean_dec_ref(v___x_1691_);
lean_dec(v_val_1689_);
v___x_1693_ = lean_box(v___x_1683_);
v___x_1694_ = lean_apply_2(v_toPure_1690_, lean_box(0), v___x_1693_);
return v___x_1694_;
}
else
{
lean_object* v_modules_1695_; lean_object* v___x_1696_; uint8_t v___x_1697_; 
v_modules_1695_ = lean_ctor_get(v___x_1691_, 3);
lean_inc_ref(v_modules_1695_);
lean_dec_ref(v___x_1691_);
v___x_1696_ = lean_array_get_size(v_modules_1695_);
v___x_1697_ = lean_nat_dec_lt(v_val_1689_, v___x_1696_);
if (v___x_1697_ == 0)
{
lean_object* v___x_1698_; lean_object* v___x_1699_; 
lean_dec_ref(v_modules_1695_);
lean_dec(v_val_1689_);
v___x_1698_ = lean_box(v_isModule_1692_);
v___x_1699_ = lean_apply_2(v_toPure_1690_, lean_box(0), v___x_1698_);
return v___x_1699_;
}
else
{
lean_object* v___x_1700_; lean_object* v_toImport_1701_; uint8_t v_importAll_1702_; 
v___x_1700_ = lean_array_fget(v_modules_1695_, v_val_1689_);
lean_dec(v_val_1689_);
lean_dec_ref(v_modules_1695_);
v_toImport_1701_ = lean_ctor_get(v___x_1700_, 0);
lean_inc_ref(v_toImport_1701_);
lean_dec(v___x_1700_);
v_importAll_1702_ = lean_ctor_get_uint8(v_toImport_1701_, sizeof(void*)*1);
lean_dec_ref(v_toImport_1701_);
if (v_importAll_1702_ == 0)
{
lean_object* v___x_1703_; lean_object* v___x_1704_; 
v___x_1703_ = lean_box(v_isModule_1692_);
v___x_1704_ = lean_apply_2(v_toPure_1690_, lean_box(0), v___x_1703_);
return v___x_1704_;
}
else
{
lean_object* v___x_1705_; lean_object* v___x_1706_; 
v___x_1705_ = lean_box(v___y_1682_);
v___x_1706_ = lean_apply_2(v_toPure_1690_, lean_box(0), v___x_1705_);
return v___x_1706_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg___lam__0___boxed(lean_object* v_env_1707_, lean_object* v_n_1708_, lean_object* v_toApplicative_1709_, lean_object* v___y_1710_, lean_object* v___x_1711_, lean_object* v_____r_1712_){
_start:
{
uint8_t v___y_758__boxed_1713_; uint8_t v___x_759__boxed_1714_; lean_object* v_res_1715_; 
v___y_758__boxed_1713_ = lean_unbox(v___y_1710_);
v___x_759__boxed_1714_ = lean_unbox(v___x_1711_);
v_res_1715_ = l_Lean_isInaccessiblePrivateName___redArg___lam__0(v_env_1707_, v_n_1708_, v_toApplicative_1709_, v___y_758__boxed_1713_, v___x_759__boxed_1714_, v_____r_1712_);
lean_dec(v_n_1708_);
lean_dec_ref(v_env_1707_);
return v_res_1715_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg___lam__1(lean_object* v_env_1716_, lean_object* v_n_1717_, lean_object* v_toApplicative_1718_, uint8_t v___x_1719_, lean_object* v_inst_1720_, lean_object* v_inst_1721_, lean_object* v_inst_1722_, lean_object* v_inst_1723_, lean_object* v_inst_1724_, lean_object* v_toBind_1725_, uint8_t v___x_1726_, uint8_t v_____do__lift_1727_){
_start:
{
uint8_t v___y_1729_; uint8_t v_isExporting_1735_; 
v_isExporting_1735_ = lean_ctor_get_uint8(v_env_1716_, sizeof(void*)*8);
if (v_isExporting_1735_ == 0)
{
v___y_1729_ = v_isExporting_1735_;
goto v___jp_1728_;
}
else
{
if (v_____do__lift_1727_ == 0)
{
lean_object* v_toPure_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; 
lean_dec(v_toBind_1725_);
lean_dec(v_inst_1724_);
lean_dec_ref(v_inst_1723_);
lean_dec(v_inst_1722_);
lean_dec_ref(v_inst_1721_);
lean_dec_ref(v_inst_1720_);
lean_dec(v_n_1717_);
lean_dec_ref(v_env_1716_);
v_toPure_1736_ = lean_ctor_get(v_toApplicative_1718_, 1);
lean_inc(v_toPure_1736_);
lean_dec_ref(v_toApplicative_1718_);
v___x_1737_ = lean_box(v___x_1719_);
v___x_1738_ = lean_apply_2(v_toPure_1736_, lean_box(0), v___x_1737_);
return v___x_1738_;
}
else
{
v___y_1729_ = v___x_1726_;
goto v___jp_1728_;
}
}
v___jp_1728_:
{
lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___f_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; 
v___x_1730_ = lean_box(v___y_1729_);
v___x_1731_ = lean_box(v___x_1719_);
lean_inc(v_n_1717_);
v___f_1732_ = lean_alloc_closure((void*)(l_Lean_isInaccessiblePrivateName___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1732_, 0, v_env_1716_);
lean_closure_set(v___f_1732_, 1, v_n_1717_);
lean_closure_set(v___f_1732_, 2, v_toApplicative_1718_);
lean_closure_set(v___f_1732_, 3, v___x_1730_);
lean_closure_set(v___f_1732_, 4, v___x_1731_);
v___x_1733_ = l_Lean_checkPrivateInPublic___redArg(v_inst_1720_, v_inst_1721_, v_inst_1722_, v_inst_1723_, v_inst_1724_, v_n_1717_);
v___x_1734_ = lean_apply_4(v_toBind_1725_, lean_box(0), lean_box(0), v___x_1733_, v___f_1732_);
return v___x_1734_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg___lam__1___boxed(lean_object* v_env_1739_, lean_object* v_n_1740_, lean_object* v_toApplicative_1741_, lean_object* v___x_1742_, lean_object* v_inst_1743_, lean_object* v_inst_1744_, lean_object* v_inst_1745_, lean_object* v_inst_1746_, lean_object* v_inst_1747_, lean_object* v_toBind_1748_, lean_object* v___x_1749_, lean_object* v_____do__lift_1750_){
_start:
{
uint8_t v___x_799__boxed_1751_; uint8_t v___x_805__boxed_1752_; uint8_t v_____do__lift_806__boxed_1753_; lean_object* v_res_1754_; 
v___x_799__boxed_1751_ = lean_unbox(v___x_1742_);
v___x_805__boxed_1752_ = lean_unbox(v___x_1749_);
v_____do__lift_806__boxed_1753_ = lean_unbox(v_____do__lift_1750_);
v_res_1754_ = l_Lean_isInaccessiblePrivateName___redArg___lam__1(v_env_1739_, v_n_1740_, v_toApplicative_1741_, v___x_799__boxed_1751_, v_inst_1743_, v_inst_1744_, v_inst_1745_, v_inst_1746_, v_inst_1747_, v_toBind_1748_, v___x_805__boxed_1752_, v_____do__lift_806__boxed_1753_);
return v_res_1754_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg___lam__2(lean_object* v_n_1755_, lean_object* v_toApplicative_1756_, uint8_t v___x_1757_, lean_object* v_inst_1758_, lean_object* v_inst_1759_, lean_object* v_inst_1760_, lean_object* v_inst_1761_, lean_object* v_inst_1762_, lean_object* v_toBind_1763_, uint8_t v___x_1764_, lean_object* v_env_1765_){
_start:
{
lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___f_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; 
v___x_1766_ = lean_box(v___x_1757_);
v___x_1767_ = lean_box(v___x_1764_);
lean_inc(v_toBind_1763_);
lean_inc(v_inst_1760_);
lean_inc_ref(v_inst_1758_);
v___f_1768_ = lean_alloc_closure((void*)(l_Lean_isInaccessiblePrivateName___redArg___lam__1___boxed), 12, 11);
lean_closure_set(v___f_1768_, 0, v_env_1765_);
lean_closure_set(v___f_1768_, 1, v_n_1755_);
lean_closure_set(v___f_1768_, 2, v_toApplicative_1756_);
lean_closure_set(v___f_1768_, 3, v___x_1766_);
lean_closure_set(v___f_1768_, 4, v_inst_1758_);
lean_closure_set(v___f_1768_, 5, v_inst_1759_);
lean_closure_set(v___f_1768_, 6, v_inst_1760_);
lean_closure_set(v___f_1768_, 7, v_inst_1761_);
lean_closure_set(v___f_1768_, 8, v_inst_1762_);
lean_closure_set(v___f_1768_, 9, v_toBind_1763_);
lean_closure_set(v___f_1768_, 10, v___x_1767_);
v___x_1769_ = l_Lean_KVMap_instValueBool;
v___x_1770_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_1771_ = l_Lean_Option_getM___redArg(v_inst_1758_, v_inst_1760_, v___x_1769_, v___x_1770_);
v___x_1772_ = lean_apply_4(v_toBind_1763_, lean_box(0), lean_box(0), v___x_1771_, v___f_1768_);
return v___x_1772_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg___lam__2___boxed(lean_object* v_n_1773_, lean_object* v_toApplicative_1774_, lean_object* v___x_1775_, lean_object* v_inst_1776_, lean_object* v_inst_1777_, lean_object* v_inst_1778_, lean_object* v_inst_1779_, lean_object* v_inst_1780_, lean_object* v_toBind_1781_, lean_object* v___x_1782_, lean_object* v_env_1783_){
_start:
{
uint8_t v___x_841__boxed_1784_; uint8_t v___x_847__boxed_1785_; lean_object* v_res_1786_; 
v___x_841__boxed_1784_ = lean_unbox(v___x_1775_);
v___x_847__boxed_1785_ = lean_unbox(v___x_1782_);
v_res_1786_ = l_Lean_isInaccessiblePrivateName___redArg___lam__2(v_n_1773_, v_toApplicative_1774_, v___x_841__boxed_1784_, v_inst_1776_, v_inst_1777_, v_inst_1778_, v_inst_1779_, v_inst_1780_, v_toBind_1781_, v___x_847__boxed_1785_, v_env_1783_);
return v_res_1786_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg(lean_object* v_inst_1787_, lean_object* v_inst_1788_, lean_object* v_inst_1789_, lean_object* v_inst_1790_, lean_object* v_inst_1791_, lean_object* v_n_1792_){
_start:
{
uint8_t v___x_1793_; 
v___x_1793_ = l_Lean_isPrivateName(v_n_1792_);
if (v___x_1793_ == 0)
{
lean_object* v_toApplicative_1794_; lean_object* v_toPure_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; 
lean_dec(v_n_1792_);
lean_dec(v_inst_1791_);
lean_dec_ref(v_inst_1790_);
lean_dec(v_inst_1788_);
lean_dec_ref(v_inst_1787_);
v_toApplicative_1794_ = lean_ctor_get(v_inst_1789_, 0);
lean_inc_ref(v_toApplicative_1794_);
lean_dec_ref(v_inst_1789_);
v_toPure_1795_ = lean_ctor_get(v_toApplicative_1794_, 1);
lean_inc(v_toPure_1795_);
lean_dec_ref(v_toApplicative_1794_);
v___x_1796_ = lean_box(v___x_1793_);
v___x_1797_ = lean_apply_2(v_toPure_1795_, lean_box(0), v___x_1796_);
return v___x_1797_;
}
else
{
lean_object* v_toApplicative_1798_; lean_object* v_toBind_1799_; lean_object* v_getEnv_1800_; uint8_t v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___f_1804_; lean_object* v___x_1805_; 
v_toApplicative_1798_ = lean_ctor_get(v_inst_1789_, 0);
lean_inc_ref(v_toApplicative_1798_);
v_toBind_1799_ = lean_ctor_get(v_inst_1789_, 1);
lean_inc_n(v_toBind_1799_, 2);
v_getEnv_1800_ = lean_ctor_get(v_inst_1790_, 0);
lean_inc(v_getEnv_1800_);
v___x_1801_ = 0;
v___x_1802_ = lean_box(v___x_1793_);
v___x_1803_ = lean_box(v___x_1801_);
v___f_1804_ = lean_alloc_closure((void*)(l_Lean_isInaccessiblePrivateName___redArg___lam__2___boxed), 11, 10);
lean_closure_set(v___f_1804_, 0, v_n_1792_);
lean_closure_set(v___f_1804_, 1, v_toApplicative_1798_);
lean_closure_set(v___f_1804_, 2, v___x_1802_);
lean_closure_set(v___f_1804_, 3, v_inst_1789_);
lean_closure_set(v___f_1804_, 4, v_inst_1790_);
lean_closure_set(v___f_1804_, 5, v_inst_1791_);
lean_closure_set(v___f_1804_, 6, v_inst_1787_);
lean_closure_set(v___f_1804_, 7, v_inst_1788_);
lean_closure_set(v___f_1804_, 8, v_toBind_1799_);
lean_closure_set(v___f_1804_, 9, v___x_1803_);
v___x_1805_ = lean_apply_4(v_toBind_1799_, lean_box(0), lean_box(0), v_getEnv_1800_, v___f_1804_);
return v___x_1805_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName(lean_object* v_m_1806_, lean_object* v_inst_1807_, lean_object* v_inst_1808_, lean_object* v_inst_1809_, lean_object* v_inst_1810_, lean_object* v_inst_1811_, lean_object* v_n_1812_){
_start:
{
lean_object* v___x_1813_; 
v___x_1813_ = l_Lean_isInaccessiblePrivateName___redArg(v_inst_1807_, v_inst_1808_, v_inst_1809_, v_inst_1810_, v_inst_1811_, v_n_1812_);
return v___x_1813_;
}
}
LEAN_EXPORT uint8_t l_Lean_resolveGlobalName___redArg___lam__0(lean_object* v_x_1814_){
_start:
{
lean_object* v_fst_1815_; uint8_t v___x_1816_; 
v_fst_1815_ = lean_ctor_get(v_x_1814_, 0);
v___x_1816_ = l_Lean_isPrivateName(v_fst_1815_);
return v___x_1816_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__0___boxed(lean_object* v_x_1817_){
_start:
{
uint8_t v_res_1818_; lean_object* v_r_1819_; 
v_res_1818_ = l_Lean_resolveGlobalName___redArg___lam__0(v_x_1817_);
lean_dec_ref(v_x_1817_);
v_r_1819_ = lean_box(v_res_1818_);
return v_r_1819_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__1(lean_object* v_toPure_1820_, lean_object* v_res_1821_, lean_object* v_____r_1822_){
_start:
{
lean_object* v___x_1823_; 
v___x_1823_ = lean_apply_2(v_toPure_1820_, lean_box(0), v_res_1821_);
return v___x_1823_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__2(uint8_t v_enableLog_1824_, lean_object* v_toPure_1825_, lean_object* v_res_1826_, lean_object* v___f_1827_, lean_object* v_inst_1828_, lean_object* v_inst_1829_, lean_object* v_inst_1830_, lean_object* v_inst_1831_, lean_object* v_inst_1832_, lean_object* v_toBind_1833_, lean_object* v___f_1834_, lean_object* v_____do__lift_1835_){
_start:
{
if (v_enableLog_1824_ == 0)
{
lean_object* v___x_1836_; 
lean_dec(v___f_1834_);
lean_dec(v_toBind_1833_);
lean_dec(v_inst_1832_);
lean_dec_ref(v_inst_1831_);
lean_dec(v_inst_1830_);
lean_dec_ref(v_inst_1829_);
lean_dec_ref(v_inst_1828_);
lean_dec_ref(v___f_1827_);
v___x_1836_ = lean_apply_2(v_toPure_1825_, lean_box(0), v_res_1826_);
return v___x_1836_;
}
else
{
uint8_t v_isExporting_1837_; 
v_isExporting_1837_ = lean_ctor_get_uint8(v_____do__lift_1835_, sizeof(void*)*8);
if (v_isExporting_1837_ == 0)
{
lean_object* v___x_1838_; 
lean_dec(v___f_1834_);
lean_dec(v_toBind_1833_);
lean_dec(v_inst_1832_);
lean_dec_ref(v_inst_1831_);
lean_dec(v_inst_1830_);
lean_dec_ref(v_inst_1829_);
lean_dec_ref(v_inst_1828_);
lean_dec_ref(v___f_1827_);
v___x_1838_ = lean_apply_2(v_toPure_1825_, lean_box(0), v_res_1826_);
return v___x_1838_;
}
else
{
lean_object* v___x_1839_; 
lean_inc(v_res_1826_);
v___x_1839_ = l_List_find_x3f___redArg(v___f_1827_, v_res_1826_);
if (lean_obj_tag(v___x_1839_) == 1)
{
lean_object* v_val_1840_; lean_object* v_fst_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; 
lean_dec(v_res_1826_);
lean_dec(v_toPure_1825_);
v_val_1840_ = lean_ctor_get(v___x_1839_, 0);
lean_inc(v_val_1840_);
lean_dec_ref_known(v___x_1839_, 1);
v_fst_1841_ = lean_ctor_get(v_val_1840_, 0);
lean_inc(v_fst_1841_);
lean_dec(v_val_1840_);
v___x_1842_ = l_Lean_checkPrivateInPublic___redArg(v_inst_1828_, v_inst_1829_, v_inst_1830_, v_inst_1831_, v_inst_1832_, v_fst_1841_);
v___x_1843_ = lean_apply_4(v_toBind_1833_, lean_box(0), lean_box(0), v___x_1842_, v___f_1834_);
return v___x_1843_;
}
else
{
lean_object* v___x_1844_; 
lean_dec(v___x_1839_);
lean_dec(v___f_1834_);
lean_dec(v_toBind_1833_);
lean_dec(v_inst_1832_);
lean_dec_ref(v_inst_1831_);
lean_dec(v_inst_1830_);
lean_dec_ref(v_inst_1829_);
lean_dec_ref(v_inst_1828_);
v___x_1844_ = lean_apply_2(v_toPure_1825_, lean_box(0), v_res_1826_);
return v___x_1844_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__2___boxed(lean_object* v_enableLog_1845_, lean_object* v_toPure_1846_, lean_object* v_res_1847_, lean_object* v___f_1848_, lean_object* v_inst_1849_, lean_object* v_inst_1850_, lean_object* v_inst_1851_, lean_object* v_inst_1852_, lean_object* v_inst_1853_, lean_object* v_toBind_1854_, lean_object* v___f_1855_, lean_object* v_____do__lift_1856_){
_start:
{
uint8_t v_enableLog_boxed_1857_; lean_object* v_res_1858_; 
v_enableLog_boxed_1857_ = lean_unbox(v_enableLog_1845_);
v_res_1858_ = l_Lean_resolveGlobalName___redArg___lam__2(v_enableLog_boxed_1857_, v_toPure_1846_, v_res_1847_, v___f_1848_, v_inst_1849_, v_inst_1850_, v_inst_1851_, v_inst_1852_, v_inst_1853_, v_toBind_1854_, v___f_1855_, v_____do__lift_1856_);
lean_dec_ref(v_____do__lift_1856_);
return v_res_1858_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__3(lean_object* v_____do__lift_1859_, lean_object* v_____do__lift_1860_, lean_object* v_____do__lift_1861_, lean_object* v_id_1862_, lean_object* v_toPure_1863_, uint8_t v_enableLog_1864_, lean_object* v___f_1865_, lean_object* v_inst_1866_, lean_object* v_inst_1867_, lean_object* v_inst_1868_, lean_object* v_inst_1869_, lean_object* v_inst_1870_, lean_object* v_toBind_1871_, lean_object* v_getEnv_1872_, lean_object* v_____do__lift_1873_){
_start:
{
lean_object* v_res_1874_; lean_object* v___f_1875_; lean_object* v___x_1876_; lean_object* v___f_1877_; lean_object* v___x_1878_; 
v_res_1874_ = l_Lean_ResolveName_resolveGlobalName(v_____do__lift_1859_, v_____do__lift_1860_, v_____do__lift_1861_, v_____do__lift_1873_, v_id_1862_);
lean_inc(v_res_1874_);
lean_inc(v_toPure_1863_);
v___f_1875_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalName___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1875_, 0, v_toPure_1863_);
lean_closure_set(v___f_1875_, 1, v_res_1874_);
v___x_1876_ = lean_box(v_enableLog_1864_);
lean_inc(v_toBind_1871_);
v___f_1877_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalName___redArg___lam__2___boxed), 12, 11);
lean_closure_set(v___f_1877_, 0, v___x_1876_);
lean_closure_set(v___f_1877_, 1, v_toPure_1863_);
lean_closure_set(v___f_1877_, 2, v_res_1874_);
lean_closure_set(v___f_1877_, 3, v___f_1865_);
lean_closure_set(v___f_1877_, 4, v_inst_1866_);
lean_closure_set(v___f_1877_, 5, v_inst_1867_);
lean_closure_set(v___f_1877_, 6, v_inst_1868_);
lean_closure_set(v___f_1877_, 7, v_inst_1869_);
lean_closure_set(v___f_1877_, 8, v_inst_1870_);
lean_closure_set(v___f_1877_, 9, v_toBind_1871_);
lean_closure_set(v___f_1877_, 10, v___f_1875_);
v___x_1878_ = lean_apply_4(v_toBind_1871_, lean_box(0), lean_box(0), v_getEnv_1872_, v___f_1877_);
return v___x_1878_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__3___boxed(lean_object* v_____do__lift_1879_, lean_object* v_____do__lift_1880_, lean_object* v_____do__lift_1881_, lean_object* v_id_1882_, lean_object* v_toPure_1883_, lean_object* v_enableLog_1884_, lean_object* v___f_1885_, lean_object* v_inst_1886_, lean_object* v_inst_1887_, lean_object* v_inst_1888_, lean_object* v_inst_1889_, lean_object* v_inst_1890_, lean_object* v_toBind_1891_, lean_object* v_getEnv_1892_, lean_object* v_____do__lift_1893_){
_start:
{
uint8_t v_enableLog_boxed_1894_; lean_object* v_res_1895_; 
v_enableLog_boxed_1894_ = lean_unbox(v_enableLog_1884_);
v_res_1895_ = l_Lean_resolveGlobalName___redArg___lam__3(v_____do__lift_1879_, v_____do__lift_1880_, v_____do__lift_1881_, v_id_1882_, v_toPure_1883_, v_enableLog_boxed_1894_, v___f_1885_, v_inst_1886_, v_inst_1887_, v_inst_1888_, v_inst_1889_, v_inst_1890_, v_toBind_1891_, v_getEnv_1892_, v_____do__lift_1893_);
lean_dec_ref(v_____do__lift_1880_);
return v_res_1895_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__4(lean_object* v_____do__lift_1896_, lean_object* v_____do__lift_1897_, lean_object* v_id_1898_, lean_object* v_toPure_1899_, uint8_t v_enableLog_1900_, lean_object* v___f_1901_, lean_object* v_inst_1902_, lean_object* v_inst_1903_, lean_object* v_inst_1904_, lean_object* v_inst_1905_, lean_object* v_inst_1906_, lean_object* v_toBind_1907_, lean_object* v_getEnv_1908_, lean_object* v_getOpenDecls_1909_, lean_object* v_____do__lift_1910_){
_start:
{
lean_object* v___x_1911_; lean_object* v___f_1912_; lean_object* v___x_1913_; 
v___x_1911_ = lean_box(v_enableLog_1900_);
lean_inc(v_toBind_1907_);
v___f_1912_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalName___redArg___lam__3___boxed), 15, 14);
lean_closure_set(v___f_1912_, 0, v_____do__lift_1896_);
lean_closure_set(v___f_1912_, 1, v_____do__lift_1897_);
lean_closure_set(v___f_1912_, 2, v_____do__lift_1910_);
lean_closure_set(v___f_1912_, 3, v_id_1898_);
lean_closure_set(v___f_1912_, 4, v_toPure_1899_);
lean_closure_set(v___f_1912_, 5, v___x_1911_);
lean_closure_set(v___f_1912_, 6, v___f_1901_);
lean_closure_set(v___f_1912_, 7, v_inst_1902_);
lean_closure_set(v___f_1912_, 8, v_inst_1903_);
lean_closure_set(v___f_1912_, 9, v_inst_1904_);
lean_closure_set(v___f_1912_, 10, v_inst_1905_);
lean_closure_set(v___f_1912_, 11, v_inst_1906_);
lean_closure_set(v___f_1912_, 12, v_toBind_1907_);
lean_closure_set(v___f_1912_, 13, v_getEnv_1908_);
v___x_1913_ = lean_apply_4(v_toBind_1907_, lean_box(0), lean_box(0), v_getOpenDecls_1909_, v___f_1912_);
return v___x_1913_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__4___boxed(lean_object* v_____do__lift_1914_, lean_object* v_____do__lift_1915_, lean_object* v_id_1916_, lean_object* v_toPure_1917_, lean_object* v_enableLog_1918_, lean_object* v___f_1919_, lean_object* v_inst_1920_, lean_object* v_inst_1921_, lean_object* v_inst_1922_, lean_object* v_inst_1923_, lean_object* v_inst_1924_, lean_object* v_toBind_1925_, lean_object* v_getEnv_1926_, lean_object* v_getOpenDecls_1927_, lean_object* v_____do__lift_1928_){
_start:
{
uint8_t v_enableLog_boxed_1929_; lean_object* v_res_1930_; 
v_enableLog_boxed_1929_ = lean_unbox(v_enableLog_1918_);
v_res_1930_ = l_Lean_resolveGlobalName___redArg___lam__4(v_____do__lift_1914_, v_____do__lift_1915_, v_id_1916_, v_toPure_1917_, v_enableLog_boxed_1929_, v___f_1919_, v_inst_1920_, v_inst_1921_, v_inst_1922_, v_inst_1923_, v_inst_1924_, v_toBind_1925_, v_getEnv_1926_, v_getOpenDecls_1927_, v_____do__lift_1928_);
return v_res_1930_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__5(lean_object* v_inst_1931_, lean_object* v_____do__lift_1932_, lean_object* v_id_1933_, lean_object* v_toPure_1934_, uint8_t v_enableLog_1935_, lean_object* v___f_1936_, lean_object* v_inst_1937_, lean_object* v_inst_1938_, lean_object* v_inst_1939_, lean_object* v_inst_1940_, lean_object* v_inst_1941_, lean_object* v_toBind_1942_, lean_object* v_getEnv_1943_, lean_object* v_____do__lift_1944_){
_start:
{
lean_object* v_getCurrNamespace_1945_; lean_object* v_getOpenDecls_1946_; lean_object* v___x_1947_; lean_object* v___f_1948_; lean_object* v___x_1949_; 
v_getCurrNamespace_1945_ = lean_ctor_get(v_inst_1931_, 0);
lean_inc(v_getCurrNamespace_1945_);
v_getOpenDecls_1946_ = lean_ctor_get(v_inst_1931_, 1);
lean_inc(v_getOpenDecls_1946_);
lean_dec_ref(v_inst_1931_);
v___x_1947_ = lean_box(v_enableLog_1935_);
lean_inc(v_toBind_1942_);
v___f_1948_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalName___redArg___lam__4___boxed), 15, 14);
lean_closure_set(v___f_1948_, 0, v_____do__lift_1932_);
lean_closure_set(v___f_1948_, 1, v_____do__lift_1944_);
lean_closure_set(v___f_1948_, 2, v_id_1933_);
lean_closure_set(v___f_1948_, 3, v_toPure_1934_);
lean_closure_set(v___f_1948_, 4, v___x_1947_);
lean_closure_set(v___f_1948_, 5, v___f_1936_);
lean_closure_set(v___f_1948_, 6, v_inst_1937_);
lean_closure_set(v___f_1948_, 7, v_inst_1938_);
lean_closure_set(v___f_1948_, 8, v_inst_1939_);
lean_closure_set(v___f_1948_, 9, v_inst_1940_);
lean_closure_set(v___f_1948_, 10, v_inst_1941_);
lean_closure_set(v___f_1948_, 11, v_toBind_1942_);
lean_closure_set(v___f_1948_, 12, v_getEnv_1943_);
lean_closure_set(v___f_1948_, 13, v_getOpenDecls_1946_);
v___x_1949_ = lean_apply_4(v_toBind_1942_, lean_box(0), lean_box(0), v_getCurrNamespace_1945_, v___f_1948_);
return v___x_1949_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__5___boxed(lean_object* v_inst_1950_, lean_object* v_____do__lift_1951_, lean_object* v_id_1952_, lean_object* v_toPure_1953_, lean_object* v_enableLog_1954_, lean_object* v___f_1955_, lean_object* v_inst_1956_, lean_object* v_inst_1957_, lean_object* v_inst_1958_, lean_object* v_inst_1959_, lean_object* v_inst_1960_, lean_object* v_toBind_1961_, lean_object* v_getEnv_1962_, lean_object* v_____do__lift_1963_){
_start:
{
uint8_t v_enableLog_boxed_1964_; lean_object* v_res_1965_; 
v_enableLog_boxed_1964_ = lean_unbox(v_enableLog_1954_);
v_res_1965_ = l_Lean_resolveGlobalName___redArg___lam__5(v_inst_1950_, v_____do__lift_1951_, v_id_1952_, v_toPure_1953_, v_enableLog_boxed_1964_, v___f_1955_, v_inst_1956_, v_inst_1957_, v_inst_1958_, v_inst_1959_, v_inst_1960_, v_toBind_1961_, v_getEnv_1962_, v_____do__lift_1963_);
return v_res_1965_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__6(lean_object* v_inst_1966_, lean_object* v_id_1967_, lean_object* v_toPure_1968_, uint8_t v_enableLog_1969_, lean_object* v___f_1970_, lean_object* v_inst_1971_, lean_object* v_inst_1972_, lean_object* v_inst_1973_, lean_object* v_inst_1974_, lean_object* v_inst_1975_, lean_object* v_toBind_1976_, lean_object* v_getEnv_1977_, lean_object* v_____do__lift_1978_){
_start:
{
lean_object* v___x_1979_; lean_object* v___f_1980_; lean_object* v___x_1981_; 
v___x_1979_ = lean_box(v_enableLog_1969_);
lean_inc(v_toBind_1976_);
lean_inc(v_inst_1973_);
v___f_1980_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalName___redArg___lam__5___boxed), 14, 13);
lean_closure_set(v___f_1980_, 0, v_inst_1966_);
lean_closure_set(v___f_1980_, 1, v_____do__lift_1978_);
lean_closure_set(v___f_1980_, 2, v_id_1967_);
lean_closure_set(v___f_1980_, 3, v_toPure_1968_);
lean_closure_set(v___f_1980_, 4, v___x_1979_);
lean_closure_set(v___f_1980_, 5, v___f_1970_);
lean_closure_set(v___f_1980_, 6, v_inst_1971_);
lean_closure_set(v___f_1980_, 7, v_inst_1972_);
lean_closure_set(v___f_1980_, 8, v_inst_1973_);
lean_closure_set(v___f_1980_, 9, v_inst_1974_);
lean_closure_set(v___f_1980_, 10, v_inst_1975_);
lean_closure_set(v___f_1980_, 11, v_toBind_1976_);
lean_closure_set(v___f_1980_, 12, v_getEnv_1977_);
v___x_1981_ = lean_apply_4(v_toBind_1976_, lean_box(0), lean_box(0), v_inst_1973_, v___f_1980_);
return v___x_1981_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__6___boxed(lean_object* v_inst_1982_, lean_object* v_id_1983_, lean_object* v_toPure_1984_, lean_object* v_enableLog_1985_, lean_object* v___f_1986_, lean_object* v_inst_1987_, lean_object* v_inst_1988_, lean_object* v_inst_1989_, lean_object* v_inst_1990_, lean_object* v_inst_1991_, lean_object* v_toBind_1992_, lean_object* v_getEnv_1993_, lean_object* v_____do__lift_1994_){
_start:
{
uint8_t v_enableLog_boxed_1995_; lean_object* v_res_1996_; 
v_enableLog_boxed_1995_ = lean_unbox(v_enableLog_1985_);
v_res_1996_ = l_Lean_resolveGlobalName___redArg___lam__6(v_inst_1982_, v_id_1983_, v_toPure_1984_, v_enableLog_boxed_1995_, v___f_1986_, v_inst_1987_, v_inst_1988_, v_inst_1989_, v_inst_1990_, v_inst_1991_, v_toBind_1992_, v_getEnv_1993_, v_____do__lift_1994_);
return v_res_1996_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg(lean_object* v_inst_1998_, lean_object* v_inst_1999_, lean_object* v_inst_2000_, lean_object* v_inst_2001_, lean_object* v_inst_2002_, lean_object* v_inst_2003_, lean_object* v_id_2004_, uint8_t v_enableLog_2005_){
_start:
{
lean_object* v_toApplicative_2006_; lean_object* v_toBind_2007_; lean_object* v_getEnv_2008_; lean_object* v_toPure_2009_; lean_object* v___f_2010_; lean_object* v___x_2011_; lean_object* v___f_2012_; lean_object* v___x_2013_; 
v_toApplicative_2006_ = lean_ctor_get(v_inst_1998_, 0);
v_toBind_2007_ = lean_ctor_get(v_inst_1998_, 1);
lean_inc_n(v_toBind_2007_, 2);
v_getEnv_2008_ = lean_ctor_get(v_inst_2000_, 0);
lean_inc_n(v_getEnv_2008_, 2);
v_toPure_2009_ = lean_ctor_get(v_toApplicative_2006_, 1);
lean_inc(v_toPure_2009_);
v___f_2010_ = ((lean_object*)(l_Lean_resolveGlobalName___redArg___closed__0));
v___x_2011_ = lean_box(v_enableLog_2005_);
v___f_2012_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalName___redArg___lam__6___boxed), 13, 12);
lean_closure_set(v___f_2012_, 0, v_inst_1999_);
lean_closure_set(v___f_2012_, 1, v_id_2004_);
lean_closure_set(v___f_2012_, 2, v_toPure_2009_);
lean_closure_set(v___f_2012_, 3, v___x_2011_);
lean_closure_set(v___f_2012_, 4, v___f_2010_);
lean_closure_set(v___f_2012_, 5, v_inst_1998_);
lean_closure_set(v___f_2012_, 6, v_inst_2000_);
lean_closure_set(v___f_2012_, 7, v_inst_2001_);
lean_closure_set(v___f_2012_, 8, v_inst_2002_);
lean_closure_set(v___f_2012_, 9, v_inst_2003_);
lean_closure_set(v___f_2012_, 10, v_toBind_2007_);
lean_closure_set(v___f_2012_, 11, v_getEnv_2008_);
v___x_2013_ = lean_apply_4(v_toBind_2007_, lean_box(0), lean_box(0), v_getEnv_2008_, v___f_2012_);
return v___x_2013_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___boxed(lean_object* v_inst_2014_, lean_object* v_inst_2015_, lean_object* v_inst_2016_, lean_object* v_inst_2017_, lean_object* v_inst_2018_, lean_object* v_inst_2019_, lean_object* v_id_2020_, lean_object* v_enableLog_2021_){
_start:
{
uint8_t v_enableLog_boxed_2022_; lean_object* v_res_2023_; 
v_enableLog_boxed_2022_ = lean_unbox(v_enableLog_2021_);
v_res_2023_ = l_Lean_resolveGlobalName___redArg(v_inst_2014_, v_inst_2015_, v_inst_2016_, v_inst_2017_, v_inst_2018_, v_inst_2019_, v_id_2020_, v_enableLog_boxed_2022_);
return v_res_2023_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName(lean_object* v_m_2024_, lean_object* v_inst_2025_, lean_object* v_inst_2026_, lean_object* v_inst_2027_, lean_object* v_inst_2028_, lean_object* v_inst_2029_, lean_object* v_inst_2030_, lean_object* v_id_2031_, uint8_t v_enableLog_2032_){
_start:
{
lean_object* v___x_2033_; 
v___x_2033_ = l_Lean_resolveGlobalName___redArg(v_inst_2025_, v_inst_2026_, v_inst_2027_, v_inst_2028_, v_inst_2029_, v_inst_2030_, v_id_2031_, v_enableLog_2032_);
return v___x_2033_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___boxed(lean_object* v_m_2034_, lean_object* v_inst_2035_, lean_object* v_inst_2036_, lean_object* v_inst_2037_, lean_object* v_inst_2038_, lean_object* v_inst_2039_, lean_object* v_inst_2040_, lean_object* v_id_2041_, lean_object* v_enableLog_2042_){
_start:
{
uint8_t v_enableLog_boxed_2043_; lean_object* v_res_2044_; 
v_enableLog_boxed_2043_ = lean_unbox(v_enableLog_2042_);
v_res_2044_ = l_Lean_resolveGlobalName(v_m_2034_, v_inst_2035_, v_inst_2036_, v_inst_2037_, v_inst_2038_, v_inst_2039_, v_inst_2040_, v_id_2041_, v_enableLog_boxed_2043_);
return v_res_2044_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__0(lean_object* v_toPure_2045_, lean_object* v_nss_2046_, lean_object* v_____r_2047_){
_start:
{
lean_object* v___x_2048_; 
v___x_2048_ = lean_apply_2(v_toPure_2045_, lean_box(0), v_nss_2046_);
return v___x_2048_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__1(lean_object* v_____do__lift_2051_, lean_object* v_____do__lift_2052_, lean_object* v_id_2053_, uint8_t v_allowEmpty_2054_, lean_object* v_toPure_2055_, lean_object* v_inst_2056_, lean_object* v_inst_2057_, lean_object* v_toBind_2058_, lean_object* v_____do__lift_2059_){
_start:
{
lean_object* v_nss_2060_; 
lean_inc(v_id_2053_);
v_nss_2060_ = l_Lean_ResolveName_resolveNamespace(v_____do__lift_2051_, v_____do__lift_2052_, v_____do__lift_2059_, v_id_2053_);
if (v_allowEmpty_2054_ == 0)
{
uint8_t v___x_2061_; 
v___x_2061_ = l_List_isEmpty___redArg(v_nss_2060_);
if (v___x_2061_ == 0)
{
lean_object* v___x_2062_; 
lean_dec(v_toBind_2058_);
lean_dec_ref(v_inst_2057_);
lean_dec_ref(v_inst_2056_);
lean_dec(v_id_2053_);
v___x_2062_ = lean_apply_2(v_toPure_2055_, lean_box(0), v_nss_2060_);
return v___x_2062_;
}
else
{
lean_object* v___f_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; 
v___f_2063_ = lean_alloc_closure((void*)(l_Lean_resolveNamespaceCore___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2063_, 0, v_toPure_2055_);
lean_closure_set(v___f_2063_, 1, v_nss_2060_);
v___x_2064_ = ((lean_object*)(l_Lean_resolveNamespaceCore___redArg___lam__1___closed__0));
v___x_2065_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_id_2053_, v___x_2061_);
v___x_2066_ = lean_string_append(v___x_2064_, v___x_2065_);
lean_dec_ref(v___x_2065_);
v___x_2067_ = ((lean_object*)(l_Lean_resolveNamespaceCore___redArg___lam__1___closed__1));
v___x_2068_ = lean_string_append(v___x_2066_, v___x_2067_);
v___x_2069_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2069_, 0, v___x_2068_);
v___x_2070_ = l_Lean_MessageData_ofFormat(v___x_2069_);
v___x_2071_ = l_Lean_throwError___redArg(v_inst_2056_, v_inst_2057_, v___x_2070_);
v___x_2072_ = lean_apply_4(v_toBind_2058_, lean_box(0), lean_box(0), v___x_2071_, v___f_2063_);
return v___x_2072_;
}
}
else
{
lean_object* v___x_2073_; 
lean_dec(v_toBind_2058_);
lean_dec_ref(v_inst_2057_);
lean_dec_ref(v_inst_2056_);
lean_dec(v_id_2053_);
v___x_2073_ = lean_apply_2(v_toPure_2055_, lean_box(0), v_nss_2060_);
return v___x_2073_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__1___boxed(lean_object* v_____do__lift_2074_, lean_object* v_____do__lift_2075_, lean_object* v_id_2076_, lean_object* v_allowEmpty_2077_, lean_object* v_toPure_2078_, lean_object* v_inst_2079_, lean_object* v_inst_2080_, lean_object* v_toBind_2081_, lean_object* v_____do__lift_2082_){
_start:
{
uint8_t v_allowEmpty_boxed_2083_; lean_object* v_res_2084_; 
v_allowEmpty_boxed_2083_ = lean_unbox(v_allowEmpty_2077_);
v_res_2084_ = l_Lean_resolveNamespaceCore___redArg___lam__1(v_____do__lift_2074_, v_____do__lift_2075_, v_id_2076_, v_allowEmpty_boxed_2083_, v_toPure_2078_, v_inst_2079_, v_inst_2080_, v_toBind_2081_, v_____do__lift_2082_);
return v_res_2084_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__2(lean_object* v_____do__lift_2085_, lean_object* v_id_2086_, uint8_t v_allowEmpty_2087_, lean_object* v_toPure_2088_, lean_object* v_inst_2089_, lean_object* v_inst_2090_, lean_object* v_toBind_2091_, lean_object* v_getOpenDecls_2092_, lean_object* v_____do__lift_2093_){
_start:
{
lean_object* v___x_2094_; lean_object* v___f_2095_; lean_object* v___x_2096_; 
v___x_2094_ = lean_box(v_allowEmpty_2087_);
lean_inc(v_toBind_2091_);
v___f_2095_ = lean_alloc_closure((void*)(l_Lean_resolveNamespaceCore___redArg___lam__1___boxed), 9, 8);
lean_closure_set(v___f_2095_, 0, v_____do__lift_2085_);
lean_closure_set(v___f_2095_, 1, v_____do__lift_2093_);
lean_closure_set(v___f_2095_, 2, v_id_2086_);
lean_closure_set(v___f_2095_, 3, v___x_2094_);
lean_closure_set(v___f_2095_, 4, v_toPure_2088_);
lean_closure_set(v___f_2095_, 5, v_inst_2089_);
lean_closure_set(v___f_2095_, 6, v_inst_2090_);
lean_closure_set(v___f_2095_, 7, v_toBind_2091_);
v___x_2096_ = lean_apply_4(v_toBind_2091_, lean_box(0), lean_box(0), v_getOpenDecls_2092_, v___f_2095_);
return v___x_2096_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__2___boxed(lean_object* v_____do__lift_2097_, lean_object* v_id_2098_, lean_object* v_allowEmpty_2099_, lean_object* v_toPure_2100_, lean_object* v_inst_2101_, lean_object* v_inst_2102_, lean_object* v_toBind_2103_, lean_object* v_getOpenDecls_2104_, lean_object* v_____do__lift_2105_){
_start:
{
uint8_t v_allowEmpty_boxed_2106_; lean_object* v_res_2107_; 
v_allowEmpty_boxed_2106_ = lean_unbox(v_allowEmpty_2099_);
v_res_2107_ = l_Lean_resolveNamespaceCore___redArg___lam__2(v_____do__lift_2097_, v_id_2098_, v_allowEmpty_boxed_2106_, v_toPure_2100_, v_inst_2101_, v_inst_2102_, v_toBind_2103_, v_getOpenDecls_2104_, v_____do__lift_2105_);
return v_res_2107_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__3(lean_object* v_inst_2108_, lean_object* v_id_2109_, uint8_t v_allowEmpty_2110_, lean_object* v_toPure_2111_, lean_object* v_inst_2112_, lean_object* v_inst_2113_, lean_object* v_toBind_2114_, lean_object* v_____do__lift_2115_){
_start:
{
lean_object* v_getCurrNamespace_2116_; lean_object* v_getOpenDecls_2117_; lean_object* v___x_2118_; lean_object* v___f_2119_; lean_object* v___x_2120_; 
v_getCurrNamespace_2116_ = lean_ctor_get(v_inst_2108_, 0);
lean_inc(v_getCurrNamespace_2116_);
v_getOpenDecls_2117_ = lean_ctor_get(v_inst_2108_, 1);
lean_inc(v_getOpenDecls_2117_);
lean_dec_ref(v_inst_2108_);
v___x_2118_ = lean_box(v_allowEmpty_2110_);
lean_inc(v_toBind_2114_);
v___f_2119_ = lean_alloc_closure((void*)(l_Lean_resolveNamespaceCore___redArg___lam__2___boxed), 9, 8);
lean_closure_set(v___f_2119_, 0, v_____do__lift_2115_);
lean_closure_set(v___f_2119_, 1, v_id_2109_);
lean_closure_set(v___f_2119_, 2, v___x_2118_);
lean_closure_set(v___f_2119_, 3, v_toPure_2111_);
lean_closure_set(v___f_2119_, 4, v_inst_2112_);
lean_closure_set(v___f_2119_, 5, v_inst_2113_);
lean_closure_set(v___f_2119_, 6, v_toBind_2114_);
lean_closure_set(v___f_2119_, 7, v_getOpenDecls_2117_);
v___x_2120_ = lean_apply_4(v_toBind_2114_, lean_box(0), lean_box(0), v_getCurrNamespace_2116_, v___f_2119_);
return v___x_2120_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__3___boxed(lean_object* v_inst_2121_, lean_object* v_id_2122_, lean_object* v_allowEmpty_2123_, lean_object* v_toPure_2124_, lean_object* v_inst_2125_, lean_object* v_inst_2126_, lean_object* v_toBind_2127_, lean_object* v_____do__lift_2128_){
_start:
{
uint8_t v_allowEmpty_boxed_2129_; lean_object* v_res_2130_; 
v_allowEmpty_boxed_2129_ = lean_unbox(v_allowEmpty_2123_);
v_res_2130_ = l_Lean_resolveNamespaceCore___redArg___lam__3(v_inst_2121_, v_id_2122_, v_allowEmpty_boxed_2129_, v_toPure_2124_, v_inst_2125_, v_inst_2126_, v_toBind_2127_, v_____do__lift_2128_);
return v_res_2130_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg(lean_object* v_inst_2131_, lean_object* v_inst_2132_, lean_object* v_inst_2133_, lean_object* v_inst_2134_, lean_object* v_id_2135_, uint8_t v_allowEmpty_2136_){
_start:
{
lean_object* v_toApplicative_2137_; lean_object* v_toBind_2138_; lean_object* v_getEnv_2139_; lean_object* v_toPure_2140_; lean_object* v___x_2141_; lean_object* v___f_2142_; lean_object* v___x_2143_; 
v_toApplicative_2137_ = lean_ctor_get(v_inst_2131_, 0);
v_toBind_2138_ = lean_ctor_get(v_inst_2131_, 1);
lean_inc_n(v_toBind_2138_, 2);
v_getEnv_2139_ = lean_ctor_get(v_inst_2133_, 0);
lean_inc(v_getEnv_2139_);
lean_dec_ref(v_inst_2133_);
v_toPure_2140_ = lean_ctor_get(v_toApplicative_2137_, 1);
lean_inc(v_toPure_2140_);
v___x_2141_ = lean_box(v_allowEmpty_2136_);
v___f_2142_ = lean_alloc_closure((void*)(l_Lean_resolveNamespaceCore___redArg___lam__3___boxed), 8, 7);
lean_closure_set(v___f_2142_, 0, v_inst_2132_);
lean_closure_set(v___f_2142_, 1, v_id_2135_);
lean_closure_set(v___f_2142_, 2, v___x_2141_);
lean_closure_set(v___f_2142_, 3, v_toPure_2140_);
lean_closure_set(v___f_2142_, 4, v_inst_2131_);
lean_closure_set(v___f_2142_, 5, v_inst_2134_);
lean_closure_set(v___f_2142_, 6, v_toBind_2138_);
v___x_2143_ = lean_apply_4(v_toBind_2138_, lean_box(0), lean_box(0), v_getEnv_2139_, v___f_2142_);
return v___x_2143_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___boxed(lean_object* v_inst_2144_, lean_object* v_inst_2145_, lean_object* v_inst_2146_, lean_object* v_inst_2147_, lean_object* v_id_2148_, lean_object* v_allowEmpty_2149_){
_start:
{
uint8_t v_allowEmpty_boxed_2150_; lean_object* v_res_2151_; 
v_allowEmpty_boxed_2150_ = lean_unbox(v_allowEmpty_2149_);
v_res_2151_ = l_Lean_resolveNamespaceCore___redArg(v_inst_2144_, v_inst_2145_, v_inst_2146_, v_inst_2147_, v_id_2148_, v_allowEmpty_boxed_2150_);
return v_res_2151_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore(lean_object* v_m_2152_, lean_object* v_inst_2153_, lean_object* v_inst_2154_, lean_object* v_inst_2155_, lean_object* v_inst_2156_, lean_object* v_id_2157_, uint8_t v_allowEmpty_2158_){
_start:
{
lean_object* v___x_2159_; 
v___x_2159_ = l_Lean_resolveNamespaceCore___redArg(v_inst_2153_, v_inst_2154_, v_inst_2155_, v_inst_2156_, v_id_2157_, v_allowEmpty_2158_);
return v___x_2159_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___boxed(lean_object* v_m_2160_, lean_object* v_inst_2161_, lean_object* v_inst_2162_, lean_object* v_inst_2163_, lean_object* v_inst_2164_, lean_object* v_id_2165_, lean_object* v_allowEmpty_2166_){
_start:
{
uint8_t v_allowEmpty_boxed_2167_; lean_object* v_res_2168_; 
v_allowEmpty_boxed_2167_ = lean_unbox(v_allowEmpty_2166_);
v_res_2168_ = l_Lean_resolveNamespaceCore(v_m_2160_, v_inst_2161_, v_inst_2162_, v_inst_2163_, v_inst_2164_, v_id_2165_, v_allowEmpty_boxed_2167_);
return v_res_2168_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespace___redArg___lam__0(lean_object* v_x_2169_){
_start:
{
if (lean_obj_tag(v_x_2169_) == 0)
{
lean_object* v_ns_2170_; lean_object* v___x_2172_; uint8_t v_isShared_2173_; uint8_t v_isSharedCheck_2177_; 
v_ns_2170_ = lean_ctor_get(v_x_2169_, 0);
v_isSharedCheck_2177_ = !lean_is_exclusive(v_x_2169_);
if (v_isSharedCheck_2177_ == 0)
{
v___x_2172_ = v_x_2169_;
v_isShared_2173_ = v_isSharedCheck_2177_;
goto v_resetjp_2171_;
}
else
{
lean_inc(v_ns_2170_);
lean_dec(v_x_2169_);
v___x_2172_ = lean_box(0);
v_isShared_2173_ = v_isSharedCheck_2177_;
goto v_resetjp_2171_;
}
v_resetjp_2171_:
{
lean_object* v___x_2175_; 
if (v_isShared_2173_ == 0)
{
lean_ctor_set_tag(v___x_2172_, 1);
v___x_2175_ = v___x_2172_;
goto v_reusejp_2174_;
}
else
{
lean_object* v_reuseFailAlloc_2176_; 
v_reuseFailAlloc_2176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2176_, 0, v_ns_2170_);
v___x_2175_ = v_reuseFailAlloc_2176_;
goto v_reusejp_2174_;
}
v_reusejp_2174_:
{
return v___x_2175_;
}
}
}
else
{
lean_object* v___x_2178_; 
lean_dec_ref(v_x_2169_);
v___x_2178_ = lean_box(0);
return v___x_2178_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespace___redArg___lam__1(lean_object* v_x_2179_, lean_object* v_withRef_2180_, lean_object* v___x_2181_, lean_object* v_oldRef_2182_){
_start:
{
lean_object* v_ref_2183_; lean_object* v___x_2184_; 
v_ref_2183_ = l_Lean_replaceRef(v_x_2179_, v_oldRef_2182_);
v___x_2184_ = lean_apply_3(v_withRef_2180_, lean_box(0), v_ref_2183_, v___x_2181_);
return v___x_2184_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespace___redArg___lam__1___boxed(lean_object* v_x_2185_, lean_object* v_withRef_2186_, lean_object* v___x_2187_, lean_object* v_oldRef_2188_){
_start:
{
lean_object* v_res_2189_; 
v_res_2189_ = l_Lean_resolveNamespace___redArg___lam__1(v_x_2185_, v_withRef_2186_, v___x_2187_, v_oldRef_2188_);
lean_dec(v_oldRef_2188_);
lean_dec(v_x_2185_);
return v_res_2189_;
}
}
static lean_object* _init_l_Lean_resolveNamespace___redArg___closed__4(void){
_start:
{
lean_object* v___x_2196_; lean_object* v___x_2197_; 
v___x_2196_ = ((lean_object*)(l_Lean_resolveNamespace___redArg___closed__3));
v___x_2197_ = l_Lean_MessageData_ofFormat(v___x_2196_);
return v___x_2197_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespace___redArg(lean_object* v_inst_2198_, lean_object* v_inst_2199_, lean_object* v_inst_2200_, lean_object* v_inst_2201_, lean_object* v_x_2202_){
_start:
{
if (lean_obj_tag(v_x_2202_) == 3)
{
lean_object* v_val_2203_; lean_object* v_preresolved_2204_; lean_object* v___f_2205_; lean_object* v___x_2206_; lean_object* v_pre_2207_; uint8_t v___x_2208_; 
v_val_2203_ = lean_ctor_get(v_x_2202_, 2);
v_preresolved_2204_ = lean_ctor_get(v_x_2202_, 3);
v___f_2205_ = ((lean_object*)(l_Lean_resolveNamespace___redArg___closed__0));
v___x_2206_ = ((lean_object*)(l_Lean_resolveNamespace___redArg___closed__1));
lean_inc(v_preresolved_2204_);
v_pre_2207_ = l_List_filterMapTR_go___redArg(v___f_2205_, v_preresolved_2204_, v___x_2206_);
v___x_2208_ = l_List_isEmpty___redArg(v_pre_2207_);
if (v___x_2208_ == 0)
{
lean_object* v_toApplicative_2209_; lean_object* v_toPure_2210_; lean_object* v___x_2211_; 
lean_dec_ref_known(v_x_2202_, 4);
lean_dec_ref(v_inst_2201_);
lean_dec_ref(v_inst_2200_);
lean_dec_ref(v_inst_2199_);
v_toApplicative_2209_ = lean_ctor_get(v_inst_2198_, 0);
lean_inc_ref(v_toApplicative_2209_);
lean_dec_ref(v_inst_2198_);
v_toPure_2210_ = lean_ctor_get(v_toApplicative_2209_, 1);
lean_inc(v_toPure_2210_);
lean_dec_ref(v_toApplicative_2209_);
v___x_2211_ = lean_apply_2(v_toPure_2210_, lean_box(0), v_pre_2207_);
return v___x_2211_;
}
else
{
lean_object* v_toMonadRef_2212_; lean_object* v_toBind_2213_; lean_object* v_getRef_2214_; lean_object* v_withRef_2215_; uint8_t v___x_2216_; lean_object* v___x_2217_; lean_object* v___f_2218_; lean_object* v___x_2219_; 
lean_dec(v_pre_2207_);
v_toMonadRef_2212_ = lean_ctor_get(v_inst_2201_, 1);
v_toBind_2213_ = lean_ctor_get(v_inst_2198_, 1);
lean_inc(v_toBind_2213_);
v_getRef_2214_ = lean_ctor_get(v_toMonadRef_2212_, 0);
lean_inc(v_getRef_2214_);
v_withRef_2215_ = lean_ctor_get(v_toMonadRef_2212_, 1);
lean_inc(v_withRef_2215_);
v___x_2216_ = 0;
lean_inc(v_val_2203_);
v___x_2217_ = l_Lean_resolveNamespaceCore___redArg(v_inst_2198_, v_inst_2199_, v_inst_2200_, v_inst_2201_, v_val_2203_, v___x_2216_);
v___f_2218_ = lean_alloc_closure((void*)(l_Lean_resolveNamespace___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_2218_, 0, v_x_2202_);
lean_closure_set(v___f_2218_, 1, v_withRef_2215_);
lean_closure_set(v___f_2218_, 2, v___x_2217_);
v___x_2219_ = lean_apply_4(v_toBind_2213_, lean_box(0), lean_box(0), v_getRef_2214_, v___f_2218_);
return v___x_2219_;
}
}
else
{
lean_object* v___x_2220_; lean_object* v___x_2221_; 
lean_dec_ref(v_inst_2200_);
lean_dec_ref(v_inst_2199_);
v___x_2220_ = lean_obj_once(&l_Lean_resolveNamespace___redArg___closed__4, &l_Lean_resolveNamespace___redArg___closed__4_once, _init_l_Lean_resolveNamespace___redArg___closed__4);
v___x_2221_ = l_Lean_throwErrorAt___redArg(v_inst_2198_, v_inst_2201_, v_x_2202_, v___x_2220_);
return v___x_2221_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespace(lean_object* v_m_2222_, lean_object* v_inst_2223_, lean_object* v_inst_2224_, lean_object* v_inst_2225_, lean_object* v_inst_2226_, lean_object* v_x_2227_){
_start:
{
lean_object* v___x_2228_; 
v___x_2228_ = l_Lean_resolveNamespace___redArg(v_inst_2223_, v_inst_2224_, v_inst_2225_, v_inst_2226_, v_x_2227_);
return v___x_2228_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveUniqueNamespace___redArg___lam__0(lean_object* v_id_2231_, lean_object* v___f_2232_, lean_object* v_inst_2233_, lean_object* v_inst_2234_, lean_object* v_toPure_2235_, lean_object* v_____do__lift_2236_){
_start:
{
if (lean_obj_tag(v_____do__lift_2236_) == 1)
{
lean_object* v_tail_2252_; 
v_tail_2252_ = lean_ctor_get(v_____do__lift_2236_, 1);
if (lean_obj_tag(v_tail_2252_) == 0)
{
lean_object* v_head_2253_; lean_object* v___x_2254_; 
lean_dec_ref(v_inst_2234_);
lean_dec_ref(v_inst_2233_);
lean_dec_ref(v___f_2232_);
v_head_2253_ = lean_ctor_get(v_____do__lift_2236_, 0);
lean_inc(v_head_2253_);
lean_dec_ref_known(v_____do__lift_2236_, 2);
v___x_2254_ = lean_apply_2(v_toPure_2235_, lean_box(0), v_head_2253_);
return v___x_2254_;
}
else
{
lean_dec(v_toPure_2235_);
goto v___jp_2237_;
}
}
else
{
lean_dec(v_toPure_2235_);
goto v___jp_2237_;
}
v___jp_2237_:
{
lean_object* v___x_2238_; lean_object* v___x_2239_; uint8_t v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; 
v___x_2238_ = ((lean_object*)(l_Lean_resolveUniqueNamespace___redArg___lam__0___closed__0));
v___x_2239_ = l_Lean_TSyntax_getId(v_id_2231_);
v___x_2240_ = 1;
v___x_2241_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2239_, v___x_2240_);
v___x_2242_ = lean_string_append(v___x_2238_, v___x_2241_);
lean_dec_ref(v___x_2241_);
v___x_2243_ = ((lean_object*)(l_Lean_resolveUniqueNamespace___redArg___lam__0___closed__1));
v___x_2244_ = lean_string_append(v___x_2242_, v___x_2243_);
v___x_2245_ = l_List_toString___redArg(v___f_2232_, v_____do__lift_2236_);
v___x_2246_ = lean_string_append(v___x_2244_, v___x_2245_);
lean_dec_ref(v___x_2245_);
v___x_2247_ = ((lean_object*)(l_Lean_resolveNamespaceCore___redArg___lam__1___closed__1));
v___x_2248_ = lean_string_append(v___x_2246_, v___x_2247_);
v___x_2249_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2249_, 0, v___x_2248_);
v___x_2250_ = l_Lean_MessageData_ofFormat(v___x_2249_);
v___x_2251_ = l_Lean_throwError___redArg(v_inst_2233_, v_inst_2234_, v___x_2250_);
return v___x_2251_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveUniqueNamespace___redArg___lam__0___boxed(lean_object* v_id_2255_, lean_object* v___f_2256_, lean_object* v_inst_2257_, lean_object* v_inst_2258_, lean_object* v_toPure_2259_, lean_object* v_____do__lift_2260_){
_start:
{
lean_object* v_res_2261_; 
v_res_2261_ = l_Lean_resolveUniqueNamespace___redArg___lam__0(v_id_2255_, v___f_2256_, v_inst_2257_, v_inst_2258_, v_toPure_2259_, v_____do__lift_2260_);
lean_dec(v_id_2255_);
return v_res_2261_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveUniqueNamespace___redArg(lean_object* v_inst_2263_, lean_object* v_inst_2264_, lean_object* v_inst_2265_, lean_object* v_inst_2266_, lean_object* v_id_2267_){
_start:
{
lean_object* v_toApplicative_2268_; lean_object* v_toBind_2269_; lean_object* v_toPure_2270_; lean_object* v___f_2271_; lean_object* v___x_2272_; lean_object* v___f_2273_; lean_object* v___x_2274_; 
v_toApplicative_2268_ = lean_ctor_get(v_inst_2263_, 0);
v_toBind_2269_ = lean_ctor_get(v_inst_2263_, 1);
lean_inc(v_toBind_2269_);
v_toPure_2270_ = lean_ctor_get(v_toApplicative_2268_, 1);
lean_inc(v_toPure_2270_);
v___f_2271_ = ((lean_object*)(l_Lean_resolveUniqueNamespace___redArg___closed__0));
lean_inc(v_id_2267_);
lean_inc_ref(v_inst_2266_);
lean_inc_ref(v_inst_2263_);
v___x_2272_ = l_Lean_resolveNamespace___redArg(v_inst_2263_, v_inst_2264_, v_inst_2265_, v_inst_2266_, v_id_2267_);
v___f_2273_ = lean_alloc_closure((void*)(l_Lean_resolveUniqueNamespace___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_2273_, 0, v_id_2267_);
lean_closure_set(v___f_2273_, 1, v___f_2271_);
lean_closure_set(v___f_2273_, 2, v_inst_2263_);
lean_closure_set(v___f_2273_, 3, v_inst_2266_);
lean_closure_set(v___f_2273_, 4, v_toPure_2270_);
v___x_2274_ = lean_apply_4(v_toBind_2269_, lean_box(0), lean_box(0), v___x_2272_, v___f_2273_);
return v___x_2274_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveUniqueNamespace(lean_object* v_m_2275_, lean_object* v_inst_2276_, lean_object* v_inst_2277_, lean_object* v_inst_2278_, lean_object* v_inst_2279_, lean_object* v_id_2280_){
_start:
{
lean_object* v___x_2281_; 
v___x_2281_ = l_Lean_resolveUniqueNamespace___redArg(v_inst_2276_, v_inst_2277_, v_inst_2278_, v_inst_2279_, v_id_2280_);
return v___x_2281_;
}
}
LEAN_EXPORT uint8_t l_Lean_filterFieldList___redArg___lam__0(lean_object* v_x_2282_){
_start:
{
lean_object* v_snd_2283_; uint8_t v___x_2284_; 
v_snd_2283_ = lean_ctor_get(v_x_2282_, 1);
v___x_2284_ = l_List_isEmpty___redArg(v_snd_2283_);
return v___x_2284_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg___lam__0___boxed(lean_object* v_x_2285_){
_start:
{
uint8_t v_res_2286_; lean_object* v_r_2287_; 
v_res_2286_ = l_Lean_filterFieldList___redArg___lam__0(v_x_2285_);
lean_dec_ref(v_x_2285_);
v_r_2287_ = lean_box(v_res_2286_);
return v_r_2287_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg___lam__1(lean_object* v_x_2288_){
_start:
{
lean_object* v_fst_2289_; 
v_fst_2289_ = lean_ctor_get(v_x_2288_, 0);
lean_inc(v_fst_2289_);
return v_fst_2289_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg___lam__1___boxed(lean_object* v_x_2290_){
_start:
{
lean_object* v_res_2291_; 
v_res_2291_ = l_Lean_filterFieldList___redArg___lam__1(v_x_2290_);
lean_dec_ref(v_x_2290_);
return v_res_2291_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg___lam__2(lean_object* v___f_2292_, lean_object* v_cs_2293_, lean_object* v_toPure_2294_, lean_object* v_____r_2295_){
_start:
{
lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; 
v___x_2296_ = lean_box(0);
v___x_2297_ = l_List_mapTR_loop___redArg(v___f_2292_, v_cs_2293_, v___x_2296_);
v___x_2298_ = lean_apply_2(v_toPure_2294_, lean_box(0), v___x_2297_);
return v___x_2298_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg___lam__3(lean_object* v___f_2299_, lean_object* v_____r_2300_){
_start:
{
lean_object* v___x_2301_; 
v___x_2301_ = lean_apply_1(v___f_2299_, v_____r_2300_);
return v___x_2301_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg___lam__4(lean_object* v_inst_2302_, lean_object* v_inst_2303_, lean_object* v_inst_2304_, lean_object* v_n_2305_, lean_object* v_toBind_2306_, lean_object* v___f_2307_, lean_object* v_____do__lift_2308_){
_start:
{
lean_object* v___x_2309_; lean_object* v___x_2310_; 
v___x_2309_ = l_Lean_throwUnknownConstantAt___redArg(v_inst_2302_, v_inst_2303_, v_inst_2304_, v_____do__lift_2308_, v_n_2305_);
v___x_2310_ = lean_apply_4(v_toBind_2306_, lean_box(0), lean_box(0), v___x_2309_, v___f_2307_);
return v___x_2310_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg(lean_object* v_inst_2313_, lean_object* v_inst_2314_, lean_object* v_inst_2315_, lean_object* v_n_2316_, lean_object* v_cs_2317_){
_start:
{
lean_object* v_toApplicative_2318_; lean_object* v_toBind_2319_; lean_object* v_toPure_2320_; lean_object* v___f_2321_; lean_object* v___f_2322_; lean_object* v___x_2323_; lean_object* v_cs_2324_; lean_object* v___f_2325_; uint8_t v___x_2326_; 
v_toApplicative_2318_ = lean_ctor_get(v_inst_2313_, 0);
v_toBind_2319_ = lean_ctor_get(v_inst_2313_, 1);
lean_inc(v_toBind_2319_);
v_toPure_2320_ = lean_ctor_get(v_toApplicative_2318_, 1);
v___f_2321_ = ((lean_object*)(l_Lean_filterFieldList___redArg___closed__0));
v___f_2322_ = ((lean_object*)(l_Lean_filterFieldList___redArg___closed__1));
v___x_2323_ = lean_box(0);
v_cs_2324_ = l_List_filterTR_loop___redArg(v___f_2321_, v_cs_2317_, v___x_2323_);
lean_inc(v_toPure_2320_);
lean_inc(v_cs_2324_);
v___f_2325_ = lean_alloc_closure((void*)(l_Lean_filterFieldList___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2325_, 0, v___f_2322_);
lean_closure_set(v___f_2325_, 1, v_cs_2324_);
lean_closure_set(v___f_2325_, 2, v_toPure_2320_);
v___x_2326_ = l_List_isEmpty___redArg(v_cs_2324_);
if (v___x_2326_ == 0)
{
lean_object* v___x_2327_; lean_object* v___x_2328_; 
lean_inc(v_toPure_2320_);
lean_dec_ref(v___f_2325_);
lean_dec(v_toBind_2319_);
lean_dec(v_n_2316_);
lean_dec_ref(v_inst_2315_);
lean_dec_ref(v_inst_2314_);
lean_dec_ref(v_inst_2313_);
v___x_2327_ = lean_box(0);
v___x_2328_ = l_Lean_filterFieldList___redArg___lam__2(v___f_2322_, v_cs_2324_, v_toPure_2320_, v___x_2327_);
return v___x_2328_;
}
else
{
lean_object* v_toMonadRef_2329_; lean_object* v_getRef_2330_; lean_object* v___f_2331_; lean_object* v___f_2332_; lean_object* v___x_2333_; 
lean_dec(v_cs_2324_);
v_toMonadRef_2329_ = lean_ctor_get(v_inst_2315_, 1);
v_getRef_2330_ = lean_ctor_get(v_toMonadRef_2329_, 0);
lean_inc(v_getRef_2330_);
v___f_2331_ = lean_alloc_closure((void*)(l_Lean_filterFieldList___redArg___lam__3), 2, 1);
lean_closure_set(v___f_2331_, 0, v___f_2325_);
lean_inc(v_toBind_2319_);
v___f_2332_ = lean_alloc_closure((void*)(l_Lean_filterFieldList___redArg___lam__4), 7, 6);
lean_closure_set(v___f_2332_, 0, v_inst_2313_);
lean_closure_set(v___f_2332_, 1, v_inst_2314_);
lean_closure_set(v___f_2332_, 2, v_inst_2315_);
lean_closure_set(v___f_2332_, 3, v_n_2316_);
lean_closure_set(v___f_2332_, 4, v_toBind_2319_);
lean_closure_set(v___f_2332_, 5, v___f_2331_);
v___x_2333_ = lean_apply_4(v_toBind_2319_, lean_box(0), lean_box(0), v_getRef_2330_, v___f_2332_);
return v___x_2333_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList(lean_object* v_m_2334_, lean_object* v_inst_2335_, lean_object* v_inst_2336_, lean_object* v_inst_2337_, lean_object* v_n_2338_, lean_object* v_cs_2339_){
_start:
{
lean_object* v___x_2340_; 
v___x_2340_ = l_Lean_filterFieldList___redArg(v_inst_2335_, v_inst_2336_, v_inst_2337_, v_n_2338_, v_cs_2339_);
return v___x_2340_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___redArg___lam__0(lean_object* v_inst_2341_, lean_object* v_inst_2342_, lean_object* v_inst_2343_, lean_object* v_n_2344_, lean_object* v_cs_2345_){
_start:
{
lean_object* v___x_2346_; 
v___x_2346_ = l_Lean_filterFieldList___redArg(v_inst_2341_, v_inst_2342_, v_inst_2343_, v_n_2344_, v_cs_2345_);
return v___x_2346_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___redArg(lean_object* v_inst_2347_, lean_object* v_inst_2348_, lean_object* v_inst_2349_, lean_object* v_inst_2350_, lean_object* v_inst_2351_, lean_object* v_inst_2352_, lean_object* v_inst_2353_, lean_object* v_n_2354_){
_start:
{
lean_object* v_toBind_2355_; lean_object* v___f_2356_; uint8_t v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; 
v_toBind_2355_ = lean_ctor_get(v_inst_2347_, 1);
lean_inc(v_toBind_2355_);
lean_inc(v_n_2354_);
lean_inc_ref(v_inst_2349_);
lean_inc_ref(v_inst_2347_);
v___f_2356_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___redArg___lam__0), 5, 4);
lean_closure_set(v___f_2356_, 0, v_inst_2347_);
lean_closure_set(v___f_2356_, 1, v_inst_2349_);
lean_closure_set(v___f_2356_, 2, v_inst_2353_);
lean_closure_set(v___f_2356_, 3, v_n_2354_);
v___x_2357_ = 1;
v___x_2358_ = l_Lean_resolveGlobalName___redArg(v_inst_2347_, v_inst_2348_, v_inst_2349_, v_inst_2350_, v_inst_2351_, v_inst_2352_, v_n_2354_, v___x_2357_);
v___x_2359_ = lean_apply_4(v_toBind_2355_, lean_box(0), lean_box(0), v___x_2358_, v___f_2356_);
return v___x_2359_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore(lean_object* v_m_2360_, lean_object* v_inst_2361_, lean_object* v_inst_2362_, lean_object* v_inst_2363_, lean_object* v_inst_2364_, lean_object* v_inst_2365_, lean_object* v_inst_2366_, lean_object* v_inst_2367_, lean_object* v_n_2368_){
_start:
{
lean_object* v___x_2369_; 
v___x_2369_ = l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___redArg(v_inst_2361_, v_inst_2362_, v_inst_2363_, v_inst_2364_, v_inst_2365_, v_inst_2366_, v_inst_2367_, v_n_2368_);
return v___x_2369_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNoOverload___redArg___lam__0(lean_object* v_declName_2370_){
_start:
{
lean_object* v___x_2371_; lean_object* v___x_2372_; 
v___x_2371_ = lean_box(0);
v___x_2372_ = l_Lean_mkConst(v_declName_2370_, v___x_2371_);
return v___x_2372_;
}
}
static lean_object* _init_l_Lean_ensureNoOverload___redArg___closed__2(void){
_start:
{
lean_object* v___x_2375_; lean_object* v___x_2376_; 
v___x_2375_ = ((lean_object*)(l_Lean_ensureNoOverload___redArg___closed__1));
v___x_2376_ = l_Lean_stringToMessageData(v___x_2375_);
return v___x_2376_;
}
}
static lean_object* _init_l_Lean_ensureNoOverload___redArg___closed__4(void){
_start:
{
lean_object* v___x_2378_; lean_object* v___x_2379_; 
v___x_2378_ = ((lean_object*)(l_Lean_ensureNoOverload___redArg___closed__3));
v___x_2379_ = l_Lean_stringToMessageData(v___x_2378_);
return v___x_2379_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNoOverload___redArg(lean_object* v_inst_2381_, lean_object* v_inst_2382_, lean_object* v_n_2383_, lean_object* v_cs_2384_){
_start:
{
lean_object* v_toApplicative_2385_; lean_object* v_toPure_2386_; lean_object* v___f_2387_; 
v_toApplicative_2385_ = lean_ctor_get(v_inst_2381_, 0);
v_toPure_2386_ = lean_ctor_get(v_toApplicative_2385_, 1);
v___f_2387_ = ((lean_object*)(l_Lean_ensureNoOverload___redArg___closed__0));
if (lean_obj_tag(v_cs_2384_) == 1)
{
lean_object* v_tail_2401_; 
v_tail_2401_ = lean_ctor_get(v_cs_2384_, 1);
if (lean_obj_tag(v_tail_2401_) == 0)
{
lean_object* v_head_2402_; lean_object* v___x_2403_; 
lean_inc(v_toPure_2386_);
lean_dec(v_n_2383_);
lean_dec_ref(v_inst_2382_);
lean_dec_ref(v_inst_2381_);
v_head_2402_ = lean_ctor_get(v_cs_2384_, 0);
lean_inc(v_head_2402_);
lean_dec_ref_known(v_cs_2384_, 2);
v___x_2403_ = lean_apply_2(v_toPure_2386_, lean_box(0), v_head_2402_);
return v___x_2403_;
}
else
{
goto v___jp_2388_;
}
}
else
{
goto v___jp_2388_;
}
v___jp_2388_:
{
lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; 
v___x_2389_ = lean_obj_once(&l_Lean_ensureNoOverload___redArg___closed__2, &l_Lean_ensureNoOverload___redArg___closed__2_once, _init_l_Lean_ensureNoOverload___redArg___closed__2);
v___x_2390_ = l_Lean_MessageData_ofName(v_n_2383_);
v___x_2391_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2391_, 0, v___x_2389_);
lean_ctor_set(v___x_2391_, 1, v___x_2390_);
v___x_2392_ = lean_obj_once(&l_Lean_ensureNoOverload___redArg___closed__4, &l_Lean_ensureNoOverload___redArg___closed__4_once, _init_l_Lean_ensureNoOverload___redArg___closed__4);
v___x_2393_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2393_, 0, v___x_2391_);
lean_ctor_set(v___x_2393_, 1, v___x_2392_);
v___x_2394_ = lean_box(0);
v___x_2395_ = l_List_mapTR_loop___redArg(v___f_2387_, v_cs_2384_, v___x_2394_);
v___x_2396_ = ((lean_object*)(l_Lean_ensureNoOverload___redArg___closed__5));
v___x_2397_ = l_List_mapTR_loop___redArg(v___x_2396_, v___x_2395_, v___x_2394_);
v___x_2398_ = l_Lean_MessageData_ofList(v___x_2397_);
v___x_2399_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2399_, 0, v___x_2393_);
lean_ctor_set(v___x_2399_, 1, v___x_2398_);
v___x_2400_ = l_Lean_throwError___redArg(v_inst_2381_, v_inst_2382_, v___x_2399_);
return v___x_2400_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNoOverload(lean_object* v_m_2404_, lean_object* v_inst_2405_, lean_object* v_inst_2406_, lean_object* v_n_2407_, lean_object* v_cs_2408_){
_start:
{
lean_object* v___x_2409_; 
v___x_2409_ = l_Lean_ensureNoOverload___redArg(v_inst_2405_, v_inst_2406_, v_n_2407_, v_cs_2408_);
return v___x_2409_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverloadCore___redArg___lam__0(lean_object* v_inst_2410_, lean_object* v_inst_2411_, lean_object* v_n_2412_, lean_object* v_____do__lift_2413_){
_start:
{
lean_object* v___x_2414_; 
v___x_2414_ = l_Lean_ensureNoOverload___redArg(v_inst_2410_, v_inst_2411_, v_n_2412_, v_____do__lift_2413_);
return v___x_2414_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverloadCore___redArg(lean_object* v_inst_2415_, lean_object* v_inst_2416_, lean_object* v_inst_2417_, lean_object* v_inst_2418_, lean_object* v_inst_2419_, lean_object* v_inst_2420_, lean_object* v_inst_2421_, lean_object* v_n_2422_){
_start:
{
lean_object* v_toBind_2423_; lean_object* v___f_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; 
v_toBind_2423_ = lean_ctor_get(v_inst_2415_, 1);
lean_inc(v_toBind_2423_);
lean_inc(v_n_2422_);
lean_inc_ref(v_inst_2421_);
lean_inc_ref(v_inst_2415_);
v___f_2424_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalConstNoOverloadCore___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2424_, 0, v_inst_2415_);
lean_closure_set(v___f_2424_, 1, v_inst_2421_);
lean_closure_set(v___f_2424_, 2, v_n_2422_);
v___x_2425_ = l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___redArg(v_inst_2415_, v_inst_2416_, v_inst_2417_, v_inst_2418_, v_inst_2419_, v_inst_2420_, v_inst_2421_, v_n_2422_);
v___x_2426_ = lean_apply_4(v_toBind_2423_, lean_box(0), lean_box(0), v___x_2425_, v___f_2424_);
return v___x_2426_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverloadCore(lean_object* v_m_2427_, lean_object* v_inst_2428_, lean_object* v_inst_2429_, lean_object* v_inst_2430_, lean_object* v_inst_2431_, lean_object* v_inst_2432_, lean_object* v_inst_2433_, lean_object* v_inst_2434_, lean_object* v_n_2435_){
_start:
{
lean_object* v___x_2436_; 
v___x_2436_ = l_Lean_resolveGlobalConstNoOverloadCore___redArg(v_inst_2428_, v_inst_2429_, v_inst_2430_, v_inst_2431_, v_inst_2432_, v_inst_2433_, v_inst_2434_, v_n_2435_);
return v___x_2436_;
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___redArg___lam__0(lean_object* v_x_2437_){
_start:
{
if (lean_obj_tag(v_x_2437_) == 1)
{
lean_object* v_fields_2438_; 
v_fields_2438_ = lean_ctor_get(v_x_2437_, 1);
if (lean_obj_tag(v_fields_2438_) == 0)
{
lean_object* v_n_2439_; lean_object* v___x_2440_; 
v_n_2439_ = lean_ctor_get(v_x_2437_, 0);
lean_inc(v_n_2439_);
v___x_2440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2440_, 0, v_n_2439_);
return v___x_2440_;
}
else
{
lean_object* v___x_2441_; 
v___x_2441_ = lean_box(0);
return v___x_2441_;
}
}
else
{
lean_object* v___x_2442_; 
v___x_2442_ = lean_box(0);
return v___x_2442_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___redArg___lam__0___boxed(lean_object* v_x_2443_){
_start:
{
lean_object* v_res_2444_; 
v_res_2444_ = l_Lean_preprocessSyntaxAndResolve___redArg___lam__0(v_x_2443_);
lean_dec_ref(v_x_2443_);
return v_res_2444_;
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___redArg___lam__1(lean_object* v_stx_2445_, lean_object* v_withRef_2446_, lean_object* v___x_2447_, lean_object* v_oldRef_2448_){
_start:
{
lean_object* v_ref_2449_; lean_object* v___x_2450_; 
v_ref_2449_ = l_Lean_replaceRef(v_stx_2445_, v_oldRef_2448_);
v___x_2450_ = lean_apply_3(v_withRef_2446_, lean_box(0), v_ref_2449_, v___x_2447_);
return v___x_2450_;
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___redArg___lam__1___boxed(lean_object* v_stx_2451_, lean_object* v_withRef_2452_, lean_object* v___x_2453_, lean_object* v_oldRef_2454_){
_start:
{
lean_object* v_res_2455_; 
v_res_2455_ = l_Lean_preprocessSyntaxAndResolve___redArg___lam__1(v_stx_2451_, v_withRef_2452_, v___x_2453_, v_oldRef_2454_);
lean_dec(v_oldRef_2454_);
lean_dec(v_stx_2451_);
return v_res_2455_;
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___redArg(lean_object* v_inst_2457_, lean_object* v_inst_2458_, lean_object* v_stx_2459_, lean_object* v_k_2460_){
_start:
{
if (lean_obj_tag(v_stx_2459_) == 3)
{
lean_object* v_val_2461_; lean_object* v_preresolved_2462_; lean_object* v___f_2463_; lean_object* v___x_2464_; lean_object* v_pre_2465_; uint8_t v___x_2466_; 
v_val_2461_ = lean_ctor_get(v_stx_2459_, 2);
v_preresolved_2462_ = lean_ctor_get(v_stx_2459_, 3);
v___f_2463_ = ((lean_object*)(l_Lean_preprocessSyntaxAndResolve___redArg___closed__0));
v___x_2464_ = ((lean_object*)(l_Lean_resolveNamespace___redArg___closed__1));
lean_inc(v_preresolved_2462_);
v_pre_2465_ = l_List_filterMapTR_go___redArg(v___f_2463_, v_preresolved_2462_, v___x_2464_);
v___x_2466_ = l_List_isEmpty___redArg(v_pre_2465_);
if (v___x_2466_ == 0)
{
lean_object* v_toApplicative_2467_; lean_object* v_toPure_2468_; lean_object* v___x_2469_; 
lean_dec_ref_known(v_stx_2459_, 4);
lean_dec(v_k_2460_);
lean_dec_ref(v_inst_2458_);
v_toApplicative_2467_ = lean_ctor_get(v_inst_2457_, 0);
lean_inc_ref(v_toApplicative_2467_);
lean_dec_ref(v_inst_2457_);
v_toPure_2468_ = lean_ctor_get(v_toApplicative_2467_, 1);
lean_inc(v_toPure_2468_);
lean_dec_ref(v_toApplicative_2467_);
v___x_2469_ = lean_apply_2(v_toPure_2468_, lean_box(0), v_pre_2465_);
return v___x_2469_;
}
else
{
lean_object* v_toMonadRef_2470_; lean_object* v_toBind_2471_; lean_object* v_getRef_2472_; lean_object* v_withRef_2473_; lean_object* v___x_2474_; lean_object* v___f_2475_; lean_object* v___x_2476_; 
lean_dec(v_pre_2465_);
v_toMonadRef_2470_ = lean_ctor_get(v_inst_2458_, 1);
lean_inc_ref(v_toMonadRef_2470_);
lean_dec_ref(v_inst_2458_);
v_toBind_2471_ = lean_ctor_get(v_inst_2457_, 1);
lean_inc(v_toBind_2471_);
lean_dec_ref(v_inst_2457_);
v_getRef_2472_ = lean_ctor_get(v_toMonadRef_2470_, 0);
lean_inc(v_getRef_2472_);
v_withRef_2473_ = lean_ctor_get(v_toMonadRef_2470_, 1);
lean_inc(v_withRef_2473_);
lean_dec_ref(v_toMonadRef_2470_);
lean_inc(v_val_2461_);
v___x_2474_ = lean_apply_1(v_k_2460_, v_val_2461_);
v___f_2475_ = lean_alloc_closure((void*)(l_Lean_preprocessSyntaxAndResolve___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_2475_, 0, v_stx_2459_);
lean_closure_set(v___f_2475_, 1, v_withRef_2473_);
lean_closure_set(v___f_2475_, 2, v___x_2474_);
v___x_2476_ = lean_apply_4(v_toBind_2471_, lean_box(0), lean_box(0), v_getRef_2472_, v___f_2475_);
return v___x_2476_;
}
}
else
{
lean_object* v___x_2477_; lean_object* v___x_2478_; 
lean_dec(v_k_2460_);
v___x_2477_ = lean_obj_once(&l_Lean_resolveNamespace___redArg___closed__4, &l_Lean_resolveNamespace___redArg___closed__4_once, _init_l_Lean_resolveNamespace___redArg___closed__4);
v___x_2478_ = l_Lean_throwErrorAt___redArg(v_inst_2457_, v_inst_2458_, v_stx_2459_, v___x_2477_);
return v___x_2478_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve(lean_object* v_m_2479_, lean_object* v_inst_2480_, lean_object* v_inst_2481_, lean_object* v_stx_2482_, lean_object* v_k_2483_){
_start:
{
lean_object* v___x_2484_; 
v___x_2484_ = l_Lean_preprocessSyntaxAndResolve___redArg(v_inst_2480_, v_inst_2481_, v_stx_2482_, v_k_2483_);
return v___x_2484_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst___redArg(lean_object* v_inst_2485_, lean_object* v_inst_2486_, lean_object* v_inst_2487_, lean_object* v_inst_2488_, lean_object* v_inst_2489_, lean_object* v_inst_2490_, lean_object* v_inst_2491_, lean_object* v_stx_2492_){
_start:
{
lean_object* v___x_2493_; lean_object* v___x_2494_; 
lean_inc_ref(v_inst_2491_);
lean_inc_ref(v_inst_2485_);
v___x_2493_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore), 9, 8);
lean_closure_set(v___x_2493_, 0, lean_box(0));
lean_closure_set(v___x_2493_, 1, v_inst_2485_);
lean_closure_set(v___x_2493_, 2, v_inst_2486_);
lean_closure_set(v___x_2493_, 3, v_inst_2487_);
lean_closure_set(v___x_2493_, 4, v_inst_2488_);
lean_closure_set(v___x_2493_, 5, v_inst_2489_);
lean_closure_set(v___x_2493_, 6, v_inst_2490_);
lean_closure_set(v___x_2493_, 7, v_inst_2491_);
v___x_2494_ = l_Lean_preprocessSyntaxAndResolve___redArg(v_inst_2485_, v_inst_2491_, v_stx_2492_, v___x_2493_);
return v___x_2494_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst(lean_object* v_m_2495_, lean_object* v_inst_2496_, lean_object* v_inst_2497_, lean_object* v_inst_2498_, lean_object* v_inst_2499_, lean_object* v_inst_2500_, lean_object* v_inst_2501_, lean_object* v_inst_2502_, lean_object* v_stx_2503_){
_start:
{
lean_object* v___x_2504_; 
v___x_2504_ = l_Lean_resolveGlobalConst___redArg(v_inst_2496_, v_inst_2497_, v_inst_2498_, v_inst_2499_, v_inst_2500_, v_inst_2501_, v_inst_2502_, v_stx_2503_);
return v___x_2504_;
}
}
static lean_object* _init_l_Lean_ensureNonAmbiguous___redArg___closed__1(void){
_start:
{
lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; 
v___x_2506_ = ((lean_object*)(l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__2));
v___x_2507_ = lean_unsigned_to_nat(11u);
v___x_2508_ = lean_unsigned_to_nat(429u);
v___x_2509_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___redArg___closed__0));
v___x_2510_ = ((lean_object*)(l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__0));
v___x_2511_ = l_mkPanicMessageWithDecl(v___x_2510_, v___x_2509_, v___x_2508_, v___x_2507_, v___x_2506_);
return v___x_2511_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNonAmbiguous___redArg(lean_object* v_inst_2515_, lean_object* v_inst_2516_, lean_object* v_id_2517_, lean_object* v_cs_2518_){
_start:
{
if (lean_obj_tag(v_cs_2518_) == 0)
{
lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; 
lean_dec(v_id_2517_);
lean_dec_ref(v_inst_2516_);
v___x_2519_ = lean_box(0);
v___x_2520_ = l_instInhabitedOfMonad___redArg(v_inst_2515_, v___x_2519_);
v___x_2521_ = lean_obj_once(&l_Lean_ensureNonAmbiguous___redArg___closed__1, &l_Lean_ensureNonAmbiguous___redArg___closed__1_once, _init_l_Lean_ensureNonAmbiguous___redArg___closed__1);
v___x_2522_ = l_panic___redArg(v___x_2520_, v___x_2521_);
lean_dec(v___x_2520_);
return v___x_2522_;
}
else
{
lean_object* v_tail_2523_; 
v_tail_2523_ = lean_ctor_get(v_cs_2518_, 1);
if (lean_obj_tag(v_tail_2523_) == 0)
{
lean_object* v_toApplicative_2524_; lean_object* v_toPure_2525_; lean_object* v_head_2526_; lean_object* v___x_2527_; 
v_toApplicative_2524_ = lean_ctor_get(v_inst_2515_, 0);
lean_inc_ref(v_toApplicative_2524_);
lean_dec(v_id_2517_);
lean_dec_ref(v_inst_2516_);
lean_dec_ref(v_inst_2515_);
v_toPure_2525_ = lean_ctor_get(v_toApplicative_2524_, 1);
lean_inc(v_toPure_2525_);
lean_dec_ref(v_toApplicative_2524_);
v_head_2526_ = lean_ctor_get(v_cs_2518_, 0);
lean_inc(v_head_2526_);
lean_dec_ref_known(v_cs_2518_, 2);
v___x_2527_ = lean_apply_2(v_toPure_2525_, lean_box(0), v_head_2526_);
return v___x_2527_;
}
else
{
lean_object* v___f_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; uint8_t v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; 
v___f_2528_ = ((lean_object*)(l_Lean_ensureNoOverload___redArg___closed__0));
v___x_2529_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___redArg___closed__2));
v___x_2530_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___redArg___closed__3));
v___x_2531_ = lean_box(0);
v___x_2532_ = 0;
lean_inc(v_id_2517_);
v___x_2533_ = l_Lean_Syntax_formatStx(v_id_2517_, v___x_2531_, v___x_2532_);
v___x_2534_ = l_Std_Format_defWidth;
v___x_2535_ = lean_unsigned_to_nat(0u);
v___x_2536_ = l_Std_Format_pretty(v___x_2533_, v___x_2534_, v___x_2535_, v___x_2535_);
v___x_2537_ = lean_string_append(v___x_2530_, v___x_2536_);
lean_dec_ref(v___x_2536_);
v___x_2538_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___redArg___closed__4));
v___x_2539_ = lean_string_append(v___x_2537_, v___x_2538_);
v___x_2540_ = lean_box(0);
v___x_2541_ = l_List_mapTR_loop___redArg(v___f_2528_, v_cs_2518_, v___x_2540_);
v___x_2542_ = l_List_toString___redArg(v___x_2529_, v___x_2541_);
v___x_2543_ = lean_string_append(v___x_2539_, v___x_2542_);
lean_dec_ref(v___x_2542_);
v___x_2544_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2544_, 0, v___x_2543_);
v___x_2545_ = l_Lean_MessageData_ofFormat(v___x_2544_);
v___x_2546_ = l_Lean_throwErrorAt___redArg(v_inst_2515_, v_inst_2516_, v_id_2517_, v___x_2545_);
return v___x_2546_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNonAmbiguous(lean_object* v_m_2547_, lean_object* v_inst_2548_, lean_object* v_inst_2549_, lean_object* v_id_2550_, lean_object* v_cs_2551_){
_start:
{
lean_object* v___x_2552_; 
v___x_2552_ = l_Lean_ensureNonAmbiguous___redArg(v_inst_2548_, v_inst_2549_, v_id_2550_, v_cs_2551_);
return v___x_2552_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverload___redArg___lam__0(lean_object* v_inst_2553_, lean_object* v_inst_2554_, lean_object* v_id_2555_, lean_object* v_____do__lift_2556_){
_start:
{
lean_object* v___x_2557_; 
v___x_2557_ = l_Lean_ensureNonAmbiguous___redArg(v_inst_2553_, v_inst_2554_, v_id_2555_, v_____do__lift_2556_);
return v___x_2557_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverload___redArg(lean_object* v_inst_2558_, lean_object* v_inst_2559_, lean_object* v_inst_2560_, lean_object* v_inst_2561_, lean_object* v_inst_2562_, lean_object* v_inst_2563_, lean_object* v_inst_2564_, lean_object* v_id_2565_){
_start:
{
lean_object* v_toBind_2566_; lean_object* v___f_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; 
v_toBind_2566_ = lean_ctor_get(v_inst_2558_, 1);
lean_inc(v_toBind_2566_);
lean_inc(v_id_2565_);
lean_inc_ref(v_inst_2564_);
lean_inc_ref(v_inst_2558_);
v___f_2567_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalConstNoOverload___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2567_, 0, v_inst_2558_);
lean_closure_set(v___f_2567_, 1, v_inst_2564_);
lean_closure_set(v___f_2567_, 2, v_id_2565_);
v___x_2568_ = l_Lean_resolveGlobalConst___redArg(v_inst_2558_, v_inst_2559_, v_inst_2560_, v_inst_2561_, v_inst_2562_, v_inst_2563_, v_inst_2564_, v_id_2565_);
v___x_2569_ = lean_apply_4(v_toBind_2566_, lean_box(0), lean_box(0), v___x_2568_, v___f_2567_);
return v___x_2569_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverload(lean_object* v_m_2570_, lean_object* v_inst_2571_, lean_object* v_inst_2572_, lean_object* v_inst_2573_, lean_object* v_inst_2574_, lean_object* v_inst_2575_, lean_object* v_inst_2576_, lean_object* v_inst_2577_, lean_object* v_id_2578_){
_start:
{
lean_object* v___x_2579_; 
v___x_2579_ = l_Lean_resolveGlobalConstNoOverload___redArg(v_inst_2571_, v_inst_2572_, v_inst_2573_, v_inst_2574_, v_inst_2575_, v_inst_2576_, v_inst_2577_, v_id_2578_);
return v___x_2579_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__0(lean_object* v___f_2580_, lean_object* v___f_2581_, uint8_t v_globalDeclFoundNext_2582_, uint8_t v_globalDeclFound_2583_, lean_object* v_r_2584_){
_start:
{
lean_object* v___x_2585_; lean_object* v_r_2586_; uint8_t v___x_2587_; 
v___x_2585_ = lean_box(0);
v_r_2586_ = l_List_filterTR_loop___redArg(v___f_2580_, v_r_2584_, v___x_2585_);
v___x_2587_ = l_List_isEmpty___redArg(v_r_2586_);
lean_dec(v_r_2586_);
if (v___x_2587_ == 0)
{
lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; 
v___x_2588_ = lean_box(0);
v___x_2589_ = lean_box(v_globalDeclFoundNext_2582_);
v___x_2590_ = lean_apply_2(v___f_2581_, v___x_2588_, v___x_2589_);
return v___x_2590_;
}
else
{
lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; 
v___x_2591_ = lean_box(0);
v___x_2592_ = lean_box(v_globalDeclFound_2583_);
v___x_2593_ = lean_apply_2(v___f_2581_, v___x_2591_, v___x_2592_);
return v___x_2593_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__0___boxed(lean_object* v___f_2594_, lean_object* v___f_2595_, lean_object* v_globalDeclFoundNext_2596_, lean_object* v_globalDeclFound_2597_, lean_object* v_r_2598_){
_start:
{
uint8_t v_globalDeclFoundNext_boxed_2599_; uint8_t v_globalDeclFound_boxed_2600_; lean_object* v_res_2601_; 
v_globalDeclFoundNext_boxed_2599_ = lean_unbox(v_globalDeclFoundNext_2596_);
v_globalDeclFound_boxed_2600_ = lean_unbox(v_globalDeclFound_2597_);
v_res_2601_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__0(v___f_2594_, v___f_2595_, v_globalDeclFoundNext_boxed_2599_, v_globalDeclFound_boxed_2600_, v_r_2598_);
return v_res_2601_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__1___boxed(lean_object* v_str_2602_, lean_object* v_projs_2603_, lean_object* v_inst_2604_, lean_object* v_inst_2605_, lean_object* v_inst_2606_, lean_object* v_inst_2607_, lean_object* v_inst_2608_, lean_object* v_inst_2609_, lean_object* v_view_2610_, lean_object* v_findLocalDecl_x3f_2611_, lean_object* v_pre_2612_, lean_object* v_____r_2613_, lean_object* v_globalDeclFoundNext_2614_){
_start:
{
uint8_t v_globalDeclFoundNext_boxed_2615_; lean_object* v_res_2616_; 
v_globalDeclFoundNext_boxed_2615_ = lean_unbox(v_globalDeclFoundNext_2614_);
v_res_2616_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__1(v_str_2602_, v_projs_2603_, v_inst_2604_, v_inst_2605_, v_inst_2606_, v_inst_2607_, v_inst_2608_, v_inst_2609_, v_view_2610_, v_findLocalDecl_x3f_2611_, v_pre_2612_, v_____r_2613_, v_globalDeclFoundNext_boxed_2615_);
return v_res_2616_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg(lean_object* v_inst_2617_, lean_object* v_inst_2618_, lean_object* v_inst_2619_, lean_object* v_inst_2620_, lean_object* v_inst_2621_, lean_object* v_inst_2622_, lean_object* v_view_2623_, lean_object* v_findLocalDecl_x3f_2624_, lean_object* v_n_2625_, lean_object* v_projs_2626_, uint8_t v_globalDeclFound_2627_){
_start:
{
lean_object* v_toApplicative_2628_; lean_object* v_imported_2629_; lean_object* v_ctx_2630_; lean_object* v_scopes_2631_; lean_object* v_toBind_2632_; lean_object* v_toPure_2633_; lean_object* v___f_2634_; lean_object* v_givenNameView_2635_; uint8_t v___y_2637_; 
v_toApplicative_2628_ = lean_ctor_get(v_inst_2617_, 0);
v_imported_2629_ = lean_ctor_get(v_view_2623_, 1);
v_ctx_2630_ = lean_ctor_get(v_view_2623_, 2);
v_scopes_2631_ = lean_ctor_get(v_view_2623_, 3);
v_toBind_2632_ = lean_ctor_get(v_inst_2617_, 1);
v_toPure_2633_ = lean_ctor_get(v_toApplicative_2628_, 1);
v___f_2634_ = ((lean_object*)(l_Lean_filterFieldList___redArg___closed__0));
lean_inc(v_scopes_2631_);
lean_inc(v_ctx_2630_);
lean_inc(v_imported_2629_);
lean_inc(v_n_2625_);
v_givenNameView_2635_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_givenNameView_2635_, 0, v_n_2625_);
lean_ctor_set(v_givenNameView_2635_, 1, v_imported_2629_);
lean_ctor_set(v_givenNameView_2635_, 2, v_ctx_2630_);
lean_ctor_set(v_givenNameView_2635_, 3, v_scopes_2631_);
if (v_globalDeclFound_2627_ == 0)
{
v___y_2637_ = v_globalDeclFound_2627_;
goto v___jp_2636_;
}
else
{
uint8_t v___x_2673_; 
v___x_2673_ = l_List_isEmpty___redArg(v_projs_2626_);
if (v___x_2673_ == 0)
{
v___y_2637_ = v_globalDeclFound_2627_;
goto v___jp_2636_;
}
else
{
uint8_t v___x_2674_; 
v___x_2674_ = 0;
v___y_2637_ = v___x_2674_;
goto v___jp_2636_;
}
}
v___jp_2636_:
{
lean_object* v___x_2638_; lean_object* v___x_2639_; 
v___x_2638_ = lean_box(v___y_2637_);
lean_inc_ref(v_findLocalDecl_x3f_2624_);
lean_inc_ref(v_givenNameView_2635_);
v___x_2639_ = lean_apply_2(v_findLocalDecl_x3f_2624_, v_givenNameView_2635_, v___x_2638_);
if (lean_obj_tag(v___x_2639_) == 0)
{
if (lean_obj_tag(v_n_2625_) == 1)
{
lean_object* v_pre_2640_; lean_object* v_str_2641_; lean_object* v___f_2642_; 
v_pre_2640_ = lean_ctor_get(v_n_2625_, 0);
lean_inc_n(v_pre_2640_, 2);
v_str_2641_ = lean_ctor_get(v_n_2625_, 1);
lean_inc_ref_n(v_str_2641_, 2);
lean_dec_ref_known(v_n_2625_, 2);
lean_inc_ref(v_findLocalDecl_x3f_2624_);
lean_inc_ref(v_view_2623_);
lean_inc(v_inst_2622_);
lean_inc_ref(v_inst_2621_);
lean_inc(v_inst_2620_);
lean_inc_ref(v_inst_2619_);
lean_inc_ref(v_inst_2618_);
lean_inc_ref(v_inst_2617_);
lean_inc(v_projs_2626_);
v___f_2642_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__1___boxed), 13, 11);
lean_closure_set(v___f_2642_, 0, v_str_2641_);
lean_closure_set(v___f_2642_, 1, v_projs_2626_);
lean_closure_set(v___f_2642_, 2, v_inst_2617_);
lean_closure_set(v___f_2642_, 3, v_inst_2618_);
lean_closure_set(v___f_2642_, 4, v_inst_2619_);
lean_closure_set(v___f_2642_, 5, v_inst_2620_);
lean_closure_set(v___f_2642_, 6, v_inst_2621_);
lean_closure_set(v___f_2642_, 7, v_inst_2622_);
lean_closure_set(v___f_2642_, 8, v_view_2623_);
lean_closure_set(v___f_2642_, 9, v_findLocalDecl_x3f_2624_);
lean_closure_set(v___f_2642_, 10, v_pre_2640_);
if (v_globalDeclFound_2627_ == 0)
{
uint8_t v_globalDeclFoundNext_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___f_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; 
lean_inc(v_toBind_2632_);
lean_dec_ref(v_str_2641_);
lean_dec(v_pre_2640_);
lean_dec(v_projs_2626_);
lean_dec_ref(v_findLocalDecl_x3f_2624_);
lean_dec_ref(v_view_2623_);
v_globalDeclFoundNext_2643_ = 1;
v___x_2644_ = lean_box(v_globalDeclFoundNext_2643_);
v___x_2645_ = lean_box(v_globalDeclFound_2627_);
v___f_2646_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2646_, 0, v___f_2634_);
lean_closure_set(v___f_2646_, 1, v___f_2642_);
lean_closure_set(v___f_2646_, 2, v___x_2644_);
lean_closure_set(v___f_2646_, 3, v___x_2645_);
v___x_2647_ = l_Lean_MacroScopesView_review(v_givenNameView_2635_);
v___x_2648_ = l_Lean_resolveGlobalName___redArg(v_inst_2617_, v_inst_2618_, v_inst_2619_, v_inst_2620_, v_inst_2621_, v_inst_2622_, v___x_2647_, v_globalDeclFound_2627_);
v___x_2649_ = lean_apply_4(v_toBind_2632_, lean_box(0), lean_box(0), v___x_2648_, v___f_2646_);
return v___x_2649_;
}
else
{
lean_object* v___x_2650_; lean_object* v___x_2651_; 
lean_dec_ref(v___f_2642_);
lean_dec_ref_known(v_givenNameView_2635_, 4);
v___x_2650_ = lean_box(0);
v___x_2651_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__1(v_str_2641_, v_projs_2626_, v_inst_2617_, v_inst_2618_, v_inst_2619_, v_inst_2620_, v_inst_2621_, v_inst_2622_, v_view_2623_, v_findLocalDecl_x3f_2624_, v_pre_2640_, v___x_2650_, v_globalDeclFound_2627_);
return v___x_2651_;
}
}
else
{
lean_object* v___x_2652_; lean_object* v___x_2653_; 
lean_inc(v_toPure_2633_);
lean_dec_ref_known(v_givenNameView_2635_, 4);
lean_dec(v_projs_2626_);
lean_dec(v_n_2625_);
lean_dec_ref(v_findLocalDecl_x3f_2624_);
lean_dec_ref(v_view_2623_);
lean_dec(v_inst_2622_);
lean_dec_ref(v_inst_2621_);
lean_dec(v_inst_2620_);
lean_dec_ref(v_inst_2619_);
lean_dec_ref(v_inst_2618_);
lean_dec_ref(v_inst_2617_);
v___x_2652_ = lean_box(0);
v___x_2653_ = lean_apply_2(v_toPure_2633_, lean_box(0), v___x_2652_);
return v___x_2653_;
}
}
else
{
lean_object* v___x_2655_; uint8_t v_isShared_2656_; uint8_t v_isSharedCheck_2670_; 
lean_inc(v_toPure_2633_);
lean_dec_ref_known(v_givenNameView_2635_, 4);
lean_dec(v_n_2625_);
lean_dec_ref(v_findLocalDecl_x3f_2624_);
lean_dec_ref(v_view_2623_);
lean_dec(v_inst_2622_);
lean_dec_ref(v_inst_2621_);
lean_dec(v_inst_2620_);
lean_dec_ref(v_inst_2619_);
lean_dec_ref(v_inst_2618_);
v_isSharedCheck_2670_ = !lean_is_exclusive(v_inst_2617_);
if (v_isSharedCheck_2670_ == 0)
{
lean_object* v_unused_2671_; lean_object* v_unused_2672_; 
v_unused_2671_ = lean_ctor_get(v_inst_2617_, 1);
lean_dec(v_unused_2671_);
v_unused_2672_ = lean_ctor_get(v_inst_2617_, 0);
lean_dec(v_unused_2672_);
v___x_2655_ = v_inst_2617_;
v_isShared_2656_ = v_isSharedCheck_2670_;
goto v_resetjp_2654_;
}
else
{
lean_dec(v_inst_2617_);
v___x_2655_ = lean_box(0);
v_isShared_2656_ = v_isSharedCheck_2670_;
goto v_resetjp_2654_;
}
v_resetjp_2654_:
{
lean_object* v_val_2657_; lean_object* v___x_2659_; uint8_t v_isShared_2660_; uint8_t v_isSharedCheck_2669_; 
v_val_2657_ = lean_ctor_get(v___x_2639_, 0);
v_isSharedCheck_2669_ = !lean_is_exclusive(v___x_2639_);
if (v_isSharedCheck_2669_ == 0)
{
v___x_2659_ = v___x_2639_;
v_isShared_2660_ = v_isSharedCheck_2669_;
goto v_resetjp_2658_;
}
else
{
lean_inc(v_val_2657_);
lean_dec(v___x_2639_);
v___x_2659_ = lean_box(0);
v_isShared_2660_ = v_isSharedCheck_2669_;
goto v_resetjp_2658_;
}
v_resetjp_2658_:
{
lean_object* v___x_2661_; lean_object* v___x_2663_; 
v___x_2661_ = l_Lean_LocalDecl_toExpr(v_val_2657_);
if (v_isShared_2656_ == 0)
{
lean_ctor_set(v___x_2655_, 1, v_projs_2626_);
lean_ctor_set(v___x_2655_, 0, v___x_2661_);
v___x_2663_ = v___x_2655_;
goto v_reusejp_2662_;
}
else
{
lean_object* v_reuseFailAlloc_2668_; 
v_reuseFailAlloc_2668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2668_, 0, v___x_2661_);
lean_ctor_set(v_reuseFailAlloc_2668_, 1, v_projs_2626_);
v___x_2663_ = v_reuseFailAlloc_2668_;
goto v_reusejp_2662_;
}
v_reusejp_2662_:
{
lean_object* v___x_2665_; 
if (v_isShared_2660_ == 0)
{
lean_ctor_set(v___x_2659_, 0, v___x_2663_);
v___x_2665_ = v___x_2659_;
goto v_reusejp_2664_;
}
else
{
lean_object* v_reuseFailAlloc_2667_; 
v_reuseFailAlloc_2667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2667_, 0, v___x_2663_);
v___x_2665_ = v_reuseFailAlloc_2667_;
goto v_reusejp_2664_;
}
v_reusejp_2664_:
{
lean_object* v___x_2666_; 
v___x_2666_ = lean_apply_2(v_toPure_2633_, lean_box(0), v___x_2665_);
return v___x_2666_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__1(lean_object* v_str_2675_, lean_object* v_projs_2676_, lean_object* v_inst_2677_, lean_object* v_inst_2678_, lean_object* v_inst_2679_, lean_object* v_inst_2680_, lean_object* v_inst_2681_, lean_object* v_inst_2682_, lean_object* v_view_2683_, lean_object* v_findLocalDecl_x3f_2684_, lean_object* v_pre_2685_, lean_object* v_____r_2686_, uint8_t v_globalDeclFoundNext_2687_){
_start:
{
lean_object* v___x_2688_; lean_object* v___x_2689_; 
v___x_2688_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2688_, 0, v_str_2675_);
lean_ctor_set(v___x_2688_, 1, v_projs_2676_);
v___x_2689_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg(v_inst_2677_, v_inst_2678_, v_inst_2679_, v_inst_2680_, v_inst_2681_, v_inst_2682_, v_view_2683_, v_findLocalDecl_x3f_2684_, v_pre_2685_, v___x_2688_, v_globalDeclFoundNext_2687_);
return v___x_2689_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___boxed(lean_object* v_inst_2690_, lean_object* v_inst_2691_, lean_object* v_inst_2692_, lean_object* v_inst_2693_, lean_object* v_inst_2694_, lean_object* v_inst_2695_, lean_object* v_view_2696_, lean_object* v_findLocalDecl_x3f_2697_, lean_object* v_n_2698_, lean_object* v_projs_2699_, lean_object* v_globalDeclFound_2700_){
_start:
{
uint8_t v_globalDeclFound_boxed_2701_; lean_object* v_res_2702_; 
v_globalDeclFound_boxed_2701_ = lean_unbox(v_globalDeclFound_2700_);
v_res_2702_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg(v_inst_2690_, v_inst_2691_, v_inst_2692_, v_inst_2693_, v_inst_2694_, v_inst_2695_, v_view_2696_, v_findLocalDecl_x3f_2697_, v_n_2698_, v_projs_2699_, v_globalDeclFound_boxed_2701_);
return v_res_2702_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop(lean_object* v_m_2703_, lean_object* v_inst_2704_, lean_object* v_inst_2705_, lean_object* v_inst_2706_, lean_object* v_inst_2707_, lean_object* v_inst_2708_, lean_object* v_inst_2709_, lean_object* v_view_2710_, lean_object* v_findLocalDecl_x3f_2711_, lean_object* v_n_2712_, lean_object* v_projs_2713_, uint8_t v_globalDeclFound_2714_){
_start:
{
lean_object* v___x_2715_; 
v___x_2715_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg(v_inst_2704_, v_inst_2705_, v_inst_2706_, v_inst_2707_, v_inst_2708_, v_inst_2709_, v_view_2710_, v_findLocalDecl_x3f_2711_, v_n_2712_, v_projs_2713_, v_globalDeclFound_2714_);
return v___x_2715_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___boxed(lean_object* v_m_2716_, lean_object* v_inst_2717_, lean_object* v_inst_2718_, lean_object* v_inst_2719_, lean_object* v_inst_2720_, lean_object* v_inst_2721_, lean_object* v_inst_2722_, lean_object* v_view_2723_, lean_object* v_findLocalDecl_x3f_2724_, lean_object* v_n_2725_, lean_object* v_projs_2726_, lean_object* v_globalDeclFound_2727_){
_start:
{
uint8_t v_globalDeclFound_boxed_2728_; lean_object* v_res_2729_; 
v_globalDeclFound_boxed_2728_ = lean_unbox(v_globalDeclFound_2727_);
v_res_2729_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop(v_m_2716_, v_inst_2717_, v_inst_2718_, v_inst_2719_, v_inst_2720_, v_inst_2721_, v_inst_2722_, v_view_2723_, v_findLocalDecl_x3f_2724_, v_n_2725_, v_projs_2726_, v_globalDeclFound_boxed_2728_);
return v_res_2729_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_go(lean_object* v_localDecl_2730_, lean_object* v_givenNameView_2731_, lean_object* v_fullDeclName_2732_, lean_object* v_ns_2733_){
_start:
{
lean_object* v_name_2734_; lean_object* v_imported_2735_; lean_object* v_ctx_2736_; lean_object* v_scopes_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; uint8_t v___x_2741_; 
v_name_2734_ = lean_ctor_get(v_givenNameView_2731_, 0);
v_imported_2735_ = lean_ctor_get(v_givenNameView_2731_, 1);
v_ctx_2736_ = lean_ctor_get(v_givenNameView_2731_, 2);
v_scopes_2737_ = lean_ctor_get(v_givenNameView_2731_, 3);
lean_inc(v_name_2734_);
lean_inc(v_ns_2733_);
v___x_2738_ = l_Lean_Name_append(v_ns_2733_, v_name_2734_);
lean_inc(v_scopes_2737_);
lean_inc(v_ctx_2736_);
lean_inc(v_imported_2735_);
v___x_2739_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2739_, 0, v___x_2738_);
lean_ctor_set(v___x_2739_, 1, v_imported_2735_);
lean_ctor_set(v___x_2739_, 2, v_ctx_2736_);
lean_ctor_set(v___x_2739_, 3, v_scopes_2737_);
v___x_2740_ = l_Lean_MacroScopesView_review(v___x_2739_);
v___x_2741_ = lean_name_eq(v___x_2740_, v_fullDeclName_2732_);
lean_dec(v___x_2740_);
if (v___x_2741_ == 0)
{
if (lean_obj_tag(v_ns_2733_) == 1)
{
lean_object* v_pre_2742_; 
v_pre_2742_ = lean_ctor_get(v_ns_2733_, 0);
lean_inc(v_pre_2742_);
lean_dec_ref_known(v_ns_2733_, 2);
v_ns_2733_ = v_pre_2742_;
goto _start;
}
else
{
lean_object* v___x_2744_; 
lean_dec(v_ns_2733_);
lean_dec_ref(v_givenNameView_2731_);
lean_dec_ref(v_localDecl_2730_);
v___x_2744_ = lean_box(0);
return v___x_2744_;
}
}
else
{
lean_object* v___x_2745_; 
lean_dec(v_ns_2733_);
lean_dec_ref(v_givenNameView_2731_);
v___x_2745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2745_, 0, v_localDecl_2730_);
return v___x_2745_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_go___boxed(lean_object* v_localDecl_2746_, lean_object* v_givenNameView_2747_, lean_object* v_fullDeclName_2748_, lean_object* v_ns_2749_){
_start:
{
lean_object* v_res_2750_; 
v_res_2750_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_go(v_localDecl_2746_, v_givenNameView_2747_, v_fullDeclName_2748_, v_ns_2749_);
lean_dec(v_fullDeclName_2748_);
return v_res_2750_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__0(lean_object* v_localDecl_2751_, lean_object* v_givenName_2752_){
_start:
{
lean_object* v___x_2753_; uint8_t v___x_2754_; 
v___x_2753_ = l_Lean_LocalDecl_userName(v_localDecl_2751_);
v___x_2754_ = lean_name_eq(v___x_2753_, v_givenName_2752_);
lean_dec(v___x_2753_);
if (v___x_2754_ == 0)
{
lean_object* v___x_2755_; 
lean_dec_ref(v_localDecl_2751_);
v___x_2755_ = lean_box(0);
return v___x_2755_;
}
else
{
lean_object* v___x_2756_; 
v___x_2756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2756_, 0, v_localDecl_2751_);
return v___x_2756_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__0___boxed(lean_object* v_localDecl_2757_, lean_object* v_givenName_2758_){
_start:
{
lean_object* v_res_2759_; 
v_res_2759_ = l_Lean_resolveLocalName___redArg___lam__0(v_localDecl_2757_, v_givenName_2758_);
lean_dec(v_givenName_2758_);
return v_res_2759_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__1(lean_object* v_matchLocalDecl_x3f_2760_, lean_object* v_givenName_2761_, uint8_t v_skipAuxDecl_2762_, lean_object* v___f_2763_, lean_object* v_auxDeclToFullName_2764_, lean_object* v_currNamespace_2765_, lean_object* v_givenNameView_2766_, lean_object* v_x_2767_){
_start:
{
if (lean_obj_tag(v_x_2767_) == 0)
{
lean_dec_ref(v_givenNameView_2766_);
lean_dec(v_currNamespace_2765_);
lean_dec(v_auxDeclToFullName_2764_);
lean_dec_ref(v___f_2763_);
lean_dec(v_givenName_2761_);
lean_dec_ref(v_matchLocalDecl_x3f_2760_);
return v_x_2767_;
}
else
{
lean_object* v_val_2768_; uint8_t v___x_2769_; 
v_val_2768_ = lean_ctor_get(v_x_2767_, 0);
v___x_2769_ = l_Lean_LocalDecl_isAuxDecl(v_val_2768_);
if (v___x_2769_ == 0)
{
lean_object* v___x_2770_; 
lean_inc(v_val_2768_);
lean_dec_ref_known(v_x_2767_, 1);
lean_dec_ref(v_givenNameView_2766_);
lean_dec(v_currNamespace_2765_);
lean_dec(v_auxDeclToFullName_2764_);
lean_dec_ref(v___f_2763_);
v___x_2770_ = lean_apply_2(v_matchLocalDecl_x3f_2760_, v_val_2768_, v_givenName_2761_);
return v___x_2770_;
}
else
{
if (v_skipAuxDecl_2762_ == 0)
{
if (v___x_2769_ == 0)
{
lean_object* v___x_2771_; 
lean_dec_ref_known(v_x_2767_, 1);
lean_dec_ref(v_givenNameView_2766_);
lean_dec(v_currNamespace_2765_);
lean_dec(v_auxDeclToFullName_2764_);
lean_dec_ref(v___f_2763_);
lean_dec(v_givenName_2761_);
lean_dec_ref(v_matchLocalDecl_x3f_2760_);
v___x_2771_ = lean_box(0);
return v___x_2771_;
}
else
{
lean_object* v___x_2772_; lean_object* v___x_2773_; 
v___x_2772_ = l_Lean_LocalDecl_fvarId(v_val_2768_);
v___x_2773_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v___f_2763_, v_auxDeclToFullName_2764_, v___x_2772_);
if (lean_obj_tag(v___x_2773_) == 1)
{
lean_object* v_val_2774_; lean_object* v_fullDeclView_2775_; lean_object* v___y_2777_; lean_object* v_name_2798_; lean_object* v___x_2799_; 
lean_dec(v_givenName_2761_);
lean_dec_ref(v_matchLocalDecl_x3f_2760_);
v_val_2774_ = lean_ctor_get(v___x_2773_, 0);
lean_inc(v_val_2774_);
lean_dec_ref_known(v___x_2773_, 1);
v_fullDeclView_2775_ = l_Lean_extractMacroScopes(v_val_2774_);
v_name_2798_ = lean_ctor_get(v_fullDeclView_2775_, 0);
lean_inc_n(v_name_2798_, 2);
v___x_2799_ = l_Lean_privateToUserName_x3f(v_name_2798_);
if (lean_obj_tag(v___x_2799_) == 0)
{
v___y_2777_ = v_name_2798_;
goto v___jp_2776_;
}
else
{
lean_object* v_val_2800_; 
lean_dec(v_name_2798_);
v_val_2800_ = lean_ctor_get(v___x_2799_, 0);
lean_inc(v_val_2800_);
lean_dec_ref_known(v___x_2799_, 1);
v___y_2777_ = v_val_2800_;
goto v___jp_2776_;
}
v___jp_2776_:
{
lean_object* v_imported_2778_; lean_object* v_ctx_2779_; lean_object* v_scopes_2780_; lean_object* v___x_2782_; uint8_t v_isShared_2783_; uint8_t v_isSharedCheck_2796_; 
v_imported_2778_ = lean_ctor_get(v_fullDeclView_2775_, 1);
v_ctx_2779_ = lean_ctor_get(v_fullDeclView_2775_, 2);
v_scopes_2780_ = lean_ctor_get(v_fullDeclView_2775_, 3);
v_isSharedCheck_2796_ = !lean_is_exclusive(v_fullDeclView_2775_);
if (v_isSharedCheck_2796_ == 0)
{
lean_object* v_unused_2797_; 
v_unused_2797_ = lean_ctor_get(v_fullDeclView_2775_, 0);
lean_dec(v_unused_2797_);
v___x_2782_ = v_fullDeclView_2775_;
v_isShared_2783_ = v_isSharedCheck_2796_;
goto v_resetjp_2781_;
}
else
{
lean_inc(v_scopes_2780_);
lean_inc(v_ctx_2779_);
lean_inc(v_imported_2778_);
lean_dec(v_fullDeclView_2775_);
v___x_2782_ = lean_box(0);
v_isShared_2783_ = v_isSharedCheck_2796_;
goto v_resetjp_2781_;
}
v_resetjp_2781_:
{
lean_object* v_fullDeclView_2785_; 
if (v_isShared_2783_ == 0)
{
lean_ctor_set(v___x_2782_, 0, v___y_2777_);
v_fullDeclView_2785_ = v___x_2782_;
goto v_reusejp_2784_;
}
else
{
lean_object* v_reuseFailAlloc_2795_; 
v_reuseFailAlloc_2795_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2795_, 0, v___y_2777_);
lean_ctor_set(v_reuseFailAlloc_2795_, 1, v_imported_2778_);
lean_ctor_set(v_reuseFailAlloc_2795_, 2, v_ctx_2779_);
lean_ctor_set(v_reuseFailAlloc_2795_, 3, v_scopes_2780_);
v_fullDeclView_2785_ = v_reuseFailAlloc_2795_;
goto v_reusejp_2784_;
}
v_reusejp_2784_:
{
lean_object* v_fullDeclName_2786_; uint8_t v___x_2787_; 
lean_inc_ref(v_fullDeclView_2785_);
v_fullDeclName_2786_ = l_Lean_MacroScopesView_review(v_fullDeclView_2785_);
v___x_2787_ = l_Lean_Name_isPrefixOf(v_currNamespace_2765_, v_fullDeclName_2786_);
if (v___x_2787_ == 0)
{
lean_object* v___x_2788_; 
lean_inc(v_val_2768_);
lean_dec_ref(v_fullDeclView_2785_);
lean_dec_ref_known(v_x_2767_, 1);
v___x_2788_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_go(v_val_2768_, v_givenNameView_2766_, v_fullDeclName_2786_, v_currNamespace_2765_);
lean_dec(v_fullDeclName_2786_);
return v___x_2788_;
}
else
{
lean_object* v___x_2789_; lean_object* v_localDeclNameView_2790_; uint8_t v___x_2791_; 
lean_dec(v_fullDeclName_2786_);
lean_dec(v_currNamespace_2765_);
v___x_2789_ = l_Lean_LocalDecl_userName(v_val_2768_);
v_localDeclNameView_2790_ = l_Lean_extractMacroScopes(v___x_2789_);
v___x_2791_ = l_Lean_MacroScopesView_isSuffixOf(v_localDeclNameView_2790_, v_givenNameView_2766_);
lean_dec_ref(v_localDeclNameView_2790_);
if (v___x_2791_ == 0)
{
lean_object* v___x_2792_; 
lean_dec_ref(v_fullDeclView_2785_);
lean_dec_ref_known(v_x_2767_, 1);
lean_dec_ref(v_givenNameView_2766_);
v___x_2792_ = lean_box(0);
return v___x_2792_;
}
else
{
uint8_t v___x_2793_; 
v___x_2793_ = l_Lean_MacroScopesView_isSuffixOf(v_givenNameView_2766_, v_fullDeclView_2785_);
lean_dec_ref(v_fullDeclView_2785_);
lean_dec_ref(v_givenNameView_2766_);
if (v___x_2793_ == 0)
{
lean_object* v___x_2794_; 
lean_dec_ref_known(v_x_2767_, 1);
v___x_2794_ = lean_box(0);
return v___x_2794_;
}
else
{
return v_x_2767_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2801_; 
lean_inc(v_val_2768_);
lean_dec(v___x_2773_);
lean_dec_ref_known(v_x_2767_, 1);
lean_dec_ref(v_givenNameView_2766_);
lean_dec(v_currNamespace_2765_);
v___x_2801_ = lean_apply_2(v_matchLocalDecl_x3f_2760_, v_val_2768_, v_givenName_2761_);
return v___x_2801_;
}
}
}
else
{
lean_object* v___x_2802_; 
lean_dec_ref_known(v_x_2767_, 1);
lean_dec_ref(v_givenNameView_2766_);
lean_dec(v_currNamespace_2765_);
lean_dec(v_auxDeclToFullName_2764_);
lean_dec_ref(v___f_2763_);
lean_dec(v_givenName_2761_);
lean_dec_ref(v_matchLocalDecl_x3f_2760_);
v___x_2802_ = lean_box(0);
return v___x_2802_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__1___boxed(lean_object* v_matchLocalDecl_x3f_2803_, lean_object* v_givenName_2804_, lean_object* v_skipAuxDecl_2805_, lean_object* v___f_2806_, lean_object* v_auxDeclToFullName_2807_, lean_object* v_currNamespace_2808_, lean_object* v_givenNameView_2809_, lean_object* v_x_2810_){
_start:
{
uint8_t v_skipAuxDecl_boxed_2811_; lean_object* v_res_2812_; 
v_skipAuxDecl_boxed_2811_ = lean_unbox(v_skipAuxDecl_2805_);
v_res_2812_ = l_Lean_resolveLocalName___redArg___lam__1(v_matchLocalDecl_x3f_2803_, v_givenName_2804_, v_skipAuxDecl_boxed_2811_, v___f_2806_, v_auxDeclToFullName_2807_, v_currNamespace_2808_, v_givenNameView_2809_, v_x_2810_);
return v_res_2812_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__2(lean_object* v_localDecl_x3f_2813_, lean_object* v_matchLocalDecl_x3f_2814_, lean_object* v_givenName_2815_, lean_object* v_x_2816_){
_start:
{
if (lean_obj_tag(v_x_2816_) == 0)
{
lean_dec(v_givenName_2815_);
lean_dec_ref(v_matchLocalDecl_x3f_2814_);
return v_x_2816_;
}
else
{
lean_object* v_val_2817_; uint8_t v___x_2818_; 
v_val_2817_ = lean_ctor_get(v_x_2816_, 0);
lean_inc(v_val_2817_);
lean_dec_ref_known(v_x_2816_, 1);
v___x_2818_ = l_Lean_LocalDecl_isAuxDecl(v_val_2817_);
if (v___x_2818_ == 0)
{
lean_dec(v_val_2817_);
lean_dec(v_givenName_2815_);
lean_dec_ref(v_matchLocalDecl_x3f_2814_);
lean_inc(v_localDecl_x3f_2813_);
return v_localDecl_x3f_2813_;
}
else
{
lean_object* v___x_2819_; 
v___x_2819_ = lean_apply_2(v_matchLocalDecl_x3f_2814_, v_val_2817_, v_givenName_2815_);
return v___x_2819_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__2___boxed(lean_object* v_localDecl_x3f_2820_, lean_object* v_matchLocalDecl_x3f_2821_, lean_object* v_givenName_2822_, lean_object* v_x_2823_){
_start:
{
lean_object* v_res_2824_; 
v_res_2824_ = l_Lean_resolveLocalName___redArg___lam__2(v_localDecl_x3f_2820_, v_matchLocalDecl_x3f_2821_, v_givenName_2822_, v_x_2823_);
lean_dec(v_localDecl_x3f_2820_);
return v_res_2824_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__3(lean_object* v_lctx_2844_, lean_object* v_matchLocalDecl_x3f_2845_, lean_object* v___f_2846_, lean_object* v_auxDeclToFullName_2847_, lean_object* v_currNamespace_2848_, lean_object* v_givenNameView_2849_, uint8_t v_skipAuxDecl_2850_){
_start:
{
lean_object* v_decls_2851_; lean_object* v_givenName_2852_; lean_object* v___x_2853_; lean_object* v___f_2854_; lean_object* v___x_2855_; lean_object* v_localDecl_x3f_2856_; 
v_decls_2851_ = lean_ctor_get(v_lctx_2844_, 1);
lean_inc_ref_n(v_decls_2851_, 2);
lean_dec_ref(v_lctx_2844_);
lean_inc_ref(v_givenNameView_2849_);
v_givenName_2852_ = l_Lean_MacroScopesView_review(v_givenNameView_2849_);
v___x_2853_ = lean_box(v_skipAuxDecl_2850_);
lean_inc(v_givenName_2852_);
lean_inc_ref(v_matchLocalDecl_x3f_2845_);
v___f_2854_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_2854_, 0, v_matchLocalDecl_x3f_2845_);
lean_closure_set(v___f_2854_, 1, v_givenName_2852_);
lean_closure_set(v___f_2854_, 2, v___x_2853_);
lean_closure_set(v___f_2854_, 3, v___f_2846_);
lean_closure_set(v___f_2854_, 4, v_auxDeclToFullName_2847_);
lean_closure_set(v___f_2854_, 5, v_currNamespace_2848_);
lean_closure_set(v___f_2854_, 6, v_givenNameView_2849_);
v___x_2855_ = ((lean_object*)(l_Lean_resolveLocalName___redArg___lam__3___closed__9));
v_localDecl_x3f_2856_ = l_Lean_PersistentArray_findSomeRevM_x3f___redArg(v___x_2855_, v_decls_2851_, v___f_2854_);
if (lean_obj_tag(v_localDecl_x3f_2856_) == 0)
{
if (v_skipAuxDecl_2850_ == 0)
{
lean_object* v___f_2857_; lean_object* v___x_2858_; 
v___f_2857_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_2857_, 0, v_localDecl_x3f_2856_);
lean_closure_set(v___f_2857_, 1, v_matchLocalDecl_x3f_2845_);
lean_closure_set(v___f_2857_, 2, v_givenName_2852_);
v___x_2858_ = l_Lean_PersistentArray_findSomeRevM_x3f___redArg(v___x_2855_, v_decls_2851_, v___f_2857_);
return v___x_2858_;
}
else
{
lean_dec(v_givenName_2852_);
lean_dec_ref(v_decls_2851_);
lean_dec_ref(v_matchLocalDecl_x3f_2845_);
return v_localDecl_x3f_2856_;
}
}
else
{
lean_dec(v_givenName_2852_);
lean_dec_ref(v_decls_2851_);
lean_dec_ref(v_matchLocalDecl_x3f_2845_);
return v_localDecl_x3f_2856_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__3___boxed(lean_object* v_lctx_2859_, lean_object* v_matchLocalDecl_x3f_2860_, lean_object* v___f_2861_, lean_object* v_auxDeclToFullName_2862_, lean_object* v_currNamespace_2863_, lean_object* v_givenNameView_2864_, lean_object* v_skipAuxDecl_2865_){
_start:
{
uint8_t v_skipAuxDecl_boxed_2866_; lean_object* v_res_2867_; 
v_skipAuxDecl_boxed_2866_ = lean_unbox(v_skipAuxDecl_2865_);
v_res_2867_ = l_Lean_resolveLocalName___redArg___lam__3(v_lctx_2859_, v_matchLocalDecl_x3f_2860_, v___f_2861_, v_auxDeclToFullName_2862_, v_currNamespace_2863_, v_givenNameView_2864_, v_skipAuxDecl_boxed_2866_);
return v_res_2867_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__4(lean_object* v_n_2868_, lean_object* v_lctx_2869_, lean_object* v_matchLocalDecl_x3f_2870_, lean_object* v___f_2871_, lean_object* v_auxDeclToFullName_2872_, lean_object* v_inst_2873_, lean_object* v_inst_2874_, lean_object* v_inst_2875_, lean_object* v_inst_2876_, lean_object* v_inst_2877_, lean_object* v_inst_2878_, lean_object* v_currNamespace_2879_){
_start:
{
lean_object* v_view_2880_; lean_object* v_name_2881_; lean_object* v_findLocalDecl_x3f_2882_; lean_object* v___x_2883_; uint8_t v___x_2884_; lean_object* v___x_2885_; 
v_view_2880_ = l_Lean_extractMacroScopes(v_n_2868_);
v_name_2881_ = lean_ctor_get(v_view_2880_, 0);
lean_inc(v_name_2881_);
v_findLocalDecl_x3f_2882_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___redArg___lam__3___boxed), 7, 5);
lean_closure_set(v_findLocalDecl_x3f_2882_, 0, v_lctx_2869_);
lean_closure_set(v_findLocalDecl_x3f_2882_, 1, v_matchLocalDecl_x3f_2870_);
lean_closure_set(v_findLocalDecl_x3f_2882_, 2, v___f_2871_);
lean_closure_set(v_findLocalDecl_x3f_2882_, 3, v_auxDeclToFullName_2872_);
lean_closure_set(v_findLocalDecl_x3f_2882_, 4, v_currNamespace_2879_);
v___x_2883_ = lean_box(0);
v___x_2884_ = 0;
v___x_2885_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg(v_inst_2873_, v_inst_2874_, v_inst_2875_, v_inst_2876_, v_inst_2877_, v_inst_2878_, v_view_2880_, v_findLocalDecl_x3f_2882_, v_name_2881_, v___x_2883_, v___x_2884_);
return v___x_2885_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__5(lean_object* v_inst_2886_, lean_object* v_n_2887_, lean_object* v_lctx_2888_, lean_object* v_matchLocalDecl_x3f_2889_, lean_object* v___f_2890_, lean_object* v_inst_2891_, lean_object* v_inst_2892_, lean_object* v_inst_2893_, lean_object* v_inst_2894_, lean_object* v_inst_2895_, lean_object* v_toBind_2896_, lean_object* v_____do__lift_2897_){
_start:
{
lean_object* v_auxDeclToFullName_2898_; lean_object* v_getCurrNamespace_2899_; lean_object* v___f_2900_; lean_object* v___x_2901_; 
v_auxDeclToFullName_2898_ = lean_ctor_get(v_____do__lift_2897_, 2);
lean_inc(v_auxDeclToFullName_2898_);
lean_dec_ref(v_____do__lift_2897_);
v_getCurrNamespace_2899_ = lean_ctor_get(v_inst_2886_, 0);
lean_inc(v_getCurrNamespace_2899_);
v___f_2900_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___redArg___lam__4), 12, 11);
lean_closure_set(v___f_2900_, 0, v_n_2887_);
lean_closure_set(v___f_2900_, 1, v_lctx_2888_);
lean_closure_set(v___f_2900_, 2, v_matchLocalDecl_x3f_2889_);
lean_closure_set(v___f_2900_, 3, v___f_2890_);
lean_closure_set(v___f_2900_, 4, v_auxDeclToFullName_2898_);
lean_closure_set(v___f_2900_, 5, v_inst_2891_);
lean_closure_set(v___f_2900_, 6, v_inst_2886_);
lean_closure_set(v___f_2900_, 7, v_inst_2892_);
lean_closure_set(v___f_2900_, 8, v_inst_2893_);
lean_closure_set(v___f_2900_, 9, v_inst_2894_);
lean_closure_set(v___f_2900_, 10, v_inst_2895_);
v___x_2901_ = lean_apply_4(v_toBind_2896_, lean_box(0), lean_box(0), v_getCurrNamespace_2899_, v___f_2900_);
return v___x_2901_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__6(lean_object* v_inst_2902_, lean_object* v_n_2903_, lean_object* v_matchLocalDecl_x3f_2904_, lean_object* v___f_2905_, lean_object* v_inst_2906_, lean_object* v_inst_2907_, lean_object* v_inst_2908_, lean_object* v_inst_2909_, lean_object* v_inst_2910_, lean_object* v_toBind_2911_, lean_object* v_inst_2912_, lean_object* v_lctx_2913_){
_start:
{
lean_object* v___f_2914_; lean_object* v___x_2915_; 
lean_inc(v_toBind_2911_);
v___f_2914_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___redArg___lam__5), 12, 11);
lean_closure_set(v___f_2914_, 0, v_inst_2902_);
lean_closure_set(v___f_2914_, 1, v_n_2903_);
lean_closure_set(v___f_2914_, 2, v_lctx_2913_);
lean_closure_set(v___f_2914_, 3, v_matchLocalDecl_x3f_2904_);
lean_closure_set(v___f_2914_, 4, v___f_2905_);
lean_closure_set(v___f_2914_, 5, v_inst_2906_);
lean_closure_set(v___f_2914_, 6, v_inst_2907_);
lean_closure_set(v___f_2914_, 7, v_inst_2908_);
lean_closure_set(v___f_2914_, 8, v_inst_2909_);
lean_closure_set(v___f_2914_, 9, v_inst_2910_);
lean_closure_set(v___f_2914_, 10, v_toBind_2911_);
v___x_2915_ = lean_apply_4(v_toBind_2911_, lean_box(0), lean_box(0), v_inst_2912_, v___f_2914_);
return v___x_2915_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg(lean_object* v_inst_2918_, lean_object* v_inst_2919_, lean_object* v_inst_2920_, lean_object* v_inst_2921_, lean_object* v_inst_2922_, lean_object* v_inst_2923_, lean_object* v_inst_2924_, lean_object* v_n_2925_){
_start:
{
lean_object* v_toBind_2926_; lean_object* v___f_2927_; lean_object* v_matchLocalDecl_x3f_2928_; lean_object* v___f_2929_; lean_object* v___x_2930_; 
v_toBind_2926_ = lean_ctor_get(v_inst_2918_, 1);
lean_inc_n(v_toBind_2926_, 2);
v___f_2927_ = ((lean_object*)(l_Lean_resolveLocalName___redArg___closed__0));
v_matchLocalDecl_x3f_2928_ = ((lean_object*)(l_Lean_resolveLocalName___redArg___closed__1));
lean_inc(v_inst_2924_);
v___f_2929_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___redArg___lam__6), 12, 11);
lean_closure_set(v___f_2929_, 0, v_inst_2919_);
lean_closure_set(v___f_2929_, 1, v_n_2925_);
lean_closure_set(v___f_2929_, 2, v_matchLocalDecl_x3f_2928_);
lean_closure_set(v___f_2929_, 3, v___f_2927_);
lean_closure_set(v___f_2929_, 4, v_inst_2918_);
lean_closure_set(v___f_2929_, 5, v_inst_2920_);
lean_closure_set(v___f_2929_, 6, v_inst_2921_);
lean_closure_set(v___f_2929_, 7, v_inst_2922_);
lean_closure_set(v___f_2929_, 8, v_inst_2923_);
lean_closure_set(v___f_2929_, 9, v_toBind_2926_);
lean_closure_set(v___f_2929_, 10, v_inst_2924_);
v___x_2930_ = lean_apply_4(v_toBind_2926_, lean_box(0), lean_box(0), v_inst_2924_, v___f_2929_);
return v___x_2930_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName(lean_object* v_m_2931_, lean_object* v_inst_2932_, lean_object* v_inst_2933_, lean_object* v_inst_2934_, lean_object* v_inst_2935_, lean_object* v_inst_2936_, lean_object* v_inst_2937_, lean_object* v_inst_2938_, lean_object* v_n_2939_){
_start:
{
lean_object* v___x_2940_; 
v___x_2940_ = l_Lean_resolveLocalName___redArg(v_inst_2932_, v_inst_2933_, v_inst_2934_, v_inst_2935_, v_inst_2936_, v_inst_2937_, v_inst_2938_, v_n_2939_);
return v___x_2940_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__0(lean_object* v_toPure_2941_, uint8_t v_____do__lift_2942_){
_start:
{
lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; 
v___x_2943_ = lean_box(v_____do__lift_2942_);
v___x_2944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2944_, 0, v___x_2943_);
v___x_2945_ = lean_apply_2(v_toPure_2941_, lean_box(0), v___x_2944_);
return v___x_2945_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__0___boxed(lean_object* v_toPure_2946_, lean_object* v_____do__lift_2947_){
_start:
{
uint8_t v_____do__lift_1160__boxed_2948_; lean_object* v_res_2949_; 
v_____do__lift_1160__boxed_2948_ = lean_unbox(v_____do__lift_2947_);
v_res_2949_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__0(v_toPure_2946_, v_____do__lift_1160__boxed_2948_);
return v_res_2949_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__1(lean_object* v_toPure_2950_, lean_object* v___y_2951_, lean_object* v_____do__lift_2952_){
_start:
{
if (lean_obj_tag(v_____do__lift_2952_) == 0)
{
lean_object* v___x_2953_; lean_object* v___x_2954_; 
lean_dec(v___y_2951_);
v___x_2953_ = lean_box(0);
v___x_2954_ = lean_apply_2(v_toPure_2950_, lean_box(0), v___x_2953_);
return v___x_2954_;
}
else
{
lean_object* v___x_2956_; uint8_t v_isShared_2957_; uint8_t v_isSharedCheck_2962_; 
v_isSharedCheck_2962_ = !lean_is_exclusive(v_____do__lift_2952_);
if (v_isSharedCheck_2962_ == 0)
{
lean_object* v_unused_2963_; 
v_unused_2963_ = lean_ctor_get(v_____do__lift_2952_, 0);
lean_dec(v_unused_2963_);
v___x_2956_ = v_____do__lift_2952_;
v_isShared_2957_ = v_isSharedCheck_2962_;
goto v_resetjp_2955_;
}
else
{
lean_dec(v_____do__lift_2952_);
v___x_2956_ = lean_box(0);
v_isShared_2957_ = v_isSharedCheck_2962_;
goto v_resetjp_2955_;
}
v_resetjp_2955_:
{
lean_object* v___x_2959_; 
if (v_isShared_2957_ == 0)
{
lean_ctor_set(v___x_2956_, 0, v___y_2951_);
v___x_2959_ = v___x_2956_;
goto v_reusejp_2958_;
}
else
{
lean_object* v_reuseFailAlloc_2961_; 
v_reuseFailAlloc_2961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2961_, 0, v___y_2951_);
v___x_2959_ = v_reuseFailAlloc_2961_;
goto v_reusejp_2958_;
}
v_reusejp_2958_:
{
lean_object* v___x_2960_; 
v___x_2960_ = lean_apply_2(v_toPure_2950_, lean_box(0), v___x_2959_);
return v___x_2960_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2(lean_object* v_toPure_2966_, lean_object* v_toBind_2967_, lean_object* v___f_2968_, lean_object* v_____do__lift_2969_){
_start:
{
if (lean_obj_tag(v_____do__lift_2969_) == 0)
{
lean_object* v___x_2970_; lean_object* v___x_2971_; 
lean_dec(v___f_2968_);
lean_dec(v_toBind_2967_);
v___x_2970_ = lean_box(0);
v___x_2971_ = lean_apply_2(v_toPure_2966_, lean_box(0), v___x_2970_);
return v___x_2971_;
}
else
{
lean_object* v_val_2972_; uint8_t v___x_2973_; 
v_val_2972_ = lean_ctor_get(v_____do__lift_2969_, 0);
v___x_2973_ = lean_unbox(v_val_2972_);
if (v___x_2973_ == 0)
{
lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; 
v___x_2974_ = lean_box(0);
v___x_2975_ = lean_apply_2(v_toPure_2966_, lean_box(0), v___x_2974_);
v___x_2976_ = lean_apply_4(v_toBind_2967_, lean_box(0), lean_box(0), v___x_2975_, v___f_2968_);
return v___x_2976_;
}
else
{
lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; 
v___x_2977_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2___closed__0));
v___x_2978_ = lean_apply_2(v_toPure_2966_, lean_box(0), v___x_2977_);
v___x_2979_ = lean_apply_4(v_toBind_2967_, lean_box(0), lean_box(0), v___x_2978_, v___f_2968_);
return v___x_2979_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2___boxed(lean_object* v_toPure_2980_, lean_object* v_toBind_2981_, lean_object* v___f_2982_, lean_object* v_____do__lift_2983_){
_start:
{
lean_object* v_res_2984_; 
v_res_2984_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2(v_toPure_2980_, v_toBind_2981_, v___f_2982_, v_____do__lift_2983_);
lean_dec(v_____do__lift_2983_);
return v_res_2984_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__3(lean_object* v_toPure_2985_, lean_object* v_filter_2986_, lean_object* v___y_2987_, lean_object* v_toBind_2988_, lean_object* v___f_2989_, lean_object* v___f_2990_, lean_object* v_____do__lift_2991_){
_start:
{
if (lean_obj_tag(v_____do__lift_2991_) == 0)
{
lean_object* v___x_2992_; lean_object* v___x_2993_; 
lean_dec(v___f_2990_);
lean_dec(v___f_2989_);
lean_dec(v_toBind_2988_);
lean_dec(v___y_2987_);
lean_dec(v_filter_2986_);
v___x_2992_ = lean_box(0);
v___x_2993_ = lean_apply_2(v_toPure_2985_, lean_box(0), v___x_2992_);
return v___x_2993_;
}
else
{
lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; 
lean_dec(v_toPure_2985_);
v___x_2994_ = lean_apply_1(v_filter_2986_, v___y_2987_);
lean_inc(v_toBind_2988_);
v___x_2995_ = lean_apply_4(v_toBind_2988_, lean_box(0), lean_box(0), v___x_2994_, v___f_2989_);
v___x_2996_ = lean_apply_4(v_toBind_2988_, lean_box(0), lean_box(0), v___x_2995_, v___f_2990_);
return v___x_2996_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__3___boxed(lean_object* v_toPure_2997_, lean_object* v_filter_2998_, lean_object* v___y_2999_, lean_object* v_toBind_3000_, lean_object* v___f_3001_, lean_object* v___f_3002_, lean_object* v_____do__lift_3003_){
_start:
{
lean_object* v_res_3004_; 
v_res_3004_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__3(v_toPure_2997_, v_filter_2998_, v___y_2999_, v_toBind_3000_, v___f_3001_, v___f_3002_, v_____do__lift_3003_);
lean_dec(v_____do__lift_3003_);
return v_res_3004_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__4(lean_object* v_toPure_3005_, lean_object* v_n_u2080_3006_, lean_object* v_toBind_3007_, lean_object* v___f_3008_, lean_object* v_____do__lift_3009_){
_start:
{
if (lean_obj_tag(v_____do__lift_3009_) == 0)
{
lean_object* v___x_3013_; lean_object* v___x_3014_; 
lean_dec(v___f_3008_);
lean_dec(v_toBind_3007_);
v___x_3013_ = lean_box(0);
v___x_3014_ = lean_apply_2(v_toPure_3005_, lean_box(0), v___x_3013_);
return v___x_3014_;
}
else
{
lean_object* v_val_3015_; 
v_val_3015_ = lean_ctor_get(v_____do__lift_3009_, 0);
if (lean_obj_tag(v_val_3015_) == 1)
{
lean_object* v_tail_3016_; 
v_tail_3016_ = lean_ctor_get(v_val_3015_, 1);
if (lean_obj_tag(v_tail_3016_) == 0)
{
lean_object* v_head_3017_; lean_object* v_fst_3018_; uint8_t v___x_3019_; 
v_head_3017_ = lean_ctor_get(v_val_3015_, 0);
v_fst_3018_ = lean_ctor_get(v_head_3017_, 0);
v___x_3019_ = lean_name_eq(v_fst_3018_, v_n_u2080_3006_);
if (v___x_3019_ == 0)
{
lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; 
v___x_3020_ = lean_box(0);
v___x_3021_ = lean_apply_2(v_toPure_3005_, lean_box(0), v___x_3020_);
v___x_3022_ = lean_apply_4(v_toBind_3007_, lean_box(0), lean_box(0), v___x_3021_, v___f_3008_);
return v___x_3022_;
}
else
{
lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; 
v___x_3023_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2___closed__0));
v___x_3024_ = lean_apply_2(v_toPure_3005_, lean_box(0), v___x_3023_);
v___x_3025_ = lean_apply_4(v_toBind_3007_, lean_box(0), lean_box(0), v___x_3024_, v___f_3008_);
return v___x_3025_;
}
}
else
{
lean_dec(v___f_3008_);
lean_dec(v_toBind_3007_);
goto v___jp_3010_;
}
}
else
{
lean_dec(v___f_3008_);
lean_dec(v_toBind_3007_);
goto v___jp_3010_;
}
}
v___jp_3010_:
{
lean_object* v___x_3011_; lean_object* v___x_3012_; 
v___x_3011_ = lean_box(0);
v___x_3012_ = lean_apply_2(v_toPure_3005_, lean_box(0), v___x_3011_);
return v___x_3012_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__4___boxed(lean_object* v_toPure_3026_, lean_object* v_n_u2080_3027_, lean_object* v_toBind_3028_, lean_object* v___f_3029_, lean_object* v_____do__lift_3030_){
_start:
{
lean_object* v_res_3031_; 
v_res_3031_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__4(v_toPure_3026_, v_n_u2080_3027_, v_toBind_3028_, v___f_3029_, v_____do__lift_3030_);
lean_dec(v_____do__lift_3030_);
lean_dec(v_n_u2080_3027_);
return v_res_3031_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg(lean_object* v_inst_3032_, lean_object* v_inst_3033_, lean_object* v_inst_3034_, lean_object* v_inst_3035_, lean_object* v_inst_3036_, lean_object* v_inst_3037_, lean_object* v_n_u2080_3038_, lean_object* v_filter_3039_, lean_object* v_view_x3f_3040_, lean_object* v_n_3041_){
_start:
{
lean_object* v___f_3042_; lean_object* v___f_3043_; lean_object* v___f_3044_; lean_object* v___f_3045_; lean_object* v___f_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v_toApplicative_3054_; lean_object* v_getEnv_3055_; lean_object* v_modifyEnv_3056_; lean_object* v___x_3058_; uint8_t v_isShared_3059_; uint8_t v_isSharedCheck_3094_; 
lean_inc_ref_n(v_inst_3032_, 8);
v___f_3042_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_3042_, 0, v_inst_3032_);
v___f_3043_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__3), 5, 1);
lean_closure_set(v___f_3043_, 0, v_inst_3032_);
v___f_3044_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__6), 5, 1);
lean_closure_set(v___f_3044_, 0, v_inst_3032_);
v___f_3045_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_3045_, 0, v_inst_3032_);
v___f_3046_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__11), 5, 1);
lean_closure_set(v___f_3046_, 0, v_inst_3032_);
v___x_3047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3047_, 0, v___f_3042_);
lean_ctor_set(v___x_3047_, 1, v___f_3043_);
v___x_3048_ = lean_alloc_closure((void*)(l_OptionT_pure), 4, 2);
lean_closure_set(v___x_3048_, 0, lean_box(0));
lean_closure_set(v___x_3048_, 1, v_inst_3032_);
v___x_3049_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3049_, 0, v___x_3047_);
lean_ctor_set(v___x_3049_, 1, v___x_3048_);
lean_ctor_set(v___x_3049_, 2, v___f_3044_);
lean_ctor_set(v___x_3049_, 3, v___f_3045_);
lean_ctor_set(v___x_3049_, 4, v___f_3046_);
v___x_3050_ = lean_alloc_closure((void*)(l_OptionT_bind), 6, 2);
lean_closure_set(v___x_3050_, 0, lean_box(0));
lean_closure_set(v___x_3050_, 1, v_inst_3032_);
v___x_3051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3051_, 0, v___x_3049_);
lean_ctor_set(v___x_3051_, 1, v___x_3050_);
v___x_3052_ = lean_alloc_closure((void*)(l_OptionT_lift), 4, 2);
lean_closure_set(v___x_3052_, 0, lean_box(0));
lean_closure_set(v___x_3052_, 1, v_inst_3032_);
lean_inc_ref(v___x_3052_);
v___x_3053_ = l_Lean_instMonadResolveNameOfMonadLift___redArg(v___x_3052_, v_inst_3033_);
v_toApplicative_3054_ = lean_ctor_get(v_inst_3032_, 0);
lean_inc_ref(v_toApplicative_3054_);
v_getEnv_3055_ = lean_ctor_get(v_inst_3034_, 0);
v_modifyEnv_3056_ = lean_ctor_get(v_inst_3034_, 1);
v_isSharedCheck_3094_ = !lean_is_exclusive(v_inst_3034_);
if (v_isSharedCheck_3094_ == 0)
{
v___x_3058_ = v_inst_3034_;
v_isShared_3059_ = v_isSharedCheck_3094_;
goto v_resetjp_3057_;
}
else
{
lean_inc(v_modifyEnv_3056_);
lean_inc(v_getEnv_3055_);
lean_dec(v_inst_3034_);
v___x_3058_ = lean_box(0);
v_isShared_3059_ = v_isSharedCheck_3094_;
goto v_resetjp_3057_;
}
v_resetjp_3057_:
{
lean_object* v_toBind_3060_; lean_object* v_toPure_3061_; lean_object* v___f_3062_; lean_object* v___f_3063_; lean_object* v___f_3064_; lean_object* v___x_3065_; lean_object* v___x_3067_; 
v_toBind_3060_ = lean_ctor_get(v_inst_3032_, 1);
lean_inc_n(v_toBind_3060_, 2);
lean_dec_ref(v_inst_3032_);
v_toPure_3061_ = lean_ctor_get(v_toApplicative_3054_, 1);
lean_inc_n(v_toPure_3061_, 3);
lean_dec_ref(v_toApplicative_3054_);
lean_inc_ref(v___x_3052_);
v___f_3062_ = lean_alloc_closure((void*)(l_Lean_instMonadEnvOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3062_, 0, v_modifyEnv_3056_);
lean_closure_set(v___f_3062_, 1, v___x_3052_);
v___f_3063_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3063_, 0, v_toPure_3061_);
v___f_3064_ = lean_alloc_closure((void*)(l_OptionT_lift___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3064_, 0, v_toPure_3061_);
lean_inc_ref(v___f_3064_);
v___x_3065_ = lean_apply_4(v_toBind_3060_, lean_box(0), lean_box(0), v_getEnv_3055_, v___f_3064_);
if (v_isShared_3059_ == 0)
{
lean_ctor_set(v___x_3058_, 1, v___f_3062_);
lean_ctor_set(v___x_3058_, 0, v___x_3065_);
v___x_3067_ = v___x_3058_;
goto v_reusejp_3066_;
}
else
{
lean_object* v_reuseFailAlloc_3093_; 
v_reuseFailAlloc_3093_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3093_, 0, v___x_3065_);
lean_ctor_set(v_reuseFailAlloc_3093_, 1, v___f_3062_);
v___x_3067_ = v_reuseFailAlloc_3093_;
goto v_reusejp_3066_;
}
v_reusejp_3066_:
{
lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___f_3070_; lean_object* v___y_3072_; 
lean_inc(v_toBind_3060_);
v___x_3068_ = lean_apply_4(v_toBind_3060_, lean_box(0), lean_box(0), v_inst_3035_, v___f_3064_);
lean_inc_ref(v___x_3052_);
v___x_3069_ = l_Lean_instMonadLogOfMonadLift___redArg(v___x_3052_, v_inst_3036_);
v___f_3070_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3070_, 0, v_inst_3037_);
lean_closure_set(v___f_3070_, 1, v___x_3052_);
if (lean_obj_tag(v_view_x3f_3040_) == 1)
{
lean_object* v_val_3080_; lean_object* v_imported_3081_; lean_object* v_ctx_3082_; lean_object* v_scopes_3083_; lean_object* v___x_3085_; uint8_t v_isShared_3086_; uint8_t v_isSharedCheck_3091_; 
v_val_3080_ = lean_ctor_get(v_view_x3f_3040_, 0);
lean_inc(v_val_3080_);
lean_dec_ref_known(v_view_x3f_3040_, 1);
v_imported_3081_ = lean_ctor_get(v_val_3080_, 1);
v_ctx_3082_ = lean_ctor_get(v_val_3080_, 2);
v_scopes_3083_ = lean_ctor_get(v_val_3080_, 3);
v_isSharedCheck_3091_ = !lean_is_exclusive(v_val_3080_);
if (v_isSharedCheck_3091_ == 0)
{
lean_object* v_unused_3092_; 
v_unused_3092_ = lean_ctor_get(v_val_3080_, 0);
lean_dec(v_unused_3092_);
v___x_3085_ = v_val_3080_;
v_isShared_3086_ = v_isSharedCheck_3091_;
goto v_resetjp_3084_;
}
else
{
lean_inc(v_scopes_3083_);
lean_inc(v_ctx_3082_);
lean_inc(v_imported_3081_);
lean_dec(v_val_3080_);
v___x_3085_ = lean_box(0);
v_isShared_3086_ = v_isSharedCheck_3091_;
goto v_resetjp_3084_;
}
v_resetjp_3084_:
{
lean_object* v___x_3088_; 
if (v_isShared_3086_ == 0)
{
lean_ctor_set(v___x_3085_, 0, v_n_3041_);
v___x_3088_ = v___x_3085_;
goto v_reusejp_3087_;
}
else
{
lean_object* v_reuseFailAlloc_3090_; 
v_reuseFailAlloc_3090_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3090_, 0, v_n_3041_);
lean_ctor_set(v_reuseFailAlloc_3090_, 1, v_imported_3081_);
lean_ctor_set(v_reuseFailAlloc_3090_, 2, v_ctx_3082_);
lean_ctor_set(v_reuseFailAlloc_3090_, 3, v_scopes_3083_);
v___x_3088_ = v_reuseFailAlloc_3090_;
goto v_reusejp_3087_;
}
v_reusejp_3087_:
{
lean_object* v___x_3089_; 
v___x_3089_ = l_Lean_MacroScopesView_review(v___x_3088_);
v___y_3072_ = v___x_3089_;
goto v___jp_3071_;
}
}
}
else
{
lean_dec(v_view_x3f_3040_);
v___y_3072_ = v_n_3041_;
goto v___jp_3071_;
}
v___jp_3071_:
{
lean_object* v___f_3073_; lean_object* v___f_3074_; lean_object* v___f_3075_; lean_object* v___f_3076_; uint8_t v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; 
lean_inc_n(v___y_3072_, 2);
lean_inc_n(v_toPure_3061_, 3);
v___f_3073_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__1), 3, 2);
lean_closure_set(v___f_3073_, 0, v_toPure_3061_);
lean_closure_set(v___f_3073_, 1, v___y_3072_);
lean_inc_n(v_toBind_3060_, 3);
v___f_3074_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_3074_, 0, v_toPure_3061_);
lean_closure_set(v___f_3074_, 1, v_toBind_3060_);
lean_closure_set(v___f_3074_, 2, v___f_3073_);
v___f_3075_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__3___boxed), 7, 6);
lean_closure_set(v___f_3075_, 0, v_toPure_3061_);
lean_closure_set(v___f_3075_, 1, v_filter_3039_);
lean_closure_set(v___f_3075_, 2, v___y_3072_);
lean_closure_set(v___f_3075_, 3, v_toBind_3060_);
lean_closure_set(v___f_3075_, 4, v___f_3063_);
lean_closure_set(v___f_3075_, 5, v___f_3074_);
v___f_3076_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__4___boxed), 5, 4);
lean_closure_set(v___f_3076_, 0, v_toPure_3061_);
lean_closure_set(v___f_3076_, 1, v_n_u2080_3038_);
lean_closure_set(v___f_3076_, 2, v_toBind_3060_);
lean_closure_set(v___f_3076_, 3, v___f_3075_);
v___x_3077_ = 0;
v___x_3078_ = l_Lean_resolveGlobalName___redArg(v___x_3051_, v___x_3053_, v___x_3067_, v___x_3068_, v___x_3069_, v___f_3070_, v___y_3072_, v___x_3077_);
v___x_3079_ = lean_apply_4(v_toBind_3060_, lean_box(0), lean_box(0), v___x_3078_, v___f_3076_);
return v___x_3079_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve(lean_object* v_m_3095_, lean_object* v_inst_3096_, lean_object* v_inst_3097_, lean_object* v_inst_3098_, lean_object* v_inst_3099_, lean_object* v_inst_3100_, lean_object* v_inst_3101_, lean_object* v_n_u2080_3102_, lean_object* v_filter_3103_, lean_object* v_view_x3f_3104_, lean_object* v_n_3105_){
_start:
{
lean_object* v___x_3106_; 
v___x_3106_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg(v_inst_3096_, v_inst_3097_, v_inst_3098_, v_inst_3099_, v_inst_3100_, v_inst_3101_, v_n_u2080_3102_, v_filter_3103_, v_view_x3f_3104_, v_n_3105_);
return v___x_3106_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__0(lean_object* v_toPure_3111_, lean_object* v_____x_3112_){
_start:
{
if (lean_obj_tag(v_____x_3112_) == 0)
{
lean_object* v___x_3113_; lean_object* v___x_3114_; 
v___x_3113_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__0___closed__1));
v___x_3114_ = lean_apply_2(v_toPure_3111_, lean_box(0), v___x_3113_);
return v___x_3114_;
}
else
{
lean_object* v___x_3115_; 
v___x_3115_ = lean_apply_2(v_toPure_3111_, lean_box(0), v_____x_3112_);
return v___x_3115_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__1(lean_object* v_toPure_3116_, lean_object* v_____do__lift_3117_){
_start:
{
if (lean_obj_tag(v_____do__lift_3117_) == 0)
{
lean_object* v___x_3118_; lean_object* v___x_3119_; 
v___x_3118_ = lean_box(0);
v___x_3119_ = lean_apply_2(v_toPure_3116_, lean_box(0), v___x_3118_);
return v___x_3119_;
}
else
{
lean_object* v_val_3120_; lean_object* v___x_3122_; uint8_t v_isShared_3123_; uint8_t v_isSharedCheck_3129_; 
v_val_3120_ = lean_ctor_get(v_____do__lift_3117_, 0);
v_isSharedCheck_3129_ = !lean_is_exclusive(v_____do__lift_3117_);
if (v_isSharedCheck_3129_ == 0)
{
v___x_3122_ = v_____do__lift_3117_;
v_isShared_3123_ = v_isSharedCheck_3129_;
goto v_resetjp_3121_;
}
else
{
lean_inc(v_val_3120_);
lean_dec(v_____do__lift_3117_);
v___x_3122_ = lean_box(0);
v_isShared_3123_ = v_isSharedCheck_3129_;
goto v_resetjp_3121_;
}
v_resetjp_3121_:
{
lean_object* v___x_3124_; lean_object* v___x_3126_; 
v___x_3124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3124_, 0, v_val_3120_);
if (v_isShared_3123_ == 0)
{
lean_ctor_set(v___x_3122_, 0, v___x_3124_);
v___x_3126_ = v___x_3122_;
goto v_reusejp_3125_;
}
else
{
lean_object* v_reuseFailAlloc_3128_; 
v_reuseFailAlloc_3128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3128_, 0, v___x_3124_);
v___x_3126_ = v_reuseFailAlloc_3128_;
goto v_reusejp_3125_;
}
v_reusejp_3125_:
{
lean_object* v___x_3127_; 
v___x_3127_ = lean_apply_2(v_toPure_3116_, lean_box(0), v___x_3126_);
return v___x_3127_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__2(lean_object* v_toPure_3130_, lean_object* v___x_3131_, lean_object* v_____do__lift_3132_){
_start:
{
if (lean_obj_tag(v_____do__lift_3132_) == 0)
{
lean_object* v___x_3133_; 
v___x_3133_ = lean_apply_2(v_toPure_3130_, lean_box(0), v___x_3131_);
return v___x_3133_;
}
else
{
lean_object* v_val_3134_; lean_object* v_fst_3135_; lean_object* v___x_3136_; 
lean_dec(v___x_3131_);
v_val_3134_ = lean_ctor_get(v_____do__lift_3132_, 0);
lean_inc(v_val_3134_);
lean_dec_ref_known(v_____do__lift_3132_, 1);
v_fst_3135_ = lean_ctor_get(v_val_3134_, 0);
lean_inc(v_fst_3135_);
lean_dec(v_val_3134_);
v___x_3136_ = lean_apply_2(v_toPure_3130_, lean_box(0), v_fst_3135_);
return v___x_3136_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__3(lean_object* v_toPure_3137_, lean_object* v___x_3138_, lean_object* v___x_3139_, lean_object* v_____do__lift_3140_){
_start:
{
if (lean_obj_tag(v_____do__lift_3140_) == 0)
{
lean_object* v___x_3141_; lean_object* v___x_3142_; 
lean_dec(v___x_3139_);
lean_dec(v___x_3138_);
v___x_3141_ = lean_box(0);
v___x_3142_ = lean_apply_2(v_toPure_3137_, lean_box(0), v___x_3141_);
return v___x_3142_;
}
else
{
lean_object* v_val_3143_; lean_object* v___x_3145_; uint8_t v_isShared_3146_; uint8_t v_isSharedCheck_3174_; 
v_val_3143_ = lean_ctor_get(v_____do__lift_3140_, 0);
v_isSharedCheck_3174_ = !lean_is_exclusive(v_____do__lift_3140_);
if (v_isSharedCheck_3174_ == 0)
{
v___x_3145_ = v_____do__lift_3140_;
v_isShared_3146_ = v_isSharedCheck_3174_;
goto v_resetjp_3144_;
}
else
{
lean_inc(v_val_3143_);
lean_dec(v_____do__lift_3140_);
v___x_3145_ = lean_box(0);
v_isShared_3146_ = v_isSharedCheck_3174_;
goto v_resetjp_3144_;
}
v_resetjp_3144_:
{
if (lean_obj_tag(v_val_3143_) == 0)
{
lean_object* v_a_3147_; lean_object* v___x_3149_; uint8_t v_isShared_3150_; uint8_t v_isSharedCheck_3160_; 
lean_dec(v___x_3139_);
v_a_3147_ = lean_ctor_get(v_val_3143_, 0);
v_isSharedCheck_3160_ = !lean_is_exclusive(v_val_3143_);
if (v_isSharedCheck_3160_ == 0)
{
v___x_3149_ = v_val_3143_;
v_isShared_3150_ = v_isSharedCheck_3160_;
goto v_resetjp_3148_;
}
else
{
lean_inc(v_a_3147_);
lean_dec(v_val_3143_);
v___x_3149_ = lean_box(0);
v_isShared_3150_ = v_isSharedCheck_3160_;
goto v_resetjp_3148_;
}
v_resetjp_3148_:
{
lean_object* v___x_3152_; 
if (v_isShared_3146_ == 0)
{
lean_ctor_set(v___x_3145_, 0, v_a_3147_);
v___x_3152_ = v___x_3145_;
goto v_reusejp_3151_;
}
else
{
lean_object* v_reuseFailAlloc_3159_; 
v_reuseFailAlloc_3159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3159_, 0, v_a_3147_);
v___x_3152_ = v_reuseFailAlloc_3159_;
goto v_reusejp_3151_;
}
v_reusejp_3151_:
{
lean_object* v___x_3153_; lean_object* v___x_3155_; 
v___x_3153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3153_, 0, v___x_3152_);
lean_ctor_set(v___x_3153_, 1, v___x_3138_);
if (v_isShared_3150_ == 0)
{
lean_ctor_set(v___x_3149_, 0, v___x_3153_);
v___x_3155_ = v___x_3149_;
goto v_reusejp_3154_;
}
else
{
lean_object* v_reuseFailAlloc_3158_; 
v_reuseFailAlloc_3158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3158_, 0, v___x_3153_);
v___x_3155_ = v_reuseFailAlloc_3158_;
goto v_reusejp_3154_;
}
v_reusejp_3154_:
{
lean_object* v___x_3156_; lean_object* v___x_3157_; 
v___x_3156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3156_, 0, v___x_3155_);
v___x_3157_ = lean_apply_2(v_toPure_3137_, lean_box(0), v___x_3156_);
return v___x_3157_;
}
}
}
}
else
{
lean_object* v___x_3162_; uint8_t v_isShared_3163_; uint8_t v_isSharedCheck_3172_; 
v_isSharedCheck_3172_ = !lean_is_exclusive(v_val_3143_);
if (v_isSharedCheck_3172_ == 0)
{
lean_object* v_unused_3173_; 
v_unused_3173_ = lean_ctor_get(v_val_3143_, 0);
lean_dec(v_unused_3173_);
v___x_3162_ = v_val_3143_;
v_isShared_3163_ = v_isSharedCheck_3172_;
goto v_resetjp_3161_;
}
else
{
lean_dec(v_val_3143_);
v___x_3162_ = lean_box(0);
v_isShared_3163_ = v_isSharedCheck_3172_;
goto v_resetjp_3161_;
}
v_resetjp_3161_:
{
lean_object* v___x_3164_; lean_object* v___x_3166_; 
v___x_3164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3164_, 0, v___x_3139_);
lean_ctor_set(v___x_3164_, 1, v___x_3138_);
if (v_isShared_3163_ == 0)
{
lean_ctor_set(v___x_3162_, 0, v___x_3164_);
v___x_3166_ = v___x_3162_;
goto v_reusejp_3165_;
}
else
{
lean_object* v_reuseFailAlloc_3171_; 
v_reuseFailAlloc_3171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3171_, 0, v___x_3164_);
v___x_3166_ = v_reuseFailAlloc_3171_;
goto v_reusejp_3165_;
}
v_reusejp_3165_:
{
lean_object* v___x_3168_; 
if (v_isShared_3146_ == 0)
{
lean_ctor_set(v___x_3145_, 0, v___x_3166_);
v___x_3168_ = v___x_3145_;
goto v_reusejp_3167_;
}
else
{
lean_object* v_reuseFailAlloc_3170_; 
v_reuseFailAlloc_3170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3170_, 0, v___x_3166_);
v___x_3168_ = v_reuseFailAlloc_3170_;
goto v_reusejp_3167_;
}
v_reusejp_3167_:
{
lean_object* v___x_3169_; 
v___x_3169_ = lean_apply_2(v_toPure_3137_, lean_box(0), v___x_3168_);
return v___x_3169_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__4(lean_object* v_toPure_3175_, lean_object* v___x_3176_, lean_object* v_inst_3177_, lean_object* v_inst_3178_, lean_object* v_inst_3179_, lean_object* v_inst_3180_, lean_object* v_inst_3181_, lean_object* v_inst_3182_, lean_object* v_n_u2080_3183_, lean_object* v_filter_3184_, lean_object* v_view_x3f_3185_, lean_object* v_toBind_3186_, lean_object* v___f_3187_, lean_object* v___f_3188_, lean_object* v_a_3189_, lean_object* v_x_3190_, lean_object* v___y_3191_){
_start:
{
lean_object* v_snd_3192_; lean_object* v___x_3193_; lean_object* v___f_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; 
v_snd_3192_ = lean_ctor_get(v___y_3191_, 1);
lean_inc(v_snd_3192_);
lean_dec_ref(v___y_3191_);
v___x_3193_ = l_Lean_Name_appendCore(v_a_3189_, v_snd_3192_);
lean_inc(v___x_3193_);
v___f_3194_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__3), 4, 3);
lean_closure_set(v___f_3194_, 0, v_toPure_3175_);
lean_closure_set(v___f_3194_, 1, v___x_3193_);
lean_closure_set(v___f_3194_, 2, v___x_3176_);
v___x_3195_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg(v_inst_3177_, v_inst_3178_, v_inst_3179_, v_inst_3180_, v_inst_3181_, v_inst_3182_, v_n_u2080_3183_, v_filter_3184_, v_view_x3f_3185_, v___x_3193_);
lean_inc_n(v_toBind_3186_, 2);
v___x_3196_ = lean_apply_4(v_toBind_3186_, lean_box(0), lean_box(0), v___x_3195_, v___f_3187_);
v___x_3197_ = lean_apply_4(v_toBind_3186_, lean_box(0), lean_box(0), v___x_3196_, v___f_3188_);
v___x_3198_ = lean_apply_4(v_toBind_3186_, lean_box(0), lean_box(0), v___x_3197_, v___f_3194_);
return v___x_3198_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__4___boxed(lean_object** _args){
lean_object* v_toPure_3199_ = _args[0];
lean_object* v___x_3200_ = _args[1];
lean_object* v_inst_3201_ = _args[2];
lean_object* v_inst_3202_ = _args[3];
lean_object* v_inst_3203_ = _args[4];
lean_object* v_inst_3204_ = _args[5];
lean_object* v_inst_3205_ = _args[6];
lean_object* v_inst_3206_ = _args[7];
lean_object* v_n_u2080_3207_ = _args[8];
lean_object* v_filter_3208_ = _args[9];
lean_object* v_view_x3f_3209_ = _args[10];
lean_object* v_toBind_3210_ = _args[11];
lean_object* v___f_3211_ = _args[12];
lean_object* v___f_3212_ = _args[13];
lean_object* v_a_3213_ = _args[14];
lean_object* v_x_3214_ = _args[15];
lean_object* v___y_3215_ = _args[16];
_start:
{
lean_object* v_res_3216_; 
v_res_3216_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__4(v_toPure_3199_, v___x_3200_, v_inst_3201_, v_inst_3202_, v_inst_3203_, v_inst_3204_, v_inst_3205_, v_inst_3206_, v_n_u2080_3207_, v_filter_3208_, v_view_x3f_3209_, v_toBind_3210_, v___f_3211_, v___f_3212_, v_a_3213_, v_x_3214_, v___y_3215_);
lean_dec(v_a_3213_);
return v_res_3216_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__5(lean_object* v_toPure_3220_, lean_object* v_n_3221_, lean_object* v_inst_3222_, lean_object* v_inst_3223_, lean_object* v_inst_3224_, lean_object* v_inst_3225_, lean_object* v_inst_3226_, lean_object* v_inst_3227_, lean_object* v_n_u2080_3228_, lean_object* v_filter_3229_, lean_object* v_view_x3f_3230_, lean_object* v_toBind_3231_, lean_object* v___f_3232_, lean_object* v___f_3233_, lean_object* v___x_3234_, lean_object* v_____do__lift_3235_){
_start:
{
if (lean_obj_tag(v_____do__lift_3235_) == 0)
{
lean_object* v___x_3236_; lean_object* v___x_3237_; 
lean_dec_ref(v___x_3234_);
lean_dec(v___f_3233_);
lean_dec(v___f_3232_);
lean_dec(v_toBind_3231_);
lean_dec(v_view_x3f_3230_);
lean_dec(v_filter_3229_);
lean_dec(v_n_u2080_3228_);
lean_dec(v_inst_3227_);
lean_dec_ref(v_inst_3226_);
lean_dec(v_inst_3225_);
lean_dec_ref(v_inst_3224_);
lean_dec_ref(v_inst_3223_);
lean_dec_ref(v_inst_3222_);
lean_dec(v_n_3221_);
v___x_3236_ = lean_box(0);
v___x_3237_ = lean_apply_2(v_toPure_3220_, lean_box(0), v___x_3236_);
return v___x_3237_;
}
else
{
lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___f_3241_; lean_object* v___f_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; 
v___x_3238_ = l_Lean_privateToUserName(v_n_3221_);
v___x_3239_ = l_Lean_Name_componentsRev(v___x_3238_);
v___x_3240_ = lean_box(0);
lean_inc(v_toPure_3220_);
v___f_3241_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__2), 3, 2);
lean_closure_set(v___f_3241_, 0, v_toPure_3220_);
lean_closure_set(v___f_3241_, 1, v___x_3240_);
lean_inc(v_toBind_3231_);
v___f_3242_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__4___boxed), 17, 14);
lean_closure_set(v___f_3242_, 0, v_toPure_3220_);
lean_closure_set(v___f_3242_, 1, v___x_3240_);
lean_closure_set(v___f_3242_, 2, v_inst_3222_);
lean_closure_set(v___f_3242_, 3, v_inst_3223_);
lean_closure_set(v___f_3242_, 4, v_inst_3224_);
lean_closure_set(v___f_3242_, 5, v_inst_3225_);
lean_closure_set(v___f_3242_, 6, v_inst_3226_);
lean_closure_set(v___f_3242_, 7, v_inst_3227_);
lean_closure_set(v___f_3242_, 8, v_n_u2080_3228_);
lean_closure_set(v___f_3242_, 9, v_filter_3229_);
lean_closure_set(v___f_3242_, 10, v_view_x3f_3230_);
lean_closure_set(v___f_3242_, 11, v_toBind_3231_);
lean_closure_set(v___f_3242_, 12, v___f_3232_);
lean_closure_set(v___f_3242_, 13, v___f_3233_);
v___x_3243_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__5___closed__0));
v___x_3244_ = l_List_forIn_x27_loop___redArg(v___x_3234_, v___f_3242_, v___x_3239_, v___x_3243_);
lean_dec(v___x_3239_);
v___x_3245_ = lean_apply_4(v_toBind_3231_, lean_box(0), lean_box(0), v___x_3244_, v___f_3241_);
return v___x_3245_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__5___boxed(lean_object* v_toPure_3246_, lean_object* v_n_3247_, lean_object* v_inst_3248_, lean_object* v_inst_3249_, lean_object* v_inst_3250_, lean_object* v_inst_3251_, lean_object* v_inst_3252_, lean_object* v_inst_3253_, lean_object* v_n_u2080_3254_, lean_object* v_filter_3255_, lean_object* v_view_x3f_3256_, lean_object* v_toBind_3257_, lean_object* v___f_3258_, lean_object* v___f_3259_, lean_object* v___x_3260_, lean_object* v_____do__lift_3261_){
_start:
{
lean_object* v_res_3262_; 
v_res_3262_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__5(v_toPure_3246_, v_n_3247_, v_inst_3248_, v_inst_3249_, v_inst_3250_, v_inst_3251_, v_inst_3252_, v_inst_3253_, v_n_u2080_3254_, v_filter_3255_, v_view_x3f_3256_, v_toBind_3257_, v___f_3258_, v___f_3259_, v___x_3260_, v_____do__lift_3261_);
lean_dec(v_____do__lift_3261_);
return v_res_3262_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg(lean_object* v_inst_3263_, lean_object* v_inst_3264_, lean_object* v_inst_3265_, lean_object* v_inst_3266_, lean_object* v_inst_3267_, lean_object* v_inst_3268_, lean_object* v_n_u2080_3269_, lean_object* v_filter_3270_, lean_object* v_view_x3f_3271_, lean_object* v_n_3272_){
_start:
{
lean_object* v___f_3273_; lean_object* v___f_3274_; lean_object* v___f_3275_; lean_object* v___f_3276_; lean_object* v___f_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___y_3284_; uint8_t v___x_3292_; 
lean_inc_ref_n(v_inst_3263_, 7);
v___f_3273_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_3273_, 0, v_inst_3263_);
v___f_3274_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__3), 5, 1);
lean_closure_set(v___f_3274_, 0, v_inst_3263_);
v___f_3275_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__6), 5, 1);
lean_closure_set(v___f_3275_, 0, v_inst_3263_);
v___f_3276_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_3276_, 0, v_inst_3263_);
v___f_3277_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__11), 5, 1);
lean_closure_set(v___f_3277_, 0, v_inst_3263_);
v___x_3278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3278_, 0, v___f_3273_);
lean_ctor_set(v___x_3278_, 1, v___f_3274_);
v___x_3279_ = lean_alloc_closure((void*)(l_OptionT_pure), 4, 2);
lean_closure_set(v___x_3279_, 0, lean_box(0));
lean_closure_set(v___x_3279_, 1, v_inst_3263_);
v___x_3280_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3280_, 0, v___x_3278_);
lean_ctor_set(v___x_3280_, 1, v___x_3279_);
lean_ctor_set(v___x_3280_, 2, v___f_3275_);
lean_ctor_set(v___x_3280_, 3, v___f_3276_);
lean_ctor_set(v___x_3280_, 4, v___f_3277_);
v___x_3281_ = lean_alloc_closure((void*)(l_OptionT_bind), 6, 2);
lean_closure_set(v___x_3281_, 0, lean_box(0));
lean_closure_set(v___x_3281_, 1, v_inst_3263_);
v___x_3282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3282_, 0, v___x_3280_);
lean_ctor_set(v___x_3282_, 1, v___x_3281_);
v___x_3292_ = l_Lean_Name_hasMacroScopes(v_n_3272_);
if (v___x_3292_ == 0)
{
lean_object* v_toApplicative_3293_; lean_object* v_toPure_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; 
v_toApplicative_3293_ = lean_ctor_get(v_inst_3263_, 0);
v_toPure_3294_ = lean_ctor_get(v_toApplicative_3293_, 1);
v___x_3295_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2___closed__0));
lean_inc(v_toPure_3294_);
v___x_3296_ = lean_apply_2(v_toPure_3294_, lean_box(0), v___x_3295_);
v___y_3284_ = v___x_3296_;
goto v___jp_3283_;
}
else
{
lean_object* v_toApplicative_3297_; lean_object* v_toPure_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; 
v_toApplicative_3297_ = lean_ctor_get(v_inst_3263_, 0);
v_toPure_3298_ = lean_ctor_get(v_toApplicative_3297_, 1);
v___x_3299_ = lean_box(0);
lean_inc(v_toPure_3298_);
v___x_3300_ = lean_apply_2(v_toPure_3298_, lean_box(0), v___x_3299_);
v___y_3284_ = v___x_3300_;
goto v___jp_3283_;
}
v___jp_3283_:
{
lean_object* v_toApplicative_3285_; lean_object* v_toBind_3286_; lean_object* v_toPure_3287_; lean_object* v___f_3288_; lean_object* v___f_3289_; lean_object* v___f_3290_; lean_object* v___x_3291_; 
v_toApplicative_3285_ = lean_ctor_get(v_inst_3263_, 0);
v_toBind_3286_ = lean_ctor_get(v_inst_3263_, 1);
lean_inc_n(v_toBind_3286_, 2);
v_toPure_3287_ = lean_ctor_get(v_toApplicative_3285_, 1);
lean_inc_n(v_toPure_3287_, 3);
v___f_3288_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3288_, 0, v_toPure_3287_);
v___f_3289_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__1), 2, 1);
lean_closure_set(v___f_3289_, 0, v_toPure_3287_);
v___f_3290_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__5___boxed), 16, 15);
lean_closure_set(v___f_3290_, 0, v_toPure_3287_);
lean_closure_set(v___f_3290_, 1, v_n_3272_);
lean_closure_set(v___f_3290_, 2, v_inst_3263_);
lean_closure_set(v___f_3290_, 3, v_inst_3264_);
lean_closure_set(v___f_3290_, 4, v_inst_3265_);
lean_closure_set(v___f_3290_, 5, v_inst_3266_);
lean_closure_set(v___f_3290_, 6, v_inst_3267_);
lean_closure_set(v___f_3290_, 7, v_inst_3268_);
lean_closure_set(v___f_3290_, 8, v_n_u2080_3269_);
lean_closure_set(v___f_3290_, 9, v_filter_3270_);
lean_closure_set(v___f_3290_, 10, v_view_x3f_3271_);
lean_closure_set(v___f_3290_, 11, v_toBind_3286_);
lean_closure_set(v___f_3290_, 12, v___f_3289_);
lean_closure_set(v___f_3290_, 13, v___f_3288_);
lean_closure_set(v___f_3290_, 14, v___x_3282_);
v___x_3291_ = lean_apply_4(v_toBind_3286_, lean_box(0), lean_box(0), v___y_3284_, v___f_3290_);
return v___x_3291_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore(lean_object* v_m_3301_, lean_object* v_inst_3302_, lean_object* v_inst_3303_, lean_object* v_inst_3304_, lean_object* v_inst_3305_, lean_object* v_inst_3306_, lean_object* v_inst_3307_, lean_object* v_n_u2080_3308_, lean_object* v_filter_3309_, lean_object* v_view_x3f_3310_, lean_object* v_n_3311_){
_start:
{
lean_object* v___x_3312_; 
v___x_3312_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg(v_inst_3302_, v_inst_3303_, v_inst_3304_, v_inst_3305_, v_inst_3306_, v_inst_3307_, v_n_u2080_3308_, v_filter_3309_, v_view_x3f_3310_, v_n_3311_);
return v___x_3312_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___lam__0(lean_object* v_n_u2081_3313_, lean_object* v_x1_3314_, lean_object* v_x2_3315_){
_start:
{
lean_object* v___x_3316_; lean_object* v___x_3317_; uint8_t v___x_3318_; 
v___x_3316_ = l_Lean_Name_getPrefix(v_x2_3315_);
v___x_3317_ = l_Lean_Name_getPrefix(v_n_u2081_3313_);
v___x_3318_ = l_Lean_Name_isPrefixOf(v___x_3316_, v___x_3317_);
lean_dec(v___x_3317_);
lean_dec(v___x_3316_);
if (v___x_3318_ == 0)
{
lean_dec(v_x2_3315_);
return v_x1_3314_;
}
else
{
lean_object* v___x_3319_; 
v___x_3319_ = lean_array_push(v_x1_3314_, v_x2_3315_);
return v___x_3319_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___lam__0___boxed(lean_object* v_n_u2081_3320_, lean_object* v_x1_3321_, lean_object* v_x2_3322_){
_start:
{
lean_object* v_res_3323_; 
v_res_3323_ = l_Lean_unresolveNameGlobal_x3f___redArg___lam__0(v_n_u2081_3320_, v_x1_3321_, v_x2_3322_);
lean_dec(v_n_u2081_3320_);
return v_res_3323_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___lam__1(lean_object* v_view_3324_, lean_object* v_n_u2081_3325_, lean_object* v_inst_3326_, lean_object* v_inst_3327_, lean_object* v_inst_3328_, lean_object* v_inst_3329_, lean_object* v_inst_3330_, lean_object* v_inst_3331_, lean_object* v_n_u2080_3332_, lean_object* v_filter_3333_, lean_object* v_toPure_3334_, lean_object* v_____do__lift_3335_){
_start:
{
if (lean_obj_tag(v_____do__lift_3335_) == 0)
{
lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; 
lean_dec(v_toPure_3334_);
v___x_3336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3336_, 0, v_view_3324_);
v___x_3337_ = l_Lean_rootNamespace;
v___x_3338_ = l_Lean_Name_append(v___x_3337_, v_n_u2081_3325_);
v___x_3339_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg(v_inst_3326_, v_inst_3327_, v_inst_3328_, v_inst_3329_, v_inst_3330_, v_inst_3331_, v_n_u2080_3332_, v_filter_3333_, v___x_3336_, v___x_3338_);
return v___x_3339_;
}
else
{
lean_object* v___x_3340_; 
lean_dec(v_filter_3333_);
lean_dec(v_n_u2080_3332_);
lean_dec(v_inst_3331_);
lean_dec_ref(v_inst_3330_);
lean_dec(v_inst_3329_);
lean_dec_ref(v_inst_3328_);
lean_dec_ref(v_inst_3327_);
lean_dec_ref(v_inst_3326_);
lean_dec(v_n_u2081_3325_);
lean_dec_ref(v_view_3324_);
v___x_3340_ = lean_apply_2(v_toPure_3334_, lean_box(0), v_____do__lift_3335_);
return v___x_3340_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___lam__2(lean_object* v_toPure_3341_, lean_object* v_inst_3342_, lean_object* v_inst_3343_, lean_object* v_inst_3344_, lean_object* v_inst_3345_, lean_object* v_inst_3346_, lean_object* v_inst_3347_, lean_object* v_n_u2080_3348_, lean_object* v_filter_3349_, lean_object* v_toBind_3350_, lean_object* v___f_3351_, uint8_t v_allowHorizAliases_3352_, lean_object* v___f_3353_, lean_object* v_____do__lift_3354_){
_start:
{
lean_object* v_aliases_3356_; 
if (lean_obj_tag(v_____do__lift_3354_) == 0)
{
lean_object* v___x_3363_; lean_object* v___x_3364_; 
lean_dec_ref(v___f_3353_);
lean_dec(v___f_3351_);
lean_dec(v_toBind_3350_);
lean_dec(v_filter_3349_);
lean_dec(v_n_u2080_3348_);
lean_dec(v_inst_3347_);
lean_dec_ref(v_inst_3346_);
lean_dec(v_inst_3345_);
lean_dec_ref(v_inst_3344_);
lean_dec_ref(v_inst_3343_);
lean_dec_ref(v_inst_3342_);
v___x_3363_ = lean_box(0);
v___x_3364_ = lean_apply_2(v_toPure_3341_, lean_box(0), v___x_3363_);
return v___x_3364_;
}
else
{
lean_object* v_val_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; 
lean_dec(v_toPure_3341_);
v_val_3365_ = lean_ctor_get(v_____do__lift_3354_, 0);
lean_inc(v_val_3365_);
lean_dec_ref_known(v_____do__lift_3354_, 1);
lean_inc(v_n_u2080_3348_);
v___x_3366_ = l_Lean_getRevAliases(v_val_3365_, v_n_u2080_3348_);
v___x_3367_ = lean_array_mk(v___x_3366_);
if (v_allowHorizAliases_3352_ == 0)
{
lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; uint8_t v___x_3372_; 
v___x_3368_ = lean_unsigned_to_nat(0u);
v___x_3369_ = lean_array_get_size(v___x_3367_);
v___x_3370_ = ((lean_object*)(l_Lean_resolveNamespace___redArg___closed__1));
v___x_3371_ = ((lean_object*)(l_Lean_resolveLocalName___redArg___lam__3___closed__9));
v___x_3372_ = lean_nat_dec_lt(v___x_3368_, v___x_3369_);
if (v___x_3372_ == 0)
{
lean_dec_ref(v___x_3367_);
lean_dec_ref(v___f_3353_);
v_aliases_3356_ = v___x_3370_;
goto v___jp_3355_;
}
else
{
uint8_t v___x_3373_; 
v___x_3373_ = lean_nat_dec_le(v___x_3369_, v___x_3369_);
if (v___x_3373_ == 0)
{
if (v___x_3372_ == 0)
{
lean_dec_ref(v___x_3367_);
lean_dec_ref(v___f_3353_);
v_aliases_3356_ = v___x_3370_;
goto v___jp_3355_;
}
else
{
size_t v___x_3374_; size_t v___x_3375_; lean_object* v___x_3376_; 
v___x_3374_ = ((size_t)0ULL);
v___x_3375_ = lean_usize_of_nat(v___x_3369_);
v___x_3376_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3371_, v___f_3353_, v___x_3367_, v___x_3374_, v___x_3375_, v___x_3370_);
v_aliases_3356_ = v___x_3376_;
goto v___jp_3355_;
}
}
else
{
size_t v___x_3377_; size_t v___x_3378_; lean_object* v___x_3379_; 
v___x_3377_ = ((size_t)0ULL);
v___x_3378_ = lean_usize_of_nat(v___x_3369_);
v___x_3379_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3371_, v___f_3353_, v___x_3367_, v___x_3377_, v___x_3378_, v___x_3370_);
v_aliases_3356_ = v___x_3379_;
goto v___jp_3355_;
}
}
}
else
{
lean_dec_ref(v___f_3353_);
v_aliases_3356_ = v___x_3367_;
goto v___jp_3355_;
}
}
v___jp_3355_:
{
lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; 
lean_inc_ref(v_inst_3342_);
v___x_3357_ = l_OptionT_instAlternative___redArg(v_inst_3342_);
v___x_3358_ = lean_box(0);
v___x_3359_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore), 11, 10);
lean_closure_set(v___x_3359_, 0, lean_box(0));
lean_closure_set(v___x_3359_, 1, v_inst_3342_);
lean_closure_set(v___x_3359_, 2, v_inst_3343_);
lean_closure_set(v___x_3359_, 3, v_inst_3344_);
lean_closure_set(v___x_3359_, 4, v_inst_3345_);
lean_closure_set(v___x_3359_, 5, v_inst_3346_);
lean_closure_set(v___x_3359_, 6, v_inst_3347_);
lean_closure_set(v___x_3359_, 7, v_n_u2080_3348_);
lean_closure_set(v___x_3359_, 8, v_filter_3349_);
lean_closure_set(v___x_3359_, 9, v___x_3358_);
v___x_3360_ = lean_unsigned_to_nat(0u);
v___x_3361_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go(lean_box(0), lean_box(0), lean_box(0), v___x_3357_, v___x_3359_, v_aliases_3356_, v___x_3360_);
v___x_3362_ = lean_apply_4(v_toBind_3350_, lean_box(0), lean_box(0), v___x_3361_, v___f_3351_);
return v___x_3362_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___lam__2___boxed(lean_object* v_toPure_3380_, lean_object* v_inst_3381_, lean_object* v_inst_3382_, lean_object* v_inst_3383_, lean_object* v_inst_3384_, lean_object* v_inst_3385_, lean_object* v_inst_3386_, lean_object* v_n_u2080_3387_, lean_object* v_filter_3388_, lean_object* v_toBind_3389_, lean_object* v___f_3390_, lean_object* v_allowHorizAliases_3391_, lean_object* v___f_3392_, lean_object* v_____do__lift_3393_){
_start:
{
uint8_t v_allowHorizAliases_boxed_3394_; lean_object* v_res_3395_; 
v_allowHorizAliases_boxed_3394_ = lean_unbox(v_allowHorizAliases_3391_);
v_res_3395_ = l_Lean_unresolveNameGlobal_x3f___redArg___lam__2(v_toPure_3380_, v_inst_3381_, v_inst_3382_, v_inst_3383_, v_inst_3384_, v_inst_3385_, v_inst_3386_, v_n_u2080_3387_, v_filter_3388_, v_toBind_3389_, v___f_3390_, v_allowHorizAliases_boxed_3394_, v___f_3392_, v_____do__lift_3393_);
return v_res_3395_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___lam__3(lean_object* v_toPure_3396_, lean_object* v_____do__lift_3397_){
_start:
{
lean_object* v___x_3398_; lean_object* v___x_3399_; 
v___x_3398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3398_, 0, v_____do__lift_3397_);
v___x_3399_ = lean_apply_2(v_toPure_3396_, lean_box(0), v___x_3398_);
return v___x_3399_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___lam__4(lean_object* v_n_u2081_3400_, lean_object* v_inst_3401_, lean_object* v_inst_3402_, lean_object* v_inst_3403_, lean_object* v_inst_3404_, lean_object* v_inst_3405_, lean_object* v_inst_3406_, lean_object* v_n_u2080_3407_, lean_object* v_filter_3408_, lean_object* v___x_3409_, lean_object* v_toPure_3410_, lean_object* v_____do__lift_3411_){
_start:
{
if (lean_obj_tag(v_____do__lift_3411_) == 0)
{
lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; 
lean_dec(v_toPure_3410_);
v___x_3412_ = l_Lean_rootNamespace;
v___x_3413_ = l_Lean_Name_append(v___x_3412_, v_n_u2081_3400_);
v___x_3414_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg(v_inst_3401_, v_inst_3402_, v_inst_3403_, v_inst_3404_, v_inst_3405_, v_inst_3406_, v_n_u2080_3407_, v_filter_3408_, v___x_3409_, v___x_3413_);
return v___x_3414_;
}
else
{
lean_object* v___x_3415_; 
lean_dec(v___x_3409_);
lean_dec(v_filter_3408_);
lean_dec(v_n_u2080_3407_);
lean_dec(v_inst_3406_);
lean_dec_ref(v_inst_3405_);
lean_dec(v_inst_3404_);
lean_dec_ref(v_inst_3403_);
lean_dec_ref(v_inst_3402_);
lean_dec_ref(v_inst_3401_);
lean_dec(v_n_u2081_3400_);
v___x_3415_ = lean_apply_2(v_toPure_3410_, lean_box(0), v_____do__lift_3411_);
return v___x_3415_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg(lean_object* v_inst_3416_, lean_object* v_inst_3417_, lean_object* v_inst_3418_, lean_object* v_inst_3419_, lean_object* v_inst_3420_, lean_object* v_inst_3421_, lean_object* v_n_u2080_3422_, uint8_t v_fullNames_3423_, uint8_t v_allowHorizAliases_3424_, lean_object* v_filter_3425_){
_start:
{
lean_object* v_view_3426_; lean_object* v_name_3427_; lean_object* v_n_u2081_3428_; 
lean_inc(v_n_u2080_3422_);
v_view_3426_ = l_Lean_extractMacroScopes(v_n_u2080_3422_);
v_name_3427_ = lean_ctor_get(v_view_3426_, 0);
lean_inc(v_name_3427_);
v_n_u2081_3428_ = l_Lean_privateToUserName(v_name_3427_);
if (v_fullNames_3423_ == 0)
{
lean_object* v_toApplicative_3429_; lean_object* v_getEnv_3430_; lean_object* v_toBind_3431_; lean_object* v_toPure_3432_; lean_object* v___f_3433_; lean_object* v___f_3434_; lean_object* v___x_3435_; lean_object* v___f_3436_; lean_object* v___f_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; 
v_toApplicative_3429_ = lean_ctor_get(v_inst_3416_, 0);
v_getEnv_3430_ = lean_ctor_get(v_inst_3418_, 0);
lean_inc(v_getEnv_3430_);
v_toBind_3431_ = lean_ctor_get(v_inst_3416_, 1);
lean_inc_n(v_toBind_3431_, 3);
v_toPure_3432_ = lean_ctor_get(v_toApplicative_3429_, 1);
lean_inc_n(v_toPure_3432_, 3);
lean_inc(v_n_u2081_3428_);
v___f_3433_ = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal_x3f___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3433_, 0, v_n_u2081_3428_);
lean_inc(v_filter_3425_);
lean_inc(v_n_u2080_3422_);
lean_inc(v_inst_3421_);
lean_inc_ref(v_inst_3420_);
lean_inc(v_inst_3419_);
lean_inc_ref(v_inst_3418_);
lean_inc_ref(v_inst_3417_);
lean_inc_ref(v_inst_3416_);
v___f_3434_ = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal_x3f___redArg___lam__1), 12, 11);
lean_closure_set(v___f_3434_, 0, v_view_3426_);
lean_closure_set(v___f_3434_, 1, v_n_u2081_3428_);
lean_closure_set(v___f_3434_, 2, v_inst_3416_);
lean_closure_set(v___f_3434_, 3, v_inst_3417_);
lean_closure_set(v___f_3434_, 4, v_inst_3418_);
lean_closure_set(v___f_3434_, 5, v_inst_3419_);
lean_closure_set(v___f_3434_, 6, v_inst_3420_);
lean_closure_set(v___f_3434_, 7, v_inst_3421_);
lean_closure_set(v___f_3434_, 8, v_n_u2080_3422_);
lean_closure_set(v___f_3434_, 9, v_filter_3425_);
lean_closure_set(v___f_3434_, 10, v_toPure_3432_);
v___x_3435_ = lean_box(v_allowHorizAliases_3424_);
v___f_3436_ = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal_x3f___redArg___lam__2___boxed), 14, 13);
lean_closure_set(v___f_3436_, 0, v_toPure_3432_);
lean_closure_set(v___f_3436_, 1, v_inst_3416_);
lean_closure_set(v___f_3436_, 2, v_inst_3417_);
lean_closure_set(v___f_3436_, 3, v_inst_3418_);
lean_closure_set(v___f_3436_, 4, v_inst_3419_);
lean_closure_set(v___f_3436_, 5, v_inst_3420_);
lean_closure_set(v___f_3436_, 6, v_inst_3421_);
lean_closure_set(v___f_3436_, 7, v_n_u2080_3422_);
lean_closure_set(v___f_3436_, 8, v_filter_3425_);
lean_closure_set(v___f_3436_, 9, v_toBind_3431_);
lean_closure_set(v___f_3436_, 10, v___f_3434_);
lean_closure_set(v___f_3436_, 11, v___x_3435_);
lean_closure_set(v___f_3436_, 12, v___f_3433_);
v___f_3437_ = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal_x3f___redArg___lam__3), 2, 1);
lean_closure_set(v___f_3437_, 0, v_toPure_3432_);
v___x_3438_ = lean_apply_4(v_toBind_3431_, lean_box(0), lean_box(0), v_getEnv_3430_, v___f_3437_);
v___x_3439_ = lean_apply_4(v_toBind_3431_, lean_box(0), lean_box(0), v___x_3438_, v___f_3436_);
return v___x_3439_;
}
else
{
lean_object* v_toApplicative_3440_; lean_object* v_toBind_3441_; lean_object* v_toPure_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___f_3445_; lean_object* v___x_3446_; 
v_toApplicative_3440_ = lean_ctor_get(v_inst_3416_, 0);
v_toBind_3441_ = lean_ctor_get(v_inst_3416_, 1);
lean_inc(v_toBind_3441_);
v_toPure_3442_ = lean_ctor_get(v_toApplicative_3440_, 1);
lean_inc(v_toPure_3442_);
v___x_3443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3443_, 0, v_view_3426_);
lean_inc(v_n_u2081_3428_);
lean_inc_ref(v___x_3443_);
lean_inc(v_filter_3425_);
lean_inc(v_n_u2080_3422_);
lean_inc(v_inst_3421_);
lean_inc_ref(v_inst_3420_);
lean_inc(v_inst_3419_);
lean_inc_ref(v_inst_3418_);
lean_inc_ref(v_inst_3417_);
lean_inc_ref(v_inst_3416_);
v___x_3444_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg(v_inst_3416_, v_inst_3417_, v_inst_3418_, v_inst_3419_, v_inst_3420_, v_inst_3421_, v_n_u2080_3422_, v_filter_3425_, v___x_3443_, v_n_u2081_3428_);
v___f_3445_ = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal_x3f___redArg___lam__4), 12, 11);
lean_closure_set(v___f_3445_, 0, v_n_u2081_3428_);
lean_closure_set(v___f_3445_, 1, v_inst_3416_);
lean_closure_set(v___f_3445_, 2, v_inst_3417_);
lean_closure_set(v___f_3445_, 3, v_inst_3418_);
lean_closure_set(v___f_3445_, 4, v_inst_3419_);
lean_closure_set(v___f_3445_, 5, v_inst_3420_);
lean_closure_set(v___f_3445_, 6, v_inst_3421_);
lean_closure_set(v___f_3445_, 7, v_n_u2080_3422_);
lean_closure_set(v___f_3445_, 8, v_filter_3425_);
lean_closure_set(v___f_3445_, 9, v___x_3443_);
lean_closure_set(v___f_3445_, 10, v_toPure_3442_);
v___x_3446_ = lean_apply_4(v_toBind_3441_, lean_box(0), lean_box(0), v___x_3444_, v___f_3445_);
return v___x_3446_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___boxed(lean_object* v_inst_3447_, lean_object* v_inst_3448_, lean_object* v_inst_3449_, lean_object* v_inst_3450_, lean_object* v_inst_3451_, lean_object* v_inst_3452_, lean_object* v_n_u2080_3453_, lean_object* v_fullNames_3454_, lean_object* v_allowHorizAliases_3455_, lean_object* v_filter_3456_){
_start:
{
uint8_t v_fullNames_boxed_3457_; uint8_t v_allowHorizAliases_boxed_3458_; lean_object* v_res_3459_; 
v_fullNames_boxed_3457_ = lean_unbox(v_fullNames_3454_);
v_allowHorizAliases_boxed_3458_ = lean_unbox(v_allowHorizAliases_3455_);
v_res_3459_ = l_Lean_unresolveNameGlobal_x3f___redArg(v_inst_3447_, v_inst_3448_, v_inst_3449_, v_inst_3450_, v_inst_3451_, v_inst_3452_, v_n_u2080_3453_, v_fullNames_boxed_3457_, v_allowHorizAliases_boxed_3458_, v_filter_3456_);
return v_res_3459_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f(lean_object* v_m_3460_, lean_object* v_inst_3461_, lean_object* v_inst_3462_, lean_object* v_inst_3463_, lean_object* v_inst_3464_, lean_object* v_inst_3465_, lean_object* v_inst_3466_, lean_object* v_n_u2080_3467_, uint8_t v_fullNames_3468_, uint8_t v_allowHorizAliases_3469_, lean_object* v_filter_3470_){
_start:
{
lean_object* v___x_3471_; 
v___x_3471_ = l_Lean_unresolveNameGlobal_x3f___redArg(v_inst_3461_, v_inst_3462_, v_inst_3463_, v_inst_3464_, v_inst_3465_, v_inst_3466_, v_n_u2080_3467_, v_fullNames_3468_, v_allowHorizAliases_3469_, v_filter_3470_);
return v___x_3471_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___boxed(lean_object* v_m_3472_, lean_object* v_inst_3473_, lean_object* v_inst_3474_, lean_object* v_inst_3475_, lean_object* v_inst_3476_, lean_object* v_inst_3477_, lean_object* v_inst_3478_, lean_object* v_n_u2080_3479_, lean_object* v_fullNames_3480_, lean_object* v_allowHorizAliases_3481_, lean_object* v_filter_3482_){
_start:
{
uint8_t v_fullNames_boxed_3483_; uint8_t v_allowHorizAliases_boxed_3484_; lean_object* v_res_3485_; 
v_fullNames_boxed_3483_ = lean_unbox(v_fullNames_3480_);
v_allowHorizAliases_boxed_3484_ = lean_unbox(v_allowHorizAliases_3481_);
v_res_3485_ = l_Lean_unresolveNameGlobal_x3f(v_m_3472_, v_inst_3473_, v_inst_3474_, v_inst_3475_, v_inst_3476_, v_inst_3477_, v_inst_3478_, v_n_u2080_3479_, v_fullNames_boxed_3483_, v_allowHorizAliases_boxed_3484_, v_filter_3482_);
return v_res_3485_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___redArg___lam__0(lean_object* v_toPure_3486_, lean_object* v_n_u2080_3487_, lean_object* v_n_x3f_3488_){
_start:
{
if (lean_obj_tag(v_n_x3f_3488_) == 0)
{
lean_object* v___x_3489_; 
v___x_3489_ = lean_apply_2(v_toPure_3486_, lean_box(0), v_n_u2080_3487_);
return v___x_3489_;
}
else
{
lean_object* v_val_3490_; lean_object* v___x_3491_; 
lean_dec(v_n_u2080_3487_);
v_val_3490_ = lean_ctor_get(v_n_x3f_3488_, 0);
lean_inc(v_val_3490_);
lean_dec_ref_known(v_n_x3f_3488_, 1);
v___x_3491_ = lean_apply_2(v_toPure_3486_, lean_box(0), v_val_3490_);
return v___x_3491_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___redArg(lean_object* v_inst_3492_, lean_object* v_inst_3493_, lean_object* v_inst_3494_, lean_object* v_inst_3495_, lean_object* v_inst_3496_, lean_object* v_inst_3497_, lean_object* v_n_u2080_3498_, uint8_t v_fullNames_3499_, uint8_t v_allowHorizAliases_3500_, lean_object* v_filter_3501_){
_start:
{
lean_object* v_toApplicative_3502_; lean_object* v_toBind_3503_; lean_object* v_toPure_3504_; lean_object* v___x_3505_; lean_object* v___f_3506_; lean_object* v___x_3507_; 
v_toApplicative_3502_ = lean_ctor_get(v_inst_3492_, 0);
v_toBind_3503_ = lean_ctor_get(v_inst_3492_, 1);
lean_inc(v_toBind_3503_);
v_toPure_3504_ = lean_ctor_get(v_toApplicative_3502_, 1);
lean_inc(v_toPure_3504_);
lean_inc(v_n_u2080_3498_);
v___x_3505_ = l_Lean_unresolveNameGlobal_x3f___redArg(v_inst_3492_, v_inst_3493_, v_inst_3494_, v_inst_3495_, v_inst_3496_, v_inst_3497_, v_n_u2080_3498_, v_fullNames_3499_, v_allowHorizAliases_3500_, v_filter_3501_);
v___f_3506_ = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3506_, 0, v_toPure_3504_);
lean_closure_set(v___f_3506_, 1, v_n_u2080_3498_);
v___x_3507_ = lean_apply_4(v_toBind_3503_, lean_box(0), lean_box(0), v___x_3505_, v___f_3506_);
return v___x_3507_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___redArg___boxed(lean_object* v_inst_3508_, lean_object* v_inst_3509_, lean_object* v_inst_3510_, lean_object* v_inst_3511_, lean_object* v_inst_3512_, lean_object* v_inst_3513_, lean_object* v_n_u2080_3514_, lean_object* v_fullNames_3515_, lean_object* v_allowHorizAliases_3516_, lean_object* v_filter_3517_){
_start:
{
uint8_t v_fullNames_boxed_3518_; uint8_t v_allowHorizAliases_boxed_3519_; lean_object* v_res_3520_; 
v_fullNames_boxed_3518_ = lean_unbox(v_fullNames_3515_);
v_allowHorizAliases_boxed_3519_ = lean_unbox(v_allowHorizAliases_3516_);
v_res_3520_ = l_Lean_unresolveNameGlobal___redArg(v_inst_3508_, v_inst_3509_, v_inst_3510_, v_inst_3511_, v_inst_3512_, v_inst_3513_, v_n_u2080_3514_, v_fullNames_boxed_3518_, v_allowHorizAliases_boxed_3519_, v_filter_3517_);
return v_res_3520_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal(lean_object* v_m_3521_, lean_object* v_inst_3522_, lean_object* v_inst_3523_, lean_object* v_inst_3524_, lean_object* v_inst_3525_, lean_object* v_inst_3526_, lean_object* v_inst_3527_, lean_object* v_n_u2080_3528_, uint8_t v_fullNames_3529_, uint8_t v_allowHorizAliases_3530_, lean_object* v_filter_3531_){
_start:
{
lean_object* v___x_3532_; 
v___x_3532_ = l_Lean_unresolveNameGlobal___redArg(v_inst_3522_, v_inst_3523_, v_inst_3524_, v_inst_3525_, v_inst_3526_, v_inst_3527_, v_n_u2080_3528_, v_fullNames_3529_, v_allowHorizAliases_3530_, v_filter_3531_);
return v___x_3532_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___boxed(lean_object* v_m_3533_, lean_object* v_inst_3534_, lean_object* v_inst_3535_, lean_object* v_inst_3536_, lean_object* v_inst_3537_, lean_object* v_inst_3538_, lean_object* v_inst_3539_, lean_object* v_n_u2080_3540_, lean_object* v_fullNames_3541_, lean_object* v_allowHorizAliases_3542_, lean_object* v_filter_3543_){
_start:
{
uint8_t v_fullNames_boxed_3544_; uint8_t v_allowHorizAliases_boxed_3545_; lean_object* v_res_3546_; 
v_fullNames_boxed_3544_ = lean_unbox(v_fullNames_3541_);
v_allowHorizAliases_boxed_3545_ = lean_unbox(v_allowHorizAliases_3542_);
v_res_3546_ = l_Lean_unresolveNameGlobal(v_m_3533_, v_inst_3534_, v_inst_3535_, v_inst_3536_, v_inst_3537_, v_inst_3538_, v_inst_3539_, v_n_u2080_3540_, v_fullNames_boxed_3544_, v_allowHorizAliases_boxed_3545_, v_filter_3543_);
return v_res_3546_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg___lam__0(lean_object* v_toFunctor_3548_, lean_object* v_inst_3549_, lean_object* v_inst_3550_, lean_object* v_inst_3551_, lean_object* v_inst_3552_, lean_object* v_inst_3553_, lean_object* v_inst_3554_, lean_object* v_inst_3555_, lean_object* v_n_3556_){
_start:
{
lean_object* v_map_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; 
v_map_3557_ = lean_ctor_get(v_toFunctor_3548_, 0);
lean_inc(v_map_3557_);
lean_dec_ref(v_toFunctor_3548_);
v___x_3558_ = ((lean_object*)(l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg___lam__0___closed__0));
v___x_3559_ = l_Lean_resolveLocalName___redArg(v_inst_3549_, v_inst_3550_, v_inst_3551_, v_inst_3552_, v_inst_3553_, v_inst_3554_, v_inst_3555_, v_n_3556_);
v___x_3560_ = lean_apply_4(v_map_3557_, lean_box(0), lean_box(0), v___x_3558_, v___x_3559_);
return v___x_3560_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg(lean_object* v_inst_3561_, lean_object* v_inst_3562_, lean_object* v_inst_3563_, lean_object* v_inst_3564_, lean_object* v_inst_3565_, lean_object* v_inst_3566_, lean_object* v_inst_3567_, lean_object* v_n_u2080_3568_, uint8_t v_fullNames_3569_){
_start:
{
lean_object* v_toApplicative_3570_; lean_object* v_toFunctor_3571_; uint8_t v___x_3572_; lean_object* v___f_3573_; lean_object* v___x_3574_; 
v_toApplicative_3570_ = lean_ctor_get(v_inst_3561_, 0);
v_toFunctor_3571_ = lean_ctor_get(v_toApplicative_3570_, 0);
v___x_3572_ = 0;
lean_inc(v_inst_3566_);
lean_inc_ref(v_inst_3565_);
lean_inc(v_inst_3564_);
lean_inc_ref(v_inst_3563_);
lean_inc_ref(v_inst_3562_);
lean_inc_ref(v_inst_3561_);
lean_inc_ref(v_toFunctor_3571_);
v___f_3573_ = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg___lam__0), 9, 8);
lean_closure_set(v___f_3573_, 0, v_toFunctor_3571_);
lean_closure_set(v___f_3573_, 1, v_inst_3561_);
lean_closure_set(v___f_3573_, 2, v_inst_3562_);
lean_closure_set(v___f_3573_, 3, v_inst_3563_);
lean_closure_set(v___f_3573_, 4, v_inst_3564_);
lean_closure_set(v___f_3573_, 5, v_inst_3565_);
lean_closure_set(v___f_3573_, 6, v_inst_3566_);
lean_closure_set(v___f_3573_, 7, v_inst_3567_);
v___x_3574_ = l_Lean_unresolveNameGlobal_x3f___redArg(v_inst_3561_, v_inst_3562_, v_inst_3563_, v_inst_3564_, v_inst_3565_, v_inst_3566_, v_n_u2080_3568_, v_fullNames_3569_, v___x_3572_, v___f_3573_);
return v___x_3574_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg___boxed(lean_object* v_inst_3575_, lean_object* v_inst_3576_, lean_object* v_inst_3577_, lean_object* v_inst_3578_, lean_object* v_inst_3579_, lean_object* v_inst_3580_, lean_object* v_inst_3581_, lean_object* v_n_u2080_3582_, lean_object* v_fullNames_3583_){
_start:
{
uint8_t v_fullNames_boxed_3584_; lean_object* v_res_3585_; 
v_fullNames_boxed_3584_ = lean_unbox(v_fullNames_3583_);
v_res_3585_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg(v_inst_3575_, v_inst_3576_, v_inst_3577_, v_inst_3578_, v_inst_3579_, v_inst_3580_, v_inst_3581_, v_n_u2080_3582_, v_fullNames_boxed_3584_);
return v_res_3585_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f(lean_object* v_m_3586_, lean_object* v_inst_3587_, lean_object* v_inst_3588_, lean_object* v_inst_3589_, lean_object* v_inst_3590_, lean_object* v_inst_3591_, lean_object* v_inst_3592_, lean_object* v_inst_3593_, lean_object* v_n_u2080_3594_, uint8_t v_fullNames_3595_){
_start:
{
lean_object* v___x_3596_; 
v___x_3596_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg(v_inst_3587_, v_inst_3588_, v_inst_3589_, v_inst_3590_, v_inst_3591_, v_inst_3592_, v_inst_3593_, v_n_u2080_3594_, v_fullNames_3595_);
return v___x_3596_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___boxed(lean_object* v_m_3597_, lean_object* v_inst_3598_, lean_object* v_inst_3599_, lean_object* v_inst_3600_, lean_object* v_inst_3601_, lean_object* v_inst_3602_, lean_object* v_inst_3603_, lean_object* v_inst_3604_, lean_object* v_n_u2080_3605_, lean_object* v_fullNames_3606_){
_start:
{
uint8_t v_fullNames_boxed_3607_; lean_object* v_res_3608_; 
v_fullNames_boxed_3607_ = lean_unbox(v_fullNames_3606_);
v_res_3608_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f(v_m_3597_, v_inst_3598_, v_inst_3599_, v_inst_3600_, v_inst_3601_, v_inst_3602_, v_inst_3603_, v_inst_3604_, v_n_u2080_3605_, v_fullNames_boxed_3607_);
return v_res_3608_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals___redArg(lean_object* v_inst_3609_, lean_object* v_inst_3610_, lean_object* v_inst_3611_, lean_object* v_inst_3612_, lean_object* v_inst_3613_, lean_object* v_inst_3614_, lean_object* v_inst_3615_, lean_object* v_n_u2080_3616_, uint8_t v_fullNames_3617_){
_start:
{
lean_object* v_toApplicative_3618_; lean_object* v_toBind_3619_; lean_object* v_toPure_3620_; lean_object* v___x_3621_; lean_object* v___f_3622_; lean_object* v___x_3623_; 
v_toApplicative_3618_ = lean_ctor_get(v_inst_3609_, 0);
v_toBind_3619_ = lean_ctor_get(v_inst_3609_, 1);
lean_inc(v_toBind_3619_);
v_toPure_3620_ = lean_ctor_get(v_toApplicative_3618_, 1);
lean_inc(v_toPure_3620_);
lean_inc(v_n_u2080_3616_);
v___x_3621_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg(v_inst_3609_, v_inst_3610_, v_inst_3611_, v_inst_3612_, v_inst_3613_, v_inst_3614_, v_inst_3615_, v_n_u2080_3616_, v_fullNames_3617_);
v___f_3622_ = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3622_, 0, v_toPure_3620_);
lean_closure_set(v___f_3622_, 1, v_n_u2080_3616_);
v___x_3623_ = lean_apply_4(v_toBind_3619_, lean_box(0), lean_box(0), v___x_3621_, v___f_3622_);
return v___x_3623_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals___redArg___boxed(lean_object* v_inst_3624_, lean_object* v_inst_3625_, lean_object* v_inst_3626_, lean_object* v_inst_3627_, lean_object* v_inst_3628_, lean_object* v_inst_3629_, lean_object* v_inst_3630_, lean_object* v_n_u2080_3631_, lean_object* v_fullNames_3632_){
_start:
{
uint8_t v_fullNames_boxed_3633_; lean_object* v_res_3634_; 
v_fullNames_boxed_3633_ = lean_unbox(v_fullNames_3632_);
v_res_3634_ = l_Lean_unresolveNameGlobalAvoidingLocals___redArg(v_inst_3624_, v_inst_3625_, v_inst_3626_, v_inst_3627_, v_inst_3628_, v_inst_3629_, v_inst_3630_, v_n_u2080_3631_, v_fullNames_boxed_3633_);
return v_res_3634_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals(lean_object* v_m_3635_, lean_object* v_inst_3636_, lean_object* v_inst_3637_, lean_object* v_inst_3638_, lean_object* v_inst_3639_, lean_object* v_inst_3640_, lean_object* v_inst_3641_, lean_object* v_inst_3642_, lean_object* v_n_u2080_3643_, uint8_t v_fullNames_3644_){
_start:
{
lean_object* v___x_3645_; 
v___x_3645_ = l_Lean_unresolveNameGlobalAvoidingLocals___redArg(v_inst_3636_, v_inst_3637_, v_inst_3638_, v_inst_3639_, v_inst_3640_, v_inst_3641_, v_inst_3642_, v_n_u2080_3643_, v_fullNames_3644_);
return v___x_3645_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals___boxed(lean_object* v_m_3646_, lean_object* v_inst_3647_, lean_object* v_inst_3648_, lean_object* v_inst_3649_, lean_object* v_inst_3650_, lean_object* v_inst_3651_, lean_object* v_inst_3652_, lean_object* v_inst_3653_, lean_object* v_n_u2080_3654_, lean_object* v_fullNames_3655_){
_start:
{
uint8_t v_fullNames_boxed_3656_; lean_object* v_res_3657_; 
v_fullNames_boxed_3656_ = lean_unbox(v_fullNames_3655_);
v_res_3657_ = l_Lean_unresolveNameGlobalAvoidingLocals(v_m_3646_, v_inst_3647_, v_inst_3648_, v_inst_3649_, v_inst_3650_, v_inst_3651_, v_inst_3652_, v_inst_3653_, v_n_u2080_3654_, v_fullNames_boxed_3656_);
return v_res_3657_;
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
