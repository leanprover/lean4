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
lean_object* lean_private_to_user_name(lean_object*);
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
uint64_t lean_uint64_of_nat(lean_object*);
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
lean_object* l_Lean_initializing();
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
static lean_once_cell_t l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg___closed__0;
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
LEAN_EXPORT lean_object* lean_add_alias(lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_75_; 
v___x_75_ = l_Lean_initializing();
if (lean_obj_tag(v___x_75_) == 0)
{
lean_object* v_a_76_; lean_object* v___x_78_; uint8_t v_isShared_79_; uint8_t v_isSharedCheck_92_; 
v_a_76_ = lean_ctor_get(v___x_75_, 0);
v_isSharedCheck_92_ = !lean_is_exclusive(v___x_75_);
if (v_isSharedCheck_92_ == 0)
{
v___x_78_ = v___x_75_;
v_isShared_79_ = v_isSharedCheck_92_;
goto v_resetjp_77_;
}
else
{
lean_inc(v_a_76_);
lean_dec(v___x_75_);
v___x_78_ = lean_box(0);
v_isShared_79_ = v_isSharedCheck_92_;
goto v_resetjp_77_;
}
v_resetjp_77_:
{
uint8_t v___x_80_; 
v___x_80_ = lean_unbox(v_a_76_);
lean_dec(v_a_76_);
if (v___x_80_ == 0)
{
lean_object* v___x_81_; lean_object* v___x_83_; 
lean_dec_ref(v_p_73_);
v___x_81_ = lean_obj_once(&l_Lean_registerReservedNamePredicate___closed__1, &l_Lean_registerReservedNamePredicate___closed__1_once, _init_l_Lean_registerReservedNamePredicate___closed__1);
if (v_isShared_79_ == 0)
{
lean_ctor_set_tag(v___x_78_, 1);
lean_ctor_set(v___x_78_, 0, v___x_81_);
v___x_83_ = v___x_78_;
goto v_reusejp_82_;
}
else
{
lean_object* v_reuseFailAlloc_84_; 
v_reuseFailAlloc_84_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_84_, 0, v___x_81_);
v___x_83_ = v_reuseFailAlloc_84_;
goto v_reusejp_82_;
}
v_reusejp_82_:
{
return v___x_83_;
}
}
else
{
lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_90_; 
v___x_85_ = l_Lean_reservedNamePredicatesRef;
v___x_86_ = lean_st_ref_take(v___x_85_);
v___x_87_ = lean_array_push(v___x_86_, v_p_73_);
v___x_88_ = lean_st_ref_set(v___x_85_, v___x_87_);
if (v_isShared_79_ == 0)
{
lean_ctor_set(v___x_78_, 0, v___x_88_);
v___x_90_ = v___x_78_;
goto v_reusejp_89_;
}
else
{
lean_object* v_reuseFailAlloc_91_; 
v_reuseFailAlloc_91_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_91_, 0, v___x_88_);
v___x_90_ = v_reuseFailAlloc_91_;
goto v_reusejp_89_;
}
v_reusejp_89_:
{
return v___x_90_;
}
}
}
}
else
{
lean_object* v_a_93_; lean_object* v___x_95_; uint8_t v_isShared_96_; uint8_t v_isSharedCheck_100_; 
lean_dec_ref(v_p_73_);
v_a_93_ = lean_ctor_get(v___x_75_, 0);
v_isSharedCheck_100_ = !lean_is_exclusive(v___x_75_);
if (v_isSharedCheck_100_ == 0)
{
v___x_95_ = v___x_75_;
v_isShared_96_ = v_isSharedCheck_100_;
goto v_resetjp_94_;
}
else
{
lean_inc(v_a_93_);
lean_dec(v___x_75_);
v___x_95_ = lean_box(0);
v_isShared_96_ = v_isSharedCheck_100_;
goto v_resetjp_94_;
}
v_resetjp_94_:
{
lean_object* v___x_98_; 
if (v_isShared_96_ == 0)
{
v___x_98_ = v___x_95_;
goto v_reusejp_97_;
}
else
{
lean_object* v_reuseFailAlloc_99_; 
v_reuseFailAlloc_99_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_99_, 0, v_a_93_);
v___x_98_ = v_reuseFailAlloc_99_;
goto v_reusejp_97_;
}
v_reusejp_97_:
{
return v___x_98_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_registerReservedNamePredicate___boxed(lean_object* v_p_101_, lean_object* v_a_102_){
_start:
{
lean_object* v_res_103_; 
v_res_103_ = l_Lean_registerReservedNamePredicate(v_p_101_);
return v_res_103_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn___lam__0_00___x40_Lean_ResolveName_405991711____hygCtx___hyg_2_(lean_object* v___x_104_){
_start:
{
lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_106_ = lean_st_ref_get(v___x_104_);
v___x_107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_107_, 0, v___x_106_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn___lam__0_00___x40_Lean_ResolveName_405991711____hygCtx___hyg_2____boxed(lean_object* v___x_108_, lean_object* v___y_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l___private_Lean_ResolveName_0__Lean_initFn___lam__0_00___x40_Lean_ResolveName_405991711____hygCtx___hyg_2_(v___x_108_);
lean_dec(v___x_108_);
return v_res_110_;
}
}
static lean_object* _init_l___private_Lean_ResolveName_0__Lean_initFn___closed__0_00___x40_Lean_ResolveName_405991711____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_111_; lean_object* v___f_112_; 
v___x_111_ = l_Lean_reservedNamePredicatesRef;
v___f_112_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_initFn___lam__0_00___x40_Lean_ResolveName_405991711____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_112_, 0, v___x_111_);
return v___f_112_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_405991711____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
v___f_114_ = lean_obj_once(&l___private_Lean_ResolveName_0__Lean_initFn___closed__0_00___x40_Lean_ResolveName_405991711____hygCtx___hyg_2_, &l___private_Lean_ResolveName_0__Lean_initFn___closed__0_00___x40_Lean_ResolveName_405991711____hygCtx___hyg_2__once, _init_l___private_Lean_ResolveName_0__Lean_initFn___closed__0_00___x40_Lean_ResolveName_405991711____hygCtx___hyg_2_);
v___x_115_ = lean_box(0);
v___x_116_ = lean_box(2);
v___x_117_ = l_Lean_registerEnvExtension___redArg(v___f_114_, v___x_115_, v___x_116_);
return v___x_117_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_405991711____hygCtx___hyg_2____boxed(lean_object* v_a_118_){
_start:
{
lean_object* v_res_119_; 
v_res_119_ = l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_405991711____hygCtx___hyg_2_();
return v_res_119_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_isReservedName_spec__0(lean_object* v_env_120_, lean_object* v_name_121_, lean_object* v_as_122_, size_t v_i_123_, size_t v_stop_124_){
_start:
{
uint8_t v___x_125_; 
v___x_125_ = lean_usize_dec_eq(v_i_123_, v_stop_124_);
if (v___x_125_ == 0)
{
lean_object* v___x_161__overap_126_; lean_object* v___x_127_; uint8_t v___x_128_; 
v___x_161__overap_126_ = lean_array_uget_borrowed(v_as_122_, v_i_123_);
lean_inc(v___x_161__overap_126_);
lean_inc(v_name_121_);
lean_inc_ref(v_env_120_);
v___x_127_ = lean_apply_2(v___x_161__overap_126_, v_env_120_, v_name_121_);
v___x_128_ = lean_unbox(v___x_127_);
if (v___x_128_ == 0)
{
size_t v___x_129_; size_t v___x_130_; 
v___x_129_ = ((size_t)1ULL);
v___x_130_ = lean_usize_add(v_i_123_, v___x_129_);
v_i_123_ = v___x_130_;
goto _start;
}
else
{
uint8_t v___x_132_; 
lean_dec(v_name_121_);
lean_dec_ref(v_env_120_);
v___x_132_ = lean_unbox(v___x_127_);
return v___x_132_;
}
}
else
{
uint8_t v___x_133_; 
lean_dec(v_name_121_);
lean_dec_ref(v_env_120_);
v___x_133_ = 0;
return v___x_133_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_isReservedName_spec__0___boxed(lean_object* v_env_134_, lean_object* v_name_135_, lean_object* v_as_136_, lean_object* v_i_137_, lean_object* v_stop_138_){
_start:
{
size_t v_i_boxed_139_; size_t v_stop_boxed_140_; uint8_t v_res_141_; lean_object* v_r_142_; 
v_i_boxed_139_ = lean_unbox_usize(v_i_137_);
lean_dec(v_i_137_);
v_stop_boxed_140_ = lean_unbox_usize(v_stop_138_);
lean_dec(v_stop_138_);
v_res_141_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_isReservedName_spec__0(v_env_134_, v_name_135_, v_as_136_, v_i_boxed_139_, v_stop_boxed_140_);
lean_dec_ref(v_as_136_);
v_r_142_ = lean_box(v_res_141_);
return v_r_142_;
}
}
static lean_object* _init_l_Lean_isReservedName___closed__0(void){
_start:
{
lean_object* v___x_143_; 
v___x_143_ = l_Array_instInhabited(lean_box(0));
return v___x_143_;
}
}
LEAN_EXPORT uint8_t lean_is_reserved_name(lean_object* v_env_144_, lean_object* v_name_145_){
_start:
{
lean_object* v___x_146_; lean_object* v_asyncMode_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; uint8_t v___x_153_; 
v___x_146_ = l_Lean_reservedNamePredicatesExt;
v_asyncMode_147_ = lean_ctor_get(v___x_146_, 2);
v___x_148_ = lean_obj_once(&l_Lean_isReservedName___closed__0, &l_Lean_isReservedName___closed__0_once, _init_l_Lean_isReservedName___closed__0);
v___x_149_ = lean_box(0);
lean_inc_ref(v_env_144_);
v___x_150_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_148_, v___x_146_, v_env_144_, v_asyncMode_147_, v___x_149_);
v___x_151_ = lean_unsigned_to_nat(0u);
v___x_152_ = lean_array_get_size(v___x_150_);
v___x_153_ = lean_nat_dec_lt(v___x_151_, v___x_152_);
if (v___x_153_ == 0)
{
lean_dec(v___x_150_);
lean_dec(v_name_145_);
lean_dec_ref(v_env_144_);
return v___x_153_;
}
else
{
if (v___x_153_ == 0)
{
lean_dec(v___x_150_);
lean_dec(v_name_145_);
lean_dec_ref(v_env_144_);
return v___x_153_;
}
else
{
size_t v___x_154_; size_t v___x_155_; uint8_t v___x_156_; 
v___x_154_ = ((size_t)0ULL);
v___x_155_ = lean_usize_of_nat(v___x_152_);
v___x_156_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_isReservedName_spec__0(v_env_144_, v_name_145_, v___x_150_, v___x_154_, v___x_155_);
lean_dec(v___x_150_);
return v___x_156_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isReservedName___boxed(lean_object* v_env_157_, lean_object* v_name_158_){
_start:
{
uint8_t v_res_159_; lean_object* v_r_160_; 
v_res_159_ = lean_is_reserved_name(v_env_157_, v_name_158_);
v_r_160_ = lean_box(v_res_159_);
return v_r_160_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__9_spec__11___redArg(lean_object* v_x_161_, lean_object* v_x_162_, lean_object* v_x_163_, lean_object* v_x_164_){
_start:
{
lean_object* v_ks_165_; lean_object* v_vs_166_; lean_object* v___x_168_; uint8_t v_isShared_169_; uint8_t v_isSharedCheck_190_; 
v_ks_165_ = lean_ctor_get(v_x_161_, 0);
v_vs_166_ = lean_ctor_get(v_x_161_, 1);
v_isSharedCheck_190_ = !lean_is_exclusive(v_x_161_);
if (v_isSharedCheck_190_ == 0)
{
v___x_168_ = v_x_161_;
v_isShared_169_ = v_isSharedCheck_190_;
goto v_resetjp_167_;
}
else
{
lean_inc(v_vs_166_);
lean_inc(v_ks_165_);
lean_dec(v_x_161_);
v___x_168_ = lean_box(0);
v_isShared_169_ = v_isSharedCheck_190_;
goto v_resetjp_167_;
}
v_resetjp_167_:
{
lean_object* v___x_170_; uint8_t v___x_171_; 
v___x_170_ = lean_array_get_size(v_ks_165_);
v___x_171_ = lean_nat_dec_lt(v_x_162_, v___x_170_);
if (v___x_171_ == 0)
{
lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_175_; 
lean_dec(v_x_162_);
v___x_172_ = lean_array_push(v_ks_165_, v_x_163_);
v___x_173_ = lean_array_push(v_vs_166_, v_x_164_);
if (v_isShared_169_ == 0)
{
lean_ctor_set(v___x_168_, 1, v___x_173_);
lean_ctor_set(v___x_168_, 0, v___x_172_);
v___x_175_ = v___x_168_;
goto v_reusejp_174_;
}
else
{
lean_object* v_reuseFailAlloc_176_; 
v_reuseFailAlloc_176_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_176_, 0, v___x_172_);
lean_ctor_set(v_reuseFailAlloc_176_, 1, v___x_173_);
v___x_175_ = v_reuseFailAlloc_176_;
goto v_reusejp_174_;
}
v_reusejp_174_:
{
return v___x_175_;
}
}
else
{
lean_object* v_k_x27_177_; uint8_t v___x_178_; 
v_k_x27_177_ = lean_array_fget_borrowed(v_ks_165_, v_x_162_);
v___x_178_ = lean_name_eq(v_x_163_, v_k_x27_177_);
if (v___x_178_ == 0)
{
lean_object* v___x_180_; 
if (v_isShared_169_ == 0)
{
v___x_180_ = v___x_168_;
goto v_reusejp_179_;
}
else
{
lean_object* v_reuseFailAlloc_184_; 
v_reuseFailAlloc_184_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_184_, 0, v_ks_165_);
lean_ctor_set(v_reuseFailAlloc_184_, 1, v_vs_166_);
v___x_180_ = v_reuseFailAlloc_184_;
goto v_reusejp_179_;
}
v_reusejp_179_:
{
lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_181_ = lean_unsigned_to_nat(1u);
v___x_182_ = lean_nat_add(v_x_162_, v___x_181_);
lean_dec(v_x_162_);
v_x_161_ = v___x_180_;
v_x_162_ = v___x_182_;
goto _start;
}
}
else
{
lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_188_; 
v___x_185_ = lean_array_fset(v_ks_165_, v_x_162_, v_x_163_);
v___x_186_ = lean_array_fset(v_vs_166_, v_x_162_, v_x_164_);
lean_dec(v_x_162_);
if (v_isShared_169_ == 0)
{
lean_ctor_set(v___x_168_, 1, v___x_186_);
lean_ctor_set(v___x_168_, 0, v___x_185_);
v___x_188_ = v___x_168_;
goto v_reusejp_187_;
}
else
{
lean_object* v_reuseFailAlloc_189_; 
v_reuseFailAlloc_189_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_189_, 0, v___x_185_);
lean_ctor_set(v_reuseFailAlloc_189_, 1, v___x_186_);
v___x_188_ = v_reuseFailAlloc_189_;
goto v_reusejp_187_;
}
v_reusejp_187_:
{
return v___x_188_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__9___redArg(lean_object* v_n_191_, lean_object* v_k_192_, lean_object* v_v_193_){
_start:
{
lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_194_ = lean_unsigned_to_nat(0u);
v___x_195_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__9_spec__11___redArg(v_n_191_, v___x_194_, v_k_192_, v_v_193_);
return v___x_195_;
}
}
static uint64_t _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg___closed__0(void){
_start:
{
lean_object* v___x_196_; uint64_t v___x_197_; 
v___x_196_ = lean_unsigned_to_nat(1723u);
v___x_197_ = lean_uint64_of_nat(v___x_196_);
return v___x_197_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_198_; 
v___x_198_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg(lean_object* v_x_199_, size_t v_x_200_, size_t v_x_201_, lean_object* v_x_202_, lean_object* v_x_203_){
_start:
{
if (lean_obj_tag(v_x_199_) == 0)
{
lean_object* v_es_204_; size_t v___x_205_; size_t v___x_206_; lean_object* v_j_207_; lean_object* v___x_208_; uint8_t v___x_209_; 
v_es_204_ = lean_ctor_get(v_x_199_, 0);
v___x_205_ = ((size_t)31ULL);
v___x_206_ = lean_usize_land(v_x_200_, v___x_205_);
v_j_207_ = lean_usize_to_nat(v___x_206_);
v___x_208_ = lean_array_get_size(v_es_204_);
v___x_209_ = lean_nat_dec_lt(v_j_207_, v___x_208_);
if (v___x_209_ == 0)
{
lean_dec(v_j_207_);
lean_dec(v_x_203_);
lean_dec(v_x_202_);
return v_x_199_;
}
else
{
lean_object* v___x_211_; uint8_t v_isShared_212_; uint8_t v_isSharedCheck_248_; 
lean_inc_ref(v_es_204_);
v_isSharedCheck_248_ = !lean_is_exclusive(v_x_199_);
if (v_isSharedCheck_248_ == 0)
{
lean_object* v_unused_249_; 
v_unused_249_ = lean_ctor_get(v_x_199_, 0);
lean_dec(v_unused_249_);
v___x_211_ = v_x_199_;
v_isShared_212_ = v_isSharedCheck_248_;
goto v_resetjp_210_;
}
else
{
lean_dec(v_x_199_);
v___x_211_ = lean_box(0);
v_isShared_212_ = v_isSharedCheck_248_;
goto v_resetjp_210_;
}
v_resetjp_210_:
{
lean_object* v_v_213_; lean_object* v___x_214_; lean_object* v_xs_x27_215_; lean_object* v___y_217_; 
v_v_213_ = lean_array_fget(v_es_204_, v_j_207_);
v___x_214_ = lean_box(0);
v_xs_x27_215_ = lean_array_fset(v_es_204_, v_j_207_, v___x_214_);
switch(lean_obj_tag(v_v_213_))
{
case 0:
{
lean_object* v_key_222_; lean_object* v_val_223_; lean_object* v___x_225_; uint8_t v_isShared_226_; uint8_t v_isSharedCheck_233_; 
v_key_222_ = lean_ctor_get(v_v_213_, 0);
v_val_223_ = lean_ctor_get(v_v_213_, 1);
v_isSharedCheck_233_ = !lean_is_exclusive(v_v_213_);
if (v_isSharedCheck_233_ == 0)
{
v___x_225_ = v_v_213_;
v_isShared_226_ = v_isSharedCheck_233_;
goto v_resetjp_224_;
}
else
{
lean_inc(v_val_223_);
lean_inc(v_key_222_);
lean_dec(v_v_213_);
v___x_225_ = lean_box(0);
v_isShared_226_ = v_isSharedCheck_233_;
goto v_resetjp_224_;
}
v_resetjp_224_:
{
uint8_t v___x_227_; 
v___x_227_ = lean_name_eq(v_x_202_, v_key_222_);
if (v___x_227_ == 0)
{
lean_object* v___x_228_; lean_object* v___x_229_; 
lean_del_object(v___x_225_);
v___x_228_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_222_, v_val_223_, v_x_202_, v_x_203_);
v___x_229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_229_, 0, v___x_228_);
v___y_217_ = v___x_229_;
goto v___jp_216_;
}
else
{
lean_object* v___x_231_; 
lean_dec(v_val_223_);
lean_dec(v_key_222_);
if (v_isShared_226_ == 0)
{
lean_ctor_set(v___x_225_, 1, v_x_203_);
lean_ctor_set(v___x_225_, 0, v_x_202_);
v___x_231_ = v___x_225_;
goto v_reusejp_230_;
}
else
{
lean_object* v_reuseFailAlloc_232_; 
v_reuseFailAlloc_232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_232_, 0, v_x_202_);
lean_ctor_set(v_reuseFailAlloc_232_, 1, v_x_203_);
v___x_231_ = v_reuseFailAlloc_232_;
goto v_reusejp_230_;
}
v_reusejp_230_:
{
v___y_217_ = v___x_231_;
goto v___jp_216_;
}
}
}
}
case 1:
{
lean_object* v_node_234_; lean_object* v___x_236_; uint8_t v_isShared_237_; uint8_t v_isSharedCheck_246_; 
v_node_234_ = lean_ctor_get(v_v_213_, 0);
v_isSharedCheck_246_ = !lean_is_exclusive(v_v_213_);
if (v_isSharedCheck_246_ == 0)
{
v___x_236_ = v_v_213_;
v_isShared_237_ = v_isSharedCheck_246_;
goto v_resetjp_235_;
}
else
{
lean_inc(v_node_234_);
lean_dec(v_v_213_);
v___x_236_ = lean_box(0);
v_isShared_237_ = v_isSharedCheck_246_;
goto v_resetjp_235_;
}
v_resetjp_235_:
{
size_t v___x_238_; size_t v___x_239_; size_t v___x_240_; size_t v___x_241_; lean_object* v___x_242_; lean_object* v___x_244_; 
v___x_238_ = ((size_t)5ULL);
v___x_239_ = lean_usize_shift_right(v_x_200_, v___x_238_);
v___x_240_ = ((size_t)1ULL);
v___x_241_ = lean_usize_add(v_x_201_, v___x_240_);
v___x_242_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg(v_node_234_, v___x_239_, v___x_241_, v_x_202_, v_x_203_);
if (v_isShared_237_ == 0)
{
lean_ctor_set(v___x_236_, 0, v___x_242_);
v___x_244_ = v___x_236_;
goto v_reusejp_243_;
}
else
{
lean_object* v_reuseFailAlloc_245_; 
v_reuseFailAlloc_245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_245_, 0, v___x_242_);
v___x_244_ = v_reuseFailAlloc_245_;
goto v_reusejp_243_;
}
v_reusejp_243_:
{
v___y_217_ = v___x_244_;
goto v___jp_216_;
}
}
}
default: 
{
lean_object* v___x_247_; 
v___x_247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_247_, 0, v_x_202_);
lean_ctor_set(v___x_247_, 1, v_x_203_);
v___y_217_ = v___x_247_;
goto v___jp_216_;
}
}
v___jp_216_:
{
lean_object* v___x_218_; lean_object* v___x_220_; 
v___x_218_ = lean_array_fset(v_xs_x27_215_, v_j_207_, v___y_217_);
lean_dec(v_j_207_);
if (v_isShared_212_ == 0)
{
lean_ctor_set(v___x_211_, 0, v___x_218_);
v___x_220_ = v___x_211_;
goto v_reusejp_219_;
}
else
{
lean_object* v_reuseFailAlloc_221_; 
v_reuseFailAlloc_221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_221_, 0, v___x_218_);
v___x_220_ = v_reuseFailAlloc_221_;
goto v_reusejp_219_;
}
v_reusejp_219_:
{
return v___x_220_;
}
}
}
}
}
else
{
lean_object* v_ks_250_; lean_object* v_vs_251_; lean_object* v___x_253_; uint8_t v_isShared_254_; uint8_t v_isSharedCheck_271_; 
v_ks_250_ = lean_ctor_get(v_x_199_, 0);
v_vs_251_ = lean_ctor_get(v_x_199_, 1);
v_isSharedCheck_271_ = !lean_is_exclusive(v_x_199_);
if (v_isSharedCheck_271_ == 0)
{
v___x_253_ = v_x_199_;
v_isShared_254_ = v_isSharedCheck_271_;
goto v_resetjp_252_;
}
else
{
lean_inc(v_vs_251_);
lean_inc(v_ks_250_);
lean_dec(v_x_199_);
v___x_253_ = lean_box(0);
v_isShared_254_ = v_isSharedCheck_271_;
goto v_resetjp_252_;
}
v_resetjp_252_:
{
lean_object* v___x_256_; 
if (v_isShared_254_ == 0)
{
v___x_256_ = v___x_253_;
goto v_reusejp_255_;
}
else
{
lean_object* v_reuseFailAlloc_270_; 
v_reuseFailAlloc_270_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_270_, 0, v_ks_250_);
lean_ctor_set(v_reuseFailAlloc_270_, 1, v_vs_251_);
v___x_256_ = v_reuseFailAlloc_270_;
goto v_reusejp_255_;
}
v_reusejp_255_:
{
lean_object* v_newNode_257_; uint8_t v___y_259_; size_t v___x_265_; uint8_t v___x_266_; 
v_newNode_257_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__9___redArg(v___x_256_, v_x_202_, v_x_203_);
v___x_265_ = ((size_t)7ULL);
v___x_266_ = lean_usize_dec_le(v___x_265_, v_x_201_);
if (v___x_266_ == 0)
{
lean_object* v___x_267_; lean_object* v___x_268_; uint8_t v___x_269_; 
v___x_267_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_257_);
v___x_268_ = lean_unsigned_to_nat(4u);
v___x_269_ = lean_nat_dec_lt(v___x_267_, v___x_268_);
lean_dec(v___x_267_);
v___y_259_ = v___x_269_;
goto v___jp_258_;
}
else
{
v___y_259_ = v___x_266_;
goto v___jp_258_;
}
v___jp_258_:
{
if (v___y_259_ == 0)
{
lean_object* v_ks_260_; lean_object* v_vs_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
v_ks_260_ = lean_ctor_get(v_newNode_257_, 0);
lean_inc_ref(v_ks_260_);
v_vs_261_ = lean_ctor_get(v_newNode_257_, 1);
lean_inc_ref(v_vs_261_);
lean_dec_ref(v_newNode_257_);
v___x_262_ = lean_unsigned_to_nat(0u);
v___x_263_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg___closed__0);
v___x_264_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg(v_x_201_, v_ks_260_, v_vs_261_, v___x_262_, v___x_263_);
lean_dec_ref(v_vs_261_);
lean_dec_ref(v_ks_260_);
return v___x_264_;
}
else
{
return v_newNode_257_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg(size_t v_depth_272_, lean_object* v_keys_273_, lean_object* v_vals_274_, lean_object* v_i_275_, lean_object* v_entries_276_){
_start:
{
lean_object* v___x_277_; uint8_t v___x_278_; 
v___x_277_ = lean_array_get_size(v_keys_273_);
v___x_278_ = lean_nat_dec_lt(v_i_275_, v___x_277_);
if (v___x_278_ == 0)
{
lean_dec(v_i_275_);
return v_entries_276_;
}
else
{
lean_object* v_k_279_; lean_object* v_v_280_; uint64_t v___y_282_; 
v_k_279_ = lean_array_fget_borrowed(v_keys_273_, v_i_275_);
v_v_280_ = lean_array_fget_borrowed(v_vals_274_, v_i_275_);
if (lean_obj_tag(v_k_279_) == 0)
{
uint64_t v___x_293_; 
v___x_293_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg___closed__0);
v___y_282_ = v___x_293_;
goto v___jp_281_;
}
else
{
uint64_t v_hash_294_; 
v_hash_294_ = lean_ctor_get_uint64(v_k_279_, sizeof(void*)*2);
v___y_282_ = v_hash_294_;
goto v___jp_281_;
}
v___jp_281_:
{
size_t v_h_283_; size_t v___x_284_; lean_object* v___x_285_; size_t v___x_286_; size_t v___x_287_; size_t v___x_288_; size_t v_h_289_; lean_object* v___x_290_; lean_object* v___x_291_; 
v_h_283_ = lean_uint64_to_usize(v___y_282_);
v___x_284_ = ((size_t)5ULL);
v___x_285_ = lean_unsigned_to_nat(1u);
v___x_286_ = ((size_t)1ULL);
v___x_287_ = lean_usize_sub(v_depth_272_, v___x_286_);
v___x_288_ = lean_usize_mul(v___x_284_, v___x_287_);
v_h_289_ = lean_usize_shift_right(v_h_283_, v___x_288_);
v___x_290_ = lean_nat_add(v_i_275_, v___x_285_);
lean_dec(v_i_275_);
lean_inc(v_v_280_);
lean_inc(v_k_279_);
v___x_291_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg(v_entries_276_, v_h_289_, v_depth_272_, v_k_279_, v_v_280_);
v_i_275_ = v___x_290_;
v_entries_276_ = v___x_291_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg___boxed(lean_object* v_depth_295_, lean_object* v_keys_296_, lean_object* v_vals_297_, lean_object* v_i_298_, lean_object* v_entries_299_){
_start:
{
size_t v_depth_boxed_300_; lean_object* v_res_301_; 
v_depth_boxed_300_ = lean_unbox_usize(v_depth_295_);
lean_dec(v_depth_295_);
v_res_301_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg(v_depth_boxed_300_, v_keys_296_, v_vals_297_, v_i_298_, v_entries_299_);
lean_dec_ref(v_vals_297_);
lean_dec_ref(v_keys_296_);
return v_res_301_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg___boxed(lean_object* v_x_302_, lean_object* v_x_303_, lean_object* v_x_304_, lean_object* v_x_305_, lean_object* v_x_306_){
_start:
{
size_t v_x_1094__boxed_307_; size_t v_x_1095__boxed_308_; lean_object* v_res_309_; 
v_x_1094__boxed_307_ = lean_unbox_usize(v_x_303_);
lean_dec(v_x_303_);
v_x_1095__boxed_308_ = lean_unbox_usize(v_x_304_);
lean_dec(v_x_304_);
v_res_309_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg(v_x_302_, v_x_1094__boxed_307_, v_x_1095__boxed_308_, v_x_305_, v_x_306_);
return v_res_309_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3___redArg(lean_object* v_x_310_, lean_object* v_x_311_, lean_object* v_x_312_){
_start:
{
uint64_t v___y_314_; 
if (lean_obj_tag(v_x_311_) == 0)
{
uint64_t v___x_318_; 
v___x_318_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg___closed__0);
v___y_314_ = v___x_318_;
goto v___jp_313_;
}
else
{
uint64_t v_hash_319_; 
v_hash_319_ = lean_ctor_get_uint64(v_x_311_, sizeof(void*)*2);
v___y_314_ = v_hash_319_;
goto v___jp_313_;
}
v___jp_313_:
{
size_t v___x_315_; size_t v___x_316_; lean_object* v___x_317_; 
v___x_315_ = lean_uint64_to_usize(v___y_314_);
v___x_316_ = ((size_t)1ULL);
v___x_317_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg(v_x_310_, v___x_315_, v___x_316_, v_x_311_, v_x_312_);
return v___x_317_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9_spec__14_spec__16___redArg(lean_object* v_x_320_, lean_object* v_x_321_){
_start:
{
if (lean_obj_tag(v_x_321_) == 0)
{
return v_x_320_;
}
else
{
lean_object* v_key_322_; lean_object* v_value_323_; lean_object* v_tail_324_; lean_object* v___x_326_; uint8_t v_isShared_327_; uint8_t v_isSharedCheck_350_; 
v_key_322_ = lean_ctor_get(v_x_321_, 0);
v_value_323_ = lean_ctor_get(v_x_321_, 1);
v_tail_324_ = lean_ctor_get(v_x_321_, 2);
v_isSharedCheck_350_ = !lean_is_exclusive(v_x_321_);
if (v_isSharedCheck_350_ == 0)
{
v___x_326_ = v_x_321_;
v_isShared_327_ = v_isSharedCheck_350_;
goto v_resetjp_325_;
}
else
{
lean_inc(v_tail_324_);
lean_inc(v_value_323_);
lean_inc(v_key_322_);
lean_dec(v_x_321_);
v___x_326_ = lean_box(0);
v_isShared_327_ = v_isSharedCheck_350_;
goto v_resetjp_325_;
}
v_resetjp_325_:
{
lean_object* v___x_328_; uint64_t v___y_330_; 
v___x_328_ = lean_array_get_size(v_x_320_);
if (lean_obj_tag(v_key_322_) == 0)
{
uint64_t v___x_348_; 
v___x_348_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg___closed__0);
v___y_330_ = v___x_348_;
goto v___jp_329_;
}
else
{
uint64_t v_hash_349_; 
v_hash_349_ = lean_ctor_get_uint64(v_key_322_, sizeof(void*)*2);
v___y_330_ = v_hash_349_;
goto v___jp_329_;
}
v___jp_329_:
{
uint64_t v___x_331_; uint64_t v___x_332_; uint64_t v_fold_333_; uint64_t v___x_334_; uint64_t v___x_335_; uint64_t v___x_336_; size_t v___x_337_; size_t v___x_338_; size_t v___x_339_; size_t v___x_340_; size_t v___x_341_; lean_object* v___x_342_; lean_object* v___x_344_; 
v___x_331_ = 32ULL;
v___x_332_ = lean_uint64_shift_right(v___y_330_, v___x_331_);
v_fold_333_ = lean_uint64_xor(v___y_330_, v___x_332_);
v___x_334_ = 16ULL;
v___x_335_ = lean_uint64_shift_right(v_fold_333_, v___x_334_);
v___x_336_ = lean_uint64_xor(v_fold_333_, v___x_335_);
v___x_337_ = lean_uint64_to_usize(v___x_336_);
v___x_338_ = lean_usize_of_nat(v___x_328_);
v___x_339_ = ((size_t)1ULL);
v___x_340_ = lean_usize_sub(v___x_338_, v___x_339_);
v___x_341_ = lean_usize_land(v___x_337_, v___x_340_);
v___x_342_ = lean_array_uget_borrowed(v_x_320_, v___x_341_);
lean_inc(v___x_342_);
if (v_isShared_327_ == 0)
{
lean_ctor_set(v___x_326_, 2, v___x_342_);
v___x_344_ = v___x_326_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v_key_322_);
lean_ctor_set(v_reuseFailAlloc_347_, 1, v_value_323_);
lean_ctor_set(v_reuseFailAlloc_347_, 2, v___x_342_);
v___x_344_ = v_reuseFailAlloc_347_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
lean_object* v___x_345_; 
v___x_345_ = lean_array_uset(v_x_320_, v___x_341_, v___x_344_);
v_x_320_ = v___x_345_;
v_x_321_ = v_tail_324_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9_spec__14___redArg(lean_object* v_i_351_, lean_object* v_source_352_, lean_object* v_target_353_){
_start:
{
lean_object* v___x_354_; uint8_t v___x_355_; 
v___x_354_ = lean_array_get_size(v_source_352_);
v___x_355_ = lean_nat_dec_lt(v_i_351_, v___x_354_);
if (v___x_355_ == 0)
{
lean_dec_ref(v_source_352_);
lean_dec(v_i_351_);
return v_target_353_;
}
else
{
lean_object* v_es_356_; lean_object* v___x_357_; lean_object* v_source_358_; lean_object* v_target_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
v_es_356_ = lean_array_fget(v_source_352_, v_i_351_);
v___x_357_ = lean_box(0);
v_source_358_ = lean_array_fset(v_source_352_, v_i_351_, v___x_357_);
v_target_359_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9_spec__14_spec__16___redArg(v_target_353_, v_es_356_);
v___x_360_ = lean_unsigned_to_nat(1u);
v___x_361_ = lean_nat_add(v_i_351_, v___x_360_);
lean_dec(v_i_351_);
v_i_351_ = v___x_361_;
v_source_352_ = v_source_358_;
v_target_353_ = v_target_359_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9___redArg(lean_object* v_data_363_){
_start:
{
lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v_nbuckets_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_364_ = lean_array_get_size(v_data_363_);
v___x_365_ = lean_unsigned_to_nat(2u);
v_nbuckets_366_ = lean_nat_mul(v___x_364_, v___x_365_);
v___x_367_ = lean_unsigned_to_nat(0u);
v___x_368_ = lean_box(0);
v___x_369_ = lean_mk_array(v_nbuckets_366_, v___x_368_);
v___x_370_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9_spec__14___redArg(v___x_367_, v_data_363_, v___x_369_);
return v___x_370_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8___redArg(lean_object* v_a_371_, lean_object* v_x_372_){
_start:
{
if (lean_obj_tag(v_x_372_) == 0)
{
uint8_t v___x_373_; 
v___x_373_ = 0;
return v___x_373_;
}
else
{
lean_object* v_key_374_; lean_object* v_tail_375_; uint8_t v___x_376_; 
v_key_374_ = lean_ctor_get(v_x_372_, 0);
v_tail_375_ = lean_ctor_get(v_x_372_, 2);
v___x_376_ = lean_name_eq(v_key_374_, v_a_371_);
if (v___x_376_ == 0)
{
v_x_372_ = v_tail_375_;
goto _start;
}
else
{
return v___x_376_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8___redArg___boxed(lean_object* v_a_378_, lean_object* v_x_379_){
_start:
{
uint8_t v_res_380_; lean_object* v_r_381_; 
v_res_380_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8___redArg(v_a_378_, v_x_379_);
lean_dec(v_x_379_);
lean_dec(v_a_378_);
v_r_381_ = lean_box(v_res_380_);
return v_r_381_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__10___redArg(lean_object* v_a_382_, lean_object* v_b_383_, lean_object* v_x_384_){
_start:
{
if (lean_obj_tag(v_x_384_) == 0)
{
lean_dec(v_b_383_);
lean_dec(v_a_382_);
return v_x_384_;
}
else
{
lean_object* v_key_385_; lean_object* v_value_386_; lean_object* v_tail_387_; lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_399_; 
v_key_385_ = lean_ctor_get(v_x_384_, 0);
v_value_386_ = lean_ctor_get(v_x_384_, 1);
v_tail_387_ = lean_ctor_get(v_x_384_, 2);
v_isSharedCheck_399_ = !lean_is_exclusive(v_x_384_);
if (v_isSharedCheck_399_ == 0)
{
v___x_389_ = v_x_384_;
v_isShared_390_ = v_isSharedCheck_399_;
goto v_resetjp_388_;
}
else
{
lean_inc(v_tail_387_);
lean_inc(v_value_386_);
lean_inc(v_key_385_);
lean_dec(v_x_384_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_399_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
uint8_t v___x_391_; 
v___x_391_ = lean_name_eq(v_key_385_, v_a_382_);
if (v___x_391_ == 0)
{
lean_object* v___x_392_; lean_object* v___x_394_; 
v___x_392_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__10___redArg(v_a_382_, v_b_383_, v_tail_387_);
if (v_isShared_390_ == 0)
{
lean_ctor_set(v___x_389_, 2, v___x_392_);
v___x_394_ = v___x_389_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v_key_385_);
lean_ctor_set(v_reuseFailAlloc_395_, 1, v_value_386_);
lean_ctor_set(v_reuseFailAlloc_395_, 2, v___x_392_);
v___x_394_ = v_reuseFailAlloc_395_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
return v___x_394_;
}
}
else
{
lean_object* v___x_397_; 
lean_dec(v_value_386_);
lean_dec(v_key_385_);
if (v_isShared_390_ == 0)
{
lean_ctor_set(v___x_389_, 1, v_b_383_);
lean_ctor_set(v___x_389_, 0, v_a_382_);
v___x_397_ = v___x_389_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v_a_382_);
lean_ctor_set(v_reuseFailAlloc_398_, 1, v_b_383_);
lean_ctor_set(v_reuseFailAlloc_398_, 2, v_tail_387_);
v___x_397_ = v_reuseFailAlloc_398_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
return v___x_397_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4___redArg(lean_object* v_m_400_, lean_object* v_a_401_, lean_object* v_b_402_){
_start:
{
lean_object* v_size_403_; lean_object* v_buckets_404_; lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_450_; 
v_size_403_ = lean_ctor_get(v_m_400_, 0);
v_buckets_404_ = lean_ctor_get(v_m_400_, 1);
v_isSharedCheck_450_ = !lean_is_exclusive(v_m_400_);
if (v_isSharedCheck_450_ == 0)
{
v___x_406_ = v_m_400_;
v_isShared_407_ = v_isSharedCheck_450_;
goto v_resetjp_405_;
}
else
{
lean_inc(v_buckets_404_);
lean_inc(v_size_403_);
lean_dec(v_m_400_);
v___x_406_ = lean_box(0);
v_isShared_407_ = v_isSharedCheck_450_;
goto v_resetjp_405_;
}
v_resetjp_405_:
{
lean_object* v___x_408_; uint64_t v___y_410_; 
v___x_408_ = lean_array_get_size(v_buckets_404_);
if (lean_obj_tag(v_a_401_) == 0)
{
uint64_t v___x_448_; 
v___x_448_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg___closed__0);
v___y_410_ = v___x_448_;
goto v___jp_409_;
}
else
{
uint64_t v_hash_449_; 
v_hash_449_ = lean_ctor_get_uint64(v_a_401_, sizeof(void*)*2);
v___y_410_ = v_hash_449_;
goto v___jp_409_;
}
v___jp_409_:
{
uint64_t v___x_411_; uint64_t v___x_412_; uint64_t v_fold_413_; uint64_t v___x_414_; uint64_t v___x_415_; uint64_t v___x_416_; size_t v___x_417_; size_t v___x_418_; size_t v___x_419_; size_t v___x_420_; size_t v___x_421_; lean_object* v_bkt_422_; uint8_t v___x_423_; 
v___x_411_ = 32ULL;
v___x_412_ = lean_uint64_shift_right(v___y_410_, v___x_411_);
v_fold_413_ = lean_uint64_xor(v___y_410_, v___x_412_);
v___x_414_ = 16ULL;
v___x_415_ = lean_uint64_shift_right(v_fold_413_, v___x_414_);
v___x_416_ = lean_uint64_xor(v_fold_413_, v___x_415_);
v___x_417_ = lean_uint64_to_usize(v___x_416_);
v___x_418_ = lean_usize_of_nat(v___x_408_);
v___x_419_ = ((size_t)1ULL);
v___x_420_ = lean_usize_sub(v___x_418_, v___x_419_);
v___x_421_ = lean_usize_land(v___x_417_, v___x_420_);
v_bkt_422_ = lean_array_uget_borrowed(v_buckets_404_, v___x_421_);
v___x_423_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8___redArg(v_a_401_, v_bkt_422_);
if (v___x_423_ == 0)
{
lean_object* v___x_424_; lean_object* v_size_x27_425_; lean_object* v___x_426_; lean_object* v_buckets_x27_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; uint8_t v___x_433_; 
v___x_424_ = lean_unsigned_to_nat(1u);
v_size_x27_425_ = lean_nat_add(v_size_403_, v___x_424_);
lean_dec(v_size_403_);
lean_inc(v_bkt_422_);
v___x_426_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_426_, 0, v_a_401_);
lean_ctor_set(v___x_426_, 1, v_b_402_);
lean_ctor_set(v___x_426_, 2, v_bkt_422_);
v_buckets_x27_427_ = lean_array_uset(v_buckets_404_, v___x_421_, v___x_426_);
v___x_428_ = lean_unsigned_to_nat(4u);
v___x_429_ = lean_nat_mul(v_size_x27_425_, v___x_428_);
v___x_430_ = lean_unsigned_to_nat(3u);
v___x_431_ = lean_nat_div(v___x_429_, v___x_430_);
lean_dec(v___x_429_);
v___x_432_ = lean_array_get_size(v_buckets_x27_427_);
v___x_433_ = lean_nat_dec_le(v___x_431_, v___x_432_);
lean_dec(v___x_431_);
if (v___x_433_ == 0)
{
lean_object* v_val_434_; lean_object* v___x_436_; 
v_val_434_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9___redArg(v_buckets_x27_427_);
if (v_isShared_407_ == 0)
{
lean_ctor_set(v___x_406_, 1, v_val_434_);
lean_ctor_set(v___x_406_, 0, v_size_x27_425_);
v___x_436_ = v___x_406_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v_size_x27_425_);
lean_ctor_set(v_reuseFailAlloc_437_, 1, v_val_434_);
v___x_436_ = v_reuseFailAlloc_437_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
return v___x_436_;
}
}
else
{
lean_object* v___x_439_; 
if (v_isShared_407_ == 0)
{
lean_ctor_set(v___x_406_, 1, v_buckets_x27_427_);
lean_ctor_set(v___x_406_, 0, v_size_x27_425_);
v___x_439_ = v___x_406_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v_size_x27_425_);
lean_ctor_set(v_reuseFailAlloc_440_, 1, v_buckets_x27_427_);
v___x_439_ = v_reuseFailAlloc_440_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
return v___x_439_;
}
}
}
else
{
lean_object* v___x_441_; lean_object* v_buckets_x27_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_446_; 
lean_inc(v_bkt_422_);
v___x_441_ = lean_box(0);
v_buckets_x27_442_ = lean_array_uset(v_buckets_404_, v___x_421_, v___x_441_);
v___x_443_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__10___redArg(v_a_401_, v_b_402_, v_bkt_422_);
v___x_444_ = lean_array_uset(v_buckets_x27_442_, v___x_421_, v___x_443_);
if (v_isShared_407_ == 0)
{
lean_ctor_set(v___x_406_, 1, v___x_444_);
v___x_446_ = v___x_406_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v_size_403_);
lean_ctor_set(v_reuseFailAlloc_447_, 1, v___x_444_);
v___x_446_ = v_reuseFailAlloc_447_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
return v___x_446_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1___redArg(lean_object* v_x_451_, lean_object* v_x_452_, lean_object* v_x_453_){
_start:
{
uint8_t v_stage_u2081_454_; 
v_stage_u2081_454_ = lean_ctor_get_uint8(v_x_451_, sizeof(void*)*2);
if (v_stage_u2081_454_ == 0)
{
lean_object* v_map_u2081_455_; lean_object* v_map_u2082_456_; lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_464_; 
v_map_u2081_455_ = lean_ctor_get(v_x_451_, 0);
v_map_u2082_456_ = lean_ctor_get(v_x_451_, 1);
v_isSharedCheck_464_ = !lean_is_exclusive(v_x_451_);
if (v_isSharedCheck_464_ == 0)
{
v___x_458_ = v_x_451_;
v_isShared_459_ = v_isSharedCheck_464_;
goto v_resetjp_457_;
}
else
{
lean_inc(v_map_u2082_456_);
lean_inc(v_map_u2081_455_);
lean_dec(v_x_451_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_464_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
lean_object* v___x_460_; lean_object* v___x_462_; 
v___x_460_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3___redArg(v_map_u2082_456_, v_x_452_, v_x_453_);
if (v_isShared_459_ == 0)
{
lean_ctor_set(v___x_458_, 1, v___x_460_);
v___x_462_ = v___x_458_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v_map_u2081_455_);
lean_ctor_set(v_reuseFailAlloc_463_, 1, v___x_460_);
lean_ctor_set_uint8(v_reuseFailAlloc_463_, sizeof(void*)*2, v_stage_u2081_454_);
v___x_462_ = v_reuseFailAlloc_463_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
return v___x_462_;
}
}
}
else
{
lean_object* v_map_u2081_465_; lean_object* v_map_u2082_466_; lean_object* v___x_468_; uint8_t v_isShared_469_; uint8_t v_isSharedCheck_474_; 
v_map_u2081_465_ = lean_ctor_get(v_x_451_, 0);
v_map_u2082_466_ = lean_ctor_get(v_x_451_, 1);
v_isSharedCheck_474_ = !lean_is_exclusive(v_x_451_);
if (v_isSharedCheck_474_ == 0)
{
v___x_468_ = v_x_451_;
v_isShared_469_ = v_isSharedCheck_474_;
goto v_resetjp_467_;
}
else
{
lean_inc(v_map_u2082_466_);
lean_inc(v_map_u2081_465_);
lean_dec(v_x_451_);
v___x_468_ = lean_box(0);
v_isShared_469_ = v_isSharedCheck_474_;
goto v_resetjp_467_;
}
v_resetjp_467_:
{
lean_object* v___x_470_; lean_object* v___x_472_; 
v___x_470_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4___redArg(v_map_u2081_465_, v_x_452_, v_x_453_);
if (v_isShared_469_ == 0)
{
lean_ctor_set(v___x_468_, 0, v___x_470_);
v___x_472_ = v___x_468_;
goto v_reusejp_471_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v___x_470_);
lean_ctor_set(v_reuseFailAlloc_473_, 1, v_map_u2082_466_);
lean_ctor_set_uint8(v_reuseFailAlloc_473_, sizeof(void*)*2, v_stage_u2081_454_);
v___x_472_ = v_reuseFailAlloc_473_;
goto v_reusejp_471_;
}
v_reusejp_471_:
{
return v___x_472_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3___redArg(lean_object* v_a_475_, lean_object* v_x_476_){
_start:
{
if (lean_obj_tag(v_x_476_) == 0)
{
lean_object* v___x_477_; 
v___x_477_ = lean_box(0);
return v___x_477_;
}
else
{
lean_object* v_key_478_; lean_object* v_value_479_; lean_object* v_tail_480_; uint8_t v___x_481_; 
v_key_478_ = lean_ctor_get(v_x_476_, 0);
v_value_479_ = lean_ctor_get(v_x_476_, 1);
v_tail_480_ = lean_ctor_get(v_x_476_, 2);
v___x_481_ = lean_name_eq(v_key_478_, v_a_475_);
if (v___x_481_ == 0)
{
v_x_476_ = v_tail_480_;
goto _start;
}
else
{
lean_object* v___x_483_; 
lean_inc(v_value_479_);
v___x_483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_483_, 0, v_value_479_);
return v___x_483_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_a_484_, lean_object* v_x_485_){
_start:
{
lean_object* v_res_486_; 
v_res_486_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3___redArg(v_a_484_, v_x_485_);
lean_dec(v_x_485_);
lean_dec(v_a_484_);
return v_res_486_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1___redArg(lean_object* v_m_487_, lean_object* v_a_488_){
_start:
{
lean_object* v_buckets_489_; lean_object* v___x_490_; uint64_t v___y_492_; 
v_buckets_489_ = lean_ctor_get(v_m_487_, 1);
v___x_490_ = lean_array_get_size(v_buckets_489_);
if (lean_obj_tag(v_a_488_) == 0)
{
uint64_t v___x_506_; 
v___x_506_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg___closed__0);
v___y_492_ = v___x_506_;
goto v___jp_491_;
}
else
{
uint64_t v_hash_507_; 
v_hash_507_ = lean_ctor_get_uint64(v_a_488_, sizeof(void*)*2);
v___y_492_ = v_hash_507_;
goto v___jp_491_;
}
v___jp_491_:
{
uint64_t v___x_493_; uint64_t v___x_494_; uint64_t v_fold_495_; uint64_t v___x_496_; uint64_t v___x_497_; uint64_t v___x_498_; size_t v___x_499_; size_t v___x_500_; size_t v___x_501_; size_t v___x_502_; size_t v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; 
v___x_493_ = 32ULL;
v___x_494_ = lean_uint64_shift_right(v___y_492_, v___x_493_);
v_fold_495_ = lean_uint64_xor(v___y_492_, v___x_494_);
v___x_496_ = 16ULL;
v___x_497_ = lean_uint64_shift_right(v_fold_495_, v___x_496_);
v___x_498_ = lean_uint64_xor(v_fold_495_, v___x_497_);
v___x_499_ = lean_uint64_to_usize(v___x_498_);
v___x_500_ = lean_usize_of_nat(v___x_490_);
v___x_501_ = ((size_t)1ULL);
v___x_502_ = lean_usize_sub(v___x_500_, v___x_501_);
v___x_503_ = lean_usize_land(v___x_499_, v___x_502_);
v___x_504_ = lean_array_uget_borrowed(v_buckets_489_, v___x_503_);
v___x_505_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3___redArg(v_a_488_, v___x_504_);
return v___x_505_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1___redArg___boxed(lean_object* v_m_508_, lean_object* v_a_509_){
_start:
{
lean_object* v_res_510_; 
v_res_510_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1___redArg(v_m_508_, v_a_509_);
lean_dec(v_a_509_);
lean_dec_ref(v_m_508_);
return v_res_510_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_keys_511_, lean_object* v_vals_512_, lean_object* v_i_513_, lean_object* v_k_514_){
_start:
{
lean_object* v___x_515_; uint8_t v___x_516_; 
v___x_515_ = lean_array_get_size(v_keys_511_);
v___x_516_ = lean_nat_dec_lt(v_i_513_, v___x_515_);
if (v___x_516_ == 0)
{
lean_object* v___x_517_; 
lean_dec(v_i_513_);
v___x_517_ = lean_box(0);
return v___x_517_;
}
else
{
lean_object* v_k_x27_518_; uint8_t v___x_519_; 
v_k_x27_518_ = lean_array_fget_borrowed(v_keys_511_, v_i_513_);
v___x_519_ = lean_name_eq(v_k_514_, v_k_x27_518_);
if (v___x_519_ == 0)
{
lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_520_ = lean_unsigned_to_nat(1u);
v___x_521_ = lean_nat_add(v_i_513_, v___x_520_);
lean_dec(v_i_513_);
v_i_513_ = v___x_521_;
goto _start;
}
else
{
lean_object* v___x_523_; lean_object* v___x_524_; 
v___x_523_ = lean_array_fget_borrowed(v_vals_512_, v_i_513_);
lean_dec(v_i_513_);
lean_inc(v___x_523_);
v___x_524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_524_, 0, v___x_523_);
return v___x_524_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_keys_525_, lean_object* v_vals_526_, lean_object* v_i_527_, lean_object* v_k_528_){
_start:
{
lean_object* v_res_529_; 
v_res_529_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4___redArg(v_keys_525_, v_vals_526_, v_i_527_, v_k_528_);
lean_dec(v_k_528_);
lean_dec_ref(v_vals_526_);
lean_dec_ref(v_keys_525_);
return v_res_529_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1___redArg(lean_object* v_x_530_, size_t v_x_531_, lean_object* v_x_532_){
_start:
{
if (lean_obj_tag(v_x_530_) == 0)
{
lean_object* v_es_533_; lean_object* v___x_534_; size_t v___x_535_; size_t v___x_536_; lean_object* v_j_537_; lean_object* v___x_538_; 
v_es_533_ = lean_ctor_get(v_x_530_, 0);
v___x_534_ = lean_box(2);
v___x_535_ = ((size_t)31ULL);
v___x_536_ = lean_usize_land(v_x_531_, v___x_535_);
v_j_537_ = lean_usize_to_nat(v___x_536_);
v___x_538_ = lean_array_get_borrowed(v___x_534_, v_es_533_, v_j_537_);
lean_dec(v_j_537_);
switch(lean_obj_tag(v___x_538_))
{
case 0:
{
lean_object* v_key_539_; lean_object* v_val_540_; uint8_t v___x_541_; 
v_key_539_ = lean_ctor_get(v___x_538_, 0);
v_val_540_ = lean_ctor_get(v___x_538_, 1);
v___x_541_ = lean_name_eq(v_x_532_, v_key_539_);
if (v___x_541_ == 0)
{
lean_object* v___x_542_; 
v___x_542_ = lean_box(0);
return v___x_542_;
}
else
{
lean_object* v___x_543_; 
lean_inc(v_val_540_);
v___x_543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_543_, 0, v_val_540_);
return v___x_543_;
}
}
case 1:
{
lean_object* v_node_544_; size_t v___x_545_; size_t v___x_546_; 
v_node_544_ = lean_ctor_get(v___x_538_, 0);
v___x_545_ = ((size_t)5ULL);
v___x_546_ = lean_usize_shift_right(v_x_531_, v___x_545_);
v_x_530_ = v_node_544_;
v_x_531_ = v___x_546_;
goto _start;
}
default: 
{
lean_object* v___x_548_; 
v___x_548_ = lean_box(0);
return v___x_548_;
}
}
}
else
{
lean_object* v_ks_549_; lean_object* v_vs_550_; lean_object* v___x_551_; lean_object* v___x_552_; 
v_ks_549_ = lean_ctor_get(v_x_530_, 0);
v_vs_550_ = lean_ctor_get(v_x_530_, 1);
v___x_551_ = lean_unsigned_to_nat(0u);
v___x_552_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4___redArg(v_ks_549_, v_vs_550_, v___x_551_, v_x_532_);
return v___x_552_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_553_, lean_object* v_x_554_, lean_object* v_x_555_){
_start:
{
size_t v_x_1614__boxed_556_; lean_object* v_res_557_; 
v_x_1614__boxed_556_ = lean_unbox_usize(v_x_554_);
lean_dec(v_x_554_);
v_res_557_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1___redArg(v_x_553_, v_x_1614__boxed_556_, v_x_555_);
lean_dec(v_x_555_);
lean_dec_ref(v_x_553_);
return v_res_557_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0___redArg(lean_object* v_x_558_, lean_object* v_x_559_){
_start:
{
uint64_t v___y_561_; 
if (lean_obj_tag(v_x_559_) == 0)
{
uint64_t v___x_564_; 
v___x_564_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg___closed__0);
v___y_561_ = v___x_564_;
goto v___jp_560_;
}
else
{
uint64_t v_hash_565_; 
v_hash_565_ = lean_ctor_get_uint64(v_x_559_, sizeof(void*)*2);
v___y_561_ = v_hash_565_;
goto v___jp_560_;
}
v___jp_560_:
{
size_t v___x_562_; lean_object* v___x_563_; 
v___x_562_ = lean_uint64_to_usize(v___y_561_);
v___x_563_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1___redArg(v_x_558_, v___x_562_, v_x_559_);
return v___x_563_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0___redArg___boxed(lean_object* v_x_566_, lean_object* v_x_567_){
_start:
{
lean_object* v_res_568_; 
v_res_568_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0___redArg(v_x_566_, v_x_567_);
lean_dec(v_x_567_);
lean_dec_ref(v_x_566_);
return v_res_568_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0___redArg(lean_object* v_x_569_, lean_object* v_x_570_){
_start:
{
uint8_t v_stage_u2081_571_; 
v_stage_u2081_571_ = lean_ctor_get_uint8(v_x_569_, sizeof(void*)*2);
if (v_stage_u2081_571_ == 0)
{
lean_object* v_map_u2081_572_; lean_object* v_map_u2082_573_; lean_object* v___x_574_; 
v_map_u2081_572_ = lean_ctor_get(v_x_569_, 0);
v_map_u2082_573_ = lean_ctor_get(v_x_569_, 1);
v___x_574_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0___redArg(v_map_u2082_573_, v_x_570_);
if (lean_obj_tag(v___x_574_) == 0)
{
lean_object* v___x_575_; 
v___x_575_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1___redArg(v_map_u2081_572_, v_x_570_);
return v___x_575_;
}
else
{
return v___x_574_;
}
}
else
{
lean_object* v_map_u2081_576_; lean_object* v___x_577_; 
v_map_u2081_576_ = lean_ctor_get(v_x_569_, 0);
v___x_577_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1___redArg(v_map_u2081_576_, v_x_570_);
return v___x_577_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0___redArg___boxed(lean_object* v_x_578_, lean_object* v_x_579_){
_start:
{
lean_object* v_res_580_; 
v_res_580_ = l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0___redArg(v_x_578_, v_x_579_);
lean_dec(v_x_579_);
lean_dec_ref(v_x_578_);
return v_res_580_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_addAliasEntry_spec__2(lean_object* v_a_581_, lean_object* v_x_582_){
_start:
{
if (lean_obj_tag(v_x_582_) == 0)
{
uint8_t v___x_583_; 
v___x_583_ = 0;
return v___x_583_;
}
else
{
lean_object* v_head_584_; lean_object* v_tail_585_; uint8_t v___x_586_; 
v_head_584_ = lean_ctor_get(v_x_582_, 0);
v_tail_585_ = lean_ctor_get(v_x_582_, 1);
v___x_586_ = lean_name_eq(v_a_581_, v_head_584_);
if (v___x_586_ == 0)
{
v_x_582_ = v_tail_585_;
goto _start;
}
else
{
return v___x_586_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_addAliasEntry_spec__2___boxed(lean_object* v_a_588_, lean_object* v_x_589_){
_start:
{
uint8_t v_res_590_; lean_object* v_r_591_; 
v_res_590_ = l_List_elem___at___00Lean_addAliasEntry_spec__2(v_a_588_, v_x_589_);
lean_dec(v_x_589_);
lean_dec(v_a_588_);
v_r_591_ = lean_box(v_res_590_);
return v_r_591_;
}
}
LEAN_EXPORT lean_object* l_Lean_addAliasEntry(lean_object* v_s_592_, lean_object* v_e_593_){
_start:
{
lean_object* v_fst_594_; lean_object* v_snd_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_611_; 
v_fst_594_ = lean_ctor_get(v_e_593_, 0);
v_snd_595_ = lean_ctor_get(v_e_593_, 1);
v_isSharedCheck_611_ = !lean_is_exclusive(v_e_593_);
if (v_isSharedCheck_611_ == 0)
{
v___x_597_ = v_e_593_;
v_isShared_598_ = v_isSharedCheck_611_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_snd_595_);
lean_inc(v_fst_594_);
lean_dec(v_e_593_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_611_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
lean_object* v___x_599_; 
v___x_599_ = l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0___redArg(v_s_592_, v_fst_594_);
if (lean_obj_tag(v___x_599_) == 0)
{
lean_object* v___x_600_; lean_object* v___x_602_; 
v___x_600_ = lean_box(0);
if (v_isShared_598_ == 0)
{
lean_ctor_set_tag(v___x_597_, 1);
lean_ctor_set(v___x_597_, 1, v___x_600_);
lean_ctor_set(v___x_597_, 0, v_snd_595_);
v___x_602_ = v___x_597_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v_snd_595_);
lean_ctor_set(v_reuseFailAlloc_604_, 1, v___x_600_);
v___x_602_ = v_reuseFailAlloc_604_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
lean_object* v___x_603_; 
v___x_603_ = l_Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1___redArg(v_s_592_, v_fst_594_, v___x_602_);
return v___x_603_;
}
}
else
{
lean_object* v_val_605_; uint8_t v___x_606_; 
v_val_605_ = lean_ctor_get(v___x_599_, 0);
lean_inc(v_val_605_);
lean_dec_ref_known(v___x_599_, 1);
v___x_606_ = l_List_elem___at___00Lean_addAliasEntry_spec__2(v_snd_595_, v_val_605_);
if (v___x_606_ == 0)
{
lean_object* v___x_608_; 
if (v_isShared_598_ == 0)
{
lean_ctor_set_tag(v___x_597_, 1);
lean_ctor_set(v___x_597_, 1, v_val_605_);
lean_ctor_set(v___x_597_, 0, v_snd_595_);
v___x_608_ = v___x_597_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v_snd_595_);
lean_ctor_set(v_reuseFailAlloc_610_, 1, v_val_605_);
v___x_608_ = v_reuseFailAlloc_610_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
lean_object* v___x_609_; 
v___x_609_ = l_Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1___redArg(v_s_592_, v_fst_594_, v___x_608_);
return v___x_609_;
}
}
else
{
lean_dec(v_val_605_);
lean_del_object(v___x_597_);
lean_dec(v_snd_595_);
lean_dec(v_fst_594_);
return v_s_592_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0(lean_object* v_00_u03b2_612_, lean_object* v_x_613_, lean_object* v_x_614_){
_start:
{
lean_object* v___x_615_; 
v___x_615_ = l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0___redArg(v_x_613_, v_x_614_);
return v___x_615_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0___boxed(lean_object* v_00_u03b2_616_, lean_object* v_x_617_, lean_object* v_x_618_){
_start:
{
lean_object* v_res_619_; 
v_res_619_ = l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0(v_00_u03b2_616_, v_x_617_, v_x_618_);
lean_dec(v_x_618_);
lean_dec_ref(v_x_617_);
return v_res_619_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1(lean_object* v_00_u03b2_620_, lean_object* v_x_621_, lean_object* v_x_622_, lean_object* v_x_623_){
_start:
{
lean_object* v___x_624_; 
v___x_624_ = l_Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1___redArg(v_x_621_, v_x_622_, v_x_623_);
return v___x_624_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0(lean_object* v_00_u03b2_625_, lean_object* v_x_626_, lean_object* v_x_627_){
_start:
{
lean_object* v___x_628_; 
v___x_628_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0___redArg(v_x_626_, v_x_627_);
return v___x_628_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0___boxed(lean_object* v_00_u03b2_629_, lean_object* v_x_630_, lean_object* v_x_631_){
_start:
{
lean_object* v_res_632_; 
v_res_632_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0(v_00_u03b2_629_, v_x_630_, v_x_631_);
lean_dec(v_x_631_);
lean_dec_ref(v_x_630_);
return v_res_632_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1(lean_object* v_00_u03b2_633_, lean_object* v_m_634_, lean_object* v_a_635_){
_start:
{
lean_object* v___x_636_; 
v___x_636_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1___redArg(v_m_634_, v_a_635_);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1___boxed(lean_object* v_00_u03b2_637_, lean_object* v_m_638_, lean_object* v_a_639_){
_start:
{
lean_object* v_res_640_; 
v_res_640_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1(v_00_u03b2_637_, v_m_638_, v_a_639_);
lean_dec(v_a_639_);
lean_dec_ref(v_m_638_);
return v_res_640_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3(lean_object* v_00_u03b2_641_, lean_object* v_x_642_, lean_object* v_x_643_, lean_object* v_x_644_){
_start:
{
lean_object* v___x_645_; 
v___x_645_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3___redArg(v_x_642_, v_x_643_, v_x_644_);
return v___x_645_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4(lean_object* v_00_u03b2_646_, lean_object* v_m_647_, lean_object* v_a_648_, lean_object* v_b_649_){
_start:
{
lean_object* v___x_650_; 
v___x_650_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4___redArg(v_m_647_, v_a_648_, v_b_649_);
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_651_, lean_object* v_x_652_, size_t v_x_653_, lean_object* v_x_654_){
_start:
{
lean_object* v___x_655_; 
v___x_655_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1___redArg(v_x_652_, v_x_653_, v_x_654_);
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_656_, lean_object* v_x_657_, lean_object* v_x_658_, lean_object* v_x_659_){
_start:
{
size_t v_x_1782__boxed_660_; lean_object* v_res_661_; 
v_x_1782__boxed_660_ = lean_unbox_usize(v_x_658_);
lean_dec(v_x_658_);
v_res_661_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1(v_00_u03b2_656_, v_x_657_, v_x_1782__boxed_660_, v_x_659_);
lean_dec(v_x_659_);
lean_dec_ref(v_x_657_);
return v_res_661_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_662_, lean_object* v_a_663_, lean_object* v_x_664_){
_start:
{
lean_object* v___x_665_; 
v___x_665_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3___redArg(v_a_663_, v_x_664_);
return v___x_665_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_666_, lean_object* v_a_667_, lean_object* v_x_668_){
_start:
{
lean_object* v_res_669_; 
v_res_669_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3(v_00_u03b2_666_, v_a_667_, v_x_668_);
lean_dec(v_x_668_);
lean_dec(v_a_667_);
return v_res_669_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_670_, lean_object* v_x_671_, size_t v_x_672_, size_t v_x_673_, lean_object* v_x_674_, lean_object* v_x_675_){
_start:
{
lean_object* v___x_676_; 
v___x_676_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg(v_x_671_, v_x_672_, v_x_673_, v_x_674_, v_x_675_);
return v___x_676_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___boxed(lean_object* v_00_u03b2_677_, lean_object* v_x_678_, lean_object* v_x_679_, lean_object* v_x_680_, lean_object* v_x_681_, lean_object* v_x_682_){
_start:
{
size_t v_x_1798__boxed_683_; size_t v_x_1799__boxed_684_; lean_object* v_res_685_; 
v_x_1798__boxed_683_ = lean_unbox_usize(v_x_679_);
lean_dec(v_x_679_);
v_x_1799__boxed_684_ = lean_unbox_usize(v_x_680_);
lean_dec(v_x_680_);
v_res_685_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6(v_00_u03b2_677_, v_x_678_, v_x_1798__boxed_683_, v_x_1799__boxed_684_, v_x_681_, v_x_682_);
return v_res_685_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8(lean_object* v_00_u03b2_686_, lean_object* v_a_687_, lean_object* v_x_688_){
_start:
{
uint8_t v___x_689_; 
v___x_689_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8___redArg(v_a_687_, v_x_688_);
return v___x_689_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8___boxed(lean_object* v_00_u03b2_690_, lean_object* v_a_691_, lean_object* v_x_692_){
_start:
{
uint8_t v_res_693_; lean_object* v_r_694_; 
v_res_693_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8(v_00_u03b2_690_, v_a_691_, v_x_692_);
lean_dec(v_x_692_);
lean_dec(v_a_691_);
v_r_694_ = lean_box(v_res_693_);
return v_r_694_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9(lean_object* v_00_u03b2_695_, lean_object* v_data_696_){
_start:
{
lean_object* v___x_697_; 
v___x_697_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9___redArg(v_data_696_);
return v___x_697_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__10(lean_object* v_00_u03b2_698_, lean_object* v_a_699_, lean_object* v_b_700_, lean_object* v_x_701_){
_start:
{
lean_object* v___x_702_; 
v___x_702_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__10___redArg(v_a_699_, v_b_700_, v_x_701_);
return v___x_702_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_703_, lean_object* v_keys_704_, lean_object* v_vals_705_, lean_object* v_heq_706_, lean_object* v_i_707_, lean_object* v_k_708_){
_start:
{
lean_object* v___x_709_; 
v___x_709_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4___redArg(v_keys_704_, v_vals_705_, v_i_707_, v_k_708_);
return v___x_709_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b2_710_, lean_object* v_keys_711_, lean_object* v_vals_712_, lean_object* v_heq_713_, lean_object* v_i_714_, lean_object* v_k_715_){
_start:
{
lean_object* v_res_716_; 
v_res_716_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4(v_00_u03b2_710_, v_keys_711_, v_vals_712_, v_heq_713_, v_i_714_, v_k_715_);
lean_dec(v_k_715_);
lean_dec_ref(v_vals_712_);
lean_dec_ref(v_keys_711_);
return v_res_716_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__9(lean_object* v_00_u03b2_717_, lean_object* v_n_718_, lean_object* v_k_719_, lean_object* v_v_720_){
_start:
{
lean_object* v___x_721_; 
v___x_721_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__9___redArg(v_n_718_, v_k_719_, v_v_720_);
return v___x_721_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10(lean_object* v_00_u03b2_722_, size_t v_depth_723_, lean_object* v_keys_724_, lean_object* v_vals_725_, lean_object* v_heq_726_, lean_object* v_i_727_, lean_object* v_entries_728_){
_start:
{
lean_object* v___x_729_; 
v___x_729_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg(v_depth_723_, v_keys_724_, v_vals_725_, v_i_727_, v_entries_728_);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___boxed(lean_object* v_00_u03b2_730_, lean_object* v_depth_731_, lean_object* v_keys_732_, lean_object* v_vals_733_, lean_object* v_heq_734_, lean_object* v_i_735_, lean_object* v_entries_736_){
_start:
{
size_t v_depth_boxed_737_; lean_object* v_res_738_; 
v_depth_boxed_737_ = lean_unbox_usize(v_depth_731_);
lean_dec(v_depth_731_);
v_res_738_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10(v_00_u03b2_730_, v_depth_boxed_737_, v_keys_732_, v_vals_733_, v_heq_734_, v_i_735_, v_entries_736_);
lean_dec_ref(v_vals_733_);
lean_dec_ref(v_keys_732_);
return v_res_738_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9_spec__14(lean_object* v_00_u03b2_739_, lean_object* v_i_740_, lean_object* v_source_741_, lean_object* v_target_742_){
_start:
{
lean_object* v___x_743_; 
v___x_743_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9_spec__14___redArg(v_i_740_, v_source_741_, v_target_742_);
return v___x_743_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__9_spec__11(lean_object* v_00_u03b2_744_, lean_object* v_x_745_, lean_object* v_x_746_, lean_object* v_x_747_, lean_object* v_x_748_){
_start:
{
lean_object* v___x_749_; 
v___x_749_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__9_spec__11___redArg(v_x_745_, v_x_746_, v_x_747_, v_x_748_);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9_spec__14_spec__16(lean_object* v_00_u03b2_750_, lean_object* v_x_751_, lean_object* v_x_752_){
_start:
{
lean_object* v___x_753_; 
v___x_753_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9_spec__14_spec__16___redArg(v_x_751_, v_x_752_);
return v___x_753_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__1___redArg(lean_object* v_m_754_){
_start:
{
uint8_t v_stage_u2081_755_; 
v_stage_u2081_755_ = lean_ctor_get_uint8(v_m_754_, sizeof(void*)*2);
if (v_stage_u2081_755_ == 0)
{
return v_m_754_;
}
else
{
lean_object* v_map_u2081_756_; lean_object* v_map_u2082_757_; lean_object* v___x_759_; uint8_t v_isShared_760_; uint8_t v_isSharedCheck_765_; 
v_map_u2081_756_ = lean_ctor_get(v_m_754_, 0);
v_map_u2082_757_ = lean_ctor_get(v_m_754_, 1);
v_isSharedCheck_765_ = !lean_is_exclusive(v_m_754_);
if (v_isSharedCheck_765_ == 0)
{
v___x_759_ = v_m_754_;
v_isShared_760_ = v_isSharedCheck_765_;
goto v_resetjp_758_;
}
else
{
lean_inc(v_map_u2082_757_);
lean_inc(v_map_u2081_756_);
lean_dec(v_m_754_);
v___x_759_ = lean_box(0);
v_isShared_760_ = v_isSharedCheck_765_;
goto v_resetjp_758_;
}
v_resetjp_758_:
{
uint8_t v___x_761_; lean_object* v___x_763_; 
v___x_761_ = 0;
if (v_isShared_760_ == 0)
{
v___x_763_ = v___x_759_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v_map_u2081_756_);
lean_ctor_set(v_reuseFailAlloc_764_, 1, v_map_u2082_757_);
v___x_763_ = v_reuseFailAlloc_764_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
lean_ctor_set_uint8(v___x_763_, sizeof(void*)*2, v___x_761_);
return v___x_763_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__1(lean_object* v_00_u03b2_766_, lean_object* v_m_767_){
_start:
{
lean_object* v___x_768_; 
v___x_768_ = l_Lean_SMap_switch___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__1___redArg(v_m_767_);
return v___x_768_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn___lam__0_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(lean_object* v_es_769_){
_start:
{
lean_object* v___x_770_; 
v___x_770_ = lean_array_mk(v_es_769_);
return v___x_770_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_as_771_, size_t v_i_772_, size_t v_stop_773_, lean_object* v_b_774_){
_start:
{
uint8_t v___x_775_; 
v___x_775_ = lean_usize_dec_eq(v_i_772_, v_stop_773_);
if (v___x_775_ == 0)
{
lean_object* v___x_776_; lean_object* v___x_777_; size_t v___x_778_; size_t v___x_779_; 
v___x_776_ = lean_array_uget_borrowed(v_as_771_, v_i_772_);
lean_inc(v___x_776_);
v___x_777_ = l_Lean_addAliasEntry(v_b_774_, v___x_776_);
v___x_778_ = ((size_t)1ULL);
v___x_779_ = lean_usize_add(v_i_772_, v___x_778_);
v_i_772_ = v___x_779_;
v_b_774_ = v___x_777_;
goto _start;
}
else
{
return v_b_774_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_as_781_, lean_object* v_i_782_, lean_object* v_stop_783_, lean_object* v_b_784_){
_start:
{
size_t v_i_boxed_785_; size_t v_stop_boxed_786_; lean_object* v_res_787_; 
v_i_boxed_785_ = lean_unbox_usize(v_i_782_);
lean_dec(v_i_782_);
v_stop_boxed_786_ = lean_unbox_usize(v_stop_783_);
lean_dec(v_stop_783_);
v_res_787_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__0(v_as_781_, v_i_boxed_785_, v_stop_boxed_786_, v_b_784_);
lean_dec_ref(v_as_781_);
return v_res_787_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_as_788_, size_t v_i_789_, size_t v_stop_790_, lean_object* v_b_791_){
_start:
{
lean_object* v___y_793_; uint8_t v___x_797_; 
v___x_797_ = lean_usize_dec_eq(v_i_789_, v_stop_790_);
if (v___x_797_ == 0)
{
lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; uint8_t v___x_801_; 
v___x_798_ = lean_array_uget_borrowed(v_as_788_, v_i_789_);
v___x_799_ = lean_unsigned_to_nat(0u);
v___x_800_ = lean_array_get_size(v___x_798_);
v___x_801_ = lean_nat_dec_lt(v___x_799_, v___x_800_);
if (v___x_801_ == 0)
{
v___y_793_ = v_b_791_;
goto v___jp_792_;
}
else
{
uint8_t v___x_802_; 
v___x_802_ = lean_nat_dec_le(v___x_800_, v___x_800_);
if (v___x_802_ == 0)
{
if (v___x_801_ == 0)
{
v___y_793_ = v_b_791_;
goto v___jp_792_;
}
else
{
size_t v___x_803_; size_t v___x_804_; lean_object* v___x_805_; 
v___x_803_ = ((size_t)0ULL);
v___x_804_ = lean_usize_of_nat(v___x_800_);
v___x_805_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__0(v___x_798_, v___x_803_, v___x_804_, v_b_791_);
v___y_793_ = v___x_805_;
goto v___jp_792_;
}
}
else
{
size_t v___x_806_; size_t v___x_807_; lean_object* v___x_808_; 
v___x_806_ = ((size_t)0ULL);
v___x_807_ = lean_usize_of_nat(v___x_800_);
v___x_808_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__0(v___x_798_, v___x_806_, v___x_807_, v_b_791_);
v___y_793_ = v___x_808_;
goto v___jp_792_;
}
}
}
else
{
return v_b_791_;
}
v___jp_792_:
{
size_t v___x_794_; size_t v___x_795_; 
v___x_794_ = ((size_t)1ULL);
v___x_795_ = lean_usize_add(v_i_789_, v___x_794_);
v_i_789_ = v___x_795_;
v_b_791_ = v___y_793_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object* v_as_809_, lean_object* v_i_810_, lean_object* v_stop_811_, lean_object* v_b_812_){
_start:
{
size_t v_i_boxed_813_; size_t v_stop_boxed_814_; lean_object* v_res_815_; 
v_i_boxed_813_ = lean_unbox_usize(v_i_810_);
lean_dec(v_i_810_);
v_stop_boxed_814_ = lean_unbox_usize(v_stop_811_);
lean_dec(v_stop_811_);
v_res_815_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__1(v_as_809_, v_i_boxed_813_, v_stop_boxed_814_, v_b_812_);
lean_dec_ref(v_as_809_);
return v_res_815_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0(lean_object* v_initState_816_, lean_object* v_as_817_){
_start:
{
lean_object* v___x_818_; lean_object* v___x_819_; uint8_t v___x_820_; 
v___x_818_ = lean_unsigned_to_nat(0u);
v___x_819_ = lean_array_get_size(v_as_817_);
v___x_820_ = lean_nat_dec_lt(v___x_818_, v___x_819_);
if (v___x_820_ == 0)
{
return v_initState_816_;
}
else
{
uint8_t v___x_821_; 
v___x_821_ = lean_nat_dec_le(v___x_819_, v___x_819_);
if (v___x_821_ == 0)
{
if (v___x_820_ == 0)
{
return v_initState_816_;
}
else
{
size_t v___x_822_; size_t v___x_823_; lean_object* v___x_824_; 
v___x_822_ = ((size_t)0ULL);
v___x_823_ = lean_usize_of_nat(v___x_819_);
v___x_824_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__1(v_as_817_, v___x_822_, v___x_823_, v_initState_816_);
return v___x_824_;
}
}
else
{
size_t v___x_825_; size_t v___x_826_; lean_object* v___x_827_; 
v___x_825_ = ((size_t)0ULL);
v___x_826_ = lean_usize_of_nat(v___x_819_);
v___x_827_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__1(v_as_817_, v___x_825_, v___x_826_, v_initState_816_);
return v___x_827_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0___boxed(lean_object* v_initState_828_, lean_object* v_as_829_){
_start:
{
lean_object* v_res_830_; 
v_res_830_ = l_Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0(v_initState_828_, v_as_829_);
lean_dec_ref(v_as_829_);
return v_res_830_;
}
}
static lean_object* _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; 
v___x_831_ = lean_box(0);
v___x_832_ = lean_unsigned_to_nat(16u);
v___x_833_ = lean_mk_array(v___x_832_, v___x_831_);
return v___x_833_;
}
}
static lean_object* _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; 
v___x_834_ = lean_obj_once(&l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_, &l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__once, _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_);
v___x_835_ = lean_unsigned_to_nat(0u);
v___x_836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_836_, 0, v___x_835_);
lean_ctor_set(v___x_836_, 1, v___x_834_);
return v___x_836_;
}
}
static lean_object* _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_837_; 
v___x_837_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_837_;
}
}
static lean_object* _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_838_; lean_object* v___x_839_; 
v___x_838_ = lean_obj_once(&l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_, &l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__once, _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_);
v___x_839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_839_, 0, v___x_838_);
return v___x_839_;
}
}
static lean_object* _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__4_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_840_; lean_object* v___x_841_; uint8_t v___x_842_; lean_object* v___x_843_; 
v___x_840_ = lean_obj_once(&l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_, &l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__once, _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_);
v___x_841_ = lean_obj_once(&l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_, &l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__once, _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_);
v___x_842_ = 1;
v___x_843_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_843_, 0, v___x_841_);
lean_ctor_set(v___x_843_, 1, v___x_840_);
lean_ctor_set_uint8(v___x_843_, sizeof(void*)*2, v___x_842_);
return v___x_843_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn___lam__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(lean_object* v_es_844_){
_start:
{
lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; 
v___x_845_ = lean_obj_once(&l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__4_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_, &l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__4_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__once, _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__4_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_);
v___x_846_ = l_Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0(v___x_845_, v_es_844_);
v___x_847_ = l_Lean_SMap_switch___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__1___redArg(v___x_846_);
return v___x_847_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn___lam__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2____boxed(lean_object* v_es_848_){
_start:
{
lean_object* v_res_849_; 
v_res_849_ = l___private_Lean_ResolveName_0__Lean_initFn___lam__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(v_es_848_);
lean_dec_ref(v_es_848_);
return v_res_849_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_866_; lean_object* v___x_867_; 
v___x_866_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_initFn___closed__6_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_));
v___x_867_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_866_);
return v___x_867_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2____boxed(lean_object* v_a_868_){
_start:
{
lean_object* v_res_869_; 
v_res_869_ = l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_();
return v_res_869_;
}
}
LEAN_EXPORT lean_object* lean_add_alias(lean_object* v_env_870_, lean_object* v_a_871_, lean_object* v_e_872_){
_start:
{
lean_object* v___x_873_; lean_object* v_toEnvExtension_874_; lean_object* v_asyncMode_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; 
v___x_873_ = l_Lean_aliasExtension;
v_toEnvExtension_874_ = lean_ctor_get(v___x_873_, 0);
v_asyncMode_875_ = lean_ctor_get(v_toEnvExtension_874_, 2);
v___x_876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_876_, 0, v_a_871_);
lean_ctor_set(v___x_876_, 1, v_e_872_);
v___x_877_ = lean_box(0);
v___x_878_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_873_, v_env_870_, v___x_876_, v_asyncMode_875_, v___x_877_);
return v___x_878_;
}
}
static lean_object* _init_l_Lean_getAliasState___closed__2(void){
_start:
{
lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; 
v___x_881_ = ((lean_object*)(l_Lean_getAliasState___closed__1));
v___x_882_ = ((lean_object*)(l_Lean_getAliasState___closed__0));
v___x_883_ = l_Lean_SMap_instInhabited(lean_box(0), lean_box(0), v___x_882_, v___x_881_);
return v___x_883_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAliasState(lean_object* v_env_884_){
_start:
{
lean_object* v___x_885_; lean_object* v_toEnvExtension_886_; lean_object* v_asyncMode_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; 
v___x_885_ = l_Lean_aliasExtension;
v_toEnvExtension_886_ = lean_ctor_get(v___x_885_, 0);
v_asyncMode_887_ = lean_ctor_get(v_toEnvExtension_886_, 2);
v___x_888_ = lean_obj_once(&l_Lean_getAliasState___closed__2, &l_Lean_getAliasState___closed__2_once, _init_l_Lean_getAliasState___closed__2);
v___x_889_ = lean_box(0);
v___x_890_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_888_, v___x_885_, v_env_884_, v_asyncMode_887_, v___x_889_);
return v___x_890_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_getAliases_spec__0(lean_object* v_env_891_, uint8_t v_skipProtected_892_, lean_object* v_a_893_, lean_object* v_a_894_){
_start:
{
if (lean_obj_tag(v_a_893_) == 0)
{
lean_object* v___x_895_; 
lean_dec_ref(v_env_891_);
v___x_895_ = l_List_reverse___redArg(v_a_894_);
return v___x_895_;
}
else
{
lean_object* v_head_896_; lean_object* v_tail_897_; lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_908_; 
v_head_896_ = lean_ctor_get(v_a_893_, 0);
v_tail_897_ = lean_ctor_get(v_a_893_, 1);
v_isSharedCheck_908_ = !lean_is_exclusive(v_a_893_);
if (v_isSharedCheck_908_ == 0)
{
v___x_899_ = v_a_893_;
v_isShared_900_ = v_isSharedCheck_908_;
goto v_resetjp_898_;
}
else
{
lean_inc(v_tail_897_);
lean_inc(v_head_896_);
lean_dec(v_a_893_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_908_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
uint8_t v___x_901_; 
lean_inc(v_head_896_);
lean_inc_ref(v_env_891_);
v___x_901_ = l_Lean_isProtected(v_env_891_, v_head_896_);
if (v___x_901_ == 0)
{
if (v_skipProtected_892_ == 0)
{
lean_del_object(v___x_899_);
lean_dec(v_head_896_);
v_a_893_ = v_tail_897_;
goto _start;
}
else
{
lean_object* v___x_904_; 
if (v_isShared_900_ == 0)
{
lean_ctor_set(v___x_899_, 1, v_a_894_);
v___x_904_ = v___x_899_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v_head_896_);
lean_ctor_set(v_reuseFailAlloc_906_, 1, v_a_894_);
v___x_904_ = v_reuseFailAlloc_906_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
v_a_893_ = v_tail_897_;
v_a_894_ = v___x_904_;
goto _start;
}
}
}
else
{
lean_del_object(v___x_899_);
lean_dec(v_head_896_);
v_a_893_ = v_tail_897_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_getAliases_spec__0___boxed(lean_object* v_env_909_, lean_object* v_skipProtected_910_, lean_object* v_a_911_, lean_object* v_a_912_){
_start:
{
uint8_t v_skipProtected_boxed_913_; lean_object* v_res_914_; 
v_skipProtected_boxed_913_ = lean_unbox(v_skipProtected_910_);
v_res_914_ = l_List_filterTR_loop___at___00Lean_getAliases_spec__0(v_env_909_, v_skipProtected_boxed_913_, v_a_911_, v_a_912_);
return v_res_914_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAliases(lean_object* v_env_915_, lean_object* v_a_916_, uint8_t v_skipProtected_917_){
_start:
{
lean_object* v___x_918_; lean_object* v_toEnvExtension_919_; lean_object* v_asyncMode_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; 
v___x_918_ = l_Lean_aliasExtension;
v_toEnvExtension_919_ = lean_ctor_get(v___x_918_, 0);
v_asyncMode_920_ = lean_ctor_get(v_toEnvExtension_919_, 2);
v___x_921_ = lean_obj_once(&l_Lean_getAliasState___closed__2, &l_Lean_getAliasState___closed__2_once, _init_l_Lean_getAliasState___closed__2);
v___x_922_ = lean_box(0);
lean_inc_ref(v_env_915_);
v___x_923_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_921_, v___x_918_, v_env_915_, v_asyncMode_920_, v___x_922_);
v___x_924_ = l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0___redArg(v___x_923_, v_a_916_);
lean_dec(v___x_923_);
if (lean_obj_tag(v___x_924_) == 0)
{
lean_object* v___x_925_; 
lean_dec_ref(v_env_915_);
v___x_925_ = lean_box(0);
return v___x_925_;
}
else
{
if (v_skipProtected_917_ == 0)
{
lean_object* v_val_926_; 
lean_dec_ref(v_env_915_);
v_val_926_ = lean_ctor_get(v___x_924_, 0);
lean_inc(v_val_926_);
lean_dec_ref_known(v___x_924_, 1);
return v_val_926_;
}
else
{
lean_object* v_val_927_; lean_object* v___x_928_; lean_object* v___x_929_; 
v_val_927_ = lean_ctor_get(v___x_924_, 0);
lean_inc(v_val_927_);
lean_dec_ref_known(v___x_924_, 1);
v___x_928_ = lean_box(0);
v___x_929_ = l_List_filterTR_loop___at___00Lean_getAliases_spec__0(v_env_915_, v_skipProtected_917_, v_val_927_, v___x_928_);
return v___x_929_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getAliases___boxed(lean_object* v_env_930_, lean_object* v_a_931_, lean_object* v_skipProtected_932_){
_start:
{
uint8_t v_skipProtected_boxed_933_; lean_object* v_res_934_; 
v_skipProtected_boxed_933_ = lean_unbox(v_skipProtected_932_);
v_res_934_ = l_Lean_getAliases(v_env_930_, v_a_931_, v_skipProtected_boxed_933_);
lean_dec(v_a_931_);
return v_res_934_;
}
}
LEAN_EXPORT lean_object* l_Lean_getRevAliases___lam__0(lean_object* v_e_935_, lean_object* v_as_936_, lean_object* v_a_937_, lean_object* v_es_938_){
_start:
{
uint8_t v___x_939_; 
v___x_939_ = l_List_elem___at___00Lean_addAliasEntry_spec__2(v_e_935_, v_es_938_);
if (v___x_939_ == 0)
{
lean_dec(v_a_937_);
return v_as_936_;
}
else
{
lean_object* v___x_940_; 
v___x_940_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_940_, 0, v_a_937_);
lean_ctor_set(v___x_940_, 1, v_as_936_);
return v___x_940_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getRevAliases___lam__0___boxed(lean_object* v_e_941_, lean_object* v_as_942_, lean_object* v_a_943_, lean_object* v_es_944_){
_start:
{
lean_object* v_res_945_; 
v_res_945_ = l_Lean_getRevAliases___lam__0(v_e_941_, v_as_942_, v_a_943_, v_es_944_);
lean_dec(v_es_944_);
lean_dec(v_e_941_);
return v_res_945_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6___redArg(lean_object* v_f_946_, lean_object* v_keys_947_, lean_object* v_vals_948_, lean_object* v_i_949_, lean_object* v_acc_950_){
_start:
{
lean_object* v___x_951_; uint8_t v___x_952_; 
v___x_951_ = lean_array_get_size(v_keys_947_);
v___x_952_ = lean_nat_dec_lt(v_i_949_, v___x_951_);
if (v___x_952_ == 0)
{
lean_dec(v_i_949_);
lean_dec(v_f_946_);
return v_acc_950_;
}
else
{
lean_object* v_k_953_; lean_object* v_v_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; 
v_k_953_ = lean_array_fget_borrowed(v_keys_947_, v_i_949_);
v_v_954_ = lean_array_fget_borrowed(v_vals_948_, v_i_949_);
lean_inc(v_f_946_);
lean_inc(v_v_954_);
lean_inc(v_k_953_);
v___x_955_ = lean_apply_3(v_f_946_, v_acc_950_, v_k_953_, v_v_954_);
v___x_956_ = lean_unsigned_to_nat(1u);
v___x_957_ = lean_nat_add(v_i_949_, v___x_956_);
lean_dec(v_i_949_);
v_i_949_ = v___x_957_;
v_acc_950_ = v___x_955_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_f_959_, lean_object* v_keys_960_, lean_object* v_vals_961_, lean_object* v_i_962_, lean_object* v_acc_963_){
_start:
{
lean_object* v_res_964_; 
v_res_964_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6___redArg(v_f_959_, v_keys_960_, v_vals_961_, v_i_962_, v_acc_963_);
lean_dec_ref(v_vals_961_);
lean_dec_ref(v_keys_960_);
return v_res_964_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_f_965_, lean_object* v_x_966_, lean_object* v_x_967_){
_start:
{
if (lean_obj_tag(v_x_966_) == 0)
{
lean_object* v_es_968_; lean_object* v___x_969_; lean_object* v___x_970_; uint8_t v___x_971_; 
v_es_968_ = lean_ctor_get(v_x_966_, 0);
v___x_969_ = lean_unsigned_to_nat(0u);
v___x_970_ = lean_array_get_size(v_es_968_);
v___x_971_ = lean_nat_dec_lt(v___x_969_, v___x_970_);
if (v___x_971_ == 0)
{
lean_dec(v_f_965_);
return v_x_967_;
}
else
{
uint8_t v___x_972_; 
v___x_972_ = lean_nat_dec_le(v___x_970_, v___x_970_);
if (v___x_972_ == 0)
{
if (v___x_971_ == 0)
{
lean_dec(v_f_965_);
return v_x_967_;
}
else
{
size_t v___x_973_; size_t v___x_974_; lean_object* v___x_975_; 
v___x_973_ = ((size_t)0ULL);
v___x_974_ = lean_usize_of_nat(v___x_970_);
v___x_975_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(v_f_965_, v_es_968_, v___x_973_, v___x_974_, v_x_967_);
return v___x_975_;
}
}
else
{
size_t v___x_976_; size_t v___x_977_; lean_object* v___x_978_; 
v___x_976_ = ((size_t)0ULL);
v___x_977_ = lean_usize_of_nat(v___x_970_);
v___x_978_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(v_f_965_, v_es_968_, v___x_976_, v___x_977_, v_x_967_);
return v___x_978_;
}
}
}
else
{
lean_object* v_ks_979_; lean_object* v_vs_980_; lean_object* v___x_981_; lean_object* v___x_982_; 
v_ks_979_ = lean_ctor_get(v_x_966_, 0);
v_vs_980_ = lean_ctor_get(v_x_966_, 1);
v___x_981_ = lean_unsigned_to_nat(0u);
v___x_982_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6___redArg(v_f_965_, v_ks_979_, v_vs_980_, v___x_981_, v_x_967_);
return v___x_982_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(lean_object* v_f_983_, lean_object* v_as_984_, size_t v_i_985_, size_t v_stop_986_, lean_object* v_b_987_){
_start:
{
lean_object* v___y_989_; uint8_t v___x_993_; 
v___x_993_ = lean_usize_dec_eq(v_i_985_, v_stop_986_);
if (v___x_993_ == 0)
{
lean_object* v___x_994_; 
v___x_994_ = lean_array_uget_borrowed(v_as_984_, v_i_985_);
switch(lean_obj_tag(v___x_994_))
{
case 0:
{
lean_object* v_key_995_; lean_object* v_val_996_; lean_object* v___x_997_; 
v_key_995_ = lean_ctor_get(v___x_994_, 0);
v_val_996_ = lean_ctor_get(v___x_994_, 1);
lean_inc(v_f_983_);
lean_inc(v_val_996_);
lean_inc(v_key_995_);
v___x_997_ = lean_apply_3(v_f_983_, v_b_987_, v_key_995_, v_val_996_);
v___y_989_ = v___x_997_;
goto v___jp_988_;
}
case 1:
{
lean_object* v_node_998_; lean_object* v___x_999_; 
v_node_998_ = lean_ctor_get(v___x_994_, 0);
lean_inc(v_f_983_);
v___x_999_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg(v_f_983_, v_node_998_, v_b_987_);
v___y_989_ = v___x_999_;
goto v___jp_988_;
}
default: 
{
v___y_989_ = v_b_987_;
goto v___jp_988_;
}
}
}
else
{
lean_dec(v_f_983_);
return v_b_987_;
}
v___jp_988_:
{
size_t v___x_990_; size_t v___x_991_; 
v___x_990_ = ((size_t)1ULL);
v___x_991_ = lean_usize_add(v_i_985_, v___x_990_);
v_i_985_ = v___x_991_;
v_b_987_ = v___y_989_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v_f_1000_, lean_object* v_as_1001_, lean_object* v_i_1002_, lean_object* v_stop_1003_, lean_object* v_b_1004_){
_start:
{
size_t v_i_boxed_1005_; size_t v_stop_boxed_1006_; lean_object* v_res_1007_; 
v_i_boxed_1005_ = lean_unbox_usize(v_i_1002_);
lean_dec(v_i_1002_);
v_stop_boxed_1006_ = lean_unbox_usize(v_stop_1003_);
lean_dec(v_stop_1003_);
v_res_1007_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(v_f_1000_, v_as_1001_, v_i_boxed_1005_, v_stop_boxed_1006_, v_b_1004_);
lean_dec_ref(v_as_1001_);
return v_res_1007_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_f_1008_, lean_object* v_x_1009_, lean_object* v_x_1010_){
_start:
{
lean_object* v_res_1011_; 
v_res_1011_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg(v_f_1008_, v_x_1009_, v_x_1010_);
lean_dec_ref(v_x_1009_);
return v_res_1011_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg___lam__0(lean_object* v_f_1012_, lean_object* v_x1_1013_, lean_object* v_x2_1014_, lean_object* v_x3_1015_){
_start:
{
lean_object* v___x_1016_; 
v___x_1016_ = lean_apply_3(v_f_1012_, v_x1_1013_, v_x2_1014_, v_x3_1015_);
return v___x_1016_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg(lean_object* v_map_1017_, lean_object* v_f_1018_, lean_object* v_init_1019_){
_start:
{
lean_object* v___f_1020_; lean_object* v___x_1021_; 
v___f_1020_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1020_, 0, v_f_1018_);
v___x_1021_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg(v___f_1020_, v_map_1017_, v_init_1019_);
return v___x_1021_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg___boxed(lean_object* v_map_1022_, lean_object* v_f_1023_, lean_object* v_init_1024_){
_start:
{
lean_object* v_res_1025_; 
v_res_1025_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg(v_map_1022_, v_f_1023_, v_init_1024_);
lean_dec_ref(v_map_1022_);
return v_res_1025_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__0___redArg(lean_object* v_f_1026_, lean_object* v_x_1027_, lean_object* v_x_1028_){
_start:
{
if (lean_obj_tag(v_x_1028_) == 0)
{
lean_dec(v_f_1026_);
return v_x_1027_;
}
else
{
lean_object* v_key_1029_; lean_object* v_value_1030_; lean_object* v_tail_1031_; lean_object* v___x_1032_; 
v_key_1029_ = lean_ctor_get(v_x_1028_, 0);
lean_inc(v_key_1029_);
v_value_1030_ = lean_ctor_get(v_x_1028_, 1);
lean_inc(v_value_1030_);
v_tail_1031_ = lean_ctor_get(v_x_1028_, 2);
lean_inc(v_tail_1031_);
lean_dec_ref_known(v_x_1028_, 3);
lean_inc(v_f_1026_);
v___x_1032_ = lean_apply_3(v_f_1026_, v_x_1027_, v_key_1029_, v_value_1030_);
v_x_1027_ = v___x_1032_;
v_x_1028_ = v_tail_1031_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2___redArg(lean_object* v_f_1034_, lean_object* v_as_1035_, size_t v_i_1036_, size_t v_stop_1037_, lean_object* v_b_1038_){
_start:
{
uint8_t v___x_1039_; 
v___x_1039_ = lean_usize_dec_eq(v_i_1036_, v_stop_1037_);
if (v___x_1039_ == 0)
{
lean_object* v___x_1040_; lean_object* v___x_1041_; size_t v___x_1042_; size_t v___x_1043_; 
v___x_1040_ = lean_array_uget_borrowed(v_as_1035_, v_i_1036_);
lean_inc(v___x_1040_);
lean_inc(v_f_1034_);
v___x_1041_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__0___redArg(v_f_1034_, v_b_1038_, v___x_1040_);
v___x_1042_ = ((size_t)1ULL);
v___x_1043_ = lean_usize_add(v_i_1036_, v___x_1042_);
v_i_1036_ = v___x_1043_;
v_b_1038_ = v___x_1041_;
goto _start;
}
else
{
lean_dec(v_f_1034_);
return v_b_1038_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2___redArg___boxed(lean_object* v_f_1045_, lean_object* v_as_1046_, lean_object* v_i_1047_, lean_object* v_stop_1048_, lean_object* v_b_1049_){
_start:
{
size_t v_i_boxed_1050_; size_t v_stop_boxed_1051_; lean_object* v_res_1052_; 
v_i_boxed_1050_ = lean_unbox_usize(v_i_1047_);
lean_dec(v_i_1047_);
v_stop_boxed_1051_ = lean_unbox_usize(v_stop_1048_);
lean_dec(v_stop_1048_);
v_res_1052_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2___redArg(v_f_1045_, v_as_1046_, v_i_boxed_1050_, v_stop_boxed_1051_, v_b_1049_);
lean_dec_ref(v_as_1046_);
return v_res_1052_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0___redArg(lean_object* v_f_1053_, lean_object* v_init_1054_, lean_object* v_m_1055_){
_start:
{
lean_object* v_map_u2081_1056_; lean_object* v_map_u2082_1057_; lean_object* v_buckets_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; uint8_t v___x_1061_; 
v_map_u2081_1056_ = lean_ctor_get(v_m_1055_, 0);
v_map_u2082_1057_ = lean_ctor_get(v_m_1055_, 1);
v_buckets_1058_ = lean_ctor_get(v_map_u2081_1056_, 1);
v___x_1059_ = lean_unsigned_to_nat(0u);
v___x_1060_ = lean_array_get_size(v_buckets_1058_);
v___x_1061_ = lean_nat_dec_lt(v___x_1059_, v___x_1060_);
if (v___x_1061_ == 0)
{
lean_object* v___x_1062_; 
v___x_1062_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg(v_map_u2082_1057_, v_f_1053_, v_init_1054_);
return v___x_1062_;
}
else
{
uint8_t v___x_1063_; 
v___x_1063_ = lean_nat_dec_le(v___x_1060_, v___x_1060_);
if (v___x_1063_ == 0)
{
if (v___x_1061_ == 0)
{
lean_object* v___x_1064_; 
v___x_1064_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg(v_map_u2082_1057_, v_f_1053_, v_init_1054_);
return v___x_1064_;
}
else
{
size_t v___x_1065_; size_t v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; 
v___x_1065_ = ((size_t)0ULL);
v___x_1066_ = lean_usize_of_nat(v___x_1060_);
lean_inc(v_f_1053_);
v___x_1067_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2___redArg(v_f_1053_, v_buckets_1058_, v___x_1065_, v___x_1066_, v_init_1054_);
v___x_1068_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg(v_map_u2082_1057_, v_f_1053_, v___x_1067_);
return v___x_1068_;
}
}
else
{
size_t v___x_1069_; size_t v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; 
v___x_1069_ = ((size_t)0ULL);
v___x_1070_ = lean_usize_of_nat(v___x_1060_);
lean_inc(v_f_1053_);
v___x_1071_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2___redArg(v_f_1053_, v_buckets_1058_, v___x_1069_, v___x_1070_, v_init_1054_);
v___x_1072_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg(v_map_u2082_1057_, v_f_1053_, v___x_1071_);
return v___x_1072_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0___redArg___boxed(lean_object* v_f_1073_, lean_object* v_init_1074_, lean_object* v_m_1075_){
_start:
{
lean_object* v_res_1076_; 
v_res_1076_ = l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0___redArg(v_f_1073_, v_init_1074_, v_m_1075_);
lean_dec_ref(v_m_1075_);
return v_res_1076_;
}
}
LEAN_EXPORT lean_object* l_Lean_getRevAliases(lean_object* v_env_1077_, lean_object* v_e_1078_){
_start:
{
lean_object* v___x_1079_; lean_object* v_toEnvExtension_1080_; lean_object* v_asyncMode_1081_; lean_object* v___f_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; 
v___x_1079_ = l_Lean_aliasExtension;
v_toEnvExtension_1080_ = lean_ctor_get(v___x_1079_, 0);
v_asyncMode_1081_ = lean_ctor_get(v_toEnvExtension_1080_, 2);
v___f_1082_ = lean_alloc_closure((void*)(l_Lean_getRevAliases___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1082_, 0, v_e_1078_);
v___x_1083_ = lean_obj_once(&l_Lean_getAliasState___closed__2, &l_Lean_getAliasState___closed__2_once, _init_l_Lean_getAliasState___closed__2);
v___x_1084_ = lean_box(0);
v___x_1085_ = lean_box(0);
v___x_1086_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1083_, v___x_1079_, v_env_1077_, v_asyncMode_1081_, v___x_1085_);
v___x_1087_ = l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0___redArg(v___f_1082_, v___x_1084_, v___x_1086_);
lean_dec(v___x_1086_);
return v___x_1087_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0(lean_object* v_00_u03b2_1088_, lean_object* v_00_u03c3_1089_, lean_object* v_f_1090_, lean_object* v_init_1091_, lean_object* v_m_1092_){
_start:
{
lean_object* v___x_1093_; 
v___x_1093_ = l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0___redArg(v_f_1090_, v_init_1091_, v_m_1092_);
return v___x_1093_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0___boxed(lean_object* v_00_u03b2_1094_, lean_object* v_00_u03c3_1095_, lean_object* v_f_1096_, lean_object* v_init_1097_, lean_object* v_m_1098_){
_start:
{
lean_object* v_res_1099_; 
v_res_1099_ = l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0(v_00_u03b2_1094_, v_00_u03c3_1095_, v_f_1096_, v_init_1097_, v_m_1098_);
lean_dec_ref(v_m_1098_);
return v_res_1099_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__0(lean_object* v_00_u03b2_1100_, lean_object* v_00_u03c3_1101_, lean_object* v_f_1102_, lean_object* v_x_1103_, lean_object* v_x_1104_){
_start:
{
lean_object* v___x_1105_; 
v___x_1105_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__0___redArg(v_f_1102_, v_x_1103_, v_x_1104_);
return v___x_1105_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1(lean_object* v_00_u03c3_1106_, lean_object* v_00_u03b2_1107_, lean_object* v_map_1108_, lean_object* v_f_1109_, lean_object* v_init_1110_){
_start:
{
lean_object* v___x_1111_; 
v___x_1111_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg(v_map_1108_, v_f_1109_, v_init_1110_);
return v___x_1111_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___boxed(lean_object* v_00_u03c3_1112_, lean_object* v_00_u03b2_1113_, lean_object* v_map_1114_, lean_object* v_f_1115_, lean_object* v_init_1116_){
_start:
{
lean_object* v_res_1117_; 
v_res_1117_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1(v_00_u03c3_1112_, v_00_u03b2_1113_, v_map_1114_, v_f_1115_, v_init_1116_);
lean_dec_ref(v_map_1114_);
return v_res_1117_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2(lean_object* v_00_u03b2_1118_, lean_object* v_00_u03c3_1119_, lean_object* v_f_1120_, lean_object* v_as_1121_, size_t v_i_1122_, size_t v_stop_1123_, lean_object* v_b_1124_){
_start:
{
lean_object* v___x_1125_; 
v___x_1125_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2___redArg(v_f_1120_, v_as_1121_, v_i_1122_, v_stop_1123_, v_b_1124_);
return v___x_1125_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1126_, lean_object* v_00_u03c3_1127_, lean_object* v_f_1128_, lean_object* v_as_1129_, lean_object* v_i_1130_, lean_object* v_stop_1131_, lean_object* v_b_1132_){
_start:
{
size_t v_i_boxed_1133_; size_t v_stop_boxed_1134_; lean_object* v_res_1135_; 
v_i_boxed_1133_ = lean_unbox_usize(v_i_1130_);
lean_dec(v_i_1130_);
v_stop_boxed_1134_ = lean_unbox_usize(v_stop_1131_);
lean_dec(v_stop_1131_);
v_res_1135_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2(v_00_u03b2_1126_, v_00_u03c3_1127_, v_f_1128_, v_as_1129_, v_i_boxed_1133_, v_stop_boxed_1134_, v_b_1132_);
lean_dec_ref(v_as_1129_);
return v_res_1135_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2___redArg(lean_object* v_map_1136_, lean_object* v_f_1137_, lean_object* v_init_1138_){
_start:
{
lean_object* v___x_1139_; 
v___x_1139_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg(v_f_1137_, v_map_1136_, v_init_1138_);
return v___x_1139_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_map_1140_, lean_object* v_f_1141_, lean_object* v_init_1142_){
_start:
{
lean_object* v_res_1143_; 
v_res_1143_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2___redArg(v_map_1140_, v_f_1141_, v_init_1142_);
lean_dec_ref(v_map_1140_);
return v_res_1143_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2(lean_object* v_00_u03c3_1144_, lean_object* v_00_u03b2_1145_, lean_object* v_map_1146_, lean_object* v_f_1147_, lean_object* v_init_1148_){
_start:
{
lean_object* v___x_1149_; 
v___x_1149_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg(v_f_1147_, v_map_1146_, v_init_1148_);
return v___x_1149_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03c3_1150_, lean_object* v_00_u03b2_1151_, lean_object* v_map_1152_, lean_object* v_f_1153_, lean_object* v_init_1154_){
_start:
{
lean_object* v_res_1155_; 
v_res_1155_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2(v_00_u03c3_1150_, v_00_u03b2_1151_, v_map_1152_, v_f_1153_, v_init_1154_);
lean_dec_ref(v_map_1152_);
return v_res_1155_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03c3_1156_, lean_object* v_00_u03b1_1157_, lean_object* v_00_u03b2_1158_, lean_object* v_f_1159_, lean_object* v_x_1160_, lean_object* v_x_1161_){
_start:
{
lean_object* v___x_1162_; 
v___x_1162_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg(v_f_1159_, v_x_1160_, v_x_1161_);
return v___x_1162_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03c3_1163_, lean_object* v_00_u03b1_1164_, lean_object* v_00_u03b2_1165_, lean_object* v_f_1166_, lean_object* v_x_1167_, lean_object* v_x_1168_){
_start:
{
lean_object* v_res_1169_; 
v_res_1169_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3(v_00_u03c3_1163_, v_00_u03b1_1164_, v_00_u03b2_1165_, v_f_1166_, v_x_1167_, v_x_1168_);
lean_dec_ref(v_x_1167_);
return v_res_1169_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5(lean_object* v_00_u03b1_1170_, lean_object* v_00_u03b2_1171_, lean_object* v_00_u03c3_1172_, lean_object* v_f_1173_, lean_object* v_as_1174_, size_t v_i_1175_, size_t v_stop_1176_, lean_object* v_b_1177_){
_start:
{
lean_object* v___x_1178_; 
v___x_1178_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(v_f_1173_, v_as_1174_, v_i_1175_, v_stop_1176_, v_b_1177_);
return v___x_1178_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5___boxed(lean_object* v_00_u03b1_1179_, lean_object* v_00_u03b2_1180_, lean_object* v_00_u03c3_1181_, lean_object* v_f_1182_, lean_object* v_as_1183_, lean_object* v_i_1184_, lean_object* v_stop_1185_, lean_object* v_b_1186_){
_start:
{
size_t v_i_boxed_1187_; size_t v_stop_boxed_1188_; lean_object* v_res_1189_; 
v_i_boxed_1187_ = lean_unbox_usize(v_i_1184_);
lean_dec(v_i_1184_);
v_stop_boxed_1188_ = lean_unbox_usize(v_stop_1185_);
lean_dec(v_stop_1185_);
v_res_1189_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5(v_00_u03b1_1179_, v_00_u03b2_1180_, v_00_u03c3_1181_, v_f_1182_, v_as_1183_, v_i_boxed_1187_, v_stop_boxed_1188_, v_b_1186_);
lean_dec_ref(v_as_1183_);
return v_res_1189_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6(lean_object* v_00_u03c3_1190_, lean_object* v_00_u03b1_1191_, lean_object* v_00_u03b2_1192_, lean_object* v_f_1193_, lean_object* v_keys_1194_, lean_object* v_vals_1195_, lean_object* v_heq_1196_, lean_object* v_i_1197_, lean_object* v_acc_1198_){
_start:
{
lean_object* v___x_1199_; 
v___x_1199_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6___redArg(v_f_1193_, v_keys_1194_, v_vals_1195_, v_i_1197_, v_acc_1198_);
return v___x_1199_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03c3_1200_, lean_object* v_00_u03b1_1201_, lean_object* v_00_u03b2_1202_, lean_object* v_f_1203_, lean_object* v_keys_1204_, lean_object* v_vals_1205_, lean_object* v_heq_1206_, lean_object* v_i_1207_, lean_object* v_acc_1208_){
_start:
{
lean_object* v_res_1209_; 
v_res_1209_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6(v_00_u03c3_1200_, v_00_u03b1_1201_, v_00_u03b2_1202_, v_f_1203_, v_keys_1204_, v_vals_1205_, v_heq_1206_, v_i_1207_, v_acc_1208_);
lean_dec_ref(v_vals_1205_);
lean_dec_ref(v_keys_1204_);
return v_res_1209_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(lean_object* v_env_1210_, lean_object* v_declName_1211_){
_start:
{
uint8_t v___y_1213_; uint8_t v___x_1216_; 
v___x_1216_ = l_Lean_Environment_containsOnBranch(v_env_1210_, v_declName_1211_);
if (v___x_1216_ == 0)
{
uint8_t v___x_1217_; 
lean_inc(v_declName_1211_);
lean_inc_ref(v_env_1210_);
v___x_1217_ = lean_is_reserved_name(v_env_1210_, v_declName_1211_);
v___y_1213_ = v___x_1217_;
goto v___jp_1212_;
}
else
{
v___y_1213_ = v___x_1216_;
goto v___jp_1212_;
}
v___jp_1212_:
{
if (v___y_1213_ == 0)
{
uint8_t v___x_1214_; uint8_t v___x_1215_; 
v___x_1214_ = 1;
v___x_1215_ = l_Lean_Environment_contains(v_env_1210_, v_declName_1211_, v___x_1214_);
return v___x_1215_;
}
else
{
lean_dec(v_declName_1211_);
lean_dec_ref(v_env_1210_);
return v___y_1213_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved___boxed(lean_object* v_env_1218_, lean_object* v_declName_1219_){
_start:
{
uint8_t v_res_1220_; lean_object* v_r_1221_; 
v_res_1220_ = l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(v_env_1218_, v_declName_1219_);
v_r_1221_ = lean_box(v_res_1220_);
return v_r_1221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__spec__0(lean_object* v_name_1222_, lean_object* v_decl_1223_, lean_object* v_ref_1224_){
_start:
{
lean_object* v_defValue_1226_; lean_object* v_descr_1227_; lean_object* v_deprecation_x3f_1228_; lean_object* v___x_1229_; uint8_t v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; 
v_defValue_1226_ = lean_ctor_get(v_decl_1223_, 0);
v_descr_1227_ = lean_ctor_get(v_decl_1223_, 1);
v_deprecation_x3f_1228_ = lean_ctor_get(v_decl_1223_, 2);
v___x_1229_ = lean_alloc_ctor(1, 0, 1);
v___x_1230_ = lean_unbox(v_defValue_1226_);
lean_ctor_set_uint8(v___x_1229_, 0, v___x_1230_);
lean_inc(v_deprecation_x3f_1228_);
lean_inc_ref(v_descr_1227_);
lean_inc_n(v_name_1222_, 2);
v___x_1231_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1231_, 0, v_name_1222_);
lean_ctor_set(v___x_1231_, 1, v_ref_1224_);
lean_ctor_set(v___x_1231_, 2, v___x_1229_);
lean_ctor_set(v___x_1231_, 3, v_descr_1227_);
lean_ctor_set(v___x_1231_, 4, v_deprecation_x3f_1228_);
v___x_1232_ = lean_register_option(v_name_1222_, v___x_1231_);
if (lean_obj_tag(v___x_1232_) == 0)
{
lean_object* v___x_1234_; uint8_t v_isShared_1235_; uint8_t v_isSharedCheck_1240_; 
v_isSharedCheck_1240_ = !lean_is_exclusive(v___x_1232_);
if (v_isSharedCheck_1240_ == 0)
{
lean_object* v_unused_1241_; 
v_unused_1241_ = lean_ctor_get(v___x_1232_, 0);
lean_dec(v_unused_1241_);
v___x_1234_ = v___x_1232_;
v_isShared_1235_ = v_isSharedCheck_1240_;
goto v_resetjp_1233_;
}
else
{
lean_dec(v___x_1232_);
v___x_1234_ = lean_box(0);
v_isShared_1235_ = v_isSharedCheck_1240_;
goto v_resetjp_1233_;
}
v_resetjp_1233_:
{
lean_object* v___x_1236_; lean_object* v___x_1238_; 
lean_inc(v_defValue_1226_);
v___x_1236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1236_, 0, v_name_1222_);
lean_ctor_set(v___x_1236_, 1, v_defValue_1226_);
if (v_isShared_1235_ == 0)
{
lean_ctor_set(v___x_1234_, 0, v___x_1236_);
v___x_1238_ = v___x_1234_;
goto v_reusejp_1237_;
}
else
{
lean_object* v_reuseFailAlloc_1239_; 
v_reuseFailAlloc_1239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1239_, 0, v___x_1236_);
v___x_1238_ = v_reuseFailAlloc_1239_;
goto v_reusejp_1237_;
}
v_reusejp_1237_:
{
return v___x_1238_;
}
}
}
else
{
lean_object* v_a_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1249_; 
lean_dec(v_name_1222_);
v_a_1242_ = lean_ctor_get(v___x_1232_, 0);
v_isSharedCheck_1249_ = !lean_is_exclusive(v___x_1232_);
if (v_isSharedCheck_1249_ == 0)
{
v___x_1244_ = v___x_1232_;
v_isShared_1245_ = v_isSharedCheck_1249_;
goto v_resetjp_1243_;
}
else
{
lean_inc(v_a_1242_);
lean_dec(v___x_1232_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1249_;
goto v_resetjp_1243_;
}
v_resetjp_1243_:
{
lean_object* v___x_1247_; 
if (v_isShared_1245_ == 0)
{
v___x_1247_ = v___x_1244_;
goto v_reusejp_1246_;
}
else
{
lean_object* v_reuseFailAlloc_1248_; 
v_reuseFailAlloc_1248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1248_, 0, v_a_1242_);
v___x_1247_ = v_reuseFailAlloc_1248_;
goto v_reusejp_1246_;
}
v_reusejp_1246_:
{
return v___x_1247_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_1250_, lean_object* v_decl_1251_, lean_object* v_ref_1252_, lean_object* v_a_1253_){
_start:
{
lean_object* v_res_1254_; 
v_res_1254_ = l_Lean_Option_register___at___00__private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__spec__0(v_name_1250_, v_decl_1251_, v_ref_1252_);
lean_dec_ref(v_decl_1251_);
return v_res_1254_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; 
v___x_1273_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__2_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_));
v___x_1274_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__4_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_));
v___x_1275_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__6_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_));
v___x_1276_ = l_Lean_Option_register___at___00__private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__spec__0(v___x_1273_, v___x_1274_, v___x_1275_);
return v___x_1276_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4____boxed(lean_object* v_a_1277_){
_start:
{
lean_object* v_res_1278_; 
v_res_1278_ = l___private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_();
return v_res_1278_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; 
v___x_1297_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__1_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4_));
v___x_1298_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__3_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4_));
v___x_1299_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__4_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4_));
v___x_1300_ = l_Lean_Option_register___at___00__private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__spec__0(v___x_1297_, v___x_1298_, v___x_1299_);
return v___x_1300_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4____boxed(lean_object* v_a_1301_){
_start:
{
lean_object* v_res_1302_; 
v_res_1302_ = l___private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4_();
return v_res_1302_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__1(lean_object* v_opts_1303_, lean_object* v_opt_1304_){
_start:
{
lean_object* v_name_1305_; lean_object* v_defValue_1306_; lean_object* v_map_1307_; lean_object* v___x_1308_; 
v_name_1305_ = lean_ctor_get(v_opt_1304_, 0);
v_defValue_1306_ = lean_ctor_get(v_opt_1304_, 1);
v_map_1307_ = lean_ctor_get(v_opts_1303_, 0);
v___x_1308_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1307_, v_name_1305_);
if (lean_obj_tag(v___x_1308_) == 0)
{
uint8_t v___x_1309_; 
v___x_1309_ = lean_unbox(v_defValue_1306_);
return v___x_1309_;
}
else
{
lean_object* v_val_1310_; 
v_val_1310_ = lean_ctor_get(v___x_1308_, 0);
lean_inc(v_val_1310_);
lean_dec_ref_known(v___x_1308_, 1);
if (lean_obj_tag(v_val_1310_) == 1)
{
uint8_t v_v_1311_; 
v_v_1311_ = lean_ctor_get_uint8(v_val_1310_, 0);
lean_dec_ref_known(v_val_1310_, 0);
return v_v_1311_;
}
else
{
uint8_t v___x_1312_; 
lean_dec(v_val_1310_);
v___x_1312_ = lean_unbox(v_defValue_1306_);
return v___x_1312_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__1___boxed(lean_object* v_opts_1313_, lean_object* v_opt_1314_){
_start:
{
uint8_t v_res_1315_; lean_object* v_r_1316_; 
v_res_1315_ = l_Lean_Option_get___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__1(v_opts_1313_, v_opt_1314_);
lean_dec_ref(v_opt_1314_);
lean_dec_ref(v_opts_1313_);
v_r_1316_ = lean_box(v_res_1315_);
return v_r_1316_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0(lean_object* v_declName_1320_, lean_object* v_env_1321_, lean_object* v_as_1322_, size_t v_sz_1323_, size_t v_i_1324_, lean_object* v_b_1325_){
_start:
{
uint8_t v___x_1326_; 
v___x_1326_ = lean_usize_dec_lt(v_i_1324_, v_sz_1323_);
if (v___x_1326_ == 0)
{
lean_dec_ref(v_env_1321_);
lean_dec(v_declName_1320_);
lean_inc_ref(v_b_1325_);
return v_b_1325_;
}
else
{
lean_object* v_a_1327_; lean_object* v_toImport_1328_; lean_object* v_module_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; uint8_t v___x_1332_; 
v_a_1327_ = lean_array_uget_borrowed(v_as_1322_, v_i_1324_);
v_toImport_1328_ = lean_ctor_get(v_a_1327_, 0);
v_module_1329_ = lean_ctor_get(v_toImport_1328_, 0);
v___x_1330_ = lean_box(0);
lean_inc(v_declName_1320_);
lean_inc(v_module_1329_);
v___x_1331_ = l_Lean_mkPrivateNameCore(v_module_1329_, v_declName_1320_);
lean_inc(v___x_1331_);
lean_inc_ref(v_env_1321_);
v___x_1332_ = l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(v_env_1321_, v___x_1331_);
if (v___x_1332_ == 0)
{
lean_object* v___x_1333_; size_t v___x_1334_; size_t v___x_1335_; 
lean_dec(v___x_1331_);
v___x_1333_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0___closed__0));
v___x_1334_ = ((size_t)1ULL);
v___x_1335_ = lean_usize_add(v_i_1324_, v___x_1334_);
v_i_1324_ = v___x_1335_;
v_b_1325_ = v___x_1333_;
goto _start;
}
else
{
lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; 
lean_dec_ref(v_env_1321_);
lean_dec(v_declName_1320_);
v___x_1337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1337_, 0, v___x_1331_);
v___x_1338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1338_, 0, v___x_1337_);
v___x_1339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1339_, 0, v___x_1338_);
lean_ctor_set(v___x_1339_, 1, v___x_1330_);
return v___x_1339_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0___boxed(lean_object* v_declName_1340_, lean_object* v_env_1341_, lean_object* v_as_1342_, lean_object* v_sz_1343_, lean_object* v_i_1344_, lean_object* v_b_1345_){
_start:
{
size_t v_sz_boxed_1346_; size_t v_i_boxed_1347_; lean_object* v_res_1348_; 
v_sz_boxed_1346_ = lean_unbox_usize(v_sz_1343_);
lean_dec(v_sz_1343_);
v_i_boxed_1347_ = lean_unbox_usize(v_i_1344_);
lean_dec(v_i_1344_);
v_res_1348_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0(v_declName_1340_, v_env_1341_, v_as_1342_, v_sz_boxed_1346_, v_i_boxed_1347_, v_b_1345_);
lean_dec_ref(v_b_1345_);
lean_dec_ref(v_as_1342_);
return v_res_1348_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName(lean_object* v_env_1349_, lean_object* v_opts_1350_, lean_object* v_declName_1351_){
_start:
{
uint8_t v_isExporting_1367_; 
v_isExporting_1367_ = lean_ctor_get_uint8(v_env_1349_, sizeof(void*)*8);
if (v_isExporting_1367_ == 0)
{
goto v___jp_1352_;
}
else
{
lean_object* v___x_1368_; uint8_t v___x_1369_; 
v___x_1368_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_1369_ = l_Lean_Option_get___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__1(v_opts_1350_, v___x_1368_);
if (v___x_1369_ == 0)
{
lean_object* v___x_1370_; 
lean_dec(v_declName_1351_);
lean_dec_ref(v_env_1349_);
v___x_1370_ = lean_box(0);
return v___x_1370_;
}
else
{
goto v___jp_1352_;
}
}
v___jp_1352_:
{
lean_object* v___x_1353_; uint8_t v___x_1354_; 
lean_inc(v_declName_1351_);
v___x_1353_ = l_Lean_mkPrivateName(v_env_1349_, v_declName_1351_);
lean_inc(v___x_1353_);
lean_inc_ref(v_env_1349_);
v___x_1354_ = l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(v_env_1349_, v___x_1353_);
if (v___x_1354_ == 0)
{
lean_object* v___x_1355_; uint8_t v_isModule_1356_; 
lean_dec(v___x_1353_);
v___x_1355_ = l_Lean_Environment_header(v_env_1349_);
v_isModule_1356_ = lean_ctor_get_uint8(v___x_1355_, sizeof(void*)*7 + 4);
if (v_isModule_1356_ == 0)
{
lean_object* v___x_1357_; 
lean_dec_ref(v___x_1355_);
lean_dec(v_declName_1351_);
lean_dec_ref(v_env_1349_);
v___x_1357_ = lean_box(0);
return v___x_1357_;
}
else
{
lean_object* v_importAllModules_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; size_t v_sz_1361_; size_t v___x_1362_; lean_object* v___x_1363_; lean_object* v_fst_1364_; 
v_importAllModules_1358_ = lean_ctor_get(v___x_1355_, 5);
lean_inc_ref(v_importAllModules_1358_);
lean_dec_ref(v___x_1355_);
v___x_1359_ = lean_box(0);
v___x_1360_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0___closed__0));
v_sz_1361_ = lean_array_size(v_importAllModules_1358_);
v___x_1362_ = ((size_t)0ULL);
v___x_1363_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0(v_declName_1351_, v_env_1349_, v_importAllModules_1358_, v_sz_1361_, v___x_1362_, v___x_1360_);
lean_dec_ref(v_importAllModules_1358_);
v_fst_1364_ = lean_ctor_get(v___x_1363_, 0);
lean_inc(v_fst_1364_);
lean_dec_ref(v___x_1363_);
if (lean_obj_tag(v_fst_1364_) == 0)
{
return v___x_1359_;
}
else
{
lean_object* v_val_1365_; 
v_val_1365_ = lean_ctor_get(v_fst_1364_, 0);
lean_inc(v_val_1365_);
lean_dec_ref_known(v_fst_1364_, 1);
return v_val_1365_;
}
}
}
else
{
lean_object* v___x_1366_; 
lean_dec(v_declName_1351_);
lean_dec_ref(v_env_1349_);
v___x_1366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1366_, 0, v___x_1353_);
return v___x_1366_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName___boxed(lean_object* v_env_1371_, lean_object* v_opts_1372_, lean_object* v_declName_1373_){
_start:
{
lean_object* v_res_1374_; 
v_res_1374_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName(v_env_1371_, v_opts_1372_, v_declName_1373_);
lean_dec_ref(v_opts_1372_);
return v_res_1374_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveQualifiedName(lean_object* v_env_1375_, lean_object* v_opts_1376_, lean_object* v_ns_1377_, lean_object* v_id_1378_){
_start:
{
lean_object* v_resolvedId_1379_; uint8_t v___x_1380_; lean_object* v_resolvedIds_1381_; 
lean_inc(v_id_1378_);
v_resolvedId_1379_ = l_Lean_Name_append(v_ns_1377_, v_id_1378_);
v___x_1380_ = l_Lean_Name_isAtomic(v_id_1378_);
lean_dec(v_id_1378_);
lean_inc_ref(v_env_1375_);
v_resolvedIds_1381_ = l_Lean_getAliases(v_env_1375_, v_resolvedId_1379_, v___x_1380_);
if (v___x_1380_ == 0)
{
goto v___jp_1382_;
}
else
{
uint8_t v___x_1388_; 
lean_inc(v_resolvedId_1379_);
lean_inc_ref(v_env_1375_);
v___x_1388_ = l_Lean_isProtected(v_env_1375_, v_resolvedId_1379_);
if (v___x_1388_ == 0)
{
goto v___jp_1382_;
}
else
{
lean_dec(v_resolvedId_1379_);
lean_dec_ref(v_env_1375_);
return v_resolvedIds_1381_;
}
}
v___jp_1382_:
{
uint8_t v___x_1383_; 
lean_inc(v_resolvedId_1379_);
lean_inc_ref(v_env_1375_);
v___x_1383_ = l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(v_env_1375_, v_resolvedId_1379_);
if (v___x_1383_ == 0)
{
lean_object* v___x_1384_; 
v___x_1384_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName(v_env_1375_, v_opts_1376_, v_resolvedId_1379_);
if (lean_obj_tag(v___x_1384_) == 1)
{
lean_object* v_val_1385_; lean_object* v___x_1386_; 
v_val_1385_ = lean_ctor_get(v___x_1384_, 0);
lean_inc(v_val_1385_);
lean_dec_ref_known(v___x_1384_, 1);
v___x_1386_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1386_, 0, v_val_1385_);
lean_ctor_set(v___x_1386_, 1, v_resolvedIds_1381_);
return v___x_1386_;
}
else
{
lean_dec(v___x_1384_);
return v_resolvedIds_1381_;
}
}
else
{
lean_object* v___x_1387_; 
lean_dec_ref(v_env_1375_);
v___x_1387_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1387_, 0, v_resolvedId_1379_);
lean_ctor_set(v___x_1387_, 1, v_resolvedIds_1381_);
return v___x_1387_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveQualifiedName___boxed(lean_object* v_env_1389_, lean_object* v_opts_1390_, lean_object* v_ns_1391_, lean_object* v_id_1392_){
_start:
{
lean_object* v_res_1393_; 
v_res_1393_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveQualifiedName(v_env_1389_, v_opts_1390_, v_ns_1391_, v_id_1392_);
lean_dec_ref(v_opts_1390_);
return v_res_1393_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveUsingNamespace(lean_object* v_env_1394_, lean_object* v_opts_1395_, lean_object* v_id_1396_, lean_object* v_x_1397_){
_start:
{
if (lean_obj_tag(v_x_1397_) == 1)
{
lean_object* v_pre_1398_; lean_object* v___x_1399_; 
v_pre_1398_ = lean_ctor_get(v_x_1397_, 0);
lean_inc(v_pre_1398_);
lean_inc(v_id_1396_);
lean_inc_ref(v_env_1394_);
v___x_1399_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveQualifiedName(v_env_1394_, v_opts_1395_, v_x_1397_, v_id_1396_);
if (lean_obj_tag(v___x_1399_) == 0)
{
v_x_1397_ = v_pre_1398_;
goto _start;
}
else
{
lean_dec(v_pre_1398_);
lean_dec(v_id_1396_);
lean_dec_ref(v_env_1394_);
return v___x_1399_;
}
}
else
{
lean_object* v___x_1401_; 
lean_dec(v_x_1397_);
lean_dec(v_id_1396_);
lean_dec_ref(v_env_1394_);
v___x_1401_ = lean_box(0);
return v___x_1401_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveUsingNamespace___boxed(lean_object* v_env_1402_, lean_object* v_opts_1403_, lean_object* v_id_1404_, lean_object* v_x_1405_){
_start:
{
lean_object* v_res_1406_; 
v_res_1406_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveUsingNamespace(v_env_1402_, v_opts_1403_, v_id_1404_, v_x_1405_);
lean_dec_ref(v_opts_1403_);
return v_res_1406_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveExact(lean_object* v_env_1407_, lean_object* v_opts_1408_, lean_object* v_id_1409_){
_start:
{
uint8_t v___x_1410_; 
v___x_1410_ = l_Lean_Name_isAtomic(v_id_1409_);
if (v___x_1410_ == 0)
{
lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v_resolvedId_1413_; uint8_t v___x_1414_; 
v___x_1411_ = l_Lean_rootNamespace;
v___x_1412_ = lean_box(0);
v_resolvedId_1413_ = l_Lean_Name_replacePrefix(v_id_1409_, v___x_1411_, v___x_1412_);
lean_inc(v_resolvedId_1413_);
lean_inc_ref(v_env_1407_);
v___x_1414_ = l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(v_env_1407_, v_resolvedId_1413_);
if (v___x_1414_ == 0)
{
lean_object* v___x_1415_; 
v___x_1415_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName(v_env_1407_, v_opts_1408_, v_resolvedId_1413_);
return v___x_1415_;
}
else
{
lean_object* v___x_1416_; 
lean_dec_ref(v_env_1407_);
v___x_1416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1416_, 0, v_resolvedId_1413_);
return v___x_1416_;
}
}
else
{
lean_object* v___x_1417_; 
lean_dec(v_id_1409_);
lean_dec_ref(v_env_1407_);
v___x_1417_ = lean_box(0);
return v___x_1417_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveExact___boxed(lean_object* v_env_1418_, lean_object* v_opts_1419_, lean_object* v_id_1420_){
_start:
{
lean_object* v_res_1421_; 
v_res_1421_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveExact(v_env_1418_, v_opts_1419_, v_id_1420_);
lean_dec_ref(v_opts_1419_);
return v_res_1421_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveOpenDecls(lean_object* v_env_1422_, lean_object* v_opts_1423_, lean_object* v_id_1424_, lean_object* v_x_1425_, lean_object* v_x_1426_){
_start:
{
if (lean_obj_tag(v_x_1425_) == 0)
{
lean_dec(v_id_1424_);
lean_dec_ref(v_env_1422_);
return v_x_1426_;
}
else
{
lean_object* v_head_1427_; 
v_head_1427_ = lean_ctor_get(v_x_1425_, 0);
lean_inc(v_head_1427_);
if (lean_obj_tag(v_head_1427_) == 0)
{
lean_object* v_tail_1428_; lean_object* v_ns_1429_; lean_object* v_except_1430_; uint8_t v___x_1431_; 
v_tail_1428_ = lean_ctor_get(v_x_1425_, 1);
lean_inc(v_tail_1428_);
lean_dec_ref_known(v_x_1425_, 2);
v_ns_1429_ = lean_ctor_get(v_head_1427_, 0);
lean_inc(v_ns_1429_);
v_except_1430_ = lean_ctor_get(v_head_1427_, 1);
lean_inc(v_except_1430_);
lean_dec_ref_known(v_head_1427_, 2);
v___x_1431_ = l_List_elem___at___00Lean_addAliasEntry_spec__2(v_id_1424_, v_except_1430_);
lean_dec(v_except_1430_);
if (v___x_1431_ == 0)
{
lean_object* v_newResolvedIds_1432_; lean_object* v___x_1433_; 
lean_inc(v_id_1424_);
lean_inc_ref(v_env_1422_);
v_newResolvedIds_1432_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveQualifiedName(v_env_1422_, v_opts_1423_, v_ns_1429_, v_id_1424_);
v___x_1433_ = l_List_appendTR___redArg(v_newResolvedIds_1432_, v_x_1426_);
v_x_1425_ = v_tail_1428_;
v_x_1426_ = v___x_1433_;
goto _start;
}
else
{
lean_dec(v_ns_1429_);
v_x_1425_ = v_tail_1428_;
goto _start;
}
}
else
{
lean_object* v_tail_1436_; lean_object* v___x_1438_; uint8_t v_isShared_1439_; uint8_t v_isSharedCheck_1456_; 
v_tail_1436_ = lean_ctor_get(v_x_1425_, 1);
v_isSharedCheck_1456_ = !lean_is_exclusive(v_x_1425_);
if (v_isSharedCheck_1456_ == 0)
{
lean_object* v_unused_1457_; 
v_unused_1457_ = lean_ctor_get(v_x_1425_, 0);
lean_dec(v_unused_1457_);
v___x_1438_ = v_x_1425_;
v_isShared_1439_ = v_isSharedCheck_1456_;
goto v_resetjp_1437_;
}
else
{
lean_inc(v_tail_1436_);
lean_dec(v_x_1425_);
v___x_1438_ = lean_box(0);
v_isShared_1439_ = v_isSharedCheck_1456_;
goto v_resetjp_1437_;
}
v_resetjp_1437_:
{
lean_object* v_id_1440_; lean_object* v_declName_1441_; uint8_t v___x_1442_; 
v_id_1440_ = lean_ctor_get(v_head_1427_, 0);
lean_inc(v_id_1440_);
v_declName_1441_ = lean_ctor_get(v_head_1427_, 1);
lean_inc(v_declName_1441_);
lean_dec_ref_known(v_head_1427_, 2);
v___x_1442_ = lean_name_eq(v_id_1440_, v_id_1424_);
if (v___x_1442_ == 0)
{
uint8_t v___x_1443_; 
v___x_1443_ = l_Lean_Name_isPrefixOf(v_id_1440_, v_id_1424_);
if (v___x_1443_ == 0)
{
lean_dec(v_declName_1441_);
lean_dec(v_id_1440_);
lean_del_object(v___x_1438_);
v_x_1425_ = v_tail_1436_;
goto _start;
}
else
{
lean_object* v_candidate_1445_; uint8_t v___x_1446_; 
lean_inc(v_id_1424_);
v_candidate_1445_ = l_Lean_Name_replacePrefix(v_id_1424_, v_id_1440_, v_declName_1441_);
lean_dec(v_declName_1441_);
lean_dec(v_id_1440_);
lean_inc(v_candidate_1445_);
lean_inc_ref(v_env_1422_);
v___x_1446_ = l_Lean_Environment_contains(v_env_1422_, v_candidate_1445_, v___x_1443_);
if (v___x_1446_ == 0)
{
lean_dec(v_candidate_1445_);
lean_del_object(v___x_1438_);
v_x_1425_ = v_tail_1436_;
goto _start;
}
else
{
lean_object* v___x_1449_; 
if (v_isShared_1439_ == 0)
{
lean_ctor_set(v___x_1438_, 1, v_x_1426_);
lean_ctor_set(v___x_1438_, 0, v_candidate_1445_);
v___x_1449_ = v___x_1438_;
goto v_reusejp_1448_;
}
else
{
lean_object* v_reuseFailAlloc_1451_; 
v_reuseFailAlloc_1451_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1451_, 0, v_candidate_1445_);
lean_ctor_set(v_reuseFailAlloc_1451_, 1, v_x_1426_);
v___x_1449_ = v_reuseFailAlloc_1451_;
goto v_reusejp_1448_;
}
v_reusejp_1448_:
{
v_x_1425_ = v_tail_1436_;
v_x_1426_ = v___x_1449_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_1453_; 
lean_dec(v_id_1440_);
if (v_isShared_1439_ == 0)
{
lean_ctor_set(v___x_1438_, 1, v_x_1426_);
lean_ctor_set(v___x_1438_, 0, v_declName_1441_);
v___x_1453_ = v___x_1438_;
goto v_reusejp_1452_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v_declName_1441_);
lean_ctor_set(v_reuseFailAlloc_1455_, 1, v_x_1426_);
v___x_1453_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1452_;
}
v_reusejp_1452_:
{
v_x_1425_ = v_tail_1436_;
v_x_1426_ = v___x_1453_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveOpenDecls___boxed(lean_object* v_env_1458_, lean_object* v_opts_1459_, lean_object* v_id_1460_, lean_object* v_x_1461_, lean_object* v_x_1462_){
_start:
{
lean_object* v_res_1463_; 
v_res_1463_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveOpenDecls(v_env_1458_, v_opts_1459_, v_id_1460_, v_x_1461_, v_x_1462_);
lean_dec_ref(v_opts_1459_);
return v_res_1463_;
}
}
LEAN_EXPORT lean_object* l_List_eraseDups___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__0(lean_object* v_as_1465_){
_start:
{
lean_object* v___f_1466_; lean_object* v___x_1467_; 
v___f_1466_ = ((lean_object*)(l_List_eraseDups___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__0___closed__0));
v___x_1467_ = l_List_eraseDupsBy___redArg(v___f_1466_, v_as_1465_);
return v___x_1467_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__1(lean_object* v_projs_1468_, lean_object* v_a_1469_, lean_object* v_a_1470_){
_start:
{
if (lean_obj_tag(v_a_1469_) == 0)
{
lean_object* v___x_1471_; 
lean_dec(v_projs_1468_);
v___x_1471_ = l_List_reverse___redArg(v_a_1470_);
return v___x_1471_;
}
else
{
lean_object* v_head_1472_; lean_object* v_tail_1473_; lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1482_; 
v_head_1472_ = lean_ctor_get(v_a_1469_, 0);
v_tail_1473_ = lean_ctor_get(v_a_1469_, 1);
v_isSharedCheck_1482_ = !lean_is_exclusive(v_a_1469_);
if (v_isSharedCheck_1482_ == 0)
{
v___x_1475_ = v_a_1469_;
v_isShared_1476_ = v_isSharedCheck_1482_;
goto v_resetjp_1474_;
}
else
{
lean_inc(v_tail_1473_);
lean_inc(v_head_1472_);
lean_dec(v_a_1469_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1482_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
lean_object* v___x_1477_; lean_object* v___x_1479_; 
lean_inc(v_projs_1468_);
v___x_1477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1477_, 0, v_head_1472_);
lean_ctor_set(v___x_1477_, 1, v_projs_1468_);
if (v_isShared_1476_ == 0)
{
lean_ctor_set(v___x_1475_, 1, v_a_1470_);
lean_ctor_set(v___x_1475_, 0, v___x_1477_);
v___x_1479_ = v___x_1475_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1481_; 
v_reuseFailAlloc_1481_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1481_, 0, v___x_1477_);
lean_ctor_set(v_reuseFailAlloc_1481_, 1, v_a_1470_);
v___x_1479_ = v_reuseFailAlloc_1481_;
goto v_reusejp_1478_;
}
v_reusejp_1478_:
{
v_a_1469_ = v_tail_1473_;
v_a_1470_ = v___x_1479_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop(lean_object* v_env_1483_, lean_object* v_opts_1484_, lean_object* v_ns_1485_, lean_object* v_openDecls_1486_, lean_object* v_extractionResult_1487_, lean_object* v_id_1488_, lean_object* v_projs_1489_){
_start:
{
if (lean_obj_tag(v_id_1488_) == 1)
{
lean_object* v_pre_1490_; lean_object* v_str_1491_; lean_object* v_imported_1492_; lean_object* v_ctx_1493_; lean_object* v_scopes_1494_; lean_object* v___x_1495_; lean_object* v_id_1496_; lean_object* v___y_1498_; lean_object* v___x_1508_; lean_object* v___y_1510_; 
v_pre_1490_ = lean_ctor_get(v_id_1488_, 0);
lean_inc(v_pre_1490_);
v_str_1491_ = lean_ctor_get(v_id_1488_, 1);
lean_inc_ref(v_str_1491_);
v_imported_1492_ = lean_ctor_get(v_extractionResult_1487_, 1);
v_ctx_1493_ = lean_ctor_get(v_extractionResult_1487_, 2);
v_scopes_1494_ = lean_ctor_get(v_extractionResult_1487_, 3);
lean_inc(v_scopes_1494_);
lean_inc(v_ctx_1493_);
lean_inc(v_imported_1492_);
v___x_1495_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1495_, 0, v_id_1488_);
lean_ctor_set(v___x_1495_, 1, v_imported_1492_);
lean_ctor_set(v___x_1495_, 2, v_ctx_1493_);
lean_ctor_set(v___x_1495_, 3, v_scopes_1494_);
v_id_1496_ = l_Lean_MacroScopesView_review(v___x_1495_);
lean_inc(v_ns_1485_);
lean_inc(v_id_1496_);
lean_inc_ref(v_env_1483_);
v___x_1508_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveUsingNamespace(v_env_1483_, v_opts_1484_, v_id_1496_, v_ns_1485_);
if (lean_obj_tag(v___x_1508_) == 0)
{
lean_object* v___x_1515_; 
lean_inc(v_id_1496_);
lean_inc_ref(v_env_1483_);
v___x_1515_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveExact(v_env_1483_, v_opts_1484_, v_id_1496_);
if (lean_obj_tag(v___x_1515_) == 0)
{
uint8_t v___x_1516_; 
lean_inc(v_id_1496_);
lean_inc_ref(v_env_1483_);
v___x_1516_ = l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(v_env_1483_, v_id_1496_);
if (v___x_1516_ == 0)
{
v___y_1510_ = v___x_1508_;
goto v___jp_1509_;
}
else
{
lean_object* v___x_1517_; 
lean_inc(v_id_1496_);
v___x_1517_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1517_, 0, v_id_1496_);
lean_ctor_set(v___x_1517_, 1, v___x_1508_);
v___y_1510_ = v___x_1517_;
goto v___jp_1509_;
}
}
else
{
lean_object* v_val_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; 
lean_dec(v_id_1496_);
lean_dec_ref(v_str_1491_);
lean_dec(v_pre_1490_);
lean_dec(v_openDecls_1486_);
lean_dec(v_ns_1485_);
lean_dec_ref(v_env_1483_);
v_val_1518_ = lean_ctor_get(v___x_1515_, 0);
lean_inc(v_val_1518_);
lean_dec_ref_known(v___x_1515_, 1);
v___x_1519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1519_, 0, v_val_1518_);
lean_ctor_set(v___x_1519_, 1, v_projs_1489_);
v___x_1520_ = lean_box(0);
v___x_1521_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1521_, 0, v___x_1519_);
lean_ctor_set(v___x_1521_, 1, v___x_1520_);
return v___x_1521_;
}
}
else
{
lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; 
lean_dec(v_id_1496_);
lean_dec_ref(v_str_1491_);
lean_dec(v_pre_1490_);
lean_dec(v_openDecls_1486_);
lean_dec(v_ns_1485_);
lean_dec_ref(v_env_1483_);
v___x_1522_ = l_List_eraseDups___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__0(v___x_1508_);
v___x_1523_ = lean_box(0);
v___x_1524_ = l_List_mapTR_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__1(v_projs_1489_, v___x_1522_, v___x_1523_);
return v___x_1524_;
}
v___jp_1497_:
{
lean_object* v_resolvedIds_1499_; uint8_t v___x_1500_; lean_object* v___x_1501_; lean_object* v_resolvedIds_1502_; 
lean_inc(v_openDecls_1486_);
lean_inc(v_id_1496_);
lean_inc_ref_n(v_env_1483_, 2);
v_resolvedIds_1499_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveOpenDecls(v_env_1483_, v_opts_1484_, v_id_1496_, v_openDecls_1486_, v___y_1498_);
v___x_1500_ = l_Lean_Name_isAtomic(v_id_1496_);
v___x_1501_ = l_Lean_getAliases(v_env_1483_, v_id_1496_, v___x_1500_);
lean_dec(v_id_1496_);
v_resolvedIds_1502_ = l_List_appendTR___redArg(v___x_1501_, v_resolvedIds_1499_);
if (lean_obj_tag(v_resolvedIds_1502_) == 0)
{
lean_object* v___x_1503_; 
v___x_1503_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1503_, 0, v_str_1491_);
lean_ctor_set(v___x_1503_, 1, v_projs_1489_);
v_id_1488_ = v_pre_1490_;
v_projs_1489_ = v___x_1503_;
goto _start;
}
else
{
lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; 
lean_dec_ref(v_str_1491_);
lean_dec(v_pre_1490_);
lean_dec(v_openDecls_1486_);
lean_dec(v_ns_1485_);
lean_dec_ref(v_env_1483_);
v___x_1505_ = l_List_eraseDups___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__0(v_resolvedIds_1502_);
v___x_1506_ = lean_box(0);
v___x_1507_ = l_List_mapTR_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__1(v_projs_1489_, v___x_1505_, v___x_1506_);
return v___x_1507_;
}
}
v___jp_1509_:
{
lean_object* v___x_1511_; 
lean_inc(v_id_1496_);
lean_inc_ref(v_env_1483_);
v___x_1511_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName(v_env_1483_, v_opts_1484_, v_id_1496_);
if (lean_obj_tag(v___x_1511_) == 1)
{
lean_object* v_val_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; 
v_val_1512_ = lean_ctor_get(v___x_1511_, 0);
lean_inc(v_val_1512_);
lean_dec_ref_known(v___x_1511_, 1);
v___x_1513_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1513_, 0, v_val_1512_);
lean_ctor_set(v___x_1513_, 1, v___x_1508_);
v___x_1514_ = l_List_appendTR___redArg(v___x_1513_, v___y_1510_);
v___y_1498_ = v___x_1514_;
goto v___jp_1497_;
}
else
{
lean_dec(v___x_1511_);
lean_dec(v___x_1508_);
v___y_1498_ = v___y_1510_;
goto v___jp_1497_;
}
}
}
else
{
lean_object* v___x_1525_; 
lean_dec(v_projs_1489_);
lean_dec(v_id_1488_);
lean_dec(v_openDecls_1486_);
lean_dec(v_ns_1485_);
lean_dec_ref(v_env_1483_);
v___x_1525_ = lean_box(0);
return v___x_1525_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop___boxed(lean_object* v_env_1526_, lean_object* v_opts_1527_, lean_object* v_ns_1528_, lean_object* v_openDecls_1529_, lean_object* v_extractionResult_1530_, lean_object* v_id_1531_, lean_object* v_projs_1532_){
_start:
{
lean_object* v_res_1533_; 
v_res_1533_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop(v_env_1526_, v_opts_1527_, v_ns_1528_, v_openDecls_1529_, v_extractionResult_1530_, v_id_1531_, v_projs_1532_);
lean_dec_ref(v_extractionResult_1530_);
lean_dec_ref(v_opts_1527_);
return v_res_1533_;
}
}
LEAN_EXPORT lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object* v_env_1534_, lean_object* v_opts_1535_, lean_object* v_ns_1536_, lean_object* v_openDecls_1537_, lean_object* v_id_1538_){
_start:
{
lean_object* v_extractionResult_1539_; lean_object* v_name_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; 
v_extractionResult_1539_ = l_Lean_extractMacroScopes(v_id_1538_);
v_name_1540_ = lean_ctor_get(v_extractionResult_1539_, 0);
lean_inc(v_name_1540_);
v___x_1541_ = lean_box(0);
v___x_1542_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop(v_env_1534_, v_opts_1535_, v_ns_1536_, v_openDecls_1537_, v_extractionResult_1539_, v_name_1540_, v___x_1541_);
lean_dec_ref(v_extractionResult_1539_);
return v___x_1542_;
}
}
LEAN_EXPORT lean_object* l_Lean_ResolveName_resolveGlobalName___boxed(lean_object* v_env_1543_, lean_object* v_opts_1544_, lean_object* v_ns_1545_, lean_object* v_openDecls_1546_, lean_object* v_id_1547_){
_start:
{
lean_object* v_res_1548_; 
v_res_1548_ = l_Lean_ResolveName_resolveGlobalName(v_env_1543_, v_opts_1544_, v_ns_1545_, v_openDecls_1546_, v_id_1547_);
lean_dec_ref(v_opts_1544_);
return v_res_1548_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_ResolveName_resolveNamespaceUsingScope_x3f_spec__0(lean_object* v_msg_1549_){
_start:
{
lean_object* v___x_1550_; lean_object* v___x_1551_; 
v___x_1550_ = lean_box(0);
v___x_1551_ = lean_panic_fn_borrowed(v___x_1550_, v_msg_1549_);
return v___x_1551_;
}
}
static lean_object* _init_l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__3(void){
_start:
{
lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; 
v___x_1555_ = ((lean_object*)(l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__2));
v___x_1556_ = lean_unsigned_to_nat(9u);
v___x_1557_ = lean_unsigned_to_nat(230u);
v___x_1558_ = ((lean_object*)(l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__1));
v___x_1559_ = ((lean_object*)(l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__0));
v___x_1560_ = l_mkPanicMessageWithDecl(v___x_1559_, v___x_1558_, v___x_1557_, v___x_1556_, v___x_1555_);
return v___x_1560_;
}
}
LEAN_EXPORT lean_object* l_Lean_ResolveName_resolveNamespaceUsingScope_x3f(lean_object* v_env_1561_, lean_object* v_n_1562_, lean_object* v_ns_1563_){
_start:
{
switch(lean_obj_tag(v_ns_1563_))
{
case 1:
{
lean_object* v_pre_1564_; lean_object* v___x_1565_; uint8_t v___x_1566_; 
v_pre_1564_ = lean_ctor_get(v_ns_1563_, 0);
lean_inc(v_pre_1564_);
lean_inc(v_n_1562_);
v___x_1565_ = l_Lean_Name_append(v_ns_1563_, v_n_1562_);
lean_inc_ref(v_env_1561_);
v___x_1566_ = l_Lean_Environment_isNamespace(v_env_1561_, v___x_1565_);
if (v___x_1566_ == 0)
{
lean_dec(v___x_1565_);
v_ns_1563_ = v_pre_1564_;
goto _start;
}
else
{
lean_object* v___x_1568_; 
lean_dec(v_pre_1564_);
lean_dec(v_n_1562_);
lean_dec_ref(v_env_1561_);
v___x_1568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1568_, 0, v___x_1565_);
return v___x_1568_;
}
}
case 0:
{
lean_object* v___x_1569_; lean_object* v_n_1570_; uint8_t v___x_1571_; 
v___x_1569_ = l_Lean_rootNamespace;
v_n_1570_ = l_Lean_Name_replacePrefix(v_n_1562_, v___x_1569_, v_ns_1563_);
v___x_1571_ = l_Lean_Environment_isNamespace(v_env_1561_, v_n_1570_);
if (v___x_1571_ == 0)
{
lean_object* v___x_1572_; 
lean_dec(v_n_1570_);
v___x_1572_ = lean_box(0);
return v___x_1572_;
}
else
{
lean_object* v___x_1573_; 
v___x_1573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1573_, 0, v_n_1570_);
return v___x_1573_;
}
}
default: 
{
lean_object* v___x_1574_; lean_object* v___x_1575_; 
lean_dec(v_ns_1563_);
lean_dec(v_n_1562_);
lean_dec_ref(v_env_1561_);
v___x_1574_ = lean_obj_once(&l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__3, &l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__3_once, _init_l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__3);
v___x_1575_ = l_panic___at___00Lean_ResolveName_resolveNamespaceUsingScope_x3f_spec__0(v___x_1574_);
return v___x_1575_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ResolveName_resolveNamespaceUsingOpenDecls(lean_object* v_env_1576_, lean_object* v_n_1577_, lean_object* v_x_1578_){
_start:
{
if (lean_obj_tag(v_x_1578_) == 0)
{
lean_object* v___x_1579_; 
lean_dec(v_n_1577_);
lean_dec_ref(v_env_1576_);
v___x_1579_ = lean_box(0);
return v___x_1579_;
}
else
{
lean_object* v_head_1580_; 
v_head_1580_ = lean_ctor_get(v_x_1578_, 0);
if (lean_obj_tag(v_head_1580_) == 0)
{
lean_object* v_tail_1581_; lean_object* v___x_1583_; uint8_t v_isShared_1584_; uint8_t v_isSharedCheck_1598_; 
lean_inc_ref(v_head_1580_);
v_tail_1581_ = lean_ctor_get(v_x_1578_, 1);
v_isSharedCheck_1598_ = !lean_is_exclusive(v_x_1578_);
if (v_isSharedCheck_1598_ == 0)
{
lean_object* v_unused_1599_; 
v_unused_1599_ = lean_ctor_get(v_x_1578_, 0);
lean_dec(v_unused_1599_);
v___x_1583_ = v_x_1578_;
v_isShared_1584_ = v_isSharedCheck_1598_;
goto v_resetjp_1582_;
}
else
{
lean_inc(v_tail_1581_);
lean_dec(v_x_1578_);
v___x_1583_ = lean_box(0);
v_isShared_1584_ = v_isSharedCheck_1598_;
goto v_resetjp_1582_;
}
v_resetjp_1582_:
{
lean_object* v_ns_1585_; lean_object* v_except_1586_; lean_object* v___x_1587_; uint8_t v___y_1589_; uint8_t v___x_1595_; 
v_ns_1585_ = lean_ctor_get(v_head_1580_, 0);
lean_inc(v_ns_1585_);
v_except_1586_ = lean_ctor_get(v_head_1580_, 1);
lean_inc(v_except_1586_);
lean_dec_ref_known(v_head_1580_, 2);
lean_inc(v_n_1577_);
v___x_1587_ = l_Lean_Name_append(v_ns_1585_, v_n_1577_);
lean_inc_ref(v_env_1576_);
v___x_1595_ = l_Lean_Environment_isNamespace(v_env_1576_, v___x_1587_);
if (v___x_1595_ == 0)
{
lean_dec(v_except_1586_);
v___y_1589_ = v___x_1595_;
goto v___jp_1588_;
}
else
{
uint8_t v___x_1596_; 
v___x_1596_ = l_List_elem___at___00Lean_addAliasEntry_spec__2(v_n_1577_, v_except_1586_);
lean_dec(v_except_1586_);
if (v___x_1596_ == 0)
{
v___y_1589_ = v___x_1595_;
goto v___jp_1588_;
}
else
{
lean_dec(v___x_1587_);
lean_del_object(v___x_1583_);
v_x_1578_ = v_tail_1581_;
goto _start;
}
}
v___jp_1588_:
{
if (v___y_1589_ == 0)
{
lean_dec(v___x_1587_);
lean_del_object(v___x_1583_);
v_x_1578_ = v_tail_1581_;
goto _start;
}
else
{
lean_object* v___x_1591_; lean_object* v___x_1593_; 
v___x_1591_ = l_Lean_ResolveName_resolveNamespaceUsingOpenDecls(v_env_1576_, v_n_1577_, v_tail_1581_);
if (v_isShared_1584_ == 0)
{
lean_ctor_set(v___x_1583_, 1, v___x_1591_);
lean_ctor_set(v___x_1583_, 0, v___x_1587_);
v___x_1593_ = v___x_1583_;
goto v_reusejp_1592_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v___x_1587_);
lean_ctor_set(v_reuseFailAlloc_1594_, 1, v___x_1591_);
v___x_1593_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1592_;
}
v_reusejp_1592_:
{
return v___x_1593_;
}
}
}
}
}
else
{
lean_object* v_tail_1600_; 
v_tail_1600_ = lean_ctor_get(v_x_1578_, 1);
lean_inc(v_tail_1600_);
lean_dec_ref_known(v_x_1578_, 2);
v_x_1578_ = v_tail_1600_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ResolveName_resolveNamespace(lean_object* v_env_1602_, lean_object* v_ns_1603_, lean_object* v_openDecls_1604_, lean_object* v_id_1605_){
_start:
{
lean_object* v___x_1606_; 
lean_inc(v_id_1605_);
lean_inc_ref(v_env_1602_);
v___x_1606_ = l_Lean_ResolveName_resolveNamespaceUsingScope_x3f(v_env_1602_, v_id_1605_, v_ns_1603_);
if (lean_obj_tag(v___x_1606_) == 0)
{
lean_object* v___x_1607_; 
v___x_1607_ = l_Lean_ResolveName_resolveNamespaceUsingOpenDecls(v_env_1602_, v_id_1605_, v_openDecls_1604_);
return v___x_1607_;
}
else
{
lean_object* v_val_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; 
v_val_1608_ = lean_ctor_get(v___x_1606_, 0);
lean_inc(v_val_1608_);
lean_dec_ref_known(v___x_1606_, 1);
v___x_1609_ = l_Lean_ResolveName_resolveNamespaceUsingOpenDecls(v_env_1602_, v_id_1605_, v_openDecls_1604_);
v___x_1610_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1610_, 0, v_val_1608_);
lean_ctor_set(v___x_1610_, 1, v___x_1609_);
return v___x_1610_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadResolveNameOfMonadLift___redArg(lean_object* v_inst_1611_, lean_object* v_inst_1612_){
_start:
{
lean_object* v_getCurrNamespace_1613_; lean_object* v_getOpenDecls_1614_; lean_object* v___x_1616_; uint8_t v_isShared_1617_; uint8_t v_isSharedCheck_1623_; 
v_getCurrNamespace_1613_ = lean_ctor_get(v_inst_1612_, 0);
v_getOpenDecls_1614_ = lean_ctor_get(v_inst_1612_, 1);
v_isSharedCheck_1623_ = !lean_is_exclusive(v_inst_1612_);
if (v_isSharedCheck_1623_ == 0)
{
v___x_1616_ = v_inst_1612_;
v_isShared_1617_ = v_isSharedCheck_1623_;
goto v_resetjp_1615_;
}
else
{
lean_inc(v_getOpenDecls_1614_);
lean_inc(v_getCurrNamespace_1613_);
lean_dec(v_inst_1612_);
v___x_1616_ = lean_box(0);
v_isShared_1617_ = v_isSharedCheck_1623_;
goto v_resetjp_1615_;
}
v_resetjp_1615_:
{
lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1621_; 
lean_inc(v_inst_1611_);
v___x_1618_ = lean_apply_2(v_inst_1611_, lean_box(0), v_getCurrNamespace_1613_);
v___x_1619_ = lean_apply_2(v_inst_1611_, lean_box(0), v_getOpenDecls_1614_);
if (v_isShared_1617_ == 0)
{
lean_ctor_set(v___x_1616_, 1, v___x_1619_);
lean_ctor_set(v___x_1616_, 0, v___x_1618_);
v___x_1621_ = v___x_1616_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1622_; 
v_reuseFailAlloc_1622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1622_, 0, v___x_1618_);
lean_ctor_set(v_reuseFailAlloc_1622_, 1, v___x_1619_);
v___x_1621_ = v_reuseFailAlloc_1622_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
return v___x_1621_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadResolveNameOfMonadLift(lean_object* v_m_1624_, lean_object* v_n_1625_, lean_object* v_inst_1626_, lean_object* v_inst_1627_){
_start:
{
lean_object* v___x_1628_; 
v___x_1628_ = l_Lean_instMonadResolveNameOfMonadLift___redArg(v_inst_1626_, v_inst_1627_);
return v___x_1628_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1630_; lean_object* v___x_1631_; 
v___x_1630_ = ((lean_object*)(l_Lean_checkPrivateInPublic___redArg___lam__0___closed__0));
v___x_1631_ = l_Lean_stringToMessageData(v___x_1630_);
return v___x_1631_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1633_; lean_object* v___x_1634_; 
v___x_1633_ = ((lean_object*)(l_Lean_checkPrivateInPublic___redArg___lam__0___closed__2));
v___x_1634_ = l_Lean_stringToMessageData(v___x_1633_);
return v___x_1634_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___redArg___lam__0(lean_object* v_____do__lift_1635_, lean_object* v_toApplicative_1636_, lean_object* v_id_1637_, lean_object* v_inst_1638_, lean_object* v_inst_1639_, lean_object* v_inst_1640_, lean_object* v_inst_1641_, uint8_t v_____do__lift_1642_){
_start:
{
uint8_t v_isExporting_1647_; 
v_isExporting_1647_ = lean_ctor_get_uint8(v_____do__lift_1635_, sizeof(void*)*8);
if (v_isExporting_1647_ == 0)
{
lean_dec(v_inst_1641_);
lean_dec(v_inst_1640_);
lean_dec_ref(v_inst_1639_);
lean_dec_ref(v_inst_1638_);
lean_dec(v_id_1637_);
goto v___jp_1643_;
}
else
{
uint8_t v___x_1648_; 
v___x_1648_ = l_Lean_isPrivateName(v_id_1637_);
if (v___x_1648_ == 0)
{
lean_dec(v_inst_1641_);
lean_dec(v_inst_1640_);
lean_dec_ref(v_inst_1639_);
lean_dec_ref(v_inst_1638_);
lean_dec(v_id_1637_);
goto v___jp_1643_;
}
else
{
if (v_____do__lift_1642_ == 0)
{
lean_dec(v_inst_1641_);
lean_dec(v_inst_1640_);
lean_dec_ref(v_inst_1639_);
lean_dec_ref(v_inst_1638_);
lean_dec(v_id_1637_);
goto v___jp_1643_;
}
else
{
lean_object* v___x_1649_; uint8_t v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; 
lean_dec_ref(v_toApplicative_1636_);
v___x_1649_ = lean_obj_once(&l_Lean_checkPrivateInPublic___redArg___lam__0___closed__1, &l_Lean_checkPrivateInPublic___redArg___lam__0___closed__1_once, _init_l_Lean_checkPrivateInPublic___redArg___lam__0___closed__1);
v___x_1650_ = 0;
v___x_1651_ = l_Lean_MessageData_ofConstName(v_id_1637_, v___x_1650_);
v___x_1652_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1652_, 0, v___x_1649_);
lean_ctor_set(v___x_1652_, 1, v___x_1651_);
v___x_1653_ = lean_obj_once(&l_Lean_checkPrivateInPublic___redArg___lam__0___closed__3, &l_Lean_checkPrivateInPublic___redArg___lam__0___closed__3_once, _init_l_Lean_checkPrivateInPublic___redArg___lam__0___closed__3);
v___x_1654_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1654_, 0, v___x_1652_);
lean_ctor_set(v___x_1654_, 1, v___x_1653_);
v___x_1655_ = l_Lean_logWarning___redArg(v_inst_1638_, v_inst_1639_, v_inst_1640_, v_inst_1641_, v___x_1654_);
return v___x_1655_;
}
}
}
v___jp_1643_:
{
lean_object* v_toPure_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; 
v_toPure_1644_ = lean_ctor_get(v_toApplicative_1636_, 1);
lean_inc(v_toPure_1644_);
lean_dec_ref(v_toApplicative_1636_);
v___x_1645_ = lean_box(0);
v___x_1646_ = lean_apply_2(v_toPure_1644_, lean_box(0), v___x_1645_);
return v___x_1646_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___redArg___lam__0___boxed(lean_object* v_____do__lift_1656_, lean_object* v_toApplicative_1657_, lean_object* v_id_1658_, lean_object* v_inst_1659_, lean_object* v_inst_1660_, lean_object* v_inst_1661_, lean_object* v_inst_1662_, lean_object* v_____do__lift_1663_){
_start:
{
uint8_t v_____do__lift_231__boxed_1664_; lean_object* v_res_1665_; 
v_____do__lift_231__boxed_1664_ = lean_unbox(v_____do__lift_1663_);
v_res_1665_ = l_Lean_checkPrivateInPublic___redArg___lam__0(v_____do__lift_1656_, v_toApplicative_1657_, v_id_1658_, v_inst_1659_, v_inst_1660_, v_inst_1661_, v_inst_1662_, v_____do__lift_231__boxed_1664_);
lean_dec_ref(v_____do__lift_1656_);
return v_res_1665_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___redArg___lam__1(lean_object* v_toApplicative_1666_, lean_object* v_id_1667_, lean_object* v_inst_1668_, lean_object* v_inst_1669_, lean_object* v_inst_1670_, lean_object* v_inst_1671_, lean_object* v___x_1672_, lean_object* v_toBind_1673_, lean_object* v_____do__lift_1674_){
_start:
{
lean_object* v___f_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; 
lean_inc(v_inst_1671_);
lean_inc_ref(v_inst_1668_);
v___f_1675_ = lean_alloc_closure((void*)(l_Lean_checkPrivateInPublic___redArg___lam__0___boxed), 8, 7);
lean_closure_set(v___f_1675_, 0, v_____do__lift_1674_);
lean_closure_set(v___f_1675_, 1, v_toApplicative_1666_);
lean_closure_set(v___f_1675_, 2, v_id_1667_);
lean_closure_set(v___f_1675_, 3, v_inst_1668_);
lean_closure_set(v___f_1675_, 4, v_inst_1669_);
lean_closure_set(v___f_1675_, 5, v_inst_1670_);
lean_closure_set(v___f_1675_, 6, v_inst_1671_);
v___x_1676_ = l_Lean_ResolveName_backward_privateInPublic_warn;
v___x_1677_ = l_Lean_Option_getM___redArg(v_inst_1668_, v_inst_1671_, v___x_1672_, v___x_1676_);
v___x_1678_ = lean_apply_4(v_toBind_1673_, lean_box(0), lean_box(0), v___x_1677_, v___f_1675_);
return v___x_1678_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___redArg(lean_object* v_inst_1679_, lean_object* v_inst_1680_, lean_object* v_inst_1681_, lean_object* v_inst_1682_, lean_object* v_inst_1683_, lean_object* v_id_1684_){
_start:
{
lean_object* v___x_1685_; lean_object* v_toApplicative_1686_; lean_object* v_toBind_1687_; lean_object* v_getEnv_1688_; lean_object* v___f_1689_; lean_object* v___x_1690_; 
v___x_1685_ = l_Lean_KVMap_instValueBool;
v_toApplicative_1686_ = lean_ctor_get(v_inst_1679_, 0);
lean_inc_ref(v_toApplicative_1686_);
v_toBind_1687_ = lean_ctor_get(v_inst_1679_, 1);
lean_inc_n(v_toBind_1687_, 2);
v_getEnv_1688_ = lean_ctor_get(v_inst_1680_, 0);
lean_inc(v_getEnv_1688_);
lean_dec_ref(v_inst_1680_);
v___f_1689_ = lean_alloc_closure((void*)(l_Lean_checkPrivateInPublic___redArg___lam__1), 9, 8);
lean_closure_set(v___f_1689_, 0, v_toApplicative_1686_);
lean_closure_set(v___f_1689_, 1, v_id_1684_);
lean_closure_set(v___f_1689_, 2, v_inst_1679_);
lean_closure_set(v___f_1689_, 3, v_inst_1682_);
lean_closure_set(v___f_1689_, 4, v_inst_1683_);
lean_closure_set(v___f_1689_, 5, v_inst_1681_);
lean_closure_set(v___f_1689_, 6, v___x_1685_);
lean_closure_set(v___f_1689_, 7, v_toBind_1687_);
v___x_1690_ = lean_apply_4(v_toBind_1687_, lean_box(0), lean_box(0), v_getEnv_1688_, v___f_1689_);
return v___x_1690_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic(lean_object* v_m_1691_, lean_object* v_inst_1692_, lean_object* v_inst_1693_, lean_object* v_inst_1694_, lean_object* v_inst_1695_, lean_object* v_inst_1696_, lean_object* v_id_1697_){
_start:
{
lean_object* v___x_1698_; 
v___x_1698_ = l_Lean_checkPrivateInPublic___redArg(v_inst_1692_, v_inst_1693_, v_inst_1694_, v_inst_1695_, v_inst_1696_, v_id_1697_);
return v___x_1698_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg___lam__0(lean_object* v_env_1699_, lean_object* v_n_1700_, lean_object* v_toApplicative_1701_, uint8_t v___y_1702_, uint8_t v___x_1703_, lean_object* v_____r_1704_){
_start:
{
lean_object* v___x_1705_; 
v___x_1705_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1699_, v_n_1700_);
if (lean_obj_tag(v___x_1705_) == 0)
{
lean_object* v_toPure_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; 
v_toPure_1706_ = lean_ctor_get(v_toApplicative_1701_, 1);
lean_inc(v_toPure_1706_);
lean_dec_ref(v_toApplicative_1701_);
v___x_1707_ = lean_box(v___y_1702_);
v___x_1708_ = lean_apply_2(v_toPure_1706_, lean_box(0), v___x_1707_);
return v___x_1708_;
}
else
{
lean_object* v_val_1709_; lean_object* v_toPure_1710_; lean_object* v___x_1711_; uint8_t v_isModule_1712_; 
v_val_1709_ = lean_ctor_get(v___x_1705_, 0);
lean_inc(v_val_1709_);
lean_dec_ref_known(v___x_1705_, 1);
v_toPure_1710_ = lean_ctor_get(v_toApplicative_1701_, 1);
lean_inc(v_toPure_1710_);
lean_dec_ref(v_toApplicative_1701_);
v___x_1711_ = l_Lean_Environment_header(v_env_1699_);
v_isModule_1712_ = lean_ctor_get_uint8(v___x_1711_, sizeof(void*)*7 + 4);
if (v_isModule_1712_ == 0)
{
lean_object* v___x_1713_; lean_object* v___x_1714_; 
lean_dec_ref(v___x_1711_);
lean_dec(v_val_1709_);
v___x_1713_ = lean_box(v___x_1703_);
v___x_1714_ = lean_apply_2(v_toPure_1710_, lean_box(0), v___x_1713_);
return v___x_1714_;
}
else
{
lean_object* v_modules_1715_; lean_object* v___x_1716_; uint8_t v___x_1717_; 
v_modules_1715_ = lean_ctor_get(v___x_1711_, 3);
lean_inc_ref(v_modules_1715_);
lean_dec_ref(v___x_1711_);
v___x_1716_ = lean_array_get_size(v_modules_1715_);
v___x_1717_ = lean_nat_dec_lt(v_val_1709_, v___x_1716_);
if (v___x_1717_ == 0)
{
lean_object* v___x_1718_; lean_object* v___x_1719_; 
lean_dec_ref(v_modules_1715_);
lean_dec(v_val_1709_);
v___x_1718_ = lean_box(v_isModule_1712_);
v___x_1719_ = lean_apply_2(v_toPure_1710_, lean_box(0), v___x_1718_);
return v___x_1719_;
}
else
{
lean_object* v___x_1720_; lean_object* v_toImport_1721_; uint8_t v_importAll_1722_; 
v___x_1720_ = lean_array_fget(v_modules_1715_, v_val_1709_);
lean_dec(v_val_1709_);
lean_dec_ref(v_modules_1715_);
v_toImport_1721_ = lean_ctor_get(v___x_1720_, 0);
lean_inc_ref(v_toImport_1721_);
lean_dec(v___x_1720_);
v_importAll_1722_ = lean_ctor_get_uint8(v_toImport_1721_, sizeof(void*)*1);
lean_dec_ref(v_toImport_1721_);
if (v_importAll_1722_ == 0)
{
lean_object* v___x_1723_; lean_object* v___x_1724_; 
v___x_1723_ = lean_box(v_isModule_1712_);
v___x_1724_ = lean_apply_2(v_toPure_1710_, lean_box(0), v___x_1723_);
return v___x_1724_;
}
else
{
lean_object* v___x_1725_; lean_object* v___x_1726_; 
v___x_1725_ = lean_box(v___y_1702_);
v___x_1726_ = lean_apply_2(v_toPure_1710_, lean_box(0), v___x_1725_);
return v___x_1726_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg___lam__0___boxed(lean_object* v_env_1727_, lean_object* v_n_1728_, lean_object* v_toApplicative_1729_, lean_object* v___y_1730_, lean_object* v___x_1731_, lean_object* v_____r_1732_){
_start:
{
uint8_t v___y_758__boxed_1733_; uint8_t v___x_759__boxed_1734_; lean_object* v_res_1735_; 
v___y_758__boxed_1733_ = lean_unbox(v___y_1730_);
v___x_759__boxed_1734_ = lean_unbox(v___x_1731_);
v_res_1735_ = l_Lean_isInaccessiblePrivateName___redArg___lam__0(v_env_1727_, v_n_1728_, v_toApplicative_1729_, v___y_758__boxed_1733_, v___x_759__boxed_1734_, v_____r_1732_);
lean_dec(v_n_1728_);
lean_dec_ref(v_env_1727_);
return v_res_1735_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg___lam__1(lean_object* v_env_1736_, lean_object* v_n_1737_, lean_object* v_toApplicative_1738_, uint8_t v___x_1739_, lean_object* v_inst_1740_, lean_object* v_inst_1741_, lean_object* v_inst_1742_, lean_object* v_inst_1743_, lean_object* v_inst_1744_, lean_object* v_toBind_1745_, uint8_t v___x_1746_, uint8_t v_____do__lift_1747_){
_start:
{
uint8_t v___y_1749_; uint8_t v_isExporting_1755_; 
v_isExporting_1755_ = lean_ctor_get_uint8(v_env_1736_, sizeof(void*)*8);
if (v_isExporting_1755_ == 0)
{
v___y_1749_ = v_isExporting_1755_;
goto v___jp_1748_;
}
else
{
if (v_____do__lift_1747_ == 0)
{
lean_object* v_toPure_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; 
lean_dec(v_toBind_1745_);
lean_dec(v_inst_1744_);
lean_dec_ref(v_inst_1743_);
lean_dec(v_inst_1742_);
lean_dec_ref(v_inst_1741_);
lean_dec_ref(v_inst_1740_);
lean_dec(v_n_1737_);
lean_dec_ref(v_env_1736_);
v_toPure_1756_ = lean_ctor_get(v_toApplicative_1738_, 1);
lean_inc(v_toPure_1756_);
lean_dec_ref(v_toApplicative_1738_);
v___x_1757_ = lean_box(v___x_1739_);
v___x_1758_ = lean_apply_2(v_toPure_1756_, lean_box(0), v___x_1757_);
return v___x_1758_;
}
else
{
v___y_1749_ = v___x_1746_;
goto v___jp_1748_;
}
}
v___jp_1748_:
{
lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___f_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; 
v___x_1750_ = lean_box(v___y_1749_);
v___x_1751_ = lean_box(v___x_1739_);
lean_inc(v_n_1737_);
v___f_1752_ = lean_alloc_closure((void*)(l_Lean_isInaccessiblePrivateName___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1752_, 0, v_env_1736_);
lean_closure_set(v___f_1752_, 1, v_n_1737_);
lean_closure_set(v___f_1752_, 2, v_toApplicative_1738_);
lean_closure_set(v___f_1752_, 3, v___x_1750_);
lean_closure_set(v___f_1752_, 4, v___x_1751_);
v___x_1753_ = l_Lean_checkPrivateInPublic___redArg(v_inst_1740_, v_inst_1741_, v_inst_1742_, v_inst_1743_, v_inst_1744_, v_n_1737_);
v___x_1754_ = lean_apply_4(v_toBind_1745_, lean_box(0), lean_box(0), v___x_1753_, v___f_1752_);
return v___x_1754_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg___lam__1___boxed(lean_object* v_env_1759_, lean_object* v_n_1760_, lean_object* v_toApplicative_1761_, lean_object* v___x_1762_, lean_object* v_inst_1763_, lean_object* v_inst_1764_, lean_object* v_inst_1765_, lean_object* v_inst_1766_, lean_object* v_inst_1767_, lean_object* v_toBind_1768_, lean_object* v___x_1769_, lean_object* v_____do__lift_1770_){
_start:
{
uint8_t v___x_799__boxed_1771_; uint8_t v___x_805__boxed_1772_; uint8_t v_____do__lift_806__boxed_1773_; lean_object* v_res_1774_; 
v___x_799__boxed_1771_ = lean_unbox(v___x_1762_);
v___x_805__boxed_1772_ = lean_unbox(v___x_1769_);
v_____do__lift_806__boxed_1773_ = lean_unbox(v_____do__lift_1770_);
v_res_1774_ = l_Lean_isInaccessiblePrivateName___redArg___lam__1(v_env_1759_, v_n_1760_, v_toApplicative_1761_, v___x_799__boxed_1771_, v_inst_1763_, v_inst_1764_, v_inst_1765_, v_inst_1766_, v_inst_1767_, v_toBind_1768_, v___x_805__boxed_1772_, v_____do__lift_806__boxed_1773_);
return v_res_1774_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg___lam__2(lean_object* v_n_1775_, lean_object* v_toApplicative_1776_, uint8_t v___x_1777_, lean_object* v_inst_1778_, lean_object* v_inst_1779_, lean_object* v_inst_1780_, lean_object* v_inst_1781_, lean_object* v_inst_1782_, lean_object* v_toBind_1783_, uint8_t v___x_1784_, lean_object* v_env_1785_){
_start:
{
lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___f_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; 
v___x_1786_ = lean_box(v___x_1777_);
v___x_1787_ = lean_box(v___x_1784_);
lean_inc(v_toBind_1783_);
lean_inc(v_inst_1780_);
lean_inc_ref(v_inst_1778_);
v___f_1788_ = lean_alloc_closure((void*)(l_Lean_isInaccessiblePrivateName___redArg___lam__1___boxed), 12, 11);
lean_closure_set(v___f_1788_, 0, v_env_1785_);
lean_closure_set(v___f_1788_, 1, v_n_1775_);
lean_closure_set(v___f_1788_, 2, v_toApplicative_1776_);
lean_closure_set(v___f_1788_, 3, v___x_1786_);
lean_closure_set(v___f_1788_, 4, v_inst_1778_);
lean_closure_set(v___f_1788_, 5, v_inst_1779_);
lean_closure_set(v___f_1788_, 6, v_inst_1780_);
lean_closure_set(v___f_1788_, 7, v_inst_1781_);
lean_closure_set(v___f_1788_, 8, v_inst_1782_);
lean_closure_set(v___f_1788_, 9, v_toBind_1783_);
lean_closure_set(v___f_1788_, 10, v___x_1787_);
v___x_1789_ = l_Lean_KVMap_instValueBool;
v___x_1790_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_1791_ = l_Lean_Option_getM___redArg(v_inst_1778_, v_inst_1780_, v___x_1789_, v___x_1790_);
v___x_1792_ = lean_apply_4(v_toBind_1783_, lean_box(0), lean_box(0), v___x_1791_, v___f_1788_);
return v___x_1792_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg___lam__2___boxed(lean_object* v_n_1793_, lean_object* v_toApplicative_1794_, lean_object* v___x_1795_, lean_object* v_inst_1796_, lean_object* v_inst_1797_, lean_object* v_inst_1798_, lean_object* v_inst_1799_, lean_object* v_inst_1800_, lean_object* v_toBind_1801_, lean_object* v___x_1802_, lean_object* v_env_1803_){
_start:
{
uint8_t v___x_841__boxed_1804_; uint8_t v___x_847__boxed_1805_; lean_object* v_res_1806_; 
v___x_841__boxed_1804_ = lean_unbox(v___x_1795_);
v___x_847__boxed_1805_ = lean_unbox(v___x_1802_);
v_res_1806_ = l_Lean_isInaccessiblePrivateName___redArg___lam__2(v_n_1793_, v_toApplicative_1794_, v___x_841__boxed_1804_, v_inst_1796_, v_inst_1797_, v_inst_1798_, v_inst_1799_, v_inst_1800_, v_toBind_1801_, v___x_847__boxed_1805_, v_env_1803_);
return v_res_1806_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg(lean_object* v_inst_1807_, lean_object* v_inst_1808_, lean_object* v_inst_1809_, lean_object* v_inst_1810_, lean_object* v_inst_1811_, lean_object* v_n_1812_){
_start:
{
uint8_t v___x_1813_; 
v___x_1813_ = l_Lean_isPrivateName(v_n_1812_);
if (v___x_1813_ == 0)
{
lean_object* v_toApplicative_1814_; lean_object* v_toPure_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; 
lean_dec(v_n_1812_);
lean_dec(v_inst_1811_);
lean_dec_ref(v_inst_1810_);
lean_dec(v_inst_1808_);
lean_dec_ref(v_inst_1807_);
v_toApplicative_1814_ = lean_ctor_get(v_inst_1809_, 0);
lean_inc_ref(v_toApplicative_1814_);
lean_dec_ref(v_inst_1809_);
v_toPure_1815_ = lean_ctor_get(v_toApplicative_1814_, 1);
lean_inc(v_toPure_1815_);
lean_dec_ref(v_toApplicative_1814_);
v___x_1816_ = lean_box(v___x_1813_);
v___x_1817_ = lean_apply_2(v_toPure_1815_, lean_box(0), v___x_1816_);
return v___x_1817_;
}
else
{
lean_object* v_toApplicative_1818_; lean_object* v_toBind_1819_; lean_object* v_getEnv_1820_; uint8_t v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___f_1824_; lean_object* v___x_1825_; 
v_toApplicative_1818_ = lean_ctor_get(v_inst_1809_, 0);
lean_inc_ref(v_toApplicative_1818_);
v_toBind_1819_ = lean_ctor_get(v_inst_1809_, 1);
lean_inc_n(v_toBind_1819_, 2);
v_getEnv_1820_ = lean_ctor_get(v_inst_1810_, 0);
lean_inc(v_getEnv_1820_);
v___x_1821_ = 0;
v___x_1822_ = lean_box(v___x_1813_);
v___x_1823_ = lean_box(v___x_1821_);
v___f_1824_ = lean_alloc_closure((void*)(l_Lean_isInaccessiblePrivateName___redArg___lam__2___boxed), 11, 10);
lean_closure_set(v___f_1824_, 0, v_n_1812_);
lean_closure_set(v___f_1824_, 1, v_toApplicative_1818_);
lean_closure_set(v___f_1824_, 2, v___x_1822_);
lean_closure_set(v___f_1824_, 3, v_inst_1809_);
lean_closure_set(v___f_1824_, 4, v_inst_1810_);
lean_closure_set(v___f_1824_, 5, v_inst_1811_);
lean_closure_set(v___f_1824_, 6, v_inst_1807_);
lean_closure_set(v___f_1824_, 7, v_inst_1808_);
lean_closure_set(v___f_1824_, 8, v_toBind_1819_);
lean_closure_set(v___f_1824_, 9, v___x_1823_);
v___x_1825_ = lean_apply_4(v_toBind_1819_, lean_box(0), lean_box(0), v_getEnv_1820_, v___f_1824_);
return v___x_1825_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName(lean_object* v_m_1826_, lean_object* v_inst_1827_, lean_object* v_inst_1828_, lean_object* v_inst_1829_, lean_object* v_inst_1830_, lean_object* v_inst_1831_, lean_object* v_n_1832_){
_start:
{
lean_object* v___x_1833_; 
v___x_1833_ = l_Lean_isInaccessiblePrivateName___redArg(v_inst_1827_, v_inst_1828_, v_inst_1829_, v_inst_1830_, v_inst_1831_, v_n_1832_);
return v___x_1833_;
}
}
LEAN_EXPORT uint8_t l_Lean_resolveGlobalName___redArg___lam__0(lean_object* v_x_1834_){
_start:
{
lean_object* v_fst_1835_; uint8_t v___x_1836_; 
v_fst_1835_ = lean_ctor_get(v_x_1834_, 0);
v___x_1836_ = l_Lean_isPrivateName(v_fst_1835_);
return v___x_1836_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__0___boxed(lean_object* v_x_1837_){
_start:
{
uint8_t v_res_1838_; lean_object* v_r_1839_; 
v_res_1838_ = l_Lean_resolveGlobalName___redArg___lam__0(v_x_1837_);
lean_dec_ref(v_x_1837_);
v_r_1839_ = lean_box(v_res_1838_);
return v_r_1839_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__1(lean_object* v_toPure_1840_, lean_object* v_res_1841_, lean_object* v_____r_1842_){
_start:
{
lean_object* v___x_1843_; 
v___x_1843_ = lean_apply_2(v_toPure_1840_, lean_box(0), v_res_1841_);
return v___x_1843_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__2(uint8_t v_enableLog_1844_, lean_object* v_toPure_1845_, lean_object* v_res_1846_, lean_object* v___f_1847_, lean_object* v_inst_1848_, lean_object* v_inst_1849_, lean_object* v_inst_1850_, lean_object* v_inst_1851_, lean_object* v_inst_1852_, lean_object* v_toBind_1853_, lean_object* v___f_1854_, lean_object* v_____do__lift_1855_){
_start:
{
if (v_enableLog_1844_ == 0)
{
lean_object* v___x_1856_; 
lean_dec(v___f_1854_);
lean_dec(v_toBind_1853_);
lean_dec(v_inst_1852_);
lean_dec_ref(v_inst_1851_);
lean_dec(v_inst_1850_);
lean_dec_ref(v_inst_1849_);
lean_dec_ref(v_inst_1848_);
lean_dec_ref(v___f_1847_);
v___x_1856_ = lean_apply_2(v_toPure_1845_, lean_box(0), v_res_1846_);
return v___x_1856_;
}
else
{
uint8_t v_isExporting_1857_; 
v_isExporting_1857_ = lean_ctor_get_uint8(v_____do__lift_1855_, sizeof(void*)*8);
if (v_isExporting_1857_ == 0)
{
lean_object* v___x_1858_; 
lean_dec(v___f_1854_);
lean_dec(v_toBind_1853_);
lean_dec(v_inst_1852_);
lean_dec_ref(v_inst_1851_);
lean_dec(v_inst_1850_);
lean_dec_ref(v_inst_1849_);
lean_dec_ref(v_inst_1848_);
lean_dec_ref(v___f_1847_);
v___x_1858_ = lean_apply_2(v_toPure_1845_, lean_box(0), v_res_1846_);
return v___x_1858_;
}
else
{
lean_object* v___x_1859_; 
lean_inc(v_res_1846_);
v___x_1859_ = l_List_find_x3f___redArg(v___f_1847_, v_res_1846_);
if (lean_obj_tag(v___x_1859_) == 1)
{
lean_object* v_val_1860_; lean_object* v_fst_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; 
lean_dec(v_res_1846_);
lean_dec(v_toPure_1845_);
v_val_1860_ = lean_ctor_get(v___x_1859_, 0);
lean_inc(v_val_1860_);
lean_dec_ref_known(v___x_1859_, 1);
v_fst_1861_ = lean_ctor_get(v_val_1860_, 0);
lean_inc(v_fst_1861_);
lean_dec(v_val_1860_);
v___x_1862_ = l_Lean_checkPrivateInPublic___redArg(v_inst_1848_, v_inst_1849_, v_inst_1850_, v_inst_1851_, v_inst_1852_, v_fst_1861_);
v___x_1863_ = lean_apply_4(v_toBind_1853_, lean_box(0), lean_box(0), v___x_1862_, v___f_1854_);
return v___x_1863_;
}
else
{
lean_object* v___x_1864_; 
lean_dec(v___x_1859_);
lean_dec(v___f_1854_);
lean_dec(v_toBind_1853_);
lean_dec(v_inst_1852_);
lean_dec_ref(v_inst_1851_);
lean_dec(v_inst_1850_);
lean_dec_ref(v_inst_1849_);
lean_dec_ref(v_inst_1848_);
v___x_1864_ = lean_apply_2(v_toPure_1845_, lean_box(0), v_res_1846_);
return v___x_1864_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__2___boxed(lean_object* v_enableLog_1865_, lean_object* v_toPure_1866_, lean_object* v_res_1867_, lean_object* v___f_1868_, lean_object* v_inst_1869_, lean_object* v_inst_1870_, lean_object* v_inst_1871_, lean_object* v_inst_1872_, lean_object* v_inst_1873_, lean_object* v_toBind_1874_, lean_object* v___f_1875_, lean_object* v_____do__lift_1876_){
_start:
{
uint8_t v_enableLog_boxed_1877_; lean_object* v_res_1878_; 
v_enableLog_boxed_1877_ = lean_unbox(v_enableLog_1865_);
v_res_1878_ = l_Lean_resolveGlobalName___redArg___lam__2(v_enableLog_boxed_1877_, v_toPure_1866_, v_res_1867_, v___f_1868_, v_inst_1869_, v_inst_1870_, v_inst_1871_, v_inst_1872_, v_inst_1873_, v_toBind_1874_, v___f_1875_, v_____do__lift_1876_);
lean_dec_ref(v_____do__lift_1876_);
return v_res_1878_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__3(lean_object* v_____do__lift_1879_, lean_object* v_____do__lift_1880_, lean_object* v_____do__lift_1881_, lean_object* v_id_1882_, lean_object* v_toPure_1883_, uint8_t v_enableLog_1884_, lean_object* v___f_1885_, lean_object* v_inst_1886_, lean_object* v_inst_1887_, lean_object* v_inst_1888_, lean_object* v_inst_1889_, lean_object* v_inst_1890_, lean_object* v_toBind_1891_, lean_object* v_getEnv_1892_, lean_object* v_____do__lift_1893_){
_start:
{
lean_object* v_res_1894_; lean_object* v___f_1895_; lean_object* v___x_1896_; lean_object* v___f_1897_; lean_object* v___x_1898_; 
v_res_1894_ = l_Lean_ResolveName_resolveGlobalName(v_____do__lift_1879_, v_____do__lift_1880_, v_____do__lift_1881_, v_____do__lift_1893_, v_id_1882_);
lean_inc(v_res_1894_);
lean_inc(v_toPure_1883_);
v___f_1895_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalName___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1895_, 0, v_toPure_1883_);
lean_closure_set(v___f_1895_, 1, v_res_1894_);
v___x_1896_ = lean_box(v_enableLog_1884_);
lean_inc(v_toBind_1891_);
v___f_1897_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalName___redArg___lam__2___boxed), 12, 11);
lean_closure_set(v___f_1897_, 0, v___x_1896_);
lean_closure_set(v___f_1897_, 1, v_toPure_1883_);
lean_closure_set(v___f_1897_, 2, v_res_1894_);
lean_closure_set(v___f_1897_, 3, v___f_1885_);
lean_closure_set(v___f_1897_, 4, v_inst_1886_);
lean_closure_set(v___f_1897_, 5, v_inst_1887_);
lean_closure_set(v___f_1897_, 6, v_inst_1888_);
lean_closure_set(v___f_1897_, 7, v_inst_1889_);
lean_closure_set(v___f_1897_, 8, v_inst_1890_);
lean_closure_set(v___f_1897_, 9, v_toBind_1891_);
lean_closure_set(v___f_1897_, 10, v___f_1895_);
v___x_1898_ = lean_apply_4(v_toBind_1891_, lean_box(0), lean_box(0), v_getEnv_1892_, v___f_1897_);
return v___x_1898_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__3___boxed(lean_object* v_____do__lift_1899_, lean_object* v_____do__lift_1900_, lean_object* v_____do__lift_1901_, lean_object* v_id_1902_, lean_object* v_toPure_1903_, lean_object* v_enableLog_1904_, lean_object* v___f_1905_, lean_object* v_inst_1906_, lean_object* v_inst_1907_, lean_object* v_inst_1908_, lean_object* v_inst_1909_, lean_object* v_inst_1910_, lean_object* v_toBind_1911_, lean_object* v_getEnv_1912_, lean_object* v_____do__lift_1913_){
_start:
{
uint8_t v_enableLog_boxed_1914_; lean_object* v_res_1915_; 
v_enableLog_boxed_1914_ = lean_unbox(v_enableLog_1904_);
v_res_1915_ = l_Lean_resolveGlobalName___redArg___lam__3(v_____do__lift_1899_, v_____do__lift_1900_, v_____do__lift_1901_, v_id_1902_, v_toPure_1903_, v_enableLog_boxed_1914_, v___f_1905_, v_inst_1906_, v_inst_1907_, v_inst_1908_, v_inst_1909_, v_inst_1910_, v_toBind_1911_, v_getEnv_1912_, v_____do__lift_1913_);
lean_dec_ref(v_____do__lift_1900_);
return v_res_1915_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__4(lean_object* v_____do__lift_1916_, lean_object* v_____do__lift_1917_, lean_object* v_id_1918_, lean_object* v_toPure_1919_, uint8_t v_enableLog_1920_, lean_object* v___f_1921_, lean_object* v_inst_1922_, lean_object* v_inst_1923_, lean_object* v_inst_1924_, lean_object* v_inst_1925_, lean_object* v_inst_1926_, lean_object* v_toBind_1927_, lean_object* v_getEnv_1928_, lean_object* v_getOpenDecls_1929_, lean_object* v_____do__lift_1930_){
_start:
{
lean_object* v___x_1931_; lean_object* v___f_1932_; lean_object* v___x_1933_; 
v___x_1931_ = lean_box(v_enableLog_1920_);
lean_inc(v_toBind_1927_);
v___f_1932_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalName___redArg___lam__3___boxed), 15, 14);
lean_closure_set(v___f_1932_, 0, v_____do__lift_1916_);
lean_closure_set(v___f_1932_, 1, v_____do__lift_1917_);
lean_closure_set(v___f_1932_, 2, v_____do__lift_1930_);
lean_closure_set(v___f_1932_, 3, v_id_1918_);
lean_closure_set(v___f_1932_, 4, v_toPure_1919_);
lean_closure_set(v___f_1932_, 5, v___x_1931_);
lean_closure_set(v___f_1932_, 6, v___f_1921_);
lean_closure_set(v___f_1932_, 7, v_inst_1922_);
lean_closure_set(v___f_1932_, 8, v_inst_1923_);
lean_closure_set(v___f_1932_, 9, v_inst_1924_);
lean_closure_set(v___f_1932_, 10, v_inst_1925_);
lean_closure_set(v___f_1932_, 11, v_inst_1926_);
lean_closure_set(v___f_1932_, 12, v_toBind_1927_);
lean_closure_set(v___f_1932_, 13, v_getEnv_1928_);
v___x_1933_ = lean_apply_4(v_toBind_1927_, lean_box(0), lean_box(0), v_getOpenDecls_1929_, v___f_1932_);
return v___x_1933_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__4___boxed(lean_object* v_____do__lift_1934_, lean_object* v_____do__lift_1935_, lean_object* v_id_1936_, lean_object* v_toPure_1937_, lean_object* v_enableLog_1938_, lean_object* v___f_1939_, lean_object* v_inst_1940_, lean_object* v_inst_1941_, lean_object* v_inst_1942_, lean_object* v_inst_1943_, lean_object* v_inst_1944_, lean_object* v_toBind_1945_, lean_object* v_getEnv_1946_, lean_object* v_getOpenDecls_1947_, lean_object* v_____do__lift_1948_){
_start:
{
uint8_t v_enableLog_boxed_1949_; lean_object* v_res_1950_; 
v_enableLog_boxed_1949_ = lean_unbox(v_enableLog_1938_);
v_res_1950_ = l_Lean_resolveGlobalName___redArg___lam__4(v_____do__lift_1934_, v_____do__lift_1935_, v_id_1936_, v_toPure_1937_, v_enableLog_boxed_1949_, v___f_1939_, v_inst_1940_, v_inst_1941_, v_inst_1942_, v_inst_1943_, v_inst_1944_, v_toBind_1945_, v_getEnv_1946_, v_getOpenDecls_1947_, v_____do__lift_1948_);
return v_res_1950_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__5(lean_object* v_inst_1951_, lean_object* v_____do__lift_1952_, lean_object* v_id_1953_, lean_object* v_toPure_1954_, uint8_t v_enableLog_1955_, lean_object* v___f_1956_, lean_object* v_inst_1957_, lean_object* v_inst_1958_, lean_object* v_inst_1959_, lean_object* v_inst_1960_, lean_object* v_inst_1961_, lean_object* v_toBind_1962_, lean_object* v_getEnv_1963_, lean_object* v_____do__lift_1964_){
_start:
{
lean_object* v_getCurrNamespace_1965_; lean_object* v_getOpenDecls_1966_; lean_object* v___x_1967_; lean_object* v___f_1968_; lean_object* v___x_1969_; 
v_getCurrNamespace_1965_ = lean_ctor_get(v_inst_1951_, 0);
lean_inc(v_getCurrNamespace_1965_);
v_getOpenDecls_1966_ = lean_ctor_get(v_inst_1951_, 1);
lean_inc(v_getOpenDecls_1966_);
lean_dec_ref(v_inst_1951_);
v___x_1967_ = lean_box(v_enableLog_1955_);
lean_inc(v_toBind_1962_);
v___f_1968_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalName___redArg___lam__4___boxed), 15, 14);
lean_closure_set(v___f_1968_, 0, v_____do__lift_1952_);
lean_closure_set(v___f_1968_, 1, v_____do__lift_1964_);
lean_closure_set(v___f_1968_, 2, v_id_1953_);
lean_closure_set(v___f_1968_, 3, v_toPure_1954_);
lean_closure_set(v___f_1968_, 4, v___x_1967_);
lean_closure_set(v___f_1968_, 5, v___f_1956_);
lean_closure_set(v___f_1968_, 6, v_inst_1957_);
lean_closure_set(v___f_1968_, 7, v_inst_1958_);
lean_closure_set(v___f_1968_, 8, v_inst_1959_);
lean_closure_set(v___f_1968_, 9, v_inst_1960_);
lean_closure_set(v___f_1968_, 10, v_inst_1961_);
lean_closure_set(v___f_1968_, 11, v_toBind_1962_);
lean_closure_set(v___f_1968_, 12, v_getEnv_1963_);
lean_closure_set(v___f_1968_, 13, v_getOpenDecls_1966_);
v___x_1969_ = lean_apply_4(v_toBind_1962_, lean_box(0), lean_box(0), v_getCurrNamespace_1965_, v___f_1968_);
return v___x_1969_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__5___boxed(lean_object* v_inst_1970_, lean_object* v_____do__lift_1971_, lean_object* v_id_1972_, lean_object* v_toPure_1973_, lean_object* v_enableLog_1974_, lean_object* v___f_1975_, lean_object* v_inst_1976_, lean_object* v_inst_1977_, lean_object* v_inst_1978_, lean_object* v_inst_1979_, lean_object* v_inst_1980_, lean_object* v_toBind_1981_, lean_object* v_getEnv_1982_, lean_object* v_____do__lift_1983_){
_start:
{
uint8_t v_enableLog_boxed_1984_; lean_object* v_res_1985_; 
v_enableLog_boxed_1984_ = lean_unbox(v_enableLog_1974_);
v_res_1985_ = l_Lean_resolveGlobalName___redArg___lam__5(v_inst_1970_, v_____do__lift_1971_, v_id_1972_, v_toPure_1973_, v_enableLog_boxed_1984_, v___f_1975_, v_inst_1976_, v_inst_1977_, v_inst_1978_, v_inst_1979_, v_inst_1980_, v_toBind_1981_, v_getEnv_1982_, v_____do__lift_1983_);
return v_res_1985_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__6(lean_object* v_inst_1986_, lean_object* v_id_1987_, lean_object* v_toPure_1988_, uint8_t v_enableLog_1989_, lean_object* v___f_1990_, lean_object* v_inst_1991_, lean_object* v_inst_1992_, lean_object* v_inst_1993_, lean_object* v_inst_1994_, lean_object* v_inst_1995_, lean_object* v_toBind_1996_, lean_object* v_getEnv_1997_, lean_object* v_____do__lift_1998_){
_start:
{
lean_object* v___x_1999_; lean_object* v___f_2000_; lean_object* v___x_2001_; 
v___x_1999_ = lean_box(v_enableLog_1989_);
lean_inc(v_toBind_1996_);
lean_inc(v_inst_1993_);
v___f_2000_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalName___redArg___lam__5___boxed), 14, 13);
lean_closure_set(v___f_2000_, 0, v_inst_1986_);
lean_closure_set(v___f_2000_, 1, v_____do__lift_1998_);
lean_closure_set(v___f_2000_, 2, v_id_1987_);
lean_closure_set(v___f_2000_, 3, v_toPure_1988_);
lean_closure_set(v___f_2000_, 4, v___x_1999_);
lean_closure_set(v___f_2000_, 5, v___f_1990_);
lean_closure_set(v___f_2000_, 6, v_inst_1991_);
lean_closure_set(v___f_2000_, 7, v_inst_1992_);
lean_closure_set(v___f_2000_, 8, v_inst_1993_);
lean_closure_set(v___f_2000_, 9, v_inst_1994_);
lean_closure_set(v___f_2000_, 10, v_inst_1995_);
lean_closure_set(v___f_2000_, 11, v_toBind_1996_);
lean_closure_set(v___f_2000_, 12, v_getEnv_1997_);
v___x_2001_ = lean_apply_4(v_toBind_1996_, lean_box(0), lean_box(0), v_inst_1993_, v___f_2000_);
return v___x_2001_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__6___boxed(lean_object* v_inst_2002_, lean_object* v_id_2003_, lean_object* v_toPure_2004_, lean_object* v_enableLog_2005_, lean_object* v___f_2006_, lean_object* v_inst_2007_, lean_object* v_inst_2008_, lean_object* v_inst_2009_, lean_object* v_inst_2010_, lean_object* v_inst_2011_, lean_object* v_toBind_2012_, lean_object* v_getEnv_2013_, lean_object* v_____do__lift_2014_){
_start:
{
uint8_t v_enableLog_boxed_2015_; lean_object* v_res_2016_; 
v_enableLog_boxed_2015_ = lean_unbox(v_enableLog_2005_);
v_res_2016_ = l_Lean_resolveGlobalName___redArg___lam__6(v_inst_2002_, v_id_2003_, v_toPure_2004_, v_enableLog_boxed_2015_, v___f_2006_, v_inst_2007_, v_inst_2008_, v_inst_2009_, v_inst_2010_, v_inst_2011_, v_toBind_2012_, v_getEnv_2013_, v_____do__lift_2014_);
return v_res_2016_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg(lean_object* v_inst_2018_, lean_object* v_inst_2019_, lean_object* v_inst_2020_, lean_object* v_inst_2021_, lean_object* v_inst_2022_, lean_object* v_inst_2023_, lean_object* v_id_2024_, uint8_t v_enableLog_2025_){
_start:
{
lean_object* v_toApplicative_2026_; lean_object* v_toBind_2027_; lean_object* v_getEnv_2028_; lean_object* v_toPure_2029_; lean_object* v___f_2030_; lean_object* v___x_2031_; lean_object* v___f_2032_; lean_object* v___x_2033_; 
v_toApplicative_2026_ = lean_ctor_get(v_inst_2018_, 0);
v_toBind_2027_ = lean_ctor_get(v_inst_2018_, 1);
lean_inc_n(v_toBind_2027_, 2);
v_getEnv_2028_ = lean_ctor_get(v_inst_2020_, 0);
lean_inc_n(v_getEnv_2028_, 2);
v_toPure_2029_ = lean_ctor_get(v_toApplicative_2026_, 1);
lean_inc(v_toPure_2029_);
v___f_2030_ = ((lean_object*)(l_Lean_resolveGlobalName___redArg___closed__0));
v___x_2031_ = lean_box(v_enableLog_2025_);
v___f_2032_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalName___redArg___lam__6___boxed), 13, 12);
lean_closure_set(v___f_2032_, 0, v_inst_2019_);
lean_closure_set(v___f_2032_, 1, v_id_2024_);
lean_closure_set(v___f_2032_, 2, v_toPure_2029_);
lean_closure_set(v___f_2032_, 3, v___x_2031_);
lean_closure_set(v___f_2032_, 4, v___f_2030_);
lean_closure_set(v___f_2032_, 5, v_inst_2018_);
lean_closure_set(v___f_2032_, 6, v_inst_2020_);
lean_closure_set(v___f_2032_, 7, v_inst_2021_);
lean_closure_set(v___f_2032_, 8, v_inst_2022_);
lean_closure_set(v___f_2032_, 9, v_inst_2023_);
lean_closure_set(v___f_2032_, 10, v_toBind_2027_);
lean_closure_set(v___f_2032_, 11, v_getEnv_2028_);
v___x_2033_ = lean_apply_4(v_toBind_2027_, lean_box(0), lean_box(0), v_getEnv_2028_, v___f_2032_);
return v___x_2033_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___boxed(lean_object* v_inst_2034_, lean_object* v_inst_2035_, lean_object* v_inst_2036_, lean_object* v_inst_2037_, lean_object* v_inst_2038_, lean_object* v_inst_2039_, lean_object* v_id_2040_, lean_object* v_enableLog_2041_){
_start:
{
uint8_t v_enableLog_boxed_2042_; lean_object* v_res_2043_; 
v_enableLog_boxed_2042_ = lean_unbox(v_enableLog_2041_);
v_res_2043_ = l_Lean_resolveGlobalName___redArg(v_inst_2034_, v_inst_2035_, v_inst_2036_, v_inst_2037_, v_inst_2038_, v_inst_2039_, v_id_2040_, v_enableLog_boxed_2042_);
return v_res_2043_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName(lean_object* v_m_2044_, lean_object* v_inst_2045_, lean_object* v_inst_2046_, lean_object* v_inst_2047_, lean_object* v_inst_2048_, lean_object* v_inst_2049_, lean_object* v_inst_2050_, lean_object* v_id_2051_, uint8_t v_enableLog_2052_){
_start:
{
lean_object* v___x_2053_; 
v___x_2053_ = l_Lean_resolveGlobalName___redArg(v_inst_2045_, v_inst_2046_, v_inst_2047_, v_inst_2048_, v_inst_2049_, v_inst_2050_, v_id_2051_, v_enableLog_2052_);
return v___x_2053_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___boxed(lean_object* v_m_2054_, lean_object* v_inst_2055_, lean_object* v_inst_2056_, lean_object* v_inst_2057_, lean_object* v_inst_2058_, lean_object* v_inst_2059_, lean_object* v_inst_2060_, lean_object* v_id_2061_, lean_object* v_enableLog_2062_){
_start:
{
uint8_t v_enableLog_boxed_2063_; lean_object* v_res_2064_; 
v_enableLog_boxed_2063_ = lean_unbox(v_enableLog_2062_);
v_res_2064_ = l_Lean_resolveGlobalName(v_m_2054_, v_inst_2055_, v_inst_2056_, v_inst_2057_, v_inst_2058_, v_inst_2059_, v_inst_2060_, v_id_2061_, v_enableLog_boxed_2063_);
return v_res_2064_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__0(lean_object* v_toPure_2065_, lean_object* v_nss_2066_, lean_object* v_____r_2067_){
_start:
{
lean_object* v___x_2068_; 
v___x_2068_ = lean_apply_2(v_toPure_2065_, lean_box(0), v_nss_2066_);
return v___x_2068_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__1(lean_object* v_____do__lift_2071_, lean_object* v_____do__lift_2072_, lean_object* v_id_2073_, uint8_t v_allowEmpty_2074_, lean_object* v_toPure_2075_, lean_object* v_inst_2076_, lean_object* v_inst_2077_, lean_object* v_toBind_2078_, lean_object* v_____do__lift_2079_){
_start:
{
lean_object* v_nss_2080_; 
lean_inc(v_id_2073_);
v_nss_2080_ = l_Lean_ResolveName_resolveNamespace(v_____do__lift_2071_, v_____do__lift_2072_, v_____do__lift_2079_, v_id_2073_);
if (v_allowEmpty_2074_ == 0)
{
uint8_t v___x_2081_; 
v___x_2081_ = l_List_isEmpty___redArg(v_nss_2080_);
if (v___x_2081_ == 0)
{
lean_object* v___x_2082_; 
lean_dec(v_toBind_2078_);
lean_dec_ref(v_inst_2077_);
lean_dec_ref(v_inst_2076_);
lean_dec(v_id_2073_);
v___x_2082_ = lean_apply_2(v_toPure_2075_, lean_box(0), v_nss_2080_);
return v___x_2082_;
}
else
{
lean_object* v___f_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; 
v___f_2083_ = lean_alloc_closure((void*)(l_Lean_resolveNamespaceCore___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2083_, 0, v_toPure_2075_);
lean_closure_set(v___f_2083_, 1, v_nss_2080_);
v___x_2084_ = ((lean_object*)(l_Lean_resolveNamespaceCore___redArg___lam__1___closed__0));
v___x_2085_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_id_2073_, v___x_2081_);
v___x_2086_ = lean_string_append(v___x_2084_, v___x_2085_);
lean_dec_ref(v___x_2085_);
v___x_2087_ = ((lean_object*)(l_Lean_resolveNamespaceCore___redArg___lam__1___closed__1));
v___x_2088_ = lean_string_append(v___x_2086_, v___x_2087_);
v___x_2089_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2089_, 0, v___x_2088_);
v___x_2090_ = l_Lean_MessageData_ofFormat(v___x_2089_);
v___x_2091_ = l_Lean_throwError___redArg(v_inst_2076_, v_inst_2077_, v___x_2090_);
v___x_2092_ = lean_apply_4(v_toBind_2078_, lean_box(0), lean_box(0), v___x_2091_, v___f_2083_);
return v___x_2092_;
}
}
else
{
lean_object* v___x_2093_; 
lean_dec(v_toBind_2078_);
lean_dec_ref(v_inst_2077_);
lean_dec_ref(v_inst_2076_);
lean_dec(v_id_2073_);
v___x_2093_ = lean_apply_2(v_toPure_2075_, lean_box(0), v_nss_2080_);
return v___x_2093_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__1___boxed(lean_object* v_____do__lift_2094_, lean_object* v_____do__lift_2095_, lean_object* v_id_2096_, lean_object* v_allowEmpty_2097_, lean_object* v_toPure_2098_, lean_object* v_inst_2099_, lean_object* v_inst_2100_, lean_object* v_toBind_2101_, lean_object* v_____do__lift_2102_){
_start:
{
uint8_t v_allowEmpty_boxed_2103_; lean_object* v_res_2104_; 
v_allowEmpty_boxed_2103_ = lean_unbox(v_allowEmpty_2097_);
v_res_2104_ = l_Lean_resolveNamespaceCore___redArg___lam__1(v_____do__lift_2094_, v_____do__lift_2095_, v_id_2096_, v_allowEmpty_boxed_2103_, v_toPure_2098_, v_inst_2099_, v_inst_2100_, v_toBind_2101_, v_____do__lift_2102_);
return v_res_2104_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__2(lean_object* v_____do__lift_2105_, lean_object* v_id_2106_, uint8_t v_allowEmpty_2107_, lean_object* v_toPure_2108_, lean_object* v_inst_2109_, lean_object* v_inst_2110_, lean_object* v_toBind_2111_, lean_object* v_getOpenDecls_2112_, lean_object* v_____do__lift_2113_){
_start:
{
lean_object* v___x_2114_; lean_object* v___f_2115_; lean_object* v___x_2116_; 
v___x_2114_ = lean_box(v_allowEmpty_2107_);
lean_inc(v_toBind_2111_);
v___f_2115_ = lean_alloc_closure((void*)(l_Lean_resolveNamespaceCore___redArg___lam__1___boxed), 9, 8);
lean_closure_set(v___f_2115_, 0, v_____do__lift_2105_);
lean_closure_set(v___f_2115_, 1, v_____do__lift_2113_);
lean_closure_set(v___f_2115_, 2, v_id_2106_);
lean_closure_set(v___f_2115_, 3, v___x_2114_);
lean_closure_set(v___f_2115_, 4, v_toPure_2108_);
lean_closure_set(v___f_2115_, 5, v_inst_2109_);
lean_closure_set(v___f_2115_, 6, v_inst_2110_);
lean_closure_set(v___f_2115_, 7, v_toBind_2111_);
v___x_2116_ = lean_apply_4(v_toBind_2111_, lean_box(0), lean_box(0), v_getOpenDecls_2112_, v___f_2115_);
return v___x_2116_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__2___boxed(lean_object* v_____do__lift_2117_, lean_object* v_id_2118_, lean_object* v_allowEmpty_2119_, lean_object* v_toPure_2120_, lean_object* v_inst_2121_, lean_object* v_inst_2122_, lean_object* v_toBind_2123_, lean_object* v_getOpenDecls_2124_, lean_object* v_____do__lift_2125_){
_start:
{
uint8_t v_allowEmpty_boxed_2126_; lean_object* v_res_2127_; 
v_allowEmpty_boxed_2126_ = lean_unbox(v_allowEmpty_2119_);
v_res_2127_ = l_Lean_resolveNamespaceCore___redArg___lam__2(v_____do__lift_2117_, v_id_2118_, v_allowEmpty_boxed_2126_, v_toPure_2120_, v_inst_2121_, v_inst_2122_, v_toBind_2123_, v_getOpenDecls_2124_, v_____do__lift_2125_);
return v_res_2127_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__3(lean_object* v_inst_2128_, lean_object* v_id_2129_, uint8_t v_allowEmpty_2130_, lean_object* v_toPure_2131_, lean_object* v_inst_2132_, lean_object* v_inst_2133_, lean_object* v_toBind_2134_, lean_object* v_____do__lift_2135_){
_start:
{
lean_object* v_getCurrNamespace_2136_; lean_object* v_getOpenDecls_2137_; lean_object* v___x_2138_; lean_object* v___f_2139_; lean_object* v___x_2140_; 
v_getCurrNamespace_2136_ = lean_ctor_get(v_inst_2128_, 0);
lean_inc(v_getCurrNamespace_2136_);
v_getOpenDecls_2137_ = lean_ctor_get(v_inst_2128_, 1);
lean_inc(v_getOpenDecls_2137_);
lean_dec_ref(v_inst_2128_);
v___x_2138_ = lean_box(v_allowEmpty_2130_);
lean_inc(v_toBind_2134_);
v___f_2139_ = lean_alloc_closure((void*)(l_Lean_resolveNamespaceCore___redArg___lam__2___boxed), 9, 8);
lean_closure_set(v___f_2139_, 0, v_____do__lift_2135_);
lean_closure_set(v___f_2139_, 1, v_id_2129_);
lean_closure_set(v___f_2139_, 2, v___x_2138_);
lean_closure_set(v___f_2139_, 3, v_toPure_2131_);
lean_closure_set(v___f_2139_, 4, v_inst_2132_);
lean_closure_set(v___f_2139_, 5, v_inst_2133_);
lean_closure_set(v___f_2139_, 6, v_toBind_2134_);
lean_closure_set(v___f_2139_, 7, v_getOpenDecls_2137_);
v___x_2140_ = lean_apply_4(v_toBind_2134_, lean_box(0), lean_box(0), v_getCurrNamespace_2136_, v___f_2139_);
return v___x_2140_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__3___boxed(lean_object* v_inst_2141_, lean_object* v_id_2142_, lean_object* v_allowEmpty_2143_, lean_object* v_toPure_2144_, lean_object* v_inst_2145_, lean_object* v_inst_2146_, lean_object* v_toBind_2147_, lean_object* v_____do__lift_2148_){
_start:
{
uint8_t v_allowEmpty_boxed_2149_; lean_object* v_res_2150_; 
v_allowEmpty_boxed_2149_ = lean_unbox(v_allowEmpty_2143_);
v_res_2150_ = l_Lean_resolveNamespaceCore___redArg___lam__3(v_inst_2141_, v_id_2142_, v_allowEmpty_boxed_2149_, v_toPure_2144_, v_inst_2145_, v_inst_2146_, v_toBind_2147_, v_____do__lift_2148_);
return v_res_2150_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg(lean_object* v_inst_2151_, lean_object* v_inst_2152_, lean_object* v_inst_2153_, lean_object* v_inst_2154_, lean_object* v_id_2155_, uint8_t v_allowEmpty_2156_){
_start:
{
lean_object* v_toApplicative_2157_; lean_object* v_toBind_2158_; lean_object* v_getEnv_2159_; lean_object* v_toPure_2160_; lean_object* v___x_2161_; lean_object* v___f_2162_; lean_object* v___x_2163_; 
v_toApplicative_2157_ = lean_ctor_get(v_inst_2151_, 0);
v_toBind_2158_ = lean_ctor_get(v_inst_2151_, 1);
lean_inc_n(v_toBind_2158_, 2);
v_getEnv_2159_ = lean_ctor_get(v_inst_2153_, 0);
lean_inc(v_getEnv_2159_);
lean_dec_ref(v_inst_2153_);
v_toPure_2160_ = lean_ctor_get(v_toApplicative_2157_, 1);
lean_inc(v_toPure_2160_);
v___x_2161_ = lean_box(v_allowEmpty_2156_);
v___f_2162_ = lean_alloc_closure((void*)(l_Lean_resolveNamespaceCore___redArg___lam__3___boxed), 8, 7);
lean_closure_set(v___f_2162_, 0, v_inst_2152_);
lean_closure_set(v___f_2162_, 1, v_id_2155_);
lean_closure_set(v___f_2162_, 2, v___x_2161_);
lean_closure_set(v___f_2162_, 3, v_toPure_2160_);
lean_closure_set(v___f_2162_, 4, v_inst_2151_);
lean_closure_set(v___f_2162_, 5, v_inst_2154_);
lean_closure_set(v___f_2162_, 6, v_toBind_2158_);
v___x_2163_ = lean_apply_4(v_toBind_2158_, lean_box(0), lean_box(0), v_getEnv_2159_, v___f_2162_);
return v___x_2163_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___boxed(lean_object* v_inst_2164_, lean_object* v_inst_2165_, lean_object* v_inst_2166_, lean_object* v_inst_2167_, lean_object* v_id_2168_, lean_object* v_allowEmpty_2169_){
_start:
{
uint8_t v_allowEmpty_boxed_2170_; lean_object* v_res_2171_; 
v_allowEmpty_boxed_2170_ = lean_unbox(v_allowEmpty_2169_);
v_res_2171_ = l_Lean_resolveNamespaceCore___redArg(v_inst_2164_, v_inst_2165_, v_inst_2166_, v_inst_2167_, v_id_2168_, v_allowEmpty_boxed_2170_);
return v_res_2171_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore(lean_object* v_m_2172_, lean_object* v_inst_2173_, lean_object* v_inst_2174_, lean_object* v_inst_2175_, lean_object* v_inst_2176_, lean_object* v_id_2177_, uint8_t v_allowEmpty_2178_){
_start:
{
lean_object* v___x_2179_; 
v___x_2179_ = l_Lean_resolveNamespaceCore___redArg(v_inst_2173_, v_inst_2174_, v_inst_2175_, v_inst_2176_, v_id_2177_, v_allowEmpty_2178_);
return v___x_2179_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___boxed(lean_object* v_m_2180_, lean_object* v_inst_2181_, lean_object* v_inst_2182_, lean_object* v_inst_2183_, lean_object* v_inst_2184_, lean_object* v_id_2185_, lean_object* v_allowEmpty_2186_){
_start:
{
uint8_t v_allowEmpty_boxed_2187_; lean_object* v_res_2188_; 
v_allowEmpty_boxed_2187_ = lean_unbox(v_allowEmpty_2186_);
v_res_2188_ = l_Lean_resolveNamespaceCore(v_m_2180_, v_inst_2181_, v_inst_2182_, v_inst_2183_, v_inst_2184_, v_id_2185_, v_allowEmpty_boxed_2187_);
return v_res_2188_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespace___redArg___lam__0(lean_object* v_x_2189_){
_start:
{
if (lean_obj_tag(v_x_2189_) == 0)
{
lean_object* v_ns_2190_; lean_object* v___x_2192_; uint8_t v_isShared_2193_; uint8_t v_isSharedCheck_2197_; 
v_ns_2190_ = lean_ctor_get(v_x_2189_, 0);
v_isSharedCheck_2197_ = !lean_is_exclusive(v_x_2189_);
if (v_isSharedCheck_2197_ == 0)
{
v___x_2192_ = v_x_2189_;
v_isShared_2193_ = v_isSharedCheck_2197_;
goto v_resetjp_2191_;
}
else
{
lean_inc(v_ns_2190_);
lean_dec(v_x_2189_);
v___x_2192_ = lean_box(0);
v_isShared_2193_ = v_isSharedCheck_2197_;
goto v_resetjp_2191_;
}
v_resetjp_2191_:
{
lean_object* v___x_2195_; 
if (v_isShared_2193_ == 0)
{
lean_ctor_set_tag(v___x_2192_, 1);
v___x_2195_ = v___x_2192_;
goto v_reusejp_2194_;
}
else
{
lean_object* v_reuseFailAlloc_2196_; 
v_reuseFailAlloc_2196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2196_, 0, v_ns_2190_);
v___x_2195_ = v_reuseFailAlloc_2196_;
goto v_reusejp_2194_;
}
v_reusejp_2194_:
{
return v___x_2195_;
}
}
}
else
{
lean_object* v___x_2198_; 
lean_dec_ref(v_x_2189_);
v___x_2198_ = lean_box(0);
return v___x_2198_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespace___redArg___lam__1(lean_object* v_x_2199_, lean_object* v_withRef_2200_, lean_object* v___x_2201_, lean_object* v_oldRef_2202_){
_start:
{
lean_object* v_ref_2203_; lean_object* v___x_2204_; 
v_ref_2203_ = l_Lean_replaceRef(v_x_2199_, v_oldRef_2202_);
v___x_2204_ = lean_apply_3(v_withRef_2200_, lean_box(0), v_ref_2203_, v___x_2201_);
return v___x_2204_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespace___redArg___lam__1___boxed(lean_object* v_x_2205_, lean_object* v_withRef_2206_, lean_object* v___x_2207_, lean_object* v_oldRef_2208_){
_start:
{
lean_object* v_res_2209_; 
v_res_2209_ = l_Lean_resolveNamespace___redArg___lam__1(v_x_2205_, v_withRef_2206_, v___x_2207_, v_oldRef_2208_);
lean_dec(v_oldRef_2208_);
lean_dec(v_x_2205_);
return v_res_2209_;
}
}
static lean_object* _init_l_Lean_resolveNamespace___redArg___closed__4(void){
_start:
{
lean_object* v___x_2216_; lean_object* v___x_2217_; 
v___x_2216_ = ((lean_object*)(l_Lean_resolveNamespace___redArg___closed__3));
v___x_2217_ = l_Lean_MessageData_ofFormat(v___x_2216_);
return v___x_2217_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespace___redArg(lean_object* v_inst_2218_, lean_object* v_inst_2219_, lean_object* v_inst_2220_, lean_object* v_inst_2221_, lean_object* v_x_2222_){
_start:
{
if (lean_obj_tag(v_x_2222_) == 3)
{
lean_object* v_val_2223_; lean_object* v_preresolved_2224_; lean_object* v___f_2225_; lean_object* v___x_2226_; lean_object* v_pre_2227_; uint8_t v___x_2228_; 
v_val_2223_ = lean_ctor_get(v_x_2222_, 2);
v_preresolved_2224_ = lean_ctor_get(v_x_2222_, 3);
v___f_2225_ = ((lean_object*)(l_Lean_resolveNamespace___redArg___closed__0));
v___x_2226_ = ((lean_object*)(l_Lean_resolveNamespace___redArg___closed__1));
lean_inc(v_preresolved_2224_);
v_pre_2227_ = l_List_filterMapTR_go___redArg(v___f_2225_, v_preresolved_2224_, v___x_2226_);
v___x_2228_ = l_List_isEmpty___redArg(v_pre_2227_);
if (v___x_2228_ == 0)
{
lean_object* v_toApplicative_2229_; lean_object* v_toPure_2230_; lean_object* v___x_2231_; 
lean_dec_ref_known(v_x_2222_, 4);
lean_dec_ref(v_inst_2221_);
lean_dec_ref(v_inst_2220_);
lean_dec_ref(v_inst_2219_);
v_toApplicative_2229_ = lean_ctor_get(v_inst_2218_, 0);
lean_inc_ref(v_toApplicative_2229_);
lean_dec_ref(v_inst_2218_);
v_toPure_2230_ = lean_ctor_get(v_toApplicative_2229_, 1);
lean_inc(v_toPure_2230_);
lean_dec_ref(v_toApplicative_2229_);
v___x_2231_ = lean_apply_2(v_toPure_2230_, lean_box(0), v_pre_2227_);
return v___x_2231_;
}
else
{
lean_object* v_toMonadRef_2232_; lean_object* v_toBind_2233_; lean_object* v_getRef_2234_; lean_object* v_withRef_2235_; uint8_t v___x_2236_; lean_object* v___x_2237_; lean_object* v___f_2238_; lean_object* v___x_2239_; 
lean_dec(v_pre_2227_);
v_toMonadRef_2232_ = lean_ctor_get(v_inst_2221_, 1);
v_toBind_2233_ = lean_ctor_get(v_inst_2218_, 1);
lean_inc(v_toBind_2233_);
v_getRef_2234_ = lean_ctor_get(v_toMonadRef_2232_, 0);
lean_inc(v_getRef_2234_);
v_withRef_2235_ = lean_ctor_get(v_toMonadRef_2232_, 1);
lean_inc(v_withRef_2235_);
v___x_2236_ = 0;
lean_inc(v_val_2223_);
v___x_2237_ = l_Lean_resolveNamespaceCore___redArg(v_inst_2218_, v_inst_2219_, v_inst_2220_, v_inst_2221_, v_val_2223_, v___x_2236_);
v___f_2238_ = lean_alloc_closure((void*)(l_Lean_resolveNamespace___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_2238_, 0, v_x_2222_);
lean_closure_set(v___f_2238_, 1, v_withRef_2235_);
lean_closure_set(v___f_2238_, 2, v___x_2237_);
v___x_2239_ = lean_apply_4(v_toBind_2233_, lean_box(0), lean_box(0), v_getRef_2234_, v___f_2238_);
return v___x_2239_;
}
}
else
{
lean_object* v___x_2240_; lean_object* v___x_2241_; 
lean_dec_ref(v_inst_2220_);
lean_dec_ref(v_inst_2219_);
v___x_2240_ = lean_obj_once(&l_Lean_resolveNamespace___redArg___closed__4, &l_Lean_resolveNamespace___redArg___closed__4_once, _init_l_Lean_resolveNamespace___redArg___closed__4);
v___x_2241_ = l_Lean_throwErrorAt___redArg(v_inst_2218_, v_inst_2221_, v_x_2222_, v___x_2240_);
return v___x_2241_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespace(lean_object* v_m_2242_, lean_object* v_inst_2243_, lean_object* v_inst_2244_, lean_object* v_inst_2245_, lean_object* v_inst_2246_, lean_object* v_x_2247_){
_start:
{
lean_object* v___x_2248_; 
v___x_2248_ = l_Lean_resolveNamespace___redArg(v_inst_2243_, v_inst_2244_, v_inst_2245_, v_inst_2246_, v_x_2247_);
return v___x_2248_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveUniqueNamespace___redArg___lam__0(lean_object* v_id_2251_, lean_object* v___f_2252_, lean_object* v_inst_2253_, lean_object* v_inst_2254_, lean_object* v_toPure_2255_, lean_object* v_____do__lift_2256_){
_start:
{
if (lean_obj_tag(v_____do__lift_2256_) == 1)
{
lean_object* v_tail_2272_; 
v_tail_2272_ = lean_ctor_get(v_____do__lift_2256_, 1);
if (lean_obj_tag(v_tail_2272_) == 0)
{
lean_object* v_head_2273_; lean_object* v___x_2274_; 
lean_dec_ref(v_inst_2254_);
lean_dec_ref(v_inst_2253_);
lean_dec_ref(v___f_2252_);
v_head_2273_ = lean_ctor_get(v_____do__lift_2256_, 0);
lean_inc(v_head_2273_);
lean_dec_ref_known(v_____do__lift_2256_, 2);
v___x_2274_ = lean_apply_2(v_toPure_2255_, lean_box(0), v_head_2273_);
return v___x_2274_;
}
else
{
lean_dec(v_toPure_2255_);
goto v___jp_2257_;
}
}
else
{
lean_dec(v_toPure_2255_);
goto v___jp_2257_;
}
v___jp_2257_:
{
lean_object* v___x_2258_; lean_object* v___x_2259_; uint8_t v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; 
v___x_2258_ = ((lean_object*)(l_Lean_resolveUniqueNamespace___redArg___lam__0___closed__0));
v___x_2259_ = l_Lean_TSyntax_getId(v_id_2251_);
v___x_2260_ = 1;
v___x_2261_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2259_, v___x_2260_);
v___x_2262_ = lean_string_append(v___x_2258_, v___x_2261_);
lean_dec_ref(v___x_2261_);
v___x_2263_ = ((lean_object*)(l_Lean_resolveUniqueNamespace___redArg___lam__0___closed__1));
v___x_2264_ = lean_string_append(v___x_2262_, v___x_2263_);
v___x_2265_ = l_List_toString___redArg(v___f_2252_, v_____do__lift_2256_);
v___x_2266_ = lean_string_append(v___x_2264_, v___x_2265_);
lean_dec_ref(v___x_2265_);
v___x_2267_ = ((lean_object*)(l_Lean_resolveNamespaceCore___redArg___lam__1___closed__1));
v___x_2268_ = lean_string_append(v___x_2266_, v___x_2267_);
v___x_2269_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2269_, 0, v___x_2268_);
v___x_2270_ = l_Lean_MessageData_ofFormat(v___x_2269_);
v___x_2271_ = l_Lean_throwError___redArg(v_inst_2253_, v_inst_2254_, v___x_2270_);
return v___x_2271_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveUniqueNamespace___redArg___lam__0___boxed(lean_object* v_id_2275_, lean_object* v___f_2276_, lean_object* v_inst_2277_, lean_object* v_inst_2278_, lean_object* v_toPure_2279_, lean_object* v_____do__lift_2280_){
_start:
{
lean_object* v_res_2281_; 
v_res_2281_ = l_Lean_resolveUniqueNamespace___redArg___lam__0(v_id_2275_, v___f_2276_, v_inst_2277_, v_inst_2278_, v_toPure_2279_, v_____do__lift_2280_);
lean_dec(v_id_2275_);
return v_res_2281_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveUniqueNamespace___redArg(lean_object* v_inst_2283_, lean_object* v_inst_2284_, lean_object* v_inst_2285_, lean_object* v_inst_2286_, lean_object* v_id_2287_){
_start:
{
lean_object* v_toApplicative_2288_; lean_object* v_toBind_2289_; lean_object* v_toPure_2290_; lean_object* v___f_2291_; lean_object* v___x_2292_; lean_object* v___f_2293_; lean_object* v___x_2294_; 
v_toApplicative_2288_ = lean_ctor_get(v_inst_2283_, 0);
v_toBind_2289_ = lean_ctor_get(v_inst_2283_, 1);
lean_inc(v_toBind_2289_);
v_toPure_2290_ = lean_ctor_get(v_toApplicative_2288_, 1);
lean_inc(v_toPure_2290_);
v___f_2291_ = ((lean_object*)(l_Lean_resolveUniqueNamespace___redArg___closed__0));
lean_inc(v_id_2287_);
lean_inc_ref(v_inst_2286_);
lean_inc_ref(v_inst_2283_);
v___x_2292_ = l_Lean_resolveNamespace___redArg(v_inst_2283_, v_inst_2284_, v_inst_2285_, v_inst_2286_, v_id_2287_);
v___f_2293_ = lean_alloc_closure((void*)(l_Lean_resolveUniqueNamespace___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_2293_, 0, v_id_2287_);
lean_closure_set(v___f_2293_, 1, v___f_2291_);
lean_closure_set(v___f_2293_, 2, v_inst_2283_);
lean_closure_set(v___f_2293_, 3, v_inst_2286_);
lean_closure_set(v___f_2293_, 4, v_toPure_2290_);
v___x_2294_ = lean_apply_4(v_toBind_2289_, lean_box(0), lean_box(0), v___x_2292_, v___f_2293_);
return v___x_2294_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveUniqueNamespace(lean_object* v_m_2295_, lean_object* v_inst_2296_, lean_object* v_inst_2297_, lean_object* v_inst_2298_, lean_object* v_inst_2299_, lean_object* v_id_2300_){
_start:
{
lean_object* v___x_2301_; 
v___x_2301_ = l_Lean_resolveUniqueNamespace___redArg(v_inst_2296_, v_inst_2297_, v_inst_2298_, v_inst_2299_, v_id_2300_);
return v___x_2301_;
}
}
LEAN_EXPORT uint8_t l_Lean_filterFieldList___redArg___lam__0(lean_object* v_x_2302_){
_start:
{
lean_object* v_snd_2303_; uint8_t v___x_2304_; 
v_snd_2303_ = lean_ctor_get(v_x_2302_, 1);
v___x_2304_ = l_List_isEmpty___redArg(v_snd_2303_);
return v___x_2304_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg___lam__0___boxed(lean_object* v_x_2305_){
_start:
{
uint8_t v_res_2306_; lean_object* v_r_2307_; 
v_res_2306_ = l_Lean_filterFieldList___redArg___lam__0(v_x_2305_);
lean_dec_ref(v_x_2305_);
v_r_2307_ = lean_box(v_res_2306_);
return v_r_2307_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg___lam__1(lean_object* v_x_2308_){
_start:
{
lean_object* v_fst_2309_; 
v_fst_2309_ = lean_ctor_get(v_x_2308_, 0);
lean_inc(v_fst_2309_);
return v_fst_2309_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg___lam__1___boxed(lean_object* v_x_2310_){
_start:
{
lean_object* v_res_2311_; 
v_res_2311_ = l_Lean_filterFieldList___redArg___lam__1(v_x_2310_);
lean_dec_ref(v_x_2310_);
return v_res_2311_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg___lam__2(lean_object* v___f_2312_, lean_object* v_cs_2313_, lean_object* v_toPure_2314_, lean_object* v_____r_2315_){
_start:
{
lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; 
v___x_2316_ = lean_box(0);
v___x_2317_ = l_List_mapTR_loop___redArg(v___f_2312_, v_cs_2313_, v___x_2316_);
v___x_2318_ = lean_apply_2(v_toPure_2314_, lean_box(0), v___x_2317_);
return v___x_2318_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg___lam__3(lean_object* v___f_2319_, lean_object* v_____r_2320_){
_start:
{
lean_object* v___x_2321_; 
v___x_2321_ = lean_apply_1(v___f_2319_, v_____r_2320_);
return v___x_2321_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg___lam__4(lean_object* v_inst_2322_, lean_object* v_inst_2323_, lean_object* v_inst_2324_, lean_object* v_n_2325_, lean_object* v_toBind_2326_, lean_object* v___f_2327_, lean_object* v_____do__lift_2328_){
_start:
{
lean_object* v___x_2329_; lean_object* v___x_2330_; 
v___x_2329_ = l_Lean_throwUnknownConstantAt___redArg(v_inst_2322_, v_inst_2323_, v_inst_2324_, v_____do__lift_2328_, v_n_2325_);
v___x_2330_ = lean_apply_4(v_toBind_2326_, lean_box(0), lean_box(0), v___x_2329_, v___f_2327_);
return v___x_2330_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg(lean_object* v_inst_2333_, lean_object* v_inst_2334_, lean_object* v_inst_2335_, lean_object* v_n_2336_, lean_object* v_cs_2337_){
_start:
{
lean_object* v_toApplicative_2338_; lean_object* v_toBind_2339_; lean_object* v_toPure_2340_; lean_object* v___f_2341_; lean_object* v___f_2342_; lean_object* v___x_2343_; lean_object* v_cs_2344_; lean_object* v___f_2345_; uint8_t v___x_2346_; 
v_toApplicative_2338_ = lean_ctor_get(v_inst_2333_, 0);
v_toBind_2339_ = lean_ctor_get(v_inst_2333_, 1);
lean_inc(v_toBind_2339_);
v_toPure_2340_ = lean_ctor_get(v_toApplicative_2338_, 1);
v___f_2341_ = ((lean_object*)(l_Lean_filterFieldList___redArg___closed__0));
v___f_2342_ = ((lean_object*)(l_Lean_filterFieldList___redArg___closed__1));
v___x_2343_ = lean_box(0);
v_cs_2344_ = l_List_filterTR_loop___redArg(v___f_2341_, v_cs_2337_, v___x_2343_);
lean_inc(v_toPure_2340_);
lean_inc(v_cs_2344_);
v___f_2345_ = lean_alloc_closure((void*)(l_Lean_filterFieldList___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2345_, 0, v___f_2342_);
lean_closure_set(v___f_2345_, 1, v_cs_2344_);
lean_closure_set(v___f_2345_, 2, v_toPure_2340_);
v___x_2346_ = l_List_isEmpty___redArg(v_cs_2344_);
if (v___x_2346_ == 0)
{
lean_object* v___x_2347_; lean_object* v___x_2348_; 
lean_inc(v_toPure_2340_);
lean_dec_ref(v___f_2345_);
lean_dec(v_toBind_2339_);
lean_dec(v_n_2336_);
lean_dec_ref(v_inst_2335_);
lean_dec_ref(v_inst_2334_);
lean_dec_ref(v_inst_2333_);
v___x_2347_ = lean_box(0);
v___x_2348_ = l_Lean_filterFieldList___redArg___lam__2(v___f_2342_, v_cs_2344_, v_toPure_2340_, v___x_2347_);
return v___x_2348_;
}
else
{
lean_object* v_toMonadRef_2349_; lean_object* v_getRef_2350_; lean_object* v___f_2351_; lean_object* v___f_2352_; lean_object* v___x_2353_; 
lean_dec(v_cs_2344_);
v_toMonadRef_2349_ = lean_ctor_get(v_inst_2335_, 1);
v_getRef_2350_ = lean_ctor_get(v_toMonadRef_2349_, 0);
lean_inc(v_getRef_2350_);
v___f_2351_ = lean_alloc_closure((void*)(l_Lean_filterFieldList___redArg___lam__3), 2, 1);
lean_closure_set(v___f_2351_, 0, v___f_2345_);
lean_inc(v_toBind_2339_);
v___f_2352_ = lean_alloc_closure((void*)(l_Lean_filterFieldList___redArg___lam__4), 7, 6);
lean_closure_set(v___f_2352_, 0, v_inst_2333_);
lean_closure_set(v___f_2352_, 1, v_inst_2334_);
lean_closure_set(v___f_2352_, 2, v_inst_2335_);
lean_closure_set(v___f_2352_, 3, v_n_2336_);
lean_closure_set(v___f_2352_, 4, v_toBind_2339_);
lean_closure_set(v___f_2352_, 5, v___f_2351_);
v___x_2353_ = lean_apply_4(v_toBind_2339_, lean_box(0), lean_box(0), v_getRef_2350_, v___f_2352_);
return v___x_2353_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList(lean_object* v_m_2354_, lean_object* v_inst_2355_, lean_object* v_inst_2356_, lean_object* v_inst_2357_, lean_object* v_n_2358_, lean_object* v_cs_2359_){
_start:
{
lean_object* v___x_2360_; 
v___x_2360_ = l_Lean_filterFieldList___redArg(v_inst_2355_, v_inst_2356_, v_inst_2357_, v_n_2358_, v_cs_2359_);
return v___x_2360_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___redArg___lam__0(lean_object* v_inst_2361_, lean_object* v_inst_2362_, lean_object* v_inst_2363_, lean_object* v_n_2364_, lean_object* v_cs_2365_){
_start:
{
lean_object* v___x_2366_; 
v___x_2366_ = l_Lean_filterFieldList___redArg(v_inst_2361_, v_inst_2362_, v_inst_2363_, v_n_2364_, v_cs_2365_);
return v___x_2366_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___redArg(lean_object* v_inst_2367_, lean_object* v_inst_2368_, lean_object* v_inst_2369_, lean_object* v_inst_2370_, lean_object* v_inst_2371_, lean_object* v_inst_2372_, lean_object* v_inst_2373_, lean_object* v_n_2374_){
_start:
{
lean_object* v_toBind_2375_; lean_object* v___f_2376_; uint8_t v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; 
v_toBind_2375_ = lean_ctor_get(v_inst_2367_, 1);
lean_inc(v_toBind_2375_);
lean_inc(v_n_2374_);
lean_inc_ref(v_inst_2369_);
lean_inc_ref(v_inst_2367_);
v___f_2376_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___redArg___lam__0), 5, 4);
lean_closure_set(v___f_2376_, 0, v_inst_2367_);
lean_closure_set(v___f_2376_, 1, v_inst_2369_);
lean_closure_set(v___f_2376_, 2, v_inst_2373_);
lean_closure_set(v___f_2376_, 3, v_n_2374_);
v___x_2377_ = 1;
v___x_2378_ = l_Lean_resolveGlobalName___redArg(v_inst_2367_, v_inst_2368_, v_inst_2369_, v_inst_2370_, v_inst_2371_, v_inst_2372_, v_n_2374_, v___x_2377_);
v___x_2379_ = lean_apply_4(v_toBind_2375_, lean_box(0), lean_box(0), v___x_2378_, v___f_2376_);
return v___x_2379_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore(lean_object* v_m_2380_, lean_object* v_inst_2381_, lean_object* v_inst_2382_, lean_object* v_inst_2383_, lean_object* v_inst_2384_, lean_object* v_inst_2385_, lean_object* v_inst_2386_, lean_object* v_inst_2387_, lean_object* v_n_2388_){
_start:
{
lean_object* v___x_2389_; 
v___x_2389_ = l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___redArg(v_inst_2381_, v_inst_2382_, v_inst_2383_, v_inst_2384_, v_inst_2385_, v_inst_2386_, v_inst_2387_, v_n_2388_);
return v___x_2389_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNoOverload___redArg___lam__0(lean_object* v_declName_2390_){
_start:
{
lean_object* v___x_2391_; lean_object* v___x_2392_; 
v___x_2391_ = lean_box(0);
v___x_2392_ = l_Lean_mkConst(v_declName_2390_, v___x_2391_);
return v___x_2392_;
}
}
static lean_object* _init_l_Lean_ensureNoOverload___redArg___closed__2(void){
_start:
{
lean_object* v___x_2395_; lean_object* v___x_2396_; 
v___x_2395_ = ((lean_object*)(l_Lean_ensureNoOverload___redArg___closed__1));
v___x_2396_ = l_Lean_stringToMessageData(v___x_2395_);
return v___x_2396_;
}
}
static lean_object* _init_l_Lean_ensureNoOverload___redArg___closed__4(void){
_start:
{
lean_object* v___x_2398_; lean_object* v___x_2399_; 
v___x_2398_ = ((lean_object*)(l_Lean_ensureNoOverload___redArg___closed__3));
v___x_2399_ = l_Lean_stringToMessageData(v___x_2398_);
return v___x_2399_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNoOverload___redArg(lean_object* v_inst_2401_, lean_object* v_inst_2402_, lean_object* v_n_2403_, lean_object* v_cs_2404_){
_start:
{
lean_object* v_toApplicative_2405_; lean_object* v_toPure_2406_; lean_object* v___f_2407_; 
v_toApplicative_2405_ = lean_ctor_get(v_inst_2401_, 0);
v_toPure_2406_ = lean_ctor_get(v_toApplicative_2405_, 1);
v___f_2407_ = ((lean_object*)(l_Lean_ensureNoOverload___redArg___closed__0));
if (lean_obj_tag(v_cs_2404_) == 1)
{
lean_object* v_tail_2421_; 
v_tail_2421_ = lean_ctor_get(v_cs_2404_, 1);
if (lean_obj_tag(v_tail_2421_) == 0)
{
lean_object* v_head_2422_; lean_object* v___x_2423_; 
lean_inc(v_toPure_2406_);
lean_dec(v_n_2403_);
lean_dec_ref(v_inst_2402_);
lean_dec_ref(v_inst_2401_);
v_head_2422_ = lean_ctor_get(v_cs_2404_, 0);
lean_inc(v_head_2422_);
lean_dec_ref_known(v_cs_2404_, 2);
v___x_2423_ = lean_apply_2(v_toPure_2406_, lean_box(0), v_head_2422_);
return v___x_2423_;
}
else
{
goto v___jp_2408_;
}
}
else
{
goto v___jp_2408_;
}
v___jp_2408_:
{
lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; 
v___x_2409_ = lean_obj_once(&l_Lean_ensureNoOverload___redArg___closed__2, &l_Lean_ensureNoOverload___redArg___closed__2_once, _init_l_Lean_ensureNoOverload___redArg___closed__2);
v___x_2410_ = l_Lean_MessageData_ofName(v_n_2403_);
v___x_2411_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2411_, 0, v___x_2409_);
lean_ctor_set(v___x_2411_, 1, v___x_2410_);
v___x_2412_ = lean_obj_once(&l_Lean_ensureNoOverload___redArg___closed__4, &l_Lean_ensureNoOverload___redArg___closed__4_once, _init_l_Lean_ensureNoOverload___redArg___closed__4);
v___x_2413_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2413_, 0, v___x_2411_);
lean_ctor_set(v___x_2413_, 1, v___x_2412_);
v___x_2414_ = lean_box(0);
v___x_2415_ = l_List_mapTR_loop___redArg(v___f_2407_, v_cs_2404_, v___x_2414_);
v___x_2416_ = ((lean_object*)(l_Lean_ensureNoOverload___redArg___closed__5));
v___x_2417_ = l_List_mapTR_loop___redArg(v___x_2416_, v___x_2415_, v___x_2414_);
v___x_2418_ = l_Lean_MessageData_ofList(v___x_2417_);
v___x_2419_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2419_, 0, v___x_2413_);
lean_ctor_set(v___x_2419_, 1, v___x_2418_);
v___x_2420_ = l_Lean_throwError___redArg(v_inst_2401_, v_inst_2402_, v___x_2419_);
return v___x_2420_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNoOverload(lean_object* v_m_2424_, lean_object* v_inst_2425_, lean_object* v_inst_2426_, lean_object* v_n_2427_, lean_object* v_cs_2428_){
_start:
{
lean_object* v___x_2429_; 
v___x_2429_ = l_Lean_ensureNoOverload___redArg(v_inst_2425_, v_inst_2426_, v_n_2427_, v_cs_2428_);
return v___x_2429_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverloadCore___redArg___lam__0(lean_object* v_inst_2430_, lean_object* v_inst_2431_, lean_object* v_n_2432_, lean_object* v_____do__lift_2433_){
_start:
{
lean_object* v___x_2434_; 
v___x_2434_ = l_Lean_ensureNoOverload___redArg(v_inst_2430_, v_inst_2431_, v_n_2432_, v_____do__lift_2433_);
return v___x_2434_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverloadCore___redArg(lean_object* v_inst_2435_, lean_object* v_inst_2436_, lean_object* v_inst_2437_, lean_object* v_inst_2438_, lean_object* v_inst_2439_, lean_object* v_inst_2440_, lean_object* v_inst_2441_, lean_object* v_n_2442_){
_start:
{
lean_object* v_toBind_2443_; lean_object* v___f_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; 
v_toBind_2443_ = lean_ctor_get(v_inst_2435_, 1);
lean_inc(v_toBind_2443_);
lean_inc(v_n_2442_);
lean_inc_ref(v_inst_2441_);
lean_inc_ref(v_inst_2435_);
v___f_2444_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalConstNoOverloadCore___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2444_, 0, v_inst_2435_);
lean_closure_set(v___f_2444_, 1, v_inst_2441_);
lean_closure_set(v___f_2444_, 2, v_n_2442_);
v___x_2445_ = l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___redArg(v_inst_2435_, v_inst_2436_, v_inst_2437_, v_inst_2438_, v_inst_2439_, v_inst_2440_, v_inst_2441_, v_n_2442_);
v___x_2446_ = lean_apply_4(v_toBind_2443_, lean_box(0), lean_box(0), v___x_2445_, v___f_2444_);
return v___x_2446_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverloadCore(lean_object* v_m_2447_, lean_object* v_inst_2448_, lean_object* v_inst_2449_, lean_object* v_inst_2450_, lean_object* v_inst_2451_, lean_object* v_inst_2452_, lean_object* v_inst_2453_, lean_object* v_inst_2454_, lean_object* v_n_2455_){
_start:
{
lean_object* v___x_2456_; 
v___x_2456_ = l_Lean_resolveGlobalConstNoOverloadCore___redArg(v_inst_2448_, v_inst_2449_, v_inst_2450_, v_inst_2451_, v_inst_2452_, v_inst_2453_, v_inst_2454_, v_n_2455_);
return v___x_2456_;
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___redArg___lam__0(lean_object* v_x_2457_){
_start:
{
if (lean_obj_tag(v_x_2457_) == 1)
{
lean_object* v_fields_2458_; 
v_fields_2458_ = lean_ctor_get(v_x_2457_, 1);
if (lean_obj_tag(v_fields_2458_) == 0)
{
lean_object* v_n_2459_; lean_object* v___x_2460_; 
v_n_2459_ = lean_ctor_get(v_x_2457_, 0);
lean_inc(v_n_2459_);
v___x_2460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2460_, 0, v_n_2459_);
return v___x_2460_;
}
else
{
lean_object* v___x_2461_; 
v___x_2461_ = lean_box(0);
return v___x_2461_;
}
}
else
{
lean_object* v___x_2462_; 
v___x_2462_ = lean_box(0);
return v___x_2462_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___redArg___lam__0___boxed(lean_object* v_x_2463_){
_start:
{
lean_object* v_res_2464_; 
v_res_2464_ = l_Lean_preprocessSyntaxAndResolve___redArg___lam__0(v_x_2463_);
lean_dec_ref(v_x_2463_);
return v_res_2464_;
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___redArg___lam__1(lean_object* v_stx_2465_, lean_object* v_withRef_2466_, lean_object* v___x_2467_, lean_object* v_oldRef_2468_){
_start:
{
lean_object* v_ref_2469_; lean_object* v___x_2470_; 
v_ref_2469_ = l_Lean_replaceRef(v_stx_2465_, v_oldRef_2468_);
v___x_2470_ = lean_apply_3(v_withRef_2466_, lean_box(0), v_ref_2469_, v___x_2467_);
return v___x_2470_;
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___redArg___lam__1___boxed(lean_object* v_stx_2471_, lean_object* v_withRef_2472_, lean_object* v___x_2473_, lean_object* v_oldRef_2474_){
_start:
{
lean_object* v_res_2475_; 
v_res_2475_ = l_Lean_preprocessSyntaxAndResolve___redArg___lam__1(v_stx_2471_, v_withRef_2472_, v___x_2473_, v_oldRef_2474_);
lean_dec(v_oldRef_2474_);
lean_dec(v_stx_2471_);
return v_res_2475_;
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___redArg(lean_object* v_inst_2477_, lean_object* v_inst_2478_, lean_object* v_stx_2479_, lean_object* v_k_2480_){
_start:
{
if (lean_obj_tag(v_stx_2479_) == 3)
{
lean_object* v_val_2481_; lean_object* v_preresolved_2482_; lean_object* v___f_2483_; lean_object* v___x_2484_; lean_object* v_pre_2485_; uint8_t v___x_2486_; 
v_val_2481_ = lean_ctor_get(v_stx_2479_, 2);
v_preresolved_2482_ = lean_ctor_get(v_stx_2479_, 3);
v___f_2483_ = ((lean_object*)(l_Lean_preprocessSyntaxAndResolve___redArg___closed__0));
v___x_2484_ = ((lean_object*)(l_Lean_resolveNamespace___redArg___closed__1));
lean_inc(v_preresolved_2482_);
v_pre_2485_ = l_List_filterMapTR_go___redArg(v___f_2483_, v_preresolved_2482_, v___x_2484_);
v___x_2486_ = l_List_isEmpty___redArg(v_pre_2485_);
if (v___x_2486_ == 0)
{
lean_object* v_toApplicative_2487_; lean_object* v_toPure_2488_; lean_object* v___x_2489_; 
lean_dec_ref_known(v_stx_2479_, 4);
lean_dec(v_k_2480_);
lean_dec_ref(v_inst_2478_);
v_toApplicative_2487_ = lean_ctor_get(v_inst_2477_, 0);
lean_inc_ref(v_toApplicative_2487_);
lean_dec_ref(v_inst_2477_);
v_toPure_2488_ = lean_ctor_get(v_toApplicative_2487_, 1);
lean_inc(v_toPure_2488_);
lean_dec_ref(v_toApplicative_2487_);
v___x_2489_ = lean_apply_2(v_toPure_2488_, lean_box(0), v_pre_2485_);
return v___x_2489_;
}
else
{
lean_object* v_toMonadRef_2490_; lean_object* v_toBind_2491_; lean_object* v_getRef_2492_; lean_object* v_withRef_2493_; lean_object* v___x_2494_; lean_object* v___f_2495_; lean_object* v___x_2496_; 
lean_dec(v_pre_2485_);
v_toMonadRef_2490_ = lean_ctor_get(v_inst_2478_, 1);
lean_inc_ref(v_toMonadRef_2490_);
lean_dec_ref(v_inst_2478_);
v_toBind_2491_ = lean_ctor_get(v_inst_2477_, 1);
lean_inc(v_toBind_2491_);
lean_dec_ref(v_inst_2477_);
v_getRef_2492_ = lean_ctor_get(v_toMonadRef_2490_, 0);
lean_inc(v_getRef_2492_);
v_withRef_2493_ = lean_ctor_get(v_toMonadRef_2490_, 1);
lean_inc(v_withRef_2493_);
lean_dec_ref(v_toMonadRef_2490_);
lean_inc(v_val_2481_);
v___x_2494_ = lean_apply_1(v_k_2480_, v_val_2481_);
v___f_2495_ = lean_alloc_closure((void*)(l_Lean_preprocessSyntaxAndResolve___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_2495_, 0, v_stx_2479_);
lean_closure_set(v___f_2495_, 1, v_withRef_2493_);
lean_closure_set(v___f_2495_, 2, v___x_2494_);
v___x_2496_ = lean_apply_4(v_toBind_2491_, lean_box(0), lean_box(0), v_getRef_2492_, v___f_2495_);
return v___x_2496_;
}
}
else
{
lean_object* v___x_2497_; lean_object* v___x_2498_; 
lean_dec(v_k_2480_);
v___x_2497_ = lean_obj_once(&l_Lean_resolveNamespace___redArg___closed__4, &l_Lean_resolveNamespace___redArg___closed__4_once, _init_l_Lean_resolveNamespace___redArg___closed__4);
v___x_2498_ = l_Lean_throwErrorAt___redArg(v_inst_2477_, v_inst_2478_, v_stx_2479_, v___x_2497_);
return v___x_2498_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve(lean_object* v_m_2499_, lean_object* v_inst_2500_, lean_object* v_inst_2501_, lean_object* v_stx_2502_, lean_object* v_k_2503_){
_start:
{
lean_object* v___x_2504_; 
v___x_2504_ = l_Lean_preprocessSyntaxAndResolve___redArg(v_inst_2500_, v_inst_2501_, v_stx_2502_, v_k_2503_);
return v___x_2504_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst___redArg(lean_object* v_inst_2505_, lean_object* v_inst_2506_, lean_object* v_inst_2507_, lean_object* v_inst_2508_, lean_object* v_inst_2509_, lean_object* v_inst_2510_, lean_object* v_inst_2511_, lean_object* v_stx_2512_){
_start:
{
lean_object* v___x_2513_; lean_object* v___x_2514_; 
lean_inc_ref(v_inst_2511_);
lean_inc_ref(v_inst_2505_);
v___x_2513_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore), 9, 8);
lean_closure_set(v___x_2513_, 0, lean_box(0));
lean_closure_set(v___x_2513_, 1, v_inst_2505_);
lean_closure_set(v___x_2513_, 2, v_inst_2506_);
lean_closure_set(v___x_2513_, 3, v_inst_2507_);
lean_closure_set(v___x_2513_, 4, v_inst_2508_);
lean_closure_set(v___x_2513_, 5, v_inst_2509_);
lean_closure_set(v___x_2513_, 6, v_inst_2510_);
lean_closure_set(v___x_2513_, 7, v_inst_2511_);
v___x_2514_ = l_Lean_preprocessSyntaxAndResolve___redArg(v_inst_2505_, v_inst_2511_, v_stx_2512_, v___x_2513_);
return v___x_2514_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst(lean_object* v_m_2515_, lean_object* v_inst_2516_, lean_object* v_inst_2517_, lean_object* v_inst_2518_, lean_object* v_inst_2519_, lean_object* v_inst_2520_, lean_object* v_inst_2521_, lean_object* v_inst_2522_, lean_object* v_stx_2523_){
_start:
{
lean_object* v___x_2524_; 
v___x_2524_ = l_Lean_resolveGlobalConst___redArg(v_inst_2516_, v_inst_2517_, v_inst_2518_, v_inst_2519_, v_inst_2520_, v_inst_2521_, v_inst_2522_, v_stx_2523_);
return v___x_2524_;
}
}
static lean_object* _init_l_Lean_ensureNonAmbiguous___redArg___closed__1(void){
_start:
{
lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; 
v___x_2526_ = ((lean_object*)(l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__2));
v___x_2527_ = lean_unsigned_to_nat(11u);
v___x_2528_ = lean_unsigned_to_nat(429u);
v___x_2529_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___redArg___closed__0));
v___x_2530_ = ((lean_object*)(l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__0));
v___x_2531_ = l_mkPanicMessageWithDecl(v___x_2530_, v___x_2529_, v___x_2528_, v___x_2527_, v___x_2526_);
return v___x_2531_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNonAmbiguous___redArg(lean_object* v_inst_2535_, lean_object* v_inst_2536_, lean_object* v_id_2537_, lean_object* v_cs_2538_){
_start:
{
if (lean_obj_tag(v_cs_2538_) == 0)
{
lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; 
lean_dec(v_id_2537_);
lean_dec_ref(v_inst_2536_);
v___x_2539_ = lean_box(0);
v___x_2540_ = l_instInhabitedOfMonad___redArg(v_inst_2535_, v___x_2539_);
v___x_2541_ = lean_obj_once(&l_Lean_ensureNonAmbiguous___redArg___closed__1, &l_Lean_ensureNonAmbiguous___redArg___closed__1_once, _init_l_Lean_ensureNonAmbiguous___redArg___closed__1);
v___x_2542_ = l_panic___redArg(v___x_2540_, v___x_2541_);
lean_dec(v___x_2540_);
return v___x_2542_;
}
else
{
lean_object* v_tail_2543_; 
v_tail_2543_ = lean_ctor_get(v_cs_2538_, 1);
if (lean_obj_tag(v_tail_2543_) == 0)
{
lean_object* v_toApplicative_2544_; lean_object* v_toPure_2545_; lean_object* v_head_2546_; lean_object* v___x_2547_; 
v_toApplicative_2544_ = lean_ctor_get(v_inst_2535_, 0);
lean_inc_ref(v_toApplicative_2544_);
lean_dec(v_id_2537_);
lean_dec_ref(v_inst_2536_);
lean_dec_ref(v_inst_2535_);
v_toPure_2545_ = lean_ctor_get(v_toApplicative_2544_, 1);
lean_inc(v_toPure_2545_);
lean_dec_ref(v_toApplicative_2544_);
v_head_2546_ = lean_ctor_get(v_cs_2538_, 0);
lean_inc(v_head_2546_);
lean_dec_ref_known(v_cs_2538_, 2);
v___x_2547_ = lean_apply_2(v_toPure_2545_, lean_box(0), v_head_2546_);
return v___x_2547_;
}
else
{
lean_object* v___f_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; uint8_t v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; 
v___f_2548_ = ((lean_object*)(l_Lean_ensureNoOverload___redArg___closed__0));
v___x_2549_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___redArg___closed__2));
v___x_2550_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___redArg___closed__3));
v___x_2551_ = lean_box(0);
v___x_2552_ = 0;
lean_inc(v_id_2537_);
v___x_2553_ = l_Lean_Syntax_formatStx(v_id_2537_, v___x_2551_, v___x_2552_);
v___x_2554_ = l_Std_Format_defWidth;
v___x_2555_ = lean_unsigned_to_nat(0u);
v___x_2556_ = l_Std_Format_pretty(v___x_2553_, v___x_2554_, v___x_2555_, v___x_2555_);
v___x_2557_ = lean_string_append(v___x_2550_, v___x_2556_);
lean_dec_ref(v___x_2556_);
v___x_2558_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___redArg___closed__4));
v___x_2559_ = lean_string_append(v___x_2557_, v___x_2558_);
v___x_2560_ = lean_box(0);
v___x_2561_ = l_List_mapTR_loop___redArg(v___f_2548_, v_cs_2538_, v___x_2560_);
v___x_2562_ = l_List_toString___redArg(v___x_2549_, v___x_2561_);
v___x_2563_ = lean_string_append(v___x_2559_, v___x_2562_);
lean_dec_ref(v___x_2562_);
v___x_2564_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2564_, 0, v___x_2563_);
v___x_2565_ = l_Lean_MessageData_ofFormat(v___x_2564_);
v___x_2566_ = l_Lean_throwErrorAt___redArg(v_inst_2535_, v_inst_2536_, v_id_2537_, v___x_2565_);
return v___x_2566_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNonAmbiguous(lean_object* v_m_2567_, lean_object* v_inst_2568_, lean_object* v_inst_2569_, lean_object* v_id_2570_, lean_object* v_cs_2571_){
_start:
{
lean_object* v___x_2572_; 
v___x_2572_ = l_Lean_ensureNonAmbiguous___redArg(v_inst_2568_, v_inst_2569_, v_id_2570_, v_cs_2571_);
return v___x_2572_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverload___redArg___lam__0(lean_object* v_inst_2573_, lean_object* v_inst_2574_, lean_object* v_id_2575_, lean_object* v_____do__lift_2576_){
_start:
{
lean_object* v___x_2577_; 
v___x_2577_ = l_Lean_ensureNonAmbiguous___redArg(v_inst_2573_, v_inst_2574_, v_id_2575_, v_____do__lift_2576_);
return v___x_2577_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverload___redArg(lean_object* v_inst_2578_, lean_object* v_inst_2579_, lean_object* v_inst_2580_, lean_object* v_inst_2581_, lean_object* v_inst_2582_, lean_object* v_inst_2583_, lean_object* v_inst_2584_, lean_object* v_id_2585_){
_start:
{
lean_object* v_toBind_2586_; lean_object* v___f_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; 
v_toBind_2586_ = lean_ctor_get(v_inst_2578_, 1);
lean_inc(v_toBind_2586_);
lean_inc(v_id_2585_);
lean_inc_ref(v_inst_2584_);
lean_inc_ref(v_inst_2578_);
v___f_2587_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalConstNoOverload___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2587_, 0, v_inst_2578_);
lean_closure_set(v___f_2587_, 1, v_inst_2584_);
lean_closure_set(v___f_2587_, 2, v_id_2585_);
v___x_2588_ = l_Lean_resolveGlobalConst___redArg(v_inst_2578_, v_inst_2579_, v_inst_2580_, v_inst_2581_, v_inst_2582_, v_inst_2583_, v_inst_2584_, v_id_2585_);
v___x_2589_ = lean_apply_4(v_toBind_2586_, lean_box(0), lean_box(0), v___x_2588_, v___f_2587_);
return v___x_2589_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverload(lean_object* v_m_2590_, lean_object* v_inst_2591_, lean_object* v_inst_2592_, lean_object* v_inst_2593_, lean_object* v_inst_2594_, lean_object* v_inst_2595_, lean_object* v_inst_2596_, lean_object* v_inst_2597_, lean_object* v_id_2598_){
_start:
{
lean_object* v___x_2599_; 
v___x_2599_ = l_Lean_resolveGlobalConstNoOverload___redArg(v_inst_2591_, v_inst_2592_, v_inst_2593_, v_inst_2594_, v_inst_2595_, v_inst_2596_, v_inst_2597_, v_id_2598_);
return v___x_2599_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__0(lean_object* v___f_2600_, lean_object* v___f_2601_, uint8_t v_globalDeclFoundNext_2602_, uint8_t v_globalDeclFound_2603_, lean_object* v_r_2604_){
_start:
{
lean_object* v___x_2605_; lean_object* v_r_2606_; uint8_t v___x_2607_; 
v___x_2605_ = lean_box(0);
v_r_2606_ = l_List_filterTR_loop___redArg(v___f_2600_, v_r_2604_, v___x_2605_);
v___x_2607_ = l_List_isEmpty___redArg(v_r_2606_);
lean_dec(v_r_2606_);
if (v___x_2607_ == 0)
{
lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; 
v___x_2608_ = lean_box(0);
v___x_2609_ = lean_box(v_globalDeclFoundNext_2602_);
v___x_2610_ = lean_apply_2(v___f_2601_, v___x_2608_, v___x_2609_);
return v___x_2610_;
}
else
{
lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; 
v___x_2611_ = lean_box(0);
v___x_2612_ = lean_box(v_globalDeclFound_2603_);
v___x_2613_ = lean_apply_2(v___f_2601_, v___x_2611_, v___x_2612_);
return v___x_2613_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__0___boxed(lean_object* v___f_2614_, lean_object* v___f_2615_, lean_object* v_globalDeclFoundNext_2616_, lean_object* v_globalDeclFound_2617_, lean_object* v_r_2618_){
_start:
{
uint8_t v_globalDeclFoundNext_boxed_2619_; uint8_t v_globalDeclFound_boxed_2620_; lean_object* v_res_2621_; 
v_globalDeclFoundNext_boxed_2619_ = lean_unbox(v_globalDeclFoundNext_2616_);
v_globalDeclFound_boxed_2620_ = lean_unbox(v_globalDeclFound_2617_);
v_res_2621_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__0(v___f_2614_, v___f_2615_, v_globalDeclFoundNext_boxed_2619_, v_globalDeclFound_boxed_2620_, v_r_2618_);
return v_res_2621_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__1___boxed(lean_object* v_str_2622_, lean_object* v_projs_2623_, lean_object* v_inst_2624_, lean_object* v_inst_2625_, lean_object* v_inst_2626_, lean_object* v_inst_2627_, lean_object* v_inst_2628_, lean_object* v_inst_2629_, lean_object* v_view_2630_, lean_object* v_findLocalDecl_x3f_2631_, lean_object* v_pre_2632_, lean_object* v_____r_2633_, lean_object* v_globalDeclFoundNext_2634_){
_start:
{
uint8_t v_globalDeclFoundNext_boxed_2635_; lean_object* v_res_2636_; 
v_globalDeclFoundNext_boxed_2635_ = lean_unbox(v_globalDeclFoundNext_2634_);
v_res_2636_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__1(v_str_2622_, v_projs_2623_, v_inst_2624_, v_inst_2625_, v_inst_2626_, v_inst_2627_, v_inst_2628_, v_inst_2629_, v_view_2630_, v_findLocalDecl_x3f_2631_, v_pre_2632_, v_____r_2633_, v_globalDeclFoundNext_boxed_2635_);
return v_res_2636_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg(lean_object* v_inst_2637_, lean_object* v_inst_2638_, lean_object* v_inst_2639_, lean_object* v_inst_2640_, lean_object* v_inst_2641_, lean_object* v_inst_2642_, lean_object* v_view_2643_, lean_object* v_findLocalDecl_x3f_2644_, lean_object* v_n_2645_, lean_object* v_projs_2646_, uint8_t v_globalDeclFound_2647_){
_start:
{
lean_object* v_toApplicative_2648_; lean_object* v_imported_2649_; lean_object* v_ctx_2650_; lean_object* v_scopes_2651_; lean_object* v_toBind_2652_; lean_object* v_toPure_2653_; lean_object* v___f_2654_; lean_object* v_givenNameView_2655_; uint8_t v___y_2657_; 
v_toApplicative_2648_ = lean_ctor_get(v_inst_2637_, 0);
v_imported_2649_ = lean_ctor_get(v_view_2643_, 1);
v_ctx_2650_ = lean_ctor_get(v_view_2643_, 2);
v_scopes_2651_ = lean_ctor_get(v_view_2643_, 3);
v_toBind_2652_ = lean_ctor_get(v_inst_2637_, 1);
v_toPure_2653_ = lean_ctor_get(v_toApplicative_2648_, 1);
v___f_2654_ = ((lean_object*)(l_Lean_filterFieldList___redArg___closed__0));
lean_inc(v_scopes_2651_);
lean_inc(v_ctx_2650_);
lean_inc(v_imported_2649_);
lean_inc(v_n_2645_);
v_givenNameView_2655_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_givenNameView_2655_, 0, v_n_2645_);
lean_ctor_set(v_givenNameView_2655_, 1, v_imported_2649_);
lean_ctor_set(v_givenNameView_2655_, 2, v_ctx_2650_);
lean_ctor_set(v_givenNameView_2655_, 3, v_scopes_2651_);
if (v_globalDeclFound_2647_ == 0)
{
v___y_2657_ = v_globalDeclFound_2647_;
goto v___jp_2656_;
}
else
{
uint8_t v___x_2693_; 
v___x_2693_ = l_List_isEmpty___redArg(v_projs_2646_);
if (v___x_2693_ == 0)
{
v___y_2657_ = v_globalDeclFound_2647_;
goto v___jp_2656_;
}
else
{
uint8_t v___x_2694_; 
v___x_2694_ = 0;
v___y_2657_ = v___x_2694_;
goto v___jp_2656_;
}
}
v___jp_2656_:
{
lean_object* v___x_2658_; lean_object* v___x_2659_; 
v___x_2658_ = lean_box(v___y_2657_);
lean_inc_ref(v_findLocalDecl_x3f_2644_);
lean_inc_ref(v_givenNameView_2655_);
v___x_2659_ = lean_apply_2(v_findLocalDecl_x3f_2644_, v_givenNameView_2655_, v___x_2658_);
if (lean_obj_tag(v___x_2659_) == 0)
{
if (lean_obj_tag(v_n_2645_) == 1)
{
lean_object* v_pre_2660_; lean_object* v_str_2661_; lean_object* v___f_2662_; 
v_pre_2660_ = lean_ctor_get(v_n_2645_, 0);
lean_inc_n(v_pre_2660_, 2);
v_str_2661_ = lean_ctor_get(v_n_2645_, 1);
lean_inc_ref_n(v_str_2661_, 2);
lean_dec_ref_known(v_n_2645_, 2);
lean_inc_ref(v_findLocalDecl_x3f_2644_);
lean_inc_ref(v_view_2643_);
lean_inc(v_inst_2642_);
lean_inc_ref(v_inst_2641_);
lean_inc(v_inst_2640_);
lean_inc_ref(v_inst_2639_);
lean_inc_ref(v_inst_2638_);
lean_inc_ref(v_inst_2637_);
lean_inc(v_projs_2646_);
v___f_2662_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__1___boxed), 13, 11);
lean_closure_set(v___f_2662_, 0, v_str_2661_);
lean_closure_set(v___f_2662_, 1, v_projs_2646_);
lean_closure_set(v___f_2662_, 2, v_inst_2637_);
lean_closure_set(v___f_2662_, 3, v_inst_2638_);
lean_closure_set(v___f_2662_, 4, v_inst_2639_);
lean_closure_set(v___f_2662_, 5, v_inst_2640_);
lean_closure_set(v___f_2662_, 6, v_inst_2641_);
lean_closure_set(v___f_2662_, 7, v_inst_2642_);
lean_closure_set(v___f_2662_, 8, v_view_2643_);
lean_closure_set(v___f_2662_, 9, v_findLocalDecl_x3f_2644_);
lean_closure_set(v___f_2662_, 10, v_pre_2660_);
if (v_globalDeclFound_2647_ == 0)
{
uint8_t v_globalDeclFoundNext_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___f_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; 
lean_inc(v_toBind_2652_);
lean_dec_ref(v_str_2661_);
lean_dec(v_pre_2660_);
lean_dec(v_projs_2646_);
lean_dec_ref(v_findLocalDecl_x3f_2644_);
lean_dec_ref(v_view_2643_);
v_globalDeclFoundNext_2663_ = 1;
v___x_2664_ = lean_box(v_globalDeclFoundNext_2663_);
v___x_2665_ = lean_box(v_globalDeclFound_2647_);
v___f_2666_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2666_, 0, v___f_2654_);
lean_closure_set(v___f_2666_, 1, v___f_2662_);
lean_closure_set(v___f_2666_, 2, v___x_2664_);
lean_closure_set(v___f_2666_, 3, v___x_2665_);
v___x_2667_ = l_Lean_MacroScopesView_review(v_givenNameView_2655_);
v___x_2668_ = l_Lean_resolveGlobalName___redArg(v_inst_2637_, v_inst_2638_, v_inst_2639_, v_inst_2640_, v_inst_2641_, v_inst_2642_, v___x_2667_, v_globalDeclFound_2647_);
v___x_2669_ = lean_apply_4(v_toBind_2652_, lean_box(0), lean_box(0), v___x_2668_, v___f_2666_);
return v___x_2669_;
}
else
{
lean_object* v___x_2670_; lean_object* v___x_2671_; 
lean_dec_ref(v___f_2662_);
lean_dec_ref_known(v_givenNameView_2655_, 4);
v___x_2670_ = lean_box(0);
v___x_2671_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__1(v_str_2661_, v_projs_2646_, v_inst_2637_, v_inst_2638_, v_inst_2639_, v_inst_2640_, v_inst_2641_, v_inst_2642_, v_view_2643_, v_findLocalDecl_x3f_2644_, v_pre_2660_, v___x_2670_, v_globalDeclFound_2647_);
return v___x_2671_;
}
}
else
{
lean_object* v___x_2672_; lean_object* v___x_2673_; 
lean_inc(v_toPure_2653_);
lean_dec_ref_known(v_givenNameView_2655_, 4);
lean_dec(v_projs_2646_);
lean_dec(v_n_2645_);
lean_dec_ref(v_findLocalDecl_x3f_2644_);
lean_dec_ref(v_view_2643_);
lean_dec(v_inst_2642_);
lean_dec_ref(v_inst_2641_);
lean_dec(v_inst_2640_);
lean_dec_ref(v_inst_2639_);
lean_dec_ref(v_inst_2638_);
lean_dec_ref(v_inst_2637_);
v___x_2672_ = lean_box(0);
v___x_2673_ = lean_apply_2(v_toPure_2653_, lean_box(0), v___x_2672_);
return v___x_2673_;
}
}
else
{
lean_object* v___x_2675_; uint8_t v_isShared_2676_; uint8_t v_isSharedCheck_2690_; 
lean_inc(v_toPure_2653_);
lean_dec_ref_known(v_givenNameView_2655_, 4);
lean_dec(v_n_2645_);
lean_dec_ref(v_findLocalDecl_x3f_2644_);
lean_dec_ref(v_view_2643_);
lean_dec(v_inst_2642_);
lean_dec_ref(v_inst_2641_);
lean_dec(v_inst_2640_);
lean_dec_ref(v_inst_2639_);
lean_dec_ref(v_inst_2638_);
v_isSharedCheck_2690_ = !lean_is_exclusive(v_inst_2637_);
if (v_isSharedCheck_2690_ == 0)
{
lean_object* v_unused_2691_; lean_object* v_unused_2692_; 
v_unused_2691_ = lean_ctor_get(v_inst_2637_, 1);
lean_dec(v_unused_2691_);
v_unused_2692_ = lean_ctor_get(v_inst_2637_, 0);
lean_dec(v_unused_2692_);
v___x_2675_ = v_inst_2637_;
v_isShared_2676_ = v_isSharedCheck_2690_;
goto v_resetjp_2674_;
}
else
{
lean_dec(v_inst_2637_);
v___x_2675_ = lean_box(0);
v_isShared_2676_ = v_isSharedCheck_2690_;
goto v_resetjp_2674_;
}
v_resetjp_2674_:
{
lean_object* v_val_2677_; lean_object* v___x_2679_; uint8_t v_isShared_2680_; uint8_t v_isSharedCheck_2689_; 
v_val_2677_ = lean_ctor_get(v___x_2659_, 0);
v_isSharedCheck_2689_ = !lean_is_exclusive(v___x_2659_);
if (v_isSharedCheck_2689_ == 0)
{
v___x_2679_ = v___x_2659_;
v_isShared_2680_ = v_isSharedCheck_2689_;
goto v_resetjp_2678_;
}
else
{
lean_inc(v_val_2677_);
lean_dec(v___x_2659_);
v___x_2679_ = lean_box(0);
v_isShared_2680_ = v_isSharedCheck_2689_;
goto v_resetjp_2678_;
}
v_resetjp_2678_:
{
lean_object* v___x_2681_; lean_object* v___x_2683_; 
v___x_2681_ = l_Lean_LocalDecl_toExpr(v_val_2677_);
if (v_isShared_2676_ == 0)
{
lean_ctor_set(v___x_2675_, 1, v_projs_2646_);
lean_ctor_set(v___x_2675_, 0, v___x_2681_);
v___x_2683_ = v___x_2675_;
goto v_reusejp_2682_;
}
else
{
lean_object* v_reuseFailAlloc_2688_; 
v_reuseFailAlloc_2688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2688_, 0, v___x_2681_);
lean_ctor_set(v_reuseFailAlloc_2688_, 1, v_projs_2646_);
v___x_2683_ = v_reuseFailAlloc_2688_;
goto v_reusejp_2682_;
}
v_reusejp_2682_:
{
lean_object* v___x_2685_; 
if (v_isShared_2680_ == 0)
{
lean_ctor_set(v___x_2679_, 0, v___x_2683_);
v___x_2685_ = v___x_2679_;
goto v_reusejp_2684_;
}
else
{
lean_object* v_reuseFailAlloc_2687_; 
v_reuseFailAlloc_2687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2687_, 0, v___x_2683_);
v___x_2685_ = v_reuseFailAlloc_2687_;
goto v_reusejp_2684_;
}
v_reusejp_2684_:
{
lean_object* v___x_2686_; 
v___x_2686_ = lean_apply_2(v_toPure_2653_, lean_box(0), v___x_2685_);
return v___x_2686_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__1(lean_object* v_str_2695_, lean_object* v_projs_2696_, lean_object* v_inst_2697_, lean_object* v_inst_2698_, lean_object* v_inst_2699_, lean_object* v_inst_2700_, lean_object* v_inst_2701_, lean_object* v_inst_2702_, lean_object* v_view_2703_, lean_object* v_findLocalDecl_x3f_2704_, lean_object* v_pre_2705_, lean_object* v_____r_2706_, uint8_t v_globalDeclFoundNext_2707_){
_start:
{
lean_object* v___x_2708_; lean_object* v___x_2709_; 
v___x_2708_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2708_, 0, v_str_2695_);
lean_ctor_set(v___x_2708_, 1, v_projs_2696_);
v___x_2709_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg(v_inst_2697_, v_inst_2698_, v_inst_2699_, v_inst_2700_, v_inst_2701_, v_inst_2702_, v_view_2703_, v_findLocalDecl_x3f_2704_, v_pre_2705_, v___x_2708_, v_globalDeclFoundNext_2707_);
return v___x_2709_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___boxed(lean_object* v_inst_2710_, lean_object* v_inst_2711_, lean_object* v_inst_2712_, lean_object* v_inst_2713_, lean_object* v_inst_2714_, lean_object* v_inst_2715_, lean_object* v_view_2716_, lean_object* v_findLocalDecl_x3f_2717_, lean_object* v_n_2718_, lean_object* v_projs_2719_, lean_object* v_globalDeclFound_2720_){
_start:
{
uint8_t v_globalDeclFound_boxed_2721_; lean_object* v_res_2722_; 
v_globalDeclFound_boxed_2721_ = lean_unbox(v_globalDeclFound_2720_);
v_res_2722_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg(v_inst_2710_, v_inst_2711_, v_inst_2712_, v_inst_2713_, v_inst_2714_, v_inst_2715_, v_view_2716_, v_findLocalDecl_x3f_2717_, v_n_2718_, v_projs_2719_, v_globalDeclFound_boxed_2721_);
return v_res_2722_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop(lean_object* v_m_2723_, lean_object* v_inst_2724_, lean_object* v_inst_2725_, lean_object* v_inst_2726_, lean_object* v_inst_2727_, lean_object* v_inst_2728_, lean_object* v_inst_2729_, lean_object* v_view_2730_, lean_object* v_findLocalDecl_x3f_2731_, lean_object* v_n_2732_, lean_object* v_projs_2733_, uint8_t v_globalDeclFound_2734_){
_start:
{
lean_object* v___x_2735_; 
v___x_2735_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg(v_inst_2724_, v_inst_2725_, v_inst_2726_, v_inst_2727_, v_inst_2728_, v_inst_2729_, v_view_2730_, v_findLocalDecl_x3f_2731_, v_n_2732_, v_projs_2733_, v_globalDeclFound_2734_);
return v___x_2735_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___boxed(lean_object* v_m_2736_, lean_object* v_inst_2737_, lean_object* v_inst_2738_, lean_object* v_inst_2739_, lean_object* v_inst_2740_, lean_object* v_inst_2741_, lean_object* v_inst_2742_, lean_object* v_view_2743_, lean_object* v_findLocalDecl_x3f_2744_, lean_object* v_n_2745_, lean_object* v_projs_2746_, lean_object* v_globalDeclFound_2747_){
_start:
{
uint8_t v_globalDeclFound_boxed_2748_; lean_object* v_res_2749_; 
v_globalDeclFound_boxed_2748_ = lean_unbox(v_globalDeclFound_2747_);
v_res_2749_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop(v_m_2736_, v_inst_2737_, v_inst_2738_, v_inst_2739_, v_inst_2740_, v_inst_2741_, v_inst_2742_, v_view_2743_, v_findLocalDecl_x3f_2744_, v_n_2745_, v_projs_2746_, v_globalDeclFound_boxed_2748_);
return v_res_2749_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_go(lean_object* v_localDecl_2750_, lean_object* v_givenNameView_2751_, lean_object* v_fullDeclName_2752_, lean_object* v_ns_2753_){
_start:
{
lean_object* v_name_2754_; lean_object* v_imported_2755_; lean_object* v_ctx_2756_; lean_object* v_scopes_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; uint8_t v___x_2761_; 
v_name_2754_ = lean_ctor_get(v_givenNameView_2751_, 0);
v_imported_2755_ = lean_ctor_get(v_givenNameView_2751_, 1);
v_ctx_2756_ = lean_ctor_get(v_givenNameView_2751_, 2);
v_scopes_2757_ = lean_ctor_get(v_givenNameView_2751_, 3);
lean_inc(v_name_2754_);
lean_inc(v_ns_2753_);
v___x_2758_ = l_Lean_Name_append(v_ns_2753_, v_name_2754_);
lean_inc(v_scopes_2757_);
lean_inc(v_ctx_2756_);
lean_inc(v_imported_2755_);
v___x_2759_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2759_, 0, v___x_2758_);
lean_ctor_set(v___x_2759_, 1, v_imported_2755_);
lean_ctor_set(v___x_2759_, 2, v_ctx_2756_);
lean_ctor_set(v___x_2759_, 3, v_scopes_2757_);
v___x_2760_ = l_Lean_MacroScopesView_review(v___x_2759_);
v___x_2761_ = lean_name_eq(v___x_2760_, v_fullDeclName_2752_);
lean_dec(v___x_2760_);
if (v___x_2761_ == 0)
{
if (lean_obj_tag(v_ns_2753_) == 1)
{
lean_object* v_pre_2762_; 
v_pre_2762_ = lean_ctor_get(v_ns_2753_, 0);
lean_inc(v_pre_2762_);
lean_dec_ref_known(v_ns_2753_, 2);
v_ns_2753_ = v_pre_2762_;
goto _start;
}
else
{
lean_object* v___x_2764_; 
lean_dec(v_ns_2753_);
lean_dec_ref(v_givenNameView_2751_);
lean_dec_ref(v_localDecl_2750_);
v___x_2764_ = lean_box(0);
return v___x_2764_;
}
}
else
{
lean_object* v___x_2765_; 
lean_dec(v_ns_2753_);
lean_dec_ref(v_givenNameView_2751_);
v___x_2765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2765_, 0, v_localDecl_2750_);
return v___x_2765_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_go___boxed(lean_object* v_localDecl_2766_, lean_object* v_givenNameView_2767_, lean_object* v_fullDeclName_2768_, lean_object* v_ns_2769_){
_start:
{
lean_object* v_res_2770_; 
v_res_2770_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_go(v_localDecl_2766_, v_givenNameView_2767_, v_fullDeclName_2768_, v_ns_2769_);
lean_dec(v_fullDeclName_2768_);
return v_res_2770_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__0(lean_object* v_localDecl_2771_, lean_object* v_givenName_2772_){
_start:
{
lean_object* v___x_2773_; uint8_t v___x_2774_; 
v___x_2773_ = l_Lean_LocalDecl_userName(v_localDecl_2771_);
v___x_2774_ = lean_name_eq(v___x_2773_, v_givenName_2772_);
lean_dec(v___x_2773_);
if (v___x_2774_ == 0)
{
lean_object* v___x_2775_; 
lean_dec_ref(v_localDecl_2771_);
v___x_2775_ = lean_box(0);
return v___x_2775_;
}
else
{
lean_object* v___x_2776_; 
v___x_2776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2776_, 0, v_localDecl_2771_);
return v___x_2776_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__0___boxed(lean_object* v_localDecl_2777_, lean_object* v_givenName_2778_){
_start:
{
lean_object* v_res_2779_; 
v_res_2779_ = l_Lean_resolveLocalName___redArg___lam__0(v_localDecl_2777_, v_givenName_2778_);
lean_dec(v_givenName_2778_);
return v_res_2779_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__1(lean_object* v_matchLocalDecl_x3f_2780_, lean_object* v_givenName_2781_, uint8_t v_skipAuxDecl_2782_, lean_object* v___f_2783_, lean_object* v_auxDeclToFullName_2784_, lean_object* v_currNamespace_2785_, lean_object* v_givenNameView_2786_, lean_object* v_x_2787_){
_start:
{
if (lean_obj_tag(v_x_2787_) == 0)
{
lean_dec_ref(v_givenNameView_2786_);
lean_dec(v_currNamespace_2785_);
lean_dec(v_auxDeclToFullName_2784_);
lean_dec_ref(v___f_2783_);
lean_dec(v_givenName_2781_);
lean_dec_ref(v_matchLocalDecl_x3f_2780_);
return v_x_2787_;
}
else
{
lean_object* v_val_2788_; uint8_t v___x_2789_; 
v_val_2788_ = lean_ctor_get(v_x_2787_, 0);
v___x_2789_ = l_Lean_LocalDecl_isAuxDecl(v_val_2788_);
if (v___x_2789_ == 0)
{
lean_object* v___x_2790_; 
lean_inc(v_val_2788_);
lean_dec_ref_known(v_x_2787_, 1);
lean_dec_ref(v_givenNameView_2786_);
lean_dec(v_currNamespace_2785_);
lean_dec(v_auxDeclToFullName_2784_);
lean_dec_ref(v___f_2783_);
v___x_2790_ = lean_apply_2(v_matchLocalDecl_x3f_2780_, v_val_2788_, v_givenName_2781_);
return v___x_2790_;
}
else
{
if (v_skipAuxDecl_2782_ == 0)
{
if (v___x_2789_ == 0)
{
lean_object* v___x_2791_; 
lean_dec_ref_known(v_x_2787_, 1);
lean_dec_ref(v_givenNameView_2786_);
lean_dec(v_currNamespace_2785_);
lean_dec(v_auxDeclToFullName_2784_);
lean_dec_ref(v___f_2783_);
lean_dec(v_givenName_2781_);
lean_dec_ref(v_matchLocalDecl_x3f_2780_);
v___x_2791_ = lean_box(0);
return v___x_2791_;
}
else
{
lean_object* v___x_2792_; lean_object* v___x_2793_; 
v___x_2792_ = l_Lean_LocalDecl_fvarId(v_val_2788_);
v___x_2793_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v___f_2783_, v_auxDeclToFullName_2784_, v___x_2792_);
if (lean_obj_tag(v___x_2793_) == 1)
{
lean_object* v_val_2794_; lean_object* v_fullDeclView_2795_; lean_object* v___y_2797_; lean_object* v_name_2818_; lean_object* v___x_2819_; 
lean_dec(v_givenName_2781_);
lean_dec_ref(v_matchLocalDecl_x3f_2780_);
v_val_2794_ = lean_ctor_get(v___x_2793_, 0);
lean_inc(v_val_2794_);
lean_dec_ref_known(v___x_2793_, 1);
v_fullDeclView_2795_ = l_Lean_extractMacroScopes(v_val_2794_);
v_name_2818_ = lean_ctor_get(v_fullDeclView_2795_, 0);
lean_inc_n(v_name_2818_, 2);
v___x_2819_ = lean_private_to_user_name(v_name_2818_);
if (lean_obj_tag(v___x_2819_) == 0)
{
v___y_2797_ = v_name_2818_;
goto v___jp_2796_;
}
else
{
lean_object* v_val_2820_; 
lean_dec(v_name_2818_);
v_val_2820_ = lean_ctor_get(v___x_2819_, 0);
lean_inc(v_val_2820_);
lean_dec_ref_known(v___x_2819_, 1);
v___y_2797_ = v_val_2820_;
goto v___jp_2796_;
}
v___jp_2796_:
{
lean_object* v_imported_2798_; lean_object* v_ctx_2799_; lean_object* v_scopes_2800_; lean_object* v___x_2802_; uint8_t v_isShared_2803_; uint8_t v_isSharedCheck_2816_; 
v_imported_2798_ = lean_ctor_get(v_fullDeclView_2795_, 1);
v_ctx_2799_ = lean_ctor_get(v_fullDeclView_2795_, 2);
v_scopes_2800_ = lean_ctor_get(v_fullDeclView_2795_, 3);
v_isSharedCheck_2816_ = !lean_is_exclusive(v_fullDeclView_2795_);
if (v_isSharedCheck_2816_ == 0)
{
lean_object* v_unused_2817_; 
v_unused_2817_ = lean_ctor_get(v_fullDeclView_2795_, 0);
lean_dec(v_unused_2817_);
v___x_2802_ = v_fullDeclView_2795_;
v_isShared_2803_ = v_isSharedCheck_2816_;
goto v_resetjp_2801_;
}
else
{
lean_inc(v_scopes_2800_);
lean_inc(v_ctx_2799_);
lean_inc(v_imported_2798_);
lean_dec(v_fullDeclView_2795_);
v___x_2802_ = lean_box(0);
v_isShared_2803_ = v_isSharedCheck_2816_;
goto v_resetjp_2801_;
}
v_resetjp_2801_:
{
lean_object* v_fullDeclView_2805_; 
if (v_isShared_2803_ == 0)
{
lean_ctor_set(v___x_2802_, 0, v___y_2797_);
v_fullDeclView_2805_ = v___x_2802_;
goto v_reusejp_2804_;
}
else
{
lean_object* v_reuseFailAlloc_2815_; 
v_reuseFailAlloc_2815_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2815_, 0, v___y_2797_);
lean_ctor_set(v_reuseFailAlloc_2815_, 1, v_imported_2798_);
lean_ctor_set(v_reuseFailAlloc_2815_, 2, v_ctx_2799_);
lean_ctor_set(v_reuseFailAlloc_2815_, 3, v_scopes_2800_);
v_fullDeclView_2805_ = v_reuseFailAlloc_2815_;
goto v_reusejp_2804_;
}
v_reusejp_2804_:
{
lean_object* v_fullDeclName_2806_; uint8_t v___x_2807_; 
lean_inc_ref(v_fullDeclView_2805_);
v_fullDeclName_2806_ = l_Lean_MacroScopesView_review(v_fullDeclView_2805_);
v___x_2807_ = l_Lean_Name_isPrefixOf(v_currNamespace_2785_, v_fullDeclName_2806_);
if (v___x_2807_ == 0)
{
lean_object* v___x_2808_; 
lean_inc(v_val_2788_);
lean_dec_ref(v_fullDeclView_2805_);
lean_dec_ref_known(v_x_2787_, 1);
v___x_2808_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_go(v_val_2788_, v_givenNameView_2786_, v_fullDeclName_2806_, v_currNamespace_2785_);
lean_dec(v_fullDeclName_2806_);
return v___x_2808_;
}
else
{
lean_object* v___x_2809_; lean_object* v_localDeclNameView_2810_; uint8_t v___x_2811_; 
lean_dec(v_fullDeclName_2806_);
lean_dec(v_currNamespace_2785_);
v___x_2809_ = l_Lean_LocalDecl_userName(v_val_2788_);
v_localDeclNameView_2810_ = l_Lean_extractMacroScopes(v___x_2809_);
v___x_2811_ = l_Lean_MacroScopesView_isSuffixOf(v_localDeclNameView_2810_, v_givenNameView_2786_);
lean_dec_ref(v_localDeclNameView_2810_);
if (v___x_2811_ == 0)
{
lean_object* v___x_2812_; 
lean_dec_ref(v_fullDeclView_2805_);
lean_dec_ref_known(v_x_2787_, 1);
lean_dec_ref(v_givenNameView_2786_);
v___x_2812_ = lean_box(0);
return v___x_2812_;
}
else
{
uint8_t v___x_2813_; 
v___x_2813_ = l_Lean_MacroScopesView_isSuffixOf(v_givenNameView_2786_, v_fullDeclView_2805_);
lean_dec_ref(v_fullDeclView_2805_);
lean_dec_ref(v_givenNameView_2786_);
if (v___x_2813_ == 0)
{
lean_object* v___x_2814_; 
lean_dec_ref_known(v_x_2787_, 1);
v___x_2814_ = lean_box(0);
return v___x_2814_;
}
else
{
return v_x_2787_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2821_; 
lean_inc(v_val_2788_);
lean_dec(v___x_2793_);
lean_dec_ref_known(v_x_2787_, 1);
lean_dec_ref(v_givenNameView_2786_);
lean_dec(v_currNamespace_2785_);
v___x_2821_ = lean_apply_2(v_matchLocalDecl_x3f_2780_, v_val_2788_, v_givenName_2781_);
return v___x_2821_;
}
}
}
else
{
lean_object* v___x_2822_; 
lean_dec_ref_known(v_x_2787_, 1);
lean_dec_ref(v_givenNameView_2786_);
lean_dec(v_currNamespace_2785_);
lean_dec(v_auxDeclToFullName_2784_);
lean_dec_ref(v___f_2783_);
lean_dec(v_givenName_2781_);
lean_dec_ref(v_matchLocalDecl_x3f_2780_);
v___x_2822_ = lean_box(0);
return v___x_2822_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__1___boxed(lean_object* v_matchLocalDecl_x3f_2823_, lean_object* v_givenName_2824_, lean_object* v_skipAuxDecl_2825_, lean_object* v___f_2826_, lean_object* v_auxDeclToFullName_2827_, lean_object* v_currNamespace_2828_, lean_object* v_givenNameView_2829_, lean_object* v_x_2830_){
_start:
{
uint8_t v_skipAuxDecl_boxed_2831_; lean_object* v_res_2832_; 
v_skipAuxDecl_boxed_2831_ = lean_unbox(v_skipAuxDecl_2825_);
v_res_2832_ = l_Lean_resolveLocalName___redArg___lam__1(v_matchLocalDecl_x3f_2823_, v_givenName_2824_, v_skipAuxDecl_boxed_2831_, v___f_2826_, v_auxDeclToFullName_2827_, v_currNamespace_2828_, v_givenNameView_2829_, v_x_2830_);
return v_res_2832_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__2(lean_object* v_localDecl_x3f_2833_, lean_object* v_matchLocalDecl_x3f_2834_, lean_object* v_givenName_2835_, lean_object* v_x_2836_){
_start:
{
if (lean_obj_tag(v_x_2836_) == 0)
{
lean_dec(v_givenName_2835_);
lean_dec_ref(v_matchLocalDecl_x3f_2834_);
return v_x_2836_;
}
else
{
lean_object* v_val_2837_; uint8_t v___x_2838_; 
v_val_2837_ = lean_ctor_get(v_x_2836_, 0);
lean_inc(v_val_2837_);
lean_dec_ref_known(v_x_2836_, 1);
v___x_2838_ = l_Lean_LocalDecl_isAuxDecl(v_val_2837_);
if (v___x_2838_ == 0)
{
lean_dec(v_val_2837_);
lean_dec(v_givenName_2835_);
lean_dec_ref(v_matchLocalDecl_x3f_2834_);
lean_inc(v_localDecl_x3f_2833_);
return v_localDecl_x3f_2833_;
}
else
{
lean_object* v___x_2839_; 
v___x_2839_ = lean_apply_2(v_matchLocalDecl_x3f_2834_, v_val_2837_, v_givenName_2835_);
return v___x_2839_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__2___boxed(lean_object* v_localDecl_x3f_2840_, lean_object* v_matchLocalDecl_x3f_2841_, lean_object* v_givenName_2842_, lean_object* v_x_2843_){
_start:
{
lean_object* v_res_2844_; 
v_res_2844_ = l_Lean_resolveLocalName___redArg___lam__2(v_localDecl_x3f_2840_, v_matchLocalDecl_x3f_2841_, v_givenName_2842_, v_x_2843_);
lean_dec(v_localDecl_x3f_2840_);
return v_res_2844_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__3(lean_object* v_lctx_2864_, lean_object* v_matchLocalDecl_x3f_2865_, lean_object* v___f_2866_, lean_object* v_auxDeclToFullName_2867_, lean_object* v_currNamespace_2868_, lean_object* v_givenNameView_2869_, uint8_t v_skipAuxDecl_2870_){
_start:
{
lean_object* v_decls_2871_; lean_object* v_givenName_2872_; lean_object* v___x_2873_; lean_object* v___f_2874_; lean_object* v___x_2875_; lean_object* v_localDecl_x3f_2876_; 
v_decls_2871_ = lean_ctor_get(v_lctx_2864_, 1);
lean_inc_ref_n(v_decls_2871_, 2);
lean_dec_ref(v_lctx_2864_);
lean_inc_ref(v_givenNameView_2869_);
v_givenName_2872_ = l_Lean_MacroScopesView_review(v_givenNameView_2869_);
v___x_2873_ = lean_box(v_skipAuxDecl_2870_);
lean_inc(v_givenName_2872_);
lean_inc_ref(v_matchLocalDecl_x3f_2865_);
v___f_2874_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_2874_, 0, v_matchLocalDecl_x3f_2865_);
lean_closure_set(v___f_2874_, 1, v_givenName_2872_);
lean_closure_set(v___f_2874_, 2, v___x_2873_);
lean_closure_set(v___f_2874_, 3, v___f_2866_);
lean_closure_set(v___f_2874_, 4, v_auxDeclToFullName_2867_);
lean_closure_set(v___f_2874_, 5, v_currNamespace_2868_);
lean_closure_set(v___f_2874_, 6, v_givenNameView_2869_);
v___x_2875_ = ((lean_object*)(l_Lean_resolveLocalName___redArg___lam__3___closed__9));
v_localDecl_x3f_2876_ = l_Lean_PersistentArray_findSomeRevM_x3f___redArg(v___x_2875_, v_decls_2871_, v___f_2874_);
if (lean_obj_tag(v_localDecl_x3f_2876_) == 0)
{
if (v_skipAuxDecl_2870_ == 0)
{
lean_object* v___f_2877_; lean_object* v___x_2878_; 
v___f_2877_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_2877_, 0, v_localDecl_x3f_2876_);
lean_closure_set(v___f_2877_, 1, v_matchLocalDecl_x3f_2865_);
lean_closure_set(v___f_2877_, 2, v_givenName_2872_);
v___x_2878_ = l_Lean_PersistentArray_findSomeRevM_x3f___redArg(v___x_2875_, v_decls_2871_, v___f_2877_);
return v___x_2878_;
}
else
{
lean_dec(v_givenName_2872_);
lean_dec_ref(v_decls_2871_);
lean_dec_ref(v_matchLocalDecl_x3f_2865_);
return v_localDecl_x3f_2876_;
}
}
else
{
lean_dec(v_givenName_2872_);
lean_dec_ref(v_decls_2871_);
lean_dec_ref(v_matchLocalDecl_x3f_2865_);
return v_localDecl_x3f_2876_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__3___boxed(lean_object* v_lctx_2879_, lean_object* v_matchLocalDecl_x3f_2880_, lean_object* v___f_2881_, lean_object* v_auxDeclToFullName_2882_, lean_object* v_currNamespace_2883_, lean_object* v_givenNameView_2884_, lean_object* v_skipAuxDecl_2885_){
_start:
{
uint8_t v_skipAuxDecl_boxed_2886_; lean_object* v_res_2887_; 
v_skipAuxDecl_boxed_2886_ = lean_unbox(v_skipAuxDecl_2885_);
v_res_2887_ = l_Lean_resolveLocalName___redArg___lam__3(v_lctx_2879_, v_matchLocalDecl_x3f_2880_, v___f_2881_, v_auxDeclToFullName_2882_, v_currNamespace_2883_, v_givenNameView_2884_, v_skipAuxDecl_boxed_2886_);
return v_res_2887_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__4(lean_object* v_n_2888_, lean_object* v_lctx_2889_, lean_object* v_matchLocalDecl_x3f_2890_, lean_object* v___f_2891_, lean_object* v_auxDeclToFullName_2892_, lean_object* v_inst_2893_, lean_object* v_inst_2894_, lean_object* v_inst_2895_, lean_object* v_inst_2896_, lean_object* v_inst_2897_, lean_object* v_inst_2898_, lean_object* v_currNamespace_2899_){
_start:
{
lean_object* v_view_2900_; lean_object* v_name_2901_; lean_object* v_findLocalDecl_x3f_2902_; lean_object* v___x_2903_; uint8_t v___x_2904_; lean_object* v___x_2905_; 
v_view_2900_ = l_Lean_extractMacroScopes(v_n_2888_);
v_name_2901_ = lean_ctor_get(v_view_2900_, 0);
lean_inc(v_name_2901_);
v_findLocalDecl_x3f_2902_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___redArg___lam__3___boxed), 7, 5);
lean_closure_set(v_findLocalDecl_x3f_2902_, 0, v_lctx_2889_);
lean_closure_set(v_findLocalDecl_x3f_2902_, 1, v_matchLocalDecl_x3f_2890_);
lean_closure_set(v_findLocalDecl_x3f_2902_, 2, v___f_2891_);
lean_closure_set(v_findLocalDecl_x3f_2902_, 3, v_auxDeclToFullName_2892_);
lean_closure_set(v_findLocalDecl_x3f_2902_, 4, v_currNamespace_2899_);
v___x_2903_ = lean_box(0);
v___x_2904_ = 0;
v___x_2905_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg(v_inst_2893_, v_inst_2894_, v_inst_2895_, v_inst_2896_, v_inst_2897_, v_inst_2898_, v_view_2900_, v_findLocalDecl_x3f_2902_, v_name_2901_, v___x_2903_, v___x_2904_);
return v___x_2905_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__5(lean_object* v_inst_2906_, lean_object* v_n_2907_, lean_object* v_lctx_2908_, lean_object* v_matchLocalDecl_x3f_2909_, lean_object* v___f_2910_, lean_object* v_inst_2911_, lean_object* v_inst_2912_, lean_object* v_inst_2913_, lean_object* v_inst_2914_, lean_object* v_inst_2915_, lean_object* v_toBind_2916_, lean_object* v_____do__lift_2917_){
_start:
{
lean_object* v_auxDeclToFullName_2918_; lean_object* v_getCurrNamespace_2919_; lean_object* v___f_2920_; lean_object* v___x_2921_; 
v_auxDeclToFullName_2918_ = lean_ctor_get(v_____do__lift_2917_, 2);
lean_inc(v_auxDeclToFullName_2918_);
lean_dec_ref(v_____do__lift_2917_);
v_getCurrNamespace_2919_ = lean_ctor_get(v_inst_2906_, 0);
lean_inc(v_getCurrNamespace_2919_);
v___f_2920_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___redArg___lam__4), 12, 11);
lean_closure_set(v___f_2920_, 0, v_n_2907_);
lean_closure_set(v___f_2920_, 1, v_lctx_2908_);
lean_closure_set(v___f_2920_, 2, v_matchLocalDecl_x3f_2909_);
lean_closure_set(v___f_2920_, 3, v___f_2910_);
lean_closure_set(v___f_2920_, 4, v_auxDeclToFullName_2918_);
lean_closure_set(v___f_2920_, 5, v_inst_2911_);
lean_closure_set(v___f_2920_, 6, v_inst_2906_);
lean_closure_set(v___f_2920_, 7, v_inst_2912_);
lean_closure_set(v___f_2920_, 8, v_inst_2913_);
lean_closure_set(v___f_2920_, 9, v_inst_2914_);
lean_closure_set(v___f_2920_, 10, v_inst_2915_);
v___x_2921_ = lean_apply_4(v_toBind_2916_, lean_box(0), lean_box(0), v_getCurrNamespace_2919_, v___f_2920_);
return v___x_2921_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__6(lean_object* v_inst_2922_, lean_object* v_n_2923_, lean_object* v_matchLocalDecl_x3f_2924_, lean_object* v___f_2925_, lean_object* v_inst_2926_, lean_object* v_inst_2927_, lean_object* v_inst_2928_, lean_object* v_inst_2929_, lean_object* v_inst_2930_, lean_object* v_toBind_2931_, lean_object* v_inst_2932_, lean_object* v_lctx_2933_){
_start:
{
lean_object* v___f_2934_; lean_object* v___x_2935_; 
lean_inc(v_toBind_2931_);
v___f_2934_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___redArg___lam__5), 12, 11);
lean_closure_set(v___f_2934_, 0, v_inst_2922_);
lean_closure_set(v___f_2934_, 1, v_n_2923_);
lean_closure_set(v___f_2934_, 2, v_lctx_2933_);
lean_closure_set(v___f_2934_, 3, v_matchLocalDecl_x3f_2924_);
lean_closure_set(v___f_2934_, 4, v___f_2925_);
lean_closure_set(v___f_2934_, 5, v_inst_2926_);
lean_closure_set(v___f_2934_, 6, v_inst_2927_);
lean_closure_set(v___f_2934_, 7, v_inst_2928_);
lean_closure_set(v___f_2934_, 8, v_inst_2929_);
lean_closure_set(v___f_2934_, 9, v_inst_2930_);
lean_closure_set(v___f_2934_, 10, v_toBind_2931_);
v___x_2935_ = lean_apply_4(v_toBind_2931_, lean_box(0), lean_box(0), v_inst_2932_, v___f_2934_);
return v___x_2935_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg(lean_object* v_inst_2938_, lean_object* v_inst_2939_, lean_object* v_inst_2940_, lean_object* v_inst_2941_, lean_object* v_inst_2942_, lean_object* v_inst_2943_, lean_object* v_inst_2944_, lean_object* v_n_2945_){
_start:
{
lean_object* v_toBind_2946_; lean_object* v___f_2947_; lean_object* v_matchLocalDecl_x3f_2948_; lean_object* v___f_2949_; lean_object* v___x_2950_; 
v_toBind_2946_ = lean_ctor_get(v_inst_2938_, 1);
lean_inc_n(v_toBind_2946_, 2);
v___f_2947_ = ((lean_object*)(l_Lean_resolveLocalName___redArg___closed__0));
v_matchLocalDecl_x3f_2948_ = ((lean_object*)(l_Lean_resolveLocalName___redArg___closed__1));
lean_inc(v_inst_2944_);
v___f_2949_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___redArg___lam__6), 12, 11);
lean_closure_set(v___f_2949_, 0, v_inst_2939_);
lean_closure_set(v___f_2949_, 1, v_n_2945_);
lean_closure_set(v___f_2949_, 2, v_matchLocalDecl_x3f_2948_);
lean_closure_set(v___f_2949_, 3, v___f_2947_);
lean_closure_set(v___f_2949_, 4, v_inst_2938_);
lean_closure_set(v___f_2949_, 5, v_inst_2940_);
lean_closure_set(v___f_2949_, 6, v_inst_2941_);
lean_closure_set(v___f_2949_, 7, v_inst_2942_);
lean_closure_set(v___f_2949_, 8, v_inst_2943_);
lean_closure_set(v___f_2949_, 9, v_toBind_2946_);
lean_closure_set(v___f_2949_, 10, v_inst_2944_);
v___x_2950_ = lean_apply_4(v_toBind_2946_, lean_box(0), lean_box(0), v_inst_2944_, v___f_2949_);
return v___x_2950_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName(lean_object* v_m_2951_, lean_object* v_inst_2952_, lean_object* v_inst_2953_, lean_object* v_inst_2954_, lean_object* v_inst_2955_, lean_object* v_inst_2956_, lean_object* v_inst_2957_, lean_object* v_inst_2958_, lean_object* v_n_2959_){
_start:
{
lean_object* v___x_2960_; 
v___x_2960_ = l_Lean_resolveLocalName___redArg(v_inst_2952_, v_inst_2953_, v_inst_2954_, v_inst_2955_, v_inst_2956_, v_inst_2957_, v_inst_2958_, v_n_2959_);
return v___x_2960_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__0(lean_object* v_toPure_2961_, uint8_t v_____do__lift_2962_){
_start:
{
lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; 
v___x_2963_ = lean_box(v_____do__lift_2962_);
v___x_2964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2964_, 0, v___x_2963_);
v___x_2965_ = lean_apply_2(v_toPure_2961_, lean_box(0), v___x_2964_);
return v___x_2965_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__0___boxed(lean_object* v_toPure_2966_, lean_object* v_____do__lift_2967_){
_start:
{
uint8_t v_____do__lift_1160__boxed_2968_; lean_object* v_res_2969_; 
v_____do__lift_1160__boxed_2968_ = lean_unbox(v_____do__lift_2967_);
v_res_2969_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__0(v_toPure_2966_, v_____do__lift_1160__boxed_2968_);
return v_res_2969_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__1(lean_object* v_toPure_2970_, lean_object* v___y_2971_, lean_object* v_____do__lift_2972_){
_start:
{
if (lean_obj_tag(v_____do__lift_2972_) == 0)
{
lean_object* v___x_2973_; lean_object* v___x_2974_; 
lean_dec(v___y_2971_);
v___x_2973_ = lean_box(0);
v___x_2974_ = lean_apply_2(v_toPure_2970_, lean_box(0), v___x_2973_);
return v___x_2974_;
}
else
{
lean_object* v___x_2976_; uint8_t v_isShared_2977_; uint8_t v_isSharedCheck_2982_; 
v_isSharedCheck_2982_ = !lean_is_exclusive(v_____do__lift_2972_);
if (v_isSharedCheck_2982_ == 0)
{
lean_object* v_unused_2983_; 
v_unused_2983_ = lean_ctor_get(v_____do__lift_2972_, 0);
lean_dec(v_unused_2983_);
v___x_2976_ = v_____do__lift_2972_;
v_isShared_2977_ = v_isSharedCheck_2982_;
goto v_resetjp_2975_;
}
else
{
lean_dec(v_____do__lift_2972_);
v___x_2976_ = lean_box(0);
v_isShared_2977_ = v_isSharedCheck_2982_;
goto v_resetjp_2975_;
}
v_resetjp_2975_:
{
lean_object* v___x_2979_; 
if (v_isShared_2977_ == 0)
{
lean_ctor_set(v___x_2976_, 0, v___y_2971_);
v___x_2979_ = v___x_2976_;
goto v_reusejp_2978_;
}
else
{
lean_object* v_reuseFailAlloc_2981_; 
v_reuseFailAlloc_2981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2981_, 0, v___y_2971_);
v___x_2979_ = v_reuseFailAlloc_2981_;
goto v_reusejp_2978_;
}
v_reusejp_2978_:
{
lean_object* v___x_2980_; 
v___x_2980_ = lean_apply_2(v_toPure_2970_, lean_box(0), v___x_2979_);
return v___x_2980_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2(lean_object* v_toPure_2986_, lean_object* v_toBind_2987_, lean_object* v___f_2988_, lean_object* v_____do__lift_2989_){
_start:
{
if (lean_obj_tag(v_____do__lift_2989_) == 0)
{
lean_object* v___x_2990_; lean_object* v___x_2991_; 
lean_dec(v___f_2988_);
lean_dec(v_toBind_2987_);
v___x_2990_ = lean_box(0);
v___x_2991_ = lean_apply_2(v_toPure_2986_, lean_box(0), v___x_2990_);
return v___x_2991_;
}
else
{
lean_object* v_val_2992_; uint8_t v___x_2993_; 
v_val_2992_ = lean_ctor_get(v_____do__lift_2989_, 0);
v___x_2993_ = lean_unbox(v_val_2992_);
if (v___x_2993_ == 0)
{
lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; 
v___x_2994_ = lean_box(0);
v___x_2995_ = lean_apply_2(v_toPure_2986_, lean_box(0), v___x_2994_);
v___x_2996_ = lean_apply_4(v_toBind_2987_, lean_box(0), lean_box(0), v___x_2995_, v___f_2988_);
return v___x_2996_;
}
else
{
lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; 
v___x_2997_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2___closed__0));
v___x_2998_ = lean_apply_2(v_toPure_2986_, lean_box(0), v___x_2997_);
v___x_2999_ = lean_apply_4(v_toBind_2987_, lean_box(0), lean_box(0), v___x_2998_, v___f_2988_);
return v___x_2999_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2___boxed(lean_object* v_toPure_3000_, lean_object* v_toBind_3001_, lean_object* v___f_3002_, lean_object* v_____do__lift_3003_){
_start:
{
lean_object* v_res_3004_; 
v_res_3004_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2(v_toPure_3000_, v_toBind_3001_, v___f_3002_, v_____do__lift_3003_);
lean_dec(v_____do__lift_3003_);
return v_res_3004_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__3(lean_object* v_toPure_3005_, lean_object* v_filter_3006_, lean_object* v___y_3007_, lean_object* v_toBind_3008_, lean_object* v___f_3009_, lean_object* v___f_3010_, lean_object* v_____do__lift_3011_){
_start:
{
if (lean_obj_tag(v_____do__lift_3011_) == 0)
{
lean_object* v___x_3012_; lean_object* v___x_3013_; 
lean_dec(v___f_3010_);
lean_dec(v___f_3009_);
lean_dec(v_toBind_3008_);
lean_dec(v___y_3007_);
lean_dec(v_filter_3006_);
v___x_3012_ = lean_box(0);
v___x_3013_ = lean_apply_2(v_toPure_3005_, lean_box(0), v___x_3012_);
return v___x_3013_;
}
else
{
lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; 
lean_dec(v_toPure_3005_);
v___x_3014_ = lean_apply_1(v_filter_3006_, v___y_3007_);
lean_inc(v_toBind_3008_);
v___x_3015_ = lean_apply_4(v_toBind_3008_, lean_box(0), lean_box(0), v___x_3014_, v___f_3009_);
v___x_3016_ = lean_apply_4(v_toBind_3008_, lean_box(0), lean_box(0), v___x_3015_, v___f_3010_);
return v___x_3016_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__3___boxed(lean_object* v_toPure_3017_, lean_object* v_filter_3018_, lean_object* v___y_3019_, lean_object* v_toBind_3020_, lean_object* v___f_3021_, lean_object* v___f_3022_, lean_object* v_____do__lift_3023_){
_start:
{
lean_object* v_res_3024_; 
v_res_3024_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__3(v_toPure_3017_, v_filter_3018_, v___y_3019_, v_toBind_3020_, v___f_3021_, v___f_3022_, v_____do__lift_3023_);
lean_dec(v_____do__lift_3023_);
return v_res_3024_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__4(lean_object* v_toPure_3025_, lean_object* v_n_u2080_3026_, lean_object* v_toBind_3027_, lean_object* v___f_3028_, lean_object* v_____do__lift_3029_){
_start:
{
if (lean_obj_tag(v_____do__lift_3029_) == 0)
{
lean_object* v___x_3033_; lean_object* v___x_3034_; 
lean_dec(v___f_3028_);
lean_dec(v_toBind_3027_);
v___x_3033_ = lean_box(0);
v___x_3034_ = lean_apply_2(v_toPure_3025_, lean_box(0), v___x_3033_);
return v___x_3034_;
}
else
{
lean_object* v_val_3035_; 
v_val_3035_ = lean_ctor_get(v_____do__lift_3029_, 0);
if (lean_obj_tag(v_val_3035_) == 1)
{
lean_object* v_tail_3036_; 
v_tail_3036_ = lean_ctor_get(v_val_3035_, 1);
if (lean_obj_tag(v_tail_3036_) == 0)
{
lean_object* v_head_3037_; lean_object* v_fst_3038_; uint8_t v___x_3039_; 
v_head_3037_ = lean_ctor_get(v_val_3035_, 0);
v_fst_3038_ = lean_ctor_get(v_head_3037_, 0);
v___x_3039_ = lean_name_eq(v_fst_3038_, v_n_u2080_3026_);
if (v___x_3039_ == 0)
{
lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; 
v___x_3040_ = lean_box(0);
v___x_3041_ = lean_apply_2(v_toPure_3025_, lean_box(0), v___x_3040_);
v___x_3042_ = lean_apply_4(v_toBind_3027_, lean_box(0), lean_box(0), v___x_3041_, v___f_3028_);
return v___x_3042_;
}
else
{
lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; 
v___x_3043_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2___closed__0));
v___x_3044_ = lean_apply_2(v_toPure_3025_, lean_box(0), v___x_3043_);
v___x_3045_ = lean_apply_4(v_toBind_3027_, lean_box(0), lean_box(0), v___x_3044_, v___f_3028_);
return v___x_3045_;
}
}
else
{
lean_dec(v___f_3028_);
lean_dec(v_toBind_3027_);
goto v___jp_3030_;
}
}
else
{
lean_dec(v___f_3028_);
lean_dec(v_toBind_3027_);
goto v___jp_3030_;
}
}
v___jp_3030_:
{
lean_object* v___x_3031_; lean_object* v___x_3032_; 
v___x_3031_ = lean_box(0);
v___x_3032_ = lean_apply_2(v_toPure_3025_, lean_box(0), v___x_3031_);
return v___x_3032_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__4___boxed(lean_object* v_toPure_3046_, lean_object* v_n_u2080_3047_, lean_object* v_toBind_3048_, lean_object* v___f_3049_, lean_object* v_____do__lift_3050_){
_start:
{
lean_object* v_res_3051_; 
v_res_3051_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__4(v_toPure_3046_, v_n_u2080_3047_, v_toBind_3048_, v___f_3049_, v_____do__lift_3050_);
lean_dec(v_____do__lift_3050_);
lean_dec(v_n_u2080_3047_);
return v_res_3051_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg(lean_object* v_inst_3052_, lean_object* v_inst_3053_, lean_object* v_inst_3054_, lean_object* v_inst_3055_, lean_object* v_inst_3056_, lean_object* v_inst_3057_, lean_object* v_n_u2080_3058_, lean_object* v_filter_3059_, lean_object* v_view_x3f_3060_, lean_object* v_n_3061_){
_start:
{
lean_object* v___f_3062_; lean_object* v___f_3063_; lean_object* v___f_3064_; lean_object* v___f_3065_; lean_object* v___f_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v_toApplicative_3074_; lean_object* v_getEnv_3075_; lean_object* v_modifyEnv_3076_; lean_object* v___x_3078_; uint8_t v_isShared_3079_; uint8_t v_isSharedCheck_3114_; 
lean_inc_ref_n(v_inst_3052_, 8);
v___f_3062_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_3062_, 0, v_inst_3052_);
v___f_3063_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__3), 5, 1);
lean_closure_set(v___f_3063_, 0, v_inst_3052_);
v___f_3064_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__6), 5, 1);
lean_closure_set(v___f_3064_, 0, v_inst_3052_);
v___f_3065_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_3065_, 0, v_inst_3052_);
v___f_3066_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__11), 5, 1);
lean_closure_set(v___f_3066_, 0, v_inst_3052_);
v___x_3067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3067_, 0, v___f_3062_);
lean_ctor_set(v___x_3067_, 1, v___f_3063_);
v___x_3068_ = lean_alloc_closure((void*)(l_OptionT_pure), 4, 2);
lean_closure_set(v___x_3068_, 0, lean_box(0));
lean_closure_set(v___x_3068_, 1, v_inst_3052_);
v___x_3069_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3069_, 0, v___x_3067_);
lean_ctor_set(v___x_3069_, 1, v___x_3068_);
lean_ctor_set(v___x_3069_, 2, v___f_3064_);
lean_ctor_set(v___x_3069_, 3, v___f_3065_);
lean_ctor_set(v___x_3069_, 4, v___f_3066_);
v___x_3070_ = lean_alloc_closure((void*)(l_OptionT_bind), 6, 2);
lean_closure_set(v___x_3070_, 0, lean_box(0));
lean_closure_set(v___x_3070_, 1, v_inst_3052_);
v___x_3071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3071_, 0, v___x_3069_);
lean_ctor_set(v___x_3071_, 1, v___x_3070_);
v___x_3072_ = lean_alloc_closure((void*)(l_OptionT_lift), 4, 2);
lean_closure_set(v___x_3072_, 0, lean_box(0));
lean_closure_set(v___x_3072_, 1, v_inst_3052_);
lean_inc_ref(v___x_3072_);
v___x_3073_ = l_Lean_instMonadResolveNameOfMonadLift___redArg(v___x_3072_, v_inst_3053_);
v_toApplicative_3074_ = lean_ctor_get(v_inst_3052_, 0);
lean_inc_ref(v_toApplicative_3074_);
v_getEnv_3075_ = lean_ctor_get(v_inst_3054_, 0);
v_modifyEnv_3076_ = lean_ctor_get(v_inst_3054_, 1);
v_isSharedCheck_3114_ = !lean_is_exclusive(v_inst_3054_);
if (v_isSharedCheck_3114_ == 0)
{
v___x_3078_ = v_inst_3054_;
v_isShared_3079_ = v_isSharedCheck_3114_;
goto v_resetjp_3077_;
}
else
{
lean_inc(v_modifyEnv_3076_);
lean_inc(v_getEnv_3075_);
lean_dec(v_inst_3054_);
v___x_3078_ = lean_box(0);
v_isShared_3079_ = v_isSharedCheck_3114_;
goto v_resetjp_3077_;
}
v_resetjp_3077_:
{
lean_object* v_toBind_3080_; lean_object* v_toPure_3081_; lean_object* v___f_3082_; lean_object* v___f_3083_; lean_object* v___f_3084_; lean_object* v___x_3085_; lean_object* v___x_3087_; 
v_toBind_3080_ = lean_ctor_get(v_inst_3052_, 1);
lean_inc_n(v_toBind_3080_, 2);
lean_dec_ref(v_inst_3052_);
v_toPure_3081_ = lean_ctor_get(v_toApplicative_3074_, 1);
lean_inc_n(v_toPure_3081_, 3);
lean_dec_ref(v_toApplicative_3074_);
lean_inc_ref(v___x_3072_);
v___f_3082_ = lean_alloc_closure((void*)(l_Lean_instMonadEnvOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3082_, 0, v_modifyEnv_3076_);
lean_closure_set(v___f_3082_, 1, v___x_3072_);
v___f_3083_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3083_, 0, v_toPure_3081_);
v___f_3084_ = lean_alloc_closure((void*)(l_OptionT_lift___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3084_, 0, v_toPure_3081_);
lean_inc_ref(v___f_3084_);
v___x_3085_ = lean_apply_4(v_toBind_3080_, lean_box(0), lean_box(0), v_getEnv_3075_, v___f_3084_);
if (v_isShared_3079_ == 0)
{
lean_ctor_set(v___x_3078_, 1, v___f_3082_);
lean_ctor_set(v___x_3078_, 0, v___x_3085_);
v___x_3087_ = v___x_3078_;
goto v_reusejp_3086_;
}
else
{
lean_object* v_reuseFailAlloc_3113_; 
v_reuseFailAlloc_3113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3113_, 0, v___x_3085_);
lean_ctor_set(v_reuseFailAlloc_3113_, 1, v___f_3082_);
v___x_3087_ = v_reuseFailAlloc_3113_;
goto v_reusejp_3086_;
}
v_reusejp_3086_:
{
lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___f_3090_; lean_object* v___y_3092_; 
lean_inc(v_toBind_3080_);
v___x_3088_ = lean_apply_4(v_toBind_3080_, lean_box(0), lean_box(0), v_inst_3055_, v___f_3084_);
lean_inc_ref(v___x_3072_);
v___x_3089_ = l_Lean_instMonadLogOfMonadLift___redArg(v___x_3072_, v_inst_3056_);
v___f_3090_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3090_, 0, v_inst_3057_);
lean_closure_set(v___f_3090_, 1, v___x_3072_);
if (lean_obj_tag(v_view_x3f_3060_) == 1)
{
lean_object* v_val_3100_; lean_object* v_imported_3101_; lean_object* v_ctx_3102_; lean_object* v_scopes_3103_; lean_object* v___x_3105_; uint8_t v_isShared_3106_; uint8_t v_isSharedCheck_3111_; 
v_val_3100_ = lean_ctor_get(v_view_x3f_3060_, 0);
lean_inc(v_val_3100_);
lean_dec_ref_known(v_view_x3f_3060_, 1);
v_imported_3101_ = lean_ctor_get(v_val_3100_, 1);
v_ctx_3102_ = lean_ctor_get(v_val_3100_, 2);
v_scopes_3103_ = lean_ctor_get(v_val_3100_, 3);
v_isSharedCheck_3111_ = !lean_is_exclusive(v_val_3100_);
if (v_isSharedCheck_3111_ == 0)
{
lean_object* v_unused_3112_; 
v_unused_3112_ = lean_ctor_get(v_val_3100_, 0);
lean_dec(v_unused_3112_);
v___x_3105_ = v_val_3100_;
v_isShared_3106_ = v_isSharedCheck_3111_;
goto v_resetjp_3104_;
}
else
{
lean_inc(v_scopes_3103_);
lean_inc(v_ctx_3102_);
lean_inc(v_imported_3101_);
lean_dec(v_val_3100_);
v___x_3105_ = lean_box(0);
v_isShared_3106_ = v_isSharedCheck_3111_;
goto v_resetjp_3104_;
}
v_resetjp_3104_:
{
lean_object* v___x_3108_; 
if (v_isShared_3106_ == 0)
{
lean_ctor_set(v___x_3105_, 0, v_n_3061_);
v___x_3108_ = v___x_3105_;
goto v_reusejp_3107_;
}
else
{
lean_object* v_reuseFailAlloc_3110_; 
v_reuseFailAlloc_3110_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3110_, 0, v_n_3061_);
lean_ctor_set(v_reuseFailAlloc_3110_, 1, v_imported_3101_);
lean_ctor_set(v_reuseFailAlloc_3110_, 2, v_ctx_3102_);
lean_ctor_set(v_reuseFailAlloc_3110_, 3, v_scopes_3103_);
v___x_3108_ = v_reuseFailAlloc_3110_;
goto v_reusejp_3107_;
}
v_reusejp_3107_:
{
lean_object* v___x_3109_; 
v___x_3109_ = l_Lean_MacroScopesView_review(v___x_3108_);
v___y_3092_ = v___x_3109_;
goto v___jp_3091_;
}
}
}
else
{
lean_dec(v_view_x3f_3060_);
v___y_3092_ = v_n_3061_;
goto v___jp_3091_;
}
v___jp_3091_:
{
lean_object* v___f_3093_; lean_object* v___f_3094_; lean_object* v___f_3095_; lean_object* v___f_3096_; uint8_t v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; 
lean_inc_n(v___y_3092_, 2);
lean_inc_n(v_toPure_3081_, 3);
v___f_3093_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__1), 3, 2);
lean_closure_set(v___f_3093_, 0, v_toPure_3081_);
lean_closure_set(v___f_3093_, 1, v___y_3092_);
lean_inc_n(v_toBind_3080_, 3);
v___f_3094_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_3094_, 0, v_toPure_3081_);
lean_closure_set(v___f_3094_, 1, v_toBind_3080_);
lean_closure_set(v___f_3094_, 2, v___f_3093_);
v___f_3095_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__3___boxed), 7, 6);
lean_closure_set(v___f_3095_, 0, v_toPure_3081_);
lean_closure_set(v___f_3095_, 1, v_filter_3059_);
lean_closure_set(v___f_3095_, 2, v___y_3092_);
lean_closure_set(v___f_3095_, 3, v_toBind_3080_);
lean_closure_set(v___f_3095_, 4, v___f_3083_);
lean_closure_set(v___f_3095_, 5, v___f_3094_);
v___f_3096_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__4___boxed), 5, 4);
lean_closure_set(v___f_3096_, 0, v_toPure_3081_);
lean_closure_set(v___f_3096_, 1, v_n_u2080_3058_);
lean_closure_set(v___f_3096_, 2, v_toBind_3080_);
lean_closure_set(v___f_3096_, 3, v___f_3095_);
v___x_3097_ = 0;
v___x_3098_ = l_Lean_resolveGlobalName___redArg(v___x_3071_, v___x_3073_, v___x_3087_, v___x_3088_, v___x_3089_, v___f_3090_, v___y_3092_, v___x_3097_);
v___x_3099_ = lean_apply_4(v_toBind_3080_, lean_box(0), lean_box(0), v___x_3098_, v___f_3096_);
return v___x_3099_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve(lean_object* v_m_3115_, lean_object* v_inst_3116_, lean_object* v_inst_3117_, lean_object* v_inst_3118_, lean_object* v_inst_3119_, lean_object* v_inst_3120_, lean_object* v_inst_3121_, lean_object* v_n_u2080_3122_, lean_object* v_filter_3123_, lean_object* v_view_x3f_3124_, lean_object* v_n_3125_){
_start:
{
lean_object* v___x_3126_; 
v___x_3126_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg(v_inst_3116_, v_inst_3117_, v_inst_3118_, v_inst_3119_, v_inst_3120_, v_inst_3121_, v_n_u2080_3122_, v_filter_3123_, v_view_x3f_3124_, v_n_3125_);
return v___x_3126_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__0(lean_object* v_toPure_3131_, lean_object* v_____x_3132_){
_start:
{
if (lean_obj_tag(v_____x_3132_) == 0)
{
lean_object* v___x_3133_; lean_object* v___x_3134_; 
v___x_3133_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__0___closed__1));
v___x_3134_ = lean_apply_2(v_toPure_3131_, lean_box(0), v___x_3133_);
return v___x_3134_;
}
else
{
lean_object* v___x_3135_; 
v___x_3135_ = lean_apply_2(v_toPure_3131_, lean_box(0), v_____x_3132_);
return v___x_3135_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__1(lean_object* v_toPure_3136_, lean_object* v_____do__lift_3137_){
_start:
{
if (lean_obj_tag(v_____do__lift_3137_) == 0)
{
lean_object* v___x_3138_; lean_object* v___x_3139_; 
v___x_3138_ = lean_box(0);
v___x_3139_ = lean_apply_2(v_toPure_3136_, lean_box(0), v___x_3138_);
return v___x_3139_;
}
else
{
lean_object* v_val_3140_; lean_object* v___x_3142_; uint8_t v_isShared_3143_; uint8_t v_isSharedCheck_3149_; 
v_val_3140_ = lean_ctor_get(v_____do__lift_3137_, 0);
v_isSharedCheck_3149_ = !lean_is_exclusive(v_____do__lift_3137_);
if (v_isSharedCheck_3149_ == 0)
{
v___x_3142_ = v_____do__lift_3137_;
v_isShared_3143_ = v_isSharedCheck_3149_;
goto v_resetjp_3141_;
}
else
{
lean_inc(v_val_3140_);
lean_dec(v_____do__lift_3137_);
v___x_3142_ = lean_box(0);
v_isShared_3143_ = v_isSharedCheck_3149_;
goto v_resetjp_3141_;
}
v_resetjp_3141_:
{
lean_object* v___x_3144_; lean_object* v___x_3146_; 
v___x_3144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3144_, 0, v_val_3140_);
if (v_isShared_3143_ == 0)
{
lean_ctor_set(v___x_3142_, 0, v___x_3144_);
v___x_3146_ = v___x_3142_;
goto v_reusejp_3145_;
}
else
{
lean_object* v_reuseFailAlloc_3148_; 
v_reuseFailAlloc_3148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3148_, 0, v___x_3144_);
v___x_3146_ = v_reuseFailAlloc_3148_;
goto v_reusejp_3145_;
}
v_reusejp_3145_:
{
lean_object* v___x_3147_; 
v___x_3147_ = lean_apply_2(v_toPure_3136_, lean_box(0), v___x_3146_);
return v___x_3147_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__2(lean_object* v_toPure_3150_, lean_object* v___x_3151_, lean_object* v_____do__lift_3152_){
_start:
{
if (lean_obj_tag(v_____do__lift_3152_) == 0)
{
lean_object* v___x_3153_; 
v___x_3153_ = lean_apply_2(v_toPure_3150_, lean_box(0), v___x_3151_);
return v___x_3153_;
}
else
{
lean_object* v_val_3154_; lean_object* v_fst_3155_; lean_object* v___x_3156_; 
lean_dec(v___x_3151_);
v_val_3154_ = lean_ctor_get(v_____do__lift_3152_, 0);
lean_inc(v_val_3154_);
lean_dec_ref_known(v_____do__lift_3152_, 1);
v_fst_3155_ = lean_ctor_get(v_val_3154_, 0);
lean_inc(v_fst_3155_);
lean_dec(v_val_3154_);
v___x_3156_ = lean_apply_2(v_toPure_3150_, lean_box(0), v_fst_3155_);
return v___x_3156_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__3(lean_object* v_toPure_3157_, lean_object* v___x_3158_, lean_object* v___x_3159_, lean_object* v_____do__lift_3160_){
_start:
{
if (lean_obj_tag(v_____do__lift_3160_) == 0)
{
lean_object* v___x_3161_; lean_object* v___x_3162_; 
lean_dec(v___x_3159_);
lean_dec(v___x_3158_);
v___x_3161_ = lean_box(0);
v___x_3162_ = lean_apply_2(v_toPure_3157_, lean_box(0), v___x_3161_);
return v___x_3162_;
}
else
{
lean_object* v_val_3163_; lean_object* v___x_3165_; uint8_t v_isShared_3166_; uint8_t v_isSharedCheck_3194_; 
v_val_3163_ = lean_ctor_get(v_____do__lift_3160_, 0);
v_isSharedCheck_3194_ = !lean_is_exclusive(v_____do__lift_3160_);
if (v_isSharedCheck_3194_ == 0)
{
v___x_3165_ = v_____do__lift_3160_;
v_isShared_3166_ = v_isSharedCheck_3194_;
goto v_resetjp_3164_;
}
else
{
lean_inc(v_val_3163_);
lean_dec(v_____do__lift_3160_);
v___x_3165_ = lean_box(0);
v_isShared_3166_ = v_isSharedCheck_3194_;
goto v_resetjp_3164_;
}
v_resetjp_3164_:
{
if (lean_obj_tag(v_val_3163_) == 0)
{
lean_object* v_a_3167_; lean_object* v___x_3169_; uint8_t v_isShared_3170_; uint8_t v_isSharedCheck_3180_; 
lean_dec(v___x_3159_);
v_a_3167_ = lean_ctor_get(v_val_3163_, 0);
v_isSharedCheck_3180_ = !lean_is_exclusive(v_val_3163_);
if (v_isSharedCheck_3180_ == 0)
{
v___x_3169_ = v_val_3163_;
v_isShared_3170_ = v_isSharedCheck_3180_;
goto v_resetjp_3168_;
}
else
{
lean_inc(v_a_3167_);
lean_dec(v_val_3163_);
v___x_3169_ = lean_box(0);
v_isShared_3170_ = v_isSharedCheck_3180_;
goto v_resetjp_3168_;
}
v_resetjp_3168_:
{
lean_object* v___x_3172_; 
if (v_isShared_3166_ == 0)
{
lean_ctor_set(v___x_3165_, 0, v_a_3167_);
v___x_3172_ = v___x_3165_;
goto v_reusejp_3171_;
}
else
{
lean_object* v_reuseFailAlloc_3179_; 
v_reuseFailAlloc_3179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3179_, 0, v_a_3167_);
v___x_3172_ = v_reuseFailAlloc_3179_;
goto v_reusejp_3171_;
}
v_reusejp_3171_:
{
lean_object* v___x_3173_; lean_object* v___x_3175_; 
v___x_3173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3173_, 0, v___x_3172_);
lean_ctor_set(v___x_3173_, 1, v___x_3158_);
if (v_isShared_3170_ == 0)
{
lean_ctor_set(v___x_3169_, 0, v___x_3173_);
v___x_3175_ = v___x_3169_;
goto v_reusejp_3174_;
}
else
{
lean_object* v_reuseFailAlloc_3178_; 
v_reuseFailAlloc_3178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3178_, 0, v___x_3173_);
v___x_3175_ = v_reuseFailAlloc_3178_;
goto v_reusejp_3174_;
}
v_reusejp_3174_:
{
lean_object* v___x_3176_; lean_object* v___x_3177_; 
v___x_3176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3176_, 0, v___x_3175_);
v___x_3177_ = lean_apply_2(v_toPure_3157_, lean_box(0), v___x_3176_);
return v___x_3177_;
}
}
}
}
else
{
lean_object* v___x_3182_; uint8_t v_isShared_3183_; uint8_t v_isSharedCheck_3192_; 
v_isSharedCheck_3192_ = !lean_is_exclusive(v_val_3163_);
if (v_isSharedCheck_3192_ == 0)
{
lean_object* v_unused_3193_; 
v_unused_3193_ = lean_ctor_get(v_val_3163_, 0);
lean_dec(v_unused_3193_);
v___x_3182_ = v_val_3163_;
v_isShared_3183_ = v_isSharedCheck_3192_;
goto v_resetjp_3181_;
}
else
{
lean_dec(v_val_3163_);
v___x_3182_ = lean_box(0);
v_isShared_3183_ = v_isSharedCheck_3192_;
goto v_resetjp_3181_;
}
v_resetjp_3181_:
{
lean_object* v___x_3184_; lean_object* v___x_3186_; 
v___x_3184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3184_, 0, v___x_3159_);
lean_ctor_set(v___x_3184_, 1, v___x_3158_);
if (v_isShared_3183_ == 0)
{
lean_ctor_set(v___x_3182_, 0, v___x_3184_);
v___x_3186_ = v___x_3182_;
goto v_reusejp_3185_;
}
else
{
lean_object* v_reuseFailAlloc_3191_; 
v_reuseFailAlloc_3191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3191_, 0, v___x_3184_);
v___x_3186_ = v_reuseFailAlloc_3191_;
goto v_reusejp_3185_;
}
v_reusejp_3185_:
{
lean_object* v___x_3188_; 
if (v_isShared_3166_ == 0)
{
lean_ctor_set(v___x_3165_, 0, v___x_3186_);
v___x_3188_ = v___x_3165_;
goto v_reusejp_3187_;
}
else
{
lean_object* v_reuseFailAlloc_3190_; 
v_reuseFailAlloc_3190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3190_, 0, v___x_3186_);
v___x_3188_ = v_reuseFailAlloc_3190_;
goto v_reusejp_3187_;
}
v_reusejp_3187_:
{
lean_object* v___x_3189_; 
v___x_3189_ = lean_apply_2(v_toPure_3157_, lean_box(0), v___x_3188_);
return v___x_3189_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__4(lean_object* v_toPure_3195_, lean_object* v___x_3196_, lean_object* v_inst_3197_, lean_object* v_inst_3198_, lean_object* v_inst_3199_, lean_object* v_inst_3200_, lean_object* v_inst_3201_, lean_object* v_inst_3202_, lean_object* v_n_u2080_3203_, lean_object* v_filter_3204_, lean_object* v_view_x3f_3205_, lean_object* v_toBind_3206_, lean_object* v___f_3207_, lean_object* v___f_3208_, lean_object* v_a_3209_, lean_object* v_x_3210_, lean_object* v___y_3211_){
_start:
{
lean_object* v_snd_3212_; lean_object* v___x_3213_; lean_object* v___f_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; 
v_snd_3212_ = lean_ctor_get(v___y_3211_, 1);
lean_inc(v_snd_3212_);
lean_dec_ref(v___y_3211_);
v___x_3213_ = l_Lean_Name_appendCore(v_a_3209_, v_snd_3212_);
lean_inc(v___x_3213_);
v___f_3214_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__3), 4, 3);
lean_closure_set(v___f_3214_, 0, v_toPure_3195_);
lean_closure_set(v___f_3214_, 1, v___x_3213_);
lean_closure_set(v___f_3214_, 2, v___x_3196_);
v___x_3215_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg(v_inst_3197_, v_inst_3198_, v_inst_3199_, v_inst_3200_, v_inst_3201_, v_inst_3202_, v_n_u2080_3203_, v_filter_3204_, v_view_x3f_3205_, v___x_3213_);
lean_inc_n(v_toBind_3206_, 2);
v___x_3216_ = lean_apply_4(v_toBind_3206_, lean_box(0), lean_box(0), v___x_3215_, v___f_3207_);
v___x_3217_ = lean_apply_4(v_toBind_3206_, lean_box(0), lean_box(0), v___x_3216_, v___f_3208_);
v___x_3218_ = lean_apply_4(v_toBind_3206_, lean_box(0), lean_box(0), v___x_3217_, v___f_3214_);
return v___x_3218_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__4___boxed(lean_object** _args){
lean_object* v_toPure_3219_ = _args[0];
lean_object* v___x_3220_ = _args[1];
lean_object* v_inst_3221_ = _args[2];
lean_object* v_inst_3222_ = _args[3];
lean_object* v_inst_3223_ = _args[4];
lean_object* v_inst_3224_ = _args[5];
lean_object* v_inst_3225_ = _args[6];
lean_object* v_inst_3226_ = _args[7];
lean_object* v_n_u2080_3227_ = _args[8];
lean_object* v_filter_3228_ = _args[9];
lean_object* v_view_x3f_3229_ = _args[10];
lean_object* v_toBind_3230_ = _args[11];
lean_object* v___f_3231_ = _args[12];
lean_object* v___f_3232_ = _args[13];
lean_object* v_a_3233_ = _args[14];
lean_object* v_x_3234_ = _args[15];
lean_object* v___y_3235_ = _args[16];
_start:
{
lean_object* v_res_3236_; 
v_res_3236_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__4(v_toPure_3219_, v___x_3220_, v_inst_3221_, v_inst_3222_, v_inst_3223_, v_inst_3224_, v_inst_3225_, v_inst_3226_, v_n_u2080_3227_, v_filter_3228_, v_view_x3f_3229_, v_toBind_3230_, v___f_3231_, v___f_3232_, v_a_3233_, v_x_3234_, v___y_3235_);
lean_dec(v_a_3233_);
return v_res_3236_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__5(lean_object* v_toPure_3240_, lean_object* v_n_3241_, lean_object* v_inst_3242_, lean_object* v_inst_3243_, lean_object* v_inst_3244_, lean_object* v_inst_3245_, lean_object* v_inst_3246_, lean_object* v_inst_3247_, lean_object* v_n_u2080_3248_, lean_object* v_filter_3249_, lean_object* v_view_x3f_3250_, lean_object* v_toBind_3251_, lean_object* v___f_3252_, lean_object* v___f_3253_, lean_object* v___x_3254_, lean_object* v_____do__lift_3255_){
_start:
{
if (lean_obj_tag(v_____do__lift_3255_) == 0)
{
lean_object* v___x_3256_; lean_object* v___x_3257_; 
lean_dec_ref(v___x_3254_);
lean_dec(v___f_3253_);
lean_dec(v___f_3252_);
lean_dec(v_toBind_3251_);
lean_dec(v_view_x3f_3250_);
lean_dec(v_filter_3249_);
lean_dec(v_n_u2080_3248_);
lean_dec(v_inst_3247_);
lean_dec_ref(v_inst_3246_);
lean_dec(v_inst_3245_);
lean_dec_ref(v_inst_3244_);
lean_dec_ref(v_inst_3243_);
lean_dec_ref(v_inst_3242_);
lean_dec(v_n_3241_);
v___x_3256_ = lean_box(0);
v___x_3257_ = lean_apply_2(v_toPure_3240_, lean_box(0), v___x_3256_);
return v___x_3257_;
}
else
{
lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___f_3261_; lean_object* v___f_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; 
v___x_3258_ = l_Lean_privateToUserName(v_n_3241_);
v___x_3259_ = l_Lean_Name_componentsRev(v___x_3258_);
v___x_3260_ = lean_box(0);
lean_inc(v_toPure_3240_);
v___f_3261_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__2), 3, 2);
lean_closure_set(v___f_3261_, 0, v_toPure_3240_);
lean_closure_set(v___f_3261_, 1, v___x_3260_);
lean_inc(v_toBind_3251_);
v___f_3262_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__4___boxed), 17, 14);
lean_closure_set(v___f_3262_, 0, v_toPure_3240_);
lean_closure_set(v___f_3262_, 1, v___x_3260_);
lean_closure_set(v___f_3262_, 2, v_inst_3242_);
lean_closure_set(v___f_3262_, 3, v_inst_3243_);
lean_closure_set(v___f_3262_, 4, v_inst_3244_);
lean_closure_set(v___f_3262_, 5, v_inst_3245_);
lean_closure_set(v___f_3262_, 6, v_inst_3246_);
lean_closure_set(v___f_3262_, 7, v_inst_3247_);
lean_closure_set(v___f_3262_, 8, v_n_u2080_3248_);
lean_closure_set(v___f_3262_, 9, v_filter_3249_);
lean_closure_set(v___f_3262_, 10, v_view_x3f_3250_);
lean_closure_set(v___f_3262_, 11, v_toBind_3251_);
lean_closure_set(v___f_3262_, 12, v___f_3252_);
lean_closure_set(v___f_3262_, 13, v___f_3253_);
v___x_3263_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__5___closed__0));
v___x_3264_ = l_List_forIn_x27_loop___redArg(v___x_3254_, v___f_3262_, v___x_3259_, v___x_3263_);
lean_dec(v___x_3259_);
v___x_3265_ = lean_apply_4(v_toBind_3251_, lean_box(0), lean_box(0), v___x_3264_, v___f_3261_);
return v___x_3265_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__5___boxed(lean_object* v_toPure_3266_, lean_object* v_n_3267_, lean_object* v_inst_3268_, lean_object* v_inst_3269_, lean_object* v_inst_3270_, lean_object* v_inst_3271_, lean_object* v_inst_3272_, lean_object* v_inst_3273_, lean_object* v_n_u2080_3274_, lean_object* v_filter_3275_, lean_object* v_view_x3f_3276_, lean_object* v_toBind_3277_, lean_object* v___f_3278_, lean_object* v___f_3279_, lean_object* v___x_3280_, lean_object* v_____do__lift_3281_){
_start:
{
lean_object* v_res_3282_; 
v_res_3282_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__5(v_toPure_3266_, v_n_3267_, v_inst_3268_, v_inst_3269_, v_inst_3270_, v_inst_3271_, v_inst_3272_, v_inst_3273_, v_n_u2080_3274_, v_filter_3275_, v_view_x3f_3276_, v_toBind_3277_, v___f_3278_, v___f_3279_, v___x_3280_, v_____do__lift_3281_);
lean_dec(v_____do__lift_3281_);
return v_res_3282_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg(lean_object* v_inst_3283_, lean_object* v_inst_3284_, lean_object* v_inst_3285_, lean_object* v_inst_3286_, lean_object* v_inst_3287_, lean_object* v_inst_3288_, lean_object* v_n_u2080_3289_, lean_object* v_filter_3290_, lean_object* v_view_x3f_3291_, lean_object* v_n_3292_){
_start:
{
lean_object* v___f_3293_; lean_object* v___f_3294_; lean_object* v___f_3295_; lean_object* v___f_3296_; lean_object* v___f_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___y_3304_; uint8_t v___x_3312_; 
lean_inc_ref_n(v_inst_3283_, 7);
v___f_3293_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_3293_, 0, v_inst_3283_);
v___f_3294_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__3), 5, 1);
lean_closure_set(v___f_3294_, 0, v_inst_3283_);
v___f_3295_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__6), 5, 1);
lean_closure_set(v___f_3295_, 0, v_inst_3283_);
v___f_3296_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_3296_, 0, v_inst_3283_);
v___f_3297_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__11), 5, 1);
lean_closure_set(v___f_3297_, 0, v_inst_3283_);
v___x_3298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3298_, 0, v___f_3293_);
lean_ctor_set(v___x_3298_, 1, v___f_3294_);
v___x_3299_ = lean_alloc_closure((void*)(l_OptionT_pure), 4, 2);
lean_closure_set(v___x_3299_, 0, lean_box(0));
lean_closure_set(v___x_3299_, 1, v_inst_3283_);
v___x_3300_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3300_, 0, v___x_3298_);
lean_ctor_set(v___x_3300_, 1, v___x_3299_);
lean_ctor_set(v___x_3300_, 2, v___f_3295_);
lean_ctor_set(v___x_3300_, 3, v___f_3296_);
lean_ctor_set(v___x_3300_, 4, v___f_3297_);
v___x_3301_ = lean_alloc_closure((void*)(l_OptionT_bind), 6, 2);
lean_closure_set(v___x_3301_, 0, lean_box(0));
lean_closure_set(v___x_3301_, 1, v_inst_3283_);
v___x_3302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3302_, 0, v___x_3300_);
lean_ctor_set(v___x_3302_, 1, v___x_3301_);
v___x_3312_ = l_Lean_Name_hasMacroScopes(v_n_3292_);
if (v___x_3312_ == 0)
{
lean_object* v_toApplicative_3313_; lean_object* v_toPure_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; 
v_toApplicative_3313_ = lean_ctor_get(v_inst_3283_, 0);
v_toPure_3314_ = lean_ctor_get(v_toApplicative_3313_, 1);
v___x_3315_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2___closed__0));
lean_inc(v_toPure_3314_);
v___x_3316_ = lean_apply_2(v_toPure_3314_, lean_box(0), v___x_3315_);
v___y_3304_ = v___x_3316_;
goto v___jp_3303_;
}
else
{
lean_object* v_toApplicative_3317_; lean_object* v_toPure_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; 
v_toApplicative_3317_ = lean_ctor_get(v_inst_3283_, 0);
v_toPure_3318_ = lean_ctor_get(v_toApplicative_3317_, 1);
v___x_3319_ = lean_box(0);
lean_inc(v_toPure_3318_);
v___x_3320_ = lean_apply_2(v_toPure_3318_, lean_box(0), v___x_3319_);
v___y_3304_ = v___x_3320_;
goto v___jp_3303_;
}
v___jp_3303_:
{
lean_object* v_toApplicative_3305_; lean_object* v_toBind_3306_; lean_object* v_toPure_3307_; lean_object* v___f_3308_; lean_object* v___f_3309_; lean_object* v___f_3310_; lean_object* v___x_3311_; 
v_toApplicative_3305_ = lean_ctor_get(v_inst_3283_, 0);
v_toBind_3306_ = lean_ctor_get(v_inst_3283_, 1);
lean_inc_n(v_toBind_3306_, 2);
v_toPure_3307_ = lean_ctor_get(v_toApplicative_3305_, 1);
lean_inc_n(v_toPure_3307_, 3);
v___f_3308_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3308_, 0, v_toPure_3307_);
v___f_3309_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__1), 2, 1);
lean_closure_set(v___f_3309_, 0, v_toPure_3307_);
v___f_3310_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__5___boxed), 16, 15);
lean_closure_set(v___f_3310_, 0, v_toPure_3307_);
lean_closure_set(v___f_3310_, 1, v_n_3292_);
lean_closure_set(v___f_3310_, 2, v_inst_3283_);
lean_closure_set(v___f_3310_, 3, v_inst_3284_);
lean_closure_set(v___f_3310_, 4, v_inst_3285_);
lean_closure_set(v___f_3310_, 5, v_inst_3286_);
lean_closure_set(v___f_3310_, 6, v_inst_3287_);
lean_closure_set(v___f_3310_, 7, v_inst_3288_);
lean_closure_set(v___f_3310_, 8, v_n_u2080_3289_);
lean_closure_set(v___f_3310_, 9, v_filter_3290_);
lean_closure_set(v___f_3310_, 10, v_view_x3f_3291_);
lean_closure_set(v___f_3310_, 11, v_toBind_3306_);
lean_closure_set(v___f_3310_, 12, v___f_3309_);
lean_closure_set(v___f_3310_, 13, v___f_3308_);
lean_closure_set(v___f_3310_, 14, v___x_3302_);
v___x_3311_ = lean_apply_4(v_toBind_3306_, lean_box(0), lean_box(0), v___y_3304_, v___f_3310_);
return v___x_3311_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore(lean_object* v_m_3321_, lean_object* v_inst_3322_, lean_object* v_inst_3323_, lean_object* v_inst_3324_, lean_object* v_inst_3325_, lean_object* v_inst_3326_, lean_object* v_inst_3327_, lean_object* v_n_u2080_3328_, lean_object* v_filter_3329_, lean_object* v_view_x3f_3330_, lean_object* v_n_3331_){
_start:
{
lean_object* v___x_3332_; 
v___x_3332_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg(v_inst_3322_, v_inst_3323_, v_inst_3324_, v_inst_3325_, v_inst_3326_, v_inst_3327_, v_n_u2080_3328_, v_filter_3329_, v_view_x3f_3330_, v_n_3331_);
return v___x_3332_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___lam__0(lean_object* v_n_u2081_3333_, lean_object* v_x1_3334_, lean_object* v_x2_3335_){
_start:
{
lean_object* v___x_3336_; lean_object* v___x_3337_; uint8_t v___x_3338_; 
v___x_3336_ = l_Lean_Name_getPrefix(v_x2_3335_);
v___x_3337_ = l_Lean_Name_getPrefix(v_n_u2081_3333_);
v___x_3338_ = l_Lean_Name_isPrefixOf(v___x_3336_, v___x_3337_);
lean_dec(v___x_3337_);
lean_dec(v___x_3336_);
if (v___x_3338_ == 0)
{
lean_dec(v_x2_3335_);
return v_x1_3334_;
}
else
{
lean_object* v___x_3339_; 
v___x_3339_ = lean_array_push(v_x1_3334_, v_x2_3335_);
return v___x_3339_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___lam__0___boxed(lean_object* v_n_u2081_3340_, lean_object* v_x1_3341_, lean_object* v_x2_3342_){
_start:
{
lean_object* v_res_3343_; 
v_res_3343_ = l_Lean_unresolveNameGlobal_x3f___redArg___lam__0(v_n_u2081_3340_, v_x1_3341_, v_x2_3342_);
lean_dec(v_n_u2081_3340_);
return v_res_3343_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___lam__1(lean_object* v_view_3344_, lean_object* v_n_u2081_3345_, lean_object* v_inst_3346_, lean_object* v_inst_3347_, lean_object* v_inst_3348_, lean_object* v_inst_3349_, lean_object* v_inst_3350_, lean_object* v_inst_3351_, lean_object* v_n_u2080_3352_, lean_object* v_filter_3353_, lean_object* v_toPure_3354_, lean_object* v_____do__lift_3355_){
_start:
{
if (lean_obj_tag(v_____do__lift_3355_) == 0)
{
lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; 
lean_dec(v_toPure_3354_);
v___x_3356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3356_, 0, v_view_3344_);
v___x_3357_ = l_Lean_rootNamespace;
v___x_3358_ = l_Lean_Name_append(v___x_3357_, v_n_u2081_3345_);
v___x_3359_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg(v_inst_3346_, v_inst_3347_, v_inst_3348_, v_inst_3349_, v_inst_3350_, v_inst_3351_, v_n_u2080_3352_, v_filter_3353_, v___x_3356_, v___x_3358_);
return v___x_3359_;
}
else
{
lean_object* v___x_3360_; 
lean_dec(v_filter_3353_);
lean_dec(v_n_u2080_3352_);
lean_dec(v_inst_3351_);
lean_dec_ref(v_inst_3350_);
lean_dec(v_inst_3349_);
lean_dec_ref(v_inst_3348_);
lean_dec_ref(v_inst_3347_);
lean_dec_ref(v_inst_3346_);
lean_dec(v_n_u2081_3345_);
lean_dec_ref(v_view_3344_);
v___x_3360_ = lean_apply_2(v_toPure_3354_, lean_box(0), v_____do__lift_3355_);
return v___x_3360_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___lam__2(lean_object* v_toPure_3361_, lean_object* v_inst_3362_, lean_object* v_inst_3363_, lean_object* v_inst_3364_, lean_object* v_inst_3365_, lean_object* v_inst_3366_, lean_object* v_inst_3367_, lean_object* v_n_u2080_3368_, lean_object* v_filter_3369_, lean_object* v_toBind_3370_, lean_object* v___f_3371_, uint8_t v_allowHorizAliases_3372_, lean_object* v___f_3373_, lean_object* v_____do__lift_3374_){
_start:
{
lean_object* v_aliases_3376_; 
if (lean_obj_tag(v_____do__lift_3374_) == 0)
{
lean_object* v___x_3383_; lean_object* v___x_3384_; 
lean_dec_ref(v___f_3373_);
lean_dec(v___f_3371_);
lean_dec(v_toBind_3370_);
lean_dec(v_filter_3369_);
lean_dec(v_n_u2080_3368_);
lean_dec(v_inst_3367_);
lean_dec_ref(v_inst_3366_);
lean_dec(v_inst_3365_);
lean_dec_ref(v_inst_3364_);
lean_dec_ref(v_inst_3363_);
lean_dec_ref(v_inst_3362_);
v___x_3383_ = lean_box(0);
v___x_3384_ = lean_apply_2(v_toPure_3361_, lean_box(0), v___x_3383_);
return v___x_3384_;
}
else
{
lean_object* v_val_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; 
lean_dec(v_toPure_3361_);
v_val_3385_ = lean_ctor_get(v_____do__lift_3374_, 0);
lean_inc(v_val_3385_);
lean_dec_ref_known(v_____do__lift_3374_, 1);
lean_inc(v_n_u2080_3368_);
v___x_3386_ = l_Lean_getRevAliases(v_val_3385_, v_n_u2080_3368_);
v___x_3387_ = lean_array_mk(v___x_3386_);
if (v_allowHorizAliases_3372_ == 0)
{
lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; uint8_t v___x_3392_; 
v___x_3388_ = lean_unsigned_to_nat(0u);
v___x_3389_ = lean_array_get_size(v___x_3387_);
v___x_3390_ = ((lean_object*)(l_Lean_resolveNamespace___redArg___closed__1));
v___x_3391_ = ((lean_object*)(l_Lean_resolveLocalName___redArg___lam__3___closed__9));
v___x_3392_ = lean_nat_dec_lt(v___x_3388_, v___x_3389_);
if (v___x_3392_ == 0)
{
lean_dec_ref(v___x_3387_);
lean_dec_ref(v___f_3373_);
v_aliases_3376_ = v___x_3390_;
goto v___jp_3375_;
}
else
{
uint8_t v___x_3393_; 
v___x_3393_ = lean_nat_dec_le(v___x_3389_, v___x_3389_);
if (v___x_3393_ == 0)
{
if (v___x_3392_ == 0)
{
lean_dec_ref(v___x_3387_);
lean_dec_ref(v___f_3373_);
v_aliases_3376_ = v___x_3390_;
goto v___jp_3375_;
}
else
{
size_t v___x_3394_; size_t v___x_3395_; lean_object* v___x_3396_; 
v___x_3394_ = ((size_t)0ULL);
v___x_3395_ = lean_usize_of_nat(v___x_3389_);
v___x_3396_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3391_, v___f_3373_, v___x_3387_, v___x_3394_, v___x_3395_, v___x_3390_);
v_aliases_3376_ = v___x_3396_;
goto v___jp_3375_;
}
}
else
{
size_t v___x_3397_; size_t v___x_3398_; lean_object* v___x_3399_; 
v___x_3397_ = ((size_t)0ULL);
v___x_3398_ = lean_usize_of_nat(v___x_3389_);
v___x_3399_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3391_, v___f_3373_, v___x_3387_, v___x_3397_, v___x_3398_, v___x_3390_);
v_aliases_3376_ = v___x_3399_;
goto v___jp_3375_;
}
}
}
else
{
lean_dec_ref(v___f_3373_);
v_aliases_3376_ = v___x_3387_;
goto v___jp_3375_;
}
}
v___jp_3375_:
{
lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; 
lean_inc_ref(v_inst_3362_);
v___x_3377_ = l_OptionT_instAlternative___redArg(v_inst_3362_);
v___x_3378_ = lean_box(0);
v___x_3379_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore), 11, 10);
lean_closure_set(v___x_3379_, 0, lean_box(0));
lean_closure_set(v___x_3379_, 1, v_inst_3362_);
lean_closure_set(v___x_3379_, 2, v_inst_3363_);
lean_closure_set(v___x_3379_, 3, v_inst_3364_);
lean_closure_set(v___x_3379_, 4, v_inst_3365_);
lean_closure_set(v___x_3379_, 5, v_inst_3366_);
lean_closure_set(v___x_3379_, 6, v_inst_3367_);
lean_closure_set(v___x_3379_, 7, v_n_u2080_3368_);
lean_closure_set(v___x_3379_, 8, v_filter_3369_);
lean_closure_set(v___x_3379_, 9, v___x_3378_);
v___x_3380_ = lean_unsigned_to_nat(0u);
v___x_3381_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go(lean_box(0), lean_box(0), lean_box(0), v___x_3377_, v___x_3379_, v_aliases_3376_, v___x_3380_);
v___x_3382_ = lean_apply_4(v_toBind_3370_, lean_box(0), lean_box(0), v___x_3381_, v___f_3371_);
return v___x_3382_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___lam__2___boxed(lean_object* v_toPure_3400_, lean_object* v_inst_3401_, lean_object* v_inst_3402_, lean_object* v_inst_3403_, lean_object* v_inst_3404_, lean_object* v_inst_3405_, lean_object* v_inst_3406_, lean_object* v_n_u2080_3407_, lean_object* v_filter_3408_, lean_object* v_toBind_3409_, lean_object* v___f_3410_, lean_object* v_allowHorizAliases_3411_, lean_object* v___f_3412_, lean_object* v_____do__lift_3413_){
_start:
{
uint8_t v_allowHorizAliases_boxed_3414_; lean_object* v_res_3415_; 
v_allowHorizAliases_boxed_3414_ = lean_unbox(v_allowHorizAliases_3411_);
v_res_3415_ = l_Lean_unresolveNameGlobal_x3f___redArg___lam__2(v_toPure_3400_, v_inst_3401_, v_inst_3402_, v_inst_3403_, v_inst_3404_, v_inst_3405_, v_inst_3406_, v_n_u2080_3407_, v_filter_3408_, v_toBind_3409_, v___f_3410_, v_allowHorizAliases_boxed_3414_, v___f_3412_, v_____do__lift_3413_);
return v_res_3415_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___lam__3(lean_object* v_toPure_3416_, lean_object* v_____do__lift_3417_){
_start:
{
lean_object* v___x_3418_; lean_object* v___x_3419_; 
v___x_3418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3418_, 0, v_____do__lift_3417_);
v___x_3419_ = lean_apply_2(v_toPure_3416_, lean_box(0), v___x_3418_);
return v___x_3419_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___lam__4(lean_object* v_n_u2081_3420_, lean_object* v_inst_3421_, lean_object* v_inst_3422_, lean_object* v_inst_3423_, lean_object* v_inst_3424_, lean_object* v_inst_3425_, lean_object* v_inst_3426_, lean_object* v_n_u2080_3427_, lean_object* v_filter_3428_, lean_object* v___x_3429_, lean_object* v_toPure_3430_, lean_object* v_____do__lift_3431_){
_start:
{
if (lean_obj_tag(v_____do__lift_3431_) == 0)
{
lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; 
lean_dec(v_toPure_3430_);
v___x_3432_ = l_Lean_rootNamespace;
v___x_3433_ = l_Lean_Name_append(v___x_3432_, v_n_u2081_3420_);
v___x_3434_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg(v_inst_3421_, v_inst_3422_, v_inst_3423_, v_inst_3424_, v_inst_3425_, v_inst_3426_, v_n_u2080_3427_, v_filter_3428_, v___x_3429_, v___x_3433_);
return v___x_3434_;
}
else
{
lean_object* v___x_3435_; 
lean_dec(v___x_3429_);
lean_dec(v_filter_3428_);
lean_dec(v_n_u2080_3427_);
lean_dec(v_inst_3426_);
lean_dec_ref(v_inst_3425_);
lean_dec(v_inst_3424_);
lean_dec_ref(v_inst_3423_);
lean_dec_ref(v_inst_3422_);
lean_dec_ref(v_inst_3421_);
lean_dec(v_n_u2081_3420_);
v___x_3435_ = lean_apply_2(v_toPure_3430_, lean_box(0), v_____do__lift_3431_);
return v___x_3435_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg(lean_object* v_inst_3436_, lean_object* v_inst_3437_, lean_object* v_inst_3438_, lean_object* v_inst_3439_, lean_object* v_inst_3440_, lean_object* v_inst_3441_, lean_object* v_n_u2080_3442_, uint8_t v_fullNames_3443_, uint8_t v_allowHorizAliases_3444_, lean_object* v_filter_3445_){
_start:
{
lean_object* v_view_3446_; lean_object* v_name_3447_; lean_object* v_n_u2081_3448_; 
lean_inc(v_n_u2080_3442_);
v_view_3446_ = l_Lean_extractMacroScopes(v_n_u2080_3442_);
v_name_3447_ = lean_ctor_get(v_view_3446_, 0);
lean_inc(v_name_3447_);
v_n_u2081_3448_ = l_Lean_privateToUserName(v_name_3447_);
if (v_fullNames_3443_ == 0)
{
lean_object* v_toApplicative_3449_; lean_object* v_getEnv_3450_; lean_object* v_toBind_3451_; lean_object* v_toPure_3452_; lean_object* v___f_3453_; lean_object* v___f_3454_; lean_object* v___x_3455_; lean_object* v___f_3456_; lean_object* v___f_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; 
v_toApplicative_3449_ = lean_ctor_get(v_inst_3436_, 0);
v_getEnv_3450_ = lean_ctor_get(v_inst_3438_, 0);
lean_inc(v_getEnv_3450_);
v_toBind_3451_ = lean_ctor_get(v_inst_3436_, 1);
lean_inc_n(v_toBind_3451_, 3);
v_toPure_3452_ = lean_ctor_get(v_toApplicative_3449_, 1);
lean_inc_n(v_toPure_3452_, 3);
lean_inc(v_n_u2081_3448_);
v___f_3453_ = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal_x3f___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3453_, 0, v_n_u2081_3448_);
lean_inc(v_filter_3445_);
lean_inc(v_n_u2080_3442_);
lean_inc(v_inst_3441_);
lean_inc_ref(v_inst_3440_);
lean_inc(v_inst_3439_);
lean_inc_ref(v_inst_3438_);
lean_inc_ref(v_inst_3437_);
lean_inc_ref(v_inst_3436_);
v___f_3454_ = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal_x3f___redArg___lam__1), 12, 11);
lean_closure_set(v___f_3454_, 0, v_view_3446_);
lean_closure_set(v___f_3454_, 1, v_n_u2081_3448_);
lean_closure_set(v___f_3454_, 2, v_inst_3436_);
lean_closure_set(v___f_3454_, 3, v_inst_3437_);
lean_closure_set(v___f_3454_, 4, v_inst_3438_);
lean_closure_set(v___f_3454_, 5, v_inst_3439_);
lean_closure_set(v___f_3454_, 6, v_inst_3440_);
lean_closure_set(v___f_3454_, 7, v_inst_3441_);
lean_closure_set(v___f_3454_, 8, v_n_u2080_3442_);
lean_closure_set(v___f_3454_, 9, v_filter_3445_);
lean_closure_set(v___f_3454_, 10, v_toPure_3452_);
v___x_3455_ = lean_box(v_allowHorizAliases_3444_);
v___f_3456_ = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal_x3f___redArg___lam__2___boxed), 14, 13);
lean_closure_set(v___f_3456_, 0, v_toPure_3452_);
lean_closure_set(v___f_3456_, 1, v_inst_3436_);
lean_closure_set(v___f_3456_, 2, v_inst_3437_);
lean_closure_set(v___f_3456_, 3, v_inst_3438_);
lean_closure_set(v___f_3456_, 4, v_inst_3439_);
lean_closure_set(v___f_3456_, 5, v_inst_3440_);
lean_closure_set(v___f_3456_, 6, v_inst_3441_);
lean_closure_set(v___f_3456_, 7, v_n_u2080_3442_);
lean_closure_set(v___f_3456_, 8, v_filter_3445_);
lean_closure_set(v___f_3456_, 9, v_toBind_3451_);
lean_closure_set(v___f_3456_, 10, v___f_3454_);
lean_closure_set(v___f_3456_, 11, v___x_3455_);
lean_closure_set(v___f_3456_, 12, v___f_3453_);
v___f_3457_ = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal_x3f___redArg___lam__3), 2, 1);
lean_closure_set(v___f_3457_, 0, v_toPure_3452_);
v___x_3458_ = lean_apply_4(v_toBind_3451_, lean_box(0), lean_box(0), v_getEnv_3450_, v___f_3457_);
v___x_3459_ = lean_apply_4(v_toBind_3451_, lean_box(0), lean_box(0), v___x_3458_, v___f_3456_);
return v___x_3459_;
}
else
{
lean_object* v_toApplicative_3460_; lean_object* v_toBind_3461_; lean_object* v_toPure_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___f_3465_; lean_object* v___x_3466_; 
v_toApplicative_3460_ = lean_ctor_get(v_inst_3436_, 0);
v_toBind_3461_ = lean_ctor_get(v_inst_3436_, 1);
lean_inc(v_toBind_3461_);
v_toPure_3462_ = lean_ctor_get(v_toApplicative_3460_, 1);
lean_inc(v_toPure_3462_);
v___x_3463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3463_, 0, v_view_3446_);
lean_inc(v_n_u2081_3448_);
lean_inc_ref(v___x_3463_);
lean_inc(v_filter_3445_);
lean_inc(v_n_u2080_3442_);
lean_inc(v_inst_3441_);
lean_inc_ref(v_inst_3440_);
lean_inc(v_inst_3439_);
lean_inc_ref(v_inst_3438_);
lean_inc_ref(v_inst_3437_);
lean_inc_ref(v_inst_3436_);
v___x_3464_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg(v_inst_3436_, v_inst_3437_, v_inst_3438_, v_inst_3439_, v_inst_3440_, v_inst_3441_, v_n_u2080_3442_, v_filter_3445_, v___x_3463_, v_n_u2081_3448_);
v___f_3465_ = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal_x3f___redArg___lam__4), 12, 11);
lean_closure_set(v___f_3465_, 0, v_n_u2081_3448_);
lean_closure_set(v___f_3465_, 1, v_inst_3436_);
lean_closure_set(v___f_3465_, 2, v_inst_3437_);
lean_closure_set(v___f_3465_, 3, v_inst_3438_);
lean_closure_set(v___f_3465_, 4, v_inst_3439_);
lean_closure_set(v___f_3465_, 5, v_inst_3440_);
lean_closure_set(v___f_3465_, 6, v_inst_3441_);
lean_closure_set(v___f_3465_, 7, v_n_u2080_3442_);
lean_closure_set(v___f_3465_, 8, v_filter_3445_);
lean_closure_set(v___f_3465_, 9, v___x_3463_);
lean_closure_set(v___f_3465_, 10, v_toPure_3462_);
v___x_3466_ = lean_apply_4(v_toBind_3461_, lean_box(0), lean_box(0), v___x_3464_, v___f_3465_);
return v___x_3466_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___boxed(lean_object* v_inst_3467_, lean_object* v_inst_3468_, lean_object* v_inst_3469_, lean_object* v_inst_3470_, lean_object* v_inst_3471_, lean_object* v_inst_3472_, lean_object* v_n_u2080_3473_, lean_object* v_fullNames_3474_, lean_object* v_allowHorizAliases_3475_, lean_object* v_filter_3476_){
_start:
{
uint8_t v_fullNames_boxed_3477_; uint8_t v_allowHorizAliases_boxed_3478_; lean_object* v_res_3479_; 
v_fullNames_boxed_3477_ = lean_unbox(v_fullNames_3474_);
v_allowHorizAliases_boxed_3478_ = lean_unbox(v_allowHorizAliases_3475_);
v_res_3479_ = l_Lean_unresolveNameGlobal_x3f___redArg(v_inst_3467_, v_inst_3468_, v_inst_3469_, v_inst_3470_, v_inst_3471_, v_inst_3472_, v_n_u2080_3473_, v_fullNames_boxed_3477_, v_allowHorizAliases_boxed_3478_, v_filter_3476_);
return v_res_3479_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f(lean_object* v_m_3480_, lean_object* v_inst_3481_, lean_object* v_inst_3482_, lean_object* v_inst_3483_, lean_object* v_inst_3484_, lean_object* v_inst_3485_, lean_object* v_inst_3486_, lean_object* v_n_u2080_3487_, uint8_t v_fullNames_3488_, uint8_t v_allowHorizAliases_3489_, lean_object* v_filter_3490_){
_start:
{
lean_object* v___x_3491_; 
v___x_3491_ = l_Lean_unresolveNameGlobal_x3f___redArg(v_inst_3481_, v_inst_3482_, v_inst_3483_, v_inst_3484_, v_inst_3485_, v_inst_3486_, v_n_u2080_3487_, v_fullNames_3488_, v_allowHorizAliases_3489_, v_filter_3490_);
return v___x_3491_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___boxed(lean_object* v_m_3492_, lean_object* v_inst_3493_, lean_object* v_inst_3494_, lean_object* v_inst_3495_, lean_object* v_inst_3496_, lean_object* v_inst_3497_, lean_object* v_inst_3498_, lean_object* v_n_u2080_3499_, lean_object* v_fullNames_3500_, lean_object* v_allowHorizAliases_3501_, lean_object* v_filter_3502_){
_start:
{
uint8_t v_fullNames_boxed_3503_; uint8_t v_allowHorizAliases_boxed_3504_; lean_object* v_res_3505_; 
v_fullNames_boxed_3503_ = lean_unbox(v_fullNames_3500_);
v_allowHorizAliases_boxed_3504_ = lean_unbox(v_allowHorizAliases_3501_);
v_res_3505_ = l_Lean_unresolveNameGlobal_x3f(v_m_3492_, v_inst_3493_, v_inst_3494_, v_inst_3495_, v_inst_3496_, v_inst_3497_, v_inst_3498_, v_n_u2080_3499_, v_fullNames_boxed_3503_, v_allowHorizAliases_boxed_3504_, v_filter_3502_);
return v_res_3505_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___redArg___lam__0(lean_object* v_toPure_3506_, lean_object* v_n_u2080_3507_, lean_object* v_n_x3f_3508_){
_start:
{
if (lean_obj_tag(v_n_x3f_3508_) == 0)
{
lean_object* v___x_3509_; 
v___x_3509_ = lean_apply_2(v_toPure_3506_, lean_box(0), v_n_u2080_3507_);
return v___x_3509_;
}
else
{
lean_object* v_val_3510_; lean_object* v___x_3511_; 
lean_dec(v_n_u2080_3507_);
v_val_3510_ = lean_ctor_get(v_n_x3f_3508_, 0);
lean_inc(v_val_3510_);
lean_dec_ref_known(v_n_x3f_3508_, 1);
v___x_3511_ = lean_apply_2(v_toPure_3506_, lean_box(0), v_val_3510_);
return v___x_3511_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___redArg(lean_object* v_inst_3512_, lean_object* v_inst_3513_, lean_object* v_inst_3514_, lean_object* v_inst_3515_, lean_object* v_inst_3516_, lean_object* v_inst_3517_, lean_object* v_n_u2080_3518_, uint8_t v_fullNames_3519_, uint8_t v_allowHorizAliases_3520_, lean_object* v_filter_3521_){
_start:
{
lean_object* v_toApplicative_3522_; lean_object* v_toBind_3523_; lean_object* v_toPure_3524_; lean_object* v___x_3525_; lean_object* v___f_3526_; lean_object* v___x_3527_; 
v_toApplicative_3522_ = lean_ctor_get(v_inst_3512_, 0);
v_toBind_3523_ = lean_ctor_get(v_inst_3512_, 1);
lean_inc(v_toBind_3523_);
v_toPure_3524_ = lean_ctor_get(v_toApplicative_3522_, 1);
lean_inc(v_toPure_3524_);
lean_inc(v_n_u2080_3518_);
v___x_3525_ = l_Lean_unresolveNameGlobal_x3f___redArg(v_inst_3512_, v_inst_3513_, v_inst_3514_, v_inst_3515_, v_inst_3516_, v_inst_3517_, v_n_u2080_3518_, v_fullNames_3519_, v_allowHorizAliases_3520_, v_filter_3521_);
v___f_3526_ = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3526_, 0, v_toPure_3524_);
lean_closure_set(v___f_3526_, 1, v_n_u2080_3518_);
v___x_3527_ = lean_apply_4(v_toBind_3523_, lean_box(0), lean_box(0), v___x_3525_, v___f_3526_);
return v___x_3527_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___redArg___boxed(lean_object* v_inst_3528_, lean_object* v_inst_3529_, lean_object* v_inst_3530_, lean_object* v_inst_3531_, lean_object* v_inst_3532_, lean_object* v_inst_3533_, lean_object* v_n_u2080_3534_, lean_object* v_fullNames_3535_, lean_object* v_allowHorizAliases_3536_, lean_object* v_filter_3537_){
_start:
{
uint8_t v_fullNames_boxed_3538_; uint8_t v_allowHorizAliases_boxed_3539_; lean_object* v_res_3540_; 
v_fullNames_boxed_3538_ = lean_unbox(v_fullNames_3535_);
v_allowHorizAliases_boxed_3539_ = lean_unbox(v_allowHorizAliases_3536_);
v_res_3540_ = l_Lean_unresolveNameGlobal___redArg(v_inst_3528_, v_inst_3529_, v_inst_3530_, v_inst_3531_, v_inst_3532_, v_inst_3533_, v_n_u2080_3534_, v_fullNames_boxed_3538_, v_allowHorizAliases_boxed_3539_, v_filter_3537_);
return v_res_3540_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal(lean_object* v_m_3541_, lean_object* v_inst_3542_, lean_object* v_inst_3543_, lean_object* v_inst_3544_, lean_object* v_inst_3545_, lean_object* v_inst_3546_, lean_object* v_inst_3547_, lean_object* v_n_u2080_3548_, uint8_t v_fullNames_3549_, uint8_t v_allowHorizAliases_3550_, lean_object* v_filter_3551_){
_start:
{
lean_object* v___x_3552_; 
v___x_3552_ = l_Lean_unresolveNameGlobal___redArg(v_inst_3542_, v_inst_3543_, v_inst_3544_, v_inst_3545_, v_inst_3546_, v_inst_3547_, v_n_u2080_3548_, v_fullNames_3549_, v_allowHorizAliases_3550_, v_filter_3551_);
return v___x_3552_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___boxed(lean_object* v_m_3553_, lean_object* v_inst_3554_, lean_object* v_inst_3555_, lean_object* v_inst_3556_, lean_object* v_inst_3557_, lean_object* v_inst_3558_, lean_object* v_inst_3559_, lean_object* v_n_u2080_3560_, lean_object* v_fullNames_3561_, lean_object* v_allowHorizAliases_3562_, lean_object* v_filter_3563_){
_start:
{
uint8_t v_fullNames_boxed_3564_; uint8_t v_allowHorizAliases_boxed_3565_; lean_object* v_res_3566_; 
v_fullNames_boxed_3564_ = lean_unbox(v_fullNames_3561_);
v_allowHorizAliases_boxed_3565_ = lean_unbox(v_allowHorizAliases_3562_);
v_res_3566_ = l_Lean_unresolveNameGlobal(v_m_3553_, v_inst_3554_, v_inst_3555_, v_inst_3556_, v_inst_3557_, v_inst_3558_, v_inst_3559_, v_n_u2080_3560_, v_fullNames_boxed_3564_, v_allowHorizAliases_boxed_3565_, v_filter_3563_);
return v_res_3566_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg___lam__0(lean_object* v_toFunctor_3568_, lean_object* v_inst_3569_, lean_object* v_inst_3570_, lean_object* v_inst_3571_, lean_object* v_inst_3572_, lean_object* v_inst_3573_, lean_object* v_inst_3574_, lean_object* v_inst_3575_, lean_object* v_n_3576_){
_start:
{
lean_object* v_map_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; 
v_map_3577_ = lean_ctor_get(v_toFunctor_3568_, 0);
lean_inc(v_map_3577_);
lean_dec_ref(v_toFunctor_3568_);
v___x_3578_ = ((lean_object*)(l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg___lam__0___closed__0));
v___x_3579_ = l_Lean_resolveLocalName___redArg(v_inst_3569_, v_inst_3570_, v_inst_3571_, v_inst_3572_, v_inst_3573_, v_inst_3574_, v_inst_3575_, v_n_3576_);
v___x_3580_ = lean_apply_4(v_map_3577_, lean_box(0), lean_box(0), v___x_3578_, v___x_3579_);
return v___x_3580_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg(lean_object* v_inst_3581_, lean_object* v_inst_3582_, lean_object* v_inst_3583_, lean_object* v_inst_3584_, lean_object* v_inst_3585_, lean_object* v_inst_3586_, lean_object* v_inst_3587_, lean_object* v_n_u2080_3588_, uint8_t v_fullNames_3589_){
_start:
{
lean_object* v_toApplicative_3590_; lean_object* v_toFunctor_3591_; uint8_t v___x_3592_; lean_object* v___f_3593_; lean_object* v___x_3594_; 
v_toApplicative_3590_ = lean_ctor_get(v_inst_3581_, 0);
v_toFunctor_3591_ = lean_ctor_get(v_toApplicative_3590_, 0);
v___x_3592_ = 0;
lean_inc(v_inst_3586_);
lean_inc_ref(v_inst_3585_);
lean_inc(v_inst_3584_);
lean_inc_ref(v_inst_3583_);
lean_inc_ref(v_inst_3582_);
lean_inc_ref(v_inst_3581_);
lean_inc_ref(v_toFunctor_3591_);
v___f_3593_ = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg___lam__0), 9, 8);
lean_closure_set(v___f_3593_, 0, v_toFunctor_3591_);
lean_closure_set(v___f_3593_, 1, v_inst_3581_);
lean_closure_set(v___f_3593_, 2, v_inst_3582_);
lean_closure_set(v___f_3593_, 3, v_inst_3583_);
lean_closure_set(v___f_3593_, 4, v_inst_3584_);
lean_closure_set(v___f_3593_, 5, v_inst_3585_);
lean_closure_set(v___f_3593_, 6, v_inst_3586_);
lean_closure_set(v___f_3593_, 7, v_inst_3587_);
v___x_3594_ = l_Lean_unresolveNameGlobal_x3f___redArg(v_inst_3581_, v_inst_3582_, v_inst_3583_, v_inst_3584_, v_inst_3585_, v_inst_3586_, v_n_u2080_3588_, v_fullNames_3589_, v___x_3592_, v___f_3593_);
return v___x_3594_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg___boxed(lean_object* v_inst_3595_, lean_object* v_inst_3596_, lean_object* v_inst_3597_, lean_object* v_inst_3598_, lean_object* v_inst_3599_, lean_object* v_inst_3600_, lean_object* v_inst_3601_, lean_object* v_n_u2080_3602_, lean_object* v_fullNames_3603_){
_start:
{
uint8_t v_fullNames_boxed_3604_; lean_object* v_res_3605_; 
v_fullNames_boxed_3604_ = lean_unbox(v_fullNames_3603_);
v_res_3605_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg(v_inst_3595_, v_inst_3596_, v_inst_3597_, v_inst_3598_, v_inst_3599_, v_inst_3600_, v_inst_3601_, v_n_u2080_3602_, v_fullNames_boxed_3604_);
return v_res_3605_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f(lean_object* v_m_3606_, lean_object* v_inst_3607_, lean_object* v_inst_3608_, lean_object* v_inst_3609_, lean_object* v_inst_3610_, lean_object* v_inst_3611_, lean_object* v_inst_3612_, lean_object* v_inst_3613_, lean_object* v_n_u2080_3614_, uint8_t v_fullNames_3615_){
_start:
{
lean_object* v___x_3616_; 
v___x_3616_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg(v_inst_3607_, v_inst_3608_, v_inst_3609_, v_inst_3610_, v_inst_3611_, v_inst_3612_, v_inst_3613_, v_n_u2080_3614_, v_fullNames_3615_);
return v___x_3616_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___boxed(lean_object* v_m_3617_, lean_object* v_inst_3618_, lean_object* v_inst_3619_, lean_object* v_inst_3620_, lean_object* v_inst_3621_, lean_object* v_inst_3622_, lean_object* v_inst_3623_, lean_object* v_inst_3624_, lean_object* v_n_u2080_3625_, lean_object* v_fullNames_3626_){
_start:
{
uint8_t v_fullNames_boxed_3627_; lean_object* v_res_3628_; 
v_fullNames_boxed_3627_ = lean_unbox(v_fullNames_3626_);
v_res_3628_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f(v_m_3617_, v_inst_3618_, v_inst_3619_, v_inst_3620_, v_inst_3621_, v_inst_3622_, v_inst_3623_, v_inst_3624_, v_n_u2080_3625_, v_fullNames_boxed_3627_);
return v_res_3628_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals___redArg(lean_object* v_inst_3629_, lean_object* v_inst_3630_, lean_object* v_inst_3631_, lean_object* v_inst_3632_, lean_object* v_inst_3633_, lean_object* v_inst_3634_, lean_object* v_inst_3635_, lean_object* v_n_u2080_3636_, uint8_t v_fullNames_3637_){
_start:
{
lean_object* v_toApplicative_3638_; lean_object* v_toBind_3639_; lean_object* v_toPure_3640_; lean_object* v___x_3641_; lean_object* v___f_3642_; lean_object* v___x_3643_; 
v_toApplicative_3638_ = lean_ctor_get(v_inst_3629_, 0);
v_toBind_3639_ = lean_ctor_get(v_inst_3629_, 1);
lean_inc(v_toBind_3639_);
v_toPure_3640_ = lean_ctor_get(v_toApplicative_3638_, 1);
lean_inc(v_toPure_3640_);
lean_inc(v_n_u2080_3636_);
v___x_3641_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg(v_inst_3629_, v_inst_3630_, v_inst_3631_, v_inst_3632_, v_inst_3633_, v_inst_3634_, v_inst_3635_, v_n_u2080_3636_, v_fullNames_3637_);
v___f_3642_ = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3642_, 0, v_toPure_3640_);
lean_closure_set(v___f_3642_, 1, v_n_u2080_3636_);
v___x_3643_ = lean_apply_4(v_toBind_3639_, lean_box(0), lean_box(0), v___x_3641_, v___f_3642_);
return v___x_3643_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals___redArg___boxed(lean_object* v_inst_3644_, lean_object* v_inst_3645_, lean_object* v_inst_3646_, lean_object* v_inst_3647_, lean_object* v_inst_3648_, lean_object* v_inst_3649_, lean_object* v_inst_3650_, lean_object* v_n_u2080_3651_, lean_object* v_fullNames_3652_){
_start:
{
uint8_t v_fullNames_boxed_3653_; lean_object* v_res_3654_; 
v_fullNames_boxed_3653_ = lean_unbox(v_fullNames_3652_);
v_res_3654_ = l_Lean_unresolveNameGlobalAvoidingLocals___redArg(v_inst_3644_, v_inst_3645_, v_inst_3646_, v_inst_3647_, v_inst_3648_, v_inst_3649_, v_inst_3650_, v_n_u2080_3651_, v_fullNames_boxed_3653_);
return v_res_3654_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals(lean_object* v_m_3655_, lean_object* v_inst_3656_, lean_object* v_inst_3657_, lean_object* v_inst_3658_, lean_object* v_inst_3659_, lean_object* v_inst_3660_, lean_object* v_inst_3661_, lean_object* v_inst_3662_, lean_object* v_n_u2080_3663_, uint8_t v_fullNames_3664_){
_start:
{
lean_object* v___x_3665_; 
v___x_3665_ = l_Lean_unresolveNameGlobalAvoidingLocals___redArg(v_inst_3656_, v_inst_3657_, v_inst_3658_, v_inst_3659_, v_inst_3660_, v_inst_3661_, v_inst_3662_, v_n_u2080_3663_, v_fullNames_3664_);
return v___x_3665_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals___boxed(lean_object* v_m_3666_, lean_object* v_inst_3667_, lean_object* v_inst_3668_, lean_object* v_inst_3669_, lean_object* v_inst_3670_, lean_object* v_inst_3671_, lean_object* v_inst_3672_, lean_object* v_inst_3673_, lean_object* v_n_u2080_3674_, lean_object* v_fullNames_3675_){
_start:
{
uint8_t v_fullNames_boxed_3676_; lean_object* v_res_3677_; 
v_fullNames_boxed_3676_ = lean_unbox(v_fullNames_3675_);
v_res_3677_ = l_Lean_unresolveNameGlobalAvoidingLocals(v_m_3666_, v_inst_3667_, v_inst_3668_, v_inst_3669_, v_inst_3670_, v_inst_3671_, v_inst_3672_, v_inst_3673_, v_n_u2080_3674_, v_fullNames_boxed_3676_);
return v_res_3677_;
}
}
lean_object* runtime_initialize_Lean_Modifiers(uint8_t builtin);
lean_object* runtime_initialize_Lean_Exception(uint8_t builtin);
lean_object* runtime_initialize_Lean_Namespace(uint8_t builtin);
lean_object* runtime_initialize_Lean_Log(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_ResolveName(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
