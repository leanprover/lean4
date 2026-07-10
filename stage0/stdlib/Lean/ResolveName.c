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
uint8_t lean_bool_not(uint8_t);
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
LEAN_EXPORT lean_object* l_Lean_addAlias(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_getAliasState___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_getAliasState___closed__0 = (const lean_object*)&l_Lean_getAliasState___closed__0_value;
static const lean_closure_object l_Lean_getAliasState___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_getAliasState___closed__1 = (const lean_object*)&l_Lean_getAliasState___closed__1_value;
static lean_once_cell_t l_Lean_getAliasState___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getAliasState___closed__2;
LEAN_EXPORT lean_object* l_Lean_getAliasState(lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_getAliases_spec__0(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg___lam__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_addAlias(lean_object* v_env_870_, lean_object* v_a_871_, lean_object* v_e_872_){
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
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_getAliases_spec__0(lean_object* v_env_891_, lean_object* v_a_892_, lean_object* v_a_893_){
_start:
{
if (lean_obj_tag(v_a_892_) == 0)
{
lean_object* v___x_894_; 
lean_dec_ref(v_env_891_);
v___x_894_ = l_List_reverse___redArg(v_a_893_);
return v___x_894_;
}
else
{
lean_object* v_head_895_; lean_object* v_tail_896_; lean_object* v___x_898_; uint8_t v_isShared_899_; uint8_t v_isSharedCheck_907_; 
v_head_895_ = lean_ctor_get(v_a_892_, 0);
v_tail_896_ = lean_ctor_get(v_a_892_, 1);
v_isSharedCheck_907_ = !lean_is_exclusive(v_a_892_);
if (v_isSharedCheck_907_ == 0)
{
v___x_898_ = v_a_892_;
v_isShared_899_ = v_isSharedCheck_907_;
goto v_resetjp_897_;
}
else
{
lean_inc(v_tail_896_);
lean_inc(v_head_895_);
lean_dec(v_a_892_);
v___x_898_ = lean_box(0);
v_isShared_899_ = v_isSharedCheck_907_;
goto v_resetjp_897_;
}
v_resetjp_897_:
{
uint8_t v___x_900_; uint8_t v___x_901_; 
lean_inc(v_head_895_);
lean_inc_ref(v_env_891_);
v___x_900_ = l_Lean_isProtected(v_env_891_, v_head_895_);
v___x_901_ = lean_bool_not(v___x_900_);
if (v___x_901_ == 0)
{
lean_del_object(v___x_898_);
lean_dec(v_head_895_);
v_a_892_ = v_tail_896_;
goto _start;
}
else
{
lean_object* v___x_904_; 
if (v_isShared_899_ == 0)
{
lean_ctor_set(v___x_898_, 1, v_a_893_);
v___x_904_ = v___x_898_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v_head_895_);
lean_ctor_set(v_reuseFailAlloc_906_, 1, v_a_893_);
v___x_904_ = v_reuseFailAlloc_906_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
v_a_892_ = v_tail_896_;
v_a_893_ = v___x_904_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getAliases(lean_object* v_env_908_, lean_object* v_a_909_, uint8_t v_skipProtected_910_){
_start:
{
lean_object* v___x_911_; lean_object* v_toEnvExtension_912_; lean_object* v_asyncMode_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; 
v___x_911_ = l_Lean_aliasExtension;
v_toEnvExtension_912_ = lean_ctor_get(v___x_911_, 0);
v_asyncMode_913_ = lean_ctor_get(v_toEnvExtension_912_, 2);
v___x_914_ = lean_obj_once(&l_Lean_getAliasState___closed__2, &l_Lean_getAliasState___closed__2_once, _init_l_Lean_getAliasState___closed__2);
v___x_915_ = lean_box(0);
lean_inc_ref(v_env_908_);
v___x_916_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_914_, v___x_911_, v_env_908_, v_asyncMode_913_, v___x_915_);
v___x_917_ = l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0___redArg(v___x_916_, v_a_909_);
lean_dec(v___x_916_);
if (lean_obj_tag(v___x_917_) == 0)
{
lean_object* v___x_918_; 
lean_dec_ref(v_env_908_);
v___x_918_ = lean_box(0);
return v___x_918_;
}
else
{
if (v_skipProtected_910_ == 0)
{
lean_object* v_val_919_; 
lean_dec_ref(v_env_908_);
v_val_919_ = lean_ctor_get(v___x_917_, 0);
lean_inc(v_val_919_);
lean_dec_ref_known(v___x_917_, 1);
return v_val_919_;
}
else
{
lean_object* v_val_920_; lean_object* v___x_921_; lean_object* v___x_922_; 
v_val_920_ = lean_ctor_get(v___x_917_, 0);
lean_inc(v_val_920_);
lean_dec_ref_known(v___x_917_, 1);
v___x_921_ = lean_box(0);
v___x_922_ = l_List_filterTR_loop___at___00Lean_getAliases_spec__0(v_env_908_, v_val_920_, v___x_921_);
return v___x_922_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getAliases___boxed(lean_object* v_env_923_, lean_object* v_a_924_, lean_object* v_skipProtected_925_){
_start:
{
uint8_t v_skipProtected_boxed_926_; lean_object* v_res_927_; 
v_skipProtected_boxed_926_ = lean_unbox(v_skipProtected_925_);
v_res_927_ = l_Lean_getAliases(v_env_923_, v_a_924_, v_skipProtected_boxed_926_);
lean_dec(v_a_924_);
return v_res_927_;
}
}
LEAN_EXPORT lean_object* l_Lean_getRevAliases___lam__0(lean_object* v_e_928_, lean_object* v_as_929_, lean_object* v_a_930_, lean_object* v_es_931_){
_start:
{
uint8_t v___x_932_; 
v___x_932_ = l_List_elem___at___00Lean_addAliasEntry_spec__2(v_e_928_, v_es_931_);
if (v___x_932_ == 0)
{
lean_dec(v_a_930_);
return v_as_929_;
}
else
{
lean_object* v___x_933_; 
v___x_933_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_933_, 0, v_a_930_);
lean_ctor_set(v___x_933_, 1, v_as_929_);
return v___x_933_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getRevAliases___lam__0___boxed(lean_object* v_e_934_, lean_object* v_as_935_, lean_object* v_a_936_, lean_object* v_es_937_){
_start:
{
lean_object* v_res_938_; 
v_res_938_ = l_Lean_getRevAliases___lam__0(v_e_934_, v_as_935_, v_a_936_, v_es_937_);
lean_dec(v_es_937_);
lean_dec(v_e_934_);
return v_res_938_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6___redArg(lean_object* v_f_939_, lean_object* v_keys_940_, lean_object* v_vals_941_, lean_object* v_i_942_, lean_object* v_acc_943_){
_start:
{
lean_object* v___x_944_; uint8_t v___x_945_; 
v___x_944_ = lean_array_get_size(v_keys_940_);
v___x_945_ = lean_nat_dec_lt(v_i_942_, v___x_944_);
if (v___x_945_ == 0)
{
lean_dec(v_i_942_);
lean_dec(v_f_939_);
return v_acc_943_;
}
else
{
lean_object* v_k_946_; lean_object* v_v_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; 
v_k_946_ = lean_array_fget_borrowed(v_keys_940_, v_i_942_);
v_v_947_ = lean_array_fget_borrowed(v_vals_941_, v_i_942_);
lean_inc(v_f_939_);
lean_inc(v_v_947_);
lean_inc(v_k_946_);
v___x_948_ = lean_apply_3(v_f_939_, v_acc_943_, v_k_946_, v_v_947_);
v___x_949_ = lean_unsigned_to_nat(1u);
v___x_950_ = lean_nat_add(v_i_942_, v___x_949_);
lean_dec(v_i_942_);
v_i_942_ = v___x_950_;
v_acc_943_ = v___x_948_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_f_952_, lean_object* v_keys_953_, lean_object* v_vals_954_, lean_object* v_i_955_, lean_object* v_acc_956_){
_start:
{
lean_object* v_res_957_; 
v_res_957_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6___redArg(v_f_952_, v_keys_953_, v_vals_954_, v_i_955_, v_acc_956_);
lean_dec_ref(v_vals_954_);
lean_dec_ref(v_keys_953_);
return v_res_957_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_f_958_, lean_object* v_x_959_, lean_object* v_x_960_){
_start:
{
if (lean_obj_tag(v_x_959_) == 0)
{
lean_object* v_es_961_; lean_object* v___x_962_; lean_object* v___x_963_; uint8_t v___x_964_; 
v_es_961_ = lean_ctor_get(v_x_959_, 0);
v___x_962_ = lean_unsigned_to_nat(0u);
v___x_963_ = lean_array_get_size(v_es_961_);
v___x_964_ = lean_nat_dec_lt(v___x_962_, v___x_963_);
if (v___x_964_ == 0)
{
lean_dec(v_f_958_);
return v_x_960_;
}
else
{
uint8_t v___x_965_; 
v___x_965_ = lean_nat_dec_le(v___x_963_, v___x_963_);
if (v___x_965_ == 0)
{
if (v___x_964_ == 0)
{
lean_dec(v_f_958_);
return v_x_960_;
}
else
{
size_t v___x_966_; size_t v___x_967_; lean_object* v___x_968_; 
v___x_966_ = ((size_t)0ULL);
v___x_967_ = lean_usize_of_nat(v___x_963_);
v___x_968_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(v_f_958_, v_es_961_, v___x_966_, v___x_967_, v_x_960_);
return v___x_968_;
}
}
else
{
size_t v___x_969_; size_t v___x_970_; lean_object* v___x_971_; 
v___x_969_ = ((size_t)0ULL);
v___x_970_ = lean_usize_of_nat(v___x_963_);
v___x_971_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(v_f_958_, v_es_961_, v___x_969_, v___x_970_, v_x_960_);
return v___x_971_;
}
}
}
else
{
lean_object* v_ks_972_; lean_object* v_vs_973_; lean_object* v___x_974_; lean_object* v___x_975_; 
v_ks_972_ = lean_ctor_get(v_x_959_, 0);
v_vs_973_ = lean_ctor_get(v_x_959_, 1);
v___x_974_ = lean_unsigned_to_nat(0u);
v___x_975_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6___redArg(v_f_958_, v_ks_972_, v_vs_973_, v___x_974_, v_x_960_);
return v___x_975_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(lean_object* v_f_976_, lean_object* v_as_977_, size_t v_i_978_, size_t v_stop_979_, lean_object* v_b_980_){
_start:
{
lean_object* v___y_982_; uint8_t v___x_986_; 
v___x_986_ = lean_usize_dec_eq(v_i_978_, v_stop_979_);
if (v___x_986_ == 0)
{
lean_object* v___x_987_; 
v___x_987_ = lean_array_uget_borrowed(v_as_977_, v_i_978_);
switch(lean_obj_tag(v___x_987_))
{
case 0:
{
lean_object* v_key_988_; lean_object* v_val_989_; lean_object* v___x_990_; 
v_key_988_ = lean_ctor_get(v___x_987_, 0);
v_val_989_ = lean_ctor_get(v___x_987_, 1);
lean_inc(v_f_976_);
lean_inc(v_val_989_);
lean_inc(v_key_988_);
v___x_990_ = lean_apply_3(v_f_976_, v_b_980_, v_key_988_, v_val_989_);
v___y_982_ = v___x_990_;
goto v___jp_981_;
}
case 1:
{
lean_object* v_node_991_; lean_object* v___x_992_; 
v_node_991_ = lean_ctor_get(v___x_987_, 0);
lean_inc(v_f_976_);
v___x_992_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg(v_f_976_, v_node_991_, v_b_980_);
v___y_982_ = v___x_992_;
goto v___jp_981_;
}
default: 
{
v___y_982_ = v_b_980_;
goto v___jp_981_;
}
}
}
else
{
lean_dec(v_f_976_);
return v_b_980_;
}
v___jp_981_:
{
size_t v___x_983_; size_t v___x_984_; 
v___x_983_ = ((size_t)1ULL);
v___x_984_ = lean_usize_add(v_i_978_, v___x_983_);
v_i_978_ = v___x_984_;
v_b_980_ = v___y_982_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v_f_993_, lean_object* v_as_994_, lean_object* v_i_995_, lean_object* v_stop_996_, lean_object* v_b_997_){
_start:
{
size_t v_i_boxed_998_; size_t v_stop_boxed_999_; lean_object* v_res_1000_; 
v_i_boxed_998_ = lean_unbox_usize(v_i_995_);
lean_dec(v_i_995_);
v_stop_boxed_999_ = lean_unbox_usize(v_stop_996_);
lean_dec(v_stop_996_);
v_res_1000_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(v_f_993_, v_as_994_, v_i_boxed_998_, v_stop_boxed_999_, v_b_997_);
lean_dec_ref(v_as_994_);
return v_res_1000_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_f_1001_, lean_object* v_x_1002_, lean_object* v_x_1003_){
_start:
{
lean_object* v_res_1004_; 
v_res_1004_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg(v_f_1001_, v_x_1002_, v_x_1003_);
lean_dec_ref(v_x_1002_);
return v_res_1004_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg___lam__0(lean_object* v_f_1005_, lean_object* v_x1_1006_, lean_object* v_x2_1007_, lean_object* v_x3_1008_){
_start:
{
lean_object* v___x_1009_; 
v___x_1009_ = lean_apply_3(v_f_1005_, v_x1_1006_, v_x2_1007_, v_x3_1008_);
return v___x_1009_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg(lean_object* v_map_1010_, lean_object* v_f_1011_, lean_object* v_init_1012_){
_start:
{
lean_object* v___f_1013_; lean_object* v___x_1014_; 
v___f_1013_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1013_, 0, v_f_1011_);
v___x_1014_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg(v___f_1013_, v_map_1010_, v_init_1012_);
return v___x_1014_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg___boxed(lean_object* v_map_1015_, lean_object* v_f_1016_, lean_object* v_init_1017_){
_start:
{
lean_object* v_res_1018_; 
v_res_1018_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg(v_map_1015_, v_f_1016_, v_init_1017_);
lean_dec_ref(v_map_1015_);
return v_res_1018_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__0___redArg(lean_object* v_f_1019_, lean_object* v_x_1020_, lean_object* v_x_1021_){
_start:
{
if (lean_obj_tag(v_x_1021_) == 0)
{
lean_dec(v_f_1019_);
return v_x_1020_;
}
else
{
lean_object* v_key_1022_; lean_object* v_value_1023_; lean_object* v_tail_1024_; lean_object* v___x_1025_; 
v_key_1022_ = lean_ctor_get(v_x_1021_, 0);
lean_inc(v_key_1022_);
v_value_1023_ = lean_ctor_get(v_x_1021_, 1);
lean_inc(v_value_1023_);
v_tail_1024_ = lean_ctor_get(v_x_1021_, 2);
lean_inc(v_tail_1024_);
lean_dec_ref_known(v_x_1021_, 3);
lean_inc(v_f_1019_);
v___x_1025_ = lean_apply_3(v_f_1019_, v_x_1020_, v_key_1022_, v_value_1023_);
v_x_1020_ = v___x_1025_;
v_x_1021_ = v_tail_1024_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2___redArg(lean_object* v_f_1027_, lean_object* v_as_1028_, size_t v_i_1029_, size_t v_stop_1030_, lean_object* v_b_1031_){
_start:
{
uint8_t v___x_1032_; 
v___x_1032_ = lean_usize_dec_eq(v_i_1029_, v_stop_1030_);
if (v___x_1032_ == 0)
{
lean_object* v___x_1033_; lean_object* v___x_1034_; size_t v___x_1035_; size_t v___x_1036_; 
v___x_1033_ = lean_array_uget_borrowed(v_as_1028_, v_i_1029_);
lean_inc(v___x_1033_);
lean_inc(v_f_1027_);
v___x_1034_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__0___redArg(v_f_1027_, v_b_1031_, v___x_1033_);
v___x_1035_ = ((size_t)1ULL);
v___x_1036_ = lean_usize_add(v_i_1029_, v___x_1035_);
v_i_1029_ = v___x_1036_;
v_b_1031_ = v___x_1034_;
goto _start;
}
else
{
lean_dec(v_f_1027_);
return v_b_1031_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2___redArg___boxed(lean_object* v_f_1038_, lean_object* v_as_1039_, lean_object* v_i_1040_, lean_object* v_stop_1041_, lean_object* v_b_1042_){
_start:
{
size_t v_i_boxed_1043_; size_t v_stop_boxed_1044_; lean_object* v_res_1045_; 
v_i_boxed_1043_ = lean_unbox_usize(v_i_1040_);
lean_dec(v_i_1040_);
v_stop_boxed_1044_ = lean_unbox_usize(v_stop_1041_);
lean_dec(v_stop_1041_);
v_res_1045_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2___redArg(v_f_1038_, v_as_1039_, v_i_boxed_1043_, v_stop_boxed_1044_, v_b_1042_);
lean_dec_ref(v_as_1039_);
return v_res_1045_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0___redArg(lean_object* v_f_1046_, lean_object* v_init_1047_, lean_object* v_m_1048_){
_start:
{
lean_object* v_map_u2081_1049_; lean_object* v_map_u2082_1050_; lean_object* v_buckets_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; uint8_t v___x_1054_; 
v_map_u2081_1049_ = lean_ctor_get(v_m_1048_, 0);
v_map_u2082_1050_ = lean_ctor_get(v_m_1048_, 1);
v_buckets_1051_ = lean_ctor_get(v_map_u2081_1049_, 1);
v___x_1052_ = lean_unsigned_to_nat(0u);
v___x_1053_ = lean_array_get_size(v_buckets_1051_);
v___x_1054_ = lean_nat_dec_lt(v___x_1052_, v___x_1053_);
if (v___x_1054_ == 0)
{
lean_object* v___x_1055_; 
v___x_1055_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg(v_map_u2082_1050_, v_f_1046_, v_init_1047_);
return v___x_1055_;
}
else
{
uint8_t v___x_1056_; 
v___x_1056_ = lean_nat_dec_le(v___x_1053_, v___x_1053_);
if (v___x_1056_ == 0)
{
if (v___x_1054_ == 0)
{
lean_object* v___x_1057_; 
v___x_1057_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg(v_map_u2082_1050_, v_f_1046_, v_init_1047_);
return v___x_1057_;
}
else
{
size_t v___x_1058_; size_t v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; 
v___x_1058_ = ((size_t)0ULL);
v___x_1059_ = lean_usize_of_nat(v___x_1053_);
lean_inc(v_f_1046_);
v___x_1060_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2___redArg(v_f_1046_, v_buckets_1051_, v___x_1058_, v___x_1059_, v_init_1047_);
v___x_1061_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg(v_map_u2082_1050_, v_f_1046_, v___x_1060_);
return v___x_1061_;
}
}
else
{
size_t v___x_1062_; size_t v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; 
v___x_1062_ = ((size_t)0ULL);
v___x_1063_ = lean_usize_of_nat(v___x_1053_);
lean_inc(v_f_1046_);
v___x_1064_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2___redArg(v_f_1046_, v_buckets_1051_, v___x_1062_, v___x_1063_, v_init_1047_);
v___x_1065_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg(v_map_u2082_1050_, v_f_1046_, v___x_1064_);
return v___x_1065_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0___redArg___boxed(lean_object* v_f_1066_, lean_object* v_init_1067_, lean_object* v_m_1068_){
_start:
{
lean_object* v_res_1069_; 
v_res_1069_ = l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0___redArg(v_f_1066_, v_init_1067_, v_m_1068_);
lean_dec_ref(v_m_1068_);
return v_res_1069_;
}
}
LEAN_EXPORT lean_object* l_Lean_getRevAliases(lean_object* v_env_1070_, lean_object* v_e_1071_){
_start:
{
lean_object* v___x_1072_; lean_object* v_toEnvExtension_1073_; lean_object* v_asyncMode_1074_; lean_object* v___f_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; 
v___x_1072_ = l_Lean_aliasExtension;
v_toEnvExtension_1073_ = lean_ctor_get(v___x_1072_, 0);
v_asyncMode_1074_ = lean_ctor_get(v_toEnvExtension_1073_, 2);
v___f_1075_ = lean_alloc_closure((void*)(l_Lean_getRevAliases___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1075_, 0, v_e_1071_);
v___x_1076_ = lean_obj_once(&l_Lean_getAliasState___closed__2, &l_Lean_getAliasState___closed__2_once, _init_l_Lean_getAliasState___closed__2);
v___x_1077_ = lean_box(0);
v___x_1078_ = lean_box(0);
v___x_1079_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1076_, v___x_1072_, v_env_1070_, v_asyncMode_1074_, v___x_1078_);
v___x_1080_ = l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0___redArg(v___f_1075_, v___x_1077_, v___x_1079_);
lean_dec(v___x_1079_);
return v___x_1080_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0(lean_object* v_00_u03b2_1081_, lean_object* v_00_u03c3_1082_, lean_object* v_f_1083_, lean_object* v_init_1084_, lean_object* v_m_1085_){
_start:
{
lean_object* v___x_1086_; 
v___x_1086_ = l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0___redArg(v_f_1083_, v_init_1084_, v_m_1085_);
return v___x_1086_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0___boxed(lean_object* v_00_u03b2_1087_, lean_object* v_00_u03c3_1088_, lean_object* v_f_1089_, lean_object* v_init_1090_, lean_object* v_m_1091_){
_start:
{
lean_object* v_res_1092_; 
v_res_1092_ = l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0(v_00_u03b2_1087_, v_00_u03c3_1088_, v_f_1089_, v_init_1090_, v_m_1091_);
lean_dec_ref(v_m_1091_);
return v_res_1092_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__0(lean_object* v_00_u03b2_1093_, lean_object* v_00_u03c3_1094_, lean_object* v_f_1095_, lean_object* v_x_1096_, lean_object* v_x_1097_){
_start:
{
lean_object* v___x_1098_; 
v___x_1098_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__0___redArg(v_f_1095_, v_x_1096_, v_x_1097_);
return v___x_1098_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1(lean_object* v_00_u03c3_1099_, lean_object* v_00_u03b2_1100_, lean_object* v_map_1101_, lean_object* v_f_1102_, lean_object* v_init_1103_){
_start:
{
lean_object* v___x_1104_; 
v___x_1104_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg(v_map_1101_, v_f_1102_, v_init_1103_);
return v___x_1104_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___boxed(lean_object* v_00_u03c3_1105_, lean_object* v_00_u03b2_1106_, lean_object* v_map_1107_, lean_object* v_f_1108_, lean_object* v_init_1109_){
_start:
{
lean_object* v_res_1110_; 
v_res_1110_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1(v_00_u03c3_1105_, v_00_u03b2_1106_, v_map_1107_, v_f_1108_, v_init_1109_);
lean_dec_ref(v_map_1107_);
return v_res_1110_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2(lean_object* v_00_u03b2_1111_, lean_object* v_00_u03c3_1112_, lean_object* v_f_1113_, lean_object* v_as_1114_, size_t v_i_1115_, size_t v_stop_1116_, lean_object* v_b_1117_){
_start:
{
lean_object* v___x_1118_; 
v___x_1118_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2___redArg(v_f_1113_, v_as_1114_, v_i_1115_, v_stop_1116_, v_b_1117_);
return v___x_1118_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1119_, lean_object* v_00_u03c3_1120_, lean_object* v_f_1121_, lean_object* v_as_1122_, lean_object* v_i_1123_, lean_object* v_stop_1124_, lean_object* v_b_1125_){
_start:
{
size_t v_i_boxed_1126_; size_t v_stop_boxed_1127_; lean_object* v_res_1128_; 
v_i_boxed_1126_ = lean_unbox_usize(v_i_1123_);
lean_dec(v_i_1123_);
v_stop_boxed_1127_ = lean_unbox_usize(v_stop_1124_);
lean_dec(v_stop_1124_);
v_res_1128_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2(v_00_u03b2_1119_, v_00_u03c3_1120_, v_f_1121_, v_as_1122_, v_i_boxed_1126_, v_stop_boxed_1127_, v_b_1125_);
lean_dec_ref(v_as_1122_);
return v_res_1128_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2___redArg(lean_object* v_map_1129_, lean_object* v_f_1130_, lean_object* v_init_1131_){
_start:
{
lean_object* v___x_1132_; 
v___x_1132_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg(v_f_1130_, v_map_1129_, v_init_1131_);
return v___x_1132_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_map_1133_, lean_object* v_f_1134_, lean_object* v_init_1135_){
_start:
{
lean_object* v_res_1136_; 
v_res_1136_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2___redArg(v_map_1133_, v_f_1134_, v_init_1135_);
lean_dec_ref(v_map_1133_);
return v_res_1136_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2(lean_object* v_00_u03c3_1137_, lean_object* v_00_u03b2_1138_, lean_object* v_map_1139_, lean_object* v_f_1140_, lean_object* v_init_1141_){
_start:
{
lean_object* v___x_1142_; 
v___x_1142_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg(v_f_1140_, v_map_1139_, v_init_1141_);
return v___x_1142_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03c3_1143_, lean_object* v_00_u03b2_1144_, lean_object* v_map_1145_, lean_object* v_f_1146_, lean_object* v_init_1147_){
_start:
{
lean_object* v_res_1148_; 
v_res_1148_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2(v_00_u03c3_1143_, v_00_u03b2_1144_, v_map_1145_, v_f_1146_, v_init_1147_);
lean_dec_ref(v_map_1145_);
return v_res_1148_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03c3_1149_, lean_object* v_00_u03b1_1150_, lean_object* v_00_u03b2_1151_, lean_object* v_f_1152_, lean_object* v_x_1153_, lean_object* v_x_1154_){
_start:
{
lean_object* v___x_1155_; 
v___x_1155_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg(v_f_1152_, v_x_1153_, v_x_1154_);
return v___x_1155_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03c3_1156_, lean_object* v_00_u03b1_1157_, lean_object* v_00_u03b2_1158_, lean_object* v_f_1159_, lean_object* v_x_1160_, lean_object* v_x_1161_){
_start:
{
lean_object* v_res_1162_; 
v_res_1162_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3(v_00_u03c3_1156_, v_00_u03b1_1157_, v_00_u03b2_1158_, v_f_1159_, v_x_1160_, v_x_1161_);
lean_dec_ref(v_x_1160_);
return v_res_1162_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5(lean_object* v_00_u03b1_1163_, lean_object* v_00_u03b2_1164_, lean_object* v_00_u03c3_1165_, lean_object* v_f_1166_, lean_object* v_as_1167_, size_t v_i_1168_, size_t v_stop_1169_, lean_object* v_b_1170_){
_start:
{
lean_object* v___x_1171_; 
v___x_1171_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(v_f_1166_, v_as_1167_, v_i_1168_, v_stop_1169_, v_b_1170_);
return v___x_1171_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5___boxed(lean_object* v_00_u03b1_1172_, lean_object* v_00_u03b2_1173_, lean_object* v_00_u03c3_1174_, lean_object* v_f_1175_, lean_object* v_as_1176_, lean_object* v_i_1177_, lean_object* v_stop_1178_, lean_object* v_b_1179_){
_start:
{
size_t v_i_boxed_1180_; size_t v_stop_boxed_1181_; lean_object* v_res_1182_; 
v_i_boxed_1180_ = lean_unbox_usize(v_i_1177_);
lean_dec(v_i_1177_);
v_stop_boxed_1181_ = lean_unbox_usize(v_stop_1178_);
lean_dec(v_stop_1178_);
v_res_1182_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5(v_00_u03b1_1172_, v_00_u03b2_1173_, v_00_u03c3_1174_, v_f_1175_, v_as_1176_, v_i_boxed_1180_, v_stop_boxed_1181_, v_b_1179_);
lean_dec_ref(v_as_1176_);
return v_res_1182_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6(lean_object* v_00_u03c3_1183_, lean_object* v_00_u03b1_1184_, lean_object* v_00_u03b2_1185_, lean_object* v_f_1186_, lean_object* v_keys_1187_, lean_object* v_vals_1188_, lean_object* v_heq_1189_, lean_object* v_i_1190_, lean_object* v_acc_1191_){
_start:
{
lean_object* v___x_1192_; 
v___x_1192_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6___redArg(v_f_1186_, v_keys_1187_, v_vals_1188_, v_i_1190_, v_acc_1191_);
return v___x_1192_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03c3_1193_, lean_object* v_00_u03b1_1194_, lean_object* v_00_u03b2_1195_, lean_object* v_f_1196_, lean_object* v_keys_1197_, lean_object* v_vals_1198_, lean_object* v_heq_1199_, lean_object* v_i_1200_, lean_object* v_acc_1201_){
_start:
{
lean_object* v_res_1202_; 
v_res_1202_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6(v_00_u03c3_1193_, v_00_u03b1_1194_, v_00_u03b2_1195_, v_f_1196_, v_keys_1197_, v_vals_1198_, v_heq_1199_, v_i_1200_, v_acc_1201_);
lean_dec_ref(v_vals_1198_);
lean_dec_ref(v_keys_1197_);
return v_res_1202_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(lean_object* v_env_1203_, lean_object* v_declName_1204_){
_start:
{
uint8_t v___y_1206_; uint8_t v___x_1209_; 
v___x_1209_ = l_Lean_Environment_containsOnBranch(v_env_1203_, v_declName_1204_);
if (v___x_1209_ == 0)
{
uint8_t v___x_1210_; 
lean_inc(v_declName_1204_);
lean_inc_ref(v_env_1203_);
v___x_1210_ = lean_is_reserved_name(v_env_1203_, v_declName_1204_);
v___y_1206_ = v___x_1210_;
goto v___jp_1205_;
}
else
{
v___y_1206_ = v___x_1209_;
goto v___jp_1205_;
}
v___jp_1205_:
{
if (v___y_1206_ == 0)
{
uint8_t v___x_1207_; uint8_t v___x_1208_; 
v___x_1207_ = 1;
v___x_1208_ = l_Lean_Environment_contains(v_env_1203_, v_declName_1204_, v___x_1207_);
return v___x_1208_;
}
else
{
lean_dec(v_declName_1204_);
lean_dec_ref(v_env_1203_);
return v___y_1206_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved___boxed(lean_object* v_env_1211_, lean_object* v_declName_1212_){
_start:
{
uint8_t v_res_1213_; lean_object* v_r_1214_; 
v_res_1213_ = l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(v_env_1211_, v_declName_1212_);
v_r_1214_ = lean_box(v_res_1213_);
return v_r_1214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__spec__0(lean_object* v_name_1215_, lean_object* v_decl_1216_, lean_object* v_ref_1217_){
_start:
{
lean_object* v_defValue_1219_; lean_object* v_descr_1220_; lean_object* v_deprecation_x3f_1221_; lean_object* v___x_1222_; uint8_t v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; 
v_defValue_1219_ = lean_ctor_get(v_decl_1216_, 0);
v_descr_1220_ = lean_ctor_get(v_decl_1216_, 1);
v_deprecation_x3f_1221_ = lean_ctor_get(v_decl_1216_, 2);
v___x_1222_ = lean_alloc_ctor(1, 0, 1);
v___x_1223_ = lean_unbox(v_defValue_1219_);
lean_ctor_set_uint8(v___x_1222_, 0, v___x_1223_);
lean_inc(v_deprecation_x3f_1221_);
lean_inc_ref(v_descr_1220_);
lean_inc_n(v_name_1215_, 2);
v___x_1224_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1224_, 0, v_name_1215_);
lean_ctor_set(v___x_1224_, 1, v_ref_1217_);
lean_ctor_set(v___x_1224_, 2, v___x_1222_);
lean_ctor_set(v___x_1224_, 3, v_descr_1220_);
lean_ctor_set(v___x_1224_, 4, v_deprecation_x3f_1221_);
v___x_1225_ = lean_register_option(v_name_1215_, v___x_1224_);
if (lean_obj_tag(v___x_1225_) == 0)
{
lean_object* v___x_1227_; uint8_t v_isShared_1228_; uint8_t v_isSharedCheck_1233_; 
v_isSharedCheck_1233_ = !lean_is_exclusive(v___x_1225_);
if (v_isSharedCheck_1233_ == 0)
{
lean_object* v_unused_1234_; 
v_unused_1234_ = lean_ctor_get(v___x_1225_, 0);
lean_dec(v_unused_1234_);
v___x_1227_ = v___x_1225_;
v_isShared_1228_ = v_isSharedCheck_1233_;
goto v_resetjp_1226_;
}
else
{
lean_dec(v___x_1225_);
v___x_1227_ = lean_box(0);
v_isShared_1228_ = v_isSharedCheck_1233_;
goto v_resetjp_1226_;
}
v_resetjp_1226_:
{
lean_object* v___x_1229_; lean_object* v___x_1231_; 
lean_inc(v_defValue_1219_);
v___x_1229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1229_, 0, v_name_1215_);
lean_ctor_set(v___x_1229_, 1, v_defValue_1219_);
if (v_isShared_1228_ == 0)
{
lean_ctor_set(v___x_1227_, 0, v___x_1229_);
v___x_1231_ = v___x_1227_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v___x_1229_);
v___x_1231_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
return v___x_1231_;
}
}
}
else
{
lean_object* v_a_1235_; lean_object* v___x_1237_; uint8_t v_isShared_1238_; uint8_t v_isSharedCheck_1242_; 
lean_dec(v_name_1215_);
v_a_1235_ = lean_ctor_get(v___x_1225_, 0);
v_isSharedCheck_1242_ = !lean_is_exclusive(v___x_1225_);
if (v_isSharedCheck_1242_ == 0)
{
v___x_1237_ = v___x_1225_;
v_isShared_1238_ = v_isSharedCheck_1242_;
goto v_resetjp_1236_;
}
else
{
lean_inc(v_a_1235_);
lean_dec(v___x_1225_);
v___x_1237_ = lean_box(0);
v_isShared_1238_ = v_isSharedCheck_1242_;
goto v_resetjp_1236_;
}
v_resetjp_1236_:
{
lean_object* v___x_1240_; 
if (v_isShared_1238_ == 0)
{
v___x_1240_ = v___x_1237_;
goto v_reusejp_1239_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v_a_1235_);
v___x_1240_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1239_;
}
v_reusejp_1239_:
{
return v___x_1240_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_1243_, lean_object* v_decl_1244_, lean_object* v_ref_1245_, lean_object* v_a_1246_){
_start:
{
lean_object* v_res_1247_; 
v_res_1247_ = l_Lean_Option_register___at___00__private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__spec__0(v_name_1243_, v_decl_1244_, v_ref_1245_);
lean_dec_ref(v_decl_1244_);
return v_res_1247_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; 
v___x_1266_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__2_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_));
v___x_1267_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__4_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_));
v___x_1268_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__6_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_));
v___x_1269_ = l_Lean_Option_register___at___00__private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__spec__0(v___x_1266_, v___x_1267_, v___x_1268_);
return v___x_1269_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4____boxed(lean_object* v_a_1270_){
_start:
{
lean_object* v_res_1271_; 
v_res_1271_ = l___private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_();
return v_res_1271_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; 
v___x_1290_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__1_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4_));
v___x_1291_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__3_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4_));
v___x_1292_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__4_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4_));
v___x_1293_ = l_Lean_Option_register___at___00__private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__spec__0(v___x_1290_, v___x_1291_, v___x_1292_);
return v___x_1293_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4____boxed(lean_object* v_a_1294_){
_start:
{
lean_object* v_res_1295_; 
v_res_1295_ = l___private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4_();
return v_res_1295_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__1(lean_object* v_opts_1296_, lean_object* v_opt_1297_){
_start:
{
lean_object* v_name_1298_; lean_object* v_defValue_1299_; lean_object* v_map_1300_; lean_object* v___x_1301_; 
v_name_1298_ = lean_ctor_get(v_opt_1297_, 0);
v_defValue_1299_ = lean_ctor_get(v_opt_1297_, 1);
v_map_1300_ = lean_ctor_get(v_opts_1296_, 0);
v___x_1301_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1300_, v_name_1298_);
if (lean_obj_tag(v___x_1301_) == 0)
{
uint8_t v___x_1302_; 
v___x_1302_ = lean_unbox(v_defValue_1299_);
return v___x_1302_;
}
else
{
lean_object* v_val_1303_; 
v_val_1303_ = lean_ctor_get(v___x_1301_, 0);
lean_inc(v_val_1303_);
lean_dec_ref_known(v___x_1301_, 1);
if (lean_obj_tag(v_val_1303_) == 1)
{
uint8_t v_v_1304_; 
v_v_1304_ = lean_ctor_get_uint8(v_val_1303_, 0);
lean_dec_ref_known(v_val_1303_, 0);
return v_v_1304_;
}
else
{
uint8_t v___x_1305_; 
lean_dec(v_val_1303_);
v___x_1305_ = lean_unbox(v_defValue_1299_);
return v___x_1305_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__1___boxed(lean_object* v_opts_1306_, lean_object* v_opt_1307_){
_start:
{
uint8_t v_res_1308_; lean_object* v_r_1309_; 
v_res_1308_ = l_Lean_Option_get___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__1(v_opts_1306_, v_opt_1307_);
lean_dec_ref(v_opt_1307_);
lean_dec_ref(v_opts_1306_);
v_r_1309_ = lean_box(v_res_1308_);
return v_r_1309_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0(lean_object* v_declName_1313_, lean_object* v_env_1314_, lean_object* v_as_1315_, size_t v_sz_1316_, size_t v_i_1317_, lean_object* v_b_1318_){
_start:
{
uint8_t v___x_1319_; 
v___x_1319_ = lean_usize_dec_lt(v_i_1317_, v_sz_1316_);
if (v___x_1319_ == 0)
{
lean_dec_ref(v_env_1314_);
lean_dec(v_declName_1313_);
lean_inc_ref(v_b_1318_);
return v_b_1318_;
}
else
{
lean_object* v_a_1320_; lean_object* v_toImport_1321_; lean_object* v_module_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; uint8_t v___x_1325_; 
v_a_1320_ = lean_array_uget_borrowed(v_as_1315_, v_i_1317_);
v_toImport_1321_ = lean_ctor_get(v_a_1320_, 0);
v_module_1322_ = lean_ctor_get(v_toImport_1321_, 0);
v___x_1323_ = lean_box(0);
lean_inc(v_declName_1313_);
lean_inc(v_module_1322_);
v___x_1324_ = l_Lean_mkPrivateNameCore(v_module_1322_, v_declName_1313_);
lean_inc(v___x_1324_);
lean_inc_ref(v_env_1314_);
v___x_1325_ = l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(v_env_1314_, v___x_1324_);
if (v___x_1325_ == 0)
{
lean_object* v___x_1326_; size_t v___x_1327_; size_t v___x_1328_; 
lean_dec(v___x_1324_);
v___x_1326_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0___closed__0));
v___x_1327_ = ((size_t)1ULL);
v___x_1328_ = lean_usize_add(v_i_1317_, v___x_1327_);
v_i_1317_ = v___x_1328_;
v_b_1318_ = v___x_1326_;
goto _start;
}
else
{
lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; 
lean_dec_ref(v_env_1314_);
lean_dec(v_declName_1313_);
v___x_1330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1330_, 0, v___x_1324_);
v___x_1331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1331_, 0, v___x_1330_);
v___x_1332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1332_, 0, v___x_1331_);
lean_ctor_set(v___x_1332_, 1, v___x_1323_);
return v___x_1332_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0___boxed(lean_object* v_declName_1333_, lean_object* v_env_1334_, lean_object* v_as_1335_, lean_object* v_sz_1336_, lean_object* v_i_1337_, lean_object* v_b_1338_){
_start:
{
size_t v_sz_boxed_1339_; size_t v_i_boxed_1340_; lean_object* v_res_1341_; 
v_sz_boxed_1339_ = lean_unbox_usize(v_sz_1336_);
lean_dec(v_sz_1336_);
v_i_boxed_1340_ = lean_unbox_usize(v_i_1337_);
lean_dec(v_i_1337_);
v_res_1341_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0(v_declName_1333_, v_env_1334_, v_as_1335_, v_sz_boxed_1339_, v_i_boxed_1340_, v_b_1338_);
lean_dec_ref(v_b_1338_);
lean_dec_ref(v_as_1335_);
return v_res_1341_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName(lean_object* v_env_1342_, lean_object* v_opts_1343_, lean_object* v_declName_1344_){
_start:
{
uint8_t v___y_1346_; uint8_t v_isExporting_1362_; uint8_t v___x_1363_; 
v_isExporting_1362_ = lean_ctor_get_uint8(v_env_1342_, sizeof(void*)*8);
v___x_1363_ = lean_bool_not(v_isExporting_1362_);
if (v___x_1363_ == 0)
{
lean_object* v___x_1364_; uint8_t v___x_1365_; 
v___x_1364_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_1365_ = l_Lean_Option_get___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__1(v_opts_1343_, v___x_1364_);
v___y_1346_ = v___x_1365_;
goto v___jp_1345_;
}
else
{
v___y_1346_ = v___x_1363_;
goto v___jp_1345_;
}
v___jp_1345_:
{
if (v___y_1346_ == 0)
{
lean_object* v___x_1347_; 
lean_dec(v_declName_1344_);
lean_dec_ref(v_env_1342_);
v___x_1347_ = lean_box(0);
return v___x_1347_;
}
else
{
lean_object* v___x_1348_; uint8_t v___x_1349_; 
lean_inc(v_declName_1344_);
v___x_1348_ = l_Lean_mkPrivateName(v_env_1342_, v_declName_1344_);
lean_inc(v___x_1348_);
lean_inc_ref(v_env_1342_);
v___x_1349_ = l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(v_env_1342_, v___x_1348_);
if (v___x_1349_ == 0)
{
lean_object* v___x_1350_; uint8_t v_isModule_1351_; 
lean_dec(v___x_1348_);
v___x_1350_ = l_Lean_Environment_header(v_env_1342_);
v_isModule_1351_ = lean_ctor_get_uint8(v___x_1350_, sizeof(void*)*7 + 4);
if (v_isModule_1351_ == 0)
{
lean_object* v___x_1352_; 
lean_dec_ref(v___x_1350_);
lean_dec(v_declName_1344_);
lean_dec_ref(v_env_1342_);
v___x_1352_ = lean_box(0);
return v___x_1352_;
}
else
{
lean_object* v_importAllModules_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; size_t v_sz_1356_; size_t v___x_1357_; lean_object* v___x_1358_; lean_object* v_fst_1359_; 
v_importAllModules_1353_ = lean_ctor_get(v___x_1350_, 5);
lean_inc_ref(v_importAllModules_1353_);
lean_dec_ref(v___x_1350_);
v___x_1354_ = lean_box(0);
v___x_1355_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0___closed__0));
v_sz_1356_ = lean_array_size(v_importAllModules_1353_);
v___x_1357_ = ((size_t)0ULL);
v___x_1358_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0(v_declName_1344_, v_env_1342_, v_importAllModules_1353_, v_sz_1356_, v___x_1357_, v___x_1355_);
lean_dec_ref(v_importAllModules_1353_);
v_fst_1359_ = lean_ctor_get(v___x_1358_, 0);
lean_inc(v_fst_1359_);
lean_dec_ref(v___x_1358_);
if (lean_obj_tag(v_fst_1359_) == 0)
{
return v___x_1354_;
}
else
{
lean_object* v_val_1360_; 
v_val_1360_ = lean_ctor_get(v_fst_1359_, 0);
lean_inc(v_val_1360_);
lean_dec_ref_known(v_fst_1359_, 1);
return v_val_1360_;
}
}
}
else
{
lean_object* v___x_1361_; 
lean_dec(v_declName_1344_);
lean_dec_ref(v_env_1342_);
v___x_1361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1361_, 0, v___x_1348_);
return v___x_1361_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName___boxed(lean_object* v_env_1366_, lean_object* v_opts_1367_, lean_object* v_declName_1368_){
_start:
{
lean_object* v_res_1369_; 
v_res_1369_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName(v_env_1366_, v_opts_1367_, v_declName_1368_);
lean_dec_ref(v_opts_1367_);
return v_res_1369_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveQualifiedName(lean_object* v_env_1370_, lean_object* v_opts_1371_, lean_object* v_ns_1372_, lean_object* v_id_1373_){
_start:
{
lean_object* v_resolvedId_1374_; uint8_t v___x_1375_; lean_object* v_resolvedIds_1376_; uint8_t v___y_1378_; uint8_t v___x_1384_; 
lean_inc(v_id_1373_);
v_resolvedId_1374_ = l_Lean_Name_append(v_ns_1372_, v_id_1373_);
v___x_1375_ = l_Lean_Name_isAtomic(v_id_1373_);
lean_dec(v_id_1373_);
lean_inc_ref(v_env_1370_);
v_resolvedIds_1376_ = l_Lean_getAliases(v_env_1370_, v_resolvedId_1374_, v___x_1375_);
v___x_1384_ = lean_bool_not(v___x_1375_);
if (v___x_1384_ == 0)
{
uint8_t v___x_1385_; uint8_t v___x_1386_; 
lean_inc(v_resolvedId_1374_);
lean_inc_ref(v_env_1370_);
v___x_1385_ = l_Lean_isProtected(v_env_1370_, v_resolvedId_1374_);
v___x_1386_ = lean_bool_not(v___x_1385_);
v___y_1378_ = v___x_1386_;
goto v___jp_1377_;
}
else
{
v___y_1378_ = v___x_1384_;
goto v___jp_1377_;
}
v___jp_1377_:
{
if (v___y_1378_ == 0)
{
lean_dec(v_resolvedId_1374_);
lean_dec_ref(v_env_1370_);
return v_resolvedIds_1376_;
}
else
{
uint8_t v___x_1379_; 
lean_inc(v_resolvedId_1374_);
lean_inc_ref(v_env_1370_);
v___x_1379_ = l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(v_env_1370_, v_resolvedId_1374_);
if (v___x_1379_ == 0)
{
lean_object* v___x_1380_; 
v___x_1380_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName(v_env_1370_, v_opts_1371_, v_resolvedId_1374_);
if (lean_obj_tag(v___x_1380_) == 1)
{
lean_object* v_val_1381_; lean_object* v___x_1382_; 
v_val_1381_ = lean_ctor_get(v___x_1380_, 0);
lean_inc(v_val_1381_);
lean_dec_ref_known(v___x_1380_, 1);
v___x_1382_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1382_, 0, v_val_1381_);
lean_ctor_set(v___x_1382_, 1, v_resolvedIds_1376_);
return v___x_1382_;
}
else
{
lean_dec(v___x_1380_);
return v_resolvedIds_1376_;
}
}
else
{
lean_object* v___x_1383_; 
lean_dec_ref(v_env_1370_);
v___x_1383_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1383_, 0, v_resolvedId_1374_);
lean_ctor_set(v___x_1383_, 1, v_resolvedIds_1376_);
return v___x_1383_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveQualifiedName___boxed(lean_object* v_env_1387_, lean_object* v_opts_1388_, lean_object* v_ns_1389_, lean_object* v_id_1390_){
_start:
{
lean_object* v_res_1391_; 
v_res_1391_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveQualifiedName(v_env_1387_, v_opts_1388_, v_ns_1389_, v_id_1390_);
lean_dec_ref(v_opts_1388_);
return v_res_1391_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveUsingNamespace(lean_object* v_env_1392_, lean_object* v_opts_1393_, lean_object* v_id_1394_, lean_object* v_x_1395_){
_start:
{
if (lean_obj_tag(v_x_1395_) == 1)
{
lean_object* v_pre_1396_; lean_object* v___x_1397_; 
v_pre_1396_ = lean_ctor_get(v_x_1395_, 0);
lean_inc(v_pre_1396_);
lean_inc(v_id_1394_);
lean_inc_ref(v_env_1392_);
v___x_1397_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveQualifiedName(v_env_1392_, v_opts_1393_, v_x_1395_, v_id_1394_);
if (lean_obj_tag(v___x_1397_) == 0)
{
v_x_1395_ = v_pre_1396_;
goto _start;
}
else
{
lean_dec(v_pre_1396_);
lean_dec(v_id_1394_);
lean_dec_ref(v_env_1392_);
return v___x_1397_;
}
}
else
{
lean_object* v___x_1399_; 
lean_dec(v_x_1395_);
lean_dec(v_id_1394_);
lean_dec_ref(v_env_1392_);
v___x_1399_ = lean_box(0);
return v___x_1399_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveUsingNamespace___boxed(lean_object* v_env_1400_, lean_object* v_opts_1401_, lean_object* v_id_1402_, lean_object* v_x_1403_){
_start:
{
lean_object* v_res_1404_; 
v_res_1404_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveUsingNamespace(v_env_1400_, v_opts_1401_, v_id_1402_, v_x_1403_);
lean_dec_ref(v_opts_1401_);
return v_res_1404_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveExact(lean_object* v_env_1405_, lean_object* v_opts_1406_, lean_object* v_id_1407_){
_start:
{
uint8_t v___x_1408_; 
v___x_1408_ = l_Lean_Name_isAtomic(v_id_1407_);
if (v___x_1408_ == 0)
{
lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v_resolvedId_1411_; uint8_t v___x_1412_; 
v___x_1409_ = l_Lean_rootNamespace;
v___x_1410_ = lean_box(0);
v_resolvedId_1411_ = l_Lean_Name_replacePrefix(v_id_1407_, v___x_1409_, v___x_1410_);
lean_inc(v_resolvedId_1411_);
lean_inc_ref(v_env_1405_);
v___x_1412_ = l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(v_env_1405_, v_resolvedId_1411_);
if (v___x_1412_ == 0)
{
lean_object* v___x_1413_; 
v___x_1413_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName(v_env_1405_, v_opts_1406_, v_resolvedId_1411_);
return v___x_1413_;
}
else
{
lean_object* v___x_1414_; 
lean_dec_ref(v_env_1405_);
v___x_1414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1414_, 0, v_resolvedId_1411_);
return v___x_1414_;
}
}
else
{
lean_object* v___x_1415_; 
lean_dec(v_id_1407_);
lean_dec_ref(v_env_1405_);
v___x_1415_ = lean_box(0);
return v___x_1415_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveExact___boxed(lean_object* v_env_1416_, lean_object* v_opts_1417_, lean_object* v_id_1418_){
_start:
{
lean_object* v_res_1419_; 
v_res_1419_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveExact(v_env_1416_, v_opts_1417_, v_id_1418_);
lean_dec_ref(v_opts_1417_);
return v_res_1419_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveOpenDecls(lean_object* v_env_1420_, lean_object* v_opts_1421_, lean_object* v_id_1422_, lean_object* v_x_1423_, lean_object* v_x_1424_){
_start:
{
if (lean_obj_tag(v_x_1423_) == 0)
{
lean_dec(v_id_1422_);
lean_dec_ref(v_env_1420_);
return v_x_1424_;
}
else
{
lean_object* v_head_1425_; 
v_head_1425_ = lean_ctor_get(v_x_1423_, 0);
lean_inc(v_head_1425_);
if (lean_obj_tag(v_head_1425_) == 0)
{
lean_object* v_tail_1426_; lean_object* v_ns_1427_; lean_object* v_except_1428_; uint8_t v___x_1429_; 
v_tail_1426_ = lean_ctor_get(v_x_1423_, 1);
lean_inc(v_tail_1426_);
lean_dec_ref_known(v_x_1423_, 2);
v_ns_1427_ = lean_ctor_get(v_head_1425_, 0);
lean_inc(v_ns_1427_);
v_except_1428_ = lean_ctor_get(v_head_1425_, 1);
lean_inc(v_except_1428_);
lean_dec_ref_known(v_head_1425_, 2);
v___x_1429_ = l_List_elem___at___00Lean_addAliasEntry_spec__2(v_id_1422_, v_except_1428_);
lean_dec(v_except_1428_);
if (v___x_1429_ == 0)
{
lean_object* v_newResolvedIds_1430_; lean_object* v___x_1431_; 
lean_inc(v_id_1422_);
lean_inc_ref(v_env_1420_);
v_newResolvedIds_1430_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveQualifiedName(v_env_1420_, v_opts_1421_, v_ns_1427_, v_id_1422_);
v___x_1431_ = l_List_appendTR___redArg(v_newResolvedIds_1430_, v_x_1424_);
v_x_1423_ = v_tail_1426_;
v_x_1424_ = v___x_1431_;
goto _start;
}
else
{
lean_dec(v_ns_1427_);
v_x_1423_ = v_tail_1426_;
goto _start;
}
}
else
{
lean_object* v_tail_1434_; lean_object* v___x_1436_; uint8_t v_isShared_1437_; uint8_t v_isSharedCheck_1454_; 
v_tail_1434_ = lean_ctor_get(v_x_1423_, 1);
v_isSharedCheck_1454_ = !lean_is_exclusive(v_x_1423_);
if (v_isSharedCheck_1454_ == 0)
{
lean_object* v_unused_1455_; 
v_unused_1455_ = lean_ctor_get(v_x_1423_, 0);
lean_dec(v_unused_1455_);
v___x_1436_ = v_x_1423_;
v_isShared_1437_ = v_isSharedCheck_1454_;
goto v_resetjp_1435_;
}
else
{
lean_inc(v_tail_1434_);
lean_dec(v_x_1423_);
v___x_1436_ = lean_box(0);
v_isShared_1437_ = v_isSharedCheck_1454_;
goto v_resetjp_1435_;
}
v_resetjp_1435_:
{
lean_object* v_id_1438_; lean_object* v_declName_1439_; uint8_t v___x_1440_; 
v_id_1438_ = lean_ctor_get(v_head_1425_, 0);
lean_inc(v_id_1438_);
v_declName_1439_ = lean_ctor_get(v_head_1425_, 1);
lean_inc(v_declName_1439_);
lean_dec_ref_known(v_head_1425_, 2);
v___x_1440_ = lean_name_eq(v_id_1438_, v_id_1422_);
if (v___x_1440_ == 0)
{
uint8_t v___x_1441_; 
v___x_1441_ = l_Lean_Name_isPrefixOf(v_id_1438_, v_id_1422_);
if (v___x_1441_ == 0)
{
lean_dec(v_declName_1439_);
lean_dec(v_id_1438_);
lean_del_object(v___x_1436_);
v_x_1423_ = v_tail_1434_;
goto _start;
}
else
{
lean_object* v_candidate_1443_; uint8_t v___x_1444_; 
lean_inc(v_id_1422_);
v_candidate_1443_ = l_Lean_Name_replacePrefix(v_id_1422_, v_id_1438_, v_declName_1439_);
lean_dec(v_declName_1439_);
lean_dec(v_id_1438_);
lean_inc(v_candidate_1443_);
lean_inc_ref(v_env_1420_);
v___x_1444_ = l_Lean_Environment_contains(v_env_1420_, v_candidate_1443_, v___x_1441_);
if (v___x_1444_ == 0)
{
lean_dec(v_candidate_1443_);
lean_del_object(v___x_1436_);
v_x_1423_ = v_tail_1434_;
goto _start;
}
else
{
lean_object* v___x_1447_; 
if (v_isShared_1437_ == 0)
{
lean_ctor_set(v___x_1436_, 1, v_x_1424_);
lean_ctor_set(v___x_1436_, 0, v_candidate_1443_);
v___x_1447_ = v___x_1436_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v_candidate_1443_);
lean_ctor_set(v_reuseFailAlloc_1449_, 1, v_x_1424_);
v___x_1447_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
v_x_1423_ = v_tail_1434_;
v_x_1424_ = v___x_1447_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_1451_; 
lean_dec(v_id_1438_);
if (v_isShared_1437_ == 0)
{
lean_ctor_set(v___x_1436_, 1, v_x_1424_);
lean_ctor_set(v___x_1436_, 0, v_declName_1439_);
v___x_1451_ = v___x_1436_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v_declName_1439_);
lean_ctor_set(v_reuseFailAlloc_1453_, 1, v_x_1424_);
v___x_1451_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
v_x_1423_ = v_tail_1434_;
v_x_1424_ = v___x_1451_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveOpenDecls___boxed(lean_object* v_env_1456_, lean_object* v_opts_1457_, lean_object* v_id_1458_, lean_object* v_x_1459_, lean_object* v_x_1460_){
_start:
{
lean_object* v_res_1461_; 
v_res_1461_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveOpenDecls(v_env_1456_, v_opts_1457_, v_id_1458_, v_x_1459_, v_x_1460_);
lean_dec_ref(v_opts_1457_);
return v_res_1461_;
}
}
LEAN_EXPORT lean_object* l_List_eraseDups___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__0(lean_object* v_as_1463_){
_start:
{
lean_object* v___f_1464_; lean_object* v___x_1465_; 
v___f_1464_ = ((lean_object*)(l_List_eraseDups___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__0___closed__0));
v___x_1465_ = l_List_eraseDupsBy___redArg(v___f_1464_, v_as_1463_);
return v___x_1465_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__1(lean_object* v_projs_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_){
_start:
{
if (lean_obj_tag(v_a_1467_) == 0)
{
lean_object* v___x_1469_; 
lean_dec(v_projs_1466_);
v___x_1469_ = l_List_reverse___redArg(v_a_1468_);
return v___x_1469_;
}
else
{
lean_object* v_head_1470_; lean_object* v_tail_1471_; lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1480_; 
v_head_1470_ = lean_ctor_get(v_a_1467_, 0);
v_tail_1471_ = lean_ctor_get(v_a_1467_, 1);
v_isSharedCheck_1480_ = !lean_is_exclusive(v_a_1467_);
if (v_isSharedCheck_1480_ == 0)
{
v___x_1473_ = v_a_1467_;
v_isShared_1474_ = v_isSharedCheck_1480_;
goto v_resetjp_1472_;
}
else
{
lean_inc(v_tail_1471_);
lean_inc(v_head_1470_);
lean_dec(v_a_1467_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1480_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
lean_object* v___x_1475_; lean_object* v___x_1477_; 
lean_inc(v_projs_1466_);
v___x_1475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1475_, 0, v_head_1470_);
lean_ctor_set(v___x_1475_, 1, v_projs_1466_);
if (v_isShared_1474_ == 0)
{
lean_ctor_set(v___x_1473_, 1, v_a_1468_);
lean_ctor_set(v___x_1473_, 0, v___x_1475_);
v___x_1477_ = v___x_1473_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v___x_1475_);
lean_ctor_set(v_reuseFailAlloc_1479_, 1, v_a_1468_);
v___x_1477_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
v_a_1467_ = v_tail_1471_;
v_a_1468_ = v___x_1477_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop(lean_object* v_env_1481_, lean_object* v_opts_1482_, lean_object* v_ns_1483_, lean_object* v_openDecls_1484_, lean_object* v_extractionResult_1485_, lean_object* v_id_1486_, lean_object* v_projs_1487_){
_start:
{
if (lean_obj_tag(v_id_1486_) == 1)
{
lean_object* v_pre_1488_; lean_object* v_str_1489_; lean_object* v_imported_1490_; lean_object* v_ctx_1491_; lean_object* v_scopes_1492_; lean_object* v___x_1493_; lean_object* v_id_1494_; lean_object* v___y_1496_; lean_object* v___x_1506_; lean_object* v___y_1508_; 
v_pre_1488_ = lean_ctor_get(v_id_1486_, 0);
lean_inc(v_pre_1488_);
v_str_1489_ = lean_ctor_get(v_id_1486_, 1);
lean_inc_ref(v_str_1489_);
v_imported_1490_ = lean_ctor_get(v_extractionResult_1485_, 1);
v_ctx_1491_ = lean_ctor_get(v_extractionResult_1485_, 2);
v_scopes_1492_ = lean_ctor_get(v_extractionResult_1485_, 3);
lean_inc(v_scopes_1492_);
lean_inc(v_ctx_1491_);
lean_inc(v_imported_1490_);
v___x_1493_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1493_, 0, v_id_1486_);
lean_ctor_set(v___x_1493_, 1, v_imported_1490_);
lean_ctor_set(v___x_1493_, 2, v_ctx_1491_);
lean_ctor_set(v___x_1493_, 3, v_scopes_1492_);
v_id_1494_ = l_Lean_MacroScopesView_review(v___x_1493_);
lean_inc(v_ns_1483_);
lean_inc(v_id_1494_);
lean_inc_ref(v_env_1481_);
v___x_1506_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveUsingNamespace(v_env_1481_, v_opts_1482_, v_id_1494_, v_ns_1483_);
if (lean_obj_tag(v___x_1506_) == 0)
{
lean_object* v___x_1513_; 
lean_inc(v_id_1494_);
lean_inc_ref(v_env_1481_);
v___x_1513_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveExact(v_env_1481_, v_opts_1482_, v_id_1494_);
if (lean_obj_tag(v___x_1513_) == 0)
{
uint8_t v___x_1514_; 
lean_inc(v_id_1494_);
lean_inc_ref(v_env_1481_);
v___x_1514_ = l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(v_env_1481_, v_id_1494_);
if (v___x_1514_ == 0)
{
v___y_1508_ = v___x_1506_;
goto v___jp_1507_;
}
else
{
lean_object* v___x_1515_; 
lean_inc(v_id_1494_);
v___x_1515_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1515_, 0, v_id_1494_);
lean_ctor_set(v___x_1515_, 1, v___x_1506_);
v___y_1508_ = v___x_1515_;
goto v___jp_1507_;
}
}
else
{
lean_object* v_val_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; 
lean_dec(v_id_1494_);
lean_dec_ref(v_str_1489_);
lean_dec(v_pre_1488_);
lean_dec(v_openDecls_1484_);
lean_dec(v_ns_1483_);
lean_dec_ref(v_env_1481_);
v_val_1516_ = lean_ctor_get(v___x_1513_, 0);
lean_inc(v_val_1516_);
lean_dec_ref_known(v___x_1513_, 1);
v___x_1517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1517_, 0, v_val_1516_);
lean_ctor_set(v___x_1517_, 1, v_projs_1487_);
v___x_1518_ = lean_box(0);
v___x_1519_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1519_, 0, v___x_1517_);
lean_ctor_set(v___x_1519_, 1, v___x_1518_);
return v___x_1519_;
}
}
else
{
lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; 
lean_dec(v_id_1494_);
lean_dec_ref(v_str_1489_);
lean_dec(v_pre_1488_);
lean_dec(v_openDecls_1484_);
lean_dec(v_ns_1483_);
lean_dec_ref(v_env_1481_);
v___x_1520_ = l_List_eraseDups___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__0(v___x_1506_);
v___x_1521_ = lean_box(0);
v___x_1522_ = l_List_mapTR_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__1(v_projs_1487_, v___x_1520_, v___x_1521_);
return v___x_1522_;
}
v___jp_1495_:
{
lean_object* v_resolvedIds_1497_; uint8_t v___x_1498_; lean_object* v___x_1499_; lean_object* v_resolvedIds_1500_; 
lean_inc(v_openDecls_1484_);
lean_inc(v_id_1494_);
lean_inc_ref_n(v_env_1481_, 2);
v_resolvedIds_1497_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveOpenDecls(v_env_1481_, v_opts_1482_, v_id_1494_, v_openDecls_1484_, v___y_1496_);
v___x_1498_ = l_Lean_Name_isAtomic(v_id_1494_);
v___x_1499_ = l_Lean_getAliases(v_env_1481_, v_id_1494_, v___x_1498_);
lean_dec(v_id_1494_);
v_resolvedIds_1500_ = l_List_appendTR___redArg(v___x_1499_, v_resolvedIds_1497_);
if (lean_obj_tag(v_resolvedIds_1500_) == 0)
{
lean_object* v___x_1501_; 
v___x_1501_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1501_, 0, v_str_1489_);
lean_ctor_set(v___x_1501_, 1, v_projs_1487_);
v_id_1486_ = v_pre_1488_;
v_projs_1487_ = v___x_1501_;
goto _start;
}
else
{
lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; 
lean_dec_ref(v_str_1489_);
lean_dec(v_pre_1488_);
lean_dec(v_openDecls_1484_);
lean_dec(v_ns_1483_);
lean_dec_ref(v_env_1481_);
v___x_1503_ = l_List_eraseDups___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__0(v_resolvedIds_1500_);
v___x_1504_ = lean_box(0);
v___x_1505_ = l_List_mapTR_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__1(v_projs_1487_, v___x_1503_, v___x_1504_);
return v___x_1505_;
}
}
v___jp_1507_:
{
lean_object* v___x_1509_; 
lean_inc(v_id_1494_);
lean_inc_ref(v_env_1481_);
v___x_1509_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName(v_env_1481_, v_opts_1482_, v_id_1494_);
if (lean_obj_tag(v___x_1509_) == 1)
{
lean_object* v_val_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; 
v_val_1510_ = lean_ctor_get(v___x_1509_, 0);
lean_inc(v_val_1510_);
lean_dec_ref_known(v___x_1509_, 1);
v___x_1511_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1511_, 0, v_val_1510_);
lean_ctor_set(v___x_1511_, 1, v___x_1506_);
v___x_1512_ = l_List_appendTR___redArg(v___x_1511_, v___y_1508_);
v___y_1496_ = v___x_1512_;
goto v___jp_1495_;
}
else
{
lean_dec(v___x_1509_);
lean_dec(v___x_1506_);
v___y_1496_ = v___y_1508_;
goto v___jp_1495_;
}
}
}
else
{
lean_object* v___x_1523_; 
lean_dec(v_projs_1487_);
lean_dec(v_id_1486_);
lean_dec(v_openDecls_1484_);
lean_dec(v_ns_1483_);
lean_dec_ref(v_env_1481_);
v___x_1523_ = lean_box(0);
return v___x_1523_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop___boxed(lean_object* v_env_1524_, lean_object* v_opts_1525_, lean_object* v_ns_1526_, lean_object* v_openDecls_1527_, lean_object* v_extractionResult_1528_, lean_object* v_id_1529_, lean_object* v_projs_1530_){
_start:
{
lean_object* v_res_1531_; 
v_res_1531_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop(v_env_1524_, v_opts_1525_, v_ns_1526_, v_openDecls_1527_, v_extractionResult_1528_, v_id_1529_, v_projs_1530_);
lean_dec_ref(v_extractionResult_1528_);
lean_dec_ref(v_opts_1525_);
return v_res_1531_;
}
}
LEAN_EXPORT lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object* v_env_1532_, lean_object* v_opts_1533_, lean_object* v_ns_1534_, lean_object* v_openDecls_1535_, lean_object* v_id_1536_){
_start:
{
lean_object* v_extractionResult_1537_; lean_object* v_name_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; 
v_extractionResult_1537_ = l_Lean_extractMacroScopes(v_id_1536_);
v_name_1538_ = lean_ctor_get(v_extractionResult_1537_, 0);
lean_inc(v_name_1538_);
v___x_1539_ = lean_box(0);
v___x_1540_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop(v_env_1532_, v_opts_1533_, v_ns_1534_, v_openDecls_1535_, v_extractionResult_1537_, v_name_1538_, v___x_1539_);
lean_dec_ref(v_extractionResult_1537_);
return v___x_1540_;
}
}
LEAN_EXPORT lean_object* l_Lean_ResolveName_resolveGlobalName___boxed(lean_object* v_env_1541_, lean_object* v_opts_1542_, lean_object* v_ns_1543_, lean_object* v_openDecls_1544_, lean_object* v_id_1545_){
_start:
{
lean_object* v_res_1546_; 
v_res_1546_ = l_Lean_ResolveName_resolveGlobalName(v_env_1541_, v_opts_1542_, v_ns_1543_, v_openDecls_1544_, v_id_1545_);
lean_dec_ref(v_opts_1542_);
return v_res_1546_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_ResolveName_resolveNamespaceUsingScope_x3f_spec__0(lean_object* v_msg_1547_){
_start:
{
lean_object* v___x_1548_; lean_object* v___x_1549_; 
v___x_1548_ = lean_box(0);
v___x_1549_ = lean_panic_fn_borrowed(v___x_1548_, v_msg_1547_);
return v___x_1549_;
}
}
static lean_object* _init_l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__3(void){
_start:
{
lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; 
v___x_1553_ = ((lean_object*)(l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__2));
v___x_1554_ = lean_unsigned_to_nat(9u);
v___x_1555_ = lean_unsigned_to_nat(230u);
v___x_1556_ = ((lean_object*)(l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__1));
v___x_1557_ = ((lean_object*)(l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__0));
v___x_1558_ = l_mkPanicMessageWithDecl(v___x_1557_, v___x_1556_, v___x_1555_, v___x_1554_, v___x_1553_);
return v___x_1558_;
}
}
LEAN_EXPORT lean_object* l_Lean_ResolveName_resolveNamespaceUsingScope_x3f(lean_object* v_env_1559_, lean_object* v_n_1560_, lean_object* v_ns_1561_){
_start:
{
switch(lean_obj_tag(v_ns_1561_))
{
case 1:
{
lean_object* v_pre_1562_; lean_object* v___x_1563_; uint8_t v___x_1564_; 
v_pre_1562_ = lean_ctor_get(v_ns_1561_, 0);
lean_inc(v_pre_1562_);
lean_inc(v_n_1560_);
v___x_1563_ = l_Lean_Name_append(v_ns_1561_, v_n_1560_);
lean_inc_ref(v_env_1559_);
v___x_1564_ = l_Lean_Environment_isNamespace(v_env_1559_, v___x_1563_);
if (v___x_1564_ == 0)
{
lean_dec(v___x_1563_);
v_ns_1561_ = v_pre_1562_;
goto _start;
}
else
{
lean_object* v___x_1566_; 
lean_dec(v_pre_1562_);
lean_dec(v_n_1560_);
lean_dec_ref(v_env_1559_);
v___x_1566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1566_, 0, v___x_1563_);
return v___x_1566_;
}
}
case 0:
{
lean_object* v___x_1567_; lean_object* v_n_1568_; uint8_t v___x_1569_; 
v___x_1567_ = l_Lean_rootNamespace;
v_n_1568_ = l_Lean_Name_replacePrefix(v_n_1560_, v___x_1567_, v_ns_1561_);
v___x_1569_ = l_Lean_Environment_isNamespace(v_env_1559_, v_n_1568_);
if (v___x_1569_ == 0)
{
lean_object* v___x_1570_; 
lean_dec(v_n_1568_);
v___x_1570_ = lean_box(0);
return v___x_1570_;
}
else
{
lean_object* v___x_1571_; 
v___x_1571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1571_, 0, v_n_1568_);
return v___x_1571_;
}
}
default: 
{
lean_object* v___x_1572_; lean_object* v___x_1573_; 
lean_dec(v_ns_1561_);
lean_dec(v_n_1560_);
lean_dec_ref(v_env_1559_);
v___x_1572_ = lean_obj_once(&l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__3, &l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__3_once, _init_l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__3);
v___x_1573_ = l_panic___at___00Lean_ResolveName_resolveNamespaceUsingScope_x3f_spec__0(v___x_1572_);
return v___x_1573_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ResolveName_resolveNamespaceUsingOpenDecls(lean_object* v_env_1574_, lean_object* v_n_1575_, lean_object* v_x_1576_){
_start:
{
if (lean_obj_tag(v_x_1576_) == 0)
{
lean_object* v___x_1577_; 
lean_dec(v_n_1575_);
lean_dec_ref(v_env_1574_);
v___x_1577_ = lean_box(0);
return v___x_1577_;
}
else
{
lean_object* v_head_1578_; 
v_head_1578_ = lean_ctor_get(v_x_1576_, 0);
if (lean_obj_tag(v_head_1578_) == 0)
{
lean_object* v_tail_1579_; lean_object* v___x_1581_; uint8_t v_isShared_1582_; uint8_t v_isSharedCheck_1596_; 
lean_inc_ref(v_head_1578_);
v_tail_1579_ = lean_ctor_get(v_x_1576_, 1);
v_isSharedCheck_1596_ = !lean_is_exclusive(v_x_1576_);
if (v_isSharedCheck_1596_ == 0)
{
lean_object* v_unused_1597_; 
v_unused_1597_ = lean_ctor_get(v_x_1576_, 0);
lean_dec(v_unused_1597_);
v___x_1581_ = v_x_1576_;
v_isShared_1582_ = v_isSharedCheck_1596_;
goto v_resetjp_1580_;
}
else
{
lean_inc(v_tail_1579_);
lean_dec(v_x_1576_);
v___x_1581_ = lean_box(0);
v_isShared_1582_ = v_isSharedCheck_1596_;
goto v_resetjp_1580_;
}
v_resetjp_1580_:
{
lean_object* v_ns_1583_; lean_object* v_except_1584_; lean_object* v___x_1585_; uint8_t v___y_1587_; uint8_t v___x_1593_; 
v_ns_1583_ = lean_ctor_get(v_head_1578_, 0);
lean_inc(v_ns_1583_);
v_except_1584_ = lean_ctor_get(v_head_1578_, 1);
lean_inc(v_except_1584_);
lean_dec_ref_known(v_head_1578_, 2);
lean_inc(v_n_1575_);
v___x_1585_ = l_Lean_Name_append(v_ns_1583_, v_n_1575_);
lean_inc_ref(v_env_1574_);
v___x_1593_ = l_Lean_Environment_isNamespace(v_env_1574_, v___x_1585_);
if (v___x_1593_ == 0)
{
lean_dec(v_except_1584_);
v___y_1587_ = v___x_1593_;
goto v___jp_1586_;
}
else
{
uint8_t v___x_1594_; uint8_t v___x_1595_; 
v___x_1594_ = l_List_elem___at___00Lean_addAliasEntry_spec__2(v_n_1575_, v_except_1584_);
lean_dec(v_except_1584_);
v___x_1595_ = lean_bool_not(v___x_1594_);
v___y_1587_ = v___x_1595_;
goto v___jp_1586_;
}
v___jp_1586_:
{
if (v___y_1587_ == 0)
{
lean_dec(v___x_1585_);
lean_del_object(v___x_1581_);
v_x_1576_ = v_tail_1579_;
goto _start;
}
else
{
lean_object* v___x_1589_; lean_object* v___x_1591_; 
v___x_1589_ = l_Lean_ResolveName_resolveNamespaceUsingOpenDecls(v_env_1574_, v_n_1575_, v_tail_1579_);
if (v_isShared_1582_ == 0)
{
lean_ctor_set(v___x_1581_, 1, v___x_1589_);
lean_ctor_set(v___x_1581_, 0, v___x_1585_);
v___x_1591_ = v___x_1581_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1592_; 
v_reuseFailAlloc_1592_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1592_, 0, v___x_1585_);
lean_ctor_set(v_reuseFailAlloc_1592_, 1, v___x_1589_);
v___x_1591_ = v_reuseFailAlloc_1592_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
return v___x_1591_;
}
}
}
}
}
else
{
lean_object* v_tail_1598_; 
v_tail_1598_ = lean_ctor_get(v_x_1576_, 1);
lean_inc(v_tail_1598_);
lean_dec_ref_known(v_x_1576_, 2);
v_x_1576_ = v_tail_1598_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ResolveName_resolveNamespace(lean_object* v_env_1600_, lean_object* v_ns_1601_, lean_object* v_openDecls_1602_, lean_object* v_id_1603_){
_start:
{
lean_object* v___x_1604_; 
lean_inc(v_id_1603_);
lean_inc_ref(v_env_1600_);
v___x_1604_ = l_Lean_ResolveName_resolveNamespaceUsingScope_x3f(v_env_1600_, v_id_1603_, v_ns_1601_);
if (lean_obj_tag(v___x_1604_) == 0)
{
lean_object* v___x_1605_; 
v___x_1605_ = l_Lean_ResolveName_resolveNamespaceUsingOpenDecls(v_env_1600_, v_id_1603_, v_openDecls_1602_);
return v___x_1605_;
}
else
{
lean_object* v_val_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; 
v_val_1606_ = lean_ctor_get(v___x_1604_, 0);
lean_inc(v_val_1606_);
lean_dec_ref_known(v___x_1604_, 1);
v___x_1607_ = l_Lean_ResolveName_resolveNamespaceUsingOpenDecls(v_env_1600_, v_id_1603_, v_openDecls_1602_);
v___x_1608_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1608_, 0, v_val_1606_);
lean_ctor_set(v___x_1608_, 1, v___x_1607_);
return v___x_1608_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadResolveNameOfMonadLift___redArg(lean_object* v_inst_1609_, lean_object* v_inst_1610_){
_start:
{
lean_object* v_getCurrNamespace_1611_; lean_object* v_getOpenDecls_1612_; lean_object* v___x_1614_; uint8_t v_isShared_1615_; uint8_t v_isSharedCheck_1621_; 
v_getCurrNamespace_1611_ = lean_ctor_get(v_inst_1610_, 0);
v_getOpenDecls_1612_ = lean_ctor_get(v_inst_1610_, 1);
v_isSharedCheck_1621_ = !lean_is_exclusive(v_inst_1610_);
if (v_isSharedCheck_1621_ == 0)
{
v___x_1614_ = v_inst_1610_;
v_isShared_1615_ = v_isSharedCheck_1621_;
goto v_resetjp_1613_;
}
else
{
lean_inc(v_getOpenDecls_1612_);
lean_inc(v_getCurrNamespace_1611_);
lean_dec(v_inst_1610_);
v___x_1614_ = lean_box(0);
v_isShared_1615_ = v_isSharedCheck_1621_;
goto v_resetjp_1613_;
}
v_resetjp_1613_:
{
lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1619_; 
lean_inc(v_inst_1609_);
v___x_1616_ = lean_apply_2(v_inst_1609_, lean_box(0), v_getCurrNamespace_1611_);
v___x_1617_ = lean_apply_2(v_inst_1609_, lean_box(0), v_getOpenDecls_1612_);
if (v_isShared_1615_ == 0)
{
lean_ctor_set(v___x_1614_, 1, v___x_1617_);
lean_ctor_set(v___x_1614_, 0, v___x_1616_);
v___x_1619_ = v___x_1614_;
goto v_reusejp_1618_;
}
else
{
lean_object* v_reuseFailAlloc_1620_; 
v_reuseFailAlloc_1620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1620_, 0, v___x_1616_);
lean_ctor_set(v_reuseFailAlloc_1620_, 1, v___x_1617_);
v___x_1619_ = v_reuseFailAlloc_1620_;
goto v_reusejp_1618_;
}
v_reusejp_1618_:
{
return v___x_1619_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadResolveNameOfMonadLift(lean_object* v_m_1622_, lean_object* v_n_1623_, lean_object* v_inst_1624_, lean_object* v_inst_1625_){
_start:
{
lean_object* v___x_1626_; 
v___x_1626_ = l_Lean_instMonadResolveNameOfMonadLift___redArg(v_inst_1624_, v_inst_1625_);
return v___x_1626_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1628_; lean_object* v___x_1629_; 
v___x_1628_ = ((lean_object*)(l_Lean_checkPrivateInPublic___redArg___lam__0___closed__0));
v___x_1629_ = l_Lean_stringToMessageData(v___x_1628_);
return v___x_1629_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1631_; lean_object* v___x_1632_; 
v___x_1631_ = ((lean_object*)(l_Lean_checkPrivateInPublic___redArg___lam__0___closed__2));
v___x_1632_ = l_Lean_stringToMessageData(v___x_1631_);
return v___x_1632_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___redArg___lam__0(lean_object* v_____do__lift_1633_, lean_object* v_toApplicative_1634_, lean_object* v_id_1635_, lean_object* v_inst_1636_, lean_object* v_inst_1637_, lean_object* v_inst_1638_, lean_object* v_inst_1639_, uint8_t v_____do__lift_1640_){
_start:
{
uint8_t v_isExporting_1645_; 
v_isExporting_1645_ = lean_ctor_get_uint8(v_____do__lift_1633_, sizeof(void*)*8);
if (v_isExporting_1645_ == 0)
{
lean_dec(v_inst_1639_);
lean_dec(v_inst_1638_);
lean_dec_ref(v_inst_1637_);
lean_dec_ref(v_inst_1636_);
lean_dec(v_id_1635_);
goto v___jp_1641_;
}
else
{
uint8_t v___x_1646_; 
v___x_1646_ = l_Lean_isPrivateName(v_id_1635_);
if (v___x_1646_ == 0)
{
lean_dec(v_inst_1639_);
lean_dec(v_inst_1638_);
lean_dec_ref(v_inst_1637_);
lean_dec_ref(v_inst_1636_);
lean_dec(v_id_1635_);
goto v___jp_1641_;
}
else
{
if (v_____do__lift_1640_ == 0)
{
lean_dec(v_inst_1639_);
lean_dec(v_inst_1638_);
lean_dec_ref(v_inst_1637_);
lean_dec_ref(v_inst_1636_);
lean_dec(v_id_1635_);
goto v___jp_1641_;
}
else
{
lean_object* v___x_1647_; uint8_t v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; 
lean_dec_ref(v_toApplicative_1634_);
v___x_1647_ = lean_obj_once(&l_Lean_checkPrivateInPublic___redArg___lam__0___closed__1, &l_Lean_checkPrivateInPublic___redArg___lam__0___closed__1_once, _init_l_Lean_checkPrivateInPublic___redArg___lam__0___closed__1);
v___x_1648_ = 0;
v___x_1649_ = l_Lean_MessageData_ofConstName(v_id_1635_, v___x_1648_);
v___x_1650_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1650_, 0, v___x_1647_);
lean_ctor_set(v___x_1650_, 1, v___x_1649_);
v___x_1651_ = lean_obj_once(&l_Lean_checkPrivateInPublic___redArg___lam__0___closed__3, &l_Lean_checkPrivateInPublic___redArg___lam__0___closed__3_once, _init_l_Lean_checkPrivateInPublic___redArg___lam__0___closed__3);
v___x_1652_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1652_, 0, v___x_1650_);
lean_ctor_set(v___x_1652_, 1, v___x_1651_);
v___x_1653_ = l_Lean_logWarning___redArg(v_inst_1636_, v_inst_1637_, v_inst_1638_, v_inst_1639_, v___x_1652_);
return v___x_1653_;
}
}
}
v___jp_1641_:
{
lean_object* v_toPure_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; 
v_toPure_1642_ = lean_ctor_get(v_toApplicative_1634_, 1);
lean_inc(v_toPure_1642_);
lean_dec_ref(v_toApplicative_1634_);
v___x_1643_ = lean_box(0);
v___x_1644_ = lean_apply_2(v_toPure_1642_, lean_box(0), v___x_1643_);
return v___x_1644_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___redArg___lam__0___boxed(lean_object* v_____do__lift_1654_, lean_object* v_toApplicative_1655_, lean_object* v_id_1656_, lean_object* v_inst_1657_, lean_object* v_inst_1658_, lean_object* v_inst_1659_, lean_object* v_inst_1660_, lean_object* v_____do__lift_1661_){
_start:
{
uint8_t v_____do__lift_231__boxed_1662_; lean_object* v_res_1663_; 
v_____do__lift_231__boxed_1662_ = lean_unbox(v_____do__lift_1661_);
v_res_1663_ = l_Lean_checkPrivateInPublic___redArg___lam__0(v_____do__lift_1654_, v_toApplicative_1655_, v_id_1656_, v_inst_1657_, v_inst_1658_, v_inst_1659_, v_inst_1660_, v_____do__lift_231__boxed_1662_);
lean_dec_ref(v_____do__lift_1654_);
return v_res_1663_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___redArg___lam__1(lean_object* v_toApplicative_1664_, lean_object* v_id_1665_, lean_object* v_inst_1666_, lean_object* v_inst_1667_, lean_object* v_inst_1668_, lean_object* v_inst_1669_, lean_object* v___x_1670_, lean_object* v_toBind_1671_, lean_object* v_____do__lift_1672_){
_start:
{
lean_object* v___f_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; 
lean_inc(v_inst_1669_);
lean_inc_ref(v_inst_1666_);
v___f_1673_ = lean_alloc_closure((void*)(l_Lean_checkPrivateInPublic___redArg___lam__0___boxed), 8, 7);
lean_closure_set(v___f_1673_, 0, v_____do__lift_1672_);
lean_closure_set(v___f_1673_, 1, v_toApplicative_1664_);
lean_closure_set(v___f_1673_, 2, v_id_1665_);
lean_closure_set(v___f_1673_, 3, v_inst_1666_);
lean_closure_set(v___f_1673_, 4, v_inst_1667_);
lean_closure_set(v___f_1673_, 5, v_inst_1668_);
lean_closure_set(v___f_1673_, 6, v_inst_1669_);
v___x_1674_ = l_Lean_ResolveName_backward_privateInPublic_warn;
v___x_1675_ = l_Lean_Option_getM___redArg(v_inst_1666_, v_inst_1669_, v___x_1670_, v___x_1674_);
v___x_1676_ = lean_apply_4(v_toBind_1671_, lean_box(0), lean_box(0), v___x_1675_, v___f_1673_);
return v___x_1676_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___redArg(lean_object* v_inst_1677_, lean_object* v_inst_1678_, lean_object* v_inst_1679_, lean_object* v_inst_1680_, lean_object* v_inst_1681_, lean_object* v_id_1682_){
_start:
{
lean_object* v___x_1683_; lean_object* v_toApplicative_1684_; lean_object* v_toBind_1685_; lean_object* v_getEnv_1686_; lean_object* v___f_1687_; lean_object* v___x_1688_; 
v___x_1683_ = l_Lean_KVMap_instValueBool;
v_toApplicative_1684_ = lean_ctor_get(v_inst_1677_, 0);
lean_inc_ref(v_toApplicative_1684_);
v_toBind_1685_ = lean_ctor_get(v_inst_1677_, 1);
lean_inc_n(v_toBind_1685_, 2);
v_getEnv_1686_ = lean_ctor_get(v_inst_1678_, 0);
lean_inc(v_getEnv_1686_);
lean_dec_ref(v_inst_1678_);
v___f_1687_ = lean_alloc_closure((void*)(l_Lean_checkPrivateInPublic___redArg___lam__1), 9, 8);
lean_closure_set(v___f_1687_, 0, v_toApplicative_1684_);
lean_closure_set(v___f_1687_, 1, v_id_1682_);
lean_closure_set(v___f_1687_, 2, v_inst_1677_);
lean_closure_set(v___f_1687_, 3, v_inst_1680_);
lean_closure_set(v___f_1687_, 4, v_inst_1681_);
lean_closure_set(v___f_1687_, 5, v_inst_1679_);
lean_closure_set(v___f_1687_, 6, v___x_1683_);
lean_closure_set(v___f_1687_, 7, v_toBind_1685_);
v___x_1688_ = lean_apply_4(v_toBind_1685_, lean_box(0), lean_box(0), v_getEnv_1686_, v___f_1687_);
return v___x_1688_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic(lean_object* v_m_1689_, lean_object* v_inst_1690_, lean_object* v_inst_1691_, lean_object* v_inst_1692_, lean_object* v_inst_1693_, lean_object* v_inst_1694_, lean_object* v_id_1695_){
_start:
{
lean_object* v___x_1696_; 
v___x_1696_ = l_Lean_checkPrivateInPublic___redArg(v_inst_1690_, v_inst_1691_, v_inst_1692_, v_inst_1693_, v_inst_1694_, v_id_1695_);
return v___x_1696_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg___lam__0(lean_object* v_env_1697_, lean_object* v_n_1698_, lean_object* v_toApplicative_1699_, uint8_t v___y_1700_, uint8_t v___x_1701_, lean_object* v_____r_1702_){
_start:
{
lean_object* v___x_1703_; 
v___x_1703_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1697_, v_n_1698_);
if (lean_obj_tag(v___x_1703_) == 0)
{
lean_object* v_toPure_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; 
v_toPure_1704_ = lean_ctor_get(v_toApplicative_1699_, 1);
lean_inc(v_toPure_1704_);
lean_dec_ref(v_toApplicative_1699_);
v___x_1705_ = lean_box(v___y_1700_);
v___x_1706_ = lean_apply_2(v_toPure_1704_, lean_box(0), v___x_1705_);
return v___x_1706_;
}
else
{
lean_object* v_val_1707_; lean_object* v_toPure_1708_; lean_object* v___x_1709_; uint8_t v_isModule_1710_; lean_object* v_modules_1711_; uint8_t v___x_1712_; 
v_val_1707_ = lean_ctor_get(v___x_1703_, 0);
lean_inc(v_val_1707_);
lean_dec_ref_known(v___x_1703_, 1);
v_toPure_1708_ = lean_ctor_get(v_toApplicative_1699_, 1);
lean_inc(v_toPure_1708_);
lean_dec_ref(v_toApplicative_1699_);
v___x_1709_ = l_Lean_Environment_header(v_env_1697_);
v_isModule_1710_ = lean_ctor_get_uint8(v___x_1709_, sizeof(void*)*7 + 4);
v_modules_1711_ = lean_ctor_get(v___x_1709_, 3);
lean_inc_ref(v_modules_1711_);
lean_dec_ref(v___x_1709_);
v___x_1712_ = lean_bool_not(v_isModule_1710_);
if (v___x_1712_ == 0)
{
lean_object* v___x_1713_; uint8_t v___x_1714_; 
v___x_1713_ = lean_array_get_size(v_modules_1711_);
v___x_1714_ = lean_nat_dec_lt(v_val_1707_, v___x_1713_);
if (v___x_1714_ == 0)
{
uint8_t v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; 
lean_dec_ref(v_modules_1711_);
lean_dec(v_val_1707_);
v___x_1715_ = lean_bool_not(v___x_1712_);
v___x_1716_ = lean_box(v___x_1715_);
v___x_1717_ = lean_apply_2(v_toPure_1708_, lean_box(0), v___x_1716_);
return v___x_1717_;
}
else
{
lean_object* v___x_1718_; lean_object* v_toImport_1719_; uint8_t v_importAll_1720_; uint8_t v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; 
v___x_1718_ = lean_array_fget(v_modules_1711_, v_val_1707_);
lean_dec(v_val_1707_);
lean_dec_ref(v_modules_1711_);
v_toImport_1719_ = lean_ctor_get(v___x_1718_, 0);
lean_inc_ref(v_toImport_1719_);
lean_dec(v___x_1718_);
v_importAll_1720_ = lean_ctor_get_uint8(v_toImport_1719_, sizeof(void*)*1);
lean_dec_ref(v_toImport_1719_);
v___x_1721_ = lean_bool_not(v_importAll_1720_);
v___x_1722_ = lean_box(v___x_1721_);
v___x_1723_ = lean_apply_2(v_toPure_1708_, lean_box(0), v___x_1722_);
return v___x_1723_;
}
}
else
{
lean_object* v___x_1724_; lean_object* v___x_1725_; 
lean_dec_ref(v_modules_1711_);
lean_dec(v_val_1707_);
v___x_1724_ = lean_box(v___x_1701_);
v___x_1725_ = lean_apply_2(v_toPure_1708_, lean_box(0), v___x_1724_);
return v___x_1725_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg___lam__0___boxed(lean_object* v_env_1726_, lean_object* v_n_1727_, lean_object* v_toApplicative_1728_, lean_object* v___y_1729_, lean_object* v___x_1730_, lean_object* v_____r_1731_){
_start:
{
uint8_t v___y_567__boxed_1732_; uint8_t v___x_568__boxed_1733_; lean_object* v_res_1734_; 
v___y_567__boxed_1732_ = lean_unbox(v___y_1729_);
v___x_568__boxed_1733_ = lean_unbox(v___x_1730_);
v_res_1734_ = l_Lean_isInaccessiblePrivateName___redArg___lam__0(v_env_1726_, v_n_1727_, v_toApplicative_1728_, v___y_567__boxed_1732_, v___x_568__boxed_1733_, v_____r_1731_);
lean_dec(v_n_1727_);
lean_dec_ref(v_env_1726_);
return v_res_1734_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg___lam__1(lean_object* v_env_1735_, lean_object* v_n_1736_, lean_object* v_toApplicative_1737_, uint8_t v___x_1738_, lean_object* v_inst_1739_, lean_object* v_inst_1740_, lean_object* v_inst_1741_, lean_object* v_inst_1742_, lean_object* v_inst_1743_, lean_object* v_toBind_1744_, uint8_t v_____do__lift_1745_){
_start:
{
uint8_t v___y_1747_; uint8_t v_isExporting_1753_; 
v_isExporting_1753_ = lean_ctor_get_uint8(v_env_1735_, sizeof(void*)*8);
if (v_isExporting_1753_ == 0)
{
v___y_1747_ = v_isExporting_1753_;
goto v___jp_1746_;
}
else
{
uint8_t v___x_1754_; 
v___x_1754_ = lean_bool_not(v_____do__lift_1745_);
if (v___x_1754_ == 0)
{
v___y_1747_ = v___x_1754_;
goto v___jp_1746_;
}
else
{
lean_object* v_toPure_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; 
lean_dec(v_toBind_1744_);
lean_dec(v_inst_1743_);
lean_dec_ref(v_inst_1742_);
lean_dec(v_inst_1741_);
lean_dec_ref(v_inst_1740_);
lean_dec_ref(v_inst_1739_);
lean_dec(v_n_1736_);
lean_dec_ref(v_env_1735_);
v_toPure_1755_ = lean_ctor_get(v_toApplicative_1737_, 1);
lean_inc(v_toPure_1755_);
lean_dec_ref(v_toApplicative_1737_);
v___x_1756_ = lean_box(v___x_1738_);
v___x_1757_ = lean_apply_2(v_toPure_1755_, lean_box(0), v___x_1756_);
return v___x_1757_;
}
}
v___jp_1746_:
{
lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___f_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; 
v___x_1748_ = lean_box(v___y_1747_);
v___x_1749_ = lean_box(v___x_1738_);
lean_inc(v_n_1736_);
v___f_1750_ = lean_alloc_closure((void*)(l_Lean_isInaccessiblePrivateName___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1750_, 0, v_env_1735_);
lean_closure_set(v___f_1750_, 1, v_n_1736_);
lean_closure_set(v___f_1750_, 2, v_toApplicative_1737_);
lean_closure_set(v___f_1750_, 3, v___x_1748_);
lean_closure_set(v___f_1750_, 4, v___x_1749_);
v___x_1751_ = l_Lean_checkPrivateInPublic___redArg(v_inst_1739_, v_inst_1740_, v_inst_1741_, v_inst_1742_, v_inst_1743_, v_n_1736_);
v___x_1752_ = lean_apply_4(v_toBind_1744_, lean_box(0), lean_box(0), v___x_1751_, v___f_1750_);
return v___x_1752_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg___lam__1___boxed(lean_object* v_env_1758_, lean_object* v_n_1759_, lean_object* v_toApplicative_1760_, lean_object* v___x_1761_, lean_object* v_inst_1762_, lean_object* v_inst_1763_, lean_object* v_inst_1764_, lean_object* v_inst_1765_, lean_object* v_inst_1766_, lean_object* v_toBind_1767_, lean_object* v_____do__lift_1768_){
_start:
{
uint8_t v___x_610__boxed_1769_; uint8_t v_____do__lift_616__boxed_1770_; lean_object* v_res_1771_; 
v___x_610__boxed_1769_ = lean_unbox(v___x_1761_);
v_____do__lift_616__boxed_1770_ = lean_unbox(v_____do__lift_1768_);
v_res_1771_ = l_Lean_isInaccessiblePrivateName___redArg___lam__1(v_env_1758_, v_n_1759_, v_toApplicative_1760_, v___x_610__boxed_1769_, v_inst_1762_, v_inst_1763_, v_inst_1764_, v_inst_1765_, v_inst_1766_, v_toBind_1767_, v_____do__lift_616__boxed_1770_);
return v_res_1771_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg___lam__2(lean_object* v_n_1772_, lean_object* v_toApplicative_1773_, uint8_t v___x_1774_, lean_object* v_inst_1775_, lean_object* v_inst_1776_, lean_object* v_inst_1777_, lean_object* v_inst_1778_, lean_object* v_inst_1779_, lean_object* v_toBind_1780_, lean_object* v_env_1781_){
_start:
{
lean_object* v___x_1782_; lean_object* v___f_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; 
v___x_1782_ = lean_box(v___x_1774_);
lean_inc(v_toBind_1780_);
lean_inc(v_inst_1777_);
lean_inc_ref(v_inst_1775_);
v___f_1783_ = lean_alloc_closure((void*)(l_Lean_isInaccessiblePrivateName___redArg___lam__1___boxed), 11, 10);
lean_closure_set(v___f_1783_, 0, v_env_1781_);
lean_closure_set(v___f_1783_, 1, v_n_1772_);
lean_closure_set(v___f_1783_, 2, v_toApplicative_1773_);
lean_closure_set(v___f_1783_, 3, v___x_1782_);
lean_closure_set(v___f_1783_, 4, v_inst_1775_);
lean_closure_set(v___f_1783_, 5, v_inst_1776_);
lean_closure_set(v___f_1783_, 6, v_inst_1777_);
lean_closure_set(v___f_1783_, 7, v_inst_1778_);
lean_closure_set(v___f_1783_, 8, v_inst_1779_);
lean_closure_set(v___f_1783_, 9, v_toBind_1780_);
v___x_1784_ = l_Lean_KVMap_instValueBool;
v___x_1785_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_1786_ = l_Lean_Option_getM___redArg(v_inst_1775_, v_inst_1777_, v___x_1784_, v___x_1785_);
v___x_1787_ = lean_apply_4(v_toBind_1780_, lean_box(0), lean_box(0), v___x_1786_, v___f_1783_);
return v___x_1787_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg___lam__2___boxed(lean_object* v_n_1788_, lean_object* v_toApplicative_1789_, lean_object* v___x_1790_, lean_object* v_inst_1791_, lean_object* v_inst_1792_, lean_object* v_inst_1793_, lean_object* v_inst_1794_, lean_object* v_inst_1795_, lean_object* v_toBind_1796_, lean_object* v_env_1797_){
_start:
{
uint8_t v___x_651__boxed_1798_; lean_object* v_res_1799_; 
v___x_651__boxed_1798_ = lean_unbox(v___x_1790_);
v_res_1799_ = l_Lean_isInaccessiblePrivateName___redArg___lam__2(v_n_1788_, v_toApplicative_1789_, v___x_651__boxed_1798_, v_inst_1791_, v_inst_1792_, v_inst_1793_, v_inst_1794_, v_inst_1795_, v_toBind_1796_, v_env_1797_);
return v_res_1799_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg(lean_object* v_inst_1800_, lean_object* v_inst_1801_, lean_object* v_inst_1802_, lean_object* v_inst_1803_, lean_object* v_inst_1804_, lean_object* v_n_1805_){
_start:
{
uint8_t v___x_1806_; uint8_t v___x_1807_; 
v___x_1806_ = l_Lean_isPrivateName(v_n_1805_);
v___x_1807_ = lean_bool_not(v___x_1806_);
if (v___x_1807_ == 0)
{
lean_object* v_toApplicative_1808_; lean_object* v_toBind_1809_; lean_object* v_getEnv_1810_; uint8_t v___x_1811_; lean_object* v___x_1812_; lean_object* v___f_1813_; lean_object* v___x_1814_; 
v_toApplicative_1808_ = lean_ctor_get(v_inst_1802_, 0);
lean_inc_ref(v_toApplicative_1808_);
v_toBind_1809_ = lean_ctor_get(v_inst_1802_, 1);
lean_inc_n(v_toBind_1809_, 2);
v_getEnv_1810_ = lean_ctor_get(v_inst_1803_, 0);
lean_inc(v_getEnv_1810_);
v___x_1811_ = 1;
v___x_1812_ = lean_box(v___x_1811_);
v___f_1813_ = lean_alloc_closure((void*)(l_Lean_isInaccessiblePrivateName___redArg___lam__2___boxed), 10, 9);
lean_closure_set(v___f_1813_, 0, v_n_1805_);
lean_closure_set(v___f_1813_, 1, v_toApplicative_1808_);
lean_closure_set(v___f_1813_, 2, v___x_1812_);
lean_closure_set(v___f_1813_, 3, v_inst_1802_);
lean_closure_set(v___f_1813_, 4, v_inst_1803_);
lean_closure_set(v___f_1813_, 5, v_inst_1804_);
lean_closure_set(v___f_1813_, 6, v_inst_1800_);
lean_closure_set(v___f_1813_, 7, v_inst_1801_);
lean_closure_set(v___f_1813_, 8, v_toBind_1809_);
v___x_1814_ = lean_apply_4(v_toBind_1809_, lean_box(0), lean_box(0), v_getEnv_1810_, v___f_1813_);
return v___x_1814_;
}
else
{
lean_object* v_toApplicative_1815_; lean_object* v_toPure_1816_; uint8_t v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; 
lean_dec(v_n_1805_);
lean_dec(v_inst_1804_);
lean_dec_ref(v_inst_1803_);
lean_dec(v_inst_1801_);
lean_dec_ref(v_inst_1800_);
v_toApplicative_1815_ = lean_ctor_get(v_inst_1802_, 0);
lean_inc_ref(v_toApplicative_1815_);
lean_dec_ref(v_inst_1802_);
v_toPure_1816_ = lean_ctor_get(v_toApplicative_1815_, 1);
lean_inc(v_toPure_1816_);
lean_dec_ref(v_toApplicative_1815_);
v___x_1817_ = 0;
v___x_1818_ = lean_box(v___x_1817_);
v___x_1819_ = lean_apply_2(v_toPure_1816_, lean_box(0), v___x_1818_);
return v___x_1819_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName(lean_object* v_m_1820_, lean_object* v_inst_1821_, lean_object* v_inst_1822_, lean_object* v_inst_1823_, lean_object* v_inst_1824_, lean_object* v_inst_1825_, lean_object* v_n_1826_){
_start:
{
lean_object* v___x_1827_; 
v___x_1827_ = l_Lean_isInaccessiblePrivateName___redArg(v_inst_1821_, v_inst_1822_, v_inst_1823_, v_inst_1824_, v_inst_1825_, v_n_1826_);
return v___x_1827_;
}
}
LEAN_EXPORT uint8_t l_Lean_resolveGlobalName___redArg___lam__0(lean_object* v_x_1828_){
_start:
{
lean_object* v_fst_1829_; uint8_t v___x_1830_; 
v_fst_1829_ = lean_ctor_get(v_x_1828_, 0);
v___x_1830_ = l_Lean_isPrivateName(v_fst_1829_);
return v___x_1830_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__0___boxed(lean_object* v_x_1831_){
_start:
{
uint8_t v_res_1832_; lean_object* v_r_1833_; 
v_res_1832_ = l_Lean_resolveGlobalName___redArg___lam__0(v_x_1831_);
lean_dec_ref(v_x_1831_);
v_r_1833_ = lean_box(v_res_1832_);
return v_r_1833_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__1(lean_object* v_toPure_1834_, lean_object* v_res_1835_, lean_object* v_____r_1836_){
_start:
{
lean_object* v___x_1837_; 
v___x_1837_ = lean_apply_2(v_toPure_1834_, lean_box(0), v_res_1835_);
return v___x_1837_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__2(uint8_t v_enableLog_1838_, lean_object* v_toPure_1839_, lean_object* v_res_1840_, lean_object* v___f_1841_, lean_object* v_inst_1842_, lean_object* v_inst_1843_, lean_object* v_inst_1844_, lean_object* v_inst_1845_, lean_object* v_inst_1846_, lean_object* v_toBind_1847_, lean_object* v___f_1848_, lean_object* v_____do__lift_1849_){
_start:
{
if (v_enableLog_1838_ == 0)
{
lean_object* v___x_1850_; 
lean_dec(v___f_1848_);
lean_dec(v_toBind_1847_);
lean_dec(v_inst_1846_);
lean_dec_ref(v_inst_1845_);
lean_dec(v_inst_1844_);
lean_dec_ref(v_inst_1843_);
lean_dec_ref(v_inst_1842_);
lean_dec_ref(v___f_1841_);
v___x_1850_ = lean_apply_2(v_toPure_1839_, lean_box(0), v_res_1840_);
return v___x_1850_;
}
else
{
uint8_t v_isExporting_1851_; 
v_isExporting_1851_ = lean_ctor_get_uint8(v_____do__lift_1849_, sizeof(void*)*8);
if (v_isExporting_1851_ == 0)
{
lean_object* v___x_1852_; 
lean_dec(v___f_1848_);
lean_dec(v_toBind_1847_);
lean_dec(v_inst_1846_);
lean_dec_ref(v_inst_1845_);
lean_dec(v_inst_1844_);
lean_dec_ref(v_inst_1843_);
lean_dec_ref(v_inst_1842_);
lean_dec_ref(v___f_1841_);
v___x_1852_ = lean_apply_2(v_toPure_1839_, lean_box(0), v_res_1840_);
return v___x_1852_;
}
else
{
lean_object* v___x_1853_; 
lean_inc(v_res_1840_);
v___x_1853_ = l_List_find_x3f___redArg(v___f_1841_, v_res_1840_);
if (lean_obj_tag(v___x_1853_) == 1)
{
lean_object* v_val_1854_; lean_object* v_fst_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; 
lean_dec(v_res_1840_);
lean_dec(v_toPure_1839_);
v_val_1854_ = lean_ctor_get(v___x_1853_, 0);
lean_inc(v_val_1854_);
lean_dec_ref_known(v___x_1853_, 1);
v_fst_1855_ = lean_ctor_get(v_val_1854_, 0);
lean_inc(v_fst_1855_);
lean_dec(v_val_1854_);
v___x_1856_ = l_Lean_checkPrivateInPublic___redArg(v_inst_1842_, v_inst_1843_, v_inst_1844_, v_inst_1845_, v_inst_1846_, v_fst_1855_);
v___x_1857_ = lean_apply_4(v_toBind_1847_, lean_box(0), lean_box(0), v___x_1856_, v___f_1848_);
return v___x_1857_;
}
else
{
lean_object* v___x_1858_; 
lean_dec(v___x_1853_);
lean_dec(v___f_1848_);
lean_dec(v_toBind_1847_);
lean_dec(v_inst_1846_);
lean_dec_ref(v_inst_1845_);
lean_dec(v_inst_1844_);
lean_dec_ref(v_inst_1843_);
lean_dec_ref(v_inst_1842_);
v___x_1858_ = lean_apply_2(v_toPure_1839_, lean_box(0), v_res_1840_);
return v___x_1858_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__2___boxed(lean_object* v_enableLog_1859_, lean_object* v_toPure_1860_, lean_object* v_res_1861_, lean_object* v___f_1862_, lean_object* v_inst_1863_, lean_object* v_inst_1864_, lean_object* v_inst_1865_, lean_object* v_inst_1866_, lean_object* v_inst_1867_, lean_object* v_toBind_1868_, lean_object* v___f_1869_, lean_object* v_____do__lift_1870_){
_start:
{
uint8_t v_enableLog_boxed_1871_; lean_object* v_res_1872_; 
v_enableLog_boxed_1871_ = lean_unbox(v_enableLog_1859_);
v_res_1872_ = l_Lean_resolveGlobalName___redArg___lam__2(v_enableLog_boxed_1871_, v_toPure_1860_, v_res_1861_, v___f_1862_, v_inst_1863_, v_inst_1864_, v_inst_1865_, v_inst_1866_, v_inst_1867_, v_toBind_1868_, v___f_1869_, v_____do__lift_1870_);
lean_dec_ref(v_____do__lift_1870_);
return v_res_1872_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__3(lean_object* v_____do__lift_1873_, lean_object* v_____do__lift_1874_, lean_object* v_____do__lift_1875_, lean_object* v_id_1876_, lean_object* v_toPure_1877_, uint8_t v_enableLog_1878_, lean_object* v___f_1879_, lean_object* v_inst_1880_, lean_object* v_inst_1881_, lean_object* v_inst_1882_, lean_object* v_inst_1883_, lean_object* v_inst_1884_, lean_object* v_toBind_1885_, lean_object* v_getEnv_1886_, lean_object* v_____do__lift_1887_){
_start:
{
lean_object* v_res_1888_; lean_object* v___f_1889_; lean_object* v___x_1890_; lean_object* v___f_1891_; lean_object* v___x_1892_; 
v_res_1888_ = l_Lean_ResolveName_resolveGlobalName(v_____do__lift_1873_, v_____do__lift_1874_, v_____do__lift_1875_, v_____do__lift_1887_, v_id_1876_);
lean_inc(v_res_1888_);
lean_inc(v_toPure_1877_);
v___f_1889_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalName___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1889_, 0, v_toPure_1877_);
lean_closure_set(v___f_1889_, 1, v_res_1888_);
v___x_1890_ = lean_box(v_enableLog_1878_);
lean_inc(v_toBind_1885_);
v___f_1891_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalName___redArg___lam__2___boxed), 12, 11);
lean_closure_set(v___f_1891_, 0, v___x_1890_);
lean_closure_set(v___f_1891_, 1, v_toPure_1877_);
lean_closure_set(v___f_1891_, 2, v_res_1888_);
lean_closure_set(v___f_1891_, 3, v___f_1879_);
lean_closure_set(v___f_1891_, 4, v_inst_1880_);
lean_closure_set(v___f_1891_, 5, v_inst_1881_);
lean_closure_set(v___f_1891_, 6, v_inst_1882_);
lean_closure_set(v___f_1891_, 7, v_inst_1883_);
lean_closure_set(v___f_1891_, 8, v_inst_1884_);
lean_closure_set(v___f_1891_, 9, v_toBind_1885_);
lean_closure_set(v___f_1891_, 10, v___f_1889_);
v___x_1892_ = lean_apply_4(v_toBind_1885_, lean_box(0), lean_box(0), v_getEnv_1886_, v___f_1891_);
return v___x_1892_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__3___boxed(lean_object* v_____do__lift_1893_, lean_object* v_____do__lift_1894_, lean_object* v_____do__lift_1895_, lean_object* v_id_1896_, lean_object* v_toPure_1897_, lean_object* v_enableLog_1898_, lean_object* v___f_1899_, lean_object* v_inst_1900_, lean_object* v_inst_1901_, lean_object* v_inst_1902_, lean_object* v_inst_1903_, lean_object* v_inst_1904_, lean_object* v_toBind_1905_, lean_object* v_getEnv_1906_, lean_object* v_____do__lift_1907_){
_start:
{
uint8_t v_enableLog_boxed_1908_; lean_object* v_res_1909_; 
v_enableLog_boxed_1908_ = lean_unbox(v_enableLog_1898_);
v_res_1909_ = l_Lean_resolveGlobalName___redArg___lam__3(v_____do__lift_1893_, v_____do__lift_1894_, v_____do__lift_1895_, v_id_1896_, v_toPure_1897_, v_enableLog_boxed_1908_, v___f_1899_, v_inst_1900_, v_inst_1901_, v_inst_1902_, v_inst_1903_, v_inst_1904_, v_toBind_1905_, v_getEnv_1906_, v_____do__lift_1907_);
lean_dec_ref(v_____do__lift_1894_);
return v_res_1909_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__4(lean_object* v_____do__lift_1910_, lean_object* v_____do__lift_1911_, lean_object* v_id_1912_, lean_object* v_toPure_1913_, uint8_t v_enableLog_1914_, lean_object* v___f_1915_, lean_object* v_inst_1916_, lean_object* v_inst_1917_, lean_object* v_inst_1918_, lean_object* v_inst_1919_, lean_object* v_inst_1920_, lean_object* v_toBind_1921_, lean_object* v_getEnv_1922_, lean_object* v_getOpenDecls_1923_, lean_object* v_____do__lift_1924_){
_start:
{
lean_object* v___x_1925_; lean_object* v___f_1926_; lean_object* v___x_1927_; 
v___x_1925_ = lean_box(v_enableLog_1914_);
lean_inc(v_toBind_1921_);
v___f_1926_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalName___redArg___lam__3___boxed), 15, 14);
lean_closure_set(v___f_1926_, 0, v_____do__lift_1910_);
lean_closure_set(v___f_1926_, 1, v_____do__lift_1911_);
lean_closure_set(v___f_1926_, 2, v_____do__lift_1924_);
lean_closure_set(v___f_1926_, 3, v_id_1912_);
lean_closure_set(v___f_1926_, 4, v_toPure_1913_);
lean_closure_set(v___f_1926_, 5, v___x_1925_);
lean_closure_set(v___f_1926_, 6, v___f_1915_);
lean_closure_set(v___f_1926_, 7, v_inst_1916_);
lean_closure_set(v___f_1926_, 8, v_inst_1917_);
lean_closure_set(v___f_1926_, 9, v_inst_1918_);
lean_closure_set(v___f_1926_, 10, v_inst_1919_);
lean_closure_set(v___f_1926_, 11, v_inst_1920_);
lean_closure_set(v___f_1926_, 12, v_toBind_1921_);
lean_closure_set(v___f_1926_, 13, v_getEnv_1922_);
v___x_1927_ = lean_apply_4(v_toBind_1921_, lean_box(0), lean_box(0), v_getOpenDecls_1923_, v___f_1926_);
return v___x_1927_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__4___boxed(lean_object* v_____do__lift_1928_, lean_object* v_____do__lift_1929_, lean_object* v_id_1930_, lean_object* v_toPure_1931_, lean_object* v_enableLog_1932_, lean_object* v___f_1933_, lean_object* v_inst_1934_, lean_object* v_inst_1935_, lean_object* v_inst_1936_, lean_object* v_inst_1937_, lean_object* v_inst_1938_, lean_object* v_toBind_1939_, lean_object* v_getEnv_1940_, lean_object* v_getOpenDecls_1941_, lean_object* v_____do__lift_1942_){
_start:
{
uint8_t v_enableLog_boxed_1943_; lean_object* v_res_1944_; 
v_enableLog_boxed_1943_ = lean_unbox(v_enableLog_1932_);
v_res_1944_ = l_Lean_resolveGlobalName___redArg___lam__4(v_____do__lift_1928_, v_____do__lift_1929_, v_id_1930_, v_toPure_1931_, v_enableLog_boxed_1943_, v___f_1933_, v_inst_1934_, v_inst_1935_, v_inst_1936_, v_inst_1937_, v_inst_1938_, v_toBind_1939_, v_getEnv_1940_, v_getOpenDecls_1941_, v_____do__lift_1942_);
return v_res_1944_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__5(lean_object* v_inst_1945_, lean_object* v_____do__lift_1946_, lean_object* v_id_1947_, lean_object* v_toPure_1948_, uint8_t v_enableLog_1949_, lean_object* v___f_1950_, lean_object* v_inst_1951_, lean_object* v_inst_1952_, lean_object* v_inst_1953_, lean_object* v_inst_1954_, lean_object* v_inst_1955_, lean_object* v_toBind_1956_, lean_object* v_getEnv_1957_, lean_object* v_____do__lift_1958_){
_start:
{
lean_object* v_getCurrNamespace_1959_; lean_object* v_getOpenDecls_1960_; lean_object* v___x_1961_; lean_object* v___f_1962_; lean_object* v___x_1963_; 
v_getCurrNamespace_1959_ = lean_ctor_get(v_inst_1945_, 0);
lean_inc(v_getCurrNamespace_1959_);
v_getOpenDecls_1960_ = lean_ctor_get(v_inst_1945_, 1);
lean_inc(v_getOpenDecls_1960_);
lean_dec_ref(v_inst_1945_);
v___x_1961_ = lean_box(v_enableLog_1949_);
lean_inc(v_toBind_1956_);
v___f_1962_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalName___redArg___lam__4___boxed), 15, 14);
lean_closure_set(v___f_1962_, 0, v_____do__lift_1946_);
lean_closure_set(v___f_1962_, 1, v_____do__lift_1958_);
lean_closure_set(v___f_1962_, 2, v_id_1947_);
lean_closure_set(v___f_1962_, 3, v_toPure_1948_);
lean_closure_set(v___f_1962_, 4, v___x_1961_);
lean_closure_set(v___f_1962_, 5, v___f_1950_);
lean_closure_set(v___f_1962_, 6, v_inst_1951_);
lean_closure_set(v___f_1962_, 7, v_inst_1952_);
lean_closure_set(v___f_1962_, 8, v_inst_1953_);
lean_closure_set(v___f_1962_, 9, v_inst_1954_);
lean_closure_set(v___f_1962_, 10, v_inst_1955_);
lean_closure_set(v___f_1962_, 11, v_toBind_1956_);
lean_closure_set(v___f_1962_, 12, v_getEnv_1957_);
lean_closure_set(v___f_1962_, 13, v_getOpenDecls_1960_);
v___x_1963_ = lean_apply_4(v_toBind_1956_, lean_box(0), lean_box(0), v_getCurrNamespace_1959_, v___f_1962_);
return v___x_1963_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__5___boxed(lean_object* v_inst_1964_, lean_object* v_____do__lift_1965_, lean_object* v_id_1966_, lean_object* v_toPure_1967_, lean_object* v_enableLog_1968_, lean_object* v___f_1969_, lean_object* v_inst_1970_, lean_object* v_inst_1971_, lean_object* v_inst_1972_, lean_object* v_inst_1973_, lean_object* v_inst_1974_, lean_object* v_toBind_1975_, lean_object* v_getEnv_1976_, lean_object* v_____do__lift_1977_){
_start:
{
uint8_t v_enableLog_boxed_1978_; lean_object* v_res_1979_; 
v_enableLog_boxed_1978_ = lean_unbox(v_enableLog_1968_);
v_res_1979_ = l_Lean_resolveGlobalName___redArg___lam__5(v_inst_1964_, v_____do__lift_1965_, v_id_1966_, v_toPure_1967_, v_enableLog_boxed_1978_, v___f_1969_, v_inst_1970_, v_inst_1971_, v_inst_1972_, v_inst_1973_, v_inst_1974_, v_toBind_1975_, v_getEnv_1976_, v_____do__lift_1977_);
return v_res_1979_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__6(lean_object* v_inst_1980_, lean_object* v_id_1981_, lean_object* v_toPure_1982_, uint8_t v_enableLog_1983_, lean_object* v___f_1984_, lean_object* v_inst_1985_, lean_object* v_inst_1986_, lean_object* v_inst_1987_, lean_object* v_inst_1988_, lean_object* v_inst_1989_, lean_object* v_toBind_1990_, lean_object* v_getEnv_1991_, lean_object* v_____do__lift_1992_){
_start:
{
lean_object* v___x_1993_; lean_object* v___f_1994_; lean_object* v___x_1995_; 
v___x_1993_ = lean_box(v_enableLog_1983_);
lean_inc(v_toBind_1990_);
lean_inc(v_inst_1987_);
v___f_1994_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalName___redArg___lam__5___boxed), 14, 13);
lean_closure_set(v___f_1994_, 0, v_inst_1980_);
lean_closure_set(v___f_1994_, 1, v_____do__lift_1992_);
lean_closure_set(v___f_1994_, 2, v_id_1981_);
lean_closure_set(v___f_1994_, 3, v_toPure_1982_);
lean_closure_set(v___f_1994_, 4, v___x_1993_);
lean_closure_set(v___f_1994_, 5, v___f_1984_);
lean_closure_set(v___f_1994_, 6, v_inst_1985_);
lean_closure_set(v___f_1994_, 7, v_inst_1986_);
lean_closure_set(v___f_1994_, 8, v_inst_1987_);
lean_closure_set(v___f_1994_, 9, v_inst_1988_);
lean_closure_set(v___f_1994_, 10, v_inst_1989_);
lean_closure_set(v___f_1994_, 11, v_toBind_1990_);
lean_closure_set(v___f_1994_, 12, v_getEnv_1991_);
v___x_1995_ = lean_apply_4(v_toBind_1990_, lean_box(0), lean_box(0), v_inst_1987_, v___f_1994_);
return v___x_1995_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__6___boxed(lean_object* v_inst_1996_, lean_object* v_id_1997_, lean_object* v_toPure_1998_, lean_object* v_enableLog_1999_, lean_object* v___f_2000_, lean_object* v_inst_2001_, lean_object* v_inst_2002_, lean_object* v_inst_2003_, lean_object* v_inst_2004_, lean_object* v_inst_2005_, lean_object* v_toBind_2006_, lean_object* v_getEnv_2007_, lean_object* v_____do__lift_2008_){
_start:
{
uint8_t v_enableLog_boxed_2009_; lean_object* v_res_2010_; 
v_enableLog_boxed_2009_ = lean_unbox(v_enableLog_1999_);
v_res_2010_ = l_Lean_resolveGlobalName___redArg___lam__6(v_inst_1996_, v_id_1997_, v_toPure_1998_, v_enableLog_boxed_2009_, v___f_2000_, v_inst_2001_, v_inst_2002_, v_inst_2003_, v_inst_2004_, v_inst_2005_, v_toBind_2006_, v_getEnv_2007_, v_____do__lift_2008_);
return v_res_2010_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg(lean_object* v_inst_2012_, lean_object* v_inst_2013_, lean_object* v_inst_2014_, lean_object* v_inst_2015_, lean_object* v_inst_2016_, lean_object* v_inst_2017_, lean_object* v_id_2018_, uint8_t v_enableLog_2019_){
_start:
{
lean_object* v_toApplicative_2020_; lean_object* v_toBind_2021_; lean_object* v_getEnv_2022_; lean_object* v_toPure_2023_; lean_object* v___f_2024_; lean_object* v___x_2025_; lean_object* v___f_2026_; lean_object* v___x_2027_; 
v_toApplicative_2020_ = lean_ctor_get(v_inst_2012_, 0);
v_toBind_2021_ = lean_ctor_get(v_inst_2012_, 1);
lean_inc_n(v_toBind_2021_, 2);
v_getEnv_2022_ = lean_ctor_get(v_inst_2014_, 0);
lean_inc_n(v_getEnv_2022_, 2);
v_toPure_2023_ = lean_ctor_get(v_toApplicative_2020_, 1);
lean_inc(v_toPure_2023_);
v___f_2024_ = ((lean_object*)(l_Lean_resolveGlobalName___redArg___closed__0));
v___x_2025_ = lean_box(v_enableLog_2019_);
v___f_2026_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalName___redArg___lam__6___boxed), 13, 12);
lean_closure_set(v___f_2026_, 0, v_inst_2013_);
lean_closure_set(v___f_2026_, 1, v_id_2018_);
lean_closure_set(v___f_2026_, 2, v_toPure_2023_);
lean_closure_set(v___f_2026_, 3, v___x_2025_);
lean_closure_set(v___f_2026_, 4, v___f_2024_);
lean_closure_set(v___f_2026_, 5, v_inst_2012_);
lean_closure_set(v___f_2026_, 6, v_inst_2014_);
lean_closure_set(v___f_2026_, 7, v_inst_2015_);
lean_closure_set(v___f_2026_, 8, v_inst_2016_);
lean_closure_set(v___f_2026_, 9, v_inst_2017_);
lean_closure_set(v___f_2026_, 10, v_toBind_2021_);
lean_closure_set(v___f_2026_, 11, v_getEnv_2022_);
v___x_2027_ = lean_apply_4(v_toBind_2021_, lean_box(0), lean_box(0), v_getEnv_2022_, v___f_2026_);
return v___x_2027_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___boxed(lean_object* v_inst_2028_, lean_object* v_inst_2029_, lean_object* v_inst_2030_, lean_object* v_inst_2031_, lean_object* v_inst_2032_, lean_object* v_inst_2033_, lean_object* v_id_2034_, lean_object* v_enableLog_2035_){
_start:
{
uint8_t v_enableLog_boxed_2036_; lean_object* v_res_2037_; 
v_enableLog_boxed_2036_ = lean_unbox(v_enableLog_2035_);
v_res_2037_ = l_Lean_resolveGlobalName___redArg(v_inst_2028_, v_inst_2029_, v_inst_2030_, v_inst_2031_, v_inst_2032_, v_inst_2033_, v_id_2034_, v_enableLog_boxed_2036_);
return v_res_2037_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName(lean_object* v_m_2038_, lean_object* v_inst_2039_, lean_object* v_inst_2040_, lean_object* v_inst_2041_, lean_object* v_inst_2042_, lean_object* v_inst_2043_, lean_object* v_inst_2044_, lean_object* v_id_2045_, uint8_t v_enableLog_2046_){
_start:
{
lean_object* v___x_2047_; 
v___x_2047_ = l_Lean_resolveGlobalName___redArg(v_inst_2039_, v_inst_2040_, v_inst_2041_, v_inst_2042_, v_inst_2043_, v_inst_2044_, v_id_2045_, v_enableLog_2046_);
return v___x_2047_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___boxed(lean_object* v_m_2048_, lean_object* v_inst_2049_, lean_object* v_inst_2050_, lean_object* v_inst_2051_, lean_object* v_inst_2052_, lean_object* v_inst_2053_, lean_object* v_inst_2054_, lean_object* v_id_2055_, lean_object* v_enableLog_2056_){
_start:
{
uint8_t v_enableLog_boxed_2057_; lean_object* v_res_2058_; 
v_enableLog_boxed_2057_ = lean_unbox(v_enableLog_2056_);
v_res_2058_ = l_Lean_resolveGlobalName(v_m_2048_, v_inst_2049_, v_inst_2050_, v_inst_2051_, v_inst_2052_, v_inst_2053_, v_inst_2054_, v_id_2055_, v_enableLog_boxed_2057_);
return v_res_2058_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__0(lean_object* v_toPure_2059_, lean_object* v_nss_2060_, lean_object* v_____r_2061_){
_start:
{
lean_object* v___x_2062_; 
v___x_2062_ = lean_apply_2(v_toPure_2059_, lean_box(0), v_nss_2060_);
return v___x_2062_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__1(lean_object* v_____do__lift_2065_, lean_object* v_____do__lift_2066_, lean_object* v_id_2067_, lean_object* v_toPure_2068_, lean_object* v_inst_2069_, lean_object* v_inst_2070_, lean_object* v_toBind_2071_, uint8_t v_allowEmpty_2072_, lean_object* v_____do__lift_2073_){
_start:
{
lean_object* v_nss_2074_; lean_object* v___f_2075_; uint8_t v___y_2077_; uint8_t v___x_2088_; 
lean_inc(v_id_2067_);
v_nss_2074_ = l_Lean_ResolveName_resolveNamespace(v_____do__lift_2065_, v_____do__lift_2066_, v_____do__lift_2073_, v_id_2067_);
lean_inc(v_nss_2074_);
lean_inc(v_toPure_2068_);
v___f_2075_ = lean_alloc_closure((void*)(l_Lean_resolveNamespaceCore___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2075_, 0, v_toPure_2068_);
lean_closure_set(v___f_2075_, 1, v_nss_2074_);
v___x_2088_ = lean_bool_not(v_allowEmpty_2072_);
if (v___x_2088_ == 0)
{
v___y_2077_ = v___x_2088_;
goto v___jp_2076_;
}
else
{
uint8_t v___x_2089_; 
v___x_2089_ = l_List_isEmpty___redArg(v_nss_2074_);
v___y_2077_ = v___x_2089_;
goto v___jp_2076_;
}
v___jp_2076_:
{
if (v___y_2077_ == 0)
{
lean_object* v___x_2078_; 
lean_dec_ref(v___f_2075_);
lean_dec(v_toBind_2071_);
lean_dec_ref(v_inst_2070_);
lean_dec_ref(v_inst_2069_);
lean_dec(v_id_2067_);
v___x_2078_ = lean_apply_2(v_toPure_2068_, lean_box(0), v_nss_2074_);
return v___x_2078_;
}
else
{
lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; 
lean_dec(v_nss_2074_);
lean_dec(v_toPure_2068_);
v___x_2079_ = ((lean_object*)(l_Lean_resolveNamespaceCore___redArg___lam__1___closed__0));
v___x_2080_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_id_2067_, v___y_2077_);
v___x_2081_ = lean_string_append(v___x_2079_, v___x_2080_);
lean_dec_ref(v___x_2080_);
v___x_2082_ = ((lean_object*)(l_Lean_resolveNamespaceCore___redArg___lam__1___closed__1));
v___x_2083_ = lean_string_append(v___x_2081_, v___x_2082_);
v___x_2084_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2084_, 0, v___x_2083_);
v___x_2085_ = l_Lean_MessageData_ofFormat(v___x_2084_);
v___x_2086_ = l_Lean_throwError___redArg(v_inst_2069_, v_inst_2070_, v___x_2085_);
v___x_2087_ = lean_apply_4(v_toBind_2071_, lean_box(0), lean_box(0), v___x_2086_, v___f_2075_);
return v___x_2087_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__1___boxed(lean_object* v_____do__lift_2090_, lean_object* v_____do__lift_2091_, lean_object* v_id_2092_, lean_object* v_toPure_2093_, lean_object* v_inst_2094_, lean_object* v_inst_2095_, lean_object* v_toBind_2096_, lean_object* v_allowEmpty_2097_, lean_object* v_____do__lift_2098_){
_start:
{
uint8_t v_allowEmpty_boxed_2099_; lean_object* v_res_2100_; 
v_allowEmpty_boxed_2099_ = lean_unbox(v_allowEmpty_2097_);
v_res_2100_ = l_Lean_resolveNamespaceCore___redArg___lam__1(v_____do__lift_2090_, v_____do__lift_2091_, v_id_2092_, v_toPure_2093_, v_inst_2094_, v_inst_2095_, v_toBind_2096_, v_allowEmpty_boxed_2099_, v_____do__lift_2098_);
return v_res_2100_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__2(lean_object* v_____do__lift_2101_, lean_object* v_id_2102_, lean_object* v_toPure_2103_, lean_object* v_inst_2104_, lean_object* v_inst_2105_, lean_object* v_toBind_2106_, uint8_t v_allowEmpty_2107_, lean_object* v_getOpenDecls_2108_, lean_object* v_____do__lift_2109_){
_start:
{
lean_object* v___x_2110_; lean_object* v___f_2111_; lean_object* v___x_2112_; 
v___x_2110_ = lean_box(v_allowEmpty_2107_);
lean_inc(v_toBind_2106_);
v___f_2111_ = lean_alloc_closure((void*)(l_Lean_resolveNamespaceCore___redArg___lam__1___boxed), 9, 8);
lean_closure_set(v___f_2111_, 0, v_____do__lift_2101_);
lean_closure_set(v___f_2111_, 1, v_____do__lift_2109_);
lean_closure_set(v___f_2111_, 2, v_id_2102_);
lean_closure_set(v___f_2111_, 3, v_toPure_2103_);
lean_closure_set(v___f_2111_, 4, v_inst_2104_);
lean_closure_set(v___f_2111_, 5, v_inst_2105_);
lean_closure_set(v___f_2111_, 6, v_toBind_2106_);
lean_closure_set(v___f_2111_, 7, v___x_2110_);
v___x_2112_ = lean_apply_4(v_toBind_2106_, lean_box(0), lean_box(0), v_getOpenDecls_2108_, v___f_2111_);
return v___x_2112_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__2___boxed(lean_object* v_____do__lift_2113_, lean_object* v_id_2114_, lean_object* v_toPure_2115_, lean_object* v_inst_2116_, lean_object* v_inst_2117_, lean_object* v_toBind_2118_, lean_object* v_allowEmpty_2119_, lean_object* v_getOpenDecls_2120_, lean_object* v_____do__lift_2121_){
_start:
{
uint8_t v_allowEmpty_boxed_2122_; lean_object* v_res_2123_; 
v_allowEmpty_boxed_2122_ = lean_unbox(v_allowEmpty_2119_);
v_res_2123_ = l_Lean_resolveNamespaceCore___redArg___lam__2(v_____do__lift_2113_, v_id_2114_, v_toPure_2115_, v_inst_2116_, v_inst_2117_, v_toBind_2118_, v_allowEmpty_boxed_2122_, v_getOpenDecls_2120_, v_____do__lift_2121_);
return v_res_2123_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__3(lean_object* v_inst_2124_, lean_object* v_id_2125_, lean_object* v_toPure_2126_, lean_object* v_inst_2127_, lean_object* v_inst_2128_, lean_object* v_toBind_2129_, uint8_t v_allowEmpty_2130_, lean_object* v_____do__lift_2131_){
_start:
{
lean_object* v_getCurrNamespace_2132_; lean_object* v_getOpenDecls_2133_; lean_object* v___x_2134_; lean_object* v___f_2135_; lean_object* v___x_2136_; 
v_getCurrNamespace_2132_ = lean_ctor_get(v_inst_2124_, 0);
lean_inc(v_getCurrNamespace_2132_);
v_getOpenDecls_2133_ = lean_ctor_get(v_inst_2124_, 1);
lean_inc(v_getOpenDecls_2133_);
lean_dec_ref(v_inst_2124_);
v___x_2134_ = lean_box(v_allowEmpty_2130_);
lean_inc(v_toBind_2129_);
v___f_2135_ = lean_alloc_closure((void*)(l_Lean_resolveNamespaceCore___redArg___lam__2___boxed), 9, 8);
lean_closure_set(v___f_2135_, 0, v_____do__lift_2131_);
lean_closure_set(v___f_2135_, 1, v_id_2125_);
lean_closure_set(v___f_2135_, 2, v_toPure_2126_);
lean_closure_set(v___f_2135_, 3, v_inst_2127_);
lean_closure_set(v___f_2135_, 4, v_inst_2128_);
lean_closure_set(v___f_2135_, 5, v_toBind_2129_);
lean_closure_set(v___f_2135_, 6, v___x_2134_);
lean_closure_set(v___f_2135_, 7, v_getOpenDecls_2133_);
v___x_2136_ = lean_apply_4(v_toBind_2129_, lean_box(0), lean_box(0), v_getCurrNamespace_2132_, v___f_2135_);
return v___x_2136_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__3___boxed(lean_object* v_inst_2137_, lean_object* v_id_2138_, lean_object* v_toPure_2139_, lean_object* v_inst_2140_, lean_object* v_inst_2141_, lean_object* v_toBind_2142_, lean_object* v_allowEmpty_2143_, lean_object* v_____do__lift_2144_){
_start:
{
uint8_t v_allowEmpty_boxed_2145_; lean_object* v_res_2146_; 
v_allowEmpty_boxed_2145_ = lean_unbox(v_allowEmpty_2143_);
v_res_2146_ = l_Lean_resolveNamespaceCore___redArg___lam__3(v_inst_2137_, v_id_2138_, v_toPure_2139_, v_inst_2140_, v_inst_2141_, v_toBind_2142_, v_allowEmpty_boxed_2145_, v_____do__lift_2144_);
return v_res_2146_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg(lean_object* v_inst_2147_, lean_object* v_inst_2148_, lean_object* v_inst_2149_, lean_object* v_inst_2150_, lean_object* v_id_2151_, uint8_t v_allowEmpty_2152_){
_start:
{
lean_object* v_toApplicative_2153_; lean_object* v_toBind_2154_; lean_object* v_getEnv_2155_; lean_object* v_toPure_2156_; lean_object* v___x_2157_; lean_object* v___f_2158_; lean_object* v___x_2159_; 
v_toApplicative_2153_ = lean_ctor_get(v_inst_2147_, 0);
v_toBind_2154_ = lean_ctor_get(v_inst_2147_, 1);
lean_inc_n(v_toBind_2154_, 2);
v_getEnv_2155_ = lean_ctor_get(v_inst_2149_, 0);
lean_inc(v_getEnv_2155_);
lean_dec_ref(v_inst_2149_);
v_toPure_2156_ = lean_ctor_get(v_toApplicative_2153_, 1);
lean_inc(v_toPure_2156_);
v___x_2157_ = lean_box(v_allowEmpty_2152_);
v___f_2158_ = lean_alloc_closure((void*)(l_Lean_resolveNamespaceCore___redArg___lam__3___boxed), 8, 7);
lean_closure_set(v___f_2158_, 0, v_inst_2148_);
lean_closure_set(v___f_2158_, 1, v_id_2151_);
lean_closure_set(v___f_2158_, 2, v_toPure_2156_);
lean_closure_set(v___f_2158_, 3, v_inst_2147_);
lean_closure_set(v___f_2158_, 4, v_inst_2150_);
lean_closure_set(v___f_2158_, 5, v_toBind_2154_);
lean_closure_set(v___f_2158_, 6, v___x_2157_);
v___x_2159_ = lean_apply_4(v_toBind_2154_, lean_box(0), lean_box(0), v_getEnv_2155_, v___f_2158_);
return v___x_2159_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___boxed(lean_object* v_inst_2160_, lean_object* v_inst_2161_, lean_object* v_inst_2162_, lean_object* v_inst_2163_, lean_object* v_id_2164_, lean_object* v_allowEmpty_2165_){
_start:
{
uint8_t v_allowEmpty_boxed_2166_; lean_object* v_res_2167_; 
v_allowEmpty_boxed_2166_ = lean_unbox(v_allowEmpty_2165_);
v_res_2167_ = l_Lean_resolveNamespaceCore___redArg(v_inst_2160_, v_inst_2161_, v_inst_2162_, v_inst_2163_, v_id_2164_, v_allowEmpty_boxed_2166_);
return v_res_2167_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore(lean_object* v_m_2168_, lean_object* v_inst_2169_, lean_object* v_inst_2170_, lean_object* v_inst_2171_, lean_object* v_inst_2172_, lean_object* v_id_2173_, uint8_t v_allowEmpty_2174_){
_start:
{
lean_object* v___x_2175_; 
v___x_2175_ = l_Lean_resolveNamespaceCore___redArg(v_inst_2169_, v_inst_2170_, v_inst_2171_, v_inst_2172_, v_id_2173_, v_allowEmpty_2174_);
return v___x_2175_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___boxed(lean_object* v_m_2176_, lean_object* v_inst_2177_, lean_object* v_inst_2178_, lean_object* v_inst_2179_, lean_object* v_inst_2180_, lean_object* v_id_2181_, lean_object* v_allowEmpty_2182_){
_start:
{
uint8_t v_allowEmpty_boxed_2183_; lean_object* v_res_2184_; 
v_allowEmpty_boxed_2183_ = lean_unbox(v_allowEmpty_2182_);
v_res_2184_ = l_Lean_resolveNamespaceCore(v_m_2176_, v_inst_2177_, v_inst_2178_, v_inst_2179_, v_inst_2180_, v_id_2181_, v_allowEmpty_boxed_2183_);
return v_res_2184_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespace___redArg___lam__0(lean_object* v_x_2185_){
_start:
{
if (lean_obj_tag(v_x_2185_) == 0)
{
lean_object* v_ns_2186_; lean_object* v___x_2188_; uint8_t v_isShared_2189_; uint8_t v_isSharedCheck_2193_; 
v_ns_2186_ = lean_ctor_get(v_x_2185_, 0);
v_isSharedCheck_2193_ = !lean_is_exclusive(v_x_2185_);
if (v_isSharedCheck_2193_ == 0)
{
v___x_2188_ = v_x_2185_;
v_isShared_2189_ = v_isSharedCheck_2193_;
goto v_resetjp_2187_;
}
else
{
lean_inc(v_ns_2186_);
lean_dec(v_x_2185_);
v___x_2188_ = lean_box(0);
v_isShared_2189_ = v_isSharedCheck_2193_;
goto v_resetjp_2187_;
}
v_resetjp_2187_:
{
lean_object* v___x_2191_; 
if (v_isShared_2189_ == 0)
{
lean_ctor_set_tag(v___x_2188_, 1);
v___x_2191_ = v___x_2188_;
goto v_reusejp_2190_;
}
else
{
lean_object* v_reuseFailAlloc_2192_; 
v_reuseFailAlloc_2192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2192_, 0, v_ns_2186_);
v___x_2191_ = v_reuseFailAlloc_2192_;
goto v_reusejp_2190_;
}
v_reusejp_2190_:
{
return v___x_2191_;
}
}
}
else
{
lean_object* v___x_2194_; 
lean_dec_ref(v_x_2185_);
v___x_2194_ = lean_box(0);
return v___x_2194_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespace___redArg___lam__1(lean_object* v_x_2195_, lean_object* v_withRef_2196_, lean_object* v___x_2197_, lean_object* v_oldRef_2198_){
_start:
{
lean_object* v_ref_2199_; lean_object* v___x_2200_; 
v_ref_2199_ = l_Lean_replaceRef(v_x_2195_, v_oldRef_2198_);
v___x_2200_ = lean_apply_3(v_withRef_2196_, lean_box(0), v_ref_2199_, v___x_2197_);
return v___x_2200_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespace___redArg___lam__1___boxed(lean_object* v_x_2201_, lean_object* v_withRef_2202_, lean_object* v___x_2203_, lean_object* v_oldRef_2204_){
_start:
{
lean_object* v_res_2205_; 
v_res_2205_ = l_Lean_resolveNamespace___redArg___lam__1(v_x_2201_, v_withRef_2202_, v___x_2203_, v_oldRef_2204_);
lean_dec(v_oldRef_2204_);
lean_dec(v_x_2201_);
return v_res_2205_;
}
}
static lean_object* _init_l_Lean_resolveNamespace___redArg___closed__4(void){
_start:
{
lean_object* v___x_2212_; lean_object* v___x_2213_; 
v___x_2212_ = ((lean_object*)(l_Lean_resolveNamespace___redArg___closed__3));
v___x_2213_ = l_Lean_MessageData_ofFormat(v___x_2212_);
return v___x_2213_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespace___redArg(lean_object* v_inst_2214_, lean_object* v_inst_2215_, lean_object* v_inst_2216_, lean_object* v_inst_2217_, lean_object* v_x_2218_){
_start:
{
if (lean_obj_tag(v_x_2218_) == 3)
{
lean_object* v_val_2219_; lean_object* v_preresolved_2220_; lean_object* v___f_2221_; lean_object* v___x_2222_; lean_object* v_pre_2223_; uint8_t v___x_2224_; 
v_val_2219_ = lean_ctor_get(v_x_2218_, 2);
v_preresolved_2220_ = lean_ctor_get(v_x_2218_, 3);
v___f_2221_ = ((lean_object*)(l_Lean_resolveNamespace___redArg___closed__0));
v___x_2222_ = ((lean_object*)(l_Lean_resolveNamespace___redArg___closed__1));
lean_inc(v_preresolved_2220_);
v_pre_2223_ = l_List_filterMapTR_go___redArg(v___f_2221_, v_preresolved_2220_, v___x_2222_);
v___x_2224_ = l_List_isEmpty___redArg(v_pre_2223_);
if (v___x_2224_ == 0)
{
lean_object* v_toApplicative_2225_; lean_object* v_toPure_2226_; lean_object* v___x_2227_; 
lean_dec_ref_known(v_x_2218_, 4);
lean_dec_ref(v_inst_2217_);
lean_dec_ref(v_inst_2216_);
lean_dec_ref(v_inst_2215_);
v_toApplicative_2225_ = lean_ctor_get(v_inst_2214_, 0);
lean_inc_ref(v_toApplicative_2225_);
lean_dec_ref(v_inst_2214_);
v_toPure_2226_ = lean_ctor_get(v_toApplicative_2225_, 1);
lean_inc(v_toPure_2226_);
lean_dec_ref(v_toApplicative_2225_);
v___x_2227_ = lean_apply_2(v_toPure_2226_, lean_box(0), v_pre_2223_);
return v___x_2227_;
}
else
{
lean_object* v_toMonadRef_2228_; lean_object* v_toBind_2229_; lean_object* v_getRef_2230_; lean_object* v_withRef_2231_; uint8_t v___x_2232_; lean_object* v___x_2233_; lean_object* v___f_2234_; lean_object* v___x_2235_; 
lean_dec(v_pre_2223_);
v_toMonadRef_2228_ = lean_ctor_get(v_inst_2217_, 1);
v_toBind_2229_ = lean_ctor_get(v_inst_2214_, 1);
lean_inc(v_toBind_2229_);
v_getRef_2230_ = lean_ctor_get(v_toMonadRef_2228_, 0);
lean_inc(v_getRef_2230_);
v_withRef_2231_ = lean_ctor_get(v_toMonadRef_2228_, 1);
lean_inc(v_withRef_2231_);
v___x_2232_ = 0;
lean_inc(v_val_2219_);
v___x_2233_ = l_Lean_resolveNamespaceCore___redArg(v_inst_2214_, v_inst_2215_, v_inst_2216_, v_inst_2217_, v_val_2219_, v___x_2232_);
v___f_2234_ = lean_alloc_closure((void*)(l_Lean_resolveNamespace___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_2234_, 0, v_x_2218_);
lean_closure_set(v___f_2234_, 1, v_withRef_2231_);
lean_closure_set(v___f_2234_, 2, v___x_2233_);
v___x_2235_ = lean_apply_4(v_toBind_2229_, lean_box(0), lean_box(0), v_getRef_2230_, v___f_2234_);
return v___x_2235_;
}
}
else
{
lean_object* v___x_2236_; lean_object* v___x_2237_; 
lean_dec_ref(v_inst_2216_);
lean_dec_ref(v_inst_2215_);
v___x_2236_ = lean_obj_once(&l_Lean_resolveNamespace___redArg___closed__4, &l_Lean_resolveNamespace___redArg___closed__4_once, _init_l_Lean_resolveNamespace___redArg___closed__4);
v___x_2237_ = l_Lean_throwErrorAt___redArg(v_inst_2214_, v_inst_2217_, v_x_2218_, v___x_2236_);
return v___x_2237_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespace(lean_object* v_m_2238_, lean_object* v_inst_2239_, lean_object* v_inst_2240_, lean_object* v_inst_2241_, lean_object* v_inst_2242_, lean_object* v_x_2243_){
_start:
{
lean_object* v___x_2244_; 
v___x_2244_ = l_Lean_resolveNamespace___redArg(v_inst_2239_, v_inst_2240_, v_inst_2241_, v_inst_2242_, v_x_2243_);
return v___x_2244_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveUniqueNamespace___redArg___lam__0(lean_object* v_id_2247_, lean_object* v___f_2248_, lean_object* v_inst_2249_, lean_object* v_inst_2250_, lean_object* v_toPure_2251_, lean_object* v_____do__lift_2252_){
_start:
{
if (lean_obj_tag(v_____do__lift_2252_) == 1)
{
lean_object* v_tail_2268_; 
v_tail_2268_ = lean_ctor_get(v_____do__lift_2252_, 1);
if (lean_obj_tag(v_tail_2268_) == 0)
{
lean_object* v_head_2269_; lean_object* v___x_2270_; 
lean_dec_ref(v_inst_2250_);
lean_dec_ref(v_inst_2249_);
lean_dec_ref(v___f_2248_);
v_head_2269_ = lean_ctor_get(v_____do__lift_2252_, 0);
lean_inc(v_head_2269_);
lean_dec_ref_known(v_____do__lift_2252_, 2);
v___x_2270_ = lean_apply_2(v_toPure_2251_, lean_box(0), v_head_2269_);
return v___x_2270_;
}
else
{
lean_dec(v_toPure_2251_);
goto v___jp_2253_;
}
}
else
{
lean_dec(v_toPure_2251_);
goto v___jp_2253_;
}
v___jp_2253_:
{
lean_object* v___x_2254_; lean_object* v___x_2255_; uint8_t v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; 
v___x_2254_ = ((lean_object*)(l_Lean_resolveUniqueNamespace___redArg___lam__0___closed__0));
v___x_2255_ = l_Lean_TSyntax_getId(v_id_2247_);
v___x_2256_ = 1;
v___x_2257_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2255_, v___x_2256_);
v___x_2258_ = lean_string_append(v___x_2254_, v___x_2257_);
lean_dec_ref(v___x_2257_);
v___x_2259_ = ((lean_object*)(l_Lean_resolveUniqueNamespace___redArg___lam__0___closed__1));
v___x_2260_ = lean_string_append(v___x_2258_, v___x_2259_);
v___x_2261_ = l_List_toString___redArg(v___f_2248_, v_____do__lift_2252_);
v___x_2262_ = lean_string_append(v___x_2260_, v___x_2261_);
lean_dec_ref(v___x_2261_);
v___x_2263_ = ((lean_object*)(l_Lean_resolveNamespaceCore___redArg___lam__1___closed__1));
v___x_2264_ = lean_string_append(v___x_2262_, v___x_2263_);
v___x_2265_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2265_, 0, v___x_2264_);
v___x_2266_ = l_Lean_MessageData_ofFormat(v___x_2265_);
v___x_2267_ = l_Lean_throwError___redArg(v_inst_2249_, v_inst_2250_, v___x_2266_);
return v___x_2267_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveUniqueNamespace___redArg___lam__0___boxed(lean_object* v_id_2271_, lean_object* v___f_2272_, lean_object* v_inst_2273_, lean_object* v_inst_2274_, lean_object* v_toPure_2275_, lean_object* v_____do__lift_2276_){
_start:
{
lean_object* v_res_2277_; 
v_res_2277_ = l_Lean_resolveUniqueNamespace___redArg___lam__0(v_id_2271_, v___f_2272_, v_inst_2273_, v_inst_2274_, v_toPure_2275_, v_____do__lift_2276_);
lean_dec(v_id_2271_);
return v_res_2277_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveUniqueNamespace___redArg(lean_object* v_inst_2279_, lean_object* v_inst_2280_, lean_object* v_inst_2281_, lean_object* v_inst_2282_, lean_object* v_id_2283_){
_start:
{
lean_object* v_toApplicative_2284_; lean_object* v_toBind_2285_; lean_object* v_toPure_2286_; lean_object* v___f_2287_; lean_object* v___x_2288_; lean_object* v___f_2289_; lean_object* v___x_2290_; 
v_toApplicative_2284_ = lean_ctor_get(v_inst_2279_, 0);
v_toBind_2285_ = lean_ctor_get(v_inst_2279_, 1);
lean_inc(v_toBind_2285_);
v_toPure_2286_ = lean_ctor_get(v_toApplicative_2284_, 1);
lean_inc(v_toPure_2286_);
v___f_2287_ = ((lean_object*)(l_Lean_resolveUniqueNamespace___redArg___closed__0));
lean_inc(v_id_2283_);
lean_inc_ref(v_inst_2282_);
lean_inc_ref(v_inst_2279_);
v___x_2288_ = l_Lean_resolveNamespace___redArg(v_inst_2279_, v_inst_2280_, v_inst_2281_, v_inst_2282_, v_id_2283_);
v___f_2289_ = lean_alloc_closure((void*)(l_Lean_resolveUniqueNamespace___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_2289_, 0, v_id_2283_);
lean_closure_set(v___f_2289_, 1, v___f_2287_);
lean_closure_set(v___f_2289_, 2, v_inst_2279_);
lean_closure_set(v___f_2289_, 3, v_inst_2282_);
lean_closure_set(v___f_2289_, 4, v_toPure_2286_);
v___x_2290_ = lean_apply_4(v_toBind_2285_, lean_box(0), lean_box(0), v___x_2288_, v___f_2289_);
return v___x_2290_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveUniqueNamespace(lean_object* v_m_2291_, lean_object* v_inst_2292_, lean_object* v_inst_2293_, lean_object* v_inst_2294_, lean_object* v_inst_2295_, lean_object* v_id_2296_){
_start:
{
lean_object* v___x_2297_; 
v___x_2297_ = l_Lean_resolveUniqueNamespace___redArg(v_inst_2292_, v_inst_2293_, v_inst_2294_, v_inst_2295_, v_id_2296_);
return v___x_2297_;
}
}
LEAN_EXPORT uint8_t l_Lean_filterFieldList___redArg___lam__0(lean_object* v_x_2298_){
_start:
{
lean_object* v_snd_2299_; uint8_t v___x_2300_; 
v_snd_2299_ = lean_ctor_get(v_x_2298_, 1);
v___x_2300_ = l_List_isEmpty___redArg(v_snd_2299_);
return v___x_2300_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg___lam__0___boxed(lean_object* v_x_2301_){
_start:
{
uint8_t v_res_2302_; lean_object* v_r_2303_; 
v_res_2302_ = l_Lean_filterFieldList___redArg___lam__0(v_x_2301_);
lean_dec_ref(v_x_2301_);
v_r_2303_ = lean_box(v_res_2302_);
return v_r_2303_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg___lam__1(lean_object* v_x_2304_){
_start:
{
lean_object* v_fst_2305_; 
v_fst_2305_ = lean_ctor_get(v_x_2304_, 0);
lean_inc(v_fst_2305_);
return v_fst_2305_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg___lam__1___boxed(lean_object* v_x_2306_){
_start:
{
lean_object* v_res_2307_; 
v_res_2307_ = l_Lean_filterFieldList___redArg___lam__1(v_x_2306_);
lean_dec_ref(v_x_2306_);
return v_res_2307_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg___lam__2(lean_object* v___f_2308_, lean_object* v_cs_2309_, lean_object* v_toPure_2310_, lean_object* v_____r_2311_){
_start:
{
lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; 
v___x_2312_ = lean_box(0);
v___x_2313_ = l_List_mapTR_loop___redArg(v___f_2308_, v_cs_2309_, v___x_2312_);
v___x_2314_ = lean_apply_2(v_toPure_2310_, lean_box(0), v___x_2313_);
return v___x_2314_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg___lam__3(lean_object* v___f_2315_, lean_object* v_____r_2316_){
_start:
{
lean_object* v___x_2317_; 
v___x_2317_ = lean_apply_1(v___f_2315_, v_____r_2316_);
return v___x_2317_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg___lam__4(lean_object* v_inst_2318_, lean_object* v_inst_2319_, lean_object* v_inst_2320_, lean_object* v_n_2321_, lean_object* v_toBind_2322_, lean_object* v___f_2323_, lean_object* v_____do__lift_2324_){
_start:
{
lean_object* v___x_2325_; lean_object* v___x_2326_; 
v___x_2325_ = l_Lean_throwUnknownConstantAt___redArg(v_inst_2318_, v_inst_2319_, v_inst_2320_, v_____do__lift_2324_, v_n_2321_);
v___x_2326_ = lean_apply_4(v_toBind_2322_, lean_box(0), lean_box(0), v___x_2325_, v___f_2323_);
return v___x_2326_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg(lean_object* v_inst_2329_, lean_object* v_inst_2330_, lean_object* v_inst_2331_, lean_object* v_n_2332_, lean_object* v_cs_2333_){
_start:
{
lean_object* v_toApplicative_2334_; lean_object* v_toBind_2335_; lean_object* v_toPure_2336_; lean_object* v___f_2337_; lean_object* v___f_2338_; lean_object* v___x_2339_; lean_object* v_cs_2340_; lean_object* v___f_2341_; uint8_t v___x_2342_; 
v_toApplicative_2334_ = lean_ctor_get(v_inst_2329_, 0);
v_toBind_2335_ = lean_ctor_get(v_inst_2329_, 1);
lean_inc(v_toBind_2335_);
v_toPure_2336_ = lean_ctor_get(v_toApplicative_2334_, 1);
v___f_2337_ = ((lean_object*)(l_Lean_filterFieldList___redArg___closed__0));
v___f_2338_ = ((lean_object*)(l_Lean_filterFieldList___redArg___closed__1));
v___x_2339_ = lean_box(0);
v_cs_2340_ = l_List_filterTR_loop___redArg(v___f_2337_, v_cs_2333_, v___x_2339_);
lean_inc(v_toPure_2336_);
lean_inc(v_cs_2340_);
v___f_2341_ = lean_alloc_closure((void*)(l_Lean_filterFieldList___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2341_, 0, v___f_2338_);
lean_closure_set(v___f_2341_, 1, v_cs_2340_);
lean_closure_set(v___f_2341_, 2, v_toPure_2336_);
v___x_2342_ = l_List_isEmpty___redArg(v_cs_2340_);
if (v___x_2342_ == 0)
{
lean_object* v___x_2343_; lean_object* v___x_2344_; 
lean_inc(v_toPure_2336_);
lean_dec_ref(v___f_2341_);
lean_dec(v_toBind_2335_);
lean_dec(v_n_2332_);
lean_dec_ref(v_inst_2331_);
lean_dec_ref(v_inst_2330_);
lean_dec_ref(v_inst_2329_);
v___x_2343_ = lean_box(0);
v___x_2344_ = l_Lean_filterFieldList___redArg___lam__2(v___f_2338_, v_cs_2340_, v_toPure_2336_, v___x_2343_);
return v___x_2344_;
}
else
{
lean_object* v_toMonadRef_2345_; lean_object* v_getRef_2346_; lean_object* v___f_2347_; lean_object* v___f_2348_; lean_object* v___x_2349_; 
lean_dec(v_cs_2340_);
v_toMonadRef_2345_ = lean_ctor_get(v_inst_2331_, 1);
v_getRef_2346_ = lean_ctor_get(v_toMonadRef_2345_, 0);
lean_inc(v_getRef_2346_);
v___f_2347_ = lean_alloc_closure((void*)(l_Lean_filterFieldList___redArg___lam__3), 2, 1);
lean_closure_set(v___f_2347_, 0, v___f_2341_);
lean_inc(v_toBind_2335_);
v___f_2348_ = lean_alloc_closure((void*)(l_Lean_filterFieldList___redArg___lam__4), 7, 6);
lean_closure_set(v___f_2348_, 0, v_inst_2329_);
lean_closure_set(v___f_2348_, 1, v_inst_2330_);
lean_closure_set(v___f_2348_, 2, v_inst_2331_);
lean_closure_set(v___f_2348_, 3, v_n_2332_);
lean_closure_set(v___f_2348_, 4, v_toBind_2335_);
lean_closure_set(v___f_2348_, 5, v___f_2347_);
v___x_2349_ = lean_apply_4(v_toBind_2335_, lean_box(0), lean_box(0), v_getRef_2346_, v___f_2348_);
return v___x_2349_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList(lean_object* v_m_2350_, lean_object* v_inst_2351_, lean_object* v_inst_2352_, lean_object* v_inst_2353_, lean_object* v_n_2354_, lean_object* v_cs_2355_){
_start:
{
lean_object* v___x_2356_; 
v___x_2356_ = l_Lean_filterFieldList___redArg(v_inst_2351_, v_inst_2352_, v_inst_2353_, v_n_2354_, v_cs_2355_);
return v___x_2356_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___redArg___lam__0(lean_object* v_inst_2357_, lean_object* v_inst_2358_, lean_object* v_inst_2359_, lean_object* v_n_2360_, lean_object* v_cs_2361_){
_start:
{
lean_object* v___x_2362_; 
v___x_2362_ = l_Lean_filterFieldList___redArg(v_inst_2357_, v_inst_2358_, v_inst_2359_, v_n_2360_, v_cs_2361_);
return v___x_2362_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___redArg(lean_object* v_inst_2363_, lean_object* v_inst_2364_, lean_object* v_inst_2365_, lean_object* v_inst_2366_, lean_object* v_inst_2367_, lean_object* v_inst_2368_, lean_object* v_inst_2369_, lean_object* v_n_2370_){
_start:
{
lean_object* v_toBind_2371_; lean_object* v___f_2372_; uint8_t v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; 
v_toBind_2371_ = lean_ctor_get(v_inst_2363_, 1);
lean_inc(v_toBind_2371_);
lean_inc(v_n_2370_);
lean_inc_ref(v_inst_2365_);
lean_inc_ref(v_inst_2363_);
v___f_2372_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___redArg___lam__0), 5, 4);
lean_closure_set(v___f_2372_, 0, v_inst_2363_);
lean_closure_set(v___f_2372_, 1, v_inst_2365_);
lean_closure_set(v___f_2372_, 2, v_inst_2369_);
lean_closure_set(v___f_2372_, 3, v_n_2370_);
v___x_2373_ = 1;
v___x_2374_ = l_Lean_resolveGlobalName___redArg(v_inst_2363_, v_inst_2364_, v_inst_2365_, v_inst_2366_, v_inst_2367_, v_inst_2368_, v_n_2370_, v___x_2373_);
v___x_2375_ = lean_apply_4(v_toBind_2371_, lean_box(0), lean_box(0), v___x_2374_, v___f_2372_);
return v___x_2375_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore(lean_object* v_m_2376_, lean_object* v_inst_2377_, lean_object* v_inst_2378_, lean_object* v_inst_2379_, lean_object* v_inst_2380_, lean_object* v_inst_2381_, lean_object* v_inst_2382_, lean_object* v_inst_2383_, lean_object* v_n_2384_){
_start:
{
lean_object* v___x_2385_; 
v___x_2385_ = l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___redArg(v_inst_2377_, v_inst_2378_, v_inst_2379_, v_inst_2380_, v_inst_2381_, v_inst_2382_, v_inst_2383_, v_n_2384_);
return v___x_2385_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNoOverload___redArg___lam__0(lean_object* v_declName_2386_){
_start:
{
lean_object* v___x_2387_; lean_object* v___x_2388_; 
v___x_2387_ = lean_box(0);
v___x_2388_ = l_Lean_mkConst(v_declName_2386_, v___x_2387_);
return v___x_2388_;
}
}
static lean_object* _init_l_Lean_ensureNoOverload___redArg___closed__2(void){
_start:
{
lean_object* v___x_2391_; lean_object* v___x_2392_; 
v___x_2391_ = ((lean_object*)(l_Lean_ensureNoOverload___redArg___closed__1));
v___x_2392_ = l_Lean_stringToMessageData(v___x_2391_);
return v___x_2392_;
}
}
static lean_object* _init_l_Lean_ensureNoOverload___redArg___closed__4(void){
_start:
{
lean_object* v___x_2394_; lean_object* v___x_2395_; 
v___x_2394_ = ((lean_object*)(l_Lean_ensureNoOverload___redArg___closed__3));
v___x_2395_ = l_Lean_stringToMessageData(v___x_2394_);
return v___x_2395_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNoOverload___redArg(lean_object* v_inst_2397_, lean_object* v_inst_2398_, lean_object* v_n_2399_, lean_object* v_cs_2400_){
_start:
{
lean_object* v_toApplicative_2401_; lean_object* v_toPure_2402_; lean_object* v___f_2403_; 
v_toApplicative_2401_ = lean_ctor_get(v_inst_2397_, 0);
v_toPure_2402_ = lean_ctor_get(v_toApplicative_2401_, 1);
v___f_2403_ = ((lean_object*)(l_Lean_ensureNoOverload___redArg___closed__0));
if (lean_obj_tag(v_cs_2400_) == 1)
{
lean_object* v_tail_2417_; 
v_tail_2417_ = lean_ctor_get(v_cs_2400_, 1);
if (lean_obj_tag(v_tail_2417_) == 0)
{
lean_object* v_head_2418_; lean_object* v___x_2419_; 
lean_inc(v_toPure_2402_);
lean_dec(v_n_2399_);
lean_dec_ref(v_inst_2398_);
lean_dec_ref(v_inst_2397_);
v_head_2418_ = lean_ctor_get(v_cs_2400_, 0);
lean_inc(v_head_2418_);
lean_dec_ref_known(v_cs_2400_, 2);
v___x_2419_ = lean_apply_2(v_toPure_2402_, lean_box(0), v_head_2418_);
return v___x_2419_;
}
else
{
goto v___jp_2404_;
}
}
else
{
goto v___jp_2404_;
}
v___jp_2404_:
{
lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; 
v___x_2405_ = lean_obj_once(&l_Lean_ensureNoOverload___redArg___closed__2, &l_Lean_ensureNoOverload___redArg___closed__2_once, _init_l_Lean_ensureNoOverload___redArg___closed__2);
v___x_2406_ = l_Lean_MessageData_ofName(v_n_2399_);
v___x_2407_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2407_, 0, v___x_2405_);
lean_ctor_set(v___x_2407_, 1, v___x_2406_);
v___x_2408_ = lean_obj_once(&l_Lean_ensureNoOverload___redArg___closed__4, &l_Lean_ensureNoOverload___redArg___closed__4_once, _init_l_Lean_ensureNoOverload___redArg___closed__4);
v___x_2409_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2409_, 0, v___x_2407_);
lean_ctor_set(v___x_2409_, 1, v___x_2408_);
v___x_2410_ = lean_box(0);
v___x_2411_ = l_List_mapTR_loop___redArg(v___f_2403_, v_cs_2400_, v___x_2410_);
v___x_2412_ = ((lean_object*)(l_Lean_ensureNoOverload___redArg___closed__5));
v___x_2413_ = l_List_mapTR_loop___redArg(v___x_2412_, v___x_2411_, v___x_2410_);
v___x_2414_ = l_Lean_MessageData_ofList(v___x_2413_);
v___x_2415_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2415_, 0, v___x_2409_);
lean_ctor_set(v___x_2415_, 1, v___x_2414_);
v___x_2416_ = l_Lean_throwError___redArg(v_inst_2397_, v_inst_2398_, v___x_2415_);
return v___x_2416_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNoOverload(lean_object* v_m_2420_, lean_object* v_inst_2421_, lean_object* v_inst_2422_, lean_object* v_n_2423_, lean_object* v_cs_2424_){
_start:
{
lean_object* v___x_2425_; 
v___x_2425_ = l_Lean_ensureNoOverload___redArg(v_inst_2421_, v_inst_2422_, v_n_2423_, v_cs_2424_);
return v___x_2425_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverloadCore___redArg___lam__0(lean_object* v_inst_2426_, lean_object* v_inst_2427_, lean_object* v_n_2428_, lean_object* v_____do__lift_2429_){
_start:
{
lean_object* v___x_2430_; 
v___x_2430_ = l_Lean_ensureNoOverload___redArg(v_inst_2426_, v_inst_2427_, v_n_2428_, v_____do__lift_2429_);
return v___x_2430_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverloadCore___redArg(lean_object* v_inst_2431_, lean_object* v_inst_2432_, lean_object* v_inst_2433_, lean_object* v_inst_2434_, lean_object* v_inst_2435_, lean_object* v_inst_2436_, lean_object* v_inst_2437_, lean_object* v_n_2438_){
_start:
{
lean_object* v_toBind_2439_; lean_object* v___f_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; 
v_toBind_2439_ = lean_ctor_get(v_inst_2431_, 1);
lean_inc(v_toBind_2439_);
lean_inc(v_n_2438_);
lean_inc_ref(v_inst_2437_);
lean_inc_ref(v_inst_2431_);
v___f_2440_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalConstNoOverloadCore___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2440_, 0, v_inst_2431_);
lean_closure_set(v___f_2440_, 1, v_inst_2437_);
lean_closure_set(v___f_2440_, 2, v_n_2438_);
v___x_2441_ = l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___redArg(v_inst_2431_, v_inst_2432_, v_inst_2433_, v_inst_2434_, v_inst_2435_, v_inst_2436_, v_inst_2437_, v_n_2438_);
v___x_2442_ = lean_apply_4(v_toBind_2439_, lean_box(0), lean_box(0), v___x_2441_, v___f_2440_);
return v___x_2442_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverloadCore(lean_object* v_m_2443_, lean_object* v_inst_2444_, lean_object* v_inst_2445_, lean_object* v_inst_2446_, lean_object* v_inst_2447_, lean_object* v_inst_2448_, lean_object* v_inst_2449_, lean_object* v_inst_2450_, lean_object* v_n_2451_){
_start:
{
lean_object* v___x_2452_; 
v___x_2452_ = l_Lean_resolveGlobalConstNoOverloadCore___redArg(v_inst_2444_, v_inst_2445_, v_inst_2446_, v_inst_2447_, v_inst_2448_, v_inst_2449_, v_inst_2450_, v_n_2451_);
return v___x_2452_;
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___redArg___lam__0(lean_object* v_x_2453_){
_start:
{
if (lean_obj_tag(v_x_2453_) == 1)
{
lean_object* v_fields_2454_; 
v_fields_2454_ = lean_ctor_get(v_x_2453_, 1);
if (lean_obj_tag(v_fields_2454_) == 0)
{
lean_object* v_n_2455_; lean_object* v___x_2456_; 
v_n_2455_ = lean_ctor_get(v_x_2453_, 0);
lean_inc(v_n_2455_);
v___x_2456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2456_, 0, v_n_2455_);
return v___x_2456_;
}
else
{
lean_object* v___x_2457_; 
v___x_2457_ = lean_box(0);
return v___x_2457_;
}
}
else
{
lean_object* v___x_2458_; 
v___x_2458_ = lean_box(0);
return v___x_2458_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___redArg___lam__0___boxed(lean_object* v_x_2459_){
_start:
{
lean_object* v_res_2460_; 
v_res_2460_ = l_Lean_preprocessSyntaxAndResolve___redArg___lam__0(v_x_2459_);
lean_dec_ref(v_x_2459_);
return v_res_2460_;
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___redArg___lam__1(lean_object* v_stx_2461_, lean_object* v_withRef_2462_, lean_object* v___x_2463_, lean_object* v_oldRef_2464_){
_start:
{
lean_object* v_ref_2465_; lean_object* v___x_2466_; 
v_ref_2465_ = l_Lean_replaceRef(v_stx_2461_, v_oldRef_2464_);
v___x_2466_ = lean_apply_3(v_withRef_2462_, lean_box(0), v_ref_2465_, v___x_2463_);
return v___x_2466_;
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___redArg___lam__1___boxed(lean_object* v_stx_2467_, lean_object* v_withRef_2468_, lean_object* v___x_2469_, lean_object* v_oldRef_2470_){
_start:
{
lean_object* v_res_2471_; 
v_res_2471_ = l_Lean_preprocessSyntaxAndResolve___redArg___lam__1(v_stx_2467_, v_withRef_2468_, v___x_2469_, v_oldRef_2470_);
lean_dec(v_oldRef_2470_);
lean_dec(v_stx_2467_);
return v_res_2471_;
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___redArg(lean_object* v_inst_2473_, lean_object* v_inst_2474_, lean_object* v_stx_2475_, lean_object* v_k_2476_){
_start:
{
if (lean_obj_tag(v_stx_2475_) == 3)
{
lean_object* v_val_2477_; lean_object* v_preresolved_2478_; lean_object* v___f_2479_; lean_object* v___x_2480_; lean_object* v_pre_2481_; uint8_t v___x_2482_; 
v_val_2477_ = lean_ctor_get(v_stx_2475_, 2);
v_preresolved_2478_ = lean_ctor_get(v_stx_2475_, 3);
v___f_2479_ = ((lean_object*)(l_Lean_preprocessSyntaxAndResolve___redArg___closed__0));
v___x_2480_ = ((lean_object*)(l_Lean_resolveNamespace___redArg___closed__1));
lean_inc(v_preresolved_2478_);
v_pre_2481_ = l_List_filterMapTR_go___redArg(v___f_2479_, v_preresolved_2478_, v___x_2480_);
v___x_2482_ = l_List_isEmpty___redArg(v_pre_2481_);
if (v___x_2482_ == 0)
{
lean_object* v_toApplicative_2483_; lean_object* v_toPure_2484_; lean_object* v___x_2485_; 
lean_dec_ref_known(v_stx_2475_, 4);
lean_dec(v_k_2476_);
lean_dec_ref(v_inst_2474_);
v_toApplicative_2483_ = lean_ctor_get(v_inst_2473_, 0);
lean_inc_ref(v_toApplicative_2483_);
lean_dec_ref(v_inst_2473_);
v_toPure_2484_ = lean_ctor_get(v_toApplicative_2483_, 1);
lean_inc(v_toPure_2484_);
lean_dec_ref(v_toApplicative_2483_);
v___x_2485_ = lean_apply_2(v_toPure_2484_, lean_box(0), v_pre_2481_);
return v___x_2485_;
}
else
{
lean_object* v_toMonadRef_2486_; lean_object* v_toBind_2487_; lean_object* v_getRef_2488_; lean_object* v_withRef_2489_; lean_object* v___x_2490_; lean_object* v___f_2491_; lean_object* v___x_2492_; 
lean_dec(v_pre_2481_);
v_toMonadRef_2486_ = lean_ctor_get(v_inst_2474_, 1);
lean_inc_ref(v_toMonadRef_2486_);
lean_dec_ref(v_inst_2474_);
v_toBind_2487_ = lean_ctor_get(v_inst_2473_, 1);
lean_inc(v_toBind_2487_);
lean_dec_ref(v_inst_2473_);
v_getRef_2488_ = lean_ctor_get(v_toMonadRef_2486_, 0);
lean_inc(v_getRef_2488_);
v_withRef_2489_ = lean_ctor_get(v_toMonadRef_2486_, 1);
lean_inc(v_withRef_2489_);
lean_dec_ref(v_toMonadRef_2486_);
lean_inc(v_val_2477_);
v___x_2490_ = lean_apply_1(v_k_2476_, v_val_2477_);
v___f_2491_ = lean_alloc_closure((void*)(l_Lean_preprocessSyntaxAndResolve___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_2491_, 0, v_stx_2475_);
lean_closure_set(v___f_2491_, 1, v_withRef_2489_);
lean_closure_set(v___f_2491_, 2, v___x_2490_);
v___x_2492_ = lean_apply_4(v_toBind_2487_, lean_box(0), lean_box(0), v_getRef_2488_, v___f_2491_);
return v___x_2492_;
}
}
else
{
lean_object* v___x_2493_; lean_object* v___x_2494_; 
lean_dec(v_k_2476_);
v___x_2493_ = lean_obj_once(&l_Lean_resolveNamespace___redArg___closed__4, &l_Lean_resolveNamespace___redArg___closed__4_once, _init_l_Lean_resolveNamespace___redArg___closed__4);
v___x_2494_ = l_Lean_throwErrorAt___redArg(v_inst_2473_, v_inst_2474_, v_stx_2475_, v___x_2493_);
return v___x_2494_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve(lean_object* v_m_2495_, lean_object* v_inst_2496_, lean_object* v_inst_2497_, lean_object* v_stx_2498_, lean_object* v_k_2499_){
_start:
{
lean_object* v___x_2500_; 
v___x_2500_ = l_Lean_preprocessSyntaxAndResolve___redArg(v_inst_2496_, v_inst_2497_, v_stx_2498_, v_k_2499_);
return v___x_2500_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst___redArg(lean_object* v_inst_2501_, lean_object* v_inst_2502_, lean_object* v_inst_2503_, lean_object* v_inst_2504_, lean_object* v_inst_2505_, lean_object* v_inst_2506_, lean_object* v_inst_2507_, lean_object* v_stx_2508_){
_start:
{
lean_object* v___x_2509_; lean_object* v___x_2510_; 
lean_inc_ref(v_inst_2507_);
lean_inc_ref(v_inst_2501_);
v___x_2509_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore), 9, 8);
lean_closure_set(v___x_2509_, 0, lean_box(0));
lean_closure_set(v___x_2509_, 1, v_inst_2501_);
lean_closure_set(v___x_2509_, 2, v_inst_2502_);
lean_closure_set(v___x_2509_, 3, v_inst_2503_);
lean_closure_set(v___x_2509_, 4, v_inst_2504_);
lean_closure_set(v___x_2509_, 5, v_inst_2505_);
lean_closure_set(v___x_2509_, 6, v_inst_2506_);
lean_closure_set(v___x_2509_, 7, v_inst_2507_);
v___x_2510_ = l_Lean_preprocessSyntaxAndResolve___redArg(v_inst_2501_, v_inst_2507_, v_stx_2508_, v___x_2509_);
return v___x_2510_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst(lean_object* v_m_2511_, lean_object* v_inst_2512_, lean_object* v_inst_2513_, lean_object* v_inst_2514_, lean_object* v_inst_2515_, lean_object* v_inst_2516_, lean_object* v_inst_2517_, lean_object* v_inst_2518_, lean_object* v_stx_2519_){
_start:
{
lean_object* v___x_2520_; 
v___x_2520_ = l_Lean_resolveGlobalConst___redArg(v_inst_2512_, v_inst_2513_, v_inst_2514_, v_inst_2515_, v_inst_2516_, v_inst_2517_, v_inst_2518_, v_stx_2519_);
return v___x_2520_;
}
}
static lean_object* _init_l_Lean_ensureNonAmbiguous___redArg___closed__1(void){
_start:
{
lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; 
v___x_2522_ = ((lean_object*)(l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__2));
v___x_2523_ = lean_unsigned_to_nat(11u);
v___x_2524_ = lean_unsigned_to_nat(429u);
v___x_2525_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___redArg___closed__0));
v___x_2526_ = ((lean_object*)(l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__0));
v___x_2527_ = l_mkPanicMessageWithDecl(v___x_2526_, v___x_2525_, v___x_2524_, v___x_2523_, v___x_2522_);
return v___x_2527_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNonAmbiguous___redArg(lean_object* v_inst_2531_, lean_object* v_inst_2532_, lean_object* v_id_2533_, lean_object* v_cs_2534_){
_start:
{
if (lean_obj_tag(v_cs_2534_) == 0)
{
lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; 
lean_dec(v_id_2533_);
lean_dec_ref(v_inst_2532_);
v___x_2535_ = lean_box(0);
v___x_2536_ = l_instInhabitedOfMonad___redArg(v_inst_2531_, v___x_2535_);
v___x_2537_ = lean_obj_once(&l_Lean_ensureNonAmbiguous___redArg___closed__1, &l_Lean_ensureNonAmbiguous___redArg___closed__1_once, _init_l_Lean_ensureNonAmbiguous___redArg___closed__1);
v___x_2538_ = l_panic___redArg(v___x_2536_, v___x_2537_);
lean_dec(v___x_2536_);
return v___x_2538_;
}
else
{
lean_object* v_tail_2539_; 
v_tail_2539_ = lean_ctor_get(v_cs_2534_, 1);
if (lean_obj_tag(v_tail_2539_) == 0)
{
lean_object* v_toApplicative_2540_; lean_object* v_toPure_2541_; lean_object* v_head_2542_; lean_object* v___x_2543_; 
v_toApplicative_2540_ = lean_ctor_get(v_inst_2531_, 0);
lean_inc_ref(v_toApplicative_2540_);
lean_dec(v_id_2533_);
lean_dec_ref(v_inst_2532_);
lean_dec_ref(v_inst_2531_);
v_toPure_2541_ = lean_ctor_get(v_toApplicative_2540_, 1);
lean_inc(v_toPure_2541_);
lean_dec_ref(v_toApplicative_2540_);
v_head_2542_ = lean_ctor_get(v_cs_2534_, 0);
lean_inc(v_head_2542_);
lean_dec_ref_known(v_cs_2534_, 2);
v___x_2543_ = lean_apply_2(v_toPure_2541_, lean_box(0), v_head_2542_);
return v___x_2543_;
}
else
{
lean_object* v___f_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; uint8_t v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; 
v___f_2544_ = ((lean_object*)(l_Lean_ensureNoOverload___redArg___closed__0));
v___x_2545_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___redArg___closed__2));
v___x_2546_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___redArg___closed__3));
v___x_2547_ = lean_box(0);
v___x_2548_ = 0;
lean_inc(v_id_2533_);
v___x_2549_ = l_Lean_Syntax_formatStx(v_id_2533_, v___x_2547_, v___x_2548_);
v___x_2550_ = l_Std_Format_defWidth;
v___x_2551_ = lean_unsigned_to_nat(0u);
v___x_2552_ = l_Std_Format_pretty(v___x_2549_, v___x_2550_, v___x_2551_, v___x_2551_);
v___x_2553_ = lean_string_append(v___x_2546_, v___x_2552_);
lean_dec_ref(v___x_2552_);
v___x_2554_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___redArg___closed__4));
v___x_2555_ = lean_string_append(v___x_2553_, v___x_2554_);
v___x_2556_ = lean_box(0);
v___x_2557_ = l_List_mapTR_loop___redArg(v___f_2544_, v_cs_2534_, v___x_2556_);
v___x_2558_ = l_List_toString___redArg(v___x_2545_, v___x_2557_);
v___x_2559_ = lean_string_append(v___x_2555_, v___x_2558_);
lean_dec_ref(v___x_2558_);
v___x_2560_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2560_, 0, v___x_2559_);
v___x_2561_ = l_Lean_MessageData_ofFormat(v___x_2560_);
v___x_2562_ = l_Lean_throwErrorAt___redArg(v_inst_2531_, v_inst_2532_, v_id_2533_, v___x_2561_);
return v___x_2562_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNonAmbiguous(lean_object* v_m_2563_, lean_object* v_inst_2564_, lean_object* v_inst_2565_, lean_object* v_id_2566_, lean_object* v_cs_2567_){
_start:
{
lean_object* v___x_2568_; 
v___x_2568_ = l_Lean_ensureNonAmbiguous___redArg(v_inst_2564_, v_inst_2565_, v_id_2566_, v_cs_2567_);
return v___x_2568_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverload___redArg___lam__0(lean_object* v_inst_2569_, lean_object* v_inst_2570_, lean_object* v_id_2571_, lean_object* v_____do__lift_2572_){
_start:
{
lean_object* v___x_2573_; 
v___x_2573_ = l_Lean_ensureNonAmbiguous___redArg(v_inst_2569_, v_inst_2570_, v_id_2571_, v_____do__lift_2572_);
return v___x_2573_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverload___redArg(lean_object* v_inst_2574_, lean_object* v_inst_2575_, lean_object* v_inst_2576_, lean_object* v_inst_2577_, lean_object* v_inst_2578_, lean_object* v_inst_2579_, lean_object* v_inst_2580_, lean_object* v_id_2581_){
_start:
{
lean_object* v_toBind_2582_; lean_object* v___f_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; 
v_toBind_2582_ = lean_ctor_get(v_inst_2574_, 1);
lean_inc(v_toBind_2582_);
lean_inc(v_id_2581_);
lean_inc_ref(v_inst_2580_);
lean_inc_ref(v_inst_2574_);
v___f_2583_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalConstNoOverload___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2583_, 0, v_inst_2574_);
lean_closure_set(v___f_2583_, 1, v_inst_2580_);
lean_closure_set(v___f_2583_, 2, v_id_2581_);
v___x_2584_ = l_Lean_resolveGlobalConst___redArg(v_inst_2574_, v_inst_2575_, v_inst_2576_, v_inst_2577_, v_inst_2578_, v_inst_2579_, v_inst_2580_, v_id_2581_);
v___x_2585_ = lean_apply_4(v_toBind_2582_, lean_box(0), lean_box(0), v___x_2584_, v___f_2583_);
return v___x_2585_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverload(lean_object* v_m_2586_, lean_object* v_inst_2587_, lean_object* v_inst_2588_, lean_object* v_inst_2589_, lean_object* v_inst_2590_, lean_object* v_inst_2591_, lean_object* v_inst_2592_, lean_object* v_inst_2593_, lean_object* v_id_2594_){
_start:
{
lean_object* v___x_2595_; 
v___x_2595_ = l_Lean_resolveGlobalConstNoOverload___redArg(v_inst_2587_, v_inst_2588_, v_inst_2589_, v_inst_2590_, v_inst_2591_, v_inst_2592_, v_inst_2593_, v_id_2594_);
return v___x_2595_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__0(lean_object* v___f_2596_, lean_object* v___f_2597_, uint8_t v_globalDeclFoundNext_2598_, uint8_t v_globalDeclFound_2599_, lean_object* v_r_2600_){
_start:
{
lean_object* v___x_2601_; lean_object* v_r_2602_; uint8_t v___x_2603_; 
v___x_2601_ = lean_box(0);
v_r_2602_ = l_List_filterTR_loop___redArg(v___f_2596_, v_r_2600_, v___x_2601_);
v___x_2603_ = l_List_isEmpty___redArg(v_r_2602_);
lean_dec(v_r_2602_);
if (v___x_2603_ == 0)
{
lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; 
v___x_2604_ = lean_box(0);
v___x_2605_ = lean_box(v_globalDeclFoundNext_2598_);
v___x_2606_ = lean_apply_2(v___f_2597_, v___x_2604_, v___x_2605_);
return v___x_2606_;
}
else
{
lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; 
v___x_2607_ = lean_box(0);
v___x_2608_ = lean_box(v_globalDeclFound_2599_);
v___x_2609_ = lean_apply_2(v___f_2597_, v___x_2607_, v___x_2608_);
return v___x_2609_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__0___boxed(lean_object* v___f_2610_, lean_object* v___f_2611_, lean_object* v_globalDeclFoundNext_2612_, lean_object* v_globalDeclFound_2613_, lean_object* v_r_2614_){
_start:
{
uint8_t v_globalDeclFoundNext_boxed_2615_; uint8_t v_globalDeclFound_boxed_2616_; lean_object* v_res_2617_; 
v_globalDeclFoundNext_boxed_2615_ = lean_unbox(v_globalDeclFoundNext_2612_);
v_globalDeclFound_boxed_2616_ = lean_unbox(v_globalDeclFound_2613_);
v_res_2617_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__0(v___f_2610_, v___f_2611_, v_globalDeclFoundNext_boxed_2615_, v_globalDeclFound_boxed_2616_, v_r_2614_);
return v_res_2617_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__1___boxed(lean_object* v_str_2618_, lean_object* v_projs_2619_, lean_object* v_inst_2620_, lean_object* v_inst_2621_, lean_object* v_inst_2622_, lean_object* v_inst_2623_, lean_object* v_inst_2624_, lean_object* v_inst_2625_, lean_object* v_view_2626_, lean_object* v_findLocalDecl_x3f_2627_, lean_object* v_pre_2628_, lean_object* v_____r_2629_, lean_object* v_globalDeclFoundNext_2630_){
_start:
{
uint8_t v_globalDeclFoundNext_boxed_2631_; lean_object* v_res_2632_; 
v_globalDeclFoundNext_boxed_2631_ = lean_unbox(v_globalDeclFoundNext_2630_);
v_res_2632_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__1(v_str_2618_, v_projs_2619_, v_inst_2620_, v_inst_2621_, v_inst_2622_, v_inst_2623_, v_inst_2624_, v_inst_2625_, v_view_2626_, v_findLocalDecl_x3f_2627_, v_pre_2628_, v_____r_2629_, v_globalDeclFoundNext_boxed_2631_);
return v_res_2632_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg(lean_object* v_inst_2633_, lean_object* v_inst_2634_, lean_object* v_inst_2635_, lean_object* v_inst_2636_, lean_object* v_inst_2637_, lean_object* v_inst_2638_, lean_object* v_view_2639_, lean_object* v_findLocalDecl_x3f_2640_, lean_object* v_n_2641_, lean_object* v_projs_2642_, uint8_t v_globalDeclFound_2643_){
_start:
{
lean_object* v_toApplicative_2644_; lean_object* v_imported_2645_; lean_object* v_ctx_2646_; lean_object* v_scopes_2647_; lean_object* v_toBind_2648_; lean_object* v_toPure_2649_; lean_object* v___f_2650_; lean_object* v_givenNameView_2651_; uint8_t v___y_2653_; 
v_toApplicative_2644_ = lean_ctor_get(v_inst_2633_, 0);
v_imported_2645_ = lean_ctor_get(v_view_2639_, 1);
v_ctx_2646_ = lean_ctor_get(v_view_2639_, 2);
v_scopes_2647_ = lean_ctor_get(v_view_2639_, 3);
v_toBind_2648_ = lean_ctor_get(v_inst_2633_, 1);
v_toPure_2649_ = lean_ctor_get(v_toApplicative_2644_, 1);
v___f_2650_ = ((lean_object*)(l_Lean_filterFieldList___redArg___closed__0));
lean_inc(v_scopes_2647_);
lean_inc(v_ctx_2646_);
lean_inc(v_imported_2645_);
lean_inc(v_n_2641_);
v_givenNameView_2651_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_givenNameView_2651_, 0, v_n_2641_);
lean_ctor_set(v_givenNameView_2651_, 1, v_imported_2645_);
lean_ctor_set(v_givenNameView_2651_, 2, v_ctx_2646_);
lean_ctor_set(v_givenNameView_2651_, 3, v_scopes_2647_);
if (v_globalDeclFound_2643_ == 0)
{
v___y_2653_ = v_globalDeclFound_2643_;
goto v___jp_2652_;
}
else
{
uint8_t v___x_2689_; uint8_t v___x_2690_; 
v___x_2689_ = l_List_isEmpty___redArg(v_projs_2642_);
v___x_2690_ = lean_bool_not(v___x_2689_);
v___y_2653_ = v___x_2690_;
goto v___jp_2652_;
}
v___jp_2652_:
{
lean_object* v___x_2654_; lean_object* v___x_2655_; 
v___x_2654_ = lean_box(v___y_2653_);
lean_inc_ref(v_findLocalDecl_x3f_2640_);
lean_inc_ref(v_givenNameView_2651_);
v___x_2655_ = lean_apply_2(v_findLocalDecl_x3f_2640_, v_givenNameView_2651_, v___x_2654_);
if (lean_obj_tag(v___x_2655_) == 0)
{
if (lean_obj_tag(v_n_2641_) == 1)
{
lean_object* v_pre_2656_; lean_object* v_str_2657_; lean_object* v___f_2658_; 
v_pre_2656_ = lean_ctor_get(v_n_2641_, 0);
lean_inc_n(v_pre_2656_, 2);
v_str_2657_ = lean_ctor_get(v_n_2641_, 1);
lean_inc_ref_n(v_str_2657_, 2);
lean_dec_ref_known(v_n_2641_, 2);
lean_inc_ref(v_findLocalDecl_x3f_2640_);
lean_inc_ref(v_view_2639_);
lean_inc(v_inst_2638_);
lean_inc_ref(v_inst_2637_);
lean_inc(v_inst_2636_);
lean_inc_ref(v_inst_2635_);
lean_inc_ref(v_inst_2634_);
lean_inc_ref(v_inst_2633_);
lean_inc(v_projs_2642_);
v___f_2658_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__1___boxed), 13, 11);
lean_closure_set(v___f_2658_, 0, v_str_2657_);
lean_closure_set(v___f_2658_, 1, v_projs_2642_);
lean_closure_set(v___f_2658_, 2, v_inst_2633_);
lean_closure_set(v___f_2658_, 3, v_inst_2634_);
lean_closure_set(v___f_2658_, 4, v_inst_2635_);
lean_closure_set(v___f_2658_, 5, v_inst_2636_);
lean_closure_set(v___f_2658_, 6, v_inst_2637_);
lean_closure_set(v___f_2658_, 7, v_inst_2638_);
lean_closure_set(v___f_2658_, 8, v_view_2639_);
lean_closure_set(v___f_2658_, 9, v_findLocalDecl_x3f_2640_);
lean_closure_set(v___f_2658_, 10, v_pre_2656_);
if (v_globalDeclFound_2643_ == 0)
{
uint8_t v_globalDeclFoundNext_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___f_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; 
lean_inc(v_toBind_2648_);
lean_dec_ref(v_str_2657_);
lean_dec(v_pre_2656_);
lean_dec(v_projs_2642_);
lean_dec_ref(v_findLocalDecl_x3f_2640_);
lean_dec_ref(v_view_2639_);
v_globalDeclFoundNext_2659_ = 1;
v___x_2660_ = lean_box(v_globalDeclFoundNext_2659_);
v___x_2661_ = lean_box(v_globalDeclFound_2643_);
v___f_2662_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2662_, 0, v___f_2650_);
lean_closure_set(v___f_2662_, 1, v___f_2658_);
lean_closure_set(v___f_2662_, 2, v___x_2660_);
lean_closure_set(v___f_2662_, 3, v___x_2661_);
v___x_2663_ = l_Lean_MacroScopesView_review(v_givenNameView_2651_);
v___x_2664_ = l_Lean_resolveGlobalName___redArg(v_inst_2633_, v_inst_2634_, v_inst_2635_, v_inst_2636_, v_inst_2637_, v_inst_2638_, v___x_2663_, v_globalDeclFound_2643_);
v___x_2665_ = lean_apply_4(v_toBind_2648_, lean_box(0), lean_box(0), v___x_2664_, v___f_2662_);
return v___x_2665_;
}
else
{
lean_object* v___x_2666_; lean_object* v___x_2667_; 
lean_dec_ref(v___f_2658_);
lean_dec_ref_known(v_givenNameView_2651_, 4);
v___x_2666_ = lean_box(0);
v___x_2667_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__1(v_str_2657_, v_projs_2642_, v_inst_2633_, v_inst_2634_, v_inst_2635_, v_inst_2636_, v_inst_2637_, v_inst_2638_, v_view_2639_, v_findLocalDecl_x3f_2640_, v_pre_2656_, v___x_2666_, v_globalDeclFound_2643_);
return v___x_2667_;
}
}
else
{
lean_object* v___x_2668_; lean_object* v___x_2669_; 
lean_inc(v_toPure_2649_);
lean_dec_ref_known(v_givenNameView_2651_, 4);
lean_dec(v_projs_2642_);
lean_dec(v_n_2641_);
lean_dec_ref(v_findLocalDecl_x3f_2640_);
lean_dec_ref(v_view_2639_);
lean_dec(v_inst_2638_);
lean_dec_ref(v_inst_2637_);
lean_dec(v_inst_2636_);
lean_dec_ref(v_inst_2635_);
lean_dec_ref(v_inst_2634_);
lean_dec_ref(v_inst_2633_);
v___x_2668_ = lean_box(0);
v___x_2669_ = lean_apply_2(v_toPure_2649_, lean_box(0), v___x_2668_);
return v___x_2669_;
}
}
else
{
lean_object* v___x_2671_; uint8_t v_isShared_2672_; uint8_t v_isSharedCheck_2686_; 
lean_inc(v_toPure_2649_);
lean_dec_ref_known(v_givenNameView_2651_, 4);
lean_dec(v_n_2641_);
lean_dec_ref(v_findLocalDecl_x3f_2640_);
lean_dec_ref(v_view_2639_);
lean_dec(v_inst_2638_);
lean_dec_ref(v_inst_2637_);
lean_dec(v_inst_2636_);
lean_dec_ref(v_inst_2635_);
lean_dec_ref(v_inst_2634_);
v_isSharedCheck_2686_ = !lean_is_exclusive(v_inst_2633_);
if (v_isSharedCheck_2686_ == 0)
{
lean_object* v_unused_2687_; lean_object* v_unused_2688_; 
v_unused_2687_ = lean_ctor_get(v_inst_2633_, 1);
lean_dec(v_unused_2687_);
v_unused_2688_ = lean_ctor_get(v_inst_2633_, 0);
lean_dec(v_unused_2688_);
v___x_2671_ = v_inst_2633_;
v_isShared_2672_ = v_isSharedCheck_2686_;
goto v_resetjp_2670_;
}
else
{
lean_dec(v_inst_2633_);
v___x_2671_ = lean_box(0);
v_isShared_2672_ = v_isSharedCheck_2686_;
goto v_resetjp_2670_;
}
v_resetjp_2670_:
{
lean_object* v_val_2673_; lean_object* v___x_2675_; uint8_t v_isShared_2676_; uint8_t v_isSharedCheck_2685_; 
v_val_2673_ = lean_ctor_get(v___x_2655_, 0);
v_isSharedCheck_2685_ = !lean_is_exclusive(v___x_2655_);
if (v_isSharedCheck_2685_ == 0)
{
v___x_2675_ = v___x_2655_;
v_isShared_2676_ = v_isSharedCheck_2685_;
goto v_resetjp_2674_;
}
else
{
lean_inc(v_val_2673_);
lean_dec(v___x_2655_);
v___x_2675_ = lean_box(0);
v_isShared_2676_ = v_isSharedCheck_2685_;
goto v_resetjp_2674_;
}
v_resetjp_2674_:
{
lean_object* v___x_2677_; lean_object* v___x_2679_; 
v___x_2677_ = l_Lean_LocalDecl_toExpr(v_val_2673_);
if (v_isShared_2672_ == 0)
{
lean_ctor_set(v___x_2671_, 1, v_projs_2642_);
lean_ctor_set(v___x_2671_, 0, v___x_2677_);
v___x_2679_ = v___x_2671_;
goto v_reusejp_2678_;
}
else
{
lean_object* v_reuseFailAlloc_2684_; 
v_reuseFailAlloc_2684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2684_, 0, v___x_2677_);
lean_ctor_set(v_reuseFailAlloc_2684_, 1, v_projs_2642_);
v___x_2679_ = v_reuseFailAlloc_2684_;
goto v_reusejp_2678_;
}
v_reusejp_2678_:
{
lean_object* v___x_2681_; 
if (v_isShared_2676_ == 0)
{
lean_ctor_set(v___x_2675_, 0, v___x_2679_);
v___x_2681_ = v___x_2675_;
goto v_reusejp_2680_;
}
else
{
lean_object* v_reuseFailAlloc_2683_; 
v_reuseFailAlloc_2683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2683_, 0, v___x_2679_);
v___x_2681_ = v_reuseFailAlloc_2683_;
goto v_reusejp_2680_;
}
v_reusejp_2680_:
{
lean_object* v___x_2682_; 
v___x_2682_ = lean_apply_2(v_toPure_2649_, lean_box(0), v___x_2681_);
return v___x_2682_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__1(lean_object* v_str_2691_, lean_object* v_projs_2692_, lean_object* v_inst_2693_, lean_object* v_inst_2694_, lean_object* v_inst_2695_, lean_object* v_inst_2696_, lean_object* v_inst_2697_, lean_object* v_inst_2698_, lean_object* v_view_2699_, lean_object* v_findLocalDecl_x3f_2700_, lean_object* v_pre_2701_, lean_object* v_____r_2702_, uint8_t v_globalDeclFoundNext_2703_){
_start:
{
lean_object* v___x_2704_; lean_object* v___x_2705_; 
v___x_2704_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2704_, 0, v_str_2691_);
lean_ctor_set(v___x_2704_, 1, v_projs_2692_);
v___x_2705_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg(v_inst_2693_, v_inst_2694_, v_inst_2695_, v_inst_2696_, v_inst_2697_, v_inst_2698_, v_view_2699_, v_findLocalDecl_x3f_2700_, v_pre_2701_, v___x_2704_, v_globalDeclFoundNext_2703_);
return v___x_2705_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___boxed(lean_object* v_inst_2706_, lean_object* v_inst_2707_, lean_object* v_inst_2708_, lean_object* v_inst_2709_, lean_object* v_inst_2710_, lean_object* v_inst_2711_, lean_object* v_view_2712_, lean_object* v_findLocalDecl_x3f_2713_, lean_object* v_n_2714_, lean_object* v_projs_2715_, lean_object* v_globalDeclFound_2716_){
_start:
{
uint8_t v_globalDeclFound_boxed_2717_; lean_object* v_res_2718_; 
v_globalDeclFound_boxed_2717_ = lean_unbox(v_globalDeclFound_2716_);
v_res_2718_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg(v_inst_2706_, v_inst_2707_, v_inst_2708_, v_inst_2709_, v_inst_2710_, v_inst_2711_, v_view_2712_, v_findLocalDecl_x3f_2713_, v_n_2714_, v_projs_2715_, v_globalDeclFound_boxed_2717_);
return v_res_2718_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop(lean_object* v_m_2719_, lean_object* v_inst_2720_, lean_object* v_inst_2721_, lean_object* v_inst_2722_, lean_object* v_inst_2723_, lean_object* v_inst_2724_, lean_object* v_inst_2725_, lean_object* v_view_2726_, lean_object* v_findLocalDecl_x3f_2727_, lean_object* v_n_2728_, lean_object* v_projs_2729_, uint8_t v_globalDeclFound_2730_){
_start:
{
lean_object* v___x_2731_; 
v___x_2731_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg(v_inst_2720_, v_inst_2721_, v_inst_2722_, v_inst_2723_, v_inst_2724_, v_inst_2725_, v_view_2726_, v_findLocalDecl_x3f_2727_, v_n_2728_, v_projs_2729_, v_globalDeclFound_2730_);
return v___x_2731_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___boxed(lean_object* v_m_2732_, lean_object* v_inst_2733_, lean_object* v_inst_2734_, lean_object* v_inst_2735_, lean_object* v_inst_2736_, lean_object* v_inst_2737_, lean_object* v_inst_2738_, lean_object* v_view_2739_, lean_object* v_findLocalDecl_x3f_2740_, lean_object* v_n_2741_, lean_object* v_projs_2742_, lean_object* v_globalDeclFound_2743_){
_start:
{
uint8_t v_globalDeclFound_boxed_2744_; lean_object* v_res_2745_; 
v_globalDeclFound_boxed_2744_ = lean_unbox(v_globalDeclFound_2743_);
v_res_2745_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop(v_m_2732_, v_inst_2733_, v_inst_2734_, v_inst_2735_, v_inst_2736_, v_inst_2737_, v_inst_2738_, v_view_2739_, v_findLocalDecl_x3f_2740_, v_n_2741_, v_projs_2742_, v_globalDeclFound_boxed_2744_);
return v_res_2745_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_go(lean_object* v_localDecl_2746_, lean_object* v_givenNameView_2747_, lean_object* v_fullDeclName_2748_, lean_object* v_ns_2749_){
_start:
{
lean_object* v_name_2750_; lean_object* v_imported_2751_; lean_object* v_ctx_2752_; lean_object* v_scopes_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; uint8_t v___x_2757_; 
v_name_2750_ = lean_ctor_get(v_givenNameView_2747_, 0);
v_imported_2751_ = lean_ctor_get(v_givenNameView_2747_, 1);
v_ctx_2752_ = lean_ctor_get(v_givenNameView_2747_, 2);
v_scopes_2753_ = lean_ctor_get(v_givenNameView_2747_, 3);
lean_inc(v_name_2750_);
lean_inc(v_ns_2749_);
v___x_2754_ = l_Lean_Name_append(v_ns_2749_, v_name_2750_);
lean_inc(v_scopes_2753_);
lean_inc(v_ctx_2752_);
lean_inc(v_imported_2751_);
v___x_2755_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2755_, 0, v___x_2754_);
lean_ctor_set(v___x_2755_, 1, v_imported_2751_);
lean_ctor_set(v___x_2755_, 2, v_ctx_2752_);
lean_ctor_set(v___x_2755_, 3, v_scopes_2753_);
v___x_2756_ = l_Lean_MacroScopesView_review(v___x_2755_);
v___x_2757_ = lean_name_eq(v___x_2756_, v_fullDeclName_2748_);
lean_dec(v___x_2756_);
if (v___x_2757_ == 0)
{
if (lean_obj_tag(v_ns_2749_) == 1)
{
lean_object* v_pre_2758_; 
v_pre_2758_ = lean_ctor_get(v_ns_2749_, 0);
lean_inc(v_pre_2758_);
lean_dec_ref_known(v_ns_2749_, 2);
v_ns_2749_ = v_pre_2758_;
goto _start;
}
else
{
lean_object* v___x_2760_; 
lean_dec(v_ns_2749_);
lean_dec_ref(v_givenNameView_2747_);
lean_dec_ref(v_localDecl_2746_);
v___x_2760_ = lean_box(0);
return v___x_2760_;
}
}
else
{
lean_object* v___x_2761_; 
lean_dec(v_ns_2749_);
lean_dec_ref(v_givenNameView_2747_);
v___x_2761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2761_, 0, v_localDecl_2746_);
return v___x_2761_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_go___boxed(lean_object* v_localDecl_2762_, lean_object* v_givenNameView_2763_, lean_object* v_fullDeclName_2764_, lean_object* v_ns_2765_){
_start:
{
lean_object* v_res_2766_; 
v_res_2766_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_go(v_localDecl_2762_, v_givenNameView_2763_, v_fullDeclName_2764_, v_ns_2765_);
lean_dec(v_fullDeclName_2764_);
return v_res_2766_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__0(lean_object* v_localDecl_2767_, lean_object* v_givenName_2768_){
_start:
{
lean_object* v___x_2769_; uint8_t v___x_2770_; 
v___x_2769_ = l_Lean_LocalDecl_userName(v_localDecl_2767_);
v___x_2770_ = lean_name_eq(v___x_2769_, v_givenName_2768_);
lean_dec(v___x_2769_);
if (v___x_2770_ == 0)
{
lean_object* v___x_2771_; 
lean_dec_ref(v_localDecl_2767_);
v___x_2771_ = lean_box(0);
return v___x_2771_;
}
else
{
lean_object* v___x_2772_; 
v___x_2772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2772_, 0, v_localDecl_2767_);
return v___x_2772_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__0___boxed(lean_object* v_localDecl_2773_, lean_object* v_givenName_2774_){
_start:
{
lean_object* v_res_2775_; 
v_res_2775_ = l_Lean_resolveLocalName___redArg___lam__0(v_localDecl_2773_, v_givenName_2774_);
lean_dec(v_givenName_2774_);
return v_res_2775_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__1(lean_object* v_matchLocalDecl_x3f_2776_, lean_object* v_givenName_2777_, uint8_t v_skipAuxDecl_2778_, lean_object* v___f_2779_, lean_object* v_auxDeclToFullName_2780_, lean_object* v_currNamespace_2781_, lean_object* v_givenNameView_2782_, lean_object* v_x_2783_){
_start:
{
if (lean_obj_tag(v_x_2783_) == 0)
{
lean_dec_ref(v_givenNameView_2782_);
lean_dec(v_currNamespace_2781_);
lean_dec(v_auxDeclToFullName_2780_);
lean_dec_ref(v___f_2779_);
lean_dec(v_givenName_2777_);
lean_dec_ref(v_matchLocalDecl_x3f_2776_);
return v_x_2783_;
}
else
{
lean_object* v_val_2784_; uint8_t v___x_2785_; 
v_val_2784_ = lean_ctor_get(v_x_2783_, 0);
v___x_2785_ = l_Lean_LocalDecl_isAuxDecl(v_val_2784_);
if (v___x_2785_ == 0)
{
lean_object* v___x_2786_; 
lean_inc(v_val_2784_);
lean_dec_ref_known(v_x_2783_, 1);
lean_dec_ref(v_givenNameView_2782_);
lean_dec(v_currNamespace_2781_);
lean_dec(v_auxDeclToFullName_2780_);
lean_dec_ref(v___f_2779_);
v___x_2786_ = lean_apply_2(v_matchLocalDecl_x3f_2776_, v_val_2784_, v_givenName_2777_);
return v___x_2786_;
}
else
{
uint8_t v___x_2787_; 
v___x_2787_ = lean_bool_not(v_skipAuxDecl_2778_);
if (v___x_2787_ == 0)
{
lean_object* v___x_2788_; 
lean_dec_ref_known(v_x_2783_, 1);
lean_dec_ref(v_givenNameView_2782_);
lean_dec(v_currNamespace_2781_);
lean_dec(v_auxDeclToFullName_2780_);
lean_dec_ref(v___f_2779_);
lean_dec(v_givenName_2777_);
lean_dec_ref(v_matchLocalDecl_x3f_2776_);
v___x_2788_ = lean_box(0);
return v___x_2788_;
}
else
{
lean_object* v___x_2789_; lean_object* v___x_2790_; 
v___x_2789_ = l_Lean_LocalDecl_fvarId(v_val_2784_);
v___x_2790_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v___f_2779_, v_auxDeclToFullName_2780_, v___x_2789_);
if (lean_obj_tag(v___x_2790_) == 1)
{
lean_object* v_val_2791_; lean_object* v_fullDeclView_2792_; lean_object* v___y_2794_; lean_object* v_name_2815_; lean_object* v___x_2816_; 
lean_dec(v_givenName_2777_);
lean_dec_ref(v_matchLocalDecl_x3f_2776_);
v_val_2791_ = lean_ctor_get(v___x_2790_, 0);
lean_inc(v_val_2791_);
lean_dec_ref_known(v___x_2790_, 1);
v_fullDeclView_2792_ = l_Lean_extractMacroScopes(v_val_2791_);
v_name_2815_ = lean_ctor_get(v_fullDeclView_2792_, 0);
lean_inc_n(v_name_2815_, 2);
v___x_2816_ = l_Lean_privateToUserName_x3f(v_name_2815_);
if (lean_obj_tag(v___x_2816_) == 0)
{
v___y_2794_ = v_name_2815_;
goto v___jp_2793_;
}
else
{
lean_object* v_val_2817_; 
lean_dec(v_name_2815_);
v_val_2817_ = lean_ctor_get(v___x_2816_, 0);
lean_inc(v_val_2817_);
lean_dec_ref_known(v___x_2816_, 1);
v___y_2794_ = v_val_2817_;
goto v___jp_2793_;
}
v___jp_2793_:
{
lean_object* v_imported_2795_; lean_object* v_ctx_2796_; lean_object* v_scopes_2797_; lean_object* v___x_2799_; uint8_t v_isShared_2800_; uint8_t v_isSharedCheck_2813_; 
v_imported_2795_ = lean_ctor_get(v_fullDeclView_2792_, 1);
v_ctx_2796_ = lean_ctor_get(v_fullDeclView_2792_, 2);
v_scopes_2797_ = lean_ctor_get(v_fullDeclView_2792_, 3);
v_isSharedCheck_2813_ = !lean_is_exclusive(v_fullDeclView_2792_);
if (v_isSharedCheck_2813_ == 0)
{
lean_object* v_unused_2814_; 
v_unused_2814_ = lean_ctor_get(v_fullDeclView_2792_, 0);
lean_dec(v_unused_2814_);
v___x_2799_ = v_fullDeclView_2792_;
v_isShared_2800_ = v_isSharedCheck_2813_;
goto v_resetjp_2798_;
}
else
{
lean_inc(v_scopes_2797_);
lean_inc(v_ctx_2796_);
lean_inc(v_imported_2795_);
lean_dec(v_fullDeclView_2792_);
v___x_2799_ = lean_box(0);
v_isShared_2800_ = v_isSharedCheck_2813_;
goto v_resetjp_2798_;
}
v_resetjp_2798_:
{
lean_object* v_fullDeclView_2802_; 
if (v_isShared_2800_ == 0)
{
lean_ctor_set(v___x_2799_, 0, v___y_2794_);
v_fullDeclView_2802_ = v___x_2799_;
goto v_reusejp_2801_;
}
else
{
lean_object* v_reuseFailAlloc_2812_; 
v_reuseFailAlloc_2812_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2812_, 0, v___y_2794_);
lean_ctor_set(v_reuseFailAlloc_2812_, 1, v_imported_2795_);
lean_ctor_set(v_reuseFailAlloc_2812_, 2, v_ctx_2796_);
lean_ctor_set(v_reuseFailAlloc_2812_, 3, v_scopes_2797_);
v_fullDeclView_2802_ = v_reuseFailAlloc_2812_;
goto v_reusejp_2801_;
}
v_reusejp_2801_:
{
lean_object* v_fullDeclName_2803_; uint8_t v___x_2804_; 
lean_inc_ref(v_fullDeclView_2802_);
v_fullDeclName_2803_ = l_Lean_MacroScopesView_review(v_fullDeclView_2802_);
v___x_2804_ = l_Lean_Name_isPrefixOf(v_currNamespace_2781_, v_fullDeclName_2803_);
if (v___x_2804_ == 0)
{
lean_object* v___x_2805_; 
lean_inc(v_val_2784_);
lean_dec_ref(v_fullDeclView_2802_);
lean_dec_ref_known(v_x_2783_, 1);
v___x_2805_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_go(v_val_2784_, v_givenNameView_2782_, v_fullDeclName_2803_, v_currNamespace_2781_);
lean_dec(v_fullDeclName_2803_);
return v___x_2805_;
}
else
{
lean_object* v___x_2806_; lean_object* v_localDeclNameView_2807_; uint8_t v___x_2808_; 
lean_dec(v_fullDeclName_2803_);
lean_dec(v_currNamespace_2781_);
v___x_2806_ = l_Lean_LocalDecl_userName(v_val_2784_);
v_localDeclNameView_2807_ = l_Lean_extractMacroScopes(v___x_2806_);
v___x_2808_ = l_Lean_MacroScopesView_isSuffixOf(v_localDeclNameView_2807_, v_givenNameView_2782_);
lean_dec_ref(v_localDeclNameView_2807_);
if (v___x_2808_ == 0)
{
lean_object* v___x_2809_; 
lean_dec_ref(v_fullDeclView_2802_);
lean_dec_ref_known(v_x_2783_, 1);
lean_dec_ref(v_givenNameView_2782_);
v___x_2809_ = lean_box(0);
return v___x_2809_;
}
else
{
uint8_t v___x_2810_; 
v___x_2810_ = l_Lean_MacroScopesView_isSuffixOf(v_givenNameView_2782_, v_fullDeclView_2802_);
lean_dec_ref(v_fullDeclView_2802_);
lean_dec_ref(v_givenNameView_2782_);
if (v___x_2810_ == 0)
{
lean_object* v___x_2811_; 
lean_dec_ref_known(v_x_2783_, 1);
v___x_2811_ = lean_box(0);
return v___x_2811_;
}
else
{
return v_x_2783_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2818_; 
lean_inc(v_val_2784_);
lean_dec(v___x_2790_);
lean_dec_ref_known(v_x_2783_, 1);
lean_dec_ref(v_givenNameView_2782_);
lean_dec(v_currNamespace_2781_);
v___x_2818_ = lean_apply_2(v_matchLocalDecl_x3f_2776_, v_val_2784_, v_givenName_2777_);
return v___x_2818_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__1___boxed(lean_object* v_matchLocalDecl_x3f_2819_, lean_object* v_givenName_2820_, lean_object* v_skipAuxDecl_2821_, lean_object* v___f_2822_, lean_object* v_auxDeclToFullName_2823_, lean_object* v_currNamespace_2824_, lean_object* v_givenNameView_2825_, lean_object* v_x_2826_){
_start:
{
uint8_t v_skipAuxDecl_boxed_2827_; lean_object* v_res_2828_; 
v_skipAuxDecl_boxed_2827_ = lean_unbox(v_skipAuxDecl_2821_);
v_res_2828_ = l_Lean_resolveLocalName___redArg___lam__1(v_matchLocalDecl_x3f_2819_, v_givenName_2820_, v_skipAuxDecl_boxed_2827_, v___f_2822_, v_auxDeclToFullName_2823_, v_currNamespace_2824_, v_givenNameView_2825_, v_x_2826_);
return v_res_2828_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__2(lean_object* v_localDecl_x3f_2829_, lean_object* v_matchLocalDecl_x3f_2830_, lean_object* v_givenName_2831_, lean_object* v_x_2832_){
_start:
{
if (lean_obj_tag(v_x_2832_) == 0)
{
lean_dec(v_givenName_2831_);
lean_dec_ref(v_matchLocalDecl_x3f_2830_);
return v_x_2832_;
}
else
{
lean_object* v_val_2833_; uint8_t v___x_2834_; 
v_val_2833_ = lean_ctor_get(v_x_2832_, 0);
lean_inc(v_val_2833_);
lean_dec_ref_known(v_x_2832_, 1);
v___x_2834_ = l_Lean_LocalDecl_isAuxDecl(v_val_2833_);
if (v___x_2834_ == 0)
{
lean_dec(v_val_2833_);
lean_dec(v_givenName_2831_);
lean_dec_ref(v_matchLocalDecl_x3f_2830_);
lean_inc(v_localDecl_x3f_2829_);
return v_localDecl_x3f_2829_;
}
else
{
lean_object* v___x_2835_; 
v___x_2835_ = lean_apply_2(v_matchLocalDecl_x3f_2830_, v_val_2833_, v_givenName_2831_);
return v___x_2835_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__2___boxed(lean_object* v_localDecl_x3f_2836_, lean_object* v_matchLocalDecl_x3f_2837_, lean_object* v_givenName_2838_, lean_object* v_x_2839_){
_start:
{
lean_object* v_res_2840_; 
v_res_2840_ = l_Lean_resolveLocalName___redArg___lam__2(v_localDecl_x3f_2836_, v_matchLocalDecl_x3f_2837_, v_givenName_2838_, v_x_2839_);
lean_dec(v_localDecl_x3f_2836_);
return v_res_2840_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__3(lean_object* v_lctx_2860_, lean_object* v_matchLocalDecl_x3f_2861_, lean_object* v___f_2862_, lean_object* v_auxDeclToFullName_2863_, lean_object* v_currNamespace_2864_, lean_object* v_givenNameView_2865_, uint8_t v_skipAuxDecl_2866_){
_start:
{
lean_object* v_decls_2867_; lean_object* v_givenName_2868_; lean_object* v___x_2869_; lean_object* v___f_2870_; lean_object* v___x_2871_; lean_object* v_localDecl_x3f_2872_; 
v_decls_2867_ = lean_ctor_get(v_lctx_2860_, 1);
lean_inc_ref_n(v_decls_2867_, 2);
lean_dec_ref(v_lctx_2860_);
lean_inc_ref(v_givenNameView_2865_);
v_givenName_2868_ = l_Lean_MacroScopesView_review(v_givenNameView_2865_);
v___x_2869_ = lean_box(v_skipAuxDecl_2866_);
lean_inc(v_givenName_2868_);
lean_inc_ref(v_matchLocalDecl_x3f_2861_);
v___f_2870_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_2870_, 0, v_matchLocalDecl_x3f_2861_);
lean_closure_set(v___f_2870_, 1, v_givenName_2868_);
lean_closure_set(v___f_2870_, 2, v___x_2869_);
lean_closure_set(v___f_2870_, 3, v___f_2862_);
lean_closure_set(v___f_2870_, 4, v_auxDeclToFullName_2863_);
lean_closure_set(v___f_2870_, 5, v_currNamespace_2864_);
lean_closure_set(v___f_2870_, 6, v_givenNameView_2865_);
v___x_2871_ = ((lean_object*)(l_Lean_resolveLocalName___redArg___lam__3___closed__9));
v_localDecl_x3f_2872_ = l_Lean_PersistentArray_findSomeRevM_x3f___redArg(v___x_2871_, v_decls_2867_, v___f_2870_);
if (lean_obj_tag(v_localDecl_x3f_2872_) == 0)
{
if (v_skipAuxDecl_2866_ == 0)
{
lean_object* v___f_2873_; lean_object* v___x_2874_; 
v___f_2873_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_2873_, 0, v_localDecl_x3f_2872_);
lean_closure_set(v___f_2873_, 1, v_matchLocalDecl_x3f_2861_);
lean_closure_set(v___f_2873_, 2, v_givenName_2868_);
v___x_2874_ = l_Lean_PersistentArray_findSomeRevM_x3f___redArg(v___x_2871_, v_decls_2867_, v___f_2873_);
return v___x_2874_;
}
else
{
lean_dec(v_givenName_2868_);
lean_dec_ref(v_decls_2867_);
lean_dec_ref(v_matchLocalDecl_x3f_2861_);
return v_localDecl_x3f_2872_;
}
}
else
{
lean_dec(v_givenName_2868_);
lean_dec_ref(v_decls_2867_);
lean_dec_ref(v_matchLocalDecl_x3f_2861_);
return v_localDecl_x3f_2872_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__3___boxed(lean_object* v_lctx_2875_, lean_object* v_matchLocalDecl_x3f_2876_, lean_object* v___f_2877_, lean_object* v_auxDeclToFullName_2878_, lean_object* v_currNamespace_2879_, lean_object* v_givenNameView_2880_, lean_object* v_skipAuxDecl_2881_){
_start:
{
uint8_t v_skipAuxDecl_boxed_2882_; lean_object* v_res_2883_; 
v_skipAuxDecl_boxed_2882_ = lean_unbox(v_skipAuxDecl_2881_);
v_res_2883_ = l_Lean_resolveLocalName___redArg___lam__3(v_lctx_2875_, v_matchLocalDecl_x3f_2876_, v___f_2877_, v_auxDeclToFullName_2878_, v_currNamespace_2879_, v_givenNameView_2880_, v_skipAuxDecl_boxed_2882_);
return v_res_2883_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__4(lean_object* v_n_2884_, lean_object* v_lctx_2885_, lean_object* v_matchLocalDecl_x3f_2886_, lean_object* v___f_2887_, lean_object* v_auxDeclToFullName_2888_, lean_object* v_inst_2889_, lean_object* v_inst_2890_, lean_object* v_inst_2891_, lean_object* v_inst_2892_, lean_object* v_inst_2893_, lean_object* v_inst_2894_, lean_object* v_currNamespace_2895_){
_start:
{
lean_object* v_view_2896_; lean_object* v_name_2897_; lean_object* v_findLocalDecl_x3f_2898_; lean_object* v___x_2899_; uint8_t v___x_2900_; lean_object* v___x_2901_; 
v_view_2896_ = l_Lean_extractMacroScopes(v_n_2884_);
v_name_2897_ = lean_ctor_get(v_view_2896_, 0);
lean_inc(v_name_2897_);
v_findLocalDecl_x3f_2898_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___redArg___lam__3___boxed), 7, 5);
lean_closure_set(v_findLocalDecl_x3f_2898_, 0, v_lctx_2885_);
lean_closure_set(v_findLocalDecl_x3f_2898_, 1, v_matchLocalDecl_x3f_2886_);
lean_closure_set(v_findLocalDecl_x3f_2898_, 2, v___f_2887_);
lean_closure_set(v_findLocalDecl_x3f_2898_, 3, v_auxDeclToFullName_2888_);
lean_closure_set(v_findLocalDecl_x3f_2898_, 4, v_currNamespace_2895_);
v___x_2899_ = lean_box(0);
v___x_2900_ = 0;
v___x_2901_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg(v_inst_2889_, v_inst_2890_, v_inst_2891_, v_inst_2892_, v_inst_2893_, v_inst_2894_, v_view_2896_, v_findLocalDecl_x3f_2898_, v_name_2897_, v___x_2899_, v___x_2900_);
return v___x_2901_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__5(lean_object* v_inst_2902_, lean_object* v_n_2903_, lean_object* v_lctx_2904_, lean_object* v_matchLocalDecl_x3f_2905_, lean_object* v___f_2906_, lean_object* v_inst_2907_, lean_object* v_inst_2908_, lean_object* v_inst_2909_, lean_object* v_inst_2910_, lean_object* v_inst_2911_, lean_object* v_toBind_2912_, lean_object* v_____do__lift_2913_){
_start:
{
lean_object* v_auxDeclToFullName_2914_; lean_object* v_getCurrNamespace_2915_; lean_object* v___f_2916_; lean_object* v___x_2917_; 
v_auxDeclToFullName_2914_ = lean_ctor_get(v_____do__lift_2913_, 2);
lean_inc(v_auxDeclToFullName_2914_);
lean_dec_ref(v_____do__lift_2913_);
v_getCurrNamespace_2915_ = lean_ctor_get(v_inst_2902_, 0);
lean_inc(v_getCurrNamespace_2915_);
v___f_2916_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___redArg___lam__4), 12, 11);
lean_closure_set(v___f_2916_, 0, v_n_2903_);
lean_closure_set(v___f_2916_, 1, v_lctx_2904_);
lean_closure_set(v___f_2916_, 2, v_matchLocalDecl_x3f_2905_);
lean_closure_set(v___f_2916_, 3, v___f_2906_);
lean_closure_set(v___f_2916_, 4, v_auxDeclToFullName_2914_);
lean_closure_set(v___f_2916_, 5, v_inst_2907_);
lean_closure_set(v___f_2916_, 6, v_inst_2902_);
lean_closure_set(v___f_2916_, 7, v_inst_2908_);
lean_closure_set(v___f_2916_, 8, v_inst_2909_);
lean_closure_set(v___f_2916_, 9, v_inst_2910_);
lean_closure_set(v___f_2916_, 10, v_inst_2911_);
v___x_2917_ = lean_apply_4(v_toBind_2912_, lean_box(0), lean_box(0), v_getCurrNamespace_2915_, v___f_2916_);
return v___x_2917_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__6(lean_object* v_inst_2918_, lean_object* v_n_2919_, lean_object* v_matchLocalDecl_x3f_2920_, lean_object* v___f_2921_, lean_object* v_inst_2922_, lean_object* v_inst_2923_, lean_object* v_inst_2924_, lean_object* v_inst_2925_, lean_object* v_inst_2926_, lean_object* v_toBind_2927_, lean_object* v_inst_2928_, lean_object* v_lctx_2929_){
_start:
{
lean_object* v___f_2930_; lean_object* v___x_2931_; 
lean_inc(v_toBind_2927_);
v___f_2930_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___redArg___lam__5), 12, 11);
lean_closure_set(v___f_2930_, 0, v_inst_2918_);
lean_closure_set(v___f_2930_, 1, v_n_2919_);
lean_closure_set(v___f_2930_, 2, v_lctx_2929_);
lean_closure_set(v___f_2930_, 3, v_matchLocalDecl_x3f_2920_);
lean_closure_set(v___f_2930_, 4, v___f_2921_);
lean_closure_set(v___f_2930_, 5, v_inst_2922_);
lean_closure_set(v___f_2930_, 6, v_inst_2923_);
lean_closure_set(v___f_2930_, 7, v_inst_2924_);
lean_closure_set(v___f_2930_, 8, v_inst_2925_);
lean_closure_set(v___f_2930_, 9, v_inst_2926_);
lean_closure_set(v___f_2930_, 10, v_toBind_2927_);
v___x_2931_ = lean_apply_4(v_toBind_2927_, lean_box(0), lean_box(0), v_inst_2928_, v___f_2930_);
return v___x_2931_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg(lean_object* v_inst_2934_, lean_object* v_inst_2935_, lean_object* v_inst_2936_, lean_object* v_inst_2937_, lean_object* v_inst_2938_, lean_object* v_inst_2939_, lean_object* v_inst_2940_, lean_object* v_n_2941_){
_start:
{
lean_object* v_toBind_2942_; lean_object* v___f_2943_; lean_object* v_matchLocalDecl_x3f_2944_; lean_object* v___f_2945_; lean_object* v___x_2946_; 
v_toBind_2942_ = lean_ctor_get(v_inst_2934_, 1);
lean_inc_n(v_toBind_2942_, 2);
v___f_2943_ = ((lean_object*)(l_Lean_resolveLocalName___redArg___closed__0));
v_matchLocalDecl_x3f_2944_ = ((lean_object*)(l_Lean_resolveLocalName___redArg___closed__1));
lean_inc(v_inst_2940_);
v___f_2945_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___redArg___lam__6), 12, 11);
lean_closure_set(v___f_2945_, 0, v_inst_2935_);
lean_closure_set(v___f_2945_, 1, v_n_2941_);
lean_closure_set(v___f_2945_, 2, v_matchLocalDecl_x3f_2944_);
lean_closure_set(v___f_2945_, 3, v___f_2943_);
lean_closure_set(v___f_2945_, 4, v_inst_2934_);
lean_closure_set(v___f_2945_, 5, v_inst_2936_);
lean_closure_set(v___f_2945_, 6, v_inst_2937_);
lean_closure_set(v___f_2945_, 7, v_inst_2938_);
lean_closure_set(v___f_2945_, 8, v_inst_2939_);
lean_closure_set(v___f_2945_, 9, v_toBind_2942_);
lean_closure_set(v___f_2945_, 10, v_inst_2940_);
v___x_2946_ = lean_apply_4(v_toBind_2942_, lean_box(0), lean_box(0), v_inst_2940_, v___f_2945_);
return v___x_2946_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName(lean_object* v_m_2947_, lean_object* v_inst_2948_, lean_object* v_inst_2949_, lean_object* v_inst_2950_, lean_object* v_inst_2951_, lean_object* v_inst_2952_, lean_object* v_inst_2953_, lean_object* v_inst_2954_, lean_object* v_n_2955_){
_start:
{
lean_object* v___x_2956_; 
v___x_2956_ = l_Lean_resolveLocalName___redArg(v_inst_2948_, v_inst_2949_, v_inst_2950_, v_inst_2951_, v_inst_2952_, v_inst_2953_, v_inst_2954_, v_n_2955_);
return v___x_2956_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__0(lean_object* v_toPure_2957_, uint8_t v_____do__lift_2958_){
_start:
{
lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; 
v___x_2959_ = lean_box(v_____do__lift_2958_);
v___x_2960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2960_, 0, v___x_2959_);
v___x_2961_ = lean_apply_2(v_toPure_2957_, lean_box(0), v___x_2960_);
return v___x_2961_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__0___boxed(lean_object* v_toPure_2962_, lean_object* v_____do__lift_2963_){
_start:
{
uint8_t v_____do__lift_1160__boxed_2964_; lean_object* v_res_2965_; 
v_____do__lift_1160__boxed_2964_ = lean_unbox(v_____do__lift_2963_);
v_res_2965_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__0(v_toPure_2962_, v_____do__lift_1160__boxed_2964_);
return v_res_2965_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__1(lean_object* v_toPure_2966_, lean_object* v___y_2967_, lean_object* v_____do__lift_2968_){
_start:
{
if (lean_obj_tag(v_____do__lift_2968_) == 0)
{
lean_object* v___x_2969_; lean_object* v___x_2970_; 
lean_dec(v___y_2967_);
v___x_2969_ = lean_box(0);
v___x_2970_ = lean_apply_2(v_toPure_2966_, lean_box(0), v___x_2969_);
return v___x_2970_;
}
else
{
lean_object* v___x_2972_; uint8_t v_isShared_2973_; uint8_t v_isSharedCheck_2978_; 
v_isSharedCheck_2978_ = !lean_is_exclusive(v_____do__lift_2968_);
if (v_isSharedCheck_2978_ == 0)
{
lean_object* v_unused_2979_; 
v_unused_2979_ = lean_ctor_get(v_____do__lift_2968_, 0);
lean_dec(v_unused_2979_);
v___x_2972_ = v_____do__lift_2968_;
v_isShared_2973_ = v_isSharedCheck_2978_;
goto v_resetjp_2971_;
}
else
{
lean_dec(v_____do__lift_2968_);
v___x_2972_ = lean_box(0);
v_isShared_2973_ = v_isSharedCheck_2978_;
goto v_resetjp_2971_;
}
v_resetjp_2971_:
{
lean_object* v___x_2975_; 
if (v_isShared_2973_ == 0)
{
lean_ctor_set(v___x_2972_, 0, v___y_2967_);
v___x_2975_ = v___x_2972_;
goto v_reusejp_2974_;
}
else
{
lean_object* v_reuseFailAlloc_2977_; 
v_reuseFailAlloc_2977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2977_, 0, v___y_2967_);
v___x_2975_ = v_reuseFailAlloc_2977_;
goto v_reusejp_2974_;
}
v_reusejp_2974_:
{
lean_object* v___x_2976_; 
v___x_2976_ = lean_apply_2(v_toPure_2966_, lean_box(0), v___x_2975_);
return v___x_2976_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2(lean_object* v_toPure_2982_, lean_object* v_toBind_2983_, lean_object* v___f_2984_, lean_object* v_____do__lift_2985_){
_start:
{
if (lean_obj_tag(v_____do__lift_2985_) == 0)
{
lean_object* v___x_2986_; lean_object* v___x_2987_; 
lean_dec(v___f_2984_);
lean_dec(v_toBind_2983_);
v___x_2986_ = lean_box(0);
v___x_2987_ = lean_apply_2(v_toPure_2982_, lean_box(0), v___x_2986_);
return v___x_2987_;
}
else
{
lean_object* v_val_2988_; uint8_t v___x_2989_; 
v_val_2988_ = lean_ctor_get(v_____do__lift_2985_, 0);
v___x_2989_ = lean_unbox(v_val_2988_);
if (v___x_2989_ == 0)
{
lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; 
v___x_2990_ = lean_box(0);
v___x_2991_ = lean_apply_2(v_toPure_2982_, lean_box(0), v___x_2990_);
v___x_2992_ = lean_apply_4(v_toBind_2983_, lean_box(0), lean_box(0), v___x_2991_, v___f_2984_);
return v___x_2992_;
}
else
{
lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; 
v___x_2993_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2___closed__0));
v___x_2994_ = lean_apply_2(v_toPure_2982_, lean_box(0), v___x_2993_);
v___x_2995_ = lean_apply_4(v_toBind_2983_, lean_box(0), lean_box(0), v___x_2994_, v___f_2984_);
return v___x_2995_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2___boxed(lean_object* v_toPure_2996_, lean_object* v_toBind_2997_, lean_object* v___f_2998_, lean_object* v_____do__lift_2999_){
_start:
{
lean_object* v_res_3000_; 
v_res_3000_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2(v_toPure_2996_, v_toBind_2997_, v___f_2998_, v_____do__lift_2999_);
lean_dec(v_____do__lift_2999_);
return v_res_3000_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__3(lean_object* v_toPure_3001_, lean_object* v_filter_3002_, lean_object* v___y_3003_, lean_object* v_toBind_3004_, lean_object* v___f_3005_, lean_object* v___f_3006_, lean_object* v_____do__lift_3007_){
_start:
{
if (lean_obj_tag(v_____do__lift_3007_) == 0)
{
lean_object* v___x_3008_; lean_object* v___x_3009_; 
lean_dec(v___f_3006_);
lean_dec(v___f_3005_);
lean_dec(v_toBind_3004_);
lean_dec(v___y_3003_);
lean_dec(v_filter_3002_);
v___x_3008_ = lean_box(0);
v___x_3009_ = lean_apply_2(v_toPure_3001_, lean_box(0), v___x_3008_);
return v___x_3009_;
}
else
{
lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; 
lean_dec(v_toPure_3001_);
v___x_3010_ = lean_apply_1(v_filter_3002_, v___y_3003_);
lean_inc(v_toBind_3004_);
v___x_3011_ = lean_apply_4(v_toBind_3004_, lean_box(0), lean_box(0), v___x_3010_, v___f_3005_);
v___x_3012_ = lean_apply_4(v_toBind_3004_, lean_box(0), lean_box(0), v___x_3011_, v___f_3006_);
return v___x_3012_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__3___boxed(lean_object* v_toPure_3013_, lean_object* v_filter_3014_, lean_object* v___y_3015_, lean_object* v_toBind_3016_, lean_object* v___f_3017_, lean_object* v___f_3018_, lean_object* v_____do__lift_3019_){
_start:
{
lean_object* v_res_3020_; 
v_res_3020_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__3(v_toPure_3013_, v_filter_3014_, v___y_3015_, v_toBind_3016_, v___f_3017_, v___f_3018_, v_____do__lift_3019_);
lean_dec(v_____do__lift_3019_);
return v_res_3020_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__4(lean_object* v_toPure_3021_, lean_object* v_n_u2080_3022_, lean_object* v_toBind_3023_, lean_object* v___f_3024_, lean_object* v_____do__lift_3025_){
_start:
{
if (lean_obj_tag(v_____do__lift_3025_) == 0)
{
lean_object* v___x_3029_; lean_object* v___x_3030_; 
lean_dec(v___f_3024_);
lean_dec(v_toBind_3023_);
v___x_3029_ = lean_box(0);
v___x_3030_ = lean_apply_2(v_toPure_3021_, lean_box(0), v___x_3029_);
return v___x_3030_;
}
else
{
lean_object* v_val_3031_; 
v_val_3031_ = lean_ctor_get(v_____do__lift_3025_, 0);
if (lean_obj_tag(v_val_3031_) == 1)
{
lean_object* v_tail_3032_; 
v_tail_3032_ = lean_ctor_get(v_val_3031_, 1);
if (lean_obj_tag(v_tail_3032_) == 0)
{
lean_object* v_head_3033_; lean_object* v_fst_3034_; uint8_t v___x_3035_; 
v_head_3033_ = lean_ctor_get(v_val_3031_, 0);
v_fst_3034_ = lean_ctor_get(v_head_3033_, 0);
v___x_3035_ = lean_name_eq(v_fst_3034_, v_n_u2080_3022_);
if (v___x_3035_ == 0)
{
lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; 
v___x_3036_ = lean_box(0);
v___x_3037_ = lean_apply_2(v_toPure_3021_, lean_box(0), v___x_3036_);
v___x_3038_ = lean_apply_4(v_toBind_3023_, lean_box(0), lean_box(0), v___x_3037_, v___f_3024_);
return v___x_3038_;
}
else
{
lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; 
v___x_3039_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2___closed__0));
v___x_3040_ = lean_apply_2(v_toPure_3021_, lean_box(0), v___x_3039_);
v___x_3041_ = lean_apply_4(v_toBind_3023_, lean_box(0), lean_box(0), v___x_3040_, v___f_3024_);
return v___x_3041_;
}
}
else
{
lean_dec(v___f_3024_);
lean_dec(v_toBind_3023_);
goto v___jp_3026_;
}
}
else
{
lean_dec(v___f_3024_);
lean_dec(v_toBind_3023_);
goto v___jp_3026_;
}
}
v___jp_3026_:
{
lean_object* v___x_3027_; lean_object* v___x_3028_; 
v___x_3027_ = lean_box(0);
v___x_3028_ = lean_apply_2(v_toPure_3021_, lean_box(0), v___x_3027_);
return v___x_3028_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__4___boxed(lean_object* v_toPure_3042_, lean_object* v_n_u2080_3043_, lean_object* v_toBind_3044_, lean_object* v___f_3045_, lean_object* v_____do__lift_3046_){
_start:
{
lean_object* v_res_3047_; 
v_res_3047_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__4(v_toPure_3042_, v_n_u2080_3043_, v_toBind_3044_, v___f_3045_, v_____do__lift_3046_);
lean_dec(v_____do__lift_3046_);
lean_dec(v_n_u2080_3043_);
return v_res_3047_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg(lean_object* v_inst_3048_, lean_object* v_inst_3049_, lean_object* v_inst_3050_, lean_object* v_inst_3051_, lean_object* v_inst_3052_, lean_object* v_inst_3053_, lean_object* v_n_u2080_3054_, lean_object* v_filter_3055_, lean_object* v_view_x3f_3056_, lean_object* v_n_3057_){
_start:
{
lean_object* v___f_3058_; lean_object* v___f_3059_; lean_object* v___f_3060_; lean_object* v___f_3061_; lean_object* v___f_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v_toApplicative_3070_; lean_object* v_getEnv_3071_; lean_object* v_modifyEnv_3072_; lean_object* v___x_3074_; uint8_t v_isShared_3075_; uint8_t v_isSharedCheck_3110_; 
lean_inc_ref_n(v_inst_3048_, 8);
v___f_3058_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_3058_, 0, v_inst_3048_);
v___f_3059_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__3), 5, 1);
lean_closure_set(v___f_3059_, 0, v_inst_3048_);
v___f_3060_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__6), 5, 1);
lean_closure_set(v___f_3060_, 0, v_inst_3048_);
v___f_3061_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_3061_, 0, v_inst_3048_);
v___f_3062_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__11), 5, 1);
lean_closure_set(v___f_3062_, 0, v_inst_3048_);
v___x_3063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3063_, 0, v___f_3058_);
lean_ctor_set(v___x_3063_, 1, v___f_3059_);
v___x_3064_ = lean_alloc_closure((void*)(l_OptionT_pure), 4, 2);
lean_closure_set(v___x_3064_, 0, lean_box(0));
lean_closure_set(v___x_3064_, 1, v_inst_3048_);
v___x_3065_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3065_, 0, v___x_3063_);
lean_ctor_set(v___x_3065_, 1, v___x_3064_);
lean_ctor_set(v___x_3065_, 2, v___f_3060_);
lean_ctor_set(v___x_3065_, 3, v___f_3061_);
lean_ctor_set(v___x_3065_, 4, v___f_3062_);
v___x_3066_ = lean_alloc_closure((void*)(l_OptionT_bind), 6, 2);
lean_closure_set(v___x_3066_, 0, lean_box(0));
lean_closure_set(v___x_3066_, 1, v_inst_3048_);
v___x_3067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3067_, 0, v___x_3065_);
lean_ctor_set(v___x_3067_, 1, v___x_3066_);
v___x_3068_ = lean_alloc_closure((void*)(l_OptionT_lift), 4, 2);
lean_closure_set(v___x_3068_, 0, lean_box(0));
lean_closure_set(v___x_3068_, 1, v_inst_3048_);
lean_inc_ref(v___x_3068_);
v___x_3069_ = l_Lean_instMonadResolveNameOfMonadLift___redArg(v___x_3068_, v_inst_3049_);
v_toApplicative_3070_ = lean_ctor_get(v_inst_3048_, 0);
lean_inc_ref(v_toApplicative_3070_);
v_getEnv_3071_ = lean_ctor_get(v_inst_3050_, 0);
v_modifyEnv_3072_ = lean_ctor_get(v_inst_3050_, 1);
v_isSharedCheck_3110_ = !lean_is_exclusive(v_inst_3050_);
if (v_isSharedCheck_3110_ == 0)
{
v___x_3074_ = v_inst_3050_;
v_isShared_3075_ = v_isSharedCheck_3110_;
goto v_resetjp_3073_;
}
else
{
lean_inc(v_modifyEnv_3072_);
lean_inc(v_getEnv_3071_);
lean_dec(v_inst_3050_);
v___x_3074_ = lean_box(0);
v_isShared_3075_ = v_isSharedCheck_3110_;
goto v_resetjp_3073_;
}
v_resetjp_3073_:
{
lean_object* v_toBind_3076_; lean_object* v_toPure_3077_; lean_object* v___f_3078_; lean_object* v___f_3079_; lean_object* v___f_3080_; lean_object* v___x_3081_; lean_object* v___x_3083_; 
v_toBind_3076_ = lean_ctor_get(v_inst_3048_, 1);
lean_inc_n(v_toBind_3076_, 2);
lean_dec_ref(v_inst_3048_);
v_toPure_3077_ = lean_ctor_get(v_toApplicative_3070_, 1);
lean_inc_n(v_toPure_3077_, 3);
lean_dec_ref(v_toApplicative_3070_);
lean_inc_ref(v___x_3068_);
v___f_3078_ = lean_alloc_closure((void*)(l_Lean_instMonadEnvOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3078_, 0, v_modifyEnv_3072_);
lean_closure_set(v___f_3078_, 1, v___x_3068_);
v___f_3079_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3079_, 0, v_toPure_3077_);
v___f_3080_ = lean_alloc_closure((void*)(l_OptionT_lift___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3080_, 0, v_toPure_3077_);
lean_inc_ref(v___f_3080_);
v___x_3081_ = lean_apply_4(v_toBind_3076_, lean_box(0), lean_box(0), v_getEnv_3071_, v___f_3080_);
if (v_isShared_3075_ == 0)
{
lean_ctor_set(v___x_3074_, 1, v___f_3078_);
lean_ctor_set(v___x_3074_, 0, v___x_3081_);
v___x_3083_ = v___x_3074_;
goto v_reusejp_3082_;
}
else
{
lean_object* v_reuseFailAlloc_3109_; 
v_reuseFailAlloc_3109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3109_, 0, v___x_3081_);
lean_ctor_set(v_reuseFailAlloc_3109_, 1, v___f_3078_);
v___x_3083_ = v_reuseFailAlloc_3109_;
goto v_reusejp_3082_;
}
v_reusejp_3082_:
{
lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___f_3086_; lean_object* v___y_3088_; 
lean_inc(v_toBind_3076_);
v___x_3084_ = lean_apply_4(v_toBind_3076_, lean_box(0), lean_box(0), v_inst_3051_, v___f_3080_);
lean_inc_ref(v___x_3068_);
v___x_3085_ = l_Lean_instMonadLogOfMonadLift___redArg(v___x_3068_, v_inst_3052_);
v___f_3086_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3086_, 0, v_inst_3053_);
lean_closure_set(v___f_3086_, 1, v___x_3068_);
if (lean_obj_tag(v_view_x3f_3056_) == 1)
{
lean_object* v_val_3096_; lean_object* v_imported_3097_; lean_object* v_ctx_3098_; lean_object* v_scopes_3099_; lean_object* v___x_3101_; uint8_t v_isShared_3102_; uint8_t v_isSharedCheck_3107_; 
v_val_3096_ = lean_ctor_get(v_view_x3f_3056_, 0);
lean_inc(v_val_3096_);
lean_dec_ref_known(v_view_x3f_3056_, 1);
v_imported_3097_ = lean_ctor_get(v_val_3096_, 1);
v_ctx_3098_ = lean_ctor_get(v_val_3096_, 2);
v_scopes_3099_ = lean_ctor_get(v_val_3096_, 3);
v_isSharedCheck_3107_ = !lean_is_exclusive(v_val_3096_);
if (v_isSharedCheck_3107_ == 0)
{
lean_object* v_unused_3108_; 
v_unused_3108_ = lean_ctor_get(v_val_3096_, 0);
lean_dec(v_unused_3108_);
v___x_3101_ = v_val_3096_;
v_isShared_3102_ = v_isSharedCheck_3107_;
goto v_resetjp_3100_;
}
else
{
lean_inc(v_scopes_3099_);
lean_inc(v_ctx_3098_);
lean_inc(v_imported_3097_);
lean_dec(v_val_3096_);
v___x_3101_ = lean_box(0);
v_isShared_3102_ = v_isSharedCheck_3107_;
goto v_resetjp_3100_;
}
v_resetjp_3100_:
{
lean_object* v___x_3104_; 
if (v_isShared_3102_ == 0)
{
lean_ctor_set(v___x_3101_, 0, v_n_3057_);
v___x_3104_ = v___x_3101_;
goto v_reusejp_3103_;
}
else
{
lean_object* v_reuseFailAlloc_3106_; 
v_reuseFailAlloc_3106_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3106_, 0, v_n_3057_);
lean_ctor_set(v_reuseFailAlloc_3106_, 1, v_imported_3097_);
lean_ctor_set(v_reuseFailAlloc_3106_, 2, v_ctx_3098_);
lean_ctor_set(v_reuseFailAlloc_3106_, 3, v_scopes_3099_);
v___x_3104_ = v_reuseFailAlloc_3106_;
goto v_reusejp_3103_;
}
v_reusejp_3103_:
{
lean_object* v___x_3105_; 
v___x_3105_ = l_Lean_MacroScopesView_review(v___x_3104_);
v___y_3088_ = v___x_3105_;
goto v___jp_3087_;
}
}
}
else
{
lean_dec(v_view_x3f_3056_);
v___y_3088_ = v_n_3057_;
goto v___jp_3087_;
}
v___jp_3087_:
{
lean_object* v___f_3089_; lean_object* v___f_3090_; lean_object* v___f_3091_; lean_object* v___f_3092_; uint8_t v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; 
lean_inc_n(v___y_3088_, 2);
lean_inc_n(v_toPure_3077_, 3);
v___f_3089_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__1), 3, 2);
lean_closure_set(v___f_3089_, 0, v_toPure_3077_);
lean_closure_set(v___f_3089_, 1, v___y_3088_);
lean_inc_n(v_toBind_3076_, 3);
v___f_3090_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_3090_, 0, v_toPure_3077_);
lean_closure_set(v___f_3090_, 1, v_toBind_3076_);
lean_closure_set(v___f_3090_, 2, v___f_3089_);
v___f_3091_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__3___boxed), 7, 6);
lean_closure_set(v___f_3091_, 0, v_toPure_3077_);
lean_closure_set(v___f_3091_, 1, v_filter_3055_);
lean_closure_set(v___f_3091_, 2, v___y_3088_);
lean_closure_set(v___f_3091_, 3, v_toBind_3076_);
lean_closure_set(v___f_3091_, 4, v___f_3079_);
lean_closure_set(v___f_3091_, 5, v___f_3090_);
v___f_3092_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__4___boxed), 5, 4);
lean_closure_set(v___f_3092_, 0, v_toPure_3077_);
lean_closure_set(v___f_3092_, 1, v_n_u2080_3054_);
lean_closure_set(v___f_3092_, 2, v_toBind_3076_);
lean_closure_set(v___f_3092_, 3, v___f_3091_);
v___x_3093_ = 0;
v___x_3094_ = l_Lean_resolveGlobalName___redArg(v___x_3067_, v___x_3069_, v___x_3083_, v___x_3084_, v___x_3085_, v___f_3086_, v___y_3088_, v___x_3093_);
v___x_3095_ = lean_apply_4(v_toBind_3076_, lean_box(0), lean_box(0), v___x_3094_, v___f_3092_);
return v___x_3095_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve(lean_object* v_m_3111_, lean_object* v_inst_3112_, lean_object* v_inst_3113_, lean_object* v_inst_3114_, lean_object* v_inst_3115_, lean_object* v_inst_3116_, lean_object* v_inst_3117_, lean_object* v_n_u2080_3118_, lean_object* v_filter_3119_, lean_object* v_view_x3f_3120_, lean_object* v_n_3121_){
_start:
{
lean_object* v___x_3122_; 
v___x_3122_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg(v_inst_3112_, v_inst_3113_, v_inst_3114_, v_inst_3115_, v_inst_3116_, v_inst_3117_, v_n_u2080_3118_, v_filter_3119_, v_view_x3f_3120_, v_n_3121_);
return v___x_3122_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__0(lean_object* v_toPure_3127_, lean_object* v_____x_3128_){
_start:
{
if (lean_obj_tag(v_____x_3128_) == 0)
{
lean_object* v___x_3129_; lean_object* v___x_3130_; 
v___x_3129_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__0___closed__1));
v___x_3130_ = lean_apply_2(v_toPure_3127_, lean_box(0), v___x_3129_);
return v___x_3130_;
}
else
{
lean_object* v___x_3131_; 
v___x_3131_ = lean_apply_2(v_toPure_3127_, lean_box(0), v_____x_3128_);
return v___x_3131_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__1(lean_object* v_toPure_3132_, lean_object* v_____do__lift_3133_){
_start:
{
if (lean_obj_tag(v_____do__lift_3133_) == 0)
{
lean_object* v___x_3134_; lean_object* v___x_3135_; 
v___x_3134_ = lean_box(0);
v___x_3135_ = lean_apply_2(v_toPure_3132_, lean_box(0), v___x_3134_);
return v___x_3135_;
}
else
{
lean_object* v_val_3136_; lean_object* v___x_3138_; uint8_t v_isShared_3139_; uint8_t v_isSharedCheck_3145_; 
v_val_3136_ = lean_ctor_get(v_____do__lift_3133_, 0);
v_isSharedCheck_3145_ = !lean_is_exclusive(v_____do__lift_3133_);
if (v_isSharedCheck_3145_ == 0)
{
v___x_3138_ = v_____do__lift_3133_;
v_isShared_3139_ = v_isSharedCheck_3145_;
goto v_resetjp_3137_;
}
else
{
lean_inc(v_val_3136_);
lean_dec(v_____do__lift_3133_);
v___x_3138_ = lean_box(0);
v_isShared_3139_ = v_isSharedCheck_3145_;
goto v_resetjp_3137_;
}
v_resetjp_3137_:
{
lean_object* v___x_3140_; lean_object* v___x_3142_; 
v___x_3140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3140_, 0, v_val_3136_);
if (v_isShared_3139_ == 0)
{
lean_ctor_set(v___x_3138_, 0, v___x_3140_);
v___x_3142_ = v___x_3138_;
goto v_reusejp_3141_;
}
else
{
lean_object* v_reuseFailAlloc_3144_; 
v_reuseFailAlloc_3144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3144_, 0, v___x_3140_);
v___x_3142_ = v_reuseFailAlloc_3144_;
goto v_reusejp_3141_;
}
v_reusejp_3141_:
{
lean_object* v___x_3143_; 
v___x_3143_ = lean_apply_2(v_toPure_3132_, lean_box(0), v___x_3142_);
return v___x_3143_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__2(lean_object* v_toPure_3146_, lean_object* v___x_3147_, lean_object* v_____do__lift_3148_){
_start:
{
if (lean_obj_tag(v_____do__lift_3148_) == 0)
{
lean_object* v___x_3149_; 
v___x_3149_ = lean_apply_2(v_toPure_3146_, lean_box(0), v___x_3147_);
return v___x_3149_;
}
else
{
lean_object* v_val_3150_; lean_object* v_fst_3151_; lean_object* v___x_3152_; 
lean_dec(v___x_3147_);
v_val_3150_ = lean_ctor_get(v_____do__lift_3148_, 0);
lean_inc(v_val_3150_);
lean_dec_ref_known(v_____do__lift_3148_, 1);
v_fst_3151_ = lean_ctor_get(v_val_3150_, 0);
lean_inc(v_fst_3151_);
lean_dec(v_val_3150_);
v___x_3152_ = lean_apply_2(v_toPure_3146_, lean_box(0), v_fst_3151_);
return v___x_3152_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__3(lean_object* v_toPure_3153_, lean_object* v___x_3154_, lean_object* v___x_3155_, lean_object* v_____do__lift_3156_){
_start:
{
if (lean_obj_tag(v_____do__lift_3156_) == 0)
{
lean_object* v___x_3157_; lean_object* v___x_3158_; 
lean_dec(v___x_3155_);
lean_dec(v___x_3154_);
v___x_3157_ = lean_box(0);
v___x_3158_ = lean_apply_2(v_toPure_3153_, lean_box(0), v___x_3157_);
return v___x_3158_;
}
else
{
lean_object* v_val_3159_; lean_object* v___x_3161_; uint8_t v_isShared_3162_; uint8_t v_isSharedCheck_3190_; 
v_val_3159_ = lean_ctor_get(v_____do__lift_3156_, 0);
v_isSharedCheck_3190_ = !lean_is_exclusive(v_____do__lift_3156_);
if (v_isSharedCheck_3190_ == 0)
{
v___x_3161_ = v_____do__lift_3156_;
v_isShared_3162_ = v_isSharedCheck_3190_;
goto v_resetjp_3160_;
}
else
{
lean_inc(v_val_3159_);
lean_dec(v_____do__lift_3156_);
v___x_3161_ = lean_box(0);
v_isShared_3162_ = v_isSharedCheck_3190_;
goto v_resetjp_3160_;
}
v_resetjp_3160_:
{
if (lean_obj_tag(v_val_3159_) == 0)
{
lean_object* v_a_3163_; lean_object* v___x_3165_; uint8_t v_isShared_3166_; uint8_t v_isSharedCheck_3176_; 
lean_dec(v___x_3155_);
v_a_3163_ = lean_ctor_get(v_val_3159_, 0);
v_isSharedCheck_3176_ = !lean_is_exclusive(v_val_3159_);
if (v_isSharedCheck_3176_ == 0)
{
v___x_3165_ = v_val_3159_;
v_isShared_3166_ = v_isSharedCheck_3176_;
goto v_resetjp_3164_;
}
else
{
lean_inc(v_a_3163_);
lean_dec(v_val_3159_);
v___x_3165_ = lean_box(0);
v_isShared_3166_ = v_isSharedCheck_3176_;
goto v_resetjp_3164_;
}
v_resetjp_3164_:
{
lean_object* v___x_3168_; 
if (v_isShared_3162_ == 0)
{
lean_ctor_set(v___x_3161_, 0, v_a_3163_);
v___x_3168_ = v___x_3161_;
goto v_reusejp_3167_;
}
else
{
lean_object* v_reuseFailAlloc_3175_; 
v_reuseFailAlloc_3175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3175_, 0, v_a_3163_);
v___x_3168_ = v_reuseFailAlloc_3175_;
goto v_reusejp_3167_;
}
v_reusejp_3167_:
{
lean_object* v___x_3169_; lean_object* v___x_3171_; 
v___x_3169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3169_, 0, v___x_3168_);
lean_ctor_set(v___x_3169_, 1, v___x_3154_);
if (v_isShared_3166_ == 0)
{
lean_ctor_set(v___x_3165_, 0, v___x_3169_);
v___x_3171_ = v___x_3165_;
goto v_reusejp_3170_;
}
else
{
lean_object* v_reuseFailAlloc_3174_; 
v_reuseFailAlloc_3174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3174_, 0, v___x_3169_);
v___x_3171_ = v_reuseFailAlloc_3174_;
goto v_reusejp_3170_;
}
v_reusejp_3170_:
{
lean_object* v___x_3172_; lean_object* v___x_3173_; 
v___x_3172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3172_, 0, v___x_3171_);
v___x_3173_ = lean_apply_2(v_toPure_3153_, lean_box(0), v___x_3172_);
return v___x_3173_;
}
}
}
}
else
{
lean_object* v___x_3178_; uint8_t v_isShared_3179_; uint8_t v_isSharedCheck_3188_; 
v_isSharedCheck_3188_ = !lean_is_exclusive(v_val_3159_);
if (v_isSharedCheck_3188_ == 0)
{
lean_object* v_unused_3189_; 
v_unused_3189_ = lean_ctor_get(v_val_3159_, 0);
lean_dec(v_unused_3189_);
v___x_3178_ = v_val_3159_;
v_isShared_3179_ = v_isSharedCheck_3188_;
goto v_resetjp_3177_;
}
else
{
lean_dec(v_val_3159_);
v___x_3178_ = lean_box(0);
v_isShared_3179_ = v_isSharedCheck_3188_;
goto v_resetjp_3177_;
}
v_resetjp_3177_:
{
lean_object* v___x_3180_; lean_object* v___x_3182_; 
v___x_3180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3180_, 0, v___x_3155_);
lean_ctor_set(v___x_3180_, 1, v___x_3154_);
if (v_isShared_3179_ == 0)
{
lean_ctor_set(v___x_3178_, 0, v___x_3180_);
v___x_3182_ = v___x_3178_;
goto v_reusejp_3181_;
}
else
{
lean_object* v_reuseFailAlloc_3187_; 
v_reuseFailAlloc_3187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3187_, 0, v___x_3180_);
v___x_3182_ = v_reuseFailAlloc_3187_;
goto v_reusejp_3181_;
}
v_reusejp_3181_:
{
lean_object* v___x_3184_; 
if (v_isShared_3162_ == 0)
{
lean_ctor_set(v___x_3161_, 0, v___x_3182_);
v___x_3184_ = v___x_3161_;
goto v_reusejp_3183_;
}
else
{
lean_object* v_reuseFailAlloc_3186_; 
v_reuseFailAlloc_3186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3186_, 0, v___x_3182_);
v___x_3184_ = v_reuseFailAlloc_3186_;
goto v_reusejp_3183_;
}
v_reusejp_3183_:
{
lean_object* v___x_3185_; 
v___x_3185_ = lean_apply_2(v_toPure_3153_, lean_box(0), v___x_3184_);
return v___x_3185_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__4(lean_object* v_toPure_3191_, lean_object* v___x_3192_, lean_object* v_inst_3193_, lean_object* v_inst_3194_, lean_object* v_inst_3195_, lean_object* v_inst_3196_, lean_object* v_inst_3197_, lean_object* v_inst_3198_, lean_object* v_n_u2080_3199_, lean_object* v_filter_3200_, lean_object* v_view_x3f_3201_, lean_object* v_toBind_3202_, lean_object* v___f_3203_, lean_object* v___f_3204_, lean_object* v_a_3205_, lean_object* v_x_3206_, lean_object* v___y_3207_){
_start:
{
lean_object* v_snd_3208_; lean_object* v___x_3209_; lean_object* v___f_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; 
v_snd_3208_ = lean_ctor_get(v___y_3207_, 1);
lean_inc(v_snd_3208_);
lean_dec_ref(v___y_3207_);
v___x_3209_ = l_Lean_Name_appendCore(v_a_3205_, v_snd_3208_);
lean_inc(v___x_3209_);
v___f_3210_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__3), 4, 3);
lean_closure_set(v___f_3210_, 0, v_toPure_3191_);
lean_closure_set(v___f_3210_, 1, v___x_3209_);
lean_closure_set(v___f_3210_, 2, v___x_3192_);
v___x_3211_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg(v_inst_3193_, v_inst_3194_, v_inst_3195_, v_inst_3196_, v_inst_3197_, v_inst_3198_, v_n_u2080_3199_, v_filter_3200_, v_view_x3f_3201_, v___x_3209_);
lean_inc_n(v_toBind_3202_, 2);
v___x_3212_ = lean_apply_4(v_toBind_3202_, lean_box(0), lean_box(0), v___x_3211_, v___f_3203_);
v___x_3213_ = lean_apply_4(v_toBind_3202_, lean_box(0), lean_box(0), v___x_3212_, v___f_3204_);
v___x_3214_ = lean_apply_4(v_toBind_3202_, lean_box(0), lean_box(0), v___x_3213_, v___f_3210_);
return v___x_3214_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__4___boxed(lean_object** _args){
lean_object* v_toPure_3215_ = _args[0];
lean_object* v___x_3216_ = _args[1];
lean_object* v_inst_3217_ = _args[2];
lean_object* v_inst_3218_ = _args[3];
lean_object* v_inst_3219_ = _args[4];
lean_object* v_inst_3220_ = _args[5];
lean_object* v_inst_3221_ = _args[6];
lean_object* v_inst_3222_ = _args[7];
lean_object* v_n_u2080_3223_ = _args[8];
lean_object* v_filter_3224_ = _args[9];
lean_object* v_view_x3f_3225_ = _args[10];
lean_object* v_toBind_3226_ = _args[11];
lean_object* v___f_3227_ = _args[12];
lean_object* v___f_3228_ = _args[13];
lean_object* v_a_3229_ = _args[14];
lean_object* v_x_3230_ = _args[15];
lean_object* v___y_3231_ = _args[16];
_start:
{
lean_object* v_res_3232_; 
v_res_3232_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__4(v_toPure_3215_, v___x_3216_, v_inst_3217_, v_inst_3218_, v_inst_3219_, v_inst_3220_, v_inst_3221_, v_inst_3222_, v_n_u2080_3223_, v_filter_3224_, v_view_x3f_3225_, v_toBind_3226_, v___f_3227_, v___f_3228_, v_a_3229_, v_x_3230_, v___y_3231_);
lean_dec(v_a_3229_);
return v_res_3232_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__5(lean_object* v_toPure_3236_, lean_object* v_n_3237_, lean_object* v_inst_3238_, lean_object* v_inst_3239_, lean_object* v_inst_3240_, lean_object* v_inst_3241_, lean_object* v_inst_3242_, lean_object* v_inst_3243_, lean_object* v_n_u2080_3244_, lean_object* v_filter_3245_, lean_object* v_view_x3f_3246_, lean_object* v_toBind_3247_, lean_object* v___f_3248_, lean_object* v___f_3249_, lean_object* v___x_3250_, lean_object* v_____do__lift_3251_){
_start:
{
if (lean_obj_tag(v_____do__lift_3251_) == 0)
{
lean_object* v___x_3252_; lean_object* v___x_3253_; 
lean_dec_ref(v___x_3250_);
lean_dec(v___f_3249_);
lean_dec(v___f_3248_);
lean_dec(v_toBind_3247_);
lean_dec(v_view_x3f_3246_);
lean_dec(v_filter_3245_);
lean_dec(v_n_u2080_3244_);
lean_dec(v_inst_3243_);
lean_dec_ref(v_inst_3242_);
lean_dec(v_inst_3241_);
lean_dec_ref(v_inst_3240_);
lean_dec_ref(v_inst_3239_);
lean_dec_ref(v_inst_3238_);
lean_dec(v_n_3237_);
v___x_3252_ = lean_box(0);
v___x_3253_ = lean_apply_2(v_toPure_3236_, lean_box(0), v___x_3252_);
return v___x_3253_;
}
else
{
lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___f_3257_; lean_object* v___f_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; 
v___x_3254_ = l_Lean_privateToUserName(v_n_3237_);
v___x_3255_ = l_Lean_Name_componentsRev(v___x_3254_);
v___x_3256_ = lean_box(0);
lean_inc(v_toPure_3236_);
v___f_3257_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__2), 3, 2);
lean_closure_set(v___f_3257_, 0, v_toPure_3236_);
lean_closure_set(v___f_3257_, 1, v___x_3256_);
lean_inc(v_toBind_3247_);
v___f_3258_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__4___boxed), 17, 14);
lean_closure_set(v___f_3258_, 0, v_toPure_3236_);
lean_closure_set(v___f_3258_, 1, v___x_3256_);
lean_closure_set(v___f_3258_, 2, v_inst_3238_);
lean_closure_set(v___f_3258_, 3, v_inst_3239_);
lean_closure_set(v___f_3258_, 4, v_inst_3240_);
lean_closure_set(v___f_3258_, 5, v_inst_3241_);
lean_closure_set(v___f_3258_, 6, v_inst_3242_);
lean_closure_set(v___f_3258_, 7, v_inst_3243_);
lean_closure_set(v___f_3258_, 8, v_n_u2080_3244_);
lean_closure_set(v___f_3258_, 9, v_filter_3245_);
lean_closure_set(v___f_3258_, 10, v_view_x3f_3246_);
lean_closure_set(v___f_3258_, 11, v_toBind_3247_);
lean_closure_set(v___f_3258_, 12, v___f_3248_);
lean_closure_set(v___f_3258_, 13, v___f_3249_);
v___x_3259_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__5___closed__0));
v___x_3260_ = l_List_forIn_x27_loop___redArg(v___x_3250_, v___f_3258_, v___x_3255_, v___x_3259_);
lean_dec(v___x_3255_);
v___x_3261_ = lean_apply_4(v_toBind_3247_, lean_box(0), lean_box(0), v___x_3260_, v___f_3257_);
return v___x_3261_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__5___boxed(lean_object* v_toPure_3262_, lean_object* v_n_3263_, lean_object* v_inst_3264_, lean_object* v_inst_3265_, lean_object* v_inst_3266_, lean_object* v_inst_3267_, lean_object* v_inst_3268_, lean_object* v_inst_3269_, lean_object* v_n_u2080_3270_, lean_object* v_filter_3271_, lean_object* v_view_x3f_3272_, lean_object* v_toBind_3273_, lean_object* v___f_3274_, lean_object* v___f_3275_, lean_object* v___x_3276_, lean_object* v_____do__lift_3277_){
_start:
{
lean_object* v_res_3278_; 
v_res_3278_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__5(v_toPure_3262_, v_n_3263_, v_inst_3264_, v_inst_3265_, v_inst_3266_, v_inst_3267_, v_inst_3268_, v_inst_3269_, v_n_u2080_3270_, v_filter_3271_, v_view_x3f_3272_, v_toBind_3273_, v___f_3274_, v___f_3275_, v___x_3276_, v_____do__lift_3277_);
lean_dec(v_____do__lift_3277_);
return v_res_3278_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg(lean_object* v_inst_3279_, lean_object* v_inst_3280_, lean_object* v_inst_3281_, lean_object* v_inst_3282_, lean_object* v_inst_3283_, lean_object* v_inst_3284_, lean_object* v_n_u2080_3285_, lean_object* v_filter_3286_, lean_object* v_view_x3f_3287_, lean_object* v_n_3288_){
_start:
{
lean_object* v___f_3289_; lean_object* v___f_3290_; lean_object* v___f_3291_; lean_object* v___f_3292_; lean_object* v___f_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___y_3300_; uint8_t v___x_3308_; uint8_t v___x_3309_; 
lean_inc_ref_n(v_inst_3279_, 7);
v___f_3289_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_3289_, 0, v_inst_3279_);
v___f_3290_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__3), 5, 1);
lean_closure_set(v___f_3290_, 0, v_inst_3279_);
v___f_3291_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__6), 5, 1);
lean_closure_set(v___f_3291_, 0, v_inst_3279_);
v___f_3292_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_3292_, 0, v_inst_3279_);
v___f_3293_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__11), 5, 1);
lean_closure_set(v___f_3293_, 0, v_inst_3279_);
v___x_3294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3294_, 0, v___f_3289_);
lean_ctor_set(v___x_3294_, 1, v___f_3290_);
v___x_3295_ = lean_alloc_closure((void*)(l_OptionT_pure), 4, 2);
lean_closure_set(v___x_3295_, 0, lean_box(0));
lean_closure_set(v___x_3295_, 1, v_inst_3279_);
v___x_3296_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3296_, 0, v___x_3294_);
lean_ctor_set(v___x_3296_, 1, v___x_3295_);
lean_ctor_set(v___x_3296_, 2, v___f_3291_);
lean_ctor_set(v___x_3296_, 3, v___f_3292_);
lean_ctor_set(v___x_3296_, 4, v___f_3293_);
v___x_3297_ = lean_alloc_closure((void*)(l_OptionT_bind), 6, 2);
lean_closure_set(v___x_3297_, 0, lean_box(0));
lean_closure_set(v___x_3297_, 1, v_inst_3279_);
v___x_3298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3298_, 0, v___x_3296_);
lean_ctor_set(v___x_3298_, 1, v___x_3297_);
v___x_3308_ = l_Lean_Name_hasMacroScopes(v_n_3288_);
v___x_3309_ = lean_bool_not(v___x_3308_);
if (v___x_3309_ == 0)
{
lean_object* v_toApplicative_3310_; lean_object* v_toPure_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; 
v_toApplicative_3310_ = lean_ctor_get(v_inst_3279_, 0);
v_toPure_3311_ = lean_ctor_get(v_toApplicative_3310_, 1);
v___x_3312_ = lean_box(0);
lean_inc(v_toPure_3311_);
v___x_3313_ = lean_apply_2(v_toPure_3311_, lean_box(0), v___x_3312_);
v___y_3300_ = v___x_3313_;
goto v___jp_3299_;
}
else
{
lean_object* v_toApplicative_3314_; lean_object* v_toPure_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; 
v_toApplicative_3314_ = lean_ctor_get(v_inst_3279_, 0);
v_toPure_3315_ = lean_ctor_get(v_toApplicative_3314_, 1);
v___x_3316_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2___closed__0));
lean_inc(v_toPure_3315_);
v___x_3317_ = lean_apply_2(v_toPure_3315_, lean_box(0), v___x_3316_);
v___y_3300_ = v___x_3317_;
goto v___jp_3299_;
}
v___jp_3299_:
{
lean_object* v_toApplicative_3301_; lean_object* v_toBind_3302_; lean_object* v_toPure_3303_; lean_object* v___f_3304_; lean_object* v___f_3305_; lean_object* v___f_3306_; lean_object* v___x_3307_; 
v_toApplicative_3301_ = lean_ctor_get(v_inst_3279_, 0);
v_toBind_3302_ = lean_ctor_get(v_inst_3279_, 1);
lean_inc_n(v_toBind_3302_, 2);
v_toPure_3303_ = lean_ctor_get(v_toApplicative_3301_, 1);
lean_inc_n(v_toPure_3303_, 3);
v___f_3304_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3304_, 0, v_toPure_3303_);
v___f_3305_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__1), 2, 1);
lean_closure_set(v___f_3305_, 0, v_toPure_3303_);
v___f_3306_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__5___boxed), 16, 15);
lean_closure_set(v___f_3306_, 0, v_toPure_3303_);
lean_closure_set(v___f_3306_, 1, v_n_3288_);
lean_closure_set(v___f_3306_, 2, v_inst_3279_);
lean_closure_set(v___f_3306_, 3, v_inst_3280_);
lean_closure_set(v___f_3306_, 4, v_inst_3281_);
lean_closure_set(v___f_3306_, 5, v_inst_3282_);
lean_closure_set(v___f_3306_, 6, v_inst_3283_);
lean_closure_set(v___f_3306_, 7, v_inst_3284_);
lean_closure_set(v___f_3306_, 8, v_n_u2080_3285_);
lean_closure_set(v___f_3306_, 9, v_filter_3286_);
lean_closure_set(v___f_3306_, 10, v_view_x3f_3287_);
lean_closure_set(v___f_3306_, 11, v_toBind_3302_);
lean_closure_set(v___f_3306_, 12, v___f_3305_);
lean_closure_set(v___f_3306_, 13, v___f_3304_);
lean_closure_set(v___f_3306_, 14, v___x_3298_);
v___x_3307_ = lean_apply_4(v_toBind_3302_, lean_box(0), lean_box(0), v___y_3300_, v___f_3306_);
return v___x_3307_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore(lean_object* v_m_3318_, lean_object* v_inst_3319_, lean_object* v_inst_3320_, lean_object* v_inst_3321_, lean_object* v_inst_3322_, lean_object* v_inst_3323_, lean_object* v_inst_3324_, lean_object* v_n_u2080_3325_, lean_object* v_filter_3326_, lean_object* v_view_x3f_3327_, lean_object* v_n_3328_){
_start:
{
lean_object* v___x_3329_; 
v___x_3329_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg(v_inst_3319_, v_inst_3320_, v_inst_3321_, v_inst_3322_, v_inst_3323_, v_inst_3324_, v_n_u2080_3325_, v_filter_3326_, v_view_x3f_3327_, v_n_3328_);
return v___x_3329_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___lam__0(lean_object* v_n_u2081_3330_, lean_object* v_x1_3331_, lean_object* v_x2_3332_){
_start:
{
lean_object* v___x_3333_; lean_object* v___x_3334_; uint8_t v___x_3335_; 
v___x_3333_ = l_Lean_Name_getPrefix(v_x2_3332_);
v___x_3334_ = l_Lean_Name_getPrefix(v_n_u2081_3330_);
v___x_3335_ = l_Lean_Name_isPrefixOf(v___x_3333_, v___x_3334_);
lean_dec(v___x_3334_);
lean_dec(v___x_3333_);
if (v___x_3335_ == 0)
{
lean_dec(v_x2_3332_);
return v_x1_3331_;
}
else
{
lean_object* v___x_3336_; 
v___x_3336_ = lean_array_push(v_x1_3331_, v_x2_3332_);
return v___x_3336_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___lam__0___boxed(lean_object* v_n_u2081_3337_, lean_object* v_x1_3338_, lean_object* v_x2_3339_){
_start:
{
lean_object* v_res_3340_; 
v_res_3340_ = l_Lean_unresolveNameGlobal_x3f___redArg___lam__0(v_n_u2081_3337_, v_x1_3338_, v_x2_3339_);
lean_dec(v_n_u2081_3337_);
return v_res_3340_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___lam__1(lean_object* v_view_3341_, lean_object* v_n_u2081_3342_, lean_object* v_inst_3343_, lean_object* v_inst_3344_, lean_object* v_inst_3345_, lean_object* v_inst_3346_, lean_object* v_inst_3347_, lean_object* v_inst_3348_, lean_object* v_n_u2080_3349_, lean_object* v_filter_3350_, lean_object* v_toPure_3351_, lean_object* v_____do__lift_3352_){
_start:
{
if (lean_obj_tag(v_____do__lift_3352_) == 0)
{
lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; 
lean_dec(v_toPure_3351_);
v___x_3353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3353_, 0, v_view_3341_);
v___x_3354_ = l_Lean_rootNamespace;
v___x_3355_ = l_Lean_Name_append(v___x_3354_, v_n_u2081_3342_);
v___x_3356_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg(v_inst_3343_, v_inst_3344_, v_inst_3345_, v_inst_3346_, v_inst_3347_, v_inst_3348_, v_n_u2080_3349_, v_filter_3350_, v___x_3353_, v___x_3355_);
return v___x_3356_;
}
else
{
lean_object* v___x_3357_; 
lean_dec(v_filter_3350_);
lean_dec(v_n_u2080_3349_);
lean_dec(v_inst_3348_);
lean_dec_ref(v_inst_3347_);
lean_dec(v_inst_3346_);
lean_dec_ref(v_inst_3345_);
lean_dec_ref(v_inst_3344_);
lean_dec_ref(v_inst_3343_);
lean_dec(v_n_u2081_3342_);
lean_dec_ref(v_view_3341_);
v___x_3357_ = lean_apply_2(v_toPure_3351_, lean_box(0), v_____do__lift_3352_);
return v___x_3357_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___lam__2(lean_object* v_toPure_3358_, lean_object* v_inst_3359_, lean_object* v_inst_3360_, lean_object* v_inst_3361_, lean_object* v_inst_3362_, lean_object* v_inst_3363_, lean_object* v_inst_3364_, lean_object* v_n_u2080_3365_, lean_object* v_filter_3366_, lean_object* v_toBind_3367_, lean_object* v___f_3368_, uint8_t v_allowHorizAliases_3369_, lean_object* v___f_3370_, lean_object* v_____do__lift_3371_){
_start:
{
lean_object* v_aliases_3373_; 
if (lean_obj_tag(v_____do__lift_3371_) == 0)
{
lean_object* v___x_3380_; lean_object* v___x_3381_; 
lean_dec_ref(v___f_3370_);
lean_dec(v___f_3368_);
lean_dec(v_toBind_3367_);
lean_dec(v_filter_3366_);
lean_dec(v_n_u2080_3365_);
lean_dec(v_inst_3364_);
lean_dec_ref(v_inst_3363_);
lean_dec(v_inst_3362_);
lean_dec_ref(v_inst_3361_);
lean_dec_ref(v_inst_3360_);
lean_dec_ref(v_inst_3359_);
v___x_3380_ = lean_box(0);
v___x_3381_ = lean_apply_2(v_toPure_3358_, lean_box(0), v___x_3380_);
return v___x_3381_;
}
else
{
lean_object* v_val_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; 
lean_dec(v_toPure_3358_);
v_val_3382_ = lean_ctor_get(v_____do__lift_3371_, 0);
lean_inc(v_val_3382_);
lean_dec_ref_known(v_____do__lift_3371_, 1);
lean_inc(v_n_u2080_3365_);
v___x_3383_ = l_Lean_getRevAliases(v_val_3382_, v_n_u2080_3365_);
v___x_3384_ = lean_array_mk(v___x_3383_);
if (v_allowHorizAliases_3369_ == 0)
{
lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; uint8_t v___x_3389_; 
v___x_3385_ = lean_unsigned_to_nat(0u);
v___x_3386_ = lean_array_get_size(v___x_3384_);
v___x_3387_ = ((lean_object*)(l_Lean_resolveNamespace___redArg___closed__1));
v___x_3388_ = ((lean_object*)(l_Lean_resolveLocalName___redArg___lam__3___closed__9));
v___x_3389_ = lean_nat_dec_lt(v___x_3385_, v___x_3386_);
if (v___x_3389_ == 0)
{
lean_dec_ref(v___x_3384_);
lean_dec_ref(v___f_3370_);
v_aliases_3373_ = v___x_3387_;
goto v___jp_3372_;
}
else
{
uint8_t v___x_3390_; 
v___x_3390_ = lean_nat_dec_le(v___x_3386_, v___x_3386_);
if (v___x_3390_ == 0)
{
if (v___x_3389_ == 0)
{
lean_dec_ref(v___x_3384_);
lean_dec_ref(v___f_3370_);
v_aliases_3373_ = v___x_3387_;
goto v___jp_3372_;
}
else
{
size_t v___x_3391_; size_t v___x_3392_; lean_object* v___x_3393_; 
v___x_3391_ = ((size_t)0ULL);
v___x_3392_ = lean_usize_of_nat(v___x_3386_);
v___x_3393_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3388_, v___f_3370_, v___x_3384_, v___x_3391_, v___x_3392_, v___x_3387_);
v_aliases_3373_ = v___x_3393_;
goto v___jp_3372_;
}
}
else
{
size_t v___x_3394_; size_t v___x_3395_; lean_object* v___x_3396_; 
v___x_3394_ = ((size_t)0ULL);
v___x_3395_ = lean_usize_of_nat(v___x_3386_);
v___x_3396_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3388_, v___f_3370_, v___x_3384_, v___x_3394_, v___x_3395_, v___x_3387_);
v_aliases_3373_ = v___x_3396_;
goto v___jp_3372_;
}
}
}
else
{
lean_dec_ref(v___f_3370_);
v_aliases_3373_ = v___x_3384_;
goto v___jp_3372_;
}
}
v___jp_3372_:
{
lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; 
lean_inc_ref(v_inst_3359_);
v___x_3374_ = l_OptionT_instAlternative___redArg(v_inst_3359_);
v___x_3375_ = lean_box(0);
v___x_3376_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore), 11, 10);
lean_closure_set(v___x_3376_, 0, lean_box(0));
lean_closure_set(v___x_3376_, 1, v_inst_3359_);
lean_closure_set(v___x_3376_, 2, v_inst_3360_);
lean_closure_set(v___x_3376_, 3, v_inst_3361_);
lean_closure_set(v___x_3376_, 4, v_inst_3362_);
lean_closure_set(v___x_3376_, 5, v_inst_3363_);
lean_closure_set(v___x_3376_, 6, v_inst_3364_);
lean_closure_set(v___x_3376_, 7, v_n_u2080_3365_);
lean_closure_set(v___x_3376_, 8, v_filter_3366_);
lean_closure_set(v___x_3376_, 9, v___x_3375_);
v___x_3377_ = lean_unsigned_to_nat(0u);
v___x_3378_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go(lean_box(0), lean_box(0), lean_box(0), v___x_3374_, v___x_3376_, v_aliases_3373_, v___x_3377_);
v___x_3379_ = lean_apply_4(v_toBind_3367_, lean_box(0), lean_box(0), v___x_3378_, v___f_3368_);
return v___x_3379_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___lam__2___boxed(lean_object* v_toPure_3397_, lean_object* v_inst_3398_, lean_object* v_inst_3399_, lean_object* v_inst_3400_, lean_object* v_inst_3401_, lean_object* v_inst_3402_, lean_object* v_inst_3403_, lean_object* v_n_u2080_3404_, lean_object* v_filter_3405_, lean_object* v_toBind_3406_, lean_object* v___f_3407_, lean_object* v_allowHorizAliases_3408_, lean_object* v___f_3409_, lean_object* v_____do__lift_3410_){
_start:
{
uint8_t v_allowHorizAliases_boxed_3411_; lean_object* v_res_3412_; 
v_allowHorizAliases_boxed_3411_ = lean_unbox(v_allowHorizAliases_3408_);
v_res_3412_ = l_Lean_unresolveNameGlobal_x3f___redArg___lam__2(v_toPure_3397_, v_inst_3398_, v_inst_3399_, v_inst_3400_, v_inst_3401_, v_inst_3402_, v_inst_3403_, v_n_u2080_3404_, v_filter_3405_, v_toBind_3406_, v___f_3407_, v_allowHorizAliases_boxed_3411_, v___f_3409_, v_____do__lift_3410_);
return v_res_3412_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___lam__3(lean_object* v_toPure_3413_, lean_object* v_____do__lift_3414_){
_start:
{
lean_object* v___x_3415_; lean_object* v___x_3416_; 
v___x_3415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3415_, 0, v_____do__lift_3414_);
v___x_3416_ = lean_apply_2(v_toPure_3413_, lean_box(0), v___x_3415_);
return v___x_3416_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___lam__4(lean_object* v_n_u2081_3417_, lean_object* v_inst_3418_, lean_object* v_inst_3419_, lean_object* v_inst_3420_, lean_object* v_inst_3421_, lean_object* v_inst_3422_, lean_object* v_inst_3423_, lean_object* v_n_u2080_3424_, lean_object* v_filter_3425_, lean_object* v___x_3426_, lean_object* v_toPure_3427_, lean_object* v_____do__lift_3428_){
_start:
{
if (lean_obj_tag(v_____do__lift_3428_) == 0)
{
lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; 
lean_dec(v_toPure_3427_);
v___x_3429_ = l_Lean_rootNamespace;
v___x_3430_ = l_Lean_Name_append(v___x_3429_, v_n_u2081_3417_);
v___x_3431_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg(v_inst_3418_, v_inst_3419_, v_inst_3420_, v_inst_3421_, v_inst_3422_, v_inst_3423_, v_n_u2080_3424_, v_filter_3425_, v___x_3426_, v___x_3430_);
return v___x_3431_;
}
else
{
lean_object* v___x_3432_; 
lean_dec(v___x_3426_);
lean_dec(v_filter_3425_);
lean_dec(v_n_u2080_3424_);
lean_dec(v_inst_3423_);
lean_dec_ref(v_inst_3422_);
lean_dec(v_inst_3421_);
lean_dec_ref(v_inst_3420_);
lean_dec_ref(v_inst_3419_);
lean_dec_ref(v_inst_3418_);
lean_dec(v_n_u2081_3417_);
v___x_3432_ = lean_apply_2(v_toPure_3427_, lean_box(0), v_____do__lift_3428_);
return v___x_3432_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg(lean_object* v_inst_3433_, lean_object* v_inst_3434_, lean_object* v_inst_3435_, lean_object* v_inst_3436_, lean_object* v_inst_3437_, lean_object* v_inst_3438_, lean_object* v_n_u2080_3439_, uint8_t v_fullNames_3440_, uint8_t v_allowHorizAliases_3441_, lean_object* v_filter_3442_){
_start:
{
lean_object* v_view_3443_; lean_object* v_name_3444_; lean_object* v_n_u2081_3445_; 
lean_inc(v_n_u2080_3439_);
v_view_3443_ = l_Lean_extractMacroScopes(v_n_u2080_3439_);
v_name_3444_ = lean_ctor_get(v_view_3443_, 0);
lean_inc(v_name_3444_);
v_n_u2081_3445_ = l_Lean_privateToUserName(v_name_3444_);
if (v_fullNames_3440_ == 0)
{
lean_object* v_toApplicative_3446_; lean_object* v_getEnv_3447_; lean_object* v_toBind_3448_; lean_object* v_toPure_3449_; lean_object* v___f_3450_; lean_object* v___f_3451_; lean_object* v___x_3452_; lean_object* v___f_3453_; lean_object* v___f_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; 
v_toApplicative_3446_ = lean_ctor_get(v_inst_3433_, 0);
v_getEnv_3447_ = lean_ctor_get(v_inst_3435_, 0);
lean_inc(v_getEnv_3447_);
v_toBind_3448_ = lean_ctor_get(v_inst_3433_, 1);
lean_inc_n(v_toBind_3448_, 3);
v_toPure_3449_ = lean_ctor_get(v_toApplicative_3446_, 1);
lean_inc_n(v_toPure_3449_, 3);
lean_inc(v_n_u2081_3445_);
v___f_3450_ = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal_x3f___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3450_, 0, v_n_u2081_3445_);
lean_inc(v_filter_3442_);
lean_inc(v_n_u2080_3439_);
lean_inc(v_inst_3438_);
lean_inc_ref(v_inst_3437_);
lean_inc(v_inst_3436_);
lean_inc_ref(v_inst_3435_);
lean_inc_ref(v_inst_3434_);
lean_inc_ref(v_inst_3433_);
v___f_3451_ = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal_x3f___redArg___lam__1), 12, 11);
lean_closure_set(v___f_3451_, 0, v_view_3443_);
lean_closure_set(v___f_3451_, 1, v_n_u2081_3445_);
lean_closure_set(v___f_3451_, 2, v_inst_3433_);
lean_closure_set(v___f_3451_, 3, v_inst_3434_);
lean_closure_set(v___f_3451_, 4, v_inst_3435_);
lean_closure_set(v___f_3451_, 5, v_inst_3436_);
lean_closure_set(v___f_3451_, 6, v_inst_3437_);
lean_closure_set(v___f_3451_, 7, v_inst_3438_);
lean_closure_set(v___f_3451_, 8, v_n_u2080_3439_);
lean_closure_set(v___f_3451_, 9, v_filter_3442_);
lean_closure_set(v___f_3451_, 10, v_toPure_3449_);
v___x_3452_ = lean_box(v_allowHorizAliases_3441_);
v___f_3453_ = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal_x3f___redArg___lam__2___boxed), 14, 13);
lean_closure_set(v___f_3453_, 0, v_toPure_3449_);
lean_closure_set(v___f_3453_, 1, v_inst_3433_);
lean_closure_set(v___f_3453_, 2, v_inst_3434_);
lean_closure_set(v___f_3453_, 3, v_inst_3435_);
lean_closure_set(v___f_3453_, 4, v_inst_3436_);
lean_closure_set(v___f_3453_, 5, v_inst_3437_);
lean_closure_set(v___f_3453_, 6, v_inst_3438_);
lean_closure_set(v___f_3453_, 7, v_n_u2080_3439_);
lean_closure_set(v___f_3453_, 8, v_filter_3442_);
lean_closure_set(v___f_3453_, 9, v_toBind_3448_);
lean_closure_set(v___f_3453_, 10, v___f_3451_);
lean_closure_set(v___f_3453_, 11, v___x_3452_);
lean_closure_set(v___f_3453_, 12, v___f_3450_);
v___f_3454_ = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal_x3f___redArg___lam__3), 2, 1);
lean_closure_set(v___f_3454_, 0, v_toPure_3449_);
v___x_3455_ = lean_apply_4(v_toBind_3448_, lean_box(0), lean_box(0), v_getEnv_3447_, v___f_3454_);
v___x_3456_ = lean_apply_4(v_toBind_3448_, lean_box(0), lean_box(0), v___x_3455_, v___f_3453_);
return v___x_3456_;
}
else
{
lean_object* v_toApplicative_3457_; lean_object* v_toBind_3458_; lean_object* v_toPure_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___f_3462_; lean_object* v___x_3463_; 
v_toApplicative_3457_ = lean_ctor_get(v_inst_3433_, 0);
v_toBind_3458_ = lean_ctor_get(v_inst_3433_, 1);
lean_inc(v_toBind_3458_);
v_toPure_3459_ = lean_ctor_get(v_toApplicative_3457_, 1);
lean_inc(v_toPure_3459_);
v___x_3460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3460_, 0, v_view_3443_);
lean_inc(v_n_u2081_3445_);
lean_inc_ref(v___x_3460_);
lean_inc(v_filter_3442_);
lean_inc(v_n_u2080_3439_);
lean_inc(v_inst_3438_);
lean_inc_ref(v_inst_3437_);
lean_inc(v_inst_3436_);
lean_inc_ref(v_inst_3435_);
lean_inc_ref(v_inst_3434_);
lean_inc_ref(v_inst_3433_);
v___x_3461_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg(v_inst_3433_, v_inst_3434_, v_inst_3435_, v_inst_3436_, v_inst_3437_, v_inst_3438_, v_n_u2080_3439_, v_filter_3442_, v___x_3460_, v_n_u2081_3445_);
v___f_3462_ = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal_x3f___redArg___lam__4), 12, 11);
lean_closure_set(v___f_3462_, 0, v_n_u2081_3445_);
lean_closure_set(v___f_3462_, 1, v_inst_3433_);
lean_closure_set(v___f_3462_, 2, v_inst_3434_);
lean_closure_set(v___f_3462_, 3, v_inst_3435_);
lean_closure_set(v___f_3462_, 4, v_inst_3436_);
lean_closure_set(v___f_3462_, 5, v_inst_3437_);
lean_closure_set(v___f_3462_, 6, v_inst_3438_);
lean_closure_set(v___f_3462_, 7, v_n_u2080_3439_);
lean_closure_set(v___f_3462_, 8, v_filter_3442_);
lean_closure_set(v___f_3462_, 9, v___x_3460_);
lean_closure_set(v___f_3462_, 10, v_toPure_3459_);
v___x_3463_ = lean_apply_4(v_toBind_3458_, lean_box(0), lean_box(0), v___x_3461_, v___f_3462_);
return v___x_3463_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___boxed(lean_object* v_inst_3464_, lean_object* v_inst_3465_, lean_object* v_inst_3466_, lean_object* v_inst_3467_, lean_object* v_inst_3468_, lean_object* v_inst_3469_, lean_object* v_n_u2080_3470_, lean_object* v_fullNames_3471_, lean_object* v_allowHorizAliases_3472_, lean_object* v_filter_3473_){
_start:
{
uint8_t v_fullNames_boxed_3474_; uint8_t v_allowHorizAliases_boxed_3475_; lean_object* v_res_3476_; 
v_fullNames_boxed_3474_ = lean_unbox(v_fullNames_3471_);
v_allowHorizAliases_boxed_3475_ = lean_unbox(v_allowHorizAliases_3472_);
v_res_3476_ = l_Lean_unresolveNameGlobal_x3f___redArg(v_inst_3464_, v_inst_3465_, v_inst_3466_, v_inst_3467_, v_inst_3468_, v_inst_3469_, v_n_u2080_3470_, v_fullNames_boxed_3474_, v_allowHorizAliases_boxed_3475_, v_filter_3473_);
return v_res_3476_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f(lean_object* v_m_3477_, lean_object* v_inst_3478_, lean_object* v_inst_3479_, lean_object* v_inst_3480_, lean_object* v_inst_3481_, lean_object* v_inst_3482_, lean_object* v_inst_3483_, lean_object* v_n_u2080_3484_, uint8_t v_fullNames_3485_, uint8_t v_allowHorizAliases_3486_, lean_object* v_filter_3487_){
_start:
{
lean_object* v___x_3488_; 
v___x_3488_ = l_Lean_unresolveNameGlobal_x3f___redArg(v_inst_3478_, v_inst_3479_, v_inst_3480_, v_inst_3481_, v_inst_3482_, v_inst_3483_, v_n_u2080_3484_, v_fullNames_3485_, v_allowHorizAliases_3486_, v_filter_3487_);
return v___x_3488_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___boxed(lean_object* v_m_3489_, lean_object* v_inst_3490_, lean_object* v_inst_3491_, lean_object* v_inst_3492_, lean_object* v_inst_3493_, lean_object* v_inst_3494_, lean_object* v_inst_3495_, lean_object* v_n_u2080_3496_, lean_object* v_fullNames_3497_, lean_object* v_allowHorizAliases_3498_, lean_object* v_filter_3499_){
_start:
{
uint8_t v_fullNames_boxed_3500_; uint8_t v_allowHorizAliases_boxed_3501_; lean_object* v_res_3502_; 
v_fullNames_boxed_3500_ = lean_unbox(v_fullNames_3497_);
v_allowHorizAliases_boxed_3501_ = lean_unbox(v_allowHorizAliases_3498_);
v_res_3502_ = l_Lean_unresolveNameGlobal_x3f(v_m_3489_, v_inst_3490_, v_inst_3491_, v_inst_3492_, v_inst_3493_, v_inst_3494_, v_inst_3495_, v_n_u2080_3496_, v_fullNames_boxed_3500_, v_allowHorizAliases_boxed_3501_, v_filter_3499_);
return v_res_3502_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___redArg___lam__0(lean_object* v_toPure_3503_, lean_object* v_n_u2080_3504_, lean_object* v_n_x3f_3505_){
_start:
{
if (lean_obj_tag(v_n_x3f_3505_) == 0)
{
lean_object* v___x_3506_; 
v___x_3506_ = lean_apply_2(v_toPure_3503_, lean_box(0), v_n_u2080_3504_);
return v___x_3506_;
}
else
{
lean_object* v_val_3507_; lean_object* v___x_3508_; 
lean_dec(v_n_u2080_3504_);
v_val_3507_ = lean_ctor_get(v_n_x3f_3505_, 0);
lean_inc(v_val_3507_);
lean_dec_ref_known(v_n_x3f_3505_, 1);
v___x_3508_ = lean_apply_2(v_toPure_3503_, lean_box(0), v_val_3507_);
return v___x_3508_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___redArg(lean_object* v_inst_3509_, lean_object* v_inst_3510_, lean_object* v_inst_3511_, lean_object* v_inst_3512_, lean_object* v_inst_3513_, lean_object* v_inst_3514_, lean_object* v_n_u2080_3515_, uint8_t v_fullNames_3516_, uint8_t v_allowHorizAliases_3517_, lean_object* v_filter_3518_){
_start:
{
lean_object* v_toApplicative_3519_; lean_object* v_toBind_3520_; lean_object* v_toPure_3521_; lean_object* v___x_3522_; lean_object* v___f_3523_; lean_object* v___x_3524_; 
v_toApplicative_3519_ = lean_ctor_get(v_inst_3509_, 0);
v_toBind_3520_ = lean_ctor_get(v_inst_3509_, 1);
lean_inc(v_toBind_3520_);
v_toPure_3521_ = lean_ctor_get(v_toApplicative_3519_, 1);
lean_inc(v_toPure_3521_);
lean_inc(v_n_u2080_3515_);
v___x_3522_ = l_Lean_unresolveNameGlobal_x3f___redArg(v_inst_3509_, v_inst_3510_, v_inst_3511_, v_inst_3512_, v_inst_3513_, v_inst_3514_, v_n_u2080_3515_, v_fullNames_3516_, v_allowHorizAliases_3517_, v_filter_3518_);
v___f_3523_ = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3523_, 0, v_toPure_3521_);
lean_closure_set(v___f_3523_, 1, v_n_u2080_3515_);
v___x_3524_ = lean_apply_4(v_toBind_3520_, lean_box(0), lean_box(0), v___x_3522_, v___f_3523_);
return v___x_3524_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___redArg___boxed(lean_object* v_inst_3525_, lean_object* v_inst_3526_, lean_object* v_inst_3527_, lean_object* v_inst_3528_, lean_object* v_inst_3529_, lean_object* v_inst_3530_, lean_object* v_n_u2080_3531_, lean_object* v_fullNames_3532_, lean_object* v_allowHorizAliases_3533_, lean_object* v_filter_3534_){
_start:
{
uint8_t v_fullNames_boxed_3535_; uint8_t v_allowHorizAliases_boxed_3536_; lean_object* v_res_3537_; 
v_fullNames_boxed_3535_ = lean_unbox(v_fullNames_3532_);
v_allowHorizAliases_boxed_3536_ = lean_unbox(v_allowHorizAliases_3533_);
v_res_3537_ = l_Lean_unresolveNameGlobal___redArg(v_inst_3525_, v_inst_3526_, v_inst_3527_, v_inst_3528_, v_inst_3529_, v_inst_3530_, v_n_u2080_3531_, v_fullNames_boxed_3535_, v_allowHorizAliases_boxed_3536_, v_filter_3534_);
return v_res_3537_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal(lean_object* v_m_3538_, lean_object* v_inst_3539_, lean_object* v_inst_3540_, lean_object* v_inst_3541_, lean_object* v_inst_3542_, lean_object* v_inst_3543_, lean_object* v_inst_3544_, lean_object* v_n_u2080_3545_, uint8_t v_fullNames_3546_, uint8_t v_allowHorizAliases_3547_, lean_object* v_filter_3548_){
_start:
{
lean_object* v___x_3549_; 
v___x_3549_ = l_Lean_unresolveNameGlobal___redArg(v_inst_3539_, v_inst_3540_, v_inst_3541_, v_inst_3542_, v_inst_3543_, v_inst_3544_, v_n_u2080_3545_, v_fullNames_3546_, v_allowHorizAliases_3547_, v_filter_3548_);
return v___x_3549_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___boxed(lean_object* v_m_3550_, lean_object* v_inst_3551_, lean_object* v_inst_3552_, lean_object* v_inst_3553_, lean_object* v_inst_3554_, lean_object* v_inst_3555_, lean_object* v_inst_3556_, lean_object* v_n_u2080_3557_, lean_object* v_fullNames_3558_, lean_object* v_allowHorizAliases_3559_, lean_object* v_filter_3560_){
_start:
{
uint8_t v_fullNames_boxed_3561_; uint8_t v_allowHorizAliases_boxed_3562_; lean_object* v_res_3563_; 
v_fullNames_boxed_3561_ = lean_unbox(v_fullNames_3558_);
v_allowHorizAliases_boxed_3562_ = lean_unbox(v_allowHorizAliases_3559_);
v_res_3563_ = l_Lean_unresolveNameGlobal(v_m_3550_, v_inst_3551_, v_inst_3552_, v_inst_3553_, v_inst_3554_, v_inst_3555_, v_inst_3556_, v_n_u2080_3557_, v_fullNames_boxed_3561_, v_allowHorizAliases_boxed_3562_, v_filter_3560_);
return v_res_3563_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg___lam__0(lean_object* v_toFunctor_3565_, lean_object* v_inst_3566_, lean_object* v_inst_3567_, lean_object* v_inst_3568_, lean_object* v_inst_3569_, lean_object* v_inst_3570_, lean_object* v_inst_3571_, lean_object* v_inst_3572_, lean_object* v_n_3573_){
_start:
{
lean_object* v_map_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; 
v_map_3574_ = lean_ctor_get(v_toFunctor_3565_, 0);
lean_inc(v_map_3574_);
lean_dec_ref(v_toFunctor_3565_);
v___x_3575_ = ((lean_object*)(l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg___lam__0___closed__0));
v___x_3576_ = l_Lean_resolveLocalName___redArg(v_inst_3566_, v_inst_3567_, v_inst_3568_, v_inst_3569_, v_inst_3570_, v_inst_3571_, v_inst_3572_, v_n_3573_);
v___x_3577_ = lean_apply_4(v_map_3574_, lean_box(0), lean_box(0), v___x_3575_, v___x_3576_);
return v___x_3577_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg(lean_object* v_inst_3578_, lean_object* v_inst_3579_, lean_object* v_inst_3580_, lean_object* v_inst_3581_, lean_object* v_inst_3582_, lean_object* v_inst_3583_, lean_object* v_inst_3584_, lean_object* v_n_u2080_3585_, uint8_t v_fullNames_3586_){
_start:
{
lean_object* v_toApplicative_3587_; lean_object* v_toFunctor_3588_; uint8_t v___x_3589_; lean_object* v___f_3590_; lean_object* v___x_3591_; 
v_toApplicative_3587_ = lean_ctor_get(v_inst_3578_, 0);
v_toFunctor_3588_ = lean_ctor_get(v_toApplicative_3587_, 0);
v___x_3589_ = 0;
lean_inc(v_inst_3583_);
lean_inc_ref(v_inst_3582_);
lean_inc(v_inst_3581_);
lean_inc_ref(v_inst_3580_);
lean_inc_ref(v_inst_3579_);
lean_inc_ref(v_inst_3578_);
lean_inc_ref(v_toFunctor_3588_);
v___f_3590_ = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg___lam__0), 9, 8);
lean_closure_set(v___f_3590_, 0, v_toFunctor_3588_);
lean_closure_set(v___f_3590_, 1, v_inst_3578_);
lean_closure_set(v___f_3590_, 2, v_inst_3579_);
lean_closure_set(v___f_3590_, 3, v_inst_3580_);
lean_closure_set(v___f_3590_, 4, v_inst_3581_);
lean_closure_set(v___f_3590_, 5, v_inst_3582_);
lean_closure_set(v___f_3590_, 6, v_inst_3583_);
lean_closure_set(v___f_3590_, 7, v_inst_3584_);
v___x_3591_ = l_Lean_unresolveNameGlobal_x3f___redArg(v_inst_3578_, v_inst_3579_, v_inst_3580_, v_inst_3581_, v_inst_3582_, v_inst_3583_, v_n_u2080_3585_, v_fullNames_3586_, v___x_3589_, v___f_3590_);
return v___x_3591_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg___boxed(lean_object* v_inst_3592_, lean_object* v_inst_3593_, lean_object* v_inst_3594_, lean_object* v_inst_3595_, lean_object* v_inst_3596_, lean_object* v_inst_3597_, lean_object* v_inst_3598_, lean_object* v_n_u2080_3599_, lean_object* v_fullNames_3600_){
_start:
{
uint8_t v_fullNames_boxed_3601_; lean_object* v_res_3602_; 
v_fullNames_boxed_3601_ = lean_unbox(v_fullNames_3600_);
v_res_3602_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg(v_inst_3592_, v_inst_3593_, v_inst_3594_, v_inst_3595_, v_inst_3596_, v_inst_3597_, v_inst_3598_, v_n_u2080_3599_, v_fullNames_boxed_3601_);
return v_res_3602_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f(lean_object* v_m_3603_, lean_object* v_inst_3604_, lean_object* v_inst_3605_, lean_object* v_inst_3606_, lean_object* v_inst_3607_, lean_object* v_inst_3608_, lean_object* v_inst_3609_, lean_object* v_inst_3610_, lean_object* v_n_u2080_3611_, uint8_t v_fullNames_3612_){
_start:
{
lean_object* v___x_3613_; 
v___x_3613_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg(v_inst_3604_, v_inst_3605_, v_inst_3606_, v_inst_3607_, v_inst_3608_, v_inst_3609_, v_inst_3610_, v_n_u2080_3611_, v_fullNames_3612_);
return v___x_3613_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___boxed(lean_object* v_m_3614_, lean_object* v_inst_3615_, lean_object* v_inst_3616_, lean_object* v_inst_3617_, lean_object* v_inst_3618_, lean_object* v_inst_3619_, lean_object* v_inst_3620_, lean_object* v_inst_3621_, lean_object* v_n_u2080_3622_, lean_object* v_fullNames_3623_){
_start:
{
uint8_t v_fullNames_boxed_3624_; lean_object* v_res_3625_; 
v_fullNames_boxed_3624_ = lean_unbox(v_fullNames_3623_);
v_res_3625_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f(v_m_3614_, v_inst_3615_, v_inst_3616_, v_inst_3617_, v_inst_3618_, v_inst_3619_, v_inst_3620_, v_inst_3621_, v_n_u2080_3622_, v_fullNames_boxed_3624_);
return v_res_3625_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals___redArg(lean_object* v_inst_3626_, lean_object* v_inst_3627_, lean_object* v_inst_3628_, lean_object* v_inst_3629_, lean_object* v_inst_3630_, lean_object* v_inst_3631_, lean_object* v_inst_3632_, lean_object* v_n_u2080_3633_, uint8_t v_fullNames_3634_){
_start:
{
lean_object* v_toApplicative_3635_; lean_object* v_toBind_3636_; lean_object* v_toPure_3637_; lean_object* v___x_3638_; lean_object* v___f_3639_; lean_object* v___x_3640_; 
v_toApplicative_3635_ = lean_ctor_get(v_inst_3626_, 0);
v_toBind_3636_ = lean_ctor_get(v_inst_3626_, 1);
lean_inc(v_toBind_3636_);
v_toPure_3637_ = lean_ctor_get(v_toApplicative_3635_, 1);
lean_inc(v_toPure_3637_);
lean_inc(v_n_u2080_3633_);
v___x_3638_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg(v_inst_3626_, v_inst_3627_, v_inst_3628_, v_inst_3629_, v_inst_3630_, v_inst_3631_, v_inst_3632_, v_n_u2080_3633_, v_fullNames_3634_);
v___f_3639_ = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3639_, 0, v_toPure_3637_);
lean_closure_set(v___f_3639_, 1, v_n_u2080_3633_);
v___x_3640_ = lean_apply_4(v_toBind_3636_, lean_box(0), lean_box(0), v___x_3638_, v___f_3639_);
return v___x_3640_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals___redArg___boxed(lean_object* v_inst_3641_, lean_object* v_inst_3642_, lean_object* v_inst_3643_, lean_object* v_inst_3644_, lean_object* v_inst_3645_, lean_object* v_inst_3646_, lean_object* v_inst_3647_, lean_object* v_n_u2080_3648_, lean_object* v_fullNames_3649_){
_start:
{
uint8_t v_fullNames_boxed_3650_; lean_object* v_res_3651_; 
v_fullNames_boxed_3650_ = lean_unbox(v_fullNames_3649_);
v_res_3651_ = l_Lean_unresolveNameGlobalAvoidingLocals___redArg(v_inst_3641_, v_inst_3642_, v_inst_3643_, v_inst_3644_, v_inst_3645_, v_inst_3646_, v_inst_3647_, v_n_u2080_3648_, v_fullNames_boxed_3650_);
return v_res_3651_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals(lean_object* v_m_3652_, lean_object* v_inst_3653_, lean_object* v_inst_3654_, lean_object* v_inst_3655_, lean_object* v_inst_3656_, lean_object* v_inst_3657_, lean_object* v_inst_3658_, lean_object* v_inst_3659_, lean_object* v_n_u2080_3660_, uint8_t v_fullNames_3661_){
_start:
{
lean_object* v___x_3662_; 
v___x_3662_ = l_Lean_unresolveNameGlobalAvoidingLocals___redArg(v_inst_3653_, v_inst_3654_, v_inst_3655_, v_inst_3656_, v_inst_3657_, v_inst_3658_, v_inst_3659_, v_n_u2080_3660_, v_fullNames_3661_);
return v___x_3662_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals___boxed(lean_object* v_m_3663_, lean_object* v_inst_3664_, lean_object* v_inst_3665_, lean_object* v_inst_3666_, lean_object* v_inst_3667_, lean_object* v_inst_3668_, lean_object* v_inst_3669_, lean_object* v_inst_3670_, lean_object* v_n_u2080_3671_, lean_object* v_fullNames_3672_){
_start:
{
uint8_t v_fullNames_boxed_3673_; lean_object* v_res_3674_; 
v_fullNames_boxed_3673_ = lean_unbox(v_fullNames_3672_);
v_res_3674_ = l_Lean_unresolveNameGlobalAvoidingLocals(v_m_3663_, v_inst_3664_, v_inst_3665_, v_inst_3666_, v_inst_3667_, v_inst_3668_, v_inst_3669_, v_inst_3670_, v_n_u2080_3671_, v_fullNames_boxed_3673_);
return v_res_3674_;
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
