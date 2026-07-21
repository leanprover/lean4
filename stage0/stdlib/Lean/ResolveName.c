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
static uint64_t _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg___closed__0(void){
_start:
{
lean_object* v___x_178_; uint64_t v___x_179_; 
v___x_178_ = lean_unsigned_to_nat(1723u);
v___x_179_ = lean_uint64_of_nat(v___x_178_);
return v___x_179_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_180_; 
v___x_180_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg(lean_object* v_x_181_, size_t v_x_182_, size_t v_x_183_, lean_object* v_x_184_, lean_object* v_x_185_){
_start:
{
if (lean_obj_tag(v_x_181_) == 0)
{
lean_object* v_es_186_; size_t v___x_187_; size_t v___x_188_; lean_object* v_j_189_; lean_object* v___x_190_; uint8_t v___x_191_; 
v_es_186_ = lean_ctor_get(v_x_181_, 0);
v___x_187_ = ((size_t)31ULL);
v___x_188_ = lean_usize_land(v_x_182_, v___x_187_);
v_j_189_ = lean_usize_to_nat(v___x_188_);
v___x_190_ = lean_array_get_size(v_es_186_);
v___x_191_ = lean_nat_dec_lt(v_j_189_, v___x_190_);
if (v___x_191_ == 0)
{
lean_dec(v_j_189_);
lean_dec(v_x_185_);
lean_dec(v_x_184_);
return v_x_181_;
}
else
{
lean_object* v___x_193_; uint8_t v_isShared_194_; uint8_t v_isSharedCheck_230_; 
lean_inc_ref(v_es_186_);
v_isSharedCheck_230_ = !lean_is_exclusive(v_x_181_);
if (v_isSharedCheck_230_ == 0)
{
lean_object* v_unused_231_; 
v_unused_231_ = lean_ctor_get(v_x_181_, 0);
lean_dec(v_unused_231_);
v___x_193_ = v_x_181_;
v_isShared_194_ = v_isSharedCheck_230_;
goto v_resetjp_192_;
}
else
{
lean_dec(v_x_181_);
v___x_193_ = lean_box(0);
v_isShared_194_ = v_isSharedCheck_230_;
goto v_resetjp_192_;
}
v_resetjp_192_:
{
lean_object* v_v_195_; lean_object* v___x_196_; lean_object* v_xs_x27_197_; lean_object* v___y_199_; 
v_v_195_ = lean_array_fget(v_es_186_, v_j_189_);
v___x_196_ = lean_box(0);
v_xs_x27_197_ = lean_array_fset(v_es_186_, v_j_189_, v___x_196_);
switch(lean_obj_tag(v_v_195_))
{
case 0:
{
lean_object* v_key_204_; lean_object* v_val_205_; lean_object* v___x_207_; uint8_t v_isShared_208_; uint8_t v_isSharedCheck_215_; 
v_key_204_ = lean_ctor_get(v_v_195_, 0);
v_val_205_ = lean_ctor_get(v_v_195_, 1);
v_isSharedCheck_215_ = !lean_is_exclusive(v_v_195_);
if (v_isSharedCheck_215_ == 0)
{
v___x_207_ = v_v_195_;
v_isShared_208_ = v_isSharedCheck_215_;
goto v_resetjp_206_;
}
else
{
lean_inc(v_val_205_);
lean_inc(v_key_204_);
lean_dec(v_v_195_);
v___x_207_ = lean_box(0);
v_isShared_208_ = v_isSharedCheck_215_;
goto v_resetjp_206_;
}
v_resetjp_206_:
{
uint8_t v___x_209_; 
v___x_209_ = lean_name_eq(v_x_184_, v_key_204_);
if (v___x_209_ == 0)
{
lean_object* v___x_210_; lean_object* v___x_211_; 
lean_del_object(v___x_207_);
v___x_210_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_204_, v_val_205_, v_x_184_, v_x_185_);
v___x_211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_211_, 0, v___x_210_);
v___y_199_ = v___x_211_;
goto v___jp_198_;
}
else
{
lean_object* v___x_213_; 
lean_dec(v_val_205_);
lean_dec(v_key_204_);
if (v_isShared_208_ == 0)
{
lean_ctor_set(v___x_207_, 1, v_x_185_);
lean_ctor_set(v___x_207_, 0, v_x_184_);
v___x_213_ = v___x_207_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v_x_184_);
lean_ctor_set(v_reuseFailAlloc_214_, 1, v_x_185_);
v___x_213_ = v_reuseFailAlloc_214_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
v___y_199_ = v___x_213_;
goto v___jp_198_;
}
}
}
}
case 1:
{
lean_object* v_node_216_; lean_object* v___x_218_; uint8_t v_isShared_219_; uint8_t v_isSharedCheck_228_; 
v_node_216_ = lean_ctor_get(v_v_195_, 0);
v_isSharedCheck_228_ = !lean_is_exclusive(v_v_195_);
if (v_isSharedCheck_228_ == 0)
{
v___x_218_ = v_v_195_;
v_isShared_219_ = v_isSharedCheck_228_;
goto v_resetjp_217_;
}
else
{
lean_inc(v_node_216_);
lean_dec(v_v_195_);
v___x_218_ = lean_box(0);
v_isShared_219_ = v_isSharedCheck_228_;
goto v_resetjp_217_;
}
v_resetjp_217_:
{
size_t v___x_220_; size_t v___x_221_; size_t v___x_222_; size_t v___x_223_; lean_object* v___x_224_; lean_object* v___x_226_; 
v___x_220_ = ((size_t)5ULL);
v___x_221_ = lean_usize_shift_right(v_x_182_, v___x_220_);
v___x_222_ = ((size_t)1ULL);
v___x_223_ = lean_usize_add(v_x_183_, v___x_222_);
v___x_224_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg(v_node_216_, v___x_221_, v___x_223_, v_x_184_, v_x_185_);
if (v_isShared_219_ == 0)
{
lean_ctor_set(v___x_218_, 0, v___x_224_);
v___x_226_ = v___x_218_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v___x_224_);
v___x_226_ = v_reuseFailAlloc_227_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
v___y_199_ = v___x_226_;
goto v___jp_198_;
}
}
}
default: 
{
lean_object* v___x_229_; 
v___x_229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_229_, 0, v_x_184_);
lean_ctor_set(v___x_229_, 1, v_x_185_);
v___y_199_ = v___x_229_;
goto v___jp_198_;
}
}
v___jp_198_:
{
lean_object* v___x_200_; lean_object* v___x_202_; 
v___x_200_ = lean_array_fset(v_xs_x27_197_, v_j_189_, v___y_199_);
lean_dec(v_j_189_);
if (v_isShared_194_ == 0)
{
lean_ctor_set(v___x_193_, 0, v___x_200_);
v___x_202_ = v___x_193_;
goto v_reusejp_201_;
}
else
{
lean_object* v_reuseFailAlloc_203_; 
v_reuseFailAlloc_203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_203_, 0, v___x_200_);
v___x_202_ = v_reuseFailAlloc_203_;
goto v_reusejp_201_;
}
v_reusejp_201_:
{
return v___x_202_;
}
}
}
}
}
else
{
lean_object* v_ks_232_; lean_object* v_vs_233_; lean_object* v___x_235_; uint8_t v_isShared_236_; uint8_t v_isSharedCheck_253_; 
v_ks_232_ = lean_ctor_get(v_x_181_, 0);
v_vs_233_ = lean_ctor_get(v_x_181_, 1);
v_isSharedCheck_253_ = !lean_is_exclusive(v_x_181_);
if (v_isSharedCheck_253_ == 0)
{
v___x_235_ = v_x_181_;
v_isShared_236_ = v_isSharedCheck_253_;
goto v_resetjp_234_;
}
else
{
lean_inc(v_vs_233_);
lean_inc(v_ks_232_);
lean_dec(v_x_181_);
v___x_235_ = lean_box(0);
v_isShared_236_ = v_isSharedCheck_253_;
goto v_resetjp_234_;
}
v_resetjp_234_:
{
lean_object* v___x_238_; 
if (v_isShared_236_ == 0)
{
v___x_238_ = v___x_235_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v_ks_232_);
lean_ctor_set(v_reuseFailAlloc_252_, 1, v_vs_233_);
v___x_238_ = v_reuseFailAlloc_252_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
lean_object* v_newNode_239_; uint8_t v___y_241_; size_t v___x_247_; uint8_t v___x_248_; 
v_newNode_239_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__9___redArg(v___x_238_, v_x_184_, v_x_185_);
v___x_247_ = ((size_t)7ULL);
v___x_248_ = lean_usize_dec_le(v___x_247_, v_x_183_);
if (v___x_248_ == 0)
{
lean_object* v___x_249_; lean_object* v___x_250_; uint8_t v___x_251_; 
v___x_249_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_239_);
v___x_250_ = lean_unsigned_to_nat(4u);
v___x_251_ = lean_nat_dec_lt(v___x_249_, v___x_250_);
lean_dec(v___x_249_);
v___y_241_ = v___x_251_;
goto v___jp_240_;
}
else
{
v___y_241_ = v___x_248_;
goto v___jp_240_;
}
v___jp_240_:
{
if (v___y_241_ == 0)
{
lean_object* v_ks_242_; lean_object* v_vs_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; 
v_ks_242_ = lean_ctor_get(v_newNode_239_, 0);
lean_inc_ref(v_ks_242_);
v_vs_243_ = lean_ctor_get(v_newNode_239_, 1);
lean_inc_ref(v_vs_243_);
lean_dec_ref(v_newNode_239_);
v___x_244_ = lean_unsigned_to_nat(0u);
v___x_245_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg___closed__0);
v___x_246_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg(v_x_183_, v_ks_242_, v_vs_243_, v___x_244_, v___x_245_);
lean_dec_ref(v_vs_243_);
lean_dec_ref(v_ks_242_);
return v___x_246_;
}
else
{
return v_newNode_239_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg(size_t v_depth_254_, lean_object* v_keys_255_, lean_object* v_vals_256_, lean_object* v_i_257_, lean_object* v_entries_258_){
_start:
{
lean_object* v___x_259_; uint8_t v___x_260_; 
v___x_259_ = lean_array_get_size(v_keys_255_);
v___x_260_ = lean_nat_dec_lt(v_i_257_, v___x_259_);
if (v___x_260_ == 0)
{
lean_dec(v_i_257_);
return v_entries_258_;
}
else
{
lean_object* v_k_261_; lean_object* v_v_262_; uint64_t v___y_264_; 
v_k_261_ = lean_array_fget_borrowed(v_keys_255_, v_i_257_);
v_v_262_ = lean_array_fget_borrowed(v_vals_256_, v_i_257_);
if (lean_obj_tag(v_k_261_) == 0)
{
uint64_t v___x_275_; 
v___x_275_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg___closed__0);
v___y_264_ = v___x_275_;
goto v___jp_263_;
}
else
{
uint64_t v_hash_276_; 
v_hash_276_ = lean_ctor_get_uint64(v_k_261_, sizeof(void*)*2);
v___y_264_ = v_hash_276_;
goto v___jp_263_;
}
v___jp_263_:
{
size_t v_h_265_; size_t v___x_266_; lean_object* v___x_267_; size_t v___x_268_; size_t v___x_269_; size_t v___x_270_; size_t v_h_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
v_h_265_ = lean_uint64_to_usize(v___y_264_);
v___x_266_ = ((size_t)5ULL);
v___x_267_ = lean_unsigned_to_nat(1u);
v___x_268_ = ((size_t)1ULL);
v___x_269_ = lean_usize_sub(v_depth_254_, v___x_268_);
v___x_270_ = lean_usize_mul(v___x_266_, v___x_269_);
v_h_271_ = lean_usize_shift_right(v_h_265_, v___x_270_);
v___x_272_ = lean_nat_add(v_i_257_, v___x_267_);
lean_dec(v_i_257_);
lean_inc(v_v_262_);
lean_inc(v_k_261_);
v___x_273_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg(v_entries_258_, v_h_271_, v_depth_254_, v_k_261_, v_v_262_);
v_i_257_ = v___x_272_;
v_entries_258_ = v___x_273_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg___boxed(lean_object* v_depth_277_, lean_object* v_keys_278_, lean_object* v_vals_279_, lean_object* v_i_280_, lean_object* v_entries_281_){
_start:
{
size_t v_depth_boxed_282_; lean_object* v_res_283_; 
v_depth_boxed_282_ = lean_unbox_usize(v_depth_277_);
lean_dec(v_depth_277_);
v_res_283_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg(v_depth_boxed_282_, v_keys_278_, v_vals_279_, v_i_280_, v_entries_281_);
lean_dec_ref(v_vals_279_);
lean_dec_ref(v_keys_278_);
return v_res_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg___boxed(lean_object* v_x_284_, lean_object* v_x_285_, lean_object* v_x_286_, lean_object* v_x_287_, lean_object* v_x_288_){
_start:
{
size_t v_x_1094__boxed_289_; size_t v_x_1095__boxed_290_; lean_object* v_res_291_; 
v_x_1094__boxed_289_ = lean_unbox_usize(v_x_285_);
lean_dec(v_x_285_);
v_x_1095__boxed_290_ = lean_unbox_usize(v_x_286_);
lean_dec(v_x_286_);
v_res_291_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg(v_x_284_, v_x_1094__boxed_289_, v_x_1095__boxed_290_, v_x_287_, v_x_288_);
return v_res_291_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3___redArg(lean_object* v_x_292_, lean_object* v_x_293_, lean_object* v_x_294_){
_start:
{
uint64_t v___y_296_; 
if (lean_obj_tag(v_x_293_) == 0)
{
uint64_t v___x_300_; 
v___x_300_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg___closed__0);
v___y_296_ = v___x_300_;
goto v___jp_295_;
}
else
{
uint64_t v_hash_301_; 
v_hash_301_ = lean_ctor_get_uint64(v_x_293_, sizeof(void*)*2);
v___y_296_ = v_hash_301_;
goto v___jp_295_;
}
v___jp_295_:
{
size_t v___x_297_; size_t v___x_298_; lean_object* v___x_299_; 
v___x_297_ = lean_uint64_to_usize(v___y_296_);
v___x_298_ = ((size_t)1ULL);
v___x_299_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg(v_x_292_, v___x_297_, v___x_298_, v_x_293_, v_x_294_);
return v___x_299_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9_spec__14_spec__16___redArg(lean_object* v_x_302_, lean_object* v_x_303_){
_start:
{
if (lean_obj_tag(v_x_303_) == 0)
{
return v_x_302_;
}
else
{
lean_object* v_key_304_; lean_object* v_value_305_; lean_object* v_tail_306_; lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_332_; 
v_key_304_ = lean_ctor_get(v_x_303_, 0);
v_value_305_ = lean_ctor_get(v_x_303_, 1);
v_tail_306_ = lean_ctor_get(v_x_303_, 2);
v_isSharedCheck_332_ = !lean_is_exclusive(v_x_303_);
if (v_isSharedCheck_332_ == 0)
{
v___x_308_ = v_x_303_;
v_isShared_309_ = v_isSharedCheck_332_;
goto v_resetjp_307_;
}
else
{
lean_inc(v_tail_306_);
lean_inc(v_value_305_);
lean_inc(v_key_304_);
lean_dec(v_x_303_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_332_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
lean_object* v___x_310_; uint64_t v___y_312_; 
v___x_310_ = lean_array_get_size(v_x_302_);
if (lean_obj_tag(v_key_304_) == 0)
{
uint64_t v___x_330_; 
v___x_330_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg___closed__0);
v___y_312_ = v___x_330_;
goto v___jp_311_;
}
else
{
uint64_t v_hash_331_; 
v_hash_331_ = lean_ctor_get_uint64(v_key_304_, sizeof(void*)*2);
v___y_312_ = v_hash_331_;
goto v___jp_311_;
}
v___jp_311_:
{
uint64_t v___x_313_; uint64_t v___x_314_; uint64_t v_fold_315_; uint64_t v___x_316_; uint64_t v___x_317_; uint64_t v___x_318_; size_t v___x_319_; size_t v___x_320_; size_t v___x_321_; size_t v___x_322_; size_t v___x_323_; lean_object* v___x_324_; lean_object* v___x_326_; 
v___x_313_ = 32ULL;
v___x_314_ = lean_uint64_shift_right(v___y_312_, v___x_313_);
v_fold_315_ = lean_uint64_xor(v___y_312_, v___x_314_);
v___x_316_ = 16ULL;
v___x_317_ = lean_uint64_shift_right(v_fold_315_, v___x_316_);
v___x_318_ = lean_uint64_xor(v_fold_315_, v___x_317_);
v___x_319_ = lean_uint64_to_usize(v___x_318_);
v___x_320_ = lean_usize_of_nat(v___x_310_);
v___x_321_ = ((size_t)1ULL);
v___x_322_ = lean_usize_sub(v___x_320_, v___x_321_);
v___x_323_ = lean_usize_land(v___x_319_, v___x_322_);
v___x_324_ = lean_array_uget_borrowed(v_x_302_, v___x_323_);
lean_inc(v___x_324_);
if (v_isShared_309_ == 0)
{
lean_ctor_set(v___x_308_, 2, v___x_324_);
v___x_326_ = v___x_308_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v_key_304_);
lean_ctor_set(v_reuseFailAlloc_329_, 1, v_value_305_);
lean_ctor_set(v_reuseFailAlloc_329_, 2, v___x_324_);
v___x_326_ = v_reuseFailAlloc_329_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
lean_object* v___x_327_; 
v___x_327_ = lean_array_uset(v_x_302_, v___x_323_, v___x_326_);
v_x_302_ = v___x_327_;
v_x_303_ = v_tail_306_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9_spec__14___redArg(lean_object* v_i_333_, lean_object* v_source_334_, lean_object* v_target_335_){
_start:
{
lean_object* v___x_336_; uint8_t v___x_337_; 
v___x_336_ = lean_array_get_size(v_source_334_);
v___x_337_ = lean_nat_dec_lt(v_i_333_, v___x_336_);
if (v___x_337_ == 0)
{
lean_dec_ref(v_source_334_);
lean_dec(v_i_333_);
return v_target_335_;
}
else
{
lean_object* v_es_338_; lean_object* v___x_339_; lean_object* v_source_340_; lean_object* v_target_341_; lean_object* v___x_342_; lean_object* v___x_343_; 
v_es_338_ = lean_array_fget(v_source_334_, v_i_333_);
v___x_339_ = lean_box(0);
v_source_340_ = lean_array_fset(v_source_334_, v_i_333_, v___x_339_);
v_target_341_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9_spec__14_spec__16___redArg(v_target_335_, v_es_338_);
v___x_342_ = lean_unsigned_to_nat(1u);
v___x_343_ = lean_nat_add(v_i_333_, v___x_342_);
lean_dec(v_i_333_);
v_i_333_ = v___x_343_;
v_source_334_ = v_source_340_;
v_target_335_ = v_target_341_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9___redArg(lean_object* v_data_345_){
_start:
{
lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v_nbuckets_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_346_ = lean_array_get_size(v_data_345_);
v___x_347_ = lean_unsigned_to_nat(2u);
v_nbuckets_348_ = lean_nat_mul(v___x_346_, v___x_347_);
v___x_349_ = lean_unsigned_to_nat(0u);
v___x_350_ = lean_box(0);
v___x_351_ = lean_mk_array(v_nbuckets_348_, v___x_350_);
v___x_352_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9_spec__14___redArg(v___x_349_, v_data_345_, v___x_351_);
return v___x_352_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8___redArg(lean_object* v_a_353_, lean_object* v_x_354_){
_start:
{
if (lean_obj_tag(v_x_354_) == 0)
{
uint8_t v___x_355_; 
v___x_355_ = 0;
return v___x_355_;
}
else
{
lean_object* v_key_356_; lean_object* v_tail_357_; uint8_t v___x_358_; 
v_key_356_ = lean_ctor_get(v_x_354_, 0);
v_tail_357_ = lean_ctor_get(v_x_354_, 2);
v___x_358_ = lean_name_eq(v_key_356_, v_a_353_);
if (v___x_358_ == 0)
{
v_x_354_ = v_tail_357_;
goto _start;
}
else
{
return v___x_358_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8___redArg___boxed(lean_object* v_a_360_, lean_object* v_x_361_){
_start:
{
uint8_t v_res_362_; lean_object* v_r_363_; 
v_res_362_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8___redArg(v_a_360_, v_x_361_);
lean_dec(v_x_361_);
lean_dec(v_a_360_);
v_r_363_ = lean_box(v_res_362_);
return v_r_363_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__10___redArg(lean_object* v_a_364_, lean_object* v_b_365_, lean_object* v_x_366_){
_start:
{
if (lean_obj_tag(v_x_366_) == 0)
{
lean_dec(v_b_365_);
lean_dec(v_a_364_);
return v_x_366_;
}
else
{
lean_object* v_key_367_; lean_object* v_value_368_; lean_object* v_tail_369_; lean_object* v___x_371_; uint8_t v_isShared_372_; uint8_t v_isSharedCheck_381_; 
v_key_367_ = lean_ctor_get(v_x_366_, 0);
v_value_368_ = lean_ctor_get(v_x_366_, 1);
v_tail_369_ = lean_ctor_get(v_x_366_, 2);
v_isSharedCheck_381_ = !lean_is_exclusive(v_x_366_);
if (v_isSharedCheck_381_ == 0)
{
v___x_371_ = v_x_366_;
v_isShared_372_ = v_isSharedCheck_381_;
goto v_resetjp_370_;
}
else
{
lean_inc(v_tail_369_);
lean_inc(v_value_368_);
lean_inc(v_key_367_);
lean_dec(v_x_366_);
v___x_371_ = lean_box(0);
v_isShared_372_ = v_isSharedCheck_381_;
goto v_resetjp_370_;
}
v_resetjp_370_:
{
uint8_t v___x_373_; 
v___x_373_ = lean_name_eq(v_key_367_, v_a_364_);
if (v___x_373_ == 0)
{
lean_object* v___x_374_; lean_object* v___x_376_; 
v___x_374_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__10___redArg(v_a_364_, v_b_365_, v_tail_369_);
if (v_isShared_372_ == 0)
{
lean_ctor_set(v___x_371_, 2, v___x_374_);
v___x_376_ = v___x_371_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v_key_367_);
lean_ctor_set(v_reuseFailAlloc_377_, 1, v_value_368_);
lean_ctor_set(v_reuseFailAlloc_377_, 2, v___x_374_);
v___x_376_ = v_reuseFailAlloc_377_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
return v___x_376_;
}
}
else
{
lean_object* v___x_379_; 
lean_dec(v_value_368_);
lean_dec(v_key_367_);
if (v_isShared_372_ == 0)
{
lean_ctor_set(v___x_371_, 1, v_b_365_);
lean_ctor_set(v___x_371_, 0, v_a_364_);
v___x_379_ = v___x_371_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v_a_364_);
lean_ctor_set(v_reuseFailAlloc_380_, 1, v_b_365_);
lean_ctor_set(v_reuseFailAlloc_380_, 2, v_tail_369_);
v___x_379_ = v_reuseFailAlloc_380_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
return v___x_379_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4___redArg(lean_object* v_m_382_, lean_object* v_a_383_, lean_object* v_b_384_){
_start:
{
lean_object* v_size_385_; lean_object* v_buckets_386_; lean_object* v___x_388_; uint8_t v_isShared_389_; uint8_t v_isSharedCheck_432_; 
v_size_385_ = lean_ctor_get(v_m_382_, 0);
v_buckets_386_ = lean_ctor_get(v_m_382_, 1);
v_isSharedCheck_432_ = !lean_is_exclusive(v_m_382_);
if (v_isSharedCheck_432_ == 0)
{
v___x_388_ = v_m_382_;
v_isShared_389_ = v_isSharedCheck_432_;
goto v_resetjp_387_;
}
else
{
lean_inc(v_buckets_386_);
lean_inc(v_size_385_);
lean_dec(v_m_382_);
v___x_388_ = lean_box(0);
v_isShared_389_ = v_isSharedCheck_432_;
goto v_resetjp_387_;
}
v_resetjp_387_:
{
lean_object* v___x_390_; uint64_t v___y_392_; 
v___x_390_ = lean_array_get_size(v_buckets_386_);
if (lean_obj_tag(v_a_383_) == 0)
{
uint64_t v___x_430_; 
v___x_430_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg___closed__0);
v___y_392_ = v___x_430_;
goto v___jp_391_;
}
else
{
uint64_t v_hash_431_; 
v_hash_431_ = lean_ctor_get_uint64(v_a_383_, sizeof(void*)*2);
v___y_392_ = v_hash_431_;
goto v___jp_391_;
}
v___jp_391_:
{
uint64_t v___x_393_; uint64_t v___x_394_; uint64_t v_fold_395_; uint64_t v___x_396_; uint64_t v___x_397_; uint64_t v___x_398_; size_t v___x_399_; size_t v___x_400_; size_t v___x_401_; size_t v___x_402_; size_t v___x_403_; lean_object* v_bkt_404_; uint8_t v___x_405_; 
v___x_393_ = 32ULL;
v___x_394_ = lean_uint64_shift_right(v___y_392_, v___x_393_);
v_fold_395_ = lean_uint64_xor(v___y_392_, v___x_394_);
v___x_396_ = 16ULL;
v___x_397_ = lean_uint64_shift_right(v_fold_395_, v___x_396_);
v___x_398_ = lean_uint64_xor(v_fold_395_, v___x_397_);
v___x_399_ = lean_uint64_to_usize(v___x_398_);
v___x_400_ = lean_usize_of_nat(v___x_390_);
v___x_401_ = ((size_t)1ULL);
v___x_402_ = lean_usize_sub(v___x_400_, v___x_401_);
v___x_403_ = lean_usize_land(v___x_399_, v___x_402_);
v_bkt_404_ = lean_array_uget_borrowed(v_buckets_386_, v___x_403_);
v___x_405_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8___redArg(v_a_383_, v_bkt_404_);
if (v___x_405_ == 0)
{
lean_object* v___x_406_; lean_object* v_size_x27_407_; lean_object* v___x_408_; lean_object* v_buckets_x27_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; uint8_t v___x_415_; 
v___x_406_ = lean_unsigned_to_nat(1u);
v_size_x27_407_ = lean_nat_add(v_size_385_, v___x_406_);
lean_dec(v_size_385_);
lean_inc(v_bkt_404_);
v___x_408_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_408_, 0, v_a_383_);
lean_ctor_set(v___x_408_, 1, v_b_384_);
lean_ctor_set(v___x_408_, 2, v_bkt_404_);
v_buckets_x27_409_ = lean_array_uset(v_buckets_386_, v___x_403_, v___x_408_);
v___x_410_ = lean_unsigned_to_nat(4u);
v___x_411_ = lean_nat_mul(v_size_x27_407_, v___x_410_);
v___x_412_ = lean_unsigned_to_nat(3u);
v___x_413_ = lean_nat_div(v___x_411_, v___x_412_);
lean_dec(v___x_411_);
v___x_414_ = lean_array_get_size(v_buckets_x27_409_);
v___x_415_ = lean_nat_dec_le(v___x_413_, v___x_414_);
lean_dec(v___x_413_);
if (v___x_415_ == 0)
{
lean_object* v_val_416_; lean_object* v___x_418_; 
v_val_416_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9___redArg(v_buckets_x27_409_);
if (v_isShared_389_ == 0)
{
lean_ctor_set(v___x_388_, 1, v_val_416_);
lean_ctor_set(v___x_388_, 0, v_size_x27_407_);
v___x_418_ = v___x_388_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v_size_x27_407_);
lean_ctor_set(v_reuseFailAlloc_419_, 1, v_val_416_);
v___x_418_ = v_reuseFailAlloc_419_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
return v___x_418_;
}
}
else
{
lean_object* v___x_421_; 
if (v_isShared_389_ == 0)
{
lean_ctor_set(v___x_388_, 1, v_buckets_x27_409_);
lean_ctor_set(v___x_388_, 0, v_size_x27_407_);
v___x_421_ = v___x_388_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v_size_x27_407_);
lean_ctor_set(v_reuseFailAlloc_422_, 1, v_buckets_x27_409_);
v___x_421_ = v_reuseFailAlloc_422_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
return v___x_421_;
}
}
}
else
{
lean_object* v___x_423_; lean_object* v_buckets_x27_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_428_; 
lean_inc(v_bkt_404_);
v___x_423_ = lean_box(0);
v_buckets_x27_424_ = lean_array_uset(v_buckets_386_, v___x_403_, v___x_423_);
v___x_425_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__10___redArg(v_a_383_, v_b_384_, v_bkt_404_);
v___x_426_ = lean_array_uset(v_buckets_x27_424_, v___x_403_, v___x_425_);
if (v_isShared_389_ == 0)
{
lean_ctor_set(v___x_388_, 1, v___x_426_);
v___x_428_ = v___x_388_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v_size_385_);
lean_ctor_set(v_reuseFailAlloc_429_, 1, v___x_426_);
v___x_428_ = v_reuseFailAlloc_429_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
return v___x_428_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1___redArg(lean_object* v_x_433_, lean_object* v_x_434_, lean_object* v_x_435_){
_start:
{
uint8_t v_stage_u2081_436_; 
v_stage_u2081_436_ = lean_ctor_get_uint8(v_x_433_, sizeof(void*)*2);
if (v_stage_u2081_436_ == 0)
{
lean_object* v_map_u2081_437_; lean_object* v_map_u2082_438_; lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_446_; 
v_map_u2081_437_ = lean_ctor_get(v_x_433_, 0);
v_map_u2082_438_ = lean_ctor_get(v_x_433_, 1);
v_isSharedCheck_446_ = !lean_is_exclusive(v_x_433_);
if (v_isSharedCheck_446_ == 0)
{
v___x_440_ = v_x_433_;
v_isShared_441_ = v_isSharedCheck_446_;
goto v_resetjp_439_;
}
else
{
lean_inc(v_map_u2082_438_);
lean_inc(v_map_u2081_437_);
lean_dec(v_x_433_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_446_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
lean_object* v___x_442_; lean_object* v___x_444_; 
v___x_442_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3___redArg(v_map_u2082_438_, v_x_434_, v_x_435_);
if (v_isShared_441_ == 0)
{
lean_ctor_set(v___x_440_, 1, v___x_442_);
v___x_444_ = v___x_440_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v_map_u2081_437_);
lean_ctor_set(v_reuseFailAlloc_445_, 1, v___x_442_);
lean_ctor_set_uint8(v_reuseFailAlloc_445_, sizeof(void*)*2, v_stage_u2081_436_);
v___x_444_ = v_reuseFailAlloc_445_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
return v___x_444_;
}
}
}
else
{
lean_object* v_map_u2081_447_; lean_object* v_map_u2082_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_456_; 
v_map_u2081_447_ = lean_ctor_get(v_x_433_, 0);
v_map_u2082_448_ = lean_ctor_get(v_x_433_, 1);
v_isSharedCheck_456_ = !lean_is_exclusive(v_x_433_);
if (v_isSharedCheck_456_ == 0)
{
v___x_450_ = v_x_433_;
v_isShared_451_ = v_isSharedCheck_456_;
goto v_resetjp_449_;
}
else
{
lean_inc(v_map_u2082_448_);
lean_inc(v_map_u2081_447_);
lean_dec(v_x_433_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_456_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
lean_object* v___x_452_; lean_object* v___x_454_; 
v___x_452_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4___redArg(v_map_u2081_447_, v_x_434_, v_x_435_);
if (v_isShared_451_ == 0)
{
lean_ctor_set(v___x_450_, 0, v___x_452_);
v___x_454_ = v___x_450_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v___x_452_);
lean_ctor_set(v_reuseFailAlloc_455_, 1, v_map_u2082_448_);
lean_ctor_set_uint8(v_reuseFailAlloc_455_, sizeof(void*)*2, v_stage_u2081_436_);
v___x_454_ = v_reuseFailAlloc_455_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
return v___x_454_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3___redArg(lean_object* v_a_457_, lean_object* v_x_458_){
_start:
{
if (lean_obj_tag(v_x_458_) == 0)
{
lean_object* v___x_459_; 
v___x_459_ = lean_box(0);
return v___x_459_;
}
else
{
lean_object* v_key_460_; lean_object* v_value_461_; lean_object* v_tail_462_; uint8_t v___x_463_; 
v_key_460_ = lean_ctor_get(v_x_458_, 0);
v_value_461_ = lean_ctor_get(v_x_458_, 1);
v_tail_462_ = lean_ctor_get(v_x_458_, 2);
v___x_463_ = lean_name_eq(v_key_460_, v_a_457_);
if (v___x_463_ == 0)
{
v_x_458_ = v_tail_462_;
goto _start;
}
else
{
lean_object* v___x_465_; 
lean_inc(v_value_461_);
v___x_465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_465_, 0, v_value_461_);
return v___x_465_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_a_466_, lean_object* v_x_467_){
_start:
{
lean_object* v_res_468_; 
v_res_468_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3___redArg(v_a_466_, v_x_467_);
lean_dec(v_x_467_);
lean_dec(v_a_466_);
return v_res_468_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1___redArg(lean_object* v_m_469_, lean_object* v_a_470_){
_start:
{
lean_object* v_buckets_471_; lean_object* v___x_472_; uint64_t v___y_474_; 
v_buckets_471_ = lean_ctor_get(v_m_469_, 1);
v___x_472_ = lean_array_get_size(v_buckets_471_);
if (lean_obj_tag(v_a_470_) == 0)
{
uint64_t v___x_488_; 
v___x_488_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg___closed__0);
v___y_474_ = v___x_488_;
goto v___jp_473_;
}
else
{
uint64_t v_hash_489_; 
v_hash_489_ = lean_ctor_get_uint64(v_a_470_, sizeof(void*)*2);
v___y_474_ = v_hash_489_;
goto v___jp_473_;
}
v___jp_473_:
{
uint64_t v___x_475_; uint64_t v___x_476_; uint64_t v_fold_477_; uint64_t v___x_478_; uint64_t v___x_479_; uint64_t v___x_480_; size_t v___x_481_; size_t v___x_482_; size_t v___x_483_; size_t v___x_484_; size_t v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; 
v___x_475_ = 32ULL;
v___x_476_ = lean_uint64_shift_right(v___y_474_, v___x_475_);
v_fold_477_ = lean_uint64_xor(v___y_474_, v___x_476_);
v___x_478_ = 16ULL;
v___x_479_ = lean_uint64_shift_right(v_fold_477_, v___x_478_);
v___x_480_ = lean_uint64_xor(v_fold_477_, v___x_479_);
v___x_481_ = lean_uint64_to_usize(v___x_480_);
v___x_482_ = lean_usize_of_nat(v___x_472_);
v___x_483_ = ((size_t)1ULL);
v___x_484_ = lean_usize_sub(v___x_482_, v___x_483_);
v___x_485_ = lean_usize_land(v___x_481_, v___x_484_);
v___x_486_ = lean_array_uget_borrowed(v_buckets_471_, v___x_485_);
v___x_487_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3___redArg(v_a_470_, v___x_486_);
return v___x_487_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1___redArg___boxed(lean_object* v_m_490_, lean_object* v_a_491_){
_start:
{
lean_object* v_res_492_; 
v_res_492_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1___redArg(v_m_490_, v_a_491_);
lean_dec(v_a_491_);
lean_dec_ref(v_m_490_);
return v_res_492_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v_keys_493_, lean_object* v_vals_494_, lean_object* v_i_495_, lean_object* v_k_496_){
_start:
{
lean_object* v___x_497_; uint8_t v___x_498_; 
v___x_497_ = lean_array_get_size(v_keys_493_);
v___x_498_ = lean_nat_dec_lt(v_i_495_, v___x_497_);
if (v___x_498_ == 0)
{
lean_object* v___x_499_; 
lean_dec(v_i_495_);
v___x_499_ = lean_box(0);
return v___x_499_;
}
else
{
lean_object* v_k_x27_500_; uint8_t v___x_501_; 
v_k_x27_500_ = lean_array_fget_borrowed(v_keys_493_, v_i_495_);
v___x_501_ = lean_name_eq(v_k_496_, v_k_x27_500_);
if (v___x_501_ == 0)
{
lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_502_ = lean_unsigned_to_nat(1u);
v___x_503_ = lean_nat_add(v_i_495_, v___x_502_);
lean_dec(v_i_495_);
v_i_495_ = v___x_503_;
goto _start;
}
else
{
lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_505_ = lean_array_fget_borrowed(v_vals_494_, v_i_495_);
lean_dec(v_i_495_);
lean_inc(v___x_505_);
v___x_506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_506_, 0, v___x_505_);
return v___x_506_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_keys_507_, lean_object* v_vals_508_, lean_object* v_i_509_, lean_object* v_k_510_){
_start:
{
lean_object* v_res_511_; 
v_res_511_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4___redArg(v_keys_507_, v_vals_508_, v_i_509_, v_k_510_);
lean_dec(v_k_510_);
lean_dec_ref(v_vals_508_);
lean_dec_ref(v_keys_507_);
return v_res_511_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1___redArg(lean_object* v_x_512_, size_t v_x_513_, lean_object* v_x_514_){
_start:
{
if (lean_obj_tag(v_x_512_) == 0)
{
lean_object* v_es_515_; lean_object* v___x_516_; size_t v___x_517_; size_t v___x_518_; lean_object* v_j_519_; lean_object* v___x_520_; 
v_es_515_ = lean_ctor_get(v_x_512_, 0);
v___x_516_ = lean_box(2);
v___x_517_ = ((size_t)31ULL);
v___x_518_ = lean_usize_land(v_x_513_, v___x_517_);
v_j_519_ = lean_usize_to_nat(v___x_518_);
v___x_520_ = lean_array_get_borrowed(v___x_516_, v_es_515_, v_j_519_);
lean_dec(v_j_519_);
switch(lean_obj_tag(v___x_520_))
{
case 0:
{
lean_object* v_key_521_; lean_object* v_val_522_; uint8_t v___x_523_; 
v_key_521_ = lean_ctor_get(v___x_520_, 0);
v_val_522_ = lean_ctor_get(v___x_520_, 1);
v___x_523_ = lean_name_eq(v_x_514_, v_key_521_);
if (v___x_523_ == 0)
{
lean_object* v___x_524_; 
v___x_524_ = lean_box(0);
return v___x_524_;
}
else
{
lean_object* v___x_525_; 
lean_inc(v_val_522_);
v___x_525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_525_, 0, v_val_522_);
return v___x_525_;
}
}
case 1:
{
lean_object* v_node_526_; size_t v___x_527_; size_t v___x_528_; 
v_node_526_ = lean_ctor_get(v___x_520_, 0);
v___x_527_ = ((size_t)5ULL);
v___x_528_ = lean_usize_shift_right(v_x_513_, v___x_527_);
v_x_512_ = v_node_526_;
v_x_513_ = v___x_528_;
goto _start;
}
default: 
{
lean_object* v___x_530_; 
v___x_530_ = lean_box(0);
return v___x_530_;
}
}
}
else
{
lean_object* v_ks_531_; lean_object* v_vs_532_; lean_object* v___x_533_; lean_object* v___x_534_; 
v_ks_531_ = lean_ctor_get(v_x_512_, 0);
v_vs_532_ = lean_ctor_get(v_x_512_, 1);
v___x_533_ = lean_unsigned_to_nat(0u);
v___x_534_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4___redArg(v_ks_531_, v_vs_532_, v___x_533_, v_x_514_);
return v___x_534_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_535_, lean_object* v_x_536_, lean_object* v_x_537_){
_start:
{
size_t v_x_1614__boxed_538_; lean_object* v_res_539_; 
v_x_1614__boxed_538_ = lean_unbox_usize(v_x_536_);
lean_dec(v_x_536_);
v_res_539_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1___redArg(v_x_535_, v_x_1614__boxed_538_, v_x_537_);
lean_dec(v_x_537_);
lean_dec_ref(v_x_535_);
return v_res_539_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0___redArg(lean_object* v_x_540_, lean_object* v_x_541_){
_start:
{
uint64_t v___y_543_; 
if (lean_obj_tag(v_x_541_) == 0)
{
uint64_t v___x_546_; 
v___x_546_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg___closed__0);
v___y_543_ = v___x_546_;
goto v___jp_542_;
}
else
{
uint64_t v_hash_547_; 
v_hash_547_ = lean_ctor_get_uint64(v_x_541_, sizeof(void*)*2);
v___y_543_ = v_hash_547_;
goto v___jp_542_;
}
v___jp_542_:
{
size_t v___x_544_; lean_object* v___x_545_; 
v___x_544_ = lean_uint64_to_usize(v___y_543_);
v___x_545_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1___redArg(v_x_540_, v___x_544_, v_x_541_);
return v___x_545_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0___redArg___boxed(lean_object* v_x_548_, lean_object* v_x_549_){
_start:
{
lean_object* v_res_550_; 
v_res_550_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0___redArg(v_x_548_, v_x_549_);
lean_dec(v_x_549_);
lean_dec_ref(v_x_548_);
return v_res_550_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0___redArg(lean_object* v_x_551_, lean_object* v_x_552_){
_start:
{
uint8_t v_stage_u2081_553_; 
v_stage_u2081_553_ = lean_ctor_get_uint8(v_x_551_, sizeof(void*)*2);
if (v_stage_u2081_553_ == 0)
{
lean_object* v_map_u2081_554_; lean_object* v_map_u2082_555_; lean_object* v___x_556_; 
v_map_u2081_554_ = lean_ctor_get(v_x_551_, 0);
v_map_u2082_555_ = lean_ctor_get(v_x_551_, 1);
v___x_556_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0___redArg(v_map_u2082_555_, v_x_552_);
if (lean_obj_tag(v___x_556_) == 0)
{
lean_object* v___x_557_; 
v___x_557_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1___redArg(v_map_u2081_554_, v_x_552_);
return v___x_557_;
}
else
{
return v___x_556_;
}
}
else
{
lean_object* v_map_u2081_558_; lean_object* v___x_559_; 
v_map_u2081_558_ = lean_ctor_get(v_x_551_, 0);
v___x_559_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1___redArg(v_map_u2081_558_, v_x_552_);
return v___x_559_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0___redArg___boxed(lean_object* v_x_560_, lean_object* v_x_561_){
_start:
{
lean_object* v_res_562_; 
v_res_562_ = l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0___redArg(v_x_560_, v_x_561_);
lean_dec(v_x_561_);
lean_dec_ref(v_x_560_);
return v_res_562_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean_addAliasEntry_spec__2(lean_object* v_a_563_, lean_object* v_x_564_){
_start:
{
if (lean_obj_tag(v_x_564_) == 0)
{
uint8_t v___x_565_; 
v___x_565_ = 0;
return v___x_565_;
}
else
{
lean_object* v_head_566_; lean_object* v_tail_567_; uint8_t v___x_568_; 
v_head_566_ = lean_ctor_get(v_x_564_, 0);
v_tail_567_ = lean_ctor_get(v_x_564_, 1);
v___x_568_ = lean_name_eq(v_a_563_, v_head_566_);
if (v___x_568_ == 0)
{
v_x_564_ = v_tail_567_;
goto _start;
}
else
{
return v___x_568_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean_addAliasEntry_spec__2___boxed(lean_object* v_a_570_, lean_object* v_x_571_){
_start:
{
uint8_t v_res_572_; lean_object* v_r_573_; 
v_res_572_ = l_List_elem___at___00Lean_addAliasEntry_spec__2(v_a_570_, v_x_571_);
lean_dec(v_x_571_);
lean_dec(v_a_570_);
v_r_573_ = lean_box(v_res_572_);
return v_r_573_;
}
}
LEAN_EXPORT lean_object* l_Lean_addAliasEntry(lean_object* v_s_574_, lean_object* v_e_575_){
_start:
{
lean_object* v_fst_576_; lean_object* v_snd_577_; lean_object* v___x_579_; uint8_t v_isShared_580_; uint8_t v_isSharedCheck_593_; 
v_fst_576_ = lean_ctor_get(v_e_575_, 0);
v_snd_577_ = lean_ctor_get(v_e_575_, 1);
v_isSharedCheck_593_ = !lean_is_exclusive(v_e_575_);
if (v_isSharedCheck_593_ == 0)
{
v___x_579_ = v_e_575_;
v_isShared_580_ = v_isSharedCheck_593_;
goto v_resetjp_578_;
}
else
{
lean_inc(v_snd_577_);
lean_inc(v_fst_576_);
lean_dec(v_e_575_);
v___x_579_ = lean_box(0);
v_isShared_580_ = v_isSharedCheck_593_;
goto v_resetjp_578_;
}
v_resetjp_578_:
{
lean_object* v___x_581_; 
v___x_581_ = l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0___redArg(v_s_574_, v_fst_576_);
if (lean_obj_tag(v___x_581_) == 0)
{
lean_object* v___x_582_; lean_object* v___x_584_; 
v___x_582_ = lean_box(0);
if (v_isShared_580_ == 0)
{
lean_ctor_set_tag(v___x_579_, 1);
lean_ctor_set(v___x_579_, 1, v___x_582_);
lean_ctor_set(v___x_579_, 0, v_snd_577_);
v___x_584_ = v___x_579_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v_snd_577_);
lean_ctor_set(v_reuseFailAlloc_586_, 1, v___x_582_);
v___x_584_ = v_reuseFailAlloc_586_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
lean_object* v___x_585_; 
v___x_585_ = l_Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1___redArg(v_s_574_, v_fst_576_, v___x_584_);
return v___x_585_;
}
}
else
{
lean_object* v_val_587_; uint8_t v___x_588_; 
v_val_587_ = lean_ctor_get(v___x_581_, 0);
lean_inc(v_val_587_);
lean_dec_ref_known(v___x_581_, 1);
v___x_588_ = l_List_elem___at___00Lean_addAliasEntry_spec__2(v_snd_577_, v_val_587_);
if (v___x_588_ == 0)
{
lean_object* v___x_590_; 
if (v_isShared_580_ == 0)
{
lean_ctor_set_tag(v___x_579_, 1);
lean_ctor_set(v___x_579_, 1, v_val_587_);
lean_ctor_set(v___x_579_, 0, v_snd_577_);
v___x_590_ = v___x_579_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_592_; 
v_reuseFailAlloc_592_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_592_, 0, v_snd_577_);
lean_ctor_set(v_reuseFailAlloc_592_, 1, v_val_587_);
v___x_590_ = v_reuseFailAlloc_592_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
lean_object* v___x_591_; 
v___x_591_ = l_Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1___redArg(v_s_574_, v_fst_576_, v___x_590_);
return v___x_591_;
}
}
else
{
lean_dec(v_val_587_);
lean_del_object(v___x_579_);
lean_dec(v_snd_577_);
lean_dec(v_fst_576_);
return v_s_574_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0(lean_object* v_00_u03b2_594_, lean_object* v_x_595_, lean_object* v_x_596_){
_start:
{
lean_object* v___x_597_; 
v___x_597_ = l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0___redArg(v_x_595_, v_x_596_);
return v___x_597_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0___boxed(lean_object* v_00_u03b2_598_, lean_object* v_x_599_, lean_object* v_x_600_){
_start:
{
lean_object* v_res_601_; 
v_res_601_ = l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0(v_00_u03b2_598_, v_x_599_, v_x_600_);
lean_dec(v_x_600_);
lean_dec_ref(v_x_599_);
return v_res_601_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1(lean_object* v_00_u03b2_602_, lean_object* v_x_603_, lean_object* v_x_604_, lean_object* v_x_605_){
_start:
{
lean_object* v___x_606_; 
v___x_606_ = l_Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1___redArg(v_x_603_, v_x_604_, v_x_605_);
return v___x_606_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0(lean_object* v_00_u03b2_607_, lean_object* v_x_608_, lean_object* v_x_609_){
_start:
{
lean_object* v___x_610_; 
v___x_610_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0___redArg(v_x_608_, v_x_609_);
return v___x_610_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0___boxed(lean_object* v_00_u03b2_611_, lean_object* v_x_612_, lean_object* v_x_613_){
_start:
{
lean_object* v_res_614_; 
v_res_614_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0(v_00_u03b2_611_, v_x_612_, v_x_613_);
lean_dec(v_x_613_);
lean_dec_ref(v_x_612_);
return v_res_614_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1(lean_object* v_00_u03b2_615_, lean_object* v_m_616_, lean_object* v_a_617_){
_start:
{
lean_object* v___x_618_; 
v___x_618_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1___redArg(v_m_616_, v_a_617_);
return v___x_618_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1___boxed(lean_object* v_00_u03b2_619_, lean_object* v_m_620_, lean_object* v_a_621_){
_start:
{
lean_object* v_res_622_; 
v_res_622_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1(v_00_u03b2_619_, v_m_620_, v_a_621_);
lean_dec(v_a_621_);
lean_dec_ref(v_m_620_);
return v_res_622_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3(lean_object* v_00_u03b2_623_, lean_object* v_x_624_, lean_object* v_x_625_, lean_object* v_x_626_){
_start:
{
lean_object* v___x_627_; 
v___x_627_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3___redArg(v_x_624_, v_x_625_, v_x_626_);
return v___x_627_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4(lean_object* v_00_u03b2_628_, lean_object* v_m_629_, lean_object* v_a_630_, lean_object* v_b_631_){
_start:
{
lean_object* v___x_632_; 
v___x_632_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4___redArg(v_m_629_, v_a_630_, v_b_631_);
return v___x_632_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_633_, lean_object* v_x_634_, size_t v_x_635_, lean_object* v_x_636_){
_start:
{
lean_object* v___x_637_; 
v___x_637_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1___redArg(v_x_634_, v_x_635_, v_x_636_);
return v___x_637_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_638_, lean_object* v_x_639_, lean_object* v_x_640_, lean_object* v_x_641_){
_start:
{
size_t v_x_1782__boxed_642_; lean_object* v_res_643_; 
v_x_1782__boxed_642_ = lean_unbox_usize(v_x_640_);
lean_dec(v_x_640_);
v_res_643_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1(v_00_u03b2_638_, v_x_639_, v_x_1782__boxed_642_, v_x_641_);
lean_dec(v_x_641_);
lean_dec_ref(v_x_639_);
return v_res_643_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_644_, lean_object* v_a_645_, lean_object* v_x_646_){
_start:
{
lean_object* v___x_647_; 
v___x_647_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3___redArg(v_a_645_, v_x_646_);
return v___x_647_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_648_, lean_object* v_a_649_, lean_object* v_x_650_){
_start:
{
lean_object* v_res_651_; 
v_res_651_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__1_spec__3(v_00_u03b2_648_, v_a_649_, v_x_650_);
lean_dec(v_x_650_);
lean_dec(v_a_649_);
return v_res_651_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6(lean_object* v_00_u03b2_652_, lean_object* v_x_653_, size_t v_x_654_, size_t v_x_655_, lean_object* v_x_656_, lean_object* v_x_657_){
_start:
{
lean_object* v___x_658_; 
v___x_658_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___redArg(v_x_653_, v_x_654_, v_x_655_, v_x_656_, v_x_657_);
return v___x_658_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6___boxed(lean_object* v_00_u03b2_659_, lean_object* v_x_660_, lean_object* v_x_661_, lean_object* v_x_662_, lean_object* v_x_663_, lean_object* v_x_664_){
_start:
{
size_t v_x_1798__boxed_665_; size_t v_x_1799__boxed_666_; lean_object* v_res_667_; 
v_x_1798__boxed_665_ = lean_unbox_usize(v_x_661_);
lean_dec(v_x_661_);
v_x_1799__boxed_666_ = lean_unbox_usize(v_x_662_);
lean_dec(v_x_662_);
v_res_667_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6(v_00_u03b2_659_, v_x_660_, v_x_1798__boxed_665_, v_x_1799__boxed_666_, v_x_663_, v_x_664_);
return v_res_667_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8(lean_object* v_00_u03b2_668_, lean_object* v_a_669_, lean_object* v_x_670_){
_start:
{
uint8_t v___x_671_; 
v___x_671_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8___redArg(v_a_669_, v_x_670_);
return v___x_671_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8___boxed(lean_object* v_00_u03b2_672_, lean_object* v_a_673_, lean_object* v_x_674_){
_start:
{
uint8_t v_res_675_; lean_object* v_r_676_; 
v_res_675_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__8(v_00_u03b2_672_, v_a_673_, v_x_674_);
lean_dec(v_x_674_);
lean_dec(v_a_673_);
v_r_676_ = lean_box(v_res_675_);
return v_r_676_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9(lean_object* v_00_u03b2_677_, lean_object* v_data_678_){
_start:
{
lean_object* v___x_679_; 
v___x_679_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9___redArg(v_data_678_);
return v___x_679_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__10(lean_object* v_00_u03b2_680_, lean_object* v_a_681_, lean_object* v_b_682_, lean_object* v_x_683_){
_start:
{
lean_object* v___x_684_; 
v___x_684_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__10___redArg(v_a_681_, v_b_682_, v_x_683_);
return v___x_684_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_685_, lean_object* v_keys_686_, lean_object* v_vals_687_, lean_object* v_heq_688_, lean_object* v_i_689_, lean_object* v_k_690_){
_start:
{
lean_object* v___x_691_; 
v___x_691_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4___redArg(v_keys_686_, v_vals_687_, v_i_689_, v_k_690_);
return v___x_691_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v_00_u03b2_692_, lean_object* v_keys_693_, lean_object* v_vals_694_, lean_object* v_heq_695_, lean_object* v_i_696_, lean_object* v_k_697_){
_start:
{
lean_object* v_res_698_; 
v_res_698_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0_spec__0_spec__1_spec__4(v_00_u03b2_692_, v_keys_693_, v_vals_694_, v_heq_695_, v_i_696_, v_k_697_);
lean_dec(v_k_697_);
lean_dec_ref(v_vals_694_);
lean_dec_ref(v_keys_693_);
return v_res_698_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__9(lean_object* v_00_u03b2_699_, lean_object* v_n_700_, lean_object* v_k_701_, lean_object* v_v_702_){
_start:
{
lean_object* v___x_703_; 
v___x_703_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__9___redArg(v_n_700_, v_k_701_, v_v_702_);
return v___x_703_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10(lean_object* v_00_u03b2_704_, size_t v_depth_705_, lean_object* v_keys_706_, lean_object* v_vals_707_, lean_object* v_heq_708_, lean_object* v_i_709_, lean_object* v_entries_710_){
_start:
{
lean_object* v___x_711_; 
v___x_711_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___redArg(v_depth_705_, v_keys_706_, v_vals_707_, v_i_709_, v_entries_710_);
return v___x_711_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10___boxed(lean_object* v_00_u03b2_712_, lean_object* v_depth_713_, lean_object* v_keys_714_, lean_object* v_vals_715_, lean_object* v_heq_716_, lean_object* v_i_717_, lean_object* v_entries_718_){
_start:
{
size_t v_depth_boxed_719_; lean_object* v_res_720_; 
v_depth_boxed_719_ = lean_unbox_usize(v_depth_713_);
lean_dec(v_depth_713_);
v_res_720_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__10(v_00_u03b2_712_, v_depth_boxed_719_, v_keys_714_, v_vals_715_, v_heq_716_, v_i_717_, v_entries_718_);
lean_dec_ref(v_vals_715_);
lean_dec_ref(v_keys_714_);
return v_res_720_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9_spec__14(lean_object* v_00_u03b2_721_, lean_object* v_i_722_, lean_object* v_source_723_, lean_object* v_target_724_){
_start:
{
lean_object* v___x_725_; 
v___x_725_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9_spec__14___redArg(v_i_722_, v_source_723_, v_target_724_);
return v___x_725_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__9_spec__11(lean_object* v_00_u03b2_726_, lean_object* v_x_727_, lean_object* v_x_728_, lean_object* v_x_729_, lean_object* v_x_730_){
_start:
{
lean_object* v___x_731_; 
v___x_731_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__3_spec__6_spec__9_spec__11___redArg(v_x_727_, v_x_728_, v_x_729_, v_x_730_);
return v___x_731_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9_spec__14_spec__16(lean_object* v_00_u03b2_732_, lean_object* v_x_733_, lean_object* v_x_734_){
_start:
{
lean_object* v___x_735_; 
v___x_735_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00Lean_addAliasEntry_spec__1_spec__4_spec__9_spec__14_spec__16___redArg(v_x_733_, v_x_734_);
return v___x_735_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__1___redArg(lean_object* v_m_736_){
_start:
{
uint8_t v_stage_u2081_737_; 
v_stage_u2081_737_ = lean_ctor_get_uint8(v_m_736_, sizeof(void*)*2);
if (v_stage_u2081_737_ == 0)
{
return v_m_736_;
}
else
{
lean_object* v_map_u2081_738_; lean_object* v_map_u2082_739_; lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_747_; 
v_map_u2081_738_ = lean_ctor_get(v_m_736_, 0);
v_map_u2082_739_ = lean_ctor_get(v_m_736_, 1);
v_isSharedCheck_747_ = !lean_is_exclusive(v_m_736_);
if (v_isSharedCheck_747_ == 0)
{
v___x_741_ = v_m_736_;
v_isShared_742_ = v_isSharedCheck_747_;
goto v_resetjp_740_;
}
else
{
lean_inc(v_map_u2082_739_);
lean_inc(v_map_u2081_738_);
lean_dec(v_m_736_);
v___x_741_ = lean_box(0);
v_isShared_742_ = v_isSharedCheck_747_;
goto v_resetjp_740_;
}
v_resetjp_740_:
{
uint8_t v___x_743_; lean_object* v___x_745_; 
v___x_743_ = 0;
if (v_isShared_742_ == 0)
{
v___x_745_ = v___x_741_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v_map_u2081_738_);
lean_ctor_set(v_reuseFailAlloc_746_, 1, v_map_u2082_739_);
v___x_745_ = v_reuseFailAlloc_746_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
lean_ctor_set_uint8(v___x_745_, sizeof(void*)*2, v___x_743_);
return v___x_745_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_switch___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__1(lean_object* v_00_u03b2_748_, lean_object* v_m_749_){
_start:
{
lean_object* v___x_750_; 
v___x_750_ = l_Lean_SMap_switch___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__1___redArg(v_m_749_);
return v___x_750_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn___lam__0_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(lean_object* v_es_751_){
_start:
{
lean_object* v___x_752_; 
v___x_752_ = lean_array_mk(v_es_751_);
return v___x_752_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_as_753_, size_t v_i_754_, size_t v_stop_755_, lean_object* v_b_756_){
_start:
{
uint8_t v___x_757_; 
v___x_757_ = lean_usize_dec_eq(v_i_754_, v_stop_755_);
if (v___x_757_ == 0)
{
lean_object* v___x_758_; lean_object* v___x_759_; size_t v___x_760_; size_t v___x_761_; 
v___x_758_ = lean_array_uget_borrowed(v_as_753_, v_i_754_);
lean_inc(v___x_758_);
v___x_759_ = l_Lean_addAliasEntry(v_b_756_, v___x_758_);
v___x_760_ = ((size_t)1ULL);
v___x_761_ = lean_usize_add(v_i_754_, v___x_760_);
v_i_754_ = v___x_761_;
v_b_756_ = v___x_759_;
goto _start;
}
else
{
return v_b_756_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_as_763_, lean_object* v_i_764_, lean_object* v_stop_765_, lean_object* v_b_766_){
_start:
{
size_t v_i_boxed_767_; size_t v_stop_boxed_768_; lean_object* v_res_769_; 
v_i_boxed_767_ = lean_unbox_usize(v_i_764_);
lean_dec(v_i_764_);
v_stop_boxed_768_ = lean_unbox_usize(v_stop_765_);
lean_dec(v_stop_765_);
v_res_769_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__0(v_as_763_, v_i_boxed_767_, v_stop_boxed_768_, v_b_766_);
lean_dec_ref(v_as_763_);
return v_res_769_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_as_770_, size_t v_i_771_, size_t v_stop_772_, lean_object* v_b_773_){
_start:
{
lean_object* v___y_775_; uint8_t v___x_779_; 
v___x_779_ = lean_usize_dec_eq(v_i_771_, v_stop_772_);
if (v___x_779_ == 0)
{
lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; uint8_t v___x_783_; 
v___x_780_ = lean_array_uget_borrowed(v_as_770_, v_i_771_);
v___x_781_ = lean_unsigned_to_nat(0u);
v___x_782_ = lean_array_get_size(v___x_780_);
v___x_783_ = lean_nat_dec_lt(v___x_781_, v___x_782_);
if (v___x_783_ == 0)
{
v___y_775_ = v_b_773_;
goto v___jp_774_;
}
else
{
uint8_t v___x_784_; 
v___x_784_ = lean_nat_dec_le(v___x_782_, v___x_782_);
if (v___x_784_ == 0)
{
if (v___x_783_ == 0)
{
v___y_775_ = v_b_773_;
goto v___jp_774_;
}
else
{
size_t v___x_785_; size_t v___x_786_; lean_object* v___x_787_; 
v___x_785_ = ((size_t)0ULL);
v___x_786_ = lean_usize_of_nat(v___x_782_);
v___x_787_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__0(v___x_780_, v___x_785_, v___x_786_, v_b_773_);
v___y_775_ = v___x_787_;
goto v___jp_774_;
}
}
else
{
size_t v___x_788_; size_t v___x_789_; lean_object* v___x_790_; 
v___x_788_ = ((size_t)0ULL);
v___x_789_ = lean_usize_of_nat(v___x_782_);
v___x_790_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__0(v___x_780_, v___x_788_, v___x_789_, v_b_773_);
v___y_775_ = v___x_790_;
goto v___jp_774_;
}
}
}
else
{
return v_b_773_;
}
v___jp_774_:
{
size_t v___x_776_; size_t v___x_777_; 
v___x_776_ = ((size_t)1ULL);
v___x_777_ = lean_usize_add(v_i_771_, v___x_776_);
v_i_771_ = v___x_777_;
v_b_773_ = v___y_775_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object* v_as_791_, lean_object* v_i_792_, lean_object* v_stop_793_, lean_object* v_b_794_){
_start:
{
size_t v_i_boxed_795_; size_t v_stop_boxed_796_; lean_object* v_res_797_; 
v_i_boxed_795_ = lean_unbox_usize(v_i_792_);
lean_dec(v_i_792_);
v_stop_boxed_796_ = lean_unbox_usize(v_stop_793_);
lean_dec(v_stop_793_);
v_res_797_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__1(v_as_791_, v_i_boxed_795_, v_stop_boxed_796_, v_b_794_);
lean_dec_ref(v_as_791_);
return v_res_797_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0(lean_object* v_initState_798_, lean_object* v_as_799_){
_start:
{
lean_object* v___x_800_; lean_object* v___x_801_; uint8_t v___x_802_; 
v___x_800_ = lean_unsigned_to_nat(0u);
v___x_801_ = lean_array_get_size(v_as_799_);
v___x_802_ = lean_nat_dec_lt(v___x_800_, v___x_801_);
if (v___x_802_ == 0)
{
return v_initState_798_;
}
else
{
uint8_t v___x_803_; 
v___x_803_ = lean_nat_dec_le(v___x_801_, v___x_801_);
if (v___x_803_ == 0)
{
if (v___x_802_ == 0)
{
return v_initState_798_;
}
else
{
size_t v___x_804_; size_t v___x_805_; lean_object* v___x_806_; 
v___x_804_ = ((size_t)0ULL);
v___x_805_ = lean_usize_of_nat(v___x_801_);
v___x_806_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__1(v_as_799_, v___x_804_, v___x_805_, v_initState_798_);
return v___x_806_;
}
}
else
{
size_t v___x_807_; size_t v___x_808_; lean_object* v___x_809_; 
v___x_807_ = ((size_t)0ULL);
v___x_808_ = lean_usize_of_nat(v___x_801_);
v___x_809_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0_spec__1(v_as_799_, v___x_807_, v___x_808_, v_initState_798_);
return v___x_809_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0___boxed(lean_object* v_initState_810_, lean_object* v_as_811_){
_start:
{
lean_object* v_res_812_; 
v_res_812_ = l_Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0(v_initState_810_, v_as_811_);
lean_dec_ref(v_as_811_);
return v_res_812_;
}
}
static lean_object* _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; 
v___x_813_ = lean_box(0);
v___x_814_ = lean_unsigned_to_nat(16u);
v___x_815_ = lean_mk_array(v___x_814_, v___x_813_);
return v___x_815_;
}
}
static lean_object* _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; 
v___x_816_ = lean_obj_once(&l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_, &l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__once, _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_);
v___x_817_ = lean_unsigned_to_nat(0u);
v___x_818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_818_, 0, v___x_817_);
lean_ctor_set(v___x_818_, 1, v___x_816_);
return v___x_818_;
}
}
static lean_object* _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_819_; 
v___x_819_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_819_;
}
}
static lean_object* _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_820_; lean_object* v___x_821_; 
v___x_820_ = lean_obj_once(&l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_, &l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__once, _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__2_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_);
v___x_821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_821_, 0, v___x_820_);
return v___x_821_;
}
}
static lean_object* _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__4_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_822_; lean_object* v___x_823_; uint8_t v___x_824_; lean_object* v___x_825_; 
v___x_822_ = lean_obj_once(&l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_, &l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__once, _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__3_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_);
v___x_823_ = lean_obj_once(&l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_, &l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__once, _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_);
v___x_824_ = 1;
v___x_825_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_825_, 0, v___x_823_);
lean_ctor_set(v___x_825_, 1, v___x_822_);
lean_ctor_set_uint8(v___x_825_, sizeof(void*)*2, v___x_824_);
return v___x_825_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn___lam__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(lean_object* v_es_826_){
_start:
{
lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; 
v___x_827_ = lean_obj_once(&l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__4_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_, &l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__4_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__once, _init_l___private_Lean_ResolveName_0__Lean_initFn___lam__1___closed__4_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_);
v___x_828_ = l_Lean_mkStateFromImportedEntries___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__0(v___x_827_, v_es_826_);
v___x_829_ = l_Lean_SMap_switch___at___00__private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2__spec__1___redArg(v___x_828_);
return v___x_829_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn___lam__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2____boxed(lean_object* v_es_830_){
_start:
{
lean_object* v_res_831_; 
v_res_831_ = l___private_Lean_ResolveName_0__Lean_initFn___lam__1_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(v_es_830_);
lean_dec_ref(v_es_830_);
return v_res_831_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_848_; lean_object* v___x_849_; 
v___x_848_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_initFn___closed__6_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_));
v___x_849_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_848_);
return v___x_849_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2____boxed(lean_object* v_a_850_){
_start:
{
lean_object* v_res_851_; 
v_res_851_ = l___private_Lean_ResolveName_0__Lean_initFn_00___x40_Lean_ResolveName_1437735408____hygCtx___hyg_2_();
return v_res_851_;
}
}
LEAN_EXPORT lean_object* l_Lean_addAlias(lean_object* v_env_852_, lean_object* v_a_853_, lean_object* v_e_854_){
_start:
{
lean_object* v___x_855_; lean_object* v_toEnvExtension_856_; lean_object* v_asyncMode_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; 
v___x_855_ = l_Lean_aliasExtension;
v_toEnvExtension_856_ = lean_ctor_get(v___x_855_, 0);
v_asyncMode_857_ = lean_ctor_get(v_toEnvExtension_856_, 2);
v___x_858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_858_, 0, v_a_853_);
lean_ctor_set(v___x_858_, 1, v_e_854_);
v___x_859_ = lean_box(0);
v___x_860_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_855_, v_env_852_, v___x_858_, v_asyncMode_857_, v___x_859_);
return v___x_860_;
}
}
static lean_object* _init_l_Lean_getAliasState___closed__2(void){
_start:
{
lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; 
v___x_863_ = ((lean_object*)(l_Lean_getAliasState___closed__1));
v___x_864_ = ((lean_object*)(l_Lean_getAliasState___closed__0));
v___x_865_ = l_Lean_SMap_instInhabited(lean_box(0), lean_box(0), v___x_864_, v___x_863_);
return v___x_865_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAliasState(lean_object* v_env_866_){
_start:
{
lean_object* v___x_867_; lean_object* v_toEnvExtension_868_; lean_object* v_asyncMode_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; 
v___x_867_ = l_Lean_aliasExtension;
v_toEnvExtension_868_ = lean_ctor_get(v___x_867_, 0);
v_asyncMode_869_ = lean_ctor_get(v_toEnvExtension_868_, 2);
v___x_870_ = lean_obj_once(&l_Lean_getAliasState___closed__2, &l_Lean_getAliasState___closed__2_once, _init_l_Lean_getAliasState___closed__2);
v___x_871_ = lean_box(0);
v___x_872_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_870_, v___x_867_, v_env_866_, v_asyncMode_869_, v___x_871_);
return v___x_872_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_getAliases_spec__0(lean_object* v_env_873_, uint8_t v_skipProtected_874_, lean_object* v_a_875_, lean_object* v_a_876_){
_start:
{
if (lean_obj_tag(v_a_875_) == 0)
{
lean_object* v___x_877_; 
lean_dec_ref(v_env_873_);
v___x_877_ = l_List_reverse___redArg(v_a_876_);
return v___x_877_;
}
else
{
lean_object* v_head_878_; lean_object* v_tail_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_890_; 
v_head_878_ = lean_ctor_get(v_a_875_, 0);
v_tail_879_ = lean_ctor_get(v_a_875_, 1);
v_isSharedCheck_890_ = !lean_is_exclusive(v_a_875_);
if (v_isSharedCheck_890_ == 0)
{
v___x_881_ = v_a_875_;
v_isShared_882_ = v_isSharedCheck_890_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_tail_879_);
lean_inc(v_head_878_);
lean_dec(v_a_875_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_890_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
uint8_t v___x_883_; 
lean_inc(v_head_878_);
lean_inc_ref(v_env_873_);
v___x_883_ = l_Lean_isProtected(v_env_873_, v_head_878_);
if (v___x_883_ == 0)
{
if (v_skipProtected_874_ == 0)
{
lean_del_object(v___x_881_);
lean_dec(v_head_878_);
v_a_875_ = v_tail_879_;
goto _start;
}
else
{
lean_object* v___x_886_; 
if (v_isShared_882_ == 0)
{
lean_ctor_set(v___x_881_, 1, v_a_876_);
v___x_886_ = v___x_881_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v_head_878_);
lean_ctor_set(v_reuseFailAlloc_888_, 1, v_a_876_);
v___x_886_ = v_reuseFailAlloc_888_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
v_a_875_ = v_tail_879_;
v_a_876_ = v___x_886_;
goto _start;
}
}
}
else
{
lean_del_object(v___x_881_);
lean_dec(v_head_878_);
v_a_875_ = v_tail_879_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00Lean_getAliases_spec__0___boxed(lean_object* v_env_891_, lean_object* v_skipProtected_892_, lean_object* v_a_893_, lean_object* v_a_894_){
_start:
{
uint8_t v_skipProtected_boxed_895_; lean_object* v_res_896_; 
v_skipProtected_boxed_895_ = lean_unbox(v_skipProtected_892_);
v_res_896_ = l_List_filterTR_loop___at___00Lean_getAliases_spec__0(v_env_891_, v_skipProtected_boxed_895_, v_a_893_, v_a_894_);
return v_res_896_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAliases(lean_object* v_env_897_, lean_object* v_a_898_, uint8_t v_skipProtected_899_){
_start:
{
lean_object* v___x_900_; lean_object* v_toEnvExtension_901_; lean_object* v_asyncMode_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; 
v___x_900_ = l_Lean_aliasExtension;
v_toEnvExtension_901_ = lean_ctor_get(v___x_900_, 0);
v_asyncMode_902_ = lean_ctor_get(v_toEnvExtension_901_, 2);
v___x_903_ = lean_obj_once(&l_Lean_getAliasState___closed__2, &l_Lean_getAliasState___closed__2_once, _init_l_Lean_getAliasState___closed__2);
v___x_904_ = lean_box(0);
lean_inc_ref(v_env_897_);
v___x_905_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_903_, v___x_900_, v_env_897_, v_asyncMode_902_, v___x_904_);
v___x_906_ = l_Lean_SMap_find_x3f___at___00Lean_addAliasEntry_spec__0___redArg(v___x_905_, v_a_898_);
lean_dec(v___x_905_);
if (lean_obj_tag(v___x_906_) == 0)
{
lean_object* v___x_907_; 
lean_dec_ref(v_env_897_);
v___x_907_ = lean_box(0);
return v___x_907_;
}
else
{
if (v_skipProtected_899_ == 0)
{
lean_object* v_val_908_; 
lean_dec_ref(v_env_897_);
v_val_908_ = lean_ctor_get(v___x_906_, 0);
lean_inc(v_val_908_);
lean_dec_ref_known(v___x_906_, 1);
return v_val_908_;
}
else
{
lean_object* v_val_909_; lean_object* v___x_910_; lean_object* v___x_911_; 
v_val_909_ = lean_ctor_get(v___x_906_, 0);
lean_inc(v_val_909_);
lean_dec_ref_known(v___x_906_, 1);
v___x_910_ = lean_box(0);
v___x_911_ = l_List_filterTR_loop___at___00Lean_getAliases_spec__0(v_env_897_, v_skipProtected_899_, v_val_909_, v___x_910_);
return v___x_911_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getAliases___boxed(lean_object* v_env_912_, lean_object* v_a_913_, lean_object* v_skipProtected_914_){
_start:
{
uint8_t v_skipProtected_boxed_915_; lean_object* v_res_916_; 
v_skipProtected_boxed_915_ = lean_unbox(v_skipProtected_914_);
v_res_916_ = l_Lean_getAliases(v_env_912_, v_a_913_, v_skipProtected_boxed_915_);
lean_dec(v_a_913_);
return v_res_916_;
}
}
LEAN_EXPORT lean_object* l_Lean_getRevAliases___lam__0(lean_object* v_e_917_, lean_object* v_as_918_, lean_object* v_a_919_, lean_object* v_es_920_){
_start:
{
uint8_t v___x_921_; 
v___x_921_ = l_List_elem___at___00Lean_addAliasEntry_spec__2(v_e_917_, v_es_920_);
if (v___x_921_ == 0)
{
lean_dec(v_a_919_);
return v_as_918_;
}
else
{
lean_object* v___x_922_; 
v___x_922_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_922_, 0, v_a_919_);
lean_ctor_set(v___x_922_, 1, v_as_918_);
return v___x_922_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getRevAliases___lam__0___boxed(lean_object* v_e_923_, lean_object* v_as_924_, lean_object* v_a_925_, lean_object* v_es_926_){
_start:
{
lean_object* v_res_927_; 
v_res_927_ = l_Lean_getRevAliases___lam__0(v_e_923_, v_as_924_, v_a_925_, v_es_926_);
lean_dec(v_es_926_);
lean_dec(v_e_923_);
return v_res_927_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6___redArg(lean_object* v_f_928_, lean_object* v_keys_929_, lean_object* v_vals_930_, lean_object* v_i_931_, lean_object* v_acc_932_){
_start:
{
lean_object* v___x_933_; uint8_t v___x_934_; 
v___x_933_ = lean_array_get_size(v_keys_929_);
v___x_934_ = lean_nat_dec_lt(v_i_931_, v___x_933_);
if (v___x_934_ == 0)
{
lean_dec(v_i_931_);
lean_dec(v_f_928_);
return v_acc_932_;
}
else
{
lean_object* v_k_935_; lean_object* v_v_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; 
v_k_935_ = lean_array_fget_borrowed(v_keys_929_, v_i_931_);
v_v_936_ = lean_array_fget_borrowed(v_vals_930_, v_i_931_);
lean_inc(v_f_928_);
lean_inc(v_v_936_);
lean_inc(v_k_935_);
v___x_937_ = lean_apply_3(v_f_928_, v_acc_932_, v_k_935_, v_v_936_);
v___x_938_ = lean_unsigned_to_nat(1u);
v___x_939_ = lean_nat_add(v_i_931_, v___x_938_);
lean_dec(v_i_931_);
v_i_931_ = v___x_939_;
v_acc_932_ = v___x_937_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_f_941_, lean_object* v_keys_942_, lean_object* v_vals_943_, lean_object* v_i_944_, lean_object* v_acc_945_){
_start:
{
lean_object* v_res_946_; 
v_res_946_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6___redArg(v_f_941_, v_keys_942_, v_vals_943_, v_i_944_, v_acc_945_);
lean_dec_ref(v_vals_943_);
lean_dec_ref(v_keys_942_);
return v_res_946_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_f_947_, lean_object* v_x_948_, lean_object* v_x_949_){
_start:
{
if (lean_obj_tag(v_x_948_) == 0)
{
lean_object* v_es_950_; lean_object* v___x_951_; lean_object* v___x_952_; uint8_t v___x_953_; 
v_es_950_ = lean_ctor_get(v_x_948_, 0);
v___x_951_ = lean_unsigned_to_nat(0u);
v___x_952_ = lean_array_get_size(v_es_950_);
v___x_953_ = lean_nat_dec_lt(v___x_951_, v___x_952_);
if (v___x_953_ == 0)
{
lean_dec(v_f_947_);
return v_x_949_;
}
else
{
uint8_t v___x_954_; 
v___x_954_ = lean_nat_dec_le(v___x_952_, v___x_952_);
if (v___x_954_ == 0)
{
if (v___x_953_ == 0)
{
lean_dec(v_f_947_);
return v_x_949_;
}
else
{
size_t v___x_955_; size_t v___x_956_; lean_object* v___x_957_; 
v___x_955_ = ((size_t)0ULL);
v___x_956_ = lean_usize_of_nat(v___x_952_);
v___x_957_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(v_f_947_, v_es_950_, v___x_955_, v___x_956_, v_x_949_);
return v___x_957_;
}
}
else
{
size_t v___x_958_; size_t v___x_959_; lean_object* v___x_960_; 
v___x_958_ = ((size_t)0ULL);
v___x_959_ = lean_usize_of_nat(v___x_952_);
v___x_960_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(v_f_947_, v_es_950_, v___x_958_, v___x_959_, v_x_949_);
return v___x_960_;
}
}
}
else
{
lean_object* v_ks_961_; lean_object* v_vs_962_; lean_object* v___x_963_; lean_object* v___x_964_; 
v_ks_961_ = lean_ctor_get(v_x_948_, 0);
v_vs_962_ = lean_ctor_get(v_x_948_, 1);
v___x_963_ = lean_unsigned_to_nat(0u);
v___x_964_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6___redArg(v_f_947_, v_ks_961_, v_vs_962_, v___x_963_, v_x_949_);
return v___x_964_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(lean_object* v_f_965_, lean_object* v_as_966_, size_t v_i_967_, size_t v_stop_968_, lean_object* v_b_969_){
_start:
{
lean_object* v___y_971_; uint8_t v___x_975_; 
v___x_975_ = lean_usize_dec_eq(v_i_967_, v_stop_968_);
if (v___x_975_ == 0)
{
lean_object* v___x_976_; 
v___x_976_ = lean_array_uget_borrowed(v_as_966_, v_i_967_);
switch(lean_obj_tag(v___x_976_))
{
case 0:
{
lean_object* v_key_977_; lean_object* v_val_978_; lean_object* v___x_979_; 
v_key_977_ = lean_ctor_get(v___x_976_, 0);
v_val_978_ = lean_ctor_get(v___x_976_, 1);
lean_inc(v_f_965_);
lean_inc(v_val_978_);
lean_inc(v_key_977_);
v___x_979_ = lean_apply_3(v_f_965_, v_b_969_, v_key_977_, v_val_978_);
v___y_971_ = v___x_979_;
goto v___jp_970_;
}
case 1:
{
lean_object* v_node_980_; lean_object* v___x_981_; 
v_node_980_ = lean_ctor_get(v___x_976_, 0);
lean_inc(v_f_965_);
v___x_981_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg(v_f_965_, v_node_980_, v_b_969_);
v___y_971_ = v___x_981_;
goto v___jp_970_;
}
default: 
{
v___y_971_ = v_b_969_;
goto v___jp_970_;
}
}
}
else
{
lean_dec(v_f_965_);
return v_b_969_;
}
v___jp_970_:
{
size_t v___x_972_; size_t v___x_973_; 
v___x_972_ = ((size_t)1ULL);
v___x_973_ = lean_usize_add(v_i_967_, v___x_972_);
v_i_967_ = v___x_973_;
v_b_969_ = v___y_971_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v_f_982_, lean_object* v_as_983_, lean_object* v_i_984_, lean_object* v_stop_985_, lean_object* v_b_986_){
_start:
{
size_t v_i_boxed_987_; size_t v_stop_boxed_988_; lean_object* v_res_989_; 
v_i_boxed_987_ = lean_unbox_usize(v_i_984_);
lean_dec(v_i_984_);
v_stop_boxed_988_ = lean_unbox_usize(v_stop_985_);
lean_dec(v_stop_985_);
v_res_989_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(v_f_982_, v_as_983_, v_i_boxed_987_, v_stop_boxed_988_, v_b_986_);
lean_dec_ref(v_as_983_);
return v_res_989_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_f_990_, lean_object* v_x_991_, lean_object* v_x_992_){
_start:
{
lean_object* v_res_993_; 
v_res_993_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg(v_f_990_, v_x_991_, v_x_992_);
lean_dec_ref(v_x_991_);
return v_res_993_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg___lam__0(lean_object* v_f_994_, lean_object* v_x1_995_, lean_object* v_x2_996_, lean_object* v_x3_997_){
_start:
{
lean_object* v___x_998_; 
v___x_998_ = lean_apply_3(v_f_994_, v_x1_995_, v_x2_996_, v_x3_997_);
return v___x_998_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg(lean_object* v_map_999_, lean_object* v_f_1000_, lean_object* v_init_1001_){
_start:
{
lean_object* v___f_1002_; lean_object* v___x_1003_; 
v___f_1002_ = lean_alloc_closure((void*)(l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1002_, 0, v_f_1000_);
v___x_1003_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg(v___f_1002_, v_map_999_, v_init_1001_);
return v___x_1003_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg___boxed(lean_object* v_map_1004_, lean_object* v_f_1005_, lean_object* v_init_1006_){
_start:
{
lean_object* v_res_1007_; 
v_res_1007_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg(v_map_1004_, v_f_1005_, v_init_1006_);
lean_dec_ref(v_map_1004_);
return v_res_1007_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__0___redArg(lean_object* v_f_1008_, lean_object* v_x_1009_, lean_object* v_x_1010_){
_start:
{
if (lean_obj_tag(v_x_1010_) == 0)
{
lean_dec(v_f_1008_);
return v_x_1009_;
}
else
{
lean_object* v_key_1011_; lean_object* v_value_1012_; lean_object* v_tail_1013_; lean_object* v___x_1014_; 
v_key_1011_ = lean_ctor_get(v_x_1010_, 0);
lean_inc(v_key_1011_);
v_value_1012_ = lean_ctor_get(v_x_1010_, 1);
lean_inc(v_value_1012_);
v_tail_1013_ = lean_ctor_get(v_x_1010_, 2);
lean_inc(v_tail_1013_);
lean_dec_ref_known(v_x_1010_, 3);
lean_inc(v_f_1008_);
v___x_1014_ = lean_apply_3(v_f_1008_, v_x_1009_, v_key_1011_, v_value_1012_);
v_x_1009_ = v___x_1014_;
v_x_1010_ = v_tail_1013_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2___redArg(lean_object* v_f_1016_, lean_object* v_as_1017_, size_t v_i_1018_, size_t v_stop_1019_, lean_object* v_b_1020_){
_start:
{
uint8_t v___x_1021_; 
v___x_1021_ = lean_usize_dec_eq(v_i_1018_, v_stop_1019_);
if (v___x_1021_ == 0)
{
lean_object* v___x_1022_; lean_object* v___x_1023_; size_t v___x_1024_; size_t v___x_1025_; 
v___x_1022_ = lean_array_uget_borrowed(v_as_1017_, v_i_1018_);
lean_inc(v___x_1022_);
lean_inc(v_f_1016_);
v___x_1023_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__0___redArg(v_f_1016_, v_b_1020_, v___x_1022_);
v___x_1024_ = ((size_t)1ULL);
v___x_1025_ = lean_usize_add(v_i_1018_, v___x_1024_);
v_i_1018_ = v___x_1025_;
v_b_1020_ = v___x_1023_;
goto _start;
}
else
{
lean_dec(v_f_1016_);
return v_b_1020_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2___redArg___boxed(lean_object* v_f_1027_, lean_object* v_as_1028_, lean_object* v_i_1029_, lean_object* v_stop_1030_, lean_object* v_b_1031_){
_start:
{
size_t v_i_boxed_1032_; size_t v_stop_boxed_1033_; lean_object* v_res_1034_; 
v_i_boxed_1032_ = lean_unbox_usize(v_i_1029_);
lean_dec(v_i_1029_);
v_stop_boxed_1033_ = lean_unbox_usize(v_stop_1030_);
lean_dec(v_stop_1030_);
v_res_1034_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2___redArg(v_f_1027_, v_as_1028_, v_i_boxed_1032_, v_stop_boxed_1033_, v_b_1031_);
lean_dec_ref(v_as_1028_);
return v_res_1034_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0___redArg(lean_object* v_f_1035_, lean_object* v_init_1036_, lean_object* v_m_1037_){
_start:
{
lean_object* v_map_u2081_1038_; lean_object* v_map_u2082_1039_; lean_object* v_buckets_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; uint8_t v___x_1043_; 
v_map_u2081_1038_ = lean_ctor_get(v_m_1037_, 0);
v_map_u2082_1039_ = lean_ctor_get(v_m_1037_, 1);
v_buckets_1040_ = lean_ctor_get(v_map_u2081_1038_, 1);
v___x_1041_ = lean_unsigned_to_nat(0u);
v___x_1042_ = lean_array_get_size(v_buckets_1040_);
v___x_1043_ = lean_nat_dec_lt(v___x_1041_, v___x_1042_);
if (v___x_1043_ == 0)
{
lean_object* v___x_1044_; 
v___x_1044_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg(v_map_u2082_1039_, v_f_1035_, v_init_1036_);
return v___x_1044_;
}
else
{
uint8_t v___x_1045_; 
v___x_1045_ = lean_nat_dec_le(v___x_1042_, v___x_1042_);
if (v___x_1045_ == 0)
{
if (v___x_1043_ == 0)
{
lean_object* v___x_1046_; 
v___x_1046_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg(v_map_u2082_1039_, v_f_1035_, v_init_1036_);
return v___x_1046_;
}
else
{
size_t v___x_1047_; size_t v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; 
v___x_1047_ = ((size_t)0ULL);
v___x_1048_ = lean_usize_of_nat(v___x_1042_);
lean_inc(v_f_1035_);
v___x_1049_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2___redArg(v_f_1035_, v_buckets_1040_, v___x_1047_, v___x_1048_, v_init_1036_);
v___x_1050_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg(v_map_u2082_1039_, v_f_1035_, v___x_1049_);
return v___x_1050_;
}
}
else
{
size_t v___x_1051_; size_t v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; 
v___x_1051_ = ((size_t)0ULL);
v___x_1052_ = lean_usize_of_nat(v___x_1042_);
lean_inc(v_f_1035_);
v___x_1053_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2___redArg(v_f_1035_, v_buckets_1040_, v___x_1051_, v___x_1052_, v_init_1036_);
v___x_1054_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg(v_map_u2082_1039_, v_f_1035_, v___x_1053_);
return v___x_1054_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0___redArg___boxed(lean_object* v_f_1055_, lean_object* v_init_1056_, lean_object* v_m_1057_){
_start:
{
lean_object* v_res_1058_; 
v_res_1058_ = l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0___redArg(v_f_1055_, v_init_1056_, v_m_1057_);
lean_dec_ref(v_m_1057_);
return v_res_1058_;
}
}
LEAN_EXPORT lean_object* l_Lean_getRevAliases(lean_object* v_env_1059_, lean_object* v_e_1060_){
_start:
{
lean_object* v___x_1061_; lean_object* v_toEnvExtension_1062_; lean_object* v_asyncMode_1063_; lean_object* v___f_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; 
v___x_1061_ = l_Lean_aliasExtension;
v_toEnvExtension_1062_ = lean_ctor_get(v___x_1061_, 0);
v_asyncMode_1063_ = lean_ctor_get(v_toEnvExtension_1062_, 2);
v___f_1064_ = lean_alloc_closure((void*)(l_Lean_getRevAliases___lam__0___boxed), 4, 1);
lean_closure_set(v___f_1064_, 0, v_e_1060_);
v___x_1065_ = lean_obj_once(&l_Lean_getAliasState___closed__2, &l_Lean_getAliasState___closed__2_once, _init_l_Lean_getAliasState___closed__2);
v___x_1066_ = lean_box(0);
v___x_1067_ = lean_box(0);
v___x_1068_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_1065_, v___x_1061_, v_env_1059_, v_asyncMode_1063_, v___x_1067_);
v___x_1069_ = l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0___redArg(v___f_1064_, v___x_1066_, v___x_1068_);
lean_dec(v___x_1068_);
return v___x_1069_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0(lean_object* v_00_u03b2_1070_, lean_object* v_00_u03c3_1071_, lean_object* v_f_1072_, lean_object* v_init_1073_, lean_object* v_m_1074_){
_start:
{
lean_object* v___x_1075_; 
v___x_1075_ = l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0___redArg(v_f_1072_, v_init_1073_, v_m_1074_);
return v___x_1075_;
}
}
LEAN_EXPORT lean_object* l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0___boxed(lean_object* v_00_u03b2_1076_, lean_object* v_00_u03c3_1077_, lean_object* v_f_1078_, lean_object* v_init_1079_, lean_object* v_m_1080_){
_start:
{
lean_object* v_res_1081_; 
v_res_1081_ = l_Lean_SMap_fold___at___00Lean_getRevAliases_spec__0(v_00_u03b2_1076_, v_00_u03c3_1077_, v_f_1078_, v_init_1079_, v_m_1080_);
lean_dec_ref(v_m_1080_);
return v_res_1081_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__0(lean_object* v_00_u03b2_1082_, lean_object* v_00_u03c3_1083_, lean_object* v_f_1084_, lean_object* v_x_1085_, lean_object* v_x_1086_){
_start:
{
lean_object* v___x_1087_; 
v___x_1087_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__0___redArg(v_f_1084_, v_x_1085_, v_x_1086_);
return v___x_1087_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1(lean_object* v_00_u03c3_1088_, lean_object* v_00_u03b2_1089_, lean_object* v_map_1090_, lean_object* v_f_1091_, lean_object* v_init_1092_){
_start:
{
lean_object* v___x_1093_; 
v___x_1093_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___redArg(v_map_1090_, v_f_1091_, v_init_1092_);
return v___x_1093_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1___boxed(lean_object* v_00_u03c3_1094_, lean_object* v_00_u03b2_1095_, lean_object* v_map_1096_, lean_object* v_f_1097_, lean_object* v_init_1098_){
_start:
{
lean_object* v_res_1099_; 
v_res_1099_ = l_Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1(v_00_u03c3_1094_, v_00_u03b2_1095_, v_map_1096_, v_f_1097_, v_init_1098_);
lean_dec_ref(v_map_1096_);
return v_res_1099_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2(lean_object* v_00_u03b2_1100_, lean_object* v_00_u03c3_1101_, lean_object* v_f_1102_, lean_object* v_as_1103_, size_t v_i_1104_, size_t v_stop_1105_, lean_object* v_b_1106_){
_start:
{
lean_object* v___x_1107_; 
v___x_1107_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2___redArg(v_f_1102_, v_as_1103_, v_i_1104_, v_stop_1105_, v_b_1106_);
return v___x_1107_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1108_, lean_object* v_00_u03c3_1109_, lean_object* v_f_1110_, lean_object* v_as_1111_, lean_object* v_i_1112_, lean_object* v_stop_1113_, lean_object* v_b_1114_){
_start:
{
size_t v_i_boxed_1115_; size_t v_stop_boxed_1116_; lean_object* v_res_1117_; 
v_i_boxed_1115_ = lean_unbox_usize(v_i_1112_);
lean_dec(v_i_1112_);
v_stop_boxed_1116_ = lean_unbox_usize(v_stop_1113_);
lean_dec(v_stop_1113_);
v_res_1117_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__2(v_00_u03b2_1108_, v_00_u03c3_1109_, v_f_1110_, v_as_1111_, v_i_boxed_1115_, v_stop_boxed_1116_, v_b_1114_);
lean_dec_ref(v_as_1111_);
return v_res_1117_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2___redArg(lean_object* v_map_1118_, lean_object* v_f_1119_, lean_object* v_init_1120_){
_start:
{
lean_object* v___x_1121_; 
v___x_1121_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg(v_f_1119_, v_map_1118_, v_init_1120_);
return v___x_1121_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_map_1122_, lean_object* v_f_1123_, lean_object* v_init_1124_){
_start:
{
lean_object* v_res_1125_; 
v_res_1125_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2___redArg(v_map_1122_, v_f_1123_, v_init_1124_);
lean_dec_ref(v_map_1122_);
return v_res_1125_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2(lean_object* v_00_u03c3_1126_, lean_object* v_00_u03b2_1127_, lean_object* v_map_1128_, lean_object* v_f_1129_, lean_object* v_init_1130_){
_start:
{
lean_object* v___x_1131_; 
v___x_1131_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg(v_f_1129_, v_map_1128_, v_init_1130_);
return v___x_1131_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03c3_1132_, lean_object* v_00_u03b2_1133_, lean_object* v_map_1134_, lean_object* v_f_1135_, lean_object* v_init_1136_){
_start:
{
lean_object* v_res_1137_; 
v_res_1137_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2(v_00_u03c3_1132_, v_00_u03b2_1133_, v_map_1134_, v_f_1135_, v_init_1136_);
lean_dec_ref(v_map_1134_);
return v_res_1137_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03c3_1138_, lean_object* v_00_u03b1_1139_, lean_object* v_00_u03b2_1140_, lean_object* v_f_1141_, lean_object* v_x_1142_, lean_object* v_x_1143_){
_start:
{
lean_object* v___x_1144_; 
v___x_1144_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___redArg(v_f_1141_, v_x_1142_, v_x_1143_);
return v___x_1144_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03c3_1145_, lean_object* v_00_u03b1_1146_, lean_object* v_00_u03b2_1147_, lean_object* v_f_1148_, lean_object* v_x_1149_, lean_object* v_x_1150_){
_start:
{
lean_object* v_res_1151_; 
v_res_1151_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3(v_00_u03c3_1145_, v_00_u03b1_1146_, v_00_u03b2_1147_, v_f_1148_, v_x_1149_, v_x_1150_);
lean_dec_ref(v_x_1149_);
return v_res_1151_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5(lean_object* v_00_u03b1_1152_, lean_object* v_00_u03b2_1153_, lean_object* v_00_u03c3_1154_, lean_object* v_f_1155_, lean_object* v_as_1156_, size_t v_i_1157_, size_t v_stop_1158_, lean_object* v_b_1159_){
_start:
{
lean_object* v___x_1160_; 
v___x_1160_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5___redArg(v_f_1155_, v_as_1156_, v_i_1157_, v_stop_1158_, v_b_1159_);
return v___x_1160_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5___boxed(lean_object* v_00_u03b1_1161_, lean_object* v_00_u03b2_1162_, lean_object* v_00_u03c3_1163_, lean_object* v_f_1164_, lean_object* v_as_1165_, lean_object* v_i_1166_, lean_object* v_stop_1167_, lean_object* v_b_1168_){
_start:
{
size_t v_i_boxed_1169_; size_t v_stop_boxed_1170_; lean_object* v_res_1171_; 
v_i_boxed_1169_ = lean_unbox_usize(v_i_1166_);
lean_dec(v_i_1166_);
v_stop_boxed_1170_ = lean_unbox_usize(v_stop_1167_);
lean_dec(v_stop_1167_);
v_res_1171_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__5(v_00_u03b1_1161_, v_00_u03b2_1162_, v_00_u03c3_1163_, v_f_1164_, v_as_1165_, v_i_boxed_1169_, v_stop_boxed_1170_, v_b_1168_);
lean_dec_ref(v_as_1165_);
return v_res_1171_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6(lean_object* v_00_u03c3_1172_, lean_object* v_00_u03b1_1173_, lean_object* v_00_u03b2_1174_, lean_object* v_f_1175_, lean_object* v_keys_1176_, lean_object* v_vals_1177_, lean_object* v_heq_1178_, lean_object* v_i_1179_, lean_object* v_acc_1180_){
_start:
{
lean_object* v___x_1181_; 
v___x_1181_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6___redArg(v_f_1175_, v_keys_1176_, v_vals_1177_, v_i_1179_, v_acc_1180_);
return v___x_1181_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6___boxed(lean_object* v_00_u03c3_1182_, lean_object* v_00_u03b1_1183_, lean_object* v_00_u03b2_1184_, lean_object* v_f_1185_, lean_object* v_keys_1186_, lean_object* v_vals_1187_, lean_object* v_heq_1188_, lean_object* v_i_1189_, lean_object* v_acc_1190_){
_start:
{
lean_object* v_res_1191_; 
v_res_1191_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00Lean_SMap_fold___at___00Lean_getRevAliases_spec__0_spec__1_spec__2_spec__3_spec__6(v_00_u03c3_1182_, v_00_u03b1_1183_, v_00_u03b2_1184_, v_f_1185_, v_keys_1186_, v_vals_1187_, v_heq_1188_, v_i_1189_, v_acc_1190_);
lean_dec_ref(v_vals_1187_);
lean_dec_ref(v_keys_1186_);
return v_res_1191_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(lean_object* v_env_1192_, lean_object* v_declName_1193_){
_start:
{
uint8_t v___y_1195_; uint8_t v___x_1198_; 
v___x_1198_ = l_Lean_Environment_containsOnBranch(v_env_1192_, v_declName_1193_);
if (v___x_1198_ == 0)
{
uint8_t v___x_1199_; 
lean_inc(v_declName_1193_);
lean_inc_ref(v_env_1192_);
v___x_1199_ = lean_is_reserved_name(v_env_1192_, v_declName_1193_);
v___y_1195_ = v___x_1199_;
goto v___jp_1194_;
}
else
{
v___y_1195_ = v___x_1198_;
goto v___jp_1194_;
}
v___jp_1194_:
{
if (v___y_1195_ == 0)
{
uint8_t v___x_1196_; uint8_t v___x_1197_; 
v___x_1196_ = 1;
v___x_1197_ = l_Lean_Environment_contains(v_env_1192_, v_declName_1193_, v___x_1196_);
return v___x_1197_;
}
else
{
lean_dec(v_declName_1193_);
lean_dec_ref(v_env_1192_);
return v___y_1195_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved___boxed(lean_object* v_env_1200_, lean_object* v_declName_1201_){
_start:
{
uint8_t v_res_1202_; lean_object* v_r_1203_; 
v_res_1202_ = l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(v_env_1200_, v_declName_1201_);
v_r_1203_ = lean_box(v_res_1202_);
return v_r_1203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__spec__0(lean_object* v_name_1204_, lean_object* v_decl_1205_, lean_object* v_ref_1206_){
_start:
{
lean_object* v_defValue_1208_; lean_object* v_descr_1209_; lean_object* v_deprecation_x3f_1210_; lean_object* v___x_1211_; uint8_t v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; 
v_defValue_1208_ = lean_ctor_get(v_decl_1205_, 0);
v_descr_1209_ = lean_ctor_get(v_decl_1205_, 1);
v_deprecation_x3f_1210_ = lean_ctor_get(v_decl_1205_, 2);
v___x_1211_ = lean_alloc_ctor(1, 0, 1);
v___x_1212_ = lean_unbox(v_defValue_1208_);
lean_ctor_set_uint8(v___x_1211_, 0, v___x_1212_);
lean_inc(v_deprecation_x3f_1210_);
lean_inc_ref(v_descr_1209_);
lean_inc_n(v_name_1204_, 2);
v___x_1213_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1213_, 0, v_name_1204_);
lean_ctor_set(v___x_1213_, 1, v_ref_1206_);
lean_ctor_set(v___x_1213_, 2, v___x_1211_);
lean_ctor_set(v___x_1213_, 3, v_descr_1209_);
lean_ctor_set(v___x_1213_, 4, v_deprecation_x3f_1210_);
v___x_1214_ = lean_register_option(v_name_1204_, v___x_1213_);
if (lean_obj_tag(v___x_1214_) == 0)
{
lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1222_; 
v_isSharedCheck_1222_ = !lean_is_exclusive(v___x_1214_);
if (v_isSharedCheck_1222_ == 0)
{
lean_object* v_unused_1223_; 
v_unused_1223_ = lean_ctor_get(v___x_1214_, 0);
lean_dec(v_unused_1223_);
v___x_1216_ = v___x_1214_;
v_isShared_1217_ = v_isSharedCheck_1222_;
goto v_resetjp_1215_;
}
else
{
lean_dec(v___x_1214_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1222_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
lean_object* v___x_1218_; lean_object* v___x_1220_; 
lean_inc(v_defValue_1208_);
v___x_1218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1218_, 0, v_name_1204_);
lean_ctor_set(v___x_1218_, 1, v_defValue_1208_);
if (v_isShared_1217_ == 0)
{
lean_ctor_set(v___x_1216_, 0, v___x_1218_);
v___x_1220_ = v___x_1216_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v___x_1218_);
v___x_1220_ = v_reuseFailAlloc_1221_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
return v___x_1220_;
}
}
}
else
{
lean_object* v_a_1224_; lean_object* v___x_1226_; uint8_t v_isShared_1227_; uint8_t v_isSharedCheck_1231_; 
lean_dec(v_name_1204_);
v_a_1224_ = lean_ctor_get(v___x_1214_, 0);
v_isSharedCheck_1231_ = !lean_is_exclusive(v___x_1214_);
if (v_isSharedCheck_1231_ == 0)
{
v___x_1226_ = v___x_1214_;
v_isShared_1227_ = v_isSharedCheck_1231_;
goto v_resetjp_1225_;
}
else
{
lean_inc(v_a_1224_);
lean_dec(v___x_1214_);
v___x_1226_ = lean_box(0);
v_isShared_1227_ = v_isSharedCheck_1231_;
goto v_resetjp_1225_;
}
v_resetjp_1225_:
{
lean_object* v___x_1229_; 
if (v_isShared_1227_ == 0)
{
v___x_1229_ = v___x_1226_;
goto v_reusejp_1228_;
}
else
{
lean_object* v_reuseFailAlloc_1230_; 
v_reuseFailAlloc_1230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1230_, 0, v_a_1224_);
v___x_1229_ = v_reuseFailAlloc_1230_;
goto v_reusejp_1228_;
}
v_reusejp_1228_:
{
return v___x_1229_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_1232_, lean_object* v_decl_1233_, lean_object* v_ref_1234_, lean_object* v_a_1235_){
_start:
{
lean_object* v_res_1236_; 
v_res_1236_ = l_Lean_Option_register___at___00__private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__spec__0(v_name_1232_, v_decl_1233_, v_ref_1234_);
lean_dec_ref(v_decl_1233_);
return v_res_1236_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; 
v___x_1255_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__2_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_));
v___x_1256_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__4_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_));
v___x_1257_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__6_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_));
v___x_1258_ = l_Lean_Option_register___at___00__private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__spec__0(v___x_1255_, v___x_1256_, v___x_1257_);
return v___x_1258_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4____boxed(lean_object* v_a_1259_){
_start:
{
lean_object* v_res_1260_; 
v_res_1260_ = l___private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4_();
return v_res_1260_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; 
v___x_1279_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__1_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4_));
v___x_1280_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__3_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4_));
v___x_1281_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_ResolveName_initFn___closed__4_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4_));
v___x_1282_ = l_Lean_Option_register___at___00__private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_3045884420____hygCtx___hyg_4__spec__0(v___x_1279_, v___x_1280_, v___x_1281_);
return v___x_1282_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4____boxed(lean_object* v_a_1283_){
_start:
{
lean_object* v_res_1284_; 
v_res_1284_ = l___private_Lean_ResolveName_0__Lean_ResolveName_initFn_00___x40_Lean_ResolveName_2661638853____hygCtx___hyg_4_();
return v_res_1284_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__1(lean_object* v_opts_1285_, lean_object* v_opt_1286_){
_start:
{
lean_object* v_name_1287_; lean_object* v_defValue_1288_; lean_object* v_map_1289_; lean_object* v___x_1290_; 
v_name_1287_ = lean_ctor_get(v_opt_1286_, 0);
v_defValue_1288_ = lean_ctor_get(v_opt_1286_, 1);
v_map_1289_ = lean_ctor_get(v_opts_1285_, 0);
v___x_1290_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1289_, v_name_1287_);
if (lean_obj_tag(v___x_1290_) == 0)
{
uint8_t v___x_1291_; 
v___x_1291_ = lean_unbox(v_defValue_1288_);
return v___x_1291_;
}
else
{
lean_object* v_val_1292_; 
v_val_1292_ = lean_ctor_get(v___x_1290_, 0);
lean_inc(v_val_1292_);
lean_dec_ref_known(v___x_1290_, 1);
if (lean_obj_tag(v_val_1292_) == 1)
{
uint8_t v_v_1293_; 
v_v_1293_ = lean_ctor_get_uint8(v_val_1292_, 0);
lean_dec_ref_known(v_val_1292_, 0);
return v_v_1293_;
}
else
{
uint8_t v___x_1294_; 
lean_dec(v_val_1292_);
v___x_1294_ = lean_unbox(v_defValue_1288_);
return v___x_1294_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__1___boxed(lean_object* v_opts_1295_, lean_object* v_opt_1296_){
_start:
{
uint8_t v_res_1297_; lean_object* v_r_1298_; 
v_res_1297_ = l_Lean_Option_get___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__1(v_opts_1295_, v_opt_1296_);
lean_dec_ref(v_opt_1296_);
lean_dec_ref(v_opts_1295_);
v_r_1298_ = lean_box(v_res_1297_);
return v_r_1298_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0(lean_object* v_declName_1302_, lean_object* v_env_1303_, lean_object* v_as_1304_, size_t v_sz_1305_, size_t v_i_1306_, lean_object* v_b_1307_){
_start:
{
uint8_t v___x_1308_; 
v___x_1308_ = lean_usize_dec_lt(v_i_1306_, v_sz_1305_);
if (v___x_1308_ == 0)
{
lean_dec_ref(v_env_1303_);
lean_dec(v_declName_1302_);
lean_inc_ref(v_b_1307_);
return v_b_1307_;
}
else
{
lean_object* v_a_1309_; lean_object* v_toImport_1310_; lean_object* v_module_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; uint8_t v___x_1314_; 
v_a_1309_ = lean_array_uget_borrowed(v_as_1304_, v_i_1306_);
v_toImport_1310_ = lean_ctor_get(v_a_1309_, 0);
v_module_1311_ = lean_ctor_get(v_toImport_1310_, 0);
v___x_1312_ = lean_box(0);
lean_inc(v_declName_1302_);
lean_inc(v_module_1311_);
v___x_1313_ = l_Lean_mkPrivateNameCore(v_module_1311_, v_declName_1302_);
lean_inc(v___x_1313_);
lean_inc_ref(v_env_1303_);
v___x_1314_ = l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(v_env_1303_, v___x_1313_);
if (v___x_1314_ == 0)
{
lean_object* v___x_1315_; size_t v___x_1316_; size_t v___x_1317_; 
lean_dec(v___x_1313_);
v___x_1315_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0___closed__0));
v___x_1316_ = ((size_t)1ULL);
v___x_1317_ = lean_usize_add(v_i_1306_, v___x_1316_);
v_i_1306_ = v___x_1317_;
v_b_1307_ = v___x_1315_;
goto _start;
}
else
{
lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; 
lean_dec_ref(v_env_1303_);
lean_dec(v_declName_1302_);
v___x_1319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1319_, 0, v___x_1313_);
v___x_1320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1320_, 0, v___x_1319_);
v___x_1321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1321_, 0, v___x_1320_);
lean_ctor_set(v___x_1321_, 1, v___x_1312_);
return v___x_1321_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0___boxed(lean_object* v_declName_1322_, lean_object* v_env_1323_, lean_object* v_as_1324_, lean_object* v_sz_1325_, lean_object* v_i_1326_, lean_object* v_b_1327_){
_start:
{
size_t v_sz_boxed_1328_; size_t v_i_boxed_1329_; lean_object* v_res_1330_; 
v_sz_boxed_1328_ = lean_unbox_usize(v_sz_1325_);
lean_dec(v_sz_1325_);
v_i_boxed_1329_ = lean_unbox_usize(v_i_1326_);
lean_dec(v_i_1326_);
v_res_1330_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0(v_declName_1322_, v_env_1323_, v_as_1324_, v_sz_boxed_1328_, v_i_boxed_1329_, v_b_1327_);
lean_dec_ref(v_b_1327_);
lean_dec_ref(v_as_1324_);
return v_res_1330_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName(lean_object* v_env_1331_, lean_object* v_opts_1332_, lean_object* v_declName_1333_){
_start:
{
uint8_t v_isExporting_1349_; 
v_isExporting_1349_ = lean_ctor_get_uint8(v_env_1331_, sizeof(void*)*8);
if (v_isExporting_1349_ == 0)
{
goto v___jp_1334_;
}
else
{
lean_object* v___x_1350_; uint8_t v___x_1351_; 
v___x_1350_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_1351_ = l_Lean_Option_get___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__1(v_opts_1332_, v___x_1350_);
if (v___x_1351_ == 0)
{
lean_object* v___x_1352_; 
lean_dec(v_declName_1333_);
lean_dec_ref(v_env_1331_);
v___x_1352_ = lean_box(0);
return v___x_1352_;
}
else
{
goto v___jp_1334_;
}
}
v___jp_1334_:
{
lean_object* v___x_1335_; uint8_t v___x_1336_; 
lean_inc(v_declName_1333_);
v___x_1335_ = l_Lean_mkPrivateName(v_env_1331_, v_declName_1333_);
lean_inc(v___x_1335_);
lean_inc_ref(v_env_1331_);
v___x_1336_ = l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(v_env_1331_, v___x_1335_);
if (v___x_1336_ == 0)
{
lean_object* v___x_1337_; uint8_t v_isModule_1338_; 
lean_dec(v___x_1335_);
v___x_1337_ = l_Lean_Environment_header(v_env_1331_);
v_isModule_1338_ = lean_ctor_get_uint8(v___x_1337_, sizeof(void*)*7 + 4);
if (v_isModule_1338_ == 0)
{
lean_object* v___x_1339_; 
lean_dec_ref(v___x_1337_);
lean_dec(v_declName_1333_);
lean_dec_ref(v_env_1331_);
v___x_1339_ = lean_box(0);
return v___x_1339_;
}
else
{
lean_object* v_importAllModules_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; size_t v_sz_1343_; size_t v___x_1344_; lean_object* v___x_1345_; lean_object* v_fst_1346_; 
v_importAllModules_1340_ = lean_ctor_get(v___x_1337_, 5);
lean_inc_ref(v_importAllModules_1340_);
lean_dec_ref(v___x_1337_);
v___x_1341_ = lean_box(0);
v___x_1342_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0___closed__0));
v_sz_1343_ = lean_array_size(v_importAllModules_1340_);
v___x_1344_ = ((size_t)0ULL);
v___x_1345_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName_spec__0(v_declName_1333_, v_env_1331_, v_importAllModules_1340_, v_sz_1343_, v___x_1344_, v___x_1342_);
lean_dec_ref(v_importAllModules_1340_);
v_fst_1346_ = lean_ctor_get(v___x_1345_, 0);
lean_inc(v_fst_1346_);
lean_dec_ref(v___x_1345_);
if (lean_obj_tag(v_fst_1346_) == 0)
{
return v___x_1341_;
}
else
{
lean_object* v_val_1347_; 
v_val_1347_ = lean_ctor_get(v_fst_1346_, 0);
lean_inc(v_val_1347_);
lean_dec_ref_known(v_fst_1346_, 1);
return v_val_1347_;
}
}
}
else
{
lean_object* v___x_1348_; 
lean_dec(v_declName_1333_);
lean_dec_ref(v_env_1331_);
v___x_1348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1348_, 0, v___x_1335_);
return v___x_1348_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName___boxed(lean_object* v_env_1353_, lean_object* v_opts_1354_, lean_object* v_declName_1355_){
_start:
{
lean_object* v_res_1356_; 
v_res_1356_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName(v_env_1353_, v_opts_1354_, v_declName_1355_);
lean_dec_ref(v_opts_1354_);
return v_res_1356_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveQualifiedName(lean_object* v_env_1357_, lean_object* v_opts_1358_, lean_object* v_ns_1359_, lean_object* v_id_1360_){
_start:
{
lean_object* v_resolvedId_1361_; uint8_t v___x_1362_; lean_object* v_resolvedIds_1363_; 
lean_inc(v_id_1360_);
v_resolvedId_1361_ = l_Lean_Name_append(v_ns_1359_, v_id_1360_);
v___x_1362_ = l_Lean_Name_isAtomic(v_id_1360_);
lean_dec(v_id_1360_);
lean_inc_ref(v_env_1357_);
v_resolvedIds_1363_ = l_Lean_getAliases(v_env_1357_, v_resolvedId_1361_, v___x_1362_);
if (v___x_1362_ == 0)
{
goto v___jp_1364_;
}
else
{
uint8_t v___x_1370_; 
lean_inc(v_resolvedId_1361_);
lean_inc_ref(v_env_1357_);
v___x_1370_ = l_Lean_isProtected(v_env_1357_, v_resolvedId_1361_);
if (v___x_1370_ == 0)
{
goto v___jp_1364_;
}
else
{
lean_dec(v_resolvedId_1361_);
lean_dec_ref(v_env_1357_);
return v_resolvedIds_1363_;
}
}
v___jp_1364_:
{
uint8_t v___x_1365_; 
lean_inc(v_resolvedId_1361_);
lean_inc_ref(v_env_1357_);
v___x_1365_ = l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(v_env_1357_, v_resolvedId_1361_);
if (v___x_1365_ == 0)
{
lean_object* v___x_1366_; 
v___x_1366_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName(v_env_1357_, v_opts_1358_, v_resolvedId_1361_);
if (lean_obj_tag(v___x_1366_) == 1)
{
lean_object* v_val_1367_; lean_object* v___x_1368_; 
v_val_1367_ = lean_ctor_get(v___x_1366_, 0);
lean_inc(v_val_1367_);
lean_dec_ref_known(v___x_1366_, 1);
v___x_1368_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1368_, 0, v_val_1367_);
lean_ctor_set(v___x_1368_, 1, v_resolvedIds_1363_);
return v___x_1368_;
}
else
{
lean_dec(v___x_1366_);
return v_resolvedIds_1363_;
}
}
else
{
lean_object* v___x_1369_; 
lean_dec_ref(v_env_1357_);
v___x_1369_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1369_, 0, v_resolvedId_1361_);
lean_ctor_set(v___x_1369_, 1, v_resolvedIds_1363_);
return v___x_1369_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveQualifiedName___boxed(lean_object* v_env_1371_, lean_object* v_opts_1372_, lean_object* v_ns_1373_, lean_object* v_id_1374_){
_start:
{
lean_object* v_res_1375_; 
v_res_1375_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveQualifiedName(v_env_1371_, v_opts_1372_, v_ns_1373_, v_id_1374_);
lean_dec_ref(v_opts_1372_);
return v_res_1375_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveUsingNamespace(lean_object* v_env_1376_, lean_object* v_opts_1377_, lean_object* v_id_1378_, lean_object* v_x_1379_){
_start:
{
if (lean_obj_tag(v_x_1379_) == 1)
{
lean_object* v_pre_1380_; lean_object* v___x_1381_; 
v_pre_1380_ = lean_ctor_get(v_x_1379_, 0);
lean_inc(v_pre_1380_);
lean_inc(v_id_1378_);
lean_inc_ref(v_env_1376_);
v___x_1381_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveQualifiedName(v_env_1376_, v_opts_1377_, v_x_1379_, v_id_1378_);
if (lean_obj_tag(v___x_1381_) == 0)
{
v_x_1379_ = v_pre_1380_;
goto _start;
}
else
{
lean_dec(v_pre_1380_);
lean_dec(v_id_1378_);
lean_dec_ref(v_env_1376_);
return v___x_1381_;
}
}
else
{
lean_object* v___x_1383_; 
lean_dec(v_x_1379_);
lean_dec(v_id_1378_);
lean_dec_ref(v_env_1376_);
v___x_1383_ = lean_box(0);
return v___x_1383_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveUsingNamespace___boxed(lean_object* v_env_1384_, lean_object* v_opts_1385_, lean_object* v_id_1386_, lean_object* v_x_1387_){
_start:
{
lean_object* v_res_1388_; 
v_res_1388_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveUsingNamespace(v_env_1384_, v_opts_1385_, v_id_1386_, v_x_1387_);
lean_dec_ref(v_opts_1385_);
return v_res_1388_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveExact(lean_object* v_env_1389_, lean_object* v_opts_1390_, lean_object* v_id_1391_){
_start:
{
uint8_t v___x_1392_; 
v___x_1392_ = l_Lean_Name_isAtomic(v_id_1391_);
if (v___x_1392_ == 0)
{
lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v_resolvedId_1395_; uint8_t v___x_1396_; 
v___x_1393_ = l_Lean_rootNamespace;
v___x_1394_ = lean_box(0);
v_resolvedId_1395_ = l_Lean_Name_replacePrefix(v_id_1391_, v___x_1393_, v___x_1394_);
lean_inc(v_resolvedId_1395_);
lean_inc_ref(v_env_1389_);
v___x_1396_ = l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(v_env_1389_, v_resolvedId_1395_);
if (v___x_1396_ == 0)
{
lean_object* v___x_1397_; 
v___x_1397_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName(v_env_1389_, v_opts_1390_, v_resolvedId_1395_);
return v___x_1397_;
}
else
{
lean_object* v___x_1398_; 
lean_dec_ref(v_env_1389_);
v___x_1398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1398_, 0, v_resolvedId_1395_);
return v___x_1398_;
}
}
else
{
lean_object* v___x_1399_; 
lean_dec(v_id_1391_);
lean_dec_ref(v_env_1389_);
v___x_1399_ = lean_box(0);
return v___x_1399_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveExact___boxed(lean_object* v_env_1400_, lean_object* v_opts_1401_, lean_object* v_id_1402_){
_start:
{
lean_object* v_res_1403_; 
v_res_1403_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveExact(v_env_1400_, v_opts_1401_, v_id_1402_);
lean_dec_ref(v_opts_1401_);
return v_res_1403_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveOpenDecls(lean_object* v_env_1404_, lean_object* v_opts_1405_, lean_object* v_id_1406_, lean_object* v_x_1407_, lean_object* v_x_1408_){
_start:
{
if (lean_obj_tag(v_x_1407_) == 0)
{
lean_dec(v_id_1406_);
lean_dec_ref(v_env_1404_);
return v_x_1408_;
}
else
{
lean_object* v_head_1409_; 
v_head_1409_ = lean_ctor_get(v_x_1407_, 0);
lean_inc(v_head_1409_);
if (lean_obj_tag(v_head_1409_) == 0)
{
lean_object* v_tail_1410_; lean_object* v_ns_1411_; lean_object* v_except_1412_; uint8_t v___x_1413_; 
v_tail_1410_ = lean_ctor_get(v_x_1407_, 1);
lean_inc(v_tail_1410_);
lean_dec_ref_known(v_x_1407_, 2);
v_ns_1411_ = lean_ctor_get(v_head_1409_, 0);
lean_inc(v_ns_1411_);
v_except_1412_ = lean_ctor_get(v_head_1409_, 1);
lean_inc(v_except_1412_);
lean_dec_ref_known(v_head_1409_, 2);
v___x_1413_ = l_List_elem___at___00Lean_addAliasEntry_spec__2(v_id_1406_, v_except_1412_);
lean_dec(v_except_1412_);
if (v___x_1413_ == 0)
{
lean_object* v_newResolvedIds_1414_; lean_object* v___x_1415_; 
lean_inc(v_id_1406_);
lean_inc_ref(v_env_1404_);
v_newResolvedIds_1414_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveQualifiedName(v_env_1404_, v_opts_1405_, v_ns_1411_, v_id_1406_);
v___x_1415_ = l_List_appendTR___redArg(v_newResolvedIds_1414_, v_x_1408_);
v_x_1407_ = v_tail_1410_;
v_x_1408_ = v___x_1415_;
goto _start;
}
else
{
lean_dec(v_ns_1411_);
v_x_1407_ = v_tail_1410_;
goto _start;
}
}
else
{
lean_object* v_tail_1418_; lean_object* v___x_1420_; uint8_t v_isShared_1421_; uint8_t v_isSharedCheck_1438_; 
v_tail_1418_ = lean_ctor_get(v_x_1407_, 1);
v_isSharedCheck_1438_ = !lean_is_exclusive(v_x_1407_);
if (v_isSharedCheck_1438_ == 0)
{
lean_object* v_unused_1439_; 
v_unused_1439_ = lean_ctor_get(v_x_1407_, 0);
lean_dec(v_unused_1439_);
v___x_1420_ = v_x_1407_;
v_isShared_1421_ = v_isSharedCheck_1438_;
goto v_resetjp_1419_;
}
else
{
lean_inc(v_tail_1418_);
lean_dec(v_x_1407_);
v___x_1420_ = lean_box(0);
v_isShared_1421_ = v_isSharedCheck_1438_;
goto v_resetjp_1419_;
}
v_resetjp_1419_:
{
lean_object* v_id_1422_; lean_object* v_declName_1423_; uint8_t v___x_1424_; 
v_id_1422_ = lean_ctor_get(v_head_1409_, 0);
lean_inc(v_id_1422_);
v_declName_1423_ = lean_ctor_get(v_head_1409_, 1);
lean_inc(v_declName_1423_);
lean_dec_ref_known(v_head_1409_, 2);
v___x_1424_ = lean_name_eq(v_id_1422_, v_id_1406_);
if (v___x_1424_ == 0)
{
uint8_t v___x_1425_; 
v___x_1425_ = l_Lean_Name_isPrefixOf(v_id_1422_, v_id_1406_);
if (v___x_1425_ == 0)
{
lean_dec(v_declName_1423_);
lean_dec(v_id_1422_);
lean_del_object(v___x_1420_);
v_x_1407_ = v_tail_1418_;
goto _start;
}
else
{
lean_object* v_candidate_1427_; uint8_t v___x_1428_; 
lean_inc(v_id_1406_);
v_candidate_1427_ = l_Lean_Name_replacePrefix(v_id_1406_, v_id_1422_, v_declName_1423_);
lean_dec(v_declName_1423_);
lean_dec(v_id_1422_);
lean_inc(v_candidate_1427_);
lean_inc_ref(v_env_1404_);
v___x_1428_ = l_Lean_Environment_contains(v_env_1404_, v_candidate_1427_, v___x_1425_);
if (v___x_1428_ == 0)
{
lean_dec(v_candidate_1427_);
lean_del_object(v___x_1420_);
v_x_1407_ = v_tail_1418_;
goto _start;
}
else
{
lean_object* v___x_1431_; 
if (v_isShared_1421_ == 0)
{
lean_ctor_set(v___x_1420_, 1, v_x_1408_);
lean_ctor_set(v___x_1420_, 0, v_candidate_1427_);
v___x_1431_ = v___x_1420_;
goto v_reusejp_1430_;
}
else
{
lean_object* v_reuseFailAlloc_1433_; 
v_reuseFailAlloc_1433_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1433_, 0, v_candidate_1427_);
lean_ctor_set(v_reuseFailAlloc_1433_, 1, v_x_1408_);
v___x_1431_ = v_reuseFailAlloc_1433_;
goto v_reusejp_1430_;
}
v_reusejp_1430_:
{
v_x_1407_ = v_tail_1418_;
v_x_1408_ = v___x_1431_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_1435_; 
lean_dec(v_id_1422_);
if (v_isShared_1421_ == 0)
{
lean_ctor_set(v___x_1420_, 1, v_x_1408_);
lean_ctor_set(v___x_1420_, 0, v_declName_1423_);
v___x_1435_ = v___x_1420_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v_declName_1423_);
lean_ctor_set(v_reuseFailAlloc_1437_, 1, v_x_1408_);
v___x_1435_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
v_x_1407_ = v_tail_1418_;
v_x_1408_ = v___x_1435_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveOpenDecls___boxed(lean_object* v_env_1440_, lean_object* v_opts_1441_, lean_object* v_id_1442_, lean_object* v_x_1443_, lean_object* v_x_1444_){
_start:
{
lean_object* v_res_1445_; 
v_res_1445_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveOpenDecls(v_env_1440_, v_opts_1441_, v_id_1442_, v_x_1443_, v_x_1444_);
lean_dec_ref(v_opts_1441_);
return v_res_1445_;
}
}
LEAN_EXPORT lean_object* l_List_eraseDups___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__0(lean_object* v_as_1447_){
_start:
{
lean_object* v___f_1448_; lean_object* v___x_1449_; 
v___f_1448_ = ((lean_object*)(l_List_eraseDups___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__0___closed__0));
v___x_1449_ = l_List_eraseDupsBy___redArg(v___f_1448_, v_as_1447_);
return v___x_1449_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__1(lean_object* v_projs_1450_, lean_object* v_a_1451_, lean_object* v_a_1452_){
_start:
{
if (lean_obj_tag(v_a_1451_) == 0)
{
lean_object* v___x_1453_; 
lean_dec(v_projs_1450_);
v___x_1453_ = l_List_reverse___redArg(v_a_1452_);
return v___x_1453_;
}
else
{
lean_object* v_head_1454_; lean_object* v_tail_1455_; lean_object* v___x_1457_; uint8_t v_isShared_1458_; uint8_t v_isSharedCheck_1464_; 
v_head_1454_ = lean_ctor_get(v_a_1451_, 0);
v_tail_1455_ = lean_ctor_get(v_a_1451_, 1);
v_isSharedCheck_1464_ = !lean_is_exclusive(v_a_1451_);
if (v_isSharedCheck_1464_ == 0)
{
v___x_1457_ = v_a_1451_;
v_isShared_1458_ = v_isSharedCheck_1464_;
goto v_resetjp_1456_;
}
else
{
lean_inc(v_tail_1455_);
lean_inc(v_head_1454_);
lean_dec(v_a_1451_);
v___x_1457_ = lean_box(0);
v_isShared_1458_ = v_isSharedCheck_1464_;
goto v_resetjp_1456_;
}
v_resetjp_1456_:
{
lean_object* v___x_1459_; lean_object* v___x_1461_; 
lean_inc(v_projs_1450_);
v___x_1459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1459_, 0, v_head_1454_);
lean_ctor_set(v___x_1459_, 1, v_projs_1450_);
if (v_isShared_1458_ == 0)
{
lean_ctor_set(v___x_1457_, 1, v_a_1452_);
lean_ctor_set(v___x_1457_, 0, v___x_1459_);
v___x_1461_ = v___x_1457_;
goto v_reusejp_1460_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v___x_1459_);
lean_ctor_set(v_reuseFailAlloc_1463_, 1, v_a_1452_);
v___x_1461_ = v_reuseFailAlloc_1463_;
goto v_reusejp_1460_;
}
v_reusejp_1460_:
{
v_a_1451_ = v_tail_1455_;
v_a_1452_ = v___x_1461_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop(lean_object* v_env_1465_, lean_object* v_opts_1466_, lean_object* v_ns_1467_, lean_object* v_openDecls_1468_, lean_object* v_extractionResult_1469_, lean_object* v_id_1470_, lean_object* v_projs_1471_){
_start:
{
if (lean_obj_tag(v_id_1470_) == 1)
{
lean_object* v_pre_1472_; lean_object* v_str_1473_; lean_object* v_imported_1474_; lean_object* v_ctx_1475_; lean_object* v_scopes_1476_; lean_object* v___x_1477_; lean_object* v_id_1478_; lean_object* v___y_1480_; lean_object* v___x_1490_; lean_object* v___y_1492_; 
v_pre_1472_ = lean_ctor_get(v_id_1470_, 0);
lean_inc(v_pre_1472_);
v_str_1473_ = lean_ctor_get(v_id_1470_, 1);
lean_inc_ref(v_str_1473_);
v_imported_1474_ = lean_ctor_get(v_extractionResult_1469_, 1);
v_ctx_1475_ = lean_ctor_get(v_extractionResult_1469_, 2);
v_scopes_1476_ = lean_ctor_get(v_extractionResult_1469_, 3);
lean_inc(v_scopes_1476_);
lean_inc(v_ctx_1475_);
lean_inc(v_imported_1474_);
v___x_1477_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1477_, 0, v_id_1470_);
lean_ctor_set(v___x_1477_, 1, v_imported_1474_);
lean_ctor_set(v___x_1477_, 2, v_ctx_1475_);
lean_ctor_set(v___x_1477_, 3, v_scopes_1476_);
v_id_1478_ = l_Lean_MacroScopesView_review(v___x_1477_);
lean_inc(v_ns_1467_);
lean_inc(v_id_1478_);
lean_inc_ref(v_env_1465_);
v___x_1490_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveUsingNamespace(v_env_1465_, v_opts_1466_, v_id_1478_, v_ns_1467_);
if (lean_obj_tag(v___x_1490_) == 0)
{
lean_object* v___x_1497_; 
lean_inc(v_id_1478_);
lean_inc_ref(v_env_1465_);
v___x_1497_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveExact(v_env_1465_, v_opts_1466_, v_id_1478_);
if (lean_obj_tag(v___x_1497_) == 0)
{
uint8_t v___x_1498_; 
lean_inc(v_id_1478_);
lean_inc_ref(v_env_1465_);
v___x_1498_ = l___private_Lean_ResolveName_0__Lean_ResolveName_containsDeclOrReserved(v_env_1465_, v_id_1478_);
if (v___x_1498_ == 0)
{
v___y_1492_ = v___x_1490_;
goto v___jp_1491_;
}
else
{
lean_object* v___x_1499_; 
lean_inc(v_id_1478_);
v___x_1499_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1499_, 0, v_id_1478_);
lean_ctor_set(v___x_1499_, 1, v___x_1490_);
v___y_1492_ = v___x_1499_;
goto v___jp_1491_;
}
}
else
{
lean_object* v_val_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; 
lean_dec(v_id_1478_);
lean_dec_ref(v_str_1473_);
lean_dec(v_pre_1472_);
lean_dec(v_openDecls_1468_);
lean_dec(v_ns_1467_);
lean_dec_ref(v_env_1465_);
v_val_1500_ = lean_ctor_get(v___x_1497_, 0);
lean_inc(v_val_1500_);
lean_dec_ref_known(v___x_1497_, 1);
v___x_1501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1501_, 0, v_val_1500_);
lean_ctor_set(v___x_1501_, 1, v_projs_1471_);
v___x_1502_ = lean_box(0);
v___x_1503_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1503_, 0, v___x_1501_);
lean_ctor_set(v___x_1503_, 1, v___x_1502_);
return v___x_1503_;
}
}
else
{
lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; 
lean_dec(v_id_1478_);
lean_dec_ref(v_str_1473_);
lean_dec(v_pre_1472_);
lean_dec(v_openDecls_1468_);
lean_dec(v_ns_1467_);
lean_dec_ref(v_env_1465_);
v___x_1504_ = l_List_eraseDups___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__0(v___x_1490_);
v___x_1505_ = lean_box(0);
v___x_1506_ = l_List_mapTR_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__1(v_projs_1471_, v___x_1504_, v___x_1505_);
return v___x_1506_;
}
v___jp_1479_:
{
lean_object* v_resolvedIds_1481_; uint8_t v___x_1482_; lean_object* v___x_1483_; lean_object* v_resolvedIds_1484_; 
lean_inc(v_openDecls_1468_);
lean_inc(v_id_1478_);
lean_inc_ref_n(v_env_1465_, 2);
v_resolvedIds_1481_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveOpenDecls(v_env_1465_, v_opts_1466_, v_id_1478_, v_openDecls_1468_, v___y_1480_);
v___x_1482_ = l_Lean_Name_isAtomic(v_id_1478_);
v___x_1483_ = l_Lean_getAliases(v_env_1465_, v_id_1478_, v___x_1482_);
lean_dec(v_id_1478_);
v_resolvedIds_1484_ = l_List_appendTR___redArg(v___x_1483_, v_resolvedIds_1481_);
if (lean_obj_tag(v_resolvedIds_1484_) == 0)
{
lean_object* v___x_1485_; 
v___x_1485_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1485_, 0, v_str_1473_);
lean_ctor_set(v___x_1485_, 1, v_projs_1471_);
v_id_1470_ = v_pre_1472_;
v_projs_1471_ = v___x_1485_;
goto _start;
}
else
{
lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; 
lean_dec_ref(v_str_1473_);
lean_dec(v_pre_1472_);
lean_dec(v_openDecls_1468_);
lean_dec(v_ns_1467_);
lean_dec_ref(v_env_1465_);
v___x_1487_ = l_List_eraseDups___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__0(v_resolvedIds_1484_);
v___x_1488_ = lean_box(0);
v___x_1489_ = l_List_mapTR_loop___at___00__private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop_spec__1(v_projs_1471_, v___x_1487_, v___x_1488_);
return v___x_1489_;
}
}
v___jp_1491_:
{
lean_object* v___x_1493_; 
lean_inc(v_id_1478_);
lean_inc_ref(v_env_1465_);
v___x_1493_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolvePrivateName(v_env_1465_, v_opts_1466_, v_id_1478_);
if (lean_obj_tag(v___x_1493_) == 1)
{
lean_object* v_val_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; 
v_val_1494_ = lean_ctor_get(v___x_1493_, 0);
lean_inc(v_val_1494_);
lean_dec_ref_known(v___x_1493_, 1);
v___x_1495_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1495_, 0, v_val_1494_);
lean_ctor_set(v___x_1495_, 1, v___x_1490_);
v___x_1496_ = l_List_appendTR___redArg(v___x_1495_, v___y_1492_);
v___y_1480_ = v___x_1496_;
goto v___jp_1479_;
}
else
{
lean_dec(v___x_1493_);
lean_dec(v___x_1490_);
v___y_1480_ = v___y_1492_;
goto v___jp_1479_;
}
}
}
else
{
lean_object* v___x_1507_; 
lean_dec(v_projs_1471_);
lean_dec(v_id_1470_);
lean_dec(v_openDecls_1468_);
lean_dec(v_ns_1467_);
lean_dec_ref(v_env_1465_);
v___x_1507_ = lean_box(0);
return v___x_1507_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop___boxed(lean_object* v_env_1508_, lean_object* v_opts_1509_, lean_object* v_ns_1510_, lean_object* v_openDecls_1511_, lean_object* v_extractionResult_1512_, lean_object* v_id_1513_, lean_object* v_projs_1514_){
_start:
{
lean_object* v_res_1515_; 
v_res_1515_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop(v_env_1508_, v_opts_1509_, v_ns_1510_, v_openDecls_1511_, v_extractionResult_1512_, v_id_1513_, v_projs_1514_);
lean_dec_ref(v_extractionResult_1512_);
lean_dec_ref(v_opts_1509_);
return v_res_1515_;
}
}
LEAN_EXPORT lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object* v_env_1516_, lean_object* v_opts_1517_, lean_object* v_ns_1518_, lean_object* v_openDecls_1519_, lean_object* v_id_1520_){
_start:
{
lean_object* v_extractionResult_1521_; lean_object* v_name_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; 
v_extractionResult_1521_ = l_Lean_extractMacroScopes(v_id_1520_);
v_name_1522_ = lean_ctor_get(v_extractionResult_1521_, 0);
lean_inc(v_name_1522_);
v___x_1523_ = lean_box(0);
v___x_1524_ = l___private_Lean_ResolveName_0__Lean_ResolveName_resolveGlobalName_loop(v_env_1516_, v_opts_1517_, v_ns_1518_, v_openDecls_1519_, v_extractionResult_1521_, v_name_1522_, v___x_1523_);
lean_dec_ref(v_extractionResult_1521_);
return v___x_1524_;
}
}
LEAN_EXPORT lean_object* l_Lean_ResolveName_resolveGlobalName___boxed(lean_object* v_env_1525_, lean_object* v_opts_1526_, lean_object* v_ns_1527_, lean_object* v_openDecls_1528_, lean_object* v_id_1529_){
_start:
{
lean_object* v_res_1530_; 
v_res_1530_ = l_Lean_ResolveName_resolveGlobalName(v_env_1525_, v_opts_1526_, v_ns_1527_, v_openDecls_1528_, v_id_1529_);
lean_dec_ref(v_opts_1526_);
return v_res_1530_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_ResolveName_resolveNamespaceUsingScope_x3f_spec__0(lean_object* v_msg_1531_){
_start:
{
lean_object* v___x_1532_; lean_object* v___x_1533_; 
v___x_1532_ = lean_box(0);
v___x_1533_ = lean_panic_fn_borrowed(v___x_1532_, v_msg_1531_);
return v___x_1533_;
}
}
static lean_object* _init_l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__3(void){
_start:
{
lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; 
v___x_1537_ = ((lean_object*)(l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__2));
v___x_1538_ = lean_unsigned_to_nat(9u);
v___x_1539_ = lean_unsigned_to_nat(230u);
v___x_1540_ = ((lean_object*)(l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__1));
v___x_1541_ = ((lean_object*)(l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__0));
v___x_1542_ = l_mkPanicMessageWithDecl(v___x_1541_, v___x_1540_, v___x_1539_, v___x_1538_, v___x_1537_);
return v___x_1542_;
}
}
LEAN_EXPORT lean_object* l_Lean_ResolveName_resolveNamespaceUsingScope_x3f(lean_object* v_env_1543_, lean_object* v_n_1544_, lean_object* v_ns_1545_){
_start:
{
switch(lean_obj_tag(v_ns_1545_))
{
case 1:
{
lean_object* v_pre_1546_; lean_object* v___x_1547_; uint8_t v___x_1548_; 
v_pre_1546_ = lean_ctor_get(v_ns_1545_, 0);
lean_inc(v_pre_1546_);
lean_inc(v_n_1544_);
v___x_1547_ = l_Lean_Name_append(v_ns_1545_, v_n_1544_);
lean_inc_ref(v_env_1543_);
v___x_1548_ = l_Lean_Environment_isNamespace(v_env_1543_, v___x_1547_);
if (v___x_1548_ == 0)
{
lean_dec(v___x_1547_);
v_ns_1545_ = v_pre_1546_;
goto _start;
}
else
{
lean_object* v___x_1550_; 
lean_dec(v_pre_1546_);
lean_dec(v_n_1544_);
lean_dec_ref(v_env_1543_);
v___x_1550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1550_, 0, v___x_1547_);
return v___x_1550_;
}
}
case 0:
{
lean_object* v___x_1551_; lean_object* v_n_1552_; uint8_t v___x_1553_; 
v___x_1551_ = l_Lean_rootNamespace;
v_n_1552_ = l_Lean_Name_replacePrefix(v_n_1544_, v___x_1551_, v_ns_1545_);
v___x_1553_ = l_Lean_Environment_isNamespace(v_env_1543_, v_n_1552_);
if (v___x_1553_ == 0)
{
lean_object* v___x_1554_; 
lean_dec(v_n_1552_);
v___x_1554_ = lean_box(0);
return v___x_1554_;
}
else
{
lean_object* v___x_1555_; 
v___x_1555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1555_, 0, v_n_1552_);
return v___x_1555_;
}
}
default: 
{
lean_object* v___x_1556_; lean_object* v___x_1557_; 
lean_dec(v_ns_1545_);
lean_dec(v_n_1544_);
lean_dec_ref(v_env_1543_);
v___x_1556_ = lean_obj_once(&l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__3, &l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__3_once, _init_l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__3);
v___x_1557_ = l_panic___at___00Lean_ResolveName_resolveNamespaceUsingScope_x3f_spec__0(v___x_1556_);
return v___x_1557_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ResolveName_resolveNamespaceUsingOpenDecls(lean_object* v_env_1558_, lean_object* v_n_1559_, lean_object* v_x_1560_){
_start:
{
if (lean_obj_tag(v_x_1560_) == 0)
{
lean_object* v___x_1561_; 
lean_dec(v_n_1559_);
lean_dec_ref(v_env_1558_);
v___x_1561_ = lean_box(0);
return v___x_1561_;
}
else
{
lean_object* v_head_1562_; 
v_head_1562_ = lean_ctor_get(v_x_1560_, 0);
if (lean_obj_tag(v_head_1562_) == 0)
{
lean_object* v_tail_1563_; lean_object* v___x_1565_; uint8_t v_isShared_1566_; uint8_t v_isSharedCheck_1580_; 
lean_inc_ref(v_head_1562_);
v_tail_1563_ = lean_ctor_get(v_x_1560_, 1);
v_isSharedCheck_1580_ = !lean_is_exclusive(v_x_1560_);
if (v_isSharedCheck_1580_ == 0)
{
lean_object* v_unused_1581_; 
v_unused_1581_ = lean_ctor_get(v_x_1560_, 0);
lean_dec(v_unused_1581_);
v___x_1565_ = v_x_1560_;
v_isShared_1566_ = v_isSharedCheck_1580_;
goto v_resetjp_1564_;
}
else
{
lean_inc(v_tail_1563_);
lean_dec(v_x_1560_);
v___x_1565_ = lean_box(0);
v_isShared_1566_ = v_isSharedCheck_1580_;
goto v_resetjp_1564_;
}
v_resetjp_1564_:
{
lean_object* v_ns_1567_; lean_object* v_except_1568_; lean_object* v___x_1569_; uint8_t v___y_1571_; uint8_t v___x_1577_; 
v_ns_1567_ = lean_ctor_get(v_head_1562_, 0);
lean_inc(v_ns_1567_);
v_except_1568_ = lean_ctor_get(v_head_1562_, 1);
lean_inc(v_except_1568_);
lean_dec_ref_known(v_head_1562_, 2);
lean_inc(v_n_1559_);
v___x_1569_ = l_Lean_Name_append(v_ns_1567_, v_n_1559_);
lean_inc_ref(v_env_1558_);
v___x_1577_ = l_Lean_Environment_isNamespace(v_env_1558_, v___x_1569_);
if (v___x_1577_ == 0)
{
lean_dec(v_except_1568_);
v___y_1571_ = v___x_1577_;
goto v___jp_1570_;
}
else
{
uint8_t v___x_1578_; 
v___x_1578_ = l_List_elem___at___00Lean_addAliasEntry_spec__2(v_n_1559_, v_except_1568_);
lean_dec(v_except_1568_);
if (v___x_1578_ == 0)
{
v___y_1571_ = v___x_1577_;
goto v___jp_1570_;
}
else
{
lean_dec(v___x_1569_);
lean_del_object(v___x_1565_);
v_x_1560_ = v_tail_1563_;
goto _start;
}
}
v___jp_1570_:
{
if (v___y_1571_ == 0)
{
lean_dec(v___x_1569_);
lean_del_object(v___x_1565_);
v_x_1560_ = v_tail_1563_;
goto _start;
}
else
{
lean_object* v___x_1573_; lean_object* v___x_1575_; 
v___x_1573_ = l_Lean_ResolveName_resolveNamespaceUsingOpenDecls(v_env_1558_, v_n_1559_, v_tail_1563_);
if (v_isShared_1566_ == 0)
{
lean_ctor_set(v___x_1565_, 1, v___x_1573_);
lean_ctor_set(v___x_1565_, 0, v___x_1569_);
v___x_1575_ = v___x_1565_;
goto v_reusejp_1574_;
}
else
{
lean_object* v_reuseFailAlloc_1576_; 
v_reuseFailAlloc_1576_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1576_, 0, v___x_1569_);
lean_ctor_set(v_reuseFailAlloc_1576_, 1, v___x_1573_);
v___x_1575_ = v_reuseFailAlloc_1576_;
goto v_reusejp_1574_;
}
v_reusejp_1574_:
{
return v___x_1575_;
}
}
}
}
}
else
{
lean_object* v_tail_1582_; 
v_tail_1582_ = lean_ctor_get(v_x_1560_, 1);
lean_inc(v_tail_1582_);
lean_dec_ref_known(v_x_1560_, 2);
v_x_1560_ = v_tail_1582_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ResolveName_resolveNamespace(lean_object* v_env_1584_, lean_object* v_ns_1585_, lean_object* v_openDecls_1586_, lean_object* v_id_1587_){
_start:
{
lean_object* v___x_1588_; 
lean_inc(v_id_1587_);
lean_inc_ref(v_env_1584_);
v___x_1588_ = l_Lean_ResolveName_resolveNamespaceUsingScope_x3f(v_env_1584_, v_id_1587_, v_ns_1585_);
if (lean_obj_tag(v___x_1588_) == 0)
{
lean_object* v___x_1589_; 
v___x_1589_ = l_Lean_ResolveName_resolveNamespaceUsingOpenDecls(v_env_1584_, v_id_1587_, v_openDecls_1586_);
return v___x_1589_;
}
else
{
lean_object* v_val_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; 
v_val_1590_ = lean_ctor_get(v___x_1588_, 0);
lean_inc(v_val_1590_);
lean_dec_ref_known(v___x_1588_, 1);
v___x_1591_ = l_Lean_ResolveName_resolveNamespaceUsingOpenDecls(v_env_1584_, v_id_1587_, v_openDecls_1586_);
v___x_1592_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1592_, 0, v_val_1590_);
lean_ctor_set(v___x_1592_, 1, v___x_1591_);
return v___x_1592_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadResolveNameOfMonadLift___redArg(lean_object* v_inst_1593_, lean_object* v_inst_1594_){
_start:
{
lean_object* v_getCurrNamespace_1595_; lean_object* v_getOpenDecls_1596_; lean_object* v___x_1598_; uint8_t v_isShared_1599_; uint8_t v_isSharedCheck_1605_; 
v_getCurrNamespace_1595_ = lean_ctor_get(v_inst_1594_, 0);
v_getOpenDecls_1596_ = lean_ctor_get(v_inst_1594_, 1);
v_isSharedCheck_1605_ = !lean_is_exclusive(v_inst_1594_);
if (v_isSharedCheck_1605_ == 0)
{
v___x_1598_ = v_inst_1594_;
v_isShared_1599_ = v_isSharedCheck_1605_;
goto v_resetjp_1597_;
}
else
{
lean_inc(v_getOpenDecls_1596_);
lean_inc(v_getCurrNamespace_1595_);
lean_dec(v_inst_1594_);
v___x_1598_ = lean_box(0);
v_isShared_1599_ = v_isSharedCheck_1605_;
goto v_resetjp_1597_;
}
v_resetjp_1597_:
{
lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1603_; 
lean_inc(v_inst_1593_);
v___x_1600_ = lean_apply_2(v_inst_1593_, lean_box(0), v_getCurrNamespace_1595_);
v___x_1601_ = lean_apply_2(v_inst_1593_, lean_box(0), v_getOpenDecls_1596_);
if (v_isShared_1599_ == 0)
{
lean_ctor_set(v___x_1598_, 1, v___x_1601_);
lean_ctor_set(v___x_1598_, 0, v___x_1600_);
v___x_1603_ = v___x_1598_;
goto v_reusejp_1602_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v___x_1600_);
lean_ctor_set(v_reuseFailAlloc_1604_, 1, v___x_1601_);
v___x_1603_ = v_reuseFailAlloc_1604_;
goto v_reusejp_1602_;
}
v_reusejp_1602_:
{
return v___x_1603_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadResolveNameOfMonadLift(lean_object* v_m_1606_, lean_object* v_n_1607_, lean_object* v_inst_1608_, lean_object* v_inst_1609_){
_start:
{
lean_object* v___x_1610_; 
v___x_1610_ = l_Lean_instMonadResolveNameOfMonadLift___redArg(v_inst_1608_, v_inst_1609_);
return v___x_1610_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_1612_; lean_object* v___x_1613_; 
v___x_1612_ = ((lean_object*)(l_Lean_checkPrivateInPublic___redArg___lam__0___closed__0));
v___x_1613_ = l_Lean_stringToMessageData(v___x_1612_);
return v___x_1613_;
}
}
static lean_object* _init_l_Lean_checkPrivateInPublic___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1615_; lean_object* v___x_1616_; 
v___x_1615_ = ((lean_object*)(l_Lean_checkPrivateInPublic___redArg___lam__0___closed__2));
v___x_1616_ = l_Lean_stringToMessageData(v___x_1615_);
return v___x_1616_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___redArg___lam__0(lean_object* v_____do__lift_1617_, lean_object* v_toApplicative_1618_, lean_object* v_id_1619_, lean_object* v_inst_1620_, lean_object* v_inst_1621_, lean_object* v_inst_1622_, lean_object* v_inst_1623_, uint8_t v_____do__lift_1624_){
_start:
{
uint8_t v_isExporting_1629_; 
v_isExporting_1629_ = lean_ctor_get_uint8(v_____do__lift_1617_, sizeof(void*)*8);
if (v_isExporting_1629_ == 0)
{
lean_dec(v_inst_1623_);
lean_dec(v_inst_1622_);
lean_dec_ref(v_inst_1621_);
lean_dec_ref(v_inst_1620_);
lean_dec(v_id_1619_);
goto v___jp_1625_;
}
else
{
uint8_t v___x_1630_; 
v___x_1630_ = l_Lean_isPrivateName(v_id_1619_);
if (v___x_1630_ == 0)
{
lean_dec(v_inst_1623_);
lean_dec(v_inst_1622_);
lean_dec_ref(v_inst_1621_);
lean_dec_ref(v_inst_1620_);
lean_dec(v_id_1619_);
goto v___jp_1625_;
}
else
{
if (v_____do__lift_1624_ == 0)
{
lean_dec(v_inst_1623_);
lean_dec(v_inst_1622_);
lean_dec_ref(v_inst_1621_);
lean_dec_ref(v_inst_1620_);
lean_dec(v_id_1619_);
goto v___jp_1625_;
}
else
{
lean_object* v___x_1631_; uint8_t v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; 
lean_dec_ref(v_toApplicative_1618_);
v___x_1631_ = lean_obj_once(&l_Lean_checkPrivateInPublic___redArg___lam__0___closed__1, &l_Lean_checkPrivateInPublic___redArg___lam__0___closed__1_once, _init_l_Lean_checkPrivateInPublic___redArg___lam__0___closed__1);
v___x_1632_ = 0;
v___x_1633_ = l_Lean_MessageData_ofConstName(v_id_1619_, v___x_1632_);
v___x_1634_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1634_, 0, v___x_1631_);
lean_ctor_set(v___x_1634_, 1, v___x_1633_);
v___x_1635_ = lean_obj_once(&l_Lean_checkPrivateInPublic___redArg___lam__0___closed__3, &l_Lean_checkPrivateInPublic___redArg___lam__0___closed__3_once, _init_l_Lean_checkPrivateInPublic___redArg___lam__0___closed__3);
v___x_1636_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1636_, 0, v___x_1634_);
lean_ctor_set(v___x_1636_, 1, v___x_1635_);
v___x_1637_ = l_Lean_logWarning___redArg(v_inst_1620_, v_inst_1621_, v_inst_1622_, v_inst_1623_, v___x_1636_);
return v___x_1637_;
}
}
}
v___jp_1625_:
{
lean_object* v_toPure_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; 
v_toPure_1626_ = lean_ctor_get(v_toApplicative_1618_, 1);
lean_inc(v_toPure_1626_);
lean_dec_ref(v_toApplicative_1618_);
v___x_1627_ = lean_box(0);
v___x_1628_ = lean_apply_2(v_toPure_1626_, lean_box(0), v___x_1627_);
return v___x_1628_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___redArg___lam__0___boxed(lean_object* v_____do__lift_1638_, lean_object* v_toApplicative_1639_, lean_object* v_id_1640_, lean_object* v_inst_1641_, lean_object* v_inst_1642_, lean_object* v_inst_1643_, lean_object* v_inst_1644_, lean_object* v_____do__lift_1645_){
_start:
{
uint8_t v_____do__lift_231__boxed_1646_; lean_object* v_res_1647_; 
v_____do__lift_231__boxed_1646_ = lean_unbox(v_____do__lift_1645_);
v_res_1647_ = l_Lean_checkPrivateInPublic___redArg___lam__0(v_____do__lift_1638_, v_toApplicative_1639_, v_id_1640_, v_inst_1641_, v_inst_1642_, v_inst_1643_, v_inst_1644_, v_____do__lift_231__boxed_1646_);
lean_dec_ref(v_____do__lift_1638_);
return v_res_1647_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___redArg___lam__1(lean_object* v_toApplicative_1648_, lean_object* v_id_1649_, lean_object* v_inst_1650_, lean_object* v_inst_1651_, lean_object* v_inst_1652_, lean_object* v_inst_1653_, lean_object* v___x_1654_, lean_object* v_toBind_1655_, lean_object* v_____do__lift_1656_){
_start:
{
lean_object* v___f_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; 
lean_inc(v_inst_1653_);
lean_inc_ref(v_inst_1650_);
v___f_1657_ = lean_alloc_closure((void*)(l_Lean_checkPrivateInPublic___redArg___lam__0___boxed), 8, 7);
lean_closure_set(v___f_1657_, 0, v_____do__lift_1656_);
lean_closure_set(v___f_1657_, 1, v_toApplicative_1648_);
lean_closure_set(v___f_1657_, 2, v_id_1649_);
lean_closure_set(v___f_1657_, 3, v_inst_1650_);
lean_closure_set(v___f_1657_, 4, v_inst_1651_);
lean_closure_set(v___f_1657_, 5, v_inst_1652_);
lean_closure_set(v___f_1657_, 6, v_inst_1653_);
v___x_1658_ = l_Lean_ResolveName_backward_privateInPublic_warn;
v___x_1659_ = l_Lean_Option_getM___redArg(v_inst_1650_, v_inst_1653_, v___x_1654_, v___x_1658_);
v___x_1660_ = lean_apply_4(v_toBind_1655_, lean_box(0), lean_box(0), v___x_1659_, v___f_1657_);
return v___x_1660_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic___redArg(lean_object* v_inst_1661_, lean_object* v_inst_1662_, lean_object* v_inst_1663_, lean_object* v_inst_1664_, lean_object* v_inst_1665_, lean_object* v_id_1666_){
_start:
{
lean_object* v___x_1667_; lean_object* v_toApplicative_1668_; lean_object* v_toBind_1669_; lean_object* v_getEnv_1670_; lean_object* v___f_1671_; lean_object* v___x_1672_; 
v___x_1667_ = l_Lean_KVMap_instValueBool;
v_toApplicative_1668_ = lean_ctor_get(v_inst_1661_, 0);
lean_inc_ref(v_toApplicative_1668_);
v_toBind_1669_ = lean_ctor_get(v_inst_1661_, 1);
lean_inc_n(v_toBind_1669_, 2);
v_getEnv_1670_ = lean_ctor_get(v_inst_1662_, 0);
lean_inc(v_getEnv_1670_);
lean_dec_ref(v_inst_1662_);
v___f_1671_ = lean_alloc_closure((void*)(l_Lean_checkPrivateInPublic___redArg___lam__1), 9, 8);
lean_closure_set(v___f_1671_, 0, v_toApplicative_1668_);
lean_closure_set(v___f_1671_, 1, v_id_1666_);
lean_closure_set(v___f_1671_, 2, v_inst_1661_);
lean_closure_set(v___f_1671_, 3, v_inst_1664_);
lean_closure_set(v___f_1671_, 4, v_inst_1665_);
lean_closure_set(v___f_1671_, 5, v_inst_1663_);
lean_closure_set(v___f_1671_, 6, v___x_1667_);
lean_closure_set(v___f_1671_, 7, v_toBind_1669_);
v___x_1672_ = lean_apply_4(v_toBind_1669_, lean_box(0), lean_box(0), v_getEnv_1670_, v___f_1671_);
return v___x_1672_;
}
}
LEAN_EXPORT lean_object* l_Lean_checkPrivateInPublic(lean_object* v_m_1673_, lean_object* v_inst_1674_, lean_object* v_inst_1675_, lean_object* v_inst_1676_, lean_object* v_inst_1677_, lean_object* v_inst_1678_, lean_object* v_id_1679_){
_start:
{
lean_object* v___x_1680_; 
v___x_1680_ = l_Lean_checkPrivateInPublic___redArg(v_inst_1674_, v_inst_1675_, v_inst_1676_, v_inst_1677_, v_inst_1678_, v_id_1679_);
return v___x_1680_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg___lam__0(lean_object* v_env_1681_, lean_object* v_n_1682_, lean_object* v_toApplicative_1683_, uint8_t v___y_1684_, uint8_t v___x_1685_, lean_object* v_____r_1686_){
_start:
{
lean_object* v___x_1687_; 
v___x_1687_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1681_, v_n_1682_);
if (lean_obj_tag(v___x_1687_) == 0)
{
lean_object* v_toPure_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; 
v_toPure_1688_ = lean_ctor_get(v_toApplicative_1683_, 1);
lean_inc(v_toPure_1688_);
lean_dec_ref(v_toApplicative_1683_);
v___x_1689_ = lean_box(v___y_1684_);
v___x_1690_ = lean_apply_2(v_toPure_1688_, lean_box(0), v___x_1689_);
return v___x_1690_;
}
else
{
lean_object* v_val_1691_; lean_object* v_toPure_1692_; lean_object* v___x_1693_; uint8_t v_isModule_1694_; 
v_val_1691_ = lean_ctor_get(v___x_1687_, 0);
lean_inc(v_val_1691_);
lean_dec_ref_known(v___x_1687_, 1);
v_toPure_1692_ = lean_ctor_get(v_toApplicative_1683_, 1);
lean_inc(v_toPure_1692_);
lean_dec_ref(v_toApplicative_1683_);
v___x_1693_ = l_Lean_Environment_header(v_env_1681_);
v_isModule_1694_ = lean_ctor_get_uint8(v___x_1693_, sizeof(void*)*7 + 4);
if (v_isModule_1694_ == 0)
{
lean_object* v___x_1695_; lean_object* v___x_1696_; 
lean_dec_ref(v___x_1693_);
lean_dec(v_val_1691_);
v___x_1695_ = lean_box(v___x_1685_);
v___x_1696_ = lean_apply_2(v_toPure_1692_, lean_box(0), v___x_1695_);
return v___x_1696_;
}
else
{
lean_object* v_modules_1697_; lean_object* v___x_1698_; uint8_t v___x_1699_; 
v_modules_1697_ = lean_ctor_get(v___x_1693_, 3);
lean_inc_ref(v_modules_1697_);
lean_dec_ref(v___x_1693_);
v___x_1698_ = lean_array_get_size(v_modules_1697_);
v___x_1699_ = lean_nat_dec_lt(v_val_1691_, v___x_1698_);
if (v___x_1699_ == 0)
{
lean_object* v___x_1700_; lean_object* v___x_1701_; 
lean_dec_ref(v_modules_1697_);
lean_dec(v_val_1691_);
v___x_1700_ = lean_box(v_isModule_1694_);
v___x_1701_ = lean_apply_2(v_toPure_1692_, lean_box(0), v___x_1700_);
return v___x_1701_;
}
else
{
lean_object* v___x_1702_; lean_object* v_toImport_1703_; uint8_t v_importAll_1704_; 
v___x_1702_ = lean_array_fget(v_modules_1697_, v_val_1691_);
lean_dec(v_val_1691_);
lean_dec_ref(v_modules_1697_);
v_toImport_1703_ = lean_ctor_get(v___x_1702_, 0);
lean_inc_ref(v_toImport_1703_);
lean_dec(v___x_1702_);
v_importAll_1704_ = lean_ctor_get_uint8(v_toImport_1703_, sizeof(void*)*1);
lean_dec_ref(v_toImport_1703_);
if (v_importAll_1704_ == 0)
{
lean_object* v___x_1705_; lean_object* v___x_1706_; 
v___x_1705_ = lean_box(v_isModule_1694_);
v___x_1706_ = lean_apply_2(v_toPure_1692_, lean_box(0), v___x_1705_);
return v___x_1706_;
}
else
{
lean_object* v___x_1707_; lean_object* v___x_1708_; 
v___x_1707_ = lean_box(v___y_1684_);
v___x_1708_ = lean_apply_2(v_toPure_1692_, lean_box(0), v___x_1707_);
return v___x_1708_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg___lam__0___boxed(lean_object* v_env_1709_, lean_object* v_n_1710_, lean_object* v_toApplicative_1711_, lean_object* v___y_1712_, lean_object* v___x_1713_, lean_object* v_____r_1714_){
_start:
{
uint8_t v___y_758__boxed_1715_; uint8_t v___x_759__boxed_1716_; lean_object* v_res_1717_; 
v___y_758__boxed_1715_ = lean_unbox(v___y_1712_);
v___x_759__boxed_1716_ = lean_unbox(v___x_1713_);
v_res_1717_ = l_Lean_isInaccessiblePrivateName___redArg___lam__0(v_env_1709_, v_n_1710_, v_toApplicative_1711_, v___y_758__boxed_1715_, v___x_759__boxed_1716_, v_____r_1714_);
lean_dec(v_n_1710_);
lean_dec_ref(v_env_1709_);
return v_res_1717_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg___lam__1(lean_object* v_env_1718_, lean_object* v_n_1719_, lean_object* v_toApplicative_1720_, uint8_t v___x_1721_, lean_object* v_inst_1722_, lean_object* v_inst_1723_, lean_object* v_inst_1724_, lean_object* v_inst_1725_, lean_object* v_inst_1726_, lean_object* v_toBind_1727_, uint8_t v___x_1728_, uint8_t v_____do__lift_1729_){
_start:
{
uint8_t v___y_1731_; uint8_t v_isExporting_1737_; 
v_isExporting_1737_ = lean_ctor_get_uint8(v_env_1718_, sizeof(void*)*8);
if (v_isExporting_1737_ == 0)
{
v___y_1731_ = v_isExporting_1737_;
goto v___jp_1730_;
}
else
{
if (v_____do__lift_1729_ == 0)
{
lean_object* v_toPure_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; 
lean_dec(v_toBind_1727_);
lean_dec(v_inst_1726_);
lean_dec_ref(v_inst_1725_);
lean_dec(v_inst_1724_);
lean_dec_ref(v_inst_1723_);
lean_dec_ref(v_inst_1722_);
lean_dec(v_n_1719_);
lean_dec_ref(v_env_1718_);
v_toPure_1738_ = lean_ctor_get(v_toApplicative_1720_, 1);
lean_inc(v_toPure_1738_);
lean_dec_ref(v_toApplicative_1720_);
v___x_1739_ = lean_box(v___x_1721_);
v___x_1740_ = lean_apply_2(v_toPure_1738_, lean_box(0), v___x_1739_);
return v___x_1740_;
}
else
{
v___y_1731_ = v___x_1728_;
goto v___jp_1730_;
}
}
v___jp_1730_:
{
lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___f_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; 
v___x_1732_ = lean_box(v___y_1731_);
v___x_1733_ = lean_box(v___x_1721_);
lean_inc(v_n_1719_);
v___f_1734_ = lean_alloc_closure((void*)(l_Lean_isInaccessiblePrivateName___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_1734_, 0, v_env_1718_);
lean_closure_set(v___f_1734_, 1, v_n_1719_);
lean_closure_set(v___f_1734_, 2, v_toApplicative_1720_);
lean_closure_set(v___f_1734_, 3, v___x_1732_);
lean_closure_set(v___f_1734_, 4, v___x_1733_);
v___x_1735_ = l_Lean_checkPrivateInPublic___redArg(v_inst_1722_, v_inst_1723_, v_inst_1724_, v_inst_1725_, v_inst_1726_, v_n_1719_);
v___x_1736_ = lean_apply_4(v_toBind_1727_, lean_box(0), lean_box(0), v___x_1735_, v___f_1734_);
return v___x_1736_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg___lam__1___boxed(lean_object* v_env_1741_, lean_object* v_n_1742_, lean_object* v_toApplicative_1743_, lean_object* v___x_1744_, lean_object* v_inst_1745_, lean_object* v_inst_1746_, lean_object* v_inst_1747_, lean_object* v_inst_1748_, lean_object* v_inst_1749_, lean_object* v_toBind_1750_, lean_object* v___x_1751_, lean_object* v_____do__lift_1752_){
_start:
{
uint8_t v___x_799__boxed_1753_; uint8_t v___x_805__boxed_1754_; uint8_t v_____do__lift_806__boxed_1755_; lean_object* v_res_1756_; 
v___x_799__boxed_1753_ = lean_unbox(v___x_1744_);
v___x_805__boxed_1754_ = lean_unbox(v___x_1751_);
v_____do__lift_806__boxed_1755_ = lean_unbox(v_____do__lift_1752_);
v_res_1756_ = l_Lean_isInaccessiblePrivateName___redArg___lam__1(v_env_1741_, v_n_1742_, v_toApplicative_1743_, v___x_799__boxed_1753_, v_inst_1745_, v_inst_1746_, v_inst_1747_, v_inst_1748_, v_inst_1749_, v_toBind_1750_, v___x_805__boxed_1754_, v_____do__lift_806__boxed_1755_);
return v_res_1756_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg___lam__2(lean_object* v_n_1757_, lean_object* v_toApplicative_1758_, uint8_t v___x_1759_, lean_object* v_inst_1760_, lean_object* v_inst_1761_, lean_object* v_inst_1762_, lean_object* v_inst_1763_, lean_object* v_inst_1764_, lean_object* v_toBind_1765_, uint8_t v___x_1766_, lean_object* v_env_1767_){
_start:
{
lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___f_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; 
v___x_1768_ = lean_box(v___x_1759_);
v___x_1769_ = lean_box(v___x_1766_);
lean_inc(v_toBind_1765_);
lean_inc(v_inst_1762_);
lean_inc_ref(v_inst_1760_);
v___f_1770_ = lean_alloc_closure((void*)(l_Lean_isInaccessiblePrivateName___redArg___lam__1___boxed), 12, 11);
lean_closure_set(v___f_1770_, 0, v_env_1767_);
lean_closure_set(v___f_1770_, 1, v_n_1757_);
lean_closure_set(v___f_1770_, 2, v_toApplicative_1758_);
lean_closure_set(v___f_1770_, 3, v___x_1768_);
lean_closure_set(v___f_1770_, 4, v_inst_1760_);
lean_closure_set(v___f_1770_, 5, v_inst_1761_);
lean_closure_set(v___f_1770_, 6, v_inst_1762_);
lean_closure_set(v___f_1770_, 7, v_inst_1763_);
lean_closure_set(v___f_1770_, 8, v_inst_1764_);
lean_closure_set(v___f_1770_, 9, v_toBind_1765_);
lean_closure_set(v___f_1770_, 10, v___x_1769_);
v___x_1771_ = l_Lean_KVMap_instValueBool;
v___x_1772_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_1773_ = l_Lean_Option_getM___redArg(v_inst_1760_, v_inst_1762_, v___x_1771_, v___x_1772_);
v___x_1774_ = lean_apply_4(v_toBind_1765_, lean_box(0), lean_box(0), v___x_1773_, v___f_1770_);
return v___x_1774_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg___lam__2___boxed(lean_object* v_n_1775_, lean_object* v_toApplicative_1776_, lean_object* v___x_1777_, lean_object* v_inst_1778_, lean_object* v_inst_1779_, lean_object* v_inst_1780_, lean_object* v_inst_1781_, lean_object* v_inst_1782_, lean_object* v_toBind_1783_, lean_object* v___x_1784_, lean_object* v_env_1785_){
_start:
{
uint8_t v___x_841__boxed_1786_; uint8_t v___x_847__boxed_1787_; lean_object* v_res_1788_; 
v___x_841__boxed_1786_ = lean_unbox(v___x_1777_);
v___x_847__boxed_1787_ = lean_unbox(v___x_1784_);
v_res_1788_ = l_Lean_isInaccessiblePrivateName___redArg___lam__2(v_n_1775_, v_toApplicative_1776_, v___x_841__boxed_1786_, v_inst_1778_, v_inst_1779_, v_inst_1780_, v_inst_1781_, v_inst_1782_, v_toBind_1783_, v___x_847__boxed_1787_, v_env_1785_);
return v_res_1788_;
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName___redArg(lean_object* v_inst_1789_, lean_object* v_inst_1790_, lean_object* v_inst_1791_, lean_object* v_inst_1792_, lean_object* v_inst_1793_, lean_object* v_n_1794_){
_start:
{
uint8_t v___x_1795_; 
v___x_1795_ = l_Lean_isPrivateName(v_n_1794_);
if (v___x_1795_ == 0)
{
lean_object* v_toApplicative_1796_; lean_object* v_toPure_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; 
lean_dec(v_n_1794_);
lean_dec(v_inst_1793_);
lean_dec_ref(v_inst_1792_);
lean_dec(v_inst_1790_);
lean_dec_ref(v_inst_1789_);
v_toApplicative_1796_ = lean_ctor_get(v_inst_1791_, 0);
lean_inc_ref(v_toApplicative_1796_);
lean_dec_ref(v_inst_1791_);
v_toPure_1797_ = lean_ctor_get(v_toApplicative_1796_, 1);
lean_inc(v_toPure_1797_);
lean_dec_ref(v_toApplicative_1796_);
v___x_1798_ = lean_box(v___x_1795_);
v___x_1799_ = lean_apply_2(v_toPure_1797_, lean_box(0), v___x_1798_);
return v___x_1799_;
}
else
{
lean_object* v_toApplicative_1800_; lean_object* v_toBind_1801_; lean_object* v_getEnv_1802_; uint8_t v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___f_1806_; lean_object* v___x_1807_; 
v_toApplicative_1800_ = lean_ctor_get(v_inst_1791_, 0);
lean_inc_ref(v_toApplicative_1800_);
v_toBind_1801_ = lean_ctor_get(v_inst_1791_, 1);
lean_inc_n(v_toBind_1801_, 2);
v_getEnv_1802_ = lean_ctor_get(v_inst_1792_, 0);
lean_inc(v_getEnv_1802_);
v___x_1803_ = 0;
v___x_1804_ = lean_box(v___x_1795_);
v___x_1805_ = lean_box(v___x_1803_);
v___f_1806_ = lean_alloc_closure((void*)(l_Lean_isInaccessiblePrivateName___redArg___lam__2___boxed), 11, 10);
lean_closure_set(v___f_1806_, 0, v_n_1794_);
lean_closure_set(v___f_1806_, 1, v_toApplicative_1800_);
lean_closure_set(v___f_1806_, 2, v___x_1804_);
lean_closure_set(v___f_1806_, 3, v_inst_1791_);
lean_closure_set(v___f_1806_, 4, v_inst_1792_);
lean_closure_set(v___f_1806_, 5, v_inst_1793_);
lean_closure_set(v___f_1806_, 6, v_inst_1789_);
lean_closure_set(v___f_1806_, 7, v_inst_1790_);
lean_closure_set(v___f_1806_, 8, v_toBind_1801_);
lean_closure_set(v___f_1806_, 9, v___x_1805_);
v___x_1807_ = lean_apply_4(v_toBind_1801_, lean_box(0), lean_box(0), v_getEnv_1802_, v___f_1806_);
return v___x_1807_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isInaccessiblePrivateName(lean_object* v_m_1808_, lean_object* v_inst_1809_, lean_object* v_inst_1810_, lean_object* v_inst_1811_, lean_object* v_inst_1812_, lean_object* v_inst_1813_, lean_object* v_n_1814_){
_start:
{
lean_object* v___x_1815_; 
v___x_1815_ = l_Lean_isInaccessiblePrivateName___redArg(v_inst_1809_, v_inst_1810_, v_inst_1811_, v_inst_1812_, v_inst_1813_, v_n_1814_);
return v___x_1815_;
}
}
LEAN_EXPORT uint8_t l_Lean_resolveGlobalName___redArg___lam__0(lean_object* v_x_1816_){
_start:
{
lean_object* v_fst_1817_; uint8_t v___x_1818_; 
v_fst_1817_ = lean_ctor_get(v_x_1816_, 0);
v___x_1818_ = l_Lean_isPrivateName(v_fst_1817_);
return v___x_1818_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__0___boxed(lean_object* v_x_1819_){
_start:
{
uint8_t v_res_1820_; lean_object* v_r_1821_; 
v_res_1820_ = l_Lean_resolveGlobalName___redArg___lam__0(v_x_1819_);
lean_dec_ref(v_x_1819_);
v_r_1821_ = lean_box(v_res_1820_);
return v_r_1821_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__1(lean_object* v_toPure_1822_, lean_object* v_res_1823_, lean_object* v_____r_1824_){
_start:
{
lean_object* v___x_1825_; 
v___x_1825_ = lean_apply_2(v_toPure_1822_, lean_box(0), v_res_1823_);
return v___x_1825_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__2(uint8_t v_enableLog_1826_, lean_object* v_toPure_1827_, lean_object* v_res_1828_, lean_object* v___f_1829_, lean_object* v_inst_1830_, lean_object* v_inst_1831_, lean_object* v_inst_1832_, lean_object* v_inst_1833_, lean_object* v_inst_1834_, lean_object* v_toBind_1835_, lean_object* v___f_1836_, lean_object* v_____do__lift_1837_){
_start:
{
if (v_enableLog_1826_ == 0)
{
lean_object* v___x_1838_; 
lean_dec(v___f_1836_);
lean_dec(v_toBind_1835_);
lean_dec(v_inst_1834_);
lean_dec_ref(v_inst_1833_);
lean_dec(v_inst_1832_);
lean_dec_ref(v_inst_1831_);
lean_dec_ref(v_inst_1830_);
lean_dec_ref(v___f_1829_);
v___x_1838_ = lean_apply_2(v_toPure_1827_, lean_box(0), v_res_1828_);
return v___x_1838_;
}
else
{
uint8_t v_isExporting_1839_; 
v_isExporting_1839_ = lean_ctor_get_uint8(v_____do__lift_1837_, sizeof(void*)*8);
if (v_isExporting_1839_ == 0)
{
lean_object* v___x_1840_; 
lean_dec(v___f_1836_);
lean_dec(v_toBind_1835_);
lean_dec(v_inst_1834_);
lean_dec_ref(v_inst_1833_);
lean_dec(v_inst_1832_);
lean_dec_ref(v_inst_1831_);
lean_dec_ref(v_inst_1830_);
lean_dec_ref(v___f_1829_);
v___x_1840_ = lean_apply_2(v_toPure_1827_, lean_box(0), v_res_1828_);
return v___x_1840_;
}
else
{
lean_object* v___x_1841_; 
lean_inc(v_res_1828_);
v___x_1841_ = l_List_find_x3f___redArg(v___f_1829_, v_res_1828_);
if (lean_obj_tag(v___x_1841_) == 1)
{
lean_object* v_val_1842_; lean_object* v_fst_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; 
lean_dec(v_res_1828_);
lean_dec(v_toPure_1827_);
v_val_1842_ = lean_ctor_get(v___x_1841_, 0);
lean_inc(v_val_1842_);
lean_dec_ref_known(v___x_1841_, 1);
v_fst_1843_ = lean_ctor_get(v_val_1842_, 0);
lean_inc(v_fst_1843_);
lean_dec(v_val_1842_);
v___x_1844_ = l_Lean_checkPrivateInPublic___redArg(v_inst_1830_, v_inst_1831_, v_inst_1832_, v_inst_1833_, v_inst_1834_, v_fst_1843_);
v___x_1845_ = lean_apply_4(v_toBind_1835_, lean_box(0), lean_box(0), v___x_1844_, v___f_1836_);
return v___x_1845_;
}
else
{
lean_object* v___x_1846_; 
lean_dec(v___x_1841_);
lean_dec(v___f_1836_);
lean_dec(v_toBind_1835_);
lean_dec(v_inst_1834_);
lean_dec_ref(v_inst_1833_);
lean_dec(v_inst_1832_);
lean_dec_ref(v_inst_1831_);
lean_dec_ref(v_inst_1830_);
v___x_1846_ = lean_apply_2(v_toPure_1827_, lean_box(0), v_res_1828_);
return v___x_1846_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__2___boxed(lean_object* v_enableLog_1847_, lean_object* v_toPure_1848_, lean_object* v_res_1849_, lean_object* v___f_1850_, lean_object* v_inst_1851_, lean_object* v_inst_1852_, lean_object* v_inst_1853_, lean_object* v_inst_1854_, lean_object* v_inst_1855_, lean_object* v_toBind_1856_, lean_object* v___f_1857_, lean_object* v_____do__lift_1858_){
_start:
{
uint8_t v_enableLog_boxed_1859_; lean_object* v_res_1860_; 
v_enableLog_boxed_1859_ = lean_unbox(v_enableLog_1847_);
v_res_1860_ = l_Lean_resolveGlobalName___redArg___lam__2(v_enableLog_boxed_1859_, v_toPure_1848_, v_res_1849_, v___f_1850_, v_inst_1851_, v_inst_1852_, v_inst_1853_, v_inst_1854_, v_inst_1855_, v_toBind_1856_, v___f_1857_, v_____do__lift_1858_);
lean_dec_ref(v_____do__lift_1858_);
return v_res_1860_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__3(lean_object* v_____do__lift_1861_, lean_object* v_____do__lift_1862_, lean_object* v_____do__lift_1863_, lean_object* v_id_1864_, lean_object* v_toPure_1865_, uint8_t v_enableLog_1866_, lean_object* v___f_1867_, lean_object* v_inst_1868_, lean_object* v_inst_1869_, lean_object* v_inst_1870_, lean_object* v_inst_1871_, lean_object* v_inst_1872_, lean_object* v_toBind_1873_, lean_object* v_getEnv_1874_, lean_object* v_____do__lift_1875_){
_start:
{
lean_object* v_res_1876_; lean_object* v___f_1877_; lean_object* v___x_1878_; lean_object* v___f_1879_; lean_object* v___x_1880_; 
v_res_1876_ = l_Lean_ResolveName_resolveGlobalName(v_____do__lift_1861_, v_____do__lift_1862_, v_____do__lift_1863_, v_____do__lift_1875_, v_id_1864_);
lean_inc(v_res_1876_);
lean_inc(v_toPure_1865_);
v___f_1877_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalName___redArg___lam__1), 3, 2);
lean_closure_set(v___f_1877_, 0, v_toPure_1865_);
lean_closure_set(v___f_1877_, 1, v_res_1876_);
v___x_1878_ = lean_box(v_enableLog_1866_);
lean_inc(v_toBind_1873_);
v___f_1879_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalName___redArg___lam__2___boxed), 12, 11);
lean_closure_set(v___f_1879_, 0, v___x_1878_);
lean_closure_set(v___f_1879_, 1, v_toPure_1865_);
lean_closure_set(v___f_1879_, 2, v_res_1876_);
lean_closure_set(v___f_1879_, 3, v___f_1867_);
lean_closure_set(v___f_1879_, 4, v_inst_1868_);
lean_closure_set(v___f_1879_, 5, v_inst_1869_);
lean_closure_set(v___f_1879_, 6, v_inst_1870_);
lean_closure_set(v___f_1879_, 7, v_inst_1871_);
lean_closure_set(v___f_1879_, 8, v_inst_1872_);
lean_closure_set(v___f_1879_, 9, v_toBind_1873_);
lean_closure_set(v___f_1879_, 10, v___f_1877_);
v___x_1880_ = lean_apply_4(v_toBind_1873_, lean_box(0), lean_box(0), v_getEnv_1874_, v___f_1879_);
return v___x_1880_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__3___boxed(lean_object* v_____do__lift_1881_, lean_object* v_____do__lift_1882_, lean_object* v_____do__lift_1883_, lean_object* v_id_1884_, lean_object* v_toPure_1885_, lean_object* v_enableLog_1886_, lean_object* v___f_1887_, lean_object* v_inst_1888_, lean_object* v_inst_1889_, lean_object* v_inst_1890_, lean_object* v_inst_1891_, lean_object* v_inst_1892_, lean_object* v_toBind_1893_, lean_object* v_getEnv_1894_, lean_object* v_____do__lift_1895_){
_start:
{
uint8_t v_enableLog_boxed_1896_; lean_object* v_res_1897_; 
v_enableLog_boxed_1896_ = lean_unbox(v_enableLog_1886_);
v_res_1897_ = l_Lean_resolveGlobalName___redArg___lam__3(v_____do__lift_1881_, v_____do__lift_1882_, v_____do__lift_1883_, v_id_1884_, v_toPure_1885_, v_enableLog_boxed_1896_, v___f_1887_, v_inst_1888_, v_inst_1889_, v_inst_1890_, v_inst_1891_, v_inst_1892_, v_toBind_1893_, v_getEnv_1894_, v_____do__lift_1895_);
lean_dec_ref(v_____do__lift_1882_);
return v_res_1897_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__4(lean_object* v_____do__lift_1898_, lean_object* v_____do__lift_1899_, lean_object* v_id_1900_, lean_object* v_toPure_1901_, uint8_t v_enableLog_1902_, lean_object* v___f_1903_, lean_object* v_inst_1904_, lean_object* v_inst_1905_, lean_object* v_inst_1906_, lean_object* v_inst_1907_, lean_object* v_inst_1908_, lean_object* v_toBind_1909_, lean_object* v_getEnv_1910_, lean_object* v_getOpenDecls_1911_, lean_object* v_____do__lift_1912_){
_start:
{
lean_object* v___x_1913_; lean_object* v___f_1914_; lean_object* v___x_1915_; 
v___x_1913_ = lean_box(v_enableLog_1902_);
lean_inc(v_toBind_1909_);
v___f_1914_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalName___redArg___lam__3___boxed), 15, 14);
lean_closure_set(v___f_1914_, 0, v_____do__lift_1898_);
lean_closure_set(v___f_1914_, 1, v_____do__lift_1899_);
lean_closure_set(v___f_1914_, 2, v_____do__lift_1912_);
lean_closure_set(v___f_1914_, 3, v_id_1900_);
lean_closure_set(v___f_1914_, 4, v_toPure_1901_);
lean_closure_set(v___f_1914_, 5, v___x_1913_);
lean_closure_set(v___f_1914_, 6, v___f_1903_);
lean_closure_set(v___f_1914_, 7, v_inst_1904_);
lean_closure_set(v___f_1914_, 8, v_inst_1905_);
lean_closure_set(v___f_1914_, 9, v_inst_1906_);
lean_closure_set(v___f_1914_, 10, v_inst_1907_);
lean_closure_set(v___f_1914_, 11, v_inst_1908_);
lean_closure_set(v___f_1914_, 12, v_toBind_1909_);
lean_closure_set(v___f_1914_, 13, v_getEnv_1910_);
v___x_1915_ = lean_apply_4(v_toBind_1909_, lean_box(0), lean_box(0), v_getOpenDecls_1911_, v___f_1914_);
return v___x_1915_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__4___boxed(lean_object* v_____do__lift_1916_, lean_object* v_____do__lift_1917_, lean_object* v_id_1918_, lean_object* v_toPure_1919_, lean_object* v_enableLog_1920_, lean_object* v___f_1921_, lean_object* v_inst_1922_, lean_object* v_inst_1923_, lean_object* v_inst_1924_, lean_object* v_inst_1925_, lean_object* v_inst_1926_, lean_object* v_toBind_1927_, lean_object* v_getEnv_1928_, lean_object* v_getOpenDecls_1929_, lean_object* v_____do__lift_1930_){
_start:
{
uint8_t v_enableLog_boxed_1931_; lean_object* v_res_1932_; 
v_enableLog_boxed_1931_ = lean_unbox(v_enableLog_1920_);
v_res_1932_ = l_Lean_resolveGlobalName___redArg___lam__4(v_____do__lift_1916_, v_____do__lift_1917_, v_id_1918_, v_toPure_1919_, v_enableLog_boxed_1931_, v___f_1921_, v_inst_1922_, v_inst_1923_, v_inst_1924_, v_inst_1925_, v_inst_1926_, v_toBind_1927_, v_getEnv_1928_, v_getOpenDecls_1929_, v_____do__lift_1930_);
return v_res_1932_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__5(lean_object* v_inst_1933_, lean_object* v_____do__lift_1934_, lean_object* v_id_1935_, lean_object* v_toPure_1936_, uint8_t v_enableLog_1937_, lean_object* v___f_1938_, lean_object* v_inst_1939_, lean_object* v_inst_1940_, lean_object* v_inst_1941_, lean_object* v_inst_1942_, lean_object* v_inst_1943_, lean_object* v_toBind_1944_, lean_object* v_getEnv_1945_, lean_object* v_____do__lift_1946_){
_start:
{
lean_object* v_getCurrNamespace_1947_; lean_object* v_getOpenDecls_1948_; lean_object* v___x_1949_; lean_object* v___f_1950_; lean_object* v___x_1951_; 
v_getCurrNamespace_1947_ = lean_ctor_get(v_inst_1933_, 0);
lean_inc(v_getCurrNamespace_1947_);
v_getOpenDecls_1948_ = lean_ctor_get(v_inst_1933_, 1);
lean_inc(v_getOpenDecls_1948_);
lean_dec_ref(v_inst_1933_);
v___x_1949_ = lean_box(v_enableLog_1937_);
lean_inc(v_toBind_1944_);
v___f_1950_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalName___redArg___lam__4___boxed), 15, 14);
lean_closure_set(v___f_1950_, 0, v_____do__lift_1934_);
lean_closure_set(v___f_1950_, 1, v_____do__lift_1946_);
lean_closure_set(v___f_1950_, 2, v_id_1935_);
lean_closure_set(v___f_1950_, 3, v_toPure_1936_);
lean_closure_set(v___f_1950_, 4, v___x_1949_);
lean_closure_set(v___f_1950_, 5, v___f_1938_);
lean_closure_set(v___f_1950_, 6, v_inst_1939_);
lean_closure_set(v___f_1950_, 7, v_inst_1940_);
lean_closure_set(v___f_1950_, 8, v_inst_1941_);
lean_closure_set(v___f_1950_, 9, v_inst_1942_);
lean_closure_set(v___f_1950_, 10, v_inst_1943_);
lean_closure_set(v___f_1950_, 11, v_toBind_1944_);
lean_closure_set(v___f_1950_, 12, v_getEnv_1945_);
lean_closure_set(v___f_1950_, 13, v_getOpenDecls_1948_);
v___x_1951_ = lean_apply_4(v_toBind_1944_, lean_box(0), lean_box(0), v_getCurrNamespace_1947_, v___f_1950_);
return v___x_1951_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__5___boxed(lean_object* v_inst_1952_, lean_object* v_____do__lift_1953_, lean_object* v_id_1954_, lean_object* v_toPure_1955_, lean_object* v_enableLog_1956_, lean_object* v___f_1957_, lean_object* v_inst_1958_, lean_object* v_inst_1959_, lean_object* v_inst_1960_, lean_object* v_inst_1961_, lean_object* v_inst_1962_, lean_object* v_toBind_1963_, lean_object* v_getEnv_1964_, lean_object* v_____do__lift_1965_){
_start:
{
uint8_t v_enableLog_boxed_1966_; lean_object* v_res_1967_; 
v_enableLog_boxed_1966_ = lean_unbox(v_enableLog_1956_);
v_res_1967_ = l_Lean_resolveGlobalName___redArg___lam__5(v_inst_1952_, v_____do__lift_1953_, v_id_1954_, v_toPure_1955_, v_enableLog_boxed_1966_, v___f_1957_, v_inst_1958_, v_inst_1959_, v_inst_1960_, v_inst_1961_, v_inst_1962_, v_toBind_1963_, v_getEnv_1964_, v_____do__lift_1965_);
return v_res_1967_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__6(lean_object* v_inst_1968_, lean_object* v_id_1969_, lean_object* v_toPure_1970_, uint8_t v_enableLog_1971_, lean_object* v___f_1972_, lean_object* v_inst_1973_, lean_object* v_inst_1974_, lean_object* v_inst_1975_, lean_object* v_inst_1976_, lean_object* v_inst_1977_, lean_object* v_toBind_1978_, lean_object* v_getEnv_1979_, lean_object* v_____do__lift_1980_){
_start:
{
lean_object* v___x_1981_; lean_object* v___f_1982_; lean_object* v___x_1983_; 
v___x_1981_ = lean_box(v_enableLog_1971_);
lean_inc(v_toBind_1978_);
lean_inc(v_inst_1975_);
v___f_1982_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalName___redArg___lam__5___boxed), 14, 13);
lean_closure_set(v___f_1982_, 0, v_inst_1968_);
lean_closure_set(v___f_1982_, 1, v_____do__lift_1980_);
lean_closure_set(v___f_1982_, 2, v_id_1969_);
lean_closure_set(v___f_1982_, 3, v_toPure_1970_);
lean_closure_set(v___f_1982_, 4, v___x_1981_);
lean_closure_set(v___f_1982_, 5, v___f_1972_);
lean_closure_set(v___f_1982_, 6, v_inst_1973_);
lean_closure_set(v___f_1982_, 7, v_inst_1974_);
lean_closure_set(v___f_1982_, 8, v_inst_1975_);
lean_closure_set(v___f_1982_, 9, v_inst_1976_);
lean_closure_set(v___f_1982_, 10, v_inst_1977_);
lean_closure_set(v___f_1982_, 11, v_toBind_1978_);
lean_closure_set(v___f_1982_, 12, v_getEnv_1979_);
v___x_1983_ = lean_apply_4(v_toBind_1978_, lean_box(0), lean_box(0), v_inst_1975_, v___f_1982_);
return v___x_1983_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___lam__6___boxed(lean_object* v_inst_1984_, lean_object* v_id_1985_, lean_object* v_toPure_1986_, lean_object* v_enableLog_1987_, lean_object* v___f_1988_, lean_object* v_inst_1989_, lean_object* v_inst_1990_, lean_object* v_inst_1991_, lean_object* v_inst_1992_, lean_object* v_inst_1993_, lean_object* v_toBind_1994_, lean_object* v_getEnv_1995_, lean_object* v_____do__lift_1996_){
_start:
{
uint8_t v_enableLog_boxed_1997_; lean_object* v_res_1998_; 
v_enableLog_boxed_1997_ = lean_unbox(v_enableLog_1987_);
v_res_1998_ = l_Lean_resolveGlobalName___redArg___lam__6(v_inst_1984_, v_id_1985_, v_toPure_1986_, v_enableLog_boxed_1997_, v___f_1988_, v_inst_1989_, v_inst_1990_, v_inst_1991_, v_inst_1992_, v_inst_1993_, v_toBind_1994_, v_getEnv_1995_, v_____do__lift_1996_);
return v_res_1998_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg(lean_object* v_inst_2000_, lean_object* v_inst_2001_, lean_object* v_inst_2002_, lean_object* v_inst_2003_, lean_object* v_inst_2004_, lean_object* v_inst_2005_, lean_object* v_id_2006_, uint8_t v_enableLog_2007_){
_start:
{
lean_object* v_toApplicative_2008_; lean_object* v_toBind_2009_; lean_object* v_getEnv_2010_; lean_object* v_toPure_2011_; lean_object* v___f_2012_; lean_object* v___x_2013_; lean_object* v___f_2014_; lean_object* v___x_2015_; 
v_toApplicative_2008_ = lean_ctor_get(v_inst_2000_, 0);
v_toBind_2009_ = lean_ctor_get(v_inst_2000_, 1);
lean_inc_n(v_toBind_2009_, 2);
v_getEnv_2010_ = lean_ctor_get(v_inst_2002_, 0);
lean_inc_n(v_getEnv_2010_, 2);
v_toPure_2011_ = lean_ctor_get(v_toApplicative_2008_, 1);
lean_inc(v_toPure_2011_);
v___f_2012_ = ((lean_object*)(l_Lean_resolveGlobalName___redArg___closed__0));
v___x_2013_ = lean_box(v_enableLog_2007_);
v___f_2014_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalName___redArg___lam__6___boxed), 13, 12);
lean_closure_set(v___f_2014_, 0, v_inst_2001_);
lean_closure_set(v___f_2014_, 1, v_id_2006_);
lean_closure_set(v___f_2014_, 2, v_toPure_2011_);
lean_closure_set(v___f_2014_, 3, v___x_2013_);
lean_closure_set(v___f_2014_, 4, v___f_2012_);
lean_closure_set(v___f_2014_, 5, v_inst_2000_);
lean_closure_set(v___f_2014_, 6, v_inst_2002_);
lean_closure_set(v___f_2014_, 7, v_inst_2003_);
lean_closure_set(v___f_2014_, 8, v_inst_2004_);
lean_closure_set(v___f_2014_, 9, v_inst_2005_);
lean_closure_set(v___f_2014_, 10, v_toBind_2009_);
lean_closure_set(v___f_2014_, 11, v_getEnv_2010_);
v___x_2015_ = lean_apply_4(v_toBind_2009_, lean_box(0), lean_box(0), v_getEnv_2010_, v___f_2014_);
return v___x_2015_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___redArg___boxed(lean_object* v_inst_2016_, lean_object* v_inst_2017_, lean_object* v_inst_2018_, lean_object* v_inst_2019_, lean_object* v_inst_2020_, lean_object* v_inst_2021_, lean_object* v_id_2022_, lean_object* v_enableLog_2023_){
_start:
{
uint8_t v_enableLog_boxed_2024_; lean_object* v_res_2025_; 
v_enableLog_boxed_2024_ = lean_unbox(v_enableLog_2023_);
v_res_2025_ = l_Lean_resolveGlobalName___redArg(v_inst_2016_, v_inst_2017_, v_inst_2018_, v_inst_2019_, v_inst_2020_, v_inst_2021_, v_id_2022_, v_enableLog_boxed_2024_);
return v_res_2025_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName(lean_object* v_m_2026_, lean_object* v_inst_2027_, lean_object* v_inst_2028_, lean_object* v_inst_2029_, lean_object* v_inst_2030_, lean_object* v_inst_2031_, lean_object* v_inst_2032_, lean_object* v_id_2033_, uint8_t v_enableLog_2034_){
_start:
{
lean_object* v___x_2035_; 
v___x_2035_ = l_Lean_resolveGlobalName___redArg(v_inst_2027_, v_inst_2028_, v_inst_2029_, v_inst_2030_, v_inst_2031_, v_inst_2032_, v_id_2033_, v_enableLog_2034_);
return v___x_2035_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalName___boxed(lean_object* v_m_2036_, lean_object* v_inst_2037_, lean_object* v_inst_2038_, lean_object* v_inst_2039_, lean_object* v_inst_2040_, lean_object* v_inst_2041_, lean_object* v_inst_2042_, lean_object* v_id_2043_, lean_object* v_enableLog_2044_){
_start:
{
uint8_t v_enableLog_boxed_2045_; lean_object* v_res_2046_; 
v_enableLog_boxed_2045_ = lean_unbox(v_enableLog_2044_);
v_res_2046_ = l_Lean_resolveGlobalName(v_m_2036_, v_inst_2037_, v_inst_2038_, v_inst_2039_, v_inst_2040_, v_inst_2041_, v_inst_2042_, v_id_2043_, v_enableLog_boxed_2045_);
return v_res_2046_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__0(lean_object* v_toPure_2047_, lean_object* v_nss_2048_, lean_object* v_____r_2049_){
_start:
{
lean_object* v___x_2050_; 
v___x_2050_ = lean_apply_2(v_toPure_2047_, lean_box(0), v_nss_2048_);
return v___x_2050_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__1(lean_object* v_____do__lift_2053_, lean_object* v_____do__lift_2054_, lean_object* v_id_2055_, uint8_t v_allowEmpty_2056_, lean_object* v_toPure_2057_, lean_object* v_inst_2058_, lean_object* v_inst_2059_, lean_object* v_toBind_2060_, lean_object* v_____do__lift_2061_){
_start:
{
lean_object* v_nss_2062_; 
lean_inc(v_id_2055_);
v_nss_2062_ = l_Lean_ResolveName_resolveNamespace(v_____do__lift_2053_, v_____do__lift_2054_, v_____do__lift_2061_, v_id_2055_);
if (v_allowEmpty_2056_ == 0)
{
uint8_t v___x_2063_; 
v___x_2063_ = l_List_isEmpty___redArg(v_nss_2062_);
if (v___x_2063_ == 0)
{
lean_object* v___x_2064_; 
lean_dec(v_toBind_2060_);
lean_dec_ref(v_inst_2059_);
lean_dec_ref(v_inst_2058_);
lean_dec(v_id_2055_);
v___x_2064_ = lean_apply_2(v_toPure_2057_, lean_box(0), v_nss_2062_);
return v___x_2064_;
}
else
{
lean_object* v___f_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; 
v___f_2065_ = lean_alloc_closure((void*)(l_Lean_resolveNamespaceCore___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2065_, 0, v_toPure_2057_);
lean_closure_set(v___f_2065_, 1, v_nss_2062_);
v___x_2066_ = ((lean_object*)(l_Lean_resolveNamespaceCore___redArg___lam__1___closed__0));
v___x_2067_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_id_2055_, v___x_2063_);
v___x_2068_ = lean_string_append(v___x_2066_, v___x_2067_);
lean_dec_ref(v___x_2067_);
v___x_2069_ = ((lean_object*)(l_Lean_resolveNamespaceCore___redArg___lam__1___closed__1));
v___x_2070_ = lean_string_append(v___x_2068_, v___x_2069_);
v___x_2071_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2071_, 0, v___x_2070_);
v___x_2072_ = l_Lean_MessageData_ofFormat(v___x_2071_);
v___x_2073_ = l_Lean_throwError___redArg(v_inst_2058_, v_inst_2059_, v___x_2072_);
v___x_2074_ = lean_apply_4(v_toBind_2060_, lean_box(0), lean_box(0), v___x_2073_, v___f_2065_);
return v___x_2074_;
}
}
else
{
lean_object* v___x_2075_; 
lean_dec(v_toBind_2060_);
lean_dec_ref(v_inst_2059_);
lean_dec_ref(v_inst_2058_);
lean_dec(v_id_2055_);
v___x_2075_ = lean_apply_2(v_toPure_2057_, lean_box(0), v_nss_2062_);
return v___x_2075_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__1___boxed(lean_object* v_____do__lift_2076_, lean_object* v_____do__lift_2077_, lean_object* v_id_2078_, lean_object* v_allowEmpty_2079_, lean_object* v_toPure_2080_, lean_object* v_inst_2081_, lean_object* v_inst_2082_, lean_object* v_toBind_2083_, lean_object* v_____do__lift_2084_){
_start:
{
uint8_t v_allowEmpty_boxed_2085_; lean_object* v_res_2086_; 
v_allowEmpty_boxed_2085_ = lean_unbox(v_allowEmpty_2079_);
v_res_2086_ = l_Lean_resolveNamespaceCore___redArg___lam__1(v_____do__lift_2076_, v_____do__lift_2077_, v_id_2078_, v_allowEmpty_boxed_2085_, v_toPure_2080_, v_inst_2081_, v_inst_2082_, v_toBind_2083_, v_____do__lift_2084_);
return v_res_2086_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__2(lean_object* v_____do__lift_2087_, lean_object* v_id_2088_, uint8_t v_allowEmpty_2089_, lean_object* v_toPure_2090_, lean_object* v_inst_2091_, lean_object* v_inst_2092_, lean_object* v_toBind_2093_, lean_object* v_getOpenDecls_2094_, lean_object* v_____do__lift_2095_){
_start:
{
lean_object* v___x_2096_; lean_object* v___f_2097_; lean_object* v___x_2098_; 
v___x_2096_ = lean_box(v_allowEmpty_2089_);
lean_inc(v_toBind_2093_);
v___f_2097_ = lean_alloc_closure((void*)(l_Lean_resolveNamespaceCore___redArg___lam__1___boxed), 9, 8);
lean_closure_set(v___f_2097_, 0, v_____do__lift_2087_);
lean_closure_set(v___f_2097_, 1, v_____do__lift_2095_);
lean_closure_set(v___f_2097_, 2, v_id_2088_);
lean_closure_set(v___f_2097_, 3, v___x_2096_);
lean_closure_set(v___f_2097_, 4, v_toPure_2090_);
lean_closure_set(v___f_2097_, 5, v_inst_2091_);
lean_closure_set(v___f_2097_, 6, v_inst_2092_);
lean_closure_set(v___f_2097_, 7, v_toBind_2093_);
v___x_2098_ = lean_apply_4(v_toBind_2093_, lean_box(0), lean_box(0), v_getOpenDecls_2094_, v___f_2097_);
return v___x_2098_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__2___boxed(lean_object* v_____do__lift_2099_, lean_object* v_id_2100_, lean_object* v_allowEmpty_2101_, lean_object* v_toPure_2102_, lean_object* v_inst_2103_, lean_object* v_inst_2104_, lean_object* v_toBind_2105_, lean_object* v_getOpenDecls_2106_, lean_object* v_____do__lift_2107_){
_start:
{
uint8_t v_allowEmpty_boxed_2108_; lean_object* v_res_2109_; 
v_allowEmpty_boxed_2108_ = lean_unbox(v_allowEmpty_2101_);
v_res_2109_ = l_Lean_resolveNamespaceCore___redArg___lam__2(v_____do__lift_2099_, v_id_2100_, v_allowEmpty_boxed_2108_, v_toPure_2102_, v_inst_2103_, v_inst_2104_, v_toBind_2105_, v_getOpenDecls_2106_, v_____do__lift_2107_);
return v_res_2109_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__3(lean_object* v_inst_2110_, lean_object* v_id_2111_, uint8_t v_allowEmpty_2112_, lean_object* v_toPure_2113_, lean_object* v_inst_2114_, lean_object* v_inst_2115_, lean_object* v_toBind_2116_, lean_object* v_____do__lift_2117_){
_start:
{
lean_object* v_getCurrNamespace_2118_; lean_object* v_getOpenDecls_2119_; lean_object* v___x_2120_; lean_object* v___f_2121_; lean_object* v___x_2122_; 
v_getCurrNamespace_2118_ = lean_ctor_get(v_inst_2110_, 0);
lean_inc(v_getCurrNamespace_2118_);
v_getOpenDecls_2119_ = lean_ctor_get(v_inst_2110_, 1);
lean_inc(v_getOpenDecls_2119_);
lean_dec_ref(v_inst_2110_);
v___x_2120_ = lean_box(v_allowEmpty_2112_);
lean_inc(v_toBind_2116_);
v___f_2121_ = lean_alloc_closure((void*)(l_Lean_resolveNamespaceCore___redArg___lam__2___boxed), 9, 8);
lean_closure_set(v___f_2121_, 0, v_____do__lift_2117_);
lean_closure_set(v___f_2121_, 1, v_id_2111_);
lean_closure_set(v___f_2121_, 2, v___x_2120_);
lean_closure_set(v___f_2121_, 3, v_toPure_2113_);
lean_closure_set(v___f_2121_, 4, v_inst_2114_);
lean_closure_set(v___f_2121_, 5, v_inst_2115_);
lean_closure_set(v___f_2121_, 6, v_toBind_2116_);
lean_closure_set(v___f_2121_, 7, v_getOpenDecls_2119_);
v___x_2122_ = lean_apply_4(v_toBind_2116_, lean_box(0), lean_box(0), v_getCurrNamespace_2118_, v___f_2121_);
return v___x_2122_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___lam__3___boxed(lean_object* v_inst_2123_, lean_object* v_id_2124_, lean_object* v_allowEmpty_2125_, lean_object* v_toPure_2126_, lean_object* v_inst_2127_, lean_object* v_inst_2128_, lean_object* v_toBind_2129_, lean_object* v_____do__lift_2130_){
_start:
{
uint8_t v_allowEmpty_boxed_2131_; lean_object* v_res_2132_; 
v_allowEmpty_boxed_2131_ = lean_unbox(v_allowEmpty_2125_);
v_res_2132_ = l_Lean_resolveNamespaceCore___redArg___lam__3(v_inst_2123_, v_id_2124_, v_allowEmpty_boxed_2131_, v_toPure_2126_, v_inst_2127_, v_inst_2128_, v_toBind_2129_, v_____do__lift_2130_);
return v_res_2132_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg(lean_object* v_inst_2133_, lean_object* v_inst_2134_, lean_object* v_inst_2135_, lean_object* v_inst_2136_, lean_object* v_id_2137_, uint8_t v_allowEmpty_2138_){
_start:
{
lean_object* v_toApplicative_2139_; lean_object* v_toBind_2140_; lean_object* v_getEnv_2141_; lean_object* v_toPure_2142_; lean_object* v___x_2143_; lean_object* v___f_2144_; lean_object* v___x_2145_; 
v_toApplicative_2139_ = lean_ctor_get(v_inst_2133_, 0);
v_toBind_2140_ = lean_ctor_get(v_inst_2133_, 1);
lean_inc_n(v_toBind_2140_, 2);
v_getEnv_2141_ = lean_ctor_get(v_inst_2135_, 0);
lean_inc(v_getEnv_2141_);
lean_dec_ref(v_inst_2135_);
v_toPure_2142_ = lean_ctor_get(v_toApplicative_2139_, 1);
lean_inc(v_toPure_2142_);
v___x_2143_ = lean_box(v_allowEmpty_2138_);
v___f_2144_ = lean_alloc_closure((void*)(l_Lean_resolveNamespaceCore___redArg___lam__3___boxed), 8, 7);
lean_closure_set(v___f_2144_, 0, v_inst_2134_);
lean_closure_set(v___f_2144_, 1, v_id_2137_);
lean_closure_set(v___f_2144_, 2, v___x_2143_);
lean_closure_set(v___f_2144_, 3, v_toPure_2142_);
lean_closure_set(v___f_2144_, 4, v_inst_2133_);
lean_closure_set(v___f_2144_, 5, v_inst_2136_);
lean_closure_set(v___f_2144_, 6, v_toBind_2140_);
v___x_2145_ = lean_apply_4(v_toBind_2140_, lean_box(0), lean_box(0), v_getEnv_2141_, v___f_2144_);
return v___x_2145_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___redArg___boxed(lean_object* v_inst_2146_, lean_object* v_inst_2147_, lean_object* v_inst_2148_, lean_object* v_inst_2149_, lean_object* v_id_2150_, lean_object* v_allowEmpty_2151_){
_start:
{
uint8_t v_allowEmpty_boxed_2152_; lean_object* v_res_2153_; 
v_allowEmpty_boxed_2152_ = lean_unbox(v_allowEmpty_2151_);
v_res_2153_ = l_Lean_resolveNamespaceCore___redArg(v_inst_2146_, v_inst_2147_, v_inst_2148_, v_inst_2149_, v_id_2150_, v_allowEmpty_boxed_2152_);
return v_res_2153_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore(lean_object* v_m_2154_, lean_object* v_inst_2155_, lean_object* v_inst_2156_, lean_object* v_inst_2157_, lean_object* v_inst_2158_, lean_object* v_id_2159_, uint8_t v_allowEmpty_2160_){
_start:
{
lean_object* v___x_2161_; 
v___x_2161_ = l_Lean_resolveNamespaceCore___redArg(v_inst_2155_, v_inst_2156_, v_inst_2157_, v_inst_2158_, v_id_2159_, v_allowEmpty_2160_);
return v___x_2161_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespaceCore___boxed(lean_object* v_m_2162_, lean_object* v_inst_2163_, lean_object* v_inst_2164_, lean_object* v_inst_2165_, lean_object* v_inst_2166_, lean_object* v_id_2167_, lean_object* v_allowEmpty_2168_){
_start:
{
uint8_t v_allowEmpty_boxed_2169_; lean_object* v_res_2170_; 
v_allowEmpty_boxed_2169_ = lean_unbox(v_allowEmpty_2168_);
v_res_2170_ = l_Lean_resolveNamespaceCore(v_m_2162_, v_inst_2163_, v_inst_2164_, v_inst_2165_, v_inst_2166_, v_id_2167_, v_allowEmpty_boxed_2169_);
return v_res_2170_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespace___redArg___lam__0(lean_object* v_x_2171_){
_start:
{
if (lean_obj_tag(v_x_2171_) == 0)
{
lean_object* v_ns_2172_; lean_object* v___x_2174_; uint8_t v_isShared_2175_; uint8_t v_isSharedCheck_2179_; 
v_ns_2172_ = lean_ctor_get(v_x_2171_, 0);
v_isSharedCheck_2179_ = !lean_is_exclusive(v_x_2171_);
if (v_isSharedCheck_2179_ == 0)
{
v___x_2174_ = v_x_2171_;
v_isShared_2175_ = v_isSharedCheck_2179_;
goto v_resetjp_2173_;
}
else
{
lean_inc(v_ns_2172_);
lean_dec(v_x_2171_);
v___x_2174_ = lean_box(0);
v_isShared_2175_ = v_isSharedCheck_2179_;
goto v_resetjp_2173_;
}
v_resetjp_2173_:
{
lean_object* v___x_2177_; 
if (v_isShared_2175_ == 0)
{
lean_ctor_set_tag(v___x_2174_, 1);
v___x_2177_ = v___x_2174_;
goto v_reusejp_2176_;
}
else
{
lean_object* v_reuseFailAlloc_2178_; 
v_reuseFailAlloc_2178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2178_, 0, v_ns_2172_);
v___x_2177_ = v_reuseFailAlloc_2178_;
goto v_reusejp_2176_;
}
v_reusejp_2176_:
{
return v___x_2177_;
}
}
}
else
{
lean_object* v___x_2180_; 
lean_dec_ref(v_x_2171_);
v___x_2180_ = lean_box(0);
return v___x_2180_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespace___redArg___lam__1(lean_object* v_x_2181_, lean_object* v_withRef_2182_, lean_object* v___x_2183_, lean_object* v_oldRef_2184_){
_start:
{
lean_object* v_ref_2185_; lean_object* v___x_2186_; 
v_ref_2185_ = l_Lean_replaceRef(v_x_2181_, v_oldRef_2184_);
v___x_2186_ = lean_apply_3(v_withRef_2182_, lean_box(0), v_ref_2185_, v___x_2183_);
return v___x_2186_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespace___redArg___lam__1___boxed(lean_object* v_x_2187_, lean_object* v_withRef_2188_, lean_object* v___x_2189_, lean_object* v_oldRef_2190_){
_start:
{
lean_object* v_res_2191_; 
v_res_2191_ = l_Lean_resolveNamespace___redArg___lam__1(v_x_2187_, v_withRef_2188_, v___x_2189_, v_oldRef_2190_);
lean_dec(v_oldRef_2190_);
lean_dec(v_x_2187_);
return v_res_2191_;
}
}
static lean_object* _init_l_Lean_resolveNamespace___redArg___closed__4(void){
_start:
{
lean_object* v___x_2198_; lean_object* v___x_2199_; 
v___x_2198_ = ((lean_object*)(l_Lean_resolveNamespace___redArg___closed__3));
v___x_2199_ = l_Lean_MessageData_ofFormat(v___x_2198_);
return v___x_2199_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespace___redArg(lean_object* v_inst_2200_, lean_object* v_inst_2201_, lean_object* v_inst_2202_, lean_object* v_inst_2203_, lean_object* v_x_2204_){
_start:
{
if (lean_obj_tag(v_x_2204_) == 3)
{
lean_object* v_val_2205_; lean_object* v_preresolved_2206_; lean_object* v___f_2207_; lean_object* v___x_2208_; lean_object* v_pre_2209_; uint8_t v___x_2210_; 
v_val_2205_ = lean_ctor_get(v_x_2204_, 2);
v_preresolved_2206_ = lean_ctor_get(v_x_2204_, 3);
v___f_2207_ = ((lean_object*)(l_Lean_resolveNamespace___redArg___closed__0));
v___x_2208_ = ((lean_object*)(l_Lean_resolveNamespace___redArg___closed__1));
lean_inc(v_preresolved_2206_);
v_pre_2209_ = l_List_filterMapTR_go___redArg(v___f_2207_, v_preresolved_2206_, v___x_2208_);
v___x_2210_ = l_List_isEmpty___redArg(v_pre_2209_);
if (v___x_2210_ == 0)
{
lean_object* v_toApplicative_2211_; lean_object* v_toPure_2212_; lean_object* v___x_2213_; 
lean_dec_ref_known(v_x_2204_, 4);
lean_dec_ref(v_inst_2203_);
lean_dec_ref(v_inst_2202_);
lean_dec_ref(v_inst_2201_);
v_toApplicative_2211_ = lean_ctor_get(v_inst_2200_, 0);
lean_inc_ref(v_toApplicative_2211_);
lean_dec_ref(v_inst_2200_);
v_toPure_2212_ = lean_ctor_get(v_toApplicative_2211_, 1);
lean_inc(v_toPure_2212_);
lean_dec_ref(v_toApplicative_2211_);
v___x_2213_ = lean_apply_2(v_toPure_2212_, lean_box(0), v_pre_2209_);
return v___x_2213_;
}
else
{
lean_object* v_toMonadRef_2214_; lean_object* v_toBind_2215_; lean_object* v_getRef_2216_; lean_object* v_withRef_2217_; uint8_t v___x_2218_; lean_object* v___x_2219_; lean_object* v___f_2220_; lean_object* v___x_2221_; 
lean_dec(v_pre_2209_);
v_toMonadRef_2214_ = lean_ctor_get(v_inst_2203_, 1);
v_toBind_2215_ = lean_ctor_get(v_inst_2200_, 1);
lean_inc(v_toBind_2215_);
v_getRef_2216_ = lean_ctor_get(v_toMonadRef_2214_, 0);
lean_inc(v_getRef_2216_);
v_withRef_2217_ = lean_ctor_get(v_toMonadRef_2214_, 1);
lean_inc(v_withRef_2217_);
v___x_2218_ = 0;
lean_inc(v_val_2205_);
v___x_2219_ = l_Lean_resolveNamespaceCore___redArg(v_inst_2200_, v_inst_2201_, v_inst_2202_, v_inst_2203_, v_val_2205_, v___x_2218_);
v___f_2220_ = lean_alloc_closure((void*)(l_Lean_resolveNamespace___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_2220_, 0, v_x_2204_);
lean_closure_set(v___f_2220_, 1, v_withRef_2217_);
lean_closure_set(v___f_2220_, 2, v___x_2219_);
v___x_2221_ = lean_apply_4(v_toBind_2215_, lean_box(0), lean_box(0), v_getRef_2216_, v___f_2220_);
return v___x_2221_;
}
}
else
{
lean_object* v___x_2222_; lean_object* v___x_2223_; 
lean_dec_ref(v_inst_2202_);
lean_dec_ref(v_inst_2201_);
v___x_2222_ = lean_obj_once(&l_Lean_resolveNamespace___redArg___closed__4, &l_Lean_resolveNamespace___redArg___closed__4_once, _init_l_Lean_resolveNamespace___redArg___closed__4);
v___x_2223_ = l_Lean_throwErrorAt___redArg(v_inst_2200_, v_inst_2203_, v_x_2204_, v___x_2222_);
return v___x_2223_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveNamespace(lean_object* v_m_2224_, lean_object* v_inst_2225_, lean_object* v_inst_2226_, lean_object* v_inst_2227_, lean_object* v_inst_2228_, lean_object* v_x_2229_){
_start:
{
lean_object* v___x_2230_; 
v___x_2230_ = l_Lean_resolveNamespace___redArg(v_inst_2225_, v_inst_2226_, v_inst_2227_, v_inst_2228_, v_x_2229_);
return v___x_2230_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveUniqueNamespace___redArg___lam__0(lean_object* v_id_2233_, lean_object* v___f_2234_, lean_object* v_inst_2235_, lean_object* v_inst_2236_, lean_object* v_toPure_2237_, lean_object* v_____do__lift_2238_){
_start:
{
if (lean_obj_tag(v_____do__lift_2238_) == 1)
{
lean_object* v_tail_2254_; 
v_tail_2254_ = lean_ctor_get(v_____do__lift_2238_, 1);
if (lean_obj_tag(v_tail_2254_) == 0)
{
lean_object* v_head_2255_; lean_object* v___x_2256_; 
lean_dec_ref(v_inst_2236_);
lean_dec_ref(v_inst_2235_);
lean_dec_ref(v___f_2234_);
v_head_2255_ = lean_ctor_get(v_____do__lift_2238_, 0);
lean_inc(v_head_2255_);
lean_dec_ref_known(v_____do__lift_2238_, 2);
v___x_2256_ = lean_apply_2(v_toPure_2237_, lean_box(0), v_head_2255_);
return v___x_2256_;
}
else
{
lean_dec(v_toPure_2237_);
goto v___jp_2239_;
}
}
else
{
lean_dec(v_toPure_2237_);
goto v___jp_2239_;
}
v___jp_2239_:
{
lean_object* v___x_2240_; lean_object* v___x_2241_; uint8_t v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; 
v___x_2240_ = ((lean_object*)(l_Lean_resolveUniqueNamespace___redArg___lam__0___closed__0));
v___x_2241_ = l_Lean_TSyntax_getId(v_id_2233_);
v___x_2242_ = 1;
v___x_2243_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2241_, v___x_2242_);
v___x_2244_ = lean_string_append(v___x_2240_, v___x_2243_);
lean_dec_ref(v___x_2243_);
v___x_2245_ = ((lean_object*)(l_Lean_resolveUniqueNamespace___redArg___lam__0___closed__1));
v___x_2246_ = lean_string_append(v___x_2244_, v___x_2245_);
v___x_2247_ = l_List_toString___redArg(v___f_2234_, v_____do__lift_2238_);
v___x_2248_ = lean_string_append(v___x_2246_, v___x_2247_);
lean_dec_ref(v___x_2247_);
v___x_2249_ = ((lean_object*)(l_Lean_resolveNamespaceCore___redArg___lam__1___closed__1));
v___x_2250_ = lean_string_append(v___x_2248_, v___x_2249_);
v___x_2251_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2251_, 0, v___x_2250_);
v___x_2252_ = l_Lean_MessageData_ofFormat(v___x_2251_);
v___x_2253_ = l_Lean_throwError___redArg(v_inst_2235_, v_inst_2236_, v___x_2252_);
return v___x_2253_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveUniqueNamespace___redArg___lam__0___boxed(lean_object* v_id_2257_, lean_object* v___f_2258_, lean_object* v_inst_2259_, lean_object* v_inst_2260_, lean_object* v_toPure_2261_, lean_object* v_____do__lift_2262_){
_start:
{
lean_object* v_res_2263_; 
v_res_2263_ = l_Lean_resolveUniqueNamespace___redArg___lam__0(v_id_2257_, v___f_2258_, v_inst_2259_, v_inst_2260_, v_toPure_2261_, v_____do__lift_2262_);
lean_dec(v_id_2257_);
return v_res_2263_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveUniqueNamespace___redArg(lean_object* v_inst_2265_, lean_object* v_inst_2266_, lean_object* v_inst_2267_, lean_object* v_inst_2268_, lean_object* v_id_2269_){
_start:
{
lean_object* v_toApplicative_2270_; lean_object* v_toBind_2271_; lean_object* v_toPure_2272_; lean_object* v___f_2273_; lean_object* v___x_2274_; lean_object* v___f_2275_; lean_object* v___x_2276_; 
v_toApplicative_2270_ = lean_ctor_get(v_inst_2265_, 0);
v_toBind_2271_ = lean_ctor_get(v_inst_2265_, 1);
lean_inc(v_toBind_2271_);
v_toPure_2272_ = lean_ctor_get(v_toApplicative_2270_, 1);
lean_inc(v_toPure_2272_);
v___f_2273_ = ((lean_object*)(l_Lean_resolveUniqueNamespace___redArg___closed__0));
lean_inc(v_id_2269_);
lean_inc_ref(v_inst_2268_);
lean_inc_ref(v_inst_2265_);
v___x_2274_ = l_Lean_resolveNamespace___redArg(v_inst_2265_, v_inst_2266_, v_inst_2267_, v_inst_2268_, v_id_2269_);
v___f_2275_ = lean_alloc_closure((void*)(l_Lean_resolveUniqueNamespace___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_2275_, 0, v_id_2269_);
lean_closure_set(v___f_2275_, 1, v___f_2273_);
lean_closure_set(v___f_2275_, 2, v_inst_2265_);
lean_closure_set(v___f_2275_, 3, v_inst_2268_);
lean_closure_set(v___f_2275_, 4, v_toPure_2272_);
v___x_2276_ = lean_apply_4(v_toBind_2271_, lean_box(0), lean_box(0), v___x_2274_, v___f_2275_);
return v___x_2276_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveUniqueNamespace(lean_object* v_m_2277_, lean_object* v_inst_2278_, lean_object* v_inst_2279_, lean_object* v_inst_2280_, lean_object* v_inst_2281_, lean_object* v_id_2282_){
_start:
{
lean_object* v___x_2283_; 
v___x_2283_ = l_Lean_resolveUniqueNamespace___redArg(v_inst_2278_, v_inst_2279_, v_inst_2280_, v_inst_2281_, v_id_2282_);
return v___x_2283_;
}
}
LEAN_EXPORT uint8_t l_Lean_filterFieldList___redArg___lam__0(lean_object* v_x_2284_){
_start:
{
lean_object* v_snd_2285_; uint8_t v___x_2286_; 
v_snd_2285_ = lean_ctor_get(v_x_2284_, 1);
v___x_2286_ = l_List_isEmpty___redArg(v_snd_2285_);
return v___x_2286_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg___lam__0___boxed(lean_object* v_x_2287_){
_start:
{
uint8_t v_res_2288_; lean_object* v_r_2289_; 
v_res_2288_ = l_Lean_filterFieldList___redArg___lam__0(v_x_2287_);
lean_dec_ref(v_x_2287_);
v_r_2289_ = lean_box(v_res_2288_);
return v_r_2289_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg___lam__1(lean_object* v_x_2290_){
_start:
{
lean_object* v_fst_2291_; 
v_fst_2291_ = lean_ctor_get(v_x_2290_, 0);
lean_inc(v_fst_2291_);
return v_fst_2291_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg___lam__1___boxed(lean_object* v_x_2292_){
_start:
{
lean_object* v_res_2293_; 
v_res_2293_ = l_Lean_filterFieldList___redArg___lam__1(v_x_2292_);
lean_dec_ref(v_x_2292_);
return v_res_2293_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg___lam__2(lean_object* v___f_2294_, lean_object* v_cs_2295_, lean_object* v_toPure_2296_, lean_object* v_____r_2297_){
_start:
{
lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; 
v___x_2298_ = lean_box(0);
v___x_2299_ = l_List_mapTR_loop___redArg(v___f_2294_, v_cs_2295_, v___x_2298_);
v___x_2300_ = lean_apply_2(v_toPure_2296_, lean_box(0), v___x_2299_);
return v___x_2300_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg___lam__3(lean_object* v___f_2301_, lean_object* v_____r_2302_){
_start:
{
lean_object* v___x_2303_; 
v___x_2303_ = lean_apply_1(v___f_2301_, v_____r_2302_);
return v___x_2303_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg___lam__4(lean_object* v_inst_2304_, lean_object* v_inst_2305_, lean_object* v_inst_2306_, lean_object* v_n_2307_, lean_object* v_toBind_2308_, lean_object* v___f_2309_, lean_object* v_____do__lift_2310_){
_start:
{
lean_object* v___x_2311_; lean_object* v___x_2312_; 
v___x_2311_ = l_Lean_throwUnknownConstantAt___redArg(v_inst_2304_, v_inst_2305_, v_inst_2306_, v_____do__lift_2310_, v_n_2307_);
v___x_2312_ = lean_apply_4(v_toBind_2308_, lean_box(0), lean_box(0), v___x_2311_, v___f_2309_);
return v___x_2312_;
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList___redArg(lean_object* v_inst_2315_, lean_object* v_inst_2316_, lean_object* v_inst_2317_, lean_object* v_n_2318_, lean_object* v_cs_2319_){
_start:
{
lean_object* v_toApplicative_2320_; lean_object* v_toBind_2321_; lean_object* v_toPure_2322_; lean_object* v___f_2323_; lean_object* v___f_2324_; lean_object* v___x_2325_; lean_object* v_cs_2326_; lean_object* v___f_2327_; uint8_t v___x_2328_; 
v_toApplicative_2320_ = lean_ctor_get(v_inst_2315_, 0);
v_toBind_2321_ = lean_ctor_get(v_inst_2315_, 1);
lean_inc(v_toBind_2321_);
v_toPure_2322_ = lean_ctor_get(v_toApplicative_2320_, 1);
v___f_2323_ = ((lean_object*)(l_Lean_filterFieldList___redArg___closed__0));
v___f_2324_ = ((lean_object*)(l_Lean_filterFieldList___redArg___closed__1));
v___x_2325_ = lean_box(0);
v_cs_2326_ = l_List_filterTR_loop___redArg(v___f_2323_, v_cs_2319_, v___x_2325_);
lean_inc(v_toPure_2322_);
lean_inc(v_cs_2326_);
v___f_2327_ = lean_alloc_closure((void*)(l_Lean_filterFieldList___redArg___lam__2), 4, 3);
lean_closure_set(v___f_2327_, 0, v___f_2324_);
lean_closure_set(v___f_2327_, 1, v_cs_2326_);
lean_closure_set(v___f_2327_, 2, v_toPure_2322_);
v___x_2328_ = l_List_isEmpty___redArg(v_cs_2326_);
if (v___x_2328_ == 0)
{
lean_object* v___x_2329_; lean_object* v___x_2330_; 
lean_inc(v_toPure_2322_);
lean_dec_ref(v___f_2327_);
lean_dec(v_toBind_2321_);
lean_dec(v_n_2318_);
lean_dec_ref(v_inst_2317_);
lean_dec_ref(v_inst_2316_);
lean_dec_ref(v_inst_2315_);
v___x_2329_ = lean_box(0);
v___x_2330_ = l_Lean_filterFieldList___redArg___lam__2(v___f_2324_, v_cs_2326_, v_toPure_2322_, v___x_2329_);
return v___x_2330_;
}
else
{
lean_object* v_toMonadRef_2331_; lean_object* v_getRef_2332_; lean_object* v___f_2333_; lean_object* v___f_2334_; lean_object* v___x_2335_; 
lean_dec(v_cs_2326_);
v_toMonadRef_2331_ = lean_ctor_get(v_inst_2317_, 1);
v_getRef_2332_ = lean_ctor_get(v_toMonadRef_2331_, 0);
lean_inc(v_getRef_2332_);
v___f_2333_ = lean_alloc_closure((void*)(l_Lean_filterFieldList___redArg___lam__3), 2, 1);
lean_closure_set(v___f_2333_, 0, v___f_2327_);
lean_inc(v_toBind_2321_);
v___f_2334_ = lean_alloc_closure((void*)(l_Lean_filterFieldList___redArg___lam__4), 7, 6);
lean_closure_set(v___f_2334_, 0, v_inst_2315_);
lean_closure_set(v___f_2334_, 1, v_inst_2316_);
lean_closure_set(v___f_2334_, 2, v_inst_2317_);
lean_closure_set(v___f_2334_, 3, v_n_2318_);
lean_closure_set(v___f_2334_, 4, v_toBind_2321_);
lean_closure_set(v___f_2334_, 5, v___f_2333_);
v___x_2335_ = lean_apply_4(v_toBind_2321_, lean_box(0), lean_box(0), v_getRef_2332_, v___f_2334_);
return v___x_2335_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_filterFieldList(lean_object* v_m_2336_, lean_object* v_inst_2337_, lean_object* v_inst_2338_, lean_object* v_inst_2339_, lean_object* v_n_2340_, lean_object* v_cs_2341_){
_start:
{
lean_object* v___x_2342_; 
v___x_2342_ = l_Lean_filterFieldList___redArg(v_inst_2337_, v_inst_2338_, v_inst_2339_, v_n_2340_, v_cs_2341_);
return v___x_2342_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___redArg___lam__0(lean_object* v_inst_2343_, lean_object* v_inst_2344_, lean_object* v_inst_2345_, lean_object* v_n_2346_, lean_object* v_cs_2347_){
_start:
{
lean_object* v___x_2348_; 
v___x_2348_ = l_Lean_filterFieldList___redArg(v_inst_2343_, v_inst_2344_, v_inst_2345_, v_n_2346_, v_cs_2347_);
return v___x_2348_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___redArg(lean_object* v_inst_2349_, lean_object* v_inst_2350_, lean_object* v_inst_2351_, lean_object* v_inst_2352_, lean_object* v_inst_2353_, lean_object* v_inst_2354_, lean_object* v_inst_2355_, lean_object* v_n_2356_){
_start:
{
lean_object* v_toBind_2357_; lean_object* v___f_2358_; uint8_t v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; 
v_toBind_2357_ = lean_ctor_get(v_inst_2349_, 1);
lean_inc(v_toBind_2357_);
lean_inc(v_n_2356_);
lean_inc_ref(v_inst_2351_);
lean_inc_ref(v_inst_2349_);
v___f_2358_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___redArg___lam__0), 5, 4);
lean_closure_set(v___f_2358_, 0, v_inst_2349_);
lean_closure_set(v___f_2358_, 1, v_inst_2351_);
lean_closure_set(v___f_2358_, 2, v_inst_2355_);
lean_closure_set(v___f_2358_, 3, v_n_2356_);
v___x_2359_ = 1;
v___x_2360_ = l_Lean_resolveGlobalName___redArg(v_inst_2349_, v_inst_2350_, v_inst_2351_, v_inst_2352_, v_inst_2353_, v_inst_2354_, v_n_2356_, v___x_2359_);
v___x_2361_ = lean_apply_4(v_toBind_2357_, lean_box(0), lean_box(0), v___x_2360_, v___f_2358_);
return v___x_2361_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore(lean_object* v_m_2362_, lean_object* v_inst_2363_, lean_object* v_inst_2364_, lean_object* v_inst_2365_, lean_object* v_inst_2366_, lean_object* v_inst_2367_, lean_object* v_inst_2368_, lean_object* v_inst_2369_, lean_object* v_n_2370_){
_start:
{
lean_object* v___x_2371_; 
v___x_2371_ = l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___redArg(v_inst_2363_, v_inst_2364_, v_inst_2365_, v_inst_2366_, v_inst_2367_, v_inst_2368_, v_inst_2369_, v_n_2370_);
return v___x_2371_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNoOverload___redArg___lam__0(lean_object* v_declName_2372_){
_start:
{
lean_object* v___x_2373_; lean_object* v___x_2374_; 
v___x_2373_ = lean_box(0);
v___x_2374_ = l_Lean_mkConst(v_declName_2372_, v___x_2373_);
return v___x_2374_;
}
}
static lean_object* _init_l_Lean_ensureNoOverload___redArg___closed__2(void){
_start:
{
lean_object* v___x_2377_; lean_object* v___x_2378_; 
v___x_2377_ = ((lean_object*)(l_Lean_ensureNoOverload___redArg___closed__1));
v___x_2378_ = l_Lean_stringToMessageData(v___x_2377_);
return v___x_2378_;
}
}
static lean_object* _init_l_Lean_ensureNoOverload___redArg___closed__4(void){
_start:
{
lean_object* v___x_2380_; lean_object* v___x_2381_; 
v___x_2380_ = ((lean_object*)(l_Lean_ensureNoOverload___redArg___closed__3));
v___x_2381_ = l_Lean_stringToMessageData(v___x_2380_);
return v___x_2381_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNoOverload___redArg(lean_object* v_inst_2383_, lean_object* v_inst_2384_, lean_object* v_n_2385_, lean_object* v_cs_2386_){
_start:
{
lean_object* v_toApplicative_2387_; lean_object* v_toPure_2388_; lean_object* v___f_2389_; 
v_toApplicative_2387_ = lean_ctor_get(v_inst_2383_, 0);
v_toPure_2388_ = lean_ctor_get(v_toApplicative_2387_, 1);
v___f_2389_ = ((lean_object*)(l_Lean_ensureNoOverload___redArg___closed__0));
if (lean_obj_tag(v_cs_2386_) == 1)
{
lean_object* v_tail_2403_; 
v_tail_2403_ = lean_ctor_get(v_cs_2386_, 1);
if (lean_obj_tag(v_tail_2403_) == 0)
{
lean_object* v_head_2404_; lean_object* v___x_2405_; 
lean_inc(v_toPure_2388_);
lean_dec(v_n_2385_);
lean_dec_ref(v_inst_2384_);
lean_dec_ref(v_inst_2383_);
v_head_2404_ = lean_ctor_get(v_cs_2386_, 0);
lean_inc(v_head_2404_);
lean_dec_ref_known(v_cs_2386_, 2);
v___x_2405_ = lean_apply_2(v_toPure_2388_, lean_box(0), v_head_2404_);
return v___x_2405_;
}
else
{
goto v___jp_2390_;
}
}
else
{
goto v___jp_2390_;
}
v___jp_2390_:
{
lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; 
v___x_2391_ = lean_obj_once(&l_Lean_ensureNoOverload___redArg___closed__2, &l_Lean_ensureNoOverload___redArg___closed__2_once, _init_l_Lean_ensureNoOverload___redArg___closed__2);
v___x_2392_ = l_Lean_MessageData_ofName(v_n_2385_);
v___x_2393_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2393_, 0, v___x_2391_);
lean_ctor_set(v___x_2393_, 1, v___x_2392_);
v___x_2394_ = lean_obj_once(&l_Lean_ensureNoOverload___redArg___closed__4, &l_Lean_ensureNoOverload___redArg___closed__4_once, _init_l_Lean_ensureNoOverload___redArg___closed__4);
v___x_2395_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2395_, 0, v___x_2393_);
lean_ctor_set(v___x_2395_, 1, v___x_2394_);
v___x_2396_ = lean_box(0);
v___x_2397_ = l_List_mapTR_loop___redArg(v___f_2389_, v_cs_2386_, v___x_2396_);
v___x_2398_ = ((lean_object*)(l_Lean_ensureNoOverload___redArg___closed__5));
v___x_2399_ = l_List_mapTR_loop___redArg(v___x_2398_, v___x_2397_, v___x_2396_);
v___x_2400_ = l_Lean_MessageData_ofList(v___x_2399_);
v___x_2401_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2401_, 0, v___x_2395_);
lean_ctor_set(v___x_2401_, 1, v___x_2400_);
v___x_2402_ = l_Lean_throwError___redArg(v_inst_2383_, v_inst_2384_, v___x_2401_);
return v___x_2402_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNoOverload(lean_object* v_m_2406_, lean_object* v_inst_2407_, lean_object* v_inst_2408_, lean_object* v_n_2409_, lean_object* v_cs_2410_){
_start:
{
lean_object* v___x_2411_; 
v___x_2411_ = l_Lean_ensureNoOverload___redArg(v_inst_2407_, v_inst_2408_, v_n_2409_, v_cs_2410_);
return v___x_2411_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverloadCore___redArg___lam__0(lean_object* v_inst_2412_, lean_object* v_inst_2413_, lean_object* v_n_2414_, lean_object* v_____do__lift_2415_){
_start:
{
lean_object* v___x_2416_; 
v___x_2416_ = l_Lean_ensureNoOverload___redArg(v_inst_2412_, v_inst_2413_, v_n_2414_, v_____do__lift_2415_);
return v___x_2416_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverloadCore___redArg(lean_object* v_inst_2417_, lean_object* v_inst_2418_, lean_object* v_inst_2419_, lean_object* v_inst_2420_, lean_object* v_inst_2421_, lean_object* v_inst_2422_, lean_object* v_inst_2423_, lean_object* v_n_2424_){
_start:
{
lean_object* v_toBind_2425_; lean_object* v___f_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; 
v_toBind_2425_ = lean_ctor_get(v_inst_2417_, 1);
lean_inc(v_toBind_2425_);
lean_inc(v_n_2424_);
lean_inc_ref(v_inst_2423_);
lean_inc_ref(v_inst_2417_);
v___f_2426_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalConstNoOverloadCore___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2426_, 0, v_inst_2417_);
lean_closure_set(v___f_2426_, 1, v_inst_2423_);
lean_closure_set(v___f_2426_, 2, v_n_2424_);
v___x_2427_ = l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore___redArg(v_inst_2417_, v_inst_2418_, v_inst_2419_, v_inst_2420_, v_inst_2421_, v_inst_2422_, v_inst_2423_, v_n_2424_);
v___x_2428_ = lean_apply_4(v_toBind_2425_, lean_box(0), lean_box(0), v___x_2427_, v___f_2426_);
return v___x_2428_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverloadCore(lean_object* v_m_2429_, lean_object* v_inst_2430_, lean_object* v_inst_2431_, lean_object* v_inst_2432_, lean_object* v_inst_2433_, lean_object* v_inst_2434_, lean_object* v_inst_2435_, lean_object* v_inst_2436_, lean_object* v_n_2437_){
_start:
{
lean_object* v___x_2438_; 
v___x_2438_ = l_Lean_resolveGlobalConstNoOverloadCore___redArg(v_inst_2430_, v_inst_2431_, v_inst_2432_, v_inst_2433_, v_inst_2434_, v_inst_2435_, v_inst_2436_, v_n_2437_);
return v___x_2438_;
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___redArg___lam__0(lean_object* v_x_2439_){
_start:
{
if (lean_obj_tag(v_x_2439_) == 1)
{
lean_object* v_fields_2440_; 
v_fields_2440_ = lean_ctor_get(v_x_2439_, 1);
if (lean_obj_tag(v_fields_2440_) == 0)
{
lean_object* v_n_2441_; lean_object* v___x_2442_; 
v_n_2441_ = lean_ctor_get(v_x_2439_, 0);
lean_inc(v_n_2441_);
v___x_2442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2442_, 0, v_n_2441_);
return v___x_2442_;
}
else
{
lean_object* v___x_2443_; 
v___x_2443_ = lean_box(0);
return v___x_2443_;
}
}
else
{
lean_object* v___x_2444_; 
v___x_2444_ = lean_box(0);
return v___x_2444_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___redArg___lam__0___boxed(lean_object* v_x_2445_){
_start:
{
lean_object* v_res_2446_; 
v_res_2446_ = l_Lean_preprocessSyntaxAndResolve___redArg___lam__0(v_x_2445_);
lean_dec_ref(v_x_2445_);
return v_res_2446_;
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___redArg___lam__1(lean_object* v_stx_2447_, lean_object* v_withRef_2448_, lean_object* v___x_2449_, lean_object* v_oldRef_2450_){
_start:
{
lean_object* v_ref_2451_; lean_object* v___x_2452_; 
v_ref_2451_ = l_Lean_replaceRef(v_stx_2447_, v_oldRef_2450_);
v___x_2452_ = lean_apply_3(v_withRef_2448_, lean_box(0), v_ref_2451_, v___x_2449_);
return v___x_2452_;
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___redArg___lam__1___boxed(lean_object* v_stx_2453_, lean_object* v_withRef_2454_, lean_object* v___x_2455_, lean_object* v_oldRef_2456_){
_start:
{
lean_object* v_res_2457_; 
v_res_2457_ = l_Lean_preprocessSyntaxAndResolve___redArg___lam__1(v_stx_2453_, v_withRef_2454_, v___x_2455_, v_oldRef_2456_);
lean_dec(v_oldRef_2456_);
lean_dec(v_stx_2453_);
return v_res_2457_;
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve___redArg(lean_object* v_inst_2459_, lean_object* v_inst_2460_, lean_object* v_stx_2461_, lean_object* v_k_2462_){
_start:
{
if (lean_obj_tag(v_stx_2461_) == 3)
{
lean_object* v_val_2463_; lean_object* v_preresolved_2464_; lean_object* v___f_2465_; lean_object* v___x_2466_; lean_object* v_pre_2467_; uint8_t v___x_2468_; 
v_val_2463_ = lean_ctor_get(v_stx_2461_, 2);
v_preresolved_2464_ = lean_ctor_get(v_stx_2461_, 3);
v___f_2465_ = ((lean_object*)(l_Lean_preprocessSyntaxAndResolve___redArg___closed__0));
v___x_2466_ = ((lean_object*)(l_Lean_resolveNamespace___redArg___closed__1));
lean_inc(v_preresolved_2464_);
v_pre_2467_ = l_List_filterMapTR_go___redArg(v___f_2465_, v_preresolved_2464_, v___x_2466_);
v___x_2468_ = l_List_isEmpty___redArg(v_pre_2467_);
if (v___x_2468_ == 0)
{
lean_object* v_toApplicative_2469_; lean_object* v_toPure_2470_; lean_object* v___x_2471_; 
lean_dec_ref_known(v_stx_2461_, 4);
lean_dec(v_k_2462_);
lean_dec_ref(v_inst_2460_);
v_toApplicative_2469_ = lean_ctor_get(v_inst_2459_, 0);
lean_inc_ref(v_toApplicative_2469_);
lean_dec_ref(v_inst_2459_);
v_toPure_2470_ = lean_ctor_get(v_toApplicative_2469_, 1);
lean_inc(v_toPure_2470_);
lean_dec_ref(v_toApplicative_2469_);
v___x_2471_ = lean_apply_2(v_toPure_2470_, lean_box(0), v_pre_2467_);
return v___x_2471_;
}
else
{
lean_object* v_toMonadRef_2472_; lean_object* v_toBind_2473_; lean_object* v_getRef_2474_; lean_object* v_withRef_2475_; lean_object* v___x_2476_; lean_object* v___f_2477_; lean_object* v___x_2478_; 
lean_dec(v_pre_2467_);
v_toMonadRef_2472_ = lean_ctor_get(v_inst_2460_, 1);
lean_inc_ref(v_toMonadRef_2472_);
lean_dec_ref(v_inst_2460_);
v_toBind_2473_ = lean_ctor_get(v_inst_2459_, 1);
lean_inc(v_toBind_2473_);
lean_dec_ref(v_inst_2459_);
v_getRef_2474_ = lean_ctor_get(v_toMonadRef_2472_, 0);
lean_inc(v_getRef_2474_);
v_withRef_2475_ = lean_ctor_get(v_toMonadRef_2472_, 1);
lean_inc(v_withRef_2475_);
lean_dec_ref(v_toMonadRef_2472_);
lean_inc(v_val_2463_);
v___x_2476_ = lean_apply_1(v_k_2462_, v_val_2463_);
v___f_2477_ = lean_alloc_closure((void*)(l_Lean_preprocessSyntaxAndResolve___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_2477_, 0, v_stx_2461_);
lean_closure_set(v___f_2477_, 1, v_withRef_2475_);
lean_closure_set(v___f_2477_, 2, v___x_2476_);
v___x_2478_ = lean_apply_4(v_toBind_2473_, lean_box(0), lean_box(0), v_getRef_2474_, v___f_2477_);
return v___x_2478_;
}
}
else
{
lean_object* v___x_2479_; lean_object* v___x_2480_; 
lean_dec(v_k_2462_);
v___x_2479_ = lean_obj_once(&l_Lean_resolveNamespace___redArg___closed__4, &l_Lean_resolveNamespace___redArg___closed__4_once, _init_l_Lean_resolveNamespace___redArg___closed__4);
v___x_2480_ = l_Lean_throwErrorAt___redArg(v_inst_2459_, v_inst_2460_, v_stx_2461_, v___x_2479_);
return v___x_2480_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_preprocessSyntaxAndResolve(lean_object* v_m_2481_, lean_object* v_inst_2482_, lean_object* v_inst_2483_, lean_object* v_stx_2484_, lean_object* v_k_2485_){
_start:
{
lean_object* v___x_2486_; 
v___x_2486_ = l_Lean_preprocessSyntaxAndResolve___redArg(v_inst_2482_, v_inst_2483_, v_stx_2484_, v_k_2485_);
return v___x_2486_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst___redArg(lean_object* v_inst_2487_, lean_object* v_inst_2488_, lean_object* v_inst_2489_, lean_object* v_inst_2490_, lean_object* v_inst_2491_, lean_object* v_inst_2492_, lean_object* v_inst_2493_, lean_object* v_stx_2494_){
_start:
{
lean_object* v___x_2495_; lean_object* v___x_2496_; 
lean_inc_ref(v_inst_2493_);
lean_inc_ref(v_inst_2487_);
v___x_2495_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_resolveGlobalConstCore), 9, 8);
lean_closure_set(v___x_2495_, 0, lean_box(0));
lean_closure_set(v___x_2495_, 1, v_inst_2487_);
lean_closure_set(v___x_2495_, 2, v_inst_2488_);
lean_closure_set(v___x_2495_, 3, v_inst_2489_);
lean_closure_set(v___x_2495_, 4, v_inst_2490_);
lean_closure_set(v___x_2495_, 5, v_inst_2491_);
lean_closure_set(v___x_2495_, 6, v_inst_2492_);
lean_closure_set(v___x_2495_, 7, v_inst_2493_);
v___x_2496_ = l_Lean_preprocessSyntaxAndResolve___redArg(v_inst_2487_, v_inst_2493_, v_stx_2494_, v___x_2495_);
return v___x_2496_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConst(lean_object* v_m_2497_, lean_object* v_inst_2498_, lean_object* v_inst_2499_, lean_object* v_inst_2500_, lean_object* v_inst_2501_, lean_object* v_inst_2502_, lean_object* v_inst_2503_, lean_object* v_inst_2504_, lean_object* v_stx_2505_){
_start:
{
lean_object* v___x_2506_; 
v___x_2506_ = l_Lean_resolveGlobalConst___redArg(v_inst_2498_, v_inst_2499_, v_inst_2500_, v_inst_2501_, v_inst_2502_, v_inst_2503_, v_inst_2504_, v_stx_2505_);
return v___x_2506_;
}
}
static lean_object* _init_l_Lean_ensureNonAmbiguous___redArg___closed__1(void){
_start:
{
lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; 
v___x_2508_ = ((lean_object*)(l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__2));
v___x_2509_ = lean_unsigned_to_nat(11u);
v___x_2510_ = lean_unsigned_to_nat(429u);
v___x_2511_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___redArg___closed__0));
v___x_2512_ = ((lean_object*)(l_Lean_ResolveName_resolveNamespaceUsingScope_x3f___closed__0));
v___x_2513_ = l_mkPanicMessageWithDecl(v___x_2512_, v___x_2511_, v___x_2510_, v___x_2509_, v___x_2508_);
return v___x_2513_;
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNonAmbiguous___redArg(lean_object* v_inst_2517_, lean_object* v_inst_2518_, lean_object* v_id_2519_, lean_object* v_cs_2520_){
_start:
{
if (lean_obj_tag(v_cs_2520_) == 0)
{
lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; 
lean_dec(v_id_2519_);
lean_dec_ref(v_inst_2518_);
v___x_2521_ = lean_box(0);
v___x_2522_ = l_instInhabitedOfMonad___redArg(v_inst_2517_, v___x_2521_);
v___x_2523_ = lean_obj_once(&l_Lean_ensureNonAmbiguous___redArg___closed__1, &l_Lean_ensureNonAmbiguous___redArg___closed__1_once, _init_l_Lean_ensureNonAmbiguous___redArg___closed__1);
v___x_2524_ = l_panic___redArg(v___x_2522_, v___x_2523_);
lean_dec(v___x_2522_);
return v___x_2524_;
}
else
{
lean_object* v_tail_2525_; 
v_tail_2525_ = lean_ctor_get(v_cs_2520_, 1);
if (lean_obj_tag(v_tail_2525_) == 0)
{
lean_object* v_toApplicative_2526_; lean_object* v_toPure_2527_; lean_object* v_head_2528_; lean_object* v___x_2529_; 
v_toApplicative_2526_ = lean_ctor_get(v_inst_2517_, 0);
lean_inc_ref(v_toApplicative_2526_);
lean_dec(v_id_2519_);
lean_dec_ref(v_inst_2518_);
lean_dec_ref(v_inst_2517_);
v_toPure_2527_ = lean_ctor_get(v_toApplicative_2526_, 1);
lean_inc(v_toPure_2527_);
lean_dec_ref(v_toApplicative_2526_);
v_head_2528_ = lean_ctor_get(v_cs_2520_, 0);
lean_inc(v_head_2528_);
lean_dec_ref_known(v_cs_2520_, 2);
v___x_2529_ = lean_apply_2(v_toPure_2527_, lean_box(0), v_head_2528_);
return v___x_2529_;
}
else
{
lean_object* v___f_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; uint8_t v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; 
v___f_2530_ = ((lean_object*)(l_Lean_ensureNoOverload___redArg___closed__0));
v___x_2531_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___redArg___closed__2));
v___x_2532_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___redArg___closed__3));
v___x_2533_ = lean_box(0);
v___x_2534_ = 0;
lean_inc(v_id_2519_);
v___x_2535_ = l_Lean_Syntax_formatStx(v_id_2519_, v___x_2533_, v___x_2534_);
v___x_2536_ = l_Std_Format_defWidth;
v___x_2537_ = lean_unsigned_to_nat(0u);
v___x_2538_ = l_Std_Format_pretty(v___x_2535_, v___x_2536_, v___x_2537_, v___x_2537_);
v___x_2539_ = lean_string_append(v___x_2532_, v___x_2538_);
lean_dec_ref(v___x_2538_);
v___x_2540_ = ((lean_object*)(l_Lean_ensureNonAmbiguous___redArg___closed__4));
v___x_2541_ = lean_string_append(v___x_2539_, v___x_2540_);
v___x_2542_ = lean_box(0);
v___x_2543_ = l_List_mapTR_loop___redArg(v___f_2530_, v_cs_2520_, v___x_2542_);
v___x_2544_ = l_List_toString___redArg(v___x_2531_, v___x_2543_);
v___x_2545_ = lean_string_append(v___x_2541_, v___x_2544_);
lean_dec_ref(v___x_2544_);
v___x_2546_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2546_, 0, v___x_2545_);
v___x_2547_ = l_Lean_MessageData_ofFormat(v___x_2546_);
v___x_2548_ = l_Lean_throwErrorAt___redArg(v_inst_2517_, v_inst_2518_, v_id_2519_, v___x_2547_);
return v___x_2548_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ensureNonAmbiguous(lean_object* v_m_2549_, lean_object* v_inst_2550_, lean_object* v_inst_2551_, lean_object* v_id_2552_, lean_object* v_cs_2553_){
_start:
{
lean_object* v___x_2554_; 
v___x_2554_ = l_Lean_ensureNonAmbiguous___redArg(v_inst_2550_, v_inst_2551_, v_id_2552_, v_cs_2553_);
return v___x_2554_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverload___redArg___lam__0(lean_object* v_inst_2555_, lean_object* v_inst_2556_, lean_object* v_id_2557_, lean_object* v_____do__lift_2558_){
_start:
{
lean_object* v___x_2559_; 
v___x_2559_ = l_Lean_ensureNonAmbiguous___redArg(v_inst_2555_, v_inst_2556_, v_id_2557_, v_____do__lift_2558_);
return v___x_2559_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverload___redArg(lean_object* v_inst_2560_, lean_object* v_inst_2561_, lean_object* v_inst_2562_, lean_object* v_inst_2563_, lean_object* v_inst_2564_, lean_object* v_inst_2565_, lean_object* v_inst_2566_, lean_object* v_id_2567_){
_start:
{
lean_object* v_toBind_2568_; lean_object* v___f_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; 
v_toBind_2568_ = lean_ctor_get(v_inst_2560_, 1);
lean_inc(v_toBind_2568_);
lean_inc(v_id_2567_);
lean_inc_ref(v_inst_2566_);
lean_inc_ref(v_inst_2560_);
v___f_2569_ = lean_alloc_closure((void*)(l_Lean_resolveGlobalConstNoOverload___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2569_, 0, v_inst_2560_);
lean_closure_set(v___f_2569_, 1, v_inst_2566_);
lean_closure_set(v___f_2569_, 2, v_id_2567_);
v___x_2570_ = l_Lean_resolveGlobalConst___redArg(v_inst_2560_, v_inst_2561_, v_inst_2562_, v_inst_2563_, v_inst_2564_, v_inst_2565_, v_inst_2566_, v_id_2567_);
v___x_2571_ = lean_apply_4(v_toBind_2568_, lean_box(0), lean_box(0), v___x_2570_, v___f_2569_);
return v___x_2571_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveGlobalConstNoOverload(lean_object* v_m_2572_, lean_object* v_inst_2573_, lean_object* v_inst_2574_, lean_object* v_inst_2575_, lean_object* v_inst_2576_, lean_object* v_inst_2577_, lean_object* v_inst_2578_, lean_object* v_inst_2579_, lean_object* v_id_2580_){
_start:
{
lean_object* v___x_2581_; 
v___x_2581_ = l_Lean_resolveGlobalConstNoOverload___redArg(v_inst_2573_, v_inst_2574_, v_inst_2575_, v_inst_2576_, v_inst_2577_, v_inst_2578_, v_inst_2579_, v_id_2580_);
return v___x_2581_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__0(lean_object* v___f_2582_, lean_object* v___f_2583_, uint8_t v_globalDeclFoundNext_2584_, uint8_t v_globalDeclFound_2585_, lean_object* v_r_2586_){
_start:
{
lean_object* v___x_2587_; lean_object* v_r_2588_; uint8_t v___x_2589_; 
v___x_2587_ = lean_box(0);
v_r_2588_ = l_List_filterTR_loop___redArg(v___f_2582_, v_r_2586_, v___x_2587_);
v___x_2589_ = l_List_isEmpty___redArg(v_r_2588_);
lean_dec(v_r_2588_);
if (v___x_2589_ == 0)
{
lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; 
v___x_2590_ = lean_box(0);
v___x_2591_ = lean_box(v_globalDeclFoundNext_2584_);
v___x_2592_ = lean_apply_2(v___f_2583_, v___x_2590_, v___x_2591_);
return v___x_2592_;
}
else
{
lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; 
v___x_2593_ = lean_box(0);
v___x_2594_ = lean_box(v_globalDeclFound_2585_);
v___x_2595_ = lean_apply_2(v___f_2583_, v___x_2593_, v___x_2594_);
return v___x_2595_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__0___boxed(lean_object* v___f_2596_, lean_object* v___f_2597_, lean_object* v_globalDeclFoundNext_2598_, lean_object* v_globalDeclFound_2599_, lean_object* v_r_2600_){
_start:
{
uint8_t v_globalDeclFoundNext_boxed_2601_; uint8_t v_globalDeclFound_boxed_2602_; lean_object* v_res_2603_; 
v_globalDeclFoundNext_boxed_2601_ = lean_unbox(v_globalDeclFoundNext_2598_);
v_globalDeclFound_boxed_2602_ = lean_unbox(v_globalDeclFound_2599_);
v_res_2603_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__0(v___f_2596_, v___f_2597_, v_globalDeclFoundNext_boxed_2601_, v_globalDeclFound_boxed_2602_, v_r_2600_);
return v_res_2603_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__1___boxed(lean_object* v_str_2604_, lean_object* v_projs_2605_, lean_object* v_inst_2606_, lean_object* v_inst_2607_, lean_object* v_inst_2608_, lean_object* v_inst_2609_, lean_object* v_inst_2610_, lean_object* v_inst_2611_, lean_object* v_view_2612_, lean_object* v_findLocalDecl_x3f_2613_, lean_object* v_pre_2614_, lean_object* v_____r_2615_, lean_object* v_globalDeclFoundNext_2616_){
_start:
{
uint8_t v_globalDeclFoundNext_boxed_2617_; lean_object* v_res_2618_; 
v_globalDeclFoundNext_boxed_2617_ = lean_unbox(v_globalDeclFoundNext_2616_);
v_res_2618_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__1(v_str_2604_, v_projs_2605_, v_inst_2606_, v_inst_2607_, v_inst_2608_, v_inst_2609_, v_inst_2610_, v_inst_2611_, v_view_2612_, v_findLocalDecl_x3f_2613_, v_pre_2614_, v_____r_2615_, v_globalDeclFoundNext_boxed_2617_);
return v_res_2618_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg(lean_object* v_inst_2619_, lean_object* v_inst_2620_, lean_object* v_inst_2621_, lean_object* v_inst_2622_, lean_object* v_inst_2623_, lean_object* v_inst_2624_, lean_object* v_view_2625_, lean_object* v_findLocalDecl_x3f_2626_, lean_object* v_n_2627_, lean_object* v_projs_2628_, uint8_t v_globalDeclFound_2629_){
_start:
{
lean_object* v_toApplicative_2630_; lean_object* v_imported_2631_; lean_object* v_ctx_2632_; lean_object* v_scopes_2633_; lean_object* v_toBind_2634_; lean_object* v_toPure_2635_; lean_object* v___f_2636_; lean_object* v_givenNameView_2637_; uint8_t v___y_2639_; 
v_toApplicative_2630_ = lean_ctor_get(v_inst_2619_, 0);
v_imported_2631_ = lean_ctor_get(v_view_2625_, 1);
v_ctx_2632_ = lean_ctor_get(v_view_2625_, 2);
v_scopes_2633_ = lean_ctor_get(v_view_2625_, 3);
v_toBind_2634_ = lean_ctor_get(v_inst_2619_, 1);
v_toPure_2635_ = lean_ctor_get(v_toApplicative_2630_, 1);
v___f_2636_ = ((lean_object*)(l_Lean_filterFieldList___redArg___closed__0));
lean_inc(v_scopes_2633_);
lean_inc(v_ctx_2632_);
lean_inc(v_imported_2631_);
lean_inc(v_n_2627_);
v_givenNameView_2637_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_givenNameView_2637_, 0, v_n_2627_);
lean_ctor_set(v_givenNameView_2637_, 1, v_imported_2631_);
lean_ctor_set(v_givenNameView_2637_, 2, v_ctx_2632_);
lean_ctor_set(v_givenNameView_2637_, 3, v_scopes_2633_);
if (v_globalDeclFound_2629_ == 0)
{
v___y_2639_ = v_globalDeclFound_2629_;
goto v___jp_2638_;
}
else
{
uint8_t v___x_2675_; 
v___x_2675_ = l_List_isEmpty___redArg(v_projs_2628_);
if (v___x_2675_ == 0)
{
v___y_2639_ = v_globalDeclFound_2629_;
goto v___jp_2638_;
}
else
{
uint8_t v___x_2676_; 
v___x_2676_ = 0;
v___y_2639_ = v___x_2676_;
goto v___jp_2638_;
}
}
v___jp_2638_:
{
lean_object* v___x_2640_; lean_object* v___x_2641_; 
v___x_2640_ = lean_box(v___y_2639_);
lean_inc_ref(v_findLocalDecl_x3f_2626_);
lean_inc_ref(v_givenNameView_2637_);
v___x_2641_ = lean_apply_2(v_findLocalDecl_x3f_2626_, v_givenNameView_2637_, v___x_2640_);
if (lean_obj_tag(v___x_2641_) == 0)
{
if (lean_obj_tag(v_n_2627_) == 1)
{
lean_object* v_pre_2642_; lean_object* v_str_2643_; lean_object* v___f_2644_; 
v_pre_2642_ = lean_ctor_get(v_n_2627_, 0);
lean_inc_n(v_pre_2642_, 2);
v_str_2643_ = lean_ctor_get(v_n_2627_, 1);
lean_inc_ref_n(v_str_2643_, 2);
lean_dec_ref_known(v_n_2627_, 2);
lean_inc_ref(v_findLocalDecl_x3f_2626_);
lean_inc_ref(v_view_2625_);
lean_inc(v_inst_2624_);
lean_inc_ref(v_inst_2623_);
lean_inc(v_inst_2622_);
lean_inc_ref(v_inst_2621_);
lean_inc_ref(v_inst_2620_);
lean_inc_ref(v_inst_2619_);
lean_inc(v_projs_2628_);
v___f_2644_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__1___boxed), 13, 11);
lean_closure_set(v___f_2644_, 0, v_str_2643_);
lean_closure_set(v___f_2644_, 1, v_projs_2628_);
lean_closure_set(v___f_2644_, 2, v_inst_2619_);
lean_closure_set(v___f_2644_, 3, v_inst_2620_);
lean_closure_set(v___f_2644_, 4, v_inst_2621_);
lean_closure_set(v___f_2644_, 5, v_inst_2622_);
lean_closure_set(v___f_2644_, 6, v_inst_2623_);
lean_closure_set(v___f_2644_, 7, v_inst_2624_);
lean_closure_set(v___f_2644_, 8, v_view_2625_);
lean_closure_set(v___f_2644_, 9, v_findLocalDecl_x3f_2626_);
lean_closure_set(v___f_2644_, 10, v_pre_2642_);
if (v_globalDeclFound_2629_ == 0)
{
uint8_t v_globalDeclFoundNext_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___f_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; 
lean_inc(v_toBind_2634_);
lean_dec_ref(v_str_2643_);
lean_dec(v_pre_2642_);
lean_dec(v_projs_2628_);
lean_dec_ref(v_findLocalDecl_x3f_2626_);
lean_dec_ref(v_view_2625_);
v_globalDeclFoundNext_2645_ = 1;
v___x_2646_ = lean_box(v_globalDeclFoundNext_2645_);
v___x_2647_ = lean_box(v_globalDeclFound_2629_);
v___f_2648_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_2648_, 0, v___f_2636_);
lean_closure_set(v___f_2648_, 1, v___f_2644_);
lean_closure_set(v___f_2648_, 2, v___x_2646_);
lean_closure_set(v___f_2648_, 3, v___x_2647_);
v___x_2649_ = l_Lean_MacroScopesView_review(v_givenNameView_2637_);
v___x_2650_ = l_Lean_resolveGlobalName___redArg(v_inst_2619_, v_inst_2620_, v_inst_2621_, v_inst_2622_, v_inst_2623_, v_inst_2624_, v___x_2649_, v_globalDeclFound_2629_);
v___x_2651_ = lean_apply_4(v_toBind_2634_, lean_box(0), lean_box(0), v___x_2650_, v___f_2648_);
return v___x_2651_;
}
else
{
lean_object* v___x_2652_; lean_object* v___x_2653_; 
lean_dec_ref(v___f_2644_);
lean_dec_ref_known(v_givenNameView_2637_, 4);
v___x_2652_ = lean_box(0);
v___x_2653_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__1(v_str_2643_, v_projs_2628_, v_inst_2619_, v_inst_2620_, v_inst_2621_, v_inst_2622_, v_inst_2623_, v_inst_2624_, v_view_2625_, v_findLocalDecl_x3f_2626_, v_pre_2642_, v___x_2652_, v_globalDeclFound_2629_);
return v___x_2653_;
}
}
else
{
lean_object* v___x_2654_; lean_object* v___x_2655_; 
lean_inc(v_toPure_2635_);
lean_dec_ref_known(v_givenNameView_2637_, 4);
lean_dec(v_projs_2628_);
lean_dec(v_n_2627_);
lean_dec_ref(v_findLocalDecl_x3f_2626_);
lean_dec_ref(v_view_2625_);
lean_dec(v_inst_2624_);
lean_dec_ref(v_inst_2623_);
lean_dec(v_inst_2622_);
lean_dec_ref(v_inst_2621_);
lean_dec_ref(v_inst_2620_);
lean_dec_ref(v_inst_2619_);
v___x_2654_ = lean_box(0);
v___x_2655_ = lean_apply_2(v_toPure_2635_, lean_box(0), v___x_2654_);
return v___x_2655_;
}
}
else
{
lean_object* v___x_2657_; uint8_t v_isShared_2658_; uint8_t v_isSharedCheck_2672_; 
lean_inc(v_toPure_2635_);
lean_dec_ref_known(v_givenNameView_2637_, 4);
lean_dec(v_n_2627_);
lean_dec_ref(v_findLocalDecl_x3f_2626_);
lean_dec_ref(v_view_2625_);
lean_dec(v_inst_2624_);
lean_dec_ref(v_inst_2623_);
lean_dec(v_inst_2622_);
lean_dec_ref(v_inst_2621_);
lean_dec_ref(v_inst_2620_);
v_isSharedCheck_2672_ = !lean_is_exclusive(v_inst_2619_);
if (v_isSharedCheck_2672_ == 0)
{
lean_object* v_unused_2673_; lean_object* v_unused_2674_; 
v_unused_2673_ = lean_ctor_get(v_inst_2619_, 1);
lean_dec(v_unused_2673_);
v_unused_2674_ = lean_ctor_get(v_inst_2619_, 0);
lean_dec(v_unused_2674_);
v___x_2657_ = v_inst_2619_;
v_isShared_2658_ = v_isSharedCheck_2672_;
goto v_resetjp_2656_;
}
else
{
lean_dec(v_inst_2619_);
v___x_2657_ = lean_box(0);
v_isShared_2658_ = v_isSharedCheck_2672_;
goto v_resetjp_2656_;
}
v_resetjp_2656_:
{
lean_object* v_val_2659_; lean_object* v___x_2661_; uint8_t v_isShared_2662_; uint8_t v_isSharedCheck_2671_; 
v_val_2659_ = lean_ctor_get(v___x_2641_, 0);
v_isSharedCheck_2671_ = !lean_is_exclusive(v___x_2641_);
if (v_isSharedCheck_2671_ == 0)
{
v___x_2661_ = v___x_2641_;
v_isShared_2662_ = v_isSharedCheck_2671_;
goto v_resetjp_2660_;
}
else
{
lean_inc(v_val_2659_);
lean_dec(v___x_2641_);
v___x_2661_ = lean_box(0);
v_isShared_2662_ = v_isSharedCheck_2671_;
goto v_resetjp_2660_;
}
v_resetjp_2660_:
{
lean_object* v___x_2663_; lean_object* v___x_2665_; 
v___x_2663_ = l_Lean_LocalDecl_toExpr(v_val_2659_);
if (v_isShared_2658_ == 0)
{
lean_ctor_set(v___x_2657_, 1, v_projs_2628_);
lean_ctor_set(v___x_2657_, 0, v___x_2663_);
v___x_2665_ = v___x_2657_;
goto v_reusejp_2664_;
}
else
{
lean_object* v_reuseFailAlloc_2670_; 
v_reuseFailAlloc_2670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2670_, 0, v___x_2663_);
lean_ctor_set(v_reuseFailAlloc_2670_, 1, v_projs_2628_);
v___x_2665_ = v_reuseFailAlloc_2670_;
goto v_reusejp_2664_;
}
v_reusejp_2664_:
{
lean_object* v___x_2667_; 
if (v_isShared_2662_ == 0)
{
lean_ctor_set(v___x_2661_, 0, v___x_2665_);
v___x_2667_ = v___x_2661_;
goto v_reusejp_2666_;
}
else
{
lean_object* v_reuseFailAlloc_2669_; 
v_reuseFailAlloc_2669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2669_, 0, v___x_2665_);
v___x_2667_ = v_reuseFailAlloc_2669_;
goto v_reusejp_2666_;
}
v_reusejp_2666_:
{
lean_object* v___x_2668_; 
v___x_2668_ = lean_apply_2(v_toPure_2635_, lean_box(0), v___x_2667_);
return v___x_2668_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___lam__1(lean_object* v_str_2677_, lean_object* v_projs_2678_, lean_object* v_inst_2679_, lean_object* v_inst_2680_, lean_object* v_inst_2681_, lean_object* v_inst_2682_, lean_object* v_inst_2683_, lean_object* v_inst_2684_, lean_object* v_view_2685_, lean_object* v_findLocalDecl_x3f_2686_, lean_object* v_pre_2687_, lean_object* v_____r_2688_, uint8_t v_globalDeclFoundNext_2689_){
_start:
{
lean_object* v___x_2690_; lean_object* v___x_2691_; 
v___x_2690_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2690_, 0, v_str_2677_);
lean_ctor_set(v___x_2690_, 1, v_projs_2678_);
v___x_2691_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg(v_inst_2679_, v_inst_2680_, v_inst_2681_, v_inst_2682_, v_inst_2683_, v_inst_2684_, v_view_2685_, v_findLocalDecl_x3f_2686_, v_pre_2687_, v___x_2690_, v_globalDeclFoundNext_2689_);
return v___x_2691_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg___boxed(lean_object* v_inst_2692_, lean_object* v_inst_2693_, lean_object* v_inst_2694_, lean_object* v_inst_2695_, lean_object* v_inst_2696_, lean_object* v_inst_2697_, lean_object* v_view_2698_, lean_object* v_findLocalDecl_x3f_2699_, lean_object* v_n_2700_, lean_object* v_projs_2701_, lean_object* v_globalDeclFound_2702_){
_start:
{
uint8_t v_globalDeclFound_boxed_2703_; lean_object* v_res_2704_; 
v_globalDeclFound_boxed_2703_ = lean_unbox(v_globalDeclFound_2702_);
v_res_2704_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg(v_inst_2692_, v_inst_2693_, v_inst_2694_, v_inst_2695_, v_inst_2696_, v_inst_2697_, v_view_2698_, v_findLocalDecl_x3f_2699_, v_n_2700_, v_projs_2701_, v_globalDeclFound_boxed_2703_);
return v_res_2704_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop(lean_object* v_m_2705_, lean_object* v_inst_2706_, lean_object* v_inst_2707_, lean_object* v_inst_2708_, lean_object* v_inst_2709_, lean_object* v_inst_2710_, lean_object* v_inst_2711_, lean_object* v_view_2712_, lean_object* v_findLocalDecl_x3f_2713_, lean_object* v_n_2714_, lean_object* v_projs_2715_, uint8_t v_globalDeclFound_2716_){
_start:
{
lean_object* v___x_2717_; 
v___x_2717_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg(v_inst_2706_, v_inst_2707_, v_inst_2708_, v_inst_2709_, v_inst_2710_, v_inst_2711_, v_view_2712_, v_findLocalDecl_x3f_2713_, v_n_2714_, v_projs_2715_, v_globalDeclFound_2716_);
return v___x_2717_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___boxed(lean_object* v_m_2718_, lean_object* v_inst_2719_, lean_object* v_inst_2720_, lean_object* v_inst_2721_, lean_object* v_inst_2722_, lean_object* v_inst_2723_, lean_object* v_inst_2724_, lean_object* v_view_2725_, lean_object* v_findLocalDecl_x3f_2726_, lean_object* v_n_2727_, lean_object* v_projs_2728_, lean_object* v_globalDeclFound_2729_){
_start:
{
uint8_t v_globalDeclFound_boxed_2730_; lean_object* v_res_2731_; 
v_globalDeclFound_boxed_2730_ = lean_unbox(v_globalDeclFound_2729_);
v_res_2731_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop(v_m_2718_, v_inst_2719_, v_inst_2720_, v_inst_2721_, v_inst_2722_, v_inst_2723_, v_inst_2724_, v_view_2725_, v_findLocalDecl_x3f_2726_, v_n_2727_, v_projs_2728_, v_globalDeclFound_boxed_2730_);
return v_res_2731_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_go(lean_object* v_localDecl_2732_, lean_object* v_givenNameView_2733_, lean_object* v_fullDeclName_2734_, lean_object* v_ns_2735_){
_start:
{
lean_object* v_name_2736_; lean_object* v_imported_2737_; lean_object* v_ctx_2738_; lean_object* v_scopes_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; uint8_t v___x_2743_; 
v_name_2736_ = lean_ctor_get(v_givenNameView_2733_, 0);
v_imported_2737_ = lean_ctor_get(v_givenNameView_2733_, 1);
v_ctx_2738_ = lean_ctor_get(v_givenNameView_2733_, 2);
v_scopes_2739_ = lean_ctor_get(v_givenNameView_2733_, 3);
lean_inc(v_name_2736_);
lean_inc(v_ns_2735_);
v___x_2740_ = l_Lean_Name_append(v_ns_2735_, v_name_2736_);
lean_inc(v_scopes_2739_);
lean_inc(v_ctx_2738_);
lean_inc(v_imported_2737_);
v___x_2741_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2741_, 0, v___x_2740_);
lean_ctor_set(v___x_2741_, 1, v_imported_2737_);
lean_ctor_set(v___x_2741_, 2, v_ctx_2738_);
lean_ctor_set(v___x_2741_, 3, v_scopes_2739_);
v___x_2742_ = l_Lean_MacroScopesView_review(v___x_2741_);
v___x_2743_ = lean_name_eq(v___x_2742_, v_fullDeclName_2734_);
lean_dec(v___x_2742_);
if (v___x_2743_ == 0)
{
if (lean_obj_tag(v_ns_2735_) == 1)
{
lean_object* v_pre_2744_; 
v_pre_2744_ = lean_ctor_get(v_ns_2735_, 0);
lean_inc(v_pre_2744_);
lean_dec_ref_known(v_ns_2735_, 2);
v_ns_2735_ = v_pre_2744_;
goto _start;
}
else
{
lean_object* v___x_2746_; 
lean_dec(v_ns_2735_);
lean_dec_ref(v_givenNameView_2733_);
lean_dec_ref(v_localDecl_2732_);
v___x_2746_ = lean_box(0);
return v___x_2746_;
}
}
else
{
lean_object* v___x_2747_; 
lean_dec(v_ns_2735_);
lean_dec_ref(v_givenNameView_2733_);
v___x_2747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2747_, 0, v_localDecl_2732_);
return v___x_2747_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_resolveLocalName_go___boxed(lean_object* v_localDecl_2748_, lean_object* v_givenNameView_2749_, lean_object* v_fullDeclName_2750_, lean_object* v_ns_2751_){
_start:
{
lean_object* v_res_2752_; 
v_res_2752_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_go(v_localDecl_2748_, v_givenNameView_2749_, v_fullDeclName_2750_, v_ns_2751_);
lean_dec(v_fullDeclName_2750_);
return v_res_2752_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__0(lean_object* v_localDecl_2753_, lean_object* v_givenName_2754_){
_start:
{
lean_object* v___x_2755_; uint8_t v___x_2756_; 
v___x_2755_ = l_Lean_LocalDecl_userName(v_localDecl_2753_);
v___x_2756_ = lean_name_eq(v___x_2755_, v_givenName_2754_);
lean_dec(v___x_2755_);
if (v___x_2756_ == 0)
{
lean_object* v___x_2757_; 
lean_dec_ref(v_localDecl_2753_);
v___x_2757_ = lean_box(0);
return v___x_2757_;
}
else
{
lean_object* v___x_2758_; 
v___x_2758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2758_, 0, v_localDecl_2753_);
return v___x_2758_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__0___boxed(lean_object* v_localDecl_2759_, lean_object* v_givenName_2760_){
_start:
{
lean_object* v_res_2761_; 
v_res_2761_ = l_Lean_resolveLocalName___redArg___lam__0(v_localDecl_2759_, v_givenName_2760_);
lean_dec(v_givenName_2760_);
return v_res_2761_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__1(lean_object* v_matchLocalDecl_x3f_2762_, lean_object* v_givenName_2763_, uint8_t v_skipAuxDecl_2764_, lean_object* v___f_2765_, lean_object* v_auxDeclToFullName_2766_, lean_object* v_currNamespace_2767_, lean_object* v_givenNameView_2768_, lean_object* v_x_2769_){
_start:
{
if (lean_obj_tag(v_x_2769_) == 0)
{
lean_dec_ref(v_givenNameView_2768_);
lean_dec(v_currNamespace_2767_);
lean_dec(v_auxDeclToFullName_2766_);
lean_dec_ref(v___f_2765_);
lean_dec(v_givenName_2763_);
lean_dec_ref(v_matchLocalDecl_x3f_2762_);
return v_x_2769_;
}
else
{
lean_object* v_val_2770_; uint8_t v___x_2771_; 
v_val_2770_ = lean_ctor_get(v_x_2769_, 0);
v___x_2771_ = l_Lean_LocalDecl_isAuxDecl(v_val_2770_);
if (v___x_2771_ == 0)
{
lean_object* v___x_2772_; 
lean_inc(v_val_2770_);
lean_dec_ref_known(v_x_2769_, 1);
lean_dec_ref(v_givenNameView_2768_);
lean_dec(v_currNamespace_2767_);
lean_dec(v_auxDeclToFullName_2766_);
lean_dec_ref(v___f_2765_);
v___x_2772_ = lean_apply_2(v_matchLocalDecl_x3f_2762_, v_val_2770_, v_givenName_2763_);
return v___x_2772_;
}
else
{
if (v_skipAuxDecl_2764_ == 0)
{
if (v___x_2771_ == 0)
{
lean_object* v___x_2773_; 
lean_dec_ref_known(v_x_2769_, 1);
lean_dec_ref(v_givenNameView_2768_);
lean_dec(v_currNamespace_2767_);
lean_dec(v_auxDeclToFullName_2766_);
lean_dec_ref(v___f_2765_);
lean_dec(v_givenName_2763_);
lean_dec_ref(v_matchLocalDecl_x3f_2762_);
v___x_2773_ = lean_box(0);
return v___x_2773_;
}
else
{
lean_object* v___x_2774_; lean_object* v___x_2775_; 
v___x_2774_ = l_Lean_LocalDecl_fvarId(v_val_2770_);
v___x_2775_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v___f_2765_, v_auxDeclToFullName_2766_, v___x_2774_);
if (lean_obj_tag(v___x_2775_) == 1)
{
lean_object* v_val_2776_; lean_object* v_fullDeclView_2777_; lean_object* v___y_2779_; lean_object* v_name_2800_; lean_object* v___x_2801_; 
lean_dec(v_givenName_2763_);
lean_dec_ref(v_matchLocalDecl_x3f_2762_);
v_val_2776_ = lean_ctor_get(v___x_2775_, 0);
lean_inc(v_val_2776_);
lean_dec_ref_known(v___x_2775_, 1);
v_fullDeclView_2777_ = l_Lean_extractMacroScopes(v_val_2776_);
v_name_2800_ = lean_ctor_get(v_fullDeclView_2777_, 0);
lean_inc_n(v_name_2800_, 2);
v___x_2801_ = l_Lean_privateToUserName_x3f(v_name_2800_);
if (lean_obj_tag(v___x_2801_) == 0)
{
v___y_2779_ = v_name_2800_;
goto v___jp_2778_;
}
else
{
lean_object* v_val_2802_; 
lean_dec(v_name_2800_);
v_val_2802_ = lean_ctor_get(v___x_2801_, 0);
lean_inc(v_val_2802_);
lean_dec_ref_known(v___x_2801_, 1);
v___y_2779_ = v_val_2802_;
goto v___jp_2778_;
}
v___jp_2778_:
{
lean_object* v_imported_2780_; lean_object* v_ctx_2781_; lean_object* v_scopes_2782_; lean_object* v___x_2784_; uint8_t v_isShared_2785_; uint8_t v_isSharedCheck_2798_; 
v_imported_2780_ = lean_ctor_get(v_fullDeclView_2777_, 1);
v_ctx_2781_ = lean_ctor_get(v_fullDeclView_2777_, 2);
v_scopes_2782_ = lean_ctor_get(v_fullDeclView_2777_, 3);
v_isSharedCheck_2798_ = !lean_is_exclusive(v_fullDeclView_2777_);
if (v_isSharedCheck_2798_ == 0)
{
lean_object* v_unused_2799_; 
v_unused_2799_ = lean_ctor_get(v_fullDeclView_2777_, 0);
lean_dec(v_unused_2799_);
v___x_2784_ = v_fullDeclView_2777_;
v_isShared_2785_ = v_isSharedCheck_2798_;
goto v_resetjp_2783_;
}
else
{
lean_inc(v_scopes_2782_);
lean_inc(v_ctx_2781_);
lean_inc(v_imported_2780_);
lean_dec(v_fullDeclView_2777_);
v___x_2784_ = lean_box(0);
v_isShared_2785_ = v_isSharedCheck_2798_;
goto v_resetjp_2783_;
}
v_resetjp_2783_:
{
lean_object* v_fullDeclView_2787_; 
if (v_isShared_2785_ == 0)
{
lean_ctor_set(v___x_2784_, 0, v___y_2779_);
v_fullDeclView_2787_ = v___x_2784_;
goto v_reusejp_2786_;
}
else
{
lean_object* v_reuseFailAlloc_2797_; 
v_reuseFailAlloc_2797_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2797_, 0, v___y_2779_);
lean_ctor_set(v_reuseFailAlloc_2797_, 1, v_imported_2780_);
lean_ctor_set(v_reuseFailAlloc_2797_, 2, v_ctx_2781_);
lean_ctor_set(v_reuseFailAlloc_2797_, 3, v_scopes_2782_);
v_fullDeclView_2787_ = v_reuseFailAlloc_2797_;
goto v_reusejp_2786_;
}
v_reusejp_2786_:
{
lean_object* v_fullDeclName_2788_; uint8_t v___x_2789_; 
lean_inc_ref(v_fullDeclView_2787_);
v_fullDeclName_2788_ = l_Lean_MacroScopesView_review(v_fullDeclView_2787_);
v___x_2789_ = l_Lean_Name_isPrefixOf(v_currNamespace_2767_, v_fullDeclName_2788_);
if (v___x_2789_ == 0)
{
lean_object* v___x_2790_; 
lean_inc(v_val_2770_);
lean_dec_ref(v_fullDeclView_2787_);
lean_dec_ref_known(v_x_2769_, 1);
v___x_2790_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_go(v_val_2770_, v_givenNameView_2768_, v_fullDeclName_2788_, v_currNamespace_2767_);
lean_dec(v_fullDeclName_2788_);
return v___x_2790_;
}
else
{
lean_object* v___x_2791_; lean_object* v_localDeclNameView_2792_; uint8_t v___x_2793_; 
lean_dec(v_fullDeclName_2788_);
lean_dec(v_currNamespace_2767_);
v___x_2791_ = l_Lean_LocalDecl_userName(v_val_2770_);
v_localDeclNameView_2792_ = l_Lean_extractMacroScopes(v___x_2791_);
v___x_2793_ = l_Lean_MacroScopesView_isSuffixOf(v_localDeclNameView_2792_, v_givenNameView_2768_);
lean_dec_ref(v_localDeclNameView_2792_);
if (v___x_2793_ == 0)
{
lean_object* v___x_2794_; 
lean_dec_ref(v_fullDeclView_2787_);
lean_dec_ref_known(v_x_2769_, 1);
lean_dec_ref(v_givenNameView_2768_);
v___x_2794_ = lean_box(0);
return v___x_2794_;
}
else
{
uint8_t v___x_2795_; 
v___x_2795_ = l_Lean_MacroScopesView_isSuffixOf(v_givenNameView_2768_, v_fullDeclView_2787_);
lean_dec_ref(v_fullDeclView_2787_);
lean_dec_ref(v_givenNameView_2768_);
if (v___x_2795_ == 0)
{
lean_object* v___x_2796_; 
lean_dec_ref_known(v_x_2769_, 1);
v___x_2796_ = lean_box(0);
return v___x_2796_;
}
else
{
return v_x_2769_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2803_; 
lean_inc(v_val_2770_);
lean_dec(v___x_2775_);
lean_dec_ref_known(v_x_2769_, 1);
lean_dec_ref(v_givenNameView_2768_);
lean_dec(v_currNamespace_2767_);
v___x_2803_ = lean_apply_2(v_matchLocalDecl_x3f_2762_, v_val_2770_, v_givenName_2763_);
return v___x_2803_;
}
}
}
else
{
lean_object* v___x_2804_; 
lean_dec_ref_known(v_x_2769_, 1);
lean_dec_ref(v_givenNameView_2768_);
lean_dec(v_currNamespace_2767_);
lean_dec(v_auxDeclToFullName_2766_);
lean_dec_ref(v___f_2765_);
lean_dec(v_givenName_2763_);
lean_dec_ref(v_matchLocalDecl_x3f_2762_);
v___x_2804_ = lean_box(0);
return v___x_2804_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__1___boxed(lean_object* v_matchLocalDecl_x3f_2805_, lean_object* v_givenName_2806_, lean_object* v_skipAuxDecl_2807_, lean_object* v___f_2808_, lean_object* v_auxDeclToFullName_2809_, lean_object* v_currNamespace_2810_, lean_object* v_givenNameView_2811_, lean_object* v_x_2812_){
_start:
{
uint8_t v_skipAuxDecl_boxed_2813_; lean_object* v_res_2814_; 
v_skipAuxDecl_boxed_2813_ = lean_unbox(v_skipAuxDecl_2807_);
v_res_2814_ = l_Lean_resolveLocalName___redArg___lam__1(v_matchLocalDecl_x3f_2805_, v_givenName_2806_, v_skipAuxDecl_boxed_2813_, v___f_2808_, v_auxDeclToFullName_2809_, v_currNamespace_2810_, v_givenNameView_2811_, v_x_2812_);
return v_res_2814_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__2(lean_object* v_localDecl_x3f_2815_, lean_object* v_matchLocalDecl_x3f_2816_, lean_object* v_givenName_2817_, lean_object* v_x_2818_){
_start:
{
if (lean_obj_tag(v_x_2818_) == 0)
{
lean_dec(v_givenName_2817_);
lean_dec_ref(v_matchLocalDecl_x3f_2816_);
return v_x_2818_;
}
else
{
lean_object* v_val_2819_; uint8_t v___x_2820_; 
v_val_2819_ = lean_ctor_get(v_x_2818_, 0);
lean_inc(v_val_2819_);
lean_dec_ref_known(v_x_2818_, 1);
v___x_2820_ = l_Lean_LocalDecl_isAuxDecl(v_val_2819_);
if (v___x_2820_ == 0)
{
lean_dec(v_val_2819_);
lean_dec(v_givenName_2817_);
lean_dec_ref(v_matchLocalDecl_x3f_2816_);
lean_inc(v_localDecl_x3f_2815_);
return v_localDecl_x3f_2815_;
}
else
{
lean_object* v___x_2821_; 
v___x_2821_ = lean_apply_2(v_matchLocalDecl_x3f_2816_, v_val_2819_, v_givenName_2817_);
return v___x_2821_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__2___boxed(lean_object* v_localDecl_x3f_2822_, lean_object* v_matchLocalDecl_x3f_2823_, lean_object* v_givenName_2824_, lean_object* v_x_2825_){
_start:
{
lean_object* v_res_2826_; 
v_res_2826_ = l_Lean_resolveLocalName___redArg___lam__2(v_localDecl_x3f_2822_, v_matchLocalDecl_x3f_2823_, v_givenName_2824_, v_x_2825_);
lean_dec(v_localDecl_x3f_2822_);
return v_res_2826_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__3(lean_object* v_lctx_2846_, lean_object* v_matchLocalDecl_x3f_2847_, lean_object* v___f_2848_, lean_object* v_auxDeclToFullName_2849_, lean_object* v_currNamespace_2850_, lean_object* v_givenNameView_2851_, uint8_t v_skipAuxDecl_2852_){
_start:
{
lean_object* v_decls_2853_; lean_object* v_givenName_2854_; lean_object* v___x_2855_; lean_object* v___f_2856_; lean_object* v___x_2857_; lean_object* v_localDecl_x3f_2858_; 
v_decls_2853_ = lean_ctor_get(v_lctx_2846_, 1);
lean_inc_ref_n(v_decls_2853_, 2);
lean_dec_ref(v_lctx_2846_);
lean_inc_ref(v_givenNameView_2851_);
v_givenName_2854_ = l_Lean_MacroScopesView_review(v_givenNameView_2851_);
v___x_2855_ = lean_box(v_skipAuxDecl_2852_);
lean_inc(v_givenName_2854_);
lean_inc_ref(v_matchLocalDecl_x3f_2847_);
v___f_2856_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___redArg___lam__1___boxed), 8, 7);
lean_closure_set(v___f_2856_, 0, v_matchLocalDecl_x3f_2847_);
lean_closure_set(v___f_2856_, 1, v_givenName_2854_);
lean_closure_set(v___f_2856_, 2, v___x_2855_);
lean_closure_set(v___f_2856_, 3, v___f_2848_);
lean_closure_set(v___f_2856_, 4, v_auxDeclToFullName_2849_);
lean_closure_set(v___f_2856_, 5, v_currNamespace_2850_);
lean_closure_set(v___f_2856_, 6, v_givenNameView_2851_);
v___x_2857_ = ((lean_object*)(l_Lean_resolveLocalName___redArg___lam__3___closed__9));
v_localDecl_x3f_2858_ = l_Lean_PersistentArray_findSomeRevM_x3f___redArg(v___x_2857_, v_decls_2853_, v___f_2856_);
if (lean_obj_tag(v_localDecl_x3f_2858_) == 0)
{
if (v_skipAuxDecl_2852_ == 0)
{
lean_object* v___f_2859_; lean_object* v___x_2860_; 
v___f_2859_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_2859_, 0, v_localDecl_x3f_2858_);
lean_closure_set(v___f_2859_, 1, v_matchLocalDecl_x3f_2847_);
lean_closure_set(v___f_2859_, 2, v_givenName_2854_);
v___x_2860_ = l_Lean_PersistentArray_findSomeRevM_x3f___redArg(v___x_2857_, v_decls_2853_, v___f_2859_);
return v___x_2860_;
}
else
{
lean_dec(v_givenName_2854_);
lean_dec_ref(v_decls_2853_);
lean_dec_ref(v_matchLocalDecl_x3f_2847_);
return v_localDecl_x3f_2858_;
}
}
else
{
lean_dec(v_givenName_2854_);
lean_dec_ref(v_decls_2853_);
lean_dec_ref(v_matchLocalDecl_x3f_2847_);
return v_localDecl_x3f_2858_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__3___boxed(lean_object* v_lctx_2861_, lean_object* v_matchLocalDecl_x3f_2862_, lean_object* v___f_2863_, lean_object* v_auxDeclToFullName_2864_, lean_object* v_currNamespace_2865_, lean_object* v_givenNameView_2866_, lean_object* v_skipAuxDecl_2867_){
_start:
{
uint8_t v_skipAuxDecl_boxed_2868_; lean_object* v_res_2869_; 
v_skipAuxDecl_boxed_2868_ = lean_unbox(v_skipAuxDecl_2867_);
v_res_2869_ = l_Lean_resolveLocalName___redArg___lam__3(v_lctx_2861_, v_matchLocalDecl_x3f_2862_, v___f_2863_, v_auxDeclToFullName_2864_, v_currNamespace_2865_, v_givenNameView_2866_, v_skipAuxDecl_boxed_2868_);
return v_res_2869_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__4(lean_object* v_n_2870_, lean_object* v_lctx_2871_, lean_object* v_matchLocalDecl_x3f_2872_, lean_object* v___f_2873_, lean_object* v_auxDeclToFullName_2874_, lean_object* v_inst_2875_, lean_object* v_inst_2876_, lean_object* v_inst_2877_, lean_object* v_inst_2878_, lean_object* v_inst_2879_, lean_object* v_inst_2880_, lean_object* v_currNamespace_2881_){
_start:
{
lean_object* v_view_2882_; lean_object* v_name_2883_; lean_object* v_findLocalDecl_x3f_2884_; lean_object* v___x_2885_; uint8_t v___x_2886_; lean_object* v___x_2887_; 
v_view_2882_ = l_Lean_extractMacroScopes(v_n_2870_);
v_name_2883_ = lean_ctor_get(v_view_2882_, 0);
lean_inc(v_name_2883_);
v_findLocalDecl_x3f_2884_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___redArg___lam__3___boxed), 7, 5);
lean_closure_set(v_findLocalDecl_x3f_2884_, 0, v_lctx_2871_);
lean_closure_set(v_findLocalDecl_x3f_2884_, 1, v_matchLocalDecl_x3f_2872_);
lean_closure_set(v_findLocalDecl_x3f_2884_, 2, v___f_2873_);
lean_closure_set(v_findLocalDecl_x3f_2884_, 3, v_auxDeclToFullName_2874_);
lean_closure_set(v_findLocalDecl_x3f_2884_, 4, v_currNamespace_2881_);
v___x_2885_ = lean_box(0);
v___x_2886_ = 0;
v___x_2887_ = l___private_Lean_ResolveName_0__Lean_resolveLocalName_loop___redArg(v_inst_2875_, v_inst_2876_, v_inst_2877_, v_inst_2878_, v_inst_2879_, v_inst_2880_, v_view_2882_, v_findLocalDecl_x3f_2884_, v_name_2883_, v___x_2885_, v___x_2886_);
return v___x_2887_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__5(lean_object* v_inst_2888_, lean_object* v_n_2889_, lean_object* v_lctx_2890_, lean_object* v_matchLocalDecl_x3f_2891_, lean_object* v___f_2892_, lean_object* v_inst_2893_, lean_object* v_inst_2894_, lean_object* v_inst_2895_, lean_object* v_inst_2896_, lean_object* v_inst_2897_, lean_object* v_toBind_2898_, lean_object* v_____do__lift_2899_){
_start:
{
lean_object* v_auxDeclToFullName_2900_; lean_object* v_getCurrNamespace_2901_; lean_object* v___f_2902_; lean_object* v___x_2903_; 
v_auxDeclToFullName_2900_ = lean_ctor_get(v_____do__lift_2899_, 2);
lean_inc(v_auxDeclToFullName_2900_);
lean_dec_ref(v_____do__lift_2899_);
v_getCurrNamespace_2901_ = lean_ctor_get(v_inst_2888_, 0);
lean_inc(v_getCurrNamespace_2901_);
v___f_2902_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___redArg___lam__4), 12, 11);
lean_closure_set(v___f_2902_, 0, v_n_2889_);
lean_closure_set(v___f_2902_, 1, v_lctx_2890_);
lean_closure_set(v___f_2902_, 2, v_matchLocalDecl_x3f_2891_);
lean_closure_set(v___f_2902_, 3, v___f_2892_);
lean_closure_set(v___f_2902_, 4, v_auxDeclToFullName_2900_);
lean_closure_set(v___f_2902_, 5, v_inst_2893_);
lean_closure_set(v___f_2902_, 6, v_inst_2888_);
lean_closure_set(v___f_2902_, 7, v_inst_2894_);
lean_closure_set(v___f_2902_, 8, v_inst_2895_);
lean_closure_set(v___f_2902_, 9, v_inst_2896_);
lean_closure_set(v___f_2902_, 10, v_inst_2897_);
v___x_2903_ = lean_apply_4(v_toBind_2898_, lean_box(0), lean_box(0), v_getCurrNamespace_2901_, v___f_2902_);
return v___x_2903_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg___lam__6(lean_object* v_inst_2904_, lean_object* v_n_2905_, lean_object* v_matchLocalDecl_x3f_2906_, lean_object* v___f_2907_, lean_object* v_inst_2908_, lean_object* v_inst_2909_, lean_object* v_inst_2910_, lean_object* v_inst_2911_, lean_object* v_inst_2912_, lean_object* v_toBind_2913_, lean_object* v_inst_2914_, lean_object* v_lctx_2915_){
_start:
{
lean_object* v___f_2916_; lean_object* v___x_2917_; 
lean_inc(v_toBind_2913_);
v___f_2916_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___redArg___lam__5), 12, 11);
lean_closure_set(v___f_2916_, 0, v_inst_2904_);
lean_closure_set(v___f_2916_, 1, v_n_2905_);
lean_closure_set(v___f_2916_, 2, v_lctx_2915_);
lean_closure_set(v___f_2916_, 3, v_matchLocalDecl_x3f_2906_);
lean_closure_set(v___f_2916_, 4, v___f_2907_);
lean_closure_set(v___f_2916_, 5, v_inst_2908_);
lean_closure_set(v___f_2916_, 6, v_inst_2909_);
lean_closure_set(v___f_2916_, 7, v_inst_2910_);
lean_closure_set(v___f_2916_, 8, v_inst_2911_);
lean_closure_set(v___f_2916_, 9, v_inst_2912_);
lean_closure_set(v___f_2916_, 10, v_toBind_2913_);
v___x_2917_ = lean_apply_4(v_toBind_2913_, lean_box(0), lean_box(0), v_inst_2914_, v___f_2916_);
return v___x_2917_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName___redArg(lean_object* v_inst_2920_, lean_object* v_inst_2921_, lean_object* v_inst_2922_, lean_object* v_inst_2923_, lean_object* v_inst_2924_, lean_object* v_inst_2925_, lean_object* v_inst_2926_, lean_object* v_n_2927_){
_start:
{
lean_object* v_toBind_2928_; lean_object* v___f_2929_; lean_object* v_matchLocalDecl_x3f_2930_; lean_object* v___f_2931_; lean_object* v___x_2932_; 
v_toBind_2928_ = lean_ctor_get(v_inst_2920_, 1);
lean_inc_n(v_toBind_2928_, 2);
v___f_2929_ = ((lean_object*)(l_Lean_resolveLocalName___redArg___closed__0));
v_matchLocalDecl_x3f_2930_ = ((lean_object*)(l_Lean_resolveLocalName___redArg___closed__1));
lean_inc(v_inst_2926_);
v___f_2931_ = lean_alloc_closure((void*)(l_Lean_resolveLocalName___redArg___lam__6), 12, 11);
lean_closure_set(v___f_2931_, 0, v_inst_2921_);
lean_closure_set(v___f_2931_, 1, v_n_2927_);
lean_closure_set(v___f_2931_, 2, v_matchLocalDecl_x3f_2930_);
lean_closure_set(v___f_2931_, 3, v___f_2929_);
lean_closure_set(v___f_2931_, 4, v_inst_2920_);
lean_closure_set(v___f_2931_, 5, v_inst_2922_);
lean_closure_set(v___f_2931_, 6, v_inst_2923_);
lean_closure_set(v___f_2931_, 7, v_inst_2924_);
lean_closure_set(v___f_2931_, 8, v_inst_2925_);
lean_closure_set(v___f_2931_, 9, v_toBind_2928_);
lean_closure_set(v___f_2931_, 10, v_inst_2926_);
v___x_2932_ = lean_apply_4(v_toBind_2928_, lean_box(0), lean_box(0), v_inst_2926_, v___f_2931_);
return v___x_2932_;
}
}
LEAN_EXPORT lean_object* l_Lean_resolveLocalName(lean_object* v_m_2933_, lean_object* v_inst_2934_, lean_object* v_inst_2935_, lean_object* v_inst_2936_, lean_object* v_inst_2937_, lean_object* v_inst_2938_, lean_object* v_inst_2939_, lean_object* v_inst_2940_, lean_object* v_n_2941_){
_start:
{
lean_object* v___x_2942_; 
v___x_2942_ = l_Lean_resolveLocalName___redArg(v_inst_2934_, v_inst_2935_, v_inst_2936_, v_inst_2937_, v_inst_2938_, v_inst_2939_, v_inst_2940_, v_n_2941_);
return v___x_2942_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__0(lean_object* v_toPure_2943_, uint8_t v_____do__lift_2944_){
_start:
{
lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; 
v___x_2945_ = lean_box(v_____do__lift_2944_);
v___x_2946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2946_, 0, v___x_2945_);
v___x_2947_ = lean_apply_2(v_toPure_2943_, lean_box(0), v___x_2946_);
return v___x_2947_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__0___boxed(lean_object* v_toPure_2948_, lean_object* v_____do__lift_2949_){
_start:
{
uint8_t v_____do__lift_1160__boxed_2950_; lean_object* v_res_2951_; 
v_____do__lift_1160__boxed_2950_ = lean_unbox(v_____do__lift_2949_);
v_res_2951_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__0(v_toPure_2948_, v_____do__lift_1160__boxed_2950_);
return v_res_2951_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__1(lean_object* v_toPure_2952_, lean_object* v___y_2953_, lean_object* v_____do__lift_2954_){
_start:
{
if (lean_obj_tag(v_____do__lift_2954_) == 0)
{
lean_object* v___x_2955_; lean_object* v___x_2956_; 
lean_dec(v___y_2953_);
v___x_2955_ = lean_box(0);
v___x_2956_ = lean_apply_2(v_toPure_2952_, lean_box(0), v___x_2955_);
return v___x_2956_;
}
else
{
lean_object* v___x_2958_; uint8_t v_isShared_2959_; uint8_t v_isSharedCheck_2964_; 
v_isSharedCheck_2964_ = !lean_is_exclusive(v_____do__lift_2954_);
if (v_isSharedCheck_2964_ == 0)
{
lean_object* v_unused_2965_; 
v_unused_2965_ = lean_ctor_get(v_____do__lift_2954_, 0);
lean_dec(v_unused_2965_);
v___x_2958_ = v_____do__lift_2954_;
v_isShared_2959_ = v_isSharedCheck_2964_;
goto v_resetjp_2957_;
}
else
{
lean_dec(v_____do__lift_2954_);
v___x_2958_ = lean_box(0);
v_isShared_2959_ = v_isSharedCheck_2964_;
goto v_resetjp_2957_;
}
v_resetjp_2957_:
{
lean_object* v___x_2961_; 
if (v_isShared_2959_ == 0)
{
lean_ctor_set(v___x_2958_, 0, v___y_2953_);
v___x_2961_ = v___x_2958_;
goto v_reusejp_2960_;
}
else
{
lean_object* v_reuseFailAlloc_2963_; 
v_reuseFailAlloc_2963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2963_, 0, v___y_2953_);
v___x_2961_ = v_reuseFailAlloc_2963_;
goto v_reusejp_2960_;
}
v_reusejp_2960_:
{
lean_object* v___x_2962_; 
v___x_2962_ = lean_apply_2(v_toPure_2952_, lean_box(0), v___x_2961_);
return v___x_2962_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2(lean_object* v_toPure_2968_, lean_object* v_toBind_2969_, lean_object* v___f_2970_, lean_object* v_____do__lift_2971_){
_start:
{
if (lean_obj_tag(v_____do__lift_2971_) == 0)
{
lean_object* v___x_2972_; lean_object* v___x_2973_; 
lean_dec(v___f_2970_);
lean_dec(v_toBind_2969_);
v___x_2972_ = lean_box(0);
v___x_2973_ = lean_apply_2(v_toPure_2968_, lean_box(0), v___x_2972_);
return v___x_2973_;
}
else
{
lean_object* v_val_2974_; uint8_t v___x_2975_; 
v_val_2974_ = lean_ctor_get(v_____do__lift_2971_, 0);
v___x_2975_ = lean_unbox(v_val_2974_);
if (v___x_2975_ == 0)
{
lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; 
v___x_2976_ = lean_box(0);
v___x_2977_ = lean_apply_2(v_toPure_2968_, lean_box(0), v___x_2976_);
v___x_2978_ = lean_apply_4(v_toBind_2969_, lean_box(0), lean_box(0), v___x_2977_, v___f_2970_);
return v___x_2978_;
}
else
{
lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; 
v___x_2979_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2___closed__0));
v___x_2980_ = lean_apply_2(v_toPure_2968_, lean_box(0), v___x_2979_);
v___x_2981_ = lean_apply_4(v_toBind_2969_, lean_box(0), lean_box(0), v___x_2980_, v___f_2970_);
return v___x_2981_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2___boxed(lean_object* v_toPure_2982_, lean_object* v_toBind_2983_, lean_object* v___f_2984_, lean_object* v_____do__lift_2985_){
_start:
{
lean_object* v_res_2986_; 
v_res_2986_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2(v_toPure_2982_, v_toBind_2983_, v___f_2984_, v_____do__lift_2985_);
lean_dec(v_____do__lift_2985_);
return v_res_2986_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__3(lean_object* v_toPure_2987_, lean_object* v_filter_2988_, lean_object* v___y_2989_, lean_object* v_toBind_2990_, lean_object* v___f_2991_, lean_object* v___f_2992_, lean_object* v_____do__lift_2993_){
_start:
{
if (lean_obj_tag(v_____do__lift_2993_) == 0)
{
lean_object* v___x_2994_; lean_object* v___x_2995_; 
lean_dec(v___f_2992_);
lean_dec(v___f_2991_);
lean_dec(v_toBind_2990_);
lean_dec(v___y_2989_);
lean_dec(v_filter_2988_);
v___x_2994_ = lean_box(0);
v___x_2995_ = lean_apply_2(v_toPure_2987_, lean_box(0), v___x_2994_);
return v___x_2995_;
}
else
{
lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; 
lean_dec(v_toPure_2987_);
v___x_2996_ = lean_apply_1(v_filter_2988_, v___y_2989_);
lean_inc(v_toBind_2990_);
v___x_2997_ = lean_apply_4(v_toBind_2990_, lean_box(0), lean_box(0), v___x_2996_, v___f_2991_);
v___x_2998_ = lean_apply_4(v_toBind_2990_, lean_box(0), lean_box(0), v___x_2997_, v___f_2992_);
return v___x_2998_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__3___boxed(lean_object* v_toPure_2999_, lean_object* v_filter_3000_, lean_object* v___y_3001_, lean_object* v_toBind_3002_, lean_object* v___f_3003_, lean_object* v___f_3004_, lean_object* v_____do__lift_3005_){
_start:
{
lean_object* v_res_3006_; 
v_res_3006_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__3(v_toPure_2999_, v_filter_3000_, v___y_3001_, v_toBind_3002_, v___f_3003_, v___f_3004_, v_____do__lift_3005_);
lean_dec(v_____do__lift_3005_);
return v_res_3006_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__4(lean_object* v_toPure_3007_, lean_object* v_n_u2080_3008_, lean_object* v_toBind_3009_, lean_object* v___f_3010_, lean_object* v_____do__lift_3011_){
_start:
{
if (lean_obj_tag(v_____do__lift_3011_) == 0)
{
lean_object* v___x_3015_; lean_object* v___x_3016_; 
lean_dec(v___f_3010_);
lean_dec(v_toBind_3009_);
v___x_3015_ = lean_box(0);
v___x_3016_ = lean_apply_2(v_toPure_3007_, lean_box(0), v___x_3015_);
return v___x_3016_;
}
else
{
lean_object* v_val_3017_; 
v_val_3017_ = lean_ctor_get(v_____do__lift_3011_, 0);
if (lean_obj_tag(v_val_3017_) == 1)
{
lean_object* v_tail_3018_; 
v_tail_3018_ = lean_ctor_get(v_val_3017_, 1);
if (lean_obj_tag(v_tail_3018_) == 0)
{
lean_object* v_head_3019_; lean_object* v_fst_3020_; uint8_t v___x_3021_; 
v_head_3019_ = lean_ctor_get(v_val_3017_, 0);
v_fst_3020_ = lean_ctor_get(v_head_3019_, 0);
v___x_3021_ = lean_name_eq(v_fst_3020_, v_n_u2080_3008_);
if (v___x_3021_ == 0)
{
lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; 
v___x_3022_ = lean_box(0);
v___x_3023_ = lean_apply_2(v_toPure_3007_, lean_box(0), v___x_3022_);
v___x_3024_ = lean_apply_4(v_toBind_3009_, lean_box(0), lean_box(0), v___x_3023_, v___f_3010_);
return v___x_3024_;
}
else
{
lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; 
v___x_3025_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2___closed__0));
v___x_3026_ = lean_apply_2(v_toPure_3007_, lean_box(0), v___x_3025_);
v___x_3027_ = lean_apply_4(v_toBind_3009_, lean_box(0), lean_box(0), v___x_3026_, v___f_3010_);
return v___x_3027_;
}
}
else
{
lean_dec(v___f_3010_);
lean_dec(v_toBind_3009_);
goto v___jp_3012_;
}
}
else
{
lean_dec(v___f_3010_);
lean_dec(v_toBind_3009_);
goto v___jp_3012_;
}
}
v___jp_3012_:
{
lean_object* v___x_3013_; lean_object* v___x_3014_; 
v___x_3013_ = lean_box(0);
v___x_3014_ = lean_apply_2(v_toPure_3007_, lean_box(0), v___x_3013_);
return v___x_3014_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__4___boxed(lean_object* v_toPure_3028_, lean_object* v_n_u2080_3029_, lean_object* v_toBind_3030_, lean_object* v___f_3031_, lean_object* v_____do__lift_3032_){
_start:
{
lean_object* v_res_3033_; 
v_res_3033_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__4(v_toPure_3028_, v_n_u2080_3029_, v_toBind_3030_, v___f_3031_, v_____do__lift_3032_);
lean_dec(v_____do__lift_3032_);
lean_dec(v_n_u2080_3029_);
return v_res_3033_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg(lean_object* v_inst_3034_, lean_object* v_inst_3035_, lean_object* v_inst_3036_, lean_object* v_inst_3037_, lean_object* v_inst_3038_, lean_object* v_inst_3039_, lean_object* v_n_u2080_3040_, lean_object* v_filter_3041_, lean_object* v_view_x3f_3042_, lean_object* v_n_3043_){
_start:
{
lean_object* v___f_3044_; lean_object* v___f_3045_; lean_object* v___f_3046_; lean_object* v___f_3047_; lean_object* v___f_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v_toApplicative_3056_; lean_object* v_getEnv_3057_; lean_object* v_modifyEnv_3058_; lean_object* v___x_3060_; uint8_t v_isShared_3061_; uint8_t v_isSharedCheck_3096_; 
lean_inc_ref_n(v_inst_3034_, 8);
v___f_3044_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_3044_, 0, v_inst_3034_);
v___f_3045_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__3), 5, 1);
lean_closure_set(v___f_3045_, 0, v_inst_3034_);
v___f_3046_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__6), 5, 1);
lean_closure_set(v___f_3046_, 0, v_inst_3034_);
v___f_3047_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_3047_, 0, v_inst_3034_);
v___f_3048_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__11), 5, 1);
lean_closure_set(v___f_3048_, 0, v_inst_3034_);
v___x_3049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3049_, 0, v___f_3044_);
lean_ctor_set(v___x_3049_, 1, v___f_3045_);
v___x_3050_ = lean_alloc_closure((void*)(l_OptionT_pure), 4, 2);
lean_closure_set(v___x_3050_, 0, lean_box(0));
lean_closure_set(v___x_3050_, 1, v_inst_3034_);
v___x_3051_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3051_, 0, v___x_3049_);
lean_ctor_set(v___x_3051_, 1, v___x_3050_);
lean_ctor_set(v___x_3051_, 2, v___f_3046_);
lean_ctor_set(v___x_3051_, 3, v___f_3047_);
lean_ctor_set(v___x_3051_, 4, v___f_3048_);
v___x_3052_ = lean_alloc_closure((void*)(l_OptionT_bind), 6, 2);
lean_closure_set(v___x_3052_, 0, lean_box(0));
lean_closure_set(v___x_3052_, 1, v_inst_3034_);
v___x_3053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3053_, 0, v___x_3051_);
lean_ctor_set(v___x_3053_, 1, v___x_3052_);
v___x_3054_ = lean_alloc_closure((void*)(l_OptionT_lift), 4, 2);
lean_closure_set(v___x_3054_, 0, lean_box(0));
lean_closure_set(v___x_3054_, 1, v_inst_3034_);
lean_inc_ref(v___x_3054_);
v___x_3055_ = l_Lean_instMonadResolveNameOfMonadLift___redArg(v___x_3054_, v_inst_3035_);
v_toApplicative_3056_ = lean_ctor_get(v_inst_3034_, 0);
lean_inc_ref(v_toApplicative_3056_);
v_getEnv_3057_ = lean_ctor_get(v_inst_3036_, 0);
v_modifyEnv_3058_ = lean_ctor_get(v_inst_3036_, 1);
v_isSharedCheck_3096_ = !lean_is_exclusive(v_inst_3036_);
if (v_isSharedCheck_3096_ == 0)
{
v___x_3060_ = v_inst_3036_;
v_isShared_3061_ = v_isSharedCheck_3096_;
goto v_resetjp_3059_;
}
else
{
lean_inc(v_modifyEnv_3058_);
lean_inc(v_getEnv_3057_);
lean_dec(v_inst_3036_);
v___x_3060_ = lean_box(0);
v_isShared_3061_ = v_isSharedCheck_3096_;
goto v_resetjp_3059_;
}
v_resetjp_3059_:
{
lean_object* v_toBind_3062_; lean_object* v_toPure_3063_; lean_object* v___f_3064_; lean_object* v___f_3065_; lean_object* v___f_3066_; lean_object* v___x_3067_; lean_object* v___x_3069_; 
v_toBind_3062_ = lean_ctor_get(v_inst_3034_, 1);
lean_inc_n(v_toBind_3062_, 2);
lean_dec_ref(v_inst_3034_);
v_toPure_3063_ = lean_ctor_get(v_toApplicative_3056_, 1);
lean_inc_n(v_toPure_3063_, 3);
lean_dec_ref(v_toApplicative_3056_);
lean_inc_ref(v___x_3054_);
v___f_3064_ = lean_alloc_closure((void*)(l_Lean_instMonadEnvOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3064_, 0, v_modifyEnv_3058_);
lean_closure_set(v___f_3064_, 1, v___x_3054_);
v___f_3065_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3065_, 0, v_toPure_3063_);
v___f_3066_ = lean_alloc_closure((void*)(l_OptionT_lift___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3066_, 0, v_toPure_3063_);
lean_inc_ref(v___f_3066_);
v___x_3067_ = lean_apply_4(v_toBind_3062_, lean_box(0), lean_box(0), v_getEnv_3057_, v___f_3066_);
if (v_isShared_3061_ == 0)
{
lean_ctor_set(v___x_3060_, 1, v___f_3064_);
lean_ctor_set(v___x_3060_, 0, v___x_3067_);
v___x_3069_ = v___x_3060_;
goto v_reusejp_3068_;
}
else
{
lean_object* v_reuseFailAlloc_3095_; 
v_reuseFailAlloc_3095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3095_, 0, v___x_3067_);
lean_ctor_set(v_reuseFailAlloc_3095_, 1, v___f_3064_);
v___x_3069_ = v_reuseFailAlloc_3095_;
goto v_reusejp_3068_;
}
v_reusejp_3068_:
{
lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___f_3072_; lean_object* v___y_3074_; 
lean_inc(v_toBind_3062_);
v___x_3070_ = lean_apply_4(v_toBind_3062_, lean_box(0), lean_box(0), v_inst_3037_, v___f_3066_);
lean_inc_ref(v___x_3054_);
v___x_3071_ = l_Lean_instMonadLogOfMonadLift___redArg(v___x_3054_, v_inst_3038_);
v___f_3072_ = lean_alloc_closure((void*)(l_Lean_instAddMessageContextOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3072_, 0, v_inst_3039_);
lean_closure_set(v___f_3072_, 1, v___x_3054_);
if (lean_obj_tag(v_view_x3f_3042_) == 1)
{
lean_object* v_val_3082_; lean_object* v_imported_3083_; lean_object* v_ctx_3084_; lean_object* v_scopes_3085_; lean_object* v___x_3087_; uint8_t v_isShared_3088_; uint8_t v_isSharedCheck_3093_; 
v_val_3082_ = lean_ctor_get(v_view_x3f_3042_, 0);
lean_inc(v_val_3082_);
lean_dec_ref_known(v_view_x3f_3042_, 1);
v_imported_3083_ = lean_ctor_get(v_val_3082_, 1);
v_ctx_3084_ = lean_ctor_get(v_val_3082_, 2);
v_scopes_3085_ = lean_ctor_get(v_val_3082_, 3);
v_isSharedCheck_3093_ = !lean_is_exclusive(v_val_3082_);
if (v_isSharedCheck_3093_ == 0)
{
lean_object* v_unused_3094_; 
v_unused_3094_ = lean_ctor_get(v_val_3082_, 0);
lean_dec(v_unused_3094_);
v___x_3087_ = v_val_3082_;
v_isShared_3088_ = v_isSharedCheck_3093_;
goto v_resetjp_3086_;
}
else
{
lean_inc(v_scopes_3085_);
lean_inc(v_ctx_3084_);
lean_inc(v_imported_3083_);
lean_dec(v_val_3082_);
v___x_3087_ = lean_box(0);
v_isShared_3088_ = v_isSharedCheck_3093_;
goto v_resetjp_3086_;
}
v_resetjp_3086_:
{
lean_object* v___x_3090_; 
if (v_isShared_3088_ == 0)
{
lean_ctor_set(v___x_3087_, 0, v_n_3043_);
v___x_3090_ = v___x_3087_;
goto v_reusejp_3089_;
}
else
{
lean_object* v_reuseFailAlloc_3092_; 
v_reuseFailAlloc_3092_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_3092_, 0, v_n_3043_);
lean_ctor_set(v_reuseFailAlloc_3092_, 1, v_imported_3083_);
lean_ctor_set(v_reuseFailAlloc_3092_, 2, v_ctx_3084_);
lean_ctor_set(v_reuseFailAlloc_3092_, 3, v_scopes_3085_);
v___x_3090_ = v_reuseFailAlloc_3092_;
goto v_reusejp_3089_;
}
v_reusejp_3089_:
{
lean_object* v___x_3091_; 
v___x_3091_ = l_Lean_MacroScopesView_review(v___x_3090_);
v___y_3074_ = v___x_3091_;
goto v___jp_3073_;
}
}
}
else
{
lean_dec(v_view_x3f_3042_);
v___y_3074_ = v_n_3043_;
goto v___jp_3073_;
}
v___jp_3073_:
{
lean_object* v___f_3075_; lean_object* v___f_3076_; lean_object* v___f_3077_; lean_object* v___f_3078_; uint8_t v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; 
lean_inc_n(v___y_3074_, 2);
lean_inc_n(v_toPure_3063_, 3);
v___f_3075_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__1), 3, 2);
lean_closure_set(v___f_3075_, 0, v_toPure_3063_);
lean_closure_set(v___f_3075_, 1, v___y_3074_);
lean_inc_n(v_toBind_3062_, 3);
v___f_3076_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2___boxed), 4, 3);
lean_closure_set(v___f_3076_, 0, v_toPure_3063_);
lean_closure_set(v___f_3076_, 1, v_toBind_3062_);
lean_closure_set(v___f_3076_, 2, v___f_3075_);
v___f_3077_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__3___boxed), 7, 6);
lean_closure_set(v___f_3077_, 0, v_toPure_3063_);
lean_closure_set(v___f_3077_, 1, v_filter_3041_);
lean_closure_set(v___f_3077_, 2, v___y_3074_);
lean_closure_set(v___f_3077_, 3, v_toBind_3062_);
lean_closure_set(v___f_3077_, 4, v___f_3065_);
lean_closure_set(v___f_3077_, 5, v___f_3076_);
v___f_3078_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__4___boxed), 5, 4);
lean_closure_set(v___f_3078_, 0, v_toPure_3063_);
lean_closure_set(v___f_3078_, 1, v_n_u2080_3040_);
lean_closure_set(v___f_3078_, 2, v_toBind_3062_);
lean_closure_set(v___f_3078_, 3, v___f_3077_);
v___x_3079_ = 0;
v___x_3080_ = l_Lean_resolveGlobalName___redArg(v___x_3053_, v___x_3055_, v___x_3069_, v___x_3070_, v___x_3071_, v___f_3072_, v___y_3074_, v___x_3079_);
v___x_3081_ = lean_apply_4(v_toBind_3062_, lean_box(0), lean_box(0), v___x_3080_, v___f_3078_);
return v___x_3081_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve(lean_object* v_m_3097_, lean_object* v_inst_3098_, lean_object* v_inst_3099_, lean_object* v_inst_3100_, lean_object* v_inst_3101_, lean_object* v_inst_3102_, lean_object* v_inst_3103_, lean_object* v_n_u2080_3104_, lean_object* v_filter_3105_, lean_object* v_view_x3f_3106_, lean_object* v_n_3107_){
_start:
{
lean_object* v___x_3108_; 
v___x_3108_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg(v_inst_3098_, v_inst_3099_, v_inst_3100_, v_inst_3101_, v_inst_3102_, v_inst_3103_, v_n_u2080_3104_, v_filter_3105_, v_view_x3f_3106_, v_n_3107_);
return v___x_3108_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__0(lean_object* v_toPure_3113_, lean_object* v_____x_3114_){
_start:
{
if (lean_obj_tag(v_____x_3114_) == 0)
{
lean_object* v___x_3115_; lean_object* v___x_3116_; 
v___x_3115_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__0___closed__1));
v___x_3116_ = lean_apply_2(v_toPure_3113_, lean_box(0), v___x_3115_);
return v___x_3116_;
}
else
{
lean_object* v___x_3117_; 
v___x_3117_ = lean_apply_2(v_toPure_3113_, lean_box(0), v_____x_3114_);
return v___x_3117_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__1(lean_object* v_toPure_3118_, lean_object* v_____do__lift_3119_){
_start:
{
if (lean_obj_tag(v_____do__lift_3119_) == 0)
{
lean_object* v___x_3120_; lean_object* v___x_3121_; 
v___x_3120_ = lean_box(0);
v___x_3121_ = lean_apply_2(v_toPure_3118_, lean_box(0), v___x_3120_);
return v___x_3121_;
}
else
{
lean_object* v_val_3122_; lean_object* v___x_3124_; uint8_t v_isShared_3125_; uint8_t v_isSharedCheck_3131_; 
v_val_3122_ = lean_ctor_get(v_____do__lift_3119_, 0);
v_isSharedCheck_3131_ = !lean_is_exclusive(v_____do__lift_3119_);
if (v_isSharedCheck_3131_ == 0)
{
v___x_3124_ = v_____do__lift_3119_;
v_isShared_3125_ = v_isSharedCheck_3131_;
goto v_resetjp_3123_;
}
else
{
lean_inc(v_val_3122_);
lean_dec(v_____do__lift_3119_);
v___x_3124_ = lean_box(0);
v_isShared_3125_ = v_isSharedCheck_3131_;
goto v_resetjp_3123_;
}
v_resetjp_3123_:
{
lean_object* v___x_3126_; lean_object* v___x_3128_; 
v___x_3126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3126_, 0, v_val_3122_);
if (v_isShared_3125_ == 0)
{
lean_ctor_set(v___x_3124_, 0, v___x_3126_);
v___x_3128_ = v___x_3124_;
goto v_reusejp_3127_;
}
else
{
lean_object* v_reuseFailAlloc_3130_; 
v_reuseFailAlloc_3130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3130_, 0, v___x_3126_);
v___x_3128_ = v_reuseFailAlloc_3130_;
goto v_reusejp_3127_;
}
v_reusejp_3127_:
{
lean_object* v___x_3129_; 
v___x_3129_ = lean_apply_2(v_toPure_3118_, lean_box(0), v___x_3128_);
return v___x_3129_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__2(lean_object* v_toPure_3132_, lean_object* v___x_3133_, lean_object* v_____do__lift_3134_){
_start:
{
if (lean_obj_tag(v_____do__lift_3134_) == 0)
{
lean_object* v___x_3135_; 
v___x_3135_ = lean_apply_2(v_toPure_3132_, lean_box(0), v___x_3133_);
return v___x_3135_;
}
else
{
lean_object* v_val_3136_; lean_object* v_fst_3137_; lean_object* v___x_3138_; 
lean_dec(v___x_3133_);
v_val_3136_ = lean_ctor_get(v_____do__lift_3134_, 0);
lean_inc(v_val_3136_);
lean_dec_ref_known(v_____do__lift_3134_, 1);
v_fst_3137_ = lean_ctor_get(v_val_3136_, 0);
lean_inc(v_fst_3137_);
lean_dec(v_val_3136_);
v___x_3138_ = lean_apply_2(v_toPure_3132_, lean_box(0), v_fst_3137_);
return v___x_3138_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__3(lean_object* v_toPure_3139_, lean_object* v___x_3140_, lean_object* v___x_3141_, lean_object* v_____do__lift_3142_){
_start:
{
if (lean_obj_tag(v_____do__lift_3142_) == 0)
{
lean_object* v___x_3143_; lean_object* v___x_3144_; 
lean_dec(v___x_3141_);
lean_dec(v___x_3140_);
v___x_3143_ = lean_box(0);
v___x_3144_ = lean_apply_2(v_toPure_3139_, lean_box(0), v___x_3143_);
return v___x_3144_;
}
else
{
lean_object* v_val_3145_; lean_object* v___x_3147_; uint8_t v_isShared_3148_; uint8_t v_isSharedCheck_3176_; 
v_val_3145_ = lean_ctor_get(v_____do__lift_3142_, 0);
v_isSharedCheck_3176_ = !lean_is_exclusive(v_____do__lift_3142_);
if (v_isSharedCheck_3176_ == 0)
{
v___x_3147_ = v_____do__lift_3142_;
v_isShared_3148_ = v_isSharedCheck_3176_;
goto v_resetjp_3146_;
}
else
{
lean_inc(v_val_3145_);
lean_dec(v_____do__lift_3142_);
v___x_3147_ = lean_box(0);
v_isShared_3148_ = v_isSharedCheck_3176_;
goto v_resetjp_3146_;
}
v_resetjp_3146_:
{
if (lean_obj_tag(v_val_3145_) == 0)
{
lean_object* v_a_3149_; lean_object* v___x_3151_; uint8_t v_isShared_3152_; uint8_t v_isSharedCheck_3162_; 
lean_dec(v___x_3141_);
v_a_3149_ = lean_ctor_get(v_val_3145_, 0);
v_isSharedCheck_3162_ = !lean_is_exclusive(v_val_3145_);
if (v_isSharedCheck_3162_ == 0)
{
v___x_3151_ = v_val_3145_;
v_isShared_3152_ = v_isSharedCheck_3162_;
goto v_resetjp_3150_;
}
else
{
lean_inc(v_a_3149_);
lean_dec(v_val_3145_);
v___x_3151_ = lean_box(0);
v_isShared_3152_ = v_isSharedCheck_3162_;
goto v_resetjp_3150_;
}
v_resetjp_3150_:
{
lean_object* v___x_3154_; 
if (v_isShared_3148_ == 0)
{
lean_ctor_set(v___x_3147_, 0, v_a_3149_);
v___x_3154_ = v___x_3147_;
goto v_reusejp_3153_;
}
else
{
lean_object* v_reuseFailAlloc_3161_; 
v_reuseFailAlloc_3161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3161_, 0, v_a_3149_);
v___x_3154_ = v_reuseFailAlloc_3161_;
goto v_reusejp_3153_;
}
v_reusejp_3153_:
{
lean_object* v___x_3155_; lean_object* v___x_3157_; 
v___x_3155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3155_, 0, v___x_3154_);
lean_ctor_set(v___x_3155_, 1, v___x_3140_);
if (v_isShared_3152_ == 0)
{
lean_ctor_set(v___x_3151_, 0, v___x_3155_);
v___x_3157_ = v___x_3151_;
goto v_reusejp_3156_;
}
else
{
lean_object* v_reuseFailAlloc_3160_; 
v_reuseFailAlloc_3160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3160_, 0, v___x_3155_);
v___x_3157_ = v_reuseFailAlloc_3160_;
goto v_reusejp_3156_;
}
v_reusejp_3156_:
{
lean_object* v___x_3158_; lean_object* v___x_3159_; 
v___x_3158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3158_, 0, v___x_3157_);
v___x_3159_ = lean_apply_2(v_toPure_3139_, lean_box(0), v___x_3158_);
return v___x_3159_;
}
}
}
}
else
{
lean_object* v___x_3164_; uint8_t v_isShared_3165_; uint8_t v_isSharedCheck_3174_; 
v_isSharedCheck_3174_ = !lean_is_exclusive(v_val_3145_);
if (v_isSharedCheck_3174_ == 0)
{
lean_object* v_unused_3175_; 
v_unused_3175_ = lean_ctor_get(v_val_3145_, 0);
lean_dec(v_unused_3175_);
v___x_3164_ = v_val_3145_;
v_isShared_3165_ = v_isSharedCheck_3174_;
goto v_resetjp_3163_;
}
else
{
lean_dec(v_val_3145_);
v___x_3164_ = lean_box(0);
v_isShared_3165_ = v_isSharedCheck_3174_;
goto v_resetjp_3163_;
}
v_resetjp_3163_:
{
lean_object* v___x_3166_; lean_object* v___x_3168_; 
v___x_3166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3166_, 0, v___x_3141_);
lean_ctor_set(v___x_3166_, 1, v___x_3140_);
if (v_isShared_3165_ == 0)
{
lean_ctor_set(v___x_3164_, 0, v___x_3166_);
v___x_3168_ = v___x_3164_;
goto v_reusejp_3167_;
}
else
{
lean_object* v_reuseFailAlloc_3173_; 
v_reuseFailAlloc_3173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3173_, 0, v___x_3166_);
v___x_3168_ = v_reuseFailAlloc_3173_;
goto v_reusejp_3167_;
}
v_reusejp_3167_:
{
lean_object* v___x_3170_; 
if (v_isShared_3148_ == 0)
{
lean_ctor_set(v___x_3147_, 0, v___x_3168_);
v___x_3170_ = v___x_3147_;
goto v_reusejp_3169_;
}
else
{
lean_object* v_reuseFailAlloc_3172_; 
v_reuseFailAlloc_3172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3172_, 0, v___x_3168_);
v___x_3170_ = v_reuseFailAlloc_3172_;
goto v_reusejp_3169_;
}
v_reusejp_3169_:
{
lean_object* v___x_3171_; 
v___x_3171_ = lean_apply_2(v_toPure_3139_, lean_box(0), v___x_3170_);
return v___x_3171_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__4(lean_object* v_toPure_3177_, lean_object* v___x_3178_, lean_object* v_inst_3179_, lean_object* v_inst_3180_, lean_object* v_inst_3181_, lean_object* v_inst_3182_, lean_object* v_inst_3183_, lean_object* v_inst_3184_, lean_object* v_n_u2080_3185_, lean_object* v_filter_3186_, lean_object* v_view_x3f_3187_, lean_object* v_toBind_3188_, lean_object* v___f_3189_, lean_object* v___f_3190_, lean_object* v_a_3191_, lean_object* v_x_3192_, lean_object* v___y_3193_){
_start:
{
lean_object* v_snd_3194_; lean_object* v___x_3195_; lean_object* v___f_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; 
v_snd_3194_ = lean_ctor_get(v___y_3193_, 1);
lean_inc(v_snd_3194_);
lean_dec_ref(v___y_3193_);
v___x_3195_ = l_Lean_Name_appendCore(v_a_3191_, v_snd_3194_);
lean_inc(v___x_3195_);
v___f_3196_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__3), 4, 3);
lean_closure_set(v___f_3196_, 0, v_toPure_3177_);
lean_closure_set(v___f_3196_, 1, v___x_3195_);
lean_closure_set(v___f_3196_, 2, v___x_3178_);
v___x_3197_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg(v_inst_3179_, v_inst_3180_, v_inst_3181_, v_inst_3182_, v_inst_3183_, v_inst_3184_, v_n_u2080_3185_, v_filter_3186_, v_view_x3f_3187_, v___x_3195_);
lean_inc_n(v_toBind_3188_, 2);
v___x_3198_ = lean_apply_4(v_toBind_3188_, lean_box(0), lean_box(0), v___x_3197_, v___f_3189_);
v___x_3199_ = lean_apply_4(v_toBind_3188_, lean_box(0), lean_box(0), v___x_3198_, v___f_3190_);
v___x_3200_ = lean_apply_4(v_toBind_3188_, lean_box(0), lean_box(0), v___x_3199_, v___f_3196_);
return v___x_3200_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__4___boxed(lean_object** _args){
lean_object* v_toPure_3201_ = _args[0];
lean_object* v___x_3202_ = _args[1];
lean_object* v_inst_3203_ = _args[2];
lean_object* v_inst_3204_ = _args[3];
lean_object* v_inst_3205_ = _args[4];
lean_object* v_inst_3206_ = _args[5];
lean_object* v_inst_3207_ = _args[6];
lean_object* v_inst_3208_ = _args[7];
lean_object* v_n_u2080_3209_ = _args[8];
lean_object* v_filter_3210_ = _args[9];
lean_object* v_view_x3f_3211_ = _args[10];
lean_object* v_toBind_3212_ = _args[11];
lean_object* v___f_3213_ = _args[12];
lean_object* v___f_3214_ = _args[13];
lean_object* v_a_3215_ = _args[14];
lean_object* v_x_3216_ = _args[15];
lean_object* v___y_3217_ = _args[16];
_start:
{
lean_object* v_res_3218_; 
v_res_3218_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__4(v_toPure_3201_, v___x_3202_, v_inst_3203_, v_inst_3204_, v_inst_3205_, v_inst_3206_, v_inst_3207_, v_inst_3208_, v_n_u2080_3209_, v_filter_3210_, v_view_x3f_3211_, v_toBind_3212_, v___f_3213_, v___f_3214_, v_a_3215_, v_x_3216_, v___y_3217_);
lean_dec(v_a_3215_);
return v_res_3218_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__5(lean_object* v_toPure_3222_, lean_object* v_n_3223_, lean_object* v_inst_3224_, lean_object* v_inst_3225_, lean_object* v_inst_3226_, lean_object* v_inst_3227_, lean_object* v_inst_3228_, lean_object* v_inst_3229_, lean_object* v_n_u2080_3230_, lean_object* v_filter_3231_, lean_object* v_view_x3f_3232_, lean_object* v_toBind_3233_, lean_object* v___f_3234_, lean_object* v___f_3235_, lean_object* v___x_3236_, lean_object* v_____do__lift_3237_){
_start:
{
if (lean_obj_tag(v_____do__lift_3237_) == 0)
{
lean_object* v___x_3238_; lean_object* v___x_3239_; 
lean_dec_ref(v___x_3236_);
lean_dec(v___f_3235_);
lean_dec(v___f_3234_);
lean_dec(v_toBind_3233_);
lean_dec(v_view_x3f_3232_);
lean_dec(v_filter_3231_);
lean_dec(v_n_u2080_3230_);
lean_dec(v_inst_3229_);
lean_dec_ref(v_inst_3228_);
lean_dec(v_inst_3227_);
lean_dec_ref(v_inst_3226_);
lean_dec_ref(v_inst_3225_);
lean_dec_ref(v_inst_3224_);
lean_dec(v_n_3223_);
v___x_3238_ = lean_box(0);
v___x_3239_ = lean_apply_2(v_toPure_3222_, lean_box(0), v___x_3238_);
return v___x_3239_;
}
else
{
lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___f_3243_; lean_object* v___f_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; 
v___x_3240_ = l_Lean_privateToUserName(v_n_3223_);
v___x_3241_ = l_Lean_Name_componentsRev(v___x_3240_);
v___x_3242_ = lean_box(0);
lean_inc(v_toPure_3222_);
v___f_3243_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__2), 3, 2);
lean_closure_set(v___f_3243_, 0, v_toPure_3222_);
lean_closure_set(v___f_3243_, 1, v___x_3242_);
lean_inc(v_toBind_3233_);
v___f_3244_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__4___boxed), 17, 14);
lean_closure_set(v___f_3244_, 0, v_toPure_3222_);
lean_closure_set(v___f_3244_, 1, v___x_3242_);
lean_closure_set(v___f_3244_, 2, v_inst_3224_);
lean_closure_set(v___f_3244_, 3, v_inst_3225_);
lean_closure_set(v___f_3244_, 4, v_inst_3226_);
lean_closure_set(v___f_3244_, 5, v_inst_3227_);
lean_closure_set(v___f_3244_, 6, v_inst_3228_);
lean_closure_set(v___f_3244_, 7, v_inst_3229_);
lean_closure_set(v___f_3244_, 8, v_n_u2080_3230_);
lean_closure_set(v___f_3244_, 9, v_filter_3231_);
lean_closure_set(v___f_3244_, 10, v_view_x3f_3232_);
lean_closure_set(v___f_3244_, 11, v_toBind_3233_);
lean_closure_set(v___f_3244_, 12, v___f_3234_);
lean_closure_set(v___f_3244_, 13, v___f_3235_);
v___x_3245_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__5___closed__0));
v___x_3246_ = l_List_forIn_x27_loop___redArg(v___x_3236_, v___f_3244_, v___x_3241_, v___x_3245_);
lean_dec(v___x_3241_);
v___x_3247_ = lean_apply_4(v_toBind_3233_, lean_box(0), lean_box(0), v___x_3246_, v___f_3243_);
return v___x_3247_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__5___boxed(lean_object* v_toPure_3248_, lean_object* v_n_3249_, lean_object* v_inst_3250_, lean_object* v_inst_3251_, lean_object* v_inst_3252_, lean_object* v_inst_3253_, lean_object* v_inst_3254_, lean_object* v_inst_3255_, lean_object* v_n_u2080_3256_, lean_object* v_filter_3257_, lean_object* v_view_x3f_3258_, lean_object* v_toBind_3259_, lean_object* v___f_3260_, lean_object* v___f_3261_, lean_object* v___x_3262_, lean_object* v_____do__lift_3263_){
_start:
{
lean_object* v_res_3264_; 
v_res_3264_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__5(v_toPure_3248_, v_n_3249_, v_inst_3250_, v_inst_3251_, v_inst_3252_, v_inst_3253_, v_inst_3254_, v_inst_3255_, v_n_u2080_3256_, v_filter_3257_, v_view_x3f_3258_, v_toBind_3259_, v___f_3260_, v___f_3261_, v___x_3262_, v_____do__lift_3263_);
lean_dec(v_____do__lift_3263_);
return v_res_3264_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg(lean_object* v_inst_3265_, lean_object* v_inst_3266_, lean_object* v_inst_3267_, lean_object* v_inst_3268_, lean_object* v_inst_3269_, lean_object* v_inst_3270_, lean_object* v_n_u2080_3271_, lean_object* v_filter_3272_, lean_object* v_view_x3f_3273_, lean_object* v_n_3274_){
_start:
{
lean_object* v___f_3275_; lean_object* v___f_3276_; lean_object* v___f_3277_; lean_object* v___f_3278_; lean_object* v___f_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___y_3286_; uint8_t v___x_3294_; 
lean_inc_ref_n(v_inst_3265_, 7);
v___f_3275_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_3275_, 0, v_inst_3265_);
v___f_3276_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__3), 5, 1);
lean_closure_set(v___f_3276_, 0, v_inst_3265_);
v___f_3277_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__6), 5, 1);
lean_closure_set(v___f_3277_, 0, v_inst_3265_);
v___f_3278_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__9), 5, 1);
lean_closure_set(v___f_3278_, 0, v_inst_3265_);
v___f_3279_ = lean_alloc_closure((void*)(l_OptionT_instMonad___redArg___lam__11), 5, 1);
lean_closure_set(v___f_3279_, 0, v_inst_3265_);
v___x_3280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3280_, 0, v___f_3275_);
lean_ctor_set(v___x_3280_, 1, v___f_3276_);
v___x_3281_ = lean_alloc_closure((void*)(l_OptionT_pure), 4, 2);
lean_closure_set(v___x_3281_, 0, lean_box(0));
lean_closure_set(v___x_3281_, 1, v_inst_3265_);
v___x_3282_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3282_, 0, v___x_3280_);
lean_ctor_set(v___x_3282_, 1, v___x_3281_);
lean_ctor_set(v___x_3282_, 2, v___f_3277_);
lean_ctor_set(v___x_3282_, 3, v___f_3278_);
lean_ctor_set(v___x_3282_, 4, v___f_3279_);
v___x_3283_ = lean_alloc_closure((void*)(l_OptionT_bind), 6, 2);
lean_closure_set(v___x_3283_, 0, lean_box(0));
lean_closure_set(v___x_3283_, 1, v_inst_3265_);
v___x_3284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3284_, 0, v___x_3282_);
lean_ctor_set(v___x_3284_, 1, v___x_3283_);
v___x_3294_ = l_Lean_Name_hasMacroScopes(v_n_3274_);
if (v___x_3294_ == 0)
{
lean_object* v_toApplicative_3295_; lean_object* v_toPure_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; 
v_toApplicative_3295_ = lean_ctor_get(v_inst_3265_, 0);
v_toPure_3296_ = lean_ctor_get(v_toApplicative_3295_, 1);
v___x_3297_ = ((lean_object*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg___lam__2___closed__0));
lean_inc(v_toPure_3296_);
v___x_3298_ = lean_apply_2(v_toPure_3296_, lean_box(0), v___x_3297_);
v___y_3286_ = v___x_3298_;
goto v___jp_3285_;
}
else
{
lean_object* v_toApplicative_3299_; lean_object* v_toPure_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; 
v_toApplicative_3299_ = lean_ctor_get(v_inst_3265_, 0);
v_toPure_3300_ = lean_ctor_get(v_toApplicative_3299_, 1);
v___x_3301_ = lean_box(0);
lean_inc(v_toPure_3300_);
v___x_3302_ = lean_apply_2(v_toPure_3300_, lean_box(0), v___x_3301_);
v___y_3286_ = v___x_3302_;
goto v___jp_3285_;
}
v___jp_3285_:
{
lean_object* v_toApplicative_3287_; lean_object* v_toBind_3288_; lean_object* v_toPure_3289_; lean_object* v___f_3290_; lean_object* v___f_3291_; lean_object* v___f_3292_; lean_object* v___x_3293_; 
v_toApplicative_3287_ = lean_ctor_get(v_inst_3265_, 0);
v_toBind_3288_ = lean_ctor_get(v_inst_3265_, 1);
lean_inc_n(v_toBind_3288_, 2);
v_toPure_3289_ = lean_ctor_get(v_toApplicative_3287_, 1);
lean_inc_n(v_toPure_3289_, 3);
v___f_3290_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__0), 2, 1);
lean_closure_set(v___f_3290_, 0, v_toPure_3289_);
v___f_3291_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__1), 2, 1);
lean_closure_set(v___f_3291_, 0, v_toPure_3289_);
v___f_3292_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg___lam__5___boxed), 16, 15);
lean_closure_set(v___f_3292_, 0, v_toPure_3289_);
lean_closure_set(v___f_3292_, 1, v_n_3274_);
lean_closure_set(v___f_3292_, 2, v_inst_3265_);
lean_closure_set(v___f_3292_, 3, v_inst_3266_);
lean_closure_set(v___f_3292_, 4, v_inst_3267_);
lean_closure_set(v___f_3292_, 5, v_inst_3268_);
lean_closure_set(v___f_3292_, 6, v_inst_3269_);
lean_closure_set(v___f_3292_, 7, v_inst_3270_);
lean_closure_set(v___f_3292_, 8, v_n_u2080_3271_);
lean_closure_set(v___f_3292_, 9, v_filter_3272_);
lean_closure_set(v___f_3292_, 10, v_view_x3f_3273_);
lean_closure_set(v___f_3292_, 11, v_toBind_3288_);
lean_closure_set(v___f_3292_, 12, v___f_3291_);
lean_closure_set(v___f_3292_, 13, v___f_3290_);
lean_closure_set(v___f_3292_, 14, v___x_3284_);
v___x_3293_ = lean_apply_4(v_toBind_3288_, lean_box(0), lean_box(0), v___y_3286_, v___f_3292_);
return v___x_3293_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore(lean_object* v_m_3303_, lean_object* v_inst_3304_, lean_object* v_inst_3305_, lean_object* v_inst_3306_, lean_object* v_inst_3307_, lean_object* v_inst_3308_, lean_object* v_inst_3309_, lean_object* v_n_u2080_3310_, lean_object* v_filter_3311_, lean_object* v_view_x3f_3312_, lean_object* v_n_3313_){
_start:
{
lean_object* v___x_3314_; 
v___x_3314_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg(v_inst_3304_, v_inst_3305_, v_inst_3306_, v_inst_3307_, v_inst_3308_, v_inst_3309_, v_n_u2080_3310_, v_filter_3311_, v_view_x3f_3312_, v_n_3313_);
return v___x_3314_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___lam__0(lean_object* v_n_u2081_3315_, lean_object* v_x1_3316_, lean_object* v_x2_3317_){
_start:
{
lean_object* v___x_3318_; lean_object* v___x_3319_; uint8_t v___x_3320_; 
v___x_3318_ = l_Lean_Name_getPrefix(v_x2_3317_);
v___x_3319_ = l_Lean_Name_getPrefix(v_n_u2081_3315_);
v___x_3320_ = l_Lean_Name_isPrefixOf(v___x_3318_, v___x_3319_);
lean_dec(v___x_3319_);
lean_dec(v___x_3318_);
if (v___x_3320_ == 0)
{
lean_dec(v_x2_3317_);
return v_x1_3316_;
}
else
{
lean_object* v___x_3321_; 
v___x_3321_ = lean_array_push(v_x1_3316_, v_x2_3317_);
return v___x_3321_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___lam__0___boxed(lean_object* v_n_u2081_3322_, lean_object* v_x1_3323_, lean_object* v_x2_3324_){
_start:
{
lean_object* v_res_3325_; 
v_res_3325_ = l_Lean_unresolveNameGlobal_x3f___redArg___lam__0(v_n_u2081_3322_, v_x1_3323_, v_x2_3324_);
lean_dec(v_n_u2081_3322_);
return v_res_3325_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___lam__1(lean_object* v_view_3326_, lean_object* v_n_u2081_3327_, lean_object* v_inst_3328_, lean_object* v_inst_3329_, lean_object* v_inst_3330_, lean_object* v_inst_3331_, lean_object* v_inst_3332_, lean_object* v_inst_3333_, lean_object* v_n_u2080_3334_, lean_object* v_filter_3335_, lean_object* v_toPure_3336_, lean_object* v_____do__lift_3337_){
_start:
{
if (lean_obj_tag(v_____do__lift_3337_) == 0)
{
lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; 
lean_dec(v_toPure_3336_);
v___x_3338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3338_, 0, v_view_3326_);
v___x_3339_ = l_Lean_rootNamespace;
v___x_3340_ = l_Lean_Name_append(v___x_3339_, v_n_u2081_3327_);
v___x_3341_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore___redArg(v_inst_3328_, v_inst_3329_, v_inst_3330_, v_inst_3331_, v_inst_3332_, v_inst_3333_, v_n_u2080_3334_, v_filter_3335_, v___x_3338_, v___x_3340_);
return v___x_3341_;
}
else
{
lean_object* v___x_3342_; 
lean_dec(v_filter_3335_);
lean_dec(v_n_u2080_3334_);
lean_dec(v_inst_3333_);
lean_dec_ref(v_inst_3332_);
lean_dec(v_inst_3331_);
lean_dec_ref(v_inst_3330_);
lean_dec_ref(v_inst_3329_);
lean_dec_ref(v_inst_3328_);
lean_dec(v_n_u2081_3327_);
lean_dec_ref(v_view_3326_);
v___x_3342_ = lean_apply_2(v_toPure_3336_, lean_box(0), v_____do__lift_3337_);
return v___x_3342_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___lam__2(lean_object* v_toPure_3343_, lean_object* v_inst_3344_, lean_object* v_inst_3345_, lean_object* v_inst_3346_, lean_object* v_inst_3347_, lean_object* v_inst_3348_, lean_object* v_inst_3349_, lean_object* v_n_u2080_3350_, lean_object* v_filter_3351_, lean_object* v_toBind_3352_, lean_object* v___f_3353_, uint8_t v_allowHorizAliases_3354_, lean_object* v___f_3355_, lean_object* v_____do__lift_3356_){
_start:
{
lean_object* v_aliases_3358_; 
if (lean_obj_tag(v_____do__lift_3356_) == 0)
{
lean_object* v___x_3365_; lean_object* v___x_3366_; 
lean_dec_ref(v___f_3355_);
lean_dec(v___f_3353_);
lean_dec(v_toBind_3352_);
lean_dec(v_filter_3351_);
lean_dec(v_n_u2080_3350_);
lean_dec(v_inst_3349_);
lean_dec_ref(v_inst_3348_);
lean_dec(v_inst_3347_);
lean_dec_ref(v_inst_3346_);
lean_dec_ref(v_inst_3345_);
lean_dec_ref(v_inst_3344_);
v___x_3365_ = lean_box(0);
v___x_3366_ = lean_apply_2(v_toPure_3343_, lean_box(0), v___x_3365_);
return v___x_3366_;
}
else
{
lean_object* v_val_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; 
lean_dec(v_toPure_3343_);
v_val_3367_ = lean_ctor_get(v_____do__lift_3356_, 0);
lean_inc(v_val_3367_);
lean_dec_ref_known(v_____do__lift_3356_, 1);
lean_inc(v_n_u2080_3350_);
v___x_3368_ = l_Lean_getRevAliases(v_val_3367_, v_n_u2080_3350_);
v___x_3369_ = lean_array_mk(v___x_3368_);
if (v_allowHorizAliases_3354_ == 0)
{
lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; uint8_t v___x_3374_; 
v___x_3370_ = lean_unsigned_to_nat(0u);
v___x_3371_ = lean_array_get_size(v___x_3369_);
v___x_3372_ = ((lean_object*)(l_Lean_resolveNamespace___redArg___closed__1));
v___x_3373_ = ((lean_object*)(l_Lean_resolveLocalName___redArg___lam__3___closed__9));
v___x_3374_ = lean_nat_dec_lt(v___x_3370_, v___x_3371_);
if (v___x_3374_ == 0)
{
lean_dec_ref(v___x_3369_);
lean_dec_ref(v___f_3355_);
v_aliases_3358_ = v___x_3372_;
goto v___jp_3357_;
}
else
{
uint8_t v___x_3375_; 
v___x_3375_ = lean_nat_dec_le(v___x_3371_, v___x_3371_);
if (v___x_3375_ == 0)
{
if (v___x_3374_ == 0)
{
lean_dec_ref(v___x_3369_);
lean_dec_ref(v___f_3355_);
v_aliases_3358_ = v___x_3372_;
goto v___jp_3357_;
}
else
{
size_t v___x_3376_; size_t v___x_3377_; lean_object* v___x_3378_; 
v___x_3376_ = ((size_t)0ULL);
v___x_3377_ = lean_usize_of_nat(v___x_3371_);
v___x_3378_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3373_, v___f_3355_, v___x_3369_, v___x_3376_, v___x_3377_, v___x_3372_);
v_aliases_3358_ = v___x_3378_;
goto v___jp_3357_;
}
}
else
{
size_t v___x_3379_; size_t v___x_3380_; lean_object* v___x_3381_; 
v___x_3379_ = ((size_t)0ULL);
v___x_3380_ = lean_usize_of_nat(v___x_3371_);
v___x_3381_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_3373_, v___f_3355_, v___x_3369_, v___x_3379_, v___x_3380_, v___x_3372_);
v_aliases_3358_ = v___x_3381_;
goto v___jp_3357_;
}
}
}
else
{
lean_dec_ref(v___f_3355_);
v_aliases_3358_ = v___x_3369_;
goto v___jp_3357_;
}
}
v___jp_3357_:
{
lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; 
lean_inc_ref(v_inst_3344_);
v___x_3359_ = l_OptionT_instAlternative___redArg(v_inst_3344_);
v___x_3360_ = lean_box(0);
v___x_3361_ = lean_alloc_closure((void*)(l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_unresolveNameCore), 11, 10);
lean_closure_set(v___x_3361_, 0, lean_box(0));
lean_closure_set(v___x_3361_, 1, v_inst_3344_);
lean_closure_set(v___x_3361_, 2, v_inst_3345_);
lean_closure_set(v___x_3361_, 3, v_inst_3346_);
lean_closure_set(v___x_3361_, 4, v_inst_3347_);
lean_closure_set(v___x_3361_, 5, v_inst_3348_);
lean_closure_set(v___x_3361_, 6, v_inst_3349_);
lean_closure_set(v___x_3361_, 7, v_n_u2080_3350_);
lean_closure_set(v___x_3361_, 8, v_filter_3351_);
lean_closure_set(v___x_3361_, 9, v___x_3360_);
v___x_3362_ = lean_unsigned_to_nat(0u);
v___x_3363_ = l___private_Init_Data_Array_Basic_0__Array_firstM_go(lean_box(0), lean_box(0), lean_box(0), v___x_3359_, v___x_3361_, v_aliases_3358_, v___x_3362_);
v___x_3364_ = lean_apply_4(v_toBind_3352_, lean_box(0), lean_box(0), v___x_3363_, v___f_3353_);
return v___x_3364_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___lam__2___boxed(lean_object* v_toPure_3382_, lean_object* v_inst_3383_, lean_object* v_inst_3384_, lean_object* v_inst_3385_, lean_object* v_inst_3386_, lean_object* v_inst_3387_, lean_object* v_inst_3388_, lean_object* v_n_u2080_3389_, lean_object* v_filter_3390_, lean_object* v_toBind_3391_, lean_object* v___f_3392_, lean_object* v_allowHorizAliases_3393_, lean_object* v___f_3394_, lean_object* v_____do__lift_3395_){
_start:
{
uint8_t v_allowHorizAliases_boxed_3396_; lean_object* v_res_3397_; 
v_allowHorizAliases_boxed_3396_ = lean_unbox(v_allowHorizAliases_3393_);
v_res_3397_ = l_Lean_unresolveNameGlobal_x3f___redArg___lam__2(v_toPure_3382_, v_inst_3383_, v_inst_3384_, v_inst_3385_, v_inst_3386_, v_inst_3387_, v_inst_3388_, v_n_u2080_3389_, v_filter_3390_, v_toBind_3391_, v___f_3392_, v_allowHorizAliases_boxed_3396_, v___f_3394_, v_____do__lift_3395_);
return v_res_3397_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___lam__3(lean_object* v_toPure_3398_, lean_object* v_____do__lift_3399_){
_start:
{
lean_object* v___x_3400_; lean_object* v___x_3401_; 
v___x_3400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3400_, 0, v_____do__lift_3399_);
v___x_3401_ = lean_apply_2(v_toPure_3398_, lean_box(0), v___x_3400_);
return v___x_3401_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___lam__4(lean_object* v_n_u2081_3402_, lean_object* v_inst_3403_, lean_object* v_inst_3404_, lean_object* v_inst_3405_, lean_object* v_inst_3406_, lean_object* v_inst_3407_, lean_object* v_inst_3408_, lean_object* v_n_u2080_3409_, lean_object* v_filter_3410_, lean_object* v___x_3411_, lean_object* v_toPure_3412_, lean_object* v_____do__lift_3413_){
_start:
{
if (lean_obj_tag(v_____do__lift_3413_) == 0)
{
lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; 
lean_dec(v_toPure_3412_);
v___x_3414_ = l_Lean_rootNamespace;
v___x_3415_ = l_Lean_Name_append(v___x_3414_, v_n_u2081_3402_);
v___x_3416_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg(v_inst_3403_, v_inst_3404_, v_inst_3405_, v_inst_3406_, v_inst_3407_, v_inst_3408_, v_n_u2080_3409_, v_filter_3410_, v___x_3411_, v___x_3415_);
return v___x_3416_;
}
else
{
lean_object* v___x_3417_; 
lean_dec(v___x_3411_);
lean_dec(v_filter_3410_);
lean_dec(v_n_u2080_3409_);
lean_dec(v_inst_3408_);
lean_dec_ref(v_inst_3407_);
lean_dec(v_inst_3406_);
lean_dec_ref(v_inst_3405_);
lean_dec_ref(v_inst_3404_);
lean_dec_ref(v_inst_3403_);
lean_dec(v_n_u2081_3402_);
v___x_3417_ = lean_apply_2(v_toPure_3412_, lean_box(0), v_____do__lift_3413_);
return v___x_3417_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg(lean_object* v_inst_3418_, lean_object* v_inst_3419_, lean_object* v_inst_3420_, lean_object* v_inst_3421_, lean_object* v_inst_3422_, lean_object* v_inst_3423_, lean_object* v_n_u2080_3424_, uint8_t v_fullNames_3425_, uint8_t v_allowHorizAliases_3426_, lean_object* v_filter_3427_){
_start:
{
lean_object* v_view_3428_; lean_object* v_name_3429_; lean_object* v_n_u2081_3430_; 
lean_inc(v_n_u2080_3424_);
v_view_3428_ = l_Lean_extractMacroScopes(v_n_u2080_3424_);
v_name_3429_ = lean_ctor_get(v_view_3428_, 0);
lean_inc(v_name_3429_);
v_n_u2081_3430_ = l_Lean_privateToUserName(v_name_3429_);
if (v_fullNames_3425_ == 0)
{
lean_object* v_toApplicative_3431_; lean_object* v_getEnv_3432_; lean_object* v_toBind_3433_; lean_object* v_toPure_3434_; lean_object* v___f_3435_; lean_object* v___f_3436_; lean_object* v___x_3437_; lean_object* v___f_3438_; lean_object* v___f_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; 
v_toApplicative_3431_ = lean_ctor_get(v_inst_3418_, 0);
v_getEnv_3432_ = lean_ctor_get(v_inst_3420_, 0);
lean_inc(v_getEnv_3432_);
v_toBind_3433_ = lean_ctor_get(v_inst_3418_, 1);
lean_inc_n(v_toBind_3433_, 3);
v_toPure_3434_ = lean_ctor_get(v_toApplicative_3431_, 1);
lean_inc_n(v_toPure_3434_, 3);
lean_inc(v_n_u2081_3430_);
v___f_3435_ = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal_x3f___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_3435_, 0, v_n_u2081_3430_);
lean_inc(v_filter_3427_);
lean_inc(v_n_u2080_3424_);
lean_inc(v_inst_3423_);
lean_inc_ref(v_inst_3422_);
lean_inc(v_inst_3421_);
lean_inc_ref(v_inst_3420_);
lean_inc_ref(v_inst_3419_);
lean_inc_ref(v_inst_3418_);
v___f_3436_ = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal_x3f___redArg___lam__1), 12, 11);
lean_closure_set(v___f_3436_, 0, v_view_3428_);
lean_closure_set(v___f_3436_, 1, v_n_u2081_3430_);
lean_closure_set(v___f_3436_, 2, v_inst_3418_);
lean_closure_set(v___f_3436_, 3, v_inst_3419_);
lean_closure_set(v___f_3436_, 4, v_inst_3420_);
lean_closure_set(v___f_3436_, 5, v_inst_3421_);
lean_closure_set(v___f_3436_, 6, v_inst_3422_);
lean_closure_set(v___f_3436_, 7, v_inst_3423_);
lean_closure_set(v___f_3436_, 8, v_n_u2080_3424_);
lean_closure_set(v___f_3436_, 9, v_filter_3427_);
lean_closure_set(v___f_3436_, 10, v_toPure_3434_);
v___x_3437_ = lean_box(v_allowHorizAliases_3426_);
v___f_3438_ = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal_x3f___redArg___lam__2___boxed), 14, 13);
lean_closure_set(v___f_3438_, 0, v_toPure_3434_);
lean_closure_set(v___f_3438_, 1, v_inst_3418_);
lean_closure_set(v___f_3438_, 2, v_inst_3419_);
lean_closure_set(v___f_3438_, 3, v_inst_3420_);
lean_closure_set(v___f_3438_, 4, v_inst_3421_);
lean_closure_set(v___f_3438_, 5, v_inst_3422_);
lean_closure_set(v___f_3438_, 6, v_inst_3423_);
lean_closure_set(v___f_3438_, 7, v_n_u2080_3424_);
lean_closure_set(v___f_3438_, 8, v_filter_3427_);
lean_closure_set(v___f_3438_, 9, v_toBind_3433_);
lean_closure_set(v___f_3438_, 10, v___f_3436_);
lean_closure_set(v___f_3438_, 11, v___x_3437_);
lean_closure_set(v___f_3438_, 12, v___f_3435_);
v___f_3439_ = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal_x3f___redArg___lam__3), 2, 1);
lean_closure_set(v___f_3439_, 0, v_toPure_3434_);
v___x_3440_ = lean_apply_4(v_toBind_3433_, lean_box(0), lean_box(0), v_getEnv_3432_, v___f_3439_);
v___x_3441_ = lean_apply_4(v_toBind_3433_, lean_box(0), lean_box(0), v___x_3440_, v___f_3438_);
return v___x_3441_;
}
else
{
lean_object* v_toApplicative_3442_; lean_object* v_toBind_3443_; lean_object* v_toPure_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___f_3447_; lean_object* v___x_3448_; 
v_toApplicative_3442_ = lean_ctor_get(v_inst_3418_, 0);
v_toBind_3443_ = lean_ctor_get(v_inst_3418_, 1);
lean_inc(v_toBind_3443_);
v_toPure_3444_ = lean_ctor_get(v_toApplicative_3442_, 1);
lean_inc(v_toPure_3444_);
v___x_3445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3445_, 0, v_view_3428_);
lean_inc(v_n_u2081_3430_);
lean_inc_ref(v___x_3445_);
lean_inc(v_filter_3427_);
lean_inc(v_n_u2080_3424_);
lean_inc(v_inst_3423_);
lean_inc_ref(v_inst_3422_);
lean_inc(v_inst_3421_);
lean_inc_ref(v_inst_3420_);
lean_inc_ref(v_inst_3419_);
lean_inc_ref(v_inst_3418_);
v___x_3446_ = l___private_Lean_ResolveName_0__Lean_unresolveNameGlobal_x3f_tryResolve___redArg(v_inst_3418_, v_inst_3419_, v_inst_3420_, v_inst_3421_, v_inst_3422_, v_inst_3423_, v_n_u2080_3424_, v_filter_3427_, v___x_3445_, v_n_u2081_3430_);
v___f_3447_ = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal_x3f___redArg___lam__4), 12, 11);
lean_closure_set(v___f_3447_, 0, v_n_u2081_3430_);
lean_closure_set(v___f_3447_, 1, v_inst_3418_);
lean_closure_set(v___f_3447_, 2, v_inst_3419_);
lean_closure_set(v___f_3447_, 3, v_inst_3420_);
lean_closure_set(v___f_3447_, 4, v_inst_3421_);
lean_closure_set(v___f_3447_, 5, v_inst_3422_);
lean_closure_set(v___f_3447_, 6, v_inst_3423_);
lean_closure_set(v___f_3447_, 7, v_n_u2080_3424_);
lean_closure_set(v___f_3447_, 8, v_filter_3427_);
lean_closure_set(v___f_3447_, 9, v___x_3445_);
lean_closure_set(v___f_3447_, 10, v_toPure_3444_);
v___x_3448_ = lean_apply_4(v_toBind_3443_, lean_box(0), lean_box(0), v___x_3446_, v___f_3447_);
return v___x_3448_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___redArg___boxed(lean_object* v_inst_3449_, lean_object* v_inst_3450_, lean_object* v_inst_3451_, lean_object* v_inst_3452_, lean_object* v_inst_3453_, lean_object* v_inst_3454_, lean_object* v_n_u2080_3455_, lean_object* v_fullNames_3456_, lean_object* v_allowHorizAliases_3457_, lean_object* v_filter_3458_){
_start:
{
uint8_t v_fullNames_boxed_3459_; uint8_t v_allowHorizAliases_boxed_3460_; lean_object* v_res_3461_; 
v_fullNames_boxed_3459_ = lean_unbox(v_fullNames_3456_);
v_allowHorizAliases_boxed_3460_ = lean_unbox(v_allowHorizAliases_3457_);
v_res_3461_ = l_Lean_unresolveNameGlobal_x3f___redArg(v_inst_3449_, v_inst_3450_, v_inst_3451_, v_inst_3452_, v_inst_3453_, v_inst_3454_, v_n_u2080_3455_, v_fullNames_boxed_3459_, v_allowHorizAliases_boxed_3460_, v_filter_3458_);
return v_res_3461_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f(lean_object* v_m_3462_, lean_object* v_inst_3463_, lean_object* v_inst_3464_, lean_object* v_inst_3465_, lean_object* v_inst_3466_, lean_object* v_inst_3467_, lean_object* v_inst_3468_, lean_object* v_n_u2080_3469_, uint8_t v_fullNames_3470_, uint8_t v_allowHorizAliases_3471_, lean_object* v_filter_3472_){
_start:
{
lean_object* v___x_3473_; 
v___x_3473_ = l_Lean_unresolveNameGlobal_x3f___redArg(v_inst_3463_, v_inst_3464_, v_inst_3465_, v_inst_3466_, v_inst_3467_, v_inst_3468_, v_n_u2080_3469_, v_fullNames_3470_, v_allowHorizAliases_3471_, v_filter_3472_);
return v___x_3473_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal_x3f___boxed(lean_object* v_m_3474_, lean_object* v_inst_3475_, lean_object* v_inst_3476_, lean_object* v_inst_3477_, lean_object* v_inst_3478_, lean_object* v_inst_3479_, lean_object* v_inst_3480_, lean_object* v_n_u2080_3481_, lean_object* v_fullNames_3482_, lean_object* v_allowHorizAliases_3483_, lean_object* v_filter_3484_){
_start:
{
uint8_t v_fullNames_boxed_3485_; uint8_t v_allowHorizAliases_boxed_3486_; lean_object* v_res_3487_; 
v_fullNames_boxed_3485_ = lean_unbox(v_fullNames_3482_);
v_allowHorizAliases_boxed_3486_ = lean_unbox(v_allowHorizAliases_3483_);
v_res_3487_ = l_Lean_unresolveNameGlobal_x3f(v_m_3474_, v_inst_3475_, v_inst_3476_, v_inst_3477_, v_inst_3478_, v_inst_3479_, v_inst_3480_, v_n_u2080_3481_, v_fullNames_boxed_3485_, v_allowHorizAliases_boxed_3486_, v_filter_3484_);
return v_res_3487_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___redArg___lam__0(lean_object* v_toPure_3488_, lean_object* v_n_u2080_3489_, lean_object* v_n_x3f_3490_){
_start:
{
if (lean_obj_tag(v_n_x3f_3490_) == 0)
{
lean_object* v___x_3491_; 
v___x_3491_ = lean_apply_2(v_toPure_3488_, lean_box(0), v_n_u2080_3489_);
return v___x_3491_;
}
else
{
lean_object* v_val_3492_; lean_object* v___x_3493_; 
lean_dec(v_n_u2080_3489_);
v_val_3492_ = lean_ctor_get(v_n_x3f_3490_, 0);
lean_inc(v_val_3492_);
lean_dec_ref_known(v_n_x3f_3490_, 1);
v___x_3493_ = lean_apply_2(v_toPure_3488_, lean_box(0), v_val_3492_);
return v___x_3493_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___redArg(lean_object* v_inst_3494_, lean_object* v_inst_3495_, lean_object* v_inst_3496_, lean_object* v_inst_3497_, lean_object* v_inst_3498_, lean_object* v_inst_3499_, lean_object* v_n_u2080_3500_, uint8_t v_fullNames_3501_, uint8_t v_allowHorizAliases_3502_, lean_object* v_filter_3503_){
_start:
{
lean_object* v_toApplicative_3504_; lean_object* v_toBind_3505_; lean_object* v_toPure_3506_; lean_object* v___x_3507_; lean_object* v___f_3508_; lean_object* v___x_3509_; 
v_toApplicative_3504_ = lean_ctor_get(v_inst_3494_, 0);
v_toBind_3505_ = lean_ctor_get(v_inst_3494_, 1);
lean_inc(v_toBind_3505_);
v_toPure_3506_ = lean_ctor_get(v_toApplicative_3504_, 1);
lean_inc(v_toPure_3506_);
lean_inc(v_n_u2080_3500_);
v___x_3507_ = l_Lean_unresolveNameGlobal_x3f___redArg(v_inst_3494_, v_inst_3495_, v_inst_3496_, v_inst_3497_, v_inst_3498_, v_inst_3499_, v_n_u2080_3500_, v_fullNames_3501_, v_allowHorizAliases_3502_, v_filter_3503_);
v___f_3508_ = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3508_, 0, v_toPure_3506_);
lean_closure_set(v___f_3508_, 1, v_n_u2080_3500_);
v___x_3509_ = lean_apply_4(v_toBind_3505_, lean_box(0), lean_box(0), v___x_3507_, v___f_3508_);
return v___x_3509_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___redArg___boxed(lean_object* v_inst_3510_, lean_object* v_inst_3511_, lean_object* v_inst_3512_, lean_object* v_inst_3513_, lean_object* v_inst_3514_, lean_object* v_inst_3515_, lean_object* v_n_u2080_3516_, lean_object* v_fullNames_3517_, lean_object* v_allowHorizAliases_3518_, lean_object* v_filter_3519_){
_start:
{
uint8_t v_fullNames_boxed_3520_; uint8_t v_allowHorizAliases_boxed_3521_; lean_object* v_res_3522_; 
v_fullNames_boxed_3520_ = lean_unbox(v_fullNames_3517_);
v_allowHorizAliases_boxed_3521_ = lean_unbox(v_allowHorizAliases_3518_);
v_res_3522_ = l_Lean_unresolveNameGlobal___redArg(v_inst_3510_, v_inst_3511_, v_inst_3512_, v_inst_3513_, v_inst_3514_, v_inst_3515_, v_n_u2080_3516_, v_fullNames_boxed_3520_, v_allowHorizAliases_boxed_3521_, v_filter_3519_);
return v_res_3522_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal(lean_object* v_m_3523_, lean_object* v_inst_3524_, lean_object* v_inst_3525_, lean_object* v_inst_3526_, lean_object* v_inst_3527_, lean_object* v_inst_3528_, lean_object* v_inst_3529_, lean_object* v_n_u2080_3530_, uint8_t v_fullNames_3531_, uint8_t v_allowHorizAliases_3532_, lean_object* v_filter_3533_){
_start:
{
lean_object* v___x_3534_; 
v___x_3534_ = l_Lean_unresolveNameGlobal___redArg(v_inst_3524_, v_inst_3525_, v_inst_3526_, v_inst_3527_, v_inst_3528_, v_inst_3529_, v_n_u2080_3530_, v_fullNames_3531_, v_allowHorizAliases_3532_, v_filter_3533_);
return v___x_3534_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobal___boxed(lean_object* v_m_3535_, lean_object* v_inst_3536_, lean_object* v_inst_3537_, lean_object* v_inst_3538_, lean_object* v_inst_3539_, lean_object* v_inst_3540_, lean_object* v_inst_3541_, lean_object* v_n_u2080_3542_, lean_object* v_fullNames_3543_, lean_object* v_allowHorizAliases_3544_, lean_object* v_filter_3545_){
_start:
{
uint8_t v_fullNames_boxed_3546_; uint8_t v_allowHorizAliases_boxed_3547_; lean_object* v_res_3548_; 
v_fullNames_boxed_3546_ = lean_unbox(v_fullNames_3543_);
v_allowHorizAliases_boxed_3547_ = lean_unbox(v_allowHorizAliases_3544_);
v_res_3548_ = l_Lean_unresolveNameGlobal(v_m_3535_, v_inst_3536_, v_inst_3537_, v_inst_3538_, v_inst_3539_, v_inst_3540_, v_inst_3541_, v_n_u2080_3542_, v_fullNames_boxed_3546_, v_allowHorizAliases_boxed_3547_, v_filter_3545_);
return v_res_3548_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg___lam__0(lean_object* v_toFunctor_3550_, lean_object* v_inst_3551_, lean_object* v_inst_3552_, lean_object* v_inst_3553_, lean_object* v_inst_3554_, lean_object* v_inst_3555_, lean_object* v_inst_3556_, lean_object* v_inst_3557_, lean_object* v_n_3558_){
_start:
{
lean_object* v_map_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; 
v_map_3559_ = lean_ctor_get(v_toFunctor_3550_, 0);
lean_inc(v_map_3559_);
lean_dec_ref(v_toFunctor_3550_);
v___x_3560_ = ((lean_object*)(l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg___lam__0___closed__0));
v___x_3561_ = l_Lean_resolveLocalName___redArg(v_inst_3551_, v_inst_3552_, v_inst_3553_, v_inst_3554_, v_inst_3555_, v_inst_3556_, v_inst_3557_, v_n_3558_);
v___x_3562_ = lean_apply_4(v_map_3559_, lean_box(0), lean_box(0), v___x_3560_, v___x_3561_);
return v___x_3562_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg(lean_object* v_inst_3563_, lean_object* v_inst_3564_, lean_object* v_inst_3565_, lean_object* v_inst_3566_, lean_object* v_inst_3567_, lean_object* v_inst_3568_, lean_object* v_inst_3569_, lean_object* v_n_u2080_3570_, uint8_t v_fullNames_3571_){
_start:
{
lean_object* v_toApplicative_3572_; lean_object* v_toFunctor_3573_; uint8_t v___x_3574_; lean_object* v___f_3575_; lean_object* v___x_3576_; 
v_toApplicative_3572_ = lean_ctor_get(v_inst_3563_, 0);
v_toFunctor_3573_ = lean_ctor_get(v_toApplicative_3572_, 0);
v___x_3574_ = 0;
lean_inc(v_inst_3568_);
lean_inc_ref(v_inst_3567_);
lean_inc(v_inst_3566_);
lean_inc_ref(v_inst_3565_);
lean_inc_ref(v_inst_3564_);
lean_inc_ref(v_inst_3563_);
lean_inc_ref(v_toFunctor_3573_);
v___f_3575_ = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg___lam__0), 9, 8);
lean_closure_set(v___f_3575_, 0, v_toFunctor_3573_);
lean_closure_set(v___f_3575_, 1, v_inst_3563_);
lean_closure_set(v___f_3575_, 2, v_inst_3564_);
lean_closure_set(v___f_3575_, 3, v_inst_3565_);
lean_closure_set(v___f_3575_, 4, v_inst_3566_);
lean_closure_set(v___f_3575_, 5, v_inst_3567_);
lean_closure_set(v___f_3575_, 6, v_inst_3568_);
lean_closure_set(v___f_3575_, 7, v_inst_3569_);
v___x_3576_ = l_Lean_unresolveNameGlobal_x3f___redArg(v_inst_3563_, v_inst_3564_, v_inst_3565_, v_inst_3566_, v_inst_3567_, v_inst_3568_, v_n_u2080_3570_, v_fullNames_3571_, v___x_3574_, v___f_3575_);
return v___x_3576_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg___boxed(lean_object* v_inst_3577_, lean_object* v_inst_3578_, lean_object* v_inst_3579_, lean_object* v_inst_3580_, lean_object* v_inst_3581_, lean_object* v_inst_3582_, lean_object* v_inst_3583_, lean_object* v_n_u2080_3584_, lean_object* v_fullNames_3585_){
_start:
{
uint8_t v_fullNames_boxed_3586_; lean_object* v_res_3587_; 
v_fullNames_boxed_3586_ = lean_unbox(v_fullNames_3585_);
v_res_3587_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg(v_inst_3577_, v_inst_3578_, v_inst_3579_, v_inst_3580_, v_inst_3581_, v_inst_3582_, v_inst_3583_, v_n_u2080_3584_, v_fullNames_boxed_3586_);
return v_res_3587_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f(lean_object* v_m_3588_, lean_object* v_inst_3589_, lean_object* v_inst_3590_, lean_object* v_inst_3591_, lean_object* v_inst_3592_, lean_object* v_inst_3593_, lean_object* v_inst_3594_, lean_object* v_inst_3595_, lean_object* v_n_u2080_3596_, uint8_t v_fullNames_3597_){
_start:
{
lean_object* v___x_3598_; 
v___x_3598_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg(v_inst_3589_, v_inst_3590_, v_inst_3591_, v_inst_3592_, v_inst_3593_, v_inst_3594_, v_inst_3595_, v_n_u2080_3596_, v_fullNames_3597_);
return v___x_3598_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals_x3f___boxed(lean_object* v_m_3599_, lean_object* v_inst_3600_, lean_object* v_inst_3601_, lean_object* v_inst_3602_, lean_object* v_inst_3603_, lean_object* v_inst_3604_, lean_object* v_inst_3605_, lean_object* v_inst_3606_, lean_object* v_n_u2080_3607_, lean_object* v_fullNames_3608_){
_start:
{
uint8_t v_fullNames_boxed_3609_; lean_object* v_res_3610_; 
v_fullNames_boxed_3609_ = lean_unbox(v_fullNames_3608_);
v_res_3610_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f(v_m_3599_, v_inst_3600_, v_inst_3601_, v_inst_3602_, v_inst_3603_, v_inst_3604_, v_inst_3605_, v_inst_3606_, v_n_u2080_3607_, v_fullNames_boxed_3609_);
return v_res_3610_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals___redArg(lean_object* v_inst_3611_, lean_object* v_inst_3612_, lean_object* v_inst_3613_, lean_object* v_inst_3614_, lean_object* v_inst_3615_, lean_object* v_inst_3616_, lean_object* v_inst_3617_, lean_object* v_n_u2080_3618_, uint8_t v_fullNames_3619_){
_start:
{
lean_object* v_toApplicative_3620_; lean_object* v_toBind_3621_; lean_object* v_toPure_3622_; lean_object* v___x_3623_; lean_object* v___f_3624_; lean_object* v___x_3625_; 
v_toApplicative_3620_ = lean_ctor_get(v_inst_3611_, 0);
v_toBind_3621_ = lean_ctor_get(v_inst_3611_, 1);
lean_inc(v_toBind_3621_);
v_toPure_3622_ = lean_ctor_get(v_toApplicative_3620_, 1);
lean_inc(v_toPure_3622_);
lean_inc(v_n_u2080_3618_);
v___x_3623_ = l_Lean_unresolveNameGlobalAvoidingLocals_x3f___redArg(v_inst_3611_, v_inst_3612_, v_inst_3613_, v_inst_3614_, v_inst_3615_, v_inst_3616_, v_inst_3617_, v_n_u2080_3618_, v_fullNames_3619_);
v___f_3624_ = lean_alloc_closure((void*)(l_Lean_unresolveNameGlobal___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3624_, 0, v_toPure_3622_);
lean_closure_set(v___f_3624_, 1, v_n_u2080_3618_);
v___x_3625_ = lean_apply_4(v_toBind_3621_, lean_box(0), lean_box(0), v___x_3623_, v___f_3624_);
return v___x_3625_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals___redArg___boxed(lean_object* v_inst_3626_, lean_object* v_inst_3627_, lean_object* v_inst_3628_, lean_object* v_inst_3629_, lean_object* v_inst_3630_, lean_object* v_inst_3631_, lean_object* v_inst_3632_, lean_object* v_n_u2080_3633_, lean_object* v_fullNames_3634_){
_start:
{
uint8_t v_fullNames_boxed_3635_; lean_object* v_res_3636_; 
v_fullNames_boxed_3635_ = lean_unbox(v_fullNames_3634_);
v_res_3636_ = l_Lean_unresolveNameGlobalAvoidingLocals___redArg(v_inst_3626_, v_inst_3627_, v_inst_3628_, v_inst_3629_, v_inst_3630_, v_inst_3631_, v_inst_3632_, v_n_u2080_3633_, v_fullNames_boxed_3635_);
return v_res_3636_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals(lean_object* v_m_3637_, lean_object* v_inst_3638_, lean_object* v_inst_3639_, lean_object* v_inst_3640_, lean_object* v_inst_3641_, lean_object* v_inst_3642_, lean_object* v_inst_3643_, lean_object* v_inst_3644_, lean_object* v_n_u2080_3645_, uint8_t v_fullNames_3646_){
_start:
{
lean_object* v___x_3647_; 
v___x_3647_ = l_Lean_unresolveNameGlobalAvoidingLocals___redArg(v_inst_3638_, v_inst_3639_, v_inst_3640_, v_inst_3641_, v_inst_3642_, v_inst_3643_, v_inst_3644_, v_n_u2080_3645_, v_fullNames_3646_);
return v___x_3647_;
}
}
LEAN_EXPORT lean_object* l_Lean_unresolveNameGlobalAvoidingLocals___boxed(lean_object* v_m_3648_, lean_object* v_inst_3649_, lean_object* v_inst_3650_, lean_object* v_inst_3651_, lean_object* v_inst_3652_, lean_object* v_inst_3653_, lean_object* v_inst_3654_, lean_object* v_inst_3655_, lean_object* v_n_u2080_3656_, lean_object* v_fullNames_3657_){
_start:
{
uint8_t v_fullNames_boxed_3658_; lean_object* v_res_3659_; 
v_fullNames_boxed_3658_ = lean_unbox(v_fullNames_3657_);
v_res_3659_ = l_Lean_unresolveNameGlobalAvoidingLocals(v_m_3648_, v_inst_3649_, v_inst_3650_, v_inst_3651_, v_inst_3652_, v_inst_3653_, v_inst_3654_, v_inst_3655_, v_n_u2080_3656_, v_fullNames_boxed_3658_);
return v_res_3659_;
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
